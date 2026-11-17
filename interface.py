"""
Interface gráfica (Tkinter) - Alocação de geradores e capacitores por
Imunidade Biológica (CLONALG).

Uso:  python interface.py [arquivo_do_sistema.txt]

Layout: barra de ferramentas (topo) | relatório e gráfico de convergência
(esquerda) | parâmetros (direita) | indicadores e barra de progresso (rodapé).
O algoritmo roda em uma thread separada, então a janela não trava e o botão
"Parar" funciona a qualquer momento.
"""

import contextlib
import io
import os
import queue
import random
import sys
import threading
import time
import tkinter as tk
import traceback
from tkinter import filedialog, messagebox, scrolledtext, ttk
from tkinter import font as tkfont

import imunidade as im
from fluxo_de_potencia import fluxo_de_potencia
from ler_dados import ler_arquivo
from ordena import ordenar_linhas

PASTA = os.path.dirname(os.path.abspath(__file__))
ARQUIVO_PADRAO = os.path.join(PASTA, "069BusSystem.txt")

# ------------------------------------------------------------
# Parâmetros: (chave, rótulo, padrão, tipo, é_constante_do_módulo)
# ------------------------------------------------------------
PARAMS = {
    "Equipamentos": [
        ("n_ger", "Nº de geradores (0 = nenhum):", 1, int, False),
        ("P_max_kW", "Potência máx. por gerador (kW):", 1500.0, float, False),
        ("custo_ger_kW", "Custo do gerador (R$/kW):", 3500.0, float, False),
        ("n_cap", "Nº de bancos de capacitores:", 1, int, False),
        ("Q_max_kvar", "Potência máx. por banco (kvar):", 1200.0, float, False),
        ("custo_cap_kvar", "Custo do capacitor (R$/kvar):", 60.0, float, False),
        ("custo_perda_kW", "Custo das perdas (R$/kW):", 20000.0, float, False),
    ],
    "Rede": [
        ("S_base_kVA", "Potência base (kVA):", 10000.0, float, False),
        ("tol", "Tolerância do fluxo (pu):", 1e-6, float, False),
        ("V_MIN_PU", "Tensão mínima (pu):", 0.95, float, True),
        ("V_MAX_PU", "Tensão máxima (pu):", 1.05, float, True),
        ("FATOR_POTENCIA", "Fator de potência dos geradores:", 0.90, float, True),
        ("P_PASSO_KW", "Passo de potência ativa (kW):", 50.0, float, True),
        ("Q_PASSO_KVAR", "Passo dos capacitores (kvar):", 150.0, float, True),
    ],
    "CLONALG": [
        ("tam_pop", "Tamanho da população:", 30, int, False),
        ("frac_sel", "Fração selecionada (0-1):", 0.5, float, False),
        ("beta", "Fator de clonagem (beta):", 1.0, float, False),
        ("rho", "Decaimento da mutação (rho):", 3.0, float, False),
        ("frac_renov", "Fração renovada (0-1):", 0.2, float, False),
        ("max_ger", "Nº máximo de gerações:", 200, int, False),
        ("max_estag", "Parar após N gerações sem melhora:", 40, int, False),
        ("n_execucoes", "Execuções independentes:", 5, int, False),
        ("semente", "Semente aleatória:", 42, int, False),
        ("limite_exaustivo", "Limite da busca exaustiva:", 200000, int, False),
    ],
}

TEXTO_AJUDA = """\
COMO USAR

1. Abra o arquivo do sistema (botão Abrir). O sistema de 69 barras é
   carregado automaticamente se estiver na mesma pasta.
2. Ajuste os parâmetros nas abas à direita:
   - Equipamentos: quantidade, tamanho máximo e custos.
   - Rede: base, limites de tensão, fator de potência e passos.
   - CLONALG: população, gerações, execuções e semente.
3. Clique em Executar. O relatório aparece à esquerda; a aba
   "Convergência" mostra o custo da melhor solução a cada geração.
4. Parar interrompe a execução. Salvar grava o relatório em .txt.

O problema é resolvido para 1, 2, ..., N equipamentos (estágios). Se o
espaço de busca for pequeno, usa-se busca exaustiva (ótimo global
comprovado); caso contrário, CLONALG + busca local, com execuções
independentes para confirmar o resultado.

Capacitores são modelados como admitância shunt (Q = Qnom x |V|²).
"""


# ------------------------------------------------------------
# Comunicação thread -> interface
# ------------------------------------------------------------

class _Saida(io.TextIOBase):
    """Recebe os print() do algoritmo e os coloca na fila da interface."""

    def __init__(self, fila):
        self.fila = fila

    def write(self, s):
        if s:
            self.fila.put(("texto", s))
        return len(s)

    def flush(self):
        pass


class _Controle(im.ControleExecucao):
    """Envia o andamento do algoritmo para a interface (e permite parar)."""

    def __init__(self, fila):
        super().__init__()
        self.fila = fila
        self.k, self.K, self.i, self.n = 1, 1, 1, 1

    def _total(self, frac_estagio):
        return min(1.0, (self.k - 1 + min(frac_estagio, 0.99)) / self.K)

    def estagio(self, k, K, n_ger, n_cap):
        super().estagio(k, K, n_ger, n_cap)
        self.k, self.K, self.i, self.n = k, K, 1, 1
        self.fila.put(("estagio", k, K, n_ger, n_cap))

    def execucao(self, rotulo, i, n):
        super().execucao(rotulo, i, n)
        self.i, self.n = i, n
        self.fila.put(("exec", rotulo, i, n))

    def geracao(self, ger, max_ger, estag, max_estag, custo, info):
        super().geracao(ger, max_ger, estag, max_estag, custo, info)
        frac_exec = min(1.0, max(ger / max_ger, estag / max_estag))
        frac = (self.i - 1 + frac_exec) / max(self.n, self.i)
        self.fila.put(("ger", ger, custo, info["perdas_kW"], info["v_min"],
                       self._total(frac)))

    def exaustiva(self, feitos, total):
        super().exaustiva(feitos, total)
        self.fila.put(("exa", feitos, total, self._total(feitos / total)))


def _brl(x):
    return "R$ " + f"{x:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


# ------------------------------------------------------------
# Aplicação
# ------------------------------------------------------------

class App(tk.Tk):

    def __init__(self, arquivo=None):
        super().__init__()
        self.title("Alocação de Geradores e Capacitores - Imunidade Biológica (CLONALG)")
        self.geometry("1320x820")
        self.minsize(1050, 660)

        self.fila = queue.Queue()
        self.thread = None
        self.controle = None
        self.sistema = None            # (dados, (Ni, Nj, ids), caminho)
        self.vars = {}
        self.conv, self.marcas = [], []
        self.conv_sujo = False
        self.t0 = 0.0

        self._estilo()
        self._barra_ferramentas()
        self._corpo()
        self._rodape()
        self._definir_estado(False)

        self.protocol("WM_DELETE_WINDOW", self.sair)
        self.after(80, self._processar_fila)

        caminho = arquivo or (ARQUIVO_PADRAO if os.path.isfile(ARQUIVO_PADRAO) else None)
        if caminho:
            self.carregar_sistema(caminho)
        else:
            self.escrever("Nenhum sistema carregado. Use o botão Abrir.\n")

    # ---------------- construção da janela ----------------

    def _estilo(self):
        st = ttk.Style(self)
        if "clam" in st.theme_names() and sys.platform.startswith("linux"):
            st.theme_use("clam")
        st.configure("Tool.TButton", padding=(10, 4), anchor="center")
        st.configure("Titulo.TLabel", font=("TkDefaultFont", 10, "bold"))
        st.configure("Valor.TLabel", background="white", relief="sunken",
                     anchor="e", padding=(6, 3), font=("TkDefaultFont", 11, "bold"))
        # Fonte monoespaçada em que os caracteres de moldura (┌─│) se conectam
        disponiveis = set(tkfont.families())
        familia = next((f for f in ("Menlo", "Consolas", "DejaVu Sans Mono", "Liberation Mono",
                                    "Lucida Console", "Courier New") if f in disponiveis),
                       tkfont.nametofont("TkFixedFont").actual("family"))
        self.fonte_mono = tkfont.Font(family=familia, size=11)

    def _barra_ferramentas(self):
        barra = ttk.Frame(self, padding=(8, 6))
        barra.pack(side="top", fill="x")
        self.botoes = {}
        itens = [
            ("abrir", "📂\nAbrir", self.abrir),
            ("novo", "📄\nNovo", self.novo),
            ("sair", "✖\nSair", self.sair),
            None,
            ("nova", "↺\nNova análise", self.nova_analise),
            ("executar", "▶\nExecutar", self.executar),
            ("parar", "⏹\nParar", self.parar),
            ("salvar", "💾\nSalvar", self.salvar),
            None,
            ("ajuda", "?\nAjuda", self.ajuda),
            ("sobre", "ℹ\nSobre", self.sobre),
        ]
        for it in itens:
            if it is None:
                ttk.Separator(barra, orient="vertical").pack(side="left", fill="y", padx=8)
                continue
            nome, texto, cmd = it
            b = ttk.Button(barra, text=texto, command=cmd, style="Tool.TButton", width=12)
            b.pack(side="left", padx=2)
            self.botoes[nome] = b
        ttk.Separator(self, orient="horizontal").pack(side="top", fill="x")

    def _corpo(self):
        corpo = ttk.Frame(self, padding=8)
        corpo.pack(side="top", fill="both", expand=True)

        # ----- esquerda: relatório + convergência -----
        esq = ttk.Notebook(corpo)
        esq.pack(side="left", fill="both", expand=True)

        aba_rel = ttk.Frame(esq)
        esq.add(aba_rel, text="Relatório")
        self.texto = scrolledtext.ScrolledText(aba_rel, wrap="none", font=self.fonte_mono,
                                               state="disabled", undo=False,
                                               spacing1=0, spacing2=0, spacing3=0)
        self.texto.pack(fill="both", expand=True)
        xs = ttk.Scrollbar(aba_rel, orient="horizontal", command=self.texto.xview)
        xs.pack(fill="x")
        self.texto.configure(xscrollcommand=xs.set)

        aba_conv = ttk.Frame(esq)
        esq.add(aba_conv, text="Convergência")
        self.canvas = tk.Canvas(aba_conv, background="white", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda e: self._desenhar_convergencia())

        # ----- direita: parâmetros -----
        dir_ = ttk.Frame(corpo, padding=(10, 0, 0, 0))
        dir_.pack(side="right", fill="y")
        ttk.Label(dir_, text="Parâmetros", style="Titulo.TLabel").pack(anchor="w")
        nb = ttk.Notebook(dir_)
        nb.pack(fill="y", expand=True, pady=(2, 6))
        for grupo, itens in PARAMS.items():
            f = ttk.Frame(nb, padding=10)
            nb.add(f, text=grupo)
            for r, (chave, rotulo, padrao, tipo, _) in enumerate(itens):
                ttk.Label(f, text=rotulo).grid(row=r, column=0, sticky="w", pady=3)
                v = tk.StringVar(value=str(padrao))
                self.vars[chave] = v
                ttk.Entry(f, textvariable=v, width=11, justify="right").grid(
                    row=r, column=1, sticky="e", padx=(10, 0), pady=3)
            if grupo == "CLONALG":
                r = len(itens)
                ttk.Button(f, text="Trocar a semente aleatória",
                           command=self.trocar_semente).grid(
                    row=r, column=0, columnspan=2, sticky="ew", pady=(10, 3))
                self.var_fluxo = tk.BooleanVar(value=False)
                ttk.Checkbutton(f, text="Mostrar o fluxo de potência completo",
                                variable=self.var_fluxo).grid(
                    row=r + 1, column=0, columnspan=2, sticky="w", pady=3)
        ttk.Label(dir_, text="Dica: use '.' ou ',' como separador decimal.",
                  foreground="gray40").pack(anchor="w")

    def _rodape(self):
        rod = ttk.Frame(self, padding=(10, 4, 10, 10))
        rod.pack(side="bottom", fill="x")
        campos = ttk.Frame(rod)
        campos.pack(fill="x")
        self.indic = {}
        defs = [("estagio", "Estágio", 90), ("exec", "Execução", 90), ("ger", "Geração", 90),
                ("custo", "Melhor custo (R$)", 190), ("perdas", "Perdas (kW)", 110),
                ("vmin", "Tensão mín. (pu)", 120), ("tempo", "Tempo", 90)]
        for col, (k, rot, larg) in enumerate(defs):
            ttk.Label(campos, text=rot, style="Titulo.TLabel").grid(row=0, column=col, sticky="w", padx=4)
            lb = ttk.Label(campos, text="-", style="Valor.TLabel", width=max(6, larg // 9))
            lb.grid(row=1, column=col, sticky="ew", padx=4)
            campos.columnconfigure(col, weight=1)
            self.indic[k] = lb
        linha = ttk.Frame(rod)
        linha.pack(fill="x", pady=(8, 0))
        self.barra = ttk.Progressbar(linha, maximum=100, mode="determinate")
        self.barra.pack(side="left", fill="x", expand=True)
        self.lbl_pct = ttk.Label(linha, text="0%", width=6, anchor="e")
        self.lbl_pct.pack(side="left", padx=(8, 0))
        self.lbl_status = ttk.Label(rod, text="Pronto.", foreground="gray30")
        self.lbl_status.pack(anchor="w", pady=(4, 0))

    # ---------------- utilidades ----------------

    def escrever(self, s):
        self.texto.configure(state="normal")
        self.texto.insert("end", s)
        self.texto.see("end")
        self.texto.configure(state="disabled")

    def _status(self, s):
        self.lbl_status.configure(text=s)

    def _definir_estado(self, rodando):
        self.rodando = rodando
        for n in ("abrir", "novo", "nova", "executar"):
            self.botoes[n].configure(state="disabled" if rodando else "normal")
        self.botoes["parar"].configure(state="normal" if rodando else "disabled")

    def _progresso(self, frac):
        self.barra["value"] = 100 * frac
        self.lbl_pct.configure(text=f"{100 * frac:.0f}%")

    def _zerar_indicadores(self):
        for lb in self.indic.values():
            lb.configure(text="-")
        self._progresso(0)
        self.conv, self.marcas = [], []
        self.conv_sujo = True

    # ---------------- ações da barra de ferramentas ----------------

    def abrir(self):
        caminho = filedialog.askopenfilename(
            title="Abrir arquivo do sistema", initialdir=PASTA,
            filetypes=[("Arquivos de texto", "*.txt"), ("Todos", "*.*")])
        if caminho:
            self.carregar_sistema(caminho)

    def carregar_sistema(self, caminho):
        try:
            dados = ler_arquivo(caminho)
            ordem = ordenar_linhas(dados)
            if not dados["barras"] or not dados["linhas"]:
                raise ValueError("O arquivo não contém barras e/ou linhas.")
            base = fluxo_de_potencia(dados, *ordem, tol=1e-6)
        except Exception as e:
            messagebox.showerror("Erro ao abrir o arquivo", f"{type(e).__name__}: {e}")
            return
        self.sistema = (dados, ordem, caminho)
        vmin = min(abs(v) for v in base["V"].values())
        pc = sum(b["SaReal"] for b in dados["barras"])
        qc = sum(b["SaImag"] for b in dados["barras"])
        self.escrever(
            "=" * 60 + "\nSISTEMA CARREGADO\n" + "=" * 60 + "\n"
            f"Arquivo        : {os.path.basename(caminho)}\n"
            f"Barras / linhas: {len(dados['barras'])} / {len(dados['linhas'])}\n"
            f"Tensão base    : {dados['voltage_kv']} kV\n"
            f"Carga total    : {pc:.2f} kW + j{qc:.2f} kvar\n"
            f"Caso base      : perdas = {base['perdas_kW']:.3f} kW | Vmin = {vmin:.5f} pu\n\n")
        self._status(f"Sistema: {os.path.basename(caminho)}")
        self.title(f"CLONALG - {os.path.basename(caminho)}")

    def novo(self):
        for grupo in PARAMS.values():
            for chave, _, padrao, _, _ in grupo:
                self.vars[chave].set(str(padrao))
        self.var_fluxo.set(False)
        self._status("Parâmetros restaurados para os valores padrão.")

    def nova_analise(self):
        self.texto.configure(state="normal")
        self.texto.delete("1.0", "end")
        self.texto.configure(state="disabled")
        self._zerar_indicadores()
        self._status("Pronto.")

    def trocar_semente(self):
        self.vars["semente"].set(str(random.randint(1, 999999)))

    def salvar(self):
        conteudo = self.texto.get("1.0", "end").strip()
        if not conteudo:
            messagebox.showinfo("Salvar", "Não há relatório para salvar.")
            return
        caminho = filedialog.asksaveasfilename(
            title="Salvar relatório", defaultextension=".txt", initialfile="relatorio_clonalg.txt",
            filetypes=[("Arquivo de texto", "*.txt")])
        if caminho:
            with open(caminho, "w", encoding="utf-8") as f:
                f.write(conteudo + "\n")
            self._status(f"Relatório salvo em {caminho}")

    def ajuda(self):
        messagebox.showinfo("Ajuda", TEXTO_AJUDA)

    def sobre(self):
        messagebox.showinfo(
            "Sobre",
            "Alocação conjunta de geradores e bancos de capacitores\n"
            "em redes de distribuição radiais.\n\n"
            "Algoritmo: Imunidade Biológica (CLONALG)\n"
            "Fluxo de potência: varredura backward/forward")

    def sair(self):
        if self.rodando:
            if not messagebox.askyesno("Sair", "Há uma execução em andamento. Deseja sair mesmo assim?"):
                return
            self.controle.solicitar_parada()
        self.destroy()

    # ---------------- execução ----------------

    def _ler_parametros(self):
        vals = {}
        for grupo in PARAMS.values():
            for chave, rotulo, _, tipo, _ in grupo:
                txt = self.vars[chave].get().strip().replace(",", ".")
                try:
                    x = float(txt)
                    if tipo is int:
                        if x != int(x):
                            raise ValueError
                        x = int(x)
                except ValueError:
                    raise ValueError(f"Valor inválido em '{rotulo.rstrip(':')}': '{txt}'")
                vals[chave] = x

        def exige(cond, msg):
            if not cond:
                raise ValueError(msg)

        exige(vals["n_ger"] >= 0 and vals["n_cap"] >= 0, "As quantidades de equipamentos não podem ser negativas.")
        exige(vals["n_ger"] + vals["n_cap"] >= 1, "Informe ao menos 1 gerador ou 1 banco de capacitores.")
        exige(vals["S_base_kVA"] > 0 and vals["tol"] > 0, "Potência base e tolerância devem ser positivas.")
        exige(0 < vals["V_MIN_PU"] < vals["V_MAX_PU"], "A tensão mínima deve ser menor que a máxima.")
        exige(0 < vals["FATOR_POTENCIA"] <= 1, "O fator de potência deve estar em (0, 1].")
        exige(vals["P_PASSO_KW"] > 0 and vals["Q_PASSO_KVAR"] > 0, "Os passos de potência devem ser positivos.")
        exige(vals["tam_pop"] >= 2, "A população deve ter ao menos 2 indivíduos.")
        exige(0 < vals["frac_sel"] <= 1 and 0 < vals["frac_renov"] < 1,
              "Fração selecionada em (0,1] e fração renovada em (0,1).")
        exige(vals["max_ger"] >= 1 and vals["max_estag"] >= 1 and vals["n_execucoes"] >= 1,
              "Gerações, estagnação e execuções devem ser >= 1.")
        return vals

    def executar(self):
        if self.rodando:
            return
        if self.sistema is None:
            messagebox.showwarning("Executar", "Abra primeiro o arquivo do sistema.")
            return
        try:
            vals = self._ler_parametros()
        except ValueError as e:
            messagebox.showerror("Parâmetro inválido", str(e))
            return
        for chave in [c for g in PARAMS.values() for c, _, _, _, glob in g if glob]:
            setattr(im, chave, vals.pop(chave))      # constantes do módulo imunidade
        vals.update(mostrar_fluxo_final=self.var_fluxo.get(), verbose=True)

        self.controle = _Controle(self.fila)
        vals["ctl"] = self.controle
        self._zerar_indicadores()
        self.t0 = time.time()
        self._definir_estado(True)
        self._status("Executando...")
        self.thread = threading.Thread(target=self._trabalho, args=(vals,), daemon=True)
        self.thread.start()

    def _trabalho(self, args):
        dados, ordem, _ = self.sistema
        try:
            with contextlib.redirect_stdout(_Saida(self.fila)):
                res = im.imunidade(dados, *ordem, **args)
            self.fila.put(("fim", res))
        except im.Interrompido:
            self.fila.put(("parado",))
        except Exception:
            self.fila.put(("erro", traceback.format_exc()))

    def parar(self):
        if self.rodando and self.controle:
            self.controle.solicitar_parada()
            self._status("Parando...")

    # ---------------- fila de eventos ----------------

    def _processar_fila(self):
        ultimo_ger = None
        buf = []
        try:
            while True:
                ev = self.fila.get_nowait()
                tipo = ev[0]
                if tipo == "texto":
                    buf.append(ev[1])
                elif tipo == "estagio":
                    _, k, K, ng, nc = ev
                    self.indic["estagio"].configure(text=f"{k}/{K}")
                    self._status(f"Estágio {k}/{K}: {ng} gerador(es) + {nc} capacitor(es)")
                    self.conv, self.marcas, self.conv_sujo = [], [], True
                    for kk in ("exec", "ger", "custo", "perdas", "vmin"):
                        self.indic[kk].configure(text="-")
                elif tipo == "exec":
                    _, rotulo, i, n = ev
                    self.indic["exec"].configure(text=f"{i}/{n}" if i <= n else rotulo.split()[-1])
                    self.marcas.append(len(self.conv))
                    self.indic["ger"].configure(text="-")
                elif tipo == "ger":
                    ultimo_ger = ev
                    self.conv.append(ev[2])
                    self.conv_sujo = True
                elif tipo == "exa":
                    _, feitos, total, frac = ev
                    self.indic["exec"].configure(text="exaustiva")
                    self.indic["ger"].configure(text=f"{100 * feitos / total:.0f}%")
                    self._progresso(frac)
                elif tipo == "fim":
                    ultimo_ger = None            # não sobrescrever o custo final
                    self._finalizar(ev[1])
                elif tipo == "parado":
                    self._definir_estado(False)
                    self.escrever("\n*** Execução interrompida pelo usuário. ***\n")
                    self._status("Execução interrompida.")
                elif tipo == "erro":
                    self._definir_estado(False)
                    self.escrever("\n*** ERRO ***\n" + ev[1])
                    self._status("Erro durante a execução.")
                    messagebox.showerror("Erro", ev[1].strip().splitlines()[-1])
        except queue.Empty:
            pass

        if buf:
            self.escrever("".join(buf))
        if ultimo_ger:
            _, ger, custo, perdas, vmin, frac = ultimo_ger
            self.indic["ger"].configure(text=str(ger))
            self.indic["custo"].configure(text=f"{custo:,.2f}".replace(",", "X").replace(".", ",").replace("X", "."))
            self.indic["perdas"].configure(text=f"{perdas:.3f}")
            self.indic["vmin"].configure(text=f"{vmin:.5f}")
            self._progresso(frac)
        if self.rodando:
            self.indic["tempo"].configure(text=f"{time.time() - self.t0:.1f} s")
        if self.conv_sujo:
            self._desenhar_convergencia()
        self.after(100, self._processar_fila)

    def _finalizar(self, res):
        self._definir_estado(False)
        self._progresso(1.0)
        self.indic["custo"].configure(text=f"{res['custo']:,.2f}".replace(",", "X").replace(".", ",").replace("X", "."))
        self.indic["perdas"].configure(text=f"{res['perdas_kW']:.3f}")
        self.indic["vmin"].configure(text=f"{res['v_min']:.5f}")
        self.indic["tempo"].configure(text=f"{time.time() - self.t0:.1f} s")
        self._status("Concluído. Restrições atendidas." if res["viavel"]
                     else "Concluído, mas a solução VIOLA restrições (veja o relatório).")

    # ---------------- gráfico de convergência ----------------

    def _desenhar_convergencia(self):
        self.conv_sujo = False
        c = self.canvas
        c.delete("all")
        W, H = c.winfo_width(), c.winfo_height()
        ml, mr, mt, mb = 110, 20, 30, 40
        c.create_text(W / 2, 14, text="Custo da melhor solução por geração (estágio atual)",
                      font=("TkDefaultFont", 11, "bold"))
        c.create_rectangle(ml, mt, W - mr, H - mb, outline="gray60")
        dados = self.conv[-20000:]
        if len(dados) < 2:
            c.create_text(W / 2, H / 2, text="Sem dados ainda", fill="gray50")
            return
        lo, hi = min(dados), max(dados)
        folga = max((hi - lo) * 0.08, abs(hi) * 0.002, 1.0)   # evita linha colada na borda
        lo, hi = lo - folga, hi + folga
        n = len(dados)
        px = lambda i: ml + (W - ml - mr) * i / (n - 1)
        py = lambda y: (H - mb) - (H - mb - mt) * (y - lo) / (hi - lo)
        for j in range(5):
            y = lo + (hi - lo) * j / 4
            c.create_line(ml, py(y), W - mr, py(y), fill="gray88")
            c.create_text(ml - 6, py(y), text=f"{y:,.0f}".replace(",", "."), anchor="e", font=("TkDefaultFont", 9))
        for m in self.marcas:
            if 0 < m < n:
                c.create_line(px(m), mt, px(m), H - mb, fill="gray70", dash=(3, 3))
        pts = [coord for i, y in enumerate(dados) for coord in (px(i), py(y))]
        c.create_line(*pts, fill="#1f6feb", width=2)
        c.create_text(W / 2, H - 14, text="gerações acumuladas (linhas tracejadas = nova execução)  |  eixo y: custo total (R$)",
                      font=("TkDefaultFont", 9), fill="gray30")


if __name__ == "__main__":
    App(sys.argv[1] if len(sys.argv) > 1 else None).mainloop()