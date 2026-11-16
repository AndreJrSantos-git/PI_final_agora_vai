# ============================================================
# IMUNIDADE BIOLÓGICA (CLONALG) APLICADA AO FLUXO DE POTÊNCIA
# ALOCAÇÃO CONJUNTA DE GERADORES E BANCOS DE CAPACITORES (COM CUSTOS)
# ============================================================
# Anticorpo = (genes_geradores, genes_capacitores), gene = (barra, nivel)
#   gerador   : P = nivel * P_PASSO_KW ; Q = P * tan(acos(FATOR_POTENCIA))
#               (potência constante)
#   capacitor : Q_nominal = nivel * Q_PASSO_KVAR ; P = 0
#               modelado como ADMITÂNCIA SHUNT: fornece Q_nominal * |V|^2
# Função objetivo (R$) = custo das perdas + custo dos geradores
#                        + custo dos capacitores + penalidades
# Restrições por penalização: convergência, limites de tensão e
# injeção total de P e Q <= carga total (sem fluxo reverso na SE).
#
# ANÁLISE INCREMENTAL (ponto de parada):
#   O problema é resolvido para 1, 2, ..., N equipamentos. Se a redução
#   de perdas ao acrescentar o k-ésimo for < LIMIAR_GANHO_PERDAS, o
#   código continua até N, mas ao final informa que k-1 já bastava.
#
# GARANTIA DE CONVERGÊNCIA (veja _otimizar_estagio):
#   1) espaço pequeno  -> busca exaustiva (ótimo global comprovado), feita
#      ANTES do CLONALG; se couber, o CLONALG nem precisa rodar;
#   2) espaço grande   -> execuções extras automáticas até a melhor
#      solução ser reencontrada por execuções independentes, busca
#      local com vizinhança estendida e alerta se alguma execução
#      parou por limite de gerações (e não por estagnação).
# ============================================================

import math
import random
import time
from itertools import combinations, product

from fluxo_de_potencia import fluxo_de_potencia, imprimir_resultados

# ------------------------------------------------------------
# CONSTANTES (antes eram perguntadas ao usuário)
# ------------------------------------------------------------
P_PASSO_KW = 50.0             # resolução da potência ativa dos geradores
Q_PASSO_KVAR = 150.0          # resolução dos bancos de capacitores
FATOR_POTENCIA = 0.90         # fp dos geradores (injetam Q junto com P)
V_MIN_PU = 0.95               # limite inferior de tensão (PRODIST/ANEEL)
V_MAX_PU = 1.05               # limite superior de tensão
LIMIAR_GANHO_PERDAS = 0.01    # ganho < 1 % nas perdas => "já não vale a pena"

# Penalidades (em kW equivalentes de perda; multiplicadas pelo custo do kW de perda)
PENAL_TENSAO = 1.0e5          # por pu de violação de tensão acumulada
PENAL_EXCESSO = 100.0         # por kW/kvar injetado acima da carga total
CUSTO_NAO_CONVERGIU = 1.0e15

# Controle de convergência
LIMITE_EXAUSTIVO = 200000     # espaços até este tamanho são varridos por completo
MIN_CONFIRMACOES = 2          # nº de execuções independentes que devem achar o melhor custo
MAX_EXTRAS = 10               # máximo de execuções extras para obter a confirmação
RAIO_NIVEIS = 3               # vizinhança estendida: troca de barra + nível em ±3
TOL_CUSTO_REL = 1e-5          # tolerância RELATIVA para considerar "mesmo custo"


def _mesmo_custo(a, b):
    return abs(a - b) <= TOL_CUSTO_REL * max(1.0, abs(a), abs(b))


class Interrompido(Exception):
    """Lançada quando o usuário pede para parar a execução."""


class ControleExecucao:
    """
    Ganchos de progresso e parada. A versão base não faz nada (além de
    respeitar o pedido de parada); a interface gráfica herda esta classe
    para receber o andamento do algoritmo.
    """

    def __init__(self):
        self._parar = False

    def solicitar_parada(self):
        self._parar = True

    def verificar(self):
        if self._parar:
            raise Interrompido()

    def estagio(self, k, K, n_ger, n_cap):
        self.verificar()

    def execucao(self, rotulo, i, n):
        self.verificar()

    def geracao(self, ger, max_ger, estag, max_estag, custo, info):
        self.verificar()

    def exaustiva(self, feitos, total):
        self.verificar()


def _brl(x):
    return "R$ " + f"{x:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


# ============================================================
# PROBLEMA (antígeno) + AVALIAÇÃO DE AFINIDADE
# ============================================================

class _Problema:

    def __init__(self, dados, Ni, Nj, ids, n_ger, P_max_kW, n_cap, Q_max_kvar,
                 S_base_kVA, tol, custos, rng):
        self.dados, self.Ni, self.Nj, self.ids = dados, Ni, Nj, ids
        self.n_ger, self.n_cap = n_ger, n_cap
        self.nl_ger = int(P_max_kW // P_PASSO_KW)
        self.nl_cap = int(Q_max_kvar // Q_PASSO_KVAR)
        self.tan_phi = math.tan(math.acos(FATOR_POTENCIA))
        self.S_base_kVA, self.tol = S_base_kVA, tol
        self.c, self.rng = custos, rng

        if n_ger < 0 or n_cap < 0 or n_ger + n_cap < 1:
            raise ValueError("Informe ao menos 1 gerador ou 1 banco de capacitores.")
        if n_ger > 0 and self.nl_ger < 1:
            raise ValueError(f"P_max deve ser >= {P_PASSO_KW:g} kW.")
        if n_cap > 0 and self.nl_cap < 1:
            raise ValueError(f"Q_max deve ser >= {Q_PASSO_KVAR:g} kvar.")

        self.SE = next(b["id"] for b in dados["barras"] if b["type"] == "SE")
        self.candidatas = [b["id"] for b in dados["barras"] if b["id"] != self.SE]
        if max(n_ger, n_cap) > len(self.candidatas):
            raise ValueError("Quantidade de equipamentos maior que o nº de barras candidatas.")

        self.P_carga_total = sum(b["SaReal"] for b in dados["barras"])
        self.Q_carga_total = sum(b["SaImag"] for b in dados["barras"])

        # Vizinhança (grafo não direcionado) para mutação local de posição
        self.adj = {b["id"]: [] for b in dados["barras"]}
        for l in dados["linhas"]:
            self.adj[l["Ni"]].append(l["Nj"])
            self.adj[l["Nj"]].append(l["Ni"])

        self.cache, self.n_fluxos, self.n_hits = {}, 0, 0
        self.ctl = ControleExecucao()

    # ---------------- injeções e custos ----------------

    def injecoes_de(self, ab):
        """Geradores (potência constante). Retorna (inj, P_tot, Q_tot nominal);
        Q_tot inclui o Q NOMINAL dos capacitores (restrição de não-reverso)."""
        inj, P_tot, Q_tot = {}, 0.0, 0.0
        for barra, nivel in ab[0]:
            P = nivel * P_PASSO_KW
            Q = P * self.tan_phi
            inj[barra] = inj.get(barra, 0j) + complex(P, Q)
            P_tot += P
            Q_tot += Q
        for _, nivel in ab[1]:
            Q_tot += nivel * Q_PASSO_KVAR
        return inj, P_tot, Q_tot

    def capacitores_de(self, ab):
        """Bancos de capacitores {barra: kvar nominal} (admitância shunt)."""
        caps = {}
        for barra, nivel in ab[1]:
            caps[barra] = caps.get(barra, 0.0) + nivel * Q_PASSO_KVAR
        return caps

    def custo_equip(self, ab):
        """Retorna (custo dos geradores, custo dos capacitores) em R$."""
        c_ger = sum(n * P_PASSO_KW * self.c["ger_kW"] for _, n in ab[0])
        c_cap = sum(n * Q_PASSO_KVAR * self.c["cap_kvar"] for _, n in ab[1])
        return c_ger, c_cap

    # ---------------- avaliação (com cache) ----------------

    def avaliar(self, ab, usar_cache=True):
        if usar_cache and ab in self.cache:
            self.n_hits += 1
            return self.cache[ab]

        self.ctl.verificar()                 # permite parar a qualquer momento
        inj, P_tot, Q_tot = self.injecoes_de(ab)
        res = fluxo_de_potencia(self.dados, self.Ni, self.Nj, self.ids,
                                S_base_kVA=self.S_base_kVA, tol=self.tol, injecoes=inj,
                                capacitores=self.capacitores_de(ab))
        self.n_fluxos += 1

        mod = [abs(v) for v in res["V"].values()]
        viol = sum(max(0.0, V_MIN_PU - m) + max(0.0, m - V_MAX_PU) for m in mod)
        exc_P = max(0.0, P_tot - self.P_carga_total)
        exc_Q = max(0.0, Q_tot - self.Q_carga_total)

        c_ger, c_cap = self.custo_equip(ab)
        c_perd = res["perdas_kW"] * self.c["perda_kW"]
        if res["convergiu"]:
            custo = (c_perd + c_ger + c_cap + self.c["perda_kW"]
                     * (PENAL_TENSAO * viol + PENAL_EXCESSO * (exc_P + exc_Q)))
        else:
            custo = CUSTO_NAO_CONVERGIU

        info = {"custo": custo, "perdas_kW": res["perdas_kW"], "v_min": min(mod),
                "v_max": max(mod), "violacao": viol, "excesso_P": exc_P,
                "excesso_Q": exc_Q, "convergiu": res["convergiu"],
                "P_total": P_tot, "Q_total": Q_tot, "custo_perdas": c_perd,
                "custo_ger": c_ger, "custo_cap": c_cap,
                "custo_total": c_perd + c_ger + c_cap}
        if usar_cache:
            self.cache[ab] = info
        return info

    def custo(self, ab):
        return self.avaliar(ab)["custo"]

    def viavel(self, ab):
        i = self.avaliar(ab)
        return (i["convergiu"] and i["violacao"] <= 1e-12
                and i["excesso_P"] <= 1e-9 and i["excesso_Q"] <= 1e-9)

    # ---------------- operadores ----------------

    def _reparar(self, genes):
        """Garante barras distintas dentro do mesmo grupo e ordena."""
        todas = {b for b, _ in genes}
        usadas, saida = set(), []
        for b, n in genes:
            if b in usadas:
                livres = ([c for c in self.candidatas if c not in usadas and c not in todas]
                          or [c for c in self.candidatas if c not in usadas])
                b = self.rng.choice(livres)
            usadas.add(b)
            saida.append((b, n))
        return tuple(sorted(saida))

    def canonizar(self, ger, cap):
        return (self._reparar(ger), self._reparar(cap))

    def aleatorio(self):
        sorteio = lambda n, nl: tuple(sorted((b, self.rng.randint(1, nl))
                                             for b in self.rng.sample(self.candidatas, n)))
        return (sorteio(self.n_ger, self.nl_ger), sorteio(self.n_cap, self.nl_cap))

    def estender(self, ab):
        """Completa um anticorpo de estágio anterior (menos genes) até o tamanho atual."""
        def completa(genes, n, nl):
            genes = list(genes)
            usadas = {b for b, _ in genes}
            while len(genes) < n:
                b = self.rng.choice([c for c in self.candidatas if c not in usadas])
                usadas.add(b)
                genes.append((b, self.rng.randint(1, nl)))
            return genes
        return self.canonizar(completa(ab[0], self.n_ger, self.nl_ger),
                              completa(ab[1], self.n_cap, self.nl_cap))

    def _mover_barra(self, barra, alpha):
        # Prob. alpha: salto global (exploração); senão passeio curto (refinamento local)
        if self.rng.random() < alpha:
            return self.rng.choice(self.candidatas)
        for _ in range(self.rng.randint(1, 3)):
            viz = [v for v in self.adj[barra] if v != self.SE]
            if viz:
                barra = self.rng.choice(viz)
        return barra

    def _mutar_gene(self, gene, n_niveis, alpha):
        barra, nivel = gene
        mut_barra = self.rng.random() < 0.5
        if mut_barra:
            barra = self._mover_barra(barra, alpha)
        if not mut_barra or self.rng.random() < 0.5:
            passo = max(1, int(round(alpha * n_niveis * abs(self.rng.gauss(0.0, 0.5)))))
            nivel = min(n_niveis, max(1, nivel + self.rng.choice((-1, 1)) * passo))
        return (barra, nivel)

    def hipermutar(self, ab, alpha):
        """Hipermutação somática: alpha (0..1) = intensidade da mutação."""
        ger, cap = list(ab[0]), list(ab[1])
        total = self.n_ger + self.n_cap
        for idx in self.rng.sample(range(total), max(1, int(round(alpha * total)))):
            if idx < self.n_ger:
                ger[idx] = self._mutar_gene(ger[idx], self.nl_ger, alpha)
            else:
                j = idx - self.n_ger
                cap[j] = self._mutar_gene(cap[j], self.nl_cap, alpha)
        return self.canonizar(ger, cap)

    def vizinhos(self, ab, raio_niveis=None):
        """
        Vizinhos de 1 gene.
        raio_niveis=None : trocar a barra OU mudar o nível (vizinhança básica)
        raio_niveis=r    : trocar a barra E mudar o nível em até ±r (estendida)
        """
        for grupo, n_niveis in ((0, self.nl_ger), (1, self.nl_cap)):
            genes = ab[grupo]
            usadas = {b for b, _ in genes}
            for i, (barra, nivel) in enumerate(genes):
                if raio_niveis is None:
                    novos = [(nb, nivel) for nb in self.candidatas if nb != barra and nb not in usadas]
                    novos += [(barra, nn) for nn in range(1, n_niveis + 1) if nn != nivel]
                else:
                    faixa = range(max(1, nivel - raio_niveis), min(n_niveis, nivel + raio_niveis) + 1)
                    novos = [(nb, nn) for nb in self.candidatas
                             if nb != barra and nb not in usadas for nn in faixa if nn != nivel]
                for gene in novos:
                    lista = tuple(sorted(genes[:i] + (gene,) + genes[i + 1:]))
                    yield (lista, ab[1]) if grupo == 0 else (ab[0], lista)

    def tamanho_espaco(self):
        nb = len(self.candidatas)
        return (math.comb(nb, self.n_ger) * self.nl_ger ** self.n_ger
                * math.comb(nb, self.n_cap) * self.nl_cap ** self.n_cap)

    def descrever(self, ab):
        partes = []
        if ab[0]:
            partes.append("geradores: " + ", ".join(
                f"barra {b} ({n * P_PASSO_KW:g} kW)" for b, n in ab[0]))
        if ab[1]:
            partes.append("capacitores: " + ", ".join(
                f"barra {b} ({n * Q_PASSO_KVAR:g} kvar)" for b, n in ab[1]))
        return " | ".join(partes)


# ============================================================
# NÚCLEO DO CLONALG (uma execução)
# ============================================================

def _unicos(lista, N, prob):
    """Remove duplicatas e completa com anticorpos aleatórios até N."""
    vistos, saida = set(), []
    for ab in lista:
        if ab not in vistos:
            vistos.add(ab)
            saida.append(ab)
    tentativas = 0                       # evita laço infinito em espaços minúsculos
    while len(saida) < N and tentativas < 50 * N:
        tentativas += 1
        ab = prob.aleatorio()
        if ab not in vistos:
            vistos.add(ab)
            saida.append(ab)
    return saida[:N]


def _clonalg(prob, tam_pop, frac_sel, beta, rho, frac_renov, max_ger, max_estag,
             iniciais=()):
    """Retorna (melhor, gerações, motivo_parada)."""
    pop = _unicos(list(iniciais), tam_pop, prob)          # 1. população inicial
    melhor, custo_melhor, estag, geracoes = None, float("inf"), 0, 0
    motivo = "limite de gerações"

    for ger in range(1, max_ger + 1):
        geracoes = ger
        pop.sort(key=prob.custo)              # 2. afinidade (menor custo = maior)
        N = len(pop)

        if prob.custo(pop[0]) < custo_melhor - 1e-9:
            melhor, custo_melhor, estag = pop[0], prob.custo(pop[0]), 0
        else:
            estag += 1
        prob.ctl.geracao(ger, max_ger, estag, max_estag, custo_melhor, prob.avaliar(melhor))
        if estag >= max_estag:
            motivo = "estagnação"
            break

        nova_pop = list(pop)
        for rank in range(max(1, int(round(frac_sel * N)))):   # 3. seleção clonal
            pai = pop[rank]
            afin = 1.0 - rank / (N - 1) if N > 1 else 1.0
            alpha = math.exp(-rho * afin)                      # mutação inversa à afinidade
            n_clones = max(1, int(round(beta * N / (rank + 1))))  # 4. clonagem
            melhor_clone = min((prob.hipermutar(pai, alpha) for _ in range(n_clones)),
                               key=prob.custo)                 # 5/6. hipermutação
            if prob.custo(melhor_clone) < prob.custo(pai) and melhor_clone not in nova_pop:
                nova_pop[rank] = melhor_clone

        nova_pop.sort(key=prob.custo)         # 7. renovação da medula (elitista)
        for i in range(N - max(1, int(round(frac_renov * N))), N):
            nova_pop[i] = prob.aleatorio()
        pop = _unicos(nova_pop, N, prob)

    pop.sort(key=prob.custo)
    if prob.custo(pop[0]) < custo_melhor - 1e-9:
        melhor = pop[0]
    return melhor, geracoes, motivo


# ============================================================
# BUSCA LOCAL FINAL E VERIFICAÇÃO EXAUSTIVA
# ============================================================

def _reotimizar_niveis(prob, ab, max_ciclos=10):
    """
    Busca em linha nos níveis (potências) mantendo as barras fixas:
    passos de ±8, ±4, ±2, ±1 repetidos enquanto melhorarem o custo.
    """
    atual, c = ab, prob.custo(ab)
    for _ in range(max_ciclos):
        melhorou = False
        for g, nl in ((0, prob.nl_ger), (1, prob.nl_cap)):
            for i in range(len(atual[g])):
                for passo in (8, 4, 2, 1):
                    for sinal in (1, -1):
                        while True:
                            genes = atual[g]
                            barra, nivel = genes[i]
                            nn = nivel + sinal * passo
                            if not 1 <= nn <= nl:
                                break
                            lista = genes[:i] + ((barra, nn),) + genes[i + 1:]
                            cand = (lista, atual[1]) if g == 0 else (atual[0], lista)
                            cc = prob.custo(cand)
                            if cc < c - 1e-9:
                                atual, c, melhorou = cand, cc, True
                            else:
                                break
        if not melhorou:
            break
    return atual


def _aplicar_deltas(prob, ab, idxs, deltas):
    """Soma deltas aos níveis dos genes idxs (índice global: geradores e depois capacitores)."""
    genes = [list(ab[0]), list(ab[1])]
    for idx, d in zip(idxs, deltas):
        g, i = (0, idx) if idx < prob.n_ger else (1, idx - prob.n_ger)
        barra, nivel = genes[g][i]
        nn = nivel + d
        nl = prob.nl_ger if g == 0 else prob.nl_cap
        if not 1 <= nn <= nl:
            return None
        genes[g][i] = (barra, nn)
    return (tuple(sorted(genes[0])), tuple(sorted(genes[1])))


def _niveis_conjuntos(prob, ab):
    """
    Muda os níveis de 2 ou 3 genes AO MESMO TEMPO (±1, ±2 para pares; ±1 para
    trios). Necessário porque, perto do limite de tensão, mexer em um nível
    isolado piora o custo, mas mexer em vários juntos melhora.
    """
    atual, c = ab, prob.custo(ab)
    total = prob.n_ger + prob.n_cap
    melhorou = True
    while melhorou:
        melhorou = False
        for r, deltas_ok in ((2, (-2, -1, 1, 2)), (3, (-1, 1))):
            if r > total:
                continue
            for idxs in combinations(range(total), r):
                for deltas in product(deltas_ok, repeat=r):
                    cand = _aplicar_deltas(prob, atual, idxs, deltas)
                    if cand is not None and prob.custo(cand) < c - 1e-9:
                        atual, c, melhorou = cand, prob.custo(cand), True
                        break
                if melhorou:
                    break
            if melhorou:
                break
    return atual


def _construtivo(prob, base=((), ())):
    """
    Heurística gulosa: acrescenta os genes que faltam, um a um, na barra
    (com reotimização dos níveis) que resultar no menor custo.
    """
    ab = base
    for g in (0, 1):
        n_alvo = prob.n_ger if g == 0 else prob.n_cap
        while len(ab[g]) < n_alvo:
            usadas = {b for b, _ in ab[g]}
            melhor, c_melhor = None, float("inf")
            for nb in prob.candidatas:
                if nb in usadas:
                    continue
                lista = tuple(sorted(ab[g] + ((nb, 1),)))
                cand = (lista, ab[1]) if g == 0 else (ab[0], lista)
                # estágios incompletos do outro grupo ainda não têm todos os genes:
                # avalia assim mesmo (o custo reflete só o que já foi instalado)
                cand = _reotimizar_niveis(prob, cand, max_ciclos=3)
                cc = prob.custo(cand)
                if cc < c_melhor:
                    melhor, c_melhor = cand, cc
            ab = melhor
    return ab


def _prefixo(prob, anterior):
    """Aproveita os genes do estágio anterior (limitados ao tamanho atual)."""
    return (tuple(sorted(anterior[0]))[:prob.n_ger], tuple(sorted(anterior[1]))[:prob.n_cap])


def _passo_barra_reotimizado(prob, atual, custo_atual):
    """
    Vizinhança 3: troca a barra de UM gene e reotimiza todos os níveis.
    Escapa de ótimos locais em que várias coisas precisam mudar juntas
    (ex.: mover um gerador e reajustar a potência dos demais).
    """
    for g in (0, 1):
        genes = atual[g]
        usadas = {b for b, _ in genes}
        for i, (barra, nivel) in enumerate(genes):
            for nb in prob.candidatas:
                if nb == barra or nb in usadas:
                    continue
                lista = tuple(sorted(genes[:i] + ((nb, nivel),) + genes[i + 1:]))
                cand = (lista, atual[1]) if g == 0 else (atual[0], lista)
                cand = _reotimizar_niveis(prob, cand)
                if prob.custo(cand) < 1.05 * custo_atual:      # só refina candidatos promissores
                    cand = _reotimizar_niveis(prob, _niveis_conjuntos(prob, cand))
                if prob.custo(cand) < custo_atual - 1e-9:
                    return cand
    return None


def _busca_local(prob, atual):
    """
    Descida em vizinhanças crescentes (VND): 1) barra OU nível; 2) barra E
    nível; 3) troca de barra + reotimização dos níveis. Só para quando
    nenhuma encontra melhora (inclui mudança conjunta de níveis).
    """
    custo_atual = prob.custo(atual)
    melhorou = True
    while melhorou:
        melhorou = False
        for raio in (None, RAIO_NIVEIS):
            for viz in prob.vizinhos(atual, raio):
                c = prob.custo(viz)
                if c < custo_atual - 1e-9:
                    atual, custo_atual, melhorou = viz, c, True
                    break
            if melhorou:
                break
        if not melhorou:
            viz = _niveis_conjuntos(prob, atual)
            if prob.custo(viz) < custo_atual - 1e-9:
                atual, custo_atual, melhorou = viz, prob.custo(viz), True
                continue
            viz = _passo_barra_reotimizado(prob, atual, custo_atual)
            if viz is not None:
                atual, custo_atual, melhorou = viz, prob.custo(viz), True
    return atual


def _combinacoes(candidatas, n, n_niveis):
    for barras in combinations(candidatas, n):
        for niveis in product(range(1, n_niveis + 1), repeat=n):
            yield tuple(sorted(zip(barras, niveis)))


def _busca_exaustiva(prob):
    todos = ((g, c) for g in _combinacoes(prob.candidatas, prob.n_ger, prob.nl_ger)
             for c in _combinacoes(prob.candidatas, prob.n_cap, prob.nl_cap))
    melhor, c_melhor = None, float("inf")
    total = prob.tamanho_espaco()
    for i, ab in enumerate(todos, 1):    # sem cache: não guarda 200 mil dicionários
        if i % 500 == 0:
            prob.ctl.exaustiva(i, total)
        c = prob.avaliar(ab, usar_cache=False)["custo"]
        if c < c_melhor:
            melhor, c_melhor = ab, c
    return melhor, c_melhor


# ============================================================
# OTIMIZAÇÃO DE UM ESTÁGIO (n_ger geradores + n_cap capacitores)
# ============================================================

def _otimizar_estagio(dados, Ni, Nj, ids, n_ger, n_cap, P_max_kW, Q_max_kvar,
                      custos, S_base_kVA, tol, tam_pop, frac_sel, beta, rho,
                      frac_renov, max_ger, max_estag, n_execucoes, semente,
                      anterior, p, limite_exaustivo=LIMITE_EXAUSTIVO, ctl=None):
    prob = _Problema(dados, Ni, Nj, ids, n_ger, P_max_kW, n_cap, Q_max_kvar,
                     S_base_kVA, tol, custos, random.Random(semente))
    if ctl is not None:
        prob.ctl = ctl
    tam = prob.tamanho_espaco()
    p(f"  Espaço de busca: {tam:,}".replace(",", "."))

    # --- 1) Espaço pequeno: busca exaustiva ANTES de tudo (ótimo global
    #        comprovado); o CLONALG nem precisa rodar.
    if tam <= limite_exaustivo:
        p(f"  Busca exaustiva ({tam} combinações)...")
        melhor_ab, melhor_c = _busca_exaustiva(prob)
        info = prob.avaliar(melhor_ab)
        prob.cache.clear()                       # libera memória do estágio
        return {
            "prob": prob, "ab": melhor_ab, "custo": melhor_c, "info": info,
            "exaustivo": True, "confirmacoes": 0, "n_execucoes_total": 0,
            "n_limite_geracoes": 0, "custos_execs": [],
        }

    # --- 2) Espaço grande: CLONALG + busca local + confirmação independente
    execs = []                                    # (custo, anticorpo)
    n_limite = 0

    def rodar(rotulo, i, n, iniciais=()):
        nonlocal n_limite
        prob.ctl.execucao(rotulo, i, n)
        melhor, geracoes, motivo = _clonalg(prob, tam_pop, frac_sel, beta, rho,
                                            frac_renov, max_ger, max_estag, iniciais)
        melhor = _busca_local(prob, melhor)
        c = prob.custo(melhor)
        if motivo == "limite de gerações":
            n_limite += 1
        execs.append((c, melhor))
        p(f"  {rotulo}: custo = {_brl(c):>20} | {geracoes:>3} gerações ({motivo})")

    # A 1ª execução é SEMEADA (gulosa + estágio anterior); as demais partem de
    # populações aleatórias e são as realmente independentes.
    for k in range(1, n_execucoes + 1):
        ini = ()
        if k == 1:
            ini = [_construtivo(prob, ((), ()))]
            if anterior:
                ini.append(_construtivo(prob, _prefixo(prob, anterior)))
                ini += [prob.estender(anterior) for _ in range(3)]
        rodar(f"exec {k}/{n_execucoes}", k, n_execucoes, ini)

    melhor_c, melhor_ab = min(execs, key=lambda e: e[0])

    # Execuções extras até o melhor custo ser reencontrado de forma independente
    def confirmacoes():
        return sum(1 for c, _ in execs if _mesmo_custo(c, melhor_c))
    extras = 0
    while confirmacoes() < MIN_CONFIRMACOES and extras < MAX_EXTRAS:
        extras += 1
        rodar(f"exec extra {extras}/{MAX_EXTRAS}", n_execucoes + extras, n_execucoes + extras)
        c_novo, ab_novo = execs[-1]
        if c_novo < melhor_c and not _mesmo_custo(c_novo, melhor_c):
            melhor_ab, melhor_c = ab_novo, c_novo

    confirm = confirmacoes()
    info = prob.avaliar(melhor_ab)
    prob.cache.clear()                           # libera memória do estágio
    return {
        "prob": prob, "ab": melhor_ab, "custo": melhor_c, "info": info,
        "exaustivo": False, "confirmacoes": confirm, "n_execucoes_total": len(execs),
        "n_limite_geracoes": n_limite,
        "custos_execs": [c for c, _ in execs],
    }


# ============================================================
# FUNÇÃO PRINCIPAL
# ============================================================

def imunidade(
    dados, Ni_ordenado, Nj_ordenado, id_ordenado,
    n_ger=1, P_max_kW=1500.0,
    n_cap=1, Q_max_kvar=1200.0,
    custo_ger_kW=3500.0,      # R$ por kW de gerador instalado
    custo_cap_kvar=60.0,      # R$ por kvar de capacitor instalado
    custo_perda_kW=20000.0,   # R$ por kW de perda (valor presente ao longo do horizonte)
    S_base_kVA=10000.0, tol=1e-6,
    tam_pop=30, frac_sel=0.5, beta=1.0, rho=3.0, frac_renov=0.2,
    max_ger=200, max_estag=40, n_execucoes=5, semente=42,
    mostrar_fluxo_final=False, verbose=True,
    limite_exaustivo=LIMITE_EXAUSTIVO, ctl=None,   # 0 força o CLONALG em qualquer espaço (p/ validação)
):
    """Executa o CLONALG (geradores + capacitores) minimizando o custo total."""

    t0 = time.time()
    custos = {"ger_kW": custo_ger_kW, "cap_kvar": custo_cap_kvar, "perda_kW": custo_perda_kW}
    p = print if verbose else (lambda *a, **k: None)

    base = fluxo_de_potencia(dados, Ni_ordenado, Nj_ordenado, id_ordenado,
                             S_base_kVA=S_base_kVA, tol=tol)
    v_base = [abs(v) for v in base["V"].values()]
    custo_base = base["perdas_kW"] * custo_perda_kW

    p("\n" + "=" * 60 + "\nIMUNIDADE BIOLÓGICA (CLONALG) - GERADORES + CAPACITORES\n" + "=" * 60)
    p(f"Geradores                : {n_ger}"
      + (f"  (passo {P_PASSO_KW:g} kW, máx. {P_max_kW:g} kW, fp = {FATOR_POTENCIA}; "
         f"{_brl(custo_ger_kW)}/kW)" if n_ger else ""))
    p(f"Bancos de capacitores    : {n_cap}"
      + (f"  (passo {Q_PASSO_KVAR:g} kvar, máx. {Q_max_kvar:g} kvar; "
         f"{_brl(custo_cap_kvar)}/kvar)" if n_cap else ""))
    p(f"Custo das perdas         : {_brl(custo_perda_kW)}/kW")
    p(f"Limites de tensão        : {V_MIN_PU} a {V_MAX_PU} pu")
    p(f"População / geração máx. : {tam_pop} / {max_ger}  (parada após {max_estag} sem melhora)")
    p(f"Execuções independentes  : {n_execucoes}  (semente = {semente})")
    p(f"\nCASO BASE: perdas = {base['perdas_kW']:.3f} kW + j{base['perdas_kvar']:.3f} kvar | "
      f"Vmin = {min(v_base):.5f} pu | custo das perdas = {_brl(custo_base)}\n" + "-" * 60)

    # --------------------------------------------------------
    # Estágios: 1, 2, ..., K equipamentos (K = máx(n_ger, n_cap))
    # --------------------------------------------------------
    K = max(n_ger, n_cap)
    estagios, perdas_ant, anterior = [], base["perdas_kW"], None
    ponto_parada = None                      # k-1 do primeiro estágio com ganho < limiar

    for k in range(1, K + 1):
        ng, nc = min(k, n_ger), min(k, n_cap)
        p(f"ESTÁGIO {k}/{K}: {ng} gerador(es) + {nc} capacitor(es)")
        if ctl is not None:
            ctl.estagio(k, K, ng, nc)
        r = _otimizar_estagio(dados, Ni_ordenado, Nj_ordenado, id_ordenado, ng, nc,
                              P_max_kW, Q_max_kvar, custos, S_base_kVA, tol, tam_pop,
                              frac_sel, beta, rho, frac_renov, max_ger, max_estag,
                              n_execucoes, semente + 1000 * k, anterior, p,
                              limite_exaustivo, ctl)
        perdas_k = r["info"]["perdas_kW"]
        ganho = (perdas_ant - perdas_k) / perdas_ant if perdas_ant > 0 else 0.0
        r.update({"k": k, "n_ger": ng, "n_cap": nc, "ganho": ganho})
        estagios.append(r)
        if ganho < LIMIAR_GANHO_PERDAS and ponto_parada is None:
            ponto_parada = k - 1
        p(f"  -> perdas = {perdas_k:.3f} kW | ganho sobre o estágio anterior = "
          f"{100 * ganho:.2f} % | custo = {_brl(r['custo'])}\n")
        perdas_ant, anterior = perdas_k, r["ab"]

    final = estagios[-1]
    prob, melhor_global, custo_global = final["prob"], final["ab"], final["custo"]
    info = final["info"]

    # --------------------------------------------------------
    # Resultado final (estágio com todos os equipamentos pedidos)
    # --------------------------------------------------------
    injecoes, P_total, Q_total = prob.injecoes_de(melhor_global)
    res = fluxo_de_potencia(dados, Ni_ordenado, Nj_ordenado, id_ordenado,
                            S_base_kVA=S_base_kVA, tol=tol, injecoes=injecoes,
                            capacitores=prob.capacitores_de(melhor_global))
    reducao = (100.0 * (base["perdas_kW"] - res["perdas_kW"]) / base["perdas_kW"]
               if base["perdas_kW"] > 0 else 0.0)
    barra_vmin = min(res["V"], key=lambda b: abs(res["V"][b]))
    geradores = {b: complex(n * P_PASSO_KW, n * P_PASSO_KW * prob.tan_phi)
                 for b, n in melhor_global[0]}
    capacitores = {b: n * Q_PASSO_KVAR for b, n in melhor_global[1]}
    c_ger, c_cap, c_perd = info["custo_ger"], info["custo_cap"], info["custo_perdas"]
    custo_total = info["custo_total"]
    economia = custo_base - custo_total

    p("=" * 60 + "\nRESULTADO FINAL - IMUNIDADE BIOLÓGICA\n" + "=" * 60)
    if geradores:
        p("GERADORES\n" + f"{'barra':>6} {'P (kW)':>10} {'Q (kvar)':>10} {'custo':>20}")
        for b, s in sorted(geradores.items()):
            p(f"{b:>6} {s.real:>10.2f} {s.imag:>10.2f} {_brl(s.real * custo_ger_kW):>20}")
    if capacitores:
        p("\nBANCOS DE CAPACITORES (admitância shunt: Q efetivo = Q nominal x |V|²)\n"
          + f"{'barra':>6} {'Q nom.':>10} {'|V| (pu)':>9} {'Q efet.':>10} {'passos':>7} {'custo':>20}")
        for b, q in sorted(capacitores.items()):
            vb = abs(res["V"][b])
            p(f"{b:>6} {q:>10.2f} {vb:>9.4f} {q * vb ** 2:>10.2f} "
              f"{int(round(q / Q_PASSO_KVAR)):>7} {_brl(q * custo_cap_kvar):>20}")

    p(f"\nInjeção total: P = {P_total:.2f} kW | Q (nominal) = {Q_total:.2f} kvar "
      f"(carga total: {prob.P_carga_total:.2f} kW | {prob.Q_carga_total:.2f} kvar)")
    p(f"\nPerdas caso base  : {base['perdas_kW']:.3f} kW")
    p(f"Perdas otimizadas : {res['perdas_kW']:.3f} kW (redução de {reducao:.2f} %)")
    p(f"Tensão mínima     : {abs(res['V'][barra_vmin]):.5f} pu (barra {barra_vmin})"
      f"   [base: {min(v_base):.5f} pu]")
    p(f"Tensão máxima     : {info['v_max']:.5f} pu")
    p(f"Potência da SE principal: {res['S_SE_kW']:.3f} kW + j{res['S_SE_kvar']:.3f} kvar")

    p("\nCUSTOS")
    p(f"  Geradores            : {_brl(c_ger):>20}")
    p(f"  Bancos de capacitores: {_brl(c_cap):>20}")
    p(f"  Perdas ativas        : {_brl(c_perd):>20}")
    p(f"  CUSTO TOTAL          : {_brl(custo_total):>20}")
    p(f"  Custo total caso base: {_brl(custo_base):>20}  (apenas perdas)")
    p(f"  Economia líquida     : {_brl(economia):>20}")

    if prob.viavel(melhor_global):
        p("\nRestrições: ATENDIDAS")
    else:
        p(f"\nRestrições: VIOLADAS (tensão = {info['violacao']:.5f} pu, "
          f"excesso P = {info['excesso_P']:.2f} kW, excesso Q = {info['excesso_Q']:.2f} kvar)\n"
          "  -> aumente P_max/Q_max ou o nº de equipamentos.")

    # --------------------------------------------------------
    # Análise de ganho marginal (ponto de parada)
    # --------------------------------------------------------
    if K >= 1:
        p("\n" + "-" * 60 + "\nGANHO MARGINAL NAS PERDAS POR ESTÁGIO\n" + "-" * 60)
        p(f"{'estágio':>8} {'ger':>4} {'cap':>4} {'perdas (kW)':>12} {'ganho (%)':>10} {'custo total':>22}")
        p(f"{0:>8} {0:>4} {0:>4} {base['perdas_kW']:>12.3f} {'-':>10} {_brl(custo_base):>22}")
        for e in estagios:
            p(f"{e['k']:>8} {e['n_ger']:>4} {e['n_cap']:>4} {e['info']['perdas_kW']:>12.3f} "
              f"{100 * e['ganho']:>10.2f} {_brl(e['info']['custo_total']):>22}")

        if ponto_parada is None:
            p(f"\nTodos os estágios reduziram as perdas em >= {100 * LIMIAR_GANHO_PERDAS:g} %: "
              "todos os equipamentos informados se justificam.")
        elif ponto_parada == 0:
            p(f"\nJá o 1º equipamento reduziu as perdas em menos de {100 * LIMIAR_GANHO_PERDAS:g} %: "
              "do ponto de vista de perdas, a instalação não compensa.")
        else:
            e = estagios[ponto_parada - 1]
            p(f"\nPODERIA TER PARADO COM {e['n_ger']} GERADOR(ES) E {e['n_cap']} CAPACITOR(ES) "
              f"(estágio {ponto_parada}): o estágio seguinte reduziu as perdas em menos de "
              f"{100 * LIMIAR_GANHO_PERDAS:g} %.")
            p(f"  Posições ótimas desse estágio -> {e['prob'].descrever(e['ab'])}")
            p(f"  Perdas: {e['info']['perdas_kW']:.3f} kW | custo total: {_brl(e['info']['custo_total'])}")

    # Critério por CUSTO (coerente com a função objetivo): compara o custo
    # (com penalidades) entre estágios consecutivos e aponta o de menor custo.
    k_min = min(estagios, key=lambda e: e["custo"])["k"]
    parada_custo = next((e["k"] - 1 for e in estagios[1:]
                         if e["custo"] >= estagios[e["k"] - 2]["custo"]), None)
    p("\n  Critério por custo total (função objetivo):")
    for e in estagios:
        p(f"    estágio {e['k']}: {_brl(e['custo']):>20}"
          + ("   <- menor custo" if e["k"] == k_min else ""))
    if parada_custo is None:
        p("    Cada equipamento adicional reduziu o custo total.")
    else:
        p(f"    O estágio {parada_custo + 1} não reduziu o custo em relação ao estágio "
          f"{parada_custo}: do ponto de vista econômico, {parada_custo} já bastava.")

    # --------------------------------------------------------
    # Diagnóstico de convergência
    # --------------------------------------------------------
    p("\n" + "-" * 60 + "\nDIAGNÓSTICO DE CONVERGÊNCIA\n" + "-" * 60)
    todos_ok = True
    for e in estagios:
        if e["exaustivo"]:
            status = "ÓTIMO GLOBAL comprovado (busca exaustiva)"
        else:
            ok = e["confirmacoes"] >= MIN_CONFIRMACOES
            todos_ok &= ok
            status = (f"melhor custo reencontrado em {e['confirmacoes']} de "
                      f"{e['n_execucoes_total']} execuções"
                      + ("" if ok else "  [NÃO CONFIRMADO: aumente população/gerações/execuções]"))
        aviso = (f" | {e['n_limite_geracoes']} exec. pararam por limite de gerações"
                 if e["n_limite_geracoes"] else "")
        p(f"  Estágio {e['k']}: {status}{aviso}")
    if any(e["n_limite_geracoes"] for e in estagios):
        p("  ATENÇÃO: houve execução que não estagnou; aumente o nº máximo de gerações.")
    if not all(e["exaustivo"] for e in estagios):
        p("  Obs.: onde não houve busca exaustiva, a otimalidade global não é matematicamente\n"
          "  garantida; a confiança vem da repetição independente + busca local estendida.")

    p(f"\nFluxos de potência calculados : {sum(e['prob'].n_fluxos for e in estagios)}")
    p(f"Avaliações evitadas pelo cache: {sum(e['prob'].n_hits for e in estagios)}")
    p(f"Tempo total                   : {time.time() - t0:.2f} s")

    if mostrar_fluxo_final:
        imprimir_resultados(res)

    parada = None
    if ponto_parada:
        e = estagios[ponto_parada - 1]
        parada = {"estagio": ponto_parada, "n_ger": e["n_ger"], "n_cap": e["n_cap"],
                  "anticorpo": e["ab"], "perdas_kW": e["info"]["perdas_kW"]}

    return {
        "geradores": geradores, "capacitores": capacitores, "injecoes": injecoes,
        "anticorpo": melhor_global, "custo": custo_global,
        "custo_geradores": c_ger, "custo_capacitores": c_cap,
        "custo_perdas": c_perd, "custo_total": custo_total,
        "custo_total_base": custo_base, "economia": economia,
        "perdas_base_kW": base["perdas_kW"], "perdas_kW": res["perdas_kW"],
        "reducao_pct": reducao, "v_min": info["v_min"],
        "viavel": prob.viavel(melhor_global), "fluxo": res,
        "otimo_global_comprovado": all(e["exaustivo"] for e in estagios),
        "n_fluxos": sum(e["prob"].n_fluxos for e in estagios),
        "estagios": [{k: v for k, v in e.items() if k != "prob"} for e in estagios],
        "parada_recomendada": parada,
        "estagio_menor_custo": k_min,
        "parada_por_custo": parada_custo,
        "capacitores_efetivos_kvar": {b: q * abs(res["V"][b]) ** 2
                                      for b, q in capacitores.items()},
    }


# ============================================================
# ENTRADA DE DADOS PELO USUÁRIO
# ============================================================

def _ler(prompt, padrao, tipo):
    while True:
        txt = input(f"{prompt} [{padrao}]: ").strip().replace(",", ".")
        if txt == "":
            return padrao
        try:
            return tipo(txt)
        except ValueError:
            print("  Valor inválido, tente novamente.")


def pedir_dados_usuario_imunidade():
    print("\n--- Parâmetros do CLONALG (Enter = valor padrão) ---")
    p = {"n_ger": _ler("Número de novos geradores (0 = nenhum)", 1, int)}
    if p["n_ger"] > 0:
        p["P_max_kW"] = _ler("Potência ativa máxima por gerador (kW)", 1500.0, float)
        p["custo_ger_kW"] = _ler("Custo do gerador (R$/kW)", 3500.0, float)

    p["n_cap"] = _ler("Número de bancos de capacitores (0 = nenhum)", 1, int)
    if p["n_cap"] > 0:
        p["Q_max_kvar"] = _ler("Potência reativa máxima por banco (kvar)", 1200.0, float)
        p["custo_cap_kvar"] = _ler("Custo do capacitor (R$/kvar)", 60.0, float)

    p["custo_perda_kW"] = _ler("Custo das perdas (R$/kW, valor presente)", 20000.0, float)
    p["tam_pop"] = _ler("Tamanho da população", 30, int)
    p["max_ger"] = _ler("Número máximo de gerações", 200, int)
    p["n_execucoes"] = _ler("Número de execuções independentes", 5, int)
    p["semente"] = _ler("Semente aleatória", 42, int)
    resp = input("Mostrar o fluxo de potência completo da solução final? (s/n) [n]: ")
    p["mostrar_fluxo_final"] = resp.strip().lower() == "s"
    return p