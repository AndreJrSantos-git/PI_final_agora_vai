import os
import sys

from ler_dados import ler_arquivo, imprimir_dados
from ordena import ordenar_linhas, imprimir_linhas_ordenadas
from fluxo_de_potencia import fluxo_de_potencia, imprimir_resultados
from imunidade import imunidade, pedir_dados_usuario_imunidade


# Parâmetros do fluxo de potência: usados no caso base do main E na otimização,
# para que as perdas do caso base impressas sejam idênticas nos dois relatórios.
S_BASE_KVA = 10000.0   # base de potência (kVA)
TOL_FLUXO = 1e-6       # critério de convergência (pu)


# ============================================================
# PROGRAMA PRINCIPAL
# ============================================================

if __name__ == "__main__":

    # --------------------------------------------------------
    # 1. Definir o caminho do arquivo
    # --------------------------------------------------------

    if len(sys.argv) > 1:

        caminho_arquivo = sys.argv[1]

    else:

        # Procura o arquivo na mesma pasta do main.py
        pasta = os.path.dirname(os.path.abspath(__file__))
        caminho_arquivo = os.path.join(pasta, "069BusSystem.txt")

    # --------------------------------------------------------
    # 2. Ler o arquivo
    # --------------------------------------------------------

    dados = ler_arquivo(caminho_arquivo)

    # --------------------------------------------------------
    # 3. Imprimir os dados originais
    # --------------------------------------------------------

    imprimir_dados(dados)

    # --------------------------------------------------------
    # 4. Ordenar as linhas
    # --------------------------------------------------------

    Ni_ordenado, Nj_ordenado, id_ordenado = ordenar_linhas(dados)

    # --------------------------------------------------------
    # 5. Imprimir as linhas ordenadas
    # --------------------------------------------------------

    imprimir_linhas_ordenadas(
        Ni_ordenado,
        Nj_ordenado,
        id_ordenado
    )

    # --------------------------------------------------------
    # 6. Fluxo de potência (backward / forward)
    # --------------------------------------------------------

    resultado = fluxo_de_potencia(
        dados,
        Ni_ordenado,
        Nj_ordenado,
        id_ordenado,
        S_base_kVA=S_BASE_KVA,
        tol=TOL_FLUXO
    )

    # --------------------------------------------------------
    # 7. Imprimir os resultados do fluxo de potência
    # --------------------------------------------------------

    imprimir_resultados(resultado)

    # --------------------------------------------------------
    # 8. Imunidade biológica (CLONALG) - alocação de geradores e capacitores
    # --------------------------------------------------------

    resp = input("\nDeseja executar o algoritmo de Imunidade Biológica (CLONALG)? (s/n): ").strip().lower()

    if resp == "s":

        parametros = pedir_dados_usuario_imunidade()
        parametros["S_base_kVA"] = S_BASE_KVA
        parametros["tol"] = TOL_FLUXO

        resultado_imune = imunidade(
            dados,
            Ni_ordenado,
            Nj_ordenado,
            id_ordenado,
            **parametros
        )

        # A própria função imunidade() já imprime o relatório completo.