#coding: utf-8
from itertools import permutations
from itertools import combinations
import numpy.random as rd
from math import sqrt
from scipy.stats import norm
from gurobipy import *

##@file nps2p.py
#@brief Algoritmo NPS-2p para encontrar um equilíbrio em jogos de dois jogadores.
#
#@details 
# Reproduz o Algoritmo 1 de Porter et al (2008) para encontrar ao menos um equilíbrio de Nash para jogos com dois jogadores.
#
#@b Referência: Porter, R.; Nudelman, E.; Shoham, Y. Simple search methods for finding a Nash equilibrium. @a Games @a and @a Economic @a Behavior, 63, 642-662, 2008. 
#@date 07/07/2018
#@author Thiago Augusto de Oliveira Silva e Matheus Correia Teixeira
#

##@b VerificaDominacaoCondicional
#@brief Verifica a existência de ações condicionalmente dominadas para um jogador dado um suporte do oponente de acordo com a Definição 2 
#de Porter et al (2008).
# 
#@details
# Definição 2 (Porter et al (2008)) - Uma ação @f$ a_i \in S @f$ é dita condicionalmente dominada dado um conjunto de ações @f$ A^{'}_{-i} @f$
# se a seguinte condição é satisfeita:
# @f$ \exists a^{'}_i \in S, \forall a_{-i} \in A^{'}_{-i}: u_i(a_i,a_{-i}) <u_i(a^{'}_i,a_{-i}) @f$
#@param S Suporte do jogador no formato de lista
#@param Alinha Suporte do oponente no formato de lista
#@param payoff matriz de payoff indexada como payoff[id_açao_jogador1][id_acao_jogador2][id_jogador]
#@param idj variavel boleana que recebe zero quando as acoes do jogador 1 e 1 quando as acoes do jogador 2
#@retval TRUE se não existem ações dominas em S dado Alinha
#@retval FALSE se existe pelo menos uma ação dominas em S dado Alinha

def VerificaDominacaoCondicional(S,Alinha,payoff,idj):
	# S o suporte do  
	# Alinha e a lista de acoes do oponente
	# payoff 
	# idj e uma 
	resp = False
	if (len(S)==1):
		resp = False
	else:
		for a1 in range(len(list(S))):
			for a2 in range(len(list(S))):
				if (a1!=a2):
					resp = VerificaDominacao(a1,a2,Alinha,payoff,idj)
					if resp:
						break
	return resp

##@b VerificaDominacao
#@brief Verifica se uma ação é condicionalmente dominada pela outra dado um conjunto de ações do oponente
# 
#@details
# A ação @f$ a_1 \in S @f$ é dita condicionalmente dominada pela ação @f$ a_1 \in S @f$ dado um conjunto de ações @f$ A^{'}_{-i} @f$
# se a seguinte condição é satisfeita:
# @f$ \forall a_{-i} \in A^{'}_{-i}: u_i(a_1,a_{-i}) <u_i(a_2,a_{-i}) @f$
#@param a1 id da ação 1 para o jogador idj
#@param a2 id da ação 2 para o jogador idj
#@param payoff matriz de payoff indexada como payoff[id_açao_jogador1][id_acao_jogador2][id_jogador]
#@param idj variavel boleana que recebe zero quando as acoes do jogador 1 e 1 quando as acoes do jogador 2
#@retval TRUE se @f$ a_1 @f$ é condicionalmente dominada por @f$ a_1 @f$ dado @f$ A^{'}_{-i} @f$
#@retval FALSE caso contrário
def VerificaDominacao(a1,a2,listaA,payoff,idj):
	resp = True # inicialmente assume se que nao ha dominacao
	if (1-idj):
		for x in listaA:
			util1 = payoff[a1][x][0]
			util2 = payoff[a2][x][0]
			if(util1 >= util2):
				resp = False
				break
	else:
		for x in listaA:
			util1 = payoff[x][a1][1]
			util2 = payoff[x][a2][1]
			if(util1 >= util2):
				resp = False
				break
	return resp
##@b RetiraDominadosCondicionalmente
#@brief Retira de uma lista de ações as ações que são dominadas condicionalmente dado o conjunto de ações do oponente
# 
#@details
# A função testa a dependencia condicional de cada uma das ações do conjunto de ações A2 dado S1 e retira da lista quando encontra uma dominada
#
#@param A2 lista de ações a serem testadas
#@param S1 lista de ações do oponente
#@param payoff matriz de payoff indexada como payoff[id_açao_jogador1][id_acao_jogador2][id_jogador]
#@retval A2linha lista de ações contidas em A2 não dominadas dado S1

def RetiraDominadosCondicionalmente(A2,S1,payoff):
	A2linha = A2
	idj = 1

	for a1 in range(len(A2)):
		for a2 in range(len(A2)):
			if (a1!=a2):
				if(VerificaDominacao(a1,a2,S1,payoff,idj)):
					A2linha = [a for a in A2linha if a!=a1] # Retira a1 da lista 
					break
	return A2linha
##@b VerificaViabilidade
#@brief Resolve o @a Constraint @a Satisfaction @a Problem (CSP) de Porter et al (2008) para encontrar um equilíbrio dado os suportes de ações
# 
#@details
# Resolve, via Gurobi, o CSP denominado Feasibility Program 1 em Porter et al (2008), definido como:@n
#@f$ \forall i \in N,\forall a_i \in S_i: \sum_{a_{-i} \in S_{-i}}p(a_{-i})u_i(a_i,a_{-i})  = v_i @f$ @n
#@f$ \forall i \in N,\forall a_i \not \in S_i: \sum_{a_{-i} \in S_{-i}}p(a_{-i})u_i(a_i,a_{-i})  \leq v_i @f$ @n
#@f$ \forall i \in N: \sum_{a_{i} \in S_{i}}p_i(a_{i}) = 1 @f$ @n
#@f$ \forall i \in N, \forall a_i \in S_i: p_i(a_{i}) \geq 0 @f$ @n
#@param N lista de jogadores
#@param A1 lista de ações do jogador 1
#@param A2 lista de ações do jogador 2
#@param S1 lista de ações do jogador 1
#@param S2 lista de ações do jogador 2
#@param payoff matriz de payoff indexada como payoff[id_açao_jogador1][id_acao_jogador2][id_jogador]
#@retval lista contendo as seguintes informações [1, [S1], [p1],[S2], [p2]] se o CSP for viável
#@retval lista contendo as seguintes informações [0] se o CSP for inviável
def VerificaViabilidade(N,A1,A2,S1,S2,payoff):
	m = Model("Feasibility")	
	S = [S1,S2]
	A = [A1,A2]
	p=[]
	v=[]
	for i in range(len(N)):
		pi = [] 
		v.append(m.addVar(vtype = GRB.CONTINUOUS, name = "v[{}]".format(i)))
		for ida in range(len(S[i])):
			pi.append(m.addVar(lb=0.0,vtype = GRB.CONTINUOUS, name = 'p[{},{}]'.format(i,ida)))
		p.append(pi)
	m.update()

	for i in range(len(N)):
		for ids in S[i]:
			ida = A[i].index(ids)
			if (1-i == 1):
				m.addConstr(quicksum(p[1-i][S[1-i].index(idb)]*payoff[ida][A[1-i].index(idb)][0] for idb in S[1-i]) == v[i])
			else:
				m.addConstr(quicksum(p[1-i][S[1-i].index(idb)]*payoff[A[1-i].index(idb)][ida][1] for idb in S[1-i]) == v[i])  


	for i in range(len(N)):
		notS = [a for a in A[i] if a not in S[i]]
		for ids in notS:
			ida = A[i].index(ids) 
			if (1-i == 1):  
				m.addConstr(quicksum(p[1-i][S[1-i].index(idb)]*payoff[ida][A[1-i].index(idb)][0] for idb in S[1-i]) <= v[i])
			else:
				m.addConstr(quicksum(p[1-i][S[1-i].index(idb)]*payoff[A[1-i].index(idb)][ida][1] for idb in S[1-i]) <= v[i])  

	for i in N:
		m.addConstr(quicksum(p[i][ida] for ida in range(len(S[i]))) == 1)
	m.update()
	m.setParam('OutputFlag',0)
	m.optimize()
	st = m.getAttr('Status')
    
	if (st == 2):
		resp = [1]
		for i in range(len(N)):
			resp.append(S[i])
			respP = []
			for ida in range(len(S[i])):
				respP.append(p[i][ida].x)
			resp.append(respP)
	else:
		resp = [0]
	return resp
##@b Algoritmo1
#@brief Algoritmo1 proposto por  Porter et al (2008) para encontrar um equilíbrio um jogo de dois jogadores
# 
#@details
# Procura equilíbrio de Nash em um jogo de dois jogadores fazendo uma busca a partir de suporte contidos no conjunto de Ações de cada jogador.
# Inicialmente gera perfis de suporte (tamanho) os combina de forma a selecionar os menores suporte primeiro
# Para cada suporte, verifica e retira ações condicionalmente dominadas e resolve o CSP buscando um equilíbrio de Nash.
#@param A1 lista de ações do jogador 1
#@param A2 lista de ações do jogador 2
#@param payoff matriz de payoff indexada como payoff[id_açao_jogador1][id_acao_jogador2][id_jogador]
#@retval o equilíbrio através de uma lista contendo as seguintes informações [[S1], [p1],[S2], [p2]]
def Algoritmo1(A1,A2,payoff):
	N = [0,1]
	X1 = range(1,len(A1)+1) # Criar uma lista com todos os tamanhos de suporte possiveis para o jogador 1
	X2 = range(1,len(A2)+1) # Criar uma lista com todos os tamanhos de suporte possiveis para o jogador 2

	tX = [(x1,x2) for x1 in X1 for x2 in X2] # Cria uma lista de par ordenado com todas as combinacoes possiveis para os tamanhos de suporte do jogafor 1 e de jogador 2
	X = [(x[0],x[1],abs(x[0]-x[1]),x[0]+x[1]) for x in tX]
	X = sorted(X, key =lambda  x: (x[2],x[3])) # Ordena X pela primeirordem desejada
	for idx,x in enumerate(X):
		S1 = combinations(A1,x[0]) # Todos os suportes possiveis de tamanho x[0] para o jogador 1
		for s1 in S1:
			sup1 = list(s1)
			Alinha2 = RetiraDominadosCondicionalmente(A2,sup1,payoff) # retira de A2 todas as acoes que sao dominadas condicionalmente em realacao a S1
			if(not VerificaDominacaoCondicional(sup1,Alinha2,payoff,0)): # Se o resultado for falso nao existe acao condicionalmente independe
				# print('Entrou 1')
				S2 = combinations(Alinha2, x[1]) # Todos os suportes possiveis de tamanho x[1] para o jogador 2
				for s2 in S2:
					sup2 = list(s2)					
					if(not VerificaDominacaoCondicional(sup1,sup2, payoff, 0)):
						# print('Entrou 2')
						eNE = VerificaViabilidade(N,A1,A2,sup1,list(s2),payoff) # p e uma lista com a probabilidade de acada acao dentro do suporte
						st = eNE[0]
						if (st == 1):
							# print('Entrou 3')
							print 'equilíbrio encontrado no idx = {}'.format(idx)
							return eNE[1:]



# TO DO:
# COMENTAR TIPO DOXYPYPY
 
