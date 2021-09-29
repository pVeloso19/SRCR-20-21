
% Trabalho realizado por: Pedro Miguel Dias Veloso a89557 (MIEI - Universidade do Minho)

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

%:- include('grafo').
:- include('grafoReduzido').
:- include('algoritmosPesquisa').

%--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
%
%																			         EXERCICIOS PROPOSTOS
%
%--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

% (1) Gerar os circuitos de recolha tanto indiferenciada como seletiva, caso existam, que cubram um determinado território;


circuito(Regiao,C,K1) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                        nodo(Deposito,_,_,Regiao,['Deposito'],_),
                        findall(N,nodo(N,_,_,Regiao,_,_),NA), 
                        resolve_pp_k(NA,Garagem,Deposito,C,K), escrever(C), writeln(Garagem), 
                        dist(Garagem,Deposito,K2), K1 is K+K2.

circuito(Regiao,Tipo,C,K1) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                             nodo(Deposito,_,_,Regiao,['Deposito'],_),
                             findall(N,(nodo(N,_,_,Regiao,AUX2,_), pertence(Tipo,AUX2)),NA),
                             resolve_pp_k([Garagem,Deposito|NA],Garagem,Deposito,C,K), escrever(C), writeln(Garagem), 
                             dist(Garagem,Deposito,K2), K1 is K+K2.

circuito(C,K1) :- nodo(Garagem,_,_,_,['Garagem'],_), 
                 nodo(Deposito,_,_,_,['Deposito'],_),
                 findall(N,nodo(N,_,_,_,_,_),NA), 
                 resolve_pp_k(NA,Garagem,Deposito,C,K), escrever(C), writeln(Garagem), 
                 dist(Garagem,Deposito,K2), K1 is K+K2.

% (2)  Identificar quais os circuitos com mais pontos de recolha (por tipo de resíduo a recolher);

maisPontos([],(A,_,K),(A,K)).
maisPontos([(L,K)|T],(_,PT,_),R) :- comprimento(L,P), P > PT, !, maisPontos(T,(L,P,K),R).
maisPontos([(L,K)|T],(AT,PT,KT),R) :- maisPontos(T,(AT,PT,KT),R).

circuito_maisPontos(Regiao,Tipo,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                        				  nodo(Deposito,_,_,Regiao,['Deposito'],_),
                        				  findall(N,(nodo(N,_,_,Regiao,AUX2,_), pertence(Tipo,AUX2)),NA),
                        				  findall((C,K),resolve_pp_k([Garagem,Deposito|NA],Garagem,Deposito,C,K),L), 
                        				  maisPontos(L,([],0,0),(CP,K1)),
                        				  escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

circuito_maisPontos(Regiao,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                        			 nodo(Deposito,_,_,Regiao,['Deposito'],_),
                    			     findall(N,nodo(N,_,_,Regiao,_,_),NA), 
                        			 findall((C,K),resolve_pp_k([Garagem,Deposito|NA],Garagem,Deposito,C,K),L), 
                        			 maisPontos(L,([],0,0),(CP,K1)),
                        			 escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

circuito_maisPontos(CP,KP) :- nodo(Garagem,_,_,_,['Garagem'],_), 
                        	  nodo(Deposito,_,_,_,['Deposito'],_),
                        	  findall(N,nodo(N,_,_,_,_,_),NA), 
                        	  findall((C,K),resolve_pp_k([Garagem,Deposito|NA],Garagem,Deposito,C,K),L), 
                        	  maisPontos(L,([],0,0),(CP,K1)),
                        	  escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

% (3) Comparar circuitos de recolha tendo em conta os indicadores de produtividade;

head([H|T],H).
empty([]).

distanciaPercorridaCircuito([],0).
distanciaPercorridaCircuito([H|T],R) :- nao(empty(T)), distanciaPercorridaCircuito(T,N1), head(T,T1), dist(H,T1,Dist), R is N1+Dist.
distanciaPercorridaCircuito([H|T],R) :- empty(T), R is 0.

comparaCircuitos(C1,C2,C1) :- distanciaPercorridaCircuito(C1,N1), distanciaPercorridaCircuito(C2,N2), N1 < N2, !.
comparaCircuitos(C1,C2,C2).

% (4) Escolher o circuito mais rápido (usando o critério da distância);

minimoCusto([(P,X)],(P,X)).
minimoCusto([(P,X)|L],(Py,Y)):- minimoCusto(L,(Py,Y)), X>Y.
minimoCusto([(Px,X)|L],(Px,X)):- minimoCusto(L,(Py,Y)), X=<Y.

circuito_maisRapido(Regiao,Tipo,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                                  nodo(Deposito,_,_,Regiao,['Deposito'],_),
                                  findall(N,(nodo(N,_,_,Regiao,AUX2,_), pertence(Tipo,AUX2)),NA),
                                  findall((C,K),resolve_pp_k([Garagem,Deposito|NA],Garagem,Deposito,C,K),L),
                                  minimoCusto(L,(CP,K1)),
                                  escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

circuito_maisRapido(Regiao,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                                     nodo(Deposito,_,_,Regiao,['Deposito'],_),
                                     findall(N,nodo(N,_,_,Regiao,_,_),NA), 
                                     findall((C,K),resolve_pp_k(NA,Garagem,Deposito,C,K),L),
                                     minimoCusto(L,(CP,K1)),
                                     escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

circuito_maisRapido(CP,KP) :- nodo(Garagem,_,_,_,['Garagem'],_), 
                              nodo(Deposito,_,_,_,['Deposito'],_),
                              findall(N,nodo(N,_,_,_,_,_),NA), 
                              findall((C,K),resolve_pp_k(NA,Garagem,Deposito,C,K),L),
                              minimoCusto(L,(CP,K1)),
                              escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

circuito_maisRapido2(CP,KP) :- nodo(Garagem,_,_,_,['Garagem'],_), 
                             nodo(Deposito,_,_,_,['Deposito'],_),
                             findall(N,nodo(N,_,_,_,_,_),NA), 
                             resolve_estrela(NA,Garagem,Deposito,CP/K1),
                             escrever(CP), writeln(Garagem), dist(Garagem,Deposito,K2), KP is K1+K2.

% (5) Escolher o circuito mais eficiente (usando um critério de eficiência à escolha);
% Mais postos com menos Distancia (Aceita-se fazer mais 100 metros para apanhar mais um posto)

maxCusto([(P,X)],(P,X)).
maxCusto([(Px,X)|L],(Py,Y)) :- maxCusto(L,(Py,Y)), X=<Y.
maxCusto([(Px,X)|L],(Px,X)) :- maxCusto(L,(Py,Y)), X>Y.

circuito_maisEficiente(Regiao,Tipo,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                        				     nodo(Deposito,_,_,Regiao,['Deposito'],_),
                        				     findall(N,(nodo(N,_,_,Regiao,AUX2,_), pertence(Tipo,AUX2)),NA),
                        				     findall((C,K),resolve_pp_l([Garagem,Deposito|NA],Garagem,Deposito,C,K),L),
                        	                 maxCusto(L,(CP,KP)),
                        				     escrever(CP), writeln(Garagem).

circuito_maisEficiente(Regiao,CP,KP) :- nodo(Garagem,_,_,Regiao,['Garagem'],_), 
                        		        nodo(Deposito,_,_,Regiao,['Deposito'],_),
                        		        findall(N,nodo(N,_,_,Regiao,_,_),NA), 
                        		        findall((C,K),resolve_pp_l(NA,Garagem,Deposito,C,K),L),
                        	            maxCusto(L,(CP,KP)),
                        			    escrever(CP), writeln(Garagem).

circuito_maisEficiente(CP,KP) :- nodo(Garagem,_,_,_,['Garagem'],_), 
                        	     nodo(Deposito,_,_,_,['Deposito'],_),
                        	     findall(N,nodo(N,_,_,_,_,_),NA), 
                        	     findall((C,K),resolve_pp_l(NA,Garagem,Deposito,C,K),L),
                        	     maxCusto(L,(CP,KP)),
                        	     escrever(CP), writeln(Garagem).