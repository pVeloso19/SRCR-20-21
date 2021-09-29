%-----------------------------------------------------------------------------------------------------------
% Predicado responsavel por calcular a distancia entre duas coordenadas GPS

distancia(Lat1, Long1, Lat2, Long2, DistanceCost) :- ValPi is pi,
        											 Fi1 is Lat1 * (ValPi/180),
        											 Fi2 is Lat2 * (ValPi/180),
        											 DeltaFi is (Lat2-Lat1) * (ValPi/180),
        											 DeltaLambda is (Long2-Long1) * (ValPi/180),
        											 A1 is sin(DeltaFi/2) * sin(DeltaFi/2),
        											 A2 is cos(Fi1) * cos(Fi2),
        											 A3 is sin(DeltaLambda/2) * sin(DeltaLambda/2),
        											 ASum is A1 + A2 * A3,
        											 C1 is sqrt(ASum),
        											 C2 is sqrt(1.0 - ASum),
        											 C is 2 * atan2(C1, C2),
        											 Dist is 6.371*1000 * C,
        											 DistanceCost is Dist*1000. % em metros

%-----------------------------------------------------------------------------------------------------------
% Predicado responsavel por calcular a distancia entre dois pontos do grafo

dist(Nodo,Final,Euristica) :- nodo(Nodo,Lat1,Lon1,_,_,_), nodo(Final,Lat2,Lon2,_,_,_), distancia(Lat1,Lon1,Lat2,Lon2,Euristica).

%-----------------------------------------------------------------------------------------------------------
% Predicado não, responsavel por negar a veracidade de algo 

nao( Questao ) :-
    Questao, !, fail.
nao( Questao ).

%-----------------------------------------------------------------------------------------------------------
% Verifica se um determinado elemento é membro de uma lista

membro(X, [X|_]).
membro(X, [_|Xs]):-
	membro(X, Xs).

%-----------------------------------------------------------------------------------------------------------
% Concatena uma lista

concatena([X|Xs],L,[X|Ys]):-
   concatena(Xs,L,Ys).
concatena([],L,L).

%-----------------------------------------------------------------------------------------------------------
% Determina o compriemnto de uma lista

comprimento( [],0 ).
comprimento( [X|L],N ) :-
    comprimento( L,N1 ),
    N is N1+1.

%-----------------------------------------------------------------------------------------------------------
% Verifica se um determinado elemento pertence a uma lista

pertence(X, [X|_]).
pertence(X, [H|T]) :- X \= H, pertence(X, T).

%-----------------------------------------------------------------------------------------------------------
% Escreve os elementos de uma lista no ecra 

escrever([]).
escrever([H|T]) :- writeln(H), escrever(T).

%-----------------------------------------------------------------------------------------------------------
% Inverte uma lista

inverteraux([],A,A).
inverteraux([H|T],A,R) :- inverteraux(T,[H|A],R).

inverso(L,R) :- inverteraux(L,[],R).

%-----------------------------------------------------------------------------------------------------------

seleciona(E,[E|Xs],Xs).
seleciona(E,[X|Xs], [X|Ys]) :- seleciona(E,Xs,Ys). 

%------------ Profundidade -----------------------------------------------------------------------------------------------
% Realisa a pesquisa em profundidade

profundidade_todos(Nodo, Final, C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_pp_todos(NA,Nodo,Final,C).
profundidade(Nodo, Final, C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_pp(NA,Nodo,Final,C).

resolve_pp_todos(NodosPercorrer, Nodo, Final, [Nodo|Caminho]) :- profundidadeprimeiro1(NodosPercorrer,Nodo,Final,[Nodo],Caminho), comprimento(Caminho,T1), comprimento(NodosPercorrer,T2), T1>(T2-2).

resolve_pp(NodosPercorrer, Nodo, Final, [Nodo|Caminho]) :- profundidadeprimeiro1(NodosPercorrer,Nodo,Final,[Nodo],Caminho).

profundidadeprimeiro1(NodosPercorrer,Nodo,Nodo,_,[]).
profundidadeprimeiro1(NodosPercorrer,Nodo,Final, Historico, [ProxNodo|Caminho]) :- adjacente(NodosPercorrer,Nodo,ProxNodo), nao(membro(ProxNodo,Historico)), profundidadeprimeiro1(NodosPercorrer,ProxNodo,Final,[ProxNodo|Historico],Caminho).

adjacente(NodosAdmissiveis, Nodo, ProxNodo) :- aresta(Nodo,ProxNodo), pertence(Nodo,NodosAdmissiveis), pertence(ProxNodo,NodosAdmissiveis).

%------------ Profundidade com custos -----------------------------------------------------------------------------------------------
% Realisa a pesquisa em profundidade, calculando os custos

profundidade_todos_custo(Nodo, Final, C, K) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_pp_k_todos(NA,Nodo,Final,C,K).
profundidade_custo(Nodo, Final, C, K) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_pp_k(NA,Nodo,Final,C,K).

resolve_pp_k_todos(NodosPercorrer, Nodo, Final, [Nodo|Caminho], K) :- profundidadeprimeirok(NodosPercorrer, Nodo,Final,[Nodo],Caminho, 0, K), comprimento(Caminho,T1), comprimento(NodosPercorrer,T2), T1>(T2-2).

resolve_pp_k(NodosPercorrer, Nodo, Final, [Nodo|Caminho], K) :- profundidadeprimeirok(NodosPercorrer, Nodo,Final,[Nodo],Caminho, 0, K).

profundidadeprimeirok(NodosPercorrer, Nodo,Nodo,_,[],A, A).
profundidadeprimeirok(NodosPercorrer, Nodo,Final, Historico, [ProxNodo|Caminho], A, K) :- adjacenteK(NodosPercorrer, Nodo,ProxNodo, KT), 
																	                      nao(membro(ProxNodo,Historico)),
																	      				  N is A + KT,
																	      	              profundidadeprimeirok(NodosPercorrer,ProxNodo,Final,[ProxNodo|Historico],Caminho, N, K).

adjacenteK(NodosAdmissiveis, Nodo, ProxNodo, K) :- aresta(Nodo,ProxNodo), 
	                                               pertence(Nodo,NodosAdmissiveis), 
	                                               pertence(ProxNodo,NodosAdmissiveis), 
	                                               nodo(Nodo,Lat1,Lon1,_,_,_), 
	                                               nodo(ProxNodo,Lat2,Lon2,_,_,_), 
	                                               distancia(Lat1,Lon1,Lat2,Lon2,K).

%------------ Profundidade com quantidade Lixo recolhido -----------------------------------------------------------------------------------------------
% Realisa a pesquisa em profundidade, calculando a quantidade de lixo recolhida

resolve_pp_l(NodosPercorrer, Nodo, Final, [Nodo|Caminho], K) :- profundidadeprimeirol(NodosPercorrer, Nodo,Final,[Nodo],Caminho, 0, K).

profundidadeprimeirol(NodosPercorrer, Nodo,Nodo,_,[],A, A).
profundidadeprimeirol(NodosPercorrer, Nodo,Final, Historico, [ProxNodo|Caminho], A, K) :- adjacentel(NodosPercorrer, Nodo,ProxNodo, KT), 
																	                      nao(membro(ProxNodo,Historico)),
																	      				  N is A + KT,
																	      	              profundidadeprimeirol(NodosPercorrer,ProxNodo,Final,[ProxNodo|Historico],Caminho, N, K).

adjacentel(NodosAdmissiveis, Nodo, ProxNodo, K) :- aresta(Nodo,ProxNodo), 
	                                               pertence(Nodo,NodosAdmissiveis), 
	                                               pertence(ProxNodo,NodosAdmissiveis), 
	                                               nodo(ProxNodo,_,_,_,_,K).
%------------ Largura -----------------------------------------------------------------------------------------------
% Realisa a pesquisa em largura 

resolveBF(No, Final, Solucao) :- findall(N,nodo(N,_,_,_,_,_),NA), breadthFirst(NA, Final, [[No]], Solucao1), inverso(Solucao1,Solucao).

breadthFirst(NodosPercorrer, Final, [[No|Caminho]|_], [No|Caminho]) :- Final =:= No.
breadthFirst(NodosPercorrer, Final, [Caminho|Caminhos], Solucao) :- expandirLargura(NodosPercorrer, Caminho, NovosCaminhos),
                                                                    concatena(Caminhos, NovosCaminhos, Caminhos1),
                                                                    breadthFirst(NodosPercorrer, Final, Caminhos1, Solucao).

expandirLargura(NodosPercorrer, [No|Caminho],NovosCaminhos) :- findall([NovoNo,No|Caminho],(aresta(No,NovoNo), 
	                                                                                        pertence(NovoNo,NodosPercorrer), 
	                                                                                        \+ pertence(NovoNo,[No|Caminho])),
                                                                       NovosCaminhos).

%------------ Profundidade Limitada -----------------------------------------------------------------------------------------------
% Realisa a pesquisa em profundidade com um limite de profundidade

profundidade_limitada(NodosPercorrer, LimiteDeProf, Final, [(E,_)|Es], Historia, [E]):- E=:=Final.
profundidade_limitada(NodosPercorrer, LimiteDeProf, Final, [(E,LimiteDeProf)|Es],Historia,Solucao):- !, profundidade_limitada(NodosPercorrer, LimiteDeProf, Final, Es,Historia,Solucao).
profundidade_limitada(NodosPercorrer, LimiteDeProf, Final, [(E,ProfAtual)|Es], Historia, [E|Solucao]):- findall(F,(aresta(E,F), pertence(F,NodosPercorrer)),Filhos),
    																							        ProxProf is ProfAtual + 1,
   																								        expandeComProfundidadeLimitada(Filhos,ProxProf, Historia,FilhosRotulados),
    																							        concatena(FilhosRotulados,Es,ProxEs),
    																							        profundidade_limitada(NodosPercorrer, LimiteDeProf, Final, ProxEs,[E|Historia],Solucao).

expandeComProfundidadeLimitada([E|Es],P,Historia,ER):- membro(E,Historia), !,
                                                       expandeComProfundidadeLimitada(Es,P,Historia,ER).
expandeComProfundidadeLimitada([E|Es],P,Historia,[(E,P)|ER]):- expandeComProfundidadeLimitada(Es,P,Historia,ER).
expandeComProfundidadeLimitada([],_,_,[]):-!.


resolve_pp_com_profundidade_limitada(NodosPercorrer, LimiteDeProfundidade, EstadoInicial, Final, Solucao):- 
			profundidade_limitada(NodosPercorrer, LimiteDeProfundidade, Final, [(EstadoInicial,0)],[],Solucao).

resolve_pp_limitada(NodoInicial, NodoFinal, LimiteProf, Caminho) :- findall(N,nodo(N,_,_,_,_,_),L), resolve_pp_com_profundidade_limitada(L,LimiteProf,NodoInicial,NodoFinal,Caminho).  

%------------ Pesquisa Informada (Gulosa)------------------------------------------------------------------------------------------------------------------
% Realisa a pesquisa gulosa 

gulosa_todos(NI,NF,C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_gulosa_todos(NA,NI,NF,C).
gulosa(NI,NF,C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_gulosa(NA,NI,NF,C).

resolve_gulosa_todos(NodosPercorrer, Nodo, Final, Caminho/Custo) :- dist(Nodo,Final,Estima),
 									                                agulosa(NodosPercorrer,Final,[[Nodo]/0/Estima], InvCaminho/Custo/_),
 									                                comprimento(NodosPercorrer,T1),
 									                                comprimento(InvCaminho,T2),
 									                                T2 > (T1-1),
 									                                inverso(InvCaminho,Caminho).

resolve_gulosa(NodosPercorrer, Nodo, Final, Caminho/Custo) :- dist(Nodo,Final,Estima),
 									                          agulosa(NodosPercorrer,Final,[[Nodo]/0/Estima], InvCaminho/Custo/_),
 									                          inverso(InvCaminho,Caminho).

agulosa(NodosPercorrer, Final, Caminhos, Caminho) :- obtem_melhor_g(Caminhos,Caminho), Caminho = [Nodo|_]/_/_, Nodo=:=Final.
agulosa(NodosPercorrer, Final, Caminhos, SolucaoCaminho) :- obtem_melhor_g(Caminhos, MelhorCaminho),
                              		                        seleciona(MelhorCaminho,Caminhos,OutrosCaminhos),
                              		                        expande_gulosa(NodosPercorrer, Final, MelhorCaminho, ExpCaminhos),
                              	                            append(OutrosCaminhos,ExpCaminhos,NovoCaminho),
                              	                            agulosa(NodosPercorrer, Final, NovoCaminho,SolucaoCaminho).

obtem_melhor_g([Caminho],Caminho) :- !.
obtem_melhor_g([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos],MelhorCaminho) :- Est1 =< Est2, !, obtem_melhor_g([Caminho1/Custo1/Est1|Caminho],MelhorCaminho).
obtem_melhor_g([_|Caminhos],MelhorCaminho) :- obtem_melhor_g(Caminhos,MelhorCaminho).

expande_gulosa(NodosPercorrer, Final, Caminho,ExpCaminhos) :- findall(NovoCaminho,adjacente3(NodosPercorrer, Final, Caminho, NovoCaminho),ExpCaminhos).



adjacente3(NodosPercorrer, Final, [Nodo|Caminho]/Custo/_, [ProxNodo,Nodo|Caminho]/NovoCusto/Est) :- aresta(Nodo,ProxNodo),
																									pertence(Nodo,NodosAdmissiveis), pertence(ProxNodo,NodosAdmissiveis),
																					                \+ membro(ProxNodo,Caminho),
																			                        nodo(Nodo,Lat1,Lon1,_,_,_), 
																			                        nodo(ProxNodo,Lat2,Lon2,_,_,_), 
																			                        distancia(Lat1,Lon1,Lat2,Lon2,PassoCusto),								 
																			                        NovoCusto is Custo + PassoCusto, 
																			                        dist(ProxNodo,Final,Est).

%------------------ A* ---------------------
% Realisa a pesquisa A*

estrela_tudo(NI,NF,C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_estrela_tudo(NA,NI,NF,C).
estrela(NI,NF,C) :- findall(N,nodo(N,_,_,_,_,_),NA), resolve_estrela(NA,NI,NF,C).

resolve_estrela_tudo(NodosPercorrer, Nodo, Final, Caminho/Custo) :- dist(Nodo,Final,Estima),
 									   			                    estrela(NodosPercorrer, Final, [[Nodo]/0/Estima], InvCaminho/Custo/_),
 									   			                    comprimento(NodosPercorrer,T1),
 									                                comprimento(InvCaminho,T2),
 									                                T2 > (T1-1),
 									                                inverso(InvCaminho,Caminho).

resolve_estrela(NodosPercorrer, Nodo, Final, Caminho/Custo) :- dist(Nodo,Final,Estima),
 									   			               estrela(NodosPercorrer, Final, [[Nodo]/0/Estima], InvCaminho/Custo/_),
 									                           inverso(InvCaminho,Caminho).

estrela(NodosPercorrer, Final, Caminhos, Caminho) :- obtem_melhor_e(Caminhos,Caminho), Caminho = [Nodo|_]/_/_, Nodo=:=Final.
estrela(NodosPercorrer, Final, Caminhos, SolucaoCaminho) :- obtem_melhor_e(Caminhos, MelhorCaminho),
                              		                        seleciona(MelhorCaminho,Caminhos,OutrosCaminhos),
                              		                        expande_estrela(NodosPercorrer, Final, MelhorCaminho, ExpCaminhos),
                              	                            append(OutrosCaminhos,ExpCaminhos,NovoCaminho),
                              	                            estrela(NodosPercorrer, Final, NovoCaminho, SolucaoCaminho).

obtem_melhor_e([Caminho],Caminho) :- !.
obtem_melhor_e([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos],MelhorCaminho) :- Custo1 + Est1 =< Custo2 + Est2, !, 
																			   obtem_melhor_e([Caminho1/Custo1/Est1|Caminho],MelhorCaminho).
obtem_melhor_e([_|Caminhos],MelhorCaminho) :- obtem_melhor_e(Caminhos,MelhorCaminho).

expande_estrela(NodosPercorrer, Final, Caminho, ExpCaminhos) :- findall(NovoCaminho,adjacente3(NodosPercorrer, Final, Caminho, NovoCaminho),ExpCaminhos).