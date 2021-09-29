%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MIEI 

% GRUPO 5 - Fase 2
% Pedro Miguel Dias Veloso  - A89557
% Carlos João Teixeira Preto  - A89587
% Simão Freitas Monteiro - A85489
% Ricardo Gomes - A93785

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% PROLOG: Declaracoes iniciais

:- set_prolog_flag( discontiguous_warnings,off ).
:- set_prolog_flag( single_var_warnings,off ).
:- set_prolog_flag( unknown,fail ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% PROLOG: definicoes iniciais

:- op( 900,xfy,'::' ).
:- dynamic utente/10.
:- dynamic centroSaude/5.
:- dynamic staff/4.
:- dynamic vacinacaoCovid/5.

:- dynamic profissaoPrioritaria/1.
:- dynamic doenca_risco/1.
:- dynamic '-'/1.

:- discontiguous ((-)/1).
:- discontiguous (excecao/1).
%--------------------------------- - - - - - - - - - -  -  -  -  -   -

dataVacinacaoValida(D) :- data(D).

staffVacinouValido(ID) :- integer(ID), staff(ID,_,_,_).

centroSaudeValido(IC) :- integer(IC), centroSaude(IC,_,_,_,_).

numeroSegurancaSocialValida(SS) :- SS >= 10000000000, SS =< 99999999999.

numTelemovelValido(TS) :- TS >= 100000000, TS =< 999999999.

dataNascimentoValida(DA) :- data(DA), idade(DA, IDADE), IDADE > 0, IDADE =< 150.

postoSaudeValido(PS) :- integer(PS).

%>--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% Não permite a inserçã ode utentes com um id que nao seja um numero, onde o numero de segurança social tenha menos de 11 digitos,
% o telefone tenha menos de 9 digitos, a data de nascimento seja invalida, a idade seja superior a 150 anos, e que ja exista um 
% utente com o mesmo ID 

+utente(ID,SS,Nome,DA,Email,TS,Morada,Prof,D,PS) :: (integer(ID),
                                                     numeroSegurancaSocialValida(SS), 
                                                     numTelemovelValido(TS),
                                                     dataNascimentoValida(DA),
                                                     postoSaudeValido(PS),
                                                     solucoes(ID,(utente(ID,_,_,_,_,_,_,_,_,_)),S ),
                                                     comprimento( S,C ),  
				                                             C == 1,
                                                     nao(-utente(ID,SS,Nome,DA,TS,Email,Morada,Prof,D,PS))
                                                    ).

+(-utente(ID,SS,Nome,DA,Email,TS,Morada,Prof,D,PS)) :: (integer(ID),
                                                        numeroSegurancaSocialValida(SS), 
                                                        numTelemovelValido(TS),
                                                        data(DA),
                                                        postoSaudeValido(PS),
                                                        solucoes(ID,(-utente(ID,SS,Nome,DA,Email,TS,Morada,Prof,D,PS)),S ),
                                                        comprimento( S,C ),  
                                                        C > 0,
                                                        C < 3
                                                       ).

% não permite a remoção se o utente estiver registado no conhecimento de vacinaçao

-utente(ID,_,_,_,_,_,_,_,_,_) :: (solucoes(ID,(vacinacaoCovid(_,ID,_,_,_)),S ),
                                  comprimento( S,N ), 
                                  N == 0
                                 ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% Não permite a inserção de centros de saude onde o Id não seja um inteiro, o numero de telefone seja invalido, com menos de 9 digitos
% e que ja exista um centro com o mesmo ID 

+centroSaude(ID,N,M,T,E) :: (integer(ID),
                             numTelemovelValido(T),
                             solucoes(ID,(centroSaude(ID,_,_,_,_)),S ),
                             comprimento( S,C ),  
				                     C == 1,
                             nao(-centroSaude(ID,N,M,T,E))
                            ).

+(-centroSaude(ID,N,M,T,E)) :: (integer(ID),
                                numTelemovelValido(T),
                                solucoes(ID,(-centroSaude(ID,N,M,T,E)),S ),
                                comprimento( S,C ),  
                                C > 0,
                                C < 3
                               ).

% não permite a remoção se existirem elementos registados no conhecimento do staff como trabalhando nesse centro

-centroSaude(ID,_,_,_,_) :: (solucoes(ID,(staff(_,ID,_,_)),S ),
                             comprimento( S,C ),  
				                     C == 0
                            ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não permite a inserção de um staff que trabalhe num centro de saude que nao seja conhecido, e com um id repetido

+staff(ID,IC,N,M) :: (integer(ID),
                      centroSaudeValido(IC),
                      solucoes(ID,(staff(ID,_,_,_)),S ),
                      comprimento( S,C ),  
				              C == 1,
                      nao(-satff(ID,IC,N,M))
                     ).

+(-staff(ID,IC,N,M)) :: (integer(ID),
                         integer(IC),
                         solucoes(ID,(-staff(ID,IC,N,M)),S ),
                         comprimento( S,C ), 
                         C > 0,
                         C < 3
                        ).

% não pode ser retirado elementos do staff que ja vacinaram alguem, e que essa informação é conhecida

-staff(ID,_,_,_) :: (solucoes(ID,(vacinacaoCovid(ID,_,_,_,_)),S ),
                     comprimento( S,C ),
                     C == 0
                    ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não podem ser inseridos dados repetidos sobre vacinação, ou que o utente/satff sejam desconhecidos
% também é necessario que a data de vacinação seja valida

+vacinacaoCovid(IS,IU,D,V,T) :: (integer(IU),
                                 utente(IU,_,_,_,_,_,_,_,_,_),
                                 staffVacinouValido(IS),
                                 dataVacinacaoValida(D),
                                 integer(T),
                                 T >= 0,
                                 T < 3,
                                 solucoes(IS,(vacinacaoCovid(IS,IU,D,V,T)),S ),
                                 comprimento( S,C ),  
				                         C == 1,
                                 nao(-vacinacaoCovid(IS,IU,D,V,T))
                                ).

+(-vacinacaoCovid(IS,IU,D,V,T)) :: (integer(IU),
                                    integer(IS),
                                    data(D),
                                    integer(T),
                                    solucoes(IS,(-vacinacaoCovid(IS,IU,D,V,T)),S ),
                                    comprimento( S,C ),  
                                    C > 0,
                                    C < 3
                                   ).

+vacinacaoCovid(_,_,_,_,_)::(solucoes(A,(vacinacaoCovid(7,10,A,'astrazeneca', 2), nao(nulo(A))),S), comprimento(S,N), N==0).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não devem ser inseridos valores repetidos

+profissaoPrioritaria(P) :: (solucoes(P,(profissaoPrioritaria(P)),S ),
                      		   comprimento( S,C ),  
				                     C == 1,
                             nao(-profissaoPrioritaria(P))
                     		    ).

+(-profissaoPrioritaria(P)) :: (solucoes(P,(-profissaoPrioritaria(P)),S ),
                                comprimento( S,C ),  
                                C > 0,
                                C < 3
                               ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não devem ser inseridos valores repetidos

+doenca_risco(D) :: (solucoes(D,(doenca_risco(D)),S ),
                     comprimento( S,C ),  
				             C == 1,
                     nao(-doenca_risco(D))
                    ).

+(-doenca_risco(D)) :: (solucoes(D,(-doenca_risco(D)),S ),
                        comprimento( S,C ),  
                        C > 0,
                        C < 3
                       ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado solucoes: F, Q, S -> {V, F}

solucoes(X,P,S) :- findall(X,P,S).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado comprimento: S, N -> {V, F}

comprimento( [],0 ).
comprimento( [_|L],N ) :-
    comprimento( L,N1 ),
    N is N1+1.

-comprimento(Lista, Tam) :- 
    nao(comprimento(Lista, Tam)), 
    nao(excecao(comprimento(Lista, Tam))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado nao: Termo -> {V, F}

nao(T) :- T, !, fail.
nao(_).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pertence: X, Lista -> {V, F}

pertence(X, [X|_]).
pertence(X, [H|T]) :- X \= H, pertence(X, T).

-pertence(Elem, Lista) :- 
    nao(pertence(Elem, Lista)), 
    nao(excecao(pertence(Elem, Lista))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado data: Dia, Mes, Ano -> {V, F}	
data(D, 2, A) :-
    A >= 0,
	A mod 4 =:= 0,
	D >= 1,
	D =< 29.
data(D, M, A) :-
	A >= 0,
    pertence(M, [1,3,5,7,8,10,12]),
	D >= 1,
	D =< 31.
data(D, M, A) :-
	A >= 0,
    pertence(M, [4,6,9,11]),
	D >= 1,
	D =< 30.
data(D, 2, A) :-
	A >= 0,
    A mod 4 =\= 0, 
	D >= 1,
	D =< 28.
data(data(D, M, A)) :- data(D, M, A).

-data(D, M, A) :- 
    nao(data(D, M, A)), 
    nao(excecao(data(D, M, A))).

-data(data(D, M, A)) :- 
    nao(data(data(D, M, A))), 
    nao(excecao(data(data(D, M, A)))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado depois: Data, Data -> {V, F}
% Verifica se uma data vem depois de outra 

depois(data(_,_,A1), data(_,_,A2)) :- 
	A1 > A2.
depois(data(_,M1,A1), data(_,M2,A2)) :- 
	A1 >= A2,
	M1 > M2.
depois(data(D1,M1,A1), data(D2,M2,A2)) :- 
	A1 >= A2,
	M1 >= M2,
	D1 > D2.
depois(_, _) :- !, fail.

-depois(data(D1,M1,A1), data(D2,M2,A2)) :- 
    nao(depois(data(D1,M1,A1), data(D2,M2,A2))), 
    nao(excecao(depois(data(D1,M1,A1), data(D2,M2,A2)))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado antes: Data, Data -> {V,F}
% Testa se uma data ocorre antes de uma outra data

antes(D1, D2) :- nao(depois(D1,D2)).

-antes(data(D1,M1,A1), data(D2,M2,A2)) :- 
    nao(antes(data(D1,M1,A1), data(D2,M2,A2))), 
    nao(excecao(antes(data(D1,M1,A1), data(D2,M2,A2)))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado profissaoPrioritaria: Profissão -> {V, F}
% Expressa o conhecimento sobre a prioridade de uma profissão. As profissoes aqui conhecidas 
% devem ser consideradas como prioritarias na vacinação

profissaoPrioritaria('Medico').
profissaoPrioritaria('Enfermeiro').

-profissaoPrioritaria(P) :- 
    nao(profissaoPrioritaria(P)), 
    nao(excecao(profissaoPrioritaria(P))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidadatasFase1: ID_Utente, Nome_Utente -> {V, F}
% Verifica se um utente apresenta as caracteristicas para a fase 1 da vacinação

pessoasCandidadatasFase1(ID,N) :- utente(ID,_,N,_,_,_,_,P,_,_), 	 
								                  profissaoPrioritaria(P),
                                  nao(-profissaoPrioritaria(P)).

-pessoasCandidadatasFase1(ID,N) :- 
    nao(pessoasCandidadatasFase1(ID,N)), 
    nao(excecao(pessoasCandidadatasFase1(ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase1: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 1 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 1 

fase1(X):- solucoes((ID,N), pessoasCandidadatasFase1(ID,N), X).

-fase1(X) :- 
    nao(fase1(X)), 
    nao(excecao(fase1(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado data_atual: Data -> {V,F}

data_atual(data(3,5,2021)).

-data_atual(D) :- 
    nao(data_atual(D)), 
    nao(excecao(data_atual(D))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado idade: Data, Idade -> {V,F}
% Verifica/Calcula a idade de uma pessoa

idade(data(_,_,A), IDADE) :- data_atual(data(_,_,AA)), 
							 IDADE is AA-A.

-idade(D, IDADE) :- 
    nao(idade(D, IDADE)), 
    nao(excecao(idade(D, IDADE))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado doença_risco: Doença -> {V,F}

doenca_risco('Asma').
doenca_risco('Cancro').

-doenca_risco(D) :- 
    nao(doenca_risco(D)), 
    nao(excecao(doenca_risco(D))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado doenteRisco: Lista_Doentes -> {V,F}
% Verifica se alguma das doenças presentes na lista é considerada de risco

doenteRisco([]) :- !, fail.
doenteRisco([H|_]) :- doenca_risco(H), nao(-doenca_risco(H)).
doenteRisco([_|T]) :- doenteRisco(T).

-doenteRisco(Lista) :- 
    nao(doenteRisco(Lista)), 
    nao(excecao(doenteRisco(Lista))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidadatasFase2: ID_Utente, Nome_Utente -> {V, F}
% Verifica se um utente apresenta as caracteristicas para a fase 2 da vacinação

pessoasCandidadatasFase2(ID,N) :- utente(ID,_,N,DA,_,_,_,_,_,_), 
							   	  idade(DA, IDADE), 
							      IDADE >= 80,
							      fase1(F1),
							      nao(pertence((ID,N),F1)).
pessoasCandidadatasFase2(ID,N) :- utente(ID,_,N,_,_,_,_,_,D,_), 
								  doenteRisco(D),
								  fase1(F1),
								  nao(pertence((ID,N),F1)).

-pessoasCandidadatasFase2(ID,N) :- 
    nao(pessoasCandidadatasFase2(ID,N)), 
    nao(excecao(pessoasCandidadatasFase2(ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase2: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 2 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 2 

fase2(X):- solucoes((ID,N), pessoasCandidadatasFase2(ID,N), X).

-fase2(X) :- 
    nao(fase2(X)), 
    nao(excecao(fase2(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidadatasFase3: ID_Utente, Nome_Utente -> {V, F}
% Verifica se um utente apresenta as caracteristicas para a fase 3 da vacinação

pessoasCandidadatasFase3(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_),
								  fase1(F1),
								  fase2(F2),
								  nao(pertence((ID,N),F1)),
								  nao(pertence((ID,N),F2)).

-pessoasCandidadatasFase3(ID,N) :- 
    nao(pessoasCandidadatasFase3(ID,N)), 
    nao(excecao(pessoasCandidadatasFase3(ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase2: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 3 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 3 

fase3(X):- solucoes((ID,N), pessoasCandidadatasFase3(ID,N), X).

-fase3(X) :- 
    nao(fase3(X)), 
    nao(excecao(fase3(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidatas: Fase, Lista_Pessoas -> {V,F}

pessoasCandidatas(1, X) :- fase1(X).
pessoasCandidatas(2, X) :- fase2(X).
pessoasCandidatas(3, X) :- fase3(X).

excecao( pessoasCandidatas(X, _) ) :- X >= 4.

-pessoasCandidatas(F, X) :- 
    nao(pessoasCandidatas(F, X)), 
    nao(excecao(pessoasCandidatas(F, X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteVacinado: ID_Utente, Nome_Utente -> {V,F}
% Verifica se um utente já está totalmente vacinado 

utenteVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
				    	vacinacaoCovid(_, ID, _, _, T), 
						T >= 2.

-utenteVacinado(ID,N) :- 
    nao(utenteVacinado(ID,N)), 
    nao(excecao(utenteVacinado(ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasVacinadas: Lista_Pessoas -> {V,F}
% verifica se todas as pessoas na lista estão totalmente vacinadas
% por conseguinte informa todas as pessoas que estão totalmente vacinadas

pessoasVacinadas(X) :- solucoes((ID,N), utenteVacinado(ID,N), X).

-pessoasVacinadas(X) :- 
    nao(pessoasVacinadas(X)), 
    nao(excecao(pessoasVacinadas(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteNaoVacinado: ID_Utente, Nome_Utente -> {V,F}
% Verifica se um utente não está vacinado
utenteNaoVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
						   nao(vacinacaoCovid(_, ID, _, _, 2)).
utenteNaoVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
						   vacinacaoCovid(_, ID, _, _, 0).

-utenteNaoVacinado(ID,N) :- 
    nao(utenteNaoVacinado(ID,N)), 
    nao(excecao(utenteNaoVacinado(ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasNaoVacinadas: Lista_Pessoas -> {V,F}
% verifica se todas as pessoas na lista não estão vacinadas
% por conseguinte informa todas as pessoas que não estão vacinadas

pessoasNaoVacinadas(X) :- solucoes((ID,N), utenteNaoVacinado(ID,N), X).

-pessoasNaoVacinadas(X) :- 
    nao(pessoasNaoVacinadas(X)), 
    nao(excecao(pessoasNaoVacinadas(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteVacinadoIndevidamente: ID_Utente , Nome_Utente, Fase -> {V,F}
% Verifica se um utente foi bem vacinado, considerando a fase de vacinação atual

utenteVacinadoIndevidamente(ID, N, 1) :- utente(ID,_,N,_,_,_,_,_,_,_),
										 vacinacaoCovid(_, ID, _, _, _),
										 fase1(F1),
										 nao(pertence((ID,N),F1)).
utenteVacinadoIndevidamente(ID, N, 2) :- utente(ID,_,N,_,_,_,_,_,_,_),
										 vacinacaoCovid(_, ID, _, _, _),
										 fase3(F3),
										 pertence((ID,N),F3).  
utenteVacinadoIndevidamente(ID, N, 2) :- utente(ID,_,N,_,_,_,_,_,_,_),
										 vacinacaoCovid(_, ID, D, _, _),
										 fase1(F1),
										 nao(pertence((ID,N),F1)),
										 ultimaDataFase(1,UltData),
										 antes(D,UltData).
utenteVacinadoIndevidamente(ID, N, 3) :- utente(ID,_,N,_,_,_,_,_,_,_),
										 vacinacaoCovid(_, ID, D, _, _),
										 fase3(F3),
										 pertence((ID,N),F3),
										 ultimaDataFase(2,UltData),
										 antes(D,UltData).

-utenteVacinadoIndevidamente(ID, N, F) :- 
    nao(utenteVacinadoIndevidamente(ID, N, F)), 
    nao(excecao(utenteVacinadoIndevidamente(ID, N, F))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado listaVacinadosIndividamente: Fase, Lista_Pessoas, Acumulador, Resultado -> {V,F}
% Constroi uma lista com as pessoas vacinadas indevidamente 

listaVacinadosIndividamente(_,[],A,A).
listaVacinadosIndividamente(FaseAtual, [(ID,N)|Resto], A, R) :- utenteVacinadoIndevidamente(ID,N, FaseAtual), listaVacinadosIndividamente(FaseAtual, Resto, [(ID,N)|A], R).
listaVacinadosIndividamente(FaseAtual, [_|Resto], A, R) :- listaVacinadosIndividamente(FaseAtual, Resto, A, R).

-listaVacinadosIndividamente(FaseAtual, Lista, A, R) :- 
    nao(listaVacinadosIndividamente(FaseAtual, Lista, A, R)), 
    nao(excecao(listaVacinadosIndividamente(FaseAtual, Lista, A, R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasVacinadasIndevidamente: Lista -> {V,F}
% Verifica dada uma lista de utentes, se todos eles foram vacinados indevidamente
% por conseguinte informa todos os utentes vacinados indevidamente

pessoasVacinadasIndevidamente(X) :- solucoes((ID,N),utente(ID,_,N,_,_,_,_,_,_,_), L),faseAtual(FaseAtual), listaVacinadosIndividamente(FaseAtual,L,[],X).

-pessoasVacinadasIndevidamente(X) :- 
    nao(pessoasVacinadasIndevidamente(X)), 
    nao(excecao(pessoasVacinadasIndevidamente(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteNaoVacinadoCandidato: Fase, ID_Utente, Nome_Utente -> {V,F}
% verifica se um utente é candidato para a fase atual de vacinação

utenteNaoVacinadoCandidato(FaseAtual, ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_),
                                               pessoasCandidatas(FaseAtual,R),
                                               pertence((ID,N),R),
                                               nao(vacinacaoCovid(_,ID,_,_,_)).

-utenteNaoVacinadoCandidato(FaseAtual, ID,N) :- 
    nao(utenteNaoVacinadoCandidato(FaseAtual, ID,N)), 
    nao(excecao(utenteNaoVacinadoCandidato(FaseAtual, ID,N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasNaoVacinadasCandidatas: Lista -> {V,F}
% Verifica se todas as pessoas na lista são candidatas nao vacinadas à fase atual de vacinação
% por conseguinte informa todas as pessoas não vacindas candidatas 

pessoasNaoVacinadasCandidatas(X) :- faseAtual(FaseAtual), solucoes((ID, N), utenteNaoVacinadoCandidato(FaseAtual, ID,N), X).

-pessoasNaoVacinadasCandidatas(X) :- 
    nao(pessoasNaoVacinadasCandidatas(X)), 
    nao(excecao(pessoasNaoVacinadasCandidatas(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasFaltaSegundaFaseVacinacao: Lista -> {V,F}
% Verifica se todas as pessoas na lista já tomaram a 1 toma da vacina mas ainda falta a segunda 
% por conseguinte informa todas as pessoas nessa situação

pessoasFaltaSegundaFaseVacinacao(X) :- solucoes((ID,N),( utente(ID,_,N,_,_,_,_,_,_,_), 
														 vacinacaoCovid(_,ID,_,_,1), 
														 nao(vacinacaoCovid(_,ID,_,_,2)) 
												       ), X).

-pessoasFaltaSegundaFaseVacinacao(X) :- 
    nao(pessoasFaltaSegundaFaseVacinacao(X)), 
    nao(excecao(pessoasFaltaSegundaFaseVacinacao(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utente: ID_utente, Nº Segurança_Social, Nome, Data_Nasc, Email, Telefone, Morada, Profissão, [Doenças_Crónicas], ID_CentroSaúde -> {V, F}

utente(1 , 11111111111, 'Simao', data(14,12,1972), 'simao@mail.com', 930551476, 'Largo Coronel Brito Gorjao - Mafra','Gestor', ['Asma'], centro_saude_desconhecido).
utente(2 , 22222222222, 'Telmo', data(27,12,1967), 'telmo@mail.com', 961773477, morada_desconhecida,'Engenheiro Informatico', ['Colesterol','Hipertensao'], 1).
utente(3 , 33333333333, 'Tiago', data(6,11,2000), 'tiago@mail.com', telemovel_desconhecido, 'Rua dos 3 Vales - Almeirim','Motorista', [], 1).
utente(4 , 44444444444, 'Vasco', data(23,6,1953), mail_desconhecido, 961773477, 'Largo Doutor Dario Gandra Nunes - Amadora','Consultor', ['Cancro'], 2).
utente(5 , 55555555555, nome_desconhecido, data(9,12,1953), 'raul@mail.com', 918851034, 'Rua Real Fabrica do Vidro - Amadora','Professor', [], 2).
utente(6 , seguranca_social_desconhecida, 'Ana', data(12,12,1933), 'ana@mail.com', 935465241, 'R. Prof. Francisco Gentil - Barreiro','Coach', [], 3).
utente(7 , 77777777777, 'Augusta', data(17,12,1982), 'augusta@mail.com', 966148612, 'Rua S. Tomas de Aquino - Braga','Medico', ['Asma'], 4).
utente(8 , 88888888888, 'Carlota', data(7,12,1980) , 'carlota@mail.com', 930568014, 'Largo Coronel Brito Gorjao - Coimbra','Enfermeiro', doencas_desconhecidas, 5).
utente(9 , 99999999999, 'Cristina', nascimento_desconhecido, 'cristina@mail.com', 930570152, 'Rua Dr. Antonio Jose de Almeida - Covilha','Medico', [], 6).
utente(10, 10101010101, 'Eva', data(3,12,1962), 'eva@mail.com', 935465241, 'Rua Assis Leao - Evora',profissao_desconhecida, [], 7).
utente(11, 11111111111, 'Rui', data(29,6,1973), 'rui@mail.com', 998773477, 'Avenida Doutor Dario Gandra Nunes - Porto',profissao_desconhecida, ['Cancro'], 2).

excecao( utente(ID , _, Nome, Nasc, Mail, Tel, Morada,Prof, D, C) ) :- 
  utente(ID, seguranca_social_desconhecida, Nome, Nasc, Mail, Tel, Morada,Prof, D, C).

excecao( utente(ID , SS, _, Nasc, Mail, Tel, Morada,Prof, D, C) ) :- 
  utente(ID, SS, nome_desconhecido, Nasc, Mail, Tel, Morada,Prof, D, C).

excecao( utente(ID , SS, Nome, _, Mail, Tel, Morada,Prof, D, C) ) :- 
  utente(ID, SS, Nome, nascimento_desconhecido, Mail, Tel, Morada,Prof, D, C).

excecao( utente(ID , SS, Nome, Nasc, _, Tel, Morada,Prof, D, C) ) :- 
  utente(ID, SS, Nome, Nasc, mail_desconhecido, Tel, Morada,Prof, D, C).

excecao( utente(ID , SS, Nome, Nasc, Mail, _, Morada,Prof, D, C) ) :- 
  utente(ID, SS, Nome, Nasc, Mail, telemovel_desconhecido, Morada,Prof, D, C).

excecao( utente(ID , SS, Nome, Nasc, Mail, Tel, _,Prof, D, C) ) :- 
  utente(ID, SS, Nome, Nasc, Mail, Tel, morada_desconhecida,Prof, D, C).

excecao( utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,_, D, C) ) :- 
  utente(ID, SS, Nome, Nasc, Mail, Tel, Morada,profissao_desconhecida, D, C).

excecao( utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,Prof, _, C) ) :- 
  utente(ID, SS, Nome, Nasc, Mail, Tel, Morada,Prof, doencas_desconhecidas, C).

excecao( utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,Prof, D, _) ) :- 
  utente(ID, SS, Nome, Nasc, Mail, Tel, Morada,Prof, D, centro_saude_desconhecido).

-utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,Prof, D, C) :- 
    nao(utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,Prof, D, C)), 
    nao(excecao(utente(ID , SS, Nome, Nasc, Mail, Tel, Morada,Prof, D, C))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado centro_saúde: ID_centro, Nome, Morada, Telefone, Email -> {V, F}

centroSaude(1, nomeCentro_desconhecido, 'Rua General Humberto Delgado', 243592604, 'posto.almeirim@synlab.pt').
centroSaude(2, 'Posto de Analises Clinicas da Amadora' , moradaCentro_desconhecida, 914155759, 'laboratorio.amadora@synlab.pt').
centroSaude(3, 'Posto de Analises Clinicas do Barreiro', 'Avenida do Bocage', 910728308, mailCentro_desconhecido).
centroSaude(4, 'Posto de Analises Clinicas de Braga', moradaCentro_desconhecida, 935465241, 'posto.ambrosio.santos@synlab.pt').
centroSaude(5, 'Posto de Analises Clinicas de Coimbra', 'Praceta Professor Robalo Cordeiro', 239701512, 'laboratorio.coimbra@synlab.pt').
centroSaude(6, 'Posto de Analises Clinicas da Covilha', 'Av. Infante D. Henrique', telemovelCentro_desconhecido, 'posto.covilha@synlab.pt').
centroSaude(7, 'Posto de Analises Clinicas de Evora', 'Praceta Horta do Bispo', telemovelCentro_desconhecido, 'laboratorio.evora@synlab.pt').

excecao(centroSaude(8,'Posto de Analises Clinicas de Lisboa', 'Av. Horta do Bispo', 239703516, 'laboratorio.lisboa@synlab.pt')).
excecao(centroSaude(8,'Posto de Analises Clinicas de Lisboa', 'Av. Infante D. Joao', 239703516, 'laboratorio.lisboa@synlab.pt')).

excecao( centroSaude(ID, _, Morada, Tel, Mail) ) :- 
  centroSaude(ID, nomeCentro_desconhecido, Morada, Tel, Mail).

excecao( centroSaude(ID, Nome, _, Tel, Mail) ) :- 
  centroSaude(ID, Nome, moradaCentro_desconhecida, Tel, Mail).

excecao( centroSaude(ID, Nome, Morada, _, Mail) ) :- 
  centroSaude(ID, Nome, Morada, telemovelCentro_desconhecido, Mail).

excecao( centroSaude(ID, Nome, Morada, Tel, _) ) :- 
  centroSaude(ID, Nome, Morada, Tel, mailCentro_desconhecido).

-centroSaude(ID, Nome, Morada, Tel, Mail) :- 
    nao(centroSaude(ID, Nome, Morada, Tel, Mail)), 
    nao(excecao(centroSaude(ID, Nome, Morada, Tel, Mail))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -	
% Extensao do predicado staff: ID_staff, ID_centro, Nome, email -> {V, F}

staff(1, 1, 'Tatiana', mailStaff_desconhecido).
staff(2, 2, 'Augusta', 'augusta@staff.com').
staff(3, 3, nomeStaff_desconhecido, mailStaff_desconhecido).
staff(4, 4, 'Cristina', 'cristina@staff.com').
staff(5, 5, 'Eva', mailStaff_desconhecido).
staff(6, centro_desconhecido, 'Joana', 'rui@staff.com').
staff(7, 7, 'Vitor', mailStaff_desconhecido).

excecao( staff(IDS, _, Nome, Mail) ) :- 
  staff(IDS, centro_desconhecido, Nome, Mail).

excecao( staff(IDS, IDC, _, Mail) ) :- 
  staff(IDS, IDC, nomeStaff_desconhecido, Mail).

excecao( staff(IDS, IDC, Nome, _) ) :- 
  staff(IDS, IDC, Nome, mailStaff_desconhecido).

-staff(1, 2, 'Tatiana', mailStaff_desconhecido).

-staff(IDS, IDC, Nome, Mail) :- 
    nao(staff(IDS, IDC, Nome, Mail)), 
    nao(excecao(staff(IDS, IDC, Nome, Mail))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado vacinação_Covid: ID_Staf, ID_utente, Data, Vacina, Toma -> {V, F}

nulo(nulo).

%Fase1
vacinacaoCovid(id_staff_desconhecido, 7, data(1,2,2021), 'astrazeneca', 1).
vacinacaoCovid(4, 8, data(1,1,2021), 'astrazeneca', 1).
vacinacaoCovid(6, 9, data(1,1,2021), 'astrazeneca', 1).

vacinacaoCovid(id_staff_desconhecido, 7, data_desconhecida, 'astrazeneca', 2).
vacinacaoCovid(4, 8, data(20,1,2021), 'astrazeneca', 2).
vacinacaoCovid(6, 9, data(20,1,2021), 'astrazeneca', 2).

%Fase2
vacinacaoCovid(2, 1, data(30,1,2021), vacina_desconhecida, 1).
vacinacaoCovid(2, 1, data(30,2,2021), vacina_desconhecida, 2).
vacinacaoCovid(9, 11, data(20,3,2021), 'astrazeneca', 1).

%Fase3
vacinacaoCovid(5, 2, data(20,10,2021), 'astrazeneca', 1). 
vacinacaoCovid(1, 3, data(20,1,2021), vacina_desconhecida, 1).
vacinacaoCovid(7, 10, data(1,1,2021), 'astrazeneca', 1).
vacinacaoCovid(7, 10, nulo, 'astrazeneca', 2).

% não foi vacinado
-vacinacaoCovid(1,7,data(1,2,2021),'astrazeneca', 1).

excecao( vacinacaoCovid(_, IDU, D, V, T) ) :- 
  vacinacaoCovid(id_staff_desconhecido, IDU, D, V, T).

excecao( vacinacaoCovid(IDS, IDU, _, V, T) ) :- 
  vacinacaoCovid(IDS, IDU, data_desconhecida, V, T).

excecao( vacinacaoCovid(IDS, IDU, D, _, T) ) :- 
  vacinacaoCovid(IDS, IDU, D, vacina_desconhecida, T).

excecao(vacinacaoCovid(IS,IU,_,V,T)) :- vacinacaoCovid(IS,IU,nulo,V,T).

-vacinacaoCovid(IDS, IDU, D, V, T) :- 
    nao(vacinacaoCovid(IDS, IDU, D, V, T)), 
    nao(excecao(vacinacaoCovid(IDS, IDU, D, V, T))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado evolucao: Termo -> {V, F}

evolucao(Termo) :- solucoes(Inv, +Termo::Inv, S),
                   insere(Termo),
                   teste(S).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado involucao: Termo -> {V, F}

involucao(Termo) :- Termo,
					solucoes(Inv, -Termo::Inv, S),
                    remove(Termo),
                    teste(S).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado teste: Lista -> {V, F}	

teste([]).
teste([H | T]) :- H, teste(T).

-teste(Lista) :- 
    nao(teste(Lista)), 
    nao(excecao(teste(Lista))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado insere: Termo -> {V, F}	

insere(Termo) :- assert(Termo).
insere(Termo) :- retract(Termo), !, fail.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado remove: Termo -> {V, F}	

remove(Termo) :- retract(Termo).
remove(Termo) :- assert(Termo), !, fail.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado faseConcluida: Lista -> {V,F}
% Verifica se todas as pessoas na lista já tomaram a 2 toma da vacina 

faseConcluida([]).
faseConcluida([(ID,_)|T]) :- vacinacaoCovid(_, ID, _, _, Toma), Toma =:= 2, faseConcluida(T).

-faseConcluida(Lista) :- 
    nao(faseConcluida(Lista)), 
    nao(excecao(faseConcluida(Lista))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado faseAtual: Fase -> {V,F}
% Verifica se a fase dada é correspondente á fase atual
% por conseguinte calcula a fase de vacinação que está a decorrer

faseAtual(N) :- fase1(F1), faseConcluida(F1), fase2(F2), faseConcluida(F2), !, N is 3.
faseAtual(N) :- fase1(F1), faseConcluida(F1), !, N is 2.
faseAtual(N) :- N is 1.

-faseAtual(N) :- 
    nao(faseAtual(N)), 
    nao(excecao(faseAtual(N))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado ultimaDataFase: Lista_Pessoas, Acumulador, Resultado -> {V,F}
% Calcula a ultima data de vacinação para uma lista de pessoas 

ultimaDataFase([],A,A).
ultimaDataFase([(ID,_)|T],A,R) :- vacinacaoCovid(_, ID, D, _, _), depois(D,A), ultimaDataFase(T,D,R).
ultimaDataFase([(ID,_)|T],A,R) :- vacinacaoCovid(_, ID, D, _, _), antes(D,A), ultimaDataFase(T,A,R).

-ultimaDataFase(Lista,A,R) :- 
    nao(ultimaDataFase(Lista,A,R)), 
    nao(excecao(ultimaDataFase(Lista,A,R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado ultimaDataFase: Fase, Data -> {V,F}
% Verifica se a data dada corresponde á data da ultima vacina dada nessa faseAtual
% por conseguinte calcula a data da ultima vacina de uma fase 

ultimaDataFase(N,R) :- pessoasCandidatas(N,P), faseConcluida(P), ultimaDataFase(P,data(1,1,1),R).

-ultimaDataFase(N,R) :- 
    nao(ultimaDataFase(N,R)), 
    nao(excecao(ultimaDataFase(N,R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -

pessoasQueTomaramXvacina(_,[],A,A).
pessoasQueTomaramXvacina(X,[(ID,N)|T],A,R) :- vacinacaoCovid(_,ID,_,X,_), nao(pertence((ID,N),A)), pessoasQueTomaramXvacina(X,T,[(ID,N)|A],R).
pessoasQueTomaramXvacina(X,[(ID,N)|T],A,R) :- vacinacaoCovid(_,ID,_,X,_), pertence((ID,N),A), pessoasQueTomaramXvacina(X,T,A,R).
pessoasQueTomaramXvacina(X,[(ID,_)|T],A,R) :- nao(vacinacaoCovid(_,ID,_,X,_)), pessoasQueTomaramXvacina(X,T,A,R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasQueTomaramXvacina: Nome_Vacina, Lista_Pessoas -> {V,F}
% verifica se todas as pessoas de uma lista tomaram a vacinda indicada
% por conseguinte determina todas as pessoas que tomaram uma determinada vacina 
pessoasQueTomaramXvacina(X,R) :- solucoes((ID,N),utente(ID,_,N,_,_,_,_,_,_,_),R1), pessoasQueTomaramXvacina(X,R1,[],R).

-pessoasQueTomaramXvacina(X,R) :- 
    nao(pessoasQueTomaramXvacina(X,R)), 
    nao(excecao(pessoasQueTomaramXvacina(X,R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado staffPessoa: Lista, Acumulador, Resultado -> {V,F}
% Constroi uma lista com todos os elementos do staff que deram vacinas numa determinada fase 

staffPessoa([],A,A).
staffPessoa([(ID1,_)|T], A, R) :- vacinacaoCovid(ID,ID1,_,_,_), staff(ID,_,N,_), nao(pertence((ID,N),A)), !, staffPessoa(T,[(ID,N)|A],R).
staffPessoa([_|T], A, R) :- staffPessoa(T,A,R).

-staffPessoa(Lista, A, R) :- 
    nao(staffPessoa(Lista, A, R)), 
    nao(excecao(staffPessoa(Lista, A, R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado staffAtivoFase: Fase, Lista_Staff -> {V,F}
% Verifica se todos os elementos do staff dado deram vacinas na fase indicada
% por conseguinte determinada todos os elementos do staff que deram vacinas na fase

staffAtivoFase(Fase,R) :- pessoasCandidatas(Fase,P), staffPessoa(P,[],R).

-staffAtivoFase(Fase,R) :- 
    nao(staffAtivoFase(Fase,R)), 
    nao(excecao(staffAtivoFase(Fase,R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteVacinadoStaff: ID_Staff, Nome_Staff, ID_Utente, Nome_Utente -> {V,F}
% Verifica se um determinado utente foi vaciando por um determinado elemento do staff

utenteVacinadoStaff(IDStaff, NStaff, IDUtente, NUtente) :- staff(IDStaff,_,NStaff,_),
										  		   		   utente(IDUtente,_,NUtente,_,_,_,_,_,_,_),
				           				    	   		   vacinacaoCovid(IDStaff,IDUtente,_,_,_).

excecao(utenteVacinadoStaff(_, _, IDUtente, _)) :- vacinacaoCovid(id_staff_desconhecido,IDUtente,_,_,_).

-utenteVacinadoStaff(IDStaff, NStaff, IDUtente, NUtente) :- 
    nao(utenteVacinadoStaff(IDStaff, NStaff, IDUtente, NUtente)), 
    nao(excecao(utenteVacinadoStaff(IDStaff, NStaff, IDUtente, NUtente))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado	pessoasVacinadasStaff: Lista -> {V,F}
% Verifica se todos os pares (Utente,Staff) estão corretamente associados
% por conseguinte determina os pares de todos os utentes vacinados 

pessoasVacinadasStaff(X) :- solucoes((NStaff,NUtente), utenteVacinadoStaff(_,NStaff,_,NUtente), X).

-pessoasVacinadasStaff(X) :- 
    nao(pessoasVacinadasStaff(X)), 
    nao(excecao(pessoasVacinadasStaff(X))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado lugarOndeVacinado: ID_Utente, ID_Centro_Saude -> {V,F}
% Determina se um utente foi vacinado num determinado centro de saude 
% por conseguinte determinada em que centro de saude um utente foi vacinado 

lugarOndeVacinado(ID, R) :- integer(ID), !, vacinacaoCovid(IDStaff,ID,_,_,_), staff(IDStaff,R,_,_).
lugarOndeVacinado(Nome, R) :- utente(ID,_,Nome,_,_,_,_,_,_,_), vacinacaoCovid(IDStaff,ID,_,_,_), staff(IDStaff,R,_,_).

excecao( lugarOndeVacinado(ID, _) ) :- vacinacaoCovid(id_staff_desconhecido,ID,_,_,_).

-lugarOndeVacinado(ID, R) :- 
    nao(lugarOndeVacinado(ID, R)), 
    nao(excecao(lugarOndeVacinado(ID, R))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: Questao,Resposta -> {V,F}
%                            Resposta = { verdadeiro,falso,desconhecido }

demo( Questao,verdadeiro ) :-
    Questao.
demo( Questao,falso ) :-
    -Questao.
demo( Questao,desconhecido ) :-
    nao( Questao ),
    nao( -Questao ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: lista de Questao,Resposta -> {V,F}
%                            Resposta = lista com { verdadeiro,falso,desconhecido }


demoLista([],A,A).
demoLista([H|T],A,R) :- demo(H,V), demoLista(T,[V|A],R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: lista de Questao,Resposta -> {V,F}
%                            Resposta = lista com { verdadeiro,falso,desconhecido }

demoLista(X,R) :- demoLista(X,[],R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado logica: valor logico 1, valor logico 2, valor logico conjunto -> {V,F}

logica(falso,falso, falso).
logica(falso,desconhecido,falso).
logica(falso,verdadeiro,falso).
logica(desconhecido,falso,falso).
logica(desconhecido,desconhecido,desconhecido).
logica(desconhecido,verdadeiro,desconhecido).
logica(verdadeiro,falso,falso).
logica(verdadeiro,desconhecido,desconhecido).
logica(verdadeiro,verdadeiro,verdadeiro). 

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: lista de Questao,Resposta -> {V,F}
%                            Resposta = { verdadeiro,falso,desconhecido }

reduzLogica([],A,A).
reduzLogica([X|T],A,R) :- logica(X,A,R1), reduzLogica(T,R1,R). 

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do meta-predicado demo: lista de Questao,Resposta -> {V,F}
%                            Resposta = { verdadeiro,falso,desconhecido }

demoListaReduce(X,R) :- demoLista(X,R1), reduzLogica(R1,verdadeiro,R).
