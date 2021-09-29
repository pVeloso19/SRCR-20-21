%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% SIST. REPR. CONHECIMENTO E RACIOCINIO - MIEI 

% GRUPO 5
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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% Não permite a inserçã ode utentes com um id que nao seja um numero, onde o numero de segurança social tenha menos de 11 digitos,
% o telefone tenha menos de 9 digitos, a data de nascimento seja invalida, a idade seja superior a 150 anos, e que ja exista um 
% utente com o mesmo ID 

+utente(ID,SS,_,DA,_,TS,_,_,_,PS) :: (integer(ID),
                                       SS >= 10000000000,
                                       SS =< 99999999999,
                                       data(DA),
                                       TS >= 100000000,
                                       TS =< 999999999,
                                       idade(DA, IDADE),
                                       IDADE > 0,
                                       IDADE =< 150,
                                       integer(PS),
                                       solucoes(ID,(utente(ID,_,_,_,_,_,_,_,_,_)),S ),
                                       comprimento( S,C ),  
				                       C == 1
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

+centroSaude(ID,_,_,T,_) :: (integer(ID),
                             T >= 100000000,
                             T =< 999999999,
                             solucoes(ID,(centroSaude(ID,_,_,_,_)),S ),
                             comprimento( S,C ),  
				             C == 1
                            ).

% não permite a remoção se existirem elementos registados no conhecimento do staff como trabalhando nesse centro

-centroSaude(ID,_,_,_,_) :: (solucoes(ID,(staff(_,ID,_,_)),S ),
                             comprimento( S,C ),  
				             C == 0
                            ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não permite a inserçaõ de um staff que trabalhe num centro de saude que nao seja conhecido, e com um id repetido

+staff(ID,IC,_,_) :: (integer(ID),
                      integer(IC),
                      centroSaude(IC,_,_,_,_),
                      solucoes(ID,(staff(ID,_,_,_)),S ),
                      comprimento( S,C ),  
				      C == 1
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

+vacinacaoCovid(IS,IU,D,V,T) :: (integer(IS),
                                 integer(IU),
                                 utente(IU,_,_,_,_,_,_,_,_,_),
                                 staff(IS,_,_,_),
                                 data(D),
                                 integer(T),
                                 T >= 0,
                                 T < 3,
                                 solucoes(IS,(vacinacaoCovid(IS,IU,D,V,T)),S ),
                                 comprimento( S,C ),  
				                 C == 1
                                ).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não devem ser inseridos valores repetidos

+profissaoPrioritaria(P) :: (solucoes(P,(profissaoPrioritaria(P)),S ),
                      		 comprimento( S,C ),  
				             C == 1
                     		).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Invariantes

% não devem ser inseridos valores repetidos

+doenca_risco(D) :: (solucoes(D,(doenca_risco(D)),S ),
                     comprimento( S,C ),  
				     C == 1
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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado nao: Termo -> {V, F}

nao(T) :- T, !, fail.
nao(_).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pertence: X, Lista -> {V, F}

pertence(X, [X|_]).
pertence(X, [H|T]) :- X \= H, pertence(X, T).

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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado antes: Data, Data -> {V,F}
% Testa se uma data ocorre antes de uma outra data

antes(data(D1,M1,A1), data(D2,M2,A2)) :- nao(depois(data(D1,M1,A1), data(D2,M2,A2))).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado profissaoPrioritaria: Profissão -> {V, F}
% Expressa o conhecimento sobre a prioridade de uma profissão. As profissoes aqui conhecidas 
% devem ser consideradas como prioritarias na vacinação

profissaoPrioritaria('Medico').
profissaoPrioritaria('Enfermeiro').

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidadatasFase1: ID_Utente, Nome_Utente -> {V, F}
% Verifica se um utente apresenta as caracteristicas para a fase 1 da vacinação

pessoasCandidadatasFase1(ID,N) :- utente(ID,_,N,_,_,_,_,P,_,_), 
								  profissaoPrioritaria(P).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase1: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 1 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 1 

fase1(X):- solucoes((ID,N), pessoasCandidadatasFase1(ID,N), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado data_atual: Data -> {V,F}

data_atual(data(18,3,2021)).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado idade: Data, Idade -> {V,F}
% Verifica/Calcula a idade de uma pessoa

idade(data(_,_,A), IDADE) :- data_atual(data(_,_,AA)), 
							 IDADE is AA-A.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado doença_risco: Doença -> {V,F}

doenca_risco('Asma').
doenca_risco('Cancro').

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado doenteRisco: Lista_Doentes -> {V,F}
% Verifica se alguma das doenças presentes na lista é considerada de risco

doenteRisco([]) :- !, fail.
doenteRisco([H|_]) :- doenca_risco(H).
doenteRisco([_|T]) :- doenteRisco(T).

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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase2: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 2 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 2 

fase2(X):- solucoes((ID,N), pessoasCandidadatasFase2(ID,N), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidadatasFase3: ID_Utente, Nome_Utente -> {V, F}
% Verifica se um utente apresenta as caracteristicas para a fase 3 da vacinação

pessoasCandidadatasFase3(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_),
								  fase1(F1),
								  fase2(F2),
								  nao(pertence((ID,N),F1)),
								  nao(pertence((ID,N),F2)).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado fase2: Lista -> {V, F}
% Verifica se na lista estão todos os utentes candidatos à fase 3 de vacinação
% por conseguinte informa todas as pessoas candidatas à fase 3 

fase3(X):- solucoes((ID,N), pessoasCandidadatasFase3(ID,N), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasCandidatas: Fase, Lista_Pessoas -> {V,F}

pessoasCandidatas(1, X) :- fase1(X).
pessoasCandidatas(2, X) :- fase2(X).
pessoasCandidatas(3, X) :- fase3(X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteVacinado: ID_Utente, Nome_Utente -> {V,F}
% Verifica se um utente já está totalmente vacinado 

utenteVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
				    	vacinacaoCovid(_, ID, _, _, T), 
						T >= 2.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasVacinadas: Lista_Pessoas -> {V,F}
% verifica se todas as pessoas na lista estão totalmente vacinadas
% por conseguinte informa todas as pessoas que estão totalmente vacinadas

pessoasVacinadas(X) :- solucoes((ID,N), utenteVacinado(ID,N), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteNaoVacinado: ID_Utente, Nome_Utente -> {V,F}
% Verifica se um utente não está vacinado
utenteNaoVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
						   nao(vacinacaoCovid(_, ID, _, _, _)).
utenteNaoVacinado(ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_), 
						   vacinacaoCovid(_, ID, _, _, 0).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasNaoVacinadas: Lista_Pessoas -> {V,F}
% verifica se todas as pessoas na lista não estão vacinadas
% por conseguinte informa todas as pessoas que não estão vacinadas

pessoasNaoVacinadas(X) :- solucoes((ID,N), utenteNaoVacinado(ID,N), X).

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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado listaVacinadosIndividamente: Fase, Lista_Pessoas, Acumulador, Resultado -> {V,F}
% Constroi uma lista com as pessoas vacinadas indevidamente 

listaVacinadosIndividamente(_,[],A,A).
listaVacinadosIndividamente(FaseAtual, [(ID,N)|Resto], A, R) :- utenteVacinadoIndevidamente(ID,N, FaseAtual), listaVacinadosIndividamente(FaseAtual, Resto, [(ID,N)|A], R).
listaVacinadosIndividamente(FaseAtual, [_|Resto], A, R) :- listaVacinadosIndividamente(FaseAtual, Resto, A, R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasVacinadasIndevidamente: Lista -> {V,F}
% Verifica dada uma lista de utentes, se todos eles foram vacinados indevidamente
% por conseguinte informa todos os utentes vacinados indevidamente

pessoasVacinadasIndevidamente(X) :- solucoes((ID,N),utente(ID,_,N,_,_,_,_,_,_,_), L),faseAtual(FaseAtual), listaVacinadosIndividamente(FaseAtual,L,[],X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteNaoVacinadoCandidato: Fase, ID_Utente, Nome_Utente -> {V,F}
% verifica se um utente é candidato para a fase atual de vacinação

utenteNaoVacinadoCandidato(FaseAtual, ID,N) :- utente(ID,_,N,_,_,_,_,_,_,_),
                                               pessoasCandidatas(FaseAtual,R),
                                               pertence((ID,N),R),
                                               nao(vacinacaoCovid(_,ID,_,_,_)).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasNaoVacinadasCandidatas: Lista -> {V,F}
% Verifica se todas as pessoas na lista são candidatas nao vacinadas à fase atual de vacinação
% por conseguinte informa todas as pessoas não vacindas candidatas 

pessoasNaoVacinadasCandidatas(X) :- faseAtual(FaseAtual), solucoes((ID, N), utenteNaoVacinadoCandidato(FaseAtual, ID,N), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasFaltaSegundaFaseVacinacao: Lista -> {V,F}
% Verifica se todas as pessoas na lista já tomaram a 1 toma da vacina mas ainda falta a segunda 
% por conseguinte informa todas as pessoas nessa situação

pessoasFaltaSegundaFaseVacinacao(X) :- solucoes((ID,N),( utente(ID,_,N,_,_,_,_,_,_,_), 
														 vacinacaoCovid(_,ID,_,_,1), 
														 nao(vacinacaoCovid(_,ID,_,_,2)) 
												       ), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utente: ID_utente, Nº Segurança_Social, Nome, Data_Nasc, Email, Telefone, Morada, Profissão, [Doenças_Crónicas], ID_CentroSaúde -> {V, F}

utente(1 , 11111111111, 'Simao', data(14,12,1972), 'simao@mail.com', 930551476, 'Largo Coronel Brito Gorjao - Mafra','Gestor', ['Asma'], 2).
utente(2 , 22222222222, 'Telmo', data(27,12,1967), 'telmo@mail.com', 961773477, 'Praca Jose Maximo da Costa - Lourinha','Engenheiro Informatico', ['Colesterol','Hipertensao'], 1).
utente(3 , 33333333333, 'Tiago', data(6,11,2000), 'tiago@mail.com', 968895013, 'Rua dos 3 Vales - Almeirim','Motorista', [], 1).
utente(4 , 44444444444, 'Vasco', data(23,6,1953), 'vasco@mail.com', 961773477, 'Largo Doutor Dario Gandra Nunes - Amadora','Consultor', ['Cancro'], 2).
utente(5 , 55555555555, 'Raul', data(9,12,1953), 'raul@mail.com', 918851034, 'Rua Real Fabrica do Vidro - Amadora','Professor', [], 2).
utente(6 , 66666666666, 'Ana', data(12,12,1933), 'ana@mail.com', 935465241, 'R. Prof. Francisco Gentil - Barreiro','Coach', [], 3).
utente(7 , 77777777777, 'Augusta', data(17,12,1982), 'augusta@mail.com', 966148612, 'Rua S. Tomas de Aquino - Braga','Medico', ['Asma'], 4).
utente(8 , 88888888888, 'Carlota', data(7,12,1980) , 'carlota@mail.com', 930568014, 'Largo Coronel Brito Gorjao - Coimbra','Enfermeiro', [], 5).
utente(9 , 99999999999, 'Cristina', data(22,12,1980), 'cristina@mail.com', 930570152, 'Rua Dr. Antonio Jose de Almeida - Covilha','Medico', [], 6).
utente(10, 10101010101, 'Eva', data(3,12,1962), 'eva@mail.com', 935465241, 'Rua Assis Leao - Evora','Enfermeiro', [], 7).
utente(11, 11111111111, 'Rui', data(29,6,1973), 'rui@mail.com', 998773477, 'Avenida Doutor Dario Gandra Nunes - Porto','Mecânico', ['Cancro'], 2).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado centro_saúde: ID_centro, Nome, Morada, Telefone, Email -> {V, F}

centroSaude(1, 'Posto de Analises Clinicas do Almeirim', 'Rua General Humberto Delgado', 243592604, 'posto.almeirim@synlab.pt').
centroSaude(2, 'Posto de Analises Clinicas da Amadora' , 'Largo Doutor Dario Gandra Nunes', 914155759, 'laboratorio.amadora@synlab.pt').
centroSaude(3, 'Posto de Analises Clinicas do Barreiro', 'Avenida do Bocage', 910728308, 'posto.venteira@synlab.pt').
centroSaude(4, 'Posto de Analises Clinicas de Braga', 'Rua Ambrosio Santos', 935465241, 'posto.ambrosio.santos@synlab.pt').
centroSaude(5, 'Posto de Analises Clinicas de Coimbra', 'Praceta Professor Robalo Cordeiro', 239701512, 'laboratorio.coimbra@synlab.pt').
centroSaude(6, 'Posto de Analises Clinicas da Covilha', 'Av. Infante D. Henrique', 275313383, 'posto.covilha@synlab.pt').
centroSaude(7, 'Posto de Analises Clinicas de Evora', 'Praceta Horta do Bispo', 266759590, 'laboratorio.evora@synlab.pt').

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado staff: ID_staff, ID_centro, Nome, email -> {V, F}

staff(1, 1, 'Tatiana', 'tatiana@staff.com').
staff(2, 2, 'Augusta', 'augusta@staff.com').
staff(3, 3, 'Carlota', 'carlota@staff.com').
staff(4, 4, 'Cristina', 'cristina@staff.com').
staff(5, 5, 'Eva', 'eva@staff.com').
staff(6, 6, 'Rui', 'rui@staff.com').
staff(7, 7, 'Vitor', 'vitor@staff.com').

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado vacinação_Covid: ID_Staf, ID_utente, Data, Vacina, Toma -> {V, F}

%Fase1
vacinacaoCovid(3, 7, data(1,2,2021), 'astrazeneca', 1).
vacinacaoCovid(4, 8, data(1,1,2021), 'astrazeneca', 1).
vacinacaoCovid(6, 9, data(1,1,2021), 'astrazeneca', 1).
vacinacaoCovid(7, 10, data(1,1,2021), 'astrazeneca', 1).

vacinacaoCovid(3, 7, data(20,2,2021), 'astrazeneca', 2).
vacinacaoCovid(4, 8, data(20,1,2021), 'astrazeneca', 2).
vacinacaoCovid(6, 9, data(20,1,2021), 'astrazeneca', 2).
vacinacaoCovid(7, 10, data(20,1,2021), 'astrazeneca', 2).

%Fase2
vacinacaoCovid(2, 1, data(10,3,2020), 'pfizer', 1).
vacinacaoCovid(2, 1, data(30,3,2021), 'pfizer', 2).
vacinacaoCovid(9, 11, data(20,3,2021), 'astrazeneca', 1).

%Fase3
vacinacaoCovid(5, 2, data(20,10,2021), 'astrazeneca', 1). 
vacinacaoCovid(1, 3, data(20,1,2021), 'astrazeneca', 1).

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

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado faseAtual: Fase -> {V,F}
% Verifica se a fase dada é correspondente á fase atual
% por conseguinte calcula a fase de vacinação que está a decorrer

faseAtual(N) :- fase1(F1), faseConcluida(F1), fase2(F2), faseConcluida(F2), !, N is 3.
faseAtual(N) :- fase1(F1), faseConcluida(F1), !, N is 2.
faseAtual(N) :- N is 1.

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado ultimaDataFase: Lista_Pessoas, Acumulador, Resultado -> {V,F}
% Calcula a ultima data de vacinação para uma lista de pessoas 

ultimaDataFase([],A,A).
ultimaDataFase([(ID,_)|T],A,R) :- vacinacaoCovid(_, ID, D, _, _), depois(D,A), ultimaDataFase(T,D,R).
ultimaDataFase([(ID,_)|T],A,R) :- vacinacaoCovid(_, ID, D, _, _), antes(D,A), ultimaDataFase(T,A,R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado ultimaDataFase: Fase, Data -> {V,F}
% Verifica se a data dada corresponde á data da ultima vacina dada nessa faseAtual
% por conseguinte calcula a data da ultima vacina de uma fase 

ultimaDataFase(N,R) :- pessoasCandidatas(N,P), faseConcluida(P), ultimaDataFase(P,data(1,1,1),R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado pessoasQueTomaramXvacina: Nome_Vacina, Lista_Pessoas -> {V,F}
% verifica se todas as pessoas de uma lista tomaram a vacinda indicada
% por conseguinte determina todas as pessoas que tomaram uma determinada vacina 
pessoasQueTomaramXvacina(X,R) :- solucoes((ID,N),(utente(ID,_,N,_,_,_,_,_,_,_),vacinacaoCovid(_,ID,_,X,_)),R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado staffPessoa: Lista, Acumulador, Resultado -> {V,F}
% Constroi uma lista com todos os elementos do staff que deram vacinas numa determinada fase 

staffPessoa([],A,A).
staffPessoa([(ID1,_)|T], A, R) :- vacinacaoCovid(ID,ID1,_,_,_), staff(ID,_,N,_), nao(pertence((ID,N),A)), !, staffPessoa(T,[(ID,N)|A],R).
staffPessoa([_|T], A, R) :- staffPessoa(T,A,R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado staffAtivoFase: Fase, Lista_Staff -> {V,F}
% Verifica se todos os elementos do staff dado deram vacinas na fase indicada
% por conseguinte determinada todos os elementos do staff que deram vacinas na fase

staffAtivoFase(Fase,R) :- pessoasCandidatas(Fase,P), staffPessoa(P,[],R).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado utenteVacinadoStaff: ID_Staff, Nome_Staff, ID_Utente, Nome_Utente -> {V,F}
% Verifica se um determinado utente foi vaciando por um determinado elemento do staff

utenteVacinadoStaff(IDStaff, NStaff, IDUtente, NUtente) :- staff(IDStaff,_,NStaff,_),
										  		   		   utente(IDUtente,_,NUtente,_,_,_,_,_,_,_),
				           				    	   		   vacinacaoCovid(IDStaff,IDUtente,_,_,_).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado	pessoasVacinadasStaff: Lista -> {V,F}
% Verifica se todos os pares (Utente,Staff) estão corretamente associados
% por conseguinte determina os pares de todos os utentes vacinados 

pessoasVacinadasStaff(X) :- solucoes((NStaff,NUtente), utenteVacinadoStaff(_,NStaff,_,NUtente), X).

%--------------------------------- - - - - - - - - - -  -  -  -  -   -
% Extensao do predicado lugarOndeVacinado: ID_Utente, ID_Centro_Saude -> {V,F}
% Determina se um utente foi vacinado num determinado centro de saude 
% por conseguinte determinada em que centro de saude um utente foi vacinado 

lugarOndeVacinado(ID, R) :- integer(ID), !, vacinacaoCovid(IDStaff,ID,_,_,_), staff(IDStaff,R,_,_).
lugarOndeVacinado(Nome, R) :- utente(ID,_,Nome,_,_,_,_,_,_,_), vacinacaoCovid(IDStaff,ID,_,_,_), staff(IDStaff,R,_,_).