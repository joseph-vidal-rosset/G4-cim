%  G4-mic:  Automated theorem prover for minimal, intuitionistic and classical logic
%  with nanoCop 2.0 validation
% Copyright (C) 2025 Joseph Vidal-Rosset
%
% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.
%
% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.
%
% You should have received a copy of the GNU General Public License
% along with this program.  If not, see <https://www.gnu.org/licenses/>.

% =========================================================================
% MODULES
% =========================================================================
% CRITICAL: Enable occurs_check globally to prevent circular term structures
: - use_module(library(lists)).
:- use_module(library(statistics)).
:- use_module(library(terms)).
:- ['o_g4mic_nanoCop_operators'].
:- ['i_g4mic_prover'].
:- ['ii_g4mic_sc-g4_printer'].
:- ['iii_g4mic_common_nd_printing'].
:- ['iv_g4mic_nd_flag_style_printer'].
:- ['v_g4mic_nd_tree_style_printer'].
:- ['vi_g4mic_latex_utilities'].
:- ['vii_g4mic_logic_level_detection'].

% =========================================================================
% STARTUP BANNER
 % =========================================================================
% Disable automatic SWI-Prolog banner
:- set_prolog_flag(verbose, silent).

%
:- initialization(show_banner).

show_banner :-
    write('Welcome to SWI-Prolog (32 bits, version 9.3.34-20-g3517bc35f)'),nl,
    write('SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.'),nl,
    write('For legal details and online help, see https://www.swi-prolog.org'),nl,nl,

    write('╔═══════════════════════════════════════════════════════════════════╗'), nl,
    write('║                                                                   ║'), nl,
    write('🎓🎓🎓  nanoCop 2.0 & G4-mic v1.0: First-Order Logic Provers   🎓🎓🎓 '), nl,
    write('🎓🎓🎓🎓    (minimal, intuitionistic and classical logic)    🎓🎓🎓🎓'), nl,
    write('║                                                                   ║'), nl,
    write('╠═══════════════════════════════════════════════════════════════════╣'), nl,
    write('║                                                                   ║'), nl,
    write('⚠️⚠️⚠️ IMPORTANT: ALWAYS CHECK YOUR INPUT & OUTPUT  CAREFULLY! ⚠️⚠️⚠️ '), nl,
    write('║                                                                   ║'), nl,
    write('║      Your formula MUST follow the correct syntax (type help.)     ║'), nl,
    write('║                                                                   ║'), nl,
    write('╠═══════════════════════════════════════════════════════════════════╣'), nl,
    write('║                                                                   ║'), nl,
    write('║   📝  Usage:                                                      ║'), nl,
    write('║     • prove(Formula).        → proof in 3 styles + validation     ║'), nl,
    write('║     • g4mic_decides(Formula) → concise mode                       ║'), nl,
    write('║     • decide(Formula)        → alias for g4mic_decides            ║'), nl,
    write('║     • nanoCop_decides(F)     → test Formula with nanoCop only     ║'), nl,
    write('║     • help.                  → show detailed help                 ║'), nl,
    write('║     • examples.              → show formula examples              ║'), nl,
    write('║                                                                   ║'), nl,
    write('║   💡  Remember: End each request with a dot!                      ║'), nl,
    write('║                                                                   ║'), nl,
    write('╚═══════════════════════════════════════════════════════════════════╝'), nl,
    nl.



% =========================================================================
% nanoCop
% =========================================================================
/*
% nanoCop_decides/1 - Wrapper that handles equality axioms
nanoCop_decides(Formula) :-
    % Check if formula contains equality
    ( contains_equality_symbol(Formula) ->
        % Add equality axioms before proving
        leancop_equal(Formula, FormulaWithEq),
        prove(FormulaWithEq, _Proof)
    ;
        % No equality, prove directly
        prove(Formula, _Proof)
    ).

% Helper:  check if formula contains = (equality symbol)
contains_equality_symbol(_ = _) :- !.
contains_equality_symbol(~F) :- !, contains_equality_symbol(F).
contains_equality_symbol(F1 & F2) :- !,
    (contains_equality_symbol(F1) ; contains_equality_symbol(F2)).
contains_equality_symbol(F1 | F2) :- !,
    (contains_equality_symbol(F1) ; contains_equality_symbol(F2)).
contains_equality_symbol(F1 => F2) :- !,
    (contains_equality_symbol(F1) ; contains_equality_symbol(F2)).
contains_equality_symbol(F1 <=> F2) :- !,
    (contains_equality_symbol(F1) ; contains_equality_symbol(F2)).
contains_equality_symbol(![_]: F) :- !, contains_equality_symbol(F).
contains_equality_symbol(? [_]:F) :- !, contains_equality_symbol(F).
contains_equality_symbol(all _: F) :- !, contains_equality_symbol(F).
contains_equality_symbol(ex _: F) :- !, contains_equality_symbol(F).
contains_equality_symbol(_) :- fail.
*/

test_loading :-
    format('=== DIAGNOSTIQUE nanoCoP ===~n'),

    % Vérifier les fichiers
    format('1. Vérification des fichiers:~n'),
    Files = ['operators.pl', 'nanocop20_swi.pl', 'nanocop20.pl', 'nanocop_proof.pl'],
    forall(member(F, Files),
           (exists_file(F) ->
              format('  ✓ ~w trouvé~n', [F]) ;
              format('  ✗ ~w MANQUANT~n', [F]))),

    % Tenter le chargement manuel
    format('~nanoCop_deciden2. Tentative de chargement manuel:~n'),
    (exists_file('nanocop20_swi.pl') ->
        (format('  Chargement de nanocop20_swi.pl...~n'),
         catch([nanocop20_swi], E, (format('  ERREUR: ~w~n', [E]), fail))) ;
     exists_file('nanocop20.pl') ->
        (format('  Chargement de nanocop20.pl...~n'),
         catch([nanocop20], E, (format('  ERREUR: ~w~n', [E]), fail))) ;
        format('  Aucun fichier nanoCoP trouvé!~n')
    ),

    % Vérifier les prédicats
    format('~n3. Vérification des prédicats:~n'),
    Preds = [prove/2, prove2/3, bmatrix/3],
    forall(member(P, Preds),
           (current_predicate(P) ->
              format('  ✓ ~w disponible~n', [P]) ;
              format('  ✗ ~w MANQUANT~n', [P]))),

    % Test simple si possible
    format('~n4. Test simple:~n'),
    (current_predicate(prove/2) ->
        (format('  Test de prove(p, Proof)...~n'),
         (prove(p, _) ->
            format('  ✓ Test réussi~n') ;
            format('  ✗ Test échoué (normal pour ~p)~n', [p]))) ;
        format('  Impossible: prove/2 non disponible~n')
    ),

    format('~n=== FIN DIAGNOSTIQUE ===~n').

% Test rapide
quick_test :-
    [operators],
    format('Operators chargé~n'),
    (exists_file('nanocop20_swi.pl') ->
        ([nanocop20_swi], format('nanocop20_swi chargé~n')) ;
        format('nanocop20_swi non trouvé~n')),
    (current_predicate(prove/2) ->
        format('prove/2 disponible~n') ;
        format('prove/2 NON disponible~n')).

%% File: nanocop20_swi.pl  -  Version: 2.0  -  Date: 1 May 2021
%%
%% Purpose: nanoCoP: A Non-clausal Connection Prover
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage:   prove(F,P).  % where F is a first-order formula, e.g.
%%                       %  F=((p,all X:(p=>q(X)))=>all Y:q(Y))
%%                       %  and P is the returned connection proof
%%
%% Copyright: (c) 2016-2021 by Jens Otten
%% License:   GNU General Public License

:- set_prolog_flag(occurs_check,true).  % global occurs check on

:- dynamic(pathlim/0), dynamic(lit/4).

% definitions of logical connectives and quantifiers

% :- op(1130,xfy,<=>). :- op(1110,xfy,=>). :- op(500, fy,'~').
% :- op( 500, fy,all). :- op( 500, fy,ex). :- op(500,xfy,:).

% :- [operators].
% -----------------------------------------------------------------
% prove(F,Proof) - prove formula F

prove(F,Proof) :- prove2(F,[cut,comp(7)],Proof).

prove2(F,Set,Proof) :-
    bmatrix(F,Set,Mat), retractall(lit(_,_,_,_)),
    assert_matrix(Mat), prove(Mat,1,Set,Proof).

% start rule
prove(Mat,PathLim,Set,[(I^0)^V:Proof]) :-
    ( member(scut,Set) -> ( append([(I^0)^V:Cla1|_],[!|_],Mat) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) -> true ;
        ( append(MatC,[!|_],Mat) -> member((I^0)^V:Cla1,MatC) ;
        member((I^0)^V:Cla,Mat), positiveC(Cla,Cla1) ) ),
    prove(Cla1,Mat,[],[I^0],PathLim,[],Set,Proof).

prove(Mat,PathLim,Set,Proof) :-
    retract(pathlim) ->
    ( member(comp(PathLim),Set) -> prove(Mat,1,[],Proof) ;
      PathLim1 is PathLim+1, prove(Mat,PathLim1,Set,Proof) ) ;
    member(comp(_),Set) -> prove(Mat,1,[],Proof).

% axiom
prove([],_,_,_,_,_,_,[]).

% decomposition rule
prove([J:Mat1|Cla],MI,Path,PI,PathLim,Lem,Set,Proof) :-
    !, member(I^V:Cla1,Mat1),
    prove(Cla1,MI,Path,[I,J|PI],PathLim,Lem,Set,Proof1),
    prove(Cla,MI,Path,PI,PathLim,Lem,Set,Proof2),
    Proof=[J:I^V:Proof1|Proof2].

% reduction and extension rules
prove([Lit|Cla],MI,Path,PI,PathLim,Lem,Set,Proof) :-
    Proof=[Lit,I^V:[NegLit|Proof1]|Proof2],
    \+ (member(LitC,[Lit|Cla]), member(LitP,Path), LitC==LitP),
    (-NegLit=Lit;-Lit=NegLit) ->
       ( member(LitL,Lem), Lit==LitL, _ClaB1=[], Proof1=[],I=l,V=[]
         ;
         member(NegL,Path), unify_with_occurs_check(NegL,NegLit),
         _ClaB1=[], Proof1=[],I=r,V=[]
         ;
         lit(NegLit,ClaB,Cla1,Grnd1),
         ( Grnd1=g -> true ; length(Path,K), K<PathLim -> true ;
           \+ pathlim -> assert(pathlim), fail ),
         prove_ec(ClaB,Cla1,MI,PI,I^V:ClaB1,MI1),
         prove(ClaB1,MI1,[Lit|Path],[I|PI],PathLim,Lem,Set,Proof1)
       ),
       ( member(cut,Set) -> ! ; true ),
       prove(Cla,MI,Path,PI,PathLim,[Lit|Lem],Set,Proof2).

% extension clause (e-clause)
prove_ec((I^K)^V:ClaB,IV:Cla,MI,PI,ClaB1,MI1) :-
    append(MIA,[(I^K1)^V1:Cla1|MIB],MI), length(PI,K),
    ( ClaB=[J^K:[ClaB2]|_], member(J^K1,PI),
      unify_with_occurs_check(V,V1), Cla=[_:[Cla2|_]|_],
      append(ClaD,[J^K1:MI2|ClaE],Cla1),
      prove_ec(ClaB2,Cla2,MI2,PI,ClaB1,MI3),
      append(ClaD,[J^K1:MI3|ClaE],Cla3),
      append(MIA,[(I^K1)^V1:Cla3|MIB],MI1)
      ;
      (\+member(I^K1,PI);V\==V1) ->
      ClaB1=(I^K)^V:ClaB, append(MIA,[IV:Cla|MIB],MI1) ).

% -----------------------------------------------------------------
% positiveC(Clause,ClausePos) - generate positive start clause

positiveC([],[]).
positiveC([M|C],[M3|C2]) :-
    ( M=I:M1 -> positiveM(M1,M2),M2\=[],M3=I:M2 ; -_\=M,M3=M ),
    positiveC(C,C2).

positiveM([],[]).
positiveM([I:C|M],M1) :-
    ( positiveC(C,C1) -> M1=[I:C1|M2] ; M1=M2 ), positiveM(M,M2).

% -----------------------------------------------------------------
% bmatrix(Formula,Set,Matrix) - generate indexed matrix

bmatrix(F,Set,M) :-
    univar(F,[],F1),
    ( member(conj,Set), F1=(A=>C) ->
        bmatrix(A,1,MA,[],[],_,1,J,_),
        bmatrix(C,0,MC,[],[],_,J,_,_), ( member(reo(I),Set) ->
        reorderC([MA],[_:MA1],I), reorderC([MC],[_:MC1],I) ;
        _:MA1=MA, _:MC1=MC ), append(MC1,[!|MA1],M)
      ; bmatrix(F1,0,M1,[],[],_,1,_,_), ( member(reo(I),Set) ->
        reorderC([M1],[_:M],I) ; _:M=M1 ) ).

%% Ajout
bmatrix(![X]:F1, Pol, M, FreeV, FV, Paths, I, I1, K) :- !,
    bmatrix(all X:F1, Pol, M, FreeV, FV, Paths, I, I1, K).

bmatrix(?[X]:F1, Pol, M, FreeV, FV, Paths, I, I1, K) :- !,
    bmatrix(ex X:F1, Pol, M, FreeV, FV, Paths, I, I1, K).
%%% fin de l'ajout

bmatrix((F1<=>F2),Pol,M,FreeV,FV,Paths,I,I1,K) :- !,
    bmatrix(((F1=>F2),(F2=>F1)),Pol,M,FreeV,FV,Paths,I,I1,K).

bmatrix((~F),Pol,M,FreeV,FV,Paths,I,I1,K) :- !,
    Pol1 is (1-Pol), bmatrix(F,Pol1,M,FreeV,FV,Paths,I,I1,K).

bmatrix(F,Pol,M,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(uni,C,Pol), !,
    bmatrix(F1,Pol,M,FreeV,[X|FV],Paths,I,I1,K).

bmatrix(F,Pol,M,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,X:F1], bma(exist,C,Pol), !,
    append(FreeV,FV,FreeV1), I2 is I+1,
    copy_term((X,F1,FreeV1),((I^FreeV1),F2,FreeV1)),
    bmatrix(F2,Pol,M,FreeV,FV,Paths,I2,I1,K).

bmatrix(F,Pol,J^K:M3,FreeV,FV,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(alpha,C,Pol,Pol1,Pol2), !,
    bmatrix(F1,Pol1,J^K:M1,FreeV,FV,Paths1,I,I2,K),
    bmatrix(F2,Pol2,_:M2,FreeV,FV,Paths2,I2,I1,K),
    Paths is Paths1*Paths2,
    (Paths1>Paths2 -> append(M2,M1,M3) ; append(M1,M2,M3)).

bmatrix(F,Pol,I^K:[(I2^K)^FV1:C3],FreeV,FV,Paths,I,I1,K) :-
    F=..[C,F1,F2], bma(beta,C,Pol,Pol1,Pol2), !,
    ( FV=[] -> FV1=FV, F3=F1, F4=F2 ;
      copy_term((FV,F1,F2,FreeV),(FV1,F3,F4,FreeV)) ),
    append(FreeV,FV1,FreeV1),  I2 is I+1, I3 is I+2,
    bmatrix(F3,Pol1,M1,FreeV1,[],Paths1,I3,I4,K),
    bmatrix(F4,Pol2,M2,FreeV1,[],Paths2,I4,I1,K),
    Paths is Paths1+Paths2,
    ( (M1=_:[_^[]:C1];[M1]=C1), (M2=_:[_^[]:C2];[M2]=C2) ->
      (Paths1>Paths2 -> append(C2,C1,C3) ; append(C1,C2,C3)) ).

bmatrix(A,0,I^K:[(I2^K)^FV1:[A1]],FreeV,FV,1,I,I1,K)  :-
    copy_term((FV,A,FreeV),(FV1,A1,FreeV)), I2 is I+1, I1 is I+2.

bmatrix(A,1,I^K:[(I2^K)^FV1:[-A1]],FreeV,FV,1,I,I1,K) :-
    copy_term((FV,A,FreeV),(FV1,A1,FreeV)), I2 is I+1, I1 is I+2.

bma(alpha,',',1,1,1). bma(alpha,(;),0,0,0). bma(alpha,(=>),0,1,0).
bma(beta,',',0,0,0).  bma(beta,(;),1,1,1).  bma(beta,(=>),1,0,1).
bma(exist,all,0). bma(exist,ex,1). bma(uni,all,1). bma(uni,ex,0).

% -----------------------------------------------------------------
% assert_matrix(Matrix) - write matrix into Prolog's database

assert_matrix(M) :-
    member(IV:C,M), assert_clauses(C,IV:ClaB,ClaB,IV:ClaC,ClaC).
assert_matrix(_).

assert_clauses(C,ClaB,ClaB1,ClaC,ClaC1) :- !,
    append(ClaD,[M|ClaE],C),
    ( M=J:Mat -> append(MatA,[IV:Cla|MatB],Mat),
                 append([J:[IV:ClaB2]|ClaD],ClaE,ClaB1),
                 append([IV:ClaC2|MatA],MatB,Mat1),
                 append([J:Mat1|ClaD],ClaE,ClaC1),
                 assert_clauses(Cla,ClaB,ClaB2,ClaC,ClaC2)
               ; append(ClaD,ClaE,ClaB1), ClaC1=C,
                 (ground(C) -> Grnd=g ; Grnd=n),
                 assert(lit(M,ClaB,ClaC,Grnd)), fail ).

% -----------------------------------------------------------------
%  reorderC([Matrix],[MatrixReo],I) - reorder clauses

reorderC([],[],_).
reorderC([M|C],[M1|C1],I) :-
    ( M=J:M2 -> reorderM(M2,M3,I), length(M2,L), K is I mod (L*L),
      mreord(M3,M4,K), M1=J:M4 ; M1=M ), reorderC(C,C1,I).

reorderM([],[],_).
reorderM([J:C|M],[J:D|M1],I) :- reorderC(C,D,I), reorderM(M,M1,I).

mreord(M,M,0) :- !.
mreord(M,M1,I) :-
    mreord1(M,I,X,Y), append(Y,X,M2), I1 is I-1, mreord(M2,M1,I1).

mreord1([],_,[],[]).
mreord1([C|M],A,M1,M2) :-
    B is 67*A, I is B rem 101, I1 is I mod 2,
    ( I1=1 -> M1=[C|X], M2=Y ; M1=X, M2=[C|Y] ), mreord1(M,I,X,Y).

% ----------------------------
% create unique variable names

univar(X,_,X)  :- (atomic(X);var(X);X==[[]]), !.
univar(F,Q,F1) :-
    F=..[A,B|T], ( (A=ex;A=all),B=X:C -> delete2(Q,X,Q1),
    copy_term((X,C,Q1),(Y,D,Q1)), univar(D,[Y|Q],E), F1=..[A,Y:E] ;
    univar(B,Q,B1), univar(T,Q,T1), F1=..[A,B1|T1] ).

% delete variable from list
delete2([],_,[]).
delete2([X|T],Y,T1) :- X==Y, !, delete2(T,Y,T1).
delete2([X|T],Y,[X|T1]) :- delete2(T,Y,T1).

%% File: nanocop_tptp2.pl  -  Version: 1.0  -  Date: 16 January 2016
%%
%% Purpose: 1. Translate formula from TPTP into leanCoP syntax
%%          2. Add equality axioms to the given formula
%%
%% Author:  Jens Otten
%% Web:     www.leancop.de/nanocop/
%%
%% Usage: leancop_tptp2(X,F). % where X is a problem file using TPTP
%%                            %  syntax and F the translated formula
%%        leancop_equal(F,G). % where F is a formula and G the
%%                            %  formula with added equality axioms
%%
%% Copyright: (c) 2009-2016 by Jens Otten
%% License:   GNU General Public License


% definitions of logical connectives and quantifiers

% leanCoP syntax
/*
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
%                      % disjunction (;)
%                      % conjunction (,)
:- op( 500, fy, ~).    % negation
:- op( 500, fy, all).  % universal quantifier
:- op( 500, fy, ex).   % existential quantifier
:- op( 500,xfy, :).

% TPTP syntax
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, =).    % equality
:- op( 300, xf, !).     % negated equality (for !=)
:- op( 299, fx, $).     % for $true/$false
*/
% TPTP syntax to leanCoP syntax mapping

op_tptp2((A<=>B),(A1<=>B1),   [A,B],[A1,B1]).
op_tptp2((A<~>B),~((A1<=>B1)),[A,B],[A1,B1]).
op_tptp2((A=>B),(A1=>B1),     [A,B],[A1,B1]).
op_tptp2((A<=B),(B1=>A1),     [A,B],[A1,B1]).
op_tptp2((A|B),(A1;B1),       [A,B],[A1,B1]).
op_tptp2((A'~|'B),~((A1;B1)), [A,B],[A1,B1]).
op_tptp2((A&B),(A1,B1),       [A,B],[A1,B1]).
op_tptp2((A~&B),~((A1,B1)),   [A,B],[A1,B1]).
op_tptp2(~A,~A1,[A],[A1]).
op_tptp2((! [V]:A),(all V:A1),     [A],[A1]).
op_tptp2((! [V|Vars]:A),(all V:A1),[! Vars:A],[A1]).
op_tptp2((? [V]:A),(ex V:A1),      [A],[A1]).
op_tptp2((? [V|Vars]:A),(ex V:A1), [? Vars:A],[A1]).
op_tptp2($true,(true___=>true___),      [],[]).
op_tptp2($false,(false___ , ~ false___),[],[]).
op_tptp2(A=B,~(A1=B),[],[]) :- \+var(A), A=(A1!).
op_tptp2(P,P,[],[]).

%%% translate into leanCoP syntax

leancop_tptp2(File,F) :- leancop_tptp2(File,'',[_],F,_).

leancop_tptp2(File,AxPath,AxNames,F,Con) :-
    open(File,read,Stream), ( fof2cop(Stream,AxPath,AxNames,A,Con)
    -> close(Stream) ; close(Stream), fail ),
    ( Con=[] -> F=A ; A=[] -> F=Con ; F=(A=>Con) ).

fof2cop(Stream,AxPath,AxNames,F,Con) :-
    read(Stream,Term),
    ( Term=end_of_file -> F=[], Con=[] ;
      ( Term=..[fof,Name,Type,Fml|_] ->
        ( \+member(Name,AxNames) -> true ; fml2cop([Fml],[Fml1]) ),
        ( Type=conjecture -> Con=Fml1 ; Con=Con1 ) ;
        ( Term=include(File), AxNames2=[_] ;
          Term=include(File,AxNames2) ) -> name(AxPath,AL),
          name(File,FL), append(AL,FL,AxL), name(AxFile,AxL),
          leancop_tptp2(AxFile,'',AxNames2,Fml1,_), Con=Con1
      ), fof2cop(Stream,AxPath,AxNames,F1,Con1),
      ( Term=..[fof,N,Type|_], (Type=conjecture;\+member(N,AxNames))
      -> (F1=[] -> F=[] ; F=F1) ; (F1=[] -> F=Fml1 ; F=(Fml1,F1)) )
    ).

fml2cop([],[]).
fml2cop([F|Fml],[F1|Fml1]) :-
    op_tptp2(F,F1,FL,FL1) -> fml2cop(FL,FL1), fml2cop(Fml,Fml1).


%%% add equality axioms

leancop_equal(F,F1) :-
    collect_predfunc([F],PL,FL), append(PL2,[(=,2)|PL3],PL),
    append(PL2,PL3,PL1) -> basic_equal_axioms(F0),
    subst_pred_axioms(PL1,F2), (F2=[] -> F3=F0 ; F3=(F0,F2)),
    subst_func_axioms(FL,F4), (F4=[] -> F5=F3 ; F5=(F3,F4)),
    ( F=(A=>C) -> F1=((F5,A)=>C) ; F1=(F5=>F) ) ; F1=F.

basic_equal_axioms(F) :-
    F=(( all X:(X=X) ),
       ( all X:all Y:((X=Y)=>(Y=X)) ),
       ( all X:all Y:all Z:(((X=Y),(Y=Z))=>(X=Z)) )).

% generate substitution axioms

subst_pred_axioms([],[]).
subst_pred_axioms([(P,I)|PL],F) :-
    subst_axiom(A,B,C,D,E,I), subst_pred_axioms(PL,F1), P1=..[P|C],
    P2=..[P|D], E=(B,P1=>P2), ( F1=[] -> F=A ; F=(A,F1) ).

subst_func_axioms([],[]).
subst_func_axioms([(P,I)|FL],F) :-
    subst_axiom(A,B,C,D,E,I), subst_func_axioms(FL,F1), P1=..[P|C],
    P2=..[P|D], E=(B=>(P1=P2)), ( F1=[] -> F=A ; F=(A,F1) ).

subst_axiom((all X:all Y:E),(X=Y),[X],[Y],E,1).
subst_axiom(A,B,[X|C],[Y|D],E,I) :-
    I>1, I1 is I-1, subst_axiom(A1,B1,C,D,E,I1),
    A=(all X:all Y:A1), B=((X=Y),B1).

% collect predicate & function symbols

collect_predfunc([],[],[]).
collect_predfunc([F|Fml],PL,FL) :-
    ( ( F=..[<=>|F1] ; F=..[=>|F1] ; F=..[;|F1] ; F=..[','|F1] ;
        F=..[~|F1] ; (F=..[all,_:F2] ; F=..[ex,_:F2]), F1=[F2] ) ->
      collect_predfunc(F1,PL1,FL1) ; F=..[P|Arg], length(Arg,I),
      I>0 ->  PL1=[(P,I)], collect_func(Arg,FL1) ; PL1=[], FL1=[] ),
    collect_predfunc(Fml,PL2,FL2),
    union1(PL1,PL2,PL), union1(FL1,FL2,FL).

collect_func([],[]).
collect_func([F|FunL],FL) :-
    ( \+var(F), F=..[F1|Arg], length(Arg,I), I>0 ->
      collect_func(Arg,FL1), union1([(F1,I)],FL1,FL2) ; FL2=[] ),
    collect_func(FunL,FL3), union1(FL2,FL3,FL).

union1([],L,L).
union1([H|L1],L2,L3) :- member(H,L2), !, union1(L1,L2,L3).
union1([H|L1],L2,[H|L3]) :- union1(L1,L2,L3).
%%% End of nanocop_tptp
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% File: minimal_driver.pl  -  Version: 2.3
%%
%% Purpose: Minimal interface for nanoCoP with automatic equality support
%% Usage:   nanoCop_decides(Formula).
%%
%% Author: Joseph Vidal-Rosset
%% Based on: nanoCoP by Jens Otten
%% Fix: Added proper translation for # (bottom/falsum)
%% Fix v2.3: Isolated occurs_check flag to prevent interference with g4mic
% =========================================================================
% =========================================================================
% LOADING REQUIRED MODULES
% =========================================================================
/*
% :- catch([operators], _, true).
:- catch([system_check], _, true).

% Load nanoCoP core
:- catch([nanocop20_swi], _,
    % catch([nanocop20], _,
        format('WARNING: nanoCoP core not found!~n')).


% CRITICAL: Load nanocop_tptp2 for equality axioms
:- catch([nanocop_tptp2], _,
    format('WARNING: nanocop_tptp2 not found - equality support disabled!~n')).
*/
% =========================================================================
% MAIN INTERFACE with EQUALITY SUPPORT and FLAG ISOLATION
% =========================================================================
%% nanoCop_decides(+Formula) - Prove formula with automatic equality axioms
%%
%% CRITICAL: This predicate manages occurs_check flag:
%% - nanoCop requires occurs_check=true (set by its module load)
%% - g4mic requires occurs_check=false (default Prolog behavior)
%% - We force false during setup, restore to true only during nanoCop call
nanoCop_decides(Formula) :-
    % Save current state (will be true if nanoCop module is loaded)
    current_prolog_flag(occurs_check, OriginalOccursCheck),

    % CRITICAL: Force occurs_check=false IMMEDIATELY for formula processing
    % This ensures translation and preprocessing happen with correct flag
    set_prolog_flag(occurs_check, false),

    % Use setup_call_cleanup to guarantee proper flag management
    setup_call_cleanup(
        % Setup: Set occurs_check=true for nanoCop
        set_prolog_flag(occurs_check, true),
        % Call: execute nanoCop proof
        nanocop_prove_core(Formula),
        % Cleanup: Restore to false (g4mic-safe state)
        set_prolog_flag(occurs_check, false)
    ),

    % Final cleanup: restore original state
    set_prolog_flag(occurs_check, OriginalOccursCheck).

%% nanocop_prove_core(+Formula) - Core nanoCop logic
%% Assumes occurs_check=true is already set
nanocop_prove_core(Formula) :-
    % Step 1: Detect equality BEFORE translation
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    % Step 2: Translate formula (![X]:  → all X:)
    translate_formula(Formula, InternalFormula),

    % Step 3: Add equality axioms AFTER translation (if needed)
    (HasEquality = true ->
        (current_predicate(leancop_equal/2) ->
            leancop_equal(InternalFormula, TempFormula),
            (InternalFormula \= TempFormula ->
                format('~n[Equality detected - axioms added by leancop_equal]~n'),
                FormulaWithEq = TempFormula
            ;
                format('~n[Equality detected - using basic axioms (leancop_equal failed)]~n'),
                basic_equality_axioms(EqAxioms),
                FormulaWithEq = (EqAxioms => InternalFormula)
            )
        ;
            format('~n[Equality detected - using basic axioms]~n'),
            basic_equality_axioms(EqAxioms),
            FormulaWithEq = (EqAxioms => InternalFormula)
        )
    ;
        FormulaWithEq = InternalFormula
    ),

    % Step 4: Prove (occurs_check is true here)
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
    !.

% =========================================================================
% INTERNAL NANOCOP LOGIC (isolated from flag pollution)
% =========================================================================
%% nanocop_prove_isolated(+Formula) - Internal predicate with nanoCop logic
nanocop_prove_isolated(Formula) :-
    % Step 1: Detect equality BEFORE translation
    (nanocop_contains_equality(Formula) ->
        HasEquality = true
    ;
        HasEquality = false
    ),

    % Step 2: Translate formula (![X]:  → all X:)
    translate_formula(Formula, InternalFormula),

    % Step 3: Add equality axioms AFTER translation (if needed)
    (HasEquality = true ->
        (current_predicate(leancop_equal/2) ->
            % Try leancop_equal first
            leancop_equal(InternalFormula, TempFormula),
            % Check if axioms were actually added
            (InternalFormula \= TempFormula ->
                format('~n[Equality detected - axioms added by leancop_equal]~n'),
                FormulaWithEq = TempFormula
            ;
                % Fallback:  leancop_equal failed, use basic axioms
                format('~n[Equality detected - using basic axioms (leancop_equal failed)]~n'),
                basic_equality_axioms(EqAxioms),
                FormulaWithEq = (EqAxioms => InternalFormula)
            )
        ;
            % leancop_equal not available
            format('~n[Equality detected - using basic axioms]~n'),
            basic_equality_axioms(EqAxioms),
            FormulaWithEq = (EqAxioms => InternalFormula)
        )
    ;
        % No equality detected
        FormulaWithEq = InternalFormula
    ),

    % Step 4: Prove (occurs_check is already true from nanoCop module load)
    time(prove2(FormulaWithEq, [cut,comp(7)], _Proof)),
    !.

% =========================================================================
% EQUALITY DETECTION
% =========================================================================

nanocop_contains_equality((_ = _)) :- !.

nanocop_contains_equality(~A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(A & B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A | B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A => B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(A <=> B) :- !,
    (nanocop_contains_equality(A) ; nanocop_contains_equality(B)).

nanocop_contains_equality(![_]: A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(? [_]:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(all _:A) :- !,
    nanocop_contains_equality(A).

nanocop_contains_equality(ex _:A) :- !,
    nanocop_contains_equality(A).

% Compound terms (check arguments recursively)
nanocop_contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    nanocop_contains_equality(Arg), !.

% Base case: no equality
nanocop_contains_equality(_) :- fail.

% =========================================================================
% BASIC EQUALITY AXIOMS
% =========================================================================

%% basic_equality_axioms(-Axioms)
%% The three fundamental equality axioms
basic_equality_axioms((
    (all X:(X=X)),                                      % Reflexivity
    (all X:all Y:((X=Y)=>(Y=X))),                      % Symmetry
    (all X:all Y:all Z:(((X=Y),(Y=Z))=>(X=Z)))         % Transitivity
)).

% =========================================================================
% FORMULA TRANSLATION
% =========================================================================

%% translate_formula(+InputFormula, -OutputFormula)
%% Translates from TPTP syntax to nanoCoP internal syntax
translate_formula(F, F_out) :-
    translate_operators(F, F_out).

% =========================================================================
% OPERATOR TRANSLATION
% =========================================================================
% CRITICAL: Handle # (bottom/falsum) - must come FIRST before compound terms

% Bottom/falsum: # is translated to ~(p0 => p0) which represents ⊥
translate_operators(F, (~(p0 => p0))) :-
    nonvar(F),
    (F == '#' ; F == f ; F == bot ; F == bottom ; F == falsum),
    !.

% Top/verum: t is translated to (p0 => p0) which represents ⊤
translate_operators(F, (p0 => p0)) :-
    nonvar(F),
    (F == t ; F == top ; F == verum),
    !.

% Atomic formulas (must come before compound terms check)
translate_operators(F, F) :-
    atomic(F),
    \+ (F == '#'), \+ (F == f), \+ (F == bot),
    \+ (F == t), \+ (F == top),
    !.

% Variables
translate_operators(F, F) :-
    var(F), !.

% Negation
translate_operators(~A, (~A1)) :-
    !, translate_operators(A, A1).

% Disjunction
translate_operators(A | B, (A1 ; B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Conjunction
translate_operators(A & B, (A1 , B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Implication
translate_operators(A => B, (A1 => B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Biconditional
translate_operators(A <=> B, (A1 <=> B1)) :-
    !, translate_operators(A, A1), translate_operators(B, B1).

% Universal quantifier with brackets: ![X]:F
translate_operators(![Var]:A, (all RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Existential quantifier with brackets: ?[X]:F
translate_operators(?[Var]:A, (ex RealVar:A1)) :-
    !,
    substitute_var_in_formula(A, Var, RealVar, A_subst),
    translate_operators(A_subst, A1).

% Universal quantifier simple syntax: !X:F (alternative)
translate_operators(!Var:A, (all VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% Existential quantifier simple syntax: ?X:F (alternative)
translate_operators(?Var:A, (ex VarUpper:A1)) :-
    atom(Var), !,
    upcase_atom(Var, VarUpper),
    translate_operators(A, A1).

% General compound terms (predicates with arguments)
translate_operators(Term, Term1) :-
    compound(Term),
    Term =.. [F|Args],
    maplist(translate_operators, Args, Args1),
    Term1 =.. [F|Args1].

% =========================================================================
% VARIABLE SUBSTITUTION
% =========================================================================
%% substitute_var_in_formula(+Formula, +OldVar, +NewVar, -NewFormula)
substitute_var_in_formula(Var, OldVar, NewVar, NewVar) :-
    atomic(Var), Var == OldVar, !.
substitute_var_in_formula(Atom, _OldVar, _NewVar, Atom) :-
    atomic(Atom), !.
substitute_var_in_formula(Var, _OldVar, _NewVar, Var) :-
    var(Var), !.
substitute_var_in_formula(Term, OldVar, NewVar, NewTerm) :-
    compound(Term), !,
    Term =.. [F|Args],
    maplist(substitute_var_in_formula_curry(OldVar, NewVar), Args, NewArgs),
    NewTerm =.. [F|NewArgs].

substitute_var_in_formula_curry(OldVar, NewVar, Arg, NewArg) :-
    substitute_var_in_formula(Arg, OldVar, NewVar, NewArg).
%%% End of minimal driver for nanoCop integration



% =========================================================================
% ITERATION LIMITS CONFIGURATION  (DO NOT CHANGE THESE VALUES !)
% =========================================================================

logic_iteration_limit(constructive, 3).
logic_iteration_limit(classical, 4).
logic_iteration_limit(minimal, 3).
logic_iteration_limit(intuitionistic, 3).
logic_iteration_limit(fol, 4).

% =========================================================================
% UTILITY for/3
% =========================================================================

for(Threshold, M, N) :- M =< N, Threshold = M.
for(Threshold, M, N) :- M < N, M1 is M+1, for(Threshold, M1, N).

% =========================================================================
% THEOREM vs SEQUENT DETECTION (simplified)
% =========================================================================

:- dynamic current_proof_sequent/1.
:- dynamic premiss_list/1.
:- dynamic current_logic_level/1.

% =========================================================================
% OPTIMIZED CLASSICAL PATTERN DETECTION
% =========================================================================

% normalize_double_negations/2: Simplify ~~A patterns in safe contexts
normalize_double_negations(((A => #) => #), A) :-
    A \= (_ => #), !.
normalize_double_negations(A & B, NA & NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A | B, NA | NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A => B, NA => NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(A <=> B, NA <=> NB) :- !,
    normalize_double_negations(A, NA),
    normalize_double_negations(B, NB).
normalize_double_negations(![X]:A, ![X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(?[X]:A, ?[X]:NA) :- !,
    normalize_double_negations(A, NA).
normalize_double_negations(F, F).

% normalize_biconditional_order/2: Order biconditionals by complexity
normalize_biconditional_order(A <=> B, B <=> A) :-
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    CB < CA, !.
normalize_biconditional_order(A <=> B, NA <=> NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A & B, NA & NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A | B, NA | NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(A => B, NA => NB) :- !,
    normalize_biconditional_order(A, NA),
    normalize_biconditional_order(B, NB).
normalize_biconditional_order(![X]:A, ![X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(?[X]:A, ?[X]:NA) :- !,
    normalize_biconditional_order(A, NA).
normalize_biconditional_order(F, F).

% formula_complexity/2: Heuristic complexity measure
formula_complexity((A => #), C) :- !,
    formula_complexity(A, CA),
    C is CA + 2.
formula_complexity(A => B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 3.
formula_complexity(A & B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 2.
formula_complexity(A | B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 2.
formula_complexity(A <=> B, C) :- !,
    formula_complexity(A, CA),
    formula_complexity(B, CB),
    C is CA + CB + 4.
formula_complexity(![_]:A, C) :- !,
    formula_complexity(A, CA),
    C is CA + 5.
formula_complexity(?[_]:A, C) :- !,
    formula_complexity(A, CA),
    C is CA + 5.
formula_complexity(_, 1).

% =========================================================================
% CLASSICAL PATTERN DETECTION (Core)
% =========================================================================

is_classical_pattern(Formula) :-
    (   is_fol_structural_pattern(Formula) ->
        !
    ;   contains_classical_pattern(Formula)
    ).

contains_classical_pattern(Formula) :-
    is_basic_classical_pattern(Formula), !.
contains_classical_pattern(Formula) :-
    binary_connective(Formula, Left, Right),
    (contains_classical_pattern(Left) ; contains_classical_pattern(Right)), !.

binary_connective(A & B, A, B).
binary_connective(A | B, A, B).
binary_connective(A => B, A, B).
binary_connective(A <=> B, A, B).

% BASIC CLASSICAL PATTERNS
is_basic_classical_pattern(A | (A => #)) :- !.
is_basic_classical_pattern((A => #) | A) :- !.
is_basic_classical_pattern(((A => #) => #) => A) :-
    A \= (_ => #), !.
is_basic_classical_pattern(((A => _B) => A) => A) :- !.
is_basic_classical_pattern((A => B) => ((A => #) | B)) :- !.
is_basic_classical_pattern((A => B) => (B | (A => #))) :- !.
is_basic_classical_pattern((A => B) | (B => A)) :- !.
is_basic_classical_pattern(((B => #) => (A => #)) => (A => B)) :- !.
is_basic_classical_pattern((A => B) => ((B => #) => (A => #))) :- !.
is_basic_classical_pattern(((A => B) => #) => (A & (B => #))) :- !.
is_basic_classical_pattern(((A & B) => #) => ((A => #) | (B => #))) :- !.
is_basic_classical_pattern((((A => #) => B) & (A => B)) => B) :- !.
is_basic_classical_pattern(((A => B) & ((A => #) => B)) => B) :- !.

% FOL STRUCTURAL PATTERNS
is_fol_structural_pattern(((![_-_]:_ => _) => (?[_-_]:(_ => _)))) :- !.
is_fol_structural_pattern(?[_-_]:(_ => ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (_ | ![_-_]:_)) :- !.
is_fol_structural_pattern((![_-_]:(_ | _)) => (![_-_]:_ | _)) :- !.
is_fol_structural_pattern((_) => ?[_-_]:(_ & ![_-_]:(_ | _))) :- !.

% =========================================================================
% MAIN INTERFACE: prove/1
% =========================================================================

% NEW: Automatic detection for sequents with premisses
prove(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
     %  VALIDATION: Verify premisses and conclusion
    validate_sequent_formulas(G, D),
    statistics(runtime, [_T0|_]),
    write('------------------------------------------'), nl,
    write('G4 PROOF FOR SEQUENT: '),
    write_sequent_compact(G, D), nl,
    write('------------------------------------------'), nl,
    write('MODE: Sequent '), nl,
    nl,

    % Store premisses for display
    retractall(premiss_list(_)),
    % Prepare formulas BEFORE storing premisses
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),
    % Store PREPARED premisses (with ~z transformed to z => #)
    assertz(premiss_list(PrepG)),
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(G > D)),

    % Detect classical pattern in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('              🔍 CLASSICAL PATTERN DETECTED                '), nl,
        write('                  → Using classical logic                  '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        Logic = classical,
        OutputProof = Proof
    ;
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('   🔄 PHASE 1: Minimal → Intuitionistic → Classical        '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            write('   ✅ Constructive proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; time(provable_at_level(PrepG > PrepD, constructive, Proof)) ->
            write('   ✅ Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  Constructive proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic
            ),
            OutputProof = Proof
        ;
            write('   ⚠️  Constructive logic failed'), nl,
            write('┌─────────────────────────────────────────────────────────┐'), nl,
            write('              🎯 TRYING CLASSICAL LOGIC                    '), nl,
            write('└─────────────────────────────────────────────────────────┘'), nl,
            time(provable_at_level(PrepG > PrepD, classical, Proof)),
            !,  % Cut here to prevent backtracking
            % Check if refutation or proof
            (is_antisequent_proof(Proof) ->
                write('    Formula refuted (counter-model found)'), nl
            ;
                write('    Proof found in CLASSICAL LOGIC '), nl
            ),
            Logic = classical,
            OutputProof = Proof
        )
    ),
    output_proof_results(OutputProof, Logic, G > D, sequent).


% =========================================================================
% BICONDITIONAL - Complete corrected section (grouped by proof style)
% =========================================================================

prove(Left <=> Right) :- !,
    % Check if user meant sequent equivalence (<>) instead of biconditional (<=>)
    ( (is_list(Left) ; is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('║  ⚠️  SYNTAX ERROR: <=> used with sequents                     ║'), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: prove('), write(Left <=> Right), write(')'), nl,
        nl,
        write('❌ WRONG:   <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: prove(p <=> q)'), nl,
        nl,
        write('✅ CORRECT: <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: decide([p] <> [q])'), nl,
        nl,
        write('Note: For sequent equivalence, use decide/1, not prove/1'), nl,
        nl,
        fail
    ;
        % ═══════════════════════════════════════════════════════════════
        % PHASE 1 & 2: G4MIC PROOF SEARCH (both directions)
        % ═══════════════════════════════════════════════════════════════
        % Normal biconditional processing
        validate_and_warn(Left, _),
        validate_and_warn(Right, _),

        % Test direction 1
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent(Left => Right)),
        ( catch(time((decide_silent(Left => Right, Proof1, Logic1))), _, fail) ->
            Direction1Valid = true,
            (is_antisequent_proof(Proof1) -> IsRefutation1 = true ; IsRefutation1 = false)
        ;
            Direction1Valid = false, Proof1 = none, Logic1 = none, IsRefutation1 = false
        ),

        % Test direction 2
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent(Right => Left)),
        ( catch(time((decide_silent(Right => Left, Proof2, Logic2))), _, fail) ->
            Direction2Valid = true,
            (is_antisequent_proof(Proof2) -> IsRefutation2 = true ; IsRefutation2 = false)
        ;
            Direction2Valid = false, Proof2 = none, Logic2 = none, IsRefutation2 = false
        ),

        nl,
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('           ↔️  BICONDITIONAL:  Proving Both Directions           '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl, nl,

        % ═══════════════════════════════════════════════════════════════
        % SEQUENT CALCULUS (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('📐 Sequent Calculus Proofs'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - Sequent
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                ➡️   DIRECTION 1                                '), nl,
        write('           '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true ->
            ( IsRefutation1 = true ->
                write('❌ REFUTED (counter-model found)'), nl, nl
            ;
                output_logic_label(Logic1), nl, nl
            ),
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof1, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('✅ Q. E.D. '), nl, nl
        ; write('⚠️  FAILED TO PROVE OR REFUTE'), nl, nl
        ),

        % Direction 2 - Sequent
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                    ⬅️   DIRECTION 2                            '), nl,
        write('               '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true ->
            ( IsRefutation2 = true ->
                write('❌ REFUTED (counter-model found)'), nl, nl
            ;
                output_logic_label(Logic2), nl, nl
            ),
            write('\\begin{prooftree}'), nl,
            render_bussproofs(Proof2, 0, _),
            write('\\end{prooftree}'), nl, nl,
            write('✅ Q.E.D.'), nl, nl
        ; write('⚠️  FAILED TO PROVE OR REFUTE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % NATURAL DEDUCTION - TREE STYLE (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🌳 Natural Deduction - Tree Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - ND Tree
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                     ➡️   DIRECTION 1                            '), nl,
        write('                '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true, IsRefutation1 = false ->
            render_nd_tree_proof(Proof1), nl, nl,
            write('✅ Q.E.D. '), nl, nl
        ; Direction1Valid = true, IsRefutation1 = true ->
            write('(Refutation - no ND proof)'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % Direction 2 - ND Tree
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                   ⬅️   DIRECTION 2                              '), nl,
        write('                 '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true, IsRefutation2 = false ->
            render_nd_tree_proof(Proof2), nl, nl,
            write('✅ Q.E.D.'), nl, nl
        ; Direction2Valid = true, IsRefutation2 = true ->
            write('(Refutation - no ND proof)'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % NATURAL DEDUCTION - FITCH STYLE (both directions)
        % ═══════════════════════════════════════════════════════════════
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🚩 Natural Deduction - Flag Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

        % Direction 1 - Fitch
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('                     ➡️   DIRECTION 1                           '), nl,
        write('                '), write(Left => Right), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction1Valid = true, IsRefutation1 = false ->
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof1),
            write('\\end{fitch}'), nl, nl,
            write('✅ Q. E.D.'), nl, nl
        ; Direction1Valid = true, IsRefutation1 = true ->
            write('(Refutation - no ND proof)'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % Direction 2 - Fitch
        write('┌──────────────────────────────────────────────────────────────┐'), nl,
        write('              ⬅️   DIRECTION 2                                   '), nl,
        write('             '), write(Right => Left), nl,
        write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
        ( Direction2Valid = true, IsRefutation2 = false ->
            write('\\begin{fitch}'), nl,
            g4_to_fitch_theorem(Proof2),
            write('\\end{fitch}'), nl, nl,
            write('✅ Q.E.D. '), nl, nl
        ; Direction2Valid = true, IsRefutation2 = true ->
            write('(Refutation - no ND proof)'), nl, nl
        ; write('⚠️  FAILED TO PROVE'), nl, nl
        ),

        % ═══════════════════════════════════════════════════════════════
        % SUMMARY
        % ═══════════════════════════════════════════════════════════════
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('                          📊 SUMMARY                             '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl,
        write('Direction 1 ('), write(Left => Right), write('): '),
        ( Direction1Valid = true ->
            ( IsRefutation1 = true -> write('❌ INVALID (refuted)') ; write('✅ VALID in '), write(Logic1), write(' logic') )
        ; write('⚠️  FAILED')
        ), nl,
        write('Direction 2 ('), write(Right => Left), write('): '),
        ( Direction2Valid = true ->
            ( IsRefutation2 = true -> write('❌ INVALID (refuted)') ; write('✅ VALID in '), write(Logic2), write(' logic') )
        ; write('⚠️  FAILED')
        ), nl, nl,

        % ═══════════════════════════════════════════════════════════════
        % PHASE 3: EXTERNAL VALIDATION (G4MIC FIRST, THEN NANOCOP)
        % ═══════════════════════════════════════════════════════════════
        write('╔══════════════════════════════════════════════════════════════╗'), nl,
        write('                  🔍 PHASE 3: VALIDATION                         '), nl,
        write('╚══════════════════════════════════════════════════════════════╝'), nl,
        nl,

        % G4MIC VALIDATION (PRIMARY PROVER)
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('🔍 g4mic_decides output'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( catch(g4mic_decides(Left <=> Right), _, fail) ->
            write('true.'), nl,
            G4micResult = valid
        ;
            write('false.'), nl,
            G4micResult = invalid
        ),
        nl,

        % NANOCOP VALIDATION (EXTERNAL VALIDATION)
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('🔍 nanoCop_decides output'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( catch(nanoCop_decides(Left <=> Right), _, fail) ->
            write('true. '), nl,
            NanoCopResult = valid
        ;
            write('false.'), nl,
            NanoCopResult = invalid
        ),
        nl,

        % VALIDATION SUMMARY
        write('═══════════════════════════════════════════════════════════════'), nl,
        write('📊 Validation Summary'), nl,
        write('═══════════════════════════════════════════════════════════════'), nl,
        ( G4micResult = valid, NanoCopResult = valid ->
            write('✅ Both provers agree: '), write('true'), nl
        ; G4micResult = invalid, NanoCopResult = invalid ->
            write('✅ Both provers agree: '), write('false'), nl
        ; G4micResult = valid, NanoCopResult = invalid ->
            write('⚠️  Disagreement: g4mic=true, nanoCop=false'), nl
        ; G4micResult = invalid, NanoCopResult = valid ->
            write('⚠️  Disagreement: g4mic=false, nanoCop=true'), nl
        ),
        nl, nl, !
    ).

% =========================================================================
% SEQUENT EQUIVALENCE (<>) - Complete corrected section (grouped by style)
% =========================================================================

prove([Left] <> [Right]) :- !,
    validate_and_warn(Left, _),
    validate_and_warn(Right, _),

    % Test direction 1: [Left] > [Right]
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Left] > [Right])),
    ( catch(time((prove_sequent_silent([Left] > [Right], Proof1, Logic1))), _, fail) ->
        Direction1Valid = true,
        (is_antisequent_proof(Proof1) -> IsRefutation1 = true ; IsRefutation1 = false)
    ;
        Direction1Valid = false, Proof1 = none, Logic1 = none, IsRefutation1 = false
    ),

    % Test direction 2: [Right] > [Left]
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent([Right] > [Left])),
    ( catch(time((prove_sequent_silent([Right] > [Left], Proof2, Logic2))), _, fail) ->
        Direction2Valid = true,
        (is_antisequent_proof(Proof2) -> IsRefutation2 = true ; IsRefutation2 = false)
    ;
        Direction2Valid = false, Proof2 = none, Logic2 = none, IsRefutation2 = false
    ),

    nl,
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('             ↔️   EQUIVALENCE: Proving Both Directions          '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl, nl,

    % ═══════════════════════════════════════════════════════════════
    % SEQUENT CALCULUS (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('📐 Sequent Calculus Proofs'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - Sequent
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                    ➡️   DIRECTION 1                            '), nl,
    write('        '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true ->
        ( IsRefutation1 = true ->
            write('❌ REFUTED (counter-model found)'), nl, nl
        ;
            output_logic_label(Logic1), nl, nl
        ),
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof1, 0, _),
        write('\\end{prooftree}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE OR REFUTE'), nl, nl
    ),

    % Direction 2 - Sequent
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                     ⬅️   DIRECTION 2                           '), nl,
    write('         '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true ->
        ( IsRefutation2 = true ->
            write('❌ REFUTED (counter-model found)'), nl, nl
        ;
            output_logic_label(Logic2), nl, nl
        ),
        write('\\begin{prooftree}'), nl,
        render_bussproofs(Proof2, 0, _),
        write('\\end{prooftree}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; write('⚠️  FAILED TO PROVE OR REFUTE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % NATURAL DEDUCTION - TREE STYLE (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🌳 Natural Deduction - Tree Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - ND Tree
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                      ➡️   DIRECTION 1                          '), nl,
    write('        '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true, IsRefutation1 = false ->
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent([Left] > [Right])),
        retractall(premiss_list(_)),
        assertz(premiss_list([Left])),
        render_nd_tree_proof(Proof1), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; Direction1Valid = true, IsRefutation1 = true ->
        write('(Refutation - no ND proof)'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % Direction 2 - ND Tree
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                          ⬅️   DIRECTION 2                      '), nl,
    write('            '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true, IsRefutation2 = false ->
        retractall(current_proof_sequent(_)),
        assertz(current_proof_sequent([Right] > [Left])),
        retractall(premiss_list(_)),
        assertz(premiss_list([Right])),
        render_nd_tree_proof(Proof2), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; Direction2Valid = true, IsRefutation2 = true ->
        write('(Refutation - no ND proof)'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % NATURAL DEDUCTION - FITCH STYLE (both directions)
    % ═══════════════════════════════════════════════════════════════
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('🚩 Natural Deduction - Flag Style'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,

    % Direction 1 - Fitch
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                      ➡️   DIRECTION 1                          '), nl,
    write('            '), write(Left), write(' ⊢ '), write(Right), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction1Valid = true, IsRefutation1 = false ->
        write('\\begin{fitch}'), nl,
        g4_to_fitch_sequent(Proof1, [Left] > [Right]),
        write('\\end{fitch}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; Direction1Valid = true, IsRefutation1 = true ->
        write('(Refutation - no ND proof)'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % Direction 2 - Fitch
    write('┌──────────────────────────────────────────────────────────────┐'), nl,
    write('                    ⬅️   DIRECTION 2                            '), nl,
    write('         '), write(Right), write(' ⊢ '), write(Left), nl,
    write('└──────────────────────────────────────────────────────────────┘'), nl, nl,
    ( Direction2Valid = true, IsRefutation2 = false ->
        write('\\begin{fitch}'), nl,
        g4_to_fitch_sequent(Proof2, [Right] > [Left]),
        write('\\end{fitch}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ; Direction2Valid = true, IsRefutation2 = true ->
        write('(Refutation - no ND proof)'), nl, nl
    ; write('⚠️  FAILED TO PROVE'), nl, nl
    ),

    % ═══════════════════════════════════════════════════════════════
    % SUMMARY
    % ═══════════════════════════════════════════════════════════════
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('                       📊 SUMMARY                               '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl,
    write('Direction 1 ('), write(Left), write(' ⊢ '), write(Right), write('): '),
    ( Direction1Valid = true ->
        ( IsRefutation1 = true -> write('❌ INVALID (refuted)') ; write('✅ VALID in '), write(Logic1), write(' logic') )
    ; write('⚠️  FAILED')
    ), nl,
    write('Direction 2 ('), write(Right), write(' ⊢ '), write(Left), write('): '),
    ( Direction2Valid = true ->
        ( IsRefutation2 = true -> write('❌ INVALID (refuted)') ; write('✅ VALID in '), write(Logic2), write(' logic') )
    ; write('⚠️  FAILED')
    ), nl, nl, !.


% =========================================================================
% THEOREMS - Unified proof with 3 clear phases
% =========================================================================
prove(Formula) :-
    % VALIDATION: Verify the formula
    validate_and_warn(Formula, _ValidatedFormula),
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  🎯 G4 PROOF FOR: '), write(Formula), nl,
    write('═══════════════════════════════════════════════════════════'), nl,
    write('  MODE: Theorem'), nl,
    nl,

    retractall(premiss_list(_)),
    retractall(current_proof_sequent(_)),

    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),

    % ═══════════════════════════════════════════════════════════════
    % PHASE 1: CONSTRUCTIVE LOGIC (Minimal → Intuitionistic)
    % ═══════════════════════════════════════════════════════════════
    (   F2 = ((A => #) => #), A \= (_ => #)  ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('               🔍 DOUBLE NEGATION DETECTED                 '), nl,
        write('             → Trying constructive logic first             '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('          🔄 PHASE 1: CONSTRUCTIVE LOGIC                   '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        ((provable_at_level([] > [F2], constructive, Proof)) ->
            write('   ✅ Constructive proof found'), nl,
            ((provable_at_level([] > [F2], minimal, _)) ->
                write('  ✅ Proof found in MINIMAL LOGIC'), nl,
                Logic = minimal,
                OutputProof = Proof
            ;
                ( proof_uses_lbot(Proof) ->
                    write('  ✅ Proof found in INTUITIONISTIC LOGIC'), nl,
                    Logic = intuitionistic,
                    OutputProof = Proof
                )
            )
        ;
            write('   ⚠️  Constructive logic failed'), nl,
            write('┌─────────────────────────────────────────────────────────┐'), nl,
            write('      🎯 PHASE 2: CLASSICAL LOGIC (with antisequent)       '), nl,
            write('└─────────────────────────────────────────────────────────┘'), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            write('   ✅ Classical proof found'), nl,
            Logic = classical,
            OutputProof = Proof
        )
    ; is_classical_pattern(F2) ->
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('          🔍 CLASSICAL PATTERN DETECTED                    '), nl,
        write('           → Skipping constructive logic                   '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('      🎯 PHASE 2: CLASSICAL LOGIC (with antisequent)       '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
          (provable_at_level([] > [F2], classical, Proof)),
        write('   ✅ Classical proof found'), nl,
        Logic = classical,
        OutputProof = Proof
    ;
        write('┌─────────────────────────────────────────────────────────┐'), nl,
        write('    🔄 PHASE 1: Minimal → Intuitionistic                   '), nl,
        write('└─────────────────────────────────────────────────────────┘'), nl,
        ((provable_at_level([] > [F2], minimal, Proof)) ->
            write('   ✅ Proof found in MINIMAL LOGIC'), nl,
            Logic = minimal,
            OutputProof = Proof
        ; (provable_at_level([] > [F2], constructive, Proof)) ->
            write('   ✅ Constructive proof found'), nl,
            ( proof_uses_lbot(Proof) ->
                write('  → Uses explosion rule - Proof found in INTUITIONISTIC LOGIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            ;
                write('  → No explosion → INTUITIONISTIC'), nl,
                Logic = intuitionistic,
                OutputProof = Proof
            )
        ;
            write('   ⚠️  Constructive logic failed'), nl,
            write('┌─────────────────────────────────────────────────────────┐'), nl,
            write('      🎯 PHASE 2: CLASSICAL LOGIC (with antisequent)       '), nl,
            write('└─────────────────────────────────────────────────────────┘'), nl,
            time(provable_at_level([] > [F2], classical, Proof)),
            % Check if refutation or proof
            (is_antisequent_proof(Proof) ->
                write('  Formula refuted (counter-model found)'), nl
            ;
                write('  Proof found in Classical logic'), nl
            ),
            Logic = classical,
            OutputProof = Proof
        )
    ),

    % Display proof results
    output_proof_results(OutputProof, Logic, Formula, theorem),

    % ═══════════════════════════════════════════════════════════════
    % PHASE 3: EXTERNAL VALIDATION (G4MIC FIRST, THEN NANOCOP)
    % ═══════════════════════════════════════════════════════════════
    nl,
    write('╔══════════════════════════════════════════════════════════════╗'), nl,
    write('                  🔍 PHASE 3: VALIDATION                         '), nl,
    write('╚══════════════════════════════════════════════════════════════╝'), nl,
    nl,

    % G4MIC VALIDATION (PRIMARY PROVER)
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('🔍 g4mic_decides output'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( catch(g4mic_decides(Formula), _, fail) ->
        write('true.'), nl,
        G4micResult = valid
    ;
        write('false.'), nl,
        G4micResult = invalid
    ),
    nl,

    % NANOCOP VALIDATION (EXTERNAL VALIDATION)
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('🔍 nanoCop_decides output'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( catch(nanoCop_decides(Formula), _, fail) ->
        write('true.'), nl,
        NanoCopResult = valid
    ;
        write('false.'), nl,
        NanoCopResult = invalid
    ),
    nl,

    % VALIDATION SUMMARY
    write('═══════════════════════════════════════════════════════════════'), nl,
    write('📊 Validation Summary'), nl,
    write('═══════════════════════════════════════════════════════════════'), nl,
    ( G4micResult = valid, NanoCopResult = valid ->
        write('✅ Both provers agree: '), write('true'), nl
    ; G4micResult = invalid, NanoCopResult = invalid ->
        write('✅ Both provers agree: '), write('false'), nl
    ; G4micResult = valid, NanoCopResult = invalid ->
        write('⚠️  Disagreement: g4mic=true, nanoCop=false'), nl
    ; G4micResult = invalid, NanoCopResult = valid ->
        write('⚠️  Disagreement: g4mic=false, nanoCop=true'), nl
    ),
    nl, nl.

% =========================================================================
% HELPERS
% =========================================================================

% Prepare a list of formulas
prepare_sequent_formulas(GIn, DIn, GOut, DOut) :-
    maplist(prepare_and_subst, GIn, GOut),
    maplist(prepare_and_subst, DIn, DOut).

prepare_and_subst(F, FOut) :-
    prepare(F, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, FOut).

% Compact display of a sequent
write_sequent_compact([], [D]) :- !, write(' |- '), write(D).
write_sequent_compact([G], [D]) :- !, write(G), write(' |- '), write(D).
write_sequent_compact(G, [D]) :-
    write_list_compact(G),
    write(' |- '),
    write(D).

write_list_compact([X]) :- !, write(X).
write_list_compact([X|Xs]) :- write(X), write(', '), write_list_compact(Xs).

% =========================================================================
% FORMULA AND SEQUENT VALIDATION
% =========================================================================

% Validate a sequent (premisses + conclusions)
validate_sequent_formulas(G, D) :-
    % Validate all premisses
    forall(member(Premiss, G), validate_and_warn(Premiss, _)),
    % Validate all conclusions
    forall(member(Conclusion, D), validate_and_warn(Conclusion, _)).

% =========================================================================
% OUTPUT WITH MODE DETECTION
% =========================================================================

output_proof_results(Proof, LogicType, OriginalFormula, Mode) :-
    % Detect if this is an antisequent (refutation)
    (is_antisequent_proof(Proof) ->
        IsRefutation = true
    ;
        IsRefutation = false
    ),

    extract_formula_from_proof(Proof, Formula),
    detect_and_set_logic_level(Formula),
    % Store logic level for use in proof rendering (e.g., DS optimization)
    retractall(current_logic_level(_)),
    assertz(current_logic_level(LogicType)),

    % Display appropriate label
    (IsRefutation = true ->
        write('G4+IP refutation in classical logic'), nl, nl
    ;
        output_logic_label(LogicType)
    ),

    % ADDED: Display raw Prolog proof term
    nl, write('=== RAW PROLOG PROOF TERM ==='), nl,
    write('    '), portray_clause(Proof), nl, nl,
    ( catch(
          (copy_term(Proof, ProofCopy),
           numbervars(ProofCopy, 0, _),
           nl, nl),
          error(cyclic_term, _),
          (write('%% WARNING: Cannot represent proof term due to cyclic_term.'), nl, nl)
      ) -> true ; true ),

    % Sequent Calculus
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
    write('📐 Sequent Calculus Proof'), nl,
    write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
    write('\\begin{prooftree}'), nl,
    render_bussproofs(Proof, 0, _),
    write('\\end{prooftree}'), nl, nl,
    write('✅ Q.E.D.'), nl, nl,

    % Skip Natural Deduction for antisequents
    (IsRefutation = false ->
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🌳 Natural Deduction - Tree Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
        render_nd_tree_proof(Proof), nl, nl,
        write('✅ Q.E.D.'), nl, nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl,
        write('🚩 Natural Deduction - Flag Style'), nl,
        write('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━'), nl, nl,
        write('\\begin{fitch}'), nl,
        ( Mode = sequent ->
            g4_to_fitch_sequent(Proof, OriginalFormula)
        ;
            g4_to_fitch_theorem(Proof)
        ),
        write('\\end{fitch}'), nl, nl,
        write('✅ Q.E.D.'), nl, nl
    ;
        true  % Skip ND for refutations
    ),
    !.

% Helper: detect if a proof is an antisequent
% Helper: detect if a proof contains an antisequent RULE (not just asq in formulas)
is_antisequent_proof(asq(Seq, _)) :-
    % Must be asq as a PROOF RULE with a sequent
    (Seq = (_ < _) ; Seq = (_ > _)), !.
is_antisequent_proof(Proof) :-
    compound(Proof),
    Proof =.. [Functor|Args],
    % Only check sub-proofs, not the sequent (first arg)
    member(Functor, [ip, ltoto, lall, rcond, lex, rex, lor, rand,
                     lorto, land, l0cond, landto, tne, lex_lor, rall,
                     cq_c, cq_m, eq_refl, eq_sym, eq_trans, eq_trans_chain,
                     eq_cong, eq_subst_eq, eq_subst]),
    Args = [_Sequent|SubProofs],  % Skip sequent, check sub-proofs
    member(SubProof, SubProofs),
    is_antisequent_proof(SubProof).

% =========================================================================
% SILENT VERSIONS (for internal use)
% =========================================================================

decide_silent(Formula, Proof, Logic) :-
    retractall(current_proof_sequent(_)),
    assertz(current_proof_sequent(Formula)),

    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),
    progressive_proof_silent(F2, Proof, Logic).

progressive_proof_silent(Formula, Proof, Logic) :-
    ( provable_at_level([] > [Formula], minimal, Proof) ->
        Logic = minimal
    ; provable_at_level([] > [Formula], intuitionistic, Proof) ->
        Logic = intuitionistic
    ; provable_at_level([] > [Formula], classical, Proof) ->
        Logic = classical
    ).

% =========================================================================
% PROVABILITY AT A GIVEN LEVEL
% =========================================================================

provable_at_level(Sequent, constructive, P) :-
    !,
    logic_iteration_limit(constructive, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,  % Initialize before each attempt
    ( g4mic_proves(Gamma > Delta, [], Threshold, 1, _, minimal, P) -> true    % <- Essayer minimal d'abord
    ; init_eigenvars, g4mic_proves(Gamma > Delta, [], Threshold, 1, _, intuitionistic, P)     % <- Then intuitionistic if failure
    ),
    !.

provable_at_level(Sequent, LogicLevel, Proof) :-
    LogicLevel \= classical,  % For non-classical logics
    logic_iteration_limit(LogicLevel, MaxIter),
    for(Threshold, 0, MaxIter),
    Sequent = (Gamma > Delta),
    init_eigenvars,
    g4mic_proves(Gamma > Delta, [], Threshold, 1, _, LogicLevel, Proof),
    !.

% =========================================================================
% CLASSICAL LOGIC: Two-pass approach (PHASE 2)
% PASS 1: Normal proof search (antisequent disabled) - all iterations
% PASS 2: If pass 1 fails, enable antisequent and search for counter-model
% =========================================================================
provable_at_level(Sequent, classical, Proof) :-
    Sequent = (Gamma > Delta),
    logic_iteration_limit(classical, MaxIter),
    (   % PASS 1: Normal proof (all iterations)
        (for(Threshold, 0, MaxIter),
         init_eigenvars,
         g4mic_proves(Gamma > Delta, [], Threshold, 1, _, classical, Proof))
    ->  true  % Success - proof found
    ;   % PASS 2: Antisequent (only if pass 1 failed completely - all iterations)
        nb_setval(asq_enabled, true),
        once((  % USE ONCE to prevent multiple solutions
            for(Threshold, 0, MaxIter),
            init_eigenvars,
            g4mic_proves(Gamma > Delta, [], Threshold, 1, _, classical, Proof)
        )),
        nb_setval(asq_enabled, false)
    ),
    !.  % Cut to prevent backtracking to alternative proofs


% =========================================================================
% DISPLAY HELPERS
% =========================================================================

% Helper: prove sequent silently (for <> operator)
prove_sequent_silent(Sequent, Proof, Logic) :-
    Sequent = (Gamma > Delta),
    prepare_sequent_formulas(Gamma, Delta, PrepGamma, PrepDelta),
    ( member(SingleGoal, PrepDelta), is_classical_pattern(SingleGoal) ->
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ; provable_at_level(PrepGamma > PrepDelta, minimal, Proof) ->
        Logic = minimal
    ; provable_at_level(PrepGamma > PrepDelta, intuitionistic, Proof) ->
        Logic = intuitionistic
    ;
        provable_at_level(PrepGamma > PrepDelta, classical, Proof),
        Logic = classical
    ).

output_logic_label(minimal) :-
    write('G4 proofs in minimal logic'), nl, nl.
output_logic_label(intuitionistic) :-
    write('G4 proofs in intuitionistic logic'), nl, nl.
output_logic_label(classical) :-
    write('G4+IP proofs in classical logic'), nl, nl.

proof_uses_lbot(lbot(_,_)) :- !.
proof_uses_lbot(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    proof_uses_lbot(Arg).

% =========================================================================
% MINIMAL INTERFACE g4mic_decides/1
% =========================================================================

% g4mic_decides/1 for biconditionals
g4mic_decides(Left <=> Right) :- ! ,
    % Check if user meant sequent equivalence (<>) instead of biconditional (<=>)
    ( (is_list(Left) ; is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('║  ⚠️  SYNTAX ERROR: <=> used with sequents                     ║'), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: '), write(Left <=> Right), nl,
        nl,
        write('❌ WRONG:   <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: p <=> q'), nl,
        nl,
        write('✅ CORRECT: <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: [p] <> [q]'), nl,
        nl,
        write('Please use:  '), write([Left] <> [Right]), nl,
        nl,
        fail
    ;
        % Normal biconditional processing
        validate_and_warn(Left, _),
        validate_and_warn(Right, _),

        % Test direction 1: Left => Right
        time((decide_silent(Left => Right, Proof1, Logic1))),
        ( is_antisequent_proof(Proof1) ->
            write('Direction 1 ('), write(Left => Right), write(') is INVALID'), nl,
            !, fail
        ;
            write('Direction 1 ('), write(Left => Right), write(') is valid in '),
            write(Logic1), write(' logic'), nl
        ),

        % Test direction 2: Right => Left
        time((decide_silent(Right => Left, Proof2, Logic2))),
        ( is_antisequent_proof(Proof2) ->
            write('Direction 2 ('), write(Right => Left), write(') is INVALID'), nl,
            !, fail
        ;
            write('Direction 2 ('), write(Right => Left), write(') is valid in '),
            write(Logic2), write(' logic'), nl
        ),
        !
    ).

% g4mic_decides/1 for sequent equivalence (must come before Formula catch-all)
g4mic_decides([Left] <> [Right]) :- !,
    % Check if user meant biconditional (<=>) instead of sequent equivalence (<>)
    ( (\+ is_list(Left) ; \+ is_list(Right)) ->
        nl,
        write('╔═══════════════════════════════════════════════════════════════╗'), nl,
        write('║  ⚠️  SYNTAX ERROR: <> used with formulas                      ║'), nl,
        write('╚═══════════════════════════════════════════════════════════════╝'), nl,
        nl,
        write('You wrote: '), write([Left] <> [Right]), nl,
        nl,
        write('❌ WRONG:   <>  is for equivalence between SEQUENTS'), nl,
        write('   Example: [p] <> [q]'), nl,
        nl,
        write('✅ CORRECT: <=>  is for biconditionals between FORMULAS'), nl,
        write('   Example: p <=> q'), nl,
        nl,
        write('Please use:  '), write(Left <=> Right), nl,
        nl,
        fail
    ;
        % Normal sequent equivalence processing
        validate_sequent_formulas(Left, Right),

        % Test direction 1: Left > Right
        time(prove_sequent_silent(Left > Right, Proof1, Logic1)),
        ( is_antisequent_proof(Proof1) ->
            write('Direction 1 ('), write(Left), write(' > '), write(Right), write(') is INVALID'), nl,
            !, fail
        ;
            write('Direction 1 ('), write(Left), write(' > '), write(Right), write(') is valid in '),
            write(Logic1), write(' logic'), nl
        ),

        % Test direction 2: Right > Left
        time(prove_sequent_silent(Right > Left, Proof2, Logic2)),
        ( is_antisequent_proof(Proof2) ->
            write('Direction 2 ('), write(Right), write(' > '), write(Left), write(') is INVALID'), nl,
            !, fail
        ;
            write('Direction 2 ('), write(Right), write(' > '), write(Left), write(') is valid in '),
            write(Logic2), write(' logic'), nl
        ),
        !
    ).

% g4mic_decides/1 for sequents
g4mic_decides(G > D) :-
    G \= [],  % Non-empty premisses = SEQUENT
    !,
    validate_sequent_formulas(G, D),
    copy_term((G > D), (GCopy > DCopy)),
    prepare_sequent_formulas(GCopy, DCopy, PrepG, PrepD),

    % Check for classical patterns in conclusion
    ( DCopy = [SingleGoal], is_classical_pattern(SingleGoal) ->
        write('🔍 Classical pattern detected → Using classical logic'), nl,
        time(provable_at_level(PrepG > PrepD, classical, Proof)),
        ( is_antisequent_proof(Proof) ->
            write('Refuted (invalid sequent)'), nl, fail
        ;
            write('Valid in classical logic'), nl
        )
    ;
        % Normal progression: minimal → intuitionistic → classical
        ( time(provable_at_level(PrepG > PrepD, minimal, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid sequent)'), nl, fail
            ;
                write('Valid in minimal logic'), nl
            )
        ; time(provable_at_level(PrepG > PrepD, intuitionistic, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid sequent)'), nl, fail
            ;
                write('Valid in intuitionistic logic'), nl
            )
        ; time(provable_at_level(PrepG > PrepD, classical, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid sequent)'), nl, fail
            ;
                write('Valid in classical logic'), nl
            )
        ;
            write('Failed to prove or refute'), nl, fail
        )
    ),
    !.

% g4mic_decides/1 for theorems (catch-all - must come last)
g4mic_decides(Formula) :-
    copy_term(Formula, FormulaCopy),
    prepare(FormulaCopy, [], F0),
    subst_neg(F0, F1),
    subst_bicond(F1, F2),

    % Check for classical patterns first (optimization)
    ( is_classical_pattern(F2) ->
        write('🔍 Classical pattern detected → Using classical logic'), nl,
        time(provable_at_level([] > [F2], classical, Proof)),
        ( is_antisequent_proof(Proof) ->
            write('Refuted (invalid formula)'), nl, fail
        ;
            write('Valid in classical logic'), nl
        )
    ;
        % Normal progression: minimal → intuitionistic → classical
        ( time(provable_at_level([] > [F2], minimal, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid formula)'), nl, fail
            ;
                write('Valid in minimal logic'), nl
            )
        ; time(provable_at_level([] > [F2], intuitionistic, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid formula)'), nl, fail
            ;
                write('Valid in intuitionistic logic'), nl
            )
        ; time(provable_at_level([] > [F2], classical, Proof)) ->
            ( is_antisequent_proof(Proof) ->
                write('Refuted (invalid formula)'), nl, fail
            ;
                write('Valid in classical logic'), nl
            )
        ;
            write('Failed to prove or refute'), nl, fail
        )
    ),
    !.

% =========================================================================
% BACKWARD COMPATIBILITY ALIAS
% =========================================================================
% decide/1 is kept as an alias for g4mic_decides/1
decide(X) :- g4mic_decides(X).


% =========================================================================
% HELP SYSTEM
% =========================================================================

help :-
    nl,
    write('*****************************************************************'), nl,
    write('*                      G4 PROVER GUIDE                          *'), nl,
    write('*****************************************************************'), nl,
    write('## MAIN COMMANDS '), nl,
    write('  prove(Formula).            - shows the proofs of Formula'), nl,
    write('  g4mic_decides(Formula).    - says either true or false'), nl,
    write('  decide(Formula).           - alias for g4mic_decides'), nl,
    write('## SYNTAX EXAMPLES '), nl,
    write('  THEOREMS:'), nl,
    write('    prove(p => p).                    - Identity'), nl,
    write('    prove((p & q) => p).              - Conjunction elimination'), nl,
    write('  SEQUENTS (syntax of G4 prover):'), nl,
    write('    prove([p] > [p]).                 - Sequent: P |- P '), nl,
    write('    prove([p, q] > [p & q]).          - Sequent: P , Q |- P & Q '), nl,
    write('    prove([p => q, p] > [q]).         - Modus Ponens in sequent form'), nl,
    write('  BICONDITIONALS:'), nl,
    write('    prove(p <=> ~ ~ p).                - Biconditional of Double Negation '), nl,
    write('    prove(p <> ~ ~ p).                 - Bi-implication of Double Negation (sequents)'), nl,
    write('## COMMON MISTAKES '), nl,
    write('   [p] => [p]          - WRONG (use > for sequents)'), nl,
    write('   [p] > [p]           - CORRECT (sequent syntax)'), nl,
    write('   p > q               - WRONG (use => for conditional)'), nl,
    write('   p => q              - CORRECT (conditional)'), nl,
    write('   x <=> y in FOL      - WRONG (use = for equality)'), nl,
    write('   x = y in FOL        - CORRECT (equality)'), nl,
    write('## LOGICAL OPERATORS '), nl,
    write('  ~ A , (A & B) , (A | B) , (A => B) , (A <=> B) ,  # , ![x]:A ,  ?[x]:A').

examples :-
    nl,
    write('*****************************************************************'), nl,
    write('*                     EXAMPLES                                  *'), nl,
    write('*****************************************************************'), nl,
    nl,
    write('  % Identity theorem'), nl,
    write('  ?- prove(p => p).'), nl,
    write('  % Sequent with single premiss'), nl,
    write('  ?- prove([p] > [p]).'), nl,
    write('  % Sequent with multiple premisses'), nl,
    write('  ?- prove([p, q] > [p & q]).'), nl,
    write('  % Sequent: modus ponens'), nl,
    write('  ?- prove([p => q, p] > [q]).'), nl,
    write('  % Law of Excluded Middle (classical)'), nl,
    write('  ?- prove(~ p | p).'), nl,
    write('  % Drinker Paradox (classical)'), nl,
    write('  ?- prove(?[y]:(d(y) => ![x]:d(x))).'), nl,
    nl.
% =========================================================================
% INTERNAL BICONDITIONAL TRANSLATION
% A <=> B becomes (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantifiers: pass recursively into the body
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Propositional connectives
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Base case: atomic formulas
subst_bicond(A, A).

% =========================================================================
% NEGATION SUBSTITUTION (preprocessing)
% =========================================================================
% Double negation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Negation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditional
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Basic case
subst_neg(A, A).
%=================================
% END OF DRIVER
%=================================
