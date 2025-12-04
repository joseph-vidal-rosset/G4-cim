% =========================================================================
% NATURAL DEDUCTION PRINTER IN FLAG STYLE  
% =========================================================================
:- dynamic fitch_line/4.
:- dynamic abbreviated_line/1.

% =========================================================================
% FROM G4 Sequent Calculus To Natural Deduction in Fitch Style 
% =========================================================================

g4_to_fitch_sequent(Proof, OriginalSequent) :-
    !,
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    
    OriginalSequent = (_Gamma > [Conclusion]),
    
    ( premiss_list(PremList), PremList \= [] ->
        render_premiss_list(PremList, 0, 1, NextLine, InitialContext),
        LastPremLine is NextLine - 1  % CORRECTION: last premiss line
    ;
        _NextLine = 1,
        LastPremLine = 0,             % CORRECTION: no premisses
        InitialContext = []
    ),
    
    % CORRECTION: Scope=1 (indentation), CurLine=LastPremLine (numbering)
    fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, LastLine, ResLine, 0, _),
    
    % DETECT: Has any rule been applied?
    ( LastLine = LastPremLine ->
        % No line added -> pure axiom -> display reiteration
        NewLine is LastPremLine + 1,
        assert_safe_fitch_line(NewLine, Conclusion, reiteration(ResLine), 0),
        write('\\fa '),
        rewrite(Conclusion, 0, _, LatexConclusion),
        write(LatexConclusion),
        format(' &  $ R $ ~w\\\\', [ResLine]), nl
    ;
        % A rule has already displayed the conclusion -> do nothing
        true
    ).

% g4_to_fitch_theorem/1: For theorems (original behavior)
g4_to_fitch_theorem(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _).


% =========================================================================
% PREMISS DISPLAY
% =========================================================================

% render_premiss_list/5: Display a list of premisses in Fitch style
render_premiss_list([], _, Line, Line, []) :- !.

render_premiss_list([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    render_fitch_indent(Scope),
    write(' \\fj '),
    rewrite(LastPremiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, LastPremiss, premiss, Scope),
    NextLine is CurLine + 1.
    
render_premiss_list([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    render_fitch_indent(Scope),
    write(' \\fa '),
    rewrite(Premiss, 0, _, LatexFormula),
    write(LatexFormula),
    write(' &  PR\\\\'), nl,
    assert_safe_fitch_line(CurLine, Premiss, premiss, Scope),
    NextCurLine is CurLine + 1,
    render_premiss_list(Rest, Scope, NextCurLine, NextLine, RestContext).

% =========================================================================
% SAFE ASSERTION
% =========================================================================

assert_safe_fitch_line(N, Formula, Just, Scope) :-
    catch(
        (
            ( acyclic_term(Formula) ->
                Safe = Formula
            ;
                make_acyclic_term(Formula, Safe)
            ),
            assertz(fitch_line(N, Safe, Just, Scope))
        ),
        Error,
        (
            format('% Warning: Could not assert line ~w: ~w~n', [N, Error]),
            assertz(fitch_line(N, error_term(Formula), Just, Scope))
        )
    ).

% =========================================================================
% @ SUBSTITUTION HANDLING
% =========================================================================

fitch_g4_proof(@(ProofTerm, _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    fitch_g4_proof(ProofTerm, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% AXIOM
% =========================================================================

fitch_g4_proof(ax((Premisses > [Goal]), _Tag), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

fitch_g4_proof(ax((Premisses > [Goal])), Context, _Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(Goal, Premisses),
    find_context_line(Goal, Context, GoalLine),
    NextLine = CurLine,
    ResLine = GoalLine,
    VarOut = VarIn.

% =========================================================================
% PROPOSITIONAL RULES 
% =========================================================================

% L0-implies
fitch_g4_proof(l0cond((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    % FIXED: Find an implication where BOTH the implication AND its antecedent are present
    % DON'T cut until we've found a valid combination
    member(MajLine:(Ant => Cons), Context),
    member(MinLine:Ant, Context),  % This must succeed for the same Ant
    % Verify we're using formulas that match what G4 expects
    member((Ant => Cons), Premisses),
    member(Ant, Premisses),
    % NOW we can cut - we've found a valid combination
    !,
    DerLine is CurLine + 1,
    format(atom(Just), '$ \\to E $ ~w,~w', [MajLine, MinLine]),
    render_have(Scope, Cons, Just, CurLine, DerLine, VarIn, V1),
    assert_safe_fitch_line(DerLine, Cons, l0cond(MajLine, MinLine), Scope),
    fitch_g4_proof(SubProof, [DerLine:Cons|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut).

% L-and-implies
fitch_g4_proof(landto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select(((A & B) => C), Premisses, _),
    find_context_line(((A & B) => C), Context, ImpLine),
    derive_and_continue(Scope, NewFormula, '$ \\land\\to E $ ~w', [ImpLine],
                       landto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% L-or-implies: Disjunction to implications
fitch_g4_proof(lorto((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SubProof =.. [_Rule|[(SubPremisses > _SubGoal)|_]],
    findall(F, (member(F, SubPremisses), \+ member(F, Premisses)), NewFormulas),
    select(((A | B) => C), Premisses, _),
    find_context_line(((A | B) => C), Context, ImpLine),
    ( NewFormulas = [F1, F2] ->
        Line1 is CurLine + 1,
        Line2 is CurLine + 2,
        assert_safe_fitch_line(Line1, F1, lorto(ImpLine), Scope),
        assert_safe_fitch_line(Line2, F2, lorto(ImpLine), Scope),
        format(atom(Just), '$ \\lor\\to E $ ~w', [ImpLine]),
        render_have(Scope, F1, Just, CurLine, Line1, VarIn, V1),
        render_have(Scope, F2, Just, Line1, Line2, V1, V2),
        fitch_g4_proof(SubProof, [Line2:F2, Line1:F1|Context], Scope, Line2, NextLine, ResLine, V2, VarOut)
    ; NewFormulas = [F1] ->
        derive_and_continue(Scope, F1, '$ \\lor\\to E $ ~w', [ImpLine],
                           lorto(ImpLine), SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ).


% L-and: Conjunction elimination (SPECIAL CASE: implicit conjunction from comma-separated premisses)
% When premisses are given as [P1, P2, P3], they're already available individually in Context
% This happens with sequents like [A, B, C] > [Goal] where commas represent implicit &
fitch_g4_proof(land((Premisses > [_Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    % Check if this land rule is trying to decompose premisses that are already in context as separate items
    \+ member((_ & _), Premisses),  % No explicit conjunction in Premisses
    !,
    % Just continue with SubProof - no &E step needed
    % The comma-separated premisses are already in Context as individual items
    fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut).

% L-and: Conjunction elimination (NORMAL CASE: explicit conjunction)
fitch_g4_proof(land((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    select((A & B), Premisses, _),
    find_context_line((A & B), Context, ConjLine),
    ( is_direct_conjunct(Goal, (A & B)) ->
        derive_formula(Scope, Goal, '$ \\land E $ ~w', [ConjLine], land(ConjLine),
                      CurLine, NextLine, ResLine, VarIn, VarOut)
    ;
        extract_conjuncts((A & B), ConjLine, Scope, CurLine, ExtCtx, LastLine, VarIn, V1),
        append(ExtCtx, Context, NewCtx),
        fitch_g4_proof(SubProof, NewCtx, Scope, LastLine, NextLine, ResLine, V1, VarOut)
    ).

% L-bot: Explosion
fitch_g4_proof(lbot((Premisses > [Goal]), _), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    member(#, Premisses),
    member(FalseLine: #, Context),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, lbot(FalseLine), Scope),
    format(atom(Just), '$ \\bot E $ ~w', [FalseLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% R-or: Disjunction introduction
fitch_g4_proof(ror((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (_ | _), try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
        true
    ; fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, DisjunctLine, VarIn, V1),
      OrLine is SubEnd + 1,
      assert_safe_fitch_line(OrLine, Goal, ror(DisjunctLine), Scope),
      format(atom(Just), '$ \\lor I $ ~w', [DisjunctLine]),
      render_have(Scope, Goal, Just, SubEnd, OrLine, V1, VarOut),
      NextLine = OrLine,
      ResLine = OrLine
    ).

% =========================================================================
% RULES WITH HYPOTHESES (ASSUME-DISCHARGE)
% =========================================================================

% R-implies: Implication introduction
fitch_g4_proof(rcond((_ > [A => B]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% TNE: Triple negation elimination
fitch_g4_proof(tne((_ > [(A => B)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, A, assumption, Scope),
    render_hypo(Scope, A, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:A|Context], NewScope, HypLine, SubEnd, GoalLine, V1, V2),
    ImplLine is SubEnd + 1,
    assert_safe_fitch_line(ImplLine, (A => B), rcond(HypLine, GoalLine), Scope),
    format(atom(Just), '$ \\to I $ ~w-~w', [HypLine, GoalLine]),
    render_have(Scope, (A => B), Just, SubEnd, ImplLine, V2, VarOut),
    NextLine = ImplLine,
    ResLine = ImplLine.

% IP: Indirect proof / Classical
fitch_g4_proof(ip((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( Goal = (A => #) ->
        Assumption = ((A => #) => #),
        Rule = '$ DNE_{m} $'
    ;
        Assumption = (Goal => #),
        Rule = '$ IP $'
    ),
    HypLine is CurLine + 1,
    assert_safe_fitch_line(HypLine, Assumption, assumption, Scope),
    render_hypo(Scope, Assumption, 'AS', CurLine, HypLine, VarIn, V1),
    NewScope is Scope + 1,
    fitch_g4_proof(SubProof, [HypLine:Assumption|Context], NewScope, HypLine, SubEnd, BotLine, V1, V2),
    IPLine is SubEnd + 1,
    assert_safe_fitch_line(IPLine, Goal, ip(HypLine, BotLine), Scope),
    format(atom(Just), '~w ~w-~w', [Rule, HypLine, BotLine]),
    render_have(Scope, Goal, Just, SubEnd, IPLine, V2, VarOut),
    NextLine = IPLine,
    ResLine = IPLine.

% L-or: Disjunction elimination with DS optimization
% DISJUNCTIVE SYLLOGISM (DS): If we have A ∨ B and ¬A, derive B directly
% Valid in intuitionistic and classical logic (not minimal logic)
% Pattern: One branch uses explosion (¬A with A), other branch derives Goal from B
fitch_g4_proof(lor((Premisses > [_Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    % Try DS optimization: Check if we have A ∨ B and ¬A (A => #)
    select((A | B), Premisses, _),
    % Check if ¬A (i.e., A => #) is available
    ( member((A => #), Premisses), member(_NegLine:(A => #), Context) ->
        % We have A ∨ B and ¬A, so we can use DS to derive B directly
        % This is valid because SP1 would just derive ⊥ from A and ¬A, then Goal by ⊥E
        % Find the disjunction and negation in context
        ( find_disj_context(A, B, Context, DisjLine) -> true
        ; find_context_line((A | B), Context, DisjLine)
        ),
        find_context_line((A => #), Context, NegLine),
        % Derive B by DS (without showing the explosion subproof)
        DerLine is CurLine + 1,
        assert_safe_fitch_line(DerLine, B, ds(DisjLine, NegLine), Scope),
        format(atom(Just), '$ DS $ ~w,~w', [DisjLine, NegLine]),
        render_have(Scope, B, Just, CurLine, DerLine, VarIn, V1),
        % Continue with Goal derivation from B
        fitch_g4_proof(SP2, [DerLine:B|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut),
        !
    ; member((B => #), Premisses), member(_NegLine:(B => #), Context) ->
        % Symmetric case: We have A ∨ B and ¬B, derive A by DS
        ( find_disj_context(A, B, Context, DisjLine) -> true
        ; find_context_line((A | B), Context, DisjLine)
        ),
        find_context_line((B => #), Context, NegLine),
        DerLine is CurLine + 1,
        assert_safe_fitch_line(DerLine, A, ds(DisjLine, NegLine), Scope),
        format(atom(Just), '$ DS $ ~w,~w', [DisjLine, NegLine]),
        render_have(Scope, A, Just, CurLine, DerLine, VarIn, V1),
        fitch_g4_proof(SP1, [DerLine:A|Context], Scope, DerLine, NextLine, ResLine, V1, VarOut),
        !
    ;
        fail  % DS not applicable, fall through to regular ∨E
    ).

% L-or: Disjunction elimination (regular case with full ∨E)
fitch_g4_proof(lor((Premisses > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :-
    !,
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) ->
       true
    ; 
      select((A | B), Premisses, _),
      % First try to find the disjunction in the context, otherwise in premisses
      ( find_disj_context(A, B, Context, DisjLine) ->
          true
      ;
          % Disjunction is a premiss, find its line
          find_context_line((A | B), Context, DisjLine)
      ),
      NewScope is Scope + 1,
      AssLineA is CurLine + 1,
      assert_safe_fitch_line(AssLineA, A, assumption, NewScope),
      render_hypo(Scope, A, 'AS', CurLine, AssLineA, VarIn, V1),
      fitch_g4_proof(SP1, [AssLineA:A|Context], NewScope, AssLineA, EndA, GoalA, V1, V2),
      AssLineB is EndA + 1,
      assert_safe_fitch_line(AssLineB, B, assumption, NewScope),
      render_hypo(Scope, B, 'AS', EndA, AssLineB, V2, V3),
      fitch_g4_proof(SP2, [AssLineB:B|Context], NewScope, AssLineB, EndB, GoalB, V3, V4),
      ElimLine is EndB + 1,
      assert_safe_fitch_line(ElimLine, Goal, lor(DisjLine, AssLineA, AssLineB, GoalA, GoalB), Scope),
      format(atom(Just), '$ \\lor E $ ~w,~w-~w,~w-~w', [DisjLine, AssLineA, GoalA, AssLineB, GoalB]),
      render_have(Scope, Goal, Just, EndB, ElimLine, V4, VarOut),
      NextLine = ElimLine,
      ResLine = ElimLine
    ).

% =========================================================================
% BINARY RULES
% =========================================================================

% R-and: Conjunction introduction
fitch_g4_proof(rand((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    Goal = (L & _R),
    ( try_derive_immediately(Goal, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) -> true
    ; fitch_g4_proof(SP1, Context, Scope, CurLine, End1, LeftLine, VarIn, V1),
      fitch_g4_proof(SP2, [LeftLine:L|Context], Scope, End1, End2, RightLine, V1, V2),
      derive_formula(Scope, Goal, '$ \\land I $ ~w,~w', [LeftLine, RightLine], rand(LeftLine, RightLine),
                    End2, NextLine, ResLine, V2, VarOut)
    ).

% L-implies-implies: Special G4 rule
fitch_g4_proof(ltoto((Premisses > _), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select(((Ant => Inter) => Cons), Premisses, _),
    find_context_line(((Ant => Inter) => Cons), Context, ComplexLine),
    
    % STEP 1: Derive (Inter => Cons) by L->->
    ExtractLine is CurLine + 1,
    format(atom(ExtractJust), '$ \\to\\to E$ ~w', [ComplexLine]),
    render_have(Scope, (Inter => Cons), ExtractJust, CurLine, ExtractLine, VarIn, V1),
    assert_safe_fitch_line(ExtractLine, (Inter => Cons), ltoto(ComplexLine), Scope),
    
    % STEP 2: Assume Ant
    AssLine is ExtractLine + 1,
    assert_safe_fitch_line(AssLine, Ant, assumption, Scope),
    render_hypo(Scope, Ant, 'AS', ExtractLine, AssLine, V1, V2),
    NewScope is Scope + 1,
    
    % STEP 3: Prove Inter with [Ant, (Inter=>Cons) | Context]
    fitch_g4_proof(SP1, [AssLine:Ant, ExtractLine:(Inter => Cons)|Context],
                  NewScope, AssLine, SubEnd, InterLine, V2, V3),
    
    % STEP 4: Derive (Ant => Inter) by ->I
    ImpLine is SubEnd + 1,
    assert_safe_fitch_line(ImpLine, (Ant => Inter), rcond(AssLine, InterLine), Scope),
    format(atom(Just1), '$ \\to I $ ~w-~w', [AssLine, InterLine]),
    render_have(Scope, (Ant => Inter), Just1, SubEnd, ImpLine, V3, V4),
    
    % STEP 5: Derive Cons by ->E
    MPLine is ImpLine + 1,
    assert_safe_fitch_line(MPLine, Cons, l0cond(ComplexLine, ImpLine), Scope),
    format(atom(Just2), '$ \\to E $ ~w,~w', [ComplexLine, ImpLine]),
    render_have(Scope, Cons, Just2, ImpLine, MPLine, V4, V5),
    
    % STEP 6: Continue with SP2
    fitch_g4_proof(SP2, [MPLine:Cons, ImpLine:(Ant => Inter), ExtractLine:(Inter => Cons)|Context],
                  Scope, MPLine, NextLine, ResLine, V5, VarOut).

% =========================================================================
% QUANTIFICATION RULES
% =========================================================================

% R-forall
fitch_g4_proof(rall((_ > [(![Z-X]:A)]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, BodyLine, VarIn, V1),
    derive_formula(Scope, (![Z-X]:A), '$ \\forall I $ ~w', [BodyLine], rall(BodyLine),
                  SubEnd, NextLine, ResLine, V1, VarOut).

% L-forall: Universal elimination
fitch_g4_proof(lall((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses > _, SubProof, NewFormula),
    
    % Find the universal quantifier that generates NewFormula
    (
        % Case 1: NewFormula is a direct instance of a universal in Premisses
        (
            member((![Z-X]:Body), Premisses),
            % Check if Body (with substitution) gives NewFormula
            strip_annotations_deep(Body, StrippedBody),
            strip_annotations_deep(NewFormula, StrippedNew),
            unifiable(StrippedBody, StrippedNew, _),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 2: Search by equivalent structure
            member((![Z-X]:Body), Premisses),
            formulas_equivalent(Body, NewFormula),
            UniversalFormula = (![Z-X]:Body)
        ;
            % Case 3: Fallback - take the first (current behavior)
            select((![Z-X]:Body), Premisses, _),
            UniversalFormula = (![Z-X]:Body)
        )
    ),
    
    find_context_line(UniversalFormula, Context, UnivLine),
    derive_and_continue(Scope, NewFormula, '$ \\forall E $ ~w', [UnivLine], lall(UnivLine),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% R-exists
fitch_g4_proof(rex((_ > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    fitch_g4_proof(SubProof, Context, Scope, CurLine, SubEnd, _WitnessLine, VarIn, V1),
    % CORRECTION: Reference SubEnd (witness line), not WitnessLine
    derive_formula(Scope, Goal, '$ \\exists I $ ~w', [SubEnd], rex(SubEnd),
                  SubEnd, NextLine, ResLine, V1, VarOut).

% L-exists
fitch_g4_proof(lex((Premisses > [Goal]), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    select((?[Z-X]:Body), Premisses, _),
    find_context_line(?[Z-X]:Body, Context, ExistLine),
    extract_witness(SubProof, Witness),
    ( member(_:Witness, Context) ->
        fitch_g4_proof(SubProof, Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut)
    ; WitLine is CurLine + 1,
      NewScope is Scope + 1,
      assert_safe_fitch_line(WitLine, Witness, assumption, NewScope),
      render_hypo(Scope, Witness, 'AS', CurLine, WitLine, VarIn, V1),
      fitch_g4_proof(SubProof, [WitLine:Witness|Context], NewScope, WitLine, SubEnd, _GoalLine, V1, V2),
      ElimLine is SubEnd + 1,
      assert_safe_fitch_line(ElimLine, Goal, lex(ExistLine, WitLine, SubEnd), Scope),
      % CORRECTION: Reference SubEnd (last line of subproof)
      format(atom(Just), '$ \\exists E $ ~w,~w-~w', [ExistLine, WitLine, SubEnd]),
      render_have(Scope, Goal, Just, SubEnd, ElimLine, V2, VarOut),
      NextLine = ElimLine, ResLine = ElimLine
    ).

% L-exists-or: Combined existential-disjunction 
fitch_g4_proof(lex_lor((_ > [Goal]), SP1, SP2), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    SP1 =.. [_, (Prem1 > _)|_],
    SP2 =.. [_, (Prem2 > _)|_],
    member(WitA, Prem1), contains_skolem(WitA), \+ is_quantified(WitA),
    member(WitB, Prem2), contains_skolem(WitB), \+ is_quantified(WitB),
    WitLine is CurLine + 1,
    render_hypo(Scope, (WitA | WitB), 'AS', CurLine, WitLine, VarIn, V1),
    NewScope is Scope + 1,
    assume_in_scope(WitA, Goal, SP1, [WitLine:(WitA | WitB)|Context],
                   NewScope, WitLine, EndA, GoalA, V1, V2),
    assume_in_scope(WitB, Goal, SP2, [WitLine:(WitA | WitB)|Context],
                   NewScope, EndA, EndB, GoalB, V2, V3),
    DisjElim is EndB + 1,
    CaseAStart is WitLine + 1,
    CaseBStart is EndA + 1,
    format(atom(DisjJust), '$ \\lor E $ ~w,~w-~w,~w-~w',
           [WitLine, CaseAStart, GoalA, CaseBStart, GoalB]),
    render_have(NewScope, Goal, DisjJust, EndB, DisjElim, V3, V4),
    ElimLine is DisjElim + 1,
    format(atom(ExistJust), '$ \\exists E $ ~w-~w', [WitLine, DisjElim]),
    render_have(Scope, Goal, ExistJust, DisjElim, ElimLine, V4, VarOut),
    NextLine = ElimLine, ResLine = ElimLine.

% CQ_c: Classical quantifier conversion
fitch_g4_proof(cq_c((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((![Z-X]:A) => B, Premisses, _),
    find_context_line((![Z-X]:A) => B, Context, Line),
    derive_and_continue(Scope, NewFormula, '$ CQ_{c} $ ~w', [Line], cq_c(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% CQ_m: Minimal quantifier conversion
fitch_g4_proof(cq_m((Premisses > _), SubProof), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- !,
    extract_new_formula(Premisses, SubProof, NewFormula),
    select((?[Z-X]:A)=>B, Premisses, _),
    find_context_line((?[Z-X]:A)=>B, Context, Line),
    derive_and_continue(Scope, NewFormula, '$ CQ_{m} $ ~w', [Line], cq_m(Line),
                       SubProof, Context, CurLine, NextLine, ResLine, VarIn, VarOut).

% =========================================================================
% EQUALITY RULES
% =========================================================================

% Reflexivity
fitch_g4_proof(eq_refl(Delta), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_refl, Scope),
    render_have(Scope, Goal, '$ = I$', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Symmetry
fitch_g4_proof(eq_sym(_Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = B],
    find_context_line(B = A, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = B), eq_sym(EqLine), Scope),
    format(atom(Just), '$ = E $ ~w', [EqLine]),
    render_have(Scope, (A = B), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Transitivity
fitch_g4_proof(eq_trans(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = C],
    Gamma = [A = B, B = C | _Rest],  % Direct pattern matching
    find_context_line(A = B, Context, Line1),
    find_context_line(B = C, Context, Line2),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans(Line1, Line2), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [Line1, Line2]),
    render_have(Scope, (A = C), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution (Leibniz) - MAIN CASE
fitch_g4_proof(eq_subst(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal],
    Goal \= (_ = _),  % Not an equality
    
    % Extract equality and predicate from Gamma
    member(A = B, Gamma),
    member(Pred, Gamma),
    Pred \= (_ = _),
    Pred \= (A = B),
    
    % Verify that Goal is Pred with A replaced by B
    Pred =.. [PredName|Args],
    Goal =.. [PredName|GoalArgs],
    
    % Find position where substitution occurs
    nth0(Pos, Args, A),
    nth0(Pos, GoalArgs, B),
    
    % Find line numbers in context
    find_context_line(A = B, Context, EqLine),
    find_context_line(Pred, Context, PredLine),
    
    !,
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, Goal, eq_subst(EqLine, PredLine), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [EqLine, PredLine]),
    render_have(Scope, Goal, Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Congruence
fitch_g4_proof(eq_cong(_Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [LHS = RHS],
    LHS =.. [F|ArgsL],
    RHS =.. [F|ArgsR],
    find_diff_pos(ArgsL, ArgsR, _Pos, TermL, TermR),
    find_context_line(TermL = TermR, Context, EqLine),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (LHS = RHS), eq_cong(EqLine), Scope),
    format(atom(Just), '$ = E$ ~w', [EqLine]),
    render_have(Scope, (LHS = RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Substitution in equality
fitch_g4_proof(eq_subst_eq(Gamma>Delta), Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [Goal_LHS = Goal_RHS],
    member(X = Y, Gamma),
    member(Ctx_LHS = Ctx_RHS, Gamma),
    find_context_line(X = Y, Context, XY_Line),
    find_context_line(Ctx_LHS = Ctx_RHS, Context, Ctx_Line),
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (Goal_LHS = Goal_RHS), eq_subst_eq(XY_Line, Ctx_Line), Scope),
    format(atom(Just), '$ = E$ ~w,~w', [XY_Line, Ctx_Line]),
    render_have(Scope, (Goal_LHS = Goal_RHS), Just, CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% Chained transitivity
fitch_g4_proof(eq_trans_chain(_Gamma>Delta), _Context, Scope, CurLine, NextLine, ResLine, VarIn, VarOut) :- 
    !,
    Delta = [A = C],
    DerLine is CurLine + 1,
    assert_safe_fitch_line(DerLine, (A = C), eq_trans_chain, Scope),
    render_have(Scope, (A = C), '=E', CurLine, DerLine, VarIn, VarOut),
    NextLine = DerLine,
    ResLine = DerLine.

% =========================================================================
% FALLBACK
% =========================================================================

fitch_g4_proof(UnknownRule, _Context, _Scope, CurLine, CurLine, CurLine, VarIn, VarIn) :-
    format('% WARNING: Unknown rule ~w~n', [UnknownRule]).

% =========================================================================
%  END OF FITCH PRINTER 
% =========================================================================
