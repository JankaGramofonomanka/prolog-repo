:- set_prolog_flag(double_quotes, chars).

% `transform` is a DCG grammar, which transforms a DCG rule into a prolog clause
% for example:
%   ?- phrase(
%         transform(W), 
%         "nt(X, Y) --> n2(X), { pred(Y) }, [T], n3(Y)."
%       ), 
%       format("~s\n", [W]).
%
% should print
%   nt(X, Y, A, B) :- A = [a | C], n2(X, C, D), pred(Y), D = [T | E], n3(Y, E, F), B = F.

transform(Clause) -->
    { setFlag(xCount, 0) },

    spaces,
    head(Pred, Args),
    spaces,
    "-->",
    spaces,
    body(Body, A, B),
    spaces,
    
    { append(Args, [A, B], ActualArgs) },
    { mkApplication(Pred, ActualArgs, Head) },
    { concat([Head, " :- ", Body], Clause) },
    { removeFlag(xCount) }.


% head(-Pred, -Args)
head(Pred, Args) --> ident(Pred), args(Args).


% body(-Body, -A, -B)
body(Body, A, C)  --> atom(A, B, AtomSegments, GenVar),
                      spaces,
                      restOfBody(RestOfBody, B, C),
                      { ( GenVar -> freshVar(A) ; true ),
                        concat(AtomSegments, Atom),
                        concat([Atom, RestOfBody], Body)
                      }.

restOfBody(RestOfBody,  A, B) --> ", ", body(Body, A, B), { concat([", ", Body], RestOfBody) }.
restOfBody(".",         B, B) --> ".", { freshVar(B) }.


% atom(+A, +B, -AtomSegments, -GenVar)
% - `AtomSegments` is a list of strings and variables, that when concatenated 
%   (after the variables are instantiated), will form a string representing the atom.
% - `GenVar` tells us whether to generate a new variable or not.
atom(A, B, [A, " = " | SB], true) --> ['['], spaces, symbols(S), spaces, [']'], { prependItems(S, B, SB) }.
atom(A, B, [A, " = " | SB], true) --> ['"'], string(S), ['"'],                  { prependItems(S, B, SB) }.
atom(A, B, AtomSegments,    true) --> ident(Pred),
                                      args(Args),
                                      { append(Args, [A, B], ActualArgs),
                                        mkApplicationSegments(Pred, ActualArgs, AtomSegments)
                                      }.
atom(A, A, [Clauses], false)      --> "{", spaces, prolog(Clauses), spaces, "}".


symbols(S) --> symbols1(S), !.
symbols([]) --> [].

symbols1([H | T])  --> varOrIdent(H), !, restOfSymbols(T).

restOfSymbols(T) --> ",", spaces, symbols1(T).
restOfSymbols([]) --> "".


% string(-SingletonStrings)
% - `SingletonStrings` is a list of single-character strings, that when
%   concatenated, form the parsed string.
string([[H] | T]) --> [H], { H \= '"' }, !, string(T).
string([]) --> [].



freshVar(Var) :-
  getFlag(xCount, N),
  uintToString(N, NString),
  Var = ['X' | NString],
  incrFlag(xCount).







% -----------------------------------------------------------------------------
prolog("") --> "".
prolog(Prolog) -->
  nonEmptyProlog(ParsedProlog, Sep), 
  { ( Sep = "," ->  Prolog = ParsedProlog
                ;   concat(["(", ParsedProlog, ")"], Prolog)
  ) }.

nonEmptyProlog(Prolog, Sep) -->
  prologItem(Item),
  spaces,
  restOfProlog(RestOfProlog, Sep),
  { append(Item, RestOfProlog, Prolog) }.

restOfProlog(RestOfProlog, ",") --> ",", spaces, nonEmptyProlog(Prolog, ","), { append(", ", Prolog, RestOfProlog) }.
restOfProlog(RestOfProlog, ";") --> ";", spaces, nonEmptyProlog(Prolog, ";"), { append("; ", Prolog, RestOfProlog) }.
restOfProlog("", _) --> "".

prologItem("true") --> "true", !.
prologItem("false") --> "false", !.
prologItem(Item) --> ident(Pred), args(Args), { mkApplication(Pred, Args, Item) }.
prologItem(Item) --> expr(Left), spaces, predOperator(Op), spaces, expr(Right), { concat([Left, " ", Op, " ", Right], Item) }.
prologItem(Item) --> "(", spaces, nonEmptyProlog(Prolog, _), spaces, ")", { concat(["(", Prolog, ")"], Item) }.







% -----------------------------------------------------------------------------
is_lowercase(Char)  :- char_code(Char, Code), 0'a =< Code, Code =< 0'z.
is_uppercase(Char)  :- char_code(Char, Code), 0'A =< Code, Code =< 0'Z.
is_number(Char)     :- char_code(Char, Code), 0'0 =< Code, Code =< 0'9.
is_floor(Char)      :- Char = '_'.

lowercase(Char) --> [Char], { is_lowercase(Char) }.
uppercase(Char) --> [Char], { is_uppercase(Char) }.

floor(Char) --> [Char], { is_floor(Char) }.

allowed_char(Char) -->
  [Char],
  { is_lowercase(Char)
  ; is_uppercase(Char)
  ; is_number(Char)
  ; is_floor(Char)
  }.


allowed_chars([H | T]) --> allowed_char(H), !, allowed_chars(T).
allowed_chars([]) --> [].





ident(Id) --> lowercase(H), allowed_chars(T), { Id = [H | T] }.

variable(Var) --> uppercase(H), allowed_chars(T), { Var = [H | T], checkFreshVarCollision(Var) }.
variable(Var) --> floor(H),     allowed_chars(T), { Var = [H | T], checkFreshVarCollision(Var) }.

checkFreshVarCollision(Var) :-
  ( phrase(freshVarGrammar(N), Var) -> 
      getFlag(xCount, XCount),
      ( N >= XCount -> SuccN is N + 1, setFlag(xCount, SuccN) ; true )
    ;
      true
  ).

freshVarGrammar(N) --> "X", uint(N).



list(L) --> "[", spaces, innerList(IL), spaces, "]", { concat(["[", IL, "]"], L) }.

innerList(L) --> innerList1(L), !.
innerList("") --> "".

innerList1(L) --> expr(V), spaces, restOfInnerList(Rest), { append(V, Rest, L) }.

restOfInnerList(RestOfInnerList) --> ",", spaces, innerList1(InnerList),  { append(", ", InnerList, RestOfInnerList) }.
restOfInnerList(RestOfInnerList) --> "|", spaces, expr(V),                { append(" | ", V, RestOfInnerList) }.
restOfInnerList("") --> "".


operator("+")   --> "+",    !.
operator("-")   --> "-",    !.
operator("**")  --> "**",   !.
operator("*")   --> "*",    !.
operator("//")  --> "//",   !.
operator("/")   --> "/",    !.
operator("^")   --> "^",    !.
operator("mod") --> "mod",  !.
operator("rem") --> "rem".

predOperator("=:=")   --> "=:=",  !.
predOperator("=\\=")  --> "=\\=", !.
predOperator("=..")   --> "=..",  !.
predOperator("==")    --> "==",   !.
predOperator("=<")    --> "=<",   !.
predOperator("=")     --> "=",    !.
predOperator("\\==")  --> "\\==", !.
predOperator("\\=")   --> "\\=",  !.
predOperator(">=")    --> ">=",   !.
predOperator(">")     --> ">",    !.
predOperator("<")     --> "<",    !.
predOperator("is")    --> "is".


varOrIdent(Id)  --> ident(Id).
varOrIdent(Var) --> variable(Var).


args([])      --> "".
args([H | T]) --> "(", values([H | T]), ")".

values([Arg])   --> expr(Arg).
values([H | T]) --> expr(H), ",", spaces, values(T).

value(Val) --> variable(Val).
value(Val) --> ident(Func), args(Args), { mkApplication(Func, Args, Val) }.
value(Val) --> intS(Val).
value(Val) --> list(Val).

intS(S) --> "-", uint(N), { uintToString(N, SN), S = ['-' | SN] }.
intS(S) --> uint(N), { uintToString(N, S) }.



expr(Expr) --> value(Val), spaces, restOfExpr(RestOfExpr), { append(Val, RestOfExpr, Expr) }.
expr(Expr) --> "(", spaces, expr(L), spaces, ")", spaces, restOfExpr(RestOfExpr), { concat(["(", L, ")", RestOfExpr], Expr)}.

restOfExpr(RestOfExpr) --> operator(Op), !, spaces, expr(Expr), { concat([" ", Op, " ", Expr], RestOfExpr) }.
restOfExpr("") --> "".







% utils -----------------------------------------------------------------------

% concat(+Lists, -List)
concat([], "").
concat([H | T], HT) :- concat(T, S), append(H, S, HT).

intersparse([], _Sep, []).
intersparse([X], _Sep, [X]) :- !.
intersparse([H | T], Sep, [H, Sep | IT]) :- intersparse(T, Sep, IT).

spaces --> " ", !, spaces.
spaces --> "".



% mkApplication(+Func, +Args, -FuncAppliedToArgs)
mkApplication(Func, Args, FuncAppliedToArgs) :-
  mkApplicationSegments(Func, Args, Segments),
  concat(Segments, FuncAppliedToArgs).

% mkApplicationSegments(+Func, +Args, -Segments)
mkApplicationSegments(Func, [], [Func]) :- !.
mkApplicationSegments(Func, Args, AppSegments) :-
  intersparse(Args, ", ", ArgsSegments),
  concat([[Func, "("], ArgsSegments, [")"]], AppSegments).



% prependItems(+Items, +Tail, -ItemsAndTail)
prependItems([], S, [S]) :- !.
prependItems(Items, Post, ["[", ListedItems, " | ", Post, "]"]) :- 
  intersparse(Items, ", ", Segments),
  concat(Segments, ListedItems).



uint(N) --> uint1(N, _).

uint1(N, K) --> digit(D), restOfUInt(NN, PredK), { K is PredK + 1, N is D * (10 ^ K) + NN }.

restOfUInt(0, -1) --> "".
restOfUInt(N, K) --> uint1(N, K).

is_digit_code(Code) :- 0'0 =< Code, Code =< 0'9.

is_digit(D) :- char_code(D, DC), is_digit_code(DC).

digit(D) --> [C], { char_code(C, Code), is_digit_code(Code), D is Code - 0'0 }.     %'}



codesToString([], []).
codesToString([Code | Codes], [Char | Chars]) :- char_code(Char, Code), codesToString(Codes, Chars).

uintToString(N, SN) :-
  number_codes(N, Codes),
  codesToString(Codes, SN).



printstr(S) :- format("~s\n", [S]).
printstrList([]).
printstrList([H | T]) :- printstr(H), printstrList(T).

transformAndPrint(S) :- phrase(transform(Clause), S), printstr(Clause).







% flags -----------------------------------------------------------------------
:- dynamic flag/2.
flag(dummy, default).
defaultValue(xCount, 0).

getFlag(P, V) :- flag(P, V), !.
getFlag(P, Default) :- defaultValue(P, Default), !.
getFlag(_, default).


setFlag(P, V) :-
  retract(flag(P, _)),
  !,
  assert(flag(P, V)).

setFlag(P, V) :-
  assert(flag(P, V)).

removeFlag(P) :- retract(flag(P, _)).

incrFlag(P) :-
  getFlag(P, V),
  SuccV is V + 1,
  setFlag(P, SuccV).







