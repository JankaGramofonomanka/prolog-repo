

% General Utils ---------------------------------------------------------------
:- dynamic flag/2.
flag(dummy, default).
defaultValue(lastCallNumber, 0).
defaultValue(lastFailureState, (0, 0)).
defaultValue(skip, false).

getFlag(P, V) :- flag(P, V), !.

getFlag(P, Default) :- defaultValue(P, Default), !.
getFlag(_P, default).


setFlag(P, V) :-
  retract(flag(P, _)),
  !,
  assert(flag(P, V)).

setFlag(P, V) :-
  assert(flag(P, V)).


% -----------------------------------------------
concat((A, B), C, (A, BC)) :- !, concat(B, C, BC).
concat(A, B, (A, B)).

% -----------------------------------------------
% myRead(-Result)
myRead(Result) :-
  get_char(C),
  ( C = '\n' -> Result = nil

  ;             myRead(Rest),
                myAtomConcat(C, Rest, Result) 
  ).

% myAtomConcat(+Left, +Right, -LeftRight)
myAtomConcat(nil, Atom, Atom) :- !.
myAtomConcat(Atom, nil, Atom) :- !.
myAtomConcat(Atom1, Atom2, Atom) :- atom_concat(Atom1, Atom2, Atom).

% Debugger Utils --------------------------------------------------------------
incrLastCallNumber :-
  getFlag(lastCallNumber, LastCallNumber),
  setFlag(lastCallNumber, LastCallNumber + 1).

incrAndGetLastCallNumber(LastCallNumber) :-
  incrLastCallNumber,
  getFlag(lastCallNumber, LastCallNumber).

resetLastCallNumber :-
  setFlag(lastCallNumber, 0).

resetLastFailureState :-
  setFlag(lastFailureState, (0, 0)).

resetSkip :-
  setFlag(skip, false).

turnSkipOn :- setFlag(skip, true).
turnSkipOff :- setFlag(skip, false).

% turnSkipOnIfAplicable(+CMD)
turnSkipOnIfAplicable(CMD) :- 
  ( CMD = cmdSkip ->  turnSkipOn
  ;                   true
  ).

% turnSkipOffIfAplicable(+CMD)
turnSkipOffIfAplicable(CMD) :- 
  ( CMD = cmdSkip ->  turnSkipOff
  ;                   true
  ).

% mkState(+Depth, +CallNumber, -State)
mkState(Depth, CallNumber, (Depth, CallNumber)).


% printEventAndPrompt(+EventKind, +Term, +State, -CMD)
printEventAndPrompt(EventKind, Term, (Depth, CallNumber), CMD) :-
  
  getFlag(skip, Skip),
  ( Skip -> 
      CMD = cmdNull

  ;   format("~d \t~d \t[~s] ~p ? ", [CallNumber, Depth, EventKind, Term]),
      getCMD(CMD),
      ( CMD = cmdAbort, !, abort
      ; CMD = cmdExit,  !, halt
      ; true
      )
  ).
    
% printEventAndPrompt(+EventKind, +Term, +State)
printEventAndPrompt(EventKind, Term, State) :-
  printEventAndPrompt(EventKind, Term, State, _CMD).

% getCMD(-CMD)
getCMD(CMD) :-
    myRead(C),
    ( C = nil,    !, CMD = cmdCreep
    ; C = creep,  !, CMD = cmdCreep
    ; C = c,      !, CMD = cmdCreep

    ; C = skip,   !, CMD = cmdSkip
    ; C = s,      !, CMD = cmdSkip

    ; C = abort,  !, CMD = cmdAbort
    ; C = a,      !, CMD = cmdAbort

    ; C = exit,   !, CMD = cmdExit
    ; C = e,      !, CMD = cmdExit

    ; format("unsupported command: ~s\n", [C]),
      print('supported commands:\n'),
      print('creep / c / RET - creep\n'),
      print('skip  / s       - skip\n'),
      print('abort / a       - abort\n'),
      print('exit  / e       - exit\n'),
      getCMD(CMD)
    ).

% printRedoIfSecondCall(+Atom, +State, -CMD)
printRedoIfSecondCall(Atom, (Depth, CallNumber), CMD) :-
  getFlag(lastCallNumber, LastCallNumber),
  ( LastCallNumber > CallNumber ->
      printEventAndPrompt('redo', Atom, (Depth, CallNumber), CMD)
  
  ;   CMD = cmdNull
  ).

% -----------------------------------------------
printAndFail(Atom, State) :-
  printEventAndPrompt('fail', Atom, State),
  setFlag(lastFailureState, State),
  fail.

% myFail(+Atom, +State)
myFail(Atom, State) :-
  State = (Depth, CallNumber),
  getFlag(lastFailureState, (LastFailureDepth, LastFailureCallNumber)),

  ( CallNumber  > LastFailureCallNumber, !, printAndFail(Atom, State)
  ; Depth       < LastFailureDepth,      !, printAndFail(Atom, State)
  ; fail
  ).


% Actual Debugger -------------------------------------------------------------
% myTrace(+Atom)
myTrace(Atom) :-

  resetLastCallNumber,
  resetLastFailureState,
  resetSkip,
  
  myTrace(Atom, (0, 0)).

  % I do not clean up the flags, after the execution, because in case the
  % user decides to find another solution, the flags will be alredy cleaned up
  % and distort the subsequent execution of the debugger.
  % Instead I clean up the flugs before debugging.


% myTrace(+Atom, +State)
myTrace(true, _State) :- !, incrLastCallNumber.

myTrace(Atom, (Depth, _CallNumber)) :-

    incrAndGetLastCallNumber(NewCallNumber),

    mkState(Depth + 1, NewCallNumber, NewState),
    printEventAndPrompt('call', Atom, NewState, CMD),

    ( CMD = cmdSkip ->  ( turnSkipOn,
                          myTraceGoal(Atom, NewState),
                          turnSkipOff
                        ;
                          turnSkipOff,
                          myFail(Atom, NewState)
                        )

    ; 
                        ( myTraceGoal(Atom, NewState)
                        ; myFail(Atom, NewState)
                        )
    ),

    printEventAndPrompt('exit', Atom, NewState).


% -----------------------------------------------
% myTraceGoal(+Atom, +State)
myTraceGoal(Atom, State) :-
  ( predicate_property(Atom, dynamic) ->
      
      clause(Atom, Body),

      printRedoIfSecondCall(Atom, State, CMD),
      turnSkipOnIfAplicable(CMD),

      ( myTraceBodyTillCut(Body, AfterCut, HadCut, State) ; turnSkipOffIfAplicable(CMD), fail ),

      ( HadCut -> !,
                  ( myTraceBody(AfterCut, State)          ; turnSkipOffIfAplicable(CMD), fail )
                  ; 
                  true
      ),

      turnSkipOffIfAplicable(CMD)
  
  ;   call(Atom)
  ).


% -----------------------------------------------
% myTraceBody(+Body, +State)
myTraceBody(Body, State) :-
  myTraceBodyTillCut(Body, AfterCut, HadCut, State),
  ( HadCut -> !,
              myTraceBody(AfterCut, State)
              ;
              true
  ).

% -----------------------------------------------
% myTraceBodyTillCut(+Body, -AfterCut, -HadCut, +State)

% % Body = (First, Second)

% % % First = (_ ; _)
myTraceBodyTillCut(((Left ; _Right), AfterAlt), AfterCut, HadCut, State) :-
  myTraceAlternativeTillCut(Left, LeftAfterCut, LeftHadCut, State),
  ( LeftHadCut  ->  HadCut = true,
                    concat(LeftAfterCut, AfterAlt, AfterCut)
                    ;
                    myTraceBodyTillCut(AfterAlt, AfterCut, HadCut, State)
  ).

myTraceBodyTillCut(((_Left ; Right), AfterAlt), AfterCut, HadCut, State) :- !,
  myTraceAlternativeTillCut(Right, RightAfterCut, RightHadCut, State),
  ( RightHadCut ->  HadCut = true,
                    concat(RightAfterCut, AfterAlt, AfterCut)
                    ;
                    myTraceBodyTillCut(AfterAlt, AfterCut, HadCut, State)
  ).

% % % First = (_, _)
myTraceBodyTillCut(((First, Rest1), Rest2), AfterCut, HadCut, State) :- !,
  concat(Rest1, Rest2, Rest),
  myTraceBodyTillCut((First, Rest), AfterCut, HadCut, State).

% % % First = _
myTraceBodyTillCut((!, AfterCut), AfterCut, true, _State) :- !.

myTraceBodyTillCut((First, Rest), AfterCut, HadCut, State) :- !,
  myTrace(First, State),
  myTraceBodyTillCut(Rest, AfterCut, HadCut, State).

% % Body = (_ ; _)
myTraceBodyTillCut((Left; _Right), AfterCut, HadCut, State) :-
  myTraceBodyTillCut(Left, AfterCut, HadCut, State).

myTraceBodyTillCut((_Left; Right), AfterCut, HadCut, State) :- !,
  myTraceBodyTillCut(Right, AfterCut, HadCut, State).

% % Body = _
myTraceBodyTillCut(!, true, true, _State) :- !.
%myTraceBodyTillCut(true, true, false, _State) :- !.
myTraceBodyTillCut(Atom, true, false, State) :- myTrace(Atom, State).



