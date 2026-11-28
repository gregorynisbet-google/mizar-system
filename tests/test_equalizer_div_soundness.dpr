(* Unit tests for integer division (rqDiv) soundness in kernel/equalizer.pas. *)
program test_equalizer_div_soundness;

uses
  mobjects, errhan, mizenv, mconsole, mscanner, numbers, builtin, lexicon, enums,
  correl, identify, prechecker, equalizer;

var
  gPassed: integer = 0;
  gFailed: integer = 0;
  gNextConstNr: integer = 0;

procedure IgnoreError(Pos: Position; ErrNr: integer);
begin
end;

function MkIntTyp: TypPtr;
begin
  Result := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 3, nil);
end;

function AddIntConst(aDetermined: boolean; aVal: integer): integer;
var
  lDef: ConstDefPtr;
begin
  inc(gNextConstNr);
  lDef := new(ConstDefPtr, Init(NewVarTrm(ikTrmConstant, gNextConstNr), MkIntTyp));
  if aDetermined then
  begin
    lDef^.fDetermined := true;
    lDef^.fNumericValue := IntToComplex(aVal);
  end;
  InferConstDef.Insert(lDef);
  Result := InferConstDef.Count - 1;
end;

function MkConstTrm(aIdx: integer): TrmPtr;
begin
  Result := NewVarTrm(ikTrmInfConst, aIdx);
end;

function MkDiv(aLeft, aRight: TrmPtr): TrmPtr;
begin
  Result := NewFuncTrm(gBuiltIn[rqDiv], NewTrmList(aLeft, NewTrmList(aRight, nil)));
end;

procedure CheckEquate(const aName: string; aFrm: FrmPtr; aEvalVal: integer; aExpectContr: boolean);
var
  lEval: NatFunc;
  lOk: boolean;
begin
  Basic.Init(4, 4);
  Basic.Insert(aFrm);
  lEval.InitNatFunc(4, 4);
  lEval.Assign(0, aEvalVal);

  ItIsChecker := true;
  BoundVarNbr := 0;
  Equate(lEval);
  if aExpectContr then
    lOk := (Contr > 0)
  else
    lOk := (Contr = 0);

  if lOk then
  begin
    inc(gPassed);
    writeln('PASS: ', aName);
  end
  else
  begin
    inc(gFailed);
    writeln('FAIL: ', aName, ' (Contr=', Contr, ', expected Contr',
            ' ', aExpectContr, ')');
  end;

  DispEqClassInTrms;
  DispEquations;
  ItIsChecker := false;
  lEval.Done;
  Basic.Done;
end;

procedure InitEqualizerEnv;
var
  lMode, lFunc: ConstrTypPtr;
  lPred: ConstrPtr;
begin
  StopOnError := false;
  PutError := @IgnoreError;
  gTermCollection.Init(40, 40);
  InitConstructors;
  RegisteredCluster.Init(0);
  FunctorCluster.InitSorted(0, CmpFuncCluster);
  ConditionalCluster.Init(0);
  gReductions.Init(0);
  InferConstDef.InitSorted(0, CompConstDef);

  { Mode 1: object (rqAny), Mode 2: set (rqSetMode), Mode 3: Integer }
  lMode := new(ConstrTypPtr, Init(coMode, 1, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqAny] := 1;

  lMode := new(ConstrTypPtr, Init(coMode, 2, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqSetMode] := 2;

  lMode := new(ConstrTypPtr, Init(coMode, 3, 'INT_1'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 2, nil);
  Constr[coMode].Insert(lMode);

  { Predicate 1: "=" (rqEqualsTo, reflexive & symmetric) }
  lPred := new(ConstrPtr, Init(coPredicate, 1, 'HIDDEN'));
  lPred^.fProperties := [syReflexivity, sySymmetry];
  lPred^.fFirstArg := 1;
  lPred^.fSecondArg := 2;
  Constr[coPredicate].Insert(lPred);
  gBuiltIn[rqEqualsTo] := 1;

  { Functor 1: "div" (rqDiv) }
  lFunc := new(ConstrTypPtr, Init(coFunctor, 1, 'INT_1'));
  lFunc^.fConstrTyp := MkIntTyp;
  Constr[coFunctor].Insert(lFunc);
  gBuiltIn[rqDiv] := 1;

  InitReverseRequirements;
  NonZeroTyp := MkIntTyp;
end;

var
  c0, c1, c2, c3, c5, cNeg7, cNeg4, cX: integer;

begin
  InitEqualizerEnv;

  c0 := AddIntConst(true, 0);
  c1 := AddIntConst(true, 1);
  c2 := AddIntConst(true, 2);
  c3 := AddIntConst(true, 3);
  c5 := AddIntConst(true, 5);
  cNeg7 := AddIntConst(true, -7);
  cNeg4 := AddIntConst(true, -4);
  cX := AddIntConst(false, 0);

  (* Valid 1 (first, with clean TrmS): symbolic x div 1 = x is TRUE (the intended divisor=1 rule). *)
  CheckEquate('prove symbolic x div 1 = x',
    NewEqFrm(MkDiv(MkConstTrm(cX), MkConstTrm(c1)), MkConstTrm(cX)),
    0, true);

  (* Soundness 1: 1 div 2 = 1 is FALSE, so its negation must not be refuted. *)
  CheckEquate('do not refute not(1 div 2 = 1)',
    NewEqFrm(MkDiv(MkConstTrm(c1), MkConstTrm(c2)), MkConstTrm(c1)),
    0, false);

  (* Soundness 2: 1 div 0 = 1 is FALSE, so its negation must not be refuted. *)
  CheckEquate('do not refute not(1 div 0 = 1)',
    NewEqFrm(MkDiv(MkConstTrm(c1), MkConstTrm(c0)), MkConstTrm(c1)),
    0, false);

  (* Soundness 3: 1 div 2 = 0 is TRUE, so assuming it must not derive contradiction. *)
  CheckEquate('do not derive contradiction from true premise (1 div 2 = 0)',
    NewEqFrm(MkDiv(MkConstTrm(c1), MkConstTrm(c2)), MkConstTrm(c0)),
    1, false);

  (* Soundness 4: symbolic x div 2 = x is FALSE (catches stale NumericValue read on lt1). *)
  CheckEquate('do not refute not(x div 2 = x)',
    NewEqFrm(MkDiv(MkConstTrm(cX), MkConstTrm(c2)), MkConstTrm(cX)),
    0, false);

  (* Valid 2: 1 div 2 = 0 is TRUE. *)
  CheckEquate('prove 1 div 2 = 0',
    NewEqFrm(MkDiv(MkConstTrm(c1), MkConstTrm(c2)), MkConstTrm(c0)),
    0, true);

  (* Valid 3: 5 div 1 = 5 is TRUE. *)
  CheckEquate('prove 5 div 1 = 5',
    NewEqFrm(MkDiv(MkConstTrm(c5), MkConstTrm(c1)), MkConstTrm(c5)),
    0, true);

  (* Valid 4: (-7) div 2 = -4 (floor division in INT_1). *)
  CheckEquate('prove (-7) div 2 = -4',
    NewEqFrm(MkDiv(MkConstTrm(cNeg7), MkConstTrm(c2)), MkConstTrm(cNeg4)),
    0, true);

  (* Valid 5: assuming false 2 div 1 = 3 derives contradiction. *)
  CheckEquate('refute false premise (2 div 1 = 3)',
    NewEqFrm(MkDiv(MkConstTrm(c2), MkConstTrm(c1)), MkConstTrm(c3)),
    1, true);

  writeln('Summary: ', gPassed, ' passed, ', gFailed, ' failed.');
  if gFailed > 0 then Halt(1);
end.
