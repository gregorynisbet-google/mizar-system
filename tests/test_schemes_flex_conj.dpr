(* Unit tests for flex-conjunction soundness in kernel/schemes.pas (SchEqFrm). *)
program test_schemes_flex_conj;

uses
  mobjects, errhan, mizenv, mconsole, builtin, lexicon, enums, correl, schemhan, schemes;

var
  gLastErrNr: integer = 0;
  gPassed: integer = 0;
  gFailed: integer = 0;

procedure CaptureError(Pos: Position; ErrNr: integer);
begin
  gLastErrNr := ErrNr;
end;

function MkNatTyp: TypPtr;
begin
  Result := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 3, nil);
end;

function MkNum(aVal: integer): TrmPtr;
begin
  Result := TrmPtr(NewVarTrm(ikTrmNumeral, aVal));
end;

function MkBound(aNr: integer): TrmPtr;
begin
  Result := TrmPtr(NewVarTrm(ikTrmBound, aNr));
end;

function MkSchConst(aNr: integer): TrmPtr;
begin
  Result := TrmPtr(NewLocFuncTrm(ikTrmSchFunc, aNr, nil));
end;

function MkBinFunc(aLeft, aRight: TrmPtr): TrmPtr;
begin
  Result := NewFuncTrm(1, NewTrmList(aLeft, NewTrmList(aRight, nil)));
end;

function MkEq(aLeft, aRight: TrmPtr): FrmPtr;
begin
  Result := NewPredFrm(ikFrmPred, gBuiltIn[rqEqualsTo],
    NewTrmList(aLeft, NewTrmList(aRight, nil)), 0);
end;

function MkLe(aLeft, aRight: TrmPtr): FrmPtr;
begin
  Result := NewPredFrm(ikFrmPred, 2,
    NewTrmList(aLeft, NewTrmList(aRight, nil)), 0);
end;

{ Encodes: for i being Nat st aLow <= i & i <= aHigh holds aBody }
function MkRangeForall(aLow, aHigh: TrmPtr; aBody: FrmPtr): FrmPtr;
begin
  Result := NewUniv(MkNatTyp,
    NewNeg(NewConj(MkLe(aLow, MkBound(1)),
           NewConj(MkLe(MkBound(1), aHigh), NewNeg(aBody)))));
end;

function MkFlex(aLeftFrm, aRightFrm, aExp: FrmPtr; aLeftTrm, aRightTrm: TrmPtr): FrmPtr;
begin
  Result := new(FlexFrmPtr, InitD(aLeftFrm, aRightFrm, aExp, aLeftTrm, aRightTrm));
end;

procedure Check(const aName: string;
                const aSchTypes: array of TypPtr;
                const aSchProps, aInstProps: array of FrmPtr;
                aExpectOk: boolean);
var
  lTypes, lProps: MCollection;
  lSch: SchRefItem;
  lSnts: MList;
  i: integer;
  lOk: boolean;
begin
  lTypes.Init(Length(aSchTypes), 4);
  for i := 0 to High(aSchTypes) do lTypes.Insert(aSchTypes[i]);
  lProps.Init(Length(aSchProps), 4);
  for i := 0 to High(aSchProps) do lProps.Insert(aSchProps[i]);
  lSch.Init(0, 1, lTypes, lProps, schStateQuotable);

  lSnts.Init(Length(aInstProps));
  for i := 0 to High(aInstProps) do lSnts.Insert(aInstProps[i]);

  ErrorNbr := 0;
  gLastErrNr := 0;
  CurPos.Line := 1;
  CurPos.Col := 1;
  Schematize(lSch, lSnts);

  if aExpectOk then
    lOk := (ErrorNbr = 0)
  else
    lOk := (ErrorNbr > 0);

  if lOk then
  begin
    inc(gPassed);
    writeln('PASS: ', aName);
  end
  else
  begin
    inc(gFailed);
    writeln('FAIL: ', aName, ' (ErrorNbr=', ErrorNbr, ', LastErrNr=', gLastErrNr, ')');
  end;

  lSnts.Done;
  lSch.SchTypes.Done;
  lSch.SchProps.Done;
end;

procedure InitFlexEnv;
var
  lMode, lFunc: ConstrTypPtr;
begin
  StopOnError := false;
  PutError := @CaptureError;
  gTermCollection.Init(40, 40);
  InitConstructors;

  { Mode 1: object (rqAny), Mode 2: set (rqSetMode), Mode 3: Nat (widens to set) }
  lMode := new(ConstrTypPtr, Init(coMode, 1, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqAny] := 1;

  lMode := new(ConstrTypPtr, Init(coMode, 2, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqSetMode] := 2;

  lMode := new(ConstrTypPtr, Init(coMode, 3, 'TEST'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 2, nil);
  Constr[coMode].Insert(lMode);

  { Predicate 1: "=" (rqEqualsTo), Predicate 2: "<=" }
  Constr[coPredicate].Insert(new(ConstrPtr, Init(coPredicate, 1, 'HIDDEN')));
  gBuiltIn[rqEqualsTo] := 1;
  Constr[coPredicate].Insert(new(ConstrPtr, Init(coPredicate, 2, 'TEST')));

  { Functor 1: binary Nat -> Nat (e.g. truncated subtraction -') }
  lFunc := new(ConstrTypPtr, Init(coFunctor, 1, 'TEST'));
  lFunc^.fConstrTyp := MkNatTyp;
  Constr[coFunctor].Insert(lFunc);

  { Numeral type: NonZeroTyp is used by CopyTrmType for ikTrmNumeral }
  NonZeroTyp := MkNatTyp;
end;

begin
  InitFlexEnv;

  (* Soundness 1: matching endpoints (A():=f(1,0), B():=f(1,1)) but different nExpansion
     (range [0,1] on f(1,i)=2 vs range [f(1,0), f(1,1)] on i=2). *)
  Check('reject flex-conj with matching endpoints but mismatched expansion (range/body)',
    [ MkNatTyp, MkNatTyp ],
    [ MkFlex(MkEq(MkSchConst(1), MkNum(2)),
             MkEq(MkSchConst(2), MkNum(2)),
             MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))),
             MkSchConst(1), MkSchConst(2)),
      MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))) ],
    [ MkFlex(MkEq(MkBinFunc(MkNum(1), MkNum(0)), MkNum(2)),
             MkEq(MkBinFunc(MkNum(1), MkNum(1)), MkNum(2)),
             MkRangeForall(MkNum(0), MkNum(1), MkEq(MkBinFunc(MkNum(1), MkBound(1)), MkNum(2))),
             MkNum(0), MkNum(1)),
      MkRangeForall(MkBinFunc(MkNum(1), MkNum(0)), MkBinFunc(MkNum(1), MkNum(1)),
                    MkEq(MkBound(1), MkNum(2))) ],
    false);

  (* Soundness 2: same numeric endpoints, different quantified body in nExpansion. *)
  Check('reject flex-conj with matching endpoints but different expansion body',
    [ MkNatTyp, MkNatTyp ],
    [ MkFlex(MkEq(MkSchConst(1), MkSchConst(1)),
             MkEq(MkSchConst(2), MkSchConst(2)),
             MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkBound(1))),
             MkSchConst(1), MkSchConst(2)) ],
    [ MkFlex(MkEq(MkNum(0), MkNum(0)),
             MkEq(MkNum(1), MkNum(1)),
             MkRangeForall(MkNum(0), MkNum(1), MkEq(MkBound(1), MkNum(2))),
             MkNum(0), MkNum(1)) ],
    false);

  (* Valid 1: matching endpoints AND matching expansion on numerals. *)
  Check('accept flex-conj with matching endpoints and matching expansion',
    [ MkNatTyp, MkNatTyp ],
    [ MkFlex(MkEq(MkSchConst(1), MkNum(2)),
             MkEq(MkSchConst(2), MkNum(2)),
             MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))),
             MkSchConst(1), MkSchConst(2)),
      MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))) ],
    [ MkFlex(MkEq(MkNum(0), MkNum(2)),
             MkEq(MkNum(1), MkNum(2)),
             MkRangeForall(MkNum(0), MkNum(1), MkEq(MkBound(1), MkNum(2))),
             MkNum(0), MkNum(1)),
      MkRangeForall(MkNum(0), MkNum(1), MkEq(MkBound(1), MkNum(2))) ],
    true);

  (* Valid 2: matching functor endpoints AND matching expansion. *)
  Check('accept flex-conj with functor endpoints when expansion also matches',
    [ MkNatTyp, MkNatTyp ],
    [ MkFlex(MkEq(MkSchConst(1), MkNum(2)),
             MkEq(MkSchConst(2), MkNum(2)),
             MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))),
             MkSchConst(1), MkSchConst(2)),
      MkRangeForall(MkSchConst(1), MkSchConst(2), MkEq(MkBound(1), MkNum(2))) ],
    [ MkFlex(MkEq(MkBinFunc(MkNum(1), MkNum(0)), MkNum(2)),
             MkEq(MkBinFunc(MkNum(1), MkNum(1)), MkNum(2)),
             MkRangeForall(MkBinFunc(MkNum(1), MkNum(0)), MkBinFunc(MkNum(1), MkNum(1)),
                           MkEq(MkBound(1), MkNum(2))),
             MkBinFunc(MkNum(1), MkNum(0)), MkBinFunc(MkNum(1), MkNum(1))),
      MkRangeForall(MkBinFunc(MkNum(1), MkNum(0)), MkBinFunc(MkNum(1), MkNum(1)),
                    MkEq(MkBound(1), MkNum(2))) ],
    true);

  writeln('Summary: ', gPassed, ' passed, ', gFailed, ' failed.');
  if gFailed > 0 then Halt(1);
end.
