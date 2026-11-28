(* Unit tests for struct widening soundness in kernel/schemes.pas (SchWidennings). *)
program test_schemes_struct_widening;

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

function MkSetTyp: TypPtr;
begin
  Result := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 2, nil);
end;

function MkStructTyp(aStructNr: integer; aArg: TrmPtr): TypPtr;
begin
  Result := NewStandardTyp(ikTypStruct, NewEmptyCluster, NewEmptyCluster,
    aStructNr, NewTrmList(aArg, nil));
end;

function MkConst(aNr: integer): TrmPtr;
begin
  Result := TrmPtr(NewVarTrm(ikTrmConstant, aNr));
end;

function MkSchConst(aNr: integer): TrmPtr;
begin
  Result := TrmPtr(NewLocFuncTrm(ikTrmSchFunc, aNr, nil));
end;

function MkEq(aLeft, aRight: TrmPtr): FrmPtr;
begin
  Result := NewPredFrm(ikFrmPred, gBuiltIn[rqEqualsTo],
    NewTrmList(aLeft, NewTrmList(aRight, nil)), 0);
end;

function MkExistsStruct(aStructTyp: TypPtr; aBody: FrmPtr): FrmPtr;
begin
  Result := NewNeg(NewUniv(aStructTyp, NewNeg(aBody)));
end;

procedure Check(const aName: string;
                const aSchTypes: array of TypPtr;
                const aSchProps, aInstProps: array of FrmPtr;
                aExpectOk: boolean; aExpectErr: integer);
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
  else if aExpectErr > 0 then
    lOk := (ErrorNbr > 0) and (gLastErrNr = aExpectErr)
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

procedure InitStructEnv;
var
  lMode: ConstrTypPtr;
  lS1, lS2, lS3: StructConstrPtr;
begin
  StopOnError := false;
  PutError := @CaptureError;
  gTermCollection.Init(40, 40);
  InitConstructors;

  { Mode 1: object (rqAny), Mode 2: set (rqSetMode) }
  lMode := new(ConstrTypPtr, Init(coMode, 1, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqAny] := 1;

  lMode := new(ConstrTypPtr, Init(coMode, 2, 'HIDDEN'));
  lMode^.fConstrTyp := NewStandardTyp(ikTypMode, NewEmptyCluster, NewEmptyCluster, 1, nil);
  Constr[coMode].Insert(lMode);
  gBuiltIn[rqSetMode] := 2;

  { Predicate 1: "=" (rqEqualsTo) }
  Constr[coPredicate].Insert(new(ConstrPtr, Init(coPredicate, 1, 'HIDDEN')));
  gBuiltIn[rqEqualsTo] := 1;

  { Struct 1: Base over X (# f1 #) }
  lS1 := new(StructConstrPtr, Init(1, 'TEST'));
  lS1^.fPrefixes.Init(0, 0);
  lS1^.fFields := new(NatSetPtr, Init(1, 1));
  lS1^.fFields^.InsertElem(1);
  Constr[coStructMode].Insert(lS1);

  { Struct 2: Sub(Base over X) over X (# f1, f2 #) }
  lS2 := new(StructConstrPtr, Init(2, 'TEST'));
  lS2^.fPrefixes.Init(1, 1);
  lS2^.fPrefixes.Insert(MkStructTyp(1, TrmPtr(NewVarTrm(ikTrmLocus, 1))));
  lS2^.fFields := new(NatSetPtr, Init(2, 2));
  lS2^.fFields^.InsertElem(1);
  lS2^.fFields^.InsertElem(2);
  Constr[coStructMode].Insert(lS2);

  { Struct 3: Unrelated over X (# f1, f2 #) -- superset of Base fields, no widening path }
  lS3 := new(StructConstrPtr, Init(3, 'TEST'));
  lS3^.fPrefixes.Init(0, 0);
  lS3^.fFields := new(NatSetPtr, Init(2, 2));
  lS3^.fFields^.InsertElem(1);
  lS3^.fFields^.InsertElem(2);
  Constr[coStructMode].Insert(lS3);

  { Fixed constants: c1 = S1 : set, c2 = S2 : set, c3 = A : Sub over S1, c4 = U : Unrelated over S1 }
  FixedVar[1].nTyp := MkSetTyp;
  FixedVar[2].nTyp := MkSetTyp;
  FixedVar[3].nTyp := MkStructTyp(2, MkConst(1));
  FixedVar[4].nTyp := MkStructTyp(3, MkConst(1));
end;

begin
  InitStructEnv;

  (* Soundness: scheme { X() -> set, A() -> Base over X() }: ex B being Base over X() st B = A().
     Must reject X() := S2, A() := (Sub over S1) when S1 <> S2. *)
  Check('reject widening (Sub over S1) to (Base over S2) with S1 <> S2',
    [ MkSetTyp, MkStructTyp(1, MkSchConst(1)) ],
    [ MkExistsStruct(MkStructTyp(1, MkSchConst(1)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkSchConst(2))) ],
    [ MkExistsStruct(MkStructTyp(1, MkConst(2)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkConst(3))) ],
    false, 26);

  (* Soundness: must reject unrelated struct with superset fields and no widening path. *)
  Check('reject widening (Unrelated over S1) to (Base over S1) with no widening path',
    [ MkSetTyp, MkStructTyp(1, MkSchConst(1)) ],
    [ MkExistsStruct(MkStructTyp(1, MkSchConst(1)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkSchConst(2))) ],
    [ MkExistsStruct(MkStructTyp(1, MkConst(1)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkConst(4))) ],
    false, 26);

  (* Valid: widening (Sub over S1) to (Base over S1) with matching parameter. *)
  Check('accept widening (Sub over S1) to (Base over S1) with matching parameter',
    [ MkSetTyp, MkStructTyp(1, MkSchConst(1)) ],
    [ MkExistsStruct(MkStructTyp(1, MkSchConst(1)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkSchConst(2))) ],
    [ MkExistsStruct(MkStructTyp(1, MkConst(1)), MkEq(TrmPtr(NewVarTrm(ikTrmBound, 1)), MkConst(3))) ],
    true, 0);

  (* Valid: widening (Sub over S1) binds unbound X() := S1 via SchCompTyp. *)
  Check('accept widening (Sub over S1) binding X() := S1',
    [ MkSetTyp, MkStructTyp(1, MkSchConst(1)) ],
    [ MkEq(MkSchConst(2), MkSchConst(2)), MkEq(MkSchConst(1), MkSchConst(1)) ],
    [ MkEq(MkConst(3), MkConst(3)), MkEq(MkConst(1), MkConst(1)) ],
    true, 0);

  writeln('Summary: ', gPassed, ' passed, ', gFailed, ' failed.');
  if gFailed > 0 then Halt(1);
end.
