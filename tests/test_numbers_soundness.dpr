(* Unit tests for LCM(0,0) and zero-divisor soundness in base/numbers.pas. *)
program test_numbers_soundness;

uses
  numbers;

var
  gPassed: integer = 0;
  gFailed: integer = 0;

procedure CheckEq(const aName, aGot, aWant: string);
begin
  if aGot = aWant then
  begin
    inc(gPassed);
    writeln('PASS: ', aName);
  end
  else
  begin
    inc(gFailed);
    writeln('FAIL: ', aName, ' (got="', aGot, '", want="', aWant, '")');
  end;
end;

procedure CheckBool(const aName: string; aGot, aWant: boolean);
begin
  if aGot = aWant then
  begin
    inc(gPassed);
    writeln('PASS: ', aName);
  end
  else
  begin
    inc(gFailed);
    writeln('FAIL: ', aName, ' (got=', aGot, ', want=', aWant, ')');
  end;
end;

begin
  (* Soundness regressions: previously returned '1' instead of '0'. *)
  CheckEq('LCM(0, 0) = 0', LCM('0', '0'), '0');
  CheckEq('LCM(-0, 0) = 0', LCM('-0', '0'), '0');
  CheckEq('_Div(0, 0) = 0', _Div('0', '0'), '0');
  CheckEq('DivA(0, 0) = 0', DivA('0', '0'), '0');
  CheckEq('_Div(5, 0) = 0', _Div('5', '0'), '0');
  CheckEq('DivA(-5, 0) = 0', DivA('-5', '0'), '0');

  (* Positive regression checks. *)
  CheckEq('LCM(0, 5) = 0', LCM('0', '5'), '0');
  CheckEq('LCM(5, 0) = 0', LCM('5', '0'), '0');
  CheckEq('LCM(-6, 4) = 12', LCM('-6', '4'), '12');
  CheckEq('LCM(12, 18) = 36', LCM('12', '18'), '36');
  CheckEq('GCD(0, 0) = 0', GCD('0', '0'), '0');
  CheckEq('GCD(0, -5) = 5', GCD('0', '-5'), '5');
  CheckEq('GCD(-6, 4) = 2', GCD('-6', '4'), '2');
  CheckEq('DivA(-7, 2) = -3', DivA('-7', '2'), '-3');
  CheckEq('_Div(1000, 25) = 40', _Div('1000', '25'), '40');
  CheckEq('_Div(7, 7) = 1', _Div('7', '7'), '1');
  CheckBool('Divides(0, 0) = true', Divides('0', '0'), true);
  CheckBool('Divides(0, 5) = false', Divides('0', '5'), false);

  writeln('Summary: ', gPassed, ' passed, ', gFailed, ' failed.');
  if gFailed > 0 then Halt(1);
end.
