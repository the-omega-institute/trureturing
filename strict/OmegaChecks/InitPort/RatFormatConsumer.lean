module
prelude
public import OmegaInit.Data.Rat.Basic

/-- Render a normalized strict rational, including the separate integer branch of its Repr instance. -/
@[export omega_test_rat_format]
public def ratFormat (negative reprOutput : Bool) (num den : Nat) : Omega.String :=
  let signed := match negative with | .true => Omega.Int.negSucc num | .false => Omega.Int.ofNat num
  let r := Omega.mkRat signed den
  match reprOutput with
  | .true =>
    match @Omega.Repr.reprPrec Omega.Rat Omega.instReprRat r Nat.zero with
    | .text s => s
    | _ => Omega.String.ofList Omega.List.nil
  | .false => @Omega.ToString.toString Omega.Rat Omega.instToStringRat r
