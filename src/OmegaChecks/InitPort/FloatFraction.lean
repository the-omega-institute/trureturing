module
public import Lean
public import OmegaChecks.InitPort.Alternatives.FloatFraction
import all OmegaChecks.InitPort.Alternatives.FloatFraction

open Lean Float.Model Float.Model.UnpackedFloat

namespace OmegaChecks.InitPort.FloatFraction

/-- The encoding has a sign, an exponent one below the bias and a mantissa with its
leading one implicit. The integer equality reconstructs the input as a dyadic number. -/
private def spec {F : Type} (fmt : Float.Model.Format) (bits : F → BitVec fmt.numBits) (x : F)
    (u : UnpackedFloat) (result : F × Int) : Prop :=
  match u with
  | .finite s m e _ => ∃ shift q : Nat,
      2 ^ fmt.mantissaBitsWithoutImplicit ≤ q ∧ q < 2 ^ (fmt.mantissaBitsWithoutImplicit + 1) ∧
      q = m * 2 ^ shift ∧ e = result.2 - (fmt.mantissaBitsWithoutImplicit + 1 : Int) + shift ∧
      bits result.1 = packComponents fmt s (BitVec.ofNat _ (fmt.exponentBias - 1)) (BitVec.ofNat _ q)
  | _ => result = (x, 0)

private def fits (w : Nat) : UnpackedFloat → Prop
  | .finite _ m _ _ => m < 2 ^ (w+1)
  | _ => True

private theorem unpackFits (fmt : Float.Model.Format) (bits : BitVec fmt.numBits) :
    fits fmt.mantissaBitsWithoutImplicit (UnpackedFloat.unpack fmt bits) := by
  unfold UnpackedFloat.unpack
  dsimp only
  split
  · split <;> trivial
  · split
    · split
      · trivial
      · exact Nat.lt_trans (unpackMantissa bits).isLt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    · simpa only [fits, Nat.add_comm 1] using (1#1 ++ unpackMantissa bits).isLt

private theorem correct {F : Type} (fmt : Float.Model.Format) (bits : F → BitVec fmt.numBits) (make : Sign → Nat → F)
    (enc : ∀ s m, bits (make s m) =
      packComponents fmt s (BitVec.ofNat _ (fmt.exponentBias - 1)) (BitVec.ofNat _ m))
    (x : F) (u : UnpackedFloat) (bound : fits fmt.mantissaBitsWithoutImplicit u) :
    spec fmt bits x u (Alternatives.splitFraction fmt.mantissaBitsWithoutImplicit make x u) := by
  cases u with
  | notANumber | zero | infinity => rfl
  | finite s m e pos =>
    let w := fmt.mantissaBitsWithoutImplicit
    let k := w - m.log2
    have h : m.log2 ≤ w := Nat.le_of_lt_succ ((Nat.log2_lt (Nat.ne_of_gt pos)).mpr bound)
    have sum : m.log2 + k = w := Nat.add_sub_of_le h
    refine ⟨k, m * 2 ^ k, ?_, ?_, rfl, ?_, enc ..⟩
    · calc
        2 ^ w = 2 ^ m.log2 * 2 ^ k := sum ▸ Nat.pow_add ..
        _ ≤ m * 2 ^ k := Nat.mul_le_mul_right _ (Nat.log2_self_le (Nat.ne_of_gt pos))
    · calc
        m * 2 ^ k < 2 ^ (m.log2 + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos k)
        _ = 2 ^ (w + 1) := by rw [← Nat.pow_add]; congr 1; omega
    · change e = (e + ((m.log2 + 1 : Nat) : Int)) - ((w : Int) + 1) + (k : Int)
      rw [Int.natCast_add]
      omega

private theorem double (x : Float) : spec Format.binary64 (fun a : Float => a.toModel.toBits.toBitVec)
    x x.toModel.unpack (Alternatives.Float.frExp x) :=
  correct _ _ Alternatives.fraction64 (fun _ _ => rfl) _ _ (unpackFits _ _)

private theorem single (x : Float32) : spec Format.binary32 (fun a : Float32 => a.toModel.toBits.toBitVec)
    x x.toModel.unpack (Alternatives.Float32.frExp x) :=
  correct _ _ Alternatives.fraction32 (fun _ _ => rfl) _ _ (unpackFits _ _)

public def supported (n : Name) : Bool := [`Float.frExp, `Float32.frExp].contains n

/-- Exercise the bit classes where frexp's C behavior supplements the public finite
specification, together with both ends of the subnormal and normal ranges. -/
private def checkRuntime (binary64 : Bool) : Bool := Id.run do
  let (width, expBits) := if binary64 then (52, 11) else (23, 8)
  let hidden : Nat := 2 ^ width
  let infinity := (2 ^ expBits - 1) * hidden
  for sign in [0, 2 ^ expBits * hidden] do
    for magnitude in [0, 1, hidden - 1, hidden, infinity - 1, infinity, infinity + hidden / 2] do
      if magnitude > infinity && sign != 0 then continue
      let bits := sign + magnitude
      let same := if binary64 then Id.run do
        let x := Float.ofBits bits.toUInt64
        let (s, e) := x.frExp
        let (t, f) := Alternatives.Float.frExp x
        return s.toBits == t.toBits && e == f
      else Id.run do
        let x := Float32.ofBits bits.toUInt32
        let (s, e) := x.frExp
        let (t, f) := Alternatives.Float32.frExp x
        return s.toBits == t.toBits && e == f
      unless same do return false
  return true

/-- The C wrappers call frexp and set the exponent of a nonfinite input to zero.
The full representation theorem certifies the dyadic decomposition independently. -/
public def check (env : Environment) (native : OpaqueVal) (candidate : Expr) : IO Unit := do
  let binary64 := native.name == `Float.frExp
  let owner := if binary64 then `Init.Data.Float.Float else `Init.Data.Float.Float32
  let ext := if binary64 then "lean_float_frexp" else "lean_float32_frexp"
  unless supported native.name && !native.isUnsafe && env.getModuleIdx? owner != none &&
      env.getModuleIdxFor? native.name == env.getModuleIdx? owner && getExternNameFor env `c native.name == some ext do
    throw <| IO.userError "invalid floating-point fraction primitive"
  unless checkRuntime binary64 do throw <| IO.userError "native frexp boundary result mismatch"
  let theoremName := if binary64 then ``double else ``single
  let model := if binary64 then ``Alternatives.Float.frExp else ``Alternatives.Float32.frExp
  let verify : MetaM Unit := Meta.forallTelescope native.type fun args _ => do
    let #[x] := args | throwError "unexpected floating-point fraction signature"
    let proof := mkApp (mkConst theoremName) x
    let proven ← Meta.inferType proof
    let .app rel output := proven | throwError "unexpected floating-point representation theorem"
    unless rel.getAppFn.constName? == some ``spec && output == mkApp (mkConst model) x do
      throwError "invalid finite decomposition or exceptional cases"
    let claim ← Meta.mkForallFVars args (mkApp rel (mkApp candidate x))
    let .ok actual := Kernel.check env {} (mkConst theoremName) | throwError "invalid fraction proof"
    unless Kernel.isDefEqGuarded env {} claim actual do throwError "floating-point fraction candidate mismatch"
  verify.run' |>.toIO' {fileName := "<IEEE binary fraction>", fileMap := default} {env}

end OmegaChecks.InitPort.FloatFraction
