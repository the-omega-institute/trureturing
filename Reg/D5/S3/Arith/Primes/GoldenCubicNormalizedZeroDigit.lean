import D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit

open _root_.D5.S1.Scale (goldenLucas)
open _root_.D5.S3.Arith.Primes.GoldenCubicMarkedFibonacciDepth (evalMod)
open _root_.D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
private abbrev Params := Σ _ : ℕ, ℕ

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun _ => ℤ)
    (fun q => ZMod q.1)

def actual : Realization signature := realize signature
  (fun _ q v => -(3:ZMod q.1)*((3:ZMod q.1)^q.2)⁻¹*(v:ZMod q.1)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p i k h : ℕ) (u : ℤ)
    (_hp : p.Prime) (_hp3 : 3 < p) (_hi : 1 ≤ i) (_hh : 1 ≤ h)
    (_hB : goldenLucas (3^i)^2+3 = (p:ℤ)^h*u),
    ∃ (r : ZMod (p^(h+1))) (v : ℤ),
      evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) r = 0 ∧
      ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) r = 0 ∧
      (∀ s : ZMod (p^(h+1)), evalMod (p^(h+1)) (goldenLucas (3^(i+1+k))) s = 0 →
        ZMod.castHom (dvd_pow_self p (by omega : h+1 ≠ 0)) (ZMod p) s = 0 → s=r) ∧
      r = (((p:ℤ)^h*v : ℤ) : ZMod (p^(h+1))) ∧
      (∀ w : ℤ, r = (((p:ℤ)^h*w : ℤ) : ZMod (p^(h+1))) → (w:ZMod p) = (v:ZMod p)) ∧
      IsUnit (2*(goldenLucas (3^i):ℤ) : ZMod p) ∧
      R.readout () ⟨p,k⟩ v =
        (2*(goldenLucas (3^i):ℤ) : ZMod p)^3*((u:ZMod p)*(12:ZMod p)⁻¹) ∧
      ((∃ y : ZMod p, y^3 = -(3:ZMod p) * ((3:ZMod p)^k)⁻¹ * (v:ZMod p)) ↔
        ∃ z : ZMod p, z^3 = (u:ZMod p)*(12:ZMod p)⁻¹)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hB : goldenLucas (3^1)^2+3 = (19:ℤ)^1*1 := by decide +kernel
  obtain ⟨_,_,_,_,_,_,_,_,he,_⟩ :=
    h 19 1 0 1 1 (by decide) (by decide) (by decide) (by decide) hB
  change (0 : ZMod 19) = (2*(goldenLucas (3^1):ℤ) : ZMod 19)^3 *
    ((1 : ZMod 19) * (12 : ZMod 19)⁻¹) at he
  exact (by decide +kernel : ¬ ((0 : ZMod 19) =
    (2*(goldenLucas (3^1):ℤ) : ZMod 19)^3 * ((1:ZMod 19)*(12:ZMod 19)⁻¹))) he

private theorem actual_dependence :
    actual.readout () ⟨19,0⟩ 0 ≠ actual.readout () ⟨19,0⟩ 1 := by
  decide +kernel

def family : Registration arena (type_of% @native_residue_cube_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_residue_cube_readout,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨⟨19,0⟩,0,1,actual_dependence⟩

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@native_residue_cube_readout) (type_of% actual) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit.native_residue_cube_readout.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body",
        "arg","body","arg","body","arg","arg","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Arith.Primes.GoldenCubicNormalizedZeroDigit
