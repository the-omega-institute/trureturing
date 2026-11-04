import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
open _root_.D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries Finset

def claimAt (n : ℕ) : Prop :=
  ∃ Φ : PowerSeries ℤ, IsMetallic n Φ ∧
      (∀ Ψ, IsMetallic n Ψ → Ψ = Φ) ∧
      (∀ j, (shiftedHankel Φ (n + 1) j).natAbs ≤ 1) ∧
      (∀ M : ℕ, ∃ j, M < (shiftedHankel Φ (n + 3) j).natAbs) ∧
      ∃ (L : ℕ) (k : ℕ → ℕ) (b : ℕ → ℤ) (D Q : ℕ → PowerSeries ℤ)
        (s : ℕ → ℕ),
        L = (if n = 1 then 3 else 6 * n - 4) ∧
        (∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
          k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
            else (fractionData (max n 2) z).1) ∧
          b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
            else (fractionData (max n 2) z).2.1) ∧
          D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
            else (fractionData (max n 2) z).2.2)) ∧
        s 0 = 0 ∧ (∀ p, s (p + 1) = s p + k p + 1) ∧
        Q 0 = 1 ∧ Q 1 = D 0 ∧
        (∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
          C (b (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p) ∧
        (∀ p, constantCoeff (Q p) = 1 ∧ ∀ r, s p < r → coeff r (Q p) = 0) ∧
        ∀ K : ℕ, 1 ≤ K →
          let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
          let p := (K * (if n % 2 = 0 then 1 else 2)) * L
          let N := K * ρ
          let c := fun r => if r ≤ s p then coeff (s p - r) (Q p) else 0
          let d := fun r => if r ≤ s (p - 1) then coeff (s (p - 1) - r) (Q (p - 1)) else 0
          s p = N ∧ c N = 1 ∧
          (∀ r, N < r → c r = 0) ∧
          d (s (p - 1)) = 1 ∧ (∀ r, N ≤ r → d r = 0) ∧
          (∀ t, t < N → ∑ r ∈ range (N + 1), c r * coeff (n + 1 + r + t) Φ = 0) ∧
          (∀ t, t < N → ∑ r ∈ range N, d r * coeff (n + 1 + r + t) Φ =
            if t = N - 1 then -1 else 0) ∧
          shiftedHankel Φ (n + 1) N = 1

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => Prop)
def actual : Realization signature :=
  realize signature (fun _ _ n => claimAt n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n → r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by omega)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hzero : ¬ claimAt 0 := by
    rintro ⟨Φ, hΦ, _⟩
    have hc := congrArg (constantCoeff : PowerSeries ℤ →+* ℤ) hΦ.2
    norm_num [linearCoeff, hΦ.1, map_ofNat] at hc
  apply hzero
  exact Eq.mpr h (normal_family 1 (by omega))

def family : Registration arena (type_of% (@normal_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normal_family, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normal_family) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded.normal_family.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => claimAt n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms normal_family
#print axioms family
#print axioms registration
end Reg.D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnbounded
