import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Additive.PlasticTailStability
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the full tail stability theorem. The observed cardinality
of the interval family is varied in its bound only; every parameter and all
conclusions remain in the reconstructed law. Dependence uses actual tail runs. -/

namespace Reg.D5.S3.Arith.Additive.PlasticTailStability

open _root_.D5.S3.Arith.Additive.PlasticTailStability
open _root_.D5.S3.Arith.Additive.PlasticExtremal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset (Finset ℤ)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ E => E.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (n : ℕ) (_hn : 10 ≤ n) (x : ℕ → ℤ)
    (_hx : StrictMonoOn x (Set.Iio n)),
    let E := prefixSet x n
    let P := prefixSet x 10
    let T := E \ P
    let c := fun i => completed (prefixSet x i) (x i)
    let δ := 4*n-26-count E
    let K := 1+δ/3
    count E ≤ 4*n-26 ∧
    δ = 14-count P + ∑ i ∈ Finset.Ico 10 n, (4-c i) ∧
    ((Finset.Ico 10 n).filter (fun i => c i < 4)).card ≤ δ ∧
    3*((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)).card +
    4*((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))).card ≤ δ ∧
    (10 < n →
      (∃ R : Finset (Finset ℤ), R.biUnion id = T ∧ obs.readout () () R ≤ K ∧
        ∀ J ∈ R, ∃ a b : ℤ, a ≤ b ∧ J=Finset.Icc a b) ∧
      (∃ a b : ℤ, Finset.Icc a b ⊆ T ∧ a ≤ b ∧
        (n-10+K-1)/K ≤ (Finset.Icc a b).card)) ∧
    (δ ≤ 2 → (Finset.Ico 9 n).image x = Finset.Icc (x 9) (x (n-1)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : StrictMonoOn (fun i : ℕ => (i : ℤ)) (Set.Iio 11) := by
    intro a _ b _ hab
    change (a : ℤ) < (b : ℤ)
    exact_mod_cast hab
  have hh := (h 11 (by decide) (fun i => (i : ℤ)) hx).2.2.2.2.1 (by decide)
  obtain ⟨R, _, hcard, _⟩ := hh.1
  change (2 : ℕ) ≤ 1 + (4 * 11 - 26 - count (prefixSet (fun i => (i : ℤ)) 11))/3 at hcard
  have hc : count (prefixSet (fun i => (i : ℤ)) 11) = 18 := by decide +kernel
  rw [hc] at hcard
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  change ∀ _ : Unit, ∃ _ : Unit, ∃ A B : Finset (Finset ℤ), A.card ≠ B.card
  intro i
  refine ⟨(), {({10} : Finset ℤ)}, {({100} : Finset ℤ), {110}}, ?_⟩
  decide +kernel

def realization : Registration arena (type_of% (@whole_theorem_three_three)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_theorem_three_three, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Additive.PlasticTailStability.whole_theorem_three_three)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Additive.PlasticTailStability.whole_theorem_three_three.__information_unit
  realizationName := `Reg.D5.S3.Arith.Additive.PlasticTailStability.realization
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨realization⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => E.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Additive.PlasticTailStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms realization
#print axioms audit

end Reg.D5.S3.Arith.Additive.PlasticTailStability
