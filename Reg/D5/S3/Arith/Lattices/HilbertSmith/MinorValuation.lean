import D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

/-! The Cauchy product records the dependence of each minor on its column set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation

open _root_.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, Finset ℕ) (fun _ => Finset ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ p J => cauchyMinor p.1 p.2 J) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, {0}⟩, {0}, {1}, ?_⟩
  change cauchyMinor 1 {0} {0} ≠ cauchyMinor 1 {0} {1}
  norm_num [cauchyMinor, positiveDifferences, denominatorProduct, Finset.prod_product]

namespace Positivity

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L : ℕ}, 0 < L → ∀ I J : Finset ℕ, 0 < R.readout () ⟨L, I⟩ J

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl (0 : ℚ)) (h (L := 1) (by decide) ∅ ∅)

def family : Registration arena (type_of% @cauchyMinor_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cauchyMinor_pos, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cauchyMinor_pos) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.MinorValuation.cauchyMinor_pos.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation.Positivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p J => cauchyMinor p.1 p.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positivity

namespace Valuation

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n L k : ℕ}, p.Prime → L ≠ 0 → ∀ {I J : Finset ℕ},
    I ⊆ range n → J ⊆ range n → I.card = k → J.card = k →
      2 * padicValRat p (R.readout () ⟨L, I⟩ J) =
        2 * (k : ℤ) * ((L.factorization p : ℤ) - Nat.log p (2 * n - 1)) +
          ∑ a ∈ Icc 1 (Nat.log p (2 * n - 1)), (residueLoss (p ^ a) I J : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (n := 0) (L := 1) (k := 0)
    (by decide : Nat.Prime 2) (by decide)
    (I := ∅) (J := ∅) (by simp) (by simp) (by simp) (by simp)
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide : 1 < (2 : ℕ))
  norm_num [rejected, realize, htwo] at hbad

def family : Registration arena (type_of% @cauchyMinor_valuation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cauchyMinor_valuation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cauchyMinor_valuation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.MinorValuation.cauchyMinor_valuation.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation.Valuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p J => cauchyMinor p.1 p.2 J) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
    definition := none
    coordinates := #[2, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Valuation

end Reg.D5.S3.Arith.Lattices.HilbertSmith.MinorValuation
