import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import Reg.Support.SingleDependentReadout

/-! Typed source family for the injective prime-product lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k : J → ℕ) (B : J → ℝ) (lambda x : ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hprime : ∀ j, ∀ p ∈ P j, Nat.Prime p)
    (hB : ∀ j, 0 < B j) (hcap : ∀ j, ∀ p ∈ P j, (p : ℝ) ≤ B j)
    (hsize : threshold lambda x < ((∑ j, k j : ℕ) : ℝ))
    (hcost : ∑ j, (k j : ℝ) * log (B j) ≤ log x) (hx : 0 < x),
    R.readout () () (∏ j, (P j).card.choose (k j)) (tailCount lambda x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (fun _ => ∅) (fun _ => 1) (fun _ => 1) 0 1
    (by intro i j hij; simp) (by simp) (by simp) (by simp)
    (by simp [threshold, scale]) (by simp) (by norm_num)

def family : Registration arena (type_of% @multibox_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@multibox_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@multibox_bound.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.multibox_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
