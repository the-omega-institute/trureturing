import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
import Reg.Support.SingleDependentReadout

/-! Typed source family for finite-box entropy lower bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Counting

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (j0 : J) (a b r : J → ℝ) (lambda : ℝ)
    (ha : ∀ j, 0 < a j) (hab : ∀ j, a j < b j)
    (hdisj : Pairwise (fun i j => Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))))
    (hr : ∀ j, 0 < r j) (hroom : ∀ j, r j < b j - a j)
    (hsum : ∑ j, r j = 1) (hslack : lambda + ∑ j, r j * log (b j) < 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon),
    ∀ᶠ x : ℝ in atTop, R.readout () ()
      ((∑ j, (b j - a j) * binEntropy (r j / (b j - a j))) - epsilon)
      (log (tailCount lambda x : ℝ) / scale x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (J := PUnit) PUnit.unit (fun _ => 1) (fun _ => 3) (fun _ => 1)
    (-log 3 - 1) (by simp) (by norm_num) (by
      intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim)
    (by simp) (by norm_num) (by simp) (by simp; linarith)
    (epsilon := 1) (by norm_num)
  obtain ⟨x, hx⟩ := hh.exists
  exact hx

def family : Registration arena (type_of% @finite_box_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_box_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_box_lower.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Counting.finite_box_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Counting.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
