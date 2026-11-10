import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Reg.Support.SingleDependentReadout

/-! The whole literal kernel/zeta operator in the complete subexponential RH law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelSubexponential
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak.ActualKernelSubexponential

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ × ℂ) (fun _ => ℝ × ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ p => (K p.1, riemannZeta p.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

/-- Vary the same whole operator whose two projections the original law consumes.
The root let, every growth quantifier, and every Mathlib zero-law premise remain.
The family does not assume that its arbitrary operator has separable components. -/
def arena : Arena where
  signature := signature
  Law R :=
    let data : (ℝ × ℂ) → (ℝ × ℂ) := R.readout () ()
    (∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |(data (t, 0)).1| ≤ C * Real.exp (β * |t|)) →
      ∀ (rho : ℂ) (_ : (data (0, rho)).2 = 0)
        (_ : ¬∃ n : ℕ, rho = -2 * (n + 1)) (_ : rho ≠ 1), rho.re = 1 / 2

/-- Explicit preservation of the complete original proposition, not an assumed
mathematical equivalence or a weaker replacement theorem. -/
theorem original_full_type :
    (type_of% @actual_kernel_subexponential_implies_rh) ↔
      ((∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, |K t| ≤ C * Real.exp (β * |t|)) → RiemannHypothesis) := Iff.rfl

private theorem source_reconstruction :
    (type_of% @actual_kernel_subexponential_implies_rh) ↔ arena.Law actual := Iff.rfl

/-- The zero operator satisfies growth with C=1. Its zero-law falsely places
rho=2 on the critical line. This uses no negation of the actual RH proposition. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change
    ((∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |(0 : ℝ)| ≤ C * Real.exp (β * |t|)) →
      ∀ (rho : ℂ) (_ : (0 : ℂ) = 0)
        (_ : ¬∃ n : ℕ, rho = -2 * (n + 1)) (_ : rho ≠ 1), rho.re = 1 / 2) at h
  have hgrowth : ∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, |(0 : ℝ)| ≤ C * Real.exp (β * |t|) := by
    intro β _
    refine ⟨1, zero_lt_one, ?_⟩
    intro t
    simpa only [abs_zero, one_mul] using Real.exp_nonneg (β * |t|)
  have hnontrivial : ¬∃ n : ℕ, (2 : ℂ) = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hbad := h hgrowth (2 : ℂ) rfl hnontrivial (by norm_num)
  norm_num at hbad

/-- Dependence comes from the existing actual literal-K matrix witness. Holding
the complex coordinate at zero retains the nonconstant real component; rejection
is not used to justify dependence of the actual observation. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨n, x, y, hxy⟩ :=
    _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.actual_dependence ()
  by_contra hh
  push Not at hh
  apply hxy
  ext i j
  change (K (x i - x j) : ℂ) = (K (y i - y j) : ℂ)
  have he : K (x i - x j) = K (y i - y j) :=
    congrArg Prod.fst (hh () (x i - x j, (0 : ℂ)) (y i - y j, (0 : ℂ)))
  exact congrArg Complex.ofReal he

def evidence : Registration arena (type_of% @actual_kernel_subexponential_implies_rh) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_kernel_subexponential_implies_rh, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- The source is the public original theorem itself. A root let-value is a raw
source child admitted by atPath; functionOperand adds its one genuine pair input.
No named claim entry, proof expansion, Boolean predicate or source alias is used. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_kernel_subexponential_implies_rh) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelSubexponential.actual_kernel_subexponential_implies_rh.__information_unit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak.ActualKernelSubexponential.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => (K p.1, riemannZeta p.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms actual_kernel_subexponential_implies_rh
#print axioms original_full_type
#print axioms evidence
#print axioms registration

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak.ActualKernelSubexponential
end

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak.AffineTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => K t) (fun e => nomatch e)

def zeroFamily : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (tau a b : ℝ) (_ : 0 < tau)
    (_ : ∀ t : ℝ, tau ≤ t → R.readout () () t ≤ a * t + b), RiemannHypothesis

private theorem actual_law : arena.Law actual := actual_kernel_affine_tail_implies_rh

private theorem source_reconstruction :
    (type_of% @actual_kernel_affine_tail_implies_rh) ↔ arena.Law actual := Iff.rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨n, x, y, hxy⟩ :=
    _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.actual_dependence ()
  by_contra hh
  push Not at hh
  apply hxy
  ext i j
  change (K (x i - x j) : ℂ) = (K (y i - y j) : ℂ)
  exact congrArg Complex.ofReal (hh () (x i - x j) (y i - y j))

/-- With the RH conclusion fixed, this exact single-K family can vary the law
only if RH is false. No countermodel or four-slot registration is asserted. -/
private theorem variation_iff_not_rh : Variation arena actual ↔ ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨_, bad, hbad⟩ hRH
    exact hbad (fun _ _ _ _ _ => hRH)
  · intro hnot
    refine ⟨actual_law, zeroFamily, ?_⟩
    intro h
    exact hnot (h 1 0 0 zero_lt_one (by intro t ht; simp [zeroFamily, realize]))

private theorem sensitivity_implies_not_rh
    (h : Sensitivity arena actual) : ¬ RiemannHypothesis := by
  obtain ⟨bad, _, _, hbad⟩ := h.1 ()
  intro hRH
  exact hbad (fun _ _ _ _ _ => hRH)

/- The source bridge and actual dependence compile. Whole-family variation
and sensitivity are not supplied: for this faithful single-K arena they
require a proof of not RH. No Contract.Registration is claimed. -/

end
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak.AffineTail
