/-
Full-law dependent-family registrations for the actual nodal model and
uniform coefficient reconstruction. Only the selected RHS P evaluation in
the first Law and the complex norm under the second Law's left sum vary.
The imported P, Q, D, couplingColumn and arithmeticBoundarySymbol stay fixed;
all original binders, both degree bounds and the exterior identity are retained.
The reconstruction coefficient depends only on S,A, before arbitrary c,v,N.

The reconstruction audit remains unresolved under issue18783: the full Law's
hbound : ∀ n ∈ S, n.natAbs ≤ A reaches Int.natAbs, rejected by
ClosedTruthReadout as source.unsafe_or_external.
https://github.com/the-omega-institute/trureturing/issues/18783
-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
open Polynomial
open scoped BigOperators

namespace NodalModel

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℤ
  State _ := ℂ[X]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m p => p.eval (m : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

/-- This is the complete original statement with precisely one readout varied.
In particular c ranges over all naturals, and m over every exterior integer. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (S : Finset ℤ) (hS : S.Nonempty) (v : ℤ → ℂ),
    (P c S v).natDegree < S.card ∧ (Q S v).natDegree < S.card ∧
      ∀ m : ℤ, m ∉ S →
        (Real.pi : ℂ) * (D S).eval (m : ℂ) * couplingColumn c S v m =
          r.readout () m (P c S v) -
            (arithmeticBoundarySymbol c m : ℂ) * (Q S v).eval (m : ℂ)

private theorem source_reconstruction :
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.actual_nodal_polynomial_model)) ↔
      arena.Law actual := by
  constructor
  · intro h c S hS v
    exact h c S hS v
  · intro h c S hS v
    exact h c S hS v

private theorem actual_law : arena.Law actual := by
  intro c S hS v
  exact _root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.actual_nodal_polynomial_model
    c S hS v

/-- The fixed witness refutes the quantified full Law, without narrowing it.
All actual zero-vector numerators and the actual column vanish. The changed
RHS evaluation alone is one, so the exterior identity would force 0 = 1. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro hall
  have hS : ({0} : Finset ℤ).Nonempty := ⟨0, by simp⟩
  have hm : (1 : ℤ) ∉ ({0} : Finset ℤ) := by simp
  have hbad := (hall 0 ({0} : Finset ℤ) hS (fun _ : ℤ => (0 : ℂ))).2.2 1 hm
  have hzero_one : (0 : ℂ) = 1 := by
    simpa [rejected, realize, P, Q, couplingColumn] using hbad
  exact zero_ne_one hzero_one

/-- Nonconstancy concerns the actual evaluation function at a fixed m=0;
the rejected constant function is not used as a dependence witness. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0 : ℤ), (0 : ℂ[X]), (1 : ℂ[X]), ?_⟩
  simpa [actual, realize] using
    (show (0 : ℂ[X]).eval (0 : ℂ) ≠ (1 : ℂ[X]).eval (0 : ℂ) by simp)

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.actual_nodal_polynomial_model)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The selector varies only the RHS Polynomial.eval (m : Complex) function
prefix, with P c S v retained as its state. Coordinate [4] is the exterior
integer m; the fresh polynomial state is appended at context ordinal 6.
The degree bounds, Q evaluation and exterior telescope remain fixed. -/
noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.actual_nodal_polynomial_model)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.NodalModel.actual_nodal_polynomial_model.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.NodalModel.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m p => p.eval (m : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "body",
        "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end NodalModel

namespace UniformReconstruction

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

/-- S,A and every radius premise precede c,v,N exactly as in the source.
Only the norm at v(n) under the left finite sum varies, not its square,
the reconstruction constant, the scale, or either right coefficient norm. -/
def arena : Arena where
  signature := signature
  Law r := ∀ (S : Finset ℤ) (A : ℕ)
    (hS : S.Nonempty) (hA : 1 ≤ A) (hbound : ∀ n ∈ S, n.natAbs ≤ A)
    (c : ℕ) (v : ℤ → ℂ) (N : ℕ) (hN : 0 < N),
    (1 / ((S.card : ℝ) ^ 2 * (A : ℝ) ^ (2 * (S.card - 1)))) *
        (∑ n ∈ S, (r.readout () () (v n)) ^ 2) ≤
      ∑ r ∈ Finset.range S.card, (N : ℝ) ^ (2 * r) *
        (‖(P c S v).coeff r‖ ^ 2 + ‖(Q S v).coeff r‖ ^ 2)

private theorem source_reconstruction :
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.uniform_coefficient_reconstruction)) ↔
      arena.Law actual := by
  constructor
  · intro h S A hS hA hbound c v N hN
    exact h S A hS hA hbound c v N hN
  · intro h S A hS hA hbound c v N hN
    exact h S A hS hA hbound c v N hN

private theorem actual_law : arena.Law actual := by
  intro S A hS hA hbound c v N hN
  exact _root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.uniform_coefficient_reconstruction
    S A hS hA hbound c v N hN

/-- At the lawful singleton/radius/scale witness the actual P and Q are zero.
The original constant is one; the changed left norm forces 1 <= 0. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro hall
  have hS : ({0} : Finset ℤ).Nonempty := ⟨0, by simp⟩
  have hbound : ∀ n ∈ ({0} : Finset ℤ), n.natAbs ≤ (1 : ℕ) := by
    intro n hn
    have hnzero : n = 0 := Finset.mem_singleton.mp hn
    subst n
    norm_num
  have hbad := hall ({0} : Finset ℤ) 1 hS (by decide) hbound
    0 (fun _ : ℤ => (0 : ℂ)) 1 (by decide)
  have hone_le_zero : (1 : ℝ) ≤ 0 := by
    simpa [rejected, realize, P, Q] using hbad
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) hone_le_zero

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def familyRegistration : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.uniform_coefficient_reconstruction)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The selector varies the complex norm at v n under the left finite sum,
retaining v n as its state. Empty coordinates pack as Unit; the fresh Complex
state follows the nine original telescope binders and the sum's n binder.
The complete Law, including hbound and both right coefficient norms, is fixed.
Variation and sensitivity evidence reside in familyRegistration. -/
noncomputable def registration_2 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.uniform_coefficient_reconstruction)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.UniformReconstruction.uniform_coefficient_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity.UniformReconstruction.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualNodalCoercivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end UniformReconstruction

end Reg.D5.S3.Weil.ZetaBridge.ActualNodalCoercivity



