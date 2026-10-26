import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Interpolation.PositiveJJExclusion
import Reg.Support.SingleDependentReadout
import Mathlib.LinearAlgebra.Lagrange

/-! Degree-readout dependence of the original-clock reciprocal interpolation exclusion. -/

namespace Reg.D5.S1.Recurrence.Interpolation.PositiveJJExclusion

open _root_.D5.S1.Recurrence.Interpolation.PositiveJJExclusion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Polynomial

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev degreeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ[X]) (fun _ => ℕ)

def degreeActual : Realization degreeSignature :=
  realize degreeSignature (fun _ _ R => R.natDegree) (fun e => nomatch e)

def degreeRejected : Realization degreeSignature :=
  realize degreeSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem degreeDependence : ObservationalDependence degreeSignature degreeActual := by
  intro i
  refine ⟨(), 0, X, ?_⟩
  norm_num [degreeActual, realize]

abbrev interpolationArena : Arena where
  signature := degreeSignature
  Law M := ∀ (m a : ℕ) (ρ : ℝ) (u : ℕ → ℝ)
    (_hm : 5 ≤ m) (_ha : a ≤ 2 * m - 2) (_hρ : 0 < ρ)
    (_hu0 : u 0 = 1) (_hu1 : u 1 = -ρ)
    (_hr : ∀ k, u (k + 2) = u (k + 1) + u k),
    ¬ ∃ R : ℝ[X], M.readout () () R ≤ m - 1 ∧
      (∀ k, k ≤ 2 * m - 2 → u k ≠ 0) ∧
      (∀ k, k ≤ a → u k * R.eval (k : ℝ) = 1) ∧
      (∀ k, a ≤ k → k ≤ 2 * m - 2 → u k * R.eval ((k + 2 : ℕ) : ℝ) = 1)

private def counterSequence : ℕ → ℝ :=
  (Real.fibRec : LinearRecurrence ℝ).mkSol ![1, -2]

private theorem counterRecurrence (k : ℕ) :
    counterSequence (k + 2) = counterSequence (k + 1) + counterSequence k := by
  have h := (Real.fibRec : LinearRecurrence ℝ).is_sol_mkSol ![1, -2] k
  change counterSequence (k + 2) = ∑ i : Fin 2, ![(1 : ℝ), 1] i * counterSequence (k + i) at h
  simpa [Fin.sum_univ_two, add_comm] using h

private theorem counterInitial0 : counterSequence 0 = 1 := by
  simpa [counterSequence] using
    (Real.fibRec : LinearRecurrence ℝ).mkSol_eq_init ![1, -2] (0 : Fin 2)

private theorem counterInitial1 : counterSequence 1 = -(2 : ℝ) := by
  simpa [counterSequence] using
    (Real.fibRec : LinearRecurrence ℝ).mkSol_eq_init ![1, -2] (1 : Fin 2)

private theorem counterNonzero (k : ℕ) (hk : k ≤ 8) : counterSequence k ≠ 0 := by
  have h0 := counterInitial0
  have h1 := counterInitial1
  have h2 : counterSequence 2 = -1 := by linarith [counterRecurrence 0]
  have h3 : counterSequence 3 = -3 := by linarith [counterRecurrence 1]
  have h4 : counterSequence 4 = -4 := by linarith [counterRecurrence 2]
  have h5 : counterSequence 5 = -7 := by linarith [counterRecurrence 3]
  have h6 : counterSequence 6 = -11 := by linarith [counterRecurrence 4]
  have h7 : counterSequence 7 = -18 := by linarith [counterRecurrence 5]
  have h8 : counterSequence 8 = -29 := by linarith [counterRecurrence 6]
  interval_cases k <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]

private theorem interpolationArenaRejected : ¬ interpolationArena.Law degreeRejected := by
  classical
  intro h
  have h0 := counterInitial0
  have h1 := counterInitial1
  have hbad := h 5 0 2 counterSequence (by omega) (by omega) (by norm_num)
    h0 h1 counterRecurrence
  let S : Finset ℕ := insert 0 (Finset.Icc 2 10)
  let v : ℕ → ℝ := fun k => k
  let r : ℕ → ℝ := fun k => (counterSequence (k - 2))⁻¹
  let P : ℝ[X] := Lagrange.interpolate S v r
  have hinj : Set.InjOn v S := by
    intro i _ j _ hij
    exact Nat.cast_injective hij
  have hev (j : ℕ) (hj : j ∈ S) : P.eval (j : ℝ) = r j :=
    Lagrange.eval_interpolate_at_node r hinj hj
  apply hbad
  refine ⟨P, by norm_num [degreeRejected, realize], ?_, ?_, ?_⟩
  · intro k hk
    exact counterNonzero k (by omega)
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [hev 0 (by simp [S])]
    simp [r, h0]
  · intro k _ hk
    have hmem : k + 2 ∈ S := by simp [S]; omega
    rw [hev (k + 2) hmem]
    simp only [r, Nat.add_sub_cancel]
    exact mul_inv_cancel₀ (counterNonzero k (by omega))

def interpolationSource : Registration interpolationArena (type_of% @positive_jj_exclusion) where
  actual := degreeActual
  bridge := Iff.rfl
  variation := ⟨positive_jj_exclusion, degreeRejected, interpolationArenaRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    interpolationArena.Law degreeActual degreeRejected interpolationArenaRejected
  dependence := degreeDependence

def interpolationAudit :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positive_jj_exclusion) (Realization degreeSignature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Interpolation.PositiveJJExclusion.interpolationAuditUnit
  realizationName := `Reg.D5.S1.Recurrence.Interpolation.PositiveJJExclusion.interpolationSource
  realizationSource := none
  generated := false
  arena := .source ⟨interpolationArena⟩
  objectArena := .source ⟨interpolationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source interpolationArena ⟨interpolationSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize degreeSignature (fun _ _ R => R.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ[X])
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Interpolation.PositiveJJExclusion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms interpolationAudit

end
end Reg.D5.S1.Recurrence.Interpolation.PositiveJJExclusion
