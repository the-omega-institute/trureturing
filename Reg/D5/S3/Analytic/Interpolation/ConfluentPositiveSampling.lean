/-
Source registration for weightedNewtonTail_uniform_lower.

The dependent parameters are the dimension m, the exponent r, and the
entire node vector a. The state v and the output are real vectors in
dimension m. The law keeps the original hypotheses and chooses δ before
the nodes and state. The zero readout fails at m = r = 1, lo = hi = 1,
a = (1, 1), and v = 1. At the same parameters, states 0 and 1 witness
observational dependence by the public lower bound and linearity at zero.

-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling

open _root_.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev newtonSignature : Signature.{0, 0, 0, 0, 0} where
  Params := Σ m : ℕ, Σ _r : ℕ, (Fin (m + 1) → ℝ)
  State p := Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def newtonActual : Realization newtonSignature :=
  realize newtonSignature (fun _ p v => weightedNewtonTail p.2.1 p.2.2 v)
    (fun e => nomatch e)

def newtonRejected : Realization newtonSignature :=
  realize newtonSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem newtonDependence : ObservationalDependence newtonSignature newtonActual := by
  intro role
  refine ⟨⟨1, 1, fun _ => 1⟩, 0, 1, ?_⟩
  change weightedNewtonTail 1 (fun _ : Fin 2 => (1 : ℝ)) (0 : Fin 1 → ℝ) ≠
    weightedNewtonTail 1 (fun _ : Fin 2 => (1 : ℝ)) (1 : Fin 1 → ℝ)
  intro heq
  obtain ⟨δ, hδ, hbound⟩ := weightedNewtonTail_uniform_lower (m := 1) (r := 1)
    (by decide) (by decide) 1 1 (by norm_num) le_rfl
  have hle := hbound (fun _ => 1) (fun _ => ⟨le_rfl, le_rfl⟩) 1
  rw [← heq, map_zero, norm_zero, norm_one, mul_one] at hle
  exact (not_le_of_gt hδ) hle

def weightedNewtonTail_uniform_lower_arena : Arena where
  signature := newtonSignature
  Law R := ∀ {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (lo hi : ℝ) (hlo : 0 < lo) (hinterval : lo ≤ hi),
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : Fin (m + 1) → ℝ), (∀ i, a i ∈ Set.Icc lo hi) →
      ∀ v : Fin m → ℝ, δ * ‖v‖ ≤ ‖R.readout () ⟨m, r, a⟩ v‖

private theorem weightedNewtonTail_uniform_lower_actual_law :
    weightedNewtonTail_uniform_lower_arena.Law newtonActual := by
  exact @weightedNewtonTail_uniform_lower

private theorem weightedNewtonTail_uniform_lower_rejected_law :
    ¬ weightedNewtonTail_uniform_lower_arena.Law newtonRejected := by
  intro hall
  obtain ⟨δ, hδ, hbound⟩ := @hall 1 1 (by decide) (by decide) 1 1
    (by norm_num) (by norm_num)
  have hz := hbound (fun _ => 1) (by intro i; exact ⟨le_rfl, le_rfl⟩)
    (1 : Fin 1 → ℝ)
  change δ * ‖(1 : Fin 1 → ℝ)‖ ≤ ‖(0 : Fin 1 → ℝ)‖ at hz
  exact (not_le_of_gt hδ) (by simpa only [norm_one, mul_one, norm_zero] using hz)

def weightedNewtonTail_uniform_lower_family :
    Registration weightedNewtonTail_uniform_lower_arena
      (type_of% (@weightedNewtonTail_uniform_lower)) where
  actual := newtonActual
  bridge := Iff.rfl
  variation := ⟨weightedNewtonTail_uniform_lower_actual_law,
    newtonRejected, weightedNewtonTail_uniform_lower_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨newtonRejected, ?_, rfl, weightedNewtonTail_uniform_lower_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := newtonDependence

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weightedNewtonTail_uniform_lower) (type_of% newtonActual) Type Unit := {
  unitName := `Reg.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling.weightedNewtonTail_uniform_lower.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling.weightedNewtonTail_uniform_lower_family
  realizationSource := none
  generated := false
  arena := .source ⟨weightedNewtonTail_uniform_lower_arena⟩
  objectArena := .source ⟨weightedNewtonTail_uniform_lower_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightedNewtonTail_uniform_lower_arena
    ⟨weightedNewtonTail_uniform_lower_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize newtonSignature (fun _ p v => weightedNewtonTail p.2.1 p.2.2 v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
    definition := none
    -- Candidate lexical context [m,r,hm,hr,lo,hi,hlo,hinterval,δ,a,ha,v].
    coordinates := #[0, 1, 9]
    readouts := #[{
      -- Eight outer binders, Exists predicate, second And argument,
      -- three inner binders, right side of ≤, argument of the norm.
      -- The selected value is weightedNewtonTail r a v.
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
