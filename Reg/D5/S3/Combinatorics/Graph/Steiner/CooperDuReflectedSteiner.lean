import D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source registration for the uniform negative reflected Steiner eigenvalue on the star. -/

namespace Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner

open _root_.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open SimpleGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- For the original order and vector, observe whether a real scalar satisfies
the nonzero condition and every reflected row identity. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, Fin 48 → ℝ) (fun _ => ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature
    (fun _ p lam => @decide (IsHEigenpair (isTree_starGraph (0 : Fin 48)).connected
      (p.1 - 2) p.2 lam) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Keep the original order hypotheses, both witnesses and the strict sign. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ), 4 ≤ k → Even k →
    ∃ (x : Fin 48 → ℝ) (lam : ℝ), lam < 0 ∧ R.readout () ⟨k, x⟩ lam = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, _, hfalse⟩ := h 4 (by decide) ⟨2, by decide⟩
  cases hfalse

theorem dependence : ObservationalDependence signature actual := by
  classical
  intro role
  obtain ⟨x, lam, _, heigen⟩ := star_negative 4 (by decide) ⟨2, by decide⟩
  have hrejected : ¬ IsHEigenpair (isTree_starGraph (0 : Fin 48)).connected
      (4 - 2) x (lam + 1) := by
    intro h
    have hzero : x = 0 := by
      funext i
      by_contra hi
      have heq := (heigen.2 i).symm.trans (h.2 i)
      have hlam : lam = lam + 1 := (mul_left_inj' (pow_ne_zero _ hi)).mp heq
      linarith
    exact heigen.1 hzero
  refine ⟨⟨4, x⟩, lam, lam + 1, ?_⟩
  simp [actual, realize, heigen, hrejected]

def source_registration : Registration arena (∀ (k : ℕ), 4 ≤ k → Even k →
    ∃ (x : Fin 48 → ℝ) (lam : ℝ), lam < 0 ∧
      IsHEigenpair (isTree_starGraph (0 : Fin 48)).connected (k - 2) x lam) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using star_negative, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.star_negative)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p lam => @decide (IsHEigenpair (isTree_starGraph (0 : Fin 48)).connected
      (p.1 - 2) p.2 lam) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner
