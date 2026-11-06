import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
import Reg.Support.DependentFamily

/-! Faithful interventions in the actual PGM score, preserving every density and
support hypothesis and the entire centered expression. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
open _root_.D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ N : ℕ, Fin N → Matrix (Fin d) (Fin d) ℂ
  State p := Finset (Fin p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p B => pgmScore p.2.2 B) (fun e => nomatch e)

private theorem observed_dependence (i : Unit) :
    ∃ p s t, actual.readout i p s ≠ actual.readout i p t := by
  refine ⟨⟨1, 1, fun _ => 1⟩, ∅, {0}, ?_⟩
  intro h
  norm_num [actual, realize, pgmScore, CFC.one_rpow, trace] at h

namespace Centered

def rejected : Realization signature :=
  realize signature (fun _ p B => pgmScore p.2.2 B + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ), 0 < N →
    (∀ i, (ρ i).PosSemidef) → (∀ i, trace (ρ i) = 1) →
    ∀ B : Finset (Fin N), B.Nonempty →
      let S := ∑ j ∈ B, (1 / (N : ℂ)) • ρ j
      let R := S ^ (-(1 / 4) : ℝ)
      r.readout () ⟨d, N, ρ⟩ B - 1 / N =
        ∑ i ∈ B, RHLinalg.frobSq
          (R * ((1 / (N : ℂ)) • ρ i) * R - (1 / (B.card : ℝ)) • CFC.sqrt S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ρ : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  have hρ : ∀ i, (ρ i).PosSemidef := fun _ => Matrix.PosSemidef.one
  have htr : ∀ i, trace (ρ i) = 1 := by intro i; norm_num [ρ, trace]
  have ht := centered_identity ρ (by decide) hρ htr {0} (Finset.singleton_nonempty 0)
  have hr := h ρ (by decide) hρ htr {0} (Finset.singleton_nonempty 0)
  dsimp [rejected, realize] at hr
  dsimp only at ht
  linarith

def family : Registration arena (type_of% (@centered_identity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_identity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := observed_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@centered_identity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity.Centered.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity.Centered.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p B => pgmScore p.2.2 B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centered
namespace Nonnegative

def rejected : Realization signature :=
  realize signature (fun _ p B => pgmScore p.2.2 B - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ), 0 < N →
    (∀ i, (ρ i).PosSemidef) → (∀ i, trace (ρ i) = 1) →
    ∀ B : Finset (Fin N), B.Nonempty → 1 / (N : ℝ) ≤ r.readout () ⟨d, N, ρ⟩ B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr := h (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (by decide) (fun _ => Matrix.PosSemidef.one)
    (by intro i; norm_num [trace]) {0} (Finset.singleton_nonempty 0)
  norm_num [rejected, realize, pgmScore, CFC.one_rpow, trace] at hr

def family : Registration arena (type_of% (@random_guessing_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨random_guessing_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := observed_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@random_guessing_le) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity.Nonnegative.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity.Nonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p B => pgmScore p.2.2 B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonnegative
end Reg.D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
