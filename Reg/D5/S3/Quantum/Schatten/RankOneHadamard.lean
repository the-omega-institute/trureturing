import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.RankOneHadamard
import Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

/-! Full-source registrations for rank-one factorization and phase removal. -/

namespace Reg.D5.S3.Quantum.Schatten.RankOneHadamard
open _root_.D5.S3.Quantum.Schatten
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Factorization

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ)
    (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ), G.rank ≤ 1 →
    ∃ x y : Fin n → ℂ, R.readout () n G (vecMulVec x y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, y, hxy⟩ := @h 0 0 (by simp)
  exact hxy

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hentry := congrArg (fun X : Matrix (Fin 1) (Fin 1) ℂ => X 0 0) he
  norm_num at hentry

def source_registration : Registration arena (type_of% @exists_rank_one_factors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_rank_one_factors, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_rank_one_factors) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.exists_rank_one_factors.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.RankOneHadamard.Factorization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.RankOneHadamard
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Factorization

namespace Reduction
open Reg.D5.S3.Quantum.Schatten.UnitarilyInvariantNorm

abbrev localRelationSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization localRelationSignature :=
  realize localRelationSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected (i : Fin 2) : Realization localRelationSignature :=
  realize localRelationSignature (fun j _ x y => if j = i then False else x = y)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := localRelationSignature
  Law R := ∀ {n : ℕ} (ν : UINorm n) (G : Matrix (Fin n) (Fin n) ℂ), G.rank ≤ 1 →
    ∃ a b : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      ∀ W : Matrix (Fin n) (Fin n) ℂ,
        R.readout ⟨0, by decide⟩ () (ν.N (W ⊙ G)) (ν.N (diagonal (fun i => (a i : ℂ)) * W *
          diagonal (fun i => (b i : ℂ)))) ∧
        R.readout ⟨1, by decide⟩ () (ν.N (W⁻¹ ⊙ Gᵀ)) (ν.N (diagonal (fun i => (a i : ℂ)) * (W⁻¹)ᴴ *
          diagonal (fun i => (b i : ℂ))))

private theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  obtain ⟨a, b, ha, hb, hab⟩ := @h 0 zeroDimNorm 0 (by simp)
  have hh := hab 0
  fin_cases i
  · have hf := hh.1
    change (if (⟨0, by decide⟩ : Fin 2) = ⟨0, by decide⟩ then False else
      zeroDimNorm.N (0 ⊙ 0) = zeroDimNorm.N
        (diagonal (fun i => (a i : ℂ)) * 0 * diagonal (fun i => (b i : ℂ)))) at hf
    rw [if_pos (by decide)] at hf
    exact hf
  · have hf := hh.2
    change (if (⟨1, by decide⟩ : Fin 2) = ⟨1, by decide⟩ then False else
      zeroDimNorm.N (0⁻¹ ⊙ (0 : Matrix (Fin 0) (Fin 0) ℂ)ᵀ) = zeroDimNorm.N
        (diagonal (fun i => (a i : ℂ)) * (0 : Matrix (Fin 0) (Fin 0) ℂ)⁻¹ᴴ *
          diagonal (fun i => (b i : ℂ)))) at hf
    rw [if_pos (by decide)] at hf
    exact hf

private theorem dependence : ObservationalDependence localRelationSignature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @UINorm.rank_one_hadamard_reduction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@UINorm.rank_one_hadamard_reduction, rejected ⟨0, by decide⟩,
    rejected_law ⟨0, by decide⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext p x
      simp [rejected, actual, realize, hji]
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@UINorm.rank_one_hadamard_reduction) (Realization localRelationSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.UINorm.rank_one_hadamard_reduction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.RankOneHadamard.Reduction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize localRelationSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Schatten.RankOneHadamard
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reduction
end
end Reg.D5.S3.Quantum.Schatten.RankOneHadamard
