import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Analysis.VonNeumannNormalL1

/-! The full existence theorem is retained; the observed operand is its sharp
operator-norm comparison. Parameters and input/output spaces remain arbitrary. -/

open Set MeasureTheory
open scoped ComplexOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NormalFunctionals
open _root_.D5.S3.Quantum.Analysis.NormalL1Realization

noncomputable section
universe u v

namespace Reg.D5.S3.Quantum.Analysis.NormalL1Realization

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} {K : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] [ν.WeaklyRegular]
    (J : C(K, ℂ) →ₗ[ℂ] StrongDual ℂ A)
    (hpos : ∀ g : C(K, ℂ), (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ J g a)
    (hnormal : IsOrderNormal (J 1))
    (hmass : ∀ g : C(K, ℂ), J g 1 = ∫ t, g t ∂ν),
    ∃ Γ : (K →₁[ν] ℂ) →L[ℂ] StrongDual ℂ A,
      (∀ g : C(K, ℂ), Γ (ContinuousMap.toLp 1 ν ℂ g) = J g) ∧
      (∀ h : K →₁[ν] ℂ, IsOrderNormal (Γ h)) ∧
      (∀ h : K →₁[ν] ℂ, (∀ᵐ t ∂ν, 0 ≤ h t) →
        ∀ a : A, 0 ≤ a → 0 ≤ Γ h a) ∧
      (∀ h : K →₁[ν] ℂ, Γ h 1 = ∫ t, h t ∂ν) ∧ R.readout () () ‖Γ‖ 1

private theorem actual_law : arena.{u,v}.Law actual := @exists_normal_L1_extension.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  have hn : IsOrderNormal ((0 : C(PUnit.{v+1}, ℂ) →ₗ[ℂ] StrongDual ℂ A) 1) :=
    (normalDual (A := A)).zero_mem
  obtain ⟨Γ, _, _, _, _, hf⟩ := h (A := A) (K := PUnit.{v+1}) 0 0
    (by intro g hg a ha; simp) hn (by intro g; simp)
  exact hf

def family : Registration arena.{u,v} (type_of% (@exists_normal_L1_extension.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    norm_num at hf

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_normal_L1_extension.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NormalL1Realization.extensionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NormalL1Realization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NormalL1Realization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Analysis.NormalL1Realization

namespace Reg.D5.S3.Quantum.Analysis.NormalL1Realization.PositiveNorm

abbrev signature := Reg.D5.S3.Quantum.Analysis.NormalL1Realization.signature

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : StrongDual ℂ A) (_hφ : ∀ a : A, 0 ≤ a → 0 ≤ φ a),
    R.readout () () ‖φ‖ (φ 1).re

private theorem actual_law : arena.{u}.Law actual := @positive_norm_eq_mass.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  exact h (A := A) 0 (by intro a ha; simp)

def family : Registration arena.{u} (type_of% (@positive_norm_eq_mass.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hf : (1 : ℝ) = 0 := Eq.mp (congrFun h 0) rfl
    norm_num at hf

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_norm_eq_mass.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NormalL1Realization.positiveNormUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NormalL1Realization.PositiveNorm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NormalL1Realization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Analysis.NormalL1Realization.PositiveNorm
