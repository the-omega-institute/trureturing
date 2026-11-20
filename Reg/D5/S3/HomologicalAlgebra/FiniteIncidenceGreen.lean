import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of incidence propagation, contraction, and Green repair costs. -/

namespace Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen

open _root_.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
open _root_.D5.S3.HomologicalAlgebra.TotalUnimodularL1Repair (nonzeroSupport)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def realOrder : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev coordinateSignature.{level} : Signature where
  Params := Σ T : Type level, T
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def coordinateEquality.{level} : Realization coordinateSignature.{level} :=
  realize coordinateSignature (fun _ _ a b => a = b) (fun e => nomatch e)

private def falseEquality.{level} : Realization coordinateSignature.{level} :=
  realize coordinateSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equality_sensitivity.{level} (arena : Arena)
    (h : arena.signature = coordinateSignature.{level})
    (actual bad : Realization arena.signature) (hbad : ¬ arena.Law bad) :
    Sensitivity arena actual := by
  obtain ⟨sig, law⟩ := arena
  change sig = coordinateSignature.{level} at h
  subst sig
  constructor
  · intro role
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · funext anchor
      exact nomatch anchor
  · intro anchor
    exact nomatch anchor

private theorem equality_dependence.{level} :
    ObservationalDependence coordinateSignature.{level} coordinateEquality := by
  intro role
  refine ⟨⟨ULift.{level} Unit, ⟨()⟩⟩, 0, 1, ?_⟩
  intro h
  have hzero := congrFun h 0
  norm_num [coordinateEquality, realize] at hzero

private theorem order_dependence : ObservationalDependence signature realOrder := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hzero := congrFun h 0
  norm_num [realOrder, realize] at hzero

private abbrev OneFace := ULift.{u} Unit
private abbrev OneEdge := ULift.{v} Unit

private def unitInteger : Matrix OneFace.{u} OneEdge.{v} ℤ := fun _ _ => 1

private abbrev unitReal := unitInteger.{u,v}.map (Int.castRingHom ℝ)

private theorem unit_tu : unitInteger.{u,v}.IsTotallyUnimodular := by
  intro k rows cols hrows _
  have hk : k ≤ 1 := by simpa using Fintype.card_le_of_injective rows hrows
  interval_cases k
  · exact ⟨1, by simp⟩
  · exact ⟨1, by simp [Matrix.det_fin_one, unitInteger]⟩

private theorem singleton_incidence_apply {I : Type u} {J : Type v} [Unique I] [Fintype I]
    [Fintype J] [DecidableEq I] (A : Matrix J I ℝ) (hA : ∀ j i, A j i = 1)
    (x : EuclideanSpace ℝ I) (j : J) :
    incidence A x j = x default := by
  change (A.toEuclideanLin x) j = _
  rw [Matrix.toLpLin_apply]
  change (∑ i, A j i * x i) = _
  simp [hA]

private theorem unit_apply (x : EuclideanSpace ℝ OneEdge.{v}) (f : OneFace.{u}) :
    incidence unitReal.{u,v} x f = x default :=
  singleton_incidence_apply unitReal (by simp [unitInteger]) x f

private theorem unit_transpose_apply (x : EuclideanSpace ℝ OneFace.{u}) (e : OneEdge.{v}) :
    incidence (unitReal.{u,v})ᵀ x e = x default :=
  singleton_incidence_apply unitRealᵀ (by simp [unitInteger]) x e

private theorem singleton_norm {I : Type u} [Unique I] [Fintype I] (x : EuclideanSpace ℝ I) :
    ‖x‖ = ‖x default‖ := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]

private theorem unit_norm : ‖incidence (unitReal.{u,v})‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [singleton_norm, singleton_norm x, one_mul, unit_apply]

private theorem unit_image :
    faceUnit (default : OneFace.{u}) ∈ LinearMap.range (incidence (unitReal.{u,v})).toLinearMap := by
  refine ⟨EuclideanSpace.single (default : OneEdge.{v}) 1, ?_⟩
  ext f
  have hf : f = default := Subsingleton.elim _ _
  subst f
  change incidence unitReal.{u,v} (EuclideanSpace.single default 1) default = _
  rw [unit_apply]
  simp [faceUnit]

private theorem unit_face_gap (μ : ℝ) (_ : 0 < μ)
    (hμ : Module.End.HasEigenvalue (laplacianOnRange (unitReal.{u,v})) μ) :
    (1 : ℝ) ^ 2 ≤ μ := by
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have he := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hz.1)
  have hleft : incidence unitReal.{u,v} (incidence (unitReal.{u,v})ᵀ z.val) = z.val := by
    ext f
    have hf : f = default := Subsingleton.elim _ _
    subst f
    rw [unit_apply, unit_transpose_apply]
  have he' : z.val = μ • z.val := by
    change incidence unitReal.{u,v} (incidence (unitReal.{u,v})ᵀ z.val) = μ • z.val at he
    exact hleft.symm.trans he
  have hzero : (1 - μ) • z.val = 0 := by rw [sub_smul, one_smul, ← he', sub_self]
  have hz' : z.val ≠ 0 := fun h => hz.2 (Subtype.ext h)
  have hμ' := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hz')
  simp [← hμ']

private theorem unit_edge_gap (μ : ℝ) (_ : 0 < μ)
    (hμ : Module.End.HasEigenvalue
      ((incidence (unitReal.{u,v})ᵀ).comp (incidence (unitReal.{u,v}))).toLinearMap μ) :
    (1 : ℝ) ^ 2 ≤ μ := by
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hz.1
  have hleft : incidence (unitReal.{u,v})ᵀ (incidence unitReal.{u,v} z) = z := by
    ext e
    have he' : e = default := Subsingleton.elim _ _
    subst e
    rw [unit_transpose_apply, unit_apply]
  change incidence (unitReal.{u,v})ᵀ (incidence unitReal.{u,v} z) = μ • z at he
  have hzero : (1 - μ) • z = 0 := by
    rw [sub_smul, one_smul, ← hleft.symm.trans he, sub_self]
  have hμ' := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hz.2)
  simp [← hμ']

private theorem unit_contract (z : EuclideanSpace ℝ OneFace.{u})
    (hz : z ∈ LinearMap.range (incidence (unitReal.{u,v})).toLinearMap) :
    ‖residual unitReal.{u,v} 1 z‖ ≤ 0 * ‖z‖ := by
  have h := residual_contracts_of_spectral_gap unitReal.{u,v} (M := 1) (σ := 1)
    (by norm_num) le_rfl unit_norm unit_face_gap z hz
  norm_num at h ⊢
  exact h

namespace FacePropagation

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := coordinateSignature.{rowLevel}
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ) (g : F), g ∉ faceBall A f j →
      R.readout () ⟨F, g⟩ (((residual A M ^ j) (faceUnit f)) g) 0

private theorem rejected_law : ¬ arena.{u,v}.Law falseEquality := by
  intro h
  exact h (0 : Matrix (ULift.{u} Bool) OneEdge.{v} ℝ) 1 ⟨false⟩ 0 ⟨true⟩
    (by simp [faceBall])

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@residual_pow_vanishes.{rowLevel,columnLevel})) where
  actual := coordinateEquality
  bridge := Iff.rfl
  variation := ⟨@residual_pow_vanishes.{rowLevel,columnLevel}, falseEquality, rejected_law⟩
  sensitivity := equality_sensitivity arena rfl coordinateEquality falseEquality rejected_law
  dependence := equality_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@residual_pow_vanishes.{rowLevel,columnLevel}) (Realization coordinateSignature.{rowLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.residual_pow_vanishes.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.FacePropagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinateSignature.{rowLevel} (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[0, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FacePropagation

namespace TransposePropagation

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := coordinateSignature.{columnLevel}
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) (M : ℝ) (f : F) (j : ℕ) (e : E), e ∉ edgeBall A f j →
      R.readout () ⟨E, e⟩ (incidence Aᵀ ((residual A M ^ j) (faceUnit f)) e) 0

private theorem rejected_law : ¬ arena.{u,v}.Law falseEquality := by
  intro h
  exact h (0 : Matrix OneFace.{u} OneEdge.{v} ℝ) 1 default 0 default (by simp [edgeBall])

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@transpose_residual_pow_vanishes.{rowLevel,columnLevel})) where
  actual := coordinateEquality
  bridge := Iff.rfl
  variation := ⟨@transpose_residual_pow_vanishes.{rowLevel,columnLevel}, falseEquality, rejected_law⟩
  sensitivity := equality_sensitivity arena rfl coordinateEquality falseEquality rejected_law
  dependence := equality_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@transpose_residual_pow_vanishes.{rowLevel,columnLevel}) (Realization coordinateSignature.{columnLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.transpose_residual_pow_vanishes.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.TransposePropagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinateSignature.{columnLevel} (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[1, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransposePropagation

namespace ChebyshevPropagation

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := coordinateSignature.{columnLevel}
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) (M σ : ℝ) (f : F) (j : ℕ) (e : E), e ∉ edgeBall A f j →
      R.readout () ⟨E, e⟩ (chebyshevTerm A M σ f j e) 0

private theorem rejected_law : ¬ arena.{u,v}.Law falseEquality := by
  intro h
  exact h (0 : Matrix OneFace.{u} OneEdge.{v} ℝ) 2 1 default 0 default (by simp [edgeBall])

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@chebyshevTerm_vanishes.{rowLevel,columnLevel})) where
  actual := coordinateEquality
  bridge := Iff.rfl
  variation := ⟨@chebyshevTerm_vanishes.{rowLevel,columnLevel}, falseEquality, rejected_law⟩
  sensitivity := equality_sensitivity arena rfl coordinateEquality falseEquality rejected_law
  dependence := equality_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chebyshevTerm_vanishes.{rowLevel,columnLevel}) (Realization coordinateSignature.{columnLevel}) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.chebyshevTerm_vanishes.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.ChebyshevPropagation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinateSignature.{columnLevel} (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[1, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChebyshevPropagation

namespace SpectralContraction

private abbrev actual := realOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) {M σ : ℝ}, 0 < σ → σ ≤ M → ‖incidence A‖ ≤ M →
    (∀ μ > 0, Module.End.HasEigenvalue (laplacianOnRange A) μ → σ ^ 2 ≤ μ) →
    ∀ z : EuclideanSpace ℝ F, z ∈ LinearMap.range (incidence A).toLinearMap →
      R.readout () () ‖residual A M z‖ ((1 - σ ^ 2 / M ^ 2) * ‖z‖)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h unitReal.{u,v} (M := 1) (σ := 1) (by norm_num) le_rfl unit_norm unit_face_gap _ unit_image

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@residual_contracts_of_spectral_gap.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@residual_contracts_of_spectral_gap.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@residual_contracts_of_spectral_gap.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.residual_contracts_of_spectral_gap.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.SpectralContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralContraction

namespace NeumannRepair

private abbrev actual := realOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) {M q : ℝ}, 0 < M → 0 ≤ q → q < 1 → ‖incidence A‖ ≤ M →
    (∀ z ∈ LinearMap.range (incidence A).toLinearMap, ‖residual A M z‖ ≤ q * ‖z‖) →
    ∀ f : F, faceUnit f ∈ LinearMap.range (incidence A).toLinearMap →
    ∃ x : EuclideanSpace ℝ E, HasSum (neumannTerm A M f) x ∧
      incidence A x = faceUnit f ∧
      R.readout () () (∑ e, |x e|) (∑' j, neumannWeight A M q f j) ∧
      ∀ J, (∑ e ∈ Finset.univ \ edgeBall A f J, |x e|) ≤
        ∑' j, neumannWeight A M q f (j + (J + 1))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, _, hbad, _⟩ :=
    h unitReal.{u,v} (M := 1) (q := 0) (by norm_num) le_rfl zero_lt_one
      unit_norm unit_contract default unit_image
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@neumann_repair.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neumann_repair.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neumann_repair.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.neumann_repair.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.NeumannRepair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NeumannRepair

namespace ChebyshevRepair

private abbrev actual := realOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (A : Matrix F E ℝ) {M σ : ℝ}, 0 < σ → σ < M → ‖incidence A‖ ≤ M →
    (∀ μ > 0, Module.End.HasEigenvalue (laplacianOnRange A) μ → σ ^ 2 ≤ μ) →
    ∀ f : F, faceUnit f ∈ LinearMap.range (incidence A).toLinearMap →
    ∃ x : EuclideanSpace ℝ E, HasSum (chebyshevTerm A M σ f) x ∧
      incidence A x = faceUnit f ∧
      R.readout () () (∑ e, |x e|) (∑' j, chebyshevWeight A M σ f j) ∧
      ∀ J, (∑ e ∈ Finset.univ \ edgeBall A f J, |x e|) ≤
        ∑' j, chebyshevWeight A M σ f (j + (J + 1))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, _, hbad, _⟩ :=
    h unitReal.{u,v} (M := 2) (σ := 1) (by norm_num) (by norm_num)
      (unit_norm.trans (by norm_num)) unit_face_gap default unit_image
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@chebyshev_repair.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chebyshev_repair.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chebyshev_repair.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.chebyshev_repair.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.ChebyshevRepair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChebyshevRepair

namespace IntegralNeumann

private abbrev actual := realOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (D : Matrix F E ℤ), D.IsTotallyUnimodular →
    ∀ {M q : ℝ}, 0 < M → 0 ≤ q → q < 1 → ‖incidence (D.map (Int.castRingHom ℝ))‖ ≤ M →
    (∀ z ∈ LinearMap.range (incidence (D.map (Int.castRingHom ℝ))).toLinearMap,
      ‖residual (D.map (Int.castRingHom ℝ)) M z‖ ≤ q * ‖z‖) →
    ∀ f : F, faceUnit f ∈ LinearMap.range (incidence (D.map (Int.castRingHom ℝ))).toLinearMap →
    let b : F → ℤ := fun g => if g = f then 1 else 0
    let B := ∑' j, neumannWeight (D.map (Int.castRingHom ℝ)) M q f j
    ∃ z : E → ℤ, D *ᵥ z = b ∧ R.readout () () (∑ e, |(z e : ℝ)|) B ∧
      ∀ n : ℕ, (D.map (Int.castRingHom (ZMod n)) *ᵥ (fun e => (z e : ZMod n)) =
        fun g => (b g : ZMod n)) ∧
        ((nonzeroSupport (fun e => (z e : ZMod n))).card : ℝ) ≤ B

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, hbad, _⟩ :=
    h unitInteger.{u,v} unit_tu (M := 1) (q := 0) (by norm_num) le_rfl zero_lt_one
      unit_norm unit_contract default unit_image
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@neumann_integer_and_zmod_repair.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@neumann_integer_and_zmod_repair.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@neumann_integer_and_zmod_repair.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.neumann_integer_and_zmod_repair.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.IntegralNeumann.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntegralNeumann

namespace IntegralSpectral

private abbrev actual := realOrder

private abbrev arena.{rowLevel,columnLevel} : Arena where
  signature := signature
  Law R := ∀ {F : Type rowLevel} {E : Type columnLevel} [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    (D : Matrix F E ℤ), D.IsTotallyUnimodular →
    ∀ {M σ : ℝ}, 0 < σ → σ ≤ M → ‖incidence (D.map (Int.castRingHom ℝ))‖ ≤ M →
    (let A := D.map (Int.castRingHom ℝ)
      ∀ μ > 0,
        Module.End.HasEigenvalue ((incidence Aᵀ).comp (incidence A)).toLinearMap μ → σ ^ 2 ≤ μ) →
    ∀ f : F, faceUnit f ∈ LinearMap.range (incidence (D.map (Int.castRingHom ℝ))).toLinearMap →
    let A := D.map (Int.castRingHom ℝ)
    let b : F → ℤ := fun g => if g = f then 1 else 0
    let BN := ∑' j, neumannWeight A M (1 - σ ^ 2 / M ^ 2) f j
    let BC := ∑' j, chebyshevWeight A M σ f j
    let B := if σ < M then min BN BC else BN
    ∃ z : E → ℤ, D *ᵥ z = b ∧
      ((nonzeroSupport z).card : ℝ) ≤ ∑ e, |(z e : ℝ)| ∧
      R.readout () () (∑ e, |(z e : ℝ)|) B ∧
      ∀ n : ℕ, (D.map (Int.castRingHom (ZMod n)) *ᵥ (fun e => (z e : ZMod n)) =
        fun g => (b g : ZMod n)) ∧
        ((nonzeroSupport (fun e => (z e : ZMod n))).card : ℝ) ≤ B

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨_, _, _, hbad, _⟩ :=
    h unitInteger.{u,v} unit_tu (M := 1) (σ := 1) (by norm_num) le_rfl
      unit_norm unit_edge_gap default unit_image
  exact hbad

def family.{rowLevel,columnLevel} : Registration arena.{rowLevel,columnLevel} (type_of% (@spectral_integer_and_zmod_repair.{rowLevel,columnLevel})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_integer_and_zmod_repair.{rowLevel,columnLevel}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := order_dependence

def registration.{rowLevel,columnLevel} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectral_integer_and_zmod_repair.{rowLevel,columnLevel}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.spectral_integer_and_zmod_repair.__information_unit
  realizationName :=
    `Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen.IntegralSpectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{rowLevel,columnLevel}⟩
  objectArena := .source ⟨arena.{rowLevel,columnLevel}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{rowLevel,columnLevel} ⟨family.{rowLevel,columnLevel}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntegralSpectral

end

end Reg.D5.S3.HomologicalAlgebra.FiniteIncidenceGreen
