/- Source-only implementation candidate: no elaboration or kernel acceptance.
The full original VOA/CFT/anomaly/fusion/string/AdS objective remains incomplete.
The imported conformal-monodromy supplier itself remains source-only/unaccepted.
This file uses the original mode, classification and Hom restrictions; only
finite-grade traces and their analytic consequences require finite multiplicities. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleConformalMonodromy
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
import D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance
import Mathlib.LinearAlgebra.StdBasis

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleGradedCharacter

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeDiscriminantTheta LatticeDiscriminantWeil LatticeDualCosetConformal
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification ActualWeakModuleHom
open ActualWeakModuleConformalMonodromy (L0 degree tensorCoeff)
open LatticeSectorCharacterWeilCovariance (sectorGrade sectorTraceTerm sectorCharacter)
open private inverseGram_left inverseGram_right from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
open private classification_naturality familyMap from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom

universe u v w
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M) (hD : (gramReal D).PosDef)
attribute [local instance] Classical.propDecidable

/-- The literal eigenspace of the ORIGINAL omega mode 1, for every rational e. -/
def grade (e : ℚ) : Submodule ℂ M := (L0 J hD).eigenspace (e : ℂ)

/-- Labels use the canonical representative, exactly as the original classification does. -/
def GradeLabel (c : Discriminant D) (e : ℚ) := {a : Label D // degree c a = e}

/-- A coefficient model with arbitrary original multiplicities. -/
abbrev GradeCoefficients (e : ℚ) :=
  ∀ c : Discriminant D, GradeLabel c e →₀ Multiplicity J c

/-- Both inverse identities are consumed from classification, rather than assumed. -/
private theorem sectorGrade_eq (c : Discriminant D) (e : ℚ) :
    sectorGrade D (inverseGram hD) c e =
      LatticeDualCosetEnergy.rationalGrade D (dualVector D (representative D c)) e := by
  ext x
  rw [Module.End.mem_eigenspace_iff]
  exact LatticeDualCosetEnergy.moduleL_eigen_iff D (representative D c)
    (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD)
    (dualVector D (representative D c))
    (ActualWeakModuleConformalMonodromy.dualVector_duality hD _) e x

private def sectorCoeffEquiv (c : Discriminant D) (e : ℚ) :
    sectorGrade D (inverseGram hD) c e ≃ₗ[ℂ] (GradeLabel c e →₀ ℂ) :=
  (LinearEquiv.ofEq _ _ (sectorGrade_eq hD c e)).trans
    (LatticeDualCosetEnergy.gradeCoeffEquiv D (dualVector D (representative D c)) e)

private theorem sectorCoeffEquiv_apply (c : Discriminant D) (e : ℚ)
    (x : sectorGrade D (inverseGram hD) c e) (a : GradeLabel c e) :
    sectorCoeffEquiv hD c e x a = carrierCoeffEquiv D x.val a.val := rfl

private def sectorBasis (c : Discriminant D) (e : ℚ) :
    Module.Basis (GradeLabel c e) ℂ (sectorGrade D (inverseGram hD) c e) :=
  Module.Basis.ofRepr (sectorCoeffEquiv hD c e)

include hD in
private theorem gradeLabel_finite (c : Discriminant D) (e : ℚ) : Finite (GradeLabel c e) :=
  LatticeDualCosetEnergy.fiber_finite D (dualVector D (representative D c)) hD e

private theorem sectorGrade_finiteDimensional (c : Discriminant D) (e : ℚ) :
    Module.Finite ℂ (sectorGrade D (inverseGram hD) c e) := by
  letI := gradeLabel_finite hD c e
  exact Module.Finite.of_basis (sectorBasis hD c e)

private def allCoefficients : M ≃ₗ[ℂ] (∀ c : Discriminant D, Label D →₀ Multiplicity J c) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  exact ((classificationEquiv J hD).symm.trans
    (DirectSum.linearEquivFunOnFintype ℂ (Discriminant D) (Sector J))).trans
    (LinearEquiv.piCongrRight (tensorCoeff J))

private theorem allCoefficients_apply (x : M) (c : Discriminant D) (a : Label D) :
    allCoefficients J hD x c a =
      tensorCoeff J c (((classificationEquiv J hD).symm x) c) a := rfl

private def supportedGrade (e : ℚ) :
    Submodule ℂ (∀ c : Discriminant D, Label D →₀ Multiplicity J c) where
  carrier := {z | ∀ c, z c ∈ Finsupp.supported (Multiplicity J c) ℂ
    {a : Label D | degree c a = e}}
  zero_mem' c := (Finsupp.supported _ _ _).zero_mem
  add_mem' hx hy c := (Finsupp.supported _ _ _).add_mem (hx c) (hy c)
  smul_mem' s z hz c := (Finsupp.supported _ _ _).smul_mem s (hz c)

private def supportedGradeEquiv (e : ℚ) :
    supportedGrade J e ≃ₗ[ℂ] GradeCoefficients J e where
  toFun z c := Finsupp.supportedEquivFinsupp {a : Label D | degree c a = e}
    ⟨z.val c, z.property c⟩
  invFun z := ⟨fun c => ((Finsupp.supportedEquivFinsupp
    {a : Label D | degree c a = e}).symm (z c)).val,
    fun c => ((Finsupp.supportedEquivFinsupp
      {a : Label D | degree c a = e}).symm (z c)).property⟩
  left_inv z := by
    apply Subtype.ext
    funext c
    exact congrArg Subtype.val ((Finsupp.supportedEquivFinsupp
      {a : Label D | degree c a = e}).symm_apply_apply ⟨z.val c, z.property c⟩)
  right_inv z := by
    funext c
    exact (Finsupp.supportedEquivFinsupp
      {a : Label D | degree c a = e}).apply_symm_apply (z c)
  map_add' x y := by
    funext c
    exact map_add (Finsupp.supportedEquivFinsupp
      {a : Label D | degree c a = e}) ⟨x.val c, x.property c⟩ ⟨y.val c, y.property c⟩
  map_smul' s x := by
    funext c
    exact map_smul (Finsupp.supportedEquivFinsupp
      {a : Label D | degree c a = e}) s ⟨x.val c, x.property c⟩

private theorem grade_eq_comap (e : ℚ) :
    grade J hD e = (supportedGrade J e).comap (allCoefficients J hD).toLinearMap := by
  ext x
  change x ∈ (L0 J hD).eigenspace (e : ℂ) ↔ _
  rw [Module.End.mem_eigenspace_iff]
  exact ActualWeakModuleConformalMonodromy.L0_eigen_iff J hD e x

/-- Two-sided coordinates on the actual eigenspace. No finite-multiplicity premise. -/
def gradeCoefficientEquiv (e : ℚ) : grade J hD e ≃ₗ[ℂ] GradeCoefficients J e :=
  ((LinearEquiv.ofEq _ _ (grade_eq_comap J hD e)).trans
    (LinearEquiv.ofSubmodule' (allCoefficients J hD) (supportedGrade J e))).trans
    (supportedGradeEquiv J e)

/-- Forward readback is the existing ORIGINAL classification coefficient. -/
theorem gradeCoefficientEquiv_apply (e : ℚ) (x : grade J hD e)
    (c : Discriminant D) (a : GradeLabel c e) :
    gradeCoefficientEquiv J hD e x c a =
      tensorCoeff J c (((classificationEquiv J hD).symm x.val) c) a.val := by
  change allCoefficients J hD x.val c a.val = _
  exact allCoefficients_apply J hD x.val c a.val

/-- Inverse readback at every energy-e label. -/
theorem gradeCoefficientEquiv_symm_coeff (e : ℚ) (z : GradeCoefficients J e)
    (c : Discriminant D) (a : GradeLabel c e) :
    tensorCoeff J c (((classificationEquiv J hD).symm
      ((gradeCoefficientEquiv J hD e).symm z).val) c) a.val = z c a := by
  rw [← gradeCoefficientEquiv_apply, LinearEquiv.apply_symm_apply]

/-- The finite charge sum is written as its equivalent finite dependent product. -/
abbrev GradeModel (e : ℚ) :=
  ∀ c : Discriminant D, sectorGrade D (inverseGram hD) c e ⊗[ℂ] Multiplicity J c

private def sectorTensorCoeff (c : Discriminant D) (e : ℚ) :
    (sectorGrade D (inverseGram hD) c e ⊗[ℂ] Multiplicity J c) ≃ₗ[ℂ]
      (GradeLabel c e →₀ Multiplicity J c) :=
  TensorProduct.equivFinsuppOfBasisLeft (sectorBasis hD c e)

/-- Actual grade to finite sector-grade tensors, for arbitrary multiplicities. -/
def gradeEquiv (e : ℚ) : grade J hD e ≃ₗ[ℂ] GradeModel J hD e :=
  (gradeCoefficientEquiv J hD e).trans
    (LinearEquiv.piCongrRight (fun c => (sectorTensorCoeff J hD c e).symm))

theorem gradeEquiv_coeff (e : ℚ) (x : grade J hD e)
    (c : Discriminant D) (a : GradeLabel c e) :
    sectorTensorCoeff J hD c e (gradeEquiv J hD e x c) a =
      tensorCoeff J c (((classificationEquiv J hD).symm x.val) c) a.val := by
  change sectorTensorCoeff J hD c e
    ((sectorTensorCoeff J hD c e).symm (gradeCoefficientEquiv J hD e x c)) a = _
  rw [LinearEquiv.apply_symm_apply, gradeCoefficientEquiv_apply]

/-- Inverse coefficient readback for an arbitrary tuple of sector-grade tensors. -/
theorem gradeEquiv_symm_coeff (e : ℚ) (z : GradeModel J hD e)
    (c : Discriminant D) (a : GradeLabel c e) :
    tensorCoeff J c (((classificationEquiv J hD).symm
      ((gradeEquiv J hD e).symm z).val) c) a.val =
      sectorTensorCoeff J hD c e (z c) a := by
  rw [← gradeEquiv_coeff, LinearEquiv.apply_symm_apply]

/-- A true sector-grade vector produces an actual original-module eigenvector. -/
private def gradeGenerator (e : ℚ) (c : Discriminant D)
    (x : sectorGrade D (inverseGram hD) c e) (w : Multiplicity J c) : grade J hD e :=
  ⟨classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (x.val ⊗ₜ[ℂ] w)), by
    apply Module.End.mem_eigenspace_iff.mpr
    change FullJacobiCurrentTransport.mode J
      (LatticeActualConformalState.omega D (inverseGram hD)) 1
      (classificationEquiv J hD _) = _
    rw [← classification]
    simp only [canonicalModule, FullJacobiDirectSum.directSumModule_mode,
      DirectSum.lmap_lof, FullJacobiTensorModule.tensorModule_mode]
    change classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c
      (TensorProduct.map (moduleL D (representative D c) (inverseGram hD) 0)
        LinearMap.id (x.val ⊗ₜ[ℂ] w))) = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply,
      Module.End.mem_eigenspace_iff.mp x.property,
      ← TensorProduct.smul_tmul', map_smul, map_smul]⟩

private theorem gradeEquiv_generator (e : ℚ) (c : Discriminant D)
    (x : sectorGrade D (inverseGram hD) c e) (w : Multiplicity J c) :
    gradeEquiv J hD e (gradeGenerator J hD e c x w) = Pi.single c (x ⊗ₜ[ℂ] w) := by
  funext d
  apply (sectorTensorCoeff J hD d e).injective
  apply Finsupp.ext
  intro a
  rw [gradeEquiv_coeff]
  change tensorCoeff J d (((classificationEquiv J hD).symm
    (classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (x.val ⊗ₜ[ℂ] w)))) d)
    a.val = _
  rw [LinearEquiv.symm_apply_apply]
  by_cases h : c = d
  · subst d
    simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same, Pi.single_eq_same]
    change (TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D)
      (x.val ⊗ₜ[ℂ] w)) a.val =
      (TensorProduct.equivFinsuppOfBasisLeft (sectorBasis hD c e) (x ⊗ₜ[ℂ] w)) a
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    change carrierCoeffEquiv D x.val a.val • w = sectorCoeffEquiv hD c e x a • w
    rw [sectorCoeffEquiv_apply]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne c d _ (Ne.symm h)]
    simp [Pi.single_eq_of_ne (Ne.symm h)]

/-- Generator readback of the inverse, preserving the original representative. -/
theorem gradeEquiv_symm_single_tmul (e : ℚ) (c : Discriminant D)
    (x : sectorGrade D (inverseGram hD) c e) (w : Multiplicity J c) :
    ((gradeEquiv J hD e).symm (Pi.single c (x ⊗ₜ[ℂ] w))).val =
      classificationEquiv J hD (DirectSum.lof ℂ _ (Sector J) c (x.val ⊗ₜ[ℂ] w)) := by
  have h : (gradeEquiv J hD e).symm (Pi.single c (x ⊗ₜ[ℂ] w)) =
      gradeGenerator J hD e c x w := by
    apply (gradeEquiv J hD e).injective
    rw [LinearEquiv.apply_symm_apply, gradeEquiv_generator]
  exact congrArg Subtype.val h

/-- Every original all-mode intertwiner preserves each literal eigenspace. -/
theorem preserves_grade (f : ModuleHom J J) (e : ℚ) (x : M)
    (hx : x ∈ grade J hD e) : f.linearMap x ∈ grade J hD e := by
  apply Module.End.mem_eigenspace_iff.mpr
  have hx' := Module.End.mem_eigenspace_iff.mp hx
  change L0 J hD (f.linearMap x) = (e : ℂ) • f.linearMap x
  calc
    _ = f.linearMap (L0 J hD x) :=
      (f.intertwines (LatticeActualConformalState.omega D (inverseGram hD)) 1 x).symm
    _ = _ := by rw [hx', map_smul]

/-- Restriction of the independently supplied ORIGINAL endomorphism. -/
def gradeMap (f : ModuleHom J J) (e : ℚ) : Module.End ℂ (grade J hD e) :=
  (f.linearMap.comp (grade J hD e).subtype).codRestrict (grade J hD e)
    (fun x => preserves_grade J hD f e x.val x.property)

private theorem coeff_map_right {I : Type v} {V : Type w} {W : Type u}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (b : Module.Basis I ℂ V) (g : Module.End ℂ W) (z : V ⊗[ℂ] W) (a : I) :
    TensorProduct.equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id g z) a =
      g (TensorProduct.equivFinsuppOfBasisLeft b z a) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- Hom naturality is read back on actual vector-valued coefficients. -/
private theorem hom_coeff (f : ModuleHom J J) (x : M)
    (c : Discriminant D) (a : Label D) :
    tensorCoeff J c (((classificationEquiv J hD).symm (f.linearMap x)) c) a =
      restrict f c (tensorCoeff J c (((classificationEquiv J hD).symm x) c) a) := by
  have hn := classification_naturality f hD ((classificationEquiv J hD).symm x)
  rw [LinearEquiv.apply_symm_apply] at hn
  have hc : (classificationEquiv J hD).symm (f.linearMap x) =
      familyMap (restrict f) ((classificationEquiv J hD).symm x) := by
    rw [hn, LinearEquiv.symm_apply_apply]
  rw [hc, familyMap, DirectSum.lmap_apply]
  exact coeff_map_right (carrierBasis D) (restrict f c) _ a

/-- Explicit map in the finite charge sum: identity on the ACTUAL sector grade
and the actual restriction of f on the ORIGINAL multiplicity subtype. -/
def gradeModelMap (f : ModuleHom J J) (e : ℚ) : Module.End ℂ (GradeModel J hD e) :=
  LinearMap.piMap (fun c => TensorProduct.map LinearMap.id (restrict f c))

private theorem gradeEquiv_map (f : ModuleHom J J) (e : ℚ) (x : grade J hD e) :
    gradeEquiv J hD e (gradeMap J hD f e x) =
      gradeModelMap J hD f e (gradeEquiv J hD e x) := by
  funext c
  apply (sectorTensorCoeff J hD c e).injective
  apply Finsupp.ext
  intro a
  rw [gradeEquiv_coeff]
  change tensorCoeff J c (((classificationEquiv J hD).symm (f.linearMap x.val)) c) a.val =
    sectorTensorCoeff J hD c e
      (TensorProduct.map LinearMap.id (restrict f c) (gradeEquiv J hD e x c)) a
  rw [hom_coeff]
  change _ = TensorProduct.equivFinsuppOfBasisLeft (sectorBasis hD c e)
    (TensorProduct.map LinearMap.id (restrict f c) (gradeEquiv J hD e x c)) a
  rw [coeff_map_right]
  change _ = restrict f c (sectorTensorCoeff J hD c e (gradeEquiv J hD e x c) a)
  rw [gradeEquiv_coeff]

/-- Substantive conjugated-map comparison, proved rather than assumed. -/
theorem gradeMap_conjugate (f : ModuleHom J J) (e : ℚ) :
    (gradeEquiv J hD e).conj (gradeMap J hD f e) = gradeModelMap J hD f e := by
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply, gradeEquiv_map, LinearEquiv.apply_symm_apply]

section FiniteMultiplicities
variable [∀ c : Discriminant D, Module.Finite ℂ (Multiplicity J c)]

/-- Only finite multiplicities are added; the whole original carrier is arbitrary. -/
theorem grade_finiteDimensional (e : ℚ) : FiniteDimensional ℂ (grade J hD e) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  letI : ∀ c : Discriminant D, Module.Finite ℂ (sectorGrade D (inverseGram hD) c e) :=
    fun c => sectorGrade_finiteDimensional hD c e
  letI : ∀ c : Discriminant D,
      Module.Finite ℂ (sectorGrade D (inverseGram hD) c e ⊗[ℂ] Multiplicity J c) :=
    fun c => inferInstance
  exact Module.Finite.equiv (gradeEquiv J hD e).symm

/-- The finite dependent-product matrix has the original multiplicity tensor
blocks. Matrix block trace and tensor trace are the existing Mathlib suppliers. -/
private theorem gradeModelMap_trace (f : ModuleHom J J) (e : ℚ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    LinearMap.trace ℂ (GradeModel J hD e) (gradeModelMap J hD f e) =
      ∑ c : Discriminant D, LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        LinearMap.trace ℂ (sectorGrade D (inverseGram hD) c e) LinearMap.id := by
  classical
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  letI : ∀ c : Discriminant D, Module.Finite ℂ (sectorGrade D (inverseGram hD) c e) :=
    fun c => sectorGrade_finiteDimensional hD c e
  let b := fun c : Discriminant D => Module.Free.chooseBasis ℂ
    (sectorGrade D (inverseGram hD) c e ⊗[ℂ] Multiplicity J c)
  let B := Pi.basis b
  have hm : LinearMap.toMatrix B B (gradeModelMap J hD f e) =
      Matrix.blockDiagonal' (fun c => LinearMap.toMatrix (b c) (b c)
        (TensorProduct.map LinearMap.id (restrict f c))) := by
    ext ⟨c, i⟩ ⟨d, j⟩
    by_cases h : c = d
    · subst d
      simp [B, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
        gradeModelMap, LinearMap.piMap, Matrix.blockDiagonal'_apply_eq]
    · simp [B, LinearMap.toMatrix_apply', Pi.basis_apply, Pi.basis_repr,
        gradeModelMap, LinearMap.piMap, Matrix.blockDiagonal'_apply_ne, h, Ne.symm h]
  rw [LinearMap.trace_eq_matrix_trace ℂ B, hm, Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro c hc
  rw [← LinearMap.trace_eq_matrix_trace ℂ (b c), LinearMap.trace_tensorProduct', mul_comm]

/-- The trace is taken on the ACTUAL original eigenspace and actual restricted f. -/
theorem gradeMap_trace (f : ModuleHom J J) (e : ℚ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    LinearMap.trace ℂ (grade J hD e) (gradeMap J hD f e) =
      ∑ c : Discriminant D, LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        LinearMap.trace ℂ (sectorGrade D (inverseGram hD) c e) LinearMap.id := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  letI := grade_finiteDimensional J hD e
  calc
    _ = LinearMap.trace ℂ (GradeModel J hD e)
        ((gradeEquiv J hD e).conj (gradeMap J hD f e)) :=
      (LinearMap.trace_conj' (gradeMap J hD f e) (gradeEquiv J hD e)).symm
    _ = _ := by rw [gradeMap_conjugate, gradeModelMap_trace]

/-- Defined from the ACTUAL finite-grade endomorphism trace. -/
def traceTerm (f : ModuleHom J J) (τ : ℂ) (e : ℚ) : ℂ := by
  letI := grade_finiteDimensional J hD e
  exact LinearMap.trace ℂ (grade J hD e) (gradeMap J hD f e) *
    Complex.exp (2 * Real.pi * Complex.I * τ * ((e : ℂ) - D.rank / 24))

/-- The definition sums actual grade traces over ALL rational energies. -/
def character (f : ModuleHom J J) (τ : ℂ) : ℂ := ∑' e : ℚ, traceTerm J hD f τ e

private theorem traceTerm_eq (f : ModuleHom J J) (τ : ℂ) (e : ℚ) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    traceTerm J hD f τ e =
      ∑ c : Discriminant D, LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        sectorTraceTerm D hD (inverseGram hD) (inverseGram_left hD)
          (inverseGram_right hD) c τ e := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  change LinearMap.trace ℂ (grade J hD e) (gradeMap J hD f e) * _ = _
  rw [gradeMap_trace, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [sectorTraceTerm, mul_assoc]

/-- Absolute convergence is inherited only AFTER the original trace bridge. -/
theorem character_summable_norm (f : ModuleHom J J) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun e : ℚ => ‖traceTerm J hD f τ e‖) := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hs (c : Discriminant D) :=
    (LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform D hD
      (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD) c τ hτ).1
  have hw (c : Discriminant D) : Summable (fun e : ℚ =>
      ‖LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        sectorTraceTerm D hD (inverseGram hD) (inverseGram_left hD)
          (inverseGram_right hD) c τ e‖) := by
    simpa only [norm_mul] using
      (hs c).mul_left ‖LinearMap.trace ℂ (Multiplicity J c) (restrict f c)‖
  have hmajor := summable_sum (s := Finset.univ) (fun c _ => hw c)
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro e
  rw [traceTerm_eq]
  exact norm_sum_le _ _

/-- The weighted sector expression is a theorem about the trace-defined character. -/
theorem character_eq (f : ModuleHom J J) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    character J hD f τ =
      ∑ c : Discriminant D, LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        sectorCharacter D hD (inverseGram hD) (inverseGram_left hD)
          (inverseGram_right hD) c τ := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hs (c : Discriminant D) :=
    (LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform D hD
      (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD) c τ hτ).1.of_norm
  have hw (c : Discriminant D) : HasSum (fun e : ℚ =>
      LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        sectorTraceTerm D hD (inverseGram hD) (inverseGram_left hD)
          (inverseGram_right hD) c τ e)
      (LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        sectorCharacter D hD (inverseGram hD) (inverseGram_left hD)
          (inverseGram_right hD) c τ) := by
    simpa only [sectorCharacter, tsum_mul_left] using
      ((hs c).mul_left (LinearMap.trace ℂ (Multiplicity J c) (restrict f c))).hasSum
  have h := hasSum_sum (s := Finset.univ) (fun c _ => hw c)
  exact (h.congr_fun (fun e => traceTerm_eq J hD f τ e)).tsum_eq

/-- SAME negative Weil S supplier. Arbitrary multiplicity traces are weights;
no invariance of that weight vector, or identification with a positive Hopf matrix. -/
theorem character_s_transform (f : ModuleHom J J) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    character J hD f (-1 / τ) =
      ∑ c : Discriminant D, LinearMap.trace ℂ (Multiplicity J c) (restrict f c) *
        (weilS D (fun d => sectorCharacter D hD (inverseGram hD)
          (inverseGram_left hD) (inverseGram_right hD) d τ)) c := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  rw [character_eq J hD f (-1 / τ) hS]
  apply Finset.sum_congr rfl
  intro c hc
  rw [(LatticeSectorCharacterWeilCovariance.lattice_sector_character_s_transform D hD
    (inverseGram hD) (inverseGram_left hD) (inverseGram_right hD) c τ hτ).2]

end FiniteMultiplicities

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleGradedCharacter
