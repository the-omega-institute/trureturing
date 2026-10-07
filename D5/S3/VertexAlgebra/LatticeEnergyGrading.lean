/- GID: D5/S3/VertexAlgebra/LatticeEnergyGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeEnergyGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual energy grades, finite bases and internal direct-sum decomposition. -/

/-
The actual all-charge monomial basis, exact coefficient-support submodules,
finite bases, and vacuum normalization. No finite-dimensionality assumption.
Bakalov--Kac math/0402315v1 §4.1 (4.3)--(4.5), Thm4.1/(4.16);
Def2.2/(2.23)--(2.24). DLM q-alg/9508018v1 Def2.1 supplies the
ordinary-module convention, not a premise of the proofs below.
Mathlib basis/support machinery: Apache 2.0, original authors retained.
-/
import D5.S3.VertexAlgebra.LatticeChargeCoercivity
import D5.S3.VertexAlgebra.LatticeAllStateField
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticePositiveEnergy
open LatticeGeneratingFieldLocality LatticeAllStateField MvPolynomial
open scoped BigOperators DirectSum
noncomputable section

def carrierCoeffEquiv (D : LatticeData) : Carrier D ≃ₗ[ℂ] (Label D →₀ ℂ) :=
  (Finsupp.mapRange.linearEquiv (basisMonomials (Index D) ℂ).repr).trans
    (Finsupp.curryLinearEquiv ℂ).symm

def carrierBasis (D : LatticeData) : Module.Basis (Label D) ℂ (Carrier D) :=
  Module.Basis.ofRepr (carrierCoeffEquiv D)

@[simp] theorem carrierBasis_apply (D : LatticeData) (a : Label D) :
    carrierBasis D a = Finsupp.single a.1 (monomial a.2 1) := by
  apply (carrierCoeffEquiv D).injective
  change (carrierCoeffEquiv D) ((carrierCoeffEquiv D).symm (Finsupp.single a 1)) = _
  rw [LinearEquiv.apply_symm_apply]
  ext b
  change Finsupp.single a (1 : ℂ) b =
    coeff b.2 ((Finsupp.single a.1 (monomial a.2 1)) b.1)
  by_cases h : a.1 = b.1
  · simp [Finsupp.single_apply, h, coeff_monomial,
      Prod.ext_iff, and_comm]
  · simp [Finsupp.single_apply, h, Prod.ext_iff]

/-- Exact support of the actual charge/monomial coefficients at integer energy n. -/
abbrev grade (D : LatticeData) (n : ℤ) : Submodule ℂ (Carrier D) :=
  (Finsupp.supported ℂ ℂ {a : Label D | energy D a = n}).comap
    (carrierCoeffEquiv D).toLinearMap

theorem mem_grade_iff (D : LatticeData) (n : ℤ) (v : Carrier D) :
    v ∈ grade D n ↔ ∀ a : Label D, energy D a ≠ n → coeff a.2 (v a.1) = 0 := by
  change carrierCoeffEquiv D v ∈ Finsupp.supported ℂ ℂ _ ↔ _
  rw [Finsupp.mem_supported']
  rfl

/-- This equivalence uses the entire fiber; no positivity or finiteness is needed. -/
def gradeCoeffEquiv (D : LatticeData) (n : ℤ) :
    grade D n ≃ₗ[ℂ] (EnergyFiber D n →₀ ℂ) :=
  (LinearEquiv.ofSubmodule' (carrierCoeffEquiv D)
    (Finsupp.supported ℂ ℂ {a : Label D | energy D a = n})).trans
      (Finsupp.supportedEquivFinsupp _)

def gradeBasis (D : LatticeData) (n : ℤ) :
    Module.Basis (EnergyFiber D n) ℂ (grade D n) :=
  Module.Basis.ofRepr (gradeCoeffEquiv D n)

theorem grade_eq_span (D : LatticeData) (n : ℤ) :
    grade D n = Submodule.span ℂ (carrierBasis D '' {a : Label D | energy D a = n}) := by
  ext v
  change ((carrierCoeffEquiv D v).support : Set (Label D)) ⊆ {a : Label D | energy D a = n} ↔ _
  exact (carrierBasis D).mem_span_image.symm

theorem grade_finiteDimensional (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) :
    FiniteDimensional ℂ (grade D n) := by
  haveI := energyFiber_finite D hD n
  exact Module.Finite.of_basis (gradeBasis D n)

theorem grade_negative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (hn : n < 0) :
    grade D n = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  apply (carrierCoeffEquiv D).injective
  ext a
  have ha : energy D a ≠ n := by have h := energy_nonneg D hD a; omega
  exact (mem_grade_iff D n v).mp hv a ha

theorem grade_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    grade D 0 = Submodule.span ℂ {vacuum D} := by
  rw [grade_eq_span]
  have hs : {a : Label D | energy D a = 0} = {(0,0)} := by
    ext a
    simpa using energy_eq_zero_iff D hD a
  rw [hs, Set.image_singleton]
  simp [vacuum]

@[simp] theorem vacuum_nonzero (D : LatticeData) : vacuum D ≠ 0 := by
  simp [vacuum]

/-- Scalar multiplication of the actual vacuum parametrizes the entire zero grade. -/
def vacuumGradeEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : ℂ ≃ₗ[ℂ] grade D 0 :=
  (LinearEquiv.toSpanNonzeroSingleton ℂ (Carrier D) (vacuum D) (vacuum_nonzero D)).trans
    (LinearEquiv.ofEq _ _ (grade_zero D hD).symm)

theorem energyFiber_negative (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (hn : n < 0) :
    IsEmpty (EnergyFiber D n) := by
  refine ⟨fun a => ?_⟩
  have h := energy_nonneg D hD a.1
  rw [a.2] at h
  omega

theorem rank_zero_label (D : LatticeData) (hr : D.rank = 0) (a : Label D) :
    a = (0,0) := by
  apply Prod.ext
  · ext i
    have hi := i.isLt
    omega
  · ext x
    have hi := x.1.isLt
    omega

theorem rank_zero_carrier (D : LatticeData) (hr : D.rank = 0) :
    Submodule.span ℂ {vacuum D} = ⊤ := by
  have hs : Set.range (carrierBasis D) = {vacuum D} := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [rank_zero_label D hr a]
      simp [vacuum]
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      exact ⟨(0,0), by simp [hv, vacuum]⟩
  rw [← hs]
  exact (carrierBasis D).span_eq

/-- In rank zero the entire actual carrier is exactly one vacuum line. -/
def rankZeroVacuumEquiv (D : LatticeData) (hr : D.rank = 0) : ℂ ≃ₗ[ℂ] Carrier D :=
  (LinearEquiv.toSpanNonzeroSingleton ℂ (Carrier D) (vacuum D) (vacuum_nonzero D)).trans
    (LinearEquiv.ofTop _ (rank_zero_carrier D hr))

/-- The actual finite projection, transported from coefficient filtering. -/
def gradeProjection (D : LatticeData) (n : ℤ) : Module.End ℂ (Carrier D) := by
  classical
  exact (carrierCoeffEquiv D).symm.toLinearMap.comp
    ((Finsupp.supported ℂ ℂ {a : Label D | energy D a = n}).subtype.comp
      ((Finsupp.restrictDom ℂ ℂ {a : Label D | energy D a = n}).comp
        (carrierCoeffEquiv D).toLinearMap))

@[simp] theorem gradeProjection_coeff (D : LatticeData) (n : ℤ)
    (v : Carrier D) (a : Label D) :
    carrierCoeffEquiv D (gradeProjection D n v) a =
      if energy D a = n then carrierCoeffEquiv D v a else 0 := by
  classical
  simp [gradeProjection, Finsupp.filter_apply]

theorem gradeProjection_mem (D : LatticeData) (n : ℤ) (v : Carrier D) :
    gradeProjection D n v ∈ grade D n := by
  rw [mem_grade_iff]
  intro a ha
  change carrierCoeffEquiv D (gradeProjection D n v) a = 0
  simpa [ha] using gradeProjection_coeff D n v a

/-- The finite set of energies present in an arbitrary actual state. -/
def stateEnergies (D : LatticeData) (v : Carrier D) : Finset ℤ := by
  classical
  exact (carrierCoeffEquiv D v).support.image (energy D)

theorem sum_gradeProjections (D : LatticeData) (v : Carrier D) :
    ∑ n ∈ stateEnergies D v, gradeProjection D n v = v := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext a
  change ((Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap)
    (∑ n ∈ stateEnergies D v, gradeProjection D n v) = _
  rw [map_sum]
  change (∑ n ∈ stateEnergies D v, carrierCoeffEquiv D (gradeProjection D n v) a) = _
  simp_rw [gradeProjection_coeff]
  by_cases ha : a ∈ (carrierCoeffEquiv D v).support
  · have he : energy D a ∈ stateEnergies D v := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    simp [Finset.sum_ite_eq', he]
  · have hz := Finsupp.notMem_support_iff.mp ha
    simp [hz]

/-- Independence against the sum of *all* other grades. -/
theorem grades_independent (D : LatticeData) : iSupIndep (grade D) := by
  intro n
  rw [disjoint_iff_inf_le]
  rintro v ⟨hv, ho⟩
  rw [Submodule.mem_bot]
  apply (carrierCoeffEquiv D).injective
  ext a
  by_cases ha : energy D a = n
  · let f : Carrier D →ₗ[ℂ] ℂ := (Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap
    have hle : (⨆ j ≠ n, grade D j) ≤ LinearMap.ker f := by
      apply iSup₂_le
      intro j hj
      intro w hw
      exact (mem_grade_iff D j w).mp hw a (by omega)
    exact hle ho
  · exact (mem_grade_iff D n v).mp hv a ha

theorem grades_iSup (D : LatticeData) : (⨆ n : ℤ, grade D n) = ⊤ := by
  apply top_unique
  intro v hv
  rw [← sum_gradeProjections D v]
  apply Submodule.sum_mem
  intro n hn
  exact (le_iSup (grade D) n) (gradeProjection_mem D n v)

/-- The canonical sum of subtype inclusions is bijective. -/
theorem grades_internal (D : LatticeData) : DirectSum.IsInternal (grade D) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (grades_independent D) (grades_iSup D)

/-- Every arbitrary nonhomogeneous state decomposes in the actual internal direct sum. -/
def carrierEnergyDecomposition (D : LatticeData) :
    Carrier D ≃ₗ[ℂ] (⨁ n : ℤ, grade D n) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (grade D)) (grades_internal D)).symm

#print axioms grade_finiteDimensional
#print axioms grade_negative
#print axioms grade_zero
#print axioms rank_zero_carrier
#print axioms sum_gradeProjections
#print axioms grades_internal
end
end D5.S3.VertexAlgebra.LatticePositiveEnergy
