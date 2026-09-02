/- GID: D5/S3/Quantum/MultifactorCorrelationSectorDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/MultifactorCorrelationSectorDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Hermitian tensor factors split into correlation sectors indexed by subsets. -/

/- Library-search audit trail (2026-09-02):
   * Six-way repository, receipt, digest, generalized-name, and in-flight searches found the
     bipartite decomposition and an in-flight single-prime readout theorem, but no theorem proving
     the finite-family internal decomposition and all sector dimensions requested here.
   * The in-flight `SinglePrimeVisibleSpace` assumes both `DirectSum.IsInternal` and the sector
     dimension formula, so it does not cover this theorem.
   * Pinned Mathlib provides `PiTensorProduct.ofDirectSumEquiv`,
     `DirectSum.lequivCongrLeft`, `iSupIndep_range_lsingle`, `Module.finrank_directSum`, and
     `Finset.prod_one_add`. These are used directly below. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.MultifactorCorrelationSectorDecomposition

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two canonical local Hermitian sectors: scalar identity and trace zero. -/
def factorSector (d : Nat) : Bool → Submodule ℝ (HermitianSpace d)
  | false => scalarHermitian d
  | true => traceZeroHermitian d

private def hermitianRealTrace (d : Nat) : HermitianSpace d →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace A.1).re
  map_add' A B := by
    simp [Matrix.trace_add]
  map_smul' r A := by
    change (Matrix.trace (r • A.1)).re = r • (Matrix.trace A.1).re
    simp

private theorem hermitian_trace_eq_re {d : Nat} (A : HermitianSpace d) :
    Matrix.trace A.1 = ((Matrix.trace A.1).re : ℂ) := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : Matrix.conjTranspose A.1 = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  have hstar : star (Matrix.trace A.1) = Matrix.trace A.1 := by
    calc
      star (Matrix.trace A.1) = Matrix.trace (Matrix.conjTranspose A.1) :=
        (Matrix.trace_conjTranspose A.1).symm
      _ = Matrix.trace A.1 := by rw [hA]
  exact (Complex.conj_eq_iff_re.mp hstar).symm

private theorem trace_zero_eq_ker (d : Nat) :
    traceZeroHermitian d = LinearMap.ker (hermitianRealTrace d) := by
  ext A
  change Matrix.trace A.1 = 0 ↔ (Matrix.trace A.1).re = 0
  rw [hermitian_trace_eq_re A]
  simp

private theorem real_trace_identity (d : Nat) :
    hermitianRealTrace d (identityHermitian d) = d := by
  change (Matrix.trace (1 : Matrix (Fin d) (Fin d) ℂ)).re = d
  simp

private theorem scalar_trace_zero_isCompl (d : Nat) [NeZero d] :
    IsCompl (scalarHermitian d) (traceZeroHermitian d) := by
  rw [trace_zero_eq_ker]
  have htrace : hermitianRealTrace d (identityHermitian d) ≠ 0 := by
    rw [real_trace_identity]
    exact_mod_cast NeZero.ne d
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro A ⟨hA, hker⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hA
    have hr : r = 0 := by
      have hzero := LinearMap.mem_ker.mp hker
      simp only [map_smul, real_trace_identity] at hzero
      exact (mul_eq_zero.mp hzero).resolve_right (by exact_mod_cast NeZero.ne d)
    simp [hr]
  · exact (hermitianRealTrace d).span_singleton_sup_ker_eq_top htrace

private theorem factor_sector_isInternal (d : Nat) [NeZero d] :
    DirectSum.IsInternal (factorSector d) := by
  refine (DirectSum.isInternal_submodule_iff_isCompl
    (factorSector d) Bool.false_ne_true ?_).mpr ?_
  · ext b
    cases b <;> simp
  · simpa [factorSector] using scalar_trace_zero_isCompl d

/-- The canonical local decomposition into the scalar and traceless Hermitian sectors. -/
noncomputable def factorDecompositionEquiv (d : Nat) [NeZero d] :
    HermitianSpace d ≃ₗ[ℝ] DirectSum Bool (fun b => (factorSector d b : Type)) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (factorSector d))
    (factor_sector_isInternal d)).symm

/-- A Boolean choice at every factor is canonically the subset where trace-zero was chosen. -/
def supportEquiv : (ι → Bool) ≃ Finset ι where
  toFun p := Finset.univ.filter fun i => p i = true
  invFun S i := decide (i ∈ S)
  left_inv p := by
    funext i
    cases h : p i <;> simp [h]
  right_inv S := by
    ext i
    simp

/-- The real Hermitian tensor carrier for a finite family of local dimensions. -/
abbrev GlobalHermitian (d : ι → Nat) :=
  ⨂[ℝ] i, HermitianSpace (d i)

/-- The abstract tensor factor carried by the correlation subset `S`. -/
abbrev SectorTensor (d : ι → Nat) (S : Finset ι) :=
  ⨂[ℝ] i, factorSector (d i) ((supportEquiv (ι := ι)).symm S i)

/-- Tensoring the local scalar/traceless decompositions and distributing tensor product over
direct sums gives the canonical full correlation-coordinate system. -/
noncomputable def decompositionEquiv (d : ι → Nat) [∀ i, NeZero (d i)] :
    GlobalHermitian d ≃ₗ[ℝ] DirectSum (Finset ι) (SectorTensor d) :=
  let localEquiv :
      GlobalHermitian d ≃ₗ[ℝ]
        ⨂[ℝ] i, DirectSum Bool (fun b => (factorSector (d i) b : Type)) :=
    PiTensorProduct.congr (fun i => factorDecompositionEquiv (d i))
  let distribute :
      (⨂[ℝ] i, DirectSum Bool (fun b => (factorSector (d i) b : Type))) ≃ₗ[ℝ]
        DirectSum (ι → Bool) (fun p => ⨂[ℝ] i, (factorSector (d i) (p i) : Type)) :=
    PiTensorProduct.ofDirectSumEquiv
  let reindex :
      DirectSum (ι → Bool) (fun p => ⨂[ℝ] i, (factorSector (d i) (p i) : Type)) ≃ₗ[ℝ]
        DirectSum (Finset ι) (SectorTensor d) :=
    DirectSum.lequivCongrLeft ℝ (supportEquiv (ι := ι))
  localEquiv ≪≫ₗ distribute ≪≫ₗ reindex

/-- The correlation sector with trace-zero local factors exactly on `S` and scalar-identity
local factors off `S`. -/
def correlationSector (d : ι → Nat) [∀ i, NeZero (d i)] (S : Finset ι) :
    Submodule ℝ (GlobalHermitian d) :=
  (LinearMap.range
    (DFinsupp.lsingle S : SectorTensor d S →ₗ[ℝ] DirectSum (Finset ι) (SectorTensor d))).map
      (decompositionEquiv d).symm.toLinearMap

/-- The scalar coordinate of a global Hermitian tensor. Its kernel is the global trace-zero
carrier because every nonempty sector contains a trace-zero local factor. -/
def scalarCoordinate (d : ι → Nat) [∀ i, NeZero (d i)] :
    GlobalHermitian d →ₗ[ℝ] SectorTensor d ∅ :=
  (DFinsupp.lapply ∅).comp (decompositionEquiv d).toLinearMap

/-- The global trace-zero Hermitian carrier. -/
def traceZeroGlobal (d : ι → Nat) [∀ i, NeZero (d i)] :
    Submodule ℝ (GlobalHermitian d) :=
  LinearMap.ker (scalarCoordinate d)

/-- Sectors of order strictly greater than `k`, invisible to readouts retaining at most `k`
local factors. -/
def unobservedHighOrder (d : ι → Nat) [∀ i, NeZero (d i)] (k : Nat) :
    Submodule ℝ (GlobalHermitian d) :=
  ⨆ S : {S : Finset ι // k < S.card}, correlationSector d S.1

private theorem scalar_hermitian_finrank (d : Nat) [NeZero d] :
    Module.finrank ℝ (scalarHermitian d) = 1 := by
  apply finrank_span_singleton
  intro hzero
  have hval : (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := congrArg Subtype.val hzero
  exact one_ne_zero hval

private theorem factor_sector_finrank (d : Nat) [NeZero d] (b : Bool) :
    Module.finrank ℝ (factorSector d b) = if b then d ^ 2 - 1 else 1 := by
  cases b with
  | false =>
      change Module.finrank ℝ (scalarHermitian d) = 1
      exact scalar_hermitian_finrank d
  | true =>
      change Module.finrank ℝ (traceZeroHermitian d) = d ^ 2 - 1
      exact trace_zero_hermitian_finrank d

private theorem pi_tensor_finrank
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)] :
    Module.finrank ℝ (⨂[ℝ] i, V i) = ∏ i, Module.finrank ℝ (V i) := by
  let b := fun i => Module.finBasis ℝ (V i)
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi]
  simp only [Fintype.card_fin]

private theorem sector_tensor_finrank (d : ι → Nat) [∀ i, NeZero (d i)]
    (S : Finset ι) :
    Module.finrank ℝ (SectorTensor d S) = ∏ i ∈ S, (d i ^ 2 - 1) := by
  rw [pi_tensor_finrank]
  calc
    (∏ i, Module.finrank ℝ
        (factorSector (d i) ((supportEquiv (ι := ι)).symm S i))) =
        ∏ i, if i ∈ S then d i ^ 2 - 1 else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [factor_sector_finrank]
      by_cases hi : i ∈ S <;> simp [supportEquiv, hi]
    _ = ∏ i ∈ S, (d i ^ 2 - 1) := by simp

/-- Every sector has the product of the local traceless dimensions on its support. -/
theorem correlation_sector_finrank (d : ι → Nat) [∀ i, NeZero (d i)]
    (S : Finset ι) :
    Module.finrank ℝ (correlationSector d S) = ∏ i ∈ S, (d i ^ 2 - 1) := by
  rw [correlationSector, (decompositionEquiv d).symm.finrank_map_eq]
  rw [LinearMap.finrank_range_of_inj]
  · exact sector_tensor_finrank d S
  · intro x y hxy
    have hcoordinate := congrArg
      (DFinsupp.lapply S : DirectSum (Finset ι) (SectorTensor d) →ₗ[ℝ] SectorTensor d S) hxy
    change (DFinsupp.single S x) S = (DFinsupp.single S y) S at hcoordinate
    simpa only [DFinsupp.single_eq_same] using hcoordinate

private theorem correlation_sectors_isInternal (d : ι → Nat) [∀ i, NeZero (d i)] :
    DirectSum.IsInternal (correlationSector d) := by
  let coordinateSector := fun S : Finset ι =>
    LinearMap.range
      (DFinsupp.lsingle S : SectorTensor d S →ₗ[ℝ] DirectSum (Finset ι) (SectorTensor d))
  have hind : iSupIndep coordinateSector := by
    intro S
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hxS, hxOther⟩
    obtain ⟨y, rfl⟩ := hxS
    have hle : (⨆ T, ⨆ (_ : T ≠ S), coordinateSector T) ≤
        LinearMap.ker (DFinsupp.lapply S) := by
      refine iSup_le fun T => iSup_le fun hTS => ?_
      rintro _ ⟨z, rfl⟩
      exact LinearMap.mem_ker.mpr (by simp [hTS])
    have hy : y = 0 := by
      simpa using LinearMap.mem_ker.mp (hle hxOther)
    simp [hy]
  have hmapped : iSupIndep (correlationSector d) := by
    change iSupIndep (fun S => (coordinateSector S).map
      (decompositionEquiv d).symm.toLinearMap)
    exact LinearMap.iSupIndep_map (decompositionEquiv d).symm.toLinearMap
      (decompositionEquiv d).symm.injective hind
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hmapped
  have hcoordinate : ⨆ S, coordinateSector S = ⊤ := by
    simpa [coordinateSector] using
      (DFinsupp.iSup_range_lsingle (R := ℝ) (M := SectorTensor d))
  change (⨆ S, (coordinateSector S).map (decompositionEquiv d).symm.toLinearMap) = ⊤
  rw [← Submodule.map_iSup, hcoordinate, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (decompositionEquiv d).symm.surjective

private theorem global_hermitian_finrank (d : ι → Nat) :
    Module.finrank ℝ (GlobalHermitian d) = (∏ i, d i) ^ 2 := by
  rw [pi_tensor_finrank]
  simp_rw [hermitian_space_finrank]
  rw [← Finset.prod_pow]

private theorem scalar_coordinate_surjective (d : ι → Nat) [∀ i, NeZero (d i)] :
    Function.Surjective (scalarCoordinate d) := by
  intro x
  refine ⟨(decompositionEquiv d).symm (DFinsupp.single ∅ x), ?_⟩
  simp [scalarCoordinate]

private theorem trace_zero_global_finrank (d : ι → Nat) [∀ i, NeZero (d i)] :
    Module.finrank ℝ (traceZeroGlobal d) = (∏ i, d i) ^ 2 - 1 := by
  change Module.finrank ℝ (LinearMap.ker (scalarCoordinate d)) = (∏ i, d i) ^ 2 - 1
  have hrange : LinearMap.range (scalarCoordinate d) = ⊤ :=
    LinearMap.range_eq_top.mpr (scalar_coordinate_surjective d)
  have hrank : 1 + Module.finrank ℝ (LinearMap.ker (scalarCoordinate d)) =
      (∏ i, d i) ^ 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker (scalarCoordinate d)
    rw [hrange, finrank_top, sector_tensor_finrank d ∅, global_hermitian_finrank d] at h
    simpa only [Finset.prod_empty] using h
  omega

private theorem restricted_sector_finrank (d : ι → Nat) [∀ i, NeZero (d i)]
    (p : Finset ι → Prop) [DecidablePred p] :
    Module.finrank ℝ ↥(⨆ S : {S : Finset ι // p S}, correlationSector d S.1) =
      ∑ S : {S : Finset ι // p S}, ∏ i ∈ S.1, (d i ^ 2 - 1) := by
  have hInternal := correlation_sectors_isInternal d
  have hIndep : iSupIndep
      (fun S : {S : Finset ι // p S} => correlationSector d S.1) :=
    hInternal.submodule_iSupIndep.comp Subtype.val_injective
  have hinj : Function.Injective
      (DirectSum.coeLinearMap
        (fun S : {S : Finset ι // p S} => correlationSector d S.1)) :=
    hIndep.dfinsupp_lsum_injective
  rw [← DirectSum.range_coeLinearMap,
    LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]
  apply Finset.sum_congr rfl
  intro S _
  exact correlation_sector_finrank d S.1

private theorem high_order_finrank (d : ι → Nat) [∀ i, NeZero (d i)] (k : Nat) :
    Module.finrank ℝ (unobservedHighOrder d k) =
      ∑ S : {S : Finset ι // k < S.card}, ∏ i ∈ S.1, (d i ^ 2 - 1) := by
  exact restricted_sector_finrank d (fun S => k < S.card)

private theorem nonempty_sector_sum (d : ι → Nat) [∀ i, NeZero (d i)] :
    (∑ S : {S : Finset ι // S.Nonempty}, ∏ i ∈ S.1, (d i ^ 2 - 1)) =
      (∏ i, d i) ^ 2 - 1 := by
  let weight := fun S : Finset ι => ∏ i ∈ S, (d i ^ 2 - 1)
  have hall : (∑ S : Finset ι, weight S) = (∏ i, d i) ^ 2 := by
    calc
      (∑ S : Finset ι, weight S) = ∏ i, (1 + (d i ^ 2 - 1)) := by
        simpa [weight] using (Finset.prod_one_add (R := Nat)
          (s := Finset.univ) (f := fun i => d i ^ 2 - 1)).symm
      _ = ∏ i, d i ^ 2 := by
        apply Finset.prod_congr rfl
        intro i _
        exact Nat.add_sub_of_le (by
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (NeZero.ne (d i))))
      _ = (∏ i, d i) ^ 2 := by rw [Finset.prod_pow]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun S : Finset ι => S.Nonempty) weight
  have hempty :
      (∑ S : {S : Finset ι // ¬S.Nonempty}, weight S.1) = 1 := by
    letI : Unique {S : Finset ι // ¬S.Nonempty} :=
      { default := ⟨∅, by simp⟩
        uniq := fun S => Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp S.property) }
    have hdefault : (default : {S : Finset ι // ¬S.Nonempty}).1 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (default : {S : Finset ι // ¬S.Nonempty}).property
    simp [weight, hdefault]
  rw [hempty, hall] at hsplit
  calc
    (∑ S : {S : Finset ι // S.Nonempty}, ∏ i ∈ S.1, (d i ^ 2 - 1)) =
        ((∑ S : {S : Finset ι // S.Nonempty}, weight S.1) + 1) - 1 := by
      simp [weight]
    _ = (∏ i, d i) ^ 2 - 1 := by rw [hsplit]

private theorem nonempty_sectors_le_trace_zero
    (d : ι → Nat) [∀ i, NeZero (d i)] :
    (⨆ S : {S : Finset ι // S.Nonempty}, correlationSector d S.1) ≤
      traceZeroGlobal d := by
  refine iSup_le fun S => ?_
  rintro x ⟨z, ⟨y, rfl⟩, rfl⟩
  change scalarCoordinate d ((decompositionEquiv d).symm (DFinsupp.single S.1 y)) = 0
  simp [scalarCoordinate, S.property.ne_empty]

/-- The finite-family Hermitian tensor product is the internal direct sum of its subset-indexed
correlation sectors. Removing the empty scalar sector gives exactly the global trace-zero carrier;
each sector and every unobserved order tail have the expected dimensions. -/
theorem multifactor_correlation_sector_decomposition
    (d : ι → Nat) [∀ i, NeZero (d i)] :
    DirectSum.IsInternal (correlationSector d) ∧
      (⨆ S : {S : Finset ι // S.Nonempty}, correlationSector d S.1) =
        traceZeroGlobal d ∧
      Module.finrank ℝ (traceZeroGlobal d) = (∏ i, d i) ^ 2 - 1 ∧
      (∀ S, Module.finrank ℝ (correlationSector d S) =
        ∏ i ∈ S, (d i ^ 2 - 1)) ∧
      (∀ k, Module.finrank ℝ (unobservedHighOrder d k) =
        ∑ S : {S : Finset ι // k < S.card}, ∏ i ∈ S.1, (d i ^ 2 - 1)) := by
  have hInternal := correlation_sectors_isInternal d
  have hTraceDim := trace_zero_global_finrank d
  have hNonemptyDim :
      Module.finrank ℝ ↥(⨆ S : {S : Finset ι // S.Nonempty},
          correlationSector d S.1) =
        (∏ i, d i) ^ 2 - 1 := by
    exact (restricted_sector_finrank d (fun S => S.Nonempty)).trans
      (nonempty_sector_sum d)
  have hTrace :
      (⨆ S : {S : Finset ι // S.Nonempty}, correlationSector d S.1) =
        traceZeroGlobal d :=
    Submodule.eq_of_le_of_finrank_eq (nonempty_sectors_le_trace_zero d)
      (hNonemptyDim.trans hTraceDim.symm)
  exact ⟨hInternal, hTrace, hTraceDim, correlation_sector_finrank d,
    high_order_finrank d⟩

/-- Two qubits have three one-body directions per singleton sector and nine two-body
correlation directions. -/
example :
    Module.finrank ℝ (correlationSector (ι := Fin 2) (fun _ => 2) {0}) = 3 ∧
      Module.finrank ℝ (correlationSector (ι := Fin 2) (fun _ => 2) {0, 1}) = 9 := by
  constructor <;> rw [correlation_sector_finrank] <;> norm_num

#print axioms multifactor_correlation_sector_decomposition

end D5.S3.Quantum.MultifactorCorrelationSectorDecomposition
