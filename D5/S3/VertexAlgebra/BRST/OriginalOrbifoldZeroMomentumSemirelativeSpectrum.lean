/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldZeroMomentumSemirelativeSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldZeroMomentumSemirelativeSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native zero-momentum semirelative BRST spectrum. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldGhostDilaton
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The original-orbifold zero-momentum semirelative spectrum

The two relative coordinates come from the native sum ghost and antighost
zero modes, after cutting to energy zero and momentum zero on each factor.
The differential sends the second coordinate to the first via the sum of
the two chiral zero-mode connections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeSpectrum

noncomputable section

open OriginalOrbifoldCriticalMatter (Orbifold Hyperbolic Matter State)
open OriginalOrbifoldClosedSemirelative (ClosedState bMinus closedQ closedQ_square)
open OriginalOrbifoldGhostDilaton
open OriginalOrbifoldRelativeNull (ShellIndex bottom middle top)
open OriginalOrbifoldChiralZeroModeConnection (zeroBasis)
open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries Cohomology boundaryMap)

open private relativeInclusion relativeInclusion_shell relativeRetraction retract_include
  include_tmul relative_Q_zero bMinus_cPlus jointProjection_cPlus bPlus_cPlus from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldGhostDilaton
open private b0 from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
open private raise_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldChiralZeroModeConnection

local instance : AddCommGroup Matter := TensorProduct.addCommGroup (M := Orbifold) (N := Hyperbolic)
local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)
local instance : AddCommGroup ClosedState := TensorProduct.addCommGroup (M := State)
local instance : AddCommGroup ZeroRelativeTensor :=
  TensorProduct.addCommGroup (M := ↥ZeroChiralShell)

local notation "Rel" => ZeroRelativeTensor
local notation "T" => zeroShellConnection
local notation "D" => zeroShellDifferential

private theorem bPlus_relative (u : Rel) : bPlus (relativeInclusion u) = 0 := by
  have h : bPlus.comp relativeInclusion = 0 := by
    apply TensorProduct.ext'
    intro x y
    have hx : b0 (x : OriginalOrbifoldCriticalMatter.State) = 0 := x.property.1.2
    have hy : b0 (y : OriginalOrbifoldCriticalMatter.State) = 0 := y.property.1.2
    simp only [LinearMap.comp_apply, include_tmul, bPlus, LinearMap.add_apply,
      LinearMap.rTensor_tmul, TensorProduct.map_tmul, hx, hy,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h u

private theorem cPlus_preserves_shell (z : ClosedState) (hz : z ∈ zeroMomentumShell) :
    cPlus z ∈ zeroMomentumShell := by
  obtain ⟨hb, hp⟩ := (mem_zeroMomentumShell z).mp hz
  apply (mem_zeroMomentumShell _).mpr
  exact ⟨by simpa only [Module.End.mul_apply, LinearMap.add_apply, hb, map_zero, add_zero,
      LinearMap.zero_apply] using LinearMap.congr_fun bMinus_cPlus z,
    by simpa only [Module.End.mul_apply, hp] using LinearMap.congr_fun jointProjection_cPlus z⟩

private def assemble : Rel × Rel →ₗ[ℂ] zeroMomentumShell :=
  (relativeInclusion.comp (LinearMap.fst ℂ Rel Rel) +
    (cPlus.comp relativeInclusion).comp (LinearMap.snd ℂ Rel Rel)).codRestrict _
    (fun p => zeroMomentumShell.add_mem (relativeInclusion_shell p.1)
      (cPlus_preserves_shell _ (relativeInclusion_shell p.2)))

private theorem bPlus_assemble (u v : Rel) :
    bPlus (assemble (u, v) : ClosedState) = relativeInclusion v := by
  change bPlus (relativeInclusion u + cPlus (relativeInclusion v)) = _
  rw [map_add, bPlus_relative, zero_add]
  simpa only [Module.End.mul_apply, LinearMap.add_apply, bPlus_relative,
    map_zero, add_zero, Module.End.one_apply] using
    LinearMap.congr_fun bPlus_cPlus (relativeInclusion v)

private theorem assemble_bijective : Function.Bijective assemble := by
  constructor
  · rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have he := congrArg (fun z : zeroMomentumShell => bPlus (z : ClosedState)) h
    rw [bPlus_assemble, bPlus_assemble] at he
    have hv : v = v' := by
      simpa only [retract_include] using congrArg relativeRetraction he
    have hu := congrArg (fun z : zeroMomentumShell => (z : ClosedState)) h
    change relativeInclusion u + cPlus (relativeInclusion v) =
      relativeInclusion u' + cPlus (relativeInclusion v') at hu
    rw [hv] at hu
    exact Prod.ext
      (by simpa only [retract_include] using
        congrArg relativeRetraction (add_right_cancel hu)) hv
  · intro z
    obtain ⟨u, v, hz⟩ := zeroShell_decompose z
    exact ⟨(u, v), Subtype.ext hz.symm⟩

set_option maxHeartbeats 800000 in
-- Elaborate the equivalence through the native tensor-state subtypes.
/-- Native coordinates, with the sum ghost applied to the second relative state. -/
def zeroShellCoordinates : (Rel × Rel) ≃ₗ[ℂ] zeroMomentumShell :=
  LinearEquiv.ofBijective assemble assemble_bijective

theorem zeroShellCoordinates_apply (u v : Rel) :
    (zeroShellCoordinates (u, v) : ClosedState) =
      relativeInclusion u + cPlus (relativeInclusion v) := rfl

/-- The native differential has only the entry from the second to the first coordinate. -/
theorem zeroShellCoordinates_differential (u v : Rel) :
    D (zeroShellCoordinates (u, v)) = zeroShellCoordinates (T v, 0) := by
  apply Subtype.ext
  change closedQ (relativeInclusion u + cPlus (relativeInclusion v)) =
    relativeInclusion (T v) + cPlus (relativeInclusion 0)
  rw [map_add, relative_Q_zero, zero_add, map_zero, map_zero, add_zero,
    ← sumConnection_on_relative]
  simp only [sumConnection, LinearMap.add_apply, Module.End.mul_apply,
    relative_Q_zero, map_zero, add_zero]

theorem zeroShellDifferential_square : D * D = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun closedQ_square (z : ClosedState)

private abbrev tensorBasis : Module.Basis (ShellIndex × ShellIndex) ℂ Rel :=
  zeroBasis.tensorProduct zeroBasis

private theorem connection_basis (i j : ShellIndex) :
    T (tensorBasis (i, j)) =
      (if i = bottom then tensorBasis (top, j) else 0) +
      (if j = bottom then tensorBasis (i, top) else 0) := by
  simp only [zeroShellConnection, LinearMap.add_apply, Module.Basis.tensorProduct_apply',
    TensorProduct.map_tmul, LinearMap.id_apply, raise_basis]
  split <;> split <;> simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero]

private def imageGenerators : Fin 6 → Rel :=
  ![tensorBasis (top, bottom) + tensorBasis (bottom, top), tensorBasis (top, top),
    tensorBasis (top, middle 0), tensorBasis (top, middle 1),
    tensorBasis (middle 0, top), tensorBasis (middle 1, top)]

private def pivot : Fin 6 → ShellIndex × ShellIndex :=
  ![(top, bottom), (top, top), (top, middle 0), (top, middle 1), (middle 0, top), (middle 1, top)]

private theorem coord_tensorBasis (i j : ShellIndex × ShellIndex) :
    tensorBasis.coord i (tensorBasis j) = if j = i then 1 else 0 := by
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

private theorem pivot_generator (i j : Fin 6) :
    tensorBasis.coord (pivot i) (imageGenerators j) = if j = i then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [pivot, imageGenerators, Matrix.cons_val_zero', Matrix.cons_val_succ',
      map_add, coord_tensorBasis] <;>
    simp [bottom, middle, top]

set_option maxHeartbeats 800000 in
-- Elaborate through the native tensor-state subtypes.
private theorem imageGenerators_independent : LinearIndependent ℂ imageGenerators := by
  apply (Fintype.linearIndependent_iff (R := ℂ) (v := imageGenerators)).mpr
  intro c hc i
  have h := congrArg (tensorBasis.coord (pivot i)) hc
  simp only [map_sum, map_smul, map_zero, pivot_generator, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

private def preimageIndex : Fin 6 → ShellIndex × ShellIndex :=
  ![(bottom, bottom), (bottom, top), (bottom, middle 0), (bottom, middle 1),
    (middle 0, bottom), (middle 1, bottom)]

private theorem connection_preimage (i : Fin 6) :
    T (tensorBasis (preimageIndex i)) = imageGenerators i := by
  fin_cases i <;>
    simp only [preimageIndex, imageGenerators, Matrix.cons_val_zero', Matrix.cons_val_succ',
      connection_basis] <;>
    simp [bottom, middle, top]

set_option maxHeartbeats 800000 in
-- Compare the sixteen native tensor-basis images with the six generators.
private theorem connection_range :
    LinearMap.range T = Submodule.span ℂ (Set.range imageGenerators) := by
  have hg (k : Fin 6) : imageGenerators k ∈ Submodule.span ℂ (Set.range imageGenerators) :=
    Submodule.subset_span ⟨k, rfl⟩
  apply le_antisymm
  · rw [← Submodule.map_top, ← tensorBasis.span_eq, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    fin_cases i <;> fin_cases j <;> rw [connection_basis] <;>
      simp [bottom, top]
    · simpa [imageGenerators, bottom, middle, top] using hg 0
    · simpa [imageGenerators, bottom, middle, top] using hg 2
    · simpa [imageGenerators, bottom, middle, top] using hg 3
    · simpa [imageGenerators, bottom, middle, top] using hg 1
    · simpa [imageGenerators, bottom, middle, top] using hg 4
    · simpa [imageGenerators, bottom, middle, top] using hg 5
    · simpa [imageGenerators, bottom, middle, top] using hg 1
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨tensorBasis (preimageIndex i), connection_preimage i⟩

theorem zeroShellConnection_rank : Module.finrank ℂ (LinearMap.range T) = 6 := by
  rw [connection_range, finrank_span_eq_card imageGenerators_independent]
  rfl

/-- The connection cokernel on the double-relative zero shell. -/
abbrev ZeroShellCokernel := Rel ⧸ LinearMap.range T

/-- Cohomology of the actual restricted closed BRST differential. -/
abbrev ZeroShellCohomology :=
  Cohomology (R := ℂ) (M := ↥zeroMomentumShell) D zeroShellDifferential_square

local notation "S" => zeroShellCoordinates
local notation "B" => Boundaries D zeroShellDifferential_square

private theorem coordinates_cycle_iff (u v : Rel) : D (S (u, v)) = 0 ↔ T v = 0 := by
  rw [zeroShellCoordinates_differential, ← (S).map_zero, (S).injective.eq_iff]
  exact ⟨fun h => congrArg Prod.fst h, fun h => Prod.ext h rfl⟩

/-- Every boundary has second coordinate zero, and its first coordinate
lies in the range of the native sum connection. -/
theorem zeroShellCoordinates_boundary_iff (u v : Rel) :
    S (u, v) ∈ LinearMap.range D ↔ u ∈ LinearMap.range T ∧ v = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨⟨a, w⟩, rfl⟩ := (S).surjective z
    rw [zeroShellCoordinates_differential] at hz
    have hp := (S).injective hz
    exact ⟨⟨w, congrArg Prod.fst hp⟩, (congrArg Prod.snd hp).symm⟩
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact ⟨S (0, w), (zeroShellCoordinates_differential 0 w).trans
      (congrArg S (Prod.ext hw rfl))⟩

private def assembleCycle : Rel × LinearMap.ker T →ₗ[ℂ] LinearMap.ker D :=
  ((S).toLinearMap.comp (LinearMap.id.prodMap (LinearMap.ker T).subtype)).codRestrict _
    (fun p => (coordinates_cycle_iff p.1 (p.2 : Rel)).mpr p.2.property)

set_option maxHeartbeats 800000 in
-- Elaborate through the native tensor-state subtypes.
private def cycleCoordinates : (Rel × LinearMap.ker T) ≃ₗ[ℂ] LinearMap.ker D :=
  LinearEquiv.ofBijective assembleCycle ⟨by
    rintro ⟨u, v⟩ ⟨u', v'⟩ h
    have hp : (u, (v : Rel)) = (u', (v' : Rel)) :=
      (S).injective (congrArg (fun x : LinearMap.ker D => (x : zeroMomentumShell)) h)
    exact Prod.ext (congrArg (fun p : Rel × Rel => p.1) hp)
      (Subtype.ext (congrArg (fun p : Rel × Rel => p.2) hp)),
    by
      intro z
      obtain ⟨⟨u, v⟩, hz⟩ := (S).surjective (z : zeroMomentumShell)
      have hv : T v = 0 :=
        (coordinates_cycle_iff u v).mp (hz.symm ▸ z.property)
      exact ⟨(u, ⟨v, hv⟩), Subtype.ext hz⟩⟩

private def quotientCoordinates :
    LinearMap.ker D →ₗ[ℂ] ZeroShellCokernel × LinearMap.ker T :=
  ((LinearMap.range T).mkQ.prodMap LinearMap.id).comp cycleCoordinates.symm.toLinearMap

private theorem quotientCoordinates_apply (u : Rel) (v : LinearMap.ker T) :
    quotientCoordinates (cycleCoordinates (u, v)) = ((LinearMap.range T).mkQ u, v) := by
  simp only [quotientCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_apply]

private theorem quotientCoordinates_surjective : Function.Surjective quotientCoordinates := by
  rintro ⟨q, v⟩
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range T) q
  exact ⟨cycleCoordinates (u, v), quotientCoordinates_apply u v⟩

set_option maxHeartbeats 800000 in
-- Elaborate through the native tensor-state subtypes.
private theorem boundaries_eq_ker_quotientCoordinates : B = LinearMap.ker quotientCoordinates := by
  ext z
  obtain ⟨⟨u, v⟩, rfl⟩ := cycleCoordinates.surjective z
  change (∃ w, boundaryMap D zeroShellDifferential_square w = cycleCoordinates (u, v)) ↔
    quotientCoordinates (cycleCoordinates (u, v)) = 0
  rw [quotientCoordinates_apply]
  have hboundary :
      (∃ w, boundaryMap D zeroShellDifferential_square w = cycleCoordinates (u, v)) ↔
        S (u, (v : Rel)) ∈ LinearMap.range D := by
    exact ⟨fun ⟨w, hw⟩ => ⟨w, congrArg Subtype.val hw⟩,
      fun ⟨w, hw⟩ => ⟨w, Subtype.ext hw⟩⟩
  rw [hboundary, zeroShellCoordinates_boundary_iff]
  constructor
  · rintro ⟨hu, hv⟩
    exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr hu) (Subtype.ext hv)
  · intro h
    exact ⟨(Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.fst h),
      congrArg Subtype.val (congrArg Prod.snd h)⟩

set_option maxHeartbeats 800000 in
-- Elaborate the first isomorphism theorem for the native cycle quotient.
/-- A cycle with coordinates `(u,v)` represents `([u],v)` in the product
of the connection cokernel and the connection kernel. -/
def zeroShellCohomologyEquiv :
    ZeroShellCohomology ≃ₗ[ℂ] ZeroShellCokernel × LinearMap.ker T :=
  (Submodule.quotEquivOfEq _ _ boundaries_eq_ker_quotientCoordinates).trans
    (quotientCoordinates.quotKerEquivOfSurjective quotientCoordinates_surjective)

set_option maxHeartbeats 800000 in
-- Reduce the quotient maps on representatives of the native cycle space.
theorem zeroShellCohomologyEquiv_class (u v : Rel) (hv : T v = 0) :
    zeroShellCohomologyEquiv
        ((B).mkQ ⟨S (u, v), (coordinates_cycle_iff u v).mpr hv⟩) =
      ((LinearMap.range T).mkQ u, ⟨v, hv⟩) := by
  change zeroShellCohomologyEquiv ((B).mkQ (cycleCoordinates (u, ⟨v, hv⟩))) = _
  exact quotientCoordinates_apply u ⟨v, hv⟩

local instance : Module.Finite ℂ Rel := Module.Finite.of_basis tensorBasis

private theorem relativeTensor_finrank : Module.finrank ℂ Rel = 16 := by
  rw [Module.finrank_eq_card_basis tensorBasis]
  simp [Fintype.card_prod, Fintype.card_sum]

theorem zeroShellConnection_ker_finrank : Module.finrank ℂ (LinearMap.ker T) = 10 := by
  have h := LinearMap.finrank_range_add_finrank_ker T
  rw [zeroShellConnection_rank, relativeTensor_finrank] at h
  omega

theorem zeroShellConnection_coker_finrank : Module.finrank ℂ ZeroShellCokernel = 10 := by
  have h : Module.finrank ℂ ZeroShellCokernel + 6 = 16 := by
    rw [← zeroShellConnection_rank, ← relativeTensor_finrank]
    exact Submodule.finrank_quotient_add_finrank (LinearMap.range T)
  omega

set_option synthInstance.maxHeartbeats 80000 in
-- Infer the finite-dimensional vector-space instances for the two subquotients.
theorem zeroShellCohomology_finrank : Module.finrank ℂ ZeroShellCohomology = 20 := by
  rw [zeroShellCohomologyEquiv.finrank_eq, Module.finrank_prod,
    zeroShellConnection_coker_finrank, zeroShellConnection_ker_finrank]

#print axioms zeroShellCoordinates_boundary_iff
#print axioms zeroShellCohomologyEquiv
#print axioms zeroShellCohomologyEquiv_class
#print axioms zeroShellConnection_ker_finrank
#print axioms zeroShellConnection_coker_finrank
#print axioms zeroShellCohomology_finrank

#print axioms zeroShellCoordinates
#print axioms zeroShellCoordinates_apply
#print axioms zeroShellCoordinates_differential
#print axioms zeroShellDifferential_square
#print axioms zeroShellConnection_rank

end

end D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeSpectrum
