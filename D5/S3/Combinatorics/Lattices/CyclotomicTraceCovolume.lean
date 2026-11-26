/- GID: D5/S3/Combinatorics/Lattices/CyclotomicTraceCovolume
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/CyclotomicTraceCovolume
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace covolumes and exact HN semistability of cyclotomic fractional ideals. -/

import D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.InnerProductSpace.ProdL2
import D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
import D5.S3.Combinatorics.Lattices.EuclideanCommonLattice

/-! Fractional ideals with the trace-sum Euclidean metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Real places are unchanged; each complex coordinate is multiplied by square root two. -/
def traceScale : mixedSpace K ≃L[ℝ] mixedSpace K :=
  ((LinearEquiv.refl ℝ _).prodCongr
    (LinearEquiv.smulOfUnit (M := {w : InfinitePlace K // IsComplex w} → ℂ)
      (Units.mk0 (Real.sqrt 2) (by positivity)))).toContinuousLinearEquiv

/-- The Euclidean realization in which conjugate complex embeddings are both counted. -/
def traceVector (x : mixedSpace K) : euclidean.mixedSpace K :=
  (euclidean.toMixed K).symm (traceScale K x)

/-- The trace-sum lattice of a nonzero fractional ideal. -/
def traceIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I)
    (((euclidean.toMixed K).trans (traceScale K).symm).toLinearMap)

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (traceIdealLattice K I) := by
  unfold traceIdealLattice
  infer_instance

private theorem covolume_comap_det {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (f : E ≃L[ℝ] E) :
    ZLattice.covolume (ZLattice.comap ℝ L f.toLinearMap) =
      |LinearMap.det f.symm.toLinearMap| * ZLattice.covolume L := by
  let b := Free.chooseBasis ℤ L
  let b₀ := b.ofZLatticeBasis ℝ L
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _
      (b.ofZLatticeComap ℝ L f.toLinearEquiv) b₀,
    ZLattice.covolume_eq_det_mul_measureReal L volume b b₀]
  have hv : ((↑) ∘ (b.ofZLatticeComap ℝ L f.toLinearEquiv)) =
      f.symm ∘ ((↑) ∘ b) := by
    ext i
    exact b.ofZLatticeComap_apply ℝ L f.toLinearEquiv i
  rw [hv]
  change |b₀.det (f.symm.toLinearMap ∘ ((↑) ∘ b))| * _ = _
  rw [b₀.det_comp, abs_mul]
  ring

private theorem traceScale_det :
    LinearMap.det (traceScale K).toLinearMap = (2 : ℝ) ^ nrComplexPlaces K := by
  change LinearMap.det
    (LinearMap.prodMap (LinearMap.id :
      ({w : InfinitePlace K // IsReal w} → ℝ) →ₗ[ℝ] _)
      ((Real.sqrt 2) • (LinearMap.id :
        ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℝ] _))) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_smul,
    LinearMap.det_id, mul_one]
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem traceVector_norm (x : mixedSpace K) :
    ‖traceVector K x‖ ^ 2 =
      (∑ w : {w : InfinitePlace K // IsReal w}, (x.1 w) ^ 2) +
      2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖WithLp.toLp 2 x.1‖ ^ 2 +
    ‖WithLp.toLp 2 ((Real.sqrt 2) • x.2)‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Pi.smul_apply, _root_.norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Finset.mul_sum]

private theorem traceIdeal_covolume (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      Real.sqrt |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ) := by
  let L := ZLattice.comap ℝ (idealLattice K I) (traceScale K).symm.toLinearMap
  have hL : ZLattice.covolume L =
      |LinearMap.det (traceScale K).toLinearMap| * ZLattice.covolume (idealLattice K I) :=
    covolume_comap_det (idealLattice K I) (traceScale K).symm
  have he : traceIdealLattice K I =
      ZLattice.comap ℝ L (euclidean.toMixed K).toLinearMap := rfl
  rw [he, ZLattice.covolume_comap L volume volume
    (euclidean.volumePreserving_toMixed K), hL, traceScale_det,
    abs_of_nonneg (by positivity), covolume_idealLattice]
  have hpow : (2 : ℝ) ^ nrComplexPlaces K *
      (2⁻¹ : ℝ) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((2 : ℝ) ^ nrComplexPlaces K * (2⁻¹ : ℝ) ^ nrComplexPlaces K) *
        Real.sqrt |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ) := by ring
    _ = _ := by rw [hpow, one_mul]

/-- The standard Hermitian degree of a fractional ideal. -/
def idealDegree (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  -Real.log (FractionalIdeal.absNorm I.val : ℝ)

/-- The normalized discriminant translation of slopes. -/
def discriminantShift : ℝ := Real.log |(discr K : ℝ)| / (2 * finrank ℚ K)

private theorem traceIdeal_slope (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    -Real.log (ZLattice.covolume (traceIdealLattice K I)) / finrank ℚ K =
      idealDegree K I / finrank ℚ K - discriminantShift K := by
  have hI : (FractionalIdeal.absNorm I.val : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero, ne_eq, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero I
  rw [traceIdeal_covolume, Real.log_mul (Real.sqrt_ne_zero'.mpr (abs_pos.mpr
    (by exact_mod_cast discr_ne_zero K))) hI, Real.log_sqrt (abs_nonneg _)]
  unfold idealDegree discriminantShift
  ring

private theorem gram_covolume_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    EuclideanHarderNarasimhan.covolume L = ZLattice.covolume L := by
  let b := Free.chooseBasis ℤ L
  let bR := b.ofZLatticeBasis ℝ L
  let o := (stdOrthonormalBasis ℝ E).reindex
    ((stdOrthonormalBasis ℝ E).toBasis.indexEquiv bR)
  have hFD : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_def,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    simpa only [OrthonormalBasis.coe_toBasis, ENNReal.toReal_one] using
      congrArg ENNReal.toReal o.volume_parallelepiped
  rw [EuclideanHarderNarasimhan.covolume_eq_gram L b,
    ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis, hFD, mul_one,
    Matrix.gram_eq_conjTranspose_mul o]
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial]
  rw [← pow_two, Real.sqrt_sq_eq_abs, Basis.det_apply]
  congr 2

/-- The actual trace-sum metric and its exact fractional-ideal covolume. -/
theorem trace_ideal_formula (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (∀ x : mixedSpace K, ‖traceVector K x‖ ^ 2 =
      (∑ w : {w : InfinitePlace K // IsReal w}, (x.1 w) ^ 2) +
      2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) ∧
    ZLattice.covolume (traceIdealLattice K I) =
      Real.sqrt |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ) ∧
    -Real.log (ZLattice.covolume (traceIdealLattice K I)) / finrank ℚ K =
      idealDegree K I / finrank ℚ K - discriminantShift K ∧
    EuclideanHarderNarasimhan.covolume (traceIdealLattice K I) =
      Real.sqrt |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ) :=
  ⟨traceVector_norm K, traceIdeal_covolume K I, traceIdeal_slope K I,
    (gram_covolume_eq (traceIdealLattice K I)).trans (traceIdeal_covolume K I)⟩

section CyclotomicIdeal

open EuclideanSublattices EuclideanHarderNarasimhan EuclideanHNEquivariance
open HarderNarasimhan CyclotomicHNRestriction

variable {A E : Type*} [CommRing A] [IsDomain A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Module A E] [Algebra.IsAlgebraic ℤ A]
variable [FiniteDimensional ℝ E]

private theorem bottom_val (L : Submodule ℤ E) :
    (⊥ : Sublattice L).val = ⊥ := by
  apply Submodule.map_injective_of_injective L.subtype_injective
  change integral L ⊥ = (⊥ : Submodule ℤ L).map L.subtype
  rw [EuclideanCommonLattice.bot_carrier, Submodule.map_bot]

omit [FiniteDimensional ℝ E] in
private theorem top_val (L : Submodule ℤ E) :
    (⊤ : Sublattice L).val = ⊤ := rfl

omit [IsDomain A] [Algebra.IsAlgebraic ℤ A] in
private theorem saturated_eq_top (L : Submodule ℤ E) (F : Sublattice L)
    (hF : ⊥ < F)
    (hP : ∃ P : Submodule A E, P.restrictScalars ℤ = integral L F ∧
      ∀ (a : A), a ≠ 0 → ∀ x ∈ L, a • x ∈ P → x ∈ P)
    (hrank : ∀ x ∈ L, ∀ y ∈ L, y ≠ 0 →
      ∃ (a b : A), a ≠ 0 ∧ a • x = b • y) : F = ⊤ := by
  obtain ⟨P, heq, hsat⟩ := hP
  have hv : F.val ≠ ⊥ := by
    intro hv
    exact hF.ne' (Subtype.ext (hv.trans (bottom_val L).symm))
  obtain ⟨y, hy, hy0⟩ := F.val.ne_bot_iff.mp hv
  have hyP : (y : E) ∈ P := by
    change (y : E) ∈ P.restrictScalars ℤ
    rw [heq]
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  have hyE : (y : E) ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext h)
  apply top_unique
  change (⊤ : Sublattice L).val ≤ F.val
  intro x hx
  obtain ⟨a, b, ha, hab⟩ := hrank x x.property y y.property hyE
  have hxP : (x : E) ∈ P :=
    hsat a ha x x.property (by rw [hab]; exact P.smul_mem b hyP)
  have hxF : (x : E) ∈ integral L F := by
    rw [← heq]
    exact hxP
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp hxF
  exact (L.subtype_injective hux) ▸ hu

variable (z : A) (hz : Algebra.adjoin ℤ ({z} : Set A) = ⊤)
variable (L : Submodule ℤ E) [DiscreteTopology L]
variable (T : E ≃ₗᵢ[ℝ] E)
variable (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
variable (hact : ∀ x : E, T x = z • x)

include hz hT hact in
private theorem rank_one_semistable
    (hne : (⊥ : Sublattice L) ≠ ⊤)
    (hrank : ∀ x ∈ L, ∀ y ∈ L, y ≠ 0 →
      ∃ (a b : A), a ≠ 0 ∧ a • x = b • y) :
    (slopeData L).Semistable ⊥ ⊤ ∧
      ∀ l : List (Sublattice L), (slopeData L).Filtration ⊥ ⊤ l ↔ l = [⊤] := by
  obtain ⟨l, hl, hu⟩ := ((euclidean_hn L ⊥ ⊤).2.1).mpr bot_le
  cases l with
  | nil =>
    generalize ha : (⊥ : Sublattice L) = a at hl hne
    generalize hb : (⊤ : Sublattice L) = b at hl hne
    cases hl
    exact (hne rfl).elim
  | cons F l =>
    have hsat := (hn_saturated z hz L T hT hact (F :: l) hl).1 F
      (List.mem_cons_self ..)
    have hfirst : (slopeData L).Semistable ⊥ F ∧ F ≤ ⊤ ∧
        (slopeData L).Filtration F ⊤ l := by
      generalize ha : (⊥ : Sublattice L) = a at hl ⊢
      generalize hb : (⊤ : Sublattice L) = b at hl ⊢
      cases hl with | cons hs hb ht _ => exact ⟨hs, hb, ht⟩
    have hF : ⊥ < F := hfirst.1.1
    have htop := saturated_eq_top L F hF hsat hrank
    subst F
    have hnil : l = [] := by
      have htail := hfirst.2.2
      cases l with
      | nil => rfl
      | cons F l =>
        generalize hb : (⊤ : Sublattice L) = b at htail
        cases htail with
        | cons hs hb _ _ => exact (not_lt_of_ge hb hs.1).elim
    subst l
    have hsem : (slopeData L).Semistable ⊥ ⊤ := hfirst.1
    refine ⟨hsem, fun l => ?_⟩
    constructor
    · intro hl'
      exact (hu l hl').trans (hu [⊤] hl).symm
    · rintro rfl
      exact hl

section NumberField

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors


private abbrev mixedOrderModule : Module (𝓞 K) (mixedSpace K) :=
  ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toModule

local instance : Module (𝓞 K) (mixedSpace K) := mixedOrderModule K

local instance : Module (𝓞 K) (euclidean.mixedSpace K) :=
  (euclidean.toMixed K).toLinearEquiv.toAddEquiv.module (𝓞 K)

private def orderLinear (a : 𝓞 K) : euclidean.mixedSpace K →ₗ[ℝ]
    euclidean.mixedSpace K where
  toFun := fun x => a • x
  map_add' := smul_add a
  map_smul' := by
    intro r x
    apply (euclidean.toMixed K).injective
    change mixedEmbedding K (a : K) * (r • euclidean.toMixed K x) =
      r • (mixedEmbedding K (a : K) * euclidean.toMixed K x)
    exact mul_smul_comm _ _ _

private def traceMap : K →+ euclidean.mixedSpace K where
  toFun := fun x => traceVector K (mixedEmbedding K x)
  map_zero' := by simp [traceVector]
  map_add' := by intro x y; simp [traceVector]

private theorem traceScale_mul (a x : mixedSpace K) :
    traceScale K (a * x) = a * traceScale K x := by
  apply Prod.ext
  · rfl
  · funext w
    change (Real.sqrt 2) • (a.2 w * x.2 w) = a.2 w * ((Real.sqrt 2) • x.2 w)
    exact (mul_smul_comm _ _ _).symm

private theorem traceMap_smul (a : 𝓞 K) (x : K) :
    traceMap K ((a : K) * x) = a • traceMap K x := by
  apply (euclidean.toMixed K).injective
  change traceScale K (mixedEmbedding K ((a : K) * x)) =
    mixedEmbedding K (a : K) * traceScale K (mixedEmbedding K x)
  rw [map_mul, traceScale_mul]

private theorem mem_traceIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : euclidean.mixedSpace K) :
    x ∈ traceIdealLattice K I ↔ ∃ y ∈ (I : Set K), traceMap K y = x := by
  change (traceScale K).symm (euclidean.toMixed K x) ∈ idealLattice K I ↔ _
  rw [mem_idealLattice]
  constructor
  · rintro ⟨y, hy, hey⟩
    refine ⟨y, hy, ?_⟩
    apply (euclidean.toMixed K).injective
    change traceScale K (mixedEmbedding K y) = euclidean.toMixed K x
    rw [hey]
    exact (traceScale K).apply_symm_apply _
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    change mixedEmbedding K y =
      (traceScale K).symm ((euclidean.toMixed K)
        ((euclidean.toMixed K).symm (traceScale K (mixedEmbedding K y))))
    simp

private theorem traceIdeal_stable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : 𝓞 K) (x : euclidean.mixedSpace K) (hx : x ∈ traceIdealLattice K I) :
    a • x ∈ traceIdealLattice K I := by
  obtain ⟨y, hy, rfl⟩ := (mem_traceIdeal K I x).mp hx
  apply (mem_traceIdeal K I _).mpr
  refine ⟨(a : K) * y, ?_, traceMap_smul K a y⟩
  exact (I : Submodule (𝓞 K) K).smul_mem a hy

private theorem euclidean_norm_sq (x : euclidean.mixedSpace K) :
    ‖x‖ ^ 2 =
      (∑ w : {w : InfinitePlace K // IsReal w}, ‖(euclidean.toMixed K x).1 w‖ ^ 2) +
      ∑ w : {w : InfinitePlace K // IsComplex w}, ‖(euclidean.toMixed K x).2 w‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  rfl

private theorem orderLinear_norm {n : ℕ} [NeZero n] (z : 𝓞 K)
    (hz : z ^ n = 1) (x : euclidean.mixedSpace K) :
    ‖orderLinear K z x‖ = ‖x‖ := by
  have hnorm {B : Type} [NormedField B]
      (f : 𝓞 K →+* B) : ‖f z‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)).mp
    rw [← norm_pow, ← map_pow, hz, map_one, norm_one]
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  rw [euclidean_norm_sq, euclidean_norm_sq]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro w hw
    change ‖((embedding_of_isReal w.property).comp (algebraMap (𝓞 K) K)) z *
      (euclidean.toMixed K x).1 w‖ ^ 2 = _
    rw [norm_mul, hnorm ((embedding_of_isReal w.property).comp (algebraMap (𝓞 K) K)),
      one_mul]
  · apply Finset.sum_congr rfl
    intro w hw
    change ‖(w.val.embedding.comp (algebraMap (𝓞 K) K)) z *
      (euclidean.toMixed K x).2 w‖ ^ 2 = _
    rw [norm_mul, hnorm (w.val.embedding.comp (algebraMap (𝓞 K) K)), one_mul]

private def rootIsometry {n : ℕ} [NeZero n] (z : 𝓞 K) (hz : z ^ n = 1) :
    euclidean.mixedSpace K ≃ₗᵢ[ℝ] euclidean.mixedSpace K :=
  let f : euclidean.mixedSpace K →ₗᵢ[ℝ] euclidean.mixedSpace K :=
    { orderLinear K z with norm_map' := orderLinear_norm K z hz }
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

private theorem root_preserves {n : ℕ} [NeZero n]
    (z : 𝓞 K) (hz : IsPrimitiveRoot z n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceIdealLattice K I).map
      ((rootIsometry K z hz.pow_eq_one).toLinearMap.restrictScalars ℤ) =
      traceIdealLattice K I := by
  obtain ⟨u, hu⟩ := hz.isUnit (NeZero.ne n)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact traceIdeal_stable K I z x hx
  · intro x hx
    apply Submodule.mem_map.mpr
    refine ⟨(u⁻¹ : (𝓞 K)ˣ) • x, traceIdeal_stable K I (↑u⁻¹) x hx, ?_⟩
    change z • ((↑u⁻¹ : 𝓞 K) • x) = x
    rw [← hu, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

private theorem trace_rank_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : euclidean.mixedSpace K) (hx : x ∈ traceIdealLattice K I)
    (y : euclidean.mixedSpace K) (hy : y ∈ traceIdealLattice K I) (hy0 : y ≠ 0) :
    ∃ (a b : 𝓞 K), a ≠ 0 ∧ a • x = b • y := by
  obtain ⟨v, hv, rfl⟩ := (mem_traceIdeal K I x).mp hx
  obtain ⟨w, hw, rfl⟩ := (mem_traceIdeal K I y).mp hy
  have hw0 : w ≠ 0 := by intro h; exact hy0 (by simp [h])
  obtain ⟨b, a, ha, hba⟩ := IsFractionRing.div_surjective (𝓞 K) (v / w)
  have ha0 : a ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨a, ha⟩
  have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha0
  have heq : (a : K) * v = (b : K) * w := by
    apply (div_eq_div_iff haK hw0).mp at hba
    linear_combination -hba
  refine ⟨a, b, ha0, ?_⟩
  rw [← traceMap_smul, ← traceMap_smul, heq]

private theorem trace_nontrivial (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (⊥ : Sublattice (traceIdealLattice K I)) ≠ ⊤ := by
  intro heq
  have heq' := congrArg Subtype.val heq
  rw [bottom_val, top_val] at heq'
  have hzero : ∀ x : traceIdealLattice K I, x = 0 := by
    intro x
    have hx : x ∈ (⊥ : Submodule ℤ (traceIdealLattice K I)) := by
      rw [heq']
      trivial
    exact hx
  letI : Subsingleton (traceIdealLattice K I) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hr : finrank ℤ (traceIdealLattice K I) = 0 := Module.finrank_zero_of_subsingleton
  rw [ZLattice.rank ℝ, euclidean.finrank] at hr
  exact (Module.finrank_pos : 0 < finrank ℚ K).ne' hr

/-- In a full cyclotomic field, a fractional ideal with its trace-sum metric is
semistable over the integers. Its HN chain is a single factor and its normalized
average slope is the ideal's Arakelov slope minus the exact discriminant shift. -/
theorem cyclotomic_ideal_hn {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    let L := traceIdealLattice K I
    (slopeData L).Semistable ⊥ ⊤ ∧
      (∀ l : List (Sublattice L), (slopeData L).Filtration ⊥ ⊤ l ↔ l = [⊤]) ∧
      -Real.log (EuclideanHarderNarasimhan.covolume L) / finrank ℤ L =
        idealDegree K I / finrank ℚ K - discriminantShift K := by
  dsimp only
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  let z := hζ.toInteger
  let T := rootIsometry K z hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hs := rank_one_semistable z (IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ)
    (traceIdealLattice K I) T (root_preserves K z hζ.toInteger_isPrimitiveRoot I)
    (fun _ => rfl) (trace_nontrivial K I) (trace_rank_one K I)
  refine ⟨hs.1, hs.2, ?_⟩
  rw [ZLattice.rank ℝ, euclidean.finrank, gram_covolume_eq]
  exact (trace_ideal_formula K I).2.2.1

end NumberField

end CyclotomicIdeal

end D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume
