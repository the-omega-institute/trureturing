/- GID: D5/S3/HilbertOperators/CommonAnchorOrderReflection
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/CommonAnchorOrderReflection
   mirror-E: none(waiver:finite-dimensional-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Positive, mathlib/module/Mathlib.LinearAlgebra.Isomorphisms]
   utility: none
   digest: Common-anchor positive sandwich sums reflect order exactly when their linear relations admit a simultaneous decoder. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! Finite-dimensional common-anchor order reflection and simultaneous linear decoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.HilbertOperators.CommonAnchorOrderReflection

open scoped InnerProductSpace BigOperators
open ContinuousLinearMap InnerProductSpace

variable {E F S : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [Fintype S]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : CompleteSpace F := FiniteDimensional.complete ℂ F

/-- The original weighted sandwich map, with all active components retained. -/
def sandwich (V : S → E →L[ℂ] F) (p : S → ℝ) (X : E →L[ℂ] E) : F →L[ℂ] F :=
  ∑ l, (p l : ℂ) • ((V l).comp (X.comp (V l).adjoint))

/-- Reflection is quantified over every Hermitian operator on the original carrier. -/
def ReflectsPSD (V : S → E →L[ℂ] F) (p : S → ℝ) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → (sandwich V p X).IsPositive → X.IsPositive

/-- Every unit direction and every strictly positive rank-one excess is tested. -/
def RankOneTests (V : S → E →L[ℂ] F) (p : S → ℝ) : Prop :=
  ∀ x : E, ‖x‖ = 1 → ∀ η : ℝ, 0 < η →
    ¬ (sandwich V p (1 - ((1 + η : ℝ) : ℂ) • rankOne ℂ x x)).IsPositive

/-- A single complex-linear decoder works for every component simultaneously. -/
def HasDecoder (V : S → E →L[ℂ] F) : Prop :=
  ∃ C : F →L[ℂ] E, ∀ l, C.comp (V l) = 1

/-- The unweighted synthesis and sum maps use the same whole finite family. -/
def synthesis (V : S → E →L[ℂ] F) : (S → E) →ₗ[ℂ] F :=
  ∑ l, (V l).toLinearMap.comp (LinearMap.proj l)

def coordinateSum : (S → E) →ₗ[ℂ] E := ∑ l, LinearMap.proj l

/-- All complex linear relations of the local actions must preserve their sum. -/
def Compatible (V : S → E →L[ℂ] F) : Prop :=
  (synthesis V).ker ≤ (coordinateSum (E := E) (S := S)).ker

private def stack {G H : Type*} [AddCommGroup G] [Module ℂ G]
    [AddCommGroup H] [Module ℂ H] (A : S → G →ₗ[ℂ] H) :
    G →ₗ[ℂ] PiLp 2 (fun _ : S => H) :=
  (WithLp.linearEquiv 2 ℂ (S → H)).symm.toLinearMap.comp (LinearMap.pi A)

private theorem norm_stack_sq {G : Type*} [AddCommGroup G] [Module ℂ G]
    (A : S → G →ₗ[ℂ] E) (z : G) :
    ‖stack A z‖ ^ 2 = ∑ l, ‖A l z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

private theorem factor_of_kernel {G H K : Type*}
    [AddCommGroup G] [Module ℂ G] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup K] [Module ℂ K]
    (A : G →ₗ[ℂ] K) (B : G →ₗ[ℂ] H) (h : B.ker ≤ A.ker) :
    ∃ D : H →ₗ[ℂ] K, D.comp B = A := by
  let D₀ := (B.ker.liftQ A h).comp B.quotKerEquivRange.symm.toLinearMap
  obtain ⟨D, hD⟩ := D₀.exists_extend
  refine ⟨D, ?_⟩
  ext z
  have hd := congrArg (fun L => L ⟨B z, LinearMap.mem_range_self B z⟩) hD
  simpa [D₀] using hd

private theorem finite_kernel_bound {G H K : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (A : G →ₗ[ℂ] K) (B : G →ₗ[ℂ] H) (h : B.ker ≤ A.ker) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, ‖A z‖ ^ 2 ≤ c * ‖B z‖ ^ 2 := by
  obtain ⟨D, hD⟩ := factor_of_kernel A B h
  let c := ‖D.toContinuousLinearMap‖ ^ 2 + 1
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro z
  have hd : D (B z) = A z := congrArg (fun L => L z) hD
  have hn := D.toContinuousLinearMap.le_opNorm (B z)
  change ‖D (B z)‖ ≤ ‖D.toContinuousLinearMap‖ * ‖B z‖ at hn
  rw [hd] at hn
  have hs := sq_le_sq₀ (norm_nonneg (A z)) (by positivity) |>.mpr hn
  dsimp [c]
  nlinarith [sq_nonneg ‖B z‖]

private theorem sandwich_selfAdjoint (V : S → E →L[ℂ] F) (p : S → ℝ)
    {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) : IsSelfAdjoint (sandwich V p X) := by
  classical
  apply isSelfAdjoint_sum Finset.univ
  intro l _
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · simpa only [mul_def, comp_assoc] using hX.conj_adjoint (V l)

private theorem sandwich_positive (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hp : ∀ l, 0 ≤ p l) {X : E →L[ℂ] E} (hX : X.IsPositive) :
    (sandwich V p X).IsPositive := by
  apply isPositive_sum Finset.univ
  intro l _
  exact (hX.conj_adjoint (V l)).smul_of_nonneg (by simpa using hp l)

private theorem decoder_compression (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hsum : ∑ l, p l = 1) (C : F →L[ℂ] E) (hC : ∀ l, C.comp (V l) = 1)
    (X : E →L[ℂ] E) : C.comp ((sandwich V p X).comp C.adjoint) = X := by
  classical
  have hadj (l : S) : (V l).adjoint.comp C.adjoint = 1 := by
    rw [← adjoint_comp, hC l, adjoint_one]
  have hc (l : S) (y : E) : C (V l y) = y :=
    congrArg (fun L : E →L[ℂ] E => L y) (hC l)
  have ha (l : S) (y : E) : (V l).adjoint (C.adjoint y) = y :=
    congrArg (fun L : E →L[ℂ] E => L y) (hadj l)
  ext z
  simp only [sandwich, sum_apply, smul_apply, comp_apply, map_sum, map_smul, hc, ha]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum]
  simp

private theorem inner_rankOne (x u : E) :
    RCLike.re (inner ℂ ((rankOne ℂ x x) u) u) = ‖inner ℂ x u‖ ^ 2 := by
  rw [rankOne_apply, inner_smul_left, RCLike.conj_mul, RCLike.re_ofReal_pow]

private theorem norm_complement_rankOne (x u : E) (hx : ‖x‖ = 1) :
    ‖u - (rankOne ℂ x x) u‖ ^ 2 = ‖u‖ ^ 2 - ‖inner ℂ x u‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_re_symm, inner_rankOne,
    rankOne_apply, norm_smul, hx, mul_one]
  ring

private def weightedAdjoints (V : S → E →L[ℂ] F) (p : S → ℝ) :
    S → F →ₗ[ℂ] E := fun l => (Real.sqrt (p l) : ℂ) • (V l).adjoint.toLinearMap

private theorem weighted_norm (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hp : ∀ l, 0 ≤ p l) (z : F) :
    ‖stack (weightedAdjoints V p) z‖ ^ 2 = ∑ l, p l * ‖(V l).adjoint z‖ ^ 2 := by
  rw [norm_stack_sq]
  apply Finset.sum_congr rfl
  intro l _
  simp [weightedAdjoints, norm_smul, mul_pow, Real.sq_sqrt (hp l)]

private theorem weighted_complement_norm (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hp : ∀ l, 0 ≤ p l) (x : E) (hx : ‖x‖ = 1) (z : F) :
    ‖stack (fun l => (1 - rankOne ℂ x x).toLinearMap.comp
        (weightedAdjoints V p l)) z‖ ^ 2 =
      (∑ l, p l * ‖(V l).adjoint z‖ ^ 2) -
        ∑ l, p l * ‖inner ℂ x ((V l).adjoint z)‖ ^ 2 := by
  rw [norm_stack_sq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  change ‖(1 - rankOne ℂ x x) ((Real.sqrt (p l) : ℂ) • (V l).adjoint z)‖ ^ 2 = _
  rw [map_smul, norm_smul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hp l)]
  change p l * ‖(V l).adjoint z - (rankOne ℂ x x) ((V l).adjoint z)‖ ^ 2 = _
  rw [norm_complement_rankOne x _ hx]
  ring

private theorem re_complex_real_mul (r : ℝ) (z : ℂ) :
    RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by
  change ((r : ℂ) * z).re = r * z.re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem re_complex_real (r : ℝ) : RCLike.re (r : ℂ) = r := rfl

private theorem sandwich_quadratic (V : S → E →L[ℂ] F) (p : S → ℝ)
    (X : E →L[ℂ] E) (z : F) :
    RCLike.re (inner ℂ (sandwich V p X z) z) =
      ∑ l, p l * RCLike.re (inner ℂ (X ((V l).adjoint z)) ((V l).adjoint z)) := by
  classical
  simp only [sandwich, sum_apply, smul_apply, comp_apply, sum_inner, inner_smul_left,
    map_sum, Complex.conj_ofReal, re_complex_real_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [← (V l).adjoint_inner_right]

private theorem test_quadratic (V : S → E →L[ℂ] F) (p : S → ℝ)
    (x : E) (η : ℝ) (z : F) :
    RCLike.re (inner ℂ (sandwich V p (1 - ((1 + η : ℝ) : ℂ) • rankOne ℂ x x) z) z) =
      (∑ l, p l * ‖(V l).adjoint z‖ ^ 2) -
        (1 + η) * ∑ l, p l * ‖inner ℂ x ((V l).adjoint z)‖ ^ 2 := by
  rw [sandwich_quadratic, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [sub_apply, one_def, id_apply, smul_apply, inner_sub_left, inner_smul_left,
    map_sub, Complex.conj_ofReal, re_complex_real_mul, inner_self_eq_norm_sq, inner_rankOne]
  ring

private theorem test_selfAdjoint (x : E) (η : ℝ) :
    IsSelfAdjoint (1 - ((1 + η : ℝ) : ℂ) • rankOne ℂ x x) := by
  apply IsSelfAdjoint.sub (IsSelfAdjoint.one _)
  exact (show IsSelfAdjoint (((1 + η : ℝ) : ℂ)) by simp [IsSelfAdjoint]).smul
    ((isSymmetric_rankOne_self x).clm_adjoint_eq)

/-- Rank-one rejection forces a nonzero joint adjoint ray, without coefficient agreement. -/
private theorem rank_one_ray (V : S → E →L[ℂ] F) (p : S → ℝ)
    (hp : ∀ l, 0 < p l) (htest : RankOneTests V p) (x : E) (hx : ‖x‖ = 1) :
    ∃ z : F, (∀ l, (V l).adjoint z = inner ℂ x ((V l).adjoint z) • x) ∧
      ∃ l, (V l).adjoint z ≠ 0 := by
  classical
  let A := stack (weightedAdjoints V p)
  let B := stack (fun l => (1 - rankOne ℂ x x).toLinearMap.comp
    (weightedAdjoints V p l))
  have hn : ¬ B.ker ≤ A.ker := by
    intro hk
    obtain ⟨c, hc, hbound⟩ := finite_kernel_bound A B hk
    have ht := htest x hx c⁻¹ (inv_pos.mpr hc)
    apply ht
    refine ⟨(sandwich_selfAdjoint V p (test_selfAdjoint x c⁻¹)).isSymmetric, ?_⟩
    intro z
    change 0 ≤ RCLike.re (inner ℂ
      (sandwich V p (1 - ((1 + c⁻¹ : ℝ) : ℂ) • rankOne ℂ x x) z) z)
    rw [test_quadratic]
    have hA := weighted_norm V p (fun l => (hp l).le) z
    have hB := weighted_complement_norm V p (fun l => (hp l).le) x hx z
    change ‖A z‖ ^ 2 = _ at hA
    change ‖B z‖ ^ 2 = _ at hB
    have hb := hbound z
    have hi : c⁻¹ * c = 1 := inv_mul_cancel₀ hc.ne'
    have hmul := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, hi, one_mul] at hmul
    have hnon := mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg ‖B z‖)
    rw [hA, hB] at hmul
    rw [hB] at hnon
    nlinarith
  simp only [SetLike.le_def, not_forall, not_imp] at hn
  obtain ⟨z, hzB, hzA⟩ := hn
  refine ⟨z, ?_, ?_⟩
  · intro l
    have hl := congrArg (fun q : PiLp 2 (fun _ : S => E) => q l)
      (show B z = 0 from hzB)
    change (1 - rankOne ℂ x x) ((Real.sqrt (p l) : ℂ) • (V l).adjoint z) = 0 at hl
    rw [map_smul] at hl
    have hs : (Real.sqrt (p l) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hp l)).ne'
    have hz := (smul_eq_zero.mp hl).resolve_left hs
    exact sub_eq_zero.mp hz
  · by_contra h
    push_neg at h
    apply hzA
    change A z = 0
    apply (WithLp.ext_iff 2).mpr
    funext l
    change (Real.sqrt (p l) : ℂ) • (V l).adjoint z = 0
    rw [h l, smul_zero]

private theorem tests_force_compatibility [Nonempty S]
    (V : S → E →L[ℂ] F) (p : S → ℝ) (hp : ∀ l, 0 < p l)
    (e : E) (he : e ≠ 0) (v : F) (hanchor : ∀ l, V l e = v)
    (htest : RankOneTests V p) : Compatible V := by
  classical
  let l₀ : S := Classical.choice inferInstance
  intro u hu
  have hrel : ∑ l, V l (u l) = 0 := by
    simpa [synthesis, LinearMap.sum_apply, LinearMap.comp_apply] using hu
  have hunit (x : E) (hx : ‖x‖ = 1) (hex : inner ℂ e x ≠ 0) :
      inner ℂ x (∑ l, u l) = 0 := by
    obtain ⟨z, hz, l₁, hl₁⟩ := rank_one_ray V p hp htest x hx
    let c := inner ℂ x ((V l₀).adjoint z)
    have hcoeff (l : S) : (V l).adjoint z = c • x := by
      have hi : inner ℂ e ((V l).adjoint z) =
          inner ℂ e ((V l₀).adjoint z) := by
        rw [(V l).adjoint_inner_right, (V l₀).adjoint_inner_right, hanchor, hanchor]
      rw [hz l, hz l₀, inner_smul_right, inner_smul_right] at hi
      have hc : inner ℂ x ((V l).adjoint z) = c := mul_right_cancel₀ hex hi
      rw [hz l, hc]
    have hc : c ≠ 0 := by
      intro hc
      exact hl₁ (by rw [hcoeff l₁, hc, zero_smul])
    have hzsum : star c * inner ℂ x (∑ l, u l) = 0 := by
      calc
        _ = ∑ l, inner ℂ ((V l).adjoint z) (u l) := by
          simp_rw [hcoeff, inner_smul_left]
          rw [inner_sum, Finset.mul_sum]
          rfl
        _ = inner ℂ z (∑ l, V l (u l)) := by
          simp_rw [ContinuousLinearMap.adjoint_inner_left]
          rw [inner_sum]
        _ = 0 := by rw [hrel, inner_zero_right]
    exact (mul_eq_zero.mp hzsum).resolve_left (star_ne_zero.mpr hc)
  have hnonorth (x : E) (hex : inner ℂ e x ≠ 0) : inner ℂ x (∑ l, u l) = 0 := by
    have hx : x ≠ 0 := by rintro rfl; simp at hex
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let a : ℂ := (‖x‖⁻¹ : ℝ)
    have ha : a ≠ 0 := by
      dsimp [a]
      exact_mod_cast inv_ne_zero hn
    have hnorm : ‖a • x‖ = 1 := by
      simp [a, norm_smul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ hn]
    have hh := hunit (a • x) hnorm (by rw [inner_smul_right]; exact mul_ne_zero ha hex)
    rw [inner_smul_left] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by simpa using ha)
  have hall (x : E) : inner ℂ x (∑ l, u l) = 0 := by
    by_cases hex : inner ℂ e x = 0
    · have hene : inner ℂ e e ≠ 0 := inner_self_ne_zero.mpr he
      have hh := hnonorth (x + e) (by simpa [inner_add_right, hex] using hene)
      rw [inner_add_left, hnonorth e hene, add_zero] at hh
      exact hh
    · exact hnonorth x hex
  have hz : ∑ l, u l = 0 := inner_self_eq_zero.mp (hall (∑ l, u l))
  simpa [coordinateSum, LinearMap.sum_apply] using hz

private theorem decoder_iff_compatible (V : S → E →L[ℂ] F) :
    HasDecoder V ↔ Compatible V := by
  classical
  constructor
  · rintro ⟨C, hC⟩ u hu
    have hr : ∑ l, V l (u l) = 0 := by
      simpa [synthesis, LinearMap.sum_apply, LinearMap.comp_apply] using hu
    have hc (l : S) : C (V l (u l)) = u l :=
      congrArg (fun L : E →L[ℂ] E => L (u l)) (hC l)
    have hs := congrArg C hr
    simpa [map_sum, hc, coordinateSum, LinearMap.sum_apply] using hs
  · intro hk
    obtain ⟨D, hD⟩ := factor_of_kernel (coordinateSum (E := E) (S := S)) (synthesis V) hk
    refine ⟨D.toContinuousLinearMap, ?_⟩
    intro l
    ext x
    have h := congrArg (fun L : (S → E) →ₗ[ℂ] E => L (Pi.single l x)) hD
    simpa [synthesis, coordinateSum, LinearMap.comp_apply, LinearMap.sum_apply,
      Pi.single_apply, apply_ite] using h

/-- The four original conditions and the exact decoder compression on every operator.
The common image may be zero and no individual component is assumed injective. -/
theorem common_anchor_order_reflection [Nonempty S]
    (V : S → E →L[ℂ] F) (p : S → ℝ) (hp : ∀ l, 0 < p l)
    (hsum : ∑ l, p l = 1) (e : E) (he : e ≠ 0)
    (v : F) (hanchor : ∀ l, V l e = v) :
    (ReflectsPSD V p ↔ RankOneTests V p) ∧
    (RankOneTests V p ↔ HasDecoder V) ∧
    (HasDecoder V ↔ Compatible V) ∧
    (∀ (C : F →L[ℂ] E), (∀ l, C.comp (V l) = 1) →
      ∀ X : E →L[ℂ] E, C.comp ((sandwich V p X).comp C.adjoint) = X) ∧
    (∀ X : E →L[ℂ] E, X.IsPositive → (sandwich V p X).IsPositive) := by
  have h12 : ReflectsPSD V p → RankOneTests V p := by
    intro hr x hx η hη ht
    have hi := hr _ (test_selfAdjoint x η) ht
    have hn := hi.re_inner_nonneg_left x
    have hxinner : inner ℂ x x = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
    have happ : (1 - ((1 + η : ℝ) : ℂ) • rankOne ℂ x x) x = -(η : ℂ) • x := by
      simp only [sub_apply, one_def, id_apply, smul_apply, rankOne_apply, hxinner, one_smul,
        Complex.ofReal_add, Complex.ofReal_one]
      module
    rw [happ, inner_smul_left, hxinner] at hn
    simp only [map_neg, Complex.conj_ofReal, mul_one, re_complex_real] at hn
    linarith
  have h23 : RankOneTests V p → HasDecoder V := fun ht =>
    (decoder_iff_compatible V).mpr (tests_force_compatibility V p hp e he v hanchor ht)
  have h31 : HasDecoder V → ReflectsPSD V p := by
    rintro ⟨C, hC⟩ X _ hX
    have hpos := hX.conj_adjoint C
    rwa [decoder_compression V p hsum C hC X] at hpos
  exact ⟨⟨h12, fun ht => h31 (h23 ht)⟩,
    ⟨h23, fun hd => h12 (h31 hd)⟩, decoder_iff_compatible V,
    (fun C hC X => decoder_compression V p hsum C hC X),
    fun _ hX => sandwich_positive V p (fun l => (hp l).le) hX⟩

#print axioms common_anchor_order_reflection

end D5.S3.HilbertOperators.CommonAnchorOrderReflection
