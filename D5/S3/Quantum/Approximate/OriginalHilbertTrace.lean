/- GID: D5/S3/Quantum/Approximate/OriginalHilbertTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/OriginalHilbertTrace
   mirror-E: none(waiver:analytic-construction)
   anchors: []
   utility: none
   digest: Haar averaging supplies a nearby faithful trace on the original finite algebra. -/

module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Tactic

/-! The C-star norm and the original Hilbert norm are distinct. The latter is
specified by a positive Hermitian core on the very same complex vector space.
The construction is the normalized Haar average of the original
unit functional; its traciality and strict positivity feed the original-form
estimate. No change of unit or construction of the associative product is made.
-/

noncomputable section
open MeasureTheory
open MeasureTheory.Measure
open scoped InnerProductSpace

@[expose] public section

namespace D5.S3.Quantum.Approximate.OriginalHilbertTrace

variable {A : Type*} [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A]

/-- The original Hilbert norm, independently of the C-star norm on `A`. -/
def hilbertNorm (B : InnerProductSpace.Core ℂ A) (x : A) : ℝ :=
  Real.sqrt (B.inner x x).re

private def unitFunctional (B : InnerProductSpace.Core ℂ A) : A →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := B.inner 1
      map_add' := by
        letI := B
        exact InnerProductSpace.Core.inner_add_right 1
      map_smul' := by
        letI := B
        intro c x
        exact InnerProductSpace.Core.inner_smul_right 1 x }

private theorem core_star (B : InnerProductSpace.Core ℂ A)
    (hs : ∀ x, hilbertNorm B (star x) = hilbertNorm B x) (x y : A) :
    B.inner (star x) (star y) = B.inner y x := by
  letI := B
  have hd (z : A) : B.inner (star z) (star z) = B.inner z z := by
    apply Complex.ext
    · have h := congrArg (fun r : ℝ => r ^ 2) (hs z)
      exact (Real.sq_sqrt (B.re_inner_nonneg (star z))).symm.trans
        (h.trans (Real.sq_sqrt (B.re_inner_nonneg z)))
    · simp only [show (B.inner (star z) (star z)).im = 0 from
        InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) _,
        show (B.inner z z).im = 0 from InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) _]
  have hsum (v w : A) :
      B.inner (star v) (star w) + B.inner (star w) (star v) =
        B.inner v w + B.inner w v := by
    have h := hd (v + w)
    simp only [star_add, InnerProductSpace.Core.inner_add_left,
      InnerProductSpace.Core.inner_add_right] at h
    linear_combination h - hd v - hd w
  have hI := hsum x (Complex.I • y)
  simp only [star_smul, Complex.star_def, Complex.conj_I,
    InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
    map_neg, Complex.conj_I, neg_neg] at hI
  linear_combination (norm := ring_nf)
    (1 / 2 : ℂ) * hsum x y + (Complex.I / 2) * hI
  simp [Complex.I_sq]

private instance unitaryCompact : CompactSpace (unitary A) := by
  apply isCompact_iff_compactSpace.mp
  letI : ProperSpace A := FiniteDimensional.proper ℂ A
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  rw [isBounded_iff_forall_norm_le]
  exact ⟨1, fun u hu => (CStarRing.norm_of_mem_unitary hu).le⟩

local instance : MeasurableSpace (unitary A) := borel (unitary A)
local instance : BorelSpace (unitary A) := ⟨rfl⟩

private def probabilityHaar : Measure (unitary A) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

private instance probabilityHaar_probability :
    IsProbabilityMeasure (probabilityHaar (A := A)) := by
  constructor
  exact Measure.haarMeasure_self (K₀ := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩)

private instance probabilityHaar_haar : IsHaarMeasure (probabilityHaar (A := A)) :=
  inferInstanceAs (IsHaarMeasure (Measure.haarMeasure _))

private instance probabilityHaar_left :
    (probabilityHaar (A := A)).IsMulLeftInvariant :=
  inferInstanceAs (Measure.IsMulLeftInvariant (Measure.haarMeasure _))

private def conjugate (u : unitary A) (x : A) : A :=
  (star u : A) * x * u

private theorem conjugate_continuous (x : A) :
    Continuous (fun u : unitary A => conjugate u x) := by
  unfold conjugate
  fun_prop

private theorem integrable_conjugate (τ : A →L[ℂ] ℂ) (x : A) :
    Integrable (fun u : unitary A => τ (conjugate u x)) probabilityHaar :=
  (τ.continuous.comp (conjugate_continuous x)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private def averaged (τ : A →L[ℂ] ℂ) : A →ₗ[ℂ] ℂ where
  toFun x := ∫ u : unitary A, τ (conjugate u x) ∂probabilityHaar
  map_add' x y := by
    simp only [conjugate, mul_add, add_mul, map_add]
    exact integral_add (integrable_conjugate τ x) (integrable_conjugate τ y)
  map_smul' c x := by
    simp only [conjugate, mul_smul_comm, smul_mul_assoc, map_smul,
      integral_smul, RingHom.id_apply]

private theorem averaged_invariant (τ : A →L[ℂ] ℂ) (v : unitary A) (x : A) :
    averaged τ (conjugate v x) = averaged τ x := by
  change (∫ u : unitary A, τ (conjugate u (conjugate v x)) ∂probabilityHaar) = _
  have he (u : unitary A) : conjugate u (conjugate v x) = conjugate (v * u) x := by
    simp [conjugate, mul_assoc]
  simp_rw [he]
  exact integral_mul_left_eq_self (μ := probabilityHaar)
    (fun u : unitary A => τ (conjugate u x)) v

private theorem averaged_trace (τ : A →L[ℂ] ℂ) (x y : A) :
    averaged τ (x * y) = averaged τ (y * x) := by
  have hu (u : unitary A) : averaged τ ((u : A) * y) = averaged τ (y * u) := by
    have h := averaged_invariant τ u ((u : A) * y)
    simpa [conjugate, ← mul_assoc] using h.symm
  obtain ⟨u, c, hx, _⟩ := CStarAlgebra.exists_sum_four_unitary x
  rw [hx, Finset.sum_mul, Finset.mul_sum, _root_.map_sum, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, hu]

private theorem averaged_unital (τ : A →L[ℂ] ℂ) (hτ : τ 1 = 1) :
    averaged τ 1 = 1 := by
  change (∫ u : unitary A, τ (conjugate u 1) ∂probabilityHaar) = 1
  simp [conjugate, hτ]

private theorem averaged_positive (τ : A →L[ℂ] ℂ)
    (hpos : ∀ x : A, 0 ≤ (τ (star x * x)).re)
    (hfaith : ∀ x : A, x ≠ 0 → 0 < (τ (star x * x)).re)
    (x : A) (hx : x ≠ 0) : 0 < (averaged τ (star x * x)).re := by
  have he (u : unitary A) : conjugate u (star x * x) = star (x * (u : A)) * (x * u) := by
    simp [conjugate, star_mul, mul_assoc]
  have hi := integrable_conjugate τ (star x * x)
  rw [show (averaged τ (star x * x)).re =
      ∫ u : unitary A, (τ (conjugate u (star x * x))).re ∂probabilityHaar from
    (Complex.reCLM.integral_comp_comm hi).symm]
  have hc : Continuous (fun u : unitary A => (τ (conjugate u (star x * x))).re) :=
    Complex.continuous_re.comp (τ.continuous.comp (conjugate_continuous _))
  apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : unitary A)) hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  · intro u
    change 0 ≤ (τ (conjugate u (star x * x))).re
    rw [he]
    exact hpos _
  · simpa [conjugate] using (hfaith x hx).ne'

private theorem averaged_star (τ : A →L[ℂ] ℂ)
    (hs : ∀ x, τ (star x) = star (τ x)) (x : A) :
    averaged τ (star x) = star (averaged τ x) := by
  have hi := integrable_conjugate τ x
  change (∫ u : unitary A, τ (conjugate u (star x)) ∂probabilityHaar) = _
  have he (u : unitary A) : conjugate u (star x) = star (conjugate u x) := by
    simp [conjugate, star_mul, mul_assoc]
  simp_rw [he, hs]
  exact integral_conj

private theorem averaged_near (τ : A →L[ℂ] ℂ) (p : A → ℝ) (K : ℝ)
    (hcomm : ∀ x y : A, ‖τ (x * y - y * x)‖ ≤ K * p x * p y)
    (C U : ℝ) (hK : 0 ≤ K) (hp : ∀ x, 0 ≤ p x)
    (hmul : ∀ x y, p (x * y) ≤ C * p x * p y)
    (hstar : ∀ x, p (star x) = p x)
    (hunitary : ∀ u : unitary A, p u ≤ U)
    (hC : 0 ≤ C) (hU : 0 ≤ U) (x : A) :
    ‖averaged τ x - τ x‖ ≤ K * C * U ^ 2 * p x := by
  have he (u : unitary A) :
      τ (conjugate u x) - τ x = τ ((star u : A) * (x * u) - (x * u) * star u) := by
    simp [conjugate, map_sub, mul_assoc]
  have hb (u : unitary A) :
      ‖τ (conjugate u x) - τ x‖ ≤ K * C * U ^ 2 * p x := by
    rw [he]
    calc
      _ ≤ K * p (star (u : A)) * p (x * u) := hcomm _ _
      _ = K * p (u : A) * p (x * u) := by rw [hstar]
      _ ≤ K * U * (C * p x * U) := by
        gcongr
        · exact hp _
        · exact hunitary u
        · exact (hmul x u).trans
            (mul_le_mul_of_nonneg_left (hunitary u) (mul_nonneg hC (hp x)))
      _ = _ := by ring
  have hi := integrable_conjugate τ x
  change ‖(∫ u : unitary A, τ (conjugate u x) ∂probabilityHaar) - τ x‖ ≤ _
  have hc : (∫ _ : unitary A, τ x ∂probabilityHaar) = τ x := by simp
  rw [← hc, ← integral_sub hi (integrable_const _)]
  simpa using norm_integral_le_of_norm_le_const
    (μ := probabilityHaar) (Filter.Eventually.of_forall hb)

/-- Riesz representation in the original metric, with the quantitative bound
kept in that metric. This helper is consumed by the joint trace construction. -/
private theorem original_gram (B C : InnerProductSpace.Core ℂ A) (r : ℝ)
    (hnear : ∀ x y, ‖C.inner x y - B.inner x y‖ ≤
      r * hilbertNorm B x * hilbertNorm B y) :
    ∃ G : A ≃ₗ[ℂ] A,
      (∀ x y, B.inner (G x) y = C.inner x y) ∧
      (∀ x, hilbertNorm B (G x - x) ≤ r * hilbertNorm B x) := by
  letI := B
  letI := B.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore B
  letI := FiniteDimensional.completeSpace ℂ A
  let row (x : A) : A →ₗ[ℂ] ℂ :=
    { toFun := C.inner x
      map_add' := by
        letI := C
        exact InnerProductSpace.Core.inner_add_right x
      map_smul' := by
        letI := C
        intro c y
        exact InnerProductSpace.Core.inner_smul_right x y }
  let form : A →ₗ⋆[ℂ] A →L[ℂ] ℂ :=
    { toFun := fun x => (row x).toContinuousLinearMap
      map_add' := by
        intro x y
        ext z
        exact C.add_left x y z
      map_smul' := by
        intro c x
        ext y
        exact C.smul_left x y c }
  let H : A →L[ℂ] A := InnerProductSpace.continuousLinearMapOfBilin
    ⟨form, form.continuous_of_finiteDimensional⟩
  have hH (x y : A) : B.inner (H x) y = C.inner x y :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ x y
  have hinj : Function.Injective H := by
    apply (injective_iff_map_eq_zero H).mpr
    intro x hx
    apply C.definite x
    rw [← hH, hx]
    exact InnerProductSpace.Core.inner_zero_left _
  let G : A ≃ₗ[ℂ] A := LinearEquiv.ofBijective H.toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective (f := H.toLinearMap)).mp hinj⟩
  refine ⟨G, hH, ?_⟩
  intro x
  let v := G x - x
  have hv : ‖v‖ ^ 2 ≤ r * hilbertNorm B x * ‖v‖ := by
    have hi := hnear x v
    have he : B.inner v v = C.inner x v - B.inner x v := by
      change B.inner (H x - x) v = _
      rw [InnerProductSpace.Core.inner_sub_left, hH]
    have hn : ‖B.inner v v‖ = ‖v‖ ^ 2 := by
      simpa using (norm_inner_self v)
    rw [← he, hn] at hi
    exact hi
  change ‖v‖ ≤ r * hilbertNorm B x
  by_cases hz : v = 0
  · have hr : 0 ≤ r := by
      have h := hnear 1 1
      have hp : 0 < hilbertNorm B (1 : A) := norm_pos_iff.mpr one_ne_zero
      nlinarith [norm_nonneg (C.inner 1 1 - B.inner 1 1)]
    simpa [hz] using mul_nonneg hr (Real.sqrt_nonneg (B.inner x x).re)
  · have hp : 0 < ‖v‖ := norm_pos_iff.mpr hz
    nlinarith

/-- On the original finite complex vector space, an associative C-star product
close to the original adjoint-compatible product supplies one faithful unital
trace. Its positive Hermitian form has the original quantitative bound.
All norms denoted by `hilbertNorm B` are the original Hilbert norms. -/
theorem nearby_faithful_trace
    (B : InnerProductSpace.Core ℂ A) (μ : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (M q d : ℝ) (hM : 1 ≤ M) (hq1 : q < 1) (hd1 : d ≤ 1 / 8)
    (hone : B.inner 1 1 = 1)
    (hstar : ∀ x, hilbertNorm B (star x) = hilbertNorm B x)
    (hunit : ∀ x, μ x 1 = x)
    (hadj : ∀ x y z, B.inner (μ x y) z = B.inner y (μ (star x) z))
    (hμ : ∀ x y, hilbertNorm B (μ x y) ≤ M * hilbertNorm B x * hilbertNorm B y)
    (hnear : ∀ x y, hilbertNorm B (x * y - μ x y) ≤
      q * hilbertNorm B x * hilbertNorm B y)
    (hu : ∀ u : unitary A, hilbertNorm B u ≤ 1 + 2 * d) :
    ∃ t : A →ₗ[ℂ] ℂ, ∃ Bt : InnerProductSpace.Core ℂ A,
      t 1 = 1 ∧
      (∀ x y, t (x * y) = t (y * x)) ∧
      (∀ x, t (star x) = star (t x)) ∧
      (∀ x, ‖t x - B.inner 1 x‖ ≤ 8 * M * q * hilbertNorm B x) ∧
      (∀ x y, Bt.inner x y = t (star x * y)) ∧
      Bt.inner 1 1 = 1 ∧
      (∀ x y, ‖Bt.inner x y - B.inner x y‖ ≤
        17 * M ^ 2 * q * hilbertNorm B x * hilbertNorm B y) ∧
      (∀ a x y, Bt.inner (a * x) y = Bt.inner x (star a * y)) := by
  letI := B
  let p := hilbertNorm B
  let τ := unitFunctional B
  have hp (x : A) : 0 ≤ p x := Real.sqrt_nonneg _
  have hpstar (x : A) : p (star x) = p x := hstar x
  have hpone : p 1 = 1 := by simp [p, hilbertNorm, hone]
  have hq : 0 ≤ q := by
    have hb := hnear 1 1
    change p (1 * 1 - μ 1 1) ≤ q * p 1 * p 1 at hb
    simp only [hpone, mul_one] at hb
    exact (hp _).trans hb
  have hd : 0 ≤ d := by
    have hb := hu 1
    change p 1 ≤ 1 + 2 * d at hb
    rw [hpone] at hb
    linarith
  have hτ (x : A) : τ x = B.inner 1 x := rfl
  have hτnorm (x : A) : ‖τ x‖ ≤ p x := by
    rw [hτ]
    have h := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) (F := A) 1 x
    change ‖B.inner 1 x‖ ≤ p 1 * p x at h
    simpa only [hpone, one_mul] using h
  have hτone : τ 1 = 1 := hone
  have hτstar (x : A) : τ (star x) = star (τ x) := by
    have h := core_star B hstar 1 x
    calc
      τ (star x) = B.inner x 1 := by simpa only [star_one, hτ] using h
      _ = star (τ x) := (B.conj_inner_symm x 1).symm
  have hμeval (x y : A) : τ (μ x y) = B.inner (star x) y := by
    simpa only [star_star, hunit, hτ] using (hadj (star x) 1 y).symm
  have hμcomm (x y : A) : τ (μ x y) = τ (μ y x) := by
    rw [hμeval, hμeval]
    simpa only [star_star] using core_star B hstar x (star y)
  have hclose (x y : A) :
      ‖τ (x * y) - B.inner (star x) y‖ ≤ q * p x * p y := by
    rw [← hμeval, ← map_sub]
    exact (hτnorm _).trans (hnear x y)
  have hcomm (x y : A) : ‖τ (x * y - y * x)‖ ≤ 2 * q * p x * p y := by
    have he : τ (x * y - y * x) =
        (τ (x * y) - τ (μ x y)) - (τ (y * x) - τ (μ y x)) := by
      rw [map_sub, hμcomm x y]
      ring
    rw [he]
    calc
      _ ≤ ‖τ (x * y) - τ (μ x y)‖ + ‖τ (y * x) - τ (μ y x)‖ := norm_sub_le _ _
      _ ≤ q * p x * p y + q * p y * p x := by
        gcongr <;> simpa only [hμeval] using hclose _ _
      _ = _ := by ring
  have hmul (x y : A) : p (x * y) ≤ (M + q) * p x * p y := by
    letI := B.toNormedAddCommGroup
    have he : x * y = (x * y - μ x y) + μ x y := (sub_add_cancel _ _).symm
    calc
      p (x * y) = p ((x * y - μ x y) + μ x y) := congrArg p he
      _ ≤ p (x * y - μ x y) + p (μ x y) :=
        @norm_add_le A
          B.toNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup _ _
      _ ≤ q * p x * p y + M * p x * p y := add_le_add (hnear x y) (hμ x y)
      _ = _ := by ring
  have hposlower (x : A) : (1 - q) * p x ^ 2 ≤ (τ (star x * x)).re := by
    have h := hclose (star x) x
    simp only [star_star, hpstar] at h
    have hr := (abs_le.mp
      (Complex.abs_re_le_norm (τ (star x * x) - B.inner x x))).1
    have hs : p x ^ 2 = (B.inner x x).re := Real.sq_sqrt (B.re_inner_nonneg x)
    simp only [Complex.sub_re] at hr
    nlinarith
  have hpos (x : A) : 0 ≤ (τ (star x * x)).re :=
    (mul_nonneg (by linarith) (sq_nonneg _)).trans (hposlower x)
  have hfaith (x : A) (hx : x ≠ 0) : 0 < (τ (star x * x)).re := by
    letI := B.toNormedAddCommGroup
    have hn : 0 < p x := norm_pos_iff.mpr hx
    exact (mul_pos (sub_pos.mpr hq1) (sq_pos_of_pos hn)).trans_le (hposlower x)
  let t := averaged τ
  have htstar (x : A) : t (star x) = star (t x) := averaged_star τ hτstar x
  have htfaith (x : A) (hx : x ≠ 0) : 0 < (t (star x * x)).re :=
    averaged_positive τ hpos hfaith x hx
  have htpos (x : A) : 0 ≤ (t (star x * x)).re := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (htfaith x hx).le
  have htnear (x : A) : ‖t x - τ x‖ ≤ 8 * M * q * p x := by
    have hb := averaged_near τ p (2 * q) hcomm (M + q) (1 + 2 * d)
      (by positivity) hp hmul hstar hu (by linarith) (by positivity) x
    have hcoeff : 2 * q * (M + q) * (1 + 2 * d) ^ 2 ≤ 8 * M * q := by
      have hC : M + q ≤ 2 * M := by linarith
      have hU : (1 + 2 * d) ^ 2 ≤ 25 / 16 := by nlinarith
      calc
        _ ≤ 2 * q * (2 * M) * (25 / 16) := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg (by linarith : 0 ≤ M) hq]
    exact hb.trans (mul_le_mul_of_nonneg_right hcoeff (hp x))
  let Bt : InnerProductSpace.Core ℂ A :=
    { inner x y := t (star x * y)
      conj_inner_symm x y := by
        change star (t (star y * x)) = t (star x * y)
        rw [← htstar, star_mul, star_star]
      re_inner_nonneg := htpos
      add_left x y z := by simp only [star_add, add_mul, map_add]
      smul_left x y c := by simp only [star_smul, smul_mul_assoc, map_smul,
        smul_eq_mul, starRingEnd_apply]
      definite x hx := by
        by_contra hn
        have hf := htfaith x hn
        rw [hx] at hf
        exact (lt_irrefl 0) hf }
  refine ⟨t, Bt, averaged_unital τ hτone, averaged_trace τ, htstar,
    htnear, fun _ _ => rfl, ?_, ?_, ?_⟩
  · change t (star 1 * 1) = 1
    simpa using averaged_unital τ hτone
  · intro x y
    change ‖t (star x * y) - B.inner x y‖ ≤ _
    have he : t (star x * y) - B.inner x y =
        (t (star x * y) - τ (star x * y)) +
          (τ (star x * y) - B.inner x y) := by ring
    rw [he]
    calc
      _ ≤ ‖t (star x * y) - τ (star x * y)‖ +
          ‖τ (star x * y) - B.inner x y‖ := norm_add_le _ _
      _ ≤ 8 * M * q * p (star x * y) + q * p x * p y := by
        gcongr
        · exact htnear _
        · simpa only [star_star, hpstar] using hclose (star x) y
      _ ≤ 8 * M * q * ((M + q) * p x * p y) + q * p x * p y := by
        gcongr
        simpa only [hpstar] using hmul (star x) y
      _ ≤ 17 * M ^ 2 * q * p x * p y := by
        have hC : M + q ≤ 2 * M := by linarith
        have hM2 : 1 ≤ M ^ 2 := by nlinarith
        have hxy : 0 ≤ q * p x * p y := mul_nonneg (mul_nonneg hq (hp x)) (hp y)
        have h8 : 0 ≤ 8 * M * (q * p x * p y) :=
          mul_nonneg (by linarith) hxy
        nlinarith [mul_nonneg (sub_nonneg.mpr hC)
            h8,
          mul_nonneg (sub_nonneg.mpr hM2) hxy]
  · intro a x y
    change t (star (a * x) * y) = t (star x * (star a * y))
    simp only [star_mul, mul_assoc]

#print axioms nearby_faithful_trace

end D5.S3.Quantum.Approximate.OriginalHilbertTrace
