/- GID: D5/S3/Arith/QuadraticFields/QuadraticAccumulationClassification
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/QuadraticAccumulationClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual quadratic accumulation sets equal signed nonzero trace-dual norm spectra. -/

import D5.S3.Arith.QuadraticFields.QuadraticAccumulation
import Mathlib.Analysis.Normed.Group.Uniform

/-! The accumulation classification by signed norms in the actual quadratic trace dual. -/

noncomputable section

namespace D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification

open D5.S3.Arith.QuadraticFields.QuadraticAccumulation
open QuadraticAlgebra Set Filter
open scoped Topology

private theorem large_denominator_near (a x : ℝ)
    (hx : x ∈ derivedSet (approximationValues a)) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ q p : ℤ, q ≠ 0 ∧ (n : ℝ) < |(q : ℝ)| ∧
      abs (|(q : ℝ)| * ((q : ℝ) * a - p) - x) < ε := by
  classical
  let M : ℤ := ⌈(n : ℝ) * |a| + |x| + 1⌉
  let T : Set ℝ := (fun z : ℤ × ℤ => |(z.1 : ℝ)| * ((z.1 : ℝ) * a - z.2)) ''
    ((Set.Icc (-(n : ℤ)) n) ×ˢ (Set.Icc (-M) M))
  have hT : T.Finite := (Set.finite_Icc _ _ |>.prod (Set.finite_Icc _ _)).image _
  have hU : Metric.ball x (min ε 1) ∩ (T \ {x})ᶜ ∈ 𝓝 x :=
    inter_mem (Metric.ball_mem_nhds x (lt_min hε zero_lt_one))
      ((show (T \ {x}).Finite from hT.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds
        (by simp))
  obtain ⟨y, ⟨hyU, q, p, hq, rfl⟩, hyx⟩ := accPt_iff_nhds.mp hx _ hU
  have hy : abs (|(q : ℝ)| * ((q : ℝ) * a - p) - x) < min ε 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hyU.1
  refine ⟨q, p, hq, ?_, lt_of_lt_of_le hy (min_le_left _ _)⟩
  by_contra hn
  have hqn : |(q : ℝ)| ≤ n := le_of_not_gt hn
  have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hq)
  have hybound : abs (|(q : ℝ)| * ((q : ℝ) * a - p)) < |x| + 1 := by
    have ht := abs_add_le (|(q : ℝ)| * ((q : ℝ) * a - p) - x) x
    rw [sub_add_cancel] at ht
    linarith [lt_of_lt_of_le hy (min_le_right ε 1)]
  have he : |(q : ℝ) * a - p| ≤ abs (|(q : ℝ)| * ((q : ℝ) * a - p)) := by
    rw [abs_mul, abs_abs]
    nlinarith [abs_nonneg ((q : ℝ) * a - p)]
  have hpbound : |(p : ℝ)| ≤ (M : ℝ) := by
    have ht := abs_sub ((q : ℝ) * a) ((q : ℝ) * a - p)
    rw [sub_sub_cancel, abs_mul] at ht
    have hM : (n : ℝ) * |a| + |x| + 1 ≤ (M : ℝ) := Int.le_ceil _
    nlinarith [abs_nonneg a]
  have hqi : q ∈ Set.Icc (-(n : ℤ)) n := by
    have : |q| ≤ (n : ℤ) := by exact_mod_cast hqn
    exact abs_le.mp this
  have hpi : p ∈ Set.Icc (-M) M := by
    have : |p| ≤ M := by exact_mod_cast hpbound
    exact abs_le.mp this
  exact hyU.2 ⟨⟨(q,p), ⟨hqi,hpi⟩, rfl⟩, hyx⟩

private def dualVector (D : ℤ) (A B : ℚ) (q p : ℤ) : K D :=
  ⟨(q : ℚ) / 2, ((p : ℚ) - A * q) / (2 * D * B)⟩

private theorem dualVector_mem (D : ℤ) (hD : D ≠ 0) (A B : ℚ) (hB : B ≠ 0)
    (q p : ℤ) : dualVector D A B q p ∈ traceDual D A B := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  apply (mem_traceDual_iff D A B _).mpr
  constructor
  · exact ⟨q, by dsimp [dualVector]; ring⟩
  · refine ⟨p, ?_⟩
    dsimp [dualVector]
    field_simp
    ring

private theorem norm_grid (D : ℤ) (hD : D ≠ 0) (A B : ℚ) (hB : B ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ q p : ℤ, ∃ k : ℤ,
      (k : ℚ) = m * Algebra.norm ℚ (dualVector D A B q p) := by
  let f : Fin 3 → ℚ := ![1/4 - A^2/(4*D*B^2), A/(2*D*B^2), -1/(4*D*B^2)]
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  obtain ⟨a, ha⟩ := hm 0
  obtain ⟨b, hb⟩ := hm 1
  obtain ⟨c, hc⟩ := hm 2
  change (a : ℚ) = (m : ℤ) * (1/4 - A^2/(4*D*B^2)) at ha
  change (b : ℚ) = (m : ℤ) * (A/(2*D*B^2)) at hb
  change (c : ℚ) = (m : ℤ) * (-1/(4*D*B^2)) at hc
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp m.property, fun q p => ?_⟩
  refine ⟨a*q^2 + b*q*p + c*p^2, ?_⟩
  rw [norm_coordinates]
  dsimp [dualVector]
  push_cast
  rw [ha, hb, hc]
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  field_simp
  ring

private theorem norm_error (D : ℤ) (hD : 0 < D) (A B : ℚ) (hB : B ≠ 0)
    (q p : ℤ) :
    let δ : ℝ := 2 * B * Real.sqrt (D : ℝ)
    let e : ℝ := (q : ℝ) * ((A : ℝ) + B * Real.sqrt (D : ℝ)) - p
    δ * (Algebra.norm ℚ (dualVector D A B q p) : ℝ) = (q : ℝ) * e - e^2 / δ := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  have hr : Real.sqrt (D : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hD))
  dsimp only
  rw [norm_coordinates]
  dsimp [dualVector]
  push_cast
  field_simp
  ring_nf
  simp [Real.sq_sqrt (show (0 : ℝ) ≤ D by exact_mod_cast hD.le)]
  ring

/-- The complete accumulation set is the signed norm spectrum of the actual trace dual. -/
theorem derivedSet_eq_signed_norm_values (D : ℤ) (hD : 2 ≤ D) (hs : Squarefree D)
    (A B : ℚ) (hB : B ≠ 0) :
    derivedSet (approximationValues ((A : ℝ) + (B : ℝ) * Real.sqrt (D : ℝ))) =
      {x | ∃ s : RealField D A B, s ∈ realTraceDual D A B ∧ s ≠ 0 ∧
        (x = 2 * (B : ℝ) * Real.sqrt (D : ℝ) * (Algebra.norm ℚ s : ℝ) ∨
         x = -(2 * (B : ℝ) * Real.sqrt (D : ℝ) * (Algebra.norm ℚ s : ℝ)))} := by
  classical
  ext x
  constructor
  · intro hx
    let a : ℝ := (A : ℝ) + B * Real.sqrt (D : ℝ)
    let δ : ℝ := 2 * B * Real.sqrt (D : ℝ)
    have hδ : δ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast hB)) (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < D by omega))))
    have hnear (n : ℕ) := large_denominator_near a x hx n (1 / ((n : ℝ) + 1))
      (by positivity)
    choose q p hq hlarge hclose using hnear
    let y : ℕ → ℝ := fun n => |(q n : ℝ)| * ((q n : ℝ) * a - p n)
    let e : ℕ → ℝ := fun n => (q n : ℝ) * a - p n
    let c : ℕ → ℝ := fun n => if 0 < q n then 1 else -1
    have hy : Tendsto y atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _ => dist_nonneg) (fun n => by
        simpa only [Real.dist_eq] using (hclose n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hqinf : Tendsto (fun n => |(q n : ℝ)|) atTop atTop :=
      tendsto_atTop_mono (fun n => (hlarge n).le) tendsto_natCast_atTop_atTop
    have he : Tendsto e atTop (𝓝 0) := by
      have ht := hy.mul (tendsto_inv_atTop_zero.comp hqinf)
      simp only [mul_zero] at ht
      convert ht using 1
      ext n
      dsimp [y, e]
      have hqn : (q n : ℝ) ≠ 0 := by exact_mod_cast hq n
      field_simp
    have hc : Tendsto (fun n => c n * e n ^ 2) atTop (𝓝 0) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      convert he.pow 2 using 1
      · ext n
        dsimp only [c]
        split_ifs <;> simp [Real.dist_eq, abs_of_nonneg (sq_nonneg (e n))]
      · norm_num
    obtain ⟨m, hm, hgrid⟩ := norm_grid D (by omega) A B hB
    choose k hk using fun n => hgrid (q n) (p n)
    let j : ℕ → ℤ := fun n => if 0 < q n then k n else -k n
    have hid (n : ℕ) : (j n : ℝ) = (m : ℝ) / δ * (y n - c n * e n ^ 2 / δ) := by
      have hn := norm_error D (show 0 < D by omega) A B hB (q n) (p n)
      change δ * (Algebra.norm ℚ (dualVector D A B (q n) (p n)) : ℝ) =
        (q n : ℝ) * e n - e n ^ 2 / δ at hn
      have hk' : (k n : ℝ) = (m : ℝ) *
          (Algebra.norm ℚ (dualVector D A B (q n) (p n)) : ℝ) := by
        exact_mod_cast hk n
      dsimp only [j, c]
      split_ifs with hpos
      · have hpos' : (0 : ℝ) < q n := by exact_mod_cast hpos
        have hy' : y n = (q n : ℝ) * e n := by simp [y, e, abs_of_pos hpos']
        rw [hk', hy']
        field_simp
        field_simp at hn
        nlinarith [hn]
      · have hneg : (q n : ℝ) < 0 := by
          exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hpos) (hq n))
        have hy' : y n = -(q n : ℝ) * e n := by simp [y, e, abs_of_neg hneg]
        simp only [Int.cast_neg]
        rw [hk', hy']
        field_simp
        field_simp at hn
        nlinarith [hn]
    have hj : Tendsto (fun n => (j n : ℝ)) atTop (𝓝 ((m : ℝ) / δ * x)) := by
      have ht := (hy.sub (hc.div_const δ)).const_mul ((m : ℝ) / δ)
      simp only [zero_div, sub_zero] at ht
      exact ht.congr (fun n => (hid n).symm)
    obtain ⟨z, hz⟩ := Real.isClosed_range_intCast.mem_of_tendsto hj
      (Eventually.of_forall fun n => ⟨j n, rfl⟩)
    have hjz : Tendsto j atTop (𝓝 z) :=
      Real.isClosedEmbedding_intCast.isEmbedding.tendsto_nhds_iff.mpr (by
        change Tendsto (fun n => (j n : ℝ)) atTop (𝓝 (z : ℝ))
        rw [hz]
        exact hj)
    have hev : ∀ᶠ n in atTop, j n = z := by
      have ht : Tendsto j atTop (pure z) := by simpa only [nhds_discrete] using hjz
      simpa only [tendsto_pure] using ht
    obtain ⟨n, hn⟩ := hev.exists
    let t := dualVector D A B (q n) (p n)
    have ht0 : t ≠ 0 := by
      intro ht
      have hr := congrArg QuadraticAlgebra.re ht
      change (q n : ℚ) / 2 = 0 at hr
      have : q n = 0 := by exact_mod_cast (div_eq_zero_iff.mp hr).resolve_right (by norm_num)
      exact hq n this
    let : Fact (¬ IsSquare (D : ℚ)) :=
      ⟨by simpa only [Rat.isSquare_intCast_iff] using sqrt_nonsquare D hD hs⟩
    let E := coordinateEquiv D (show 0 ≤ D by omega) A B hB
    have htL := dualVector_mem D (show D ≠ 0 by omega) A B hB (q n) (p n)
    have hEL : E t ∈ realTraceDual D A B := by
      change ∀ v ∈ realLattice D A B,
        Algebra.trace ℚ (RealField D A B) (E t * v) ∈ (1 : Submodule ℤ ℚ)
      have hEα : E (alpha D A B) = realAlpha D A B := by
        apply Subtype.ext
        rw [coordinateEquiv_coe]
        simp [realEmbedding_apply, alpha, realAlpha]
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
          rcases hv with rfl | hv
          · have h := htL 1 (Submodule.subset_span (by simp))
            change Algebra.trace ℚ (K D) (t * 1) ∈ (1 : Submodule ℤ ℚ) at h
            simpa only [mul_one, Algebra.trace_eq_of_algEquiv E t] using h
          · have hv' : v = realAlpha D A B := Set.mem_singleton_iff.mp hv
            subst v
            have h := htL (alpha D A B) (Submodule.subset_span (by simp))
            change Algebra.trace ℚ (K D) (t * alpha D A B) ∈ (1 : Submodule ℤ ℚ) at h
            rwa [← hEα, ← map_mul, Algebra.trace_eq_of_algEquiv E]
      | zero => simp
      | add v w _ _ hv hw => simpa [mul_add] using add_mem hv hw
      | smul z v _ hv =>
          simpa only [mul_smul_comm, map_zsmul] using (1 : Submodule ℤ ℚ).smul_mem z hv
    refine ⟨E t, hEL, fun h => ht0 (E.injective (by simpa using h)), ?_⟩
    have hnorm : Algebra.norm ℚ t = Algebra.norm ℚ (E t) :=
      (Algebra.norm_eq_of_algEquiv E t).symm
    have hk' : (k n : ℝ) = (m : ℝ) * (Algebra.norm ℚ t : ℝ) := by exact_mod_cast hk n
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hz' : (j n : ℝ) = (m : ℝ) / δ * x := by rw [hn]; exact hz
    rw [← hnorm]
    change x = δ * (Algebra.norm ℚ t : ℝ) ∨ x = -(δ * (Algebra.norm ℚ t : ℝ))
    dsimp only [j] at hz'
    split_ifs at hz' with hpos
    · left
      rw [hk'] at hz'
      field_simp at hz'
      nlinarith [hz']
    · right
      simp only [Int.cast_neg] at hz'
      rw [hk'] at hz'
      field_simp at hz'
      nlinarith [hz']
  · rintro ⟨s, hsL, hs0, hx | hx⟩
    · exact (signed_norm_values_accumulate D hD hs A B hB s hsL hs0 x
        (by simp [hx])).2
    · exact (signed_norm_values_accumulate D hD hs A B hB s hsL hs0 x
        (by simp [hx])).2

end D5.S3.Arith.QuadraticFields.QuadraticAccumulationClassification
