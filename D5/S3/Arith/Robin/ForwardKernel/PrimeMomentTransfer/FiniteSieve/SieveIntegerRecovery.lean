/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntegerRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntegerRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint rounding and smoothing recover uniform sharp sieve moments at integer scales. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveSmoothingError
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveSmoothGrid
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveProductStability

/-! sieveScale fixed mesh followed by a large integer scale recovers the sharp interval limits. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

def UniformIntegerSmall (k : ℕ)
    (F : ℕ+ → ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ) : Prop :=
  ∀ M B : ℝ, 1 ≤ M → 1 ≤ B → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ h : ℕ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log h →
  ∀ a b : Fin k → ℝ, admissible M a b → |F Q h a b| ≤ ε * momentScale k h

/-- A positive mesh can make any fixed multiple of its square root arbitrarily small. -/
private theorem sieve_choose_mesh (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ C * Real.sqrt δ < ε := by
  let t := ε / (2 * (C + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  refine ⟨min 1 (t ^ 2), lt_min zero_lt_one (sq_pos_of_pos ht), min_le_left _ _, ?_⟩
  have hs : Real.sqrt (min 1 (t ^ 2)) ≤ t := by
    calc
      _ ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = t := Real.sqrt_sq ht.le
  have he : (2 * (C + 1)) * t = ε := mul_div_cancel₀ ε (by positivity)
  have hCt : C * t < ε := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs hC).trans_lt hCt

/-- Sharp and rounded smooth intervals have bounded fourth norms and a small difference. -/
private theorem sieve_interval_grid_norm4_bound (hMS : MSFinite) (M B : ℝ)
    (hM : 1 ≤ M) (hB : 1 ≤ B) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ᶠ H : ℝ in atTop,
      ∀ Q : ℕ+, sieveDensity Q ≤ B * Real.log H → ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
      sieveNorm4 Q (normalizedIntervalSum Q H a b) ≤ K ∧
      sieveNorm4 Q (normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b))) ≤ K ∧
      sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x -
        normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x) ≤
          C * (Real.sqrt δ + H ^ (-(1/4) : ℝ)) := by
  obtain ⟨Ce, hCe, he⟩ := sieve_interval_endpoint_norm4_bound hMS B hB
  obtain ⟨Cs, hCs, hs⟩ := sieve_smoothing_norm4_bound hMS B hB
  let C := Ce + Cs
  let K := Ce * (Real.sqrt M + 1) + 2 * C + 1
  have hCe0 : 0 ≤ Ce := by linarith
  have hCs0 : 0 ≤ Cs := by linarith
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [mul_nonneg hCe0 (add_nonneg (Real.sqrt_nonneg M) zero_le_one)]
  refine ⟨C, K, hC, hK, ?_⟩
  filter_upwards [he, hs, eventually_ge_atTop (2 : ℝ)]
    with H heH hsH hH Q hP δ hδ hδ1 a b ha hab hb
  have ht0 : 0 ≤ H ^ (-(1/4) : ℝ) := Real.rpow_nonneg (by linarith) _
  have ht1 : H ^ (-(1/4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hδs : Real.sqrt δ ≤ 1 := by simpa using Real.sqrt_le_sqrt hδ1
  obtain ⟨_hga, _hgb, hra, hrab, hrb, hea, heb⟩ :=
    sieve_grid_rounding M δ (by linarith) hδ a b ha hab hb
  have hsharp : sieveNorm4 Q (normalizedIntervalSum Q H a b) ≤ Ce * (Real.sqrt M + 1) := by
    have h := heH Q hP a b 0 0 M ha hab le_rfl le_rfl
      (by linarith) (by rw [sub_zero, abs_of_nonneg ha]; linarith)
      (by rw [sub_zero, abs_of_nonneg (ha.trans hab)]; exact hb)
    have hz : normalizedIntervalSum Q H 0 0 = fun _ => 0 := by
      funext x
      simp [normalizedIntervalSum, sieveIntervalSum, points]
    simp only [neg_div] at h
    rw [hz] at h
    simp only [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ht1) hCe0)
  have herr : sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x -
      normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x) ≤
      C * (Real.sqrt δ + H ^ (-(1/4) : ℝ)) := by
    have hround := heH Q hP a b (sieveRoundDown δ a) (sieveRoundDown δ b) δ
      ha hab hra hrab hδ.le hea heb
    have hsmooth := hsH Q hP δ hδ hδ1 _ _ hra hrab
    simp only [neg_div] at hround hsmooth
    calc
      _ = sieveNorm4 Q (fun x => (normalizedIntervalSum Q H a b x - normalizedIntervalSum Q H (sieveRoundDown δ a) (sieveRoundDown δ b) x) +
          (normalizedIntervalSum Q H (sieveRoundDown δ a) (sieveRoundDown δ b) x -
            normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x)) := by
        congr 1; funext x; ring
      _ ≤ _ := sieve_norm4_add_le Q _ _
      _ ≤ Ce * (Real.sqrt δ + H ^ (-(1/4) : ℝ)) +
          Cs * (Real.sqrt δ + H ^ (-(1/4) : ℝ)) := add_le_add hround hsmooth
      _ = _ := by dsimp [C]; ring
  have herr2 : sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x -
      normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x) ≤ 2 * C :=
    herr.trans (by
      have hh := mul_le_mul_of_nonneg_left (add_le_add hδs ht1) hC0
      linarith)
  have hsm : sieveNorm4 Q (normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b))) ≤
      Ce * (Real.sqrt M + 1) + 2 * C := by
    calc
      _ = sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x - (normalizedIntervalSum Q H a b x -
          normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x)) := by
        congr 1; funext x; ring
      _ ≤ sieveNorm4 Q (normalizedIntervalSum Q H a b) + sieveNorm4 Q (fun x => normalizedIntervalSum Q H a b x -
          normalizedWeightedSum Q H (smoothedInterval δ hδ (sieveRoundDown δ a) (sieveRoundDown δ b)) x) := by
        simp only [sieve_norm4_eq_lpNorm]
        exact lpNorm_sub_le (sieve_memLp_four Q _) (by norm_num)
      _ ≤ _ := add_le_add hsharp herr2
  exact ⟨hsharp.trans (by dsimp [K]; linarith),
    hsm.trans (by dsimp [K]; linarith), herr⟩

/-- The sharp cubic sieve moment is uniformly negligible at integer scales. -/
theorem sieve_integer_third (hMS : MSFinite) (hK : KuperbergSmoothed) :
    UniformIntegerSmall 3 sieveIntervalMoment := by
  intro M B hM hB ε hε
  obtain ⟨C, K, hC, hK1, hbound⟩ := sieve_interval_grid_norm4_bound hMS M B hM hB
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ 3 * C * K ^ 2 := by positivity
  obtain ⟨δ, hδ, hδ1, hmesh⟩ := sieve_choose_mesh (3 * C * K ^ 2) (ε / 4) hL0
    (by positivity)
  have hcast : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun h : ℕ => (3 * C * K ^ 2) * (h : ℝ) ^ (-(1/4) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, neg_div] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hcast).const_mul
        (3 * C * K ^ 2)
  filter_upwards [hcast.eventually hbound,
    sieve_grid_smoothed_third hK M B δ hM hB hδ (ε / 2) (by positivity),
    hdecay.eventually_le_const (by positivity : (0 : ℝ) < ε / 4),
    eventually_ge_atTop (2 : ℕ)] with h hb hg he hh Q hQ hP a b hab
  let ar : Fin 3 → ℝ := fun i => sieveRoundDown δ (a i)
  let br : Fin 3 → ℝ := fun i => sieveRoundDown δ (b i)
  have hr (i : Fin 3) := sieve_grid_rounding M δ (by linarith) hδ
    (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  have had : admissible M ar br := by
    intro i
    obtain ⟨_, _, ha, hab, hb, _, _⟩ := hr i
    exact ⟨ha, hab, hb⟩
  have hmem : ∀ i, ar i ∈ sieveEndpointGrid M δ ∧ br i ∈ sieveEndpointGrid M δ :=
    fun i => ⟨(hr i).1, (hr i).2.1⟩
  let F : Fin 3 → ZMod (Q : ℕ) → ℝ := fun i => normalizedIntervalSum Q h (a i) (b i)
  let G : Fin 3 → ZMod (Q : ℕ) → ℝ := fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (ar i) (br i))
  have hi (i : Fin 3) := hb Q hP δ hδ hδ1
    (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  have hD : 0 ≤ C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ)) :=
    mul_nonneg hC0 (add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hreplace := sieve_product_moment_replacement Q 3 (by norm_num) (by norm_num)
    F G K (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) hK0 hD
    (fun i => (hi i).1) (fun i => (hi i).2.1) (fun i => (hi i).2.2)
  have halgebra : (3 : ℝ) * (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) * K ^ 2 =
      (3 * C * K ^ 2) * Real.sqrt δ + (3 * C * K ^ 2) * (h : ℝ) ^ (-(1/4) : ℝ) := by
    ring
  norm_num only [Nat.cast_ofNat] at hreplace
  rw [halgebra] at hreplace
  have hsmooth : |sieveProductMoment Q G| ≤ ε / 2 := hg Q hQ hP ar br had hmem
  have hnormalized : |sieveProductMoment Q F| ≤ ε := by
    have htriangle : |sieveProductMoment Q F| ≤ |sieveProductMoment Q F - sieveProductMoment Q G| + |sieveProductMoment Q G| := by
      simpa only [sub_add_cancel] using abs_add_le (sieveProductMoment Q F - sieveProductMoment Q G) (sieveProductMoment Q G)
    linarith
  have hraw : sieveProductMoment Q F = sieveIntervalMoment Q h a b / sieveScale h ^ 3 := by
    change sieveProductMoment Q (fun i x => sieveIntervalSum Q h (a i) (b i) x / sieveScale h) = _
    rw [sieve_moment_div_scale, ← sieve_interval_moment_eq_product_moment]
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hA := (sieve_scale_power h hhR 3).1
  rw [hraw, abs_div, abs_of_pos (pow_pos hA 3)] at hnormalized
  have hfinal := (div_le_iff₀ (pow_pos hA 3)).mp hnormalized
  rwa [(sieve_scale_power h hhR 3).2] at hfinal

/-- The sharp fourth sieve Wick defect is uniformly negligible at integer scales. -/
theorem sieve_integer_fourth (hMS : MSFinite) (hK : KuperbergSmoothed) :
    UniformIntegerSmall 4 sieveIntervalWickDefect := by
  intro M B hM hB ε hε
  obtain ⟨C, K, hC, hK1, hbound⟩ := sieve_interval_grid_norm4_bound hMS M B hM hB
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ 16 * C * K ^ 3 := by positivity
  obtain ⟨δ, hδ, hδ1, hmesh⟩ := sieve_choose_mesh (16 * C * K ^ 3) (ε / 4) hL0
    (by positivity)
  have hcast : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun h : ℕ => (16 * C * K ^ 3) * (h : ℝ) ^ (-(1/4) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, neg_div] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp hcast).const_mul
        (16 * C * K ^ 3)
  filter_upwards [hcast.eventually hbound,
    sieve_grid_smoothed_fourth hK M B δ hM hB hδ (ε / 2) (by positivity),
    hdecay.eventually_le_const (by positivity : (0 : ℝ) < ε / 4),
    eventually_ge_atTop (2 : ℕ)] with h hb hg he hh Q hQ hP a b hab
  let ar : Fin 4 → ℝ := fun i => sieveRoundDown δ (a i)
  let br : Fin 4 → ℝ := fun i => sieveRoundDown δ (b i)
  have hr (i : Fin 4) := sieve_grid_rounding M δ (by linarith) hδ
    (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  have had : admissible M ar br := by
    intro i
    obtain ⟨_, _, ha, hab, hb, _, _⟩ := hr i
    exact ⟨ha, hab, hb⟩
  have hmem : ∀ i, ar i ∈ sieveEndpointGrid M δ ∧ br i ∈ sieveEndpointGrid M δ :=
    fun i => ⟨(hr i).1, (hr i).2.1⟩
  let F : Fin 4 → ZMod (Q : ℕ) → ℝ := fun i => normalizedIntervalSum Q h (a i) (b i)
  let G : Fin 4 → ZMod (Q : ℕ) → ℝ := fun i => normalizedWeightedSum Q h (smoothedInterval δ hδ (ar i) (br i))
  have hi (i : Fin 4) := hb Q hP δ hδ hδ1
    (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
  have hD : 0 ≤ C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ)) :=
    mul_nonneg hC0 (add_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hmoment := sieve_product_moment_replacement Q 4 (by norm_num) (by norm_num)
    F G K (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) hK0 hD
    (fun i => (hi i).1) (fun i => (hi i).2.1) (fun i => (hi i).2.2)
  have hpair := sieve_wick_pairing_replacement Q F G K (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) hK0 hD
    (fun i => (hi i).1) (fun i => (hi i).2.1) (fun i => (hi i).2.2)
  norm_num only [Nat.cast_ofNat] at hmoment
  have halgebra : (4 : ℝ) * (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) * K ^ 3 +
      12 * (C * (Real.sqrt δ + (h : ℝ) ^ (-(1/4) : ℝ))) * K ^ 3 =
      (16 * C * K ^ 3) * Real.sqrt δ + (16 * C * K ^ 3) * (h : ℝ) ^ (-(1/4) : ℝ) := by
    ring
  have hsmooth : |sieveWickDefect Q G| ≤ ε / 2 := hg Q hQ hP ar br had hmem
  have hnormalized : |sieveWickDefect Q F| ≤ ε := by
    have hid : sieveWickDefect Q F = (sieveProductMoment Q F - sieveProductMoment Q G) -
        (sieveWickPairing Q F - sieveWickPairing Q G) + sieveWickDefect Q G := by
      unfold sieveWickDefect
      ring
    have htriangle : |sieveWickDefect Q F| ≤
        |sieveProductMoment Q F - sieveProductMoment Q G| + |sieveWickPairing Q F - sieveWickPairing Q G| + |sieveWickDefect Q G| := by
      calc
        _ = |(sieveProductMoment Q F - sieveProductMoment Q G) - (sieveWickPairing Q F - sieveWickPairing Q G) + sieveWickDefect Q G| :=
          congrArg abs hid
        _ ≤ |(sieveProductMoment Q F - sieveProductMoment Q G) - (sieveWickPairing Q F - sieveWickPairing Q G)| + |sieveWickDefect Q G| :=
          abs_add_le _ _
        _ ≤ _ := add_le_add (abs_sub _ _) le_rfl
    have hsum := add_le_add (add_le_add hmoment hpair) hsmooth
    rw [halgebra] at hsum
    exact htriangle.trans (by linarith only [hsum, hmesh, he])
  have hraw : sieveWickDefect Q F = sieveIntervalWickDefect Q h a b / sieveScale h ^ 4 := by
    change sieveWickDefect Q (fun i x => sieveIntervalSum Q h (a i) (b i) x / sieveScale h) = _
    rw [sieve_defect_div_scale, ← sieve_interval_defect_eq_wick_defect]
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hA := (sieve_scale_power h hhR 4).1
  rw [hraw, abs_div, abs_of_pos (pow_pos hA 4)] at hnormalized
  have hfinal := (div_le_iff₀ (pow_pos hA 4)).mp hnormalized
  rwa [(sieve_scale_power h hhR 4).2] at hfinal


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
