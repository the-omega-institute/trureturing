/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: Global half-line quadrature for the paired occupation Mellin mesh. -/

import D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
import D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteCenter
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails

/-! The positive mesh breaks into origin, regular, center, regular and far
blocks. The real cutoff for the tail bound is one cell below the continuous
partition point, so the absolute tail comparison does not omit any sample. -/

open Set MeasureTheory
open scoped BigOperators

namespace D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh

open OccupiedMellinInterior OccupiedMellinCutoffs
open OccupiedMellinDiscreteCenter OccupiedMellinDiscreteTails

private theorem abs_sum_div {f : ℕ → ℝ} (N : ℕ) {n : ℝ} (hn : 0 ≤ n) :
    |(∑ i ∈ Finset.range N, f i) / n| ≤ (∑ i ∈ Finset.range N, |f i|) / n := by
  rw [abs_div, abs_of_nonneg hn]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn

private theorem small_abs {β δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (hδ : δ ≤ 1 / 2) (n K : ℕ) (hn : 0 < n) (hk : (K : ℝ) / n ≤ δ) :
    |(∑ i ∈ Finset.range K, sample β (2 / (n : ℝ)) ((i + 1 : ℕ) / (n : ℝ))) / n| ≤
      32 * δ ^ (3 / 2 : ℝ) := by
  apply (abs_sum_div K (by positivity)).trans
  have h := discrete_mellin_tail_bounds.1 β (2 / (n : ℝ)) n K hβ hβ'
    (by positivity) hn (hk.trans hδ)
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hk (by norm_num)) (by norm_num))

private theorem center_abs {β δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2) (n K : ℕ) (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n)
    (hk : (K : ℝ) / n ≤ δ) :
    |(∑ i ∈ Finset.range (2 * K), sample β (2 / (n : ℝ)) (((n - K + i : ℕ) : ℝ) / n)) / n| ≤
      56 * δ ^ (1 / 4 : ℝ) + 16 * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  let f (j : ℕ) := |sample β (2 / (n : ℝ)) ((j : ℝ) / n)|
  let fL (j : ℕ) := |sample β (2 / (n : ℝ)) (1 - (((j + 1 : ℕ) : ℝ) / n))|
  let fR (j : ℕ) := |sample β (2 / (n : ℝ)) (1 + (((j + 1 : ℕ) : ℝ) / n))|
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : (∑ i ∈ Finset.range K, f (n - K + i)) = ∑ i ∈ Finset.range K, fL i := by
    rw [← Finset.sum_range_reflect (fun i => f (n - K + i)) K]
    apply Finset.sum_congr rfl
    intro i hi
    have hix := Finset.mem_range.mp hi
    have his : i + 1 ≤ n := by omega
    have hj : n - K + (K - 1 - i) = n - (i + 1) := by omega
    dsimp only [f, fL]
    rw [hj, Nat.cast_sub his, sub_div, div_self hn0.ne']
  have hR (i : ℕ) : f (n + (i + 1)) = fR i := by
    dsimp only [f, fR]
    rw [Nat.cast_add, add_div, div_self hn0.ne']
  have hcen : f n = |sample β (2 / (n : ℝ)) 1| := by simp [f, hn0.ne']
  have hr := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le K 1))
    (f := fR) (fun i _ _ => abs_nonneg _)
  have hnear := near_center_cutoff hβ hβ' hδ hδ' n K hn hk
  apply (abs_sum_div (2 * K) hn0.le).trans
  change (∑ i ∈ Finset.range (2 * K), f (n - K + i)) / n ≤ _
  rw [show 2 * K = K + K by omega, Finset.sum_range_add, hL]
  have he : (fun i : ℕ => f (n - K + (K + i))) = fun i => f (n + i) := by
    funext i
    exact congrArg f (by omega)
  simp only [he]
  nth_rw 2 [show K = K - 1 + 1 by omega]
  rw [Finset.sum_range_succ', Nat.add_zero, hcen]
  simp_rw [hR]
  apply le_trans _ hnear
  apply div_le_div_of_nonneg_right _ hn0.le
  change (∑ i ∈ Finset.range K, fL i) + ((∑ i ∈ Finset.range (K - 1), fR i) +
    |sample β (2 / (n : ℝ)) 1|) ≤ (∑ i ∈ Finset.range K, fL i) +
      |sample β (2 / (n : ℝ)) 1| + ∑ i ∈ Finset.range K, fR i
  linarith only [hr]

private theorem sum_prefix_partition (f : ℕ → ℝ) (n K M : ℕ)
    (hK : 0 < K) (hn : 2 * K ≤ n) (hM : n + K ≤ M) :
    (∑ i ∈ Finset.range (M - 1), f (i + 1)) =
      (∑ i ∈ Finset.range (K - 1), f (i + 1)) +
      (∑ i ∈ Finset.range (n - 2 * K), f (K + i)) +
      (∑ i ∈ Finset.range (2 * K), f (n - K + i)) +
      (∑ i ∈ Finset.range (M - (n + K)), f (n + K + i)) := by
  rw [show M - 1 = (((K - 1) + (n - 2 * K)) + (2 * K)) + (M - (n + K)) by omega,
    Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  have h1 (i : ℕ) : (K - 1 + i) + 1 = K + i := by omega
  have h2 (i : ℕ) : ((K - 1 + (n - 2 * K)) + i) + 1 = n - K + i := by omega
  have h3 (i : ℕ) : ((K - 1 + (n - 2 * K) + 2 * K) + i) + 1 = n + K + i := by omega
  simp only [h1,h2,h3]

private theorem map_interval {β : ℝ} {u v : ℝ} (hU : 0 < u) (huv : u ≤ v)
    (hside : v < 1 ∨ 1 < u) :
    IntervalIntegrable (sample β 0) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le huv]
  intro x hx
  have hxpos : 0 < x := hU.trans_le hx.1
  have h1 : 0 < 0 + (1 + x) := by linarith
  have h2 : 0 < 0+|1 - x| := by
    rw [zero_add, abs_pos]
    rcases hside with h | h <;> grind
  have hA := (Real.hasDerivAt_rpow_const (x := x) (p := -(3 / 2 : ℝ))
    (Or.inl hxpos.ne')).continuousAt
  have hB : ContinuousAt (fun x : ℝ => 0 + (1 + x)) x := by fun_prop
  have hC : ContinuousAt (fun x : ℝ => 0+|1 - x|) x := by fun_prop
  exact (hA.mul (((hB.rpow_const (Or.inl h1.ne')).add
    (hC.rpow_const (Or.inl h2.ne'))).sub continuousAt_const)).continuousWithinAt

private theorem sample_measurable (β a : ℝ) : Measurable (sample β a) := by
  unfold sample
  fun_prop

private theorem triangle_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a|+|b|+|c|+|d|+|e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

/-- Global error for the actual shift 2 / n, comparing the entire positive-index
mesh with the full positive half-line integral. At the two middle boundaries
the left endpoints belong to the block on their right; no sample is duplicated. -/
theorem global_mesh_error {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (n K M : ℕ) (hn : 0 < n) (hK : 0 < K) (hM : 2 * n < M)
    (hsize : (M : ℝ) / n ≤ ((K : ℝ) / n)⁻¹) :
    let δ := (K : ℝ) / n
    let R := ((M - 1 : ℕ) : ℝ) / n
    Summable (fun i : ℕ => |sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)|) ∧
    IntegrableOn (sample β 0) (Ioi 0) ∧
    |(∫ t in Ioi (0 : ℝ), sample β 0 t) -
        (∑' i : ℕ, sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)) / n| ≤
      64 * δ ^ (3 / 2 : ℝ) + 112 * δ ^ (1 / 4 : ℝ) + 16 * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
        (32 * δ ^ (-(17 / 4 : ℝ))) / n + 8 * R ^ (-(1 / 2 : ℝ)) := by
  let δ := (K : ℝ) / n
  let R := ((M - 1 : ℕ) : ℝ) / n
  let T := (M : ℝ) / n
  let F := sample β 0
  let f (i : ℕ) := sample β (2 / (n : ℝ)) ((i : ℝ) / n)
  change Summable (fun i : ℕ => |f (i + 1)|) ∧ IntegrableOn F (Ioi 0) ∧
    |(∫ t in Ioi (0 : ℝ), F t) - (∑' i : ℕ, f (i + 1)) / n| ≤ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hKδ : 0 < δ := div_pos (by exact_mod_cast hK) hn0
  have hT : (2 : ℝ) < T := by
    apply (lt_div_iff₀ hn0).2
    exact_mod_cast hM
  have hd2 : δ ≤ 1 / 2 := by
    have hinv : (2 : ℝ) < δ⁻¹ := hT.trans_le hsize
    have hlt := (lt_inv_comm₀ (by norm_num : (0 : ℝ) < 2) hKδ).mp hinv
    simpa only [one_div] using hlt.le
  have hK2 : 2 * K ≤ n := by
    have ht := (div_le_iff₀ hn0).mp hd2
    have hk2 : (2 : ℝ) * (K : ℝ) ≤ n := by linarith
    exact_mod_cast hk2
  have hd1 : δ ≤ 1 := by linarith
  have hKn : K ≤ n := by omega
  have hMKn : n + K ≤ M := by omega
  have h2R : 2 ≤ R := by
    apply (le_div_iff₀ hn0).2
    exact_mod_cast (show 2 * n ≤ M - 1 by omega)
  have hRT : R ≤ T :=
    div_le_div_of_nonneg_right (by exact_mod_cast (Nat.sub_le M 1)) hn0.le
  have h2T : 2 ≤ T := h2R.trans hRT
  have hL : ((n - K : ℕ) : ℝ) / n = 1 - δ := by
    rw [Nat.cast_sub hKn, sub_div, div_self hn0.ne']
  have hH : ((n + K : ℕ) : ℝ) / n = 1 + δ := by
    rw [Nat.cast_add, add_div, div_self hn0.ne']
  let A := ∫ t in (0 : ℝ)..δ, F t
  let B := ∫ t in δ..(1 - δ), F t
  let C := ∫ t in (1 - δ)..(1 + δ), F t
  let D := ∫ t in (1 + δ)..T, F t
  let E := ∫ t in Ioi T, F t
  let a := (∑ i ∈ Finset.range (K - 1), f (i + 1)) / (n : ℝ)
  let b := (∑ i ∈ Finset.range (n - 2 * K), f (K + i)) / (n : ℝ)
  let c := (∑ i ∈ Finset.range (2 * K), f (n - K + i)) / (n : ℝ)
  let d := (∑ i ∈ Finset.range (M - (n + K)), f (n + K + i)) / (n : ℝ)
  let e := (∑' i : ℕ, f (M + i)) / (n : ℝ)
  let H := (16 * δ ^ (-(17 / 4 : ℝ))) / (n : ℝ)
  have ha0 : 0 ≤ 2 / (n : ℝ) := by positivity
  obtain ⟨hIA, hA⟩ := mellin_cutoff_bounds.1 β 0 δ hβ hβ' le_rfl hKδ.le hd2
  obtain ⟨hIC, hC⟩ := mellin_cutoff_bounds.2.1 β δ hβ hβ' hKδ.le hd2
  obtain ⟨hIE, hE⟩ := mellin_cutoff_bounds.2.2.1 β 0 T hβ le_rfl h2T
  have hAA : |A| ≤ 32 * δ ^ (3 / 2 : ℝ) :=
    (intervalIntegral.abs_integral_le_integral_abs hKδ.le).trans
      (hA.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hKδ.le _)))
  have hCC : |C| ≤ 56 * δ ^ (1 / 4 : ℝ) :=
    (intervalIntegral.abs_integral_le_integral_abs (by linarith : 1 - δ ≤ 1 + δ)).trans
      (hC.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hKδ.le _)))
  have hEE : |E| ≤ 4 * R ^ (-(1 / 2 : ℝ)) := by
    have ha : |E| ≤ ∫ t in Ioi T, |F t| := by
      simpa only [E, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Ioi T)) F)
    apply (ha.trans hE).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R) hRT (by norm_num)) (by norm_num)
  have hKsmall : ((K - 1 : ℕ) : ℝ) / n ≤ δ :=
    div_le_div_of_nonneg_right (by exact_mod_cast (Nat.sub_le K 1)) hn0.le
  have haa : |a| ≤ 32 * δ ^ (3 / 2 : ℝ) :=
    small_abs hβ hβ' hd2 n (K - 1) hn hKsmall
  have hcc : |c| ≤ 56 * δ ^ (1 / 4 : ℝ) + 16 * (n : ℝ) ^ (-(1 / 4 : ℝ)) :=
    center_abs hβ hβ' hKδ.le hd2 n K hn hK hKn le_rfl
  obtain ⟨hTail', eBound⟩ := discrete_mellin_tail_bounds.2 β _ n (M - 1)
    hβ ha0 hn h2R
  have heq (i : ℕ) : M - 1 + i + 1 = M + i := by omega
  simp only [heq] at hTail' eBound
  change Summable (fun i : ℕ => |f (M + i)|) at hTail'
  have hee : |e| ≤ 4 * R ^ (-(1 / 2 : ℝ)) := by
    dsimp only [e]
    rw [abs_div, abs_of_nonneg hn0.le]
    have hNorm : Summable (fun i : ℕ => ‖f (M + i)‖) := by
      simpa only [Real.norm_eq_abs] using hTail'
    have hb : |∑' i : ℕ, f (M + i)| ≤ ∑' i : ℕ, |f (M + i)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hNorm
    exact (div_le_div_of_nonneg_right hb hn0.le).trans eBound
  have habs : Summable (fun i : ℕ => |f (i + 1)|) := by
    apply (summable_nat_add_iff (M - 1)).mp
    convert hTail' using 1
    funext i
    exact congrArg (fun j => |f j|) (by omega)
  have hfull : Summable (fun i : ℕ => f (i + 1)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hsum : (∑' i : ℕ, f (i + 1)) / n = a + b + c + d + e := by
    have h := Summable.sum_add_tsum_nat_add (M - 1) hfull
    have he' (i : ℕ) : i + (M - 1) + 1 = M + i := by omega
    simp only [he'] at h
    rw [← h, sum_prefix_partition f n K M hK hK2 hMKn]
    simp only [a, b, c, d, e, add_div]
  have hB : |B - b| ≤ H := by
    have hX : ((K + (n - 2 * K) : ℕ) : ℝ) / n = 1 - δ := by
      rw [show K + (n - 2 * K) = n - K by omega, hL]
    have hlen : ((n - 2 * K : ℕ) : ℝ) / n ≤ δ⁻¹ := by
      apply le_trans _ hsize
      exact div_le_div_of_nonneg_right (by exact_mod_cast (show n - 2 * K ≤ M by omega)) hn0.le
    have hb := normalized_lattice_interior_error n K (n - 2 * K) hn
      hβ hβ' hKδ hd1 le_rfl hlen (Or.inl hX.le)
    simp only [hX, one_div_mul_eq_div] at hb
    simpa only [B, b, F, f, H, Finset.sum_div] using hb
  have hD : |D - d| ≤ H := by
    have hX : (n + K + (M - (n + K)) : ℕ) = M := by omega
    have hlen : ((M - (n + K) : ℕ) : ℝ) / n ≤ δ⁻¹ :=
      (div_le_div_of_nonneg_right (by exact_mod_cast (Nat.sub_le M (n + K))) hn0.le).trans hsize
    have hd := normalized_lattice_interior_error n (n + K) (M - (n + K)) hn
      hβ hβ' hKδ hd1 (by rw [hH]; linarith) hlen (Or.inr hH.ge)
    simp only [hH, hX, one_div_mul_eq_div] at hd
    simpa only [D, d, F, f, H, T, Finset.sum_div] using hd
  have hIA' : IntervalIntegrable F volume 0 δ := by
    refine (IntervalIntegrable.intervalIntegrable_norm_iff
      (sample_measurable β 0).aestronglyMeasurable).mp ?_
    simpa only [Real.norm_eq_abs] using hIA
  have hIB' : IntervalIntegrable F volume δ (1 - δ) :=
    map_interval hKδ (by linarith) (Or.inl (by linarith))
  have hIC' : IntervalIntegrable F volume (1 - δ) (1 + δ) := by
    refine (IntervalIntegrable.intervalIntegrable_norm_iff
      (sample_measurable β 0).aestronglyMeasurable).mp ?_
    simpa only [Real.norm_eq_abs] using hIC
  have hID' : IntervalIntegrable F volume (1 + δ) T :=
    map_interval (by linarith) (by linarith) (Or.inr (by linarith))
  have hIE' : IntegrableOn F (Ioi T) := by
    change Integrable (fun s : ℝ => |sample β 0 s|) (volume.restrict (Ioi T)) at hIE
    refine (integrable_norm_iff (sample_measurable β 0).aestronglyMeasurable).mp ?_
    simpa only [Real.norm_eq_abs] using hIE
  have allI := ((hIA'.trans hIB').trans hIC').trans hID'
  have hpositiveI : IntegrableOn F (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show 0 ≤ T by linarith)]
    exact allI.1.union hIE'
  have hI : ∫ t in Ioi (0 : ℝ), F t = A + B + C + D + E := by
    rw [← intervalIntegral.integral_interval_add_Ioi' allI hIE',
      ← intervalIntegral.integral_add_adjacent_intervals ((hIA'.trans hIB').trans hIC') hID',
      ← intervalIntegral.integral_add_adjacent_intervals (hIA'.trans hIB') hIC',
      ← intervalIntegral.integral_add_adjacent_intervals hIA' hIB']
  refine ⟨habs, hpositiveI, ?_⟩
  rw [hI, hsum,
    show A + B + C + D + E - (a + b + c + d + e) =
      (A - a) + (B - b) + (C - c) + (D - d) + (E - e) by ring]
  apply (triangle_five (A - a) (B - b) (C - c) (D - d) (E - e)).trans
  have h₁ := (abs_sub _ _).trans (add_le_add hAA haa)
  have h₃ := (abs_sub _ _).trans (add_le_add hCC hcc)
  have h₅ := (abs_sub _ _).trans (add_le_add hEE hee)
  dsimp only [H] at hB hD
  change _ ≤ 64 * δ ^ (3 / 2 : ℝ) + 112 * δ ^ (1 / 4 : ℝ) + 16 * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
    (32 * δ ^ (-(17 / 4 : ℝ))) / n + 8 * R ^ (-(1 / 2 : ℝ))
  exact (add_le_add (add_le_add (add_le_add (add_le_add h₁ hB) h₃) hD) h₅).trans_eq (by ring)

end D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
