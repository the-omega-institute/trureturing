/- GID: D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed floor partition and Abel summation for the fractional Mellin integral. -/

/-
Source port: jrgochan/prime, commit ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2.
Copyright 2026 Jason Robert Gochanour. Licensed under Apache-2.0.
The complete upstream license is retained in NymanMellinHelpers.lean.
Modified by trureturing, 2026-09-08: trimmed imports and unused declarations,
routed namespaces, current-pin API adaptation, exact prerequisite reuse.
Retirement: when this repository's installed future mathlib pin contains an
equivalent declaration, use it directly in new content; any frozen port remains
subject to the repository's frozen-content migration rules.
-/

import D5.S3.Weil.ZetaPntBounds.NymanMellinHelpers

noncomputable section
open Complex Real MeasureTheory Set Filter Topology
open D5.S3.Weil.ZetaPntBounds.NymanMellinHelpers
namespace D5.S3.Weil.ZetaPntBounds.NymanMellinFloorSeries

/-- On Ioc(k/(n+1), k/n), ⌊k/t⌋ = n (generalized floor). -/
private lemma floor_div_eq_on_Ioc_gen (k : ℕ) (n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (t : ℝ) (ht_lo : (k : ℝ)/((n : ℝ)+1) < t) (ht_hi : t ≤ (k : ℝ)/(n : ℝ)) :
    ⌊(k : ℝ)/t⌋ = (n : ℤ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have ht_pos : (0 : ℝ) < t := by linarith [div_pos hk_pos hn1_pos]
  rw [Int.floor_eq_iff]
  constructor
  · rw [Int.cast_natCast, le_div_iff₀ ht_pos]
    nlinarith [mul_div_cancel₀ (k : ℝ) (ne_of_gt hn_pos)]
  · rw [Int.cast_natCast, div_lt_iff₀ ht_pos]
    nlinarith [mul_div_cancel₀ (k : ℝ) (ne_of_gt hn1_pos)]

/-- ∫₀¹ t^{s-1}·(k/t) dt = k/(s-1) for Re(s) > 1. -/
private lemma mellin_div_integral (s : ℂ) (hs : 1 < s.re) (k : ℕ) (_hk : 1 ≤ k) :
    ∫ t in Set.Ioc (0:ℝ) 1, (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ)) =
    (↑k : ℂ) / (s - 1) := by
  -- Step 1: Replace integrand with k · t^{s-2}
  have h_eq : Set.EqOn
      (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ)))
      (fun t : ℝ => (↑k : ℂ) * (↑t : ℂ) ^ (s - 2))
      (Set.Ioc (0:ℝ) 1) := by
    intro t ⟨ht_lo, _⟩
    have ht' : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_lo)
    show (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ)) = (↑k : ℂ) * (↑t : ℂ) ^ (s - 2)
    rw [show (s - 2 : ℂ) = (s - 1) + (-1) from by ring, cpow_add _ _ ht',
        Complex.cpow_neg_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc h_eq]
  -- Step 2: Pull out k
  rw [show ∫ x in Set.Ioc (0:ℝ) 1, (↑k : ℂ) * (↑x : ℂ) ^ (s - 2) =
      (↑k : ℂ) * ∫ x in Set.Ioc (0:ℝ) 1, (↑x : ℂ) ^ (s - 2) from integral_const_mul _ _]
  -- Step 3: Evaluate ∫ t^{s-2} = 1/(s-1)
  rw [← intervalIntegral.integral_of_le (le_of_lt (by linarith : (0:ℝ) < 1))]
  rw [integral_cpow (Or.inl (show -1 < (s - 2).re from by simp [sub_re]; linarith))]
  rw [show s - 2 + 1 = s - 1 from by ring]
  rw [ofReal_one, one_cpow, ofReal_zero,
      zero_cpow (show s - 1 ≠ 0 from by
        intro h; have := congr_arg re h; simp [sub_re, one_re] at this; linarith)]
  rw [sub_zero, mul_one_div]

/-- ⋃_N Ioc(k/(N+1), 1) = Ioc(0, 1). -/
private lemma iUnion_Ioc_gen (k : ℕ) (hk : 1 ≤ k) :
    ⋃ N : ℕ, Ioc ((k:ℝ)/((N:ℝ)+1)) 1 = Ioc (0:ℝ) 1 := by
  ext x; simp only [mem_iUnion, mem_Ioc]; constructor
  · rintro ⟨N, hlo, hhi⟩
    exact ⟨by linarith [show (0:ℝ) < (k:ℝ)/((N:ℝ)+1) from by positivity], hhi⟩
  · rintro ⟨hx, hx1⟩
    obtain ⟨N, hN⟩ := exists_nat_gt ((k:ℝ)/x - 1)
    refine ⟨N, ?_, hx1⟩
    have hN1 : (0:ℝ) < (N:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [div_lt_iff₀ hN1]
    linarith [(div_lt_iff₀ hx).mp (by linarith : (k:ℝ)/x < (N:ℝ)+1)]

/-- The sequence Ioc(k/(N+1), 1) is monotone. -/
private lemma mono_Ioc_gen (k : ℕ) (hk : 1 ≤ k) :
    Monotone (fun N : ℕ => Ioc ((k:ℝ)/((N:ℝ)+1)) (1:ℝ)) := by
  intro m n hmn; apply Ioc_subset_Ioc_left
  apply div_le_div_of_nonneg_left
    (show (0:ℝ) ≤ (k:ℝ) from by positivity)
    (show (0:ℝ) < (m:ℝ)+1 from by positivity)
    (show (m:ℝ)+1 ≤ (n:ℝ)+1 from by
      have : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
      linarith)

/-- Per-piece integral: ∫ t^{s-1}·n on Ioc(k/(n+1), k/n). -/
private lemma piece_setIntegral_gen (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ t in Ioc ((k:ℝ)/((n:ℝ)+1)) ((k:ℝ)/(n:ℝ)),
      (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ) =
    (↑n : ℂ) * ((↑((k:ℝ)/(n:ℝ)) : ℂ) ^ s - (↑((k:ℝ)/((n:ℝ)+1)) : ℂ) ^ s) / s := by
  -- Replace ⌊k/t⌋ with n on this piece
  have h_eq : Set.EqOn
      (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ))
      (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * (↑n : ℂ))
      (Ioc ((k:ℝ)/((n:ℝ)+1)) ((k:ℝ)/(n:ℝ))) := by
    intro t ⟨ht_lo, ht_hi⟩
    have := floor_div_eq_on_Ioc_gen k n hk hn t ht_lo ht_hi
    simp only [this]; push_cast; norm_cast
  rw [setIntegral_congr_fun measurableSet_Ioc h_eq]
  have hab : (k:ℝ)/((n:ℝ)+1) ≤ (k:ℝ)/(n:ℝ) :=
    div_le_div_of_nonneg_left (show (0:ℝ) ≤ k from by positivity) (by positivity)
      (by linarith [show (0:ℝ) < (n:ℝ) from by positivity])
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => mul_comm _ _)]
  rw [show ∫ t in Ioc ((k:ℝ)/((n:ℝ)+1)) ((k:ℝ)/(n:ℝ)), (↑n : ℂ) * (↑t : ℂ) ^ (s - 1) =
      (↑n : ℂ) * ∫ t in Ioc ((k:ℝ)/((n:ℝ)+1)) ((k:ℝ)/(n:ℝ)), (↑t : ℂ) ^ (s - 1)
    from integral_const_mul _ _]
  rw [← intervalIntegral.integral_of_le hab]
  rw [integral_cpow (Or.inl (by simp [sub_re]; linarith))]
  rw [show s - 1 + 1 = s from by ring]; ring

/-- Generalized integrability for floor_div on Ioc(0,1). -/
private lemma floor_div_integrableOn (s : ℂ) (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ))
      (Ioc 0 1) volume := by
  have hg : IntegrableOn (fun x : ℝ => (↑x : ℂ) ^ (s - 2)) (Ioc 0 1) volume := by
    have h := @intervalIntegral.intervalIntegrable_cpow' 0 1 (s-2) (by simp [sub_re]; linarith)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1)] at h
  exact Integrable.mono (hg.norm.const_mul (↑k : ℝ))
    (by apply AEStronglyMeasurable.mul
        · exact (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
            (fun x hx => by left; simp [ofReal_re]; exact hx) |>.mono Ioc_subset_Ioi_self
            ).aestronglyMeasurable measurableSet_Ioc
        · exact ((Measurable.of_discrete (α := ℤ)).comp
            ((measurable_const.div measurable_id).floor)).aestronglyMeasurable.restrict)
    (by apply ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self
        apply (ae_restrict_mem measurableSet_Ioi).mono
        intro t ht; rw [mem_Ioi] at ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht]
        simp only [sub_re, one_re]
        have h_nn : (0 : ℤ) ≤ ⌊(k:ℝ)/t⌋ := Int.floor_nonneg.mpr (div_nonneg (by positivity) ht.le)
        rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast h_nn)]
        calc t ^ (s.re - 1) * (⌊(k:ℝ)/t⌋ : ℝ)
            ≤ t ^ (s.re - 1) * ((k:ℝ)/t) := mul_le_mul_of_nonneg_left (Int.floor_le _) (rpow_nonneg ht.le _)
          _ = (↑k : ℝ) * t ^ (s.re - 2) := by
              rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_eq_mul_inv, ← rpow_neg_one t,
                  ← rpow_add ht]; congr 1; ring_nf
          _ ≤ ‖(↑k : ℝ) * t ^ (s.re - 2)‖ := le_norm_self _
          _ = _ := by simp)

/-- N·(k/(N+1))^s → 0 as N → ∞ for Re(s) > 1. -/
private lemma tail_vanishes_gen (s : ℂ) (hs : 1 < s.re) (k : ℕ) (_hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (↑N : ℂ) * (↑((k:ℝ)/((N:ℝ)+1)) : ℂ) ^ s) atTop (nhds 0) := by
  have h_rewrite : ∀ N : ℕ,
      (↑N : ℂ) * (↑((k:ℝ)/((N:ℝ)+1)) : ℂ) ^ s =
      (↑k : ℂ) ^ s * ((↑N : ℂ) * (↑(1/((N:ℝ)+1)) : ℂ) ^ s) := by
    intro N
    have hk_nn : (0:ℝ) ≤ (k:ℝ) := by positivity
    have hN1_nn : (0:ℝ) ≤ 1/((N:ℝ)+1) := by positivity
    rw [show (k:ℝ)/((N:ℝ)+1) = (k:ℝ) * (1/((N:ℝ)+1)) from by ring,
        Complex.ofReal_mul (k:ℝ) (1/((N:ℝ)+1)),
        mul_cpow_ofReal_nonneg hk_nn hN1_nn]
    push_cast; rw [mul_comm (↑N : ℂ), mul_assoc]; congr 1; exact mul_comm _ _
  rw [show (0:ℂ) = (↑k : ℂ) ^ s * 0 from by simp]
  exact (tail_vanishes s hs).const_mul _ |>.congr (fun N => (h_rewrite N).symm)

/-- Generalized Abel summation: ∑_{i<M} (k+i)·[a_{k+i} - a_{k+i+1}]
    = k·a_k + ∑_{i<M} a_{k+i+1} - (k+M)·a_{k+M+1} - a_k.
    Actually we want: = ∑_{i<M} a_{k+i+1} + k·a_k - (k+M)·a_{k+M+1}
    Simplified: sums ∑_{i=0}^{M-1} (k+i)(a_{k+i} - a_{k+i+1})
    = k·a_k + ∑_{i=1}^{M-1} a_{k+i} - (k+M-1)·a_{k+M}
    We need to match: k + k^s·∑n^{-s} - N·tail form. -/
private lemma abel_sum_gen (a : ℕ → ℂ) (k : ℕ) : ∀ M : ℕ,
    ∑ i ∈ Finset.range M, (↑(k + i) : ℂ) * (a (k + i) - a (k + i + 1)) =
    ∑ i ∈ Finset.range M, a (k + i + 1) + (↑k : ℂ) * a k -
      (↑(k + M) : ℂ) * a (k + M) := by
  intro M; induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast; ring_nf

/-- The partial Abel sum connects to partial ζ sums for the generalized k-floor. -/
private lemma partial_sum_gen (s : ℂ) (k : ℕ) (M : ℕ) :
    ∑ i ∈ Finset.range (M+1),
      (↑(k + i) : ℂ) * ((↑((k:ℝ)/(↑(k+i):ℝ)) : ℂ) ^ s -
        (↑((k:ℝ)/(↑(k+i)+1)) : ℂ) ^ s) / s =
    (∑ i ∈ Finset.range (M+1), (↑((k:ℝ)/(↑(k+i)+1)) : ℂ) ^ s +
      (↑k : ℂ) * (↑((k:ℝ)/(↑k:ℝ)) : ℂ) ^ s -
      (↑(k + (M+1)) : ℂ) * (↑((k:ℝ)/(↑(k+(M+1)):ℝ)) : ℂ) ^ s) / s := by
  have hab := abel_sum_gen (fun n => (↑((k:ℝ)/(↑n:ℝ)) : ℂ) ^ s) k (M+1)
  rw [← Finset.sum_div]; congr 1
  convert hab using 2 <;> simp [Nat.cast_add, Nat.cast_one]

/-- Convert the Abel summation numerator to the ζ-sum form.
    ∑_{i<M+1} (k/(k+i+1))^s + k - (k+M+1)·(k/(k+M+1))^s
    = k + k^s · ∑_{n ∈ Icc(k+1,k+M)} n^{-s} - (k+M)·(k/(k+M+1))^s

    Proof sketch: Apply (k/n)^s = k^s·n^{-s}, reindex range→Icc,
    split off last term, simplify (k+M+1-1) = k+M. -/
private lemma abel_form_to_zeta_form (s : ℂ) (k : ℕ) (hk : 1 ≤ k) (M : ℕ) :
    ∑ i ∈ Finset.range (M+1), (↑((k:ℝ)/(↑(k+i)+1)) : ℂ) ^ s +
      (↑k : ℂ) -
      (↑(k + (M+1)) : ℂ) * (↑((k:ℝ)/(↑(k+(M+1)):ℝ)) : ℂ) ^ s =
    (↑k : ℂ) + (↑k : ℂ) ^ s *
      (∑ n ∈ Finset.Icc (k+1) (k+M), ((↑(n : ℕ) : ℂ) ^ (-s))) -
      (↑(k + M) : ℂ) * (↑((k:ℝ)/(↑(k+M)+1)) : ℂ) ^ s := by
  -- Step 1: Normalize ↑(k+i)+1 to ↑(k+i+1) and ↑(k+(M+1)) to ↑(k+M+1)
  simp_rw [show ∀ i : ℕ, (↑(k+i) : ℝ) + 1 = ↑(k+i+1) from fun i => by push_cast; ring]
  rw [show k + (M + 1) = k + M + 1 from by omega]
  -- Step 2: Apply (k/n)^s = k^s · n^{-s} via ofReal_div_cpow
  -- First convert the sum
  have h_sum : ∀ i ∈ Finset.range (M+1),
      (↑((k:ℝ)/↑(k+i+1)) : ℂ) ^ s = (↑(k:ℝ) : ℂ) ^ s * (↑(k+i+1:ℕ) : ℂ) ^ (-s) :=
    fun i _ => ofReal_div_cpow k (k+i+1) hk (by omega) s
  rw [Finset.sum_congr rfl h_sum]
  -- Also convert the tail term
  rw [ofReal_div_cpow k (k+M+1) hk (by omega) s]
  -- Step 3: Factor k^s from the sum
  rw [← Finset.mul_sum]
  -- Step 4: Reindex range(M+1) → Icc(k+1, k+M+1)
  have h_reindex : ∑ i ∈ Finset.range (M+1), (↑(k+i+1 : ℕ) : ℂ) ^ (-s) =
      ∑ n ∈ Finset.Icc (k+1) (k+M+1), (↑n : ℂ) ^ (-s) := by
    apply Finset.sum_bij' (fun i _ => k + i + 1) (fun n _ => n - k - 1)
      (fun i hi => by simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega)
      (fun n hn => by simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega)
      (fun i _ => by omega)
      (fun n hn => by simp only [Finset.mem_Icc] at hn; omega)
      (fun i _ => by congr 1)
  rw [h_reindex]
  -- Step 5: Split off last term: Icc(k+1, k+M+1) = Icc(k+1, k+M) ∪ {k+M+1}
  rw [show Finset.Icc (k+1) (k+M+1) = Finset.Icc (k+1) (k+M) ∪ {k+M+1} from by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]; omega]
  rw [Finset.sum_union (by simp [Finset.disjoint_singleton_right])]
  simp only [Finset.sum_singleton]
  -- Step 6: Normalize casts and ring
  push_cast
  ring

/-- Inductive decomposition: ∫_{Ioc(k/(k+M+1), 1)} f = ∑_{i<M+1} piece(k, k+i).
    By induction on M, splitting Ioc at each step and applying piece_setIntegral_gen. -/
private lemma integral_decomp_gen (s : ℂ) (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℕ,
    ∫ t in Set.Ioc ((k:ℝ)/(↑(k+M)+1)) 1,
      (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ)
    = ∑ i ∈ Finset.range (M+1),
        (↑(k + i) : ℂ) * ((↑((k:ℝ)/(↑(k+i):ℝ)) : ℂ) ^ s -
          (↑((k:ℝ)/(↑(k+i)+1)) : ℂ) ^ s) / s := by
  intro M; induction M with
  | zero =>
    have hk0 : k + 0 = k := Nat.add_zero k
    rw [show (0:ℕ) + 1 = 1 from rfl, hk0]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.add_zero]
    have h1 : Set.Ioc ((k:ℝ)/((k:ℝ)+1)) (1:ℝ) = Set.Ioc ((k:ℝ)/((k:ℝ)+1)) ((k:ℝ)/(k:ℝ)) := by
      rw [div_self (by positivity : (k:ℝ) ≠ 0)]
    rw [h1]
    exact piece_setIntegral_gen k k hk hk s hs
  | succ m ih =>
    -- Simplify k + (m+1) = k + m + 1 at Nat level
    rw [show k + (m + 1) = k + m + 1 from by omega]
    -- Set up interval splitting
    have hk_m1 : (0:ℝ) < ↑(k+m)+1 := by positivity
    have hk_m2 : (0:ℝ) < ↑(k+m+1)+1 := by positivity
    have h_le : (k:ℝ)/(↑(k+m+1)+1) ≤ (k:ℝ)/(↑(k+m)+1) :=
      div_le_div_of_nonneg_left (by positivity) hk_m1 (by push_cast; linarith)
    have h_le1 : (k:ℝ)/(↑(k+m)+1) ≤ 1 := by
      rw [div_le_one hk_m1]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
    have h_union : Set.Ioc ((k:ℝ)/(↑(k+m+1)+1)) ((k:ℝ)/(↑(k+m)+1)) ∪
        Set.Ioc ((k:ℝ)/(↑(k+m)+1)) 1 = Set.Ioc ((k:ℝ)/(↑(k+m+1)+1)) 1 :=
      Set.Ioc_union_Ioc_eq_Ioc h_le h_le1
    have h_disj : Disjoint (Set.Ioc ((k:ℝ)/(↑(k+m+1)+1)) ((k:ℝ)/(↑(k+m)+1)))
        (Set.Ioc ((k:ℝ)/(↑(k+m)+1)) 1) := Set.Ioc_disjoint_Ioc_of_le le_rfl
    have h_int_full := floor_div_integrableOn s hs k hk
    have h_int_piece : IntegrableOn (fun (t : ℝ) => (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ))
        (Set.Ioc ((k:ℝ)/(↑(k+m+1)+1)) ((k:ℝ)/(↑(k+m)+1))) volume :=
      h_int_full.mono_set (fun x ⟨hlo, hhi⟩ =>
        ⟨by linarith [div_pos (by positivity : (0:ℝ) < k) hk_m2], by linarith⟩)
    have h_int_rest : IntegrableOn (fun (t : ℝ) => (↑t : ℂ) ^ (s - 1) * (↑(⌊(k:ℝ)/t⌋) : ℂ))
        (Set.Ioc ((k:ℝ)/(↑(k+m)+1)) 1) volume :=
      h_int_full.mono_set (fun x ⟨hlo, hhi⟩ =>
        ⟨by linarith [div_pos (by positivity : (0:ℝ) < k) hk_m1], hhi⟩)
    -- Split the integral
    rw [← h_union, setIntegral_union h_disj measurableSet_Ioc h_int_piece h_int_rest]
    rw [ih]
    -- Goal: ∫ piece + ∑ range(m+1) = ∑ range((m+1)+1)
    conv_rhs => rw [Finset.sum_range_succ]
    -- Goal: ∫ piece + ∑ range(m+1) = ∑ range(m+1) + last
    rw [add_comm (∫ _ in _, _)]
    congr 1
    -- piece: ∫ Ioc(k/(↑(k+m+1)+1), k/(↑(k+m)+1)) = ↑(k+(m+1)) * ...
    -- piece_setIntegral_gen: ∫ Ioc(k/(↑(k+m+1)+1), k/↑(k+m+1)) = ↑(k+m+1) * ...
    -- These are the same since ↑(k+m)+1 = ↑(k+m+1)
    have h_n_cast : (↑(k+m) : ℝ) + 1 = ↑(k+m+1) := by push_cast; ring
    rw [h_n_cast]
    exact piece_setIntegral_gen k (k + m + 1) hk (by omega) s hs

/-- ∫₀¹ t^{s-1}·⌊k/t⌋ dt = k/s + (k^s/s)·(ζ(s) - ∑_{m<k}(m+1)^{-s}). -/
private lemma floor_div_mellin (s : ℂ) (hs : 1 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in Set.Ioc (0:ℝ) 1,
      (↑t : ℂ) ^ (s - 1) * (↑(⌊(k : ℝ)/t⌋) : ℂ) =
    (↑k : ℂ) / s + ((k : ℂ) ^ s / s) *
      (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s)))) := by
  -- Monotone convergence: partial integrals → full integral
  let f : ℝ → ℂ := fun t => (↑t : ℂ) ^ (s - 1) * (↑(⌊(k : ℝ)/t⌋) : ℂ)
  have h_tendsto_int : Tendsto
      (fun N : ℕ => ∫ t in Ioc ((k:ℝ)/((N:ℝ)+1)) 1, f t)
      atTop (nhds (∫ t in Ioc 0 1, f t)) := by
    rw [← iUnion_Ioc_gen k hk]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) (mono_Ioc_gen k hk)
      (iUnion_Ioc_gen k hk ▸ floor_div_integrableOn s hs k hk)
  show ∫ t in Set.Ioc 0 1, f t =
    (↑k : ℂ) / s + ((k : ℂ) ^ s / s) *
      (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))))
  -- The partial integrals also tend to the target (via Abel sums)
  have h_tendsto_target : Tendsto
      (fun N : ℕ => ∫ t in Ioc ((k:ℝ)/((N:ℝ)+1)) 1, f t)
      atTop (nhds ((↑k : ℂ) / s + ((k : ℂ) ^ s / s) *
        (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s)))))) := by
    -- Step 1: Partial integrals = Abel sum formula (induction)
    -- After inductive decomposition + Abel summation, each partial integral equals:
    -- [(↑k) + (↑k)^s · ∑_{n=k+1}^{N} n^{-s} - N·(k/(N+1))^s] / s
    have h_eq : ∀ᶠ N : ℕ in atTop, ∫ t in Ioc ((k:ℝ)/((N:ℝ)+1)) 1, f t =
        ((↑k : ℂ) + (↑k : ℂ) ^ s *
          (∑ n ∈ Finset.Icc (k+1) N, ((↑(n : ℕ) : ℂ) ^ (-s))) -
          (↑N : ℂ) * (↑((k:ℝ)/((N:ℝ)+1)) : ℂ) ^ s) / s := by
      filter_upwards [Filter.Ici_mem_atTop k] with N hN
      have hN' : k ≤ N := hN
      obtain ⟨M, rfl⟩ : ∃ M, N = k + M := ⟨N - k, by omega⟩
      -- Now N is replaced by k + M everywhere
      rw [integral_decomp_gen s hs k hk M]
      -- Apply partial Abel summation
      rw [partial_sum_gen s k M]
      -- Strip /s from both sides
      congr 1
      -- Simplify k/k = 1
      rw [div_self (show (k:ℝ) ≠ 0 from by positivity), ofReal_one, one_cpow, mul_one]
      exact abel_form_to_zeta_form s k hk M
    -- Step 2: ∑_{n=k+1}^{N} n^{-s} → ζ(s) - ∑_{n=1}^{k} n^{-s}
    have h_tail_zeta : Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.Icc (k+1) N, ((↑(n:ℕ) : ℂ) ^ (-s)))
        atTop (nhds (riemannZeta s -
          (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))))) := by
      have hs0 : s ≠ 0 := ne_of_apply_ne re (by linarith : s.re ≠ 0)
      -- Rewrite: eventually Icc = range - range
      suffices h : Tendsto (fun N : ℕ =>
          ∑ m ∈ Finset.range N, ((↑(m+1:ℕ) : ℂ) ^ (-s)) -
          ∑ m ∈ Finset.range k, ((↑(m+1:ℕ) : ℂ) ^ (-s)))
          atTop (nhds (riemannZeta s -
            (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))))) by
        apply h.congr'
        apply Filter.eventually_atTop.mpr
        refine ⟨k + 1, fun N hN => ?_⟩
        symm; dsimp only
        rw [show Finset.Icc (k+1) N = Finset.Ico (k+1) (N+1) from by
          ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        rw [Finset.sum_Ico_eq_add_neg _ (by omega : k+1 ≤ N+1)]
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_cpow (neg_ne_zero.mpr hs0)]
        push_cast; ring
      -- Partial zeta convergence: ∑ range(N) g → ζ
      have h_pzeta : Tendsto (fun N : ℕ =>
          ∑ m ∈ Finset.range N, ((↑(m+1:ℕ) : ℂ) ^ (-s)))
          atTop (nhds (riemannZeta s)) := by
        have := partial_zeta_tendsto s hs
        apply this.congr (fun N => ?_)
        congr 1; ext n
        rw [one_div, inv_eq_one_div, cpow_neg, one_div]
        congr 1; push_cast; ring
      exact h_pzeta.sub tendsto_const_nhds
    -- Step 3: N·(k/(N+1))^s → 0
    have h_tail := tail_vanishes_gen s hs k hk
    -- Step 4: Combine convergences
    have h_conv : Tendsto (fun N : ℕ =>
        ((↑k : ℂ) + (↑k : ℂ) ^ s *
          (∑ n ∈ Finset.Icc (k+1) N, ((↑(n : ℕ) : ℂ) ^ (-s))) -
          (↑N : ℂ) * (↑((k:ℝ)/((N:ℝ)+1)) : ℂ) ^ s) / s)
        atTop (nhds (((↑k : ℂ) + (↑k : ℂ) ^ s *
          (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s)))) - 0) / s)) :=
      Tendsto.div_const
        (((h_tail_zeta.const_mul _).const_add _).sub h_tail) s
    -- Step 5: Simplify 0 and rewrite target
    simp only [sub_zero] at h_conv
    have h_algebra : ((↑k : ℂ) + (↑k : ℂ) ^ s *
        (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))))) / s =
      (↑k : ℂ) / s + ((k : ℂ) ^ s / s) *
        (riemannZeta s - (Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s)))) := by
      ring
    rw [h_algebra] at h_conv
    exact h_conv.congr' (h_eq.mono (fun N hN => hN.symm))
  -- By uniqueness of limits
  exact tendsto_nhds_unique h_tendsto_int h_tendsto_target

/-- The general mellin_fractBasis for all k ≥ 1. -/
theorem mellin_fractBasis (k : ℕ) (hk : 1 ≤ k) (s : ℂ) (hs : 1 < s.re) :
    mellinRestricted (fractBasisC k) s =
    (k : ℂ) / (s * (s - 1)) +
    ((k : ℂ) ^ s / s) *
      ((Finset.range k).sum (fun m => ((↑(m + 1 : ℕ) : ℂ) ^ (-s))) - riemannZeta s) := by
  -- Split {k/t} = k/t - ⌊k/t⌋
  unfold mellinRestricted fractBasisC
  -- Step 1: Replace {k/t} with k/t - ⌊k/t⌋ pointwise
  have h_fract_eq : Set.EqOn
      (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * (↑(Int.fract ((k : ℝ) / t)) : ℂ))
      (fun t : ℝ => (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ)) -
                     (↑t : ℂ) ^ (s - 1) * (↑(⌊(k : ℝ) / t⌋) : ℂ))
      (Set.Ioc (0:ℝ) 1) := by
    intro t ⟨ht_lo, _⟩
    show (↑t : ℂ) ^ (s - 1) * (↑(Int.fract ((k : ℝ) / t)) : ℂ) =
         (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ)) -
         (↑t : ℂ) ^ (s - 1) * (↑(⌊(k : ℝ) / t⌋) : ℂ)
    rw [← mul_sub]
    congr 1
    -- {x} = x - ⌊x⌋
    rw [Int.fract]
    push_cast; norm_cast
  rw [setIntegral_congr_fun measurableSet_Ioc h_fract_eq]
  -- Step 2: ∫(f - g) = ∫f - ∫g
  rw [integral_sub
    (by -- IntegrableOn t^{s-1}·(k/t) = k·t^{s-2}
      have h_cpow : IntegrableOn (fun t : ℝ => (↑t : ℂ) ^ (s - 2)) (Ioc 0 1) volume := by
        have h := @intervalIntegral.intervalIntegrable_cpow' 0 1 (s-2) (by simp [sub_re]; linarith)
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1)] at h
      apply IntegrableOn.congr_fun (h_cpow.const_mul (↑k : ℂ)) _ measurableSet_Ioc
      intro t ht
      show (↑k : ℂ) * (↑t : ℂ) ^ (s - 2) = (↑t : ℂ) ^ (s - 1) * ((↑k : ℂ) / (↑t : ℂ))
      have ht' : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      rw [show (s - 2 : ℂ) = (s - 1) + (-1) from by ring, cpow_add _ _ ht', Complex.cpow_neg_one]
      ring : IntegrableOn (fun t : ℝ => (↑t : ℂ) ^ (s-1) * ((↑k:ℂ)/(↑t:ℂ)))
      (Set.Ioc 0 1) volume)
    (by -- IntegrableOn t^{s-1}·⌊k/t⌋: dominate by k·t^{Re(s)-2}
      have hg : IntegrableOn (fun x : ℝ => (↑x : ℂ) ^ (s - 2)) (Ioc 0 1) volume := by
        have h := @intervalIntegral.intervalIntegrable_cpow' 0 1 (s-2) (by simp [sub_re]; linarith)
        rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1)] at h
      exact Integrable.mono (hg.norm.const_mul (↑k : ℝ))
        (by apply AEStronglyMeasurable.mul
            · exact (ContinuousOn.cpow continuous_ofReal.continuousOn continuousOn_const
                (fun x hx => by left; simp [ofReal_re]; exact hx) |>.mono Ioc_subset_Ioi_self
                ).aestronglyMeasurable measurableSet_Ioc
            · exact ((Measurable.of_discrete (α := ℤ)).comp
                ((measurable_const.div measurable_id).floor)).aestronglyMeasurable.restrict)
        (by apply ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self
            apply (ae_restrict_mem measurableSet_Ioi).mono
            intro t ht; rw [mem_Ioi] at ht
            rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht]
            simp only [sub_re, one_re]
            have h_nn : (0 : ℤ) ≤ ⌊(k:ℝ)/t⌋ := Int.floor_nonneg.mpr (div_nonneg (by positivity) ht.le)
            rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast h_nn)]
            calc t ^ (s.re - 1) * (⌊(k:ℝ)/t⌋ : ℝ)
                ≤ t ^ (s.re - 1) * ((k:ℝ)/t) := mul_le_mul_of_nonneg_left (Int.floor_le _) (rpow_nonneg ht.le _)
              _ = (↑k : ℝ) * t ^ (s.re - 2) := by
                  rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc,
                      div_eq_mul_inv, ← rpow_neg_one t,
                      ← rpow_add ht]; congr 1; ring_nf
              _ ≤ ‖(↑k : ℝ) * t ^ (s.re - 2)‖ := le_norm_self _
              _ = _ := by simp)
      : IntegrableOn (fun t : ℝ => (↑t : ℂ) ^ (s-1) * (↑(⌊(k:ℝ)/t⌋):ℂ))
      (Set.Ioc 0 1) volume)]
  -- Step 3: Apply mellin_div_integral and floor_div_mellin
  rw [mellin_div_integral s hs k hk, floor_div_mellin s hs k hk]
  -- Step 4: Algebra: k/(s-1) - [k/s + (k^s/s)·(ζ - ∑)] = k/(s(s-1)) + (k^s/s)·(∑ - ζ)
  have hs_ne : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith
  have hs1_ne : s - 1 ≠ 0 := by
    intro h; have := congr_arg re h; simp [sub_re, one_re] at this; linarith
  field_simp
  ring


end D5.S3.Weil.ZetaPntBounds.NymanMellinFloorSeries
