/- GID: D5/S3/Analytic/Oscillation/SpectrumCommensurateAlignment
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumCommensurateAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nested denominators give frequent exact alignment with a logarithmic square tail. -/

import D5.S3.Analytic.Oscillation.SpectrumLogarithmicMissingWindow

/-! A locally finite spectrum with frequent full sine alignment at every large cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment

open OrdinateCounting (Spectrum)
open SpectrumPhaseCutoff (mass sine mem_cut)
open SpectrumCriticalMissingWindow (HasLogSquaredMass)
open SpectrumLogarithmicMissingWindow (HasLogarithmicSquareTail)

private def exponent (n : ℕ) : ℕ := Nat.log 5 (n + 1)
private def denominator (n : ℕ) : ℕ := 5 ^ exponent n
private def blockSize (n : ℕ) : ℕ := denominator n * 2 ^ n
private def Index := Σ n : ℕ, Fin (blockSize n)

private theorem denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  positivity

private theorem blockSize_pos (n : ℕ) : 0 < blockSize n :=
  Nat.mul_pos (denominator_pos n) (by positivity)

private theorem denominator_bounds (n : ℕ) :
    denominator n ≤ n + 1 ∧ n + 1 < 5 * denominator n := by
  exact ⟨Nat.pow_log_le_self 5 (Nat.succ_ne_zero n), by
    simpa [denominator, exponent, pow_succ'] using
      (Nat.lt_pow_succ_log_self (b := 5) (by decide) (n + 1))⟩

private def boundary (n : ℕ) : ℝ := 4 * 2 ^ n

private theorem boundary_succ (n : ℕ) : boundary (n + 1) = 2 * boundary n := by
  unfold boundary
  rw [pow_succ]
  ring

private theorem boundary_strictMono : StrictMono boundary := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [boundary_succ]
  have : 0 < boundary n := by unfold boundary; positivity
  linarith

private def rate (j : Index) : ℝ :=
  boundary j.1 + (4 * (j.2.val : ℝ) + 1) / (denominator j.1 : ℝ)

private def weight (j : Index) : ℝ := (2 * (j.1 : ℝ) + 1) / (blockSize j.1 : ℝ)

private theorem weight_pos (j : Index) : 0 < weight j :=
  div_pos (by positivity) (by exact_mod_cast blockSize_pos j.1)

private theorem rate_in_block (j : Index) :
    boundary j.1 < rate j ∧ rate j < boundary (j.1 + 1) := by
  have hq : (0 : ℝ) < (denominator j.1 : ℝ) := by exact_mod_cast denominator_pos j.1
  refine ⟨lt_add_of_pos_right _ (div_pos (by positivity) hq), ?_⟩
  rw [boundary_succ, rate]
  have hk : (j.2.val : ℝ) + 1 ≤ (blockSize j.1 : ℝ) := by
    exact_mod_cast j.2.isLt
  have hbound : (blockSize j.1 : ℝ) = (denominator j.1 : ℝ) * 2 ^ j.1 := by
    simp [blockSize]
  have hfrac : (4 * (j.2.val : ℝ) + 1) / (denominator j.1 : ℝ) < boundary j.1 := by
    apply (div_lt_iff₀ hq).2
    rw [boundary]
    nlinarith only [hk, hbound]
  linarith

private theorem rate_injective : Function.Injective rate := by
  intro i j hij
  have hn : i.1 = j.1 := by
    rcases lt_trichotomy i.1 j.1 with h | h | h
    · exact False.elim ((rate_in_block i).2.not_ge
        ((boundary_strictMono.monotone (Nat.succ_le_of_lt h)).trans
          ((rate_in_block j).1.le.trans_eq hij.symm)))
    · exact h
    · exact False.elim ((rate_in_block j).2.not_ge
        ((boundary_strictMono.monotone (Nat.succ_le_of_lt h)).trans
          ((rate_in_block i).1.le.trans_eq hij)))
  rcases i with ⟨n, i⟩
  rcases j with ⟨m, j⟩
  change n = m at hn
  subst m
  congr 1
  apply Fin.ext
  simp only [rate] at hij
  have hq : (0 : ℝ) < (denominator n : ℝ) := by exact_mod_cast denominator_pos n
  have hdiv := add_left_cancel hij
  have hnum := (div_left_inj' hq.ne').mp hdiv
  have : (i.val : ℝ) = j.val := by linarith
  exact_mod_cast this

private def blocks (s : Finset ℕ) : Finset Index :=
  s.sigma (fun _ => Finset.univ)

private theorem mem_blocks {s : Finset ℕ} {j : Index} : j ∈ blocks s ↔ j.1 ∈ s := by
  change j ∈ s.sigma (fun _ => Finset.univ) ↔ j.1 ∈ s
  exact Finset.mem_sigma.trans (and_iff_left (Finset.mem_univ j.2))

private theorem spectrum_finite (T : ℝ) : {j : Index | rate j ≤ T}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt T
  refine (blocks (Finset.range N)).finite_toSet.subset ?_
  intro j hj
  have hn : (j.1 : ℝ) ≤ boundary j.1 := by
    have h : ∀ n : ℕ, (n : ℝ) ≤ boundary n := by
      intro n
      induction n with
      | zero => norm_num [boundary]
      | succ n ih =>
        rw [Nat.cast_succ, boundary_succ]
        have hB : (4 : ℝ) ≤ boundary n := by
          simpa [boundary] using boundary_strictMono.monotone (Nat.zero_le n)
        linarith
    exact h j.1
  have hj' : rate j ≤ T := hj
  change j ∈ blocks (Finset.range N)
  rw [mem_blocks, Finset.mem_range]
  exact_mod_cast hn.trans_lt ((rate_in_block j).1.trans_le (hj'.trans hN.le))

private def spectrum : Spectrum where
  index := Index
  gamma := rate
  mult := fun _ => 1
  gamma_pos := fun j => (by unfold boundary; positivity : 0 < boundary j.1).trans
    (rate_in_block j).1
  gamma_injective := rate_injective
  mult_pos := fun _ => Nat.one_pos
  finite_le := spectrum_finite

private theorem index_infinite : Infinite spectrum.index := by
  apply Infinite.of_injective
    (fun n : ℕ => (⟨n, ⟨0, blockSize_pos n⟩⟩ : Index))
  intro a b h
  exact congrArg Sigma.fst h

private theorem cutoff_block {T : ℝ} (hT : 4 ≤ T) :
    ∃ n : ℕ, boundary n ≤ T ∧ T < boundary (n + 1) := by
  let m := ⌊T / 4⌋₊
  have hT' : 0 ≤ T / 4 := by linarith
  have hm : 1 ≤ m := (Nat.le_floor_iff hT').2 (by norm_num; linarith)
  refine ⟨Nat.log 2 m, ?_, ?_⟩
  · have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have hf : (m : ℝ) ≤ T / 4 := Nat.floor_le hT'
    unfold boundary
    linarith
  · have hpow : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 m + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (b := 2) (by decide) m
    have hf : T / 4 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    unfold boundary
    linarith

private theorem lower_blocks {T : ℝ} {n : ℕ} (hT : boundary n ≤ T) :
    blocks (Finset.range n) ⊆ spectrum.cut T := by
  intro j hj
  rw [mem_blocks, Finset.mem_range] at hj
  exact mem_cut.2 ((rate_in_block j).2.le.trans
    ((boundary_strictMono.monotone (Nat.succ_le_of_lt hj)).trans hT))

private theorem block_le_of_mem_cut {T : ℝ} {n : ℕ} (hT : T < boundary (n + 1))
    {j : Index} (hj : j ∈ spectrum.cut T) : j.1 ≤ n := by
  by_contra! hn
  exact (hT.trans_le (boundary_strictMono.monotone hn)).not_ge
    ((rate_in_block j).1.le.trans (mem_cut.1 hj))

private theorem log_bounds {T : ℝ} {n : ℕ}
    (hlo : boundary n ≤ T) (hhi : T < boundary (n + 1)) :
    (n : ℝ) + 2 ≤ Real.log T / Real.log 2 ∧
      Real.log T / Real.log 2 < (n : ℝ) + 3 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb (k : ℕ) : 0 < boundary k := by unfold boundary; positivity
  have hvalue (k : ℕ) : Real.log (boundary k) = ((k : ℝ) + 2) * Real.log 2 := by
    unfold boundary
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ k ≠ 0),
      Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    ring
  have hl := Real.log_le_log (hb n) hlo
  have hu := Real.log_lt_log ((hb n).trans_le hlo) hhi
  rw [hvalue] at hl hu
  exact ⟨(le_div_iff₀ hlog).2 hl, (div_lt_iff₀ hlog).2 (by push_cast at hu; linarith)⟩

private theorem sum_blocks (s : Finset ℕ) (f : Index → ℝ) :
    ∑ j ∈ blocks s, f j = ∑ n ∈ s, ∑ k : Fin (blockSize n), f ⟨n, k⟩ :=
  Finset.sum_sigma _ _ _

private theorem block_mass (n : ℕ) :
    ∑ k : Fin (blockSize n), weight ⟨n, k⟩ = 2 * (n : ℝ) + 1 := by
  have hsize : (blockSize n : ℝ) ≠ 0 := by exact_mod_cast (blockSize_pos n).ne'
  simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private theorem prefix_mass (n : ℕ) :
    ∑ j ∈ blocks (Finset.range n), weight j = (n : ℝ) ^ 2 := by
  rw [sum_blocks]
  simp_rw [block_mass]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_succ]
    ring

private theorem mass_between_squares {T : ℝ} {n : ℕ}
    (hlo : boundary n ≤ T) (hhi : T < boundary (n + 1)) :
    (n : ℝ) ^ 2 ≤ mass spectrum weight T ∧
      mass spectrum weight T ≤ ((n : ℝ) + 1) ^ 2 := by
  classical
  have hmono {s t : Finset Index} (h : s ⊆ t) :
      ∑ j ∈ s, weight j ≤ ∑ j ∈ t, weight j :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun j _ _ => (weight_pos j).le)
  have hsub : spectrum.cut T ⊆ blocks (Finset.range (n + 1)) := by
    intro j hj
    exact mem_blocks.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (block_le_of_mem_cut hhi hj)))
  have hl := hmono (lower_blocks hlo)
  have hu := hmono hsub
  rw [prefix_mass] at hl hu
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hcast] at hu
  exact ⟨hl, hu⟩

private theorem has_log_squared_mass : HasLogSquaredMass spectrum weight := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 2)⁻¹ ^ 2, 6 / Real.log 2, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with T hT
  obtain ⟨n, hlo, hhi⟩ := cutoff_block hT
  obtain ⟨hmlo, hmhi⟩ := mass_between_squares hlo hhi
  obtain ⟨hllo, hlhi⟩ := log_bounds hlo hhi
  let L := Real.log T / Real.log 2
  change (n : ℝ) + 2 ≤ L at hllo
  change L < (n : ℝ) + 3 at hlhi
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hL : 0 ≤ L := by linarith
  have hupper : mass spectrum weight T ≤ L ^ 2 :=
    hmhi.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hrewrite : (Real.log 2)⁻¹ ^ 2 * Real.log T ^ 2 = L ^ 2 := by
    simp [L, div_eq_mul_inv, mul_pow, mul_comm]
  rw [hrewrite, abs_of_nonpos (sub_nonpos.mpr hupper)]
  have hdiff : L ^ 2 - mass spectrum weight T ≤ 6 * L := by
    calc
      _ ≤ L ^ 2 - (n : ℝ) ^ 2 := sub_le_sub_left hmlo _
      _ = (L - (n : ℝ)) * (L + (n : ℝ)) := by ring
      _ ≤ 3 * (2 * L) := by
        exact mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ = _ := by ring
  rw [neg_sub]
  refine hdiff.trans ?_
  dsimp [L]
  rw [show 6 * (Real.log T / Real.log 2) = (6 / Real.log 2) * Real.log T by ring]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private def envelope (n : ℕ) : ℝ := 40 * ((n : ℝ) + 2) / 2 ^ n

private theorem block_square_bound (n : ℕ) :
    ∑ k : Fin (blockSize n), weight ⟨n, k⟩ ^ 2 ≤ envelope n - envelope (n + 1) := by
  have hq : (0 : ℝ) < (denominator n : ℝ) := by exact_mod_cast denominator_pos n
  have hsize : (0 : ℝ) < (blockSize n : ℝ) := by exact_mod_cast blockSize_pos n
  have hscale : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have hqbound : (n : ℝ) + 1 ≤ 5 * (denominator n : ℝ) := by
    exact_mod_cast (denominator_bounds n).2.le
  have hnum : (2 * (n : ℝ) + 1) ^ 2 ≤
      (20 * ((n : ℝ) + 1)) * (denominator n : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 5 * (denominator n : ℝ) - ((n : ℝ) + 1) by linarith)
      (show 0 ≤ 4 * ((n : ℝ) + 1) by positivity)]
  have hs : (blockSize n : ℝ) = (denominator n : ℝ) * 2 ^ n := by simp [blockSize]
  have hsq : ∑ k : Fin (blockSize n), weight ⟨n, k⟩ ^ 2 =
      (2 * (n : ℝ) + 1) ^ 2 / (blockSize n : ℝ) := by
    simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hstep : envelope n - envelope (n + 1) =
      (20 * ((n : ℝ) + 1)) / 2 ^ n := by
    unfold envelope
    rw [pow_succ]
    push_cast
    field_simp
    ring
  rw [hsq, hstep, div_le_div_iff₀ hsize hscale, hs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hnum hscale.le

private theorem envelope_sum (m N : ℕ) (h : m ≤ N) :
    ∑ n ∈ Finset.Ico m N, (envelope n - envelope (n + 1)) = envelope m - envelope N := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    ring

private theorem has_logarithmic_square_tail : HasLogarithmicSquareTail spectrum weight := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨320 / Real.log 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
  intro T hXT
  obtain ⟨m, hmlo, hmhi⟩ := cutoff_block hX
  obtain ⟨N, _, hNhi⟩ := cutoff_block (hX.trans hXT)
  have hmN : m ≤ N := by
    by_contra! h
    exact (hNhi.trans_le (boundary_strictMono.monotone h)).not_ge (hmlo.trans hXT)
  have hsub : spectrum.cut T \ spectrum.cut X ⊆ blocks (Finset.Ico m (N + 1)) := by
    intro j hj
    obtain ⟨hjT, hjX⟩ := Finset.mem_sdiff.1 hj
    have hjm : m ≤ j.1 := by
      by_contra! h
      exact hjX (lower_blocks hmlo (mem_blocks.2 (Finset.mem_range.2 h)))
    exact mem_blocks.2 (Finset.mem_Ico.2 ⟨hjm, Nat.lt_succ_of_le (block_le_of_mem_cut hNhi hjT)⟩)
  calc
    _ ≤ ∑ j ∈ blocks (Finset.Ico m (N + 1)), weight j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => sq_nonneg (weight j))
    _ ≤ envelope m - envelope (N + 1) := by
      rw [sum_blocks, ← envelope_sum m (N + 1) (hmN.trans (Nat.le_succ N))]
      exact Finset.sum_le_sum (fun n _ => block_square_bound n)
    _ ≤ envelope m := sub_le_self _ (by unfold envelope; positivity)
    _ ≤ 320 / Real.log 2 * Real.log X / X := by
      obtain ⟨hloglo, _⟩ := log_bounds hmlo hmhi
      have hscale : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hXpos : 0 < X := by linarith
      have hXhi : X ≤ 8 * 2 ^ m := by
        rw [boundary_succ, boundary] at hmhi
        linarith
      unfold envelope
      apply (div_le_div_iff₀ hscale hXpos).2
      calc
        _ ≤ (40 * ((m : ℝ) + 2)) * (8 * 2 ^ m) :=
          mul_le_mul_of_nonneg_left hXhi (by positivity)
        _ = 320 * ((m : ℝ) + 2) * 2 ^ m := by ring
        _ ≤ 320 * (Real.log X / Real.log 2) * 2 ^ m :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hloglo (by norm_num)) hscale.le
        _ = _ := by ring

private theorem pow_five_quarter (d : ℕ) : ∃ b : ℕ, 5 ^ d = 4 * b + 1 := by
  induction d with
  | zero => exact ⟨0, by norm_num⟩
  | succ d ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨5 * b + 1, ?_⟩
    rw [pow_succ, hb]
    ring

private theorem quarter_phase {j : Index} {N : ℕ} (h : j.1 ≤ N) :
    ∃ b : ℕ, rate j * (denominator N : ℝ) = 4 * (b : ℝ) + 1 := by
  have he : exponent j.1 ≤ exponent N := Nat.log_mono_right (Nat.succ_le_succ h)
  obtain ⟨c, hc⟩ := pow_five_quarter (exponent N - exponent j.1)
  have hq : denominator N = denominator j.1 * (4 * c + 1) := by
    rw [← hc, denominator, denominator, ← pow_add, Nat.add_sub_of_le he]
  have hq0 : (denominator j.1 : ℝ) ≠ 0 := by exact_mod_cast (denominator_pos j.1).ne'
  have hqr : (denominator N : ℝ) = (denominator j.1 : ℝ) * (4 * (c : ℝ) + 1) := by
    exact_mod_cast hq
  refine ⟨2 ^ j.1 * denominator N + (4 * j.2.val + 1) * c + j.2.val, ?_⟩
  simp only [rate, boundary, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, add_mul]
  conv_lhs => rw [show (4 * (j.2.val : ℝ) + 1) / (denominator j.1 : ℝ) *
      (denominator N : ℝ) = (4 * (j.2.val : ℝ) + 1) * (4 * (c : ℝ) + 1) by
        rw [hqr, ← mul_assoc, div_mul_cancel₀ _ hq0]]
  ring

private theorem full_alignment {T : ℝ} {N : ℕ} (hT : T < boundary (N + 1)) (m : ℤ) :
    sine spectrum weight T
        (Real.pi * (denominator N : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * denominator N)) =
      mass spectrum weight T := by
  unfold sine mass
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨b, hb⟩ := quarter_phase (block_le_of_mem_cut hT hj)
  let k : ℤ := (b : ℤ) + m * (4 * (b : ℤ) + 1)
  have harg : spectrum.gamma j *
        (Real.pi * (denominator N : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * denominator N)) =
      Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := by
    change rate j * _ = _
    calc
      _ = (rate j * (denominator N : ℝ)) * (Real.pi / 2 + (m : ℝ) * (2 * Real.pi)) := by ring
      _ = _ := by rw [hb]; simp only [k, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        Int.cast_natCast, Int.cast_one]; ring
  rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two, mul_one]

private theorem mass_pos {T : ℝ} (hT : 5 ≤ T) : 0 < mass spectrum weight T := by
  let j : Index := ⟨0, ⟨0, blockSize_pos 0⟩⟩
  have hj : j ∈ spectrum.cut T := mem_cut.2 (by
    change rate j ≤ T
    norm_num [j, rate, boundary, denominator, exponent, Nat.log_one_right]
    exact hT)
  unfold mass
  exact lt_of_lt_of_le (weight_pos j)
    (Finset.single_le_sum (fun k _ => (weight_pos k).le) hj)

private theorem progression_visits {T : ℝ} {q : ℕ} (hq : 0 < q)
    (hbound : (q : ℝ) + 1 ≤ Real.log T / Real.log 2) (A : ℝ) :
    ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * q) ∈
      Ioo A (A + (2 * Real.pi / Real.log 2) * Real.log T) := by
  let start := Real.pi * (q : ℝ) / 2
  let period := 2 * Real.pi * (q : ℝ)
  have hpi := Real.pi_pos
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hperiod : 0 < period := by dsimp [period]; positivity
  let m := ⌈(A + Real.pi - start) / period⌉
  have hlow : A + Real.pi - start ≤ (m : ℝ) * period :=
    (div_le_iff₀ hperiod).1 (Int.le_ceil _)
  have hhigh : (m : ℝ) < (A + Real.pi - start) / period + 1 := Int.ceil_lt_add_one _
  have hceil := mul_lt_mul_of_pos_right hhigh hperiod
  rw [add_mul, div_mul_cancel₀ _ hperiod.ne', one_mul] at hceil
  have hslack : period + 2 * Real.pi ≤ (2 * Real.pi / Real.log 2) * Real.log T := by
    calc
      _ = 2 * Real.pi * ((q : ℝ) + 1) := by dsimp [period]; ring
      _ ≤ 2 * Real.pi * (Real.log T / Real.log 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  refine ⟨m, ?_⟩
  change A < start + (m : ℝ) * period ∧
    start + (m : ℝ) * period < A + (2 * Real.pi / Real.log 2) * Real.log T
  exact ⟨by linarith, by linarith⟩

/-- At each cutoff at least five, one progression aligns every smaller cutoff. -/
theorem exists_logarithmic_full_alignment :
    ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
      (∀ j, 0 < w j) ∧ HasLogSquaredMass S w ∧ HasLogarithmicSquareTail S w ∧
      ∀ T : ℝ, 5 ≤ T → 0 < mass S w T ∧
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) + 1 ≤ Real.log T / Real.log 2 ∧
          (∀ (m : ℤ) (X : ℝ), X ≤ T →
            sine S w X (Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * q)) = mass S w X) ∧
          ∀ A : ℝ, ∃ m : ℤ, Real.pi * (q : ℝ) / 2 + (m : ℝ) * (2 * Real.pi * q) ∈
            Ioo A (A + (2 * Real.pi / Real.log 2) * Real.log T) := by
  refine ⟨spectrum, weight, index_infinite, weight_pos, has_log_squared_mass,
    has_logarithmic_square_tail, ?_⟩
  intro T hT
  obtain ⟨N, hlo, hhi⟩ := cutoff_block (by linarith : 4 ≤ T)
  have hq : (denominator N : ℝ) ≤ (N : ℝ) + 1 := by
    exact_mod_cast (denominator_bounds N).1
  have hbound : (denominator N : ℝ) + 1 ≤ Real.log T / Real.log 2 := by
    linarith [(log_bounds hlo hhi).1]
  exact ⟨mass_pos hT, denominator N, denominator_pos N, hbound,
    fun m X hX => full_alignment (hX.trans_lt hhi) m, progression_visits (denominator_pos N) hbound⟩

#print axioms exists_logarithmic_full_alignment

end D5.S3.Analytic.Oscillation.SpectrumCommensurateAlignment
