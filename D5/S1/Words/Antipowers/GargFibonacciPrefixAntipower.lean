/- GID: D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower
   generality: I
   mirror-B: D5/B/S1/Words/Antipowers/GargFibonacciPrefixAntipower
   mirror-E: none(waiver:universal-prefix-antipower-proof)
   anchors: []
   utility: none
   digest: Every even Fibonacci number gives Garg's specified prefix antipower. -/

/-
result:
  proof_shape: content
  escape_witness: PerturbedGoldenSampleGrid.golden_sample_grid_rank_injective
admission_basis: open-problem-resolution (#14479; Proved)
Direct frozen dependencies:
  D5/S1/Words/ReturnWords/GoldenOccurrenceGaps.golden_factor_eq_iff_cylinder_rank_eq
    statement_id: sha256:57a8b181d2344945712dd4a20afa40bdf7d0855d42f9cdc3d2cafe6a048e7c0d
  D5/S1/Words/GoldenGapPrefix.fibWord_append_rec
    statement_id: sha256:c12b5cb307a920fdccaf69fc7645b2897fbf6ffc865a2f4c0320a9d2f5c5a1ce
  D5/S1/Words/GoldenWord.goldenWord_eq_fibWord_get
    statement_id: sha256:7be520e3583f7e49ff9381fd7da2849dbe777596ec9bdad180cebc4f2824798a
  D5/S1/Words/ReturnWords/GoldenOccurrenceGaps.goldenPhase
    statement_id: sha256:05940b90b4182fec56e4bc8e2bf12af068c4a40a70e2c372dbdf2a70e0690dfc
  D5/S1/Words/GoldenFactorComplexity.goldenFactor
    statement_id: sha256:45653c076830e3d013ea9e728d954ed6444072d1161a1656d45e0c92ab921ed8
  D5/S1/Words/GoldenWord.fibWord_length
    statement_id: sha256:5a1d44cf15492ea9a6ff43c74e45238ca5f5a566d96b8b42041061ea6c98c408
  D5/S1/Words/GoldenWord.index_lt_diagonal_level
    statement_id: sha256:ff19634eb9c5de253025991ff15c85c6dcccfa77d7b54ae428fec92feb94f63c
  D5/S0/Tower/GoldenGapWord.fibWord
    statement_id: sha256:c8520ae54a0eace400fd18644db28aa25debda739a3315d6cdc8d4de6eebee63
Same-delivery prerequisite (freeze first):
  D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.golden_sample_grid_rank_injective
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Antipowers.PerturbedGoldenSampleGrid

namespace D5.S1.Words.Antipowers.GargFibonacciPrefixAntipower


open D5.S1.Words D5.S0.Tower.GoldenGapWord

def digit (b : Bool) : Fin 2 := if b then 0 else 1

def S : ℕ → List (Fin 2)
  | 0 => [0]
  | 1 => [0, 1]
  | n + 2 => S (n + 1) ++ S n

private theorem S_eq (n : ℕ) : S n = (fibWord n).map digit := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
    rw [S, fibWord_append_rec, List.map_append, ih₀, ih₁]

private theorem diagonal_bound (i : ℕ) : i < (S i).length := by
  simpa [S_eq] using index_lt_diagonal_level i

def fibW (i : ℕ) : Fin 2 := (S i).get ⟨i, diagonal_bound i⟩

private theorem fibW_bridge (i : ℕ) : fibW i = digit (goldenWord i) := by
  simp [fibW, S_eq, goldenWord, List.get_eq_getElem]

private theorem fibW_finite (Q i : ℕ) (hi : i < (fibWord Q).length) :
    fibW i = digit ((fibWord Q).get ⟨i, hi⟩) := by
  rw [fibW_bridge, goldenWord_eq_fibWord_get Q i hi]

def blockLength (n : ℕ) : ℕ := Nat.fib n / 2 + Nat.fib (n - 1)

def claim : Prop :=
  ∀ n ≥ 1, Even (Nat.fib n) → ∀ i j,
    i < Nat.fib n - 1 → j < Nat.fib n - 1 → i ≠ j →
    (fun t : Fin (blockLength n) => fibW (i * blockLength n + t)) ≠
    (fun t : Fin (blockLength n) => fibW (j * blockLength n + t))

private theorem digit_injective : Function.Injective digit := by
  intro a b h
  cases a <;> cases b <;> simp_all [digit]

private theorem factors_of_equal_blocks {n i j : ℕ}
    (h : (fun t : Fin (blockLength n) => fibW (i * blockLength n + t)) =
      (fun t : Fin (blockLength n) => fibW (j * blockLength n + t)))
    {m : ℕ} (hm : m ≤ blockLength n) :
    goldenFactor m (i * blockLength n) = goldenFactor m (j * blockLength n) := by
  apply List.ofFn_inj.mpr
  funext t
  apply digit_injective
  rw [← fibW_bridge, ← fibW_bridge]
  exact congrFun h ⟨t.val, t.isLt.trans_le hm⟩




open D5.S1.Words

private noncomputable def d (n : ℕ) : ℝ := goldenMechanicalSlope ^ n
private noncomputable def s (n : ℕ) : ℝ := (-1 : ℝ) ^ n

private theorem s_cases (n : ℕ) : s n = 1 ∨ s n = -1 := by
  unfold s
  rw [neg_one_pow_eq_ite]
  split <;> simp

private theorem conj_power (n : ℕ) : Real.goldenConj ^ n = s n * d n := by
  have he : Real.goldenConj = -goldenMechanicalSlope := by
    rw [goldenMechanicalSlope, Real.inv_goldenRatio, neg_neg]
  rw [he, neg_pow]
  rfl

private theorem residual {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib n : ℝ) * goldenMechanicalSlope = Nat.fib (n - 1) - s n * d n := by
  have h := Real.goldenConj_mul_fib_succ_add_fib (n - 1)
  rw [Nat.sub_add_cancel hn, conj_power] at h
  have hα : Real.goldenConj = -goldenMechanicalSlope := by
    rw [goldenMechanicalSlope, Real.inv_goldenRatio, neg_neg]
  rw [hα] at h
  linarith

private theorem binet_residual (n : ℕ) :
    (Nat.fib n : ℝ) * Real.sqrt 5 * d n = 1 - s n * d n ^ 2 := by
  have h := Real.coe_fib_eq n
  rw [conj_power] at h
  have hdφ : Real.goldenRatio ^ n * d n = 1 := by
    change Real.goldenRatio ^ n * (Real.goldenRatio⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ Real.goldenRatio_ne_zero, one_pow]
  have hsqrt : (0 : ℝ) < Real.sqrt 5 := by positivity
  have he := (eq_div_iff hsqrt.ne').mp h
  nlinarith [hdφ, congrArg (fun x : ℝ => x * d n) he]

private theorem large_bounds {n : ℕ} (hn : 9 ≤ n) :
    0 < d n ∧ d n < 1 / 50 ∧
    (Nat.fib n : ℝ) * d n < 9 / 20 ∧
    d n + (Nat.fib n : ℝ) * d n ^ 2 / 2 < 49 / 2000 := by
  have hα0 : (0 : ℝ) < goldenMechanicalSlope := by
    exact inv_pos.mpr Real.goldenRatio_pos
  have hα1 : goldenMechanicalSlope < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hφ : (8 / 5 : ℝ) < Real.goldenRatio := by
    have hsqrt : (11 / 5 : ℝ) < Real.sqrt 5 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
      have := Real.sqrt_nonneg (5 : ℝ)
      nlinarith
    change (8 / 5 : ℝ) < (1 + Real.sqrt 5) / 2
    linarith
  have hα : goldenMechanicalSlope < (5 / 8 : ℝ) := by
    change Real.goldenRatio⁻¹ < _
    have hi := (inv_lt_inv₀ Real.goldenRatio_pos (by norm_num : (0 : ℝ) < 8 / 5)).mpr hφ
    have hrat : (8 / 5 : ℝ)⁻¹ = 5 / 8 := by norm_num
    rw [hrat] at hi
    exact hi
  have hd0 : 0 < d n := pow_pos hα0 n
  have hd9 : d n ≤ goldenMechanicalSlope ^ 9 := by
    exact pow_le_pow_of_le_one hα0.le hα1.le hn
  have hpow : goldenMechanicalSlope ^ 9 < (5 / 8 : ℝ) ^ 9 := by
    exact pow_lt_pow_left₀ hα hα0.le (by norm_num)
  have hd50 : d n < 1 / 50 := by
    have hnum : (5 / 8 : ℝ) ^ 9 < 1 / 50 := by norm_num
    exact hd9.trans_lt (hpow.trans hnum)
  have hsqrt : (223 / 100 : ℝ) < Real.sqrt 5 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hb := binet_residual n
  have hq0 : (0 : ℝ) ≤ Nat.fib n := by positivity
  have hqd0 : (0 : ℝ) ≤ (Nat.fib n : ℝ) * d n := mul_nonneg hq0 hd0.le
  have hdsq : d n ^ 2 < (1 / 2500 : ℝ) := by nlinarith
  have hqd : (Nat.fib n : ℝ) * d n < 9 / 20 := by
    rcases s_cases n with hs | hs <;> rw [hs] at hb <;> nlinarith
  have ha : d n + (Nat.fib n : ℝ) * d n ^ 2 / 2 < 49 / 2000 := by
    nlinarith [mul_lt_mul_of_pos_right hqd hd0]
  exact ⟨hd0, hd50, hqd, ha⟩

private theorem predecessor_odd {n : ℕ} (hn : 1 ≤ n) (hq : Even (Nat.fib n)) :
    Odd (Nat.fib (n - 1)) := by
  have hpq : (Nat.fib (n - 1)).Coprime (Nat.fib n) := by
    simpa [Nat.sub_add_cancel hn] using Nat.fib_coprime_fib_succ (n - 1)
  have hp2 := hpq.of_dvd_right (even_iff_two_dvd.mp hq)
  exact Nat.coprime_two_right.mp hp2

private theorem sampling_identity {n : ℕ} (hn : 2 ≤ n) (hq : Even (Nat.fib n)) :
    ∃ M : ℤ, (Nat.fib n : ℝ) * (blockLength n : ℝ) * goldenMechanicalSlope =
      (Nat.fib n : ℝ) * M + (Nat.fib n : ℝ) / 2 + s n / 2 - d n ^ 2 / 2 := by
  let q := Nat.fib n
  let p := Nat.fib (n - 1)
  let r := Nat.fib (n - 2)
  obtain ⟨P, hP⟩ := predecessor_odd (by omega : 1 ≤ n) hq
  obtain ⟨H, hH⟩ := hq
  have hq : q = 2 * H := by dsimp [q]; omega
  have hp : p = 2 * P + 1 := by dsimp [p]; omega
  have hqr : q = p + r := by
    dsimp [q, p, r]
    have he := Nat.fib_add_two (n := n - 2)
    rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at he
    exact he.trans (Nat.add_comm _ _)
  have hαsq : goldenMechanicalSlope ^ 2 = 1 - goldenMechanicalSlope := by
    have hψ := Real.goldenConj_sq
    have hα : Real.goldenConj = -goldenMechanicalSlope := by
      rw [goldenMechanicalSlope, Real.inv_goldenRatio, neg_neg]
    rw [hα] at hψ
    nlinarith
  have hres := residual (by omega : 1 ≤ n)
  have hb := binet_residual n
  have hαsqrt : 2 * goldenMechanicalSlope + 1 = Real.sqrt 5 := by
    rw [goldenMechanicalSlope, Real.inv_goldenRatio]
    change 2 * -((1 - Real.sqrt 5) / 2) + 1 = Real.sqrt 5
    ring
  have hpα : (p : ℝ) * goldenMechanicalSlope = r + s n * (1 + goldenMechanicalSlope) * d n := by
    have hqrR : (q : ℝ) = p + r := by exact_mod_cast hqr
    change (q : ℝ) * goldenMechanicalSlope = p - s n * d n at hres
    nlinarith [congrArg (fun x : ℝ => x * goldenMechanicalSlope) hres]
  have hL : (blockLength n : ℝ) = (q : ℝ) / 2 + p := by
    have hdiv : q / 2 = H := by omega
    simp only [blockLength, Nat.cast_add]
    change ((q / 2 : ℕ) : ℝ) + p = (q : ℝ) / 2 + p
    rw [hdiv, hq]
    push_cast
    ring
  have hLα : (blockLength n : ℝ) * goldenMechanicalSlope =
      (r : ℝ) + (P : ℝ) + 1 / 2 + s n * Real.sqrt 5 * d n / 2 := by
    have hpR : (p : ℝ) = 2 * P + 1 := by exact_mod_cast hp
    change (q : ℝ) * goldenMechanicalSlope = p - s n * d n at hres
    rw [hL]
    nlinarith [hres, hpα, congrArg (fun x : ℝ => s n * d n * x) hαsqrt]
  refine ⟨((r : ℕ) : ℤ) + P, ?_⟩
  have hs2 : s n ^ 2 = 1 := by rcases s_cases n with hs | hs <;> rw [hs] <;> norm_num
  push_cast
  have hbq : (q : ℝ) * Real.sqrt 5 * d n = 1 - s n * d n ^ 2 := hb
  nlinarith [congrArg (fun x : ℝ => x * (q : ℝ)) hLα,
    congrArg (fun x : ℝ => x * s n) hbq]




open D5.S1.Words D5.S1.Words.Antipowers.PerturbedGoldenSampleGrid

private theorem sampling_phase {n : ℕ} (hn : 2 ≤ n) (heven : Even (Nat.fib n)) (j : ℕ) :
    goldenPhase (j * blockLength n) =
      Int.fract (Y (Nat.fib n) (Nat.fib (n - 1)) (s n) (d n) j / Nat.fib n) := by
  have hqpos : 0 < Nat.fib n := Nat.fib_pos.mpr (by omega)
  have hqR : (0 : ℝ) < Nat.fib n := by exact_mod_cast hqpos
  obtain ⟨M, hM⟩ := sampling_identity hn heven
  have hres := residual (by omega : 1 ≤ n)
  have hY := sampling_lift_identity (q := Nat.fib n) (p := Nat.fib (n - 1)) (s n) (d n) j
  change Int.fract (((j * blockLength n + 1 : ℕ) : ℝ) * goldenMechanicalSlope) = _
  apply Int.fract_eq_fract.mpr
  refine ⟨(j : ℤ) * M + (j / 2 : ℕ), ?_⟩
  push_cast
  have hquot : (((j : ℤ) / 2 : ℤ) : ℝ) = ((j / 2 : ℕ) : ℝ) := by norm_cast
  rw [hquot]
  have hM' := congrArg (fun x : ℝ => (j : ℝ) * x) hM
  have hYdiv : Y (Nat.fib n) (Nat.fib (n - 1)) (s n) (d n) j /
      (Nat.fib n : ℝ) * Nat.fib n = Y (Nat.fib n) (Nat.fib (n - 1)) (s n) (d n) j :=
    div_mul_cancel₀ _ hqR.ne'
  dsimp [error] at hY
  apply (mul_right_cancel₀ hqR.ne')
  nlinarith [hres, hM', hY, hYdiv]

private theorem large_distinct {n : ℕ} (hn : 9 ≤ n) (heven : Even (Nat.fib n))
    {i j : ℕ} (hi : i < Nat.fib n - 1) (hj : j < Nat.fib n - 1) (hij : i ≠ j) :
    goldenFactor (Nat.fib n - 1) (i * blockLength n) ≠
      goldenFactor (Nat.fib n - 1) (j * blockLength n) := by
  let q := Nat.fib n
  let p := Nat.fib (n - 1)
  have hqpos : 0 < q := Nat.fib_pos.mpr (by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hpq : p.Coprime q := by
    simpa [p, q, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      Nat.fib_coprime_fib_succ (n - 1)
  have hd := large_bounds hn
  have hs := s_cases n
  have hne := golden_sample_grid_rank_injective hqpos heven hpq hs hd.1 hd.2.2.1
    hd.2.2.2 (residual (by omega : 1 ≤ n)) hi hj hij
  rw [← sampling_phase (by omega : 2 ≤ n) heven i,
    ← sampling_phase (by omega : 2 ≤ n) heven j] at hne
  intro he
  have hrank := (golden_factor_eq_iff_cylinder_rank_eq _ _ _).mp he
  apply hne
  exact hrank

open D5.S0.Tower.GoldenGapWord

private theorem blockLength_ge {n : ℕ} (hn : 2 ≤ n) (heven : Even (Nat.fib n)) :
    Nat.fib n - 1 ≤ blockLength n := by
  have hrec := Nat.fib_add_two (n := n - 2)
  rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hrec
  have hmono := Nat.fib_mono (show n - 2 ≤ n - 1 by omega)
  obtain ⟨H, hH⟩ := heven
  unfold blockLength
  omega

theorem result : claim := by
  let finiteBlock (i : Fin 7) : Fin 9 → Fin 2 := fun t =>
    digit ((fibWord 9).get ⟨i.val * 9 + t.val, by
      rw [fibWord_length]
      norm_num
      omega⟩)
  have hcert : ∀ i j : Fin 7, i ≠ j → finiteBlock i ≠ finiteBlock j := by
    decide
  intro n hn heven i j hi hj hij
  by_cases hsmall : n < 9
  · have hnvalues : n = 3 ∨ n = 6 := by
      interval_cases n <;> norm_num [Nat.fib] at heven <;> omega
    rcases hnvalues with rfl | rfl
    · norm_num at hi hj
      omega
    · have hi7 : i < 7 := by norm_num at hi; exact hi
      have hj7 : j < 7 := by norm_num at hj; exact hj
      intro he
      have hL : blockLength 6 = 9 := by norm_num [blockLength]
      rw [hL] at he
      apply hcert ⟨i, hi7⟩ ⟨j, hj7⟩ (by intro h; apply hij; exact congrArg Fin.val h)
      funext t
      dsimp [finiteBlock]
      have hbi : i * 9 + t.val < (fibWord 9).length := by rw [fibWord_length]; norm_num; omega
      have hbj : j * 9 + t.val < (fibWord 9).length := by rw [fibWord_length]; norm_num; omega
      exact (fibW_finite 9 _ hbi).symm.trans ((congrFun he t).trans (fibW_finite 9 _ hbj))
  · have hn9 : 9 ≤ n := by omega
    intro he
    exact large_distinct hn9 heven hi hj hij
      (factors_of_equal_blocks he (blockLength_ge (by omega : 2 ≤ n) heven))



end D5.S1.Words.Antipowers.GargFibonacciPrefixAntipower
