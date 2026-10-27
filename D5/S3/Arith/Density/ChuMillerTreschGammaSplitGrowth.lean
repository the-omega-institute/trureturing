/- GID: D5/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth
   generality: I
   mirror-B: D5/B/S3/Arith/Density/ChuMillerTreschGammaSplitGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every prescribed Gamma-label density has a positive increasing linear-growth sequence. -/

/-
admission_basis: open-problem-resolution (#20691; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21309.
Direct frozen dependencies (declaration statement_id):
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter
    sha256:2f3fffa2e006abb3c4b960a36d958d5450218bc2fd89384af0710e73ea02b7e8
  D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter_eq_zero_or_one
    sha256:5386c38192676a913b44b62dd445e421e0db0c92e65ac92018fa6596026b4f4f
Public theorem result:
  proof_shape: content (five-edge construction and the count_formula induction).
  escape_witness: count_formula, through discrepancy and density.
The public definitions Gamma, zeroCount and claim retain the source expressions.
The floor schedule is lowerMechanicalLetter p 0, with zero intercept; no duplicate schedule
definition is introduced.
Private arithmetic and assembly declarations are organized as follows:
  exclusive: proof_shape: bind-only; consumer(s): gamma_one; escape_witness: none.
  row_coprime: proof_shape: bind-only; consumer(s): z_rows, o_rows; escape_witness: none.
  gamma_zero: proof_shape: bind-only; consumer(s): z_rows; escape_witness: none.
  gamma_one: proof_shape: bind-only; consumer(s): o_rows; escape_witness: none.
  z_rows: proof_shape: bind-only; consumer(s): block_edge; escape_witness: none.
  o_rows: proof_shape: bind-only; consumer(s): block_edge; escape_witness: none.
  sequence_block: proof_shape: bind-only; consumer(s): sequence_step, block_edge; escape_witness: none.
  sequence_bounds: proof_shape: bind-only; consumer(s): result; escape_witness: none.
  sequence_step: proof_shape: bind-only; consumer(s): sequence_strictMono; escape_witness: none.
  sequence_strictMono: proof_shape: bind-only; consumer(s): result; escape_witness: none.
  block_edge: proof_shape: bind-only; consumer(s): sequence_edge; escape_witness: none.
  sequence_edge: proof_shape: bind-only; consumer(s): count_succ; escape_witness: none.
  w_binary: proof_shape: bind-only; consumer(s): count_formula; escape_witness: none.
  count_succ: proof_shape: bind-only; consumer(s): count_formula; escape_witness: none.
  count_formula: proof_shape: content; consumer(s): discrepancy; escape_witness: count_formula.
  discrepancy: proof_shape: content; consumer(s): density; escape_witness: count_formula.
  density: proof_shape: content; consumer(s): result; escape_witness: count_formula.
The two translated chains share both endpoints and have opposite constant labels.
The floor-increment schedule selects the chains and bounds the counting error by 5.
The private growth bound is 8*n ≤ sequence w n + 9 and sequence w n ≤ 8*n+15;
the public result uses exponent 1 and coefficient 23 for n ≥ 1.
-/

import D5.S1.Words.Mechanical.MechanicalBalance

namespace D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

open Classical

/-- Section 1: `Γ(a, b)`, with `g = gcd(a, b)`. -/
noncomputable def Gamma (a b : ℕ) : ℕ :=
  if ∃ x y : ℕ, a / Nat.gcd a b * x + b / Nat.gcd a b * y =
      (a / Nat.gcd a b - 1) * (b / Nat.gcd a b - 1) / 2 then 0 else 1

/-- Corollary 2.6: `#{1 ≤ n ≤ N : Γ(a_{n−1}, a_n) = 0}`. -/
noncomputable def zeroCount (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => Gamma (a (n - 1)) (a n) = 0).card

/-- Section 3.4: for every split `p ∈ [0, 1]` there is a strictly increasing sequence of positive integers growing like
`n^k` for some `k` whose zero proportion `#{n ≤ N : Γ(a_{n−1}, a_n) = 0}/N` tends to `p`. -/
def claim : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
    (∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ C * (n : ℝ) ^ k) ∧
    Filter.Tendsto (fun N : ℕ => (zeroCount a N : ℝ) / N) Filter.atTop (nhds p)

end D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

namespace D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

/-- The two equations cannot both be soluble. -/
private theorem exclusive {a b M : ℕ} (hc : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : 2 * M = (a - 1) * (b - 1))
    {x y u v : ℕ} (h0 : a * x + b * y = M)
    (h1 : 1 + a * u + b * v = M) : False := by
  apply hc.mul_add_mul_ne_mul (a := x + u + 1) (b := y + v + 1)
    (by omega) (by omega)
  have ha' : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have hb' : b - 1 + 1 = b := Nat.sub_add_cancel hb
  nlinarith

/-- A general coprimality rule for translated certificate rows. -/
private theorem row_coprime (k c d : ℕ) (hd : d ∣ 40) (hc : Nat.Coprime c d) :
    Nat.Coprime (40 * k + c) (40 * k + (c + d)) := by
  have ht : Nat.Coprime d (c + 40 * k) :=
    (Nat.coprime_add_iff_left (dvd_mul_of_dvd_left hd k)).mpr hc.symm
  have ht' : Nat.Coprime (40 * k + c) d := by
    simpa [add_comm] using ht.symm
  simpa [add_assoc] using (Nat.coprime_self_add_right).mpr ht'

/-- An even numerator certificate determines the zero-labelled edge. -/
private theorem gamma_zero {a b x y : ℕ} (hc : Nat.Coprime a b)
    (h : 2 * (a * x + b * y) = (a - 1) * (b - 1)) : Gamma a b = 0 := by
  classical
  unfold Gamma
  rw [hc.gcd_eq_one]
  apply ite_eq_left
  refine ⟨x, y, ?_⟩
  simpa only [Nat.div_one] using (show a*x+b*y=(a-1)*(b-1)/2 by omega)

/-- An even numerator one-certificate determines the one-labelled edge. -/
private theorem gamma_one {a b u v : ℕ} (hc : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : 2 * (1 + a * u + b * v) = (a - 1) * (b - 1)) : Gamma a b = 1 := by
  classical
  unfold Gamma
  rw [hc.gcd_eq_one]
  apply ite_eq_right
  rintro ⟨x, y, hxy⟩
  have hxy' : a*x+b*y=(a-1)*(b-1)/2 := by
    simpa only [Nat.div_one] using hxy
  exact exclusive hc ha hb (M := 1 + a * u + b * v) (x := x) (y := y) (u := u) (v := v) h
    (by omega) rfl

private theorem z_rows (k : ℕ) :
    Gamma (40*k+3) (40*k+7) = 0 ∧
    Gamma (40*k+7) (40*k+17) = 0 ∧
    Gamma (40*k+17) (40*k+19) = 0 ∧
    Gamma (40*k+19) (40*k+23) = 0 ∧
    Gamma (40*k+23) (40*k+43) = 0 := by
  have hc (c d : ℕ) (hd : d ∣ 40) (hcd : Nat.Coprime c d) := row_coprime k c d hd hcd
  have hsub (c : ℕ) (h : 1 ≤ c) : 40*k+c-1 = 40*k+(c-1) := Nat.add_sub_assoc h (40*k)
  refine ⟨gamma_zero (x := 15*k+2) (y := 5*k) (hc 3 4 (by decide) (by decide)) ?_,
    gamma_zero (x := 6*k+2) (y := 14*k+2) (hc 7 10 (by decide) (by decide)) ?_,
    gamma_zero (x := 10*k+4) (y := 10*k+4) (hc 17 2 (by decide) (by decide)) ?_,
    gamma_zero (x := 15*k+8) (y := 5*k+2) (hc 19 4 (by decide) (by decide)) ?_,
    gamma_zero (x := 7*k+7) (y := 13*k+7) (hc 23 20 (by decide) (by decide)) ?_⟩
  all_goals simp [hsub]; ring

private theorem o_rows (k : ℕ) :
    Gamma (40*k+3) (40*k+23) = 1 ∧
    Gamma (40*k+23) (40*k+27) = 1 ∧
    Gamma (40*k+27) (40*k+29) = 1 ∧
    Gamma (40*k+29) (40*k+33) = 1 ∧
    Gamma (40*k+33) (40*k+43) = 1 := by
  have hc (c d : ℕ) (hd : d ∣ 40) (hcd : Nat.Coprime c d) := row_coprime k c d hd hcd
  have hsub (c : ℕ) (h : 1 ≤ c) : 40*k+c-1 = 40*k+(c-1) := Nat.add_sub_assoc h (40*k)
  refine ⟨gamma_one (u := 13*k+7) (v := 7*k) (hc 3 20 (by decide) (by decide)) (by omega) (by omega) ?_,
    gamma_one (u := 5*k+3) (v := 15*k+8) (hc 23 4 (by decide) (by decide)) (by omega) (by omega) ?_,
    gamma_one (u := 10*k+7) (v := 10*k+6) (hc 27 2 (by decide) (by decide)) (by omega) (by omega) ?_,
    gamma_one (u := 15*k+12) (v := 5*k+3) (hc 29 4 (by decide) (by decide)) (by omega) (by omega) ?_,
    gamma_one (u := 6*k+6) (v := 14*k+11) (hc 33 10 (by decide) (by decide)) (by omega) (by omega) ?_⟩
  all_goals simp [hsub]; ring

end D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

namespace D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

private noncomputable def block (t : ℤ) (j : ℕ) : ℕ :=
  if t = 1 then
    match j with | 0 => 3 | 1 => 7 | 2 => 17 | 3 => 19 | 4 => 23 | _ => 43
  else
    match j with | 0 => 3 | 1 => 23 | 2 => 27 | 3 => 29 | 4 => 33 | _ => 43

private noncomputable def sequence (w : ℕ → ℤ) (n : ℕ) : ℕ :=
  40 * (n / 5) + block (w (n / 5)) (n % 5)

private theorem sequence_block (w : ℕ → ℤ) (k j : ℕ) (hj : j ≤ 5) :
    sequence w (5*k+j) = 40*k + block (w k) j := by
  by_cases h : j < 5
  · have hd : (5*k+j)/5 = k := by omega
    have hr : (5*k+j)%5 = j := by omega
    simp only [sequence, hd, hr]
  · have h5 : j = 5 := by omega
    subst j
    have hd : (5*k+5)/5 = k+1 := by omega
    have hr : (5*k+5)%5 = 0 := by omega
    simp only [sequence, hd, hr]
    simp [block]; omega

private theorem sequence_bounds (w : ℕ → ℤ) (n : ℕ) :
    0 < sequence w n ∧ 8*n ≤ sequence w n + 9 ∧ sequence w n ≤ 8*n+15 := by
  have hr : n%5 < 5 := Nat.mod_lt n (by decide)
  have hn := Nat.mod_add_div n 5
  unfold sequence
  generalize w (n/5) = t
  generalize n%5 = j at *
  interval_cases j <;> by_cases ht : t = 1 <;> simp [block, ht] <;> omega

private theorem sequence_step (w : ℕ → ℤ) (n : ℕ) :
    sequence w n + 2 ≤ sequence w (n+1) ∧ sequence w (n+1) ≤ sequence w n + 20 := by
  have hr : n%5 < 5 := Nat.mod_lt n (by decide)
  have hn : 5*(n/5) + n%5 = n := Nat.div_add_mod n 5
  have h := sequence_block w (n/5) (n%5) (by omega)
  have h' := sequence_block w (n/5) (n%5+1) (by omega)
  rw [hn] at h
  have hn' : 5*(n/5)+(n%5+1)=n+1 := by omega
  rw [hn'] at h'
  rw [h, h']
  generalize w (n/5) = t
  generalize n%5 = j at *
  interval_cases j <;> by_cases ht : t = 1 <;> simp [block, ht]

private theorem sequence_strictMono (w : ℕ → ℤ) : StrictMono (sequence w) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := (sequence_step w n).1
  omega

private theorem block_edge (w : ℕ → ℤ) (k j : ℕ) (hj : j < 5) :
    Gamma (sequence w (5*k+j)) (sequence w (5*k+j+1)) =
      if w k = 1 then 0 else 1 := by
  have he : 5*k+j+1=5*k+(j+1) := Nat.add_assoc (5*k) j 1
  rw [he, sequence_block w k j (by omega), sequence_block w k (j+1) (by omega)]
  rcases z_rows k with ⟨hz0,hz1,hz2,hz3,hz4⟩
  rcases o_rows k with ⟨ho0,ho1,ho2,ho3,ho4⟩
  interval_cases j <;> by_cases ht : w k = 1 <;>
    simp [block, ht, hz0,hz1,hz2,hz3,hz4,ho0,ho1,ho2,ho3,ho4]

private theorem sequence_edge (w : ℕ → ℤ) (n : ℕ) :
    Gamma (sequence w n) (sequence w (n+1)) = if w (n/5) = 1 then 0 else 1 := by
  have h := block_edge w (n/5) (n%5) (Nat.mod_lt n (by decide))
  have hn : 5*(n/5)+n%5=n := Nat.div_add_mod n 5
  rw [hn] at h
  exact h

end D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth

namespace D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth


private theorem w_binary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 k = 0 ∨
      D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 k = 1 := by
  rcases hp1.eq_or_lt with h | h
  · subst p
    simp [D5.S1.Words.Mechanical.lowerMechanicalLetter]
  · exact D5.S1.Words.Mechanical.lowerMechanicalLetter_eq_zero_or_one hp0 h k

private theorem count_succ (w : ℕ → ℤ) (N : ℕ) :
    zeroCount (sequence w) (N+1) = zeroCount (sequence w) N +
      if w (N/5) = 1 then 1 else 0 := by
  have hi : Finset.Icc 1 (N+1) = insert (N+1) (Finset.Icc 1 N) := by
    simpa only [Order.succ_eq_add_one] using
      (Finset.insert_Icc_right_eq_Icc_succ (a := 1) (b := N)
        (by simp)).symm
  have hnot : N+1 ∉ Finset.Icc 1 N := by simp
  have hnot' : N+1 ∉ ((Finset.Icc 1 N).filter fun n =>
      Gamma (sequence w (n-1)) (sequence w n) = 0) := by
    intro h
    exact hnot (Finset.mem_filter.mp h).1
  have hedge := sequence_edge w N
  unfold zeroCount
  rw [hi, Finset.filter_insert]
  simp only [Nat.add_sub_cancel, hedge]
  by_cases hw : w (N/5) = 1 <;> simp [hw, hnot']

private theorem count_formula (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N : ℤ) =
      5 * ⌊((N/5 : ℕ) : ℝ)*p⌋ + (N%5 : ℕ) * D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 (N/5) := by
  induction N
  case zero => simp [zeroCount]
  case succ N ih =>
    rw [count_succ, Nat.cast_add, ih]
    have hi : ((if D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 (N/5) = 1 then 1 else 0 : ℕ) : ℤ) = D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 (N/5) := by
      rcases w_binary p hp0 hp1 (N/5) with h | h <;> simp [h]
    rw [hi]
    have hr : N%5 < 5 := Nat.mod_lt N (by decide)
    by_cases h4 : N%5 = 4
    · have hd : (N+1)/5=N/5+1 := by omega
      have hm : (N+1)%5=0 := Nat.succ_mod_succ_eq_zero_iff.mpr h4
      rw [hd, hm, h4]
      norm_num only [Nat.cast_ofNat, Nat.cast_zero, zero_mul, add_zero]
      simp only [D5.S1.Words.Mechanical.lowerMechanicalLetter, zero_add]
      ring
    · have hd : (N+1)/5=N/5 := by omega
      have hm : (N+1)%5=N%5+1 := by omega
      rw [hd, hm]
      push_cast
      ring

private theorem discrepancy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    0 ≤ p * (N : ℝ) - zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N ∧
      p * (N : ℝ) - zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N < 5 := by
  let K : ℕ := N/5
  let r : ℕ := N%5
  let e : ℝ := (K : ℝ)*p - (⌊(K : ℝ)*p⌋ : ℤ)
  let f : ℝ := ((K+1 : ℕ) : ℝ)*p - (⌊((K+1 : ℕ) : ℝ)*p⌋ : ℤ)
  have he0 : 0 ≤ e := sub_nonneg.mpr (Int.floor_le _)
  have he1 : e < 1 := Int.fract_lt_one _
  have hf0 : 0 ≤ f := sub_nonneg.mpr (Int.floor_le _)
  have hf1 : f < 1 := Int.fract_lt_one _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr5 : (r : ℝ) < 5 := by exact_mod_cast (Nat.mod_lt N (by decide : 0 < 5))
  have hN : (N : ℝ) = 5*(K : ℝ)+(r : ℝ) := by
    exact_mod_cast (show N = 5*K+r by dsimp [K,r]; omega)
  have hC : (zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N : ℝ) =
      5 * (⌊(K : ℝ)*p⌋ : ℤ) + (r : ℝ) * (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0 K : ℝ) := by
    exact_mod_cast count_formula p hp0 hp1 N
  have hidentity : p * (N : ℝ) - zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N =
      (5 - (r : ℝ))*e + (r : ℝ)*f := by
    rw [hC, hN]
    dsimp [e,f,D5.S1.Words.Mechanical.lowerMechanicalLetter]
    push_cast
    simp only [Int.fract, zero_add]
    ring
  rw [hidentity]
  constructor
  · exact add_nonneg (mul_nonneg (by linarith) he0) (mul_nonneg hr0 hf0)
  · have he := mul_lt_mul_of_pos_left he1 (by linarith : 0 < 5-(r : ℝ))
    have hf := mul_le_mul_of_nonneg_left hf1.le hr0
    nlinarith

private theorem density (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Filter.Tendsto (fun N : ℕ => (zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N : ℝ) / N)
      Filter.atTop (nhds p) := by
  have hz : Filter.Tendsto (fun N : ℕ => (5 : ℝ)/N) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 5
  have hl : Filter.Tendsto (fun N : ℕ => p - (5 : ℝ)/N) Filter.atTop (nhds p) := by
    simpa using tendsto_const_nhds.sub hz
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := Nat.cast_pos'.mpr hN
    have hd := discrepancy p hp0 hp1 N
    calc
      p - (5 : ℝ)/N = (p*(N : ℝ)-5)/N := by field_simp
      _ ≤ (zeroCount (sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0)) N : ℝ)/N :=
        (div_le_div_iff_of_pos_right hn).mpr (by linarith)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (0 : ℝ) < N := Nat.cast_pos'.mpr hN
    have hd := discrepancy p hp0 hp1 N
    exact (div_le_iff₀ hn).mpr (by linarith)

theorem result : claim := by
  intro p hp0 hp1
  refine ⟨sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0), sequence_strictMono _, fun n => (sequence_bounds _ n).1,
    ⟨1,23,?_⟩, density p hp0 hp1⟩
  intro n hn
  simp only [pow_one]
  exact_mod_cast (show sequence (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0) n ≤ 23*n by
    have h := (sequence_bounds (D5.S1.Words.Mechanical.lowerMechanicalLetter p 0) n).2.2
    omega)

end D5.S3.Arith.Density.ChuMillerTreschGammaSplitGrowth
