/- GID: D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaged Ricci curvature of the Zeitlin metric. -/

import D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Algebra.ZeitlinSixJ.RicciLimit

open Finset Filter Polynomial
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Racah

noncomputable def rPlus (l N : ℕ) : ℝ :=
  (N : ℝ) / (4 / ((N : ℝ)^2 - 1)) *
    ∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
      if Odd (i+1+(j+1)+l) then
        casimir l * (2*((i+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (i+1) * casimir (j+1)) * W N l (i+1) (j+1)^2
      else 0

noncomputable def rMinus (l N : ℕ) : ℝ :=
  (N : ℝ) / (4 / ((N : ℝ)^2 - 1)) *
    ∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
      if Odd (i+1+(j+1)+l) then
        (casimir (i+1) - casimir (j+1))^2 *
          (2*((i+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (i+1) * casimir (j+1) * casimir l) * W N l (i+1) (j+1)^2
      else 0

noncomputable def rTilde (l N : ℕ) : ℝ :=
  (rPlus l N - rMinus l N) / ((N : ℝ)^2 - 1)

def claim : Prop := ∀ l : ℕ, 2 ≤ l →
  Tendsto (fun N : ℕ => rTilde l N) atTop (nhds (-((harmonic l : ℝ) - 1) / 2)) ∧
  ∃ N0 : ℕ, ∀ N ≥ N0, rTilde l N < 0

private lemma racah_coefficient_tendsto_zero (j k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (racahCoefficient N j k : ℝ)) atTop (nhds 0) := by
  let q : ℝ[X] := ∏ r ∈ range (2*k+1),
    (Polynomial.X + Polynomial.C ((r : ℝ) - k))
  have hdeg : q.natDegree = 2*k+1 := by
    dsimp [q]
    rw [Polynomial.natDegree_prod_of_monic (range (2*k+1))
      (fun r : ℕ => Polynomial.X + Polynomial.C ((r : ℝ)-k))
      (fun r _ => Polynomial.monic_X_add_C ((r : ℝ)-k))]
    simp only [Polynomial.natDegree_X_add_C, sum_const, card_range,
      smul_eq_mul, mul_one]
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) / q.eval (N : ℝ)) atTop (nhds 0) := by
    have h := Polynomial.div_tendsto_atTop_zero_of_degree_lt
      (Polynomial.X : ℝ[X]) q (Polynomial.degree_lt_degree (by simp [hdeg]; omega))
    simpa only [Function.comp_def, Polynomial.eval_X] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : ∀ᶠ N : ℕ in atTop,
      ((N : ℚ)*Nat.factorial (N-k-1)/Nat.factorial (N+k) : ℚ) =
        (N : ℚ) / (∏ r ∈ range (2*k+1), ((N : ℚ)-k+r)) := by
    filter_upwards [eventually_gt_atTop k] with N hN
    have hn : k+1 ≤ N := by omega
    have hf := congrArg (fun n : ℕ => (n : ℚ))
      (Nat.factorial_mul_ascFactorial (N-k-1) (2*k+1))
    rw [show N-k-1+(2*k+1) = N+k by omega,
      show N-k-1+1 = N-k by omega, Nat.ascFactorial_eq_prod_range] at hf
    simp only [Nat.cast_mul, Nat.cast_prod] at hf
    have hp : (∏ r ∈ range (2*k+1), ((N-k+r : ℕ) : ℚ)) =
        ∏ r ∈ range (2*k+1), ((N : ℚ)-k+r) := by
      apply prod_congr rfl
      intro r _
      rw [Nat.cast_add, Nat.cast_sub (by omega : k ≤ N)]
    rw [hp] at hf
    have hf0 : (Nat.factorial (N-k-1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    rw [← hf]
    field_simp
  have hcast : ∀ᶠ N : ℕ in atTop,
      (racahCoefficient N j k : ℝ) =
        ((-1 : ℝ)^k * Nat.choose j k * Nat.choose (j+k) k) * ((N : ℝ)/q.eval (N : ℝ)) := by
    filter_upwards [heq] with N hN
    simp only [racahCoefficient, hN, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_one, Rat.cast_natCast, Rat.cast_div, Rat.cast_prod, Rat.cast_sub, Rat.cast_add]
    simp only [q, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    congr 2
    apply prod_congr rfl
    intro r _
    ring
  have h := hlim.const_mul ((-1 : ℝ)^k * Nat.choose j k * Nat.choose (j+k) k)
  simpa only [mul_zero] using h.congr' (Filter.EventuallyEq.symm hcast)

private lemma racah_polynomial_tendsto_one (j i : ℕ) :
    Tendsto (fun N : ℕ => (racahPolynomial N j i : ℝ)) atTop (nhds 1) := by
  have hsum := tendsto_finsetSum (range j) (fun k _ =>
    (racah_coefficient_tendsto_zero j (k+1) (by omega)).mul_const
      (racahMonomial (k+1) i : ℝ))
  simpa [racahPolynomial] using tendsto_const_nhds.add hsum

private noncomputable def oddMoment (b c N : ℕ) : ℝ :=
  ∑ i ∈ range (N-1), if Odd (i+1+b+c) then
    casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2 else 0

private lemma odd_moment_eq (b c N : ℕ) (hb : 1 ≤ b ∧ b < N)
    (hc : 1 ≤ c ∧ c < N) (hN : 2 ≤ N) :
    (N : ℝ)*oddMoment b c N =
      ((casimir b+casimir c)*(1-(racahPolynomial N b c : ℝ)) -
        2*casimir b*casimir c/((N : ℝ)^2-1))/2 := by
  obtain ⟨_, hsigned, hunsigned, _⟩ :=
    D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.result N hN
  have hs := hsigned b c hb hc
  have hu := hunsigned b c hb hc
  have hp := D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion.racah_expansion_open
    N c b hN hc.2 hb.2
  have hsplit : oddMoment b c N =
      ((∑ i ∈ range (N-1),
        casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2) -
      (-1 : ℝ)^(b+c)*(∑ i ∈ range (N-1),
        (-1 : ℝ)^(i+1)*casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*
          W N (i+1) b c^2))/2 := by
    rw [oddMoment, mul_sum, ← sum_sub_distrib, sum_div]
    apply sum_congr rfl
    intro i _
    rw [show (-1 : ℝ)^(b+c) * ((-1 : ℝ)^(i+1)*casimir (i+1)*
      (2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2) =
      (-1 : ℝ)^(i+1+b+c) *
        (casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2) by
          rw [show i+1+b+c = (b+c)+(i+1) by omega, pow_add]; ring]
    by_cases ho : Odd (i+1+b+c)
    · rw [if_pos ho, ho.neg_one_pow]
      ring
    · rw [if_neg ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
      ring
  have hsign : (-1 : ℝ)^(b+c)*(-1 : ℝ)^(N+1) = (-1 : ℝ)^(N-1+c+b) := by
    rw [← pow_add, show b+c+(N+1) = (N-1+c+b)+2 by omega, pow_add]
    norm_num
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (N : ℝ)^2-1 ≠ 0 := by nlinarith
  rw [hsplit, hu, hs]
  rw [show (-1 : ℝ)^(b+c) * ((-1 : ℝ)^(N+1) *
    (casimir b+casimir c)*Wij N c b) =
      (-1 : ℝ)^(N-1+c+b)*(casimir b+casimir c)*Wij N c b by
        rw [← mul_assoc, ← mul_assoc, hsign]]
  field_simp [hn0, hd0] at hp ⊢
  linear_combination -(casimir b+casimir c)*((N : ℝ)^2-1)*hp

private lemma odd_moment_tendsto_zero (b c : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    Tendsto (fun N : ℕ => (N : ℝ)*oddMoment b c N) atTop (nhds 0) := by
  have hpoly := racah_polynomial_tendsto_one b c
  have hden : Tendsto (fun N : ℕ => ((N : ℝ)^2-1)⁻¹) atTop (nhds 0) := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ)^2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by omega : 2 ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) ht)
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub hpoly).const_mul (casimir b+casimir c)).sub
    (hden.const_mul (2*casimir b*casimir c))
  have heq : ∀ᶠ N : ℕ in atTop,
      (N : ℝ)*oddMoment b c N =
        ((casimir b+casimir c)*(1-(racahPolynomial N b c : ℝ)) -
          2*casimir b*casimir c/((N : ℝ)^2-1))/2 := by
    filter_upwards [eventually_gt_atTop (max b c)] with N hN
    exact odd_moment_eq b c N ⟨hb, lt_of_le_of_lt (le_max_left _ _) hN⟩
      ⟨hc, lt_of_le_of_lt (le_max_right _ _) hN⟩ (by omega)
  simpa [div_eq_mul_inv] using (hlim.div_const 2).congr' (Filter.EventuallyEq.symm heq)

/-- A fixed odd-parity triple has vanishing squared six-j mass after multiplication by N. -/
theorem fixed_labels_odd_tendsto_zero (a b c : ℕ) (ho : Odd (a + b + c)) :
    Tendsto (fun N : ℕ => (N : ℝ)*W N a b c^2) atTop (nhds 0) := by
  by_cases hz : a=0 ∨ b=0 ∨ c=0
  · have hw : ∀ N, W N a b c=0 := by
      intro N
      have had : ¬ admissible (2*a) (2*b) (2*c) (N-1) (N-1) (N-1) := by
        intro h
        have ht := h.1
        have hodd := Nat.odd_iff.mp ho
        unfold triangle at ht
        rcases hz with h | h | h <;> omega
      simp [W, sixJ, had]
    simp [hw]
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have hc : 1 ≤ c := by omega
  have hweight : 0 < casimir a*(2*(a : ℝ)+1) := by
    have har : (0 : ℝ) < a := by exact_mod_cast ha
    unfold casimir
    positivity
  have hlim := (odd_moment_tendsto_zero b c hb hc).div_const
    (casimir a*(2*(a : ℝ)+1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hlim)
  · exact Eventually.of_forall (fun N => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · filter_upwards [eventually_gt_atTop a] with N hN
    have hterm : casimir a*(2*(a : ℝ)+1)*W N a b c^2 ≤ oddMoment b c N := by
      have hmem : a-1 ∈ range (N-1) := mem_range.mpr (by omega)
      have hnonneg : ∀ i ∈ range (N-1),
          0 ≤ if Odd (i+1+b+c) then
            casimir (i+1)*(2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2 else 0 := by
        intro i _
        split_ifs
        · unfold casimir
          positivity
        · exact le_rfl
      have h := single_le_sum hnonneg hmem
      simpa [oddMoment, show a-1+1=a by omega, ho] using h
    apply (le_div_iff₀ hweight).mpr
    nlinarith [mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

private lemma W_first (N a b c : ℕ) : W N a b c = W N b a c := by
  rw [D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.W_swap]
  unfold W
  exact D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.sixJ_cycle_columns _ _ _ _ _ _

private lemma W_support (N a b c : ℕ) (h : a+b < c ∨ b+c < a ∨ c+a < b) :
    W N a b c = 0 := by
  have hn : ¬ admissible (2*a) (2*b) (2*c) (N-1) (N-1) (N-1) := by
    intro ha
    have ht := ha.1
    unfold triangle at ht
    omega
  simp [W, sixJ, hn]

private noncomputable def positiveRow (l N k : ℕ) : ℝ :=
  if k < N-1 then
    (N : ℝ) * ∑ j ∈ range (N-1),
      if Odd (k+1+(j+1)+l) then
        casimir l * (2*((k+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (k+1) * casimir (j+1)) * W N l (k+1) (j+1)^2
      else 0
  else 0

private lemma positiveRow_nonneg (l N k : ℕ) : 0 ≤ positiveRow l N k := by
  unfold positiveRow
  split_ifs
  · apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro j _
    split_ifs
    · unfold casimir
      positivity
    · exact le_rfl
  · exact le_rfl

private lemma positiveRow_tendsto_zero (l k : ℕ) :
    Tendsto (fun N => positiveRow l N k) atTop (nhds 0) := by
  let f : ℕ → ℕ → ℝ := fun N j =>
    if Odd (k+1+(j+1)+l) then
      (casimir l * (2*((k+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
        (casimir (k+1) * casimir (j+1))) * ((N : ℝ)*W N l (k+1) (j+1)^2)
    else 0
  have hf (j : ℕ) : Tendsto (fun N => f N j) atTop (nhds 0) := by
    dsimp [f]
    by_cases ho : Odd (k+1+(j+1)+l)
    · simp only [if_pos ho]
      have h := fixed_labels_odd_tendsto_zero l (k+1) (j+1)
        (by convert ho using 1; omega)
      simpa using h.const_mul
        (casimir l * (2*((k+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
          (casimir (k+1) * casimir (j+1)))
    · simp only [if_neg ho]
      exact tendsto_const_nhds
  have ht := tendsto_finsetSum (range (k+l+1)) (fun j _ => hf j)
  have he : ∀ᶠ N : ℕ in atTop,
      positiveRow l N k = ∑ j ∈ range (k+l+1), f N j := by
    filter_upwards [eventually_gt_atTop (k+l+2)] with N hN
    rw [positiveRow, if_pos (by omega), mul_sum]
    have hterm (j : ℕ) :
        (N : ℝ) * (if Odd (k+1+(j+1)+l) then
          casimir l * (2*((k+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
            (casimir (k+1) * casimir (j+1)) * W N l (k+1) (j+1)^2 else 0) =
          f N j := by
      dsimp [f]
      split_ifs <;> ring
    simp_rw [hterm]
    symm
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hgt : k+l+1 ≤ j := by simpa using hj
    have hw := W_support N l (k+1) (j+1) (Or.inl (by omega))
    simp [f, hw]
  simpa using ht.congr' (Filter.EventuallyEq.symm he)

private noncomputable def rowBound (l k : ℕ) : ℝ :=
  if k+1=l then 1 else
    casimir l * (2*((k+1 : ℕ) : ℝ)+1) /
      (casimir (k+1) * |((k+1 : ℕ) : ℝ)-l| * (((k+1 : ℕ) : ℝ)+l+1))

private lemma rowBound_nonneg (l k : ℕ) : 0 ≤ rowBound l k := by
  unfold rowBound
  split_ifs
  · norm_num
  · unfold casimir
    positivity

private lemma positiveRow_le (l N k : ℕ) (hl : 2 ≤ l) (hlN : l < N)
    (hkl : k+1 ≠ l) : positiveRow l N k ≤ rowBound l k := by
  by_cases hk : k < N-1
  · have hN : 2 ≤ N := by omega
    have hkN : k+1 < N := by omega
    let C := casimir l * (2*((k+1 : ℕ) : ℝ)+1) / casimir (k+1)
    have hC : 0 ≤ C := by dsimp [C]; unfold casimir; positivity
    have he : W N l (k+1) = fun j => W N j (k+1) l := by
      funext j
      rw [D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.W_swap N l (k+1) j,
        W_first N l j (k+1), D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.W_swap N j l (k+1)]
    have hinv := (D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.result N hN).1
      (k+1) l ⟨by omega, hkN⟩ ⟨by omega, hlN⟩ hkl
    have hb : positiveRow l N k ≤ (N : ℝ)*C*
        ∑ j ∈ range (N-1), (2*((j+1 : ℕ) : ℝ)+1)/casimir (j+1)*
          W N (j+1) (k+1) l^2 := by
      rw [positiveRow, if_pos hk, mul_assoc]
      simp only [mul_sum]
      apply sum_le_sum
      intro j _
      rw [he]
      split_ifs
      · dsimp [C]
        apply le_of_eq
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · have hj : 0 ≤ (2*((j+1 : ℕ) : ℝ)+1)/casimir (j+1)*
            W N (j+1) (k+1) l^2 := by unfold casimir; positivity
        simpa using mul_nonneg (Nat.cast_nonneg N) (mul_nonneg hC hj)
    rw [hinv] at hb
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have heq : (N : ℝ)*C*(1/((N : ℝ)*|((k+1 : ℕ) : ℝ)-l| *
        (((k+1 : ℕ) : ℝ)+l+1))) = rowBound l k := by
      rw [rowBound, if_neg hkl]
      dsimp [C]
      field_simp [hn0]
    rwa [heq] at hb
  · rw [positiveRow, if_neg hk]
    exact rowBound_nonneg l k

private lemma rowBound_summable (l : ℕ) : Summable (rowBound l) := by
  have hs : Summable (fun k : ℕ => 8*casimir l / ((k+1 : ℕ) : ℝ)^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2))
    simpa only [mul_one_div] using h.mul_left (8*casimir l)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (2*l+1)] with k hk
  have hne : k+1 ≠ l := by omega
  have hkpos : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  have hlr : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hkr : 2*(l : ℝ)+1 ≤ k := by exact_mod_cast hk
  rw [Real.norm_eq_abs, abs_of_nonneg (rowBound_nonneg l k), rowBound, if_neg hne,
    abs_of_nonneg (by push_cast; linarith : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ)-l)]
  have hc : 0 ≤ casimir l := by unfold casimir; positivity
  have hd : 0 < casimir (k+1) * (((k+1 : ℕ) : ℝ)-l) *
      (((k+1 : ℕ) : ℝ)+l+1) := by
    have : (0 : ℝ) < ((k+1 : ℕ) : ℝ)-l := by push_cast; linarith
    unfold casimir
    positivity
  apply (div_le_div_iff₀ hd (sq_pos_of_pos hkpos)).mpr
  let x : ℝ := ((k+1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ k+1)
  have h1 : x ≤ 2*(x-l) := by dsimp [x]; push_cast; linarith
  have h2 : x ≤ x+l+1 := by linarith
  have h3 : 2*x+1 ≤ 3*x := by linarith
  have h4 : x ≤ casimir (k+1) := by unfold casimir; change x ≤ x*(x+1); nlinarith
  have ha : 0 ≤ x-l := by linarith
  have hb : 0 ≤ x+l+1 := by linarith
  have h5 := mul_le_mul h4 h1 (le_of_lt hkpos)
    (by unfold casimir; positivity : 0 ≤ casimir (k+1))
  have h6 := mul_le_mul h5 h2 (le_of_lt hkpos)
    (mul_nonneg (by unfold casimir; positivity) (mul_nonneg (by norm_num) ha))
  have h7 := mul_le_mul_of_nonneg_right h3 (sq_nonneg x)
  have h8 := mul_le_mul_of_nonneg_left h6 hc
  have h9 := mul_le_mul_of_nonneg_left h7 hc
  change casimir l * (2*x+1)*x^2 ≤
    8*casimir l*(casimir (k+1)*(x-l)*(x+l+1))
  nlinarith [mul_nonneg hc (mul_nonneg (by unfold casimir; positivity : 0 ≤ casimir (k+1))
    (mul_nonneg ha hb))]

private lemma normalized_positive_eq (l N : ℕ) (hN : 2 ≤ N) :
    rPlus l N / ((N : ℝ)^2-1) = (∑' k, positiveRow l N k)/4 := by
  have ht : (∑' k, positiveRow l N k) =
      ∑ k ∈ range (N-1), positiveRow l N k := by
    apply tsum_eq_sum
    intro k hk
    have : ¬k < N-1 := by simpa using hk
    simp [positiveRow, this]
  rw [ht]
  have hs : (∑ k ∈ range (N-1), positiveRow l N k) =
      (N : ℝ) * ∑ k ∈ range (N-1), ∑ j ∈ range (N-1),
        if Odd (k+1+(j+1)+l) then
          casimir l * (2*((k+1 : ℕ) : ℝ)+1) * (2*((j+1 : ℕ) : ℝ)+1) /
            (casimir (k+1) * casimir (j+1)) * W N l (k+1) (j+1)^2
        else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    simp only [positiveRow, if_pos (mem_range.mp hk)]
  rw [hs, rPlus]
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (N : ℝ)^2-1 ≠ 0 := by nlinarith
  field_simp [hd]

/-- The normalized positive contribution vanishes for each fixed label at least two. -/
theorem rPlus_tendsto_zero (l : ℕ) (hl : 2 ≤ l) :
    Tendsto (fun N => rPlus l N / ((N : ℝ)^2-1)) atTop (nhds 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k, ‖positiveRow l N k‖ ≤ rowBound l k := by
    have hdiag := (positiveRow_tendsto_zero l (l-1)).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [eventually_gt_atTop l, hdiag] with N hlN hdiag k
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveRow_nonneg l N k)]
    by_cases he : k+1=l
    · have hk : k=l-1 := by omega
      rw [rowBound, if_pos he, hk]
      exact le_of_lt hdiag
    · exact positiveRow_le l N k hl hlN he
  have h := tendsto_tsum_of_dominated_convergence (rowBound_summable l)
    (fun k => positiveRow_tendsto_zero l k) hb
  have he : ∀ᶠ N : ℕ in atTop,
      rPlus l N / ((N : ℝ)^2-1) = (∑' k, positiveRow l N k)/4 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact normalized_positive_eq l N hN
  simpa using (h.div_const 4).congr' (Filter.EventuallyEq.symm he)

end D5.S3.Quantum.Algebra.ZeitlinSixJ.RicciLimit
