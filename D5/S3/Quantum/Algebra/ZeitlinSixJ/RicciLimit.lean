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
open D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Endpoint
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Orthogonality
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Inverse
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Parity

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
      unfold W
      rw [D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.sixJ_swap_columns,
        D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.sixJ_cycle_columns]
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

private lemma odd_mass_ordered (N b c : ℕ) (hN : 2 ≤ N)
    (hb : b < N) (hc : c < N) (hbc : b ≤ c) :
    (∑ i ∈ range N, if Odd (i+b+c) then
      (2*(i : ℝ)+1)*W N i b c^2 else 0) =
        (1/(N : ℝ)+(-1 : ℝ)^(b+c+N)*Wij N c b)/2 := by
  let n := N-1
  have hn : n+1=N := by dsimp [n]; omega
  have hbn : b ≤ n := by dsimp [n]; omega
  have hcn : c ≤ n := by dsimp [n]; omega
  obtain ⟨t, ht, hlabel⟩ := channel_center_label n b c hbn hcn hbc
  let k : Fin (channelWidth n b c+1) := ⟨t, by omega⟩
  have hk : channelLabel n b c k.val = n := hlabel
  let f : ℕ → ℝ := fun i => if Odd (i+b+c) then
    (2*(i : ℝ)+1)*W N i b c^2 else 0
  have hsum : (∑ i : Fin (channelWidth n b c+1), f (c-b+i.val)) =
      ∑ i ∈ range N, f i := by
    unfold channelWidth
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (c-b+i))]
    rw [← hn]
    apply sum_shifted_support f n (min n (b+c)) (c-b) (by omega) (by omega)
    intro i hi
    have had : ¬ admissible (2*i) (2*b) (2*c) (N-1) (N-1) (N-1) := by
      intro ha
      have h1 := ha.1
      have h2 := ha.2.1
      unfold triangle at h1 h2
      dsimp [n] at hi
      omega
    simp [f, W, sixJ, had]
  have hsquare (i : Fin (channelWidth n b c+1)) :
      physicalU n b c k i^2 = (N : ℝ)*(2*((c-b+i.val : ℕ) : ℝ)+1)*
        W N (c-b+i.val) b c^2 := by
    unfold physicalU
    rw [hk, mul_pow, Real.sq_sqrt (by positivity)]
    have hw := central_symbol_is_W N (c-b+i.val) b c
    rw [← hn, Nat.add_sub_cancel_right] at hw
    rw [hw, hn]
    push_cast
    ring
  have hu := congrArg (fun A => A k k) (physicalU_orthogonality n b c hbn hcn hbc)
  have hx := congrArg (fun A => A k k) (physical_signed_addition n b c hbn hcn hbc)
  have hz : physicalZ n b c k k = (-1 : ℝ)^n*(N : ℝ)*Wij N c b := by
    unfold physicalZ indexParity
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Nat.zero_add]
    change (-1 : ℝ)^channelBase n b c *
      ((-1 : ℝ)^k.val * normalizedSixJ n (2*c) (channelLabel n b c k.val)
        n (2*b) (channelLabel n b c k.val) * (-1 : ℝ)^k.val) = _
    rw [hk, normalizedSixJ]
    have hw : sixJ n (2*c) n n (2*b) n = Wij N c b := by
      unfold Wij
      rw [← hn, Nat.add_sub_cancel_right]
      exact sixJ_swap_columns _ _ _ _ _ _
    rw [hw, show (((n+1 : ℕ) : ℝ)*((n+1 : ℕ) : ℝ)) =
      ((n+1 : ℕ) : ℝ)^2 by ring, Real.sqrt_sq (by positivity), hn]
    rw [show (-1 : ℝ)^channelBase n b c *
      ((-1 : ℝ)^k.val * ((N : ℝ)*Wij N c b) * (-1 : ℝ)^k.val) =
      (-1 : ℝ)^(channelBase n b c+k.val+k.val)*(N : ℝ)*Wij N c b by
        rw [pow_add, pow_add]; ring]
    have he : channelBase n b c+k.val+k.val=n := by
      unfold channelLabel at hk
      omega
    rw [he]
  rw [hz] at hx
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at hu
  unfold physicalX at hx
  rw [Matrix.mul_apply] at hx
  simp only [indexParity, Matrix.mul_diagonal, Matrix.transpose_apply] at hx
  have hterm (i : Fin (channelWidth n b c+1)) :
      physicalU n b c k i * physicalU n b c k i -
      (-1 : ℝ)^(b+c)*((physicalU n b c k i * (-1 : ℝ)^(c-b+i.val))*
        physicalU n b c k i) = 2*(N : ℝ)*f (c-b+i.val) := by
    rw [show physicalU n b c k i * physicalU n b c k i -
      (-1 : ℝ)^(b+c)*((physicalU n b c k i * (-1 : ℝ)^(c-b+i.val))*
        physicalU n b c k i) =
      (1-(-1 : ℝ)^(b+c+(c-b+i.val)))*physicalU n b c k i^2 by
        rw [pow_add]; ring, hsquare]
    dsimp [f]
    by_cases ho : Odd (c-b+i.val+b+c)
    · rw [if_pos ho, show b+c+(c-b+i.val) = c-b+i.val+b+c by omega,
        ho.neg_one_pow]
      ring
    · rw [if_neg ho, show b+c+(c-b+i.val) = c-b+i.val+b+c by omega,
        (Nat.not_odd_iff_even.mp ho).neg_one_pow]
      ring
  have hm : 1-(-1 : ℝ)^(b+c)*((-1 : ℝ)^n*(N : ℝ)*Wij N c b) =
      2*(N : ℝ)*(∑ i ∈ range N, f i) := by
    calc
      _ = (∑ i, physicalU n b c k i * physicalU n b c k i) -
          (-1 : ℝ)^(b+c)*(∑ i, (physicalU n b c k i * (-1 : ℝ)^(c-b+i.val))*
            physicalU n b c k i) := by rw [hu, hx]
      _ = _ := by
        rw [mul_sum, ← sum_sub_distrib]
        simp_rw [hterm]
        rw [← mul_sum, hsum]
  have hsign : -((-1 : ℝ)^(b+c)*(-1 : ℝ)^n) = (-1 : ℝ)^(b+c+N) := by
    rw [← pow_add, ← hn, show b+c+(n+1)=(b+c+n)+1 by omega, pow_succ]
    ring
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change (∑ i ∈ range N, f i) = _
  rw [← hsign]
  field_simp [hn0]
  linear_combination -hm

private lemma odd_mass (N b c : ℕ) (hN : 2 ≤ N) (hb : b < N) (hc : c < N) :
    (∑ i ∈ range (N-1), if Odd (i+1+b+c) then
      (2*((i+1 : ℕ) : ℝ)+1)*W N (i+1) b c^2 else 0) =
        (1/(N : ℝ)+(-1 : ℝ)^(b+c+N)*Wij N b c)/2 := by
  have hw : Wij N c b = Wij N b c := by
    unfold Wij
    exact sixJ_flip_pair _ _ _ _ _ _
  have hz : (if Odd (0+b+c) then (2*((0 : ℕ) : ℝ)+1)*W N 0 b c^2 else 0)=0 := by
    by_cases ho : Odd (0+b+c)
    · have had : ¬ admissible 0 (2*b) (2*c) (N-1) (N-1) (N-1) := by
        intro ha
        have ht := ha.1
        have hp := Nat.odd_iff.mp ho
        unfold triangle at ht
        omega
      simp [ho, W, sixJ, had]
    · simp only [if_neg ho]
  have hfull : (∑ i ∈ range N, if Odd (i+b+c) then
      (2*(i : ℝ)+1)*W N i b c^2 else 0) =
        (1/(N : ℝ)+(-1 : ℝ)^(b+c+N)*Wij N b c)/2 := by
    by_cases hbc : b ≤ c
    · simpa only [hw] using odd_mass_ordered N b c hN hb hc hbc
    · have h := odd_mass_ordered N c b hN hc hb (by omega)
      convert h using 1
      · apply sum_congr rfl
        intro i _
        rw [W_swap N i b c, show i+b+c=i+c+b by omega]
      · rw [show c+b+N=b+c+N by omega]
  have hshift := sum_range_succ' (fun i => if Odd (i+b+c) then
    (2*(i : ℝ)+1)*W N i b c^2 else 0) (N-1)
  rw [show N-1+1=N by omega] at hshift
  rw [hshift, hz, add_zero] at hfull
  exact hfull

/-- The normalized negative contribution is independent of dimension above the fixed label. -/
theorem rMinus_eq (l N : ℕ) (hl : 2 ≤ l) (hlN : l < N) :
    rMinus l N / ((N : ℝ)^2-1) = ((harmonic l : ℝ)-1)/2 := by
  have hN : 2 ≤ N := by omega
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (N : ℝ)^2-1 ≠ 0 := by nlinarith
  have hl0 : casimir l ≠ 0 := by
    have hp : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    unfold casimir
    positivity
  let f : ℕ → ℕ → ℝ := fun i j => if Odd (i+1+(j+1)+l) then
    (casimir (j+1)-casimir (i+1)) *
      (2*((i+1 : ℕ) : ℝ)+1)*(2*((j+1 : ℕ) : ℝ)+1) /
        (casimir (i+1)*casimir l) * W N l (i+1) (j+1)^2 else 0
  have hsplit : rMinus l N / ((N : ℝ)^2-1) =
      (N : ℝ)/(2*casimir l) * ∑ i ∈ range (N-1),
        (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
          (oddMoment (i+1) l N - casimir (i+1) *
            (∑ j ∈ range (N-1), if Odd (j+1+(i+1)+l) then
              (2*((j+1 : ℕ) : ℝ)+1)*W N (j+1) (i+1) l^2 else 0)) := by
    have ht : (∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
        if Odd (i+1+(j+1)+l) then
          (casimir (i+1)-casimir (j+1))^2 *
            (2*((i+1 : ℕ) : ℝ)+1)*(2*((j+1 : ℕ) : ℝ)+1) /
              (casimir (i+1)*casimir (j+1)*casimir l)*W N l (i+1) (j+1)^2
        else 0) = 2*(∑ i ∈ range (N-1), ∑ j ∈ range (N-1), f i j) := by
      have he : (∑ i ∈ range (N-1), ∑ j ∈ range (N-1),
          if Odd (i+1+(j+1)+l) then
            (casimir (i+1)-casimir (j+1))^2 *
              (2*((i+1 : ℕ) : ℝ)+1)*(2*((j+1 : ℕ) : ℝ)+1) /
                (casimir (i+1)*casimir (j+1)*casimir l)*W N l (i+1) (j+1)^2
          else 0) = ∑ i ∈ range (N-1), ∑ j ∈ range (N-1), (f i j+f j i) := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        dsimp [f]
        rw [show j+1+(i+1)+l=i+1+(j+1)+l by omega, W_swap N l (j+1) (i+1)]
        split_ifs
        · have hi0 : casimir (i+1) ≠ 0 := by unfold casimir; positivity
          have hj0 : casimir (j+1) ≠ 0 := by unfold casimir; positivity
          field_simp [hi0, hj0, hl0]
          ring
        · ring
      rw [he]
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun i j => f j i)]
      ring
    have hrow (i : ℕ) : (∑ j ∈ range (N-1), f i j) =
        (2*((i+1 : ℕ) : ℝ)+1)/(casimir (i+1)*casimir l) *
          (oddMoment (i+1) l N - casimir (i+1)*
            (∑ j ∈ range (N-1), if Odd (j+1+(i+1)+l) then
              (2*((j+1 : ℕ) : ℝ)+1)*W N (j+1) (i+1) l^2 else 0)) := by
      rw [oddMoment, mul_sum, ← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro j _
      dsimp [f]
      have hw : W N l (i+1) (j+1) = W N (j+1) (i+1) l := by
        unfold W
        rw [sixJ_swap_columns, sixJ_cycle_columns]
      rw [hw, show i+1+(j+1)+l=j+1+(i+1)+l by omega]
      split_ifs <;> ring
    rw [rMinus, ht]
    simp_rw [hrow]
    rw [mul_sum]
    simp only [sum_div, mul_sum]
    apply sum_congr rfl
    intro i _
    field_simp [hd0, hl0]
    ring
  rw [hsplit]
  have hrow (i : ℕ) (hi : i ∈ range (N-1)) :
      oddMoment (i+1) l N - casimir (i+1)*
        (∑ j ∈ range (N-1), if Odd (j+1+(i+1)+l) then
          (2*((j+1 : ℕ) : ℝ)+1)*W N (j+1) (i+1) l^2 else 0) =
      casimir l/2 * (1/(N : ℝ)+(-1 : ℝ)^(i+1+l+N)*Wij N (i+1) l) -
        casimir (i+1)*casimir l/((N : ℝ)*((N : ℝ)^2-1)) := by
    have hiN : i+1 < N := by have := mem_range.mp hi; omega
    have hm := odd_moment_eq (i+1) l N ⟨by omega, hiN⟩ ⟨by omega, hlN⟩ hN
    have hp := D5.S3.Quantum.Algebra.ZeitlinSixJ.Expansion.racah_expansion_open
      N l (i+1) hN hlN hiN
    have hw : Wij N l (i+1) = Wij N (i+1) l := by
      unfold Wij
      exact sixJ_flip_pair _ _ _ _ _ _
    rw [hw, show N-1+l+(i+1)=N-1+(i+1)+l by omega] at hp
    rw [← hp] at hm
    have hs : (-1 : ℝ)^(i+1+l+N) = -((-1 : ℝ)^(N-1+(i+1)+l)) := by
      rw [show i+1+l+N=(N-1+(i+1)+l)+1 by omega, pow_succ]
      ring
    rw [odd_mass N (i+1) l hN hiN hlN, hs]
    field_simp [hn0, hd0] at hm ⊢
    linear_combination hm
  have hrows := sum_congr rfl (fun i hi => congrArg
    (fun x : ℝ => (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1)*x) (hrow i hi))
  rw [hrows]
  have he : (∑ i ∈ range (N-1),
      (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
        (casimir l/2*(1/(N : ℝ)+(-1 : ℝ)^(i+1+l+N)*Wij N (i+1) l) -
          casimir (i+1)*casimir l/((N : ℝ)*((N : ℝ)^2-1)))) =
      casimir l/2*(∑ i ∈ range (N-1),
        (2*((i+1 : ℕ) : ℝ)+1)/casimir (i+1) *
          (1/(N : ℝ)+(-1 : ℝ)^(i+1+l+N)*Wij N (i+1) l)) -
        casimir l/((N : ℝ)*((N : ℝ)^2-1)) *
          ∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    have hi0 : casimir (i+1) ≠ 0 := by unfold casimir; positivity
    field_simp [hi0]
  rw [he, (D5.S3.Quantum.Algebra.ZeitlinSixJ.SumRules.result N hN).2.2.2 l ⟨by omega, hlN⟩]
  have hdim : (∑ i ∈ range (N-1), (2*((i+1 : ℕ) : ℝ)+1)) = (N : ℝ)^2-1 := by
    have hc := congrArg (fun x : ℕ => (x : ℝ)) (sum_range_id_mul_two (N-1))
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (by omega : 1 ≤ N-1), Nat.cast_sub (by omega : 1 ≤ N),
      Nat.cast_one] at hc
    simp only [Nat.cast_add, Nat.cast_one, mul_add, sum_add_distrib, ← mul_sum,
      sum_const, card_range, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    nlinarith [hc]
  rw [hdim]
  field_simp [hn0, hd0, hl0]

/-- The averaged Zeitlin Ricci curvature has the harmonic limit and is eventually negative. -/
theorem result : claim := by
  intro l hl
  have hminus : Tendsto (fun N => rMinus l N / ((N : ℝ)^2-1)) atTop
      (nhds (((harmonic l : ℝ)-1)/2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop l] with N hN
    exact (rMinus_eq l N hl hN).symm
  have hlimit : Tendsto (fun N : ℕ => rTilde l N) atTop
      (nhds (-((harmonic l : ℝ)-1)/2)) := by
    simpa only [rTilde, sub_div, zero_sub, neg_div] using
      (rPlus_tendsto_zero l hl).sub hminus
  have hh : 1 < (harmonic l : ℝ) := by
    have hm : harmonic 2 ≤ harmonic l := by
      unfold harmonic
      apply sum_le_sum_of_subset_of_nonneg (range_mono hl)
      intro i _ _
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    have hq : 1 < harmonic l := lt_of_lt_of_le (by norm_num [harmonic, sum_range_succ]) hm
    exact_mod_cast hq
  have hnegative : -((harmonic l : ℝ)-1)/2 < 0 := by linarith
  exact ⟨hlimit, eventually_atTop.mp (hlimit.eventually_lt_const hnegative)⟩

end D5.S3.Quantum.Algebra.ZeitlinSixJ.RicciLimit
