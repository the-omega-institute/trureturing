/- GID: D5/S3/Arith/InterlaceFan/SongA232624LeadingTerm
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/SongA232624LeadingTerm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact leading term for Song's odd-conductor cosine minimal-polynomial difference. -/

/-
admission_basis: open-problem-resolution (#21790; Proved)
The public definitions are the rational cosine minimal polynomial, its coefficient array, and claim.
The result proves every conjunct of claim with no additional hypotheses.
The reciprocal substitution uses Polynomial.homogenize and MvPolynomial.eval₂;
reciprocal_lift_eval applies Polynomial.eval_homogenize.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22136
Declaration names below belong to D5.S3.Arith.InterlaceFan.SongA232624LeadingTerm.
Frozen dependency identities include generated constants of their source owner.
MPR2: proof_shape: definition; escape_witness: none; consumers: MPR2_reflection_coeff, MPR2_reflection, result, claim, MPR2_bridge, a.
Direct frozen dependencies: none.
a: proof_shape: definition; escape_witness: none; consumers: result, claim.
Direct frozen dependencies: none.
claim: proof_shape: definition; escape_witness: none; consumers: result.
Direct frozen dependencies: none.
totient_radical: proof_shape: bind-only; escape_witness: none; consumers: arithmetic_setup.
Direct frozen dependencies: none.
arithmetic_setup: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_half_difference, result.
Direct frozen dependencies: none.
moebius_radical: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_half_difference.
Direct frozen dependencies: none.
reciprocalLift: proof_shape: definition; escape_witness: none; consumers: reciprocal_lift_smul, MPR2_reflection_coeff, reciprocal_lift_injective, reciprocal_lift_eval, reciprocal_lift_coeff_first, reciprocal_lift_monic, reciprocal_lift_trailing, MPR2_reflection, result, reciprocal_lift_coeff_below, primitive_trace_bridge, reciprocal_lift_coeff_top, MPR2_bridge, reciprocal_lift_sub, reciprocal_lift_sum, degree_from_lift, reciprocal_lift_degree_le.
Direct frozen dependencies: none.
reciprocal_lift_sum: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_smul, reciprocal_lift_coeff_first, reciprocal_lift_coeff_below, reciprocal_lift_coeff_top, reciprocal_lift_sub, reciprocal_lift_degree_le.
Direct frozen dependencies: none.
reciprocal_lift_coeff_below: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_trailing.
Direct frozen dependencies: none.
reciprocal_lift_coeff_first: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_injective, reciprocal_lift_trailing, degree_from_lift.
Direct frozen dependencies: none.
reciprocal_lift_trailing: proof_shape: bind-only; escape_witness: none; consumers: degree_from_lift.
Direct frozen dependencies: none.
reciprocal_lift_degree_le: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_monic.
Direct frozen dependencies: none.
reciprocal_lift_coeff_top: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_monic.
Direct frozen dependencies: none.
reciprocal_lift_monic: proof_shape: bind-only; escape_witness: none; consumers: primitive_trace_bridge.
Direct frozen dependencies: none.
reciprocal_lift_eval: proof_shape: bind-only; escape_witness: none; consumers: primitive_trace_bridge.
Direct frozen dependencies: none.
reciprocal_lift_sub: proof_shape: bind-only; escape_witness: none; consumers: reciprocal_lift_injective, result.
Direct frozen dependencies: none.
reciprocal_lift_smul: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: none.
reciprocal_lift_injective: proof_shape: bind-only; escape_witness: none; consumers: MPR2_reflection.
Direct frozen dependencies: none.
trace_minpoly_degree: proof_shape: content; escape_witness: trace_minpoly_degree; consumers: primitive_trace_bridge.
Direct frozen dependencies: none.
zeta_trace: proof_shape: bind-only; escape_witness: none; consumers: MPR2_reflection, MPR2_bridge.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
zeta_nonreal: proof_shape: bind-only; escape_witness: none; consumers: MPR2_reflection, MPR2_bridge.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta.eq_1; statement_id: sha256:4dbb1a5f4ecfb71781c968b4f51e3f9fca799113d5fcb9d0016744e44ccba9e8
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
primitive_neg: proof_shape: bind-only; escape_witness: none; consumers: MPR2_reflection, cyclotomic_reflection.
Direct frozen dependencies: none.
cyclotomic_reflection: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_half_difference.
Direct frozen dependencies: none.
normalizedCyclo: proof_shape: definition; escape_witness: none; consumers: normalizedCyclo_constant, cycloUnit_prod, cyclotomic_initial, cycloUnit_val, normalizedCyclo_prod, cycloUnit.
Direct frozen dependencies: none.
normalizedCyclo_constant: proof_shape: bind-only; escape_witness: none; consumers: cycloUnit_val, cycloUnit.
Direct frozen dependencies: none.
cycloUnit: proof_shape: definition; escape_witness: none; consumers: cyclotomic_moebius_series, cycloUnit_prod, cyclotomic_initial, cycloUnit_val.
Direct frozen dependencies: none.
cycloUnit_val: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_initial.
Direct frozen dependencies: none.
oneSubXPowUnit: proof_shape: definition; escape_witness: none; consumers: cyclotomic_moebius_series, cycloUnit_prod, cyclotomic_initial, oneSubXPowUnit_val.
Direct frozen dependencies: none.
oneSubXPowUnit_val: proof_shape: bind-only; escape_witness: none; consumers: cycloUnit_prod, cyclotomic_initial.
Direct frozen dependencies: none.
normalizedCyclo_prod: proof_shape: bind-only; escape_witness: none; consumers: cycloUnit_prod.
Direct frozen dependencies: none.
cycloUnit_prod: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_moebius_series.
Direct frozen dependencies: none.
cyclotomic_moebius_series: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_initial.
Direct frozen dependencies: none.
cyclotomic_index: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_initial.
Direct frozen dependencies: none.
nilpotent_unit_zpow: proof_shape: bind-only; escape_witness: none; consumers: cyclotomic_initial.
Direct frozen dependencies: none.
cyclotomic_initial: proof_shape: content; escape_witness: cyclotomic_initial; consumers: cyclotomic_half_difference.
Direct frozen dependencies: none.
primitive_trace_bridge: proof_shape: content; escape_witness: trace_minpoly_degree; consumers: MPR2_reflection, MPR2_bridge.
Direct frozen dependencies: none.
MPR2_bridge: proof_shape: content; escape_witness: primitive_trace_bridge; consumers: MPR2_reflection_coeff, MPR2_reflection, result.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta.eq_1; statement_id: sha256:4dbb1a5f4ecfb71781c968b4f51e3f9fca799113d5fcb9d0016744e44ccba9e8
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
MPR2_reflection: proof_shape: content; escape_witness: primitive_trace_bridge; consumers: MPR2_reflection_coeff.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta.eq_1; statement_id: sha256:4dbb1a5f4ecfb71781c968b4f51e3f9fca799113d5fcb9d0016744e44ccba9e8
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
MPR2_reflection_coeff: proof_shape: content; escape_witness: primitive_trace_bridge; consumers: result.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta.eq_1; statement_id: sha256:4dbb1a5f4ecfb71781c968b4f51e3f9fca799113d5fcb9d0016744e44ccba9e8
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
coefficient_consequences: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: none.
cyclotomic_half_difference: proof_shape: content; escape_witness: cyclotomic_initial; consumers: result.
Direct frozen dependencies: none.
degree_from_lift: proof_shape: bind-only; escape_witness: none; consumers: result.
Direct frozen dependencies: none.
result: proof_shape: content; escape_witness: cyclotomic_half_difference; consumers: settling result.
Direct frozen dependencies:
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta.eq_1; statement_id: sha256:4dbb1a5f4ecfb71781c968b4f51e3f9fca799113d5fcb9d0016744e44ccba9e8
D5/S3/Arith/InterlaceFan/Cyclotomic.evalCos._proof_1; statement_id: sha256:81c71ee02d2f72b171fc58aaa25c773cb2970afdc3859889e24aec286d6db5ae
D5/S3/Arith/InterlaceFan/Cyclotomic.zeta; statement_id: sha256:e8aa7909f91dd6e576ae9c0ca5fc87df493a148eddedc7a3d512d1874731ac68
-/

import D5.S3.Arith.InterlaceFan.Cyclotomic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Homogenize

namespace D5.S3.Arith.InterlaceFan.SongA232624LeadingTerm

/-- OEIS A232624: the monic minimal polynomial over ℚ of 2*cos(2*Pi/n).
The existing `minpoly` owner is used directly; no root-product surrogate is assumed. -/
noncomputable def MPR2 (n : ℕ) : Polynomial ℚ :=
  minpoly ℚ ((2 : ℝ) * Real.cos (2 * Real.pi / (n : ℝ)))

/-- The coefficient array a(n,j) in the source FORMULA. -/
noncomputable def a (n j : ℕ) : ℚ := (MPR2 n).coeff j

/-- Song's July 11, 2019 conjecture and its stated coefficient consequences.
`UniqueFactorizationMonoid.radical`, `Nat.totient`, and `ArithmeticFunction.cardDistinctFactors`
are the existing owners of rad, phi, and omega. For odd n>1, the range
`Odd k ∧ k < m` is exactly k=1,3,...,m-2 (empty when m=1).
-/
def claim : Prop :=
  ∀ n : ℕ, Odd n → 1 < n →
    let d : ℕ := n.totient / 2
    let m : ℕ := n / UniqueFactorizationMonoid.radical n
    let ε : ℚ := (-1 : ℚ) ^ ArithmeticFunction.cardDistinctFactors n
    let F : Polynomial ℚ := (1 / 2 : ℚ) • (MPR2 (2 * n) - MPR2 n)
    F ≠ 0 ∧
      F.natDegree = d - m ∧
      F.leadingCoeff = ε ∧
      (∀ k : ℕ, Odd k → k < m → a n (d - k) = 0 ∧ a (2 * n) (d - k) = 0) ∧
      a n (d - m) = -ε ∧ a (2 * n) (d - m) = ε

open UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

private theorem totient_radical (n : ℕ) :
    n.totient = (n / radical n) * (radical n).totient := by
  have hr : (radical n).totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_radical,
      ← Nat.radical_eq_prod_primeFactors, Nat.div_self (Nat.radical_pos n), one_mul]
  rw [hr, Nat.totient_eq_div_primeFactors_mul n, Nat.radical_eq_prod_primeFactors]

private theorem arithmetic_setup (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    0 < n / radical n ∧ Odd (n / radical n) ∧
    n / radical n ≤ n.totient / 2 := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn1
  have hr2 : 1 < radical n := Nat.one_lt_radical_iff.mpr hn1
  have hrne : radical n ≠ 2 := hn.ne_two_of_dvd_nat radical_dvd_self
  have hr3 : 2 < radical n := Nat.lt_of_le_of_ne hr2 (id (Ne.symm hrne))
  have hphi : 2 ≤ (radical n).totient := by
    have he := Nat.totient_even hr3
    have hp := Nat.totient_pos.mpr (Nat.radical_pos n)
    obtain ⟨k,hk⟩ := he
    omega
  refine ⟨Nat.div_pos (Nat.radical_le_self_iff.mpr hn0) (Nat.radical_pos n),
    hn.of_dvd_nat (Nat.div_dvd_of_dvd radical_dvd_self), ?_⟩
  rw [totient_radical]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa [mul_comm] using Nat.mul_le_mul_left (n / radical n) hphi

private theorem moebius_radical (n : ℕ) :
    μ (radical n) = (-1 : ℤ) ^ ArithmeticFunction.cardDistinctFactors n := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree squarefree_radical,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
      (Nat.radical_pos n).ne').mpr squarefree_radical]
  congr 1
  rw [ArithmeticFunction.cardDistinctFactors_apply, ArithmeticFunction.cardDistinctFactors_apply]
  simp only [← List.card_toFinset, Nat.toFinset_factors]
  rw [Nat.primeFactors_radical]

open Polynomial Finset
open scoped BigOperators

private noncomputable def reciprocalLift (d : ℕ) (p : ℚ[X]) : ℚ[X] :=
  MvPolynomial.eval₂ C ![X ^ 2 + 1, X] (p.homogenize d)

private theorem reciprocal_lift_sum (d : ℕ) (p : ℚ[X]) :
    reciprocalLift d p =
      ∑ j ∈ range (d + 1), C (p.coeff j) * ((X ^ 2 + 1) ^ j * X ^ (d - j)) := by
  classical
  simp only [reciprocalLift, Polynomial.homogenize, MvPolynomial.eval₂_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro j hj
  simp [MvPolynomial.eval₂_monomial, Finsupp.update_eq_add_single]

private theorem reciprocal_lift_coeff_below (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree ≤ d) (k : ℕ) (hk : k < d - p.natDegree) :
    (reciprocalLift d p).coeff k = 0  := by
  classical
  simp only [reciprocal_lift_sum, finsetSum_coeff]
  apply sum_eq_zero
  intro j hj
  by_cases hjp : j ≤ p.natDegree
  · have hjk : k < d - j := by omega
    simp only [coeff_C_mul]
    rw [coeff_mul_X_pow']
    simp [Nat.not_le_of_gt hjk]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
    simp

private theorem reciprocal_lift_coeff_first (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree ≤ d) :
    (reciprocalLift d p).coeff (d - p.natDegree) = p.leadingCoeff  := by
  classical
  simp only [reciprocal_lift_sum, finsetSum_coeff]
  rw [sum_eq_single p.natDegree]
  · rw [coeff_C_mul, coeff_mul_X_pow']
    simp only [le_refl, ite_true, Nat.sub_self]
    rw [coeff_zero_eq_eval_zero]
    simp
  · intro j hj hje
    by_cases hjp : j ≤ p.natDegree
    · have hjlt : j < p.natDegree := lt_of_le_of_ne hjp hje
      have hjk : d - p.natDegree < d - j := tsub_lt_tsub_left_of_le hd hjlt
      simp only [coeff_C_mul]
      rw [coeff_mul_X_pow']
      simp [Nat.not_le_of_gt hjk]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
      simp
  · intro hmem
    exact (hmem (mem_range.mpr (by omega))).elim

private theorem reciprocal_lift_trailing (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree ≤ d) (hp : p ≠ 0) :
    (reciprocalLift d p).natTrailingDegree = d - p.natDegree ∧
    (reciprocalLift d p).trailingCoeff = p.leadingCoeff  := by
  have hc := reciprocal_lift_coeff_first d p hd
  have hcn : (reciprocalLift d p).coeff (d - p.natDegree) ≠ 0 := by
    rw [hc]
    exact leadingCoeff_ne_zero.mpr hp
  have hne : reciprocalLift d p ≠ 0 := by
    intro h
    simp [h] at hcn
  have ht : (reciprocalLift d p).natTrailingDegree = d - p.natDegree := by
    apply le_antisymm (natTrailingDegree_le_of_ne_zero hcn)
    exact le_natTrailingDegree hne (fun k hk => reciprocal_lift_coeff_below d p hd k hk)
  refine ⟨ht, ?_⟩
  rw [trailingCoeff, ht, hc]

private theorem reciprocal_lift_degree_le (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree ≤ d) : (reciprocalLift d p).natDegree ≤ d + p.natDegree := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [reciprocal_lift_sum, finsetSum_coeff]
  apply sum_eq_zero
  intro j hj
  by_cases hjp : j ≤ p.natDegree
  · have hjd : j ≤ d := le_trans hjp hd
    apply coeff_eq_zero_of_natDegree_lt
    calc
      (C (p.coeff j) * ((X ^ 2 + 1) ^ j * X ^ (d - j)) : ℚ[X]).natDegree
          ≤ ((X ^ 2 + 1) ^ j * X ^ (d - j) : ℚ[X]).natDegree := natDegree_C_mul_le _ _
      _ ≤ 2 * j + (d - j) := by
        apply natDegree_mul_le_of_le
        · simpa [mul_comm] using (natDegree_pow_le (p := (X ^ 2 + 1 : ℚ[X])) (n := j))
        · simp
      _ < k := by omega
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
    simp

private theorem reciprocal_lift_coeff_top (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree ≤ d) :
    (reciprocalLift d p).coeff (d + p.natDegree) = p.leadingCoeff := by
  classical
  have hbound (j : ℕ) :
      ((X ^ 2 + 1) ^ j * X ^ (d - j) : ℚ[X]).natDegree ≤ 2 * j + (d - j) := by
    apply natDegree_mul_le_of_le
    · simpa [mul_comm] using (natDegree_pow_le (p := (X ^ 2 + 1 : ℚ[X])) (n := j))
    · simp
  simp only [reciprocal_lift_sum, finsetSum_coeff]
  rw [sum_eq_single p.natDegree]
  · rw [coeff_C_mul, coeff_mul_X_pow', if_pos (by omega)]
    rw [show d + p.natDegree - (d - p.natDegree) = 2 * p.natDegree by omega]
    have hdeg : ((X ^ 2 + 1 : ℚ[X]) ^ p.natDegree).natDegree = 2 * p.natDegree := by
      simp [natDegree_pow, mul_comm]
    have hmon : ((X ^ 2 + 1 : ℚ[X]) ^ p.natDegree).Monic :=
      (monic_X_pow_add_C (1 : ℚ) (by decide : 2 ≠ 0)).pow _
    simp only [← hdeg, coeff_natDegree, hmon.leadingCoeff, mul_one]
  · intro j hj hje
    by_cases hjp : j ≤ p.natDegree
    · have hjlt : j < p.natDegree := lt_of_le_of_ne hjp hje
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt
        ((hbound j).trans_lt (by omega)), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
      simp
  · intro hnot
    exact (hnot (mem_range.mpr (by omega))).elim

private theorem reciprocal_lift_monic (d : ℕ) (p : ℚ[X])
    (hd : p.natDegree = d) (hp : p.Monic) :
    (reciprocalLift d p).Monic ∧ (reciprocalLift d p).natDegree = 2 * d := by
  have hle := reciprocal_lift_degree_le d p hd.le
  have hc := reciprocal_lift_coeff_top d p hd.le
  rw [hd] at hle hc
  rw [hp.leadingCoeff] at hc
  have hh := monic_of_natDegree_le_of_coeff_eq_one (d + d) hle hc
  refine ⟨hh, ?_⟩
  have hdeg : (reciprocalLift d p).natDegree = d + d :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc]; norm_num)
  omega

private theorem reciprocal_lift_eval (d : ℕ) (p : ℚ[X]) (hd : p.natDegree ≤ d)
    (z : ℂ) (hz : z ≠ 0) :
    (reciprocalLift d p).eval₂ (algebraMap ℚ ℂ) z =
      z ^ d * p.eval₂ (algebraMap ℚ ℂ) (z + z⁻¹) := by
  classical
  let f := algebraMap ℚ ℂ
  have hcompose : (reciprocalLift d p).eval₂ f z =
      MvPolynomial.eval₂ f ![z ^ 2 + 1, z] (p.homogenize d) := by
    unfold reciprocalLift
    change (Polynomial.eval₂RingHom f z)
      (MvPolynomial.eval₂ C ![X ^ 2 + 1, X] (p.homogenize d)) = _
    rw [MvPolynomial.eval₂_comp_left (Polynomial.eval₂RingHom f z)]
    congr 1
    · ext q
      simp [f]
    · funext i
      fin_cases i <;> simp [Function.comp_def]
  rw [hcompose, MvPolynomial.eval₂_eq_eval_map, ← Polynomial.homogenize_map]
  rw [Polynomial.eval_homogenize (Polynomial.natDegree_map_le.trans hd)
    ![z ^ 2 + 1, z] (by simpa using hz)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Polynomial.eval_map]
  have ht : (z ^ 2 + 1) / z = z + z⁻¹ := by field_simp
  rw [ht, mul_comm]

private theorem reciprocal_lift_sub (d : ℕ) (p q : ℚ[X]) :
    reciprocalLift d (p - q) = reciprocalLift d p - reciprocalLift d q := by
  classical
  simp only [reciprocal_lift_sum, coeff_sub, C_sub, sub_mul, sum_sub_distrib]

private theorem reciprocal_lift_smul (d : ℕ) (c : ℚ) (p : ℚ[X]) :
    reciprocalLift d (c • p) = c • reciprocalLift d p := by
  classical
  simp only [reciprocal_lift_sum, coeff_smul, smul_eq_mul, C_mul]
  simp only [smul_eq_C_mul, mul_sum, mul_assoc]

private theorem reciprocal_lift_injective (d : ℕ) (p q : ℚ[X])
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (heq : reciprocalLift d p = reciprocalLift d q) : p = q := by
  have hr : (p - q).natDegree ≤ d := (natDegree_sub_le_iff_left hq).mpr hp
  have hc := reciprocal_lift_coeff_first d (p - q) hr
  rw [reciprocal_lift_sub, heq, sub_self, coeff_zero] at hc
  exact sub_eq_zero.mp (leadingCoeff_eq_zero.mp hc.symm)

open Polynomial IntermediateField

private theorem trace_minpoly_degree (ζ : ℂ) (hζ : IsIntegral ℚ ζ) (hζ0 : ζ ≠ 0)
    (ht : (ζ + ζ⁻¹).im = 0) (hnr : ζ.im ≠ 0) :
    (minpoly ℚ ζ).natDegree = 2 * (minpoly ℚ (ζ + ζ⁻¹)).natDegree := by
  classical
  let t := ζ + ζ⁻¹
  let K := ℚ⟮t⟯
  have htint : IsIntegral ℚ t := hζ.add hζ.inv
  letI := adjoin.finiteDimensional htint
  have hreal : K ≤ (IsScalarTower.toAlgHom ℚ ℝ ℂ).fieldRange := by
    apply adjoin_le_iff.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    refine ⟨t.re, ?_⟩
    change (t.re : ℂ) = t
    apply Complex.ext <;> simp [t, ht]
  have hnot : ζ ∉ K := by
    intro h
    obtain ⟨x, hx⟩ := hreal h
    have hh := congrArg Complex.im hx
    exact hnr (by simpa using hh.symm)
  have hζK : IsIntegral K ζ := hζ.tower_top
  let q : K[X] := C 1 * X ^ 2 + C (-(AdjoinSimple.gen ℚ t)) * X + C 1
  have hqdegree : q.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hqmonic : q.Monic := by
    change q.leadingCoeff = 1
    exact leadingCoeff_quadratic one_ne_zero
  have hqroot : aeval ζ q = 0 := by
    simp only [q, map_add, map_mul, map_pow, aeval_C, aeval_X, map_one,
      map_neg, AdjoinSimple.algebraMap_gen, one_mul]
    dsimp [t]
    field_simp [hζ0]
    <;> ring
  have hdegree : (minpoly K ζ).natDegree = 2 := by
    apply le_antisymm
    · rw [← hqdegree]
      exact natDegree_le_natDegree (minpoly.min K ζ hqmonic hqroot)
    · apply (minpoly.two_le_natDegree_iff hζK).mpr
      rintro ⟨x, hx⟩
      apply hnot
      exact hx ▸ x.property
  have hKle : K ≤ ℚ⟮ζ⟯ := by
    apply adjoin_le_iff.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
  have heq : (K⟮ζ⟯).restrictScalars ℚ = ℚ⟮ζ⟯ := by
    rw [restrictScalars_adjoin_eq_sup, sup_eq_right.mpr hKle]
  have hfin : Module.finrank ℚ K⟮ζ⟯ = (minpoly ℚ ζ).natDegree := by
    change Module.finrank ℚ ((K⟮ζ⟯).restrictScalars ℚ) = _
    rw [heq, adjoin.finrank hζ]
  rw [← hfin, ← Module.finrank_mul_finrank ℚ K K⟮ζ⟯,
    adjoin.finrank htint, adjoin.finrank hζK, hdegree, mul_comm]

private theorem zeta_trace (n : ℕ) :
    D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹ = ((2 * Real.cos (2 * Real.pi / n) : ℝ) : ℂ) := by
  have hform : (2 * (Real.pi : ℂ) * Complex.I / n) =
      ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h := (Complex.two_cos (((2 * Real.pi / n : ℝ) : ℂ))).symm
  simpa only [D5.S3.Arith.InterlaceFan.Cyclotomic.zeta, hform, ← Complex.exp_neg, neg_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_cos] using h

private theorem zeta_nonreal (n : ℕ) (hn : 2 < n) : (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n).im ≠ 0 := by
  have hnR : (2 : ℝ) < n := Nat.ofNat_lt_cast.mpr hn
  have hnp : 0 < (n : ℝ) := by positivity
  have hangle0 : 0 < 2 * Real.pi / n := div_pos (by positivity) hnp
  have hangle : 2 * Real.pi / n < Real.pi := by
    apply (div_lt_iff₀ hnp).mpr
    nlinarith [Real.pi_pos]
  have hs : 0 < Real.sin (2 * Real.pi / n) := Real.sin_pos_of_pos_of_lt_pi hangle0 hangle
  have hform : (2 * (Real.pi : ℂ) * Complex.I / n) =
      ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [D5.S3.Arith.InterlaceFan.Cyclotomic.zeta, hform, Complex.exp_ofReal_mul_I_im]
  exact hs.ne'

open Polynomial

private theorem primitive_neg (n : ℕ) (hn : Odd n) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (-ζ) (2 * n)  := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hneg : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)
  have hcop : (orderOf (-1 : ℂ)).Coprime (orderOf ζ) := by
    rw [← hneg.eq_orderOf, ← hζ.eq_orderOf]
    exact hn.coprime_two_left
  have h := (Commute.all (-1 : ℂ) ζ).orderOf_mul_eq_mul_orderOf_of_coprime hcop
  rw [← hneg.eq_orderOf, ← hζ.eq_orderOf] at h
  simpa only [neg_one_mul] using h

private theorem cyclotomic_reflection (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    cyclotomic (2 * n) ℚ = (cyclotomic n ℚ).comp (-X)  := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn1
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have hζn := primitive_neg n hn ζ hζ
  rw [cyclotomic_eq_minpoly_rat hζn (by omega), minpoly.neg,
    ← cyclotomic_eq_minpoly_rat hζ hn0, natDegree_cyclotomic]
  have hn3 : 2 < n := by
    have := hn.ne_two_of_dvd_nat (dvd_refl n)
    omega
  rw [(Nat.totient_even hn3).neg_one_pow, one_mul]

open Polynomial Finset UniqueFactorizationMonoid
open scoped PowerSeries ArithmeticFunction.Moebius

private noncomputable def normalizedCyclo (n : ℕ) : ℚ⟦X⟧ :=
  if n = 1 then 1 - PowerSeries.X else (cyclotomic n ℚ : ℚ[X])

private theorem normalizedCyclo_constant (n : ℕ) :
    PowerSeries.constantCoeff (normalizedCyclo n) = 1 := by
  rcases n with _ | _ | n
  · simp [normalizedCyclo, cyclotomic_zero]
  · simp [normalizedCyclo]
  · simp [normalizedCyclo, Polynomial.constantCoeff_coe, cyclotomic_coeff_zero ℚ (n := n + 1 + 1) (by omega)]

private noncomputable def cycloUnit (n : ℕ) : (ℚ⟦X⟧)ˣ :=
  ((PowerSeries.isUnit_iff_constantCoeff (φ := normalizedCyclo n)).mpr
    (by rw [normalizedCyclo_constant]; exact isUnit_one)).unit

private theorem cycloUnit_val (n : ℕ) : (cycloUnit n : ℚ⟦X⟧) = normalizedCyclo n :=
  by exact IsUnit.unit_spec _

private noncomputable def oneSubXPowUnit (n : ℕ) : (ℚ⟦X⟧)ˣ :=
  if h : 0 < n then
    ((PowerSeries.isUnit_iff_constantCoeff (φ := (1 - PowerSeries.X ^ n : ℚ⟦X⟧))).mpr
      (by simp [h.ne'])).unit
  else 1

private theorem oneSubXPowUnit_val (n : ℕ) (hn : 0 < n) :
    (oneSubXPowUnit n : ℚ⟦X⟧) = 1 - PowerSeries.X ^ n := by
  simp only [oneSubXPowUnit, dif_pos hn, IsUnit.unit_spec]

private theorem normalizedCyclo_prod (n : ℕ) (hn : 0 < n) :
    ∏ i ∈ n.divisors, normalizedCyclo i = 1 - PowerSeries.X ^ n := by
  have hf (i : ℕ) : normalizedCyclo i =
      (if i = 1 then (-1 : ℚ⟦X⟧) else 1) * (cyclotomic i ℚ : ℚ[X]) := by
    by_cases hi : i = 1
    · subst i
      simp [normalizedCyclo, cyclotomic_one, sub_eq_add_neg, add_comm]
    · simp [normalizedCyclo, hi]
  simp_rw [hf]
  rw [prod_mul_distrib]
  have hp : (∏ i ∈ n.divisors, (if i = 1 then (-1 : ℚ⟦X⟧) else 1)) = -1 := by
    simp [Nat.one_mem_divisors.mpr hn.ne']
  rw [hp]
  have hc := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℚ)
  simp only [map_prod, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub, Polynomial.coe_pow,
    Polynomial.coe_X, Polynomial.coe_one] at hc
  rw [hc]
  ring

private theorem cycloUnit_prod (n : ℕ) (hn : 0 < n) :
    ∏ i ∈ n.divisors, cycloUnit i = oneSubXPowUnit n := by
  apply Units.val_injective
  change (Units.coeHom _ (∏ i ∈ n.divisors, cycloUnit i)) = _
  rw [map_prod]
  simp only [Units.coeHom_apply, oneSubXPowUnit_val n hn]
  exact normalizedCyclo_prod n hn

private theorem cyclotomic_moebius_series (n : ℕ) (hn : 1 < n) :
    (∏ x ∈ n.divisorsAntidiagonal, oneSubXPowUnit x.2 ^ μ x.1 : (ℚ⟦X⟧)ˣ) =
      cycloUnit n := by
  exact (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq.mp cycloUnit_prod) n (by omega)

open UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

private theorem cyclotomic_index (n a b : ℕ) (hn : 0 < n)
    (hab : a * b = n) (hμ : μ a ≠ 0) :
    n / radical n ≤ b ∧ (b = n / radical n → a = radical n) := by
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by intro h; simp [h] at hab; omega)
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by intro h; simp [h] at hab; omega)
  have hadvd : a ∣ n := ⟨b, hab.symm⟩
  have har : a ∣ radical n :=
    (dvd_radical_iff (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ).isRadical hn.ne').mpr hadvd
  have harle : a ≤ radical n := Nat.le_of_dvd (Nat.radical_pos n) har
  have hdiv : n / a = b := Nat.div_eq_of_eq_mul_right ha0 (id (Eq.symm hab))
  have hle : n / radical n ≤ b := by
    rw [← hdiv]
    exact Nat.div_le_div_left harle ha0
  refine ⟨hle, ?_⟩
  intro hb
  have hmul : radical n * b = n := by
    rw [hb]
    exact Nat.mul_div_cancel' radical_dvd_self
  exact mul_right_cancel₀ hb0.ne' (hab.trans hmul.symm)

private theorem nilpotent_unit_zpow {S : Type*} [CommRing S] (u : Sˣ) (x : S)
    (hx : x * x = 0) (hu : (u : S) = 1 - x) (e : ℤ) (he : e = 1 ∨ e = -1) :
    (↑(u ^ e) : S) = 1 - (e : S) * x := by
  rcases he with rfl | rfl
  · simp [hu]
  · simp only [zpow_neg_one]
    have hi : (↑(u⁻¹) : S) = 1 + x := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hu]
      calc (1 - x) * (1 + x) = 1 - x * x := by ring
           _ = 1 := by rw [hx]; ring
    rw [hi]
    push_cast
    ring

private theorem cyclotomic_initial (n : ℕ) (hn : 1 < n) :
    ∀ k ≤ n / radical n,
      (cyclotomic n ℚ).coeff k =
        (1 - C ((μ (radical n) : ℤ) : ℚ) * X ^ (n / radical n) : ℚ[X]).coeff k := by
  classical
  let m := n / radical n
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hm : 0 < m := Nat.div_pos (Nat.radical_le_self_iff.mpr hn0.ne') (Nat.radical_pos n)
  let I : Ideal (ℚ⟦X⟧) := Ideal.span {PowerSeries.X ^ (m + 1)}
  let π := Ideal.Quotient.mk I
  let x := π PowerSeries.X
  let U := Units.map π.toMonoidHom
  have hx : x ^ (m + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxlarge (b : ℕ) (hb : m < b) : x ^ b = 0 :=
    pow_eq_zero_of_le (by omega) hx
  have hxx : (x ^ m) * (x ^ m) = 0 := by
    rw [← pow_add]
    exact hxlarge (m + m) (by omega)
  have hUval (b : ℕ) (hb : 0 < b) :
      (U (oneSubXPowUnit b) : (ℚ⟦X⟧) ⧸ I) = 1 - x ^ b := by
    change π (oneSubXPowUnit b : ℚ⟦X⟧) = _
    rw [oneSubXPowUnit_val b hb, map_sub, map_one, map_pow]
  have hprod : U (cycloUnit n) = U (oneSubXPowUnit m) ^ μ (radical n) := by
    rw [← cyclotomic_moebius_series n hn, map_prod]
    simp only [map_zpow]
    apply Finset.prod_eq_single (radical n, m)
    · intro ab hab hne
      by_cases hμ : μ ab.1 = 0
      · simp [hμ]
      · have hab' := (Nat.mem_divisorsAntidiagonal.mp hab).1
        have hi := cyclotomic_index n ab.1 ab.2 hn0 hab' hμ
        have hmb : m < ab.2 := by
          have hneq : ab.2 ≠ m := by
            intro heq
            apply hne
            exact Prod.ext (hi.2 heq) heq
          omega
        have hunit : U (oneSubXPowUnit ab.2) = 1 := by
          apply Units.ext
          rw [hUval _ (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hab)),
            hxlarge _ hmb, sub_zero, Units.val_one]
        simp [hunit]
    · intro hnot
      apply False.elim
      apply hnot
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨Nat.mul_div_cancel' radical_dvd_self, hn0.ne'⟩
  have hmu : μ (radical n) = 1 ∨ μ (radical n) = -1 :=
    ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr squarefree_radical)
  have hred : π (cyclotomic n ℚ : ℚ[X]) =
      π (1 - PowerSeries.C ((μ (radical n) : ℤ) : ℚ) * PowerSeries.X ^ m) := by
    have hh := congrArg (fun u : ((ℚ⟦X⟧) ⧸ I)ˣ => (u : (ℚ⟦X⟧) ⧸ I)) hprod
    rw [nilpotent_unit_zpow _ _ hxx (hUval m hm) _ hmu] at hh
    simpa [U, cycloUnit_val, normalizedCyclo, ne_of_gt hn, π, x] using hh
  have hmem := Ideal.Quotient.eq.mp hred
  have hdvd : PowerSeries.X ^ (m + 1) ∣
      (cyclotomic n ℚ : ℚ⟦X⟧) -
        (1 - PowerSeries.C ((μ (radical n) : ℤ) : ℚ) * PowerSeries.X ^ m) :=
    Ideal.mem_span_singleton.mp hmem
  intro k hk
  have hkzero := PowerSeries.X_pow_dvd_iff.mp hdvd k (by omega)
  have hmodel : (1 - PowerSeries.C ((μ (radical n) : ℤ) : ℚ) * PowerSeries.X ^ m) =
      ((1 - C ((μ (radical n) : ℤ) : ℚ) * X ^ m : ℚ[X]) : ℚ⟦X⟧) := by
    simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [hmodel, map_sub, Polynomial.coeff_coe, Polynomial.coeff_coe, sub_eq_zero] at hkzero
  exact hkzero

open Polynomial IntermediateField

private theorem primitive_trace_bridge (N : ℕ) (hN : 0 < N) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ N) (ht : (ζ + ζ⁻¹).im = 0) (hnr : ζ.im ≠ 0) :
    reciprocalLift (N.totient / 2) (minpoly ℚ (ζ + ζ⁻¹)) = cyclotomic N ℚ ∧
      (minpoly ℚ (ζ + ζ⁻¹)).natDegree = N.totient / 2 := by
  have hzint : IsIntegral ℚ ζ := (hζ.isIntegral hN).tower_top
  have hdeq := trace_minpoly_degree ζ hzint (hζ.ne_zero hN.ne') ht hnr
  rw [← cyclotomic_eq_minpoly_rat hζ hN, natDegree_cyclotomic] at hdeq
  have hpd : (minpoly ℚ (ζ + ζ⁻¹)).natDegree = N.totient / 2 := by omega
  have hpint : IsIntegral ℚ (ζ + ζ⁻¹) := hzint.add hzint.inv
  obtain ⟨hlmon, hldeg⟩ := reciprocal_lift_monic _ _ hpd (minpoly.monic hpint)
  have hroot : aeval ζ (reciprocalLift (N.totient / 2) (minpoly ℚ (ζ + ζ⁻¹))) = 0 := by
    change (reciprocalLift _ _).eval₂ (algebraMap ℚ ℂ) ζ = 0
    rw [reciprocal_lift_eval _ _ hpd.le ζ (hζ.ne_zero hN.ne')]
    change ζ ^ (N.totient / 2) * aeval (ζ + ζ⁻¹) (minpoly ℚ (ζ + ζ⁻¹)) = 0
    rw [minpoly.aeval, mul_zero]
  have hdvd : cyclotomic N ℚ ∣ reciprocalLift (N.totient / 2) (minpoly ℚ (ζ + ζ⁻¹)) := by
    rw [cyclotomic_eq_minpoly_rat hζ hN]
    exact minpoly.dvd ℚ ζ hroot
  refine ⟨eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic N ℚ) hlmon hdvd ?_, hpd⟩
  rw [hldeg, natDegree_cyclotomic]
  omega

private theorem MPR2_bridge (N : ℕ) (hN : 2 < N) :
    reciprocalLift (N.totient / 2) (MPR2 N) = cyclotomic N ℚ ∧
      (MPR2 N).natDegree = N.totient / 2 ∧
      (MPR2 N).Monic := by
  have hpr : IsPrimitiveRoot (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N) N := Complex.isPrimitiveRoot_exp N (by omega)
  have ht : (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N)⁻¹).im = 0 := by
    rw [zeta_trace]
    exact Complex.ofReal_im _
  have hbridge := primitive_trace_bridge N (by omega) (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N) hpr ht (zeta_nonreal N hN)
  have heq : minpoly ℚ (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N)⁻¹) = MPR2 N := by
    rw [zeta_trace, MPR2]
    exact minpoly.algebraMap_eq Complex.ofReal_injective _
  rw [heq] at hbridge
  refine ⟨hbridge.1, hbridge.2, ?_⟩
  rw [← heq]
  exact minpoly.monic (((hpr.isIntegral (by omega)).tower_top :
    IsIntegral ℚ (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N)).add ((hpr.isIntegral (by omega)).tower_top :
      IsIntegral ℚ (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta N)).inv)

open Polynomial IntermediateField

private theorem MPR2_reflection (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    MPR2 (2 * n) = (MPR2 n).scaleRoots (-1) := by
  have hn3 : 2 < n := by
    have := hn.ne_two_of_dvd_nat (dvd_refl n)
    omega
  have hpr : IsPrimitiveRoot (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n) n := Complex.isPrimitiveRoot_exp n (by omega)
  have hpr2 := primitive_neg n hn (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n) hpr
  have ht : (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹).im = 0 := by
    rw [zeta_trace]
    exact Complex.ofReal_im _
  have hnegtrace : -D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹ = -(D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹) := by
    rw [inv_neg]; ring
  have htneg : (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹).im = 0 := by
    rw [hnegtrace, Complex.neg_im, ht, neg_zero]
  have hnrneg : (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n).im ≠ 0 := by simpa using zeta_nonreal n hn3
  have hbridge := primitive_trace_bridge (2 * n) (by omega) (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n) hpr2 htneg hnrneg
  have hactual := MPR2_bridge (2 * n) (by omega)
  have htraceid : minpoly ℚ (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (-D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹) =
      (MPR2 n).scaleRoots (-1) := by
    rw [hnegtrace]
    have hzint : IsIntegral ℚ (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n) := (hpr.isIntegral (by omega)).tower_top
    have hs := IsIntegrallyClosed.minpoly_smul (R := ℚ) (S := ℂ)
      (r := (-1 : ℚ)) (by norm_num) (hzint.add hzint.inv)
    have hid : minpoly ℚ (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n + (D5.S3.Arith.InterlaceFan.Cyclotomic.zeta n)⁻¹) = MPR2 n := by
      rw [zeta_trace, MPR2]
      exact minpoly.algebraMap_eq Complex.ofReal_injective _
    simpa only [neg_one_smul, hid] using hs
  rw [htraceid] at hbridge
  apply reciprocal_lift_injective ((2 * n).totient / 2)
  · exact hactual.2.1.le
  · exact hbridge.2.le
  · exact hactual.1.trans hbridge.1.symm

private theorem MPR2_reflection_coeff (n : ℕ) (hn : Odd n) (hn1 : 1 < n) (j : ℕ) :
    (MPR2 (2 * n)).coeff j =
      (-1 : ℚ) ^ (n.totient / 2 - j) * (MPR2 n).coeff j := by
  rw [MPR2_reflection n hn hn1, coeff_scaleRoots]
  have hn3 : 2 < n := by have := hn.ne_two_of_dvd_nat (dvd_refl n); omega
  rw [(MPR2_bridge n hn3).2.1, mul_comm]

open Polynomial

private theorem coefficient_consequences (p q : ℚ[X]) (d m : ℕ) (ε : ℚ)
    (hmd : m ≤ d) (hm : Odd m)
    (hreflect : ∀ j ≤ d, q.coeff j = (-1 : ℚ) ^ (d - j) * p.coeff j)
    (hdegree : ((1 / 2 : ℚ) • (q - p)).natDegree = d - m)
    (hlead : ((1 / 2 : ℚ) • (q - p)).leadingCoeff = ε) :
    (∀ k : ℕ, Odd k → k < m → p.coeff (d - k) = 0 ∧ q.coeff (d - k) = 0) ∧
    p.coeff (d - m) = -ε ∧ q.coeff (d - m) = ε  := by
  have hcoeff (k : ℕ) (hk : k ≤ d) (hko : Odd k) :
      ((1 / 2 : ℚ) • (q - p)).coeff (d - k) = -p.coeff (d - k) := by
    rw [coeff_smul, coeff_sub, hreflect (d - k) (Nat.sub_le _ _),
      Nat.sub_sub_self hk, hko.neg_one_pow]
    simp only [smul_eq_mul]
    ring
  have hzero (k : ℕ) (hko : Odd k) (hkm : k < m) :
      p.coeff (d - k) = 0 ∧ q.coeff (d - k) = 0 := by
    have hkd : k ≤ d := le_trans hkm.le hmd
    have hgap : ((1 / 2 : ℚ) • (q - p)).natDegree < d - k := by omega
    have hz := coeff_eq_zero_of_natDegree_lt hgap
    rw [hcoeff k hkd hko, neg_eq_zero] at hz
    refine ⟨hz, ?_⟩
    rw [hreflect (d - k) (Nat.sub_le _ _), hz, mul_zero]
  have hmcoeff := hcoeff m hmd hm
  rw [← hdegree, coeff_natDegree, hlead] at hmcoeff
  rw [hdegree] at hmcoeff
  have hp : p.coeff (d - m) = -ε := by linarith
  refine ⟨hzero, hp, ?_⟩
  rw [hreflect (d - m) (Nat.sub_le _ _), Nat.sub_sub_self hmd, hm.neg_one_pow, hp]
  ring

open Polynomial UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

private theorem cyclotomic_half_difference (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (let m := n / radical n
    let ε := (-1 : ℚ) ^ ArithmeticFunction.cardDistinctFactors n
    let H := (1 / 2 : ℚ) • (cyclotomic (2 * n) ℚ - cyclotomic n ℚ)
    (∀ k < m, H.coeff k = 0) ∧ H.coeff m = ε) := by
  dsimp only
  let m := n / radical n
  have hm : 0 < m := (arithmetic_setup n hn hn1).1
  have hmo : Odd m := (arithmetic_setup n hn hn1).2.1
  have hreflect (k : ℕ) : (cyclotomic (2 * n) ℚ).coeff k =
      (cyclotomic n ℚ).coeff k * (-1 : ℚ) ^ k := by
    rw [cyclotomic_reflection n hn hn1]
    have hnegX : (-X : ℚ[X]) = C (-1) * X := by simp
    rw [hnegX, comp_C_mul_X_coeff]
  have hμ : ((μ (radical n) : ℤ) : ℚ) =
      (-1 : ℚ) ^ ArithmeticFunction.cardDistinctFactors n := by
    rw [moebius_radical n]
    push_cast
    rfl
  have hcfirst : (cyclotomic n ℚ).coeff m =
      -((-1 : ℚ) ^ ArithmeticFunction.cardDistinctFactors n) := by
    have h := cyclotomic_initial n hn1 m le_rfl
    change (cyclotomic n ℚ).coeff m =
      (1 - C ((μ (radical n) : ℤ) : ℚ) * X ^ m : ℚ[X]).coeff m at h
    rw [coeff_sub, coeff_one, if_neg hm.ne', coeff_C_mul, coeff_X_pow_self,
      mul_one, zero_sub, hμ] at h
    exact h
  constructor
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      rw [coeff_smul, coeff_sub, hreflect]
      simp
    · have h := cyclotomic_initial n hn1 k hk.le
      have hz : (cyclotomic n ℚ).coeff k = 0 := by
        simpa [coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow, hk0, Nat.ne_of_lt hk] using h
      rw [coeff_smul, coeff_sub, hreflect, hz]
      simp
  · rw [coeff_smul, coeff_sub, hreflect, hcfirst, hmo.neg_one_pow]
    simp only [smul_eq_mul]
    ring

open Polynomial UniqueFactorizationMonoid

private theorem degree_from_lift (p : ℚ[X]) (d m : ℕ) (ε : ℚ)
    (hpd : p.natDegree ≤ d) (hmd : m ≤ d) (hε : ε ≠ 0)
    (hbelow : ∀ k < m, (reciprocalLift d p).coeff k = 0)
    (hfirst : (reciprocalLift d p).coeff m = ε) :
    p ≠ 0 ∧ p.natDegree = d - m ∧ p.leadingCoeff = ε := by
  have hne : reciprocalLift d p ≠ 0 := by intro h; simp [h] at hfirst; exact hε hfirst.symm
  have hpne : p ≠ 0 := by
    intro hp
    apply hne
    simp [hp, reciprocalLift]
  have htr : (reciprocalLift d p).natTrailingDegree = m := by
    apply le_antisymm
    · exact natTrailingDegree_le_of_ne_zero (by rw [hfirst]; exact hε)
    · exact le_natTrailingDegree hne hbelow
  have heq : d - p.natDegree = m :=
    (reciprocal_lift_trailing d p hpd hpne).1.symm.trans htr
  refine ⟨hpne, by omega, ?_⟩
  have hc := reciprocal_lift_coeff_first d p hpd
  rw [heq, hfirst] at hc
  exact hc.symm

open Polynomial

theorem result : claim := by
  intro n hn hn1
  dsimp only
  have hn3 : 2 < n := by have := hn.ne_two_of_dvd_nat (dvd_refl n); omega
  let d := n.totient / 2
  let m := n / UniqueFactorizationMonoid.radical n
  let ε := (-1 : ℚ) ^ ArithmeticFunction.cardDistinctFactors n
  let F := (1 / 2 : ℚ) • (MPR2 (2 * n) - MPR2 n)
  have hnb := MPR2_bridge n hn3
  have h2nb := MPR2_bridge (2 * n) (by omega)
  rw [Nat.totient_two_mul_of_odd hn] at h2nb
  have hfd : F.natDegree ≤ d := by
    apply (natDegree_smul_le _ _).trans
    simpa [d, hnb.2.1, h2nb.2.1] using
      (natDegree_sub_le (MPR2 (2 * n)) (MPR2 n))
  have hmd : m ≤ d := (arithmetic_setup n hn hn1).2.2
  have hmo : Odd m := (arithmetic_setup n hn hn1).2.1
  have hε : ε ≠ 0 := pow_ne_zero _ (by norm_num)
  have hlift : reciprocalLift d F =
      (1 / 2 : ℚ) • (cyclotomic (2 * n) ℚ - cyclotomic n ℚ) := by
    dsimp only [F]
    rw [reciprocal_lift_smul,
      reciprocal_lift_sub, hnb.1, h2nb.1]
  have hc := cyclotomic_half_difference n hn hn1
  dsimp only at hc
  have hcon := degree_from_lift F d m ε hfd hmd hε
    (by rw [hlift]; exact hc.1) (by rw [hlift]; exact hc.2)
  have hcoeff := coefficient_consequences (MPR2 n) (MPR2 (2 * n)) d m ε
    hmd hmo (fun j _ => MPR2_reflection_coeff n hn hn1 j) hcon.2.1 hcon.2.2
  exact ⟨hcon.1, hcon.2.1, hcon.2.2, hcoeff⟩

end D5.S3.Arith.InterlaceFan.SongA232624LeadingTerm
