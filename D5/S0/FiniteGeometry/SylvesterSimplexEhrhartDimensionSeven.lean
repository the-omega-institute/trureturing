/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartDimensionSeven
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartDimensionSeven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact linear coefficient of the actual seven-dimensional source Ehrhart polynomial. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.NumberTheory.Bernoulli

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSeven

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private baseWeight sylvester_sub_one_eq_prod two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private partitionWeight finiteGeometricPolynomial periodNumerator
  binomialShiftPolynomial baseSamplePolynomial interiorSamplePolynomial
  sourceEhrhartPolynomial sourceEhrhartPolynomial_eval from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

private def prefixPeriod (j : ℕ) : ℕ := sylvester (j + 1) - 1

private def prefixBox (j : ℕ) : Finset (Fin j → ℕ) :=
  Fintype.piFinset fun i : Fin j => Finset.range (sylvester (i.1 + 1))

private def prefixMass (j : ℕ) (x : Fin j → ℕ) : ℕ :=
  ∑ i, x i * (prefixPeriod j / sylvester (i.1 + 1))

private def actualMoment (j q p : ℕ) : ℚ :=
  ∑ x ∈ prefixBox j with prefixMass j x / prefixPeriod j = q,
    ((prefixMass j x % prefixPeriod j : ℕ) : ℚ) ^ p

private irreducible_def prefixPolynomial (lemma := prefixPolynomial_def) (j : ℕ) : Polynomial ℚ :=
  ∑ x ∈ prefixBox j, Polynomial.X ^ prefixMass j x

private lemma prefixPeriod_pos (j : ℕ) : 0 < prefixPeriod j := by
  rw [prefixPeriod]
  exact Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (j + 1) (by omega)))

private lemma prefixPeriod_succ (j : ℕ) :
    prefixPeriod (j + 1) = prefixPeriod j * (prefixPeriod j + 1) := by
  rw [prefixPeriod, show j + 1 + 1 = j + 2 by omega, sylvester]
  change sylvester (j + 1) * (sylvester (j + 1) - 1) =
    (sylvester (j + 1) - 1) * ((sylvester (j + 1) - 1) + 1)
  rw [Nat.sub_add_cancel (by
    have := two_le_sylvester (j + 1) (by omega)
    omega : 1 ≤ sylvester (j + 1))]
  exact Nat.mul_comm _ _

private lemma sylvester_dvd_prefixPeriod (j : ℕ) (i : Fin j) :
    sylvester (i.1 + 1) ∣ prefixPeriod j := by
  rw [prefixPeriod, sylvester_sub_one_eq_prod (j + 1) (by omega)]
  exact Finset.dvd_prod_of_mem (fun n => sylvester n)
    (Finset.mem_range.mpr (by omega))

private lemma prefixPeriod_div_weight (j : ℕ) (i : Fin j) :
    prefixPeriod j / (prefixPeriod j / sylvester (i.1 + 1)) = sylvester (i.1 + 1) := by
  let s := sylvester (i.1 + 1)
  obtain ⟨c, hc⟩ := sylvester_dvd_prefixPeriod j i
  have hs : 0 < s := Nat.zero_lt_of_lt (two_le_sylvester (i.1 + 1) (by omega))
  have hcpos : 0 < c := by
    have hp := prefixPeriod_pos j
    rw [hc] at hp
    exact Nat.pos_of_mul_pos_left hp
  change prefixPeriod j / (prefixPeriod j / s) = s
  rw [hc]
  change s * c / (s * c / s) = s
  have hi : s * c / s = c := by
    simpa using Nat.mul_div_right c hs
  rw [hi]
  simpa using Nat.mul_div_left s hcpos

private lemma prefixPolynomial_eq_product (j : ℕ) :
    prefixPolynomial j =
      ∏ i : Fin j,
        finiteGeometricPolynomial
          (prefixPeriod j / sylvester (i.1 + 1)) (prefixPeriod j) := by
  classical
  rw [prefixPolynomial_def]
  simp_rw [finiteGeometricPolynomial, prefixPeriod_div_weight]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr
  · rfl
  · intro x hx
    rw [Finset.prod_pow_eq_pow_sum]
    rfl

private irreducible_def unitPolynomial (lemma := unitPolynomial_def) (M : ℕ) : Polynomial ℚ :=
  ∑ u ∈ Finset.range M, Polynomial.X ^ u

private lemma finiteGeometricPolynomial_one (M : ℕ) :
    finiteGeometricPolynomial 1 M = unitPolynomial M := by
  simp [finiteGeometricPolynomial, unitPolynomial_def]

private lemma mul_square_reorder (P U : Polynomial ℚ) :
    U * (P * U) = P * U ^ 2 := by
  rw [pow_two, mul_left_comm]

private lemma periodNumerator_succ_factorization (j : ℕ) :
    periodNumerator (j + 1) =
      prefixPolynomial j * unitPolynomial (prefixPeriod j) ^ 2 := by
  classical
  have hnone : partitionWeight (j + 1) none = 1 := rfl
  have hlast : partitionWeight (j + 1) (some (Fin.last j)) = 1 := by
    rw [partitionWeight, baseWeight, axisScale, if_pos (by simp)]
    have hM : 0 < sylvester (j + 1) - 1 := by
      change 0 < prefixPeriod j
      exact prefixPeriod_pos j
    simpa using Nat.div_self hM
  have hcast (i : Fin j) :
      partitionWeight (j + 1) (some i.castSucc) =
        prefixPeriod j / sylvester (i.1 + 1) := by
    rw [partitionWeight, baseWeight, axisScale,
      if_neg (by simpa using Nat.ne_of_lt i.isLt)]
    rfl
  rw [periodNumerator, Fintype.prod_option, Fin.prod_univ_castSucc]
  rw [hnone, hlast]
  simp_rw [hcast]
  change finiteGeometricPolynomial 1 (prefixPeriod j) *
      ((∏ x : Fin j,
        finiteGeometricPolynomial
          (prefixPeriod j / sylvester (x.1 + 1)) (prefixPeriod j)) *
        finiteGeometricPolynomial 1 (prefixPeriod j)) = _
  rw [← prefixPolynomial_eq_product j]
  rw [finiteGeometricPolynomial_one]
  exact mul_square_reorder _ _

private lemma periodNumerator_seven_factorization :
    periodNumerator 7 =
      prefixPolynomial 6 * unitPolynomial (prefixPeriod 6) ^ 2 := by
  simpa using periodNumerator_succ_factorization 6

private lemma prefixMass_snoc (j : ℕ) (x : Fin j → ℕ) (last : ℕ) :
    prefixMass (j + 1) (Fin.snoc x last) =
      (prefixPeriod j + 1) * prefixMass j x + prefixPeriod j * last := by
  rw [prefixMass, Fin.sum_univ_castSucc, prefixMass]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [prefixPeriod_succ]
  have hdiv (i : Fin j) :
      prefixPeriod j * (prefixPeriod j + 1) / sylvester (i.1 + 1) =
        (prefixPeriod j + 1) * (prefixPeriod j / sylvester (i.1 + 1)) := by
    rw [Nat.mul_comm (prefixPeriod j),
      Nat.mul_div_assoc _ (sylvester_dvd_prefixPeriod j i)]
  simp_rw [hdiv]
  rw [Finset.mul_sum]
  have hlast :
      prefixPeriod j * (prefixPeriod j + 1) / sylvester (j + 1) = prefixPeriod j := by
    rw [show prefixPeriod j + 1 = sylvester (j + 1) by
      rw [prefixPeriod, Nat.sub_add_cancel (by
        have := two_le_sylvester (j + 1) (by omega)
        omega : 1 ≤ sylvester (j + 1))]]
    calc
      prefixPeriod j * sylvester (j + 1) / sylvester (j + 1) =
          sylvester (j + 1) * prefixPeriod j / sylvester (j + 1) := by
            rw [Nat.mul_comm]
      _ = prefixPeriod j := Nat.mul_div_right _ (Nat.zero_lt_of_lt
        (two_le_sylvester (j + 1) (by omega)))
  rw [hlast]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private lemma prefixPeriod_add_one (j : ℕ) :
    prefixPeriod j + 1 = sylvester (j + 1) := by
  rw [prefixPeriod, Nat.sub_add_cancel (by
    have := two_le_sylvester (j + 1) (by omega)
    omega : 1 ≤ sylvester (j + 1))]

private lemma sum_prefixBox_succ (j : ℕ) (f : (Fin (j + 1) → ℕ) → ℚ) :
    ∑ z ∈ prefixBox (j + 1), f z =
      ∑ last ∈ Finset.range (prefixPeriod j + 1),
        ∑ x ∈ prefixBox j, f (Fin.snoc x last) := by
  classical
  let S : (i : Fin (j + 1)) → Finset ℕ :=
    fun i => Finset.range (sylvester (i.1 + 1))
  have hbox : Fintype.piFinset S =
      (S (Fin.last j) ×ˢ Fintype.piFinset (Fin.init S)).map
        (Fin.snocEquiv fun _ : Fin (j + 1) => ℕ).toEmbedding := by
    simpa only [Finset.filter_true] using
      (Finset.filter_piFinset_eq_map_snocEquiv S (fun _ => True))
  rw [prefixBox]
  change ∑ z ∈ Fintype.piFinset S, f z = _
  rw [hbox, Finset.sum_map, Finset.sum_product]
  have hlast : S (Fin.last j) = Finset.range (prefixPeriod j + 1) := by
    simp [S, prefixPeriod_add_one]
  have hinit : Fintype.piFinset (Fin.init S) = prefixBox j := by
    congr 1
  rw [hlast, hinit]
  change (∑ last ∈ Finset.range (prefixPeriod j + 1),
      ∑ x ∈ prefixBox j, f (Fin.snoc x last)) = _
  rfl

private lemma prefixMass_snoc_low (j : ℕ) (x : Fin j → ℕ) (last : ℕ)
    (hlast : last ≤ prefixPeriod j - prefixMass j x % prefixPeriod j) :
    prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) =
        prefixMass j x / prefixPeriod j ∧
      prefixMass (j + 1) (Fin.snoc x last) % prefixPeriod (j + 1) =
        (prefixPeriod j + 1) * (prefixMass j x % prefixPeriod j) +
          prefixPeriod j * last := by
  let L := prefixPeriod j
  let A := prefixMass j x
  let r := A % L
  let q := A / L
  have hL : 0 < L := prefixPeriod_pos j
  have hr : r < L := Nat.mod_lt A hL
  have hA : L * q + r = A := Nat.div_add_mod A L
  have hperiod : prefixPeriod (j + 1) = L * (L + 1) := prefixPeriod_succ j
  have hmass : prefixMass (j + 1) (Fin.snoc x last) =
      (L * (L + 1)) * q + ((L + 1) * r + L * last) := by
    rw [prefixMass_snoc]
    change (L + 1) * A + L * last = _
    rw [← hA]
    ring
  have hrem : (L + 1) * r + L * last < L * (L + 1) := by
    have hsum : r + last ≤ L := by
      dsimp [r, L, A] at hr hlast ⊢
      omega
    nlinarith
  constructor <;> rw [hperiod, hmass]
  · rw [Nat.mul_add_div (Nat.mul_pos hL (by omega))]
    rw [Nat.div_eq_of_lt hrem, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]

private lemma prefixMass_snoc_high (j : ℕ) (x : Fin j → ℕ) (y : ℕ)
    (hy : y < prefixMass j x % prefixPeriod j) :
    let last := prefixPeriod j - prefixMass j x % prefixPeriod j + 1 + y
    prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) =
        prefixMass j x / prefixPeriod j + 1 ∧
      prefixMass (j + 1) (Fin.snoc x last) % prefixPeriod (j + 1) =
        prefixMass j x % prefixPeriod j + prefixPeriod j * y := by
  dsimp only
  let L := prefixPeriod j
  let A := prefixMass j x
  let r := A % L
  let q := A / L
  have hL : 0 < L := prefixPeriod_pos j
  have hr : r < L := Nat.mod_lt A hL
  have hA : L * q + r = A := Nat.div_add_mod A L
  have hperiod : prefixPeriod (j + 1) = L * (L + 1) := prefixPeriod_succ j
  have hmass : prefixMass (j + 1)
      (Fin.snoc x (L - r + 1 + y)) =
      (L * (L + 1)) * (q + 1) + (r + L * y) := by
    rw [prefixMass_snoc]
    dsimp [L, A, r, q] at hA hr ⊢
    nlinarith [Nat.sub_add_cancel (Nat.le_of_lt hr)]
  have hrem : r + L * y < L * (L + 1) := by
    dsimp [L, A, r] at hr hy ⊢
    nlinarith
  constructor <;> rw [hperiod, hmass]
  · rw [Nat.mul_add_div (Nat.mul_pos hL (by omega))]
    rw [Nat.div_eq_of_lt hrem, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]

private lemma prefixBox_zero : prefixBox 0 = Finset.univ := by
  ext x
  simp [prefixBox]

private lemma prefixMass_zero (x : Fin 0 → ℕ) : prefixMass 0 x = 0 := by
  simp [prefixMass]

private lemma actualMoment_zero (q p : ℕ) :
    actualMoment 0 q p = if q = 0 then if p = 0 then 1 else 0 else 0 := by
  rcases q with _ | q <;> rcases p with _ | p <;>
    simp [actualMoment, prefixBox_zero, prefixMass_zero, prefixPeriod, sylvester]

private lemma prefixMass_eq_zero_iff (j : ℕ) (x : Fin j → ℕ) (hx : x ∈ prefixBox j) :
    prefixMass j x = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro h i
    have hterm : x i * (prefixPeriod j / sylvester (i.1 + 1)) = 0 := by
      have hle : x i * (prefixPeriod j / sylvester (i.1 + 1)) ≤ prefixMass j x := by
        rw [prefixMass]
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun i : Fin j => x i * (prefixPeriod j / sylvester (i.1 + 1)))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hweight : 0 < prefixPeriod j / sylvester (i.1 + 1) := by
      apply Nat.div_pos
      · exact Nat.le_of_dvd (prefixPeriod_pos j) (sylvester_dvd_prefixPeriod j i)
      · exact Nat.zero_lt_of_lt (two_le_sylvester (i.1 + 1) (by omega))
    exact (Nat.mul_eq_zero.mp hterm).resolve_right hweight.ne'
  · intro h
    simp [prefixMass, h]

private def powerSumPolynomial (p : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (p + 1),
    Polynomial.C
        (bernoulli i * ((p + 1).choose i : ℚ) / (p + 1 : ℚ)) *
      Polynomial.X ^ (p + 1 - i)

private lemma powerSumPolynomial_eval (n p : ℕ) :
    (powerSumPolynomial p).eval (n : ℚ) = ∑ x ∈ Finset.range n, (x : ℚ) ^ p := by
  rw [powerSumPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (sum_range_pow n p).symm

private def lowKernel (L p : ℕ) : Polynomial ℚ :=
  ∑ a ∈ Finset.range (p + 1),
    Polynomial.C
        ((p.choose a : ℚ) * (L + 1 : ℚ) ^ (p - a) * (L : ℚ) ^ a) *
      Polynomial.X ^ (p - a) *
        (powerSumPolynomial a).comp (Polynomial.C (L + 1 : ℚ) - Polynomial.X)

private def highKernel (L p : ℕ) : Polynomial ℚ :=
  ∑ a ∈ Finset.range (p + 1),
    Polynomial.C ((p.choose a : ℚ) * (L : ℚ) ^ a) *
      Polynomial.X ^ (p - a) * powerSumPolynomial a

private lemma lowKernel_eval (L r p : ℕ) (hr : r ≤ L) :
    (lowKernel L p).eval (r : ℚ) =
      ∑ x ∈ Finset.range (L - r + 1), (((L + 1) * r + L * x : ℕ) : ℚ) ^ p := by
  rw [lowKernel, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_sub]
  have harg : (L + 1 : ℚ) - (r : ℚ) = (L - r + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hr]
    push_cast
    ring
  rw [harg]
  simp_rw [powerSumPolynomial_eval (L - r + 1)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    ∑ a ∈ Finset.range (p + 1),
        ↑(p.choose a) * (↑L + 1) ^ (p - a) * ↑L ^ a * ↑r ^ (p - a) * ↑x ^ a =
        ∑ a ∈ Finset.range (p + 1),
          ↑(p.choose a) * (((L : ℚ) + 1) * (r : ℚ)) ^ (p - a) *
            ((L : ℚ) * (x : ℚ)) ^ a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_pow, mul_pow]
      ring
    _ = (((L : ℚ) + 1) * (r : ℚ) + (L : ℚ) * (x : ℚ)) ^ p := by
      calc
        _ = ((L : ℚ) * (x : ℚ) + ((L : ℚ) + 1) * (r : ℚ)) ^ p := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (add_pow ((L : ℚ) * (x : ℚ)) (((L : ℚ) + 1) * (r : ℚ)) p).symm
        _ = _ := by rw [add_comm]
    _ = (((L + 1) * r + L * x : ℕ) : ℚ) ^ p := by
      congr 1
      push_cast
      ring

private lemma highKernel_eval (L r p : ℕ) :
    (highKernel L p).eval (r : ℚ) =
      ∑ y ∈ Finset.range r, ((r + L * y : ℕ) : ℚ) ^ p := by
  rw [highKernel, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  simp_rw [powerSumPolynomial_eval]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    ∑ a ∈ Finset.range (p + 1),
        ↑(p.choose a) * ↑L ^ a * ↑r ^ (p - a) * ↑y ^ a =
        ∑ a ∈ Finset.range (p + 1),
          ↑(p.choose a) * (r : ℚ) ^ (p - a) *
            ((L : ℚ) * (y : ℚ)) ^ a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [mul_pow]
      ring
    _ = ((r : ℚ) + (L : ℚ) * (y : ℚ)) ^ p := by
      calc
        _ = ((L : ℚ) * (y : ℚ) + (r : ℚ)) ^ p := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (add_pow ((L : ℚ) * (y : ℚ)) (r : ℚ) p).symm
        _ = _ := by rw [add_comm]
    _ = ((r + L * y : ℕ) : ℚ) ^ p := by
      congr 1
      push_cast
      ring

private lemma powerSumPolynomial_natDegree_le (p : ℕ) :
    (powerSumPolynomial p).natDegree ≤ p + 1 := by
  rw [powerSumPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc
    (Polynomial.C
          (bernoulli i * ((p + 1).choose i : ℚ) / (p + 1 : ℚ)) *
        Polynomial.X ^ (p + 1 - i)).natDegree ≤
        (Polynomial.C
          (bernoulli i * ((p + 1).choose i : ℚ) / (p + 1 : ℚ))).natDegree +
          (Polynomial.X ^ (p + 1 - i)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ p + 1 - i := by simp
    _ ≤ p + 1 := Nat.sub_le _ _

private lemma lowKernel_natDegree_le (L p : ℕ) :
    (lowKernel L p).natDegree ≤ p + 1 := by
  rw [lowKernel]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  have ha' : a ≤ p := by
    have := Finset.mem_range.mp ha
    omega
  have hlinear :
      (Polynomial.C (L + 1 : ℚ) - (Polynomial.X : Polynomial ℚ)).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
      simp)
  calc
    (Polynomial.C
          ((p.choose a : ℚ) * (L + 1 : ℚ) ^ (p - a) * (L : ℚ) ^ a) *
        Polynomial.X ^ (p - a) *
          (powerSumPolynomial a).comp
            (Polynomial.C (L + 1 : ℚ) - Polynomial.X)).natDegree ≤
        (Polynomial.C
            ((p.choose a : ℚ) * (L + 1 : ℚ) ^ (p - a) * (L : ℚ) ^ a) *
          Polynomial.X ^ (p - a)).natDegree +
        ((powerSumPolynomial a).comp
          (Polynomial.C (L + 1 : ℚ) - Polynomial.X)).natDegree :=
            Polynomial.natDegree_mul_le
    _ ≤ (p - a) + (a + 1) * 1 := by
      apply Nat.add_le_add
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
      · exact Polynomial.natDegree_comp_le.trans
          (Nat.mul_le_mul (powerSumPolynomial_natDegree_le a) hlinear)
    _ ≤ p + 1 := by omega

private lemma highKernel_natDegree_le (L p : ℕ) :
    (highKernel L p).natDegree ≤ p + 1 := by
  rw [highKernel]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  have ha' : a ≤ p := by
    have := Finset.mem_range.mp ha
    omega
  calc
    (Polynomial.C ((p.choose a : ℚ) * (L : ℚ) ^ a) *
        Polynomial.X ^ (p - a) * powerSumPolynomial a).natDegree ≤
        (Polynomial.C ((p.choose a : ℚ) * (L : ℚ) ^ a) *
          Polynomial.X ^ (p - a)).natDegree +
          (powerSumPolynomial a).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (p - a) + (a + 1) := by
      exact Nat.add_le_add
        ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
        (powerSumPolynomial_natDegree_le a)
    _ ≤ p + 1 := by omega

private lemma sum_last_transition (j q p : ℕ) (x : Fin j → ℕ) :
    let L := prefixPeriod j
    let r := prefixMass j x % L
    (∑ last ∈ Finset.range (L + 1),
        if prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) = q then
          ((prefixMass (j + 1) (Fin.snoc x last) % prefixPeriod (j + 1) : ℕ) : ℚ) ^ p
        else 0) =
      (if prefixMass j x / L = q then (lowKernel L p).eval (r : ℚ) else 0) +
      if 0 < q then
        if prefixMass j x / L = q - 1 then (highKernel L p).eval (r : ℚ) else 0
      else 0 := by
  dsimp only
  let L := prefixPeriod j
  let r := prefixMass j x % L
  have hL : 0 < L := prefixPeriod_pos j
  have hr : r < L := Nat.mod_lt _ hL
  have hsplit : L + 1 = (L - r + 1) + r := by omega
  rw [hsplit, Finset.sum_range_add]
  have hlow :
      (∑ last ∈ Finset.range (L - r + 1),
          if prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) = q then
            ((prefixMass (j + 1) (Fin.snoc x last) % prefixPeriod (j + 1) : ℕ) : ℚ) ^ p
          else 0) =
        if prefixMass j x / L = q then (lowKernel L p).eval (r : ℚ) else 0 := by
    rw [lowKernel_eval L r p (Nat.le_of_lt hr)]
    by_cases hq : prefixMass j x / L = q
    · rw [if_pos hq]
      apply Finset.sum_congr rfl
      intro last hlast
      have hlast' : last ≤ L - r := by
        have := Finset.mem_range.mp hlast
        omega
      have h := prefixMass_snoc_low j x last (by simpa [L, r] using hlast')
      have hquot := h.1
      have hrem := h.2
      change prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) =
        prefixMass j x / L at hquot
      change prefixMass (j + 1) (Fin.snoc x last) % prefixPeriod (j + 1) =
        (L + 1) * r + L * last at hrem
      rw [hquot, hrem, if_pos hq]
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro last hlast
      have hlast' : last ≤ L - r := by
        have := Finset.mem_range.mp hlast
        omega
      have h := prefixMass_snoc_low j x last (by simpa [L, r] using hlast')
      have hquot := h.1
      change prefixMass (j + 1) (Fin.snoc x last) / prefixPeriod (j + 1) =
        prefixMass j x / L at hquot
      rw [hquot, if_neg hq]
  have hhigh :
      (∑ y ∈ Finset.range r,
          if prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) /
              prefixPeriod (j + 1) = q then
            ((prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) %
                prefixPeriod (j + 1) : ℕ) : ℚ) ^ p
          else 0) =
        if 0 < q then
          if prefixMass j x / L = q - 1 then (highKernel L p).eval (r : ℚ) else 0
        else 0 := by
    rw [highKernel_eval]
    by_cases hq : prefixMass j x / L + 1 = q
    · have hqpos : 0 < q := by
        rw [← hq]
        exact Nat.zero_lt_succ _
      have hqpred : prefixMass j x / L = q - 1 := by
        rw [← hq]
        exact (Nat.add_sub_cancel (prefixMass j x / L) 1).symm
      rw [if_pos hqpos, if_pos hqpred]
      apply Finset.sum_congr rfl
      intro y hy
      have h := prefixMass_snoc_high j x y (Finset.mem_range.mp hy)
      dsimp only at h
      have hquot := h.1
      have hrem := h.2
      change prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) /
        prefixPeriod (j + 1) = prefixMass j x / L + 1 at hquot
      change prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) %
        prefixPeriod (j + 1) = r + L * y at hrem
      rw [hquot, hrem, if_pos hq]
    · by_cases hqpos : 0 < q
      · have hqpred : prefixMass j x / L ≠ q - 1 := by omega
        rw [if_pos hqpos, if_neg hqpred]
        apply Finset.sum_eq_zero
        intro y hy
        have h := prefixMass_snoc_high j x y (Finset.mem_range.mp hy)
        dsimp only at h
        have hquot := h.1
        change prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) /
          prefixPeriod (j + 1) = prefixMass j x / L + 1 at hquot
        rw [hquot, if_neg hq]
      · rw [if_neg hqpos]
        apply Finset.sum_eq_zero
        intro y hy
        have h := prefixMass_snoc_high j x y (Finset.mem_range.mp hy)
        dsimp only at h
        have hquot := h.1
        change prefixMass (j + 1) (Fin.snoc x (L - r + 1 + y)) /
          prefixPeriod (j + 1) = prefixMass j x / L + 1 at hquot
        rw [hquot, if_neg (by omega)]
  rw [hlow, hhigh]

private lemma fiber_eval_eq_moments (j q n : ℕ) (P : Polynomial ℚ)
    (hP : P.natDegree < n) :
    (∑ x ∈ prefixBox j with prefixMass j x / prefixPeriod j = q,
        P.eval ((prefixMass j x % prefixPeriod j : ℕ) : ℚ)) =
      ∑ a ∈ Finset.range n, P.coeff a * actualMoment j q a := by
  unfold actualMoment
  simp_rw [Polynomial.eval_eq_sum_range' hP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

private lemma actualMoment_succ_eval (j q p : ℕ) :
    actualMoment (j + 1) q p =
      (∑ x ∈ prefixBox j with prefixMass j x / prefixPeriod j = q,
        (lowKernel (prefixPeriod j) p).eval
          ((prefixMass j x % prefixPeriod j : ℕ) : ℚ)) +
      if 0 < q then
        ∑ x ∈ prefixBox j with prefixMass j x / prefixPeriod j = q - 1,
          (highKernel (prefixPeriod j) p).eval
            ((prefixMass j x % prefixPeriod j : ℕ) : ℚ)
      else 0 := by
  rw [actualMoment, Finset.sum_filter]
  rw [sum_prefixBox_succ, Finset.sum_comm]
  simp_rw [sum_last_transition]
  rw [Finset.sum_add_distrib]
  by_cases hq : 0 < q
  · simp only [if_pos hq]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
  · simp only [if_neg hq, Finset.sum_const_zero, add_zero]
    rw [← Finset.sum_filter]

private lemma actualMoment_succ (j q p : ℕ) :
    actualMoment (j + 1) q p =
      (∑ a ∈ Finset.range (p + 2),
        (lowKernel (prefixPeriod j) p).coeff a * actualMoment j q a) +
      if 0 < q then
        ∑ a ∈ Finset.range (p + 2),
          (highKernel (prefixPeriod j) p).coeff a * actualMoment j (q - 1) a
      else 0 := by
  rw [actualMoment_succ_eval]
  rw [fiber_eval_eq_moments j q (p + 2) _ (by
    have := lowKernel_natDegree_le (prefixPeriod j) p
    omega)]
  by_cases hq : 0 < q
  · rw [if_pos hq, fiber_eval_eq_moments j (q - 1) (p + 2) _ (by
      have := highKernel_natDegree_le (prefixPeriod j) p
      omega)]
    simp only [if_pos hq]
  · simp only [if_neg hq, add_zero]

private def computedMoment : ℕ → ℕ → ℕ → ℚ
  | 0, q, p => if q = 0 then if p = 0 then 1 else 0 else 0
  | j + 1, q, p =>
      let L := prefixPeriod j
      (∑ a ∈ Finset.range (p + 2),
        (lowKernel L p).coeff a * computedMoment j q a) +
      if 0 < q then
        ∑ a ∈ Finset.range (p + 2),
          (highKernel L p).coeff a * computedMoment j (q - 1) a
      else 0

private lemma computedMoment_eq_actualMoment (j q p : ℕ) :
    computedMoment j q p = actualMoment j q p := by
  induction j generalizing q p with
  | zero =>
      rw [computedMoment, actualMoment_zero]
  | succ j ih =>
      rw [computedMoment, actualMoment_succ]
      simp_rw [ih]

private lemma prefixMass_div_lt (j : ℕ) (hj : 0 < j) (x : Fin j → ℕ)
    (hx : x ∈ prefixBox j) : prefixMass j x / prefixPeriod j < j := by
  have hterm (i : Fin j) :
      x i * (prefixPeriod j / sylvester (i.1 + 1)) < prefixPeriod j := by
    have hxi : x i < sylvester (i.1 + 1) := by
      have hi := Fintype.mem_piFinset.mp hx i
      simpa [prefixBox] using Finset.mem_range.mp hi
    obtain ⟨c, hc⟩ := sylvester_dvd_prefixPeriod j i
    have hs : 0 < sylvester (i.1 + 1) :=
      Nat.zero_lt_of_lt (two_le_sylvester (i.1 + 1) (by omega))
    have hcpos : 0 < c := by
      have hp := prefixPeriod_pos j
      rw [hc] at hp
      exact Nat.pos_of_mul_pos_left hp
    have hquot : prefixPeriod j / sylvester (i.1 + 1) = c := by
      rw [hc]
      simpa using Nat.mul_div_right c hs
    rw [hquot, hc]
    exact Nat.mul_lt_mul_of_pos_right hxi hcpos
  have hmass : prefixMass j x < j * prefixPeriod j := by
    rw [prefixMass]
    calc
      (∑ i : Fin j, x i * (prefixPeriod j / sylvester (i.1 + 1))) <
          ∑ _i : Fin j, prefixPeriod j := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact ⟨⟨0, hj⟩, Finset.mem_univ _⟩
            · intro i hi
              exact hterm i
      _ = j * prefixPeriod j := by simp [Nat.mul_comm]
  rw [Nat.div_lt_iff_lt_mul (prefixPeriod_pos j)]
  simpa [Nat.mul_comm] using hmass

private lemma snoc_mass_dvd_iff (L A last : ℕ) (hL : 0 < L) (hlast : last < L + 1) :
    L * (L + 1) ∣ (L + 1) * A + L * last ↔ L ∣ A ∧ last = 0 := by
  constructor
  · intro h
    have hsucc : L + 1 ∣ (L + 1) * A + L * last :=
      dvd_trans ⟨L, by ring⟩ h
    have hlastDvd : L + 1 ∣ L * last :=
      (Nat.dvd_add_iff_right (Nat.dvd_mul_right (L + 1) A)).mpr hsucc
    have hcop : Nat.Coprime (L + 1) L := by simp [Nat.add_comm]
    have hlastZero : last = 0 := by
      have := hcop.dvd_of_dvd_mul_left hlastDvd
      exact Nat.eq_zero_of_dvd_of_lt this hlast
    subst last
    simp only [mul_zero, add_zero] at h
    rcases h with ⟨c, hc⟩
    refine ⟨⟨c, ?_⟩, rfl⟩
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < L + 1)
    nlinarith
  · rintro ⟨⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    ring

private lemma prefixMass_mod_eq_zero_iff (j : ℕ) (x : Fin j → ℕ)
    (hx : x ∈ prefixBox j) :
    prefixMass j x % prefixPeriod j = 0 ↔ ∀ i, x i = 0 := by
  induction j with
  | zero => simp [prefixMass, prefixPeriod, sylvester]
  | succ j ih =>
      let old : Fin j → ℕ := Fin.init x
      let last := x (Fin.last j)
      have hxold : old ∈ prefixBox j := by
        rw [prefixBox]
        apply Fintype.mem_piFinset.mpr
        intro i
        have hi := Fintype.mem_piFinset.mp (show x ∈ prefixBox (j + 1) from hx) i.castSucc
        have hi' := Finset.mem_range.mp (show x i.castSucc ∈
          Finset.range (sylvester (i.1 + 1)) by simpa [prefixBox] using hi)
        apply Finset.mem_range.mpr
        change old i < sylvester (i.1 + 1)
        exact hi'
      have hlast : last < prefixPeriod j + 1 := by
        have hi := Fintype.mem_piFinset.mp hx (Fin.last j)
        simpa [prefixBox, last, prefixPeriod_add_one] using Finset.mem_range.mp hi
      have hsnoc : Fin.snoc old last = x := Fin.snoc_init_self x
      rw [← hsnoc, prefixMass_snoc, prefixPeriod_succ,
        Nat.dvd_iff_mod_eq_zero.symm, snoc_mass_dvd_iff _ _ _ (prefixPeriod_pos j) hlast,
        Nat.dvd_iff_mod_eq_zero, ih old hxold]
      constructor
      · rintro ⟨hold, hzero⟩ i
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simpa [last] using hzero
        · simpa [old] using hold k
      · intro hall
        exact ⟨fun i => by simpa [old] using hall i.castSucc,
          by simpa [last] using hall (Fin.last j)⟩

private lemma unitPolynomial_coeff (M n : ℕ) :
    (unitPolynomial M).coeff n = if n < M then 1 else 0 := by
  simp [unitPolynomial_def, Polynomial.coeff_X_pow, eq_comm]

private lemma unitPolynomial_sq_coeff_low (M n : ℕ) (hn : n < M) :
    (unitPolynomial M ^ 2).coeff n = (n + 1 : ℕ) := by
  rw [pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [unitPolynomial_coeff]
  calc
    (∑ k ∈ Finset.range n.succ,
        (if k < M then (1 : ℚ) else 0) * if n - k < M then 1 else 0) =
        ∑ _k ∈ Finset.range n.succ, (1 : ℚ) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_range.mp hk
          simp [show k < M by omega, show n - k < M by omega]
    _ = (n + 1 : ℕ) := by simp

private lemma unitPolynomial_sq_coeff_high (M n : ℕ) (hM : 0 < M)
    (hlo : M ≤ n) (hhi : n < 2 * M) :
    (unitPolynomial M ^ 2).coeff n = (2 * M - 1 - n : ℕ) := by
  rw [pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [unitPolynomial_coeff]
  have hfilter :
      {k ∈ Finset.range (n + 1) | k < M ∧ n - k < M} =
        Finset.Ioc (n - M) (M - 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  calc
    (∑ k ∈ Finset.range (n + 1),
        (if k < M then (1 : ℚ) else 0) * if n - k < M then 1 else 0) =
        ∑ k ∈ Finset.range (n + 1),
          if k < M ∧ n - k < M then (1 : ℚ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases h₁ : k < M <;> by_cases h₂ : n - k < M <;> simp [h₁, h₂]
    _ = ({k ∈ Finset.range (n + 1) | k < M ∧ n - k < M}.card : ℚ) :=
      Finset.sum_boole _ _
    _ = (2 * M - 1 - n : ℕ) := by
      rw [hfilter]
      norm_cast
      simp
      omega

private def zeroMoment (j q : ℕ) : ℚ :=
  ∑ x ∈ prefixBox j with prefixMass j x / prefixPeriod j = q,
    if prefixMass j x % prefixPeriod j = 0 then 1 else 0

private lemma zeroMoment_eq (j q : ℕ) :
    zeroMoment j q = if q = 0 then 1 else 0 := by
  classical
  let z : Fin j → ℕ := fun _ => 0
  have hzbox : z ∈ prefixBox j := by
    rw [prefixBox]
    exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr
      (Nat.zero_lt_of_lt (two_le_sylvester (i.1 + 1) (by omega)))
  have hzmass : prefixMass j z = 0 := by simp [prefixMass, z]
  by_cases hq : q = 0
  · subst q
    rw [if_pos rfl]
    rw [zeroMoment, Finset.sum_eq_single z]
    · simp [hzmass]
    · intro x hx hxz
      have hxbox : x ∈ prefixBox j := (Finset.mem_filter.mp hx).1
      have hne : prefixMass j x % prefixPeriod j ≠ 0 := by
        intro hzero
        have hall := (prefixMass_mod_eq_zero_iff j x hxbox).mp hzero
        apply hxz
        funext i
        simpa [z] using hall i
      simp [hne]
    · intro hz
      exact (hz (Finset.mem_filter.mpr ⟨hzbox, by simp [hzmass]⟩)).elim
  · rw [if_neg hq, zeroMoment]
    apply Finset.sum_eq_zero
    intro x hx
    have hxbox : x ∈ prefixBox j := (Finset.mem_filter.mp hx).1
    have hxq : prefixMass j x / prefixPeriod j = q := (Finset.mem_filter.mp hx).2
    by_cases hzero : prefixMass j x % prefixPeriod j = 0
    · have hall := (prefixMass_mod_eq_zero_iff j x hxbox).mp hzero
      have hmass := (prefixMass_eq_zero_iff j x hxbox).mpr hall
      simp [hzero]
      rw [hmass] at hxq
      simp at hxq
      exact (hq hxq.symm).elim
    · simp [hzero]

private lemma prefix_mul_unit_sq_coeff (j n : ℕ) :
    (prefixPolynomial j * unitPolynomial (prefixPeriod j) ^ 2).coeff n =
      ∑ x ∈ prefixBox j,
        if prefixMass j x ≤ n then
          (unitPolynomial (prefixPeriod j) ^ 2).coeff (n - prefixMass j x)
        else 0 := by
  classical
  rw [prefixPolynomial_def, Finset.sum_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Polynomial.coeff_X_pow_mul']

private lemma periodNumerator_seven_coeff (n : ℕ) :
    (periodNumerator 7).coeff n =
      ∑ x ∈ prefixBox 6,
        if prefixMass 6 x ≤ n then
          (unitPolynomial (prefixPeriod 6) ^ 2).coeff (n - prefixMass 6 x)
        else 0 := by
  rw [periodNumerator_seven_factorization, prefix_mul_unit_sq_coeff]

private lemma actualMoment_eq_sum_ite (j q p : ℕ) :
    actualMoment j q p =
      ∑ x ∈ prefixBox j, if prefixMass j x / prefixPeriod j = q then
        ((prefixMass j x % prefixPeriod j : ℕ) : ℚ) ^ p else 0 := by
  rw [actualMoment, Finset.sum_filter]

private lemma zeroMoment_eq_sum_ite (j q : ℕ) :
    zeroMoment j q =
      ∑ x ∈ prefixBox j, if prefixMass j x / prefixPeriod j = q then
        if prefixMass j x % prefixPeriod j = 0 then 1 else 0 else 0 := by
  rw [zeroMoment, Finset.sum_filter]

private def fiberStat (q : ℕ) (alpha beta gamma : ℚ) : ℚ :=
  alpha * actualMoment 6 q 0 + beta * actualMoment 6 q 1 + gamma * zeroMoment 6 q

set_option linter.constructorNameAsVariable false in
private lemma fiberStat_eq_sum (q : ℕ) (alpha beta gamma : ℚ) :
    fiberStat q alpha beta gamma =
      ∑ x ∈ prefixBox 6,
        if prefixMass 6 x / prefixPeriod 6 = q then
          alpha + beta * (prefixMass 6 x % prefixPeriod 6 : ℕ) +
            gamma * if prefixMass 6 x % prefixPeriod 6 = 0 then 1 else 0
        else 0 := by
  classical
  rw [fiberStat, actualMoment_eq_sum_ite, actualMoment_eq_sum_ite,
    zeroMoment_eq_sum_ite, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hq : prefixMass 6 x / prefixPeriod 6 = q <;>
    by_cases hr : prefixMass 6 x % prefixPeriod 6 = 0 <;> simp [hq, hr] <;> ring

private lemma unitPolynomial_sq_coeff_zero (M n : ℕ) (hn : 2 * M - 1 < n) :
    (unitPolynomial M ^ 2).coeff n = 0 := by
  rw [pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_eq_zero
  intro k hk
  rw [unitPolynomial_coeff, unitPolynomial_coeff]
  by_cases hkM : k < M <;> by_cases hnkM : n - k < M <;> simp [hkM, hnkM]
  have hkle : k ≤ n := by omega
  omega

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartDimensionSeven
