/- GID: D5/S3/Arith/Factorization/PrimeWordWeight
   generality: G
   mirror-B: D5/B/S3/Arith/Factorization/PrimeWordWeight
   mirror-E: none(waiver:symbolic-prime-word-estimates)
   anchors: []
   utility: none
   digest: Ordered prime-factor words, weighted recurrences and finite moments. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic

/-!
Distinct permutations of a prime-factor list carry weighted divisor and
first-letter recurrences. Their finite fractional moments are bounded for
every Dirichlet exponent above one, with the fractional exponent fixed first.
These statements do not depend on a sequence or its recurrence. The shared
namespace preserves the public constant names used by A124056Occurrence.
-/

namespace D5.S3.Arith.Recurrence.A124056Occurrence

/-- Distinct prime words, including the empty word for one. -/
def primeWords (v : ℕ) : Finset (List ℕ) := v.primeFactorsList.permutations.toFinset

abbrev omega (v : ℕ) : ℕ := v.primeFactorsList.length

def primeWordCount (v : ℕ) : ℕ := (primeWords v).card

def primeWordWeight (A v : ℕ) : ℕ := A ^ omega v * primeWordCount v

private theorem mem_primeWords {v : ℕ} (hv : v ≠ 0) (w : List ℕ) :
    w ∈ primeWords v ↔ w.prod = v ∧ ∀ p ∈ w, Nat.Prime p := by
  simp only [primeWords, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.prod_eq.trans (Nat.prod_primeFactorsList hv),
      fun p hp => Nat.prime_of_mem_primeFactorsList (h.mem_iff.mp hp)⟩
  · rintro ⟨hp, hprime⟩
    exact Nat.primeFactorsList_unique hp hprime

private theorem primeWord_length {v : ℕ} {w : List ℕ} (hw : w ∈ primeWords v) :
    w.length = omega v := by
  exact (List.mem_permutations.mp (List.mem_toFinset.mp hw)).length_eq

private theorem primeWordCount_pos (v : ℕ) : 0 < primeWordCount v := by
  apply Finset.card_pos.mpr
  exact ⟨v.primeFactorsList, by simp [primeWords]⟩

/-- Splitting a prime word at a fixed position is a bijection with a pair of
words whose first product is a divisor of that factor-count rank. -/
theorem prime_word_split (v j : ℕ) (hv : 0 < v) (hj : j ≤ omega v) :
    (∑ d ∈ v.divisors.filter (fun d => omega d = j),
      primeWordCount d * primeWordCount (v / d)) = primeWordCount v := by
  classical
  let S := (v.divisors.filter (fun d => omega d = j)).sigma
    (fun d => (primeWords d) ×ˢ (primeWords (v / d)))
  have hcard : S.card = ∑ d ∈ v.divisors.filter (fun d => omega d = j),
      primeWordCount d * primeWordCount (v / d) := by
    simp [S, primeWordCount]
  rw [← hcard]
  apply Finset.card_bij (fun x _ => x.2.1 ++ x.2.2)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hd, hw⟩
    have hdv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hd0 := ne_zero_of_dvd_ne_zero hv.ne' hdv
    have hquot : v / x.1 ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd hv hdv) (Nat.pos_of_ne_zero hd0)).ne'
    have h1 := (mem_primeWords hd0 x.2.1).mp (Finset.mem_product.mp hw).1
    have h2 := (mem_primeWords hquot x.2.2).mp (Finset.mem_product.mp hw).2
    apply (mem_primeWords hv.ne' _).mpr
    refine ⟨by rw [List.prod_append, h1.1, h2.1, Nat.mul_div_cancel' hdv], ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h1.2 p hp
    · exact h2.2 p hp
  · intro x hx y hy heq
    rcases Finset.mem_sigma.mp hx with ⟨hxd, hxw⟩
    rcases Finset.mem_sigma.mp hy with ⟨hyd, hyw⟩
    have hxl : x.2.1.length = j :=
      (primeWord_length (Finset.mem_product.mp hxw).1).trans (Finset.mem_filter.mp hxd).2
    have hyl : y.2.1.length = j :=
      (primeWord_length (Finset.mem_product.mp hyw).1).trans (Finset.mem_filter.mp hyd).2
    have hu : x.2.1 = y.2.1 := by
      have := congrArg (List.take j) heq
      simpa [hxl, hyl] using this
    have hw : x.2.2 = y.2.2 := by
      have := congrArg (List.drop j) heq
      simpa [hxl, hyl] using this
    have hxd0 := ne_zero_of_dvd_ne_zero hv.ne'
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hxd).1)
    have hyd0 := ne_zero_of_dvd_ne_zero hv.ne'
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hyd).1)
    have hd : x.1 = y.1 :=
      ((mem_primeWords hxd0 _).mp (Finset.mem_product.mp hxw).1).1.symm.trans
        ((congrArg List.prod hu).trans
          ((mem_primeWords hyd0 _).mp (Finset.mem_product.mp hyw).1).1)
    cases x with | mk xd xw =>
      cases y with | mk yd yw =>
        dsimp at hd hu hw
        subst yd
        exact congrArg (Sigma.mk xd) (Prod.ext hu hw)
  · intro w hw
    have hwp := (mem_primeWords hv.ne' w).mp hw
    let u := w.take j
    let z := w.drop j
    let d := u.prod
    have hdv : d ∣ v := ⟨z.prod, by
      simpa [d, u, z] using ((List.prod_take_mul_prod_drop w j).trans hwp.1).symm⟩
    have hd0 := ne_zero_of_dvd_ne_zero hv.ne' hdv
    have huprime : ∀ p ∈ u, Nat.Prime p :=
      fun p hp => hwp.2 p (List.mem_of_mem_take hp)
    have hzprime : ∀ p ∈ z, Nat.Prime p :=
      fun p hp => hwp.2 p (List.mem_of_mem_drop hp)
    have hu : u ∈ primeWords d := (mem_primeWords hd0 _).mpr ⟨rfl, huprime⟩
    have hul : omega d = j := by
      have hh := primeWord_length hu
      dsimp [u] at hh
      rw [List.length_take, primeWord_length hw, Nat.min_eq_left hj] at hh
      exact hh.symm
    have hzprod : z.prod = v / d := by
      apply (Nat.eq_div_iff_mul_eq_left hd0 hdv).mpr
      simpa [mul_comm, d, u, z] using
        ((List.prod_take_mul_prod_drop w j).trans hwp.1).symm
    have hz0 : v / d ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd hv hdv) (Nat.pos_of_ne_zero hd0)).ne'
    refine ⟨⟨d, u, z⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv, hv.ne'⟩, hul⟩, ?_⟩
      exact Finset.mem_product.mpr ⟨hu, (mem_primeWords hz0 _).mpr ⟨hzprod, hzprime⟩⟩
    · exact List.take_append_drop j w

private theorem omega_lt_of_proper {v d : ℕ} (hv : v ≠ 0)
    (hd : d ∈ v.properDivisors) : omega d < omega v := by
  have hsub := Nat.primeFactorsList_sublist_of_dvd (Nat.mem_properDivisors.mp hd).1 hv
  apply lt_of_le_of_ne hsub.length_le
  intro heq
  have hlist := hsub.eq_of_length heq
  have hd0 := ne_zero_of_dvd_ne_zero hv (Nat.mem_properDivisors.mp hd).1
  have hdv : d = v := by
    rw [← Nat.prod_primeFactorsList hd0, hlist, Nat.prod_primeFactorsList hv]
  exact (Nat.mem_properDivisors.mp hd).2.ne hdv

private theorem prime_word_layer_bound (v j : ℕ) (hv : 0 < v) (hj : j < omega v) :
    (∑ d ∈ v.properDivisors.filter (fun d => omega d = j), primeWordCount d) ≤
      primeWordCount v := by
  calc
    _ ≤ ∑ d ∈ v.divisors.filter (fun d => omega d = j),
        primeWordCount d * primeWordCount (v / d) := by
      apply le_trans (Finset.sum_le_sum (fun d _ =>
        Nat.le_mul_of_pos_right _ (primeWordCount_pos (v / d))))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have h := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(Nat.mem_properDivisors.mp h.1).1, hv.ne'⟩, h.2⟩
      · intros; exact Nat.zero_le _
    _ = _ := prime_word_split v j hv hj.le

/-- The geometric layer sum absorbs every proper divisor with `A=q+1`. -/
theorem prime_word_weight_bound (q v : ℕ) (hv : 0 < v) :
    q * (∑ d ∈ v.properDivisors, primeWordWeight (q + 1) d) ≤
      primeWordWeight (q + 1) v := by
  classical
  have hlayers : (∑ d ∈ v.properDivisors, primeWordWeight (q + 1) d) =
      ∑ j ∈ Finset.range (omega v),
        (q + 1) ^ j *
          ∑ d ∈ v.properDivisors.filter (fun d => omega d = j), primeWordCount d := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    simp [omega_lt_of_proper hv.ne' hd, primeWordWeight]
  rw [hlayers]
  have hsum : (∑ j ∈ Finset.range (omega v),
      (q + 1) ^ j * ∑ d ∈ v.properDivisors.filter (fun d => omega d = j),
        primeWordCount d) ≤
      (∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (prime_word_layer_bound v j hv (Finset.mem_range.mp hj))
  have hgeom (k : ℕ) : q * (∑ j ∈ Finset.range k, (q + 1) ^ j) + 1 = (q + 1) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]; nlinarith
  calc
    _ ≤ q * ((∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v) :=
      Nat.mul_le_mul_left q hsum
    _ = (q * ∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v := by ring
    _ ≤ (q + 1) ^ omega v * primeWordCount v :=
      Nat.mul_le_mul_right _ (by have := hgeom (omega v); omega)
    _ = _ := rfl

private theorem omega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    omega (m * n) = omega m + omega n := by
  exact (Nat.perm_primeFactorsList_mul hm hn).length_eq.trans (List.length_append ..)

private theorem omega_eq_one_iff_prime {n : ℕ} (hn : n ≠ 0) :
    omega n = 1 ↔ Nat.Prime n := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
    have hprod := Nat.prod_primeFactorsList hn
    rw [hp] at hprod
    simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList (n := n) (by rw [hp]; simp)
    exact hprod ▸ hprime
  · intro h
    simp [omega, Nat.primeFactorsList_prime h]

/-- Removing the first prime gives the exact weighted first-letter recurrence. -/
theorem prime_word_first_letter (A v : ℕ) (hv : 1 < v) :
    primeWordWeight A v =
      A * ∑ p ∈ v.primeFactors, primeWordWeight A (v / p) := by
  classical
  have hv0 : v ≠ 0 := by omega
  have hk : 1 ≤ omega v := by
    have := (Nat.primeFactorsList_ne_nil v).mpr hv
    exact List.length_pos_iff.mpr this
  have hset : v.divisors.filter (fun d => omega d = 1) = v.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hd, _⟩, hl⟩
      exact ⟨(omega_eq_one_iff_prime (ne_zero_of_dvd_ne_zero hv0 hd)).mp hl, hd, hv0⟩
    · rintro ⟨hp, hd, _⟩
      exact ⟨⟨hd, hv0⟩, (omega_eq_one_iff_prime hp.ne_zero).mpr hp⟩
  have hsplit := prime_word_split v 1 (by omega) hk
  rw [hset] at hsplit
  have hcount : primeWordCount v = ∑ p ∈ v.primeFactors, primeWordCount (v / p) := by
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    simp [primeWordCount, primeWords, Nat.primeFactorsList_prime hprime, List.permutations]
  unfold primeWordWeight
  rw [hcount, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hquot : v / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hprime.pos).ne'
  have heq : omega v = omega (v / p) + 1 := by
    have h := omega_mul hprime.ne_zero hquot
    rw [Nat.mul_div_cancel' hd] at h
    simpa [omega, Nat.primeFactorsList_prime hprime, Nat.add_comm] using h
  rw [heq, pow_succ]
  ring

/-- A finite prime-sum hypothesis controls every actual prime-word weight. -/
theorem prime_word_pointwise (C : ℕ) (r : ℝ)
    (hprime : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-r) ≤ 1) :
    ∀ v : ℕ, 0 < v → (primeWordWeight C v : ℝ) ≤ (v : ℝ) ^ r := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro hv
    by_cases hv1 : v = 1
    · subst v
      simp [primeWordWeight, primeWordCount, primeWords, omega]
    have hv2 : 1 < v := by omega
    rw [prime_word_first_letter C v hv2, Nat.cast_mul, Nat.cast_sum]
    calc
      _ ≤ (C : ℝ) * ∑ p ∈ v.primeFactors, ((v / p : ℕ) : ℝ) ^ r := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
        apply Finset.sum_le_sum
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        exact ih _ (Nat.div_lt_self hv hprime.one_lt)
          (Nat.div_pos (Nat.le_of_dvd hv hd) hprime.pos)
      _ = (v : ℝ) ^ r * ((C : ℝ) * ∑ p ∈ v.primeFactors, (p : ℝ) ^ (-r)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        rw [Nat.cast_div hd (by exact_mod_cast hprime.ne_zero : (p : ℝ) ≠ 0),
          Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          Real.rpow_neg (Nat.cast_nonneg _)]
        ring
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_left
          (hprime v.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp))
          (Real.rpow_nonneg (Nat.cast_nonneg v) r)

private theorem prime_sum_parameter (C : ℕ) :
    ∃ r : ℝ, 1 < r ∧ ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-r) ≤ 1 := by
  classical
  let Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / ((C : ℝ) * Z + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(k : ℝ) + 2, by have := Nat.cast_nonneg (α := ℝ) k; linarith, ?_⟩
  intro T hT
  have hp (p : ℕ) (hp : p ∈ T) :
      (p : ℝ) ^ (-((k : ℝ) + 2)) ≤ (1 / 2 : ℝ) ^ k * (p : ℝ) ^ (-2 : ℝ) := by
    have hpp : (2 : ℝ) ≤ p := by exact_mod_cast (hT p hp).two_le
    have hp0 : (0 : ℝ) < p := by positivity
    rw [show -((k : ℝ) + 2) = -(k : ℝ) + (-2) by ring, Real.rpow_add hp0,
      Real.rpow_neg hp0.le, Real.rpow_natCast, ← inv_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity)
        (by simpa using (one_div_le_one_div_of_le (by norm_num) hpp)) k)
      (Real.rpow_nonneg hp0.le _)
  have hsum : ∑ p ∈ T, (p : ℝ) ^ (-((k : ℝ) + 2)) ≤ (1 / 2 : ℝ) ^ k * Z := by
    calc
      _ ≤ ∑ p ∈ T, (1 / 2 : ℝ) ^ k * (p : ℝ) ^ (-2 : ℝ) := Finset.sum_le_sum hp
      _ = (1 / 2 : ℝ) ^ k * ∑ p ∈ T, (p : ℝ) ^ (-2 : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum T (fun n _ => by positivity)) (by positivity)
  have hk' : (1 / 2 : ℝ) ^ k * ((C : ℝ) * Z + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hk
  have hk0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hC : (C : ℝ) * (∑ p ∈ T, (p : ℝ) ^ (-((k : ℝ) + 2))) ≤
      (C : ℝ) * ((1 / 2 : ℝ) ^ k * Z) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg C)
  nlinarith

/-- The exponent is chosen using only the weight parameter, uniformly in v. -/
theorem prime_word_polynomial_bound (A : ℕ) :
    ∃ r : ℝ, 1 < r ∧ ∀ v : ℕ, 0 < v →
      (primeWordWeight (2 * A) v : ℝ) ≤ (v : ℝ) ^ r := by
  obtain ⟨r, hr, hp⟩ := prime_sum_parameter (2 * A)
  exact ⟨r, hr, prime_word_pointwise (2 * A) r hp⟩

def roughPrefix (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ∉ S)

/-- The weighted rough first moment is bounded by absorption of a finite
first-letter sum; no infinite rearrangement is used. -/
theorem rough_prime_word_sum (C : ℕ) (σ : ℝ) (S : Finset ℕ)
    (htail : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) → Disjoint T S →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ) ≤ 1 / 2) (X : ℕ) :
    (∑ n ∈ roughPrefix S X, (primeWordWeight C n : ℝ) * (n : ℝ) ^ (-σ)) ≤ 2 := by
  classical
  let G := roughPrefix S X
  let T := (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p ∉ S)
  let f : ℕ → ℝ := fun n => (primeWordWeight C n : ℝ) * (n : ℝ) ^ (-σ)
  let R : ℝ := ∑ n ∈ G, f n
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hG {n : ℕ} (hn : n ∈ G) :
      n ≤ X ∧ 0 < n ∧ ∀ p ∈ n.primeFactors, p ∉ S := by
    have h := Finset.mem_filter.mp hn
    exact ⟨by have := Finset.mem_range.mp h.1; omega, h.2⟩
  have hpG {n p : ℕ} (hn : n ∈ G) (hp : p ∈ n.primeFactors) : p ∈ T ∧ n / p ∈ G := by
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hn' := hG hn
    have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn'.2.1 hd) hprime.pos
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by have := Nat.le_of_dvd hn'.2.1 hd; omega), hprime, hn'.2.2 p hp⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by have := Nat.div_le_self n p; omega), hquot, ?_⟩
      intro l hl
      apply hn'.2.2 l
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hl,
        dvd_trans (Nat.dvd_of_mem_primeFactors hl) (Nat.div_dvd_of_dvd hd), hn'.2.1.ne'⟩
  have hrec (n : ℕ) (hn : n ∈ G.erase 1) :
      f n = ∑ p ∈ n.primeFactors, (C : ℝ) * (p : ℝ) ^ (-σ) * f (n / p) := by
    have hn' := Finset.mem_erase.mp hn
    have hnpos := (hG hn'.2).2.1
    dsimp [f]
    rw [prime_word_first_letter C n (by omega), Nat.cast_mul, Nat.cast_sum,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have heq : (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hd).symm
    rw [heq, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  let pairs := (G.erase 1).sigma (fun n => n.primeFactors)
  have hpair : (∑ n ∈ G.erase 1, f n) ≤
      ∑ z ∈ T ×ˢ G, (C : ℝ) * (z.1 : ℝ) ^ (-σ) * f z.2 := by
    calc
      _ = ∑ n ∈ G.erase 1, ∑ p ∈ n.primeFactors,
          (C : ℝ) * (p : ℝ) ^ (-σ) * f (n / p) :=
        Finset.sum_congr rfl hrec
      _ ≤ _ := by
        rw [Finset.sum_sigma']
        apply Finset.sum_le_sum_of_injOn (fun x : Sigma (fun _ : ℕ => ℕ) => (x.2, x.1 / x.2))
        · intro x hx y hy heq
          have hxp := (Finset.mem_sigma.mp hx).2
          have hyp := (Finset.mem_sigma.mp hy).2
          have hp : x.2 = y.2 := congrArg Prod.fst heq
          have hq : x.1 / x.2 = y.1 / y.2 := congrArg Prod.snd heq
          have hn : x.1 = y.1 := by
            calc
              x.1 = x.2 * (x.1 / x.2) :=
                (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hxp)).symm
              _ = y.2 * (y.1 / y.2) := by rw [hq, hp]
              _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hyp)
          exact Sigma.ext hn (by simpa using hp)
        · intro z hz
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
          have h := Finset.mem_sigma.mp hx
          exact Finset.mem_product.mpr (hpG (Finset.mem_erase.mp h.1).2 h.2)
        · intro x hx
          rfl
        · intro z hz _
          exact mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hf _)
  have hproduct : (∑ z ∈ T ×ˢ G, (C : ℝ) * (z.1 : ℝ) ^ (-σ) * f z.2) =
      ((C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ)) * R := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have ht : (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
    apply htail T
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    · apply Finset.disjoint_left.mpr
      intro p hp hs
      exact (Finset.mem_filter.mp hp).2.2 hs
  have hsplit : R ≤ 1 + ∑ n ∈ G.erase 1, f n := by
    by_cases h1 : 1 ∈ G
    · have h := Finset.sum_erase_add G f h1
      have hf1 : f 1 = 1 := by simp [f, primeWordWeight, primeWordCount, primeWords, omega]
      dsimp [R]
      rw [← h, hf1]
      linarith
    · simp [R, Finset.erase_eq_of_notMem h1]
  have hR : 0 ≤ R := Finset.sum_nonneg (fun n _ => hf n)
  rw [hproduct] at hpair
  have := mul_le_mul_of_nonneg_right ht hR
  change R ≤ 2
  linarith

theorem prime_word_weight_mono (A B v : ℕ) (hAB : A ≤ B) :
    primeWordWeight A v ≤ primeWordWeight B v := by
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAB (omega v))

/-- The doubled weight controls splitting a product into any two positive
factors, without a multiplicativity assumption. -/
theorem prime_word_product_bound (A m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    primeWordWeight A (m * n) ≤
      primeWordWeight (2 * A) m * primeWordWeight (2 * A) n := by
  classical
  have main : ∀ k m n : ℕ, m + n = k → 0 < m → 0 < n →
      primeWordWeight A (m * n) ≤
        primeWordWeight (2 * A) m * primeWordWeight (2 * A) n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hsum hm hn
      by_cases hm1 : m = 1
      · subst m
        simpa [primeWordWeight, primeWordCount, primeWords, omega] using
          prime_word_weight_mono A (2 * A) n (by omega)
      by_cases hn1 : n = 1
      · subst n
        simpa [primeWordWeight, primeWordCount, primeWords, omega] using
          prime_word_weight_mono A (2 * A) m (by omega)
      have hm2 : 1 < m := by omega
      have hn2 : 1 < n := by omega
      let f : ℕ → ℕ := fun p => primeWordWeight A (m * n / p)
      have hunion : (∑ p ∈ m.primeFactors ∪ n.primeFactors, f p) ≤
          (∑ p ∈ m.primeFactors, f p) + ∑ p ∈ n.primeFactors, f p := by
        have := Finset.sum_union_inter (s₁ := m.primeFactors) (s₂ := n.primeFactors) (f := f)
        omega
      have hleft : (∑ p ∈ m.primeFactors, f p) ≤
          ∑ p ∈ m.primeFactors, primeWordWeight (2 * A) (m / p) * primeWordWeight (2 * A) n := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hquot : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hd) hprime.pos
        have hlt := Nat.div_lt_self hm hprime.one_lt
        dsimp [f]
        rw [show m * n / p = (m / p) * n by
          simpa [mul_comm] using Nat.mul_div_assoc n hd]
        exact ih (m / p + n) (by omega) (m / p) n rfl hquot hn
      have hright : (∑ p ∈ n.primeFactors, f p) ≤
          ∑ p ∈ n.primeFactors, primeWordWeight (2 * A) m * primeWordWeight (2 * A) (n / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hprime.pos
        have hlt := Nat.div_lt_self hn hprime.one_lt
        dsimp [f]
        rw [Nat.mul_div_assoc m hd]
        exact ih (m + n / p) (by omega) m (n / p) rfl hm hquot
      calc
        _ = A * ∑ p ∈ m.primeFactors ∪ n.primeFactors, f p := by
          rw [prime_word_first_letter A (m * n) (by nlinarith), Nat.primeFactors_mul hm.ne' hn.ne']
        _ ≤ A * ((∑ p ∈ m.primeFactors, f p) + ∑ p ∈ n.primeFactors, f p) :=
          Nat.mul_le_mul_left A hunion
        _ ≤ A * ((∑ p ∈ m.primeFactors, primeWordWeight (2 * A) (m / p) *
            primeWordWeight (2 * A) n) + ∑ p ∈ n.primeFactors,
            primeWordWeight (2 * A) m * primeWordWeight (2 * A) (n / p)) :=
          Nat.mul_le_mul_left A (Nat.add_le_add hleft hright)
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          rw [prime_word_first_letter (2 * A) m hm2, prime_word_first_letter (2 * A) n hn2]
          ring
  exact main (m + n) m n rfl hm hn

private theorem prime_tail_set (C : ℕ) (σ : ℝ) (hσ : 1 < σ) :
    ∃ S : Finset ℕ, ∀ T : Finset ℕ, Disjoint T S →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  obtain ⟨S, hS⟩ := hs.vanishing
    (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * ((C : ℝ) + 1))))
  refine ⟨S, ?_⟩
  intro T hT
  have h := hS T hT
  change (∑ p ∈ T, (p : ℝ) ^ (-σ)) < 1 / (2 * ((C : ℝ) + 1)) at h
  have h' := (lt_div_iff₀ (by positivity : 0 < 2 * ((C : ℝ) + 1))).mp h
  have hsum : 0 ≤ ∑ p ∈ T, (p : ℝ) ^ (-σ) := Finset.sum_nonneg (fun p _ => by positivity)
  nlinarith

private theorem smooth_sum_bound (S : Finset ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ K : ℝ, 0 < K ∧ ∀ G : Finset ℕ, (∀ n ∈ G, n ∈ Nat.factoredNumbers S) →
      (∑ n ∈ G, (n : ℝ) ^ (-τ)) ≤ K := by
  classical
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ) ^ (-τ)
    map_one' := by simp
    map_mul' := by intro m n; simp [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hf : ∀ {p : ℕ}, Nat.Prime p → ‖f p‖ < 1 := by
    intro p hp
    dsimp [f]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hf S).1
  let K : ℝ := ∑' n : Nat.factoredNumbers S, ‖f n‖
  have hK : 0 ≤ K := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨K + 1, by linarith, ?_⟩
  intro G hG
  let E : Finset (Nat.factoredNumbers S) := G.attach.image (fun n => ⟨n.val, hG n.val n.property⟩)
  have heq : (∑ n ∈ G, (n : ℝ) ^ (-τ)) = ∑ n ∈ E, ‖f n‖ := by
    rw [Finset.sum_image]
    · change (∑ n ∈ G, (n : ℝ) ^ (-τ)) =
        ∑ n ∈ G.attach, |(n.val : ℝ) ^ (-τ)|
      simp only [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact (Finset.sum_attach G _).symm
    · intro n hn m hm heq
      exact Subtype.ext (congrArg (fun z : Nat.factoredNumbers S => z.val) heq)
  rw [heq]
  exact (hs.sum_le_tsum E (fun _ _ => norm_nonneg _)).trans (by dsimp [K]; linarith)

private theorem prime_support_split (S : Finset ℕ) (v : ℕ) (hv : 0 < v) :
    ∃ m n : ℕ, m * n = v ∧ m ∈ Nat.factoredNumbers S ∧
      0 < n ∧ (∀ p ∈ n.primeFactors, p ∉ S) := by
  classical
  let l := v.primeFactorsList
  let u := l.filter (fun p => decide (p ∈ S))
  let w := l.filter (fun p => !decide (p ∈ S))
  have hmul : u.prod * w.prod = v := by
    rw [← List.prod_append]
    exact (List.filter_append_perm _ l).prod_eq.trans (Nat.prod_primeFactorsList hv.ne')
  have hu : 0 < u.prod := Nat.pos_of_mul_pos_right (hmul.symm ▸ hv)
  have hw : 0 < w.prod := Nat.pos_of_mul_pos_left (hmul.symm ▸ hv)
  have hup : u ∈ primeWords u.prod := (mem_primeWords hu.ne' _).mpr
    ⟨rfl, fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)⟩
  have hwp : w ∈ primeWords w.prod := (mem_primeWords hw.ne' _).mpr
    ⟨rfl, fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)⟩
  have huperm := List.mem_permutations.mp (List.mem_toFinset.mp hup)
  have hwperm := List.mem_permutations.mp (List.mem_toFinset.mp hwp)
  refine ⟨u.prod, w.prod, hmul, ⟨hu.ne', ?_⟩, hw, ?_⟩
  · intro p hp
    have := (List.mem_filter.mp (huperm.mem_iff.mpr hp)).2
    simpa [u] using this
  · intro p hp
    have hp' : p ∈ w.prod.primeFactorsList := Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp
    have := (List.mem_filter.mp (hwperm.mem_iff.mpr hp')).2
    simpa [w] using this

/-- One fixed fractional exponent works for every Dirichlet exponent above one.
The conclusion is a bound over arbitrary finite positive sets. -/
theorem prime_word_finite_moment (A : ℕ) (hA : 1 ≤ A) (r s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r * s = 1 / 2)
    (hpoint : ∀ v : ℕ, 0 < v → (primeWordWeight (2 * A) v : ℝ) ≤ (v : ℝ) ^ r)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ H : ℝ, 0 < H ∧ ∀ F : Finset ℕ, (∀ v ∈ F, 0 < v) →
      (∑ v ∈ F, (primeWordWeight A v : ℝ) ^ s * (v : ℝ) ^ (-σ)) ≤ H := by
  classical
  obtain ⟨S, hS⟩ := prime_tail_set (2 * A) σ hσ
  obtain ⟨K, hK, hKB⟩ := smooth_sum_bound S (σ - 1 / 2) (by linarith)
  refine ⟨2 * K, by positivity, ?_⟩
  intro F hF
  let X := F.sup id
  let U := (Finset.range (X + 1)).filter (fun m => m ∈ Nat.factoredNumbers S)
  let V := roughPrefix S X
  have hU : (∑ m ∈ U, (m : ℝ) ^ (-(σ - 1 / 2))) ≤ K :=
    hKB U (fun m hm => (Finset.mem_filter.mp hm).2)
  have hV : (∑ n ∈ V, (primeWordWeight (2 * A) n : ℝ) * (n : ℝ) ^ (-σ)) ≤ 2 :=
    rough_prime_word_sum (2 * A) σ S (fun T _ hT => hS T hT) X
  have hex : ∀ v : ℕ, ∃ z : ℕ × ℕ, 0 < v → z.1 * z.2 = v ∧
      z.1 ∈ Nat.factoredNumbers S ∧ 0 < z.2 ∧ ∀ p ∈ z.2.primeFactors, p ∉ S := by
    intro v
    by_cases hv : 0 < v
    · obtain ⟨m, n, h⟩ := prime_support_split S v hv
      exact ⟨(m, n), fun _ => h⟩
    · exact ⟨(1, 1), fun h => (hv h).elim⟩
  choose e he using hex
  have hE (v : ℕ) (hv : v ∈ F) : e v ∈ U ×ˢ V := by
    obtain ⟨hmn, hm, hn, hnp⟩ := he v (hF v hv)
    have hmpos : 0 < (e v).1 := Nat.pos_of_ne_zero hm.1
    have hmle : (e v).1 ≤ v := (Nat.le_mul_of_pos_right _ hn).trans_eq hmn
    have hnle : (e v).2 ≤ v := (Nat.le_mul_of_pos_left _ hmpos).trans_eq hmn
    have hvX : v ≤ X := Finset.le_sup (f := id) hv
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn, hnp⟩⟩
  have hterm (v : ℕ) (hv : v ∈ F) :
      (primeWordWeight A v : ℝ) ^ s * (v : ℝ) ^ (-σ) ≤
        ((e v).1 : ℝ) ^ (-(σ - 1 / 2)) *
          ((primeWordWeight (2 * A) (e v).2 : ℝ) * ((e v).2 : ℝ) ^ (-σ)) := by
    obtain ⟨hmn, hm, hn, hnp⟩ := he v (hF v hv)
    have hmpos : 0 < (e v).1 := Nat.pos_of_ne_zero hm.1
    have hm0 : (0 : ℝ) < (e v).1 := by exact_mod_cast hmpos
    have hprod : (primeWordWeight A v : ℝ) ≤
        (primeWordWeight (2 * A) (e v).1 : ℝ) * primeWordWeight (2 * A) (e v).2 := by
      exact_mod_cast (hmn ▸ prime_word_product_bound A (e v).1 (e v).2 hmpos hn)
    have hnW : (1 : ℝ) ≤ primeWordWeight (2 * A) (e v).2 := by
      have hp : 0 < primeWordWeight (2 * A) (e v).2 :=
        Nat.mul_pos (pow_pos (by omega) _) (primeWordCount_pos _)
      exact_mod_cast hp
    have hpower : (primeWordWeight A v : ℝ) ^ s ≤
        ((e v).1 : ℝ) ^ (1 / 2 : ℝ) * (primeWordWeight (2 * A) (e v).2 : ℝ) := by
      calc
        _ ≤ ((primeWordWeight (2 * A) (e v).1 : ℝ) *
            primeWordWeight (2 * A) (e v).2) ^ s :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hprod hs.le
        _ = (primeWordWeight (2 * A) (e v).1 : ℝ) ^ s *
            (primeWordWeight (2 * A) (e v).2 : ℝ) ^ s :=
          Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ ≤ (((e v).1 : ℝ) ^ r) ^ s * (primeWordWeight (2 * A) (e v).2 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (hpoint _ hmpos) hs.le)
            (Real.rpow_le_self_of_one_le hnW hs1) (by positivity) (by positivity)
        _ = _ := by rw [← Real.rpow_mul hm0.le, hrs]
    calc
      _ ≤ (((e v).1 : ℝ) ^ (1 / 2 : ℝ) * primeWordWeight (2 * A) (e v).2) *
          (v : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right hpower (by positivity)
      _ = _ := by
        have hmnR : (v : ℝ) = ((e v).1 : ℝ) * ((e v).2 : ℝ) := by
          exact_mod_cast hmn.symm
        rw [hmnR, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        rw [show -(σ - 1 / 2) = (1 / 2 : ℝ) + (-σ) by ring, Real.rpow_add hm0]
        ring
  have hsum : (∑ v ∈ F, (primeWordWeight A v : ℝ) ^ s * (v : ℝ) ^ (-σ)) ≤
      ∑ z ∈ U ×ˢ V, (z.1 : ℝ) ^ (-(σ - 1 / 2)) *
        ((primeWordWeight (2 * A) z.2 : ℝ) * (z.2 : ℝ) ^ (-σ)) := by
    apply Finset.sum_le_sum_of_injOn e
    · intro v hv w hw heq
      exact ((he v (hF v hv)).1.symm.trans
        ((congrArg (fun z : ℕ × ℕ => z.1 * z.2) heq).trans (he w (hF w hw)).1))
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      exact hE v hv
    · exact hterm
    · intro z hz _
      positivity
  have hrect : (∑ z ∈ U ×ˢ V, (z.1 : ℝ) ^ (-(σ - 1 / 2)) *
        ((primeWordWeight (2 * A) z.2 : ℝ) * (z.2 : ℝ) ^ (-σ))) =
      (∑ m ∈ U, (m : ℝ) ^ (-(σ - 1 / 2))) *
        (∑ n ∈ V, (primeWordWeight (2 * A) n : ℝ) * (n : ℝ) ^ (-σ)) := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  rw [hrect] at hsum
  exact hsum.trans ((mul_le_mul hU hV (by positivity) hK.le).trans_eq (mul_comm K 2))

end D5.S3.Arith.Recurrence.A124056Occurrence
