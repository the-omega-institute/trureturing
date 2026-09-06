/- GID: D5/S3/PrimeGaps/GreedyResidues
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the greedy residue construction and the local-basis collision bounds. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.SieveCoefficients

namespace LongGapsBetweenPrimes

noncomputable section

/-- The elementary passage from a prime-free interval to consecutive primes.
Bertrand's postulate supplies the upper endpoint bound used in Section 2. -/
theorem consecutivePrimes_of_composite_interval {N H : ℕ} (hN : 2 ≤ N)
    (hcomposite : ∀ n : ℕ, N < n → n ≤ N + H → ¬n.Prime) :
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ p ≤ N ∧ N + H < q ∧ q ≤ 2 * N ∧ H < q - p := by
  have hex := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  let q := Nat.find hex
  obtain ⟨hq, hNq, hqN⟩ : q.Prime ∧ N < q ∧ q ≤ 2 * N := Nat.find_spec hex
  let p := Nat.findGreatest Nat.Prime N
  have hp : p.Prime := Nat.findGreatest_spec hN Nat.prime_two
  have hpN : p ≤ N := Nat.findGreatest_le N
  have hNHq : N + H < q := by
    by_contra! h
    exact hcomposite q hNq h hq
  refine ⟨p, q, ⟨hp, hq, hpN.trans_lt hNq, ?_⟩, hpN, hNHq, hqN, by omega⟩
  intro r hpr hrq hr
  by_cases hrN : r ≤ N
  · exact Nat.findGreatest_is_greatest hpr hrN hr
  · exact Nat.find_min hex hrq ⟨hr, by omega, by omega⟩

/-- The initial zero-residue sieve leaves only primes and z-smooth integers. -/
theorem prime_or_smooth_of_survives {n H : ℕ} {x w z : ℝ}
    (hn : 1 ≤ n) (hnH : n ≤ H) (hx : 0 < x) (hsmall : 2 * (H : ℝ) < x * w)
    (hsurvives : ∀ p : ℕ, p.Prime → ((p : ℝ) ≤ w ∨ (z < p ∧ (p : ℝ) ≤ x / 2)) → ¬p ∣ n) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z := by
  by_cases hprime : n.Prime
  · exact Or.inl hprime
  right
  intro p hp hpn
  by_contra! hpz
  have hpbig : x / 2 < (p : ℝ) := by
    by_contra! hpx
    exact hsurvives p hp (Or.inr ⟨hpz, hpx⟩) hpn
  obtain ⟨k, rfl⟩ := hpn
  have hk1 : k ≠ 1 := by
    intro hk
    simp [hk, hp] at hprime
  obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
  have hqn : q ∣ p * k := dvd_mul_of_dvd_right hqk p
  have hqbig : w < (q : ℝ) := by
    by_contra! hqw
    exact hsurvives q hq (Or.inl hqw) hqn
  have hkn : q ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero (by rintro rfl; simp at hn)) hqk
  have hpkH : (p : ℝ) * k ≤ H := by exact_mod_cast hnH
  have hqk' : (q : ℝ) ≤ k := by exact_mod_cast hkn
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  nlinarith [mul_le_mul_of_nonneg_left hqk' hp0,
    mul_lt_mul_of_pos_right hpbig hq0,
    mul_lt_mul_of_pos_left hqbig hx]

/-- Elements of `S` avoiding the selected residue classes. -/
def survivors (S ps : Finset ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  S.filter fun n => ∀ p ∈ ps, n % p ≠ a p

/-- The greedy product bound in (2.1), before applying Mertens' estimate. -/
theorem greedy_residue_classes (S ps : Finset ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤ (S.card : ℝ) * ∏ p ∈ ps, (1 - 1 / (p : ℝ)) := by
  classical
  induction ps using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp, by simp [survivors]⟩
  | @insert p ps hp ih =>
      have hp0 : 0 < p := hpos p (Finset.mem_insert_self p ps)
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
      obtain ⟨a, ha, hcard⟩ := ih (fun q hq => hpos q (Finset.mem_insert_of_mem hq))
      let T := survivors S ps a
      have hsum : (∑ r ∈ Finset.range p,
          ((T.filter fun n => n % p = r).card : ℝ)) = T.card := by
        exact_mod_cast (Finset.card_eq_sum_card_fiberwise
          (f := fun n => n % p) (s := T) (t := Finset.range p)
          (by intro n _; exact Finset.mem_range.mpr (Nat.mod_lt n hp0))).symm
      obtain ⟨r, hr, hlarge⟩ : ∃ r ∈ Finset.range p,
          (T.card : ℝ) / p ≤ ((T.filter fun n => n % p = r).card : ℝ) := by
        apply Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hp0.ne')
        rw [hsum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact le_of_eq (by field_simp)
      have hsplit : ((T.filter fun n => n % p = r).card : ℝ) +
          ((T.filter fun n => n % p ≠ r).card : ℝ) = T.card := by
        exact_mod_cast T.card_filter_add_card_filter_not (fun n => n % p = r)
      have hstep : ((T.filter fun n => n % p ≠ r).card : ℝ) ≤
          (T.card : ℝ) * (1 - 1 / (p : ℝ)) := by
        rw [div_eq_mul_inv] at hlarge
        simp only [one_div]
        nlinarith
      refine ⟨Function.update a p r, ?_, ?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simpa using Finset.mem_range.mp hr
        · simpa [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)] using ha q hq
      · have hsurvivors : survivors S (insert p ps) (Function.update a p r) =
            T.filter (fun n => n % p ≠ r) := by
          have hupdate : ∀ q ∈ ps, Function.update a p r q = a q := by
            intro q hq
            exact Function.update_of_ne (ne_of_mem_of_not_mem hq hp) r a
          ext n
          simp (config := { contextual := true }) only [survivors, Finset.mem_filter,
            Finset.mem_insert, forall_eq_or_imp, Function.update_self, T, hupdate]
          tauto
        rw [hsurvivors, Finset.prod_insert hp]
        calc
          _ ≤ (T.card : ℝ) * (1 - 1 / (p : ℝ)) := hstep
          _ ≤ ((S.card : ℝ) * ∏ q ∈ ps, (1 - 1 / (q : ℝ))) *
              (1 - 1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast hp0
              exact sub_nonneg.mpr ((div_le_one hpR).mpr this))
          _ = _ := by ring

/-- A symmetric matrix is controlled by its absolute row sums. This is the
2|ab| ≤ a²+b² argument invoked in the proof of (3.9). -/
theorem abs_quadratic_form_le_rows {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (hK : ∀ i j, |K i j| = |K j i|) :
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, c i ^ 2 * ∑ j, |K i j| := by
  calc
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, ∑ j, |c i * c j * K i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (c i ^ 2 + c j ^ 2) / 2 * |K i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith [sq_nonneg (|c i| - |c j|), sq_abs (c i), sq_abs (c j)]
    _ = ∑ i, c i ^ 2 * ∑ j, |K i j| := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => c j ^ 2 / 2 * |K i j|)]
      simp_rw [← hK, ← Finset.mul_sum, ← Finset.sum_add_distrib, ← add_mul, add_halves]

/-- Row sums away from the diagonal bound the quadratic error from the identity. -/
lemma quadratic_form_near_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (ε : ℝ)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1)
    (hrow : ∀ i, (∑ j, if j = i then 0 else |K i j|) ≤ ε) :
    |(∑ i, ∑ j, c i * c j * K i j) - ∑ i, c i ^ 2| ≤ ε * ∑ i, c i ^ 2 := by
  let L : ι → ι → ℝ := fun i j => if j = i then 0 else K i j
  have hL (i j : ι) : c i * c j * L i j =
      c i * c j * K i j - if j = i then c i ^ 2 else 0 := by
    by_cases hij : j = i <;> simp [L, hij, hdiag, pow_two]
  calc
    _ = |∑ i, ∑ j, c i * c j * L i j| := by
      simp_rw [hL, Finset.sum_sub_distrib]
      simp
    _ ≤ ∑ i, c i ^ 2 * ∑ j, |L i j| :=
      abs_quadratic_form_le_rows c L (by
        intro i j
        simp only [L, eq_comm, hsym i j])
    _ ≤ ∑ i, c i ^ 2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simpa only [L, apply_ite abs, abs_zero] using hrow i
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The product of selected local basis functions over all coordinates. -/
def productBasis {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (σ : (p : α) → J p) (t : (p : α) → Ω p) : ℝ :=
  ∏ p, f p (σ p) (t p)

/-- The residue factor has mean zero. -/
lemma average_residueFactor {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (residueFactor a) = 0 := by
  simp [Finset.expect, sum_residueFactor hp]

/-- The residue factor has second moment `1 / (p - 1)`. -/
lemma average_residueFactor_sq {p : ℕ} (hp : 1 < p) (a : Fin p) :
    Finset.expect Finset.univ (fun t => residueFactor a t ^ 2) = 1 / ((p : ℝ) - 1) := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_sq hp, div_eq_mul_inv,
    mul_right_comm, hp0]

/-- Distinct residue factors have covariance `-1 / (p - 1)^2`. -/
lemma average_residueFactor_mul {p : ℕ} (hp : 1 < p) (a b : Fin p) (hab : a ≠ b) :
    Finset.expect Finset.univ (fun t => residueFactor a t * residueFactor b t) =
      -1 / ((p : ℝ) - 1) ^ 2 := by
  have hp0 : p ≠ 0 := by omega
  simp [Finset.expect_eq_sum_div_card, sum_residueFactor_mul hp a b hab,
    div_eq_mul_inv, mul_right_comm, hp0]

/-- The constant function and residue factors scaled to have variance one. -/
def localBasis {p k : ℕ} (root : Fin k → Fin p) (i : Option (Fin k)) (t : Fin p) : ℝ :=
  match i with
  | none => 1
  | some j => Real.sqrt ((p : ℝ) - 1) * residueFactor (root j) t

/-- The Gram kernel for the normalized local basis. -/
def localKernel (p : ℕ) {k : ℕ} (i j : Option (Fin k)) : ℝ :=
  match i, j with
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some a, some b => if a = b then 1 else -1 / ((p : ℝ) - 1)

/-- The local Gram matrix, with the nonconstant factors normalized to variance one. -/
theorem average_localBasis_mul {p k : ℕ} (hp : 1 < p) (root : Fin k → Fin p)
    (hroot : Function.Injective root) (i j : Option (Fin k)) :
    Finset.expect Finset.univ (fun t => localBasis root i t * localBasis root j t) =
      localKernel p i j := by
  classical
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp)
  have : NeZero p := ⟨by omega⟩
  cases i with
  | none =>
      cases j <;>
        simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp,
          Finset.expect_const Finset.univ_nonempty]
  | some a =>
      cases j with
      | none =>
          simp [localBasis, localKernel, ← Finset.mul_expect, average_residueFactor hp]
      | some b =>
          simp_rw [localBasis, mul_mul_mul_comm (Real.sqrt _) _ (Real.sqrt _) _]
          rw [← Finset.mul_expect, ← pow_two, Real.sq_sqrt hpR.le]
          by_cases hab : a = b
          · subst b
            simp only [localKernel, ← pow_two, average_residueFactor_sq hp]
            exact mul_one_div_cancel (ne_of_gt hpR)
          · rw [average_residueFactor_mul hp _ _ (hroot.ne hab)]
            simp only [localKernel, if_neg hab]
            field_simp

/-- The absolute row sum of the local Gram kernel. -/
def localRow (p k : ℕ) (i : Option (Fin k)) : ℝ :=
  match i with
  | none => 1
  | some _ => 1 + ((k : ℝ) - 1) / ((p : ℝ) - 1)

/-- The local Gram kernel is symmetric. -/
lemma localKernel_symm (p : ℕ) {k : ℕ} (i j : Option (Fin k)) :
    localKernel p i j = localKernel p j i := by
  cases i <;> cases j <;> simp [localKernel, eq_comm]

/-- The local Gram kernel has diagonal entries equal to one. -/
lemma localKernel_diag (p : ℕ) {k : ℕ} (i : Option (Fin k)) :
    localKernel p i i = 1 := by cases i <;> simp [localKernel]

/-- Summing the absolute local kernel entries gives `localRow`. -/
lemma sum_abs_localKernel {p k : ℕ} (hp : 1 < p) (i : Option (Fin k)) :
    (∑ j, |localKernel p i j|) = localRow p k i := by
  have hpR : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hp.le)
  cases i with
  | none => simp [localKernel, localRow, Fintype.sum_option]
  | some a =>
      simp only [Fintype.sum_option, localKernel, abs_zero, zero_add, apply_ite abs,
        abs_one, abs_div, abs_neg, abs_of_nonneg hpR]
      simpa [localRow, eq_comm, div_eq_mul_inv] using
        sum_one_exception a 1 (1 / ((p : ℝ) - 1))

/-- The product of local Gram kernels over all coordinates. -/
def productKernel {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : ℝ := ∏ p, localKernel (size p) (σ p) (τ p)

/-- The product Gram kernel is symmetric. -/
lemma productKernel_symm {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : productKernel size σ τ = productKernel size τ σ := by
  exact Finset.prod_congr rfl fun p _ => localKernel_symm (size p) (σ p) (τ p)

/-- The product Gram kernel has diagonal entries equal to one. -/
lemma productKernel_diag {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : productKernel size σ σ = 1 := by
  simp [productKernel, localKernel_diag]

/-- The product of local row sums from the proof of (3.9). -/
theorem sum_abs_productKernel {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    (∑ τ, |productKernel size σ τ|) = ∏ p, localRow (size p) k (σ p) := by
  simp only [productKernel, Finset.abs_prod]
  rw [← Fintype.prod_sum (fun p (j : Option (Fin k)) =>
    |localKernel (size p) (σ p) j|)]
  simp_rw [sum_abs_localKernel (hsize _)]

/-- Products of local basis functions have Gram kernel `productKernel`. -/
lemma average_productBasis_localBasis {α : Type*} [Fintype α] [DecidableEq α]
    (size : α → ℕ) (hsize : ∀ p, 1 < size p) {k : ℕ}
    (root : (p : α) → Fin k → Fin (size p)) (hroot : ∀ p, Function.Injective (root p))
    (σ τ : α → Option (Fin k)) :
    Finset.expect Finset.univ (fun t => productBasis (fun p => localBasis (root p)) σ t *
      productBasis (fun p => localBasis (root p)) τ t) = productKernel size σ τ := by
  classical
  simp only [productBasis, ← Finset.prod_mul_distrib]
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_pi,
    Nat.cast_prod, ← Fintype.prod_sum (fun p t =>
      localBasis (root p) (σ p) t * localBasis (root p) (τ p) t),
    ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p _ =>
    (Finset.expect_eq_sum_div_card _ _).symm.trans
      (average_localBasis_mul (hsize p) (root p) (hroot p) (σ p) (τ p))

/-- Coordinates assigned to a nonconstant local basis function. -/
def assignmentSupport {α : Type*} [Fintype α] {k : ℕ}
    (σ : α → Option (Fin k)) : Finset α := Finset.univ.filter fun p => (σ p).isSome

/-- The product of coordinate sizes on an assignment's support. -/
def assignmentProduct {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : ℕ := ∏ p ∈ assignmentSupport σ, size p

/-- The cutoff controls the row sums uniformly, independently of the
number of auxiliary primes in P. -/
theorem assignment_row_bound {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (hk : 1 ≤ k) (σ : α → Option (Fin k))
    {z D : ℝ} (hz : 1 < z) (hsize : ∀ p, z ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((z - 1) * Real.log z)) := by
  classical
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hz1 : 0 < z - 1 := sub_pos.mpr hz
  have hk1 : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hpos (p : α) : 0 < (size p : ℝ) := hz0.trans_le (hsize p)
  have hlog : ((assignmentSupport σ).card : ℝ) * Real.log z ≤ Real.log D := by
    calc
      _ = ∑ p ∈ assignmentSupport σ, Real.log z := by simp
      _ ≤ ∑ p ∈ assignmentSupport σ, Real.log (size p) :=
        Finset.sum_le_sum fun p _ => Real.log_le_log hz0 (hsize p)
      _ = Real.log (assignmentProduct size σ) := by
        rw [assignmentProduct, Nat.cast_prod, Real.log_prod (fun p _ => (hpos p).ne')]
      _ ≤ Real.log D := Real.log_le_log (by
        rw [assignmentProduct, Nat.cast_prod]
        exact Finset.prod_pos fun p _ => hpos p) hcut
  calc
    (∏ p, localRow (size p) k (σ p)) =
        ∏ p ∈ assignmentSupport σ, (1 + ((k : ℝ) - 1) / ((size p : ℝ) - 1)) := by
      simp only [assignmentSupport, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p _
      cases σ p <;> simp [localRow]
    _ ≤ ∏ _ ∈ assignmentSupport σ, Real.exp ((k : ℝ) / (z - 1)) := by
      apply Finset.prod_le_prod
      · intro p _
        exact add_nonneg zero_le_one
          (div_nonneg hk1 (hz1.le.trans (sub_le_sub_right (hsize p) 1)))
      · intro p _
        calc
          _ ≤ 1 + (k : ℝ) / (z - 1) := add_le_add (le_refl 1)
            (div_le_div₀ (Nat.cast_nonneg k) (sub_le_self _ zero_le_one) hz1
              (sub_le_sub_right (hsize p) 1))
          _ ≤ Real.exp ((k : ℝ) / (z - 1)) := by
            simpa [add_comm] using Real.add_one_le_exp ((k : ℝ) / (z - 1))
    _ = Real.exp (((assignmentSupport σ).card : ℝ) * ((k : ℝ) / (z - 1))) := by
      simp [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hcount := (le_div_iff₀ (Real.log_pos hz)).mpr hlog
      have hbound := mul_le_mul_of_nonneg_right hcount
        (div_nonneg (Nat.cast_nonneg k) hz1.le)
      calc
        _ ≤ Real.log D / Real.log z * ((k : ℝ) / (z - 1)) := hbound
        _ = _ := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-- The indicator of the residue class `a` modulo `m`. -/
def residueIndicator (m a n : ℕ) : ℝ := if n % m = a then 1 else 0

/-- The error of counting one congruence class is at most one. -/
theorem residue_count_error_le_one {m a : ℕ} (ha : a < m) (T : ℕ) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m| ≤ 1 := by
  have hlo : ((T / m : ℕ) : ℝ) ≤ (T : ℝ) / m := Nat.cast_div_le
  have hhi : (T : ℝ) / m < ((T / m : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using Nat.lt_floor_add_one ((T : ℝ) / m)
  have hcount := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.count_modEq_card T (by omega : 0 < m) a)
  simp only [Nat.count_eq_card_filter_range, Nat.ModEq, Nat.mod_eq_of_lt ha,
    Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcount
  simp only [residueIndicator, Finset.sum_boole]
  rw [hcount]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- A residue class has frequency error at most `1 / T` on an interval of length `T`. -/
lemma residue_average_error {m a T : ℕ} (ha : a < m) (hT : 0 < T) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ)| ≤
      1 / (T : ℝ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he : (∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ) =
      ((∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m) / T := by
    field_simp [ne_of_gt hTr]
  rw [he, abs_div, abs_of_pos hTr]
  exact div_le_div_of_nonneg_right (residue_count_error_le_one ha T) hTr.le

/-- A weighted union bound, stated without a probability-space interface. -/
theorem weighted_union_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (event : ι → Ω → Prop) [∀ i, DecidablePred (event i)]
    (hw : ∀ t, 0 ≤ w t) :
    (∑ t, w t * if ∃ i, event i t then 1 else 0) ≤
      ∑ i, ∑ t, w t * if event i t then 1 else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t _
  by_cases h : ∃ i, event i t
  · obtain ⟨i, hi⟩ := h
    simpa [show ∃ j, event j t from ⟨i, hi⟩, hi] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun j => w t * if event j t then 1 else 0)
        (fun j _ => by split_ifs <;> simp [hw]) (Finset.mem_univ i))
  · simp [not_exists.mp h]

/-- Independence of two marked coordinates under a product of normalized masses. -/
theorem sum_pair_marked_product {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (w : Ω → ℝ) (hw : ∑ d, w d = 1)
    (mark : Ω → Prop) [DecidablePred mark] (i j : ι) (hij : i ≠ j) :
    (∑ r : ι → Ω, (∏ ℓ, w (r ℓ)) * if mark (r i) ∧ mark (r j) then 1 else 0) =
      (∑ d, w d * if mark d then 1 else 0) ^ 2 := by
  classical
  calc
    _ = ∏ ℓ, ∑ d, w d * if (ℓ = i ∨ ℓ = j) → mark d then 1 else 0 := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.prod_mul_distrib, Finset.prod_boole]
      congr 1
      simp only [Finset.mem_univ, forall_true_left, or_imp, forall_and, forall_eq]
    _ = ∏ ℓ ∈ ({i, j} : Finset ι), ∑ d, w d * if mark d then 1 else 0 := by
      rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset ι))]
      · simp [hij, Finset.prod_pair hij]
      · intro ℓ _ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
        simp [hℓ.1, hℓ.2, hw]
    _ = _ := by simp [Finset.prod_pair hij, pow_two]

/-- The collision estimate for independently chosen divisors: a common mark
in two coordinates costs at most the square of its one-coordinate mass. -/
theorem product_collision_bound {α Ω : Type*} [Fintype α] [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ d, 0 ≤ w d) (hsum : ∑ d, w d = 1)
    (mark : α → Ω → Prop) [∀ p, DecidablePred (mark p)] (k : ℕ) :
    (∑ r : Fin k → Ω, (∏ i, w (r i)) *
      if ∃ p i j, i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0) ≤
        (k : ℝ) ^ 2 * ∑ p, (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
  classical
  have h := weighted_union_bound
    (fun r : Fin k → Ω => ∏ i, w (r i))
    (fun (x : α × Fin k × Fin k) r =>
      x.2.1 ≠ x.2.2 ∧ mark x.1 (r x.2.1) ∧ mark x.1 (r x.2.2))
    (fun r => Finset.prod_nonneg fun i _ => hw (r i))
  calc
    _ ≤ ∑ p, ∑ i : Fin k, ∑ j : Fin k,
        ∑ r : Fin k → Ω, (∏ ℓ, w (r ℓ)) *
          if i ≠ j ∧ mark p (r i) ∧ mark p (r j) then 1 else 0 := by
      simpa only [Prod.exists, Fintype.sum_prod_type] using h
    _ ≤ ∑ p, ∑ _i : Fin k, ∑ _j : Fin k,
        (∑ d, w d * if mark p d then 1 else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [hij, sq_nonneg]
      · simpa only [hij, ne_eq, not_false_eq_true, true_and] using
          (sum_pair_marked_product w hsum (mark p) i j hij).le
    _ = _ := by simp [Finset.mul_sum, pow_two, mul_assoc]

end

end LongGapsBetweenPrimes
