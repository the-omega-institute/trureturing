/- GID: D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/NegativePowerDiagonalModPrime
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Triangular negative-power diagonals prove Hanna's mod-two and mod-three clauses. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
The normalized integer series satisfies, for every n > 1,
`[x^n] A(x / A(x)^((p - 1) * (n - 1) + 1)) = 0`.
The quotient means multiplication by a power of `invOfUnit A 1`; the constant
coefficient is proved to be one. The coefficients are constructed by the
triangular recursion, and the displayed substitution equation is proved.

One general theorem implies one clause of each of two different sequences:
A266489's (C2), `a(n) == 0 (mod 2)` for n >= 2, and A395833's
`a(n) == 0 (mod 3)` for n >= 2. At p = 2 the exponent is n; at p = 3
it is 2*n - 1. No equivalence of the two sequences is asserted.
Sources: `Library/ArithSums/hanna2016a266489.md` and
`Library/ArithSums/hanna2026a395833.md`.

The new coefficientwise construction works over any commutative ring.
Its contraction and the exact substitution-to-recursion identity establish
uniqueness. The residual of 1 + X is a signed binomial coefficient;
Mathlib's `Nat.choose_mul_right` supplies its exact factor p.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (A B : PowerSeries R) : Prop :=
  ∀ k < n, coeff k A = coeff k B

private theorem agree_iff (n : ℕ) (A B : PowerSeries R) :
    Agree n A B ↔ (X : PowerSeries R) ^ n ∣ A - B := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {A B : PowerSeries R}
    (h : Agree n A B) (m : ℕ) : Agree n (A ^ m) (B ^ m) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow A B m))

private theorem inverse_difference (A B : PowerSeries R)
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) :
    invOfUnit A 1 - invOfUnit B 1 =
      (A - B) * (-(invOfUnit A 1 * invOfUnit B 1)) := by
  have hAI := mul_invOfUnit A 1 hA
  have hBI := mul_invOfUnit B 1 hB
  calc
    _ = (B * invOfUnit B 1) * invOfUnit A 1 -
        (A * invOfUnit A 1) * invOfUnit B 1 := by rw [hAI, hBI]; ring
    _ = _ := by ring

private theorem agree_inv {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree n (invOfUnit A 1) (invOfUnit B 1) := by
  apply (agree_iff _ _ _).mpr
  rw [inverse_difference A B hA hB]
  exact dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) _

private noncomputable def tail (p : ℕ) (A : PowerSeries R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, coeff j A *
    coeff (n - j) (invOfUnit A 1 ^ (((p - 1) * (n - 1) + 1) * j))

private noncomputable def step (p : ℕ) (A : PowerSeries R) : PowerSeries R :=
  mk fun n => if n ≤ 1 then 1 else -tail p A n

private theorem step_zero (p : ℕ) (A : PowerSeries R) : constantCoeff (step p A) = 1 := by
  simp [step]

-- Positive outer degrees leave strictly lower degrees in every inverse power.
private theorem step_contract (p : ℕ) {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) : Agree (n + 1) (step p A) (step p B) := by
  intro k hk
  simp only [step, coeff_mk]
  split_ifs with hk1
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp [show k ≠ 0 by omega]
    · rw [h j (by omega), agree_pow (agree_inv hA hB h) _ (k - j) (by omega)]

private noncomputable def approximation (p : ℕ) : ℕ → PowerSeries R
  | 0 => 1
  | d + 1 => step p (approximation p d)

private theorem approximation_zero (p d : ℕ) :
    constantCoeff (approximation (R := R) p d) = 1 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero _ _

private theorem approximation_stable (p : ℕ) {d s : ℕ} (h : d ≤ s) :
    Agree d (approximation (R := R) p d) (approximation p s) := by
  induction d generalizing s with
  | zero => intro k hk; omega
  | succ d ih =>
    cases s with
    | zero => omega
    | succ s =>
      exact step_contract p (approximation_zero p d) (approximation_zero p s) (ih (by omega))

noncomputable def a (p n : ℕ) : ℤ := coeff n (approximation p (n + 1))

noncomputable def generatingSeries (p : ℕ) : PowerSeries ℤ := mk (a p)

private theorem generating_agree (p d : ℕ) :
    Agree d (generatingSeries p) (approximation p d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) p (by omega : n + 1 ≤ d) n (by omega)

private theorem generating_fixed (p : ℕ) : generatingSeries p = step p (generatingSeries p) := by
  have h0 : constantCoeff (generatingSeries p) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree p 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_zero]
  ext n
  exact (generating_agree p (n + 2) n (by omega)).trans
    (step_contract p h0 (approximation_zero p (n + 1))
      (generating_agree p (n + 1)) n (by omega)).symm

-- The outer degree n contributes a_n with multiplier one; all larger degrees vanish.
private theorem coeff_diagonal (A : PowerSeries R) (e n : ℕ) :
    coeff n (A.subst (X * invOfUnit A 1 ^ e)) =
      coeff n A + ∑ j ∈ Finset.range n,
        coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) := by
  have hz : constantCoeff (X * invOfUnit A 1 ^ e) = 0 := by simp
  rw [coeff_subst' (.of_constantCoeff_zero hz)]
  have ht (j : ℕ) :
      coeff j A • coeff n ((X * invOfUnit A 1 ^ e) ^ j) =
        if j ≤ n then coeff j A * coeff (n - j) (invOfUnit A 1 ^ (e * j)) else 0 := by
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
    split_ifs <;> simp [smul_eq_mul]
  simp_rw [ht]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · rw [Finset.sum_range_succ]
    have he : coeff n A * coeff (n - n) (invOfUnit A 1 ^ (e * n)) = coeff n A := by
      simp
    simp only [le_refl, if_true, he]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    have hjn : j ≤ n := by
      by_contra h
      simp [h] at hj
    exact Finset.mem_range.mpr (by omega)


private theorem equation_iff (p : ℕ) (A : PowerSeries R) :
    (coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ ∀ n : ℕ, 1 < n →
      coeff n (A.subst (X * invOfUnit A 1 ^ ((p - 1) * (n - 1) + 1))) = 0) ↔
      A = step p A := by
  constructor
  · rintro ⟨h0, h1, he⟩
    ext n
    simp only [step, coeff_mk]
    split_ifs with hn
    · have h : n = 0 ∨ n = 1 := by omega
      rcases h with rfl | rfl <;> assumption
    · have h := he n (by omega)
      rw [coeff_diagonal] at h
      exact eq_neg_of_add_eq_zero_left h
  · intro hf
    have hc (n : ℕ) := congrArg (coeff n) hf
    refine ⟨?_, ?_, ?_⟩
    · simpa [step] using hc 0
    · simpa [step] using hc 1
    · intro n hn
      rw [coeff_diagonal]
      have h := hc n
      simp only [step, coeff_mk, if_neg (by omega : ¬ n ≤ 1)] at h
      change coeff n A + tail p A n = 0
      rw [h, neg_add_cancel]

theorem generating_equation (p : ℕ) : coeff 0 (generatingSeries p) = 1 ∧
    coeff 1 (generatingSeries p) = 1 ∧ ∀ n : ℕ, 1 < n →
      coeff n ((generatingSeries p).subst
        (X * invOfUnit (generatingSeries p) 1 ^ ((p - 1) * (n - 1) + 1))) = 0 :=
  (equation_iff p _).mpr (generating_fixed p)

private theorem fixed_unique (p : ℕ) {A B : PowerSeries R}
    (hA : A = step p A) (hB : B = step p B) : A = B := by
  have hA0 : constantCoeff A = 1 := by rw [hA, step_zero]
  have hB0 : constantCoeff B = 1 := by rw [hB, step_zero]
  have ha : ∀ n, Agree n A B := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih => simpa only [← hA, ← hB] using step_contract p hA0 hB0 ih
  ext n
  exact ha (n + 1) n (by omega)

theorem generating_unique (p : ℕ) (B : PowerSeries ℤ) (h0 : coeff 0 B = 1)
    (h1 : coeff 1 B = 1)
    (he : ∀ n : ℕ, 1 < n →
      coeff n (B.subst (X * invOfUnit B 1 ^ ((p - 1) * (n - 1) + 1))) = 0) :
    B = generatingSeries p :=
  fixed_unique p ((equation_iff p B).mp ⟨h0, h1, he⟩) (generating_fixed p)

private theorem map_inverse {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) :
    (invOfUnit A 1).map hom = invOfUnit (A.map hom) 1 := by
  have hz : constantCoeff (A.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hA, map_one]
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_left_cancel
  rw [mul_invOfUnit _ 1 hz, ← map_mul, mul_invOfUnit _ 1 hA, map_one]

private theorem map_step {S : Type*} [CommRing S] (hom : R →+* S)
    (p : ℕ) (A : PowerSeries R) (hA : constantCoeff A = 1) :
    (step p A).map hom = step p (A.map hom) := by
  ext n
  simp only [coeff_map, step, coeff_mk]
  split_ifs
  · exact map_one hom
  · simp only [map_neg, tail, map_sum, map_mul, coeff_map]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have he : (invOfUnit A 1 ^ (((p - 1) * (n - 1) + 1) * j)).map hom =
        invOfUnit (A.map hom) 1 ^ (((p - 1) * (n - 1) + 1) * j) := by
      rw [map_pow, map_inverse hom A hA]
    exact congrArg (coeff (n - j)) he

private theorem inverse_linear :
    invOfUnit (1 + X : PowerSeries R) 1 = rescale (-1) (mk 1) := by
  have hz : constantCoeff (1 + X : PowerSeries R) = 1 := by simp
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_right_cancel
  rw [invOfUnit_mul _ 1 hz]
  have he := congrArg (rescale (-1 : R)) (mk_one_mul_one_sub_eq_one R)
  simpa using he.symm

-- Rescaling the geometric series computes the residual before reduction modulo p.
private theorem linear_residual (p r : ℕ) (hp : 1 ≤ p) (hr : 0 < r) :
    coeff (r + 1) ((1 + X : PowerSeries R).subst
      (X * invOfUnit (1 + X) 1 ^ ((p - 1) * r + 1))) =
      (-1 : R) ^ r * ((p * r).choose r : R) := by
  have hz : HasSubst (X * invOfUnit (1 + X : PowerSeries R) 1 ^ ((p - 1) * r + 1)) :=
    .of_constantCoeff_zero (show constantCoeff
      (X * invOfUnit (1 + X : PowerSeries R) 1 ^ ((p - 1) * r + 1)) = 0 by simp)
  have hone : (1 : PowerSeries R).subst
      (X * invOfUnit (1 + X : PowerSeries R) 1 ^ ((p - 1) * r + 1)) = 1 := by
    rw [← coe_substAlgHom hz, map_one]
  rw [subst_add hz, hone, subst_X hz, map_add, coeff_one,
    if_neg (by omega : r + 1 ≠ 0), zero_add, coeff_succ_X_mul,
    inverse_linear, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk]
  congr 2
  have hi : (p - 1) * r + r = p * r := by
    have := Nat.sub_add_cancel hp
    nlinarith
  rw [hi, ← Nat.choose_symm (show r ≤ p * r by nlinarith)]
  congr 1
  omega

private theorem linear_fixed (p : ℕ) (hp : 1 ≤ p) :
    (1 + X : PowerSeries (ZMod p)) = step p (1 + X) := by
  apply (equation_iff p _).mp
  refine ⟨by simp, by simp, ?_⟩
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change coeff (r + 1) ((1 + X : PowerSeries (ZMod p)).subst
    (X * invOfUnit (1 + X) 1 ^ ((p - 1) * r + 1))) = 0
  rw [linear_residual p r hp (by omega), Nat.choose_mul_right (by omega : r ≠ 0)]
  simp

private theorem mod_identity (p : ℕ) (hp : 1 ≤ p) :
    (generatingSeries p).map (Int.castRingHom (ZMod p)) = 1 + X := by
  apply fixed_unique p
  · rw [← map_step]
    · exact congrArg (PowerSeries.map (Int.castRingHom (ZMod p))) (generating_fixed p)
    · simpa only [coeff_zero_eq_constantCoeff] using (generating_equation p).1
  · exact linear_fixed p hp

theorem diagonal_conjecture_general (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 2 ≤ n) :
    (p : ℤ) ∣ a p n := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have he := congrArg (coeff n) (mod_identity p (by have := hp.two_le; omega))
  simpa [generatingSeries, coeff_map, coeff_X, show n ≠ 0 by omega, show n ≠ 1 by omega] using he

theorem hanna_conjecture_a266489 (n : ℕ) (hn : 2 ≤ n) : (2 : ℤ) ∣ a 2 n :=
  diagonal_conjecture_general 2 Nat.prime_two n hn

theorem hanna_conjecture_a395833 (n : ℕ) (hn : 2 ≤ n) : (3 : ℤ) ∣ a 3 n :=
  diagonal_conjecture_general 3 Nat.prime_three n hn

#print axioms a
#print axioms generatingSeries
#print axioms generating_equation
#print axioms generating_unique
#print axioms diagonal_conjecture_general
#print axioms hanna_conjecture_a266489
#print axioms hanna_conjecture_a395833

end D5.S1.Recurrence.Residue.NegativePowerDiagonalModPrime
