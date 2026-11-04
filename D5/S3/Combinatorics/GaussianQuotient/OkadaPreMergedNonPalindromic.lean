/- GID: D5/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GaussianQuotient/OkadaPreMergedNonPalindromic
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-three pre-merged Gaussian determinants are not almost palindromic. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import Mathlib.Algebra.Order.Monovary
import Mathlib.Data.List.Palindrome

/-! Okada's width-three pre-merged determinant conjecture. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic

open Polynomial
open scoped BigOperators
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs (gauss)

private noncomputable def qFactorial (n : ℕ) : ℤ[X] :=
  ∏ h ∈ Finset.range n, (1 - X ^ (h + 1))

private theorem qFactorial_succ (n : ℕ) :
    qFactorial (n + 1) = qFactorial n * (1 - X ^ (n + 1)) := by
  simp [qFactorial, Finset.prod_range_succ, mul_comm]

private theorem gauss_diagonal (n : ℕ) : gauss n n = 1 := by
  simpa only [Nat.sub_self, gauss] using
    D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_symmetry n n le_rfl

private theorem gauss_coeff_zero (n k : ℕ) (hkn : k ≤ n) :
    (gauss n k).coeff 0 = 1 := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst k
      simp [gauss]
  | succ n ih =>
      cases k with
      | zero => simp [gauss]
      | succ k =>
          by_cases hk : k = n
          · subst k
            rw [gauss, D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt n (n + 1)
              (by omega), gauss_diagonal]
            simp
          · have hkn' : k + 1 ≤ n := by omega
            have hnk : 0 < n - k := by omega
            rw [gauss]
            rw [coeff_add, ih (k + 1) hkn']
            rw [coeff_X_pow_mul']
            simp [hnk.ne']

private theorem gauss_coeff_one (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (gauss n k).coeff 1 = 1 := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          have hkn' : k + 1 ≤ n := by omega
          rw [gauss, coeff_add]
          by_cases hdiag : k + 1 = n
          · subst n
            rw [gauss_diagonal, coeff_one, coeff_X_pow_mul']
            simp [gauss_coeff_zero]
          · have hlt : k + 1 < n := by omega
            rw [ih (k + 1) (by omega) hlt, coeff_X_pow_mul']
            have hpow : 1 < n - k := by omega
            have hnot : ¬ n ≤ 1 + k := by omega
            simp [hnot]

def IsAlmostPalindromic (f : ℤ[X]) : Prop :=
  ((f.support.sort (· ≤ ·)).map f.coeff).Palindrome

noncomputable def preMerged {μ : ℕ} (a b : Fin μ → ℕ) : ℤ[X] :=
  (∏ i, gauss (b i) (a i)) - ∏ i, gauss (b i) (a (Fin.rev i))

def claim : Prop :=
  ∀ (μ : ℕ) (a b : Fin μ → ℕ),
    3 ≤ μ → StrictMono a → StrictMono b → (∀ i j, a i ≤ b j) →
      ¬ IsAlmostPalindromic (preMerged a b)

private theorem factorial_identity
    (n k : ℕ) (hkn : k ≤ n) :
    gauss n k * qFactorial k * qFactorial (n - k) = qFactorial n := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst hk
      simp [qFactorial, gauss]
  | succ n ih =>
      by_cases hk : k = 0
      · subst k
        simp [qFactorial, gauss]
      by_cases hkn' : k = n + 1
      · subst k
        rw [qFactorial_succ]
        rw [gauss,
          D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_zero_of_lt n (n + 1) (by omega),
          gauss_diagonal]
        simp [qFactorial]
      have hkn'' : k ≤ n := by omega
      have hkpos : 0 < k := by omega
      have hsub : n + 1 - k = n - k + 1 := Nat.succ_sub hkn''
      have hhook :
          (1 - X ^ (n + 1 - k)) * gauss (n + 1) k =
            (1 - X ^ (n + 1)) * gauss n k := by
        simpa using
          D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_hook (n + 1) k (by omega)
      rw [hsub, qFactorial_succ (n - k)]
      calc
        gauss (n + 1) k * qFactorial k *
            (qFactorial (n - k) * (1 - X ^ (n - k + 1))) =
            qFactorial k * qFactorial (n - k) *
              ((1 - X ^ (n + 1 - k)) * gauss (n + 1) k) := by
          rw [hsub, pow_succ]
          ring
        _ = qFactorial k * qFactorial (n - k) *
              ((1 - X ^ (n + 1)) * gauss n k) := by rw [hhook]
        _ = qFactorial (n + 1) := by
          calc
            qFactorial k * qFactorial (n - k) *
                ((1 - X ^ (n + 1)) * gauss n k) =
                gauss n k * qFactorial k * qFactorial (n - k) *
                  (1 - X ^ (n + 1)) := by ring
            _ = qFactorial n * (1 - X ^ (n + 1)) := by rw [ih k hkn'']
            _ = qFactorial (n + 1) := (qFactorial_succ n).symm

private theorem index_bounds
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
    (∀ i, t + 2 ≤ b i - a i) ∧
      b ⟨0, by omega⟩ - a (⟨μ - 1, by omega⟩) = t ∧
      (∀ i : Fin μ, 0 < i.val → t + 2 ≤ b i - a (Fin.rev i)) := by
  dsimp only
  let z : Fin μ := ⟨0, by omega⟩
  let u : Fin μ := ⟨1, by omega⟩
  let v : Fin μ := ⟨μ - 1, by omega⟩
  have hazu := ha (show z < u by change 0 < 1; omega)
  have hauv := ha (show u < v by change 1 < μ - 1; omega)
  have hbzu := hb (show z < u by change 0 < 1; omega)
  have hbuv := hb (show u < v by change 1 < μ - 1; omega)
  have hbase := hcross v z
  change (∀ i, b z - a v + 2 ≤ b i - a i) ∧ _ ∧ _
  refine ⟨?_, rfl, ?_⟩
  · intro i
    by_cases hiz : i = z
    · subst i
      omega
    by_cases hiv : i = v
    · subst i
      omega
    have hbi := hb (show z < i by
      change 0 < i.val
      have : i.val ≠ 0 := fun h => hiz (Fin.ext h)
      omega)
    have hai := ha (show i < v by
      change i.val < μ - 1
      have : i.val ≠ μ - 1 := fun h => hiv (Fin.ext h)
      omega)
    omega
  · intro i hi
    have hbi := hb (show z < i from hi)
    have hai := ha (show Fin.rev i < v by
      change (Fin.rev i).val < μ - 1
      simp only [Fin.val_rev]
      omega)
    change b z - a v + 2 ≤ b i - a (Fin.rev i)
    omega

private theorem qFactorial_coeff_zero (n : ℕ) : (qFactorial n).coeff 0 = 1 := by
  simp [qFactorial, coeff_zero_prod]

private theorem factorial_product_identity
    (μ : ℕ) (a b : Fin μ → ℕ) (hab : ∀ i j, a i ≤ b j) :
    (∏ i, gauss (b i) (a i)) * (∏ i, qFactorial (b i - a i)) =
      (∏ i, gauss (b i) (a (Fin.rev i))) *
        (∏ i, qFactorial (b i - a (Fin.rev i))) := by
  have hleft := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => factorial_identity (b i) (a i) (hab i i))
  have hright := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => factorial_identity (b i) (a (Fin.rev i)) (hab (Fin.rev i) i))
  simp only [Finset.prod_mul_distrib] at hleft hright
  have hrev : (∏ i, qFactorial (a (Fin.rev i))) = ∏ i, qFactorial (a i) :=
    Equiv.prod_comp Fin.revPerm (fun i => qFactorial (a i))
  rw [hrev] at hright
  have hne : (∏ i, qFactorial (a i)) ≠ 0 := by
    intro h
    have hz := congrArg (fun f : ℤ[X] => f.coeff 0) h
    simp [coeff_zero_prod, qFactorial_coeff_zero] at hz
  apply mul_right_cancel₀ hne
  calc
    _ = (∏ i, gauss (b i) (a i)) * (∏ i, qFactorial (a i)) *
        (∏ i, qFactorial (b i - a i)) := by ring
    _ = (∏ i, gauss (b i) (a (Fin.rev i))) * (∏ i, qFactorial (a i)) *
        (∏ i, qFactorial (b i - a (Fin.rev i))) := hleft.trans hright.symm
    _ = _ := by ring

private theorem qFactorial_image_stable
    {s : Type*} [CommRing s] (φ : ℤ[X] →+* s) (n m : ℕ)
    (hx : φ (X ^ (m + 1)) = 0) (hmn : m ≤ n) :
    φ (qFactorial n) = φ (qFactorial m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hz : φ (X ^ (n + 1)) = 0 := by
        simpa only [map_pow] using
          pow_eq_zero_of_le (Nat.add_le_add_right hn 1)
            (show φ X ^ (m + 1) = 0 by simpa only [map_pow] using hx)
      rw [qFactorial_succ, map_mul, ih, map_sub, map_one, hz, sub_zero, mul_one]

private theorem qFactorial_image_unit
    {s : Type*} [CommRing s] (φ : ℤ[X] →+* s) (hx : IsNilpotent (φ X)) (n : ℕ) :
    IsUnit (φ (qFactorial n)) := by
  rw [qFactorial, map_prod]
  exact IsUnit.prod_iff.mpr fun i _ => by
    simpa only [map_sub, map_one, map_pow] using (hx.pow_succ i).isUnit_one_sub

private theorem product_coeff_one
    {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (hf : ∀ i ∈ s, (f i).coeff 0 = 1) :
    (∏ i ∈ s, f i).coeff 1 = ∑ i ∈ s, (f i).coeff 1 := by
  classical
  have hz (i : ι) : (∏ j ∈ s.erase i, f j).coeff 0 = 1 := by
    rw [coeff_zero_prod]
    exact Finset.prod_eq_one fun j hj => hf j (Finset.mem_of_mem_erase hj)
  simpa only [coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one,
    finsetSum_coeff, mul_coeff_zero, hz, one_mul] using
    congrArg (fun p : ℤ[X] => p.coeff 0) (derivative_prod_finset (s := s) (f := f))

private theorem gaussian_product_low
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 0 < μ) (ha : StrictMono a)
    (hab : ∀ i, a i < b i) :
    let c := if 0 < a ⟨0, hμ⟩ then μ else μ - 1
    (∏ i, gauss (b i) (a i)).coeff 0 = 1 ∧
      (∏ i, gauss (b i) (a i)).coeff 1 = c := by
  dsimp only
  have hz : ∀ i, (gauss (b i) (a i)).coeff 0 = 1 :=
    fun i => gauss_coeff_zero _ _ (hab i).le
  refine ⟨by simp [coeff_zero_prod, hz], ?_⟩
  rw [product_coeff_one _ _ (fun i _ => hz i)]
  let z : Fin μ := ⟨0, hμ⟩
  by_cases ha0 : 0 < a z
  · rw [ite_eq_left ha0]
    have hc (i : Fin μ) : (gauss (b i) (a i)).coeff 1 = 1 := by
      apply gauss_coeff_one _ _ _ (hab i)
      exact lt_of_lt_of_le ha0 (ha.monotone (show z ≤ i from Nat.zero_le _))
    simp [hc]
  · rw [ite_eq_right ha0]
    have hc (i : Fin μ) : (gauss (b i) (a i)).coeff 1 =
        (1 : ℤ) - if i = z then 1 else 0 := by
      by_cases hi : i = z
      · subst i
        have haz : a z = 0 := by omega
        simp [haz, gauss, coeff_one]
      · have hipos : 0 < i.val := by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega
        have hai := ha (show z < i from hipos)
        rw [gauss_coeff_one _ _ (by omega) (hab i), ite_eq_right hi, sub_zero]
    simp only [hc, Finset.sum_sub_distrib]
    simp [Nat.cast_sub hμ]

private theorem low_end
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let p := preMerged a b
    let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
    let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
    p.coeff (t + 1) = 1 ∧ p.coeff (t + 2) = c + 1 ∧
      (∀ n, n < t + 1 → p.coeff n = 0) := by
  classical
  let z : Fin μ := ⟨0, by omega⟩
  let v : Fin μ := ⟨μ - 1, by omega⟩
  let t := b z - a v
  let a0 := ∏ i, gauss (b i) (a i)
  let b0 := ∏ i, gauss (b i) (a (Fin.rev i))
  let i0 : Ideal ℤ[X] := Ideal.span {X ^ (t + 3)}
  let φ := Ideal.Quotient.mk i0
  have hx : φ (X ^ (t + 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
  have hnil : IsNilpotent (φ X) := ⟨t + 3, by rw [← map_pow, hx]⟩
  have hstable (n : ℕ) (hn : t + 2 ≤ n) :
      φ (qFactorial n) = φ (qFactorial (t + 2)) :=
    qFactorial_image_stable φ n (t + 2) hx hn
  have hi := index_bounds μ a b hμ ha hb hcross
  have hd : φ (∏ i, qFactorial (b i - a i)) = φ (qFactorial (t + 2)) ^ μ := by
    rw [map_prod]
    simp_rw [hstable _ (hi.1 _)]
    simp
  have he : φ (∏ i, qFactorial (b i - a (Fin.rev i))) =
      φ (qFactorial t) * φ (qFactorial (t + 2)) ^ (μ - 1) := by
    rw [map_prod, ← Finset.mul_prod_erase Finset.univ
      (fun i => φ (qFactorial (b i - a (Fin.rev i)))) (by simp : z ∈ Finset.univ)]
    have hzrev : Fin.rev z = v := Fin.ext (Fin.val_rev z)
    rw [hzrev]
    change φ (qFactorial t) * _ = _
    congr 1
    calc
      _ = ∏ _i ∈ Finset.univ.erase z, φ (qFactorial (t + 2)) := by
        apply Finset.prod_congr rfl
        intro i hi0
        have hiz : i ≠ z := (Finset.mem_erase.1 hi0).1
        have hipos : 0 < i.val := by
          have : i.val ≠ 0 := fun h => hiz (Fin.ext h)
          omega
        exact hstable _ (hi.2.2 i hipos)
      _ = _ := by simp
  have hf := congrArg φ (factorial_product_identity μ a b hcross)
  simp only [map_mul] at hf
  rw [hd, he] at hf
  let f : ℤ[X] := (1 - X ^ (t + 1)) * (1 - X ^ (t + 2))
  have hq : φ (qFactorial (t + 2)) = φ (qFactorial t) * φ f := by
    rw [qFactorial_succ (t + 1), qFactorial_succ t]
    simp only [map_mul]
    dsimp [f]
    simp only [map_mul]
    ring
  let u := φ (qFactorial t) * φ (qFactorial (t + 2)) ^ (μ - 1)
  have hu : IsUnit u := (qFactorial_image_unit φ hnil t).mul
    ((qFactorial_image_unit φ hnil (t + 2)).pow (μ - 1))
  have heq : φ (a0 * f) = φ b0 := by
    apply hu.mul_right_cancel
    have hpow : φ (qFactorial (t + 2)) ^ μ =
        φ (qFactorial (t + 2)) ^ (μ - 1) * φ (qFactorial (t + 2)) := by
      exact (pow_sub_one_mul (by omega : μ ≠ 0) _).symm
    rw [hpow, hq] at hf
    dsimp [a0, b0, u]
    rw [map_mul, hq]
    convert hf using 1; ring
  have hdiv : (X : ℤ[X]) ^ (t + 3) ∣ a0 * f - b0 :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 heq)
  have hcoeff (n : ℕ) (hn : n < t + 3) :
      (preMerged a b).coeff n =
        (a0 * X ^ (t + 1) + a0 * X ^ (t + 2) - a0 * X ^ ((t + 1) + (t + 2))).coeff n := by
    have hc0 := X_pow_dvd_iff.1 hdiv n hn
    rw [coeff_sub] at hc0
    have hb0 : b0.coeff n = (a0 * f).coeff n := by omega
    change (a0 - b0).coeff n = _
    rw [coeff_sub, hb0, ← coeff_sub]
    congr 1
    dsimp [f]
    simp only [pow_add]
    ring
  have halow := gaussian_product_low μ a b (by omega) ha (fun i => by
    have := hi.1 i
    have := hcross i i
    omega)
  change (preMerged a b).coeff (t + 1) = 1 ∧
    (preMerged a b).coeff (t + 2) = _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoeff _ (by omega)]
    simp [coeff_sub, coeff_add, coeff_mul_X_pow', halow.1, a0]
  · rw [hcoeff _ (by omega)]
    simp only [coeff_sub, coeff_add, coeff_mul_X_pow']
    simp [show t + 2 - (t + 1) = 1 by omega, show ¬ (t + 1) + (t + 2) ≤ t + 2 by omega,
      halow.1, halow.2, a0]
  · intro n hn
    change n < t + 1 at hn
    rw [hcoeff n (by omega)]
    simp only [coeff_sub, coeff_add, coeff_mul_X_pow']
    simp [show ¬ t + 1 ≤ n by omega, show ¬ t + 2 ≤ n by omega,
      show ¬ (t + 1) + (t + 2) ≤ n by omega]

private theorem gaussian_shape (n k : ℕ) (hk : k ≤ n) :
    (gauss n k).Monic ∧ (gauss n k).natDegree = k * (n - k) ∧
      (gauss n k).reverse = gauss n k := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [gauss, reverse]
  | succ n ih =>
      cases k with
      | zero => simp [gauss, reverse]
      | succ k =>
          by_cases he : k = n
          · subst k
            simp [gauss_diagonal, reverse]
          have hk1 : k + 1 ≤ n := by omega
          obtain ⟨hm1, hd1, hr1⟩ := ih (k + 1) hk1
          obtain ⟨hm2, hd2, hr2⟩ := ih k (by omega)
          have hsub : n + 1 - (k + 1) = n - k := Nat.add_sub_add_right n 1 k
          have he1 : (k + 1) * (n - k) = k + 1 + (k + 1) * (n - (k + 1)) := by
            have : n - k = (n - (k + 1)) + 1 := by
              simpa only [Nat.sub_sub] using
                (Nat.sub_add_cancel (by omega : 1 ≤ n - k)).symm
            rw [this]
            ring
          have he2 : (k + 1) * (n - k) = (n - k) + k * (n - k) := by ring
          have hmon : (X ^ (n - k) * gauss n k).Monic := (monic_X_pow _).mul hm2
          have hdeg : (X ^ (n - k) * gauss n k).natDegree = (k + 1) * (n - k) := by
            rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hm2.ne_zero,
              natDegree_X_pow, hd2, he2]
          have hlt : (gauss n (k + 1)).natDegree <
              (X ^ (n - k) * gauss n k).natDegree := by
            rw [hd1, hdeg, he1]
            omega
          have hrec : gauss (n + 1) (k + 1) =
              gauss n (k + 1) + X ^ (n - k) * gauss n k := by rw [gauss]
          have hd : (gauss (n + 1) (k + 1)).natDegree = (k + 1) * (n - k) := by
            rw [hrec, natDegree_add_eq_right_of_natDegree_lt hlt, hdeg]
          refine ⟨hrec ▸ hmon.add_of_right (degree_lt_degree hlt), by simpa [hsub] using hd, ?_⟩
          change (gauss (n + 1) (k + 1)).reflect
            (gauss (n + 1) (k + 1)).natDegree = _
          rw [hd, hrec, reflect_add]
          have hreflect1 : (gauss n (k + 1)).reflect ((k + 1) * (n - k)) =
              X ^ (k + 1) * gauss n (k + 1) := by
            rw [he1, ← one_mul (gauss n (k + 1)), reflect_mul _ _ (by simp) hd1.le]
            rw [reflect_one, ← hd1, ← reverse, hr1]
            simp
          have hreflect2 : (X ^ (n - k) * gauss n k).reflect ((k + 1) * (n - k)) =
              gauss n k := by
            rw [he2, reflect_mul _ _ (by simp) hd2.le, reflect_monomial,
              revAt_le (le_refl _), Nat.sub_self, pow_zero, one_mul, ← hd2, ← reverse, hr2]
          rw [hreflect1, hreflect2]
          exact (D5.S3.Combinatorics.CylindricPartition.LiUncu.gauss_pascal_dual n k).symm

private theorem gaussian_product_shape
    (μ : ℕ) (a b : Fin μ → ℕ) (hab : ∀ i, a i ≤ b i) :
    (∏ i, gauss (b i) (a i)).Monic ∧
      (∏ i, gauss (b i) (a i)).natDegree = ∑ i, a i * (b i - a i) ∧
      (∏ i, gauss (b i) (a i)).reverse = ∏ i, gauss (b i) (a i) := by
  have hshape (i : Fin μ) := gaussian_shape (b i) (a i) (hab i)
  have hprod (s : Finset (Fin μ)) :
      (∏ i ∈ s, gauss (b i) (a i)).reverse = ∏ i ∈ s, gauss (b i) (a i) := by
    exact Finset.prod_induction (fun i => gauss (b i) (a i))
      (fun p => p.reverse = p)
      (fun p q hp hq => by rw [reverse_mul_of_domain, hp, hq])
      (by simp [reverse]) (fun i _ => (hshape i).2.2)
  refine ⟨monic_prod_of_monic _ _ (fun i _ => (hshape i).1), ?_, hprod Finset.univ⟩
  rw [natDegree_prod_of_monic _ _ (fun i _ => (hshape i).1)]
  exact Finset.sum_congr rfl (fun i _ => (hshape i).2.1)

private theorem reversed_degree_gap
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    (∑ i, a (Fin.rev i) * (b i - a (Fin.rev i))) + 2 ≤
      ∑ i, a i * (b i - a i) := by
  let d := ∑ i, a i * (b i - a i)
  let e := ∑ i, a (Fin.rev i) * (b i - a (Fin.rev i))
  let u := ∑ i, (a i : ℤ) * (b i : ℤ)
  let v := ∑ i, (a (Fin.rev i) : ℤ) * (b i : ℤ)
  have hd : (d : ℤ) = u - ∑ i, (a i : ℤ) * (a i : ℤ) := by
    dsimp [d, u]
    rw [← Finset.sum_sub_distrib]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (hcross i i)]
    ring
  have he : (e : ℤ) = v - ∑ i, (a i : ℤ) * (a i : ℤ) := by
    have hperm : (∑ i, (a (Fin.rev i) : ℤ) * (a (Fin.rev i) : ℤ)) =
        ∑ i, (a i : ℤ) * (a i : ℤ) :=
      Equiv.sum_comp Fin.revPerm (fun i => (a i : ℤ) * (a i : ℤ))
    rw [← hperm]
    dsimp [e, v]
    rw [← Finset.sum_sub_distrib]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (hcross (Fin.rev i) i)]
    ring
  let f := fun i : Fin μ => ((a i : ℤ) - (a (Fin.rev i) : ℤ)) *
    ((b i : ℤ) - (b (Fin.rev i) : ℤ))
  have hnonneg (i : Fin μ) : 0 ≤ f i := by
    dsimp [f]
    have hma : Monotone (fun i => (a i : ℤ)) :=
      fun i j h => Int.ofNat_le.mpr (ha.monotone h)
    have hmb : Monotone (fun i => (b i : ℤ)) :=
      fun i j h => Int.ofNat_le.mpr (hb.monotone h)
    exact (hma.monovary hmb).sub_mul_sub_nonneg (Fin.rev i) i
  have hsum : ∑ i, f i = 2 * (u - v) := by
    have hperm : (∑ i, (a (Fin.rev i) : ℤ) * (b (Fin.rev i) : ℤ)) = u :=
      Equiv.sum_comp Fin.revPerm (fun i => (a i : ℤ) * (b i : ℤ))
    have hswap : (∑ i, (a i : ℤ) * (b (Fin.rev i) : ℤ)) = v := by
      symm
      simpa [v] using Equiv.sum_comp Fin.revPerm
        (fun i => (a i : ℤ) * (b (Fin.rev i) : ℤ))
    dsimp [f]
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, hswap, hperm]
    dsimp [u, v]
    ring
  let z : Fin μ := ⟨0, by omega⟩
  let j : Fin μ := ⟨1, by omega⟩
  let k : Fin μ := ⟨μ - 1, by omega⟩
  have hazj : (a z : ℤ) < a j := by exact_mod_cast ha (show z < j from Nat.zero_lt_one)
  have hajk : (a j : ℤ) < a k := by
    exact_mod_cast ha (show j < k by change 1 < μ - 1; omega)
  have hbzj : (b z : ℤ) < b j := by exact_mod_cast hb (show z < j from Nat.zero_lt_one)
  have hbjk : (b j : ℤ) < b k := by
    exact_mod_cast hb (show j < k by change 1 < μ - 1; omega)
  have hzrev : Fin.rev z = k := Fin.ext (Fin.val_rev z)
  have hfour : 4 ≤ f z := by
    dsimp [f]
    rw [hzrev]
    have ham : (a z : ℤ) - a k ≤ -2 := by omega
    have hbm : (b z : ℤ) - b k ≤ -2 := by omega
    nlinarith [mul_nonneg (show 0 ≤ (a k : ℤ) - a z - 2 by omega)
      (show 0 ≤ (b k : ℤ) - b z - 2 by omega)]
  have hle : f z ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ z)
  have hde : (e : ℤ) + 2 ≤ d := by omega
  exact_mod_cast hde

private theorem high_end
    (μ : ℕ) (a b : Fin μ → ℕ) (hμ : 3 ≤ μ) (ha : StrictMono a)
    (hb : StrictMono b) (hcross : ∀ i j, a i ≤ b j) :
    let p := preMerged a b
    let d := ∑ i, a i * (b i - a i)
    let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
    p.natDegree = d ∧ p.coeff d = 1 ∧ p.coeff (d - 1) = c ∧
      d ≥ b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩ + 4 := by
  let z : Fin μ := ⟨0, by omega⟩
  let j : Fin μ := ⟨1, by omega⟩
  let k : Fin μ := ⟨μ - 1, by omega⟩
  let t := b z - a k
  let d := ∑ i, a i * (b i - a i)
  let a0 := ∏ i, gauss (b i) (a i)
  let b0 := ∏ i, gauss (b i) (a (Fin.rev i))
  have hi := index_bounds μ a b hμ ha hb hcross
  have has := gaussian_product_shape μ a b (fun i => hcross i i)
  change a0.Monic ∧ a0.natDegree = d ∧ a0.reverse = a0 at has
  have hbs := gaussian_product_shape μ (fun i => a (Fin.rev i)) b
    (fun i => hcross (Fin.rev i) i)
  have hdegap := reversed_degree_gap μ a b hμ ha hb hcross
  have hblt : b0.natDegree + 2 ≤ d := by
    rw [hbs.2.1]
    exact hdegap
  have hazj := ha (show z < j from Nat.zero_lt_one)
  have hajk := ha (show j < k by change 1 < μ - 1; omega)
  have hak : 2 ≤ a k := by omega
  have hdk : t + 2 ≤ b k - a k := hi.1 k
  have hkd : a k * (b k - a k) ≤ d :=
    Finset.single_le_sum (f := fun i : Fin μ => a i * (b i - a i))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hbound : t + 4 ≤ d := by nlinarith
  have halow := gaussian_product_low μ a b (by omega) ha (fun i => by
    have := hi.1 i
    have := hcross i i
    omega)
  have htop : a0.coeff d = 1 := by
    rw [← has.2.1]
    exact has.1.coeff_natDegree
  have hnext : a0.coeff (d - 1) =
      (if 0 < a z then μ else μ - 1 : ℕ) := by
    have hrev := congrArg (fun f : ℤ[X] => f.coeff 1) has.2.2
    rw [coeff_reverse, has.2.1, revAt_le (by omega)] at hrev
    exact hrev.trans halow.2
  have hbtop : b0.coeff d = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hbnext : b0.coeff (d - 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  change (a0 - b0).natDegree = d ∧ (a0 - b0).coeff d = 1 ∧
    (a0 - b0).coeff (d - 1) = _ ∧ d ≥ t + 4
  refine ⟨?_, ?_, ?_, hbound⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [has.2.1]; omega), has.2.1]
  · rw [coeff_sub, htop, hbtop, sub_zero]
  · rw [coeff_sub, hnext, hbnext, sub_zero]

private theorem palindrome_contradiction
    (p : ℤ[X]) (r d c : ℕ)
    (hfirst : p.coeff r = 1 ∧ p.coeff (r + 1) = c + 1)
    (hlast : p.natDegree = d ∧ p.coeff d = 1 ∧ p.coeff (d - 1) = c)
    (hbelow : ∀ n, n < r → p.coeff n = 0) (hcpos : 0 < c)
    (hgap : r + 1 < d - 1) (hc : c + 1 ≠ c)
    (hpal : IsAlmostPalindromic p) : False := by
  let l := p.support.sort (· ≤ ·)
  have hsorted : l.SortedLT := p.support.sortedLT_sort
  have hmem (n : ℕ) : n ∈ l ↔ p.coeff n ≠ 0 := by
    simp [l]
  have hr : r ∈ l := (hmem r).2 (by rw [hfirst.1]; norm_num)
  have hs : r + 1 ∈ l := (hmem (r + 1)).2 (by rw [hfirst.2]; positivity)
  have ht : d - 1 ∈ l := (hmem (d - 1)).2 (by
    rw [hlast.2.2]
    exact_mod_cast hcpos.ne')
  have hd : d ∈ l := (hmem d).2 (by rw [hlast.2.1]; norm_num)
  have hb (n : ℕ) (hn : n ∈ l) : r ≤ n ∧ n ≤ d := by
    refine ⟨?_, ?_⟩
    · by_contra h
      exact (hmem n).1 hn (hbelow n (by omega))
    · rw [← hlast.1]
      exact le_natDegree_of_ne_zero ((hmem n).1 hn)
  obtain ⟨ir, hir, her⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨is, his, hes⟩ := List.mem_iff_getElem.1 hs
  obtain ⟨it, hit, het⟩ := List.mem_iff_getElem.1 ht
  obtain ⟨id, hid, hed⟩ := List.mem_iff_getElem.1 hd
  have hn : 0 < l.length := by omega
  have hz : l[0] = r := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le
      (hi := hn) (hj := hir) (Nat.zero_le ir)
    have hge := (hb l[0] (List.getElem_mem hn)).1
    omega
  have hspos : 0 < is := by
    have hlt : l[0] < l[is] := by omega
    exact hsorted.getElem_lt_getElem_iff.1 hlt
  have hn2 : 1 < l.length := by omega
  have hsecond : l[1] = r + 1 := by
    have hlt := hsorted.getElem_lt_getElem_of_lt (hi := hn) (hj := hn2) (by omega : 0 < 1)
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le
      (hi := hn2) (hj := his) (by omega : 1 ≤ is)
    omega
  have htop : l[l.length - 1] = d := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le (hi := hid)
      (hj := (by omega : l.length - 1 < l.length)) (by omega : id ≤ l.length - 1)
    have hge := (hb l[l.length - 1] (List.getElem_mem (by omega))).2
    omega
  have htlt : it < l.length - 1 := by
    apply hsorted.getElem_lt_getElem_iff.1
    omega
  have hpenult : l[l.length - 2] = d - 1 := by
    have hle := hsorted.sortedLE.getElem_le_getElem_of_le (hi := hit)
      (hj := (by omega : l.length - 2 < l.length)) (by omega : it ≤ l.length - 2)
    have hlt := hsorted.getElem_lt_getElem_of_lt
      (hi := (by omega : l.length - 2 < l.length))
      (hj := (by omega : l.length - 1 < l.length)) (by omega : l.length - 2 < l.length - 1)
    omega
  change (l.map p.coeff).Palindrome at hpal
  have heq := congrArg (fun xs : List ℤ => xs[1]?)
    (List.Palindrome.iff_reverse_eq.mp hpal)
  have hidx : l.length - 1 - 1 = l.length - 2 := Nat.sub_sub l.length 1 1
  rw [List.getElem?_reverse (l := l.map p.coeff) (i := 1) (by simpa using hn2)] at heq
  simp only [List.length_map, hidx,
    List.getElem?_map, List.getElem?_eq_getElem (by omega : l.length - 2 < l.length),
    List.getElem?_eq_getElem hn2, Option.map_some, hpenult, hsecond,
    hlast.2.2, hfirst.2, Option.some.injEq] at heq
  exact hc (by exact_mod_cast heq.symm)

theorem result : claim := by
  intro μ a b hμ ha hb hcross
  let t := b ⟨0, by omega⟩ - a ⟨μ - 1, by omega⟩
  let r := t + 1
  let c := if 0 < a ⟨0, by omega⟩ then μ else μ - 1
  have hlo := low_end μ a b hμ ha hb hcross
  have hhi := high_end μ a b hμ ha hb hcross
  intro hpal
  apply palindrome_contradiction (preMerged a b) r (∑ i, a i * (b i - a i)) c
  · simpa [r, t, c] using And.intro hlo.1 hlo.2.1
  · simpa [c] using And.intro hhi.1 (And.intro hhi.2.1 hhi.2.2.1)
  · simpa [r, t] using hlo.2.2
  · dsimp [c]
    split <;> omega
  · dsimp [r, t]
    omega
  · dsimp [c]
    omega
  · exact hpal

end D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
