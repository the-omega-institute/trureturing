/- GID: D5/S3/VertexAlgebra/BRST/WeightedFreeAlgebraEulerSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/WeightedFreeAlgebraEulerSeries
   mirror-E: none(waiver:elementary-weighted-series)
   anchors: []
   utility: none
   digest: Weighted free algebra Hilbert series and rigidity of finite Euler coefficients. -/

import D5.S3.VertexAlgebra.BRST.OrderedLieMonomials
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Finite.Sigma
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Weighted free algebra Hilbert series and finite Euler coefficients

The head and tail of a word give the Hilbert series identity in §6.2 of the
direct Monster presentation argument (2026-11-24). The finite Euler product
sandwich of §6.4 then recovers the multiplicities from the diagonal coefficients.
-/

set_option autoImplicit false

open scoped BigOperators
open Module Finset
open D5.S3.VertexAlgebra.OrderedLieMonomials

namespace D5.S3.VertexAlgebra.WeightedFreeAlgebraEulerSeries

variable {X : Type*}

/-- The lists of total weight `n`. -/
abbrev WeightedWords (e : X → ℕ) (n : ℕ) := {w : List X // wordWeight e w = n}

/-- The number of letters of the specified weight. -/
noncomputable def letterCount (e : X → ℕ) (n : ℕ) : ℕ := Nat.card {x : X // e x = n}

/-- The number of words of the specified weight. -/
noncomputable def wordCount (e : X → ℕ) (n : ℕ) : ℕ := Nat.card (WeightedWords e n)

theorem finite_weightedLetters (e : X → ℕ) (n : ℕ) [Finite {x : X // e x ≤ n}] :
    Finite {x : X // e x = n} :=
  Finite.of_injective (fun x : {x : X // e x = n} =>
    (⟨x.val, x.property.le⟩ : {x : X // e x ≤ n}))
    (fun _ _ h => Subtype.ext (congrArg (fun z : {x : X // e x ≤ n} => z.val) h))

private theorem eq_nil_of_weight_zero (e : X → ℕ) (he : ∀ x, 0 < e x)
    (w : WeightedWords e 0) : w.val = [] := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | nil => rfl
  | cons x t =>
    change e x + wordWeight e t = 0 at hw
    have := he x
    omega

private def weightZeroEquiv (e : X → ℕ) (he : ∀ x, 0 < e x) :
    WeightedWords e 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], rfl⟩
  left_inv w := Subtype.ext (eq_nil_of_weight_zero e he w).symm
  right_inv u := by cases u; rfl

/-- A word of weight `n + 1` consists of a first letter of weight
`i + 1` and a tail of weight `n - i`, for a unique `i : Fin (n + 1)`. -/
def headTailEquiv (e : X → ℕ) (he : ∀ x, 0 < e x) (n : ℕ) :
    WeightedWords e (n + 1) ≃
      (Σ i : Fin (n + 1), {x : X // e x = i.val + 1} × WeightedWords e (n - i.val)) where
  toFun w := by
    obtain ⟨w, hw⟩ := w
    cases w with
    | nil => exact (Nat.succ_ne_zero n hw.symm).elim
    | cons x t =>
      change e x + wordWeight e t = n + 1 at hw
      have hx := he x
      exact ⟨⟨e x - 1, by omega⟩, ⟨x, by dsimp; omega⟩, ⟨t, by dsimp; omega⟩⟩
  invFun z := by
    obtain ⟨i, ⟨x, hx⟩, ⟨t, ht⟩⟩ := z
    refine ⟨x :: t, ?_⟩
    change e x + wordWeight e t = n + 1
    have := i.isLt
    omega
  left_inv w := by
    obtain ⟨w, hw⟩ := w
    cases w with
    | nil => exact (Nat.succ_ne_zero n hw.symm).elim
    | cons x t => rfl
  right_inv z := by
    obtain ⟨i, ⟨x, hx⟩, ⟨t, ht⟩⟩ := z
    have hi : i.val = e x - 1 := by omega
    obtain ⟨i, hiLt⟩ := i
    change i = e x - 1 at hi
    subst i
    rfl

/-- Positive letter weights and finite bounded alphabets give finite word fibers. -/
theorem finite_weightedWords (e : X → ℕ) (he : ∀ x, 0 < e x)
    (hfinite : ∀ n, Finite {x : X // e x ≤ n}) (n : ℕ) :
    Finite (WeightedWords e n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact Finite.of_equiv Unit (weightZeroEquiv e he).symm
    | succ n =>
      let (i : Fin (n + 1)) : Finite {x : X // e x = i.val + 1} :=
        @finite_weightedLetters _ e (i.val + 1) (hfinite _)
      let (i : Fin (n + 1)) : Finite (WeightedWords e (n - i.val)) :=
        ih _ (by omega)
      exact Finite.of_equiv _ (headTailEquiv e he n).symm

theorem letterCount_zero (e : X → ℕ) (he : ∀ x, 0 < e x) : letterCount e 0 = 0 := by
  let empty : IsEmpty {x : X // e x = 0} := ⟨fun x => (Nat.ne_of_gt (he x.val)) x.property⟩
  exact Nat.card_eq_zero.mpr (Or.inl empty)

theorem wordCount_zero (e : X → ℕ) (he : ∀ x, 0 < e x) : wordCount e 0 = 1 := by
  simpa [wordCount] using Nat.card_congr (weightZeroEquiv e he)

/-- The summation index `i` records the first letter's weight minus one. -/
theorem wordCount_succ (e : X → ℕ) (he : ∀ x, 0 < e x)
    (hfinite : ∀ n, Finite {x : X // e x ≤ n}) (n : ℕ) :
    wordCount e (n + 1) = ∑ i ∈ range (n + 1), letterCount e (i + 1) * wordCount e (n - i) := by
  let (i : Fin (n + 1)) : Finite {x : X // e x = i.val + 1} :=
    @finite_weightedLetters _ e (i.val + 1) (hfinite _)
  let (i : Fin (n + 1)) : Finite (WeightedWords e (n - i.val)) :=
    finite_weightedWords e he hfinite _
  rw [wordCount, Nat.card_congr (headTailEquiv e he n), Nat.card_sigma]
  simp only [Nat.card_prod]
  exact Fin.sum_univ_eq_sum_range (fun i => letterCount e (i + 1) * wordCount e (n - i)) (n + 1)

/-- The monoid-word basis of the free algebra restricts to the given weight. -/
noncomputable def freeAlgebraWeightSpaceBasis (K : Type*) [Field K] (e : X → ℕ) (n : ℕ) :
    Basis (WeightedWords e n) K (freeAlgebraWeightSpace K e n) := by
  let words : {w : FreeMonoid X // wordWeight e w.toList = n} ≃ WeightedWords e n :=
    FreeMonoid.toList.subtypeEquiv (fun _ => Iff.rfl)
  unfold freeAlgebraWeightSpace
  exact (Basis.span ((FreeAlgebra.basisFreeMonoid K X).linearIndependent.comp
    Subtype.val Subtype.val_injective)).reindex words

theorem finrank_freeAlgebraWeightSpace_eq_wordCount (K : Type*) [Field K]
    (e : X → ℕ) (n : ℕ) :
    finrank K (freeAlgebraWeightSpace K e n) = wordCount e n :=
  Module.finrank_eq_nat_card_basis (freeAlgebraWeightSpaceBasis K e n)

/-- The formal generating series of individual letters. -/
noncomputable def letterSeries (R : Type*) [Semiring R] (e : X → ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => (letterCount e n : R)

/-- The formal generating series of words, including the empty word. -/
noncomputable def wordSeries (R : Type*) [Semiring R] (e : X → ℕ) : PowerSeries R :=
  PowerSeries.mk fun n => (wordCount e n : R)

/-- Coefficientwise form of the head-tail decomposition over a semiring. -/
theorem wordSeries_eq_one_add (R : Type*) [Semiring R] (e : X → ℕ)
    (he : ∀ x, 0 < e x) (hfinite : ∀ n, Finite {x : X // e x ≤ n}) :
    wordSeries R e = 1 + letterSeries R e * wordSeries R e := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [wordSeries, letterSeries, wordCount_zero e he,
      letterCount_zero e he]
  | succ n =>
    simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
      PowerSeries.coeff_mul, wordSeries, letterSeries, PowerSeries.coeff_mk]
    rw [Finset.Nat.sum_antidiagonal_succ, letterCount_zero e he, Nat.cast_zero, zero_mul,
      zero_add]
    change (wordCount e (n + 1) : R) =
      ∑ p ∈ antidiagonal n, (letterCount e (p.1 + 1) : R) * (wordCount e p.2 : R)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (letterCount e (i + 1) : R) * (wordCount e j : R)) n,
      wordCount_succ e he hfinite, Nat.cast_sum]
    simp only [Nat.cast_mul]

/-- The formal Hilbert series satisfies the inverse identity in every degree. -/
theorem wordSeries_mul_one_sub_letterSeries (R : Type*) [CommRing R] (e : X → ℕ)
    (he : ∀ x, 0 < e x) (hfinite : ∀ n, Finite {x : X // e x ≤ n}) :
    wordSeries R e * (1 - letterSeries R e) = 1 := by
  rw [mul_sub, mul_one, mul_comm (wordSeries R e) (letterSeries R e)]
  exact sub_eq_iff_eq_add.mpr (wordSeries_eq_one_add R e he hfinite)

section EulerProduct

open Polynomial

/-- A single geometric sum in the existing finite Euler product. -/
private noncomputable def geometricFactor (cutoff degree : ℕ) : Polynomial ℕ :=
  ∑ k : Fin (cutoff + 1), (Polynomial.X : Polynomial ℕ) ^ (degree * k.val)

private theorem coeff_geometricFactor_zero (cutoff degree : ℕ) (hd : 0 < degree) :
    (geometricFactor cutoff degree).coeff 0 = 1 := by
  simp [geometricFactor, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, hd.ne',
    Fin.sum_univ_succ]

private theorem coeff_geometricFactor_of_pos_lt (cutoff : ℕ) {degree k : ℕ}
    (hk : 0 < k) (hkd : k < degree) :
    (geometricFactor cutoff degree).coeff k = 0 := by
  rw [geometricFactor, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_X_pow, ite_eq_right]
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · simp [hj, hk.ne']
  · exact ne_of_lt (hkd.trans_le (Nat.le_mul_of_pos_right _ hj))

private theorem coeff_geometricFactor_self {cutoff degree : ℕ} (hc : 0 < cutoff)
    (hd : 0 < degree) : (geometricFactor cutoff degree).coeff degree = 1 := by
  let first : Fin (cutoff + 1) := ⟨1, by omega⟩
  rw [geometricFactor, Polynomial.finsetSum_coeff, Fintype.sum_eq_single first]
  · simp [first]
  · intro j hj
    rw [Polynomial.coeff_X_pow, ite_eq_right]
    intro h
    have hmul : degree * 1 = degree * j.val := by simpa only [mul_one] using h
    exact hj (Fin.ext ((Nat.eq_of_mul_eq_mul_left hd hmul).symm))

private theorem coeff_mul_of_gap (p q : Polynomial ℕ) {k : ℕ} (hk : 0 < k)
    (hq0 : q.coeff 0 = 1) (hq : ∀ j, 0 < j → j < k → q.coeff j = 0) :
    (p * q).coeff k = p.coeff k + p.coeff 0 * q.coeff k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ', hq0, mul_one]
  congr 1
  rw [Finset.sum_eq_single (0, k)]
  · intro ij hij hne
    obtain ⟨i, j⟩ := ij
    have hsum := Finset.mem_antidiagonal.mp hij
    change i + j = k at hsum
    have hi : i ≠ 0 := by
      intro hi
      subst i
      simp at hsum
      exact hne (by rw [hsum])
    have hj : j + 1 < k + 1 := by omega
    simp [hq _ (Nat.succ_pos j) hj]
  · simp

private theorem coeff_pow_zero_of_coeff_zero (q : Polynomial ℕ) (hq0 : q.coeff 0 = 1)
    (r : ℕ) : (q ^ r).coeff 0 = 1 := by
  change Polynomial.constantCoeff (q ^ r) = 1
  rw [map_pow]
  simp [hq0]

private theorem coeff_pow_of_gap (q : Polynomial ℕ) {degree : ℕ} (hd : 0 < degree)
    (hq0 : q.coeff 0 = 1) (hq : ∀ j, 0 < j → j < degree → q.coeff j = 0) (r : ℕ) :
    (q ^ r).coeff degree = r * q.coeff degree := by
  induction r with
  | zero => simp [Polynomial.coeff_one, hd.ne']
  | succ r ih =>
    rw [pow_succ, coeff_mul_of_gap _ _ hd hq0 hq, ih, coeff_pow_zero_of_coeff_zero q hq0,
      one_mul, Nat.succ_mul]

private theorem truncatedEulerProduct_coeff_zero (a : ℕ → ℕ) (ha : a 0 = 0) (n : ℕ) :
    (truncatedEulerProduct a n).coeff 0 = 1 := by
  unfold truncatedEulerProduct
  rw [Polynomial.coeff_zero_prod]
  apply Finset.prod_eq_one
  intro m _
  change Polynomial.constantCoeff (geometricFactor n m.val ^ a m.val) = 1
  rcases Nat.eq_zero_or_pos m.val with hm | hm
  · rw [hm, ha, pow_zero, map_one]
  · rw [map_pow]
    change (geometricFactor n m.val).coeff 0 ^ a m.val = 1
    rw [coeff_geometricFactor_zero n m.val hm, one_pow]

private theorem truncatedEulerProduct_add (a c : ℕ → ℕ) (n : ℕ) :
    truncatedEulerProduct (fun j => a j + c j) n =
      truncatedEulerProduct a n * truncatedEulerProduct c n := by
  simp only [truncatedEulerProduct, pow_add, Finset.prod_mul_distrib]

/-- At any cutoff, increasing the multiplicities increases every coefficient. -/
theorem truncatedEulerProduct_coeff_mono {a b : ℕ → ℕ} (ha : a 0 = 0) (hb : b 0 = 0)
    (hab : a ≤ b) (cutoff k : ℕ) :
    (truncatedEulerProduct a cutoff).coeff k ≤ (truncatedEulerProduct b cutoff).coeff k := by
  let c : ℕ → ℕ := fun j => b j - a j
  have hb' : b = fun j => a j + c j :=
    funext fun j => (Nat.add_sub_of_le (hab j)).symm
  have hc0 : c 0 = 0 := by simp [c, ha, hb]
  rw [hb', truncatedEulerProduct_add, Polynomial.coeff_mul]
  have hmem : (k, 0) ∈ antidiagonal k := by simp
  have hle := Finset.single_le_sum
    (f := fun ij : ℕ × ℕ =>
      (truncatedEulerProduct a cutoff).coeff ij.1 * (truncatedEulerProduct c cutoff).coeff ij.2)
    (fun ij _ => Nat.zero_le _) hmem
  simpa only [truncatedEulerProduct_coeff_zero c hc0, mul_one] using hle

/-- If the lower multiplicities agree, the diagonal coefficient changes by
exactly the increment in the multiplicity at the cutoff. -/
theorem truncatedEulerProduct_coeff_eq_add_of_agree_below {a b : ℕ → ℕ}
    (ha : a 0 = 0) (hab : a ≤ b) {n : ℕ} (hn : 0 < n) (hbelow : ∀ j < n, a j = b j) :
    (truncatedEulerProduct b n).coeff n =
      (truncatedEulerProduct a n).coeff n + (b n - a n) := by
  let c : ℕ → ℕ := fun j => b j - a j
  have hb' : b = fun j => a j + c j :=
    funext fun j => (Nat.add_sub_of_le (hab j)).symm
  let q := geometricFactor n n
  have hc : truncatedEulerProduct c n = q ^ c n := by
    unfold truncatedEulerProduct
    change (∏ j : Fin (n + 1), geometricFactor n j.val ^ c j.val) = _
    rw [Fintype.prod_eq_single (Fin.last n)]
    · rfl
    · intro j hj
      have hjlt : j.val < n := by
        have hne : j.val ≠ n := fun h => hj (Fin.ext h)
        have hlt := j.isLt
        omega
      simp [c, hbelow j.val hjlt]
  have hq0 : q.coeff 0 = 1 := coeff_geometricFactor_zero n n hn
  have hgap : ∀ j, 0 < j → j < n → q.coeff j = 0 :=
    fun _ hj hjn => coeff_geometricFactor_of_pos_lt n hj hjn
  have hpowGap (j : ℕ) (hj : 0 < j) (hjn : j < n) : (q ^ c n).coeff j = 0 := by
    rw [coeff_pow_of_gap q hj hq0 (fun _ hk hkj => hgap _ hk (hkj.trans hjn)),
      hgap j hj hjn, mul_zero]
  have hprod : truncatedEulerProduct b n = truncatedEulerProduct a n * q ^ c n := by
    rw [hb', truncatedEulerProduct_add, hc]
  rw [hprod, coeff_mul_of_gap _ _ hn (coeff_pow_zero_of_coeff_zero q hq0 _) hpowGap,
    truncatedEulerProduct_coeff_zero a ha, one_mul, coeff_pow_of_gap q hn hq0 hgap,
    show q.coeff n = 1 from coeff_geometricFactor_self hn hn, mul_one]

/-- The cutoff-diagonal coefficients determine an ordered pair of multiplicity
sequences with zero constant multiplicities. -/
theorem eq_of_truncatedEulerProduct_coeff_eq {a b : ℕ → ℕ} (ha : a 0 = 0) (hb : b 0 = 0)
    (hab : a ≤ b) (hdiag : ∀ n,
      (truncatedEulerProduct a n).coeff n = (truncatedEulerProduct b n).coeff n) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ha.trans hb.symm
    · have h := truncatedEulerProduct_coeff_eq_add_of_agree_below ha hab hn ih
      rw [← hdiag n] at h
      exact Nat.le_antisymm (hab n) (Nat.sub_eq_zero_iff_le.mp (by omega))

/-- The native diagonal coefficient equality and the ordered spanning bound
force equality of the source and target multiplicities. -/
theorem multiplicities_eq_of_freeAlgebra_euler_sandwich (K : Type*) [Field K]
    (e : X → ℕ) {a b : ℕ → ℕ} (ha : a 0 = 0) (hb : b 0 = 0) (hab : a ≤ b)
    (hspan : ∀ n, finrank K (freeAlgebraWeightSpace K e n) ≤
      (truncatedEulerProduct a n).coeff n)
    (hdiag : ∀ n, (truncatedEulerProduct b n).coeff n = wordCount e n) :
    a = b := by
  apply eq_of_truncatedEulerProduct_coeff_eq ha hb hab
  intro n
  apply le_antisymm (truncatedEulerProduct_coeff_mono ha hb hab n n)
  rw [hdiag n, ← finrank_freeAlgebraWeightSpace_eq_wordCount K]
  exact hspan n

end EulerProduct

section Denominator

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The finite product of the factors `(1 - X^m) ^ b m` through degree `n`. -/
noncomputable def truncatedEulerDenominator (R : Type*) [CommRing R]
    (b : ℕ → ℕ) (n : ℕ) : PowerSeries R :=
  ∏ m : Fin (n + 1), (1 - (PowerSeries.X : PowerSeries R) ^ m.val) ^ b m.val

private theorem trunc_mul_congr {n : ℕ} {p q r s : PowerSeries R}
    (hp : trunc n p = trunc n q) (hr : trunc n r = trunc n s) :
    trunc n (p * r) = trunc n (q * s) := by
  rw [← trunc_trunc_mul_trunc p r, ← trunc_trunc_mul_trunc q s, hp, hr]

private theorem trunc_prod_congr {ι : Type*} (u : Finset ι) {n : ℕ}
    {f g : ι → PowerSeries R} (h : ∀ i ∈ u, trunc n (f i) = trunc n (g i)) :
    trunc n (∏ i ∈ u, f i) = trunc n (∏ i ∈ u, g i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact trunc_mul_congr (h i (mem_insert_self _ _))
      (ih fun j hj => h j (mem_insert_of_mem hj))

private theorem trunc_geometric_mul (n : ℕ) (m : Fin (n + 1)) (hm : 0 < m.val) :
    trunc (n + 1) ((∑ k : Fin (n + 1), (PowerSeries.X : PowerSeries R) ^ (m.val * k.val)) *
      (1 - PowerSeries.X ^ m.val)) = trunc (n + 1) 1 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (PowerSeries.X : PowerSeries R) ^ (m.val * k)) (n + 1)]
  simp_rw [pow_mul (PowerSeries.X : PowerSeries R) m.val]
  -- The finite geometric identity leaves a single term above the cutoff.
  rw [geom_sum_mul_neg, ← pow_mul, map_sub]
  have hd : n + 1 ≤ m.val * (n + 1) := by
    simpa using Nat.mul_le_mul_right (n + 1) hm
  have hzero : trunc (n + 1) ((PowerSeries.X : PowerSeries R) ^ (m.val * (n + 1))) = 0 := by
    ext k
    rw [coeff_trunc, Polynomial.coeff_zero]
    split_ifs with hk
    · rw [PowerSeries.coeff_X_pow, ite_eq_right (ne_of_lt (hk.trans_le hd))]
    · rfl
  rw [hzero, sub_zero]

private theorem trunc_euler_mul_denominator (b : ℕ → ℕ) (hb : b 0 = 0) (n : ℕ) :
    trunc (n + 1) (((truncatedEulerProduct b n).map (Nat.castRingHom R) : PowerSeries R) *
      truncatedEulerDenominator R b n) = trunc (n + 1) 1 := by
  unfold truncatedEulerProduct truncatedEulerDenominator
  change trunc (n + 1) (Polynomial.coeToPowerSeries.ringHom
    ((∏ m : Fin (n + 1), (geometricFactor n m.val) ^ b m.val).map (Nat.castRingHom R)) *
    ∏ m : Fin (n + 1), (1 - (PowerSeries.X : PowerSeries R) ^ m.val) ^ b m.val) = _
  simp only [geometricFactor, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sum,
    Polynomial.map_X, map_prod, map_pow, map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X]
  rw [← Finset.prod_mul_distrib]
  trans trunc (n + 1) (∏ _m : Fin (n + 1), (1 : PowerSeries R))
  · apply trunc_prod_congr
    intro m _
    rw [← mul_pow]
    rcases Nat.eq_zero_or_pos m.val with hm | hm
    · simp [hm, hb]
    · rw [← trunc_trunc_pow, trunc_geometric_mul n m hm, trunc_trunc_pow, one_pow]
  · rw [Finset.prod_const_one]

/-- A diagonal denominator equality through each finite cutoff yields the
natural Euler coefficients required by the multiplicity sandwich. -/
theorem truncatedEulerProduct_coeff_eq_wordCount_of_denominator [CharZero R]
    (e : X → ℕ) (he : ∀ x, 0 < e x) (hfinite : ∀ n, Finite {x : X // e x ≤ n})
    {b : ℕ → ℕ} (hb : b 0 = 0)
    (hden : ∀ n, trunc (n + 1) (truncatedEulerDenominator R b n) =
      trunc (n + 1) (1 - letterSeries R e)) (n : ℕ) :
    (truncatedEulerProduct b n).coeff n = wordCount e n := by
  let p : PowerSeries R := (truncatedEulerProduct b n).map (Nat.castRingHom R)
  let w := wordSeries R e
  let d := 1 - letterSeries R e
  have hd : d * w = 1 := by
    rw [mul_comm]
    exact wordSeries_mul_one_sub_letterSeries R e he hfinite
  have hp : trunc (n + 1) (p * d) = trunc (n + 1) 1 :=
    (trunc_mul_congr rfl (hden n).symm).trans (trunc_euler_mul_denominator b hb n)
  have h : trunc (n + 1) p = trunc (n + 1) w := calc
    trunc (n + 1) p = trunc (n + 1) (p * (d * w)) := by rw [hd, mul_one]
    _ = trunc (n + 1) ((p * d) * w) := by rw [mul_assoc]
    _ = trunc (n + 1) (1 * w) := trunc_mul_congr hp rfl
    _ = trunc (n + 1) w := by rw [one_mul]
  apply Nat.cast_injective (R := R)
  simpa [p, w, wordSeries, coeff_trunc, Polynomial.coeff_coe, Polynomial.coeff_map]
    using congrArg (fun q : Polynomial R => q.coeff n) h

/-- The finite form of the diagonal denominator identity, together with the
ordered spanning bound and the source-to-target dimension inequality, forces
equality of the two multiplicity sequences. -/
theorem multiplicities_eq_of_freeAlgebra_euler_sandwich_of_denominator
    (K : Type*) [Field K] (R : Type*) [CommRing R] [CharZero R]
    (e : X → ℕ) (he : ∀ x, 0 < e x) (hfinite : ∀ n, Finite {x : X // e x ≤ n})
    {a b : ℕ → ℕ} (ha : a 0 = 0) (hb : b 0 = 0) (hab : a ≤ b)
    (hspan : ∀ n, finrank K (freeAlgebraWeightSpace K e n) ≤
      (truncatedEulerProduct a n).coeff n)
    (hden : ∀ n, trunc (n + 1) (truncatedEulerDenominator R b n) =
      trunc (n + 1) (1 - letterSeries R e)) :
    a = b :=
  multiplicities_eq_of_freeAlgebra_euler_sandwich K e ha hb hab hspan
    (truncatedEulerProduct_coeff_eq_wordCount_of_denominator e he hfinite hb hden)

end Denominator

end D5.S3.VertexAlgebra.WeightedFreeAlgebraEulerSeries
