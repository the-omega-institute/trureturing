/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ThreeSpectrum/QuarticPacking
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact equality of the cleared discriminant and its sparse coefficient table. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.UniformExpansion
import Mathlib.Data.Int.Bitwise
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-! Exact arithmetic bridge from the quartic to its sparse coefficient table. -/

open scoped BigOperators

namespace RefinedBMV.DividedDifference.SparseExpansion

open Polynomial

private def Exponents.plus (a b : Exponents) : Exponents :=
  ⟨a.p + b.p, a.x + b.x, a.y + b.y, a.u + b.u, a.v + b.v⟩

private def Exponents.sup (a b : Exponents) : Exponents :=
  ⟨max a.p b.p, max a.x b.x, max a.y b.y, max a.u b.u, max a.v b.v⟩

private def Exponents.bounded (a b : Exponents) : Prop :=
  a.p ≤ b.p ∧ a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.u ≤ b.u ∧ a.v ≤ b.v

private theorem Exponents.bounded_trans {a b c : Exponents}
    (hab : a.bounded b) (hbc : b.bounded c) : a.bounded c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.1.trans hbc.2.2.1,
    hab.2.2.2.1.trans hbc.2.2.2.1, hab.2.2.2.2.trans hbc.2.2.2.2⟩

private theorem Exponents.bounded_plus {a b c d : Exponents}
    (hab : a.bounded b) (hcd : c.bounded d) : (a.plus c).bounded (b.plus d) :=
  ⟨Nat.add_le_add hab.1 hcd.1, Nat.add_le_add hab.2.1 hcd.2.1,
    Nat.add_le_add hab.2.2.1 hcd.2.2.1, Nat.add_le_add hab.2.2.2.1 hcd.2.2.2.1,
    Nat.add_le_add hab.2.2.2.2 hcd.2.2.2.2⟩

private theorem Exponents.bounded_sup_left (a b : Exponents) : a.bounded (a.sup b) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

private theorem Exponents.bounded_sup_right (a b : Exponents) : b.bounded (a.sup b) :=
  ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

private def coeffMass (ts : List Term) : ℤ :=
  (ts.map fun t => |t.coefficient|).sum

private def rawProduct (as bs : List Term) : List Term :=
  as.flatMap fun a => bs.map fun b => ⟨a.exponents.plus b.exponents, a.coefficient * b.coefficient⟩

private def rawNegation (ts : List Term) : List Term :=
  ts.map fun t => ⟨t.exponents, -t.coefficient⟩

private structure BoundedExpansion where
  terms : List Term
  degree : Exponents
  mass : ℤ
  term_bound : ∀ t ∈ terms, t.exponents.bounded degree
  mass_bound : coeffMass terms ≤ mass
  mass_nonneg : 0 ≤ mass

private def BoundedExpansion.single (e : Exponents) (z : ℤ) : BoundedExpansion where
  terms := [⟨e, z⟩]
  degree := e
  mass := |z|
  term_bound := by
    intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  mass_bound := by simp [coeffMass]
  mass_nonneg := abs_nonneg _

private def BoundedExpansion.add (a b : BoundedExpansion) : BoundedExpansion where
  terms := a.terms ++ b.terms
  degree := a.degree.sup b.degree
  mass := a.mass + b.mass
  term_bound := by
    intro t ht
    obtain ha | hb := List.mem_append.mp ht
    · exact Exponents.bounded_trans (a.term_bound t ha) (a.degree.bounded_sup_left b.degree)
    · exact Exponents.bounded_trans (b.term_bound t hb) (a.degree.bounded_sup_right b.degree)
  mass_bound := by
    simpa only [coeffMass, List.map_append, List.sum_append] using
      add_le_add a.mass_bound b.mass_bound
  mass_nonneg := add_nonneg a.mass_nonneg b.mass_nonneg

private def BoundedExpansion.neg (a : BoundedExpansion) : BoundedExpansion where
  terms := rawNegation a.terms
  degree := a.degree
  mass := a.mass
  term_bound := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact a.term_bound u hu
  mass_bound := by
    simpa [rawNegation, coeffMass, List.map_map, Function.comp_def] using a.mass_bound
  mass_nonneg := a.mass_nonneg

private theorem mass_product (as bs : List Term) :
    coeffMass (rawProduct as bs) = coeffMass as * coeffMass bs := by
  induction as with
  | nil => simp [rawProduct, coeffMass]
  | cons a as ih =>
    simp only [rawProduct, List.flatMap_cons, coeffMass, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, abs_mul, List.sum_map_mul_left, List.map_cons,
      List.sum_cons, add_mul] at ih ⊢
    rw [ih]

private def BoundedExpansion.mul (a b : BoundedExpansion) : BoundedExpansion where
  terms := rawProduct a.terms b.terms
  degree := a.degree.plus b.degree
  mass := a.mass * b.mass
  term_bound := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := List.mem_flatMap.mp ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hut
    exact Exponents.bounded_plus (a.term_bound u hu) (b.term_bound v hv)
  mass_bound := by
    rw [mass_product]
    exact mul_le_mul a.mass_bound b.mass_bound (by simp [coeffMass, List.sum_nonneg])
      a.mass_nonneg
  mass_nonneg := mul_nonneg a.mass_nonneg b.mass_nonneg

private instance : Add BoundedExpansion := ⟨BoundedExpansion.add⟩
private instance : Sub BoundedExpansion := ⟨fun a b => a.add b.neg⟩
private instance : Mul BoundedExpansion := ⟨BoundedExpansion.mul⟩
private instance (n : ℕ) : OfNat BoundedExpansion n :=
  ⟨BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ n⟩

private def boundedPow (a : BoundedExpansion) : ℕ → BoundedExpansion
  | 0 => 1
  | n + 1 => boundedPow a n * a

private instance : Pow BoundedExpansion ℕ := ⟨boundedPow⟩

private def rawQuartic : BoundedExpansion :=
  quarticFormula
    (BoundedExpansion.single ⟨1, 0, 0, 0, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 0, 0, 1, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 0, 0, 0, 1⟩ 1)

section Semantics

variable {R : Type*} [CommRing R] (p x y u v : R)

private def BoundedExpansion.eval (a : BoundedExpansion) : R :=
  evalTerms p x y u v a.terms

private theorem eval_bounded_add (a b : BoundedExpansion) :
    (a + b).eval p x y u v = a.eval p x y u v + b.eval p x y u v := by
  change evalTerms p x y u v (a.terms ++ b.terms) = _
  simp [BoundedExpansion.eval, evalTerms]

private theorem eval_bounded_sub (a b : BoundedExpansion) :
    (a - b).eval p x y u v = a.eval p x y u v - b.eval p x y u v := by
  change evalTerms p x y u v (a.terms ++ rawNegation b.terms) = _
  simp only [BoundedExpansion.eval, evalTerms, List.map_append, List.sum_append,
    rawNegation, List.map_map, Function.comp_def, Term.eval, Int.cast_neg, neg_mul, sub_eq_add_neg]
  congr 1
  generalize b.terms = ts
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, Term.eval, add_comm]

private theorem eval_bounded_mul (a b : BoundedExpansion) :
    (a * b).eval p x y u v = a.eval p x y u v * b.eval p x y u v := by
  change evalTerms p x y u v (rawProduct a.terms b.terms) = _
  simp only [BoundedExpansion.eval]
  generalize a.terms = as
  generalize b.terms = bs
  induction as with
  | nil => simp [rawProduct, evalTerms]
  | cons a as ih =>
    simp only [rawProduct, List.flatMap_cons, evalTerms, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, List.map_cons, List.sum_cons, add_mul] at ih ⊢
    rw [ih]
    congr 1
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro b _
    simp only [Term.eval, Exponents.plus, pow_add, Int.cast_mul]
    ring

private theorem eval_bounded_single (e : Exponents) (z : ℤ) :
    (BoundedExpansion.single e z).eval p x y u v = (z : R) *
      (p ^ e.p * x ^ e.x * y ^ e.y * u ^ e.u * v ^ e.v) := by
  simp [BoundedExpansion.single, BoundedExpansion.eval, evalTerms, Term.eval]

private theorem eval_bounded_nat (n : ℕ) :
    (@OfNat.ofNat BoundedExpansion n _).eval p x y u v = (n : R) := by
  change (BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ n).eval p x y u v = _
  simp [eval_bounded_single]

private theorem eval_bounded_pow (a : BoundedExpansion) (n : ℕ) :
    (a ^ n).eval p x y u v = a.eval p x y u v ^ n := by
  induction n with
  | zero =>
    change (1 : BoundedExpansion).eval p x y u v = _ ^ 0
    simpa using eval_bounded_nat p x y u v 1
  | succ n ih =>
    change ((a ^ n) * a).eval p x y u v = _
    rw [eval_bounded_mul, pow_succ, ih]

private theorem eval_rawQuartic :
    rawQuartic.eval p x y u v = quarticFormula p x y u v := by
  have h1 : (1 : BoundedExpansion).eval p x y u v = 1 := by
    simpa only [Nat.cast_one] using eval_bounded_nat p x y u v 1
  have h2 : (2 : BoundedExpansion).eval p x y u v = 2 := by
    simpa only [Nat.cast_ofNat] using eval_bounded_nat p x y u v 2
  have h4 : (4 : BoundedExpansion).eval p x y u v = 4 := by
    simpa only [Nat.cast_ofNat] using eval_bounded_nat p x y u v 4
  simp only [rawQuartic, quarticFormula, eval_bounded_add, eval_bounded_sub,
    eval_bounded_mul, eval_bounded_pow, eval_bounded_single, h1, h2, h4, Int.cast_one,
    pow_zero, pow_one, one_mul, mul_one]

end Semantics

section Packing

private def Exponents.index (e : Exponents) : ℕ :=
  e.p + 9 * (e.x + 13 * (e.y + 13 * (e.u + 13 * e.v)))

private def Exponents.decode (i : ℕ) : Exponents :=
  ⟨i % 9, i / 9 % 13, i / 117 % 13, i / 1521 % 13, i / 19773⟩

private def radixBounds : Exponents := ⟨8, 12, 12, 12, 12⟩

private theorem Exponents.decode_index (e : Exponents) (h : e.bounded radixBounds) :
    decode e.index = e := by
  rcases e with ⟨p, x, y, u, v⟩
  simp only [bounded, radixBounds] at h
  simp only [decode, index]
  congr 1 <;> omega

private noncomputable def packedPolynomial (ts : List Term) : ℤ[X] :=
  (ts.map fun t => monomial t.exponents.index t.coefficient).sum

private theorem packedPolynomial_coeff_bound (ts : List Term) (i : ℕ) :
    |(packedPolynomial ts).coeff i| ≤ coeffMass ts := by
  induction ts with
  | nil => simp [packedPolynomial, coeffMass]
  | cons t ts ih =>
    change |(monomial t.exponents.index t.coefficient + packedPolynomial ts).coeff i| ≤
      |t.coefficient| + coeffMass ts
    rw [coeff_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [coeff_monomial]
    split <;> simp

private theorem eval_packedPolynomial (ts : List Term) (b : ℤ) :
    (packedPolynomial ts).eval b = evalTerms b (b ^ 9) (b ^ 117) (b ^ 1521) (b ^ 19773) ts := by
  induction ts with
  | nil => simp [packedPolynomial, evalTerms]
  | cons t ts ih =>
    change (monomial t.exponents.index t.coefficient + packedPolynomial ts).eval b =
      t.eval b (b ^ 9) (b ^ 117) (b ^ 1521) (b ^ 19773) +
        evalTerms b (b ^ 9) (b ^ 117) (b ^ 1521) (b ^ 19773) ts
    rw [eval_add, eval_monomial, ih]
    congr 1
    simp only [Term.eval, Int.cast_id, Exponents.index, pow_add, pow_mul]
    simp only [← pow_mul]
    simp only [show 9 * 13 = 117 by rfl, show 9 * 13 * 13 = 1521 by rfl,
      show 9 * 13 * 13 * 13 = 19773 by rfl, mul_assoc]

private theorem eval_unpackedPolynomial {R : Type*} [CommRing R] (p x y u v : R)
    (ts : List Term) (h : ∀ t ∈ ts, t.exponents.bounded radixBounds) :
    (packedPolynomial ts).sum (fun i c => (Term.mk (Exponents.decode i) c).eval p x y u v) =
      evalTerms p x y u v ts := by
  induction ts with
  | nil => simp [packedPolynomial, evalTerms]
  | cons t ts ih =>
    change (monomial t.exponents.index t.coefficient + packedPolynomial ts).sum _ = _
    rw [sum_add_index _ _ _ (by simp [Term.eval]) (by simp [Term.eval, add_mul]),
      sum_monomial_index _ _ (by simp [Term.eval]), ih (fun u hu => h u (by simp [hu])),
      Exponents.decode_index _ (h t (by simp))]
    rfl

private theorem coeff_eq_zero_of_sum_range_eq_zero {base : ℤ} (hbase : 0 < base)
    {n : ℕ} {coeff : ℕ → ℤ} (hcoeff : ∀ i < n, |coeff i| < base)
    (hsum : (∑ i ∈ Finset.range n, coeff i * base ^ i) = 0) :
    ∀ i < n, coeff i = 0 := by
  induction n generalizing coeff with
  | zero =>
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_succ, ← mul_assoc, pow_zero, mul_one] at hsum
    rw [← Finset.sum_mul] at hsum
    have hmod : coeff 0 % base = 0 := by
      simpa only [Int.mul_add_emod_self_right, Int.zero_emod] using
        congrArg (fun z : ℤ => z % base) hsum
    have hhead : coeff 0 = 0 :=
      Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero hmod) (hcoeff 0 (Nat.zero_lt_succ n))
    rw [hhead, add_zero] at hsum
    have htail : (∑ i ∈ Finset.range n, coeff (i + 1) * base ^ i) = 0 :=
      (mul_eq_zero.mp hsum).resolve_right hbase.ne'
    intro i hi
    cases i with
    | zero => exact hhead
    | succ i =>
      exact ih (fun j hj => hcoeff (j + 1) (Nat.succ_lt_succ hj)) htail i
        (Nat.lt_of_succ_lt_succ hi)

private theorem eq_of_bounded_packed_eval {P Q : ℤ[X]} {b : ℤ}
    (hb : 0 < b) (hc : ∀ i, |(P - Q).coeff i| < b) (he : P.eval b = Q.eval b) : P = Q := by
  let n := (P - Q).natDegree + 1
  have hdegree : (P - Q).natDegree < n := Nat.lt_succ_self _
  have hsum : (∑ i ∈ Finset.range n, (P - Q).coeff i * b ^ i) = 0 := by
    rw [← Polynomial.eval_eq_sum_range' hdegree b, Polynomial.eval_sub, he, sub_self]
  apply sub_eq_zero.mp
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < n
  · exact coeff_eq_zero_of_sum_range_eq_zero hb (fun j _ => hc j) hsum i hi
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hi))

private theorem difference_abs_lt_radix
    (a b : ℤ) (ha : |a| ≤ 20000000) (hb : |b| ≤ 302600448) :
    |a - b| < 2 ^ 32 := by
  calc
    |a - b| ≤ |a| + |b| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
    _ ≤ 20000000 + 302600448 := add_le_add ha hb
    _ < 2 ^ 32 := by decide +kernel

def termFitsQuarticRadix (t : Term) : Bool :=
  decide (t.exponents.p ≤ 8 ∧ t.exponents.x ≤ 12 ∧ t.exponents.y ≤ 12 ∧
    t.exponents.u ≤ 12 ∧ t.exponents.v ≤ 12)

def quarticTableMass (ts : List Term) : ℤ := coeffMass ts

private theorem eval_eq_eval_of_packed_eq {R : Type*} [CommRing R]
    (as bs : List Term)
    (ha : ∀ t ∈ as, t.exponents.bounded radixBounds)
    (hb : ∀ t ∈ bs, t.exponents.bounded radixBounds)
    (hma : coeffMass as ≤ 20000000) (hmb : coeffMass bs ≤ 302600448)
    (he : evalTerms (2 ^ 32 : ℤ) ((2 ^ 32 : ℤ) ^ 9) ((2 ^ 32 : ℤ) ^ 117)
      ((2 ^ 32 : ℤ) ^ 1521) ((2 ^ 32 : ℤ) ^ 19773) as =
      evalTerms (2 ^ 32 : ℤ) ((2 ^ 32 : ℤ) ^ 9) ((2 ^ 32 : ℤ) ^ 117)
        ((2 ^ 32 : ℤ) ^ 1521) ((2 ^ 32 : ℤ) ^ 19773) bs)
    (p x y u v : R) :
    evalTerms p x y u v as = evalTerms p x y u v bs := by
  have heq : packedPolynomial as = packedPolynomial bs := by
    refine eq_of_bounded_packed_eval (b := 2 ^ 32) (by decide +kernel) ?_ ?_
    · intro i
      rw [coeff_sub]
      exact difference_abs_lt_radix ((packedPolynomial as).coeff i) ((packedPolynomial bs).coeff i)
        ((packedPolynomial_coeff_bound as i).trans hma)
        ((packedPolynomial_coeff_bound bs i).trans hmb)
    · rw [eval_packedPolynomial, eval_packedPolynomial]
      exact he
  rw [← eval_unpackedPolynomial p x y u v as ha, heq,
    eval_unpackedPolynomial p x y u v bs hb]

/-- Evaluation at the mixed-radix powers certifies a small-coefficient table for the
cleared quartic. Bounds ensure that no coefficient or exponent can carry. -/
theorem eval_certified_quartic_table {R : Type*} [CommRing R] (ts : List Term)
    (hdegree : ts.all termFitsQuarticRadix = true)
    (hmass : quarticTableMass ts ≤ 20000000)
    (heval :
      let b : ℤ := 2 ^ 32
      evalTerms b (b ^ 9) (b ^ 117) (b ^ 1521) (b ^ 19773) ts =
        quarticFormula b (b ^ 9) (b ^ 117) (b ^ 1521) (b ^ 19773))
    (p x y u v : R) :
    evalTerms p x y u v ts = quarticFormula p x y u v := by
  have hraw : ∀ t ∈ rawQuartic.terms, t.exponents.bounded radixBounds := by
    intro t ht
    exact Exponents.bounded_trans (rawQuartic.term_bound t ht)
      (show rawQuartic.degree.bounded radixBounds by
        exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
          by decide +kernel, by decide +kernel⟩)
  have ht : ∀ t ∈ ts, t.exponents.bounded radixBounds := by
    intro t hm
    simpa [termFitsQuarticRadix, Exponents.bounded, radixBounds, Bool.and_eq_true] using
      List.all_eq_true.mp hdegree t hm
  have hmassRaw : coeffMass rawQuartic.terms ≤ 302600448 :=
    rawQuartic.mass_bound.trans (show rawQuartic.mass ≤ 302600448 by decide +kernel)
  have hp : evalTerms (2 ^ 32 : ℤ) ((2 ^ 32 : ℤ) ^ 9) ((2 ^ 32 : ℤ) ^ 117)
      ((2 ^ 32 : ℤ) ^ 1521) ((2 ^ 32 : ℤ) ^ 19773) ts =
      rawQuartic.eval (2 ^ 32 : ℤ) ((2 ^ 32 : ℤ) ^ 9) ((2 ^ 32 : ℤ) ^ 117)
        ((2 ^ 32 : ℤ) ^ 1521) ((2 ^ 32 : ℤ) ^ 19773) :=
    heval.trans (eval_rawQuartic _ _ _ _ _).symm
  rw [← eval_rawQuartic p x y u v]
  exact eval_eq_eval_of_packed_eq ts rawQuartic.terms ht hraw hmass hmassRaw hp p x y u v

end Packing

end RefinedBMV.DividedDifference.SparseExpansion
