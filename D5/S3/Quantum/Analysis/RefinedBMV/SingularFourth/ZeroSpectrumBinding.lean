/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumBinding
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact identification of the five polynomial coefficient tables. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumFormula
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.QuarticPacking

/-! Mixed-radix identity check adapted from ThreeSpectrum.QuarticPacking.
We retain its bounded expansions and exact sparse semantics, using the public
JetMask theorem for injectivity at the radix. The fourth and fifth exponents
of its existing Term representation are unused. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.DividedDifference.SparseExpansion

open RefinedBMV.ZeroSpectrum

private def Exponents.plus (a b : Exponents) : Exponents :=
  ⟨a.p + b.p, a.x + b.x, a.y + b.y, a.u + b.u, a.v + b.v⟩

private def Exponents.sup (a b : Exponents) : Exponents :=
  ⟨max a.p b.p, max a.x b.x, max a.y b.y, max a.u b.u, max a.v b.v⟩

private def Exponents.bounded (a b : Exponents) : Prop :=
  a.p ≤ b.p ∧ a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.u ≤ b.u ∧ a.v ≤ b.v

private instance (a b : Exponents) : Decidable (a.bounded b) := by
  unfold Exponents.bounded
  infer_instance

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

private def rawFormula (k : SignPolynomial) : BoundedExpansion :=
  scaledFormula k
    (BoundedExpansion.single ⟨1, 0, 0, 0, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1)
    (BoundedExpansion.single ⟨0, 0, 1, 0, 0⟩ 1)

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

private theorem eval_rawFormula (k : SignPolynomial) :
    (rawFormula k).eval p x y 1 1 = scaledFormula k p x y := by
  have h1 : (1 : BoundedExpansion).eval p x y 1 1 = 1 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 1
  have h2 : (2 : BoundedExpansion).eval p x y 1 1 = 2 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 2
  have h3 : (3 : BoundedExpansion).eval p x y 1 1 = 3 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 3
  have h4 : (4 : BoundedExpansion).eval p x y 1 1 = 4 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 4
  have h6 : (6 : BoundedExpansion).eval p x y 1 1 = 6 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 6
  have h8 : (8 : BoundedExpansion).eval p x y 1 1 = 8 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat] using eval_bounded_nat p x y (1 : R) (1 : R) 8
  cases k <;> simp only [rawFormula, scaledFormula, eval_bounded_add, eval_bounded_sub,
    eval_bounded_mul, eval_bounded_pow, eval_bounded_single, h1, h2, h3, h4, h6, h8,
    Int.cast_one, pow_zero, pow_one, one_mul, mul_one]

end Semantics

private def Exponents.index (e : Exponents) : ℕ := e.p + 8*e.x + 64*e.y

private def Exponents.decode (i : ℕ) : Exponents := ⟨i % 8, i / 8 % 8, i / 64, 0, 0⟩

private def radixBounds : Exponents := ⟨7, 7, 32, 0, 0⟩

private theorem Exponents.decode_index (e : Exponents) (h : e.bounded radixBounds) :
    decode e.index = e := by
  rcases e with ⟨d, x, y, u, v⟩
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
    (packedPolynomial ts).eval b = evalTerms b (b^8) (b^64) 1 1 ts := by
  induction ts with
  | nil => simp [packedPolynomial, evalTerms]
  | cons t ts ih =>
    change (monomial t.exponents.index t.coefficient + packedPolynomial ts).eval b =
      t.eval b (b^8) (b^64) 1 1 + evalTerms b (b^8) (b^64) 1 1 ts
    rw [eval_add, eval_monomial, ih]
    congr 1
    simp only [Term.eval, Int.cast_id, Exponents.index, pow_add, pow_mul, one_pow, mul_one,
      mul_assoc]

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

/-- At this radix the two opposite differences pass the same zero mask.
The degree can be chosen separately for each difference. -/
private theorem nonneg_coeff_of_zero_eval (P : ℤ[X])
    (hb : ∀ i, |P.coeff i| < 2^31) (he : P.eval (2^32) = 0) :
    ∀ i, 0 ≤ P.coeff i := by
  apply DimThree.PackedCheck.coeff_nonneg_of_polynomial_mask P
    (n := P.natDegree+1) (w := 31) (Nat.lt_succ_self _)
  · intro i
    exact ⟨(abs_lt.mp (hb i)).1.le, (abs_lt.mp (hb i)).2⟩
  · change (P.eval (2^32) + ↑(DimThree.PackedCheck.polynomialMask 31
      (P.natDegree+1))).toNat &&& DimThree.PackedCheck.polynomialMask 31
      (P.natDegree+1) = _
    rw [he, zero_add, Int.toNat_natCast]
    simp

private theorem packed_eq_of_eval_eq (P Q : ℤ[X])
    (hb : ∀ i, |(P-Q).coeff i| < 2^31) (he : P.eval (2^32) = Q.eval (2^32)) :
    P = Q := by
  have h₁ := nonneg_coeff_of_zero_eval (P-Q) hb (by rw [eval_sub, he, sub_self])
  have h₂ := nonneg_coeff_of_zero_eval (Q-P) (by
    intro i
    rw [coeff_sub, abs_sub_comm, ← coeff_sub]
    exact hb i) (by rw [eval_sub, he, sub_self])
  ext i
  have ha := h₁ i
  have hc := h₂ i
  rw [coeff_sub] at ha hc
  omega

private def tableTerms (m : ℤ) (gs : List RefinedBMV.ZeroSpectrum.Group) : List Term :=
  gs.flatMap fun g => g.coefficients.map fun a =>
    ⟨⟨a.1, g.bPower, g.yPower, 0, 0⟩, m*a.2⟩

private theorem eval_groupTerms {R : Type*} [CommRing R] (m : ℤ)
    (g : RefinedBMV.ZeroSpectrum.Group) (x b y : R) :
    evalTerms x b y 1 1
      (g.coefficients.map fun a => Term.mk ⟨a.1,g.bPower,g.yPower,0,0⟩ (m*a.2)) =
      (m : R) * g.eval x b y := by
  simp only [evalTerms, List.map_map, Function.comp_def, RefinedBMV.ZeroSpectrum.Group.eval, RefinedBMV.ZeroSpectrum.Group.weight]
  simp only [← List.sum_map_mul_right, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨d,c⟩ _
  simp only [Term.eval, Int.cast_mul, pow_zero, mul_one]
  ring

private theorem eval_tableTerms {R : Type*} [CommRing R] (m : ℤ)
    (gs : List RefinedBMV.ZeroSpectrum.Group) (x b y : R) :
    evalTerms x b y 1 1 (tableTerms m gs) = (m : R) * evalGroups x b y gs := by
  induction gs with
  | nil => simp [tableTerms, evalTerms, evalGroups]
  | cons g gs ih =>
    change evalTerms x b y 1 1
      ((g.coefficients.map fun a => Term.mk ⟨a.1,g.bPower,g.yPower,0,0⟩ (m*a.2)) ++
        tableTerms m gs) = (m : R) * (g.eval x b y + evalGroups x b y gs)
    unfold evalTerms
    rw [List.map_append, List.sum_append]
    change evalTerms x b y 1 1 _ + evalTerms x b y 1 1 (tableTerms m gs) = _
    rw [eval_groupTerms, ih, mul_add]

private def table (k : SignPolynomial) : List Term :=
  tableTerms (k.multiplier : ℤ) k.groups

private def fits (t : Term) : Bool := decide (t.exponents.bounded radixBounds)

private def radix : ℤ := 2^32

-- The bound on the raw expression uses only the degree and mass fields.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem raw_bounds (k : SignPolynomial) :
    (rawFormula k).degree.bounded radixBounds ∧ (rawFormula k).mass ≤ 300000000 := by
  cases k <;> decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem table_bounds (k : SignPolynomial) :
    (table k).all fits = true ∧ coeffMass (table k) ≤ 90000000 := by
  cases k <;> decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
/-- The group powers are evaluated once per rate by evalGroups. This equality
checks the complete scaled sparse coefficient table against the factored expression. -/
private theorem packed_identity (k : SignPolynomial) :
    (k.multiplier : ℤ) * evalGroups radix (radix^8) (radix^64) k.groups =
      scaledFormula k radix (radix^8) (radix^64) := by
  cases k <;> decide +kernel

theorem zeroSpectrum_matches_scaled (k : SignPolynomial) (x b y : ℝ) :
    (k.multiplier : ℝ) * evalGroups x b y k.groups = scaledFormula k x b y := by
  have ht : ∀ t ∈ table k, t.exponents.bounded radixBounds := by
    intro t hm
    simpa only [fits, decide_eq_true_eq] using
      List.all_eq_true.mp (table_bounds k).1 t hm
  have hr : ∀ t ∈ (rawFormula k).terms, t.exponents.bounded radixBounds :=
    fun t h => Exponents.bounded_trans ((rawFormula k).term_bound t h) (raw_bounds k).1
  have hrawMass := (rawFormula k).mass_bound.trans (raw_bounds k).2
  have hsmall (i : ℕ) :
      |(packedPolynomial (table k) - packedPolynomial (rawFormula k).terms).coeff i| < 2^31 := by
    rw [coeff_sub]
    calc
      _ ≤ |(packedPolynomial (table k)).coeff i| +
          |(packedPolynomial (rawFormula k).terms).coeff i| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le ((packedPolynomial (table k)).coeff i)
                (-((packedPolynomial (rawFormula k).terms).coeff i))
      _ ≤ 90000000 + 300000000 :=
        add_le_add ((packedPolynomial_coeff_bound _ _).trans (table_bounds k).2)
          ((packedPolynomial_coeff_bound _ _).trans hrawMass)
      _ < (2 : ℤ)^31 := by decide +kernel
  have he :
      (packedPolynomial (table k)).eval radix =
        (packedPolynomial (rawFormula k).terms).eval radix := by
    rw [eval_packedPolynomial, eval_packedPolynomial]
    change evalTerms radix (radix^8) (radix^64) 1 1 (tableTerms (k.multiplier : ℤ) k.groups) =
      (rawFormula k).eval radix (radix^8) (radix^64) 1 1
    rw [eval_tableTerms, eval_rawFormula]
    exact_mod_cast packed_identity k
  have hpack := packed_eq_of_eval_eq _ _ hsmall he
  have h := congrArg (fun P : ℤ[X] => P.sum
    (fun i c => (Term.mk (Exponents.decode i) c).eval x b y (1 : ℝ) 1)) hpack
  rw [eval_unpackedPolynomial x b y 1 1 _ ht,
    eval_unpackedPolynomial x b y 1 1 _ hr] at h
  change evalTerms x b y 1 1 (tableTerms (k.multiplier : ℤ) k.groups) =
    (rawFormula k).eval x b y 1 1 at h
  rw [eval_tableTerms, eval_rawFormula] at h
  simpa only [Int.cast_natCast] using h

/-- Evaluation of each original denominator-cleared table is exactly the
corresponding closed polynomial, uniformly in its three real variables. -/
theorem zeroSpectrum_matches_closed (k : SignPolynomial) (p b y : ℝ) :
    evalGroups (p-1) b y k.groups = (k.denominator : ℝ) * k.closed p b y := by
  have h := zeroSpectrum_matches_scaled k (p-1) b y
  rw [scaledFormula_eq] at h
  have hm : (k.multiplier : ℝ) ≠ 0 := by cases k <;> norm_num [SignPolynomial.multiplier]
  apply mul_left_cancel₀ hm
  simpa only [mul_assoc] using h

end RefinedBMV.DividedDifference.SparseExpansion
