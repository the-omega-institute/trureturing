/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineRadixIdentity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed-radix identification of five-variable sparse polynomial evaluations. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask

/-! A single integer evaluation certifies a sparse polynomial identity when
the five exponent digits and the signed coefficient mass fit their radices. -/

open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion

open private BoundedExpansion BoundedExpansion.eval BoundedExpansion.degree BoundedExpansion.mass
  BoundedExpansion.terms BoundedExpansion.term_bound BoundedExpansion.mass_bound
  Exponents.bounded coeffMass from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

/-- Each exponent is a digit strictly below the corresponding radix size. -/
def Fits (sizes e : Exponents) : Prop :=
  e.p < sizes.p ∧ e.x < sizes.x ∧ e.y < sizes.y ∧ e.u < sizes.u ∧ e.v < sizes.v

instance (sizes e : Exponents) : Decidable (Fits sizes e) := by
  unfold Fits
  infer_instance

/-- The coefficient radix with `width` bits below the sign-check bit. -/
def radix (width : ℕ) : ℤ := 2 ^ (width + 1)

/-- The sum of the absolute values of the integer coefficients. -/
abbrev coefficientMass (ts : List Term) : ℤ := coeffMass ts

/-- The mixed-radix index in the variable order `p, x, y, u, v`. -/
def index (sizes e : Exponents) : ℕ :=
  e.p + sizes.p * e.x + (sizes.p * sizes.x) * e.y +
    (sizes.p * sizes.x * sizes.y) * e.u + (sizes.p * sizes.x * sizes.y * sizes.u) * e.v

/-- Recover the five digits by successive quotient and remainder operations. -/
def decode (sizes : Exponents) (i : ℕ) : Exponents :=
  let i₁ := i / sizes.p
  let i₂ := i₁ / sizes.x
  let i₃ := i₂ / sizes.y
  let i₄ := i₃ / sizes.u
  ⟨i % sizes.p, i₁ % sizes.x, i₂ % sizes.y, i₃ % sizes.u, i₄ % sizes.v⟩

private theorem index_eq_horner (sizes e : Exponents) :
    index sizes e =
      e.p + sizes.p * (e.x + sizes.x * (e.y + sizes.y * (e.u + sizes.u * e.v))) := by
  unfold index
  ring

private theorem digit_div {digit size : ℕ} (h : digit < size) (tail : ℕ) :
    (digit + size * tail) / size = tail := by
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt h), Nat.div_eq_of_lt h, zero_add]

private theorem digit_mod {digit size : ℕ} (h : digit < size) (tail : ℕ) :
    (digit + size * tail) % size = digit := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem decode_index (sizes e : Exponents) (h : Fits sizes e) :
    decode sizes (index sizes e) = e := by
  unfold Fits at h
  obtain ⟨hp, hx, hy, hu, hv⟩ := h
  cases e
  simp only [decode, index_eq_horner, digit_div hp, digit_div hx, digit_div hy, digit_div hu,
    digit_mod hp, digit_mod hx, digit_mod hy, digit_mod hu, Nat.mod_eq_of_lt hv]

/-- Evaluate at the five powers of `b` given by the mixed-radix strides. -/
def packedEval (sizes : Exponents) (b : ℤ) (ts : List Term) : ℤ :=
  evalTerms b (b ^ sizes.p) (b ^ (sizes.p * sizes.x))
    (b ^ (sizes.p * sizes.x * sizes.y)) (b ^ (sizes.p * sizes.x * sizes.y * sizes.u)) ts

private noncomputable def packedPolynomial (sizes : Exponents) (ts : List Term) : ℤ[X] :=
  (ts.map fun t => monomial (index sizes t.exponents) t.coefficient).sum

private theorem packedPolynomial_coeff_bound (sizes : Exponents) (ts : List Term) (i : ℕ) :
    |(packedPolynomial sizes ts).coeff i| ≤ coefficientMass ts := by
  induction ts with
  | nil => simp [packedPolynomial, coefficientMass, coeffMass]
  | cons t ts ih =>
    change |(monomial (index sizes t.exponents) t.coefficient +
      packedPolynomial sizes ts).coeff i| ≤ |t.coefficient| + coefficientMass ts
    rw [coeff_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rw [coeff_monomial]
    split <;> simp

private theorem eval_packedPolynomial (sizes : Exponents) (ts : List Term) (b : ℤ) :
    (packedPolynomial sizes ts).eval b = packedEval sizes b ts := by
  induction ts with
  | nil => simp [packedPolynomial, packedEval, evalTerms]
  | cons t ts ih =>
    change (monomial (index sizes t.exponents) t.coefficient +
      packedPolynomial sizes ts).eval b =
      t.eval b (b ^ sizes.p) (b ^ (sizes.p * sizes.x))
        (b ^ (sizes.p * sizes.x * sizes.y)) (b ^ (sizes.p * sizes.x * sizes.y * sizes.u)) +
      packedEval sizes b ts
    rw [eval_add, eval_monomial, ih]
    simp only [Term.eval, Int.cast_id, index, pow_add, ← pow_mul]

private theorem eval_unpackedPolynomial {R : Type*} [CommRing R] (sizes : Exponents)
    (p x y u v : R) (ts : List Term) (h : ∀ t ∈ ts, Fits sizes t.exponents) :
    (packedPolynomial sizes ts).sum (fun i c => (Term.mk (decode sizes i) c).eval p x y u v) =
      evalTerms p x y u v ts := by
  induction ts with
  | nil => simp [packedPolynomial, evalTerms]
  | cons t ts ih =>
    change (monomial (index sizes t.exponents) t.coefficient + packedPolynomial sizes ts).sum
      _ = _
    rw [sum_add_index _ _ _ (by simp [Term.eval]) (by simp [Term.eval, add_mul]),
      sum_monomial_index _ _ (by simp [Term.eval]), ih (fun a ha => h a (by simp [ha])),
      decode_index sizes _ (h t (by simp))]
    rfl

private theorem nonneg_coeff_of_zero_eval (width : ℕ) (P : ℤ[X])
    (hb : ∀ i, |P.coeff i| < (2 : ℤ) ^ width) (he : P.eval (radix width) = 0) :
    ∀ i, 0 ≤ P.coeff i := by
  apply DimThree.PackedCheck.coeff_nonneg_of_polynomial_mask P
    (n := P.natDegree + 1) (w := width) (Nat.lt_succ_self _)
  · intro i
    exact ⟨(abs_lt.mp (hb i)).1.le, (abs_lt.mp (hb i)).2⟩
  · let mask := DimThree.PackedCheck.polynomialMask width (P.natDegree + 1)
    change (P.eval (radix width) + (mask : ℤ)).toNat &&& mask = mask
    rw [he, zero_add, Int.toNat_natCast]
    simp

private theorem packed_eq_of_eval_eq (width : ℕ) (P Q : ℤ[X])
    (hb : ∀ i, |(P - Q).coeff i| < (2 : ℤ) ^ width)
    (he : P.eval (radix width) = Q.eval (radix width)) : P = Q := by
  have hpq := nonneg_coeff_of_zero_eval width (P - Q) hb (by rw [eval_sub, he, sub_self])
  have hqp := nonneg_coeff_of_zero_eval width (Q - P) (by
    intro i
    rw [coeff_sub, abs_sub_comm, ← coeff_sub]
    exact hb i) (by rw [eval_sub, he, sub_self])
  ext i
  have h₁ := hpq i
  have h₂ := hqp i
  rw [coeff_sub] at h₁ h₂
  omega

/-- A checked integer evaluation and a strict bound on the combined coefficient
mass give equality of the two sparse evaluations in every commutative ring. -/
theorem evalTerms_eq_of_packedEval_eq {R : Type*} [CommRing R]
    (sizes : Exponents) (width : ℕ) (as bs : List Term) (p x y u v : R)
    (ha : ∀ t ∈ as, Fits sizes t.exponents) (hb : ∀ t ∈ bs, Fits sizes t.exponents)
    (hmass : coefficientMass as + coefficientMass bs < (2 : ℤ) ^ width)
    (he : packedEval sizes (radix width) as = packedEval sizes (radix width) bs) :
    evalTerms p x y u v as = evalTerms p x y u v bs := by
  have hsmall (i : ℕ) :
      |(packedPolynomial sizes as - packedPolynomial sizes bs).coeff i| < (2 : ℤ) ^ width := by
    rw [coeff_sub]
    calc
      _ ≤ |(packedPolynomial sizes as).coeff i| + |(packedPolynomial sizes bs).coeff i| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((packedPolynomial sizes as).coeff i) (-((packedPolynomial sizes bs).coeff i))
      _ ≤ coefficientMass as + coefficientMass bs :=
        add_le_add (packedPolynomial_coeff_bound sizes as i) (packedPolynomial_coeff_bound sizes bs i)
      _ < (2 : ℤ) ^ width := hmass
  have hpack := packed_eq_of_eval_eq width _ _ hsmall
    (by simpa only [eval_packedPolynomial] using he)
  have h := congrArg (fun P : ℤ[X] => P.sum
    (fun i c => (Term.mk (decode sizes i) c).eval p x y u v)) hpack
  rw [eval_unpackedPolynomial sizes p x y u v as ha,
    eval_unpackedPolynomial sizes p x y u v bs hb] at h
  exact h

/-- On the circuit side, the existing expansion bounds discharge the degree and
mass hypotheses using just the `degree` and `mass` fields. -/
theorem evalTerms_eq_boundedExpansion_of_packedEval_eq {R : Type*} [CommRing R]
    (sizes : Exponents) (width : ℕ) (ts : List Term) (a : BoundedExpansion) (p x y u v : R)
    (ht : ∀ t ∈ ts, Fits sizes t.exponents) (hdeg : Fits sizes (BoundedExpansion.degree a))
    (hmass : coefficientMass ts + BoundedExpansion.mass a < (2 : ℤ) ^ width)
    (he : packedEval sizes (radix width) ts = packedEval sizes (radix width)
      (BoundedExpansion.terms a)) :
    evalTerms p x y u v ts = BoundedExpansion.eval p x y u v a := by
  change evalTerms p x y u v ts = evalTerms p x y u v (BoundedExpansion.terms a)
  refine evalTerms_eq_of_packedEval_eq sizes width ts (BoundedExpansion.terms a) p x y u v
    ht ?_ ?_ he
  · intro t ht'
    have hb := BoundedExpansion.term_bound a t ht'
    unfold Exponents.bounded at hb
    unfold Fits at hdeg ⊢
    obtain ⟨bp, bx, bY, bu, bv⟩ := hb
    obtain ⟨dp, dx, dy, du, dv⟩ := hdeg
    exact ⟨bp.trans_lt dp, bx.trans_lt dx, bY.trans_lt dy, bu.trans_lt du, bv.trans_lt dv⟩
  · exact (add_le_add le_rfl (BoundedExpansion.mass_bound a)).trans_lt hmass

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
