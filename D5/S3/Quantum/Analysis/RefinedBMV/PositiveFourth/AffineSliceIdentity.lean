/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineSliceIdentity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certify an affine polynomial identity using four-variable radix evaluations. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTablePacking
import Mathlib.Algebra.Polynomial.Roots

/-! The last variable is evaluated at `degree + 1` distinct integers.
The root bound gives the full polynomial identity. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion
open Polynomial

private def specializeTerm (j : ℕ) (t : Term) : Term :=
  ⟨{ t.exponents with v := 0 }, t.coefficient * (j : ℤ) ^ t.exponents.v⟩

def specializeLast (j : ℕ) (ts : List Term) : List Term := ts.map (specializeTerm j)

private theorem specializeTerm_eval {R : Type*} [CommRing R]
    (j : ℕ) (t : Term) (p x y u : R) :
    (specializeTerm j t).eval p x y u 1 = t.eval p x y u (j : R) := by
  simp only [specializeTerm, Term.eval, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    pow_zero, mul_one]
  ring

theorem evalTerms_specializeLast {R : Type*} [CommRing R]
    (j : ℕ) (ts : List Term) (p x y u : R) :
    evalTerms p x y u 1 (specializeLast j ts) = evalTerms p x y u (j : R) ts := by
  simp only [evalTerms, specializeLast, List.map_map, Function.comp_def, specializeTerm_eval]

private theorem specializeLast_fits (j : ℕ) (sizes : Exponents) (ts : List Term)
    (h : ∀ t ∈ ts, Fits sizes t.exponents) :
    ∀ t ∈ specializeLast j ts, Fits ⟨sizes.p, sizes.x, sizes.y, sizes.u, 1⟩ t.exponents := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨a, ha, rfl⟩
  have hz := h a ha
  exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, by decide⟩

open private coeffMass from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

/-- Substituting an integer multiplies the coefficient mass by at most
the top allowed power of the largest sample. -/
theorem specializeLast_mass_le (j limit degree : ℕ) (ts : List Term)
    (hj : j ≤ limit) (hlimit : 1 ≤ limit) (hts : ∀ t ∈ ts, t.exponents.v ≤ degree) :
    coefficientMass (specializeLast j ts) ≤
      (limit : ℤ) ^ degree * coefficientMass ts := by
  have hj' : (j : ℤ) ≤ (limit : ℤ) := by exact_mod_cast hj
  have hlimit' : (1 : ℤ) ≤ (limit : ℤ) := by exact_mod_cast hlimit
  induction ts with
  | nil => simp [specializeLast, coefficientMass, coeffMass]
  | cons t ts ih =>
    have hd := hts t (by simp)
    have hpow : (j : ℤ) ^ t.exponents.v ≤ (limit : ℤ) ^ degree :=
      (pow_le_pow_left₀ (by positivity) hj' _).trans (pow_le_pow_right₀ hlimit' hd)
    have hh := mul_le_mul_of_nonneg_right hpow (abs_nonneg t.coefficient)
    have ht := ih (fun a ha => hts a (by simp [ha]))
    change |t.coefficient * (j : ℤ) ^ t.exponents.v| +
        coefficientMass (specializeLast j ts) ≤
      (limit : ℤ) ^ degree * (|t.coefficient| + coefficientMass ts)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℤ) ^ t.exponents.v),
      mul_add, mul_comm |t.coefficient|]
    exact add_le_add hh ht

private noncomputable def lastPolynomial (ts : List Term) (p x y u : ℝ) : ℝ[X] :=
  (ts.map fun t => monomial t.exponents.v (t.eval p x y u 1)).sum

private theorem lastPolynomial_eval (ts : List Term) (p x y u v : ℝ) :
    (lastPolynomial ts p x y u).eval v = evalTerms p x y u v ts := by
  induction ts with
  | nil => simp [lastPolynomial, evalTerms]
  | cons t ts ih =>
    change (monomial t.exponents.v (t.eval p x y u 1) + lastPolynomial ts p x y u).eval v =
      t.eval p x y u v + evalTerms p x y u v ts
    rw [eval_add, eval_monomial, ih]
    simp [Term.eval, mul_assoc]

private theorem lastPolynomial_natDegree_lt (ts : List Term) (p x y u : ℝ) (n : ℕ)
    (hn : 0 < n) (h : ∀ t ∈ ts, t.exponents.v < n) :
    (lastPolynomial ts p x y u).natDegree < n := by
  induction ts with
  | nil => simpa [lastPolynomial] using hn
  | cons t ts ih =>
    change (monomial t.exponents.v (t.eval p x y u 1) + lastPolynomial ts p x y u).natDegree < n
    exact (natDegree_add_le ..).trans_lt <| max_lt
      ((natDegree_monomial_le _).trans_lt (h t (by simp)))
      (ih (fun a ha => h a (by simp [ha])))

private theorem eq_of_eval_nat_lt (P Q : ℝ[X]) (n : ℕ)
    (hdP : P.natDegree < n) (hdQ : Q.natDegree < n)
    (he : ∀ j < n, P.eval (j : ℝ) = Q.eval (j : ℝ)) : P = Q := by
  classical
  by_contra hn
  let D := P - Q
  have hD : D ≠ 0 := sub_ne_zero.mpr hn
  let points := (Finset.range n).image (fun j : ℕ => (j : ℝ))
  have hsub : points ⊆ D.roots.toFinset := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    rw [Multiset.mem_toFinset, mem_roots hD]
    change (P - Q).eval (j : ℝ) = 0
    rw [eval_sub, he j (Finset.mem_range.mp hj), sub_self]
  have hcard : points.card = n := by
    simp only [points, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hcount := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le).trans (card_roots' D))
  rw [hcard] at hcount
  exact (not_lt_of_ge hcount) ((natDegree_sub_le P Q).trans_lt (max_lt hdP hdQ))

/-- Verifying the four-variable packed equality at all required integer
arguments supplies the five-variable polynomial identity over the reals. -/
theorem evalTerms_eq_of_packedSamples (sizes : Exponents) (width : ℕ) (as bs : List Term)
    (p x y u v : ℝ) (hv : 0 < sizes.v)
    (ha : ∀ a ∈ as, Fits sizes a.exponents) (hb : ∀ b ∈ bs, Fits sizes b.exponents)
    (hmass : ∀ j < sizes.v,
      coefficientMass (specializeLast j as) + coefficientMass (specializeLast j bs) <
        (2 : ℤ) ^ width)
    (hcheck : ∀ j < sizes.v,
      let rows : Exponents := ⟨sizes.p, sizes.x, sizes.y, sizes.u, 1⟩
      packedEval rows (radix width) (specializeLast j as) =
        packedEval rows (radix width) (specializeLast j bs)) :
    evalTerms p x y u v as = evalTerms p x y u v bs := by
  rw [← lastPolynomial_eval as p x y u v, ← lastPolynomial_eval bs p x y u v]
  apply congrArg (Polynomial.eval v)
  apply eq_of_eval_nat_lt _ _ sizes.v
  · exact lastPolynomial_natDegree_lt as p x y u sizes.v hv (fun t ht => (ha t ht).2.2.2.2)
  · exact lastPolynomial_natDegree_lt bs p x y u sizes.v hv (fun t ht => (hb t ht).2.2.2.2)
  · intro j hj
    rw [lastPolynomial_eval as, lastPolynomial_eval bs, ← evalTerms_specializeLast j as,
      ← evalTerms_specializeLast j bs]
    exact evalTerms_eq_of_packedEval_eq ⟨sizes.p, sizes.x, sizes.y, sizes.u, 1⟩
      width (specializeLast j as) (specializeLast j bs) p x y u 1
      (specializeLast_fits j sizes as ha) (specializeLast_fits j sizes bs hb)
      (hmass j hj) (hcheck j hj)

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open RefinedBMV.DividedDifference.SparseExpansion
open private termExponents coefficientTerms from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTableTerms

private def sampleColumn (start j : ℕ) (col : Column) : Column :=
  ((col.1.1 - start * col.1.2, 0), col.2.map fun g =>
    { g with coefficients := g.coefficients.map (fun a => a * (j : ℤ) ^ col.1.2) })

/-- Specialize the last coordinate while keeping the same grouped radix evaluation. -/
def Certificate.sampleTable (c : Certificate) (start j : ℕ) : Certificate :=
  ⟨c.rootsU, c.columns.map (sampleColumn start j)⟩

private theorem sample_coefficientTerms (start j degree : ℕ) (u v : AffineRate) (cs : List ℤ) :
    coefficientTerms start u (v.1 - start * v.2, 0) degree
      (cs.map (fun a => a * (j : ℤ) ^ v.2)) =
    AffineRadixIdentity.specializeLast j (coefficientTerms start u v degree cs) := by
  induction cs generalizing degree with
  | nil => rfl
  | cons a cs ih =>
    change ⟨termExponents start u (v.1 - start * v.2, 0) degree,
        a * (j : ℤ) ^ v.2⟩ ::
          coefficientTerms start u (v.1 - start * v.2, 0) (degree + 1)
            (cs.map (fun x => x * (j : ℤ) ^ v.2)) =
        AffineRadixIdentity.specializeTerm j ⟨termExponents start u v degree, a⟩ ::
          AffineRadixIdentity.specializeLast j (coefficientTerms start u v (degree + 1) cs)
    rw [ih]
    simp [AffineRadixIdentity.specializeTerm, termExponents]

theorem Certificate.sampleTable_terms (c : Certificate) (start j : ℕ) :
    (c.sampleTable start j).tableTerms start =
      AffineRadixIdentity.specializeLast j (c.tableTerms start) := by
  simp only [Certificate.sampleTable, Certificate.tableTerms, Certificate.terms, sampleColumn,
    AffineRadixIdentity.specializeLast, List.flatMap_map, List.flatMap_assoc, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply congrArg (fun f : Column → List Term => c.columns.flatMap f)
  funext col
  apply congrArg (fun f : Group → List Term => col.2.flatMap f)
  funext g
  exact sample_coefficientTerms start j 0 g.rateU col.1 g.coefficients

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
