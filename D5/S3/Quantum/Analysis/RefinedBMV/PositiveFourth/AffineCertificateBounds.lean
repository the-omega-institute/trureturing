/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineCertificateBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Static degree and coefficient bounds for grouped mixed affine origins. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks

/-! Bounds on signed radix digits from the coefficient mass and affine rates. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

/-- The L1 mass of a coefficient list in ascending degree order. -/
def coefficientMass (cs : List ℤ) : ℤ := (cs.map fun a => |a|).sum

theorem coefficientMass_nonneg (cs : List ℤ) : 0 ≤ coefficientMass cs := by
  induction cs with
  | nil => simp [coefficientMass]
  | cons a cs ih =>
    change 0 ≤ |a| + coefficientMass cs
    exact add_nonneg (abs_nonneg a) ih

/-- Each coefficient is bounded in absolute value by the mass of its list. -/
theorem coeff_abs_coefficientPolynomial (cs : List ℤ) (j : ℕ) :
    |(coefficientPolynomial cs).coeff j| ≤ coefficientMass cs := by
  induction cs generalizing j with
  | nil => simp [coefficientPolynomial, coefficientMass]
  | cons a cs ih =>
    change |(C a + X * coefficientPolynomial cs).coeff j| ≤ |a| + coefficientMass cs
    cases j with
    | zero =>
      rw [coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
      exact le_add_of_nonneg_right (coefficientMass_nonneg cs)
    | succ j =>
      rw [coeff_add, coeff_C_of_ne_zero (Nat.succ_ne_zero j), coeff_X_mul, zero_add]
      exact (ih j).trans (le_add_of_nonneg_left (abs_nonneg a))

/-- The degree bound also covers the empty list and trailing zero coefficients. -/
theorem natDegree_coefficientPolynomial_le (cs : List ℤ) :
    (coefficientPolynomial cs).natDegree ≤ cs.length - 1 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a cs ih =>
    cases cs with
    | nil => simp [coefficientPolynomial]
    | cons b bs =>
      simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
      rw [coefficientPolynomial]
      apply natDegree_add_le_of_degree_le
      · simp
      · simpa only [Nat.add_comm 1] using natDegree_mul_le_of_le natDegree_X_le ih

def Certificate.mass (c : Certificate) : ℤ :=
  (c.terms.map fun t => coefficientMass t.2.coefficients).sum

/-- The combined length of the two longest strict prefixes. -/
def Certificate.maxPrefixLength (c : Certificate) : ℕ :=
  (c.rootsU.length - 1) + (c.rootsV.length - 1)

private theorem abs_nat_difference_le (a b B : ℕ) (ha : a ≤ B) (hb : b ≤ B) :
    |(b : ℤ) - a| ≤ (B : ℤ) := by
  rw [abs_le]
  constructor <;> omega

private theorem rateDifference_bound (B : ℕ) (a b : AffineRate)
    (ha : a.1 ≤ B ∧ a.2 ≤ B) (hb : b.1 ≤ B ∧ b.2 ≤ B) :
    |(rateDifference a b).1| + |(rateDifference a b).2| ≤ 2 * (B : ℤ) := by
  simpa only [rateDifference, two_mul] using
    add_le_add (abs_nat_difference_le a.1 b.1 B ha.1 hb.1)
      (abs_nat_difference_le a.2 b.2 B ha.2 hb.2)

/-- Check the degree budget, total coefficient mass, and the common coordinate
cap `B` on the two root lists. Rate membership is checked separately by
`checkRates`. -/
def Certificate.staticCheck (c : Certificate) (d B width digits : ℕ) : Bool :=
  decide (1 ≤ B ∧ d + c.maxPrefixLength < digits ∧
    c.mass * (2 * (B : ℤ)) ^ c.maxPrefixLength < (2 : ℤ) ^ width) &&
    c.terms.all (fun t => decide (t.2.coefficients.length ≤ d + 1)) &&
    c.rootsU.all (fun a => decide (a.1 ≤ B ∧ a.2 ≤ B)) &&
    c.rootsV.all (fun a => decide (a.1 ≤ B ∧ a.2 ≤ B))

/-- A static check supplies the signed radix bounds required by the mixed-origin
row checks. The root scans bound every affine difference by `2 * B`. -/
theorem Certificate.bounds_of_staticCheck (c : Certificate) (d B width digits : ℕ)
    (hrates : c.checkRates = true)
    (hstatic : c.staticCheck d B width digits = true) :
    ∀ k < c.rootsU.length, ∀ l < c.rootsV.length,
      let P := c.origin k l
      P.natDegree < digits ∧
        (∀ j, -(2 : ℤ) ^ width ≤ P.coeff j ∧ P.coeff j < (2 : ℤ) ^ width) := by
  simp only [Certificate.staticCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hstatic
  obtain ⟨⟨⟨⟨hB, hdigit, hsmall⟩, hlength⟩, hU⟩, hV⟩ := hstatic
  let size (i : c.Index) := coefficientMass (c.terms.get i).2.coefficients
  have hsize (i : c.Index) : 0 ≤ size i := coefficientMass_nonneg _
  have hweight (i : c.Index) (j : ℕ) : |(c.weight i).coeff j| ≤ size i :=
    coeff_abs_coefficientPolynomial _ _
  have hdegree (i : c.Index) : (c.weight i).natDegree ≤ d := by
    have hi := hlength (c.terms.get i) (List.get_mem c.terms i)
    unfold Certificate.weight
    exact (natDegree_coefficientPolynomial_le _).trans (by omega)
  have hmass_eq : (∑ i : c.Index, size i) = c.mass := by
    change (∑ i : Fin c.terms.length, coefficientMass (c.terms.get i).2.coefficients) =
      (c.terms.map fun t => coefficientMass t.2.coefficients).sum
    rw [← List.sum_ofFn]
    exact congrArg List.sum
      (List.ofFn_getElem_eq_map c.terms (fun t => coefficientMass t.2.coefficients))
  have hmass : 0 ≤ c.mass := by
    rw [← hmass_eq]
    exact Finset.sum_nonneg fun i _ => hsize i
  have hcap : 1 ≤ 2 * (B : ℤ) := by omega
  intro k hk l hl
  have hfactorU (i : c.Index) (a : AffineRate) (ha : a ∈ c.rootsU.take k) :
      |(rateDifference (c.rateU i) a).1| + |(rateDifference (c.rateU i) a).2| ≤
        2 * (B : ℤ) :=
    rateDifference_bound B _ _ (hU _ (c.rates_mem hrates i).1)
      (hU _ (List.mem_of_mem_take ha))
  have hfactorV (i : c.Index) (a : AffineRate) (ha : a ∈ c.rootsV.take l) :
      |(rateDifference (c.rateV i) a).1| + |(rateDifference (c.rateV i) a).2| ≤
        2 * (B : ℤ) :=
    rateDifference_bound B _ _ (hV _ (c.rates_mem hrates i).2)
      (hV _ (List.mem_of_mem_take ha))
  obtain ⟨hcoeff, hdeg⟩ := mixedOrigin_bounds c.weight c.rateU c.rateV
    (c.rootsU.take k) (c.rootsV.take l) size d (2 * (B : ℤ))
      hsize (by omega) hweight hdegree hfactorU hfactorV
  rw [hmass_eq] at hcoeff
  have hlen : (c.rootsU.take k).length + (c.rootsV.take l).length ≤ c.maxPrefixLength := by
    simp only [List.length_take, Certificate.maxPrefixLength]
    omega
  constructor
  · change (mixedOrigin c.weight c.rateU c.rateV (c.rootsU.take k)
      (c.rootsV.take l)).natDegree < digits
    omega
  · intro j
    have ha := (hcoeff j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hcap hlen) hmass)
    have hstrict := ha.trans_lt hsmall
    exact ⟨(abs_lt.mp hstrict).1.le, (abs_lt.mp hstrict).2⟩

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
