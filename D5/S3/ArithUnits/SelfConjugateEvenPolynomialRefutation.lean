/- GID: D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation
   generality: I
   mirror-B: D5/B/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.claim; result=D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.result; claim=D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.claim
   digest: A uniform characteristic-two family refutes the sparse-power self-conjugacy assertion. -/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.ZMod.Basic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.SelfConjugateEvenPolynomialRefutation

open Polynomial

abbrev F2 := ZMod 2

def U : F2[X] := X ^ 4 + X ^ 2

def P (r : ℕ) : F2[X] := U ^ r

private theorem u_monic : U.Monic := by
  exact (monic_X_pow 4).add_of_left (by norm_num)

private theorem u_degree : U.natDegree = 4 := by
  apply (natDegree_add_eq_left_of_natDegree_lt (p := (X : F2[X]) ^ 4)
    (q := (X : F2[X]) ^ 2) (by norm_num)).trans
  exact natDegree_X_pow 4

private theorem p_monic (r : ℕ) : (P r).Monic := u_monic.pow r

private theorem p_degree (r : ℕ) : (P r).natDegree = 4 * r := by
  rw [P, u_monic.natDegree_pow, u_degree, Nat.mul_comm]

private theorem u_invariant : U.comp (X + 1) = U := by
  have h2 : ((X : F2[X]) + 1) ^ 2 = X ^ 2 + 1 := by
    simpa using add_pow_char (X : F2[X]) 1 2
  have h4 : ((X : F2[X]) + 1) ^ 4 = X ^ 4 + 1 := by
    simpa using add_pow_char_pow (X : F2[X]) 1 2 2
  have hone : (1 + 1 : F2[X]) = 0 := CharTwo.add_self_eq_zero 1
  simp only [U, add_comp, pow_comp, X_comp, h2, h4]
  rw [add_add_add_comm, hone, add_zero]

private theorem p_invariant (r : ℕ) : (P r).comp (X + 1) = P r := by
  simp only [P, pow_comp, u_invariant]

private theorem p_expand (r : ℕ) :
    P r = expand F2 2 (((X : F2[X]) ^ 2 + X) ^ r) := by
  simp only [expand_eq_comp_X_pow, pow_comp, add_comp, X_comp, P, U]
  congr 1
  ring

private theorem p_even_exponents (r : ℕ) :
    ∀ n ∈ (P r).support, Even n := by
  intro n hn
  apply even_iff_two_dvd.mpr
  by_contra h
  have hc : (P r).coeff n = 0 := by
    rw [p_expand, coeff_expand (by decide : 0 < 2), ite_eq_right h]
  exact (mem_support_iff.mp hn) hc

private theorem p_constant (r : ℕ) (hr : 0 < r) : (P r).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [P, U, CharTwo.add_self_eq_zero, hr.ne']

private theorem p_eval_one (r : ℕ) (hr : 0 < r) : (P r).eval 1 = 0 := by
  simp [P, U, CharTwo.add_self_eq_zero, hr.ne']

private theorem p_even_support (r : ℕ) (hr : 0 < r) : Even (P r).support.card := by
  classical
  have hc : ∀ n ∈ (P r).support, (P r).coeff n = 1 := by
    intro n hn
    have hne := mem_support_iff.mp hn
    have h01 : ∀ a : F2, a = 0 ∨ a = 1 := by decide
    exact (h01 _).resolve_left hne
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
    ((P r).support.card : F2) = ∑ _n ∈ (P r).support, (1 : F2) := by simp
    _ = ∑ n ∈ (P r).support, (P r).coeff n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hc n hn).symm
    _ = (P r).eval 1 := by simp [eval_eq_sum, Polynomial.sum]
    _ = 0 := p_eval_one r hr

private theorem degree_not_two_power (r : ℕ) (ho : Odd r) (hr : 3 ≤ r) (k : ℕ) :
    4 * r ≠ 2 ^ k := by
  intro heq
  have hd : r ∣ 2 ^ k := by rw [← heq]; exact dvd_mul_left r 4
  have hc : r.Coprime (2 ^ k) := (Nat.coprime_two_right.mpr ho).pow_right k
  have h1 : r = 1 := by
    have hg := hc.gcd_eq_one
    rwa [Nat.gcd_eq_left hd] at hg
  omega

private theorem p_nonrepresentation (r : ℕ) (ho : Odd r) (hr : 3 ≤ r) :
    ∀ (c : F2) (m : ℕ) (k : Fin m → ℕ),
      P r ≠ C c + ∑ i : Fin m, (X : F2[X]) ^ (2 ^ k i) := by
  classical
  intro c m k heq
  have hlead : (P r).coeff (4 * r) = 1 := by
    rw [← p_degree]
    exact (p_monic r).coeff_natDegree
  have hsparse : (C c + ∑ i : Fin m, (X : F2[X]) ^ (2 ^ k i)).coeff (4 * r) = 0 := by
    simp only [coeff_add, finsetSum_coeff, coeff_X_pow]
    simp [coeff_C, show 4 * r ≠ 0 by omega, degree_not_two_power r ho hr]
  have h := congrArg (fun f : F2[X] => f.coeff (4 * r)) heq
  rw [hlead, hsparse] at h
  exact one_ne_zero h

/-- All clauses concern formal polynomials in the one polynomial ring. -/
def FamilyEvent (r : ℕ) : Prop :=
  P r ≠ 0 ∧ (P r).Monic ∧ (P r).comp (X + 1) = P r ∧
  (∀ n ∈ (P r).support, Even n) ∧
  (P r).natDegree = 4 * r ∧ Even (P r).natDegree ∧
  (P r).coeff 0 = 0 ∧ Even (P r).support.card ∧
  (X : F2[X]) ∣ P r ∧ (P r).comp (-X) = P r ∧
  ∀ (c : F2) (m : ℕ) (k : Fin m → ℕ),
    P r ≠ C c + ∑ i : Fin m, (X : F2[X]) ^ (2 ^ k i)

private theorem family_event (r : ℕ) (ho : Odd r) (hr : 3 ≤ r) : FamilyEvent r := by
  have hpos : 0 < r := by omega
  have heven : Even (P r).natDegree := by
    rw [p_degree]
    exact ⟨2 * r, by omega⟩
  have hneg : (-X : F2[X]) = X := by
    exact CharTwo.neg_eq _
  exact ⟨(p_monic r).ne_zero, p_monic r, p_invariant r, p_even_exponents r,
    p_degree r, heven, p_constant r hpos, p_even_support r hpos,
    X_dvd_iff.mpr (p_constant r hpos), by rw [hneg, comp_X],
    p_nonrepresentation r ho hr⟩

inductive EvenReading where
  | exponents | degree | support | zeroConstant | divisibleByX | reflection

/-- The six conventional domains are alternatives, with no intended-reading assertion. -/
def Domain (e : EvenReading) (p : F2[X]) : Prop :=
  match e with
  | .exponents => ∀ n ∈ p.support, Even n
  | .degree => Even p.natDegree
  | .support => Even p.support.card
  | .zeroConstant => p.coeff 0 = 0
  | .divisibleByX => (X : F2[X]) ∣ p
  | .reflection => p.comp (-X) = p

/-- The source parity rule is imposed even though nonrepresentation needs no parity. -/
def SourceParity (p : F2[X]) (m : ℕ) : Prop :=
  (p.coeff 0 ≠ 0 → Odd m) ∧ (p.coeff 0 = 0 → Even m)

/-- Literal displayed sum, with natural indices and both prose parity branches. -/
def DisplayedRepresentation (p : F2[X]) : Prop :=
  ∃ (m : ℕ) (k : Fin m → ℕ),
    p = ∑ i : Fin m, (X : F2[X]) ^ (2 ^ k i) ∧ SourceParity p m

/-- Optional-constant robustness reading, kept distinct from the literal display. -/
def ConstantRepresentation (p : F2[X]) : Prop :=
  ∃ (c : F2) (m : ℕ) (k : Fin m → ℕ),
    p = C c + ∑ i : Fin m, (X : F2[X]) ^ (2 ^ k i) ∧ SourceParity p m

def PublishedIff (e : EvenReading) : Prop :=
  ∀ p : F2[X], Domain e p → (p.comp (X + 1) = p ↔ DisplayedRepresentation p)

def OptionalConstantIff (e : EvenReading) : Prop :=
  ∀ p : F2[X], Domain e p → (p.comp (X + 1) = p ↔ ConstantRepresentation p)

private theorem domain_of_event (r : ℕ) (h : FamilyEvent r) (e : EvenReading) :
    Domain e (P r) := by
  rcases h with ⟨_, _, _, hexp, _, hdeg, hconst, hsupp, hdiv, href, _⟩
  cases e
  · exact hexp
  · exact hdeg
  · exact hsupp
  · exact hconst
  · exact hdiv
  · exact href

/-- At least one complete conventional reading of the published iff, or its
 separately stated optional-constant variant, holds. -/
def claim : Prop :=
  ∃ e : EvenReading, PublishedIff e ∨ OptionalConstantIff e

private theorem family_refutes_source (r : ℕ) (ho : Odd r) (hr : 3 ≤ r)
    (e : EvenReading) : ¬ PublishedIff e ∧ ¬ OptionalConstantIff e := by
  have hf := family_event r ho hr
  have hd := domain_of_event r hf e
  rcases hf with ⟨_, _, hinv, _, _, _, _, _, _, _, hnr⟩
  have hdisplay : ¬ DisplayedRepresentation (P r) := by
    rintro ⟨m, k, heq, _⟩
    exact hnr 0 m k (by simpa using heq)
  have hconstant : ¬ ConstantRepresentation (P r) := by
    rintro ⟨c, m, k, heq, _⟩
    exact hnr c m k heq
  exact ⟨fun h => hdisplay ((h (P r) hd).mp hinv),
    fun h => hconstant ((h (P r) hd).mp hinv)⟩

/-- None of the complete conventional source readings holds. -/
theorem result : ¬ claim := by
  rintro ⟨e, h⟩
  have href := family_refutes_source 3 (by decide) (by decide) e
  exact h.elim href.1 href.2

end D5.S3.ArithUnits.SelfConjugateEvenPolynomialRefutation
