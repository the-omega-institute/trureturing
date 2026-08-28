/- GID: D5/S3/ConceptDynamics/Fibers/IdealValuationImageGauge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/IdealValuationImageGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Int ideal values are faithful not onto; zero, unit, and sign gauge are explicit. -/

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib hit `Int.ideal_span_absNorm_eq_self`; it recovers an integer ideal
     from its nonnegative canonical generator and is applied directly.
   * `Nat.eq_of_factorization_eq` recovers a nonzero natural number from all prime
     exponents; it supplies the unique-factorization step instead of a local reproof.
   * `Nat.exists_infinite_primes` and `Nat.factorization_eq_zero_of_lt` give a prime
     outside the finite support of any one integer ideal's exponent family.
   * Current-tree `joint_residue_image_eq_compatible_pairs (m n : Nat)` identifies the
     image of `Int -> ZMod m × ZMod n`; that residue readout is not the ideal-valued
     exponent readout below, so the module is distinguished here and is not imported.
   * This is honest fallback (2): all three layers are proved concretely for `ℤ`; no
     general Dedekind-domain or class-group statement is claimed. -/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.IdealValuationImageGauge

open scoped Classical

/-- The exponent at the prime ideal `(p)` of an integer ideal. The zero ideal receives
`top` at every prime, while a nonzero ideal uses the factorization of its norm. -/
noncomputable def intIdealValuationReadout (I : Ideal ℤ) (p : Nat.Primes) : WithTop ℕ :=
  if I = ⊥ then ⊤ else (Ideal.absNorm I).factorization p.1

/-- A concrete exponent family with nonzero value at every prime. -/
def infiniteSupportExponentFamily : Nat.Primes → WithTop ℕ :=
  fun _ => 1

/-- The families realized by the integer-ideal valuation readout. -/
def intIdealValuationImage : Set (Nat.Primes → WithTop ℕ) :=
  Set.range intIdealValuationReadout

/-- All prime-ideal exponents determine an integer ideal, including the zero ideal under
the explicit `top` convention. This is the concrete kernel-layer faithfulness claim. -/
theorem int_ideal_valuation_readout_injective :
    Function.Injective intIdealValuationReadout := by
  intro I J hreadout
  by_cases hI : I = ⊥
  · subst I
    by_contra hJ
    have htwo := congrFun hreadout ⟨2, Nat.prime_two⟩
    simp [intIdealValuationReadout] at htwo
    exact hJ htwo.symm
  · by_cases hJ : J = ⊥
    · subst J
      have htwo := congrFun hreadout ⟨2, Nat.prime_two⟩
      simp [intIdealValuationReadout, hI] at htwo
    · have hnorm : Ideal.absNorm I = Ideal.absNorm J := by
        apply Nat.eq_of_factorization_eq
          (Ideal.absNorm_eq_zero_iff.not.mpr hI)
          (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
        intro p
        by_cases hp : p.Prime
        · have hpreadout := congrFun hreadout ⟨p, hp⟩
          simpa [intIdealValuationReadout, hI, hJ] using hpreadout
        · simp [Nat.factorization_eq_zero_of_not_prime, hp]
      rw [← Int.ideal_span_absNorm_eq_self I, hnorm,
        Int.ideal_span_absNorm_eq_self J]

#print axioms int_ideal_valuation_readout_injective

/-- The constant-one family is outside the image: every nonzero integer ideal has a
prime beyond its norm where the exponent vanishes, while the zero ideal reads `top`. -/
theorem infinite_support_family_not_in_image :
    infiniteSupportExponentFamily ∉ intIdealValuationImage := by
  rintro ⟨I, hreadout⟩
  by_cases hI : I = ⊥
  · have htwo := congrFun hreadout ⟨2, Nat.prime_two⟩
    simp [intIdealValuationReadout, infiniteSupportExponentFamily, hI] at htwo
  · obtain ⟨p, hp_bound, hp_prime⟩ :=
      Nat.exists_infinite_primes (Ideal.absNorm I + 1)
    have hp_large : Ideal.absNorm I < p := Nat.lt_of_succ_le hp_bound
    have hpreadout := congrFun hreadout ⟨p, hp_prime⟩
    have hp_zero := Nat.factorization_eq_zero_of_lt hp_large
    simp [intIdealValuationReadout, infiniteSupportExponentFamily, hI, hp_zero] at hpreadout

#print axioms infinite_support_family_not_in_image

/-- The ideal `(2)` has the distinct generators `2` and `-2`; the unit `-1` relates
them. This is the concrete gauge-layer witness after principality is already known. -/
theorem two_generators_unit_gauge :
    (2 : ℤ) ≠ -2 ∧
      Ideal.span ({2} : Set ℤ) = Ideal.span ({-2} : Set ℤ) ∧
      ∃ u : ℤˣ, (-2 : ℤ) = (u : ℤ) * 2 := by
  refine ⟨by norm_num, (Ideal.span_singleton_neg (x := (2 : ℤ))).symm, ?_⟩
  exact ⟨-1, by norm_num⟩

#print axioms two_generators_unit_gauge

/- Degenerate audit: the fixed prime index is inhabited and not a singleton. Thus no
empty or one-point index type makes the readout injective vacuously. -/
example : Nonempty Nat.Primes := ⟨⟨2, Nat.prime_two⟩⟩

example : ¬ Subsingleton Nat.Primes := by
  intro h
  have heq : (⟨2, Nat.prime_two⟩ : Nat.Primes) = ⟨3, Nat.prime_three⟩ :=
    h.elim _ _
  norm_num at heq

/- The zero ideal is the constant-`top` readout; generator zero is its only generator.
This is the `n = 0` specialization, and it cannot collide with the unit ideal. -/
example (p : Nat.Primes) : intIdealValuationReadout ⊥ p = ⊤ := by
  simp [intIdealValuationReadout]

example : {z : ℤ | Ideal.span {z} = ⊥} = {0} := by
  ext z
  simp

/- The unit ideal is the zero exponent family, but its generator gauge is exactly
the two integer units `1` and `-1`. -/
example (p : Nat.Primes) : intIdealValuationReadout ⊤ p = 0 := by
  simp [intIdealValuationReadout]

example : {z : ℤ | Ideal.span {z} = ⊤} = {1, -1} := by
  ext z
  simp [Ideal.span_singleton_eq_top, Int.isUnit_iff]

/- A prime ideal `(p)` has exactly the two integer generators `p` and `-p`; primality
makes `p` positive, so these generators are distinct. -/
example (p : Nat.Primes) :
    {z : ℤ | Ideal.span {z} = Ideal.span {(p.1 : ℤ)}} =
      {(p.1 : ℤ), -(p.1 : ℤ)} := by
  ext z
  simp [Ideal.span_singleton_eq_span_singleton, Int.associated_iff]

example (p : Nat.Primes) : (p.1 : ℤ) ≠ -(p.1 : ℤ) := by
  have hp : 0 < p.1 := p.2.pos
  omega

/- Constant and zero maps are explicit above and are distinct. There is no quantified
map parameter, so an identity-map specialization is not applicable to these statements. -/
example : intIdealValuationReadout ⊥ ≠ intIdealValuationReadout ⊤ := by
  intro h
  have htwo := congrFun h ⟨2, Nat.prime_two⟩
  simp [intIdealValuationReadout] at htwo

/- Primality audit: prime proofs select the coordinates used by unique factorization and
produce the arbitrarily large coordinate in the image witness. The `±2` gauge witness
itself needs only that `2` is nonzero, not that it is prime.

Assumption audit: the three public theorems have no variables, hypotheses, or instance
parameters. Their ring, prime index, zero convention, and unit witness are concrete, so
there is no necessary theorem assumption for which a counterexample theorem is due. -/

end D5.S3.ConceptDynamics.Fibers.IdealValuationImageGauge
