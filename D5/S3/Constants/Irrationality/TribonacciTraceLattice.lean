/- GID: D5/S3/Constants/Irrationality/TribonacciTraceLattice
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/TribonacciTraceLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonintegrality separates the Tribonacci deficit from the two-faced Fibonacci case. -/

import Mathlib.Analysis.RCLike.Lemmas
import D5.S3.Constants.Irrationality.TribonacciDeficitScanCertificate
import D5.S3.Constants.Irrationality.TwoFacedPrivilege

namespace D5.S3.Constants.Irrationality.TribonacciTraceLattice

set_option maxRecDepth 10000
open scoped ComplexConjugate

open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S3.Constants.Irrationality.CubicConjugateTrace
open D5.S3.Constants.Irrationality.TribonacciDeficitScan
open D5.S3.Constants.Irrationality.TwoFacedPrivilege

local notation "t" => tribonacciConstant

/- The two concrete encodings compared in PZG Remark 6.27. This is not an
arbitrary family: its branches are the repository's Fibonacci and Tribonacci
deficit functions. -/
inductive ComparedDeficitEncoding
  | fibonacci
  | tribonacci
  deriving DecidableEq

noncomputable def comparedDeficit : ComparedDeficitEncoding → Nat → Nat → Real
  | .fibonacci => D5.S1.Deficit.deficit
  | .tribonacci => tribonacciDeficit

/- Integrality of every value of the selected concrete deficit. -/
def HasIntegralDeficit (encoding : ComparedDeficitEncoding) : Prop :=
  ∀ v1 v2 : Nat, ∃ z : Int, comparedDeficit encoding v1 v2 = (z : Real)

/- The positive quantity whose square root is the imaginary separation of the
two non-Perron roots. -/
noncomputable def tribonacciSecondaryDiscriminant : Real :=
  4 * t⁻¹ - (t - 1) ^ 2

/- The non-Perron root in the open upper half-plane. -/
noncomputable def tribonacciSecondaryRootValue : Complex :=
  (((1 - t) / 2 : Real) : Complex) +
    ((Real.sqrt tribonacciSecondaryDiscriminant / 2 : Real) : Complex) * Complex.I

theorem tribonacci_secondary_root_im_pos :
    0 < tribonacciSecondaryRootValue.im := by
  have hd : 0 < tribonacciSecondaryDiscriminant := by
    exact D5.S0.Tower.Tribonacci.PerronRoot.tribonacci_errorEnergy_discriminant_pos
  simp [tribonacciSecondaryRootValue, Real.sqrt_pos.2 hd]

theorem tribonacci_secondary_root_cofactor_zero :
    conjugateCofactor tribonacciSecondaryRootValue = 0 := by
  have hd : 0 <= tribonacciSecondaryDiscriminant :=
    D5.S0.Tower.Tribonacci.PerronRoot.tribonacci_errorEnergy_discriminant_pos.le
  have hsqrt : Real.sqrt tribonacciSecondaryDiscriminant ^ 2 =
      tribonacciSecondaryDiscriminant := Real.sq_sqrt hd
  dsimp [tribonacciSecondaryDiscriminant] at hsqrt
  have hinv : t⁻¹ = t ^ 2 - t - 1 := by
    field_simp [tribonacciConstant_ne_zero]
    nlinarith [tribonacciConstant_cubic]
  apply Complex.ext
  · simp [conjugateCofactor, tribonacciSecondaryRootValue,
      tribonacciSecondaryDiscriminant, Complex.mul_re, Complex.mul_im, pow_two]
    ring_nf at hsqrt hinv ⊢
    nlinarith
  · simp [conjugateCofactor, tribonacciSecondaryRootValue,
      tribonacciSecondaryDiscriminant, Complex.mul_re, Complex.mul_im, pow_two]
    ring

theorem tribonacci_secondary_root_is_root :
    tribonacciSecondaryRootValue ^ 3 - tribonacciSecondaryRootValue ^ 2 -
        tribonacciSecondaryRootValue - 1 = 0 := by
  rw [cubic_splits_exact tribonacciSecondaryRootValue,
    tribonacci_secondary_root_cofactor_zero, mul_zero]

theorem tribonacci_secondary_root_ne_perron :
    tribonacciSecondaryRootValue ≠ (t : Complex) := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.ofReal_im] at him
  nlinarith [tribonacci_secondary_root_im_pos]

/- A source-specific carrier for one of the two non-Perron roots. Its subtype
prevents a trivial value from replacing the Tribonacci root. -/
def TribonacciSecondaryRoot :=
  {z : Complex //
    z ^ 3 - z ^ 2 - z - 1 = 0 ∧ z ≠ (t : Complex) ∧ 0 < z.im}

noncomputable def tribonacciSecondaryRoot : TribonacciSecondaryRoot :=
  ⟨tribonacciSecondaryRootValue,
    tribonacci_secondary_root_is_root,
    tribonacci_secondary_root_ne_perron,
    tribonacci_secondary_root_im_pos⟩

noncomputable def tribonacciCharacteristicPolynomialReal : Polynomial Real :=
  Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X - 1

theorem tribonacci_secondary_conjugate_is_root :
    conj tribonacciSecondaryRoot.1 ^ 3 -
        conj tribonacciSecondaryRoot.1 ^ 2 -
        conj tribonacciSecondaryRoot.1 - 1 = 0 := by
  have hroot : Polynomial.aeval tribonacciSecondaryRoot.1
      tribonacciCharacteristicPolynomialReal = 0 := by
    simpa [tribonacciCharacteristicPolynomialReal] using tribonacciSecondaryRoot.property.1
  have hconj := Polynomial.aeval_conj tribonacciCharacteristicPolynomialReal
    tribonacciSecondaryRoot.1
  rw [hroot, map_zero] at hconj
  simpa [tribonacciCharacteristicPolynomialReal] using hconj

theorem tribonacci_secondary_conjugate_ne_perron :
    conj tribonacciSecondaryRoot.1 ≠ (t : Complex) := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im, Complex.ofReal_im] at him
  nlinarith [tribonacciSecondaryRoot.property.2.2]

/- Evaluate the existing exact cubic code at any complex embedding of the
Tribonacci root. -/
noncomputable def tribonacciCodeComplexValue (z : Complex)
    (x : TribonacciCubicCode) : Complex :=
  (x.rational : Complex) + (x.linear : Complex) * z +
    (x.quadratic : Complex) * z ^ 2

/- The C/R trace of the code's value at the upper non-Perron root. -/
noncomputable def tribonacciConjugatePairTrace (x : TribonacciCubicCode) : Complex :=
  tribonacciCodeComplexValue tribonacciSecondaryRoot.1 x +
    conj (tribonacciCodeComplexValue tribonacciSecondaryRoot.1 x)

theorem tribonacci_code_value_at_conjugate (x : TribonacciCubicCode) :
    conj (tribonacciCodeComplexValue tribonacciSecondaryRoot.1 x) =
      tribonacciCodeComplexValue (conj tribonacciSecondaryRoot.1) x := by
  simp [tribonacciCodeComplexValue]

theorem tribonacci_code_value_at_perron (x : TribonacciCubicCode) :
    tribonacciCodeComplexValue (t : Complex) x =
      (tribonacciCodeValue x : Complex) := by
  simp [tribonacciCodeComplexValue, tribonacciCodeValue]

theorem tribonacci_secondary_root_add_conjugate :
    tribonacciSecondaryRoot.1 + conj tribonacciSecondaryRoot.1 =
      ((1 - t : Real) : Complex) := by
  rw [Complex.add_conj]
  simp [tribonacciSecondaryRoot, tribonacciSecondaryRootValue]
  ring

theorem tribonacci_secondary_root_mul_conjugate :
    tribonacciSecondaryRoot.1 * conj tribonacciSecondaryRoot.1 =
      ((t⁻¹ : Real) : Complex) := by
  have hd : 0 <= tribonacciSecondaryDiscriminant :=
    D5.S0.Tower.Tribonacci.PerronRoot.tribonacci_errorEnergy_discriminant_pos.le
  have hsqrt : Real.sqrt tribonacciSecondaryDiscriminant ^ 2 =
      tribonacciSecondaryDiscriminant := Real.sq_sqrt hd
  dsimp [tribonacciSecondaryDiscriminant] at hsqrt
  have hnorm : Complex.normSq tribonacciSecondaryRoot.1 = t⁻¹ := by
    rw [Complex.normSq_apply]
    simp [tribonacciSecondaryRoot, tribonacciSecondaryRootValue,
      tribonacciSecondaryDiscriminant]
    nlinarith
  calc
    tribonacciSecondaryRoot.1 * conj tribonacciSecondaryRoot.1 =
        conj tribonacciSecondaryRoot.1 * tribonacciSecondaryRoot.1 := mul_comm _ _
    _ = (Complex.normSq tribonacciSecondaryRoot.1 : Complex) :=
      Complex.normSq_eq_conj_mul_self.symm
    _ = ((t⁻¹ : Real) : Complex) := by rw [hnorm]

theorem tribonacci_secondary_root_sq_add_conjugate_sq :
    tribonacciSecondaryRoot.1 ^ 2 + conj tribonacciSecondaryRoot.1 ^ 2 =
      ((3 - t ^ 2 : Real) : Complex) := by
  have hreal : (1 - t) ^ 2 - 2 * t⁻¹ = 3 - t ^ 2 := by
    field_simp [tribonacciConstant_ne_zero]
    nlinarith [tribonacciConstant_cubic]
  calc
    tribonacciSecondaryRoot.1 ^ 2 + conj tribonacciSecondaryRoot.1 ^ 2 =
        (tribonacciSecondaryRoot.1 + conj tribonacciSecondaryRoot.1) ^ 2 -
          2 * (tribonacciSecondaryRoot.1 * conj tribonacciSecondaryRoot.1) := by ring
    _ = ((((1 - t) ^ 2 - 2 * t⁻¹ : Real) : Complex)) := by
      rw [tribonacci_secondary_root_add_conjugate,
        tribonacci_secondary_root_mul_conjugate]
      push_cast
      ring
    _ = ((3 - t ^ 2 : Real) : Complex) := by exact_mod_cast hreal

/- The sum over the real embedding and the conjugate pair is the rational
cubic trace `3a + b + 3c`. -/
theorem tribonacci_code_three_embedding_trace (x : TribonacciCubicCode) :
    (tribonacciCodeValue x : Complex) + tribonacciConjugatePairTrace x =
      ((3 * x.rational + x.linear + 3 * x.quadratic : Rat) : Complex) := by
  rw [← tribonacci_code_value_at_perron, tribonacciConjugatePairTrace,
    tribonacci_code_value_at_conjugate]
  rw [show
      tribonacciCodeComplexValue tribonacciSecondaryRoot.1 x +
          tribonacciCodeComplexValue (conj tribonacciSecondaryRoot.1) x =
        2 * (x.rational : Complex) +
          (x.linear : Complex) *
            (tribonacciSecondaryRoot.1 + conj tribonacciSecondaryRoot.1) +
          (x.quadratic : Complex) *
            (tribonacciSecondaryRoot.1 ^ 2 +
              conj tribonacciSecondaryRoot.1 ^ 2) by
        simp only [tribonacciCodeComplexValue]
        ring]
  rw [tribonacci_secondary_root_add_conjugate,
    tribonacci_secondary_root_sq_add_conjugate_sq]
  simp only [tribonacciCodeComplexValue]
  push_cast
  ring

theorem tribonacci_scan_code_has_integer_trace {x : TribonacciCubicCode}
    (hx : x ∈ tribonacciScanSpectrum) :
    ∃ k : Int,
      (tribonacciCodeValue x : Complex) + tribonacciConjugatePairTrace x =
        (k : Complex) := by
  rw [tribonacci_code_three_embedding_trace]
  simp only [tribonacciScanSpectrum, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨-1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num [tribonacciCodeZero]⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

/- Every nonintegral deficit in the exact triangular scan is congruent modulo
an integer to the negative C/R trace of its complex-conjugate pair. -/
theorem tribonacci_nonintegral_deficit_mod_integer_eq_neg_trace :
    ∀ pair : Nat × Nat, pair ∈ tribonacciNonintegralScanPairs →
      ∃ k : Int,
        ((tribonacciDeficit pair.1 pair.2 : Real) : Complex) =
          (k : Complex) - tribonacciConjugatePairTrace
            (tribonacciDeficitCodeAt 10 pair.1 pair.2) := by
  intro pair hpair
  have hscan : pair ∈ tribonacciScanPairs := (Finset.mem_filter.mp hpair).1
  have hspectrum : tribonacciDeficitCodeAt 10 pair.1 pair.2 ∈
      tribonacciScanSpectrum := by
    rw [← tribonacci_scan_spectrum_exact]
    exact Finset.mem_image.mpr ⟨pair, hscan, rfl⟩
  obtain ⟨k, hk⟩ := tribonacci_scan_code_has_integer_trace hspectrum
  refine ⟨k, ?_⟩
  have hvalue := congrArg (fun y : Real => (y : Complex))
    (tribonacci_scan_deficit_eq_code hscan)
  rw [hvalue]
  exact (eq_sub_iff_add_eq).2 hk

/- The complete exact implementation certificate from the first formalization
round. It remains public so that no previously proved scan or structural fact
is lost, but its source-specific window, counts, rounding interval, code image,
and supporting root facts are not presented as clauses of PZG Remark 6.27. -/
set_option maxHeartbeats 750000 in
-- Elaborating the seven imported certificate branches exceeds the default.
theorem tribonacci_trace_lattice_window_certificate :
    (∀ v1 v2 : Nat, 1 ≤ v1 → v1 ≤ v2 → v2 ≤ 200 →
      |tribonacciDeficit v1 v2| < (955 : Real) / 1000) ∧
    (tribonacciNonintegralScanPairs.card = 8934 ∧
      ((4435 : Rat) / 10000 ≤ (8934 : Rat) / 20100 ∧
        (8934 : Rat) / 20100 < 4445 / 10000)) ∧
    (tribonacciScanPairs.image
        (fun pair => tribonacciDeficitCodeAt 10 pair.1 pair.2) =
      tribonacciScanSpectrum) ∧
    (∀ pair : Nat × Nat, pair ∈ tribonacciNonintegralScanPairs →
      ∃ k : Int,
        ((tribonacciDeficit pair.1 pair.2 : Real) : Complex) =
          (k : Complex) - tribonacciConjugatePairTrace
            (tribonacciDeficitCodeAt 10 pair.1 pair.2)) ∧
    (∀ v1 v2 : Nat,
      D5.S1.Deficit.deficit v1 v2 = D5.S1.Deficit.deficitContraction v1 v2 ∧
        ∃ z : Int, D5.S1.Deficit.deficit v1 v2 = (z : Real)) ∧
    ((∀ z : Complex,
        z ^ 3 - z ^ 2 - z - 1 =
          (z - (t : Complex)) * conjugateCofactor z) ∧
      Irrational (1 - t)) ∧
    (((∀ v1 v2 : Nat,
        D5.S1.Deficit.deficit v1 v2 = D5.S1.Deficit.deficitContraction v1 v2 ∧
          ∃ z : Int, D5.S1.Deficit.deficit v1 v2 = (z : Real)) ∧
      Irrational (1 - t))) := by
  refine ⟨?_, ?_, tribonacci_scan_spectrum_exact,
    tribonacci_nonintegral_deficit_mod_integer_eq_neg_trace,
    quadratic_deficit_is_integral,
    cubic_trace_is_not_carried_by_the_perron_root,
    integrality_is_a_two_faced_privilege⟩
  · intro v1 v2 hv1 hv12 hv2
    exact tribonacci_deficit_scan_bound (pair := (v1, v2))
      (mem_tribonacciScanPairs_iff.mpr ⟨hv1, hv12, hv2⟩)
  · exact ⟨tribonacci_nonintegral_scan_count,
      tribonacci_nonintegral_scan_percentage_rounds_to_44_4⟩

/- A certified scan member supplies a witness for the source's unrestricted
negative assertion: the Tribonacci deficit is not always integral. The scan
window is used only to prove the existential and is absent from its type. -/
set_option maxHeartbeats 750000 in
-- Reducing certified scan membership at the concrete witness exceeds the default.
theorem tribonacci_deficit_not_always_integral :
    ∃ v1 v2 : Nat, ¬ ∃ z : Int, tribonacciDeficit v1 v2 = (z : Real) := by
  refine ⟨1, 1, tribonacci_nonintegral_of_mem_scan (pair := (1, 1)) ?_⟩
  decide

/- Within the two concrete encodings compared by the source, always-integral
deficit is exclusive to the Fibonacci encoding. Both directions carry content:
the forward direction rules out replacing Fibonacci by Tribonacci, while the
reverse direction is the two-faced integrality theorem. -/
theorem compared_deficit_has_integral_deficit_iff
    (encoding : ComparedDeficitEncoding) :
    HasIntegralDeficit encoding ↔ encoding = .fibonacci := by
  constructor
  · intro hintegral
    cases encoding with
    | fibonacci => rfl
    | tribonacci =>
        exfalso
        obtain ⟨v1, v2, hnot⟩ := tribonacci_deficit_not_always_integral
        exact hnot (hintegral v1 v2)
  · rintro rfl v1 v2
    exact (quadratic_deficit_is_integral v1 v2).2

/- CAS-A10 as a relation rather than a repeated pair of facts: the two-faced
Fibonacci integrality proposition differs from its Tribonacci replacement. -/
theorem fibonacci_integrality_is_privileged :
    HasIntegralDeficit .fibonacci ≠ HasIntegralDeficit .tribonacci := by
  intro hsame
  have hfibonacci : HasIntegralDeficit .fibonacci :=
    (compared_deficit_has_integral_deficit_iff .fibonacci).2 rfl
  have htribonacci : HasIntegralDeficit .tribonacci := hsame ▸ hfibonacci
  have hcollapse :=
    (compared_deficit_has_integral_deficit_iff .tribonacci).1 htribonacci
  cases hcollapse

/- CAS-A11: substituting the concrete Tribonacci encoding destroys the
always-integral property. -/
theorem fibonacci_two_is_not_replaceable :
    ¬ HasIntegralDeficit .tribonacci := by
  intro htribonacci
  have hcollapse :=
    (compared_deficit_has_integral_deficit_iff .tribonacci).1 htribonacci
  cases hcollapse

/-- PZG Remark 6.27, restricted to the clauses that the current vocabulary can
state without replacing a structural object by a computational surrogate.
The three leaves are respectively CAS-A2, the concrete privilege relation
CAS-A10, and the nonreplaceability assertion CAS-A11.

**What this does not claim.** CAS-A1 and CAS-A3 are not claimed here: the source
reports an output interval and 44.4 percent but supplies no input scan domain,
sample count, denominator, or rounding convention. CAS-A4 is not claimed: the
source supplies neither the nonintegral value set nor the topology in which it
is discrete; the existing eight-code scan spectrum includes zero. CAS-A5 is
not claimed: the current pointwise congruence modulo integers is not equality
with a named additive subgroup or lattice, and a nontrivial additive subgroup
of `Complex` cannot have the finite scan spectrum as its carrier. CAS-A6 and
CAS-A7 are not
claimed: `conjEquiv` exists on `GoldenInt`, but no public family of quadratic
field embeddings or exhaustion theorem connects it to the deficit. CAS-A8 is
not claimed: there is no Tribonacci number-field carrier with a proved
one-real/two-complex embedding count. CAS-A9 is not claimed: the root-sum
calculation in this module is not `Algebra.trace` on such a field. The separate
`tribonacci_trace_lattice_window_certificate` retains every exact finite-window
fact used by the prior implementation without assigning those facts to the
withdrawn source clauses. -/
theorem pzg_remark_6_27_tribonacci_trace_lattice :
    (∃ v1 v2 : Nat, ¬ ∃ z : Int, tribonacciDeficit v1 v2 = (z : Real)) ∧
      (HasIntegralDeficit .fibonacci ≠ HasIntegralDeficit .tribonacci) ∧
      ¬ HasIntegralDeficit .tribonacci :=
  ⟨tribonacci_deficit_not_always_integral,
    fibonacci_integrality_is_privileged,
    fibonacci_two_is_not_replaceable⟩

/- Preservation probe for the old trace congruence: it remains projectable from
the separately named exact window certificate. -/
example {pair : Nat × Nat} (hpair : pair ∈ tribonacciNonintegralScanPairs) :
    ∃ k : Int,
      ((tribonacciDeficit pair.1 pair.2 : Real) : Complex) =
        (k : Complex) - tribonacciConjugatePairTrace
          (tribonacciDeficitCodeAt 10 pair.1 pair.2) := by
  exact tribonacci_trace_lattice_window_certificate.2.2.2.1 pair hpair

/- Trivialization probe for the same clause: positive imaginary part forces
the two named non-Perron embeddings to be a genuinely distinct conjugate pair. -/
example : conj tribonacciSecondaryRoot.1 ≠ tribonacciSecondaryRoot.1 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  nlinarith [tribonacciSecondaryRoot.property.2.2]

/- Reverse probe for CAS-A2: the public result yields a genuine nonintegral
deficit without exposing the implementation scan as a source restriction. -/
example : ∃ v1 v2 : Nat, ¬ ∃ z : Int,
    tribonacciDeficit v1 v2 = (z : Real) :=
  pzg_remark_6_27_tribonacci_trace_lattice.1

/- Collapse probe for CAS-A10/A11: the public classifier distinguishes the two
concrete encodings, giving integrality on Fibonacci and its negation on
Tribonacci. Replacing either branch by a constant function breaks this result. -/
example : HasIntegralDeficit .fibonacci ∧ ¬ HasIntegralDeficit .tribonacci := by
  constructor
  · by_contra hfibonacci
    apply pzg_remark_6_27_tribonacci_trace_lattice.2.1
    apply propext
    exact iff_of_false hfibonacci pzg_remark_6_27_tribonacci_trace_lattice.2.2
  · exact pzg_remark_6_27_tribonacci_trace_lattice.2.2

/- The classifier's carrier itself has not collapsed to one point. -/
example : ComparedDeficitEncoding.fibonacci ≠ .tribonacci := by decide

end D5.S3.Constants.Irrationality.TribonacciTraceLattice
