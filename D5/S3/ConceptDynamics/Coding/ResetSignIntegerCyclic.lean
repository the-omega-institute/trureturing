/- GID: D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Literal Sign coefficient elimination with inverse integral polynomial quotient maps. -/
import D5.S1.Recurrence.FiniteCompanionCyclicModule
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open Polynomial
open scoped BigOperators
open ResetNumberedHistories (Sign oddTau resetLabel)

abbrev R := MonoidAlgebra ℤ Sign
abbrev QP (q : ℕ) := D5.S1.Recurrence.FiniteCompanionCyclicModule.CyclicQ resetLabel q

/-- The forward geometric sum. -/
def S (q : ℕ) : ℤ[X] := ∑ k ∈ Finset.range q, X ^ k
/-- The integral time relation. -/
def F (q : ℕ) : ℤ[X] := X ^ (2 * q) - S q ^ 2
/-- The literal sign expressed in forward time. -/
def W (q : ℕ) : ℤ[X] := S q - (X - 1) * X ^ q

abbrev QF (q : ℕ) := ℤ[X] ⧸ (Ideal.span {F q} : Ideal ℤ[X])
def fp (q : ℕ) : ℤ[X] →+* QF q := Ideal.Quotient.mk _
def pp (q : ℕ) : R[X] →+* QP q := Ideal.Quotient.mk _
def inclusion : ℤ[X] →+* R[X] := Polynomial.mapRingHom (algebraMap ℤ R)

private theorem inclusion_X : inclusion X = X := Polynomial.map_X _

private theorem inclusion_S (q : ℕ) :
    inclusion (S q) = ∑ k ∈ Finset.range q, (X : R[X]) ^ k := by
  simp only [S, map_sum, map_pow, inclusion_X]

theorem geometric (q : ℕ) : X ^ q - (X - 1) * S q = 1 := by
  rw [S, mul_geom_sum]
  ring

private theorem time_certificate (q : ℕ) : X ^ q - W q * S q = F q := by
  simp only [W, F, show 2 * q = q * 2 by omega, pow_mul]
  linear_combination -(X ^ q) * geometric q

private theorem sign_certificate (q : ℕ) :
    W q ^ 2 - 1 = ((X - 1) ^ 2 - 1) * F q := by
  simp only [W, F, show 2 * q = q * 2 by omega, pow_mul]
  linear_combination (X ^ q - (X - 1) * S q + 1) * geometric q

private theorem fp_F (q : ℕ) : fp q (F q) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem sign_square (q : ℕ) : fp q (W q) * fp q (W q) = 1 := by
  have h := congrArg (fp q) (sign_certificate q)
  simpa only [map_sub, map_pow, map_one, map_mul, fp_F, mul_zero, sub_eq_zero,
    pow_two] using h

/-- The actual two-element Sign homomorphism into the integral quotient. -/
def signHom (q : ℕ) : Sign →* QF q where
  toFun h := if h = 1 then 1 else fp q (W q)
  map_one' := by simp
  map_mul' h k := by
    rcases ResetFiniteIntegralDefect.sign_cases h with rfl | rfl <;>
      rcases ResetFiniteIntegralDefect.sign_cases k with rfl | rfl
    · simp
    · simp
    · simp
    · have ht : oddTau * oddTau = (1 : Sign) := by decide
      have hn : oddTau ≠ (1 : Sign) := by decide
      simpa [ht, hn] using (sign_square q).symm

def coefficientHom (q : ℕ) : R →+* QF q :=
  (MonoidAlgebra.lift ℤ (QF q) Sign (signHom q)).toRingHom

private theorem coefficient_tau (q : ℕ) : coefficientHom q resetLabel = fp q (W q) := by
  have hn : oddTau ≠ (1 : Sign) := by decide
  simp [coefficientHom, resetLabel, MonoidAlgebra.lift_single, signHom, hn]

def forwardPolynomial (q : ℕ) : R[X] →+* QF q :=
  Polynomial.eval₂RingHom (coefficientHom q) (fp q X)

private theorem forward_inclusion (q : ℕ) :
    (forwardPolynomial q).comp inclusion = fp q := by
  apply Polynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, inclusion, Polynomial.coe_mapRingHom,
      Polynomial.map_C]
    have hc : algebraMap ℤ R z = (z : R) := map_intCast (algebraMap ℤ R) z
    have hi : C z = (z : ℤ[X]) := map_intCast (C : ℤ →+* ℤ[X]) z
    simp only [hc, hi, map_intCast]
  · simp [inclusion_X, forwardPolynomial]

private theorem forward_relation (q : ℕ) :
    forwardPolynomial q (D5.S1.Recurrence.FiniteCompanionCyclicModule.P resetLabel q) = 0 := by
  have h := congrArg (fp q) (time_certificate q)
  simp only [map_sub, map_pow, map_mul, fp_F] at h
  simp only [D5.S1.Recurrence.FiniteCompanionCyclicModule.P,
    D5.S1.Recurrence.FiniteCompanionCyclicModule.H, map_sub, map_pow, map_mul, map_sum]
  simpa only [forwardPolynomial, Polynomial.coe_eval₂RingHom, eval₂_X, eval₂_C,
    coefficient_tau, S, map_sum, map_pow] using h

def forward (q : ℕ) : QP q →+* QF q :=
  Ideal.Quotient.lift _ (forwardPolynomial q) (by
    intro p hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨a, rfl⟩
    rw [map_mul, forward_relation, mul_zero])

private theorem label_square : resetLabel * resetLabel = (1 : R) := by
  simpa only [ResetFiniteIntegralDefect.resetFlip, resetLabel, oddTau,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_mul] using
    ResetNativeIntegralDefect.flip_twice (1 : R)

private theorem source_F_certificate (q : ℕ) :
    inclusion (F q) = (X ^ q + C resetLabel * inclusion (S q)) *
      D5.S1.Recurrence.FiniteCompanionCyclicModule.P resetLabel q := by
  have hu : (C resetLabel : R[X]) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, label_square, map_one]
  simp only [F, map_sub, map_pow, inclusion_X,
    D5.S1.Recurrence.FiniteCompanionCyclicModule.P,
    D5.S1.Recurrence.FiniteCompanionCyclicModule.H, S, map_sum]
  simp only [show 2 * q = q * 2 by omega, pow_mul]
  linear_combination (∑ k ∈ Finset.range q, (X : R[X]) ^ k) ^ 2 * hu

private theorem source_W_certificate (q : ℕ) :
    C resetLabel - inclusion (W q) = (X - 1 + C resetLabel) *
      D5.S1.Recurrence.FiniteCompanionCyclicModule.P resetLabel q := by
  have hg := congrArg inclusion (geometric q)
  have hu : (C resetLabel : R[X]) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, label_square, map_one]
  simp only [map_sub, map_pow, inclusion_X, map_one, map_mul, inclusion_S] at hg
  simp only [W, map_sub, map_mul, inclusion_X, map_one, map_pow, inclusion_S,
    D5.S1.Recurrence.FiniteCompanionCyclicModule.P,
    D5.S1.Recurrence.FiniteCompanionCyclicModule.H]
  linear_combination -(C resetLabel) * hg +
    (∑ k ∈ Finset.range q, (X : R[X]) ^ k) * hu

private theorem pp_P (q : ℕ) :
    pp q (D5.S1.Recurrence.FiniteCompanionCyclicModule.P resetLabel q) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

private theorem reverse_relation (q : ℕ) : pp q (inclusion (F q)) = 0 := by
  rw [source_F_certificate, map_mul, pp_P, mul_zero]

def backward (q : ℕ) : QF q →+* QP q :=
  Ideal.Quotient.lift _ ((pp q).comp inclusion) (by
    intro p hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨a, rfl⟩
    change pp q (inclusion (a * F q)) = 0
    rw [map_mul, map_mul, reverse_relation, mul_zero])

private theorem source_tau (q : ℕ) : pp q (C resetLabel) = pp q (inclusion (W q)) := by
  have h := congrArg (pp q) (source_W_certificate q)
  simpa only [map_sub, map_mul, pp_P, mul_zero, sub_eq_zero] using h

private theorem forward_backward (q : ℕ) :
    (forward q).comp (backward q) = RingHom.id (QF q) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change forward q (backward q (fp q p)) = fp q p
  simp only [backward, forward, fp, Ideal.Quotient.lift_mk, RingHom.comp_apply]
  exact RingHom.congr_fun (forward_inclusion q) p

private theorem backward_forward (q : ℕ) :
    (backward q).comp (forward q) = RingHom.id (QP q) := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext'
  · apply MonoidAlgebra.ringHom_ext
    · intro z
      change backward q (forward q (pp q (C (MonoidAlgebra.single 1 z)))) = _
      have hs : MonoidAlgebra.single (1 : Sign) z = (z : R) := by
        rfl
      simp only [hs, map_intCast]
    · intro h
      rcases ResetFiniteIntegralDefect.sign_cases h with rfl | rfl
      · simp [← MonoidAlgebra.one_def]
      · change backward q (forward q (pp q (C resetLabel))) = pp q (C resetLabel)
        simp only [forward, pp, Ideal.Quotient.lift_mk]
        simp only [forwardPolynomial, Polynomial.coe_eval₂RingHom, eval₂_C]
        rw [coefficient_tau]
        exact (source_tau q).symm
  · change backward q (forward q (pp q X)) = pp q X
    simp [forward, backward, pp, fp, forwardPolynomial, inclusion_X]

/-- Both actual quotient maps are inverse, preserving the original coefficient and time. -/
def ringEquiv (q : ℕ) : QP q ≃+* QF q :=
  RingEquiv.ofRingHom (forward q) (backward q) (forward_backward q) (backward_forward q)

/-- The literal integral presentation, with both inverse maps and canonical generators.
    It holds for all natural q; the positive-q native consumer therefore includes q=1. -/
theorem literal_presentation (q : ℕ) :
    (forward q).comp (backward q) = RingHom.id (QF q) ∧
    (backward q).comp (forward q) = RingHom.id (QP q) ∧
    (∀ p : ℤ[X], ringEquiv q (pp q (inclusion p)) = fp q p) ∧
    (∀ p : ℤ[X], (ringEquiv q).symm (fp q p) = pp q (inclusion p)) ∧
    ringEquiv q (pp q X) = fp q X ∧
    ringEquiv q (pp q (C resetLabel)) = fp q (W q) ∧
    (∀ z : ℤ, ringEquiv q (pp q (C (algebraMap ℤ R z))) = fp q (C z)) ∧
    ringEquiv q 1 = 1 ∧
    (q = 1 → ringEquiv q (pp q (C resetLabel)) = fp q X) := by
  refine ⟨forward_backward q, backward_forward q, ?_, ?_, ?_, ?_, ?_,
    map_one (ringEquiv q), ?_⟩
  · intro p
    change forward q (pp q (inclusion p)) = fp q p
    simp only [forward, pp, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun (forward_inclusion q) p
  · intro p
    rfl
  · change forward q (pp q X) = fp q X
    simp [forward, pp, forwardPolynomial]
  · change forward q (pp q (C resetLabel)) = fp q (W q)
    simp only [forward, pp, Ideal.Quotient.lift_mk]
    simpa only [forwardPolynomial, Polynomial.coe_eval₂RingHom, eval₂_C]
      using coefficient_tau q
  · intro z
    have hc : algebraMap ℤ R z = (z : R) := map_intCast (algebraMap ℤ R) z
    have hi : C z = (z : ℤ[X]) := map_intCast (C : ℤ →+* ℤ[X]) z
    simp only [hc, hi, map_intCast]
  · rintro rfl
    change forward 1 (pp 1 (C resetLabel)) = fp 1 X
    simp only [forward, pp, Ideal.Quotient.lift_mk]
    simp only [forwardPolynomial, Polynomial.coe_eval₂RingHom, eval₂_C]
    rw [coefficient_tau]
    have h : W 1 - X = -F 1 := by simp [W, S, F]; ring
    have hm := congrArg (fp 1) h
    simpa only [map_sub, map_neg, fp_F, neg_zero, sub_eq_zero] using hm

end D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
