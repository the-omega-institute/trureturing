/- GID: D5/S3/Constants/NewtonHankelRealRootCriterion
   generality: G
   mirror-B: D5/B/S3/Constants/NewtonHankelRealRootCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Newton Hankel positivity detects real finite spectra. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/- Library-search audit trail (2026-09-06):
   * Repository command
     searched the proposed bridge name, Hermite--Sylvester variants, and
     root/Hankel criterion variants throughout `D5/**/*.lean`; this found no
     matching criterion. The frozen finite Stieltjes and Vandermonde
     modules only prove the forward Gram factorization; the frozen Newton
     module reconstructs a split polynomial from already supplied power sums.
   * Pinned-Mathlib command
     searched the same names plus hyperbolicity and real-root variants in all
     pinned `Mathlib/**/*.lean`; this found only the unrelated two-dimensional
     predicate `Matrix.IsHyperbolic`.
     The exact primitive search
     `rg -n "Complex.re_sum" .lake/packages/mathlib/Mathlib -g '*.lean'`
     found `Complex.re_sum` in `Mathlib/Data/Complex/BigOperators.lean:44`.
     `Lagrange.eval_interpolate_at_node`,
     `Lagrange.degree_interpolate_lt`, `Polynomial.aeval_conj`, and
     `Matrix.PosSemidef.dotProduct_mulVec_nonneg` are exact primitives used
     below, but no packaged root/Hankel criterion exists.
   * Anonymous grep.app searches for `hermite sylvester` and
     `HermiteSylvester` returned HTTP 429. GitHub issue/repository searches,
     run through NyxID, found `PerAlexandersson/RealRooted`; its tree and issue
     search contain Bezoutian/interlacing criteria but no Hermite or Newton
     matrix criterion. No admissible third-party exact hit was found.
   * The remaining finite quadratic identity and conjugate-pair interpolation
     argument are therefore proved locally.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Constants.NewtonHankelRealRootCriterion

/-- The normalized real part of a finite root power sum. -/
def rootPowerMoment {d : Nat} (roots : Fin d -> Complex) (degree : Nat) : Real :=
  (∑ j, (roots j) ^ degree).re / d

/-- The Newton--Hankel matrix associated with a root list carrying multiplicity. -/
def newtonHankel {d : Nat} (roots : Fin d -> Complex) :
    Matrix (Fin d) (Fin d) Real :=
  fun i j => rootPowerMoment roots (i.1 + j.1)

/-- Evaluation of a real coefficient vector as a complex polynomial. -/
def vectorPolynomialValue {d : Nat} (coefficients : Fin d -> Real)
    (z : Complex) : Complex :=
  ∑ i, (coefficients i : Complex) * z ^ i.1

/-- A degree-`d` real polynomial whose coefficients through degree `d` are
strictly positive. -/
def HasPositiveCoefficientsOfDegree (P : Real[X]) (d : Nat) : Prop :=
  P.natDegree = d ∧ ∀ k ≤ d, 0 < P.coeff k

/-- Every complex root of a real polynomial is a strictly negative real
number. -/
def HasOnlyNegativeRealRoots (P : Real[X]) : Prop :=
  ∀ z : Complex, (P.map Complex.ofRealHom).IsRoot z →
    ∃ r : Real, r < 0 ∧ z = (r : Complex)

/-- The listed roots are the roots of `q(x) = x^d P(-1/x)`, expressed by
the equivalent root correspondence between `P` and nonzero roots of `q`.
Repeated entries retain multiplicity for the Newton moments. -/
def EnumeratesReversedRoots {d : Nat} (P : Real[X])
    (roots : Fin d → Complex) : Prop :=
  (∀ j, roots j ≠ 0) ∧
    ∀ z : Complex, (P.map Complex.ofRealHom).IsRoot z ↔
      ∃ j, z = -(roots j)⁻¹

private theorem eval_pos_of_positive_coefficients {P : Real[X]} {d : Nat}
    (hP : HasPositiveCoefficientsOfDegree P d) {x : Real} (hx : 0 ≤ x) :
    0 < P.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro k hk
    have hk' : k ≤ d := by
      rw [← hP.1]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    exact mul_nonneg (le_of_lt (hP.2 k hk')) (pow_nonneg hx k)
  · refine ⟨0, by simp, ?_⟩
    simpa using hP.2 0 (Nat.zero_le d)

private theorem eval_map_conj (p : Complex[X]) (z : Complex) :
    (p.map Complex.conjAe).eval z = conj (p.eval (conj z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        ((p + q).map Complex.conjAe).eval z =
            (p.map Complex.conjAe).eval z + (q.map Complex.conjAe).eval z := by
              rw [Polynomial.map_add, eval_add]
        _ = conj (p.eval (conj z)) + conj (q.eval (conj z)) := by rw [hp, hq]
        _ = conj (p.eval (conj z) + q.eval (conj z)) := by rw [map_add]
        _ = conj ((p + q).eval (conj z)) := by rw [eval_add]
  | monomial n a => simp [eval_monomial]

private def conjugatePairValues (z w : Complex) : Complex :=
  if w = z then Complex.I else if w = conj z then -Complex.I else 0

private theorem conjugatePairValues_conj {z w : Complex} (hz : conj z ≠ z) :
    conj (conjugatePairValues z (conj w)) = conjugatePairValues z w := by
  by_cases hwz : w = z
  · subst w
    simp [conjugatePairValues, hz, Ne.symm hz]
  by_cases hwcz : w = conj z
  · subst w
    simp [conjugatePairValues, hz, Ne.symm hz]
  have hcwz : conj w ≠ z := by
    intro h
    apply hwcz
    calc
      w = conj (conj w) := by simp
      _ = conj z := congrArg conj h
  have hcwcz : conj w ≠ conj z := by
    intro h
    apply hwz
    calc
      w = conj (conj w) := by simp
      _ = conj (conj z) := congrArg conj h
      _ = z := by simp
  simp [conjugatePairValues, hwz, hwcz, hcwz, hcwcz]

private theorem exists_real_conjugate_pair_interpolant {d : Nat}
    (roots : Fin d → Complex) (z : Complex)
    (hzmem : z ∈ Finset.univ.image roots) (hz : conj z ≠ z)
    (hconj : ∀ w, w ∈ Finset.univ.image roots ↔
      conj w ∈ Finset.univ.image roots) :
    ∃ coefficients : Fin d → Real, ∀ w ∈ Finset.univ.image roots,
      vectorPolynomialValue coefficients w = conjugatePairValues z w := by
  classical
  let s : Finset Complex := Finset.univ.image roots
  let f : Complex[X] := Lagrange.interpolate s id (conjugatePairValues z)
  have hinj : Set.InjOn id (↑s : Set Complex) := Set.injOn_id _
  have hf_eval : ∀ w ∈ s, f.eval w = conjugatePairValues z w := by
    intro w hw
    exact Lagrange.eval_interpolate_at_node _ hinj hw
  have hf_degree : f.degree < s.card := Lagrange.degree_interpolate_lt _ hinj
  have hmap_degree :
      (f.map (Complex.conjAe : Complex →+* Complex)).degree < s.card := by
    rw [Polynomial.degree_map_eq_of_injective
      (f := (Complex.conjAe : Complex →+* Complex)) Complex.conjAe.injective f]
    exact hf_degree
  have hmap_eval : ∀ w ∈ s,
      (f.map (Complex.conjAe : Complex →+* Complex)).eval w =
        conjugatePairValues z w := by
    intro w hw
    rw [eval_map_conj, hf_eval (conj w), conjugatePairValues_conj hz]
    exact (hconj w).mp hw
  have hf_real : f.map (Complex.conjAe : Complex →+* Complex) = f := by
    change f.map (Complex.conjAe : Complex →+* Complex) =
      Lagrange.interpolate s id (conjugatePairValues z)
    exact Lagrange.eq_interpolate_of_eval_eq _ hinj hmap_degree hmap_eval
  have hcoeff_real : ∀ n, ((f.coeff n).re : Complex) = f.coeff n := by
    intro n
    have h := congrArg (fun p : Complex[X] ↦ p.coeff n) hf_real
    simp only [Polynomial.coeff_map] at h
    change conj (f.coeff n) = f.coeff n at h
    exact Complex.conj_eq_iff_re.mp h
  have hcard : s.card ≤ d := by
    calc
      s.card ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
      _ = d := Fintype.card_fin d
  have hf_degree_d : f.degree < d := hf_degree.trans_le (by exact_mod_cast hcard)
  have hfne : f ≠ 0 := by
    intro hfzero
    have h := hf_eval z (by exact hzmem)
    simp [hfzero, conjugatePairValues] at h
    have him := congrArg Complex.im h
    norm_num at him
  have hnat_degree : f.natDegree < d :=
    (Polynomial.natDegree_lt_iff_degree_lt hfne).mpr hf_degree_d
  refine ⟨fun i ↦ (f.coeff i.1).re, ?_⟩
  intro w hw
  calc
    vectorPolynomialValue (fun i : Fin d ↦ (f.coeff i.1).re) w =
        ∑ i ∈ Finset.range d, ((f.coeff i).re : Complex) * w ^ i := by
          rw [vectorPolynomialValue]
          exact Fin.sum_univ_eq_sum_range
            (fun i : Nat ↦ ((f.coeff i).re : Complex) * w ^ i) d
    _ = ∑ i ∈ Finset.range d, f.coeff i * w ^ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff_real i]
    _ = f.eval w := (Polynomial.eval_eq_sum_range' hnat_degree w).symm
    _ = conjugatePairValues z w := hf_eval w (by exact hw)

private theorem newtonHankel_isHermitian {d : Nat} (roots : Fin d -> Complex) :
    (newtonHankel roots).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [newtonHankel]
  rw [add_comm]

private theorem vectorPolynomialValue_square_re {d : Nat}
    (coefficients : Fin d -> Real) (z : Complex) :
    (vectorPolynomialValue coefficients z ^ 2).re =
      ∑ i, ∑ j,
        coefficients i * (z ^ (i.1 + j.1)).re * coefficients j := by
  classical
  simp only [vectorPolynomialValue, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero]
  ring

/-- Expanding the Newton--Hankel quadratic form gives the normalized sum of
the real parts of the squared polynomial values at all roots, with repetitions
retaining their algebraic multiplicities. -/
theorem companion_trace_hankel_quadratic_identity {d : Nat}
    (roots : Fin d -> Complex) (coefficients : Fin d -> Real) :
    dotProduct coefficients (newtonHankel roots *ᵥ coefficients) =
      (∑ j, (vectorPolynomialValue coefficients (roots j) ^ 2).re) / d := by
  classical
  simp_rw [vectorPolynomialValue_square_re]
  simp only [dotProduct, mulVec, newtonHankel, rootPowerMoment]
  rw [Finset.sum_div]
  simp_rw [Complex.re_sum]
  simp_rw [div_eq_mul_inv]
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf
  calc
    _ = ∑ i, ∑ k, ∑ j,
        coefficients i * (roots k ^ i.1 * roots k ^ j.1).re * (d : Real)⁻¹ *
          coefficients j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j,
        coefficients i * (roots k ^ i.1 * roots k ^ j.1).re * (d : Real)⁻¹ *
          coefficients j := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A nonreal conjugate pair in a conjugation-stable finite root family
produces a real coefficient vector on which the Newton--Hankel quadratic form
is strictly negative. The vector is obtained by interpolation with values
`i`, `-i`, and zero on the remaining distinct roots. -/
theorem companion_trace_hankel_hermite_sylvester_bridge {d : Nat}
    (roots : Fin d → Complex)
    (hconj : ∀ w, w ∈ Finset.univ.image roots ↔
      conj w ∈ Finset.univ.image roots)
    (z : Complex) (hzmem : z ∈ Finset.univ.image roots)
    (hz : conj z ≠ z) :
    ∃ coefficients : Fin d → Real,
      dotProduct coefficients (newtonHankel roots *ᵥ coefficients) < 0 := by
  classical
  rcases exists_real_conjugate_pair_interpolant roots z hzmem hz hconj with
    ⟨coefficients, heval⟩
  refine ⟨coefficients, ?_⟩
  rw [companion_trace_hankel_quadratic_identity]
  rcases Finset.mem_image.mp hzmem with ⟨j, _, hj⟩
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hdzero
    subst d
    exact Fin.elim0 j
  have hnonpos : ∀ k,
      (vectorPolynomialValue coefficients (roots k) ^ 2).re ≤ 0 := by
    intro k
    rw [heval (roots k) (Finset.mem_image_of_mem roots (Finset.mem_univ k))]
    by_cases hkz : roots k = z
    · simp [conjugatePairValues, hkz]
    by_cases hkcz : roots k = conj z
    · simp [conjugatePairValues, hkz, hkcz]
    · simp [conjugatePairValues, hkz, hkcz]
  have hjneg :
      (vectorPolynomialValue coefficients (roots j) ^ 2).re < 0 := by
    rw [heval (roots j) (Finset.mem_image_of_mem roots (Finset.mem_univ j))]
    simp [conjugatePairValues, hj]
  have hsum : ∑ k, (vectorPolynomialValue coefficients (roots k) ^ 2).re < 0 := by
    have hlt :
        ∑ k, (vectorPolynomialValue coefficients (roots k) ^ 2).re < ∑ _k : Fin d, 0 :=
      Finset.sum_lt_sum (fun k _ ↦ hnonpos k) ⟨j, Finset.mem_univ j, hjneg⟩
    simpa using hlt
  exact div_neg_of_neg_of_pos hsum (by exact_mod_cast hd)

/-- For a conjugation-stable root enumeration carrying multiplicities, the
Newton--Hankel matrix is positive semidefinite exactly when every root is
real. -/
theorem newtonHankel_posSemidef_iff_roots_real {d : Nat}
    (roots : Fin d → Complex)
    (hconj : ∀ w, w ∈ Finset.univ.image roots ↔
      conj w ∈ Finset.univ.image roots) :
    Matrix.PosSemidef (newtonHankel roots) ↔
      ∀ j, ∃ r : Real, roots j = (r : Complex) := by
  constructor
  · intro hpsd j
    by_cases hj : conj (roots j) = roots j
    · rcases Complex.conj_eq_iff_real.mp hj with ⟨r, hr⟩
      exact ⟨r, hr⟩
    · exfalso
      rcases companion_trace_hankel_hermite_sylvester_bridge roots hconj
          (roots j) (Finset.mem_image_of_mem roots (Finset.mem_univ j)) hj with
        ⟨coefficients, hneg⟩
      have hnonneg := hpsd.dotProduct_mulVec_nonneg coefficients
      simp only [star_trivial] at hnonneg
      linarith
  · intro hreal
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (newtonHankel_isHermitian roots)
    intro coefficients
    simp only [star_trivial]
    rw [companion_trace_hankel_quadratic_identity]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j _
      rcases hreal j with ⟨r, hr⟩
      have hvalue :
          conj (vectorPolynomialValue coefficients (roots j)) =
            vectorPolynomialValue coefficients (roots j) := by
        rw [hr]
        simp [vectorPolynomialValue, map_sum]
      have hre := Complex.conj_eq_iff_re.mp hvalue
      rw [← hre]
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg (vectorPolynomialValue coefficients (roots j)).re
    · positivity

#print axioms companion_trace_hankel_quadratic_identity
#print axioms companion_trace_hankel_hermite_sylvester_bridge
#print axioms newtonHankel_posSemidef_iff_roots_real

end D5.S3.Constants.NewtonHankelRealRootCriterion
