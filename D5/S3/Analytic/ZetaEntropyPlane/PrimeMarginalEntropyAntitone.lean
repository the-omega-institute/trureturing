/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeMarginalEntropyAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime entropy falls strictly; endpoints and zero exponent audit sharp hypotheses. -/
/- Library-search audit trail (2026-08-25):
   * The repository search found the required closed form in `PrimeMarginalEntropy`
     and no existing monotonicity theorem for its geometric entropy expression.
   * Pinned Mathlib supplies `strictMonoOn_of_deriv_pos`, `Real.hasDerivAt_log`,
     `Real.log_neg`, and `Real.rpow_lt_rpow_of_neg`; all are reused below.
   * Mathlib has no combined prime-marginal entropy antitonicity declaration. -/

import D5.S3.Analytic.Zeta.PrimeMarginalEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeMarginalEntropyAntitone

open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
open D5.S3.Analytic.Zeta.ZetaEntropy
open Set

noncomputable section

/-- Entropy of a geometric distribution, expressed in terms of its ratio. -/
def hGeom (q : Real) : Real :=
  -Real.log (1 - q) - (q / (1 - q)) * Real.log q

private lemma hasDerivAt_hGeom (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt hGeom (-Real.log q / (1 - q) ^ 2) q := by
  have hq_ne : q ≠ 0 := hq0.ne'
  have hden_ne : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hlog_one_sub :
      HasDerivAt (fun x : Real => Real.log (1 - x)) (-1 / (1 - q)) q := by
    have h :=
      ((hasDerivAt_const q (1 : Real)).sub (hasDerivAt_id q)).log hden_ne
    simpa using h
  have hratio :
      HasDerivAt (fun x : Real => x / (1 - x)) (1 / (1 - q) ^ 2) q := by
    have hraw := (hasDerivAt_id q).fun_div ((hasDerivAt_id q).const_sub 1) hden_ne
    exact hraw.congr_deriv (by
      simp only [id_eq]
      field_simp [hden_ne]
      ring)
  have hraw := hlog_one_sub.neg.sub (hratio.mul (Real.hasDerivAt_log hq_ne))
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · rfl
  · field_simp [hq_ne, hden_ne]
    ring

private lemma hGeom_pos {q : Real} (hq : q ∈ Ioo (0 : Real) 1) : 0 < hGeom q := by
  have hfirst : 0 < -Real.log (1 - q) :=
    neg_pos.mpr (Real.log_neg (sub_pos.mpr hq.2) (by linarith [hq.1]))
  have hratio : 0 < q / (1 - q) := div_pos hq.1 (sub_pos.mpr hq.2)
  have hsecond : 0 < -(q / (1 - q) * Real.log q) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg hratio (Real.log_neg hq.1 hq.2))
  unfold hGeom
  linarith

/-- Lean's totalized logarithm and division give value zero at both endpoints. -/
theorem hGeom_endpoint_values : hGeom 0 = 0 ∧ hGeom 1 = 0 := by
  norm_num [hGeom]
#print axioms hGeom_endpoint_values

/-- Geometric entropy is strictly increasing for ratios strictly between zero and one. -/
theorem hGeom_strictMonoOn : StrictMonoOn hGeom (Ioo (0 : Real) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
  · intro q hq
    exact (hasDerivAt_hGeom q hq.1 hq.2).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : q ∈ Ioo (0 : Real) 1 := by
      simpa only [interior_Ioo] using hq
    rw [(hasDerivAt_hGeom q hq'.1 hq'.2).deriv]
    exact div_pos (neg_pos.mpr (Real.log_neg hq'.1 hq'.2)) (sq_pos_of_pos (sub_pos.mpr hq'.2))
#print axioms hGeom_strictMonoOn

/-- The lower endpoint can be included without losing strict monotonicity. -/
theorem hGeom_strictMonoOn_Ico : StrictMonoOn hGeom (Ico (0 : Real) 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    rw [hGeom_endpoint_values.1]
    exact hGeom_pos (by exact ⟨hxy, hy.2⟩)
  · exact hGeom_strictMonoOn ⟨hx0, hx.2⟩ ⟨hx0.trans hxy, hy.2⟩ hxy
#print axioms hGeom_strictMonoOn_Ico

/-- The upper endpoint cannot be included under Lean's totalized real operations. -/
theorem upper_endpoint_is_necessary :
    ¬ StrictMonoOn hGeom (Ioc (0 : Real) 1) := by
  intro hmono
  have hlt := hmono
    (show (1 / 2 : Real) ∈ Ioc (0 : Real) 1 by norm_num)
    (show (1 : Real) ∈ Ioc (0 : Real) 1 by norm_num)
    (by norm_num)
  rw [hGeom_endpoint_values.2] at hlt
  exact (not_lt_of_ge (hGeom_pos (by norm_num : (1 / 2 : Real) ∈ Ioo 0 1)).le) hlt
#print axioms upper_endpoint_is_necessary

/-- A positive exponent makes prime negative powers strictly decrease with the prime. -/
theorem prime_rpow_lt_of_lt
    (s : Real) (hs : 0 < s) (p r : Nat.Primes) (hpr : p.1 < r.1) :
    (r.1 : Real) ^ (-s) < (p.1 : Real) ^ (-s) := by
  exact Real.rpow_lt_rpow_of_neg (by exact_mod_cast p.2.pos)
    (by exact_mod_cast hpr) (neg_lt_zero.mpr hs)
#print axioms prime_rpow_lt_of_lt

/-- At exponent zero, even the concrete ordered primes two and three have equal weights. -/
theorem positive_exponent_is_necessary :
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    let r : Nat.Primes := ⟨3, Nat.prime_three⟩
    p.1 < r.1 ∧ ¬ ((r.1 : Real) ^ (-(0 : Real)) < (p.1 : Real) ^ (-(0 : Real))) := by
  norm_num
#print axioms positive_exponent_is_necessary

/-- At exponent one the two-three prime weight comparison remains strict. -/
theorem two_three_rpow_at_one :
    (3 : Real) ^ (-(1 : Real)) < (2 : Real) ^ (-(1 : Real)) := by
  exact prime_rpow_lt_of_lt 1 zero_lt_one
    (⟨2, Nat.prime_two⟩ : Nat.Primes) (⟨3, Nat.prime_three⟩ : Nat.Primes) (by norm_num)
#print axioms two_three_rpow_at_one

/-- The existing prime-marginal entropy formula is exactly `hGeom` at the prime ratio. -/
theorem primeExponent_entropy_eq_hGeom (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    countableEntropy (primeExponentPMF s hs p) = hGeom ((p.1 : Real) ^ (-s)) := by
  rw [primeExponent_entropy_eq]
  unfold hGeom
  rw [Real.log_rpow (by exact_mod_cast p.2.pos)]
  ring
#print axioms primeExponent_entropy_eq_hGeom

/-- At fixed inverse temperature above one, prime-marginal entropy strictly decreases. -/
theorem primeExponent_entropy_strictAntitone
    (s : Real) (hs : 1 < s) (p r : Nat.Primes) (hpr : p.1 < r.1) :
    countableEntropy (primeExponentPMF s hs r) <
      countableEntropy (primeExponentPMF s hs p) := by
  rw [primeExponent_entropy_eq_hGeom, primeExponent_entropy_eq_hGeom]
  apply hGeom_strictMonoOn
  · exact ⟨Real.rpow_pos_of_pos (by exact_mod_cast r.2.pos) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast r.2.one_lt) (by linarith)⟩
  · exact ⟨Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)⟩
  · exact prime_rpow_lt_of_lt s (by linarith) p r hpr
#print axioms primeExponent_entropy_strictAntitone

/-- Without strict prime order, both the weight and entropy conclusions fail at prime two. -/
theorem strict_prime_order_is_necessary :
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    ¬ ((p.1 : Real) ^ (-(2 : Real)) < (p.1 : Real) ^ (-(2 : Real))) ∧
      ¬ (countableEntropy (primeExponentPMF 2 (by norm_num) p) <
        countableEntropy (primeExponentPMF 2 (by norm_num) p)) := by
  simp
#print axioms strict_prime_order_is_necessary

/-- For the smallest ordered prime pair, the three-coordinate entropy is strictly smaller. -/
theorem two_three_entropy_strict (s : Real) (hs : 1 < s) :
    countableEntropy
        (primeExponentPMF s hs (⟨3, Nat.prime_three⟩ : Nat.Primes)) <
      countableEntropy
        (primeExponentPMF s hs (⟨2, Nat.prime_two⟩ : Nat.Primes)) := by
  exact primeExponent_entropy_strictAntitone s hs
    (⟨2, Nat.prime_two⟩ : Nat.Primes) (⟨3, Nat.prime_three⟩ : Nat.Primes) (by norm_num)
#print axioms two_three_entropy_strict

/- Degeneracy audit:
   * As `q -> 0+`, both terms tend to zero, matching `hGeom 0 = 0`; the lower
     endpoint is therefore included by `hGeom_strictMonoOn_Ico`.
   * As `q -> 1-`, `-log (1-q) -> +infinity` while the second term tends to one,
     but totalization gives `hGeom 1 = 0`; `upper_endpoint_is_necessary` records
     the resulting counterexample to including one.
   * Negative-power antitonicity needs only `0 < s`; it remains true at `s = 1`.
     The stronger `1 < s` is retained solely because `primeExponentPMF` requires it.
   * Every theorem assumption is used. The two non-definitional strict assumptions
     have the named counterexamples above; the PMF convergence proof is a dependent
     constructor argument, so there is no well-typed counterexample without it.
   * No type parameters, maps, or natural-number indices occur in the main statement;
     empty types, singleton types, constant maps, identity maps, zero maps, and `n = 0`
     therefore introduce no additional hypothesis. -/

end

end D5.S3.Analytic.ZetaEntropyPlane.PrimeMarginalEntropyAntitone
