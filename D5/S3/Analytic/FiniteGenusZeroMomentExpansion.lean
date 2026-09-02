/- GID: D5/S3/Analytic/FiniteGenusZeroMomentExpansion
   generality: G
   mirror-B: D5/B/S3/Analytic/FiniteGenusZeroMomentExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite genus-zero factors have an exact logarithmic derivative and moment expansion. -/

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic

/- Library-search audit trail (2026-09-02):
   * Six-route searches covered genus-zero products, central inverse-power moments,
     logarithmic derivatives, finite geometric remainders, digestion receipts,
     theorem-body generalizations, and every in-flight lane. Existing D5 results
     treat Gamma Weierstrass factors, unrelated power sums, or positive Fredholm
     products; none states the finite identities below.
   * Pinned Mathlib supplies `logDeriv_prod`, `logDeriv_fun_pow`,
     `geom_sum_mul_neg`, and `Finset.sum_comm`; they are used directly.
   * The source's infinite canonical product and analytic Taylor expansion require
     convergence and order infrastructure. The corrected statement is finite and
     retains the exact truncation remainder, with every denominator nonzero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.FiniteGenusZeroMomentExpansion

/-- The finite product built from genus-zero factors and natural multiplicities. -/
noncomputable def centralProduct {J : Type*} (s : Finset J)
    (v : J -> ℂ) (m : J -> Nat) (w : ℂ) : ℂ :=
  ∏ j ∈ s, (1 + v j * w) ^ m j

/-- The finite weighted power sum of the nodes. -/
noncomputable def centralMoment {J : Type*} (s : Finset J)
    (v : J -> ℂ) (m : J -> Nat) (n : Nat) : ℂ :=
  ∑ j ∈ s, (m j : ℂ) * v j ^ n

/-- The partial-fraction sum attached to the finite product. -/
noncomputable def centralLogSum {J : Type*} (s : Finset J)
    (v : J -> ℂ) (m : J -> Nat) (w : ℂ) : ℂ :=
  ∑ j ∈ s, (m j : ℂ) * v j / (1 + v j * w)

/-- The exact remainder after truncating the finite central-moment expansion. -/
noncomputable def centralMomentRemainder {J : Type*} (s : Finset J)
    (v : J -> ℂ) (m : J -> Nat) (w : ℂ) (K : Nat) : ℂ :=
  ∑ j ∈ s,
    (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w)

/-- The logarithmic derivative of a finite genus-zero product is its
partial-fraction sum. -/
theorem logDeriv_centralProduct {J : Type*} (s : Finset J)
    (v : J -> ℂ) (m : J -> Nat) (w : ℂ)
    (hw : ∀ j ∈ s, 1 + v j * w ≠ 0) :
    logDeriv (centralProduct s v m) w = centralLogSum s v m w := by
  unfold centralProduct centralLogSum
  rw [logDeriv_prod (f := fun j z => (1 + v j * z) ^ m j)
    (fun j hj => pow_ne_zero _ (hw j hj)) (fun j _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  have hd : HasDerivAt (fun z : ℂ => 1 + v j * z) (v j) w := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id w).const_mul (v j)).const_add 1
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring

private theorem reciprocal_one_add_eq_geom_add_remainder
    (a : ℂ) (K : Nat) (ha : 1 + a ≠ 0) :
    1 / (1 + a) =
      (∑ n ∈ Finset.range K, (-a) ^ n) + (-a) ^ K / (1 + a) := by
  rw [div_eq_iff ha, add_mul, div_mul_cancel₀ _ ha]
  rw [show 1 + a = 1 - (-a) by ring, geom_sum_mul_neg]
  ring

private theorem sum_weighted_geometric_eq_moment_sum {J : Type*}
    (s : Finset J) (v : J -> ℂ) (m : J -> Nat) (w : ℂ) (K : Nat) :
    (∑ j ∈ s, (m j : ℂ) * v j *
      ∑ n ∈ Finset.range K, (-(v j * w)) ^ n) =
      ∑ n ∈ Finset.range K,
        (-1 : ℂ) ^ n * centralMoment s v m (n + 1) * w ^ n := by
  unfold centralMoment
  calc
    (∑ j ∈ s, (m j : ℂ) * v j *
        ∑ n ∈ Finset.range K, (-(v j * w)) ^ n) =
        ∑ j ∈ s, ∑ n ∈ Finset.range K,
          (m j : ℂ) * v j * (-(v j * w)) ^ n := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range K, ∑ j ∈ s,
        (m j : ℂ) * v j * (-(v j * w)) ^ n := by
          rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range K,
        (-1 : ℂ) ^ n * (∑ j ∈ s, (m j : ℂ) * v j ^ (n + 1)) *
          w ^ n := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- The finite logarithmic sum has the central-moment expansion through every
order, plus an exact remainder. -/
theorem centralLogSum_eq_momentExpansion_add_remainder {J : Type*}
    (s : Finset J) (v : J -> ℂ) (m : J -> Nat) (w : ℂ) (K : Nat)
    (hw : ∀ j ∈ s, 1 + v j * w ≠ 0) :
    centralLogSum s v m w =
      (∑ n ∈ Finset.range K,
        (-1 : ℂ) ^ n * centralMoment s v m (n + 1) * w ^ n) +
      centralMomentRemainder s v m w K := by
  have hnode : ∀ j ∈ s,
      (m j : ℂ) * v j / (1 + v j * w) =
        (m j : ℂ) * v j * (∑ n ∈ Finset.range K, (-(v j * w)) ^ n) +
          (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w) := by
    intro j hj
    have hgeom := reciprocal_one_add_eq_geom_add_remainder
      (v j * w) K (hw j hj)
    calc
      (m j : ℂ) * v j / (1 + v j * w) =
          (m j : ℂ) * v j * (1 / (1 + v j * w)) := by ring
      _ = (m j : ℂ) * v j *
          ((∑ n ∈ Finset.range K, (-(v j * w)) ^ n) +
            (-(v j * w)) ^ K / (1 + v j * w)) := by rw [hgeom]
      _ = (m j : ℂ) * v j * (∑ n ∈ Finset.range K, (-(v j * w)) ^ n) +
          (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w) := by ring
  unfold centralLogSum centralMomentRemainder
  calc
    (∑ j ∈ s, (m j : ℂ) * v j / (1 + v j * w)) =
        ∑ j ∈ s,
          ((m j : ℂ) * v j * (∑ n ∈ Finset.range K, (-(v j * w)) ^ n) +
            (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w)) := by
              apply Finset.sum_congr rfl
              exact hnode
    _ = (∑ j ∈ s, (m j : ℂ) * v j *
          ∑ n ∈ Finset.range K, (-(v j * w)) ^ n) +
        ∑ j ∈ s,
          (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range K,
          (-1 : ℂ) ^ n * centralMoment s v m (n + 1) * w ^ n) +
        ∑ j ∈ s,
          (m j : ℂ) * v j * (-(v j * w)) ^ K / (1 + v j * w) := by
            rw [sum_weighted_geometric_eq_moment_sum]

#print axioms logDeriv_centralProduct
#print axioms centralLogSum_eq_momentExpansion_add_remainder

end D5.S3.Analytic.FiniteGenusZeroMomentExpansion
