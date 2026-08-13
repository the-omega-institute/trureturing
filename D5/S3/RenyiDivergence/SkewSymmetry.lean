/- GID: D5/S3/RenyiDivergence/SkewSymmetry
   generality: G
   mirror-B: D5/B/S3/RenyiDivergence/SkewSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the alpha-complement skew symmetry of finite Renyi divergence. -/

/- Library-search audit trail (2026-08-13):
   * Searched pinned mathlib for `Renyi`, `Rényi`, `renyiDivergence`, real-power endpoint
     lemmas, complement-exponent arithmetic, finite-sum congruence, and division cancellation.
   * No probability-theory Renyi divergence was found; the name hits are for Erdos--Renyi
     random graphs. Reused `Real.rpow_zero`, `Finset.sum_congr`, ring normalization, and field
     cancellation. `Real.zero_rpow` confirms the zero-base convention but is not needed below.
   * Searched this working tree for every Renyi declaration and for skew symmetry, duality,
     self-duality, half-order symmetry, and alpha/`1 - alpha` formulas. No equivalent theorem
     was found. The frozen definition and half-order Bhattacharyya identity are imported.
   * The import closure is Basic -> Bhattacharyya -> Metric -> Pinsker ->
     {GrandmotherTheorem, ZeroSupportDPI} -> ClassicalDPI -> Mathlib. Every repository module
     in this closure has generality G; Mathlib is external to the repository header system.
-/

import D5.S3.RenyiDivergence.Basic

namespace D5.S3.RenyiDivergence

/-!
The product identity is primary: it expresses the common logarithmic power sum without dividing
by either exceptional order. The exact endpoint residues of the totalized definition are
`Real.log (sum p)` at order one and `Real.log (sum q)` at order zero. Thus the all-order theorem
asks only that the relevant residue vanish; normalization is sufficient, while pointwise
nonnegativity and strict positivity are unnecessary. Away from zero and one, no hypotheses on
the finite real functions are needed, and zero-base `Real.rpow` behavior causes no obstruction
because the two power sums agree termwise without changing either base or exponent.

The solved form is secondary because division by `alpha - 1` excludes order one. At order zero it
also retains the genuine `Real.log (sum q) = 0` endpoint condition. Finally, complementing the
order maps `(0, 1)` onto itself, but maps `alpha > 1` to a negative order. Consequently this
duality does not turn the frozen below-one data-processing inequality into an above-one theorem;
that gap remains open.
-/

/-- Product-form skew symmetry under the exact conditions forced at the two totalized endpoints.
The `p` condition is used only when `alpha = 1`, and the `q` condition only when `alpha = 0`. -/
theorem renyi_divergence_skew_symmetry {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real)
    (hp : alpha = 1 -> Real.log (∑ i, p i) = 0)
    (hq : alpha = 0 -> Real.log (∑ i, q i) = 0) :
    (alpha - 1) * renyiDivergence alpha p q =
      -alpha * renyiDivergence (1 - alpha) q p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  by_cases halpha_zero : alpha = 0
  · subst alpha
    simp [renyiDivergence, hq rfl]
  by_cases halpha_one : alpha = 1
  · subst alpha
    simp [renyiDivergence, hp rfl]
  rw [renyiDivergence, renyiDivergence]
  have hsum :
      (∑ i, (q i) ^ (1 - alpha) * (p i) ^ (1 - (1 - alpha))) =
        ∑ i, (p i) ^ alpha * (q i) ^ (1 - alpha) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show 1 - (1 - alpha) = alpha by ring, mul_comm]
  rw [hsum]
  rw [show 1 - alpha - 1 = -alpha by ring]
  field_simp [halpha_zero, halpha_one]

/-- Normalized laws satisfy product-form skew symmetry at every real order. No sign hypothesis is
needed: normalization is used only to make the two endpoint logarithms `Real.log 1`. -/
theorem renyi_divergence_skew_symmetry_of_normalized {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    (alpha - 1) * renyiDivergence alpha p q =
      -alpha * renyiDivergence (1 - alpha) q p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact renyi_divergence_skew_symmetry alpha p q
    (fun _ => by rw [hp, Real.log_one])
    (fun _ => by rw [hq, Real.log_one])

/-- Away from the two totalized endpoints, product-form skew symmetry is purely algebraic and
requires no normalization, nonnegativity, positivity, or support condition. -/
theorem renyi_divergence_skew_symmetry_of_ne_zero_one {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha_zero : alpha ≠ 0)
    (halpha_one : alpha ≠ 1) :
    (alpha - 1) * renyiDivergence alpha p q =
      -alpha * renyiDivergence (1 - alpha) q p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact renyi_divergence_skew_symmetry alpha p q
    (fun h => (halpha_one h).elim) (fun h => (halpha_zero h).elim)

/-- Solved-form skew symmetry. Division forces `alpha != 1`; at the retained order-zero endpoint,
the totalized definition additionally forces the displayed logarithmic condition on `q`. -/
theorem renyi_divergence_eq_scaled_dual {ι : Type*} [Fintype ι]
    (alpha : Real) (p q : ι -> Real) (halpha_one : alpha ≠ 1)
    (hq : alpha = 0 -> Real.log (∑ i, q i) = 0) :
    renyiDivergence alpha p q =
      (alpha / (1 - alpha)) * renyiDivergence (1 - alpha) q p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have hproduct := renyi_divergence_skew_symmetry alpha p q
    (fun h => (halpha_one h).elim) hq
  apply (mul_left_cancel₀ (sub_ne_zero.mpr halpha_one))
  calc
    (alpha - 1) * renyiDivergence alpha p q =
        -alpha * renyiDivergence (1 - alpha) q p := hproduct
    _ = (alpha - 1) *
        ((alpha / (1 - alpha)) * renyiDivergence (1 - alpha) q p) := by
      field_simp [halpha_one]
      ring

/-- The self-dual order is symmetric. This is a specialization of the product identity, not a
separate expansion of the definition. -/
theorem renyi_divergence_one_half_symmetry {ι : Type*} [Fintype ι]
    (p q : ι -> Real) :
    renyiDivergence (1 / 2) p q = renyiDivergence (1 / 2) q p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  have h := renyi_divergence_skew_symmetry_of_ne_zero_one
    (1 / 2) p q (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

/-- Cross-check against the frozen Bhattacharyya link. The self-dual order exchanges the two
laws, so the divergence read in the `q, p` orientation equals the Bhattacharyya expression of the
`p, q` orientation. Both notions occur in the statement and their orientations differ, so this is
the consistency claim itself rather than a Bhattacharyya identity proved through a detour. Only
nonnegativity of `p` is needed: the exchange comes from the symmetry above, not from a second
appeal to the frozen theorem. -/
theorem renyi_divergence_one_half_dual_eq_bhattacharyya
    {ι : Type*} [Fintype ι] (p q : ι -> Real)
    (hp : forall i, 0 <= p i) :
    renyiDivergence (1 / 2) q p =
      -2 * Real.log (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya p q) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  rw [renyi_divergence_one_half_symmetry q p]
  exact renyi_divergence_one_half p q hp

#print axioms renyi_divergence_skew_symmetry
#print axioms renyi_divergence_skew_symmetry_of_normalized
#print axioms renyi_divergence_skew_symmetry_of_ne_zero_one
#print axioms renyi_divergence_eq_scaled_dual
#print axioms renyi_divergence_one_half_symmetry
#print axioms renyi_divergence_one_half_dual_eq_bhattacharyya

end D5.S3.RenyiDivergence
