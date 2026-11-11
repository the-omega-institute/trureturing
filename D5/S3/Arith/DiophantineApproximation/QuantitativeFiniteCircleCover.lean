/- GID: D5/S3/Arith/DiophantineApproximation/QuantitativeFiniteCircleCover
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/QuantitativeFiniteCircleCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.Basic, mathlib/module/Mathlib.Algebra.Order.Round, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A bounded integer block meets every open interval of width w after excluding the explicit small-denominator obstructions. -/

/-
The finite-cover argument is from the completed Pro research input
non-dyadic-actual-price-power-followup.answer.txt, finite-circle lemma (28).
The implementation below uses the pinned Mathlib Dirichlet theorem directly.
No irrationality assumption occurs, including in the reduced-grid construction.
-/

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! A bounded integer block meets every open interval of width `w` after the
explicit small-denominator obstructions are excluded. -/

namespace D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover

/-- Bézout and integer remainder explicitly lift every grid residue to an index
in the half-open block `0 ≤ k < q`. The integer lift has the sign required by
the final circle interval. Consumed by `rational_grid_near`. -/
private theorem coprime_grid_representation (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcp : Nat.Coprime p.natAbs q) (r : ℤ) :
    ∃ k : ℕ, k < q ∧ ∃ ell : ℤ, (k : ℤ) * p - ell * (q : ℤ) = r := by
  have hcp' : IsCoprime p (q : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa only [Int.natAbs_natCast] using hcp)
  obtain ⟨u, v, hbez⟩ := hcp'
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq
  let k : ℕ := ((u * r) % (q : ℤ)).toNat
  have hkcast : (k : ℤ) = (u * r) % (q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have hkz : (k : ℤ) < (q : ℤ) := by
    rw [hkcast]
    exact Int.emod_lt_of_pos _ hqz
  have hk : k < q := by exact_mod_cast hkz
  have hdivision :
      (k : ℤ) + (q : ℤ) * ((u * r) / (q : ℤ)) = u * r := by
    rw [hkcast]
    exact Int.emod_add_mul_ediv _ _
  refine ⟨k, hk, -(v * r + p * ((u * r) / (q : ℤ))), ?_⟩
  linear_combination p * hdivision + r * hbez

/-- A reduced rational grid has covering radius `1 / (2*q)`, with an actual
bounded natural index and integer lift. Consumed by `orbit_near_of_approx`. -/
private theorem rational_grid_near (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcp : Nat.Coprime p.natAbs q) (x : ℝ) :
    ∃ k : ℕ, k < q ∧ ∃ ell : ℤ,
      |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (ell : ℝ) - x| ≤
        1 / (2 * (q : ℝ)) := by
  let r : ℤ := round ((q : ℝ) * x)
  obtain ⟨k, hk, ell, hgrid⟩ := coprime_grid_representation p q hq hcp r
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hgridR : (k : ℝ) * (p : ℝ) - (ell : ℝ) * (q : ℝ) = (r : ℝ) := by
    exact_mod_cast hgrid
  have hquot :
      (k : ℝ) * ((p : ℝ) / (q : ℝ)) - (ell : ℝ) = (r : ℝ) / (q : ℝ) := by
    apply (eq_div_iff hqR.ne').2
    calc
      ((k : ℝ) * ((p : ℝ) / (q : ℝ)) - (ell : ℝ)) * (q : ℝ) =
          (k : ℝ) * (p : ℝ) - (ell : ℝ) * (q : ℝ) := by
            field_simp [hqR.ne']
      _ = (r : ℝ) := hgridR
  have hround : |(q : ℝ) * x - (r : ℝ)| ≤ (1 : ℝ) / 2 :=
    abs_sub_round ((q : ℝ) * x)
  have hscale :
      ((r : ℝ) / (q : ℝ) - x) * (q : ℝ) = (r : ℝ) - (q : ℝ) * x := by
    field_simp [hqR.ne']
  have herr : |(r : ℝ) / (q : ℝ) - x| * (q : ℝ) ≤ (1 : ℝ) / 2 := by
    calc
      |(r : ℝ) / (q : ℝ) - x| * (q : ℝ) =
          |((r : ℝ) / (q : ℝ) - x) * (q : ℝ)| := by
            rw [abs_mul, abs_of_pos hqR]
      _ = |(r : ℝ) - (q : ℝ) * x| := by rw [hscale]
      _ = |(q : ℝ) * x - (r : ℝ)| := abs_sub_comm _ _
      _ ≤ (1 : ℝ) / 2 := hround
  refine ⟨k, hk, ell, ?_⟩
  rw [hquot]
  calc
    |(r : ℝ) / (q : ℝ) - x| ≤ ((1 : ℝ) / 2) / (q : ℝ) :=
      (le_div_iff₀ hqR).2 herr
    _ = 1 / (2 * (q : ℝ)) := by rw [div_div]

/-- Perturb the reduced rational grid using exactly the Dirichlet error bound.
The factor `k` is bounded by the reduced denominator, not by a free density
hypothesis. Consumed by `quantitative_finite_circle_cover`. -/
private theorem orbit_near_of_approx (theta x : ℝ) (N : ℕ) (hN : 0 < N)
    (r : ℚ)
    (happrox : |theta - (r : ℝ)| ≤
      1 / (((N : ℝ) + 1) * (r.den : ℝ))) :
    ∃ k : ℕ, k < r.den ∧ ∃ ell : ℤ,
      |(k : ℝ) * theta - (ell : ℝ) - x| ≤
        1 / (2 * (r.den : ℝ)) + 1 / (N : ℝ) := by
  obtain ⟨k, hk, ell, hgrid⟩ :=
    rational_grid_near r.num r.den r.pos r.reduced x
  have hgrid' :
      |(k : ℝ) * (r : ℝ) - (ell : ℝ) - x| ≤ 1 / (2 * (r.den : ℝ)) := by
    simpa only [Rat.cast_def] using hgrid
  have hdenR : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hkR : (k : ℝ) ≤ (r.den : ℝ) := by exact_mod_cast hk.le
  have hrecip : 1 / ((N : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNR (by linarith)
  have herr : |(k : ℝ) * (theta - (r : ℝ))| ≤ 1 / (N : ℝ) := by
    calc
      |(k : ℝ) * (theta - (r : ℝ))| = (k : ℝ) * |theta - (r : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ (r.den : ℝ) * |theta - (r : ℝ)| :=
        mul_le_mul_of_nonneg_right hkR (abs_nonneg _)
      _ ≤ (r.den : ℝ) * (1 / (((N : ℝ) + 1) * (r.den : ℝ))) :=
        mul_le_mul_of_nonneg_left happrox hdenR.le
      _ = 1 / ((N : ℝ) + 1) := by
        field_simp [hdenR.ne', hN1]
      _ ≤ 1 / (N : ℝ) := hrecip
  refine ⟨k, hk, ell, ?_⟩
  calc
    |(k : ℝ) * theta - (ell : ℝ) - x| =
        |((k : ℝ) * (r : ℝ) - (ell : ℝ) - x) +
          (k : ℝ) * (theta - (r : ℝ))| := by congr 1 <;> ring
    _ ≤ |(k : ℝ) * (r : ℝ) - (ell : ℝ) - x| +
        |(k : ℝ) * (theta - (r : ℝ))| := abs_add_le _ _
    _ ≤ 1 / (2 * (r.den : ℝ)) + 1 / (N : ℝ) := add_le_add hgrid' herr

/-- Quantitative finite circle cover for every real `theta`, including rational
`theta`. With `H = ceil (4/w)`, exclude only the explicitly finite family of
small-denominator obstructions. The witness lies in `[N,2*N]` and in the open
lifted interval `(t,t+w)`. No upper-width, Diophantine, or irrationality
assumption is added.

The original all-B/all-record/RH power-scale goal remains open; this theorem
only supplies the stated finite-window result under its explicit hypotheses. -/
theorem quantitative_finite_circle_cover (theta t w : ℝ) (N : ℕ)
    (hw : 0 < w)
    (hbudget : 4 / w ≤ (N : ℝ))
    (havoid : ∀ h a : ℤ, 1 ≤ h → h ≤ ⌈(4 : ℝ) / w⌉ →
      1 / (N : ℝ) < |(h : ℝ) * theta - (a : ℝ)|) :
    ∃ b : ℕ, N ≤ b ∧ b ≤ 2 * N ∧ ∃ ell : ℤ,
      t < (b : ℝ) * theta - (ell : ℝ) ∧
        (b : ℝ) * theta - (ell : ℝ) < t + w := by
  have hNR : 0 < (N : ℝ) :=
    lt_of_lt_of_le (div_pos (by norm_num) hw) hbudget
  have hN : 0 < N := by exact_mod_cast hNR
  obtain ⟨r, happrox, hdenN⟩ := Real.exists_rat_abs_sub_le_and_den_le theta hN
  have hdenR : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hrecip : 1 / ((N : ℝ) + 1) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNR (by linarith)
  have hscaled :
      |(r.den : ℝ) * theta - (r.num : ℝ)| ≤ 1 / ((N : ℝ) + 1) := by
    calc
      |(r.den : ℝ) * theta - (r.num : ℝ)| =
          |(r.den : ℝ) * (theta - (r : ℝ))| := by
            congr 1
            rw [Rat.cast_def]
            field_simp [hdenR.ne']
      _ = (r.den : ℝ) * |theta - (r : ℝ)| := by
        rw [abs_mul, abs_of_pos hdenR]
      _ ≤ (r.den : ℝ) * (1 / (((N : ℝ) + 1) * (r.den : ℝ))) :=
        mul_le_mul_of_nonneg_left happrox hdenR.le
      _ = 1 / ((N : ℝ) + 1) := by
        field_simp [hdenR.ne', hN1]
  have hdenH : ⌈(4 : ℝ) / w⌉ < (r.den : ℤ) := by
    by_contra hnot
    have hdle : (r.den : ℤ) ≤ ⌈(4 : ℝ) / w⌉ := le_of_not_gt hnot
    have hd1 : (1 : ℤ) ≤ (r.den : ℤ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr r.pos)
    have hbad := havoid (r.den : ℤ) r.num hd1 hdle
    have hgood : |(r.den : ℝ) * theta - (r.num : ℝ)| ≤ 1 / (N : ℝ) :=
      hscaled.trans hrecip
    have hbad' : 1 / (N : ℝ) < |(r.den : ℝ) * theta - (r.num : ℝ)| := by
      simpa only [Int.cast_natCast] using hbad
    exact (not_lt_of_ge hgood) hbad'
  have hdenlarge : 4 / w < (r.den : ℝ) := by
    have hcast : (⌈(4 : ℝ) / w⌉ : ℝ) < (r.den : ℝ) := by
      exact_mod_cast hdenH
    exact lt_of_le_of_lt (Int.le_ceil ((4 : ℝ) / w)) hcast
  have hqw : 4 < (r.den : ℝ) * w := (div_lt_iff₀ hw).1 hdenlarge
  have hNw : 4 ≤ (N : ℝ) * w := (div_le_iff₀ hw).1 hbudget
  have hmesh : 1 / (2 * (r.den : ℝ)) < w / 8 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hdenR)).2
    nlinarith [hqw]
  have herror : 1 / (N : ℝ) ≤ w / 4 := by
    apply (div_le_iff₀ hNR).2
    nlinarith [hNw]
  have hradius : 1 / (2 * (r.den : ℝ)) + 1 / (N : ℝ) < w / 2 := by
    linarith
  obtain ⟨k, hk, ell, hcover⟩ :=
    orbit_near_of_approx theta (t + w / 2 - (N : ℝ) * theta) N hN r happrox
  have hcenter :
      |((N + k : ℕ) : ℝ) * theta - (ell : ℝ) - (t + w / 2)| < w / 2 := by
    have htranslate :
        ((N + k : ℕ) : ℝ) * theta - (ell : ℝ) - (t + w / 2) =
          (k : ℝ) * theta - (ell : ℝ) - (t + w / 2 - (N : ℝ) * theta) := by
      push_cast
      ring
    rw [htranslate]
    exact lt_of_le_of_lt hcover hradius
  obtain ⟨hlower, hupper⟩ := abs_lt.mp hcenter
  exact ⟨N + k, by omega, by omega, ell, by linarith, by linarith⟩

end D5.S3.Arith.DiophantineApproximation.QuantitativeFiniteCircleCover
