/- GID: D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assuming every complete quotient satisfies a nonzero integral quadratic whose three coefficients are uniformly bounded, a quadratic irrational has eventually periodic continued-fraction coefficients; the required uniform bound is not proved here. -/

import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Defs

/- Library-search audit trail (2026-08-23):
   * `rg -n -F 'quadratic_irrational_eventually_periodic_of_bounded_complete_quotients'
     D5 Golden/Frozen/accepted` returned no hit.
   * Repository searches for `periodic|reduced|Galois|完全商` found no public or private theorem
     proving this direction. The brief's `PeriodicImpliesQuadratic` module is absent from both
     this worktree and `origin/dev`, so its promised definitions could not be imported.
   * Pinned-Mathlib searches for Lagrange's theorem, periodic quadratic irrationals, and reduced
     quadratic irrationals found no matching theorem. This proof reuses `GenContFract.of_s_succ`,
     `Polynomial.finite_setOf_isRoot`, `Set.Infinite.exists_ne_map_eq_of_mapsTo`,
     `Set.finite_Icc`, and `Set.Finite.prod`.
   * The unproved hard step is exposed in `BoundedCompleteQuotientCertificate`: uniformly bounded
     nonzero integer quadratic coefficients for every complete quotient. The theorem proves the
     resulting finite state space implies periodicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic

/-- An irrational real satisfying a nonzero integral polynomial of degree at most two. -/
def IsQuadraticIrrational (x : ℝ) : Prop :=
  Irrational x ∧
    ∃ a b c : ℤ,
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0

/-- The `n`th complete quotient, obtained by iterating inverse fractional part. -/
noncomputable def completeQuotient (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => completeQuotient (Int.fract x)⁻¹ n

/-- The real polynomial encoded by an integral quadratic coefficient triple. -/
noncomputable def quadraticPolynomial (coefficients : ℤ × ℤ × ℤ) : Polynomial ℝ :=
  Polynomial.monomial 0 (coefficients.2.2 : ℝ) +
    Polynomial.monomial 1 (coefficients.2.1 : ℝ) +
      Polynomial.monomial 2 (coefficients.1 : ℝ)

/-- A nonzero integral coefficient triple encodes a nonzero real polynomial. -/
theorem quadraticPolynomial_ne_zero (coefficients : ℤ × ℤ × ℤ)
    (hcoefficients : coefficients ≠ (0, 0, 0)) :
    quadraticPolynomial coefficients ≠ 0 := by
  rcases coefficients with ⟨a, b, c⟩
  intro hzero
  apply hcoefficients
  have ha : a = 0 := by
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 2) hzero
    simp only [quadraticPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial] at hcoeff
    norm_num at hcoeff
    exact hcoeff
  have hb : b = 0 := by
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) hzero
    simp only [quadraticPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial] at hcoeff
    norm_num at hcoeff
    exact hcoeff
  have hc : c = 0 := by
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 0) hzero
    simp only [quadraticPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial] at hcoeff
    norm_num at hcoeff
    exact hcoeff
  exact Prod.ext ha (Prod.ext hb hc)

/-- A finite-state certificate for the difficult boundedness step in Lagrange's theorem.
Each complete quotient is represented by a uniformly bounded integral quadratic coefficient
triple. -/
structure BoundedCompleteQuotientCertificate (x : ℝ) where
  bound : ℕ
  coefficients : ℕ → ℤ × ℤ × ℤ
  nonzero : ∀ n, coefficients n ≠ (0, 0, 0)
  bounded : ∀ n,
    |(coefficients n).1| ≤ (bound : ℤ) ∧
      |(coefficients n).2.1| ≤ (bound : ℤ) ∧
        |(coefficients n).2.2| ≤ (bound : ℤ)
  equation : ∀ n,
    let q := completeQuotient x n
    ((coefficients n).1 : ℝ) * q ^ 2 +
        ((coefficients n).2.1 : ℝ) * q + ((coefficients n).2.2 : ℝ) = 0

/-- The coefficient stream of a generalized continued fraction is periodic after some index. -/
def EventuallyPeriodicCoefficients (g : GenContFract ℝ) : Prop :=
  ∃ start period : ℕ, 0 < period ∧
    ∀ offset : ℕ,
      g.s.get? (start + offset + period) = g.s.get? (start + offset)

/-- Shifting the coefficient stream by `steps` exposes the continued fraction of the
corresponding complete quotient. -/
theorem of_s_get?_add_eq_completeQuotient (x : ℝ) (offset steps : ℕ) :
    (GenContFract.of x).s.get? (offset + steps) =
      (GenContFract.of (completeQuotient x steps)).s.get? offset := by
  induction steps generalizing x with
  | zero => rfl
  | succ steps ih =>
      calc
        (GenContFract.of x).s.get? (offset + Nat.succ steps) =
            (GenContFract.of x).s.get? ((offset + steps) + 1) := by
              rw [Nat.add_assoc]
        _ = (GenContFract.of (Int.fract x)⁻¹).s.get? (offset + steps) :=
          GenContFract.of_s_succ x (offset + steps)
        _ = (GenContFract.of (completeQuotient (Int.fract x)⁻¹ steps)).s.get? offset :=
          ih (Int.fract x)⁻¹
        _ = (GenContFract.of (completeQuotient x (Nat.succ steps))).s.get? offset := rfl

/-- Conditional Lagrange direction B: the explicitly assumed bounded complete-quotient
certificate forces the regular continued-fraction coefficient stream to be eventually periodic. -/
theorem quadratic_irrational_eventually_periodic_of_bounded_complete_quotients
    (x : ℝ) (_hx : IsQuadraticIrrational x)
    (certificate : BoundedCompleteQuotientCertificate x) :
    EventuallyPeriodicCoefficients (GenContFract.of x) := by
  let coefficientInterval : Set ℤ :=
    Set.Icc (-(certificate.bound : ℤ)) (certificate.bound : ℤ)
  let coefficientStates : Set (ℤ × ℤ × ℤ) :=
    coefficientInterval ×ˢ coefficientInterval ×ˢ coefficientInterval
  have coefficientStates_finite : coefficientStates.Finite := by
    exact
      (Set.finite_Icc (-(certificate.bound : ℤ)) (certificate.bound : ℤ)).prod
        ((Set.finite_Icc (-(certificate.bound : ℤ)) (certificate.bound : ℤ)).prod
          (Set.finite_Icc (-(certificate.bound : ℤ)) (certificate.bound : ℤ)))
  have coefficients_mapsTo :
      Set.MapsTo certificate.coefficients Set.univ coefficientStates := by
    intro n _
    obtain ⟨ha, hb, hc⟩ := certificate.bounded n
    exact ⟨abs_le.mp ha, abs_le.mp hb, abs_le.mp hc⟩
  have coefficientRange_finite : (Set.range certificate.coefficients).Finite :=
    coefficientStates_finite.subset fun _ ⟨n, hn⟩ =>
      hn ▸ coefficients_mapsTo (Set.mem_univ n)
  let quotientCandidates : Set ℝ :=
    ⋃ coefficients ∈ Set.range certificate.coefficients,
      {q | (quadraticPolynomial coefficients).IsRoot q}
  have quotientCandidates_finite : quotientCandidates.Finite := by
    dsimp [quotientCandidates]
    refine coefficientRange_finite.biUnion ?_
    intro coefficients hcoefficients
    apply Polynomial.finite_setOf_isRoot
    apply quadraticPolynomial_ne_zero coefficients
    obtain ⟨n, hn⟩ := hcoefficients
    exact hn ▸ certificate.nonzero n
  have quotients_mapsTo :
      Set.MapsTo (completeQuotient x) Set.univ quotientCandidates := by
    intro n _
    dsimp [quotientCandidates]
    rw [Set.mem_iUnion]
    refine ⟨certificate.coefficients n, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨⟨n, rfl⟩, ?_⟩
    change
      (quadraticPolynomial (certificate.coefficients n)).IsRoot
        (completeQuotient x n)
    rw [Polynomial.IsRoot.def]
    simpa [quadraticPolynomial, add_comm, add_left_comm, add_assoc] using
      certificate.equation n
  obtain ⟨m, _, n, _, hmn, hquotients⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo
      quotients_mapsTo quotientCandidates_finite
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · refine ⟨m, n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    intro offset
    calc
      (GenContFract.of x).s.get? (m + offset + (n - m)) =
          (GenContFract.of x).s.get? (offset + n) := by
        congr 1
        calc
          m + offset + (n - m) = (m + (n - m)) + offset := by ac_rfl
          _ = n + offset := by rw [Nat.add_sub_of_le hlt.le]
          _ = offset + n := Nat.add_comm n offset
      _ = (GenContFract.of (completeQuotient x n)).s.get? offset :=
        of_s_get?_add_eq_completeQuotient x offset n
      _ = (GenContFract.of (completeQuotient x m)).s.get? offset := by
        rw [hquotients]
      _ = (GenContFract.of x).s.get? (offset + m) :=
        (of_s_get?_add_eq_completeQuotient x offset m).symm
      _ = (GenContFract.of x).s.get? (m + offset) := by rw [Nat.add_comm]
  · refine ⟨n, m - n, Nat.sub_pos_of_lt hgt, ?_⟩
    intro offset
    calc
      (GenContFract.of x).s.get? (n + offset + (m - n)) =
          (GenContFract.of x).s.get? (offset + m) := by
        congr 1
        calc
          n + offset + (m - n) = (n + (m - n)) + offset := by ac_rfl
          _ = m + offset := by rw [Nat.add_sub_of_le hgt.le]
          _ = offset + m := Nat.add_comm m offset
      _ = (GenContFract.of (completeQuotient x m)).s.get? offset :=
        of_s_get?_add_eq_completeQuotient x offset m
      _ = (GenContFract.of (completeQuotient x n)).s.get? offset := by
        rw [hquotients]
      _ = (GenContFract.of x).s.get? (offset + n) :=
        (of_s_get?_add_eq_completeQuotient x offset n).symm
      _ = (GenContFract.of x).s.get? (n + offset) := by rw [Nat.add_comm]

example : completeQuotient 0 3 = 0 := by
  norm_num [completeQuotient]

#print axioms quadratic_irrational_eventually_periodic_of_bounded_complete_quotients

end D5.S1.Depth.ContinuedFractions.QuadraticImpliesPeriodic
