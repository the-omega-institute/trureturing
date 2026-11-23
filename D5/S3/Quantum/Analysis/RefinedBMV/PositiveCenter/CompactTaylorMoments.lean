/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point enclosures for the regularized marginal and tilted joint moments. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalTails

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open SmallCorner (momentHorner normalizedMomentCoeffs normalized_moment_eval_swap
  normalized_moment_eval_joint)

theorem Model.horner_sound {s t z x : ℝ} {X : Model} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (cs : List ℚ) :
    (Model.horner cs X).Encloses s t z (momentHorner x cs) := by
  induction cs with
  | nil => exact Model.zero_sound s t z
  | cons c cs ih =>
    simpa only [Model.horner, List.foldr_cons, momentHorner, mul_comm x, add_comm (c : ℝ)]
      using Model.add_sound (Model.mul_sound hb ih hx) (Model.ofRat_sound c s t z)

/-- Enclose a tilted moment with the spacing coefficients collected before rounding. -/
def tiltedMoment (j terms : ℕ) (r : ℚ) (X H : Model) : Model :=
  let approximation := Model.series terms (fun n => Model.horner (compactTiltedMomentCoefficients j n) H) X
  approximation.widen ((36 / 11 : ℚ) ^ j * (7 / 44) * (2 * r) ^ terms /
    (terms.factorial : ℚ) / (1 - 2 * r / (terms.succ : ℚ)))

theorem tiltedMoment_sound {p j terms : ℕ} (hp : 11 ≤ p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X H : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (tiltedMoment j terms r X H).Encloses s t z (compactPositiveMoment p j x) := by
  apply Model.widen_sound (g := compactPositiveMomentTaylorUpTo (3 / (p : ℝ)) j terms x)
  · unfold compactPositiveMomentTaylorUpTo
    apply Model.series_sound hb hx
    intro n _
    rw [← compactTiltedMomentCoefficients_eval]
    exact Model.horner_sound hb hh _
  · push_cast
    simpa only [Nat.cast_succ] using compactPositiveMoment_sub_taylorUpTo_le hp hm hr hsmall

private theorem marginalTaylorUpTo_eq_moments {p : ℕ} (hp : 0 < p) (k terms : ℕ) (x : ℝ) :
    compactMarginalTaylorUpTo p k terms x =
      ∑ i ∈ Finset.range terms,
        (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k + i + 2)) *
          ((k + i).factorial : ℝ) / (i.factorial : ℝ)) * x ^ i := by
  unfold compactMarginalTaylorUpTo
  apply Finset.sum_congr rfl
  intro i _
  rw [normalized_moment_eval_swap 0 (k + i + 2) (by omega), normalized_moment_eval_joint hp]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_succ, Nat.cast_succ]
  field_simp [show (0 : ℝ) < (k + i).factorial by positivity,
    show (0 : ℝ) < i.factorial by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 + 1 by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 2 by positivity]
  <;> ring

/-- Approximate a derivative of the regularized marginal on a centered interval. -/
def marginalMoment (k terms : ℕ) (r : ℚ) (X H : Model) : Model :=
  let approximation := Model.series terms (fun i =>
    (Model.horner (normalizedMomentCoeffs 0 (k + i + 2)) H).mul
      (Model.ofRat (((k + i).factorial : ℚ) / i.factorial))) X
  approximation.widen (((2 : ℚ) ^ (k + 1) * (2 * r) ^ terms / (terms.factorial : ℚ) /
    (1 - 2 * r / (terms.succ : ℚ))) / (((terms + k : ℕ) : ℚ) + 1) / (((terms + k : ℕ) : ℚ) + 2))

theorem marginalMoment_sound {p k terms : ℕ} (hp : 0 < p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X H : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (marginalMoment k terms r X H).Encloses s t z (iteratedDeriv k (compactZ p) x) := by
  apply Model.widen_sound (g := compactMarginalTaylorUpTo p k terms x)
  · rw [marginalTaylorUpTo_eq_moments hp]
    apply Model.series_sound hb hx
    intro i _
    simpa only [Rat.cast_div, Rat.cast_natCast, mul_div_assoc] using
      Model.mul_sound hb (Model.horner_sound hb hh (normalizedMomentCoeffs 0 (k + i + 2)))
        (Model.ofRat_sound (((k + i).factorial : ℚ) / i.factorial) s t z)
  · push_cast
    simpa only [Nat.cast_succ, Nat.cast_add] using
      iteratedDeriv_compactZ_sub_taylorUpTo_le (k := k) hp hm hr hsmall

/-- Assemble the even Taylor lower bound from the enclosed tilted moments. -/
def jointEvenTaylor (order : ℕ) (A InvSinhc : Model) (moment : ℕ → Model) : Model :=
  InvSinhc.mul (Model.sum order fun j =>
    ((A.pow (2 * j)).mul (Model.ofRat (1 / ((2 * j + 1).factorial : ℚ)))).mul (moment j))

theorem jointEvenTaylor_sound {p order : ℕ} {s t z u v : ℝ}
    {A InvSinhc : Model} {moment : ℕ → Model}
    (hb : InBox s t z) (ha : A.Encloses s t z (u / 2))
    (hInv : InvSinhc.Encloses s t z (1 / (Real.sinh ((3 / (p : ℝ)) * (u / 2)) /
      ((3 / (p : ℝ)) * (u / 2)))))
    (hm : ∀ j < order, (moment j).Encloses s t z (compactPositiveMoment p (2 * j) (v - u / 2))) :
    (jointEvenTaylor order A InvSinhc moment).Encloses s t z
      (compositionMomentEvenTaylor p order u v) := by
  have hsum := Model.sum_sound (n := order)
    (c := fun j => ((A.pow (2 * j)).mul (Model.ofRat (1 / ((2 * j + 1).factorial : ℚ)))).mul (moment j))
    (f := fun j => ((u / 2) ^ (2 * j) / ((2 * j + 1).factorial : ℝ)) *
      compactPositiveMoment p (2 * j) (v - u / 2)) (by
    intro j hj
    have hcoefficient := Model.mul_sound hb (Model.pow_sound hb ha (2 * j))
      (Model.ofRat_sound (1 / ((2 * j + 1).factorial : ℚ)) s t z)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, mul_one_div] using
      Model.mul_sound hb hcoefficient (hm j hj))
  simpa only [jointEvenTaylor, compositionMomentEvenTaylor, one_div_div] using
    Model.mul_sound hb hInv hsum

end RefinedBMV.PositiveCenter.CompactTaylorModel
