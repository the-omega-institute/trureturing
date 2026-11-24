/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorMoments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point enclosures for the regularized marginal and tilted joint moments. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalTails

/-! Fixed-point enclosures for marginal and tilted joint moments. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open DimThree (evalTerms)
open DimThree.Certificate (Term)

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

/-- Collect the rounded terms and the exact absolute residual in fixed-point units. -/
private def roundShortSpacing (k : ℕ) : List ℚ → List Term × ℚ
  | [] => ([], 0)
  | r :: rs =>
    let scaled : ℚ := r * scale
    let q : ℤ := if k ≤ 6 then round scaled else 0
    let tail := roundShortSpacing (k + 1) rs
    let ts := if q = 0 then tail.1 else ⟨(0, 0, k), q⟩ :: tail.1
    (ts, |scaled - (q : ℚ)| + tail.2)

private theorem roundShortSpacing_sound {s t z : ℝ} (hz : |z| ≤ 1) (rs : List ℚ) (k : ℕ) :
    |(scale : ℝ) * (momentHorner z rs * z ^ k) -
      evalTerms s t z (roundShortSpacing k rs).1| ≤ ((roundShortSpacing k rs).2 : ℝ) := by
  induction rs generalizing k with
  | nil => simp [roundShortSpacing, momentHorner, evalTerms]
  | cons r rs ih =>
    let q : ℤ := if k ≤ 6 then round (r * scale) else 0
    let tail := roundShortSpacing (k + 1) rs
    have he :
        evalTerms s t z (roundShortSpacing k (r :: rs)).1 =
          (q : ℝ) * z ^ k + evalTerms s t z tail.1 := by
      change evalTerms s t z (if q = 0 then tail.1 else ⟨(0, 0, k), q⟩ :: tail.1) = _
      by_cases h : q = 0 <;> simp [h, evalTerms, Term.eval]
    rw [he, momentHorner]
    change |(scale : ℝ) * (((r : ℝ) + z * momentHorner z rs) * z ^ k) -
      ((q : ℝ) * z ^ k + evalTerms s t z tail.1)| ≤
        ((|r * (scale : ℚ) - (q : ℚ)| + tail.2 : ℚ) : ℝ)
    rw [Rat.cast_add, Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
    rw [show (scale : ℝ) * (((r : ℝ) + z * momentHorner z rs) * z ^ k) -
          ((q : ℝ) * z ^ k + evalTerms s t z tail.1) =
        ((r : ℝ) * scale - (q : ℝ)) * z ^ k +
          ((scale : ℝ) * (momentHorner z rs * z ^ (k + 1)) - evalTerms s t z tail.1) by
      rw [pow_succ]
      ring]
    refine (abs_add_le ..).trans (add_le_add ?_ (ih (k + 1)))
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)

section

open private coeffAdd coeffScale from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

/-- Add the coefficients of `b + (1 + z) * p(z)`, where `bs` lists those of `p`. -/
private def addSpacingShift (b : ℤ) : List ℤ → List ℤ
  | [] => [b]
  | c :: cs => (c + b) :: addSpacingShift c cs

private def recenterSpacingInts : List ℤ → List ℤ
  | [] => []
  | b :: bs => addSpacingShift b (recenterSpacingInts bs)

private theorem addSpacingShift_cast (b : ℤ) (bs : List ℤ) :
    (addSpacingShift b bs).map (fun c : ℤ => (c : ℚ)) =
      coeffAdd (bs.map fun c : ℤ => (c : ℚ)) ((b : ℚ) :: bs.map fun c : ℤ => (c : ℚ)) := by
  induction bs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    simp only [addSpacingShift, List.map_cons, coeffAdd, Int.cast_add, ih]

private theorem recenterSpacingInts_cast (bs : List ℤ) :
    (recenterSpacingInts bs).map (fun c : ℤ => (c : ℚ)) =
      SmallCorner.recenterMomentCoeffs 1 (bs.map fun c : ℤ => (c : ℚ)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hscale (rs : List ℚ) : coeffScale 1 rs = rs := by simp [coeffScale]
    simp only [recenterSpacingInts, addSpacingShift_cast, List.map_cons,
      SmallCorner.recenterMomentCoeffs, hscale, ih]

end

/-- Round each coefficient after multiplying by its current scale factor. -/
private def roundSpacingInput (m : ℚ) : List ℚ → List ℤ
  | [] => []
  | c :: cs => round (m * c) :: roundSpacingInput (m * (3 / 22)) cs

private theorem roundSpacingInput_sound (w : ℝ) (hw : |w| ≤ 2) (m : ℚ) (cs : List ℚ) :
    |(m : ℝ) * momentHorner ((3 / 22 : ℝ) * w) cs -
      momentHorner w ((roundSpacingInput m cs).map fun b : ℤ => (b : ℚ))| ≤
      ((2 : ℝ) ^ cs.length - 1) / 2 := by
  induction cs generalizing m with
  | nil => simp [roundSpacingInput, momentHorner]
  | cons c cs ih =>
    let err := ((m * (3 / 22 : ℚ) : ℚ) : ℝ) * momentHorner ((3 / 22 : ℝ) * w) cs -
      momentHorner w ((roundSpacingInput (m * (3 / 22)) cs).map fun b : ℤ => (b : ℚ))
    have hhead : |(m : ℝ) * (c : ℝ) - (round (m * c) : ℝ)| ≤ 1 / 2 := by
      have hq := (Rat.cast_mono (K := ℝ)) (abs_sub_round (m * c))
      simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast,
        Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
    have htail : |err| ≤ ((2 : ℝ) ^ cs.length - 1) / 2 := ih (m * (3 / 22))
    simp only [roundSpacingInput, List.map_cons, momentHorner, Rat.cast_intCast,
      List.length_cons, pow_succ]
    rw [show (m : ℝ) * ((c : ℝ) + (3 / 22 : ℝ) * w *
            momentHorner ((3 / 22 : ℝ) * w) cs) -
          ((round (m * c) : ℝ) +
            w * momentHorner w ((roundSpacingInput (m * (3 / 22)) cs).map fun b : ℤ => (b : ℚ))) =
        ((m : ℝ) * (c : ℝ) - (round (m * c) : ℝ)) + w * err by
      simp only [err, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
      ring]
    calc
      _ ≤ |(m : ℝ) * (c : ℝ) - (round (m * c) : ℝ)| + |w * err| := abs_add_le ..
      _ ≤ 1 / 2 + 2 * (((2 : ℝ) ^ cs.length - 1) / 2) := by
        rw [abs_mul]
        exact add_le_add hhead (mul_le_mul hw htail (abs_nonneg _) (by norm_num))
      _ = _ := by ring

private theorem momentHorner_div (z : ℝ) (B : ℚ) (cs : List ℚ) :
    momentHorner z (cs.map fun c => c / B) = momentHorner z cs / (B : ℝ) := by
  induction cs with
  | nil => simp [momentHorner]
  | cons c cs ih =>
    simp only [List.map_cons, momentHorner, Rat.cast_div, ih]
    ring

private def shortSpacingFactor (cs : List ℚ) : ℚ := (scale : ℚ) * 2 ^ cs.length

private def shortSpacingCoeffs (cs : List ℚ) : List ℚ :=
  let B := shortSpacingFactor cs
  let bs := roundSpacingInput B cs
  (recenterSpacingInts bs).map fun b : ℤ => (b : ℚ) / B

private theorem shortSpacingCoeffs_sound (cs : List ℚ) {z h : ℝ}
    (hz : |z| ≤ 1) (hh : h = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z) :
    |momentHorner h cs - momentHorner z (shortSpacingCoeffs cs)| ≤
      (1 / 2 : ℝ) / (scale : ℝ) := by
  let B := shortSpacingFactor cs
  let bs := roundSpacingInput B cs
  let qs := bs.map fun b : ℤ => (b : ℚ)
  have hB : (B : ℝ) = (scale : ℝ) * (2 : ℝ) ^ cs.length := by
    simp only [B, shortSpacingFactor, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  have hBpos : 0 < (B : ℝ) := by
    rw [hB]
    exact mul_pos scale_real_pos (by positivity)
  have hw : |1 + z| ≤ (2 : ℝ) := by
    calc
      _ ≤ |(1 : ℝ)| + |z| := abs_add_le ..
      _ ≤ 2 := by rw [abs_one]; linarith
  have heval : momentHorner z (shortSpacingCoeffs cs) = momentHorner (1 + z) qs / (B : ℝ) := by
    change momentHorner z ((recenterSpacingInts bs).map fun b : ℤ => (b : ℚ) / B) = _
    rw [show ((recenterSpacingInts bs).map fun b : ℤ => (b : ℚ) / B) =
          ((recenterSpacingInts bs).map fun b : ℤ => (b : ℚ)).map (fun c => c / B) by
        simp only [List.map_map]
        rfl,
      momentHorner_div, recenterSpacingInts_cast]
    simpa only [Rat.cast_one, one_mul] using
      congrArg (fun x : ℝ => x / (B : ℝ)) (SmallCorner.recenterMomentCoeffs_eval 1 z qs)
  have hh' : h = (3 / 22 : ℝ) * (1 + z) := hh.trans (by ring)
  rw [heval, show momentHorner h cs - momentHorner (1 + z) qs / (B : ℝ) =
        ((B : ℝ) * momentHorner h cs - momentHorner (1 + z) qs) / (B : ℝ) by
      rw [sub_div, mul_div_cancel_left₀ _ hBpos.ne'],
    abs_div, abs_of_pos hBpos]
  apply (div_le_iff₀ hBpos).2
  calc
    _ ≤ ((2 : ℝ) ^ cs.length - 1) / 2 := by
      rw [hh']
      exact roundSpacingInput_sound (1 + z) hw B cs
    _ ≤ (2 : ℝ) ^ cs.length / 2 := by linarith
    _ = _ := by rw [hB]; field_simp [scale_real_pos.ne'] <;> ring

/-- Enclose a spacing polynomial at h = 3/22 + (3/22) * z, keeping degrees up to six. -/
def Model.shortSpacing (cs : List ℚ) : Model :=
  let rounded := roundShortSpacing 0 (shortSpacingCoeffs cs)
  -- Add the input rounding budget before the single ceiling in `widen`.
  (⟨⟨rounded.1⟩, 0⟩ : Model).widen ((rounded.2 + 1 / 2) / scale)

theorem Model.shortSpacing_sound (cs : List ℚ) {s t z h : ℝ}
    (hz : |z| ≤ 1) (hh : h = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z) :
    (Model.shortSpacing cs).Encloses s t z (momentHorner h cs) := by
  let coeffs := shortSpacingCoeffs cs
  let rounded := roundShortSpacing 0 coeffs
  let M : Model := ⟨⟨rounded.1⟩, 0⟩
  change (M.widen ((rounded.2 + 1 / 2) / scale)).Encloses s t z (momentHorner h cs)
  apply Model.widen_sound (g := M.eval s t z)
  · simp [Model.Encloses, M]
  · have hround := roundShortSpacing_sound (s := s) (t := t) hz coeffs 0
    rw [pow_zero, mul_one] at hround
    have hmodel : |momentHorner z coeffs - M.eval s t z| ≤
        (rounded.2 : ℝ) / (scale : ℝ) := by
      change |momentHorner z coeffs - evalTerms s t z rounded.1 / (scale : ℝ)| ≤ _
      rw [show momentHorner z coeffs - evalTerms s t z rounded.1 / (scale : ℝ) =
          ((scale : ℝ) * momentHorner z coeffs - evalTerms s t z rounded.1) / (scale : ℝ) by
        rw [sub_div, mul_div_cancel_left₀ _ scale_real_pos.ne']]
      rw [abs_div, abs_of_pos scale_real_pos]
      exact div_le_div_of_nonneg_right hround scale_real_pos.le
    calc
      _ ≤ |momentHorner h cs - momentHorner z coeffs| +
          |momentHorner z coeffs - M.eval s t z| := abs_sub_le ..
      _ ≤ (1 / 2 : ℝ) / (scale : ℝ) + (rounded.2 : ℝ) / (scale : ℝ) :=
        add_le_add (shortSpacingCoeffs_sound cs hz hh) hmodel
      _ = _ := by
        simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
          add_div]
        exact add_comm _ _

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

private def marginalMomentUsing (evalSpacing : List ℚ → Model) (coeffs : ℕ → List ℚ)
    (k terms : ℕ) (r : ℚ) (X : Model) : Model :=
  let approximation := Model.series terms (fun i =>
    (evalSpacing (coeffs (k + i + 2))).mul
      (Model.ofRat (((k + i).factorial : ℚ) / i.factorial))) X
  approximation.widen (((2 : ℚ) ^ (k + 1) * (2 * r) ^ terms / (terms.factorial : ℚ) /
    (1 - 2 * r / (terms.succ : ℚ))) / (((terms + k : ℕ) : ℚ) + 1) / (((terms + k : ℕ) : ℚ) + 2))

private theorem marginalMomentUsing_sound {p k terms : ℕ} {coeffs : ℕ → List ℚ}
    {evalSpacing : List ℚ → Model}
    (hcoeffs : ∀ m, momentHorner (3 / (p : ℝ)) (coeffs m) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 m))
    (hp : 0 < p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X : Model} {r : ℚ}
    (hb : InBox s t z)
    (hh : ∀ cs, (evalSpacing cs).Encloses s t z (momentHorner (3 / (p : ℝ)) cs))
    (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (marginalMomentUsing evalSpacing coeffs k terms r X).Encloses s t z
      (iteratedDeriv k (compactZ p) x) := by
  apply Model.widen_sound (g := compactMarginalTaylorUpTo p k terms x)
  · rw [marginalTaylorUpTo_eq_moments hp]
    apply Model.series_sound hb hx
    intro i _
    rw [← hcoeffs (k + i + 2)]
    simpa only [Rat.cast_div, Rat.cast_natCast, mul_div_assoc] using
      Model.mul_sound hb (hh (coeffs (k + i + 2)))
        (Model.ofRat_sound (((k + i).factorial : ℚ) / i.factorial) s t z)
  · push_cast
    simpa only [Nat.cast_succ, Nat.cast_add] using
      iteratedDeriv_compactZ_sub_taylorUpTo_le (k := k) hp hm hr hsmall

/-- Approximate a derivative of the regularized marginal using the supplied coefficient lists. -/
def marginalMomentWith (coeffs : ℕ → List ℚ) (k terms : ℕ) (r : ℚ) (X H : Model) : Model :=
  marginalMomentUsing (fun cs => Model.horner cs H) coeffs k terms r X

theorem marginalMomentWith_sound {p k terms : ℕ} {coeffs : ℕ → List ℚ}
    (hcoeffs : ∀ m, momentHorner (3 / (p : ℝ)) (coeffs m) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 m))
    (hp : 0 < p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X H : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (marginalMomentWith coeffs k terms r X H).Encloses s t z (iteratedDeriv k (compactZ p) x) :=
  marginalMomentUsing_sound (evalSpacing := fun cs => Model.horner cs H) hcoeffs hp hm hb
    (Model.horner_sound hb hh) hx hr hsmall

/-- The marginal enclosure for the short box's exact spacing coordinate. -/
def shortMarginalMomentWith (coeffs : ℕ → List ℚ) (k terms : ℕ) (r : ℚ) (X : Model) : Model :=
  marginalMomentUsing Model.shortSpacing coeffs k terms r X

theorem shortMarginalMomentWith_sound {p k terms : ℕ} {coeffs : ℕ → List ℚ}
    (hcoeffs : ∀ m, momentHorner (3 / (p : ℝ)) (coeffs m) =
      momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 m))
    (hp : 0 < p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X : Model} {r : ℚ}
    (hb : InBox s t z) (hh : 3 / (p : ℝ) = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z)
    (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (shortMarginalMomentWith coeffs k terms r X).Encloses s t z (iteratedDeriv k (compactZ p) x) :=
  marginalMomentUsing_sound (evalSpacing := Model.shortSpacing) hcoeffs hp hm hb
    (fun cs => Model.shortSpacing_sound cs hb.2.2 hh) hx hr hsmall

/-- Approximate a derivative of the regularized marginal on a centered interval. -/
def marginalMoment (k terms : ℕ) (r : ℚ) (X H : Model) : Model :=
  marginalMomentWith (normalizedMomentCoeffs 0) k terms r X H

theorem marginalMoment_sound {p k terms : ℕ} (hp : 0 < p) (hm : 2 ≤ terms)
    {s t z x : ℝ} {X H : Model} {r : ℚ}
    (hb : InBox s t z) (hh : H.Encloses s t z (3 / (p : ℝ))) (hx : X.Encloses s t z x)
    (hr : |x| ≤ (r : ℝ)) (hsmall : 2 * (r : ℝ) / (terms.succ : ℝ) < 1) :
    (marginalMoment k terms r X H).Encloses s t z (iteratedDeriv k (compactZ p) x) :=
  marginalMomentWith_sound (coeffs := normalizedMomentCoeffs 0) (fun _ => rfl)
    hp hm hb hh hx hr hsmall

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
