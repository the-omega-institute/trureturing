/- GID: D5/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryStability
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ThreeMomentMemoryStability
   mirror-E: none(waiver:all-lag-analytic-error-estimate)
   anchors: []
   utility: none
   digest: A clipped three-moment inverse estimates every memory coefficient with
     error (3+11k)*epsilon, without any positive lower bound on the coupling. -/

import D5.S3.Observer.ProbabilisticClosure.ThreeMomentMemoryRecovery
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.ThreeMomentMemoryStability

/-- Clipping concerns the reconstructed hidden multiplier, not the true state. -/
def clip (x : Real) : Real := max (-1) (min 1 x)

/-- The zero branch is essential near zero coupling. This estimator uses only
three noisy response numbers, and no hidden coordinate or coupling lower bound. -/
noncomputable def estimate (s1 s2 s3 : Real) (k : Nat) : Real :=
  let g := s2-s1^2
  let z := s3-2*s1*s2+s1^3
  if g ≤ 0 then 0 else g*(clip (z/g))^k

/-- A finite-data stability theorem for the actual scalar memory v^2*w^k.
The observed moments are u, u^2+v^2, u^3+2uv^2+v^2w. Clipping the first two
noisy moments into [-1,1] preserves their error bounds under the stated true
bounds. There is deliberately no assumption v^2 >= gamma > 0. -/
theorem three_moment_error_bound
    (u v w s1 s2 s3 epsilon : Real)
    (he : 0 ≤ epsilon) (hu : |u| ≤ 1) (hw : |w| ≤ 1)
    (hr2 : |u^2+v^2| ≤ 1) (hs1 : |s1| ≤ 1) (hs2 : |s2| ≤ 1)
    (h1 : |s1-u| ≤ epsilon)
    (h2 : |s2-(u^2+v^2)| ≤ epsilon)
    (h3 : |s3-(u^3+2*u*v^2+v^2*w)| ≤ epsilon) (k : Nat) :
    |estimate s1 s2 s3 k-v^2*w^k| ≤ (3+11*(k : Real))*epsilon := by
  have subTriangle (a b : Real) : |a-b| ≤ |a|+|b| := by
    simpa using (abs_sub_le a 0 b)
  have powBound (x : Real) (hx : |x| ≤ 1) : ∀ j : Nat, |x^j| ≤ 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ, abs_mul]
      exact (mul_le_mul ih hx (abs_nonneg x) (by norm_num)).trans (by norm_num)
  have powDiff (x y : Real) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
      ∀ j : Nat, |x^j-y^j| ≤ (j : Real)*|x-y| := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hid : x^(j+1)-y^(j+1) = (x^j-y^j)*x+y^j*(x-y) := by
        simp only [pow_succ]
        ring
      calc
        |x^(j+1)-y^(j+1)| = |(x^j-y^j)*x+y^j*(x-y)| := by rw [hid]
        _ ≤ |(x^j-y^j)*x|+|y^j*(x-y)| := abs_add _ _
        _ = |x^j-y^j|*|x|+|y^j|*|x-y| := by rw [abs_mul, abs_mul]
        _ ≤ ((j : Real)*|x-y|)*1+1*|x-y| :=
          add_le_add (mul_le_mul ih hx (abs_nonneg x) (by positivity))
            (mul_le_mul_of_nonneg_right (powBound y hy j) (abs_nonneg _))
        _ = ((j+1 : Nat) : Real)*|x-y| := by push_cast; ring
  have clipBound (x : Real) : |clip x| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have clipDistance (x : Real) : |clip x-w| ≤ |x-w| := by
    obtain ⟨hw0, hw1⟩ := abs_le.mp hw
    by_cases hlo : x ≤ -1
    · have hc : clip x = -1 := by
        simp [clip, min_eq_right (show x ≤ 1 by linarith), max_eq_left hlo]
      rw [hc, abs_of_nonpos (by linarith : -1-w ≤ 0),
        abs_of_nonpos (by linarith : x-w ≤ 0)]
      linarith
    by_cases hhi : 1 ≤ x
    · have hc : clip x = 1 := by simp [clip, min_eq_left hhi]
      rw [hc, abs_of_nonneg (by linarith : 0 ≤ 1-w),
        abs_of_nonneg (by linarith : 0 ≤ x-w)]
      linarith
    · have hc : clip x = x := by
        simp [clip, min_eq_right (show x ≤ 1 by linarith),
          max_eq_right (show -1 ≤ x by linarith)]
      rw [hc]
  let g := v^2
  let gh := s2-s1^2
  let zh := s3-2*s1*s2+s1^3
  have hg : 0 ≤ g := sq_nonneg v
  have hsq : |s1^2-u^2| ≤ 2*epsilon := by
    have hh := powDiff s1 u hs1 hu 2
    norm_num at hh
    linarith
  have hcube : |s1^3-u^3| ≤ 3*epsilon := by
    have hh := powDiff s1 u hs1 hu 3
    norm_num at hh
    linarith
  have hge : |gh-g| ≤ 3*epsilon := by
    have hid : gh-g = (s2-(u^2+v^2))-(s1^2-u^2) := by dsimp [gh,g]; ring
    rw [hid]
    exact (subTriangle _ _).trans (by linarith)
  have hprod : |s1*s2-u*(u^2+v^2)| ≤ 2*epsilon := by
    have hid : s1*s2-u*(u^2+v^2) = (s1-u)*s2+u*(s2-(u^2+v^2)) := by ring
    rw [hid]
    calc
      |(s1-u)*s2+u*(s2-(u^2+v^2))| ≤
          |(s1-u)*s2|+|u*(s2-(u^2+v^2))| := abs_add _ _
      _ = |s1-u|*|s2|+|u|*|s2-(u^2+v^2)| := by rw [abs_mul, abs_mul]
      _ ≤ epsilon*1+1*epsilon :=
        add_le_add (mul_le_mul h1 hs2 (abs_nonneg _) he)
          (mul_le_mul hu h2 (abs_nonneg _) (by norm_num))
      _ = 2*epsilon := by ring
  have hze : |zh-g*w| ≤ 8*epsilon := by
    have hid : zh-g*w =
        ((s3-(u^3+2*u*v^2+v^2*w))-2*(s1*s2-u*(u^2+v^2)))+(s1^3-u^3) := by
      dsimp [zh,g]
      ring
    rw [hid]
    calc
      _ ≤ |(s3-(u^3+2*u*v^2+v^2*w))-2*(s1*s2-u*(u^2+v^2))|+|s1^3-u^3| := abs_add _ _
      _ ≤ (|s3-(u^3+2*u*v^2+v^2*w)|+|2*(s1*s2-u*(u^2+v^2))|)+|s1^3-u^3| := by
        exact add_le_add_right (subTriangle _ _) _
      _ ≤ 8*epsilon := by rw [abs_mul]; norm_num; linarith
  change |(if gh ≤ 0 then 0 else gh*(clip (zh/gh))^k)-g*w^k| ≤ _
  by_cases hzero : gh ≤ 0
  · rw [if_pos hzero]
    have hgb : g ≤ 3*epsilon := by
      have hh := (abs_le.mp hge).1
      linarith
    calc
      |0-g*w^k| = g*|w^k| := by rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg hg]
      _ ≤ g*1 := mul_le_mul_of_nonneg_left (powBound w hw k) hg
      _ ≤ (3+11*(k : Real))*epsilon := by
        have hk : 0 ≤ (k : Real) := Nat.cast_nonneg _
        nlinarith
  · have hpos : 0 < gh := lt_of_not_ge hzero
    rw [if_neg hzero]
    have weighted : gh*|clip (zh/gh)-w| ≤ 11*epsilon := by
      calc
        gh*|clip (zh/gh)-w| ≤ gh*|zh/gh-w| :=
          mul_le_mul_of_nonneg_left (clipDistance _) hpos.le
        _ = |gh*(zh/gh-w)| := by rw [abs_mul, abs_of_pos hpos]
        _ = |zh-gh*w| := by
          congr 1
          field_simp [ne_of_gt hpos]
          <;> ring
        _ = |(zh-g*w)-(gh-g)*w| := by congr 1; ring
        _ ≤ |zh-g*w|+|(gh-g)*w| := subTriangle _ _
        _ = |zh-g*w|+|gh-g|*|w| := by rw [abs_mul]
        _ ≤ 8*epsilon+3*epsilon*1 :=
          add_le_add hze (mul_le_mul hge hw (abs_nonneg _) (by positivity))
        _ = 11*epsilon := by ring
    have hd := powDiff (clip (zh/gh)) w (clipBound _) hw k
    have hmain : gh*|clip (zh/gh)^k-w^k| ≤ (k : Real)*(11*epsilon) := by
      calc
        _ ≤ gh*((k : Real)*|clip (zh/gh)-w|) := mul_le_mul_of_nonneg_left hd hpos.le
        _ = (k : Real)*(gh*|clip (zh/gh)-w|) := by ring
        _ ≤ (k : Real)*(11*epsilon) := mul_le_mul_of_nonneg_left weighted (Nat.cast_nonneg _)
    have hid : gh*clip (zh/gh)^k-g*w^k =
        gh*(clip (zh/gh)^k-w^k)+(gh-g)*w^k := by ring
    rw [hid]
    calc
      _ ≤ |gh*(clip (zh/gh)^k-w^k)|+|(gh-g)*w^k| := abs_add _ _
      _ = gh*|clip (zh/gh)^k-w^k|+|gh-g|*|w^k| := by
        rw [abs_mul, abs_mul, abs_of_pos hpos]
      _ ≤ (k : Real)*(11*epsilon)+3*epsilon*1 :=
        add_le_add hmain (mul_le_mul hge (powBound w hw k) (abs_nonneg _) (by positivity))
      _ = (3+11*(k : Real))*epsilon := by ring

#print axioms three_moment_error_bound

end D5.S3.Observer.ProbabilisticClosure.ThreeMomentMemoryStability
