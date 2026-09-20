/- GID: D5/S3/Arith/ZeckendorfTwoReadTomography
   generality: G
   mirror-B: none(waiver:all-positive-moduli-two-read-separation)
   mirror-E: none(waiver:explicit-unit-inverse-and-finite-mass-recovery)
   anchors: []
   digest: Two correlated modular reads isolate each projective Fibonacci state and recover its mass. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ZeckendorfTwoReadTomography

open scoped BigOperators

/-- Residue after the first guarded continuation, with coefficients (-r*e,-r*f). -/
def firstResidual {M : ℕ} (r e f rp up vp : ZMod M) : ZMod M :=
  rp - r * (e * up + f * vp)

/-- Residue after a second guarded continuation with coefficients (v,-u).
The first accumulated residue is retained: there is no reset between reads. -/
def secondResidual {M : ℕ} (r u v e f rp up vp : ZMod M) : ZMod M :=
  firstResidual r e f rp up vp + v * up - u * vp

/-- Explicit two-read separation over every positive composite or prime modulus.
The rows have actual Bezout certificates. Distinct indexed projective rows
are separated by a NONZERO determinant, not an assumed invertible determinant.
The final identity recovers any signed real mass, so includes probabilities.
Literal legal-word realization is supplied by the preceding guarded compiler;
this theorem certifies the two cumulative modular tests and their mass sum. -/
theorem result {M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
    (U V E F : ι → ZMod M)
    (hrow : ∀ i, E i * U i + F i * V i = 1)
    (hsep : ∀ i j, i ≠ j → V i * U j - U i * V j ≠ 0)
    (d : ι) (r : ZMod M) :
    (∀ rp up vp ep fp : ZMod M, ep * up + fp * vp = 1 →
      ((firstResidual r (E d) (F d) rp up vp = 0 ∧
       secondResidual r (U d) (V d) (E d) (F d) rp up vp = 0) ↔
      ∃ a aInv : ZMod M, a * aInv = 1 ∧
        rp = a * r ∧ up = a * U d ∧ vp = a * V d)) ∧
    (∀ mu : ι → ZMod M → ℝ,
      (∑ i, ∑ rp : ZMod M,
        if firstResidual r (E d) (F d) rp (U i) (V i) = 0 ∧
           secondResidual r (U d) (V d) (E d) (F d) rp (U i) (V i) = 0
        then mu i rp else 0) = mu d r) := by
  classical
  have hd := hrow d
  constructor
  · intro rp up vp ep fp hp
    constructor
    · rintro ⟨hfirst, hsecond⟩
      dsimp [firstResidual] at hfirst
      dsimp [secondResidual, firstResidual] at hsecond
      let a : ZMod M := E d * up + F d * vp
      have hr : rp = a * r := by
        dsimp [a]
        linear_combination hfirst
      have hcross : V d * up - U d * vp = 0 := by
        linear_combination hsecond - hfirst
      have hu : up = a * U d := by
        dsimp [a]
        linear_combination -up * hd + F d * hcross
      have hv : vp = a * V d := by
        dsimp [a]
        linear_combination -vp * hd - E d * hcross
      refine ⟨a, ep * U d + fp * V d, ?_, hr, hu, hv⟩
      calc
        a * (ep * U d + fp * V d) = ep * up + fp * vp := by
          rw [hu, hv]
          ring
        _ = 1 := hp
    · rintro ⟨a, aInv, ha, hr, hu, hv⟩
      constructor
      · dsimp [firstResidual]
        rw [hr, hu, hv]
        linear_combination -a * r * hd
      · dsimp [secondResidual, firstResidual]
        rw [hr, hu, hv]
        linear_combination -a * r * hd
  · intro mu
    have event : ∀ i (rp : ZMod M),
        (firstResidual r (E d) (F d) rp (U i) (V i) = 0 ∧
         secondResidual r (U d) (V d) (E d) (F d) rp (U i) (V i) = 0) ↔
          i = d ∧ rp = r := by
      intro i rp
      constructor
      · rintro ⟨hfirst, hsecond⟩
        have hcross : V d * U i - U d * V i = 0 := by
          dsimp [secondResidual] at hsecond
          rw [hfirst, zero_add] at hsecond
          exact hsecond
        have hi : i = d := by
          by_contra hne
          exact hsep d i (Ne.symm hne) hcross
        subst i
        refine ⟨rfl, ?_⟩
        dsimp [firstResidual] at hfirst
        rw [hd, mul_one] at hfirst
        exact sub_eq_zero.mp hfirst
      · rintro ⟨rfl, rfl⟩
        constructor
        · simp [firstResidual, hd]
        · dsimp [secondResidual, firstResidual]
          rw [hd]
          ring
    calc
      _ = ∑ i, if i = d then mu d r else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hid : i = d
        · subst i
          simp only [event]
          simp
        · simp only [event]
          simp [hid]
      _ = mu d r := by simp

end D5.S3.Arith.ZeckendorfTwoReadTomography
