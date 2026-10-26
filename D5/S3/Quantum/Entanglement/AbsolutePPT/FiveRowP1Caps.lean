/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Caps
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Caps
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: none
   digest: Symbolic tail cap implications including zero mass and zero-width chord cases. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Caps
open D5.S0.Certificates.BoxCover.QuadraticCorner
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra

/-- Rational chord data are checked, rather than trusting an integer square
root implementation. A zero-width interval is also admitted. -/
def chordOK (box : Box 4) (m b : ℚ) : Prop :=
  0 ≤ m*(box 3).1+b ∧ (m*(box 3).1+b)^2 ≤ (box 3).1 ∧
  0 ≤ m*(box 3).2+b ∧ (m*(box 3).2+b)^2 ≤ (box 3).2
instance (box : Box 4) (m b : ℚ) : Decidable (chordOK box m b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def cap (branch : Bool) (box : Box 4) (m b : ℚ) : P :=
  if branch then
    if (box 2).2=0 then fixed 0
    else mulA ![0,0,1,0,0] ![2,-1,0,0,-3/(box 2).2]
  else mulA ![0,0,1,0,0] ![2-b,-1,0,0,-m]

private theorem chord_sound (lo hi m b q : ℝ) (hq : lo ≤ q) (hq' : q ≤ hi)
    (h0 : 0 ≤ m*lo+b) (h0' : (m*lo+b)^2 ≤ lo)
    (h1 : 0 ≤ m*hi+b) (h1' : (m*hi+b)^2 ≤ hi) :
    0 ≤ m*q+b ∧ (m*q+b)^2 ≤ q := by
  have hlin := quadratic_lower b m 0 lo hi q 0 hq hq'
    (by simpa [add_comm] using h0) (by simpa [add_comm] using h1)
  have hs := quadratic_lower (-b^2) (1-2*m*b) (-m^2) lo hi q 0 hq hq'
    (by nlinarith only [h0']) (by nlinarith only [h1'])
  have he : max (-m^2) 0 = 0 := max_eq_right (neg_nonpos.mpr (sq_nonneg m))
  rw [he] at hs
  norm_num only [max_self, zero_mul, zero_div, zero_sub] at hlin hs
  constructor <;> nlinarith only [hlin, hs]

/-- The ninth cap follows from the ORIGINAL tail disjunction. In particular
H=0 and Dhi=0 do not enter a division argument. -/
theorem cap_sound {r H D q a : ℝ} (h : Hyp r H D q a)
    (branch : Bool) (hb : Branch branch r H D q a)
    (box : Box 4) (hx : Inside box ![r,H,D,q]) (m b : ℚ)
    (hm : branch=false → chordOK box m b) :
    a ≤ ev (cap branch box m b) ![r,H,D,q] := by
  have hid := charge_identity h
  cases branch with
  | false =>
      obtain ⟨h0,h0',h1,h1'⟩ := hm rfl
      have hh0 : (0 : ℝ) ≤ (m : ℝ)*((box 3).1 : ℝ)+(b : ℝ) := by exact_mod_cast h0
      have hh0' : ((m : ℝ)*((box 3).1 : ℝ)+(b : ℝ))^2 ≤ ((box 3).1 : ℝ) := by exact_mod_cast h0'
      have hh1 : (0 : ℝ) ≤ (m : ℝ)*((box 3).2 : ℝ)+(b : ℝ) := by exact_mod_cast h1
      have hh1' : ((m : ℝ)*((box 3).2 : ℝ)+(b : ℝ))^2 ≤ ((box 3).2 : ℝ) := by exact_mod_cast h1'
      have hs := chord_sound ((box 3).1 : ℝ) ((box 3).2 : ℝ) m b q
        (hx 3).1 (hx 3).2 hh0 hh0' hh1 hh1'
      have hc0 := h.charge0
      simp only [Branch, Bool.false_eq_true, if_false] at hb
      have hc : (m : ℝ)*q+b ≤ charge r H a := by nlinarith [hs.1, hs.2]
      have hp := mul_le_mul_of_nonneg_left hc h.H0
      simp [cap, av]
      nlinarith only [hid, hp]
  | true =>
      by_cases hd : (box 2).2=0
      · simpa [cap, hd] using fixed_sound h 0
      · have hDhi : 0 < ((box 2).2 : ℝ) := by
          have hnonneg : (0 : ℚ) ≤ (box 2).2 := by exact_mod_cast h.D0.trans (hx 2).2
          have hpos : (0 : ℚ) < (box 2).2 := lt_of_le_of_ne hnonneg (Ne.symm hd)
          exact_mod_cast hpos
        have hc0 := h.charge0
        have hmul : charge r H a * D ≤ charge r H a * ((box 2).2 : ℝ) := by
          simpa using mul_le_mul_of_nonneg_left (hx 2).2 hc0
        simp only [Branch, if_true] at hb
        have hdiv : 3*q/((box 2).2 : ℝ) ≤ charge r H a :=
          (div_le_iff₀ hDhi).2 (by nlinarith only [hb, hmul])
        calc
          a = H*(2-r-charge r H a) := hid
          _ ≤ H*(2-r-3*q/((box 2).2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (sub_le_sub_left hdiv _) h.H0
          _ = ev (cap true box m b) ![r,H,D,q] := by
            simp [cap, hd, av]
            ring_nf <;> simp

end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Caps
