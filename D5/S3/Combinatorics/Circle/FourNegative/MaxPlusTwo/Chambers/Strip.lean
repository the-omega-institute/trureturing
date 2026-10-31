/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Strip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Strip
   mirror-E: none(waiver:internal-strong-strip)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Strong shadow-charge invariants imply both literal first-ear prefix strips. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Source

/-! The old height is r-Q and the enlarged height after the first ear is h+r. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport

private def Strong (f q : ℕ→ℤ) (B h Q : ℤ) : List ℕ→Prop
  | [] => 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B
  | i::xs => 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B ∧
      Strong f q B (h+f i) (Q-q i) xs

/-- A common physical prefix satisfies both strips, including arbitrary prefix lengths. -/
private theorem strong_strips (f q : ℕ→ℤ) (B h Q : ℤ) (xs : List ℕ)
    (hs : Strong f q B h Q xs) :
    InStrip f (B-1) h xs ∧ InStrip (fun i => 2*f i-q i) (2*B-1) (2*h+Q) xs := by
  induction xs generalizing h Q with
  | nil =>
    dsimp [Strong] at hs
    exact ⟨⟨hs.1,hs.2.1⟩,⟨by omega,by omega⟩⟩
  | cons i xs ih =>
    obtain ⟨h0,hB,r0,rB,rest⟩ := hs
    obtain ⟨old,new⟩ := ih (h+f i) (Q-q i) rest
    constructor
    · exact ⟨h0,hB,old⟩
    · refine ⟨by omega,by omega,?_⟩
      convert new using 1 <;> ring

/-- At a proper prefix the remaining final-negative charge gives the strict old ceiling. -/
private theorem strong_of_shadow (B h Q : ℤ) (h0 : 0≤h) (hQ : 1≤Q)
    (hr : h+Q≤B) : 0≤h ∧ h≤B-1 ∧ 0≤h+Q ∧ h+Q≤B := by
  omega

/-- The lift preserves strong bounds when the actual remaining charge is unchanged. -/
private theorem lift_bounds (M B h Q : ℤ) (hM : 1≤M) (hB : 1≤B)
    (h0 : 0≤h) (hQ : 0≤Q) (hr : h+Q≤B)
    (hproper : 1≤Q ∨ h=0 ∧ Q=0) :
    let h' := M*h+(M-1)*Q
    0≤h' ∧ h'≤M*B-1 ∧ 0≤h'+Q ∧ h'+Q≤M*B := by
  dsimp only
  have hleft := mul_nonneg (show 0≤M by omega) h0
  have hright := mul_nonneg (show 0≤M-1 by omega) hQ
  have hmul := mul_le_mul_of_nonneg_left hr (show 0≤M by omega)
  have hMB : 1≤M*B := by nlinarith
  rcases hproper with hp|⟨rfl,rfl⟩ <;> constructor
  · nlinarith
  · refine ⟨?_,?_,?_⟩ <;> nlinarith
  · norm_num
  · norm_num at *
    omega

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
