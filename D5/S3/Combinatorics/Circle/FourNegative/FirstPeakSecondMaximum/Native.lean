/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Native
   generality: I
   mirror-B: none(waiver:private-consumed-source-masses)
   mirror-E: none(waiver:private-consumed-source-masses)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact native terminal masses in both centered source rows. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

/-! Native for the paired physical source construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum
open private sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue chain_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private last_double from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

private theorem native_masses (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (r : Fin 4) :
    let len := chainLength a b c d r
    let i := chainStart b c d r + (len-1)
    let C : ℤ := ((2 ^ (len-1)-1:ℕ):ℤ)
    C * base a b c d r + oldValue a b c d i=nextBase a b c d r-base a b c d r ∧ 
    C * newBase a b c d r + newValue a b c d i=nextNewBase a b c d r-newBase a b c d r ∧ 
    2 * oldValue a b c d i=nextBase a b c d r-sourceMod a b c d ∧ 
    2 * newValue a b c d i=nextNewBase a b c d r-(2 * sourceMod a b c d + 1) := by
  dsimp only
  have hl : 0<chainLength a b c d r := by fin_cases r <;> simp [chainLength] <;> omega
  have rel : (2:ℤ) ^ (chainLength a b c d r) * base a b c d r=sourceMod a b c d + nextBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,base,sourceMod,nextBase] <;> ring
  have reln : (2:ℤ) ^ (chainLength a b c d r) * newBase a b c d r=
      (2 * sourceMod a b c d + 1) + nextNewBase a b c d r := by
    fin_cases r <;> dsimp [chainLength,newBase,base,charge,sourceMod,nextNewBase] <;> ring
  have hf := (chain_values a b c d ha hb hc hd).2.1 r (chainLength a b c d r-1) (by omega)
  have hg := (chain_values a b c d ha hb hc hd).2.2.1 r (chainLength a b c d r-1) (by omega)
  rw [if_neg (by omega)] at hf hg
  have hfo : 2 * oldValue a b c d (chainStart b c d r + (chainLength a b c d r-1))=
      nextBase a b c d r-sourceMod a b c d := by
    rw [hf]; exact last_double _ _ _ _ hl rel
  have hgo : 2 * newValue a b c d (chainStart b c d r + (chainLength a b c d r-1))=
      nextNewBase a b c d r-(2 * sourceMod a b c d + 1) := by
    rw [hg]; exact last_double _ _ _ _ hl reln
  have hp : (2:ℤ) ^ (chainLength a b c d r)=2 * 2 ^ (chainLength a b c d r-1) := by
    conv_lhs => rw [show chainLength a b c d r=(chainLength a b c d r-1) + 1 by omega,pow_succ]
    ring
  have hcast : ((2 ^ (chainLength a b c d r-1)-1:ℕ):ℤ)=(2:ℤ) ^ (chainLength a b c d r-1)-1 := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (chainLength a b c d r-1); omega)]
    norm_cast
  rw [hp] at rel reln
  rw [hcast]
  exact ⟨by nlinarith only [rel,hfo,hp],by nlinarith only [reln,hgo,hp],hfo,hgo⟩
end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum
