/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/SourceMasses
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-source-mass-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Existing actual centered rows evaluated on the boundary physical masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-! Exact source-owner chain values summed over literal occurrence masks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size sourceMod base newBase chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private masked_weighted_masses
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

private theorem paired_terminal (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (r : Fin 4) :
    oldValue a b c d (chainStart b c d r+(chainLength a b c d r-1)) =
      -(sourceMod a b c d-nextBase a b c d r)/2 ∧
    newValue a b c d (chainStart b c d r+(chainLength a b c d r-1)) =
      -((2*sourceMod a b c d+1)-nextNewBase a b c d r)/2 := by
  have hn : 2 ≤ chainLength a b c d r := by fin_cases r <;> simp [chainLength,ha,hb,hc,hd]
  have h := chain_values a b c d ha hb hc hd
  constructor
  · simpa only [if_neg (by omega : ¬chainLength a b c d r-1+1<chainLength a b c d r)]
      using h.2.1 r (chainLength a b c d r-1) (by omega)
  · simpa only [if_neg (by omega : ¬chainLength a b c d r-1+1<chainLength a b c d r)]
      using h.2.2.1 r (chainLength a b c d r-1) (by omega)

-- A physical partition supplies both masses, not just an old-row allocation.
-- The mask containments are the only combinatorial premises of this helper;
-- the final boundary constructor must prove them from its integer formulas.
set_option maxHeartbeats 1400000 in
private theorem masked_source_masses (a b c d u r p q w : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hu : u<2^(d-1)) (hr : r<2^(d-1))
    (hp : p<2^(c-1)) (hq : q<2^(c-1)) (hw : w<2^(b-1))
    (hru : ∀ e<d-1, r.testBit e=true → u.testBit e=true)
    (hqp : ∀ e<c-1, q.testBit e=true → p.testBit e=true) :
    let P := maskedBlocks a b c d u r 0 0 p q w
    ∀ side : Bool,
      let F := if side then newBase a b c d else base a b c d
      let f := if side then newValue a b c d else oldValue a b c d
      let U := ((2^(d-1)-1:ℕ):ℤ)*F 0
      let V := ((2^(c-1)-1:ℕ):ℤ)*F 1
      let W := ((2^(b-1)-1:ℕ):ℤ)*F 2
      let X := ((2^(a-1)-1:ℕ):ℤ)*F 3
      (P.first.map f).sum = U-F 0*u ∧
      (P.second.map f).sum = V+F 0*u-(F 0*r+F 1*p) ∧
      (P.third.map f).sum = W+(F 0*r+F 1*p)-(F 1*q+F 2*w) ∧
      (P.fourth.map f).sum = X+(F 1*q+F 2*w) := by
  dsimp only
  intro side
  let F := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  have hvals := chain_values a b c d ha hb hc hd
  have hseries (j : Fin 4) : ∀ e<chainLength a b c d j-1,
      f (chainStart b c d j+e)=2^e*F j := by
    intro e he
    cases side
    · exact (hvals.2.1 j e (by omega)).trans (if_pos (by omega))
    · exact (hvals.2.2.1 j e (by omega)).trans (if_pos (by omega))
  have hfull (j : Fin 4) :
      ((chamberLabels (chainLength a b c d j-1) (chainStart b c d j)
        (2^(chainLength a b c d j-1)-1)).map f).sum =
      ((2^(chainLength a b c d j-1)-1:ℕ):ℤ)*F j := by
    apply chamberLabels_sum
    · have hh : 0<(2:ℕ)^(chainLength a b c d j-1) := by positivity
      omega
    · exact hseries j
  have hzU : ∀ e<d-1, f (0+e)=2^e*F 0 := by simpa [chainLength,chainStart] using hseries 0
  have hzV : ∀ e<c-1, f (d+e)=2^e*F 1 := by simpa [chainLength,chainStart] using hseries 1
  have hzW : ∀ e<b-1, f (d+c+e)=2^e*F 2 := by simpa [chainLength,chainStart] using hseries 2
  have hU := hfull 0
  have hV := hfull 1
  have hW := hfull 2
  have hX := hfull 3
  dsimp only [chainLength,chainStart] at hU hV hW hX
  have hm := masked_weighted_masses a b c d u r 0 0 p q w f
    (F 0) (F 1) (F 2)
    (((2^(d-1)-1:ℕ):ℤ)*F 0) (((2^(c-1)-1:ℕ):ℤ)*F 1)
    (((2^(b-1)-1:ℕ):ℤ)*F 2) (((2^(a-1)-1:ℕ):ℤ)*F 3)
    hu hr (by positivity) (by positivity) hp hq hw hru
    (by intro e _ he; simp at he) hqp (by simp)
    hzU hzV hzW hU hV hW hX
  simpa only [Nat.cast_zero,mul_zero,sub_zero,zero_add,add_zero] using hm

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
