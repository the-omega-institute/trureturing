/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/Source
   generality: I
   mirror-B: none(waiver:private-consumed-physical-source)
   mirror-E: none(waiver:private-consumed-physical-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact d=a physical dictionary and literal insertion bridge. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.Endpoint

/-! Exact d=a physical dictionary and literal insertion bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size seed sourceMod base newBase charge oldValue newValue chainLength chainStart
  nextBase nextNewBase chain_values new_base_bounds source_totals actual_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private insertAt blocksWord
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private mask full terminal full_split sub_split chain_inventory mask_mass mask_positive
  complement_mass split_mass terminal_double terminal_nonpositive source_odd native_balance
  full_double four_checks fresh_total
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y : ℤ) : ℤ := 1+x+x^2+x^2*y
private def L (x z : ℤ) : ℤ := 1+z+x*z+x^2*z
private def H (y z : ℤ) : ℤ := 1+y+y*z
private def K (x y z : ℤ) : ℤ := H y z+x*y*z
private def SU (x y : ℤ) : ℤ := 2*B x y-1
private def SV (x z : ℤ) : ℤ := 2*L x z-1-z
private def SW (x y z : ℤ) : ℤ := 2*K x y z-H y z

private theorem dictionary (a b c : ℕ) :
    base a b c a = ![A (2^a) (2^b) (2^c), B (2^a) (2^b),
      L (2^a) (2^c), K (2^a) (2^b) (2^c)] ∧
    newBase a b c a = ![2*A (2^a) (2^b) (2^c), SU (2^a) (2^b),
      SV (2^a) (2^c), SW (2^a) (2^b) (2^c)] := by
  constructor <;> funext r <;> fin_cases r <;>
    dsimp [base,newBase,charge,A,B,L,H,K,SU,SV,SW] <;> ring

private theorem heads_positive (x y z : ℤ) (hx : 4≤x) (hy : 4≤y) (hz : 4≤z) :
    1≤A x y z ∧ 1≤B x y ∧ 1≤L x z ∧ 1≤K x y z ∧
    1≤SU x y ∧ 1≤SV x z ∧ 1≤SW x y z := by
  have xp : 0≤x := by omega
  have yp : 0≤y := by omega
  have zp : 0≤z := by omega
  have hA : 0≤A x y z-1 := by dsimp [A]; ring_nf; positivity
  have hB : 0≤B x y-1 := by dsimp [B]; ring_nf; positivity
  have hL : 0≤L x z-1 := by dsimp [L]; ring_nf; positivity
  have hK : 0≤K x y z-1 := by dsimp [K,H]; ring_nf; positivity
  have hU : 0≤SU x y-1 := by dsimp [SU,B]; ring_nf; positivity
  have hV : 0≤SV x z-1 := by dsimp [SV,L]; ring_nf; positivity
  have hW : 0≤SW x y z-1 := by dsimp [SW,K,H]; ring_nf; positivity
  omega

private theorem pow_split (n m : ℕ) (h : m≤n) :
    (2:ℤ)^n=2^(n-m)*2^m := by rw [←pow_add,Nat.sub_add_cancel h]

private theorem pow_lower (n l : ℕ) (h : l≤n) : (2:ℤ)^l≤2^n :=
  pow_le_pow_right₀ (by norm_num) h

private theorem full_cap (a b c : ℕ) (r : Fin 4) :
    full a b c a r<2^(chainLength a b c a r-1) := by
  dsimp [full]
  have := Nat.two_pow_pos (chainLength a b c a r-1)
  omega

/- A consumed bridge: the caller supplies actual bank lists and their checked
   scalar endpoints, rather than an abstract divisible stock. -/
private theorem packets_strip (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (side : Bool) (bs : List (List ℕ×ℕ))
    (hpos : ∀ pkt∈bs, ∀ i∈pkt.1,
      0≤(if side then newValue a b c a else oldValue a b c a) i)
    (hneg : ∀ pkt∈bs,
      (if side then newValue a b c a else oldValue a b c a) pkt.2≤0)
    (hchecks : packetChecks (if side then newValue a b c a else oldValue a b c a)
      (if side then sourceMod a b c a else sourceMod a b c a/2) 0 bs) :
    InStrip (if side then newValue a b c a else oldValue a b c a)
      (if side then sourceMod a b c a else sourceMod a b c a/2) 0 (blocksWord bs) := by
  have hN : 0≤sourceMod a b c a := by
    have h := (chain_values a b c a ha hb hc ha).1 0
    omega
  apply (strip_iff_packetChecks _ _ 0 bs ⟨by omega,?_⟩ hpos hneg).mpr hchecks
  cases side <;> simp only [ite_true,ite_false,Bool.false_eq_true] <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
