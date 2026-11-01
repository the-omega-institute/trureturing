/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Values
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:private-consumed-physical-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Both exact source rows, terminal recurrences, and rational mass identities. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Physical
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Arithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb r s v dyadic_eqs from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private lengths offsets nativeMask roundingD roundingW from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Supports
open private modelMask modelExpr mask_coordinates from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Arithmetic
open private bank terminal order blocks word bank_masses from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Physical
open private qHead qNewHead qMask qMass qNegative qPeak qExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
open private sourceMod base newBase charge nextBase nextNewBase chainLength chainStart
  oldValue newValue chain_values from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open scoped BigOperators

private def Nq (p : Parameters) : ℚ :=
  (2^(r p)*2^p.c*2^p.d)*(2*2^(r p)*2^p.c*2^p.d*2^(s p))*2^p.c*2^p.d-1

private theorem head_coordinates (p : Parameters) (chain : Fin 4) :
    (base p.a p.b p.c p.d chain : ℚ) =
      qHead (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) chain ∧
    (newBase p.a p.b p.c p.d chain : ℚ) =
      qNewHead (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) chain := by
  have hx := (dyadic_eqs p).2.1
  have hy := (dyadic_eqs p).2.2.1
  constructor <;> fin_cases chain <;>
    dsimp [base,newBase,charge,qHead,qNewHead] <;>
    push_cast <;> simp only [hx,hy] <;> ring

private theorem modulus_coordinate (p : Parameters) :
    (sourceMod p.a p.b p.c p.d : ℚ) = Nq p := by
  dsimp [sourceMod,Nq]
  push_cast
  rw [(dyadic_eqs p).2.1,(dyadic_eqs p).2.2.1]

private theorem cap_coordinate (p : Parameters) :
    ((sourceMod p.a p.b p.c p.d / 2 : ℤ) : ℚ) = (Nq p-1)/2 := by
  have ha := p.ha; have hc := p.hc; have hd := p.hd
  let C : ℤ := (2 : ℤ)^(p.a-1)*2^p.b*2^p.c*2^p.d-1
  have hpow : (2 : ℤ)^p.a = 2*2^(p.a-1) := by
    conv_lhs => rw [show p.a = (p.a-1)+1 by omega,pow_succ]
    ring
  have hN : sourceMod p.a p.b p.c p.d = 2*C+1 := by
    dsimp [sourceMod,C]; rw [hpow]; ring
  have hdiv : sourceMod p.a p.b p.c p.d / 2 = C := by omega
  have hcast : (sourceMod p.a p.b p.c p.d : ℚ) = 2*(C : ℚ)+1 := by exact_mod_cast hN
  rw [modulus_coordinate] at hcast
  rw [hdiv]; linarith

private theorem head_recurrences (p : Parameters) (chain : Fin 4) :
    (2 : ℤ)^(chainLength p.a p.b p.c p.d chain)*base p.a p.b p.c p.d chain =
      sourceMod p.a p.b p.c p.d + nextBase p.a p.b p.c p.d chain ∧
    (2 : ℤ)^(chainLength p.a p.b p.c p.d chain)*newBase p.a p.b p.c p.d chain =
      (2*sourceMod p.a p.b p.c p.d+1) + nextNewBase p.a p.b p.c p.d chain := by
  constructor <;> fin_cases chain <;>
    dsimp [chainLength,base,newBase,charge,nextBase,nextNewBase,sourceMod] <;> ring

private theorem terminal_doubles (p : Parameters) (chain : Fin 4) :
    2*oldValue p.a p.b p.c p.d (terminal p chain) =
      nextBase p.a p.b p.c p.d chain-sourceMod p.a p.b p.c p.d ∧
    2*newValue p.a p.b p.c p.d (terminal p chain) =
      nextNewBase p.a p.b p.c p.d chain-(2*sourceMod p.a p.b p.c p.d+1) := by
  have ha := p.ha; have hb := p.hb; have hc := p.hc; have hd := p.hd
  have hv := chain_values p.a p.b p.c p.d (by omega) (by omega) hc (by omega)
  have hlen : lengths p chain+1 = chainLength p.a p.b p.c p.d chain := by
    fin_cases chain <;> dsimp [lengths,chainLength] <;> omega
  have hf := hv.2.1 chain (lengths p chain) (by omega)
  have hg := hv.2.2.1 chain (lengths p chain) (by omega)
  have hidx : chainStart p.b p.c p.d chain+lengths p chain = terminal p chain := rfl
  rw [hidx,if_neg (by omega)] at hf hg
  have hp : (2 : ℤ)^(chainLength p.a p.b p.c p.d chain) = 2*2^(lengths p chain) := by
    rw [← hlen,pow_succ]; ring
  obtain ⟨hrec,hrec'⟩ := head_recurrences p chain
  rw [hp] at hrec hrec'
  have hnum : -(sourceMod p.a p.b p.c p.d-nextBase p.a p.b p.c p.d chain) =
      2*(nextBase p.a p.b p.c p.d chain-2^(lengths p chain)*base p.a p.b p.c p.d chain) := by
    linarith
  have hnum' : -((2*sourceMod p.a p.b p.c p.d+1)-nextNewBase p.a p.b p.c p.d chain) =
      2*(nextNewBase p.a p.b p.c p.d chain-2^(lengths p chain)*newBase p.a p.b p.c p.d chain) := by
    linarith
  rw [hnum] at hf
  rw [hnum'] at hg
  constructor <;> omega

private theorem negative_coordinates (p : Parameters) (j : Fin 4) :
    (oldValue p.a p.b p.c p.d (terminal p (order j)) : ℚ) =
      qNegative (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) 0 j ∧
    (newValue p.a p.b p.c p.d (terminal p (order j)) : ℚ) =
      qNegative (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) 1 j := by
  obtain ⟨hf,hg⟩ := terminal_doubles p (order j)
  have hf' : 2*(oldValue p.a p.b p.c p.d (terminal p (order j)) : ℚ) =
      (nextBase p.a p.b p.c p.d (order j) : ℚ)-Nq p := by
    rw [← modulus_coordinate]; exact_mod_cast hf
  have hg' : 2*(newValue p.a p.b p.c p.d (terminal p (order j)) : ℚ) =
      (nextNewBase p.a p.b p.c p.d (order j) : ℚ)-(2*Nq p+1) := by
    rw [← modulus_coordinate]; exact_mod_cast hg
  constructor
  · fin_cases j <;> dsimp [order,nextBase] at hf' <;>
      rw [(head_coordinates p _).1] at hf' <;> dsimp [qNegative] <;>
      change _ = (_-Nq p)/2 <;> linarith
  · fin_cases j <;> dsimp [order,nextNewBase] at hg' <;>
      first | rw [(head_coordinates p _).2] at hg' | rw [(head_coordinates p _).1] at hg'
    all_goals dsimp [qNegative]
    all_goals change _ = (_-(2*Nq p+1))/2
    all_goals linarith

private theorem mass_coordinates (p : Parameters) (j : Fin 4) :
    (((bank p j).map (oldValue p.a p.b p.c p.d)).sum : ℚ) =
      qMass (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p))
        (roundingD p) (roundingW p) 0 j ∧
    (((bank p j).map (newValue p.a p.b p.c p.d)).sum : ℚ) =
      qMass (2^p.c) (2^p.d) (2^(r p)) (2^(s p)) (if p.c = 2 then 2*2^(v p)-1 else 2*2^(v p))
        (roundingD p) (roundingW p) 1 j := by
  constructor
  · rw [(bank_masses p j).1]
    push_cast
    dsimp only [qMass]
    simp_rw [if_pos rfl,mask_coordinates,(head_coordinates p _).1]
    rfl
  · rw [(bank_masses p j).2]
    push_cast
    dsimp only [qMass]
    simp_rw [if_neg (by decide : (1:Fin 4) ≠ 0),mask_coordinates,(head_coordinates p _).2]
    rfl

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
