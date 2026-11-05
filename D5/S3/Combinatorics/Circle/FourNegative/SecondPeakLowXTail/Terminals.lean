/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Terminals
   generality: I
   mirror-B: none(waiver:private-consumed-endpoint-bridge)
   mirror-E: none(waiver:private-consumed-endpoint-bridge)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Actual centered terminal values agree with the rational four-bank model. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalBanks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

-- Reuses native_masses' proved doubled terminal identities. In particular,
-- this bridge never treats an integer floor quotient as rational division.
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open private physicalDomain physical_coordinates
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic
open private qHead qNewHead qModulus qTerminal
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private terminal physicalValue physical_heads
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalBanks
open private sourceMod nextBase nextNewBase from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase chainStart chainLength oldValue newValue)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def terminalChain : Fin 4 → Fin 4 := ![0,3,2,1]

private theorem physical_moduli (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) :
    qModulus ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) isNew =
      if isNew then 2*(sourceMod a b c d : ℚ)+1 else (sourceMod a b c d : ℚ) := by
  obtain ⟨hw,hL,hy,hE,hD,hV,hS,hH⟩ := physical_coordinates a b c d h
  have hY : 2*(2:ℚ)^a*2^(b-a-1) = 2^b := by
    rw [mul_assoc,hy,← pow_succ']
    congr 1
    rcases h with ⟨hc,ha,hd,hb⟩
    omega
  cases isNew <;> simp only [qModulus, Bool.false_eq_true, ↓reduceIte,
    sourceMod, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_one]
  all_goals rw [hY,hw]
  all_goals ring

private theorem terminal_index (a b c d : ℕ) (h : physicalDomain a b c d)
    (bank : Fin 4) :
    terminal a b c d bank = chainStart b c d (terminalChain bank) +
      (chainLength a b c d (terminalChain bank)-1) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases bank <;> simp only [terminal,terminalChain,chainStart,chainLength,size,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  all_goals omega

private theorem physical_terminal_values (a b c d : ℕ)
    (h : physicalDomain a b c d) (isNew : Bool) (bank : Fin 4) :
    physicalValue a b c d isNew (terminal a b c d bank) =
      qTerminal ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) isNew bank := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hm := native_masses a b c d ha hb hc hd (terminalChain bank)
  have hi := terminal_index a b c d h bank
  have ho : (2:ℤ)*oldValue a b c d (terminal a b c d bank) =
      nextBase a b c d (terminalChain bank)-sourceMod a b c d := by
    rw [hi]
    exact hm.2.2.1
  have hn : (2:ℤ)*newValue a b c d (terminal a b c d bank) =
      nextNewBase a b c d (terminalChain bank)-(2*sourceMod a b c d+1) := by
    rw [hi]
    exact hm.2.2.2
  have hoQ : (2:ℚ)*(oldValue a b c d (terminal a b c d bank):ℚ) =
      (nextBase a b c d (terminalChain bank):ℚ)-(sourceMod a b c d:ℚ) := by
    exact_mod_cast ho
  have hnQ : (2:ℚ)*(newValue a b c d (terminal a b c d bank):ℚ) =
      (nextNewBase a b c d (terminalChain bank):ℚ)-
        (2*(sourceMod a b c d:ℚ)+1) := by
    exact_mod_cast hn
  obtain ⟨hA,hB⟩ := physical_heads a b c d h
  have hM := physical_moduli a b c d h isNew
  cases isNew
  · simp only [Bool.false_eq_true,↓reduceIte] at hM
    simp only [physicalValue,Bool.false_eq_true,↓reduceIte]
    rw [qTerminal,hM]
    fin_cases bank <;> simp only [terminalChain,nextBase,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at hoQ ⊢
    all_goals rw [← hA]
    all_goals linarith only [hoQ]
  · simp only [↓reduceIte] at hM
    simp only [physicalValue,↓reduceIte]
    rw [qTerminal,hM]
    fin_cases bank <;> simp only [terminalChain,nextNewBase,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at hnQ ⊢
    all_goals first | rw [← hA] | rw [← hB]
    all_goals linarith only [hnQ]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
