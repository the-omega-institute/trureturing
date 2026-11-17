/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/PhysicalStrips
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Full-domain parity-tail physical source construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalBanks
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.StripAlgebra
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! Exact casts of the selected physical masks and terminals.
Integer quotients enter rational identities through their exact divisibility equations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail

open scoped BigOperators
open private physicalDomain physical_coordinates dyadic_lower
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalSelection
open private exponentMask physicalBank physical_mass terminal
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalBanks
open private parityMask parityMass parityPeak selectorNumerator six_strip_sides
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.StripAlgebra
open private qHead qNewHead qModulus qTerminal
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private charge sourceMod nextBase nextNewBase from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase oldValue newValue chainStart chainLength)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private theorem rational_coordinates (a b c d : ℕ) (hd : physicalDomain a b c d) :
    let u := (2 : ℚ)^(a-c)
    let z := (2 : ℚ)^c
    let h := (2 : ℚ)^(d-a)
    let t := (2 : ℚ)^(b-d-1)
    u*z=2^a ∧ u*z*h=2^d ∧ h*t=2^(b-a-1) ∧
      2*(u*z)*(h*t)=2^b ∧ z/2=2^(c-1) ∧
      u*z*h/2=2^(d-1) ∧ u*(z/2-1)=2^(a-1)-u := by
  rcases hd with ⟨hc,ha,hd,hb⟩
  dsimp only
  have hx : (2 : ℚ)^(a-c)*2^c=2^a := by
    rw [←pow_add,Nat.sub_add_cancel (by omega : c ≤ a)]
  have hw : (2 : ℚ)^(a-c)*2^c*2^(d-a)=2^d := by
    rw [hx,←pow_add,Nat.add_sub_of_le (by omega : a ≤ d)]
  have hq : (2 : ℚ)^(d-a)*2^(b-d-1)=2^(b-a-1) := by
    rw [←pow_add]; congr 1; omega
  have hy : 2*((2 : ℚ)^(a-c)*2^c)*(2^(d-a)*2^(b-d-1))=2^b := by
    rw [hx,hq,←pow_succ',←pow_add]
    congr 1; omega
  have hz2 : 2*(2 : ℚ)^(c-1)=2^c := by
    rw [←pow_succ']; congr 1; omega
  have hw2 : 2*(2 : ℚ)^(d-1)=2^d := by
    rw [←pow_succ']; congr 1; omega
  have hzhalf : (2 : ℚ)^c/2=2^(c-1) := by linarith only [hz2]
  have hux : (2 : ℚ)^(a-c)*2^(c-1)=2^(a-1) := by
    rw [←pow_add]; congr 1; omega
  refine ⟨hx,hw,hq,hy,hzhalf,?_,?_⟩
  · rw [hw]; linarith only [hw2]
  · rw [hzhalf]; nlinarith only [hux]

private theorem physical_heads (a b c d : ℕ) (h : physicalDomain a b c d) :
    (∀ r : Fin 4, (base a b c d r : ℚ)=
      qHead ((2:ℚ)^c) (2^(a-c)*2^c) (2^(d-a)) (2^(d-a)*2^(b-d-1)) r) ∧
    (∀ r : Fin 4, (newBase a b c d r : ℚ)=
      qNewHead ((2:ℚ)^c) (2^(a-c)*2^c) (2^(d-a)) (2^(d-a)*2^(b-d-1)) r) := by
  obtain ⟨hx,hw,hq,hy,hz,hcap,hhalf⟩ := rational_coordinates a b c d h
  constructor <;> intro r <;> fin_cases r <;>
    simp only [base,newBase,charge,qHead,qNewHead,
      Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_one,
      Int.cast_zero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] <;>
    simp only [←hx,←hw,←hy] <;> ring

private theorem physical_modulus (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) :
    qModulus ((2:ℚ)^c) (2^(a-c)*2^c) (2^(d-a))
      (2^(d-a)*2^(b-d-1)) isNew =
      if isNew then 2*(sourceMod a b c d : ℚ)+1 else (sourceMod a b c d : ℚ) := by
  obtain ⟨hx,hw,hq,hy,hz,hcap,hhalf⟩ := rational_coordinates a b c d h
  cases isNew <;> simp only [qModulus,Bool.false_eq_true,↓reduceIte,
    sourceMod,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_one]
  all_goals rw [←hx,←hw,←hy]
  all_goals ring

private theorem mask_cast (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (r j : Fin 4) :
    (exponentMask a b c d alpha S r j : ℚ)=
      parityMask ((2:ℚ)^(a-c)) (2^c) (2^(d-a)) (2^(b-d-1)) alpha S r j := by
  obtain ⟨hx,hw,hq,hy,hz,hcap,hhalf⟩ := rational_coordinates a b c d h
  fin_cases r <;> fin_cases j <;>
    simp only [exponentMask,parityMask,Int.cast_sub,Int.cast_add,Int.cast_mul,
      Int.cast_pow,Int.cast_natCast,Int.cast_ofNat,Int.cast_one,Int.cast_zero,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] <;>
    first
    | rfl
    | simpa only [hx,hq]
    | simpa only [hhalf]
    | simpa only [hcap]
    | simpa only [hz]

private def physicalRow (a b c d : ℕ) (isNew : Bool) : ℕ → ℤ :=
  if isNew then newValue a b c d else oldValue a b c d

private theorem bank_mass_cast (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (isNew : Bool) (r : Fin 4) :
    ((∑ i ∈ physicalBank a b c d alpha S r, physicalRow a b c d isNew i : ℤ) : ℚ)=
      parityMass ((2:ℚ)^(a-c)) (2^c) (2^(d-a)) (2^(b-d-1)) alpha S isNew r := by
  have hm := physical_mass a b c d alpha S h hAlpha hS2 hSh isNew r
  change (∑ i ∈ physicalBank a b c d alpha S r, physicalRow a b c d isNew i)=_ at hm
  rw [hm,Int.cast_sum]
  dsimp [parityMass]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Int.cast_mul,mask_cast a b c d alpha S h r j]
  cases isNew <;> simp only [Bool.false_eq_true,↓reduceIte]
  · rw [(physical_heads a b c d h).1]
  · rw [(physical_heads a b c d h).2]

private def terminalChain : Fin 4 → Fin 4 := ![0,3,2,1]

private theorem terminal_index (a b c d : ℕ) (h : physicalDomain a b c d)
    (r : Fin 4) : terminal a b c d r =
      chainStart b c d (terminalChain r)+(chainLength a b c d (terminalChain r)-1) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases r <;> simp only [terminal,terminalChain,chainStart,chainLength,size,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] <;> omega

private theorem terminal_cast (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (r : Fin 4) :
    (physicalRow a b c d isNew (terminal a b c d r) : ℚ)=
      qTerminal ((2:ℚ)^c) (2^(a-c)*2^c) (2^(d-a))
        (2^(d-a)*2^(b-d-1)) isNew r := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hm := native_masses a b c d ha hb hc hd (terminalChain r)
  have hi := terminal_index a b c d h r
  have ho : (2:ℤ)*oldValue a b c d (terminal a b c d r)=
      nextBase a b c d (terminalChain r)-sourceMod a b c d := by
    rw [hi]; exact hm.2.2.1
  have hn : (2:ℤ)*newValue a b c d (terminal a b c d r)=
      nextNewBase a b c d (terminalChain r)-(2*sourceMod a b c d+1) := by
    rw [hi]; exact hm.2.2.2
  have hoQ : (2:ℚ)*(oldValue a b c d (terminal a b c d r):ℚ)=
      (nextBase a b c d (terminalChain r):ℚ)-(sourceMod a b c d:ℚ) := by exact_mod_cast ho
  have hnQ : (2:ℚ)*(newValue a b c d (terminal a b c d r):ℚ)=
      (nextNewBase a b c d (terminalChain r):ℚ)-(2*(sourceMod a b c d:ℚ)+1) := by
    exact_mod_cast hn
  obtain ⟨hA,hB⟩ := physical_heads a b c d h
  have hM := physical_modulus a b c d h isNew
  cases isNew
  · simp only [Bool.false_eq_true,↓reduceIte] at hM
    simp only [physicalRow,Bool.false_eq_true,↓reduceIte]
    rw [qTerminal,hM]
    fin_cases r <;> simp only [terminalChain,nextBase,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at hoQ ⊢
    all_goals rw [←hA]
    all_goals linarith only [hoQ]
  · simp only [↓reduceIte] at hM
    simp only [physicalRow,↓reduceIte]
    rw [qTerminal,hM]
    fin_cases r <;> simp only [terminalChain,nextNewBase,Bool.false_eq_true,↓reduceIte,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at hnQ ⊢
    all_goals first | rw [←hA] | rw [←hB]
    all_goals linarith only [hnQ]

private theorem selected_six (a b c d alpha S : ℕ) (delta : ℤ)
    (h : physicalDomain a b c d)
    (hS2 : 2 ≤ S) (hS4 : 4*S ≤ 7*2^c)
    (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*((2:ℤ)^(a-c)-1))
    (hid : 2*(2:ℤ)^(a-c)*(2^c+1)*(alpha:ℤ)=
      (((2:ℤ)^(a-c))^2*2^c+1)*2^(d-a)+
        ((2:ℤ)^(a-c)*2^c+1)*(S:ℤ)-15*(2:ℤ)^(a-c)*2^c/8+delta)
    (hB : 8*(15*(2:ℤ)^(a-c)*2^c/8)=15*(2:ℤ)^(a-c)*2^c) :
    let u := (2:ℚ)^(a-c)
    let z := (2:ℚ)^c
    let h' := (2:ℚ)^(d-a)
    let t := (2:ℚ)^(b-d-1)
    (∀ r : Fin 4, r.val < 3 → 0 ≤ parityPeak u z h' t alpha S false r+
      qTerminal z (u*z) h' (h'*t) false r) ∧
    (∀ r : Fin 4, r.val < 3 → parityPeak u z h' t alpha S true r ≤
      qModulus z (u*z) h' (h'*t) false) := by
  let u := (2:ℚ)^(a-c)
  let z := (2:ℚ)^c
  let hh := (2:ℚ)^(d-a)
  let t := (2:ℚ)^(b-d-1)
  have huI : (4:ℤ) ≤ 2^(a-c) := by
    simpa using dyadic_lower (a-c) 2 (by have := h.2.1; omega)
  have hzI : (16:ℤ) ≤ 2^c := by simpa using dyadic_lower c 4 h.1
  have hhI : 2*(2:ℤ)^c ≤ 2^(d-a) := by
    have hp := dyadic_lower (d-a) (c+1) (by have := h.2.2.1; omega)
    simpa only [pow_succ'] using hp
  have htI : (1:ℤ) ≤ 2^(b-d-1) := by simpa using dyadic_lower (b-d-1) 0 (by omega)
  have hu : 4 ≤ u := by dsimp only [u]; exact_mod_cast huI
  have hz : 16 ≤ z := by dsimp only [z]; exact_mod_cast hzI
  have hhh : 2*z ≤ hh := by dsimp only [z,hh]; exact_mod_cast hhI
  have ht : 1 ≤ t := by dsimp only [t]; exact_mod_cast htI
  have hs : (2:ℚ) ≤ (S:ℚ) := by exact_mod_cast hS2
  have hs4 : (4:ℚ)*(S:ℚ) ≤ 7*z := by dsimp only [z]; exact_mod_cast hS4
  have hdQ : (0:ℚ) ≤ (delta:ℚ) := by exact_mod_cast hd0
  have hdJQ : (delta:ℚ) ≤ 2*(u-1) := by dsimp only [u]; exact_mod_cast hdJ
  let B : ℤ := 15*(2:ℤ)^(a-c)*2^c/8
  have hBQ : (8:ℚ)*(B:ℚ)=15*u*z := by dsimp only [B,u,z]; exact_mod_cast hB
  have hIQ : 2*u*(z+1)*(alpha:ℚ)=
      (u^2*z+1)*hh+(u*z+1)*(S:ℚ)-(B:ℚ)+(delta:ℚ) := by dsimp only [u,z,hh,B]; exact_mod_cast hid
  have heq : 2*u*(z+1)*(alpha:ℚ)=selectorNumerator u z hh S delta := by
    dsimp [selectorNumerator]
    linarith only [hIQ,hBQ]
  exact six_strip_sides u z hh t alpha S delta hu hz hhh ht hs hs4 hdQ hdJQ heq

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
