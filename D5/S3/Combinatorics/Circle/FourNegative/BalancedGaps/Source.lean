/- GID: D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Source
   mirror-E: none(waiver:consumed-geometric-source-masses)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Doubled masses and negative increments of the actual physical partition. -/
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Physical
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
open PacketNormalForm
open private correction transfer from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Arithmetic
open private positivePacket negativeLabel assigned native_labels assigned_labels
  from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Physical
open private size chainStart chainLength negatives oldValue newValue base newBase sourceMod
  nextBase nextNewBase charge chain_values packet_masses
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private theorem length_lower (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (r : Fin 4) :
    2 ≤ chainLength a b c d r := by fin_cases r <;> simp_all [chainLength]

private theorem geometric_mass (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (f : ℕ → ℤ) (v : Fin 4 → ℤ)
    (hf : ∀ r : Fin 4, ∀ i < chainLength a b c d r-1,
      f (chainStart b c d r+i) = (2:ℤ)^i*v r) (r : Fin 4) :
    2*(∑ i ∈ positivePacket a b c d r, f i) =
      ((2:ℤ)^(chainLength a b c d r)-2)*v r := by
  have hl := length_lower a b c d ha hb hc hd r
  have hsum : (∑ i ∈ positivePacket a b c d r, f i) =
      (∑ i ∈ Finset.range (chainLength a b c d r-1), (2:ℤ)^i)*v r := by
    unfold positivePacket
    rw [show chainStart b c d r+(chainLength a b c d r-1) =
      (chainLength a b c d r-1)+chainStart b c d r by omega]
    have hshift := Finset.sum_Ico_add f 0 (chainLength a b c d r-1) (chainStart b c d r)
    simp only [zero_add,Nat.Ico_zero_eq_range] at hshift
    rw [← hshift]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact hf r i (Finset.mem_range.mp hi)
  have hgeom : (∑ i ∈ Finset.range (chainLength a b c d r-1), (2:ℤ)^i) =
      (2:ℤ)^(chainLength a b c d r-1)-1 := by
    simpa using geom_sum_mul (2:ℤ) (chainLength a b c d r-1)
  have hp : (2:ℤ)^(chainLength a b c d r) =
      2*(2:ℤ)^(chainLength a b c d r-1) := by
    conv_lhs => rw [show chainLength a b c d r = (chainLength a b c d r-1)+1 by omega]
    rw [pow_succ]; ring
  rw [hsum,hgeom,hp]
  ring

private theorem native_mass (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (r : Fin 4) :
    2*oldMass a b c d (positivePacket a b c d r) =
      ((2:ℤ)^(chainLength a b c d r)-2)*base a b c d r ∧
    2*newMass a b c d (positivePacket a b c d r) =
      ((2:ℤ)^(chainLength a b c d r)-2)*newBase a b c d r := by
  have hv := chain_values a b c d ha hb hc hd
  have hm := packet_masses a b c d ha hb hc hd (positivePacket a b c d r)
    (native_labels a b c d ha hb hc hd r).1
  constructor
  · rw [show oldMass a b c d (positivePacket a b c d r) =
      ∑ i ∈ positivePacket a b c d r, oldValue a b c d i from hm.1.symm]
    apply geometric_mass a b c d ha hb hc hd (oldValue a b c d) (base a b c d) _ r
    intro j i hi
    rw [hv.2.1 j i (by omega), if_pos (by omega)]
  · rw [show newMass a b c d (positivePacket a b c d r) =
      ∑ i ∈ positivePacket a b c d r, newValue a b c d i from hm.2.symm]
    apply geometric_mass a b c d ha hb hc hd (newValue a b c d) (newBase a b c d) _ r
    intro j i hi
    rw [hv.2.2.1 j i (by omega), if_pos (by omega)]

private theorem start_not_mem (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (src dst : Fin 4) (hne : src≠dst) :
    chainStart b c d src ∉ positivePacket a b c d dst := by
  fin_cases src <;> fin_cases dst <;>
    simp_all [positivePacket,chainStart,chainLength,Finset.mem_Ico] <;> omega

private theorem transfer_ne (n : Fin 16) (src dst : Fin 4)
    (h : transfer n = some (src,dst)) : src≠dst := by
  fin_cases n <;> norm_num [transfer] at h <;> rcases h with ⟨rfl,rfl⟩ <;> decide

private theorem assigned_sum (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (f : ℕ → ℤ) (v : Fin 4 → ℤ)
    (hf : ∀ r, f (chainStart b c d r) = v r)
    (hm : ∀ r, 2*(∑ i ∈ positivePacket a b c d r, f i) =
      ((2:ℤ)^(chainLength a b c d r)-2)*v r) (n : Fin 16) (r : Fin 4) :
    2*(∑ i ∈ assigned a b c d n r, f i) =
      ((2:ℤ)^(chainLength a b c d r)-2)*v r + correction n v r := by
  cases he : transfer n with
  | none => simpa [assigned,correction,he] using hm r
  | some p =>
    rcases p with ⟨src,dst⟩
    have hne := transfer_ne n src dst he
    by_cases hrs : r=src
    · subst r
      have hs := Finset.sum_erase_add (positivePacket a b c d src) f
        (native_labels a b c d ha hb hc hd src).2
      simp only [assigned,correction,he,ite_eq_left rfl,ite_eq_right hne,ite_true,ite_false]
      rw [hf] at hs
      linarith [hm src]
    · by_cases hrd : r=dst
      · subst r
        rw [show assigned a b c d n dst = insert (chainStart b c d src)
          (positivePacket a b c d dst) by simp [assigned,he,Ne.symm hne]]
        rw [Finset.sum_insert (start_not_mem a b c d ha hb hc hd src dst hne),hf]
        simp only [correction,he,ite_eq_left rfl,ite_eq_right (Ne.symm hne),ite_true,ite_false]
        linarith [hm dst]
      · simpa [assigned,correction,he,hrs,hrd] using hm r

private theorem assigned_masses (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (n : Fin 16) (r : Fin 4) :
    2*oldMass a b c d (assigned a b c d n r) =
      ((2:ℤ)^(chainLength a b c d r)-2)*base a b c d r + correction n (base a b c d) r ∧
    2*newMass a b c d (assigned a b c d n r) =
      ((2:ℤ)^(chainLength a b c d r)-2)*newBase a b c d r + correction n (newBase a b c d) r := by
  have hv := chain_values a b c d ha hb hc hd
  have hfirst (r : Fin 4) : oldValue a b c d (chainStart b c d r) = base a b c d r ∧
      newValue a b c d (chainStart b c d r) = newBase a b c d r := by
    have hl := length_lower a b c d ha hb hc hd r
    constructor
    · simpa [show 0+1<chainLength a b c d r by omega] using hv.2.1 r 0 (by omega)
    · simpa [show 0+1<chainLength a b c d r by omega] using hv.2.2.1 r 0 (by omega)
  have hnative := native_mass a b c d ha hb hc hd
  have hnative' (r : Fin 4) := packet_masses a b c d ha hb hc hd
    (positivePacket a b c d r) (native_labels a b c d ha hb hc hd r).1
  have hm := packet_masses a b c d ha hb hc hd (assigned a b c d n r)
    (assigned_labels a b c d ha hb hc hd n r)
  constructor
  · rw [show oldMass a b c d (assigned a b c d n r) =
      ∑ i ∈ assigned a b c d n r, oldValue a b c d i from hm.1.symm]
    apply assigned_sum a b c d ha hb hc hd (oldValue a b c d) (base a b c d)
      (fun r => (hfirst r).1) _ n r
    intro r; rw [(hnative' r).1]; exact (hnative r).1
  · rw [show newMass a b c d (assigned a b c d n r) =
      ∑ i ∈ assigned a b c d n r, newValue a b c d i from hm.2.symm]
    apply assigned_sum a b c d ha hb hc hd (newValue a b c d) (newBase a b c d)
      (fun r => (hfirst r).2) _ n r
    intro r; rw [(hnative' r).2]; exact (hnative r).2

private theorem source_doubles (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    2*(sourceMod a b c d/2) = sourceMod a b c d-1 ∧
    ∀ r : Fin 4,
      2*oldValue a b c d (negativeLabel a b c d r) = nextBase a b c d r-sourceMod a b c d ∧
      2*newValue a b c d (negativeLabel a b c d r) = nextNewBase a b c d r-(2*sourceMod a b c d+1) := by
  have hp (e : ℕ) (he : 2≤e) : ∃ z : ℤ, (2:ℤ)^e=2*z := by
    refine ⟨(2:ℤ)^(e-1),?_⟩
    conv_lhs => rw [show e=(e-1)+1 by omega]
    rw [pow_succ]; ring
  obtain ⟨x,hx⟩ := hp a ha
  obtain ⟨y,hy⟩ := hp b hb
  obtain ⟨z,hz⟩ := hp c hc
  obtain ⟨t,ht⟩ := hp d hd
  constructor
  · dsimp [sourceMod]
    rw [hx,hy,hz,ht]
    ring_nf
    omega
  · intro r
    have hl := length_lower a b c d ha hb hc hd r
    have hv := chain_values a b c d ha hb hc hd
    have hf := hv.2.1 r (chainLength a b c d r-1) (by omega)
    have hg := hv.2.2.1 r (chainLength a b c d r-1) (by omega)
    rw [if_neg (by omega)] at hf hg
    change oldValue a b c d (negativeLabel a b c d r) = _ at hf
    change newValue a b c d (negativeLabel a b c d r) = _ at hg
    rw [hf,hg]
    fin_cases r <;> dsimp [nextBase,nextNewBase,newBase,charge,base,sourceMod] <;>
      rw [hx,hy,hz,ht] <;> ring_nf <;> constructor <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
