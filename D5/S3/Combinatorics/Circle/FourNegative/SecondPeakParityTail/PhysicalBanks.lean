/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/PhysicalBanks
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Full-domain parity-tail physical source construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalSelection
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Order.Interval.Finset.Nat

/-!
Actual-label allocation and both actual source masses.
Chains are U,V,W,X. Banks have terminal order U,X,W,V.
Every choice below is produced by the exact integral selector; no physical
certificate or arbitrary source family is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
open scoped BigOperators
open private physicalDomain physical_coordinates selected_arithmetic
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalSelection
open D5.S3.Combinatorics.Circle.ThreeBitSource (mask_complement)
open private base newBase oldValue newValue chainOf chain_index chain_values source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size chainLength chainStart negatives)

private def lowWeight (a b d S : ℕ) : ℕ :=
  (2^(d-a)-S)*2^(b-d-1)
private def lowComplement (a b d S : ℕ) : ℕ :=
  2^(b-a-1)-1-lowWeight a b d S

-- High W clears precisely bits 0 and a-c before shifting by q's exponent.
-- They have weights 1 and u. In particular bit 0 is not accidentally retained.
private def highBits (a c s : ℕ) : Finset ℕ :=
  (Finset.range a \ {0,a-c}).image (s+·)

private theorem high_mem (a c s i : ℕ) :
    i ∈ highBits a c s ↔
      s ≤ i ∧ i < s+a ∧ i ≠ s ∧ i ≠ s+(a-c) := by
  simp only [highBits,Finset.mem_image,Finset.mem_sdiff,Finset.mem_range,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨e,⟨he,hne⟩,rfl⟩
    omega
  · rintro ⟨hl,hu,h0,hU⟩
    exact ⟨i-s,⟨by omega,by omega⟩,by omega⟩

private theorem bits_bound (n len i : ℕ) (hn : n < 2^len)
    (hi : i ∈ n.bitIndices.toFinset) : i < len := by
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  by_contra hh
  have hm := Nat.pow_le_pow_right (by decide : 0 < 2) (show len ≤ i by omega)
  omega

private theorem low_split (a b c d S : ℕ) (h : physicalDomain a b c d)
    (hS2 : 2 ≤ S) (hSh : S < 2^(d-a)) :
    lowWeight a b d S + lowComplement a b d S = 2^(b-a-1)-1 ∧
    lowWeight a b d S + 2 ≤ 2^(b-a-1) ∧
    Disjoint (lowWeight a b d S).bitIndices.toFinset
      (lowComplement a b d S).bitIndices.toFinset ∧
    (lowWeight a b d S).bitIndices.toFinset ∪
      (lowComplement a b d S).bitIndices.toFinset = Finset.range (b-a-1) := by
  rcases h with ⟨hc,ha,hd,hb⟩
  have hq : 2^(d-a)*2^(b-d-1) = (2 : ℕ)^(b-a-1) := by
    rw [←pow_add]
    congr 1
    omega
  have hsplit : lowWeight a b d S + S*2^(b-d-1) = 2^(b-a-1) := by
    dsimp [lowWeight]
    rw [←Nat.add_mul,Nat.sub_add_cancel hSh.le,hq]
  have ht : 1 ≤ (2 : ℕ)^(b-d-1) := by have := Nat.two_pow_pos (b-d-1); omega
  have hSt : 2 ≤ S*2^(b-d-1) :=
    le_trans (by omega : 2 ≤ 2*2^(b-d-1)) (Nat.mul_le_mul_right _ hS2)
  have hlow : lowWeight a b d S + 2 ≤ 2^(b-a-1) := by omega
  have he : lowWeight a b d S + lowComplement a b d S = 2^(b-a-1)-1 := by
    dsimp [lowComplement]
    omega
  obtain ⟨hdis,hfull⟩ := mask_complement (b-a-1)
    (lowWeight a b d S) (lowComplement a b d S) he
  exact ⟨he,hlow,hdis,hfull⟩

-- Arguments are chain, then bank. Alpha is the chosen integer's exact toNat.
private def localBits (a b c d alpha S : ℕ) : Fin 4 → Fin 4 → Finset ℕ :=
  ![![alpha.bitIndices.toFinset,∅,(2^(d-1)-1-alpha).bitIndices.toFinset,∅],
    ![∅,∅,∅,Finset.range (c-1)],
    ![highBits a c (b-a-1),
      insert (b-a-1+(a-c)) (lowWeight a b d S).bitIndices.toFinset,∅,
      insert (b-a-1) (lowComplement a b d S).bitIndices.toFinset],
    ![∅,Finset.Ico (a-c) (a-1),∅,Finset.range (a-c)]]

private theorem local_internal (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (chain bank : Fin 4) (i : ℕ) (hi : i ∈ localBits a b c d alpha S chain bank) :
    i < chainLength a b c d chain-1 := by
  obtain ⟨he,hlow,_,_⟩ := low_split a b c d S h hS2 hSh
  have hqpos : 0 < (2 : ℕ)^(b-a-1) := Nat.two_pow_pos _
  have hA (hm : i ∈ alpha.bitIndices.toFinset) : i < d-1 :=
    bits_bound alpha (d-1) i (by omega) hm
  have hAc (hm : i ∈ (2^(d-1)-1-alpha).bitIndices.toFinset) : i < d-1 :=
    bits_bound _ (d-1) i (by have := Nat.two_pow_pos (d-1); omega) hm
  have hL (hm : i ∈ (lowWeight a b d S).bitIndices.toFinset) : i < b-a-1 :=
    bits_bound _ (b-a-1) i (by omega) hm
  have hC (hm : i ∈ (lowComplement a b d S).bitIndices.toFinset) : i < b-a-1 :=
    bits_bound _ (b-a-1) i (by omega) hm
  rcases h with ⟨hc,ha,hd,hb⟩
  by_cases hiL : i ∈ (lowWeight a b d S).bitIndices.toFinset <;>
    by_cases hiC : i ∈ (lowComplement a b d S).bitIndices.toFinset
  all_goals try have hLb := hL hiL
  all_goals try have hCb := hC hiC
  all_goals fin_cases chain <;> fin_cases bank
  all_goals simp only [localBits,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Finset.notMem_empty,Finset.mem_range,Finset.mem_Ico,
    Finset.mem_insert,high_mem,hiL,hiC,false_or,or_false,true_or,or_true] at hi ⊢
  all_goals first | exact hA hi | exact hAc hi | omega

private theorem local_disjoint (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (chain bank other : Fin 4) (hne : bank ≠ other) :
    Disjoint (localBits a b c d alpha S chain bank)
      (localBits a b c d alpha S chain other) := by
  obtain ⟨_,hlow,hLC,_⟩ := low_split a b c d S h hS2 hSh
  have hqpos := Nat.two_pow_pos (b-a-1)
  have hUC := (mask_complement (d-1) alpha (2^(d-1)-1-alpha) (by omega)).1
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hL (hm : i ∈ (lowWeight a b d S).bitIndices.toFinset) : i < b-a-1 :=
    bits_bound _ (b-a-1) i (by omega) hm
  have hC (hm : i ∈ (lowComplement a b d S).bitIndices.toFinset) : i < b-a-1 :=
    bits_bound _ (b-a-1) i (by
      have hh := (low_split a b c d S h hS2 hSh).1
      omega) hm
  have hLC' : ¬(i ∈ (lowWeight a b d S).bitIndices.toFinset ∧
      i ∈ (lowComplement a b d S).bitIndices.toFinset) :=
    fun hh => Finset.disjoint_left.mp hLC hh.1 hh.2
  have hUC' : ¬(i ∈ alpha.bitIndices.toFinset ∧
      i ∈ (2^(d-1)-1-alpha).bitIndices.toFinset) :=
    fun hh => Finset.disjoint_left.mp hUC hh.1 hh.2
  rcases h with ⟨hc,ha,hd,hb⟩
  by_cases hiL : i ∈ (lowWeight a b d S).bitIndices.toFinset <;>
    by_cases hiC : i ∈ (lowComplement a b d S).bitIndices.toFinset
  all_goals try exact (hLC' ⟨hiL,hiC⟩).elim
  all_goals try have hLb := hL hiL
  all_goals try have hCb := hC hiC
  all_goals fin_cases chain <;> fin_cases bank <;> fin_cases other
  all_goals try exact (hne rfl).elim
  all_goals simp only [localBits,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Finset.notMem_empty,Finset.mem_range,Finset.mem_Ico,
    Finset.mem_insert,high_mem,hiL,hiC,false_or,or_false,true_or,or_true] at hi hj
  all_goals first
    | exact (hUC' ⟨hi,hj⟩).elim
    | exact (hUC' ⟨hj,hi⟩).elim
    | omega

private theorem local_cover (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (chain : Fin 4) :
    localBits a b c d alpha S chain 0 ∪ localBits a b c d alpha S chain 1 ∪
      localBits a b c d alpha S chain 2 ∪ localBits a b c d alpha S chain 3 =
      Finset.range (chainLength a b c d chain-1) := by
  have hUC := (mask_complement (d-1) alpha (2^(d-1)-1-alpha) (by omega)).2
  have hLC := (low_split a b c d S h hS2 hSh).2.2.2
  apply Finset.Subset.antisymm
  · intro i hi
    simp only [Finset.mem_union] at hi
    rcases hi with ((hi|hi)|hi)|hi
    · exact Finset.mem_range.mpr (local_internal a b c d alpha S h hAlpha hS2 hSh chain 0 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d alpha S h hAlpha hS2 hSh chain 1 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d alpha S h hAlpha hS2 hSh chain 2 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d alpha S h hAlpha hS2 hSh chain 3 i hi)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    have hlow : i < b-a-1 →
        i ∈ (lowWeight a b d S).bitIndices.toFinset ∨
        i ∈ (lowComplement a b d S).bitIndices.toFinset := by
      intro hh
      apply Finset.mem_union.mp
      rw [hLC]
      exact Finset.mem_range.mpr hh
    rcases h with ⟨hc,ha,hd,hb⟩
    fin_cases chain
    all_goals simp only [localBits,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Finset.mem_union,Finset.notMem_empty,Finset.mem_range,
      Finset.mem_Ico,Finset.mem_insert,high_mem,false_or,or_false] at hi' ⊢
    · have hm : i ∈ alpha.bitIndices.toFinset ∪
          (2^(d-1)-1-alpha).bitIndices.toFinset := by rw [hUC]; exact hi
      exact Finset.mem_union.mp hm
    · exact hi'
    · by_cases hil : i < b-a-1
      · rcases hlow hil with hh|hh <;> simp only [hh,or_true,true_or]
      · omega
    · omega

private def exponentMask (a b c d alpha S : ℕ) : Fin 4 → Fin 4 → ℤ :=
  let u := (2 : ℤ)^(a-c)
  let h := (2 : ℤ)^(d-a)
  let t := (2 : ℤ)^(b-d-1)
  let q := (2 : ℤ)^(b-a-1)
  ![![(alpha : ℤ),0,(2^a-u-2)*q,0],
    ![0,0,u*q+(h-(S : ℤ))*t,2^(a-1)-u],
    ![2^(d-1)-1-(alpha : ℤ),0,0,0],
    ![0,2^(c-1)-1,2*q-1-(h-(S : ℤ))*t,u-1]]

-- The same sixteen masks in the approved ordinary coordinates, without a
-- rational relaxation or a change in bank/chain indexing.
private theorem mask_coordinates (a b c d alpha S : ℕ) (h : physicalDomain a b c d) :
    exponentMask a b c d alpha S =
      let u := (2 : ℤ)^(a-c)
      let z := (2 : ℤ)^c
      let h := (2 : ℤ)^(d-a)
      let t := (2 : ℤ)^(b-d-1)
      let x := u*z
      let q := h*t
      ![![(alpha : ℤ),0,(x-u-2)*q,0],
        ![0,0,u*q+(h-(S : ℤ))*t,u*(z/2-1)],
        ![x*h/2-1-(alpha : ℤ),0,0,0],
        ![0,z/2-1,2*q-1-(h-(S : ℤ))*t,u-1]] := by
  obtain ⟨hx,_,hq,hzhalf,hcap,hxhalf⟩ := physical_coordinates a b c d h
  dsimp only at hx hq hzhalf hcap hxhalf ⊢
  funext bank chain
  fin_cases bank <;> fin_cases chain
  all_goals simp only [exponentMask,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,←hx,←hq,←hzhalf,←hcap,←hxhalf]

private def terminal (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d-1,size a b c d-1,d+c+b-1,d+c-1]

private theorem terminal_inventory (a b c d : ℕ) (h : physicalDomain a b c d) :
    Function.Injective (terminal a b c d) ∧
    (∀ r : Fin 4, terminal a b c d r < size a b c d) ∧
    (Finset.univ.image (terminal a b c d)) = (negatives a b c d).toFinset := by
  rcases h with ⟨hc,ha,hd,hb⟩
  refine ⟨?_,?_,?_⟩
  · intro r s he
    fin_cases r <;> fin_cases s
    all_goals simp only [terminal,size,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply] at he ⊢
    all_goals first | rfl | omega
  · intro r
    fin_cases r <;> simp only [terminal,size,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply] <;> omega
  · ext i
    simp only [Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset,
      negatives,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]
    constructor
    · rintro ⟨r,rfl⟩
      fin_cases r <;> simp [terminal]
    · intro hi
      rcases hi with hi|hi|hi|hi
      · exact ⟨0,by simpa [terminal] using hi.symm⟩
      · exact ⟨3,by simpa [terminal] using hi.symm⟩
      · exact ⟨2,by simpa [terminal] using hi.symm⟩
      · exact ⟨1,by simpa [terminal] using hi.symm⟩

set_option maxHeartbeats 4000000 in
private theorem local_sums (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (chain bank : Fin 4) :
    (∑ e ∈ localBits a b c d alpha S chain bank, (2 : ℤ)^e) =
      exponentMask a b c d alpha S bank chain := by
  classical
  have hs (n : ℕ) : (∑ e ∈ Finset.range n, (2 : ℤ)^e) = 2^n-1 := by
    simpa only [show (2 : ℤ)-1=1 by norm_num,mul_one] using geom_sum_mul (2 : ℤ) n
  have ht (l r : ℕ) (hle : l ≤ r) :
      (∑ e ∈ Finset.Ico l r, (2 : ℤ)^e) = 2^r-2^l := by
    simpa only [show (2 : ℤ)-1=1 by norm_num,mul_one] using geom_sum_Ico_mul (2 : ℤ) hle
  have bits (n : ℕ) : (∑ e ∈ n.bitIndices.toFinset, (2 : ℤ)^e) = (n : ℤ) := by
    exact_mod_cast (Finset.sum_toFinset_bitIndices_two_pow n)
  obtain ⟨hlo,hlow,_,_⟩ := low_split a b c d S h hS2 hSh
  have hqpos := Nat.two_pow_pos (b-a-1)
  have hLbound (i : ℕ) (hi : i ∈ (lowWeight a b d S).bitIndices.toFinset) :
      i < b-a-1 := bits_bound _ _ _ (by omega) hi
  have hCbound (i : ℕ) (hi : i ∈ (lowComplement a b d S).bitIndices.toFinset) :
      i < b-a-1 := bits_bound _ _ _ (by omega) hi
  have hLCast : (lowWeight a b d S : ℤ) =
      ((2 : ℤ)^(d-a)-(S : ℤ))*2^(b-d-1) := by
    simp only [lowWeight,Nat.cast_mul,Nat.cast_sub hSh.le,Nat.cast_pow,Nat.cast_ofNat]
  have hCCast : (lowComplement a b d S : ℤ) =
      (2 : ℤ)^(b-a-1)-1-((2 : ℤ)^(d-a)-(S : ℤ))*2^(b-d-1) := by
    have he : (lowWeight a b d S : ℤ)+(lowComplement a b d S : ℤ)+1 =
        (2 : ℤ)^(b-a-1) := by
      exact_mod_cast (show lowWeight a b d S + lowComplement a b d S + 1 =
        2^(b-a-1) by omega)
    rw [hLCast] at he
    linarith only [he]
  have hUC : (2^(d-1)-1-alpha : ℕ)+alpha+1 = 2^(d-1) := by omega
  have hUCast : ((2^(d-1)-1-alpha : ℕ) : ℤ) =
      (2 : ℤ)^(d-1)-1-(alpha : ℤ) := by
    have he : ((2^(d-1)-1-alpha : ℕ) : ℤ)+(alpha : ℤ)+1 = (2 : ℤ)^(d-1) := by
      exact_mod_cast hUC
    linarith only [he]
  have hhU : (∑ e ∈ (2^(d-1)-1-alpha).bitIndices.toFinset, (2 : ℤ)^e) =
      2^(d-1)-1-(alpha : ℤ) := by rw [bits,hUCast]
  have hhW : (∑ e ∈ highBits a c (b-a-1), (2 : ℤ)^e) =
      (2^a-2^(a-c)-2)*2^(b-a-1) := by
    have hsub : ({0,a-c} : Finset ℕ) ⊆ Finset.range a := by
      rcases h with ⟨hc,ha,hd,hb⟩
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton,Finset.mem_range] at hi ⊢
      omega
    have hne : (0 : ℕ) ≠ a-c := by rcases h with ⟨hc,ha,hd,hb⟩; omega
    have hd := Finset.sum_sdiff (f := fun e : ℕ => (2 : ℤ)^e) hsub
    rw [hs,Finset.sum_pair hne,pow_zero] at hd
    have hrest : (∑ e ∈ Finset.range a \ {0,a-c}, (2 : ℤ)^e) =
        2^a-2^(a-c)-2 := by linarith only [hd]
    rw [highBits,Finset.sum_image (by intro i hi j hj hij; exact Nat.add_left_cancel hij)]
    simp_rw [pow_add]
    rw [←Finset.mul_sum,hrest]
    ring
  have hhWX : (∑ e ∈ insert (b-a-1+(a-c)) (lowWeight a b d S).bitIndices.toFinset,
      (2 : ℤ)^e) = 2^(a-c)*2^(b-a-1)+
        ((2 : ℤ)^(d-a)-(S : ℤ))*2^(b-d-1) := by
    rw [Finset.sum_insert (by intro hm; have hh := hLbound _ hm; omega),bits,hLCast,pow_add]
    ring
  have hhWV : (∑ e ∈ insert (b-a-1) (lowComplement a b d S).bitIndices.toFinset,
      (2 : ℤ)^e) = 2*2^(b-a-1)-1-
        ((2 : ℤ)^(d-a)-(S : ℤ))*2^(b-d-1) := by
    rw [Finset.sum_insert (by intro hm; have hh := hCbound _ hm; omega),bits,hCCast]
    ring
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases chain <;> fin_cases bank
  all_goals simp only [localBits,exponentMask,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Finset.sum_empty]
  all_goals first
    | rfl
    | exact hhU
    | exact hhW
    | exact hhWX
    | exact hhWV
    | exact bits _
    | exact hs _
    | exact ht _ _ (by omega)

private theorem mask_capacities (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (bank chain : Fin 4) :
    0 ≤ exponentMask a b c d alpha S bank chain ∧
      exponentMask a b c d alpha S bank chain <
        (2 : ℤ)^(chainLength a b c d chain-1) := by
  have hsub : localBits a b c d alpha S chain bank ⊆
      Finset.range (chainLength a b c d chain-1) := by
    intro i hi
    exact Finset.mem_range.mpr
      (local_internal a b c d alpha S h hAlpha hS2 hSh chain bank i hi)
  have h0 : 0 ≤ ∑ e ∈ localBits a b c d alpha S chain bank, (2 : ℤ)^e :=
    Finset.sum_nonneg (fun e _ => by positivity)
  have hle : (∑ e ∈ localBits a b c d alpha S chain bank, (2 : ℤ)^e) ≤
      ∑ e ∈ Finset.range (chainLength a b c d chain-1), (2 : ℤ)^e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro e he hn; positivity)
  have hs : (∑ e ∈ Finset.range (chainLength a b c d chain-1), (2 : ℤ)^e) =
      2^(chainLength a b c d chain-1)-1 := by
    simpa only [show (2 : ℤ)-1=1 by norm_num,mul_one] using
      geom_sum_mul (2 : ℤ) (chainLength a b c d chain-1)
  rw [local_sums a b c d alpha S h hAlpha hS2 hSh chain bank] at h0 hle
  rw [hs] at hle
  exact ⟨h0,by omega⟩

private def physicalBank (a b c d alpha S : ℕ) (bank : Fin 4) : Finset ℕ :=
  (Finset.univ : Finset (Fin 4)).biUnion fun chain =>
    (localBits a b c d alpha S chain bank).image (chainStart b c d chain+·)

private theorem physical_mem (a b c d alpha S i : ℕ) (bank : Fin 4) :
    i ∈ physicalBank a b c d alpha S bank ↔
      ∃ chain : Fin 4, ∃ e ∈ localBits a b c d alpha S chain bank,
        chainStart b c d chain+e = i := by
  simp [physicalBank,Finset.mem_biUnion,Finset.mem_image]

-- The existing physical chain classifier supplies uniqueness of the offset.
private theorem local_chain (a b c d : ℕ) (chain : Fin 4) (e : ℕ)
    (he : e < chainLength a b c d chain-1) :
    chainOf b c d (chainStart b c d chain+e) = chain := by
  fin_cases chain
  · change e < d-1 at he
    change chainOf b c d (0+e) = 0
    rw [zero_add,chainOf,if_pos (by omega)]
  · change e < c-1 at he
    change chainOf b c d (d+e) = 1
    rw [chainOf,if_neg (by omega),if_pos (by omega)]
  · change e < b-1 at he
    change chainOf b c d (d+c+e) = 2
    rw [chainOf,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  · change chainOf b c d (d+c+b+e) = 3
    rw [chainOf,if_neg (by omega),if_neg (by omega),if_neg (by omega)]

private theorem physical_internal (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (bank : Fin 4) (i : ℕ) (hi : i ∈ physicalBank a b c d alpha S bank) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  obtain ⟨chain,e,he,rfl⟩ := (physical_mem a b c d alpha S i bank).mp hi
  have he' := local_internal a b c d alpha S h hAlpha hS2 hSh chain bank e he
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases chain
  all_goals simp only [size,negatives,chainStart,chainLength,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at he' ⊢
  all_goals omega

private theorem physical_disjoint (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (bank other : Fin 4) (hne : bank ≠ other) :
    Disjoint (physicalBank a b c d alpha S bank) (physicalBank a b c d alpha S other) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨r,e,he,hei⟩ := (physical_mem a b c d alpha S i bank).mp hi
  obtain ⟨s,f,hf,hfi⟩ := (physical_mem a b c d alpha S i other).mp hj
  have hr := local_chain a b c d r e
    (local_internal a b c d alpha S h hAlpha hS2 hSh r bank e he)
  have hs := local_chain a b c d s f
    (local_internal a b c d alpha S h hAlpha hS2 hSh s other f hf)
  rw [hei] at hr
  rw [hfi] at hs
  have hrs : r=s := hr.symm.trans hs
  cases hrs
  have hef : e=f := Nat.add_left_cancel (hei.trans hfi.symm)
  subst f
  exact Finset.disjoint_left.mp (local_disjoint a b c d alpha S h hAlpha hS2 hSh r bank other hne) he hf

private theorem physical_cover (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a)) :
    (Finset.univ : Finset (Fin 4)).biUnion (physicalBank a b c d alpha S) =
      Finset.range (size a b c d) \ (negatives a b c d).toFinset := by
  classical
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  ext i
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_sdiff,
    Finset.mem_range,List.mem_toFinset]
  constructor
  · rintro ⟨bank,hi⟩
    exact physical_internal a b c d alpha S h hAlpha hS2 hSh bank i hi
  · rintro ⟨hi,hn⟩
    obtain ⟨he,_,hp⟩ := chain_index a b c d i ha hb hc hd hi
    let chain := chainOf b c d i
    let e := i-chainStart b c d chain
    have hei : chainStart b c d chain+e=i := he
    have hel : e < chainLength a b c d chain-1 := by
      have hh := hp hn
      dsimp [chain,e] at *
      omega
    have hm : e ∈ localBits a b c d alpha S chain 0 ∪
        localBits a b c d alpha S chain 1 ∪ localBits a b c d alpha S chain 2 ∪
        localBits a b c d alpha S chain 3 := by
      rw [local_cover a b c d alpha S h hAlpha hS2 hSh chain]
      exact Finset.mem_range.mpr hel
    simp only [Finset.mem_union] at hm
    rcases hm with ((hm|hm)|hm)|hm
    · exact ⟨0,(physical_mem a b c d alpha S i 0).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨1,(physical_mem a b c d alpha S i 1).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨2,(physical_mem a b c d alpha S i 2).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨3,(physical_mem a b c d alpha S i 3).mpr ⟨chain,e,hm,hei⟩⟩

-- Both rows below are the centered sources from PacketNormalForm.Source.
private theorem physical_mass (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (isNew : Bool) (bank : Fin 4) :
    let f := if isNew then newValue a b c d else oldValue a b c d
    let F := if isNew then newBase a b c d else base a b c d
    (∑ i ∈ physicalBank a b c d alpha S bank, f i) =
      ∑ chain : Fin 4, exponentMask a b c d alpha S bank chain * F chain := by
  classical
  dsimp only
  let f := if isNew then newValue a b c d else oldValue a b c d
  let F := if isNew then newBase a b c d else base a b c d
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  obtain ⟨_,hf,hg,_⟩ := chain_values a b c d ha hb hc hd
  have hv (chain : Fin 4) (e : ℕ) (he : e ∈ localBits a b c d alpha S chain bank) :
      f (chainStart b c d chain+e) = (2 : ℤ)^e*F chain := by
    have hl := local_internal a b c d alpha S h hAlpha hS2 hSh chain bank e he
    cases isNew
    · exact (hf chain e (by omega)).trans (if_pos (by omega))
    · exact (hg chain e (by omega)).trans (if_pos (by omega))
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 4)))
      (fun chain => (localBits a b c d alpha S chain bank).image (chainStart b c d chain+·)) := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
    obtain ⟨f',hf',hfi⟩ := Finset.mem_image.mp hj
    have hrc := local_chain a b c d r e
      (local_internal a b c d alpha S h hAlpha hS2 hSh r bank e he)
    have hsc := local_chain a b c d s f'
      (local_internal a b c d alpha S h hAlpha hS2 hSh s bank f' hf')
    rw [hei] at hrc
    rw [hfi] at hsc
    exact hrs (hrc.symm.trans hsc)
  rw [physicalBank,Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro chain hc'
  rw [Finset.sum_image (by intro i hi j hj he; exact Nat.add_left_cancel he)]
  calc
    (∑ e ∈ localBits a b c d alpha S chain bank, f (chainStart b c d chain+e)) =
        ∑ e ∈ localBits a b c d alpha S chain bank, (2 : ℤ)^e*F chain := by
      exact Finset.sum_congr rfl (fun e he => hv chain e he)
    _ = (∑ e ∈ localBits a b c d alpha S chain bank, (2 : ℤ)^e)*F chain :=
      (Finset.sum_mul _ _ _).symm
    _ = exponentMask a b c d alpha S bank chain*F chain := by
      rw [local_sums a b c d alpha S h hAlpha hS2 hSh chain bank]

-- This is an actual ordered list of W occurrences. Its last entry is q's bit;
-- the preceding entries have low mask St-1 and are strictly below that bit.
private def wLast (a b c d S : ℕ) : List ℕ :=
  (lowComplement a b d S).bitIndices.map (d+c+·) ++ [d+c+(b-a-1)]

private theorem w_last_inventory (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hS2 : 2 ≤ S) (hSh : S < 2^(d-a)) :
    (wLast a b c d S).Nodup ∧
    (wLast a b c d S).toFinset =
      (localBits a b c d alpha S 2 3).image (d+c+·) ∧
    (lowComplement a b d S : ℤ) = (S : ℤ)*2^(b-d-1)-1 := by
  obtain ⟨he,hlow,_,_⟩ := low_split a b c d S h hS2 hSh
  have hqpos := Nat.two_pow_pos (b-a-1)
  have hbound (i : ℕ) (hi : i ∈ (lowComplement a b d S).bitIndices) : i < b-a-1 :=
    bits_bound _ _ _ (by omega) (List.mem_toFinset.mpr hi)
  have hnd : ((lowComplement a b d S).bitIndices.map (d+c+·)).Nodup :=
    (Nat.bitIndices_nodup (n := lowComplement a b d S)).map
      (by intro i j hh; exact Nat.add_left_cancel hh)
  have hdis : List.Disjoint ((lowComplement a b d S).bitIndices.map (d+c+·))
      [d+c+(b-a-1)] := by
    apply List.disjoint_left.mpr
    intro i hi hj
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi
    have hh := hbound e he
    simp only [List.mem_singleton] at hj
    omega
  refine ⟨hnd.append (by simp) hdis,?_,?_⟩
  · ext i
    simp only [wLast,List.mem_toFinset,List.mem_append,List.mem_map,List.mem_singleton,
      localBits,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Finset.mem_image,Finset.mem_insert,List.mem_toFinset]
    constructor
    · rintro (⟨e,he,hei⟩|hei)
      · exact ⟨e,Or.inr he,hei⟩
      · exact ⟨b-a-1,Or.inl rfl,hei.symm⟩
    · rintro ⟨e,he,hei⟩
      rcases he with rfl|he
      · exact Or.inr hei.symm
      · exact Or.inl ⟨e,he,hei⟩
  · have hq : (2 : ℤ)^(d-a)*2^(b-d-1) = 2^(b-a-1) :=
      (physical_coordinates a b c d h).2.2.1
    have he' : (lowWeight a b d S : ℤ)+(lowComplement a b d S : ℤ)+1 =
        (2 : ℤ)^(b-a-1) := by
      exact_mod_cast (show lowWeight a b d S+lowComplement a b d S+1 =
        2^(b-a-1) by omega)
    have hL : (lowWeight a b d S : ℤ) =
        ((2 : ℤ)^(d-a)-(S : ℤ))*2^(b-d-1) := by
      simp only [lowWeight,Nat.cast_mul,Nat.cast_sub hSh.le,Nat.cast_pow,Nat.cast_ofNat]
    rw [hL,←hq] at he'
    nlinarith only [he']

/-- The consumed layer: exact selector data, every physical positive label once,
both actual source masses, and the literal q-last W subword. No endpoint premise. -/
private theorem physical_selection (a b c d : ℕ) (h : physicalDomain a b c d) :
    ∃ alpha S : ℕ, ∃ delta : ℤ,
      0 < alpha ∧ alpha < 2^(d-1)-1 ∧
      2 ≤ S ∧ 4*S ≤ 7*2^c ∧ S < 2^(d-a) ∧
      0 ≤ delta ∧ delta ≤ 2*((2 : ℤ)^(a-c)-1) ∧
      2*(2 : ℤ)^(a-c)*(2^c+1)*(alpha : ℤ) =
        (((2 : ℤ)^(a-c))^2*2^c+1)*2^(d-a) +
        ((2 : ℤ)^(a-c)*2^c+1)*(S : ℤ)-15*(2 : ℤ)^(a-c)*2^c/8+delta ∧
      8*(15*(2 : ℤ)^(a-c)*2^c/8) = 15*(2 : ℤ)^(a-c)*2^c ∧
      (∀ bank other : Fin 4, bank ≠ other →
        Disjoint (physicalBank a b c d alpha S bank) (physicalBank a b c d alpha S other)) ∧
      (Finset.univ : Finset (Fin 4)).biUnion (physicalBank a b c d alpha S) =
        Finset.range (size a b c d) \ (negatives a b c d).toFinset ∧
      (∀ isNew : Bool, ∀ bank : Fin 4,
        (∑ i ∈ physicalBank a b c d alpha S bank,
          (if isNew then newValue a b c d else oldValue a b c d) i) =
        ∑ chain : Fin 4, exponentMask a b c d alpha S bank chain *
          (if isNew then newBase a b c d else base a b c d) chain) ∧
      (wLast a b c d S).Nodup ∧
      (wLast a b c d S).toFinset = (localBits a b c d alpha S 2 3).image (d+c+·) ∧
      (lowComplement a b d S : ℤ) = (S : ℤ)*2^(b-d-1)-1 ∧
      Function.Injective (terminal a b c d) ∧
      (∀ r : Fin 4, terminal a b c d r < size a b c d) ∧
      Finset.univ.image (terminal a b c d) = (negatives a b c d).toFinset ∧
      exponentMask a b c d alpha S =
        (let u := (2 : ℤ)^(a-c)
         let z := (2 : ℤ)^c
         let h := (2 : ℤ)^(d-a)
         let t := (2 : ℤ)^(b-d-1)
         let x := u*z
         let q := h*t
         ![![(alpha : ℤ),0,(x-u-2)*q,0],
           ![0,0,u*q+(h-(S : ℤ))*t,u*(z/2-1)],
           ![x*h/2-1-(alpha : ℤ),0,0,0],
           ![0,z/2-1,2*q-1-(h-(S : ℤ))*t,u-1]]) ∧
      (∀ bank chain : Fin 4, 0 ≤ exponentMask a b c d alpha S bank chain ∧
        exponentMask a b c d alpha S bank chain <
          (2 : ℤ)^(chainLength a b c d chain-1)) ∧
      ((List.range (size a b c d)).map (oldValue a b c d)).sum = 0 ∧
      ((List.range (size a b c d)).map (newValue a b c d)).sum = -base a b c d 0 ∧
      newValue a b c d (size a b c d) = base a b c d 0 ∧
      ((List.range (size a b c d+1)).map (newValue a b c d)).sum = 0 := by
  obtain ⟨alpha,S,delta,ha0,hac,hS2,hS4,hSh,hd0,hdJ,hid,hB⟩ := selected_arithmetic a b c d h
  refine ⟨alpha,S,delta,ha0,hac,hS2,hS4,hSh,hd0,hdJ,hid,hB,?_,?_,?_,?_⟩
  · exact physical_disjoint a b c d alpha S h hac hS2 hSh
  · exact physical_cover a b c d alpha S h hac hS2 hSh
  · exact physical_mass a b c d alpha S h hac hS2 hSh
  · obtain ⟨hnd,hw,hlow⟩ := w_last_inventory a b c d alpha S h hS2 hSh
    obtain ⟨htinj,htbound,htfull⟩ := terminal_inventory a b c d h
    have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
    have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
    have hc : 2 ≤ c := by have := h.1; omega
    have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
    obtain ⟨hf,hg,he⟩ := source_totals a b c d ha hb hc hd
    refine ⟨hnd,hw,hlow,htinj,htbound,htfull,mask_coordinates a b c d alpha S h,
      mask_capacities a b c d alpha S h hac hS2 hSh,hf,hg,he,?_⟩
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,
      List.sum_singleton,hg,he]
    ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
