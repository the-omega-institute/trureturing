/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/PhysicalBanks
   generality: I
   mirror-B: none(waiver:private-implementation-for-later-endpoint)
   mirror-E: none(waiver:private-implementation-for-later-endpoint)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum, mathlib/module/Mathlib.Data.Finset.Union]
   utility: none
   digest: Constructive four-bank exponent inventory and actual old/new source masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

-- Attribution: the sealed Model.lean and its raw_expressions source; the caller's
-- specified physical ranges and collision rule. No endpoint is asserted here.
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
open scoped BigOperators
open private physicalDomain eOn rOn collide eExponent rExponent eWeight rWeight
  reservation_bounds reservation_choices physical_coordinates physical_regimes
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic
open private qHead qNewHead qMask qMass
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private size base newBase charge chainStart chainLength oldValue newValue negatives
  chain_values chainOf chain_index source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def eBits (a b : ℕ) : Finset ℕ :=
  if eOn a b then {eExponent a b} else ∅
private def rBits (a b c d : ℕ) : Finset ℕ :=
  if rOn b c d then {rExponent a b c d} else ∅

private theorem reservation_sets (a b c d : ℕ) (h : physicalDomain a b c d) :
    eBits a b ⊆ Finset.range (b-a) ∧
    rBits a b c d ⊆ Finset.range (b-a) ∧
    Disjoint (rBits a b c d) (eBits a b) := by
  obtain ⟨he,hr,hne⟩ := reservation_bounds a b c d h
  have em (i : ℕ) : i ∈ eBits a b ↔ eOn a b ∧ i=eExponent a b := by
    by_cases hh : eOn a b <;> simp [eBits,hh]
  have rm (i : ℕ) : i ∈ rBits a b c d ↔ rOn b c d ∧ i=rExponent a b c d := by
    by_cases hh : rOn b c d <;> simp [rBits,hh]
  refine ⟨?_,?_,Finset.disjoint_left.mpr ?_⟩
  · intro i hi
    obtain ⟨hh,rfl⟩ := (em i).mp hi
    exact Finset.mem_range.mpr (he hh)
  · intro i hi
    obtain ⟨hh,rfl⟩ := (rm i).mp hi
    exact Finset.mem_range.mpr (hr hh)
  · intro i hi hj
    obtain ⟨hh,rfl⟩ := (em i).mp hj
    obtain ⟨hh',heq⟩ := (rm (eExponent a b)).mp hi
    exact hne hh hh' heq

-- Arguments are chain then bank. Chains are the actual U,V,W,X chains of
-- lengths d,c,b,a, rather than a permutation of the rational head vector.
private def localBits (a b c d : ℕ) : Fin 4 → Fin 4 → Finset ℕ :=
  ![![∅,Finset.range (d-c-1),Finset.Ico (d-c-1) (d-1),∅],
    ![{c-2},Finset.range (c-2),∅,∅],
    ![∅,rBits a b c d,Finset.range (b-a) \ (rBits a b c d ∪ eBits a b),
      Finset.Ico (b-a) (b-1) ∪ eBits a b],
    ![Finset.Ico (a-2*c-1) (a-2),{a-2},Finset.range (a-2*c-1),∅]]

private theorem local_internal (a b c d : ℕ) (h : physicalDomain a b c d)
    (chain bank : Fin 4) (i : ℕ) (hi : i ∈ localBits a b c d chain bank) :
    i < chainLength a b c d chain - 1 := by
  obtain ⟨he,hr,_⟩ := reservation_sets a b c d h
  have heB : i ∈ eBits a b → i < b-a := fun hh => Finset.mem_range.mp (he hh)
  have hrB : i ∈ rBits a b c d → i < b-a := fun hh => Finset.mem_range.mp (hr hh)
  rcases h with ⟨hc,ha,hd,hb⟩
  by_cases hiE : i ∈ eBits a b <;> by_cases hiR : i ∈ rBits a b c d
  all_goals try have hei := heB hiE
  all_goals try have hri := hrB hiR
  all_goals fin_cases chain <;> fin_cases bank
  all_goals simp only [localBits,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.notMem_empty,Finset.mem_singleton,
    Finset.mem_range,Finset.mem_Ico,Finset.mem_sdiff,Finset.mem_union,hiE,hiR] at hi ⊢
  all_goals simp_all only [false_or, or_false, true_or, or_true, true_and, and_true,
    false_and, and_false, not_true_eq_false, not_false_eq_true]
  all_goals omega

private theorem local_disjoint (a b c d : ℕ) (h : physicalDomain a b c d)
    (chain bank other : Fin 4) (hne : bank ≠ other) :
    Disjoint (localBits a b c d chain bank) (localBits a b c d chain other) := by
  obtain ⟨he,hr,hRE⟩ := reservation_sets a b c d h
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have heB : i ∈ eBits a b → i < b-a := fun hh => Finset.mem_range.mp (he hh)
  have hrB : i ∈ rBits a b c d → i < b-a := fun hh => Finset.mem_range.mp (hr hh)
  have hnot : ¬ (i ∈ rBits a b c d ∧ i ∈ eBits a b) :=
    fun hh => Finset.disjoint_left.mp hRE hh.1 hh.2
  rcases h with ⟨hc,ha,hd,hb⟩
  by_cases hiE : i ∈ eBits a b <;> by_cases hiR : i ∈ rBits a b c d
  all_goals try exact (hnot ⟨hiR,hiE⟩).elim
  all_goals try have hei := heB hiE
  all_goals try have hri := hrB hiR
  all_goals fin_cases chain <;> fin_cases bank <;> fin_cases other
  all_goals try exact (hne rfl).elim
  all_goals simp only [localBits,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.notMem_empty,Finset.mem_singleton,
    Finset.mem_range,Finset.mem_Ico,Finset.mem_sdiff,Finset.mem_union,hiE,hiR] at hi hj
  all_goals simp_all only [false_or, or_false, true_or, or_true, true_and, and_true,
    false_and, and_false, not_true_eq_false, not_false_eq_true]
  all_goals omega

private theorem local_cover (a b c d : ℕ) (h : physicalDomain a b c d) (chain : Fin 4) :
    localBits a b c d chain 0 ∪ localBits a b c d chain 1 ∪
      localBits a b c d chain 2 ∪ localBits a b c d chain 3 =
      Finset.range (chainLength a b c d chain - 1) := by
  apply Finset.Subset.antisymm
  · intro i hi
    simp only [Finset.mem_union] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact Finset.mem_range.mpr (local_internal a b c d h chain 0 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d h chain 1 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d h chain 2 i hi)
    · exact Finset.mem_range.mpr (local_internal a b c d h chain 3 i hi)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases h with ⟨hc,ha,hd,hb⟩
    fin_cases chain
    all_goals simp only [localBits,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
      Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Finset.mem_union,Finset.notMem_empty,Finset.mem_singleton,
      Finset.mem_range,Finset.mem_Ico,Finset.mem_sdiff,false_or,or_false,or_assoc] at hi' ⊢
    · omega
    · omega
    · by_cases hiR : i ∈ rBits a b c d
      · exact Or.inl hiR
      · by_cases hiE : i ∈ eBits a b
        · exact Or.inr (Or.inr (Or.inr hiE))
        · by_cases hil : i < b-a
          · exact Or.inr (Or.inl ⟨hil,fun hh => hh.elim hiR hiE⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨by omega,hi'⟩))
    · omega

private def physicalBank (a b c d : ℕ) (bank : Fin 4) : Finset ℕ :=
  (Finset.univ : Finset (Fin 4)).biUnion fun chain =>
    (localBits a b c d chain bank).image (chainStart b c d chain + ·)

private theorem physical_mem (a b c d i : ℕ) (bank : Fin 4) :
    i ∈ physicalBank a b c d bank ↔
      ∃ chain : Fin 4, ∃ e ∈ localBits a b c d chain bank,
        chainStart b c d chain + e = i := by
  simp [physicalBank,Finset.mem_biUnion,Finset.mem_image]

private theorem physical_chain_unique (a b c d : ℕ) (r s : Fin 4) (e f : ℕ)
    (he : e < chainLength a b c d r - 1)
    (hf : f < chainLength a b c d s - 1)
    (heq : chainStart b c d r + e = chainStart b c d s + f) : r=s := by
  fin_cases r <;> fin_cases s
  all_goals simp only [chainStart,chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at he hf heq ⊢
  all_goals first | rfl | omega

private theorem physical_internal (a b c d : ℕ) (h : physicalDomain a b c d)
    (bank : Fin 4) (i : ℕ) (hi : i ∈ physicalBank a b c d bank) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  obtain ⟨chain,e,he,rfl⟩ := (physical_mem a b c d i bank).mp hi
  have hi := local_internal a b c d h chain bank e he
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases chain
  all_goals simp only [size,negatives,chainStart,chainLength,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,List.mem_cons,
    List.mem_singleton,List.mem_nil_iff,or_false] at hi ⊢
  all_goals omega

private theorem physical_disjoint (a b c d : ℕ) (h : physicalDomain a b c d)
    (bank other : Fin 4) (hne : bank ≠ other) :
    Disjoint (physicalBank a b c d bank) (physicalBank a b c d other) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨r,e,he,hei⟩ := (physical_mem a b c d i bank).mp hi
  obtain ⟨s,f,hf,hfi⟩ := (physical_mem a b c d i other).mp hj
  have hrs := physical_chain_unique a b c d r s e f
    (local_internal a b c d h r bank e he) (local_internal a b c d h s other f hf)
    (hei.trans hfi.symm)
  subst s
  have hef : e=f := Nat.add_left_cancel (hei.trans hfi.symm)
  subst f
  exact Finset.disjoint_left.mp (local_disjoint a b c d h r bank other hne) he hf

-- This is the complete physical inventory needed by a later four_perm consumer.
-- The four omitted labels are exactly d-1, d+c-1, d+c+b-1, k-1.
private theorem physical_cover (a b c d : ℕ) (h : physicalDomain a b c d) :
    (Finset.univ : Finset (Fin 4)).biUnion (physicalBank a b c d) =
      Finset.range (size a b c d) \ (negatives a b c d).toFinset := by
  classical
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  ext i
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_sdiff,
    Finset.mem_range,List.mem_toFinset]
  constructor
  · rintro ⟨bank,hi⟩
    exact physical_internal a b c d h bank i hi
  · rintro ⟨hi,hn⟩
    obtain ⟨he,_,hp⟩ := chain_index a b c d i ha hb hc hd hi
    let chain := chainOf b c d i
    let e := i-chainStart b c d chain
    have hei : chainStart b c d chain + e = i := he
    have hel : e < chainLength a b c d chain - 1 := by
      have hh := hp hn
      dsimp [chain,e] at *
      omega
    have hm : e ∈ localBits a b c d chain 0 ∪ localBits a b c d chain 1 ∪
        localBits a b c d chain 2 ∪ localBits a b c d chain 3 := by
      rw [local_cover a b c d h chain]
      exact Finset.mem_range.mpr hel
    simp only [Finset.mem_union] at hm
    rcases hm with ((hm|hm)|hm)|hm
    · exact ⟨0,(physical_mem a b c d i 0).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨1,(physical_mem a b c d i 1).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨2,(physical_mem a b c d i 2).mpr ⟨chain,e,hm,hei⟩⟩
    · exact ⟨3,(physical_mem a b c d i 3).mpr ⟨chain,e,hm,hei⟩⟩

-- Terminal order is bank order U,X,W,V, not the chain order U,V,W,X.
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
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] at he ⊢
    all_goals first | rfl | omega
  · intro r
    fin_cases r <;> simp only [terminal,size,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply] <;> omega
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

-- No binary-decoder layer is needed: each chosen exponent is a physical bit.
-- Range/Ico sums use mathlib's existing geometric sums, including empty range 0.
private def exponentMask (a b c d : ℕ) : Fin 4 → Fin 4 → ℚ :=
  ![![0,2^(c-2),0,2^(a-2)-2^(a-2*c-1)],
    ![2^(d-c-1)-1,2^(c-2)-1,rWeight a b c d,2^(a-2)],
    ![2^(d-1)-2^(d-c-1),0,2^(b-a)-1-rWeight a b c d-eWeight a b,
      2^(a-2*c-1)-1],
    ![0,0,2^(b-1)-2^(b-a)+eWeight a b,0]]

private theorem local_sums (a b c d : ℕ) (h : physicalDomain a b c d)
    (bank chain : Fin 4) :
    (∑ e ∈ localBits a b c d chain bank, (2:ℚ)^e) = exponentMask a b c d bank chain := by
  classical
  have hs (n : ℕ) : (∑ e ∈ Finset.range n, (2:ℚ)^e) = 2^n-1 := by
    simpa only [show (2:ℚ)-1=1 by norm_num, mul_one] using geom_sum_mul (2:ℚ) n
  have ht (l u : ℕ) (hle : l ≤ u) :
      (∑ e ∈ Finset.Ico l u, (2:ℚ)^e) = 2^u-2^l := by
    simpa only [show (2:ℚ)-1=1 by norm_num, mul_one] using geom_sum_Ico_mul (2:ℚ) hle
  have es : (∑ e ∈ eBits a b, (2:ℚ)^e) = eWeight a b := by
    by_cases he : eOn a b <;> simp [eBits,eWeight,he]
  have rs : (∑ e ∈ rBits a b c d, (2:ℚ)^e) = rWeight a b c d := by
    by_cases hr : rOn b c d <;> simp [rBits,rWeight,hr]
  obtain ⟨he,hr,hRE⟩ := reservation_sets a b c d h
  have hsub : rBits a b c d ∪ eBits a b ⊆ Finset.range (b-a) :=
    Finset.union_subset hr he
  have hdiff := Finset.sum_sdiff (f := fun e : ℕ => (2:ℚ)^e) hsub
  rw [Finset.sum_union hRE,rs,es,hs] at hdiff
  have hhigh : Disjoint (Finset.Ico (b-a) (b-1)) (eBits a b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hl := (Finset.mem_Ico.mp hi).1
    have hh := Finset.mem_range.mp (he hj)
    omega
  have hhighsum : (∑ e ∈ Finset.Ico (b-a) (b-1) ∪ eBits a b, (2:ℚ)^e) =
      2^(b-1)-2^(b-a)+eWeight a b := by
    rcases h with ⟨hc,ha,hd,hb⟩
    rw [Finset.sum_union hhigh,ht _ _ (by omega),es]
  rcases h with ⟨hc,ha,hd,hb⟩
  fin_cases chain <;> fin_cases bank
  all_goals simp only [localBits,exponentMask,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero',
    Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Finset.sum_empty,Finset.sum_singleton]
  all_goals first
    | rfl
    | exact hs _
    | exact ht _ _ (by omega)
    | exact rs
    | exact hhighsum
    | linarith only [hdiff]

private theorem model_masks (a b c d : ℕ) (h : physicalDomain a b c d)
    (bank chain : Fin 4) :
    exponentMask a b c d bank chain =
      qMask ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) bank chain := by
  obtain ⟨hw,hL,hy,hE,hD,hV,hS,hH⟩ := physical_coordinates a b c d h
  rw [hw] at hS hH
  fin_cases bank <;> fin_cases chain
  all_goals simp [exponentMask,qMask,hw,hL,hy,hE,hD,hV,hS,hH]

private theorem physical_heads (a b c d : ℕ) (h : physicalDomain a b c d) :
    (∀ chain : Fin 4, (base a b c d chain : ℚ) =
      qHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain) ∧
    (∀ chain : Fin 4, (newBase a b c d chain : ℚ) =
      qNewHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain) := by
  obtain ⟨hw,hL,hy,hE,hD,hV,hS,hH⟩ := physical_coordinates a b c d h
  have hY : 2*(2:ℚ)^a*2^(b-a-1) = 2^b := by
    rw [mul_assoc,hy,← pow_succ']
    congr 1
    rcases h with ⟨hc,ha,hd,hb⟩
    omega
  constructor
  · intro chain
    fin_cases chain <;> simp [base,qHead,hw,hY] <;> ring
  · intro chain
    fin_cases chain <;> simp [newBase,base,charge,qNewHead,qHead,hw,hY] <;> ring

private def physicalValue (a b c d : ℕ) (isNew : Bool) (i : ℕ) : ℚ :=
  if isNew then (newValue a b c d i : ℚ) else (oldValue a b c d i : ℚ)

private theorem actual_chain_values (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (chain : Fin 4) (e : ℕ) (he : e < chainLength a b c d chain-1) :
    physicalValue a b c d isNew (chainStart b c d chain+e) = (2:ℚ)^e *
      (if isNew then qNewHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain
        else qHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain) := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hel : e < chainLength a b c d chain := by omega
  have hep : e+1 < chainLength a b c d chain := by omega
  obtain ⟨_,hf,hg,_⟩ := chain_values a b c d ha hb hc hd
  obtain ⟨hA,hB⟩ := physical_heads a b c d h
  cases isNew
  · have hh := hf chain e hel
    rw [if_pos hep] at hh
    simpa [physicalValue,Int.cast_mul,Int.cast_pow,hA chain] using
      congrArg (fun n : ℤ => (n:ℚ)) hh
  · have hh := hg chain e hel
    rw [if_pos hep] at hh
    simpa [physicalValue,Int.cast_mul,Int.cast_pow,hB chain] using
      congrArg (fun n : ℤ => (n:ℚ)) hh

-- All summands here are actual centered-source values, rather than arbitrary
-- values postulated to have the desired masks.
private theorem physical_mass (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (bank : Fin 4) :
    (∑ i ∈ physicalBank a b c d bank, physicalValue a b c d isNew i) =
      qMass ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) isNew bank := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 4)))
      (fun chain => (localBits a b c d chain bank).image (chainStart b c d chain + ·)) := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
    obtain ⟨f,hf,hfi⟩ := Finset.mem_image.mp hj
    exact hrs (physical_chain_unique a b c d r s e f
      (local_internal a b c d h r bank e he) (local_internal a b c d h s bank f hf)
      (hei.trans hfi.symm))
  rw [physicalBank,Finset.sum_biUnion hdis]
  unfold qMass
  apply Finset.sum_congr rfl
  intro chain hc
  rw [Finset.sum_image (by intro i hi j hj he; exact Nat.add_left_cancel he)]
  calc
    (∑ e ∈ localBits a b c d chain bank,
        physicalValue a b c d isNew (chainStart b c d chain+e)) =
      ∑ e ∈ localBits a b c d chain bank, (2:ℚ)^e *
        (if isNew then qNewHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain
          else qHead ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) chain) := by
      apply Finset.sum_congr rfl
      intro e he
      exact actual_chain_values a b c d h isNew chain e (local_internal a b c d h chain bank e he)
    _ = _ := by
      rw [← Finset.sum_mul,local_sums a b c d h bank chain,model_masks a b c d h bank chain]


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
