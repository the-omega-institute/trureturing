import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C3Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.DiagonalArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalBanks

/-! Prepared residual construction.  Required original-owner publications, with unchanged bodies:
   PacketNormalForm.Source: size, chainStart, chainLength, negatives;
   PacketNormalForm.Structure: blocksWord;
   PacketNormalForm.Certificate: orderedPackets.
   SecondPeakLowXTail.PhysicalBanks: physical_chain_unique.
   All uses below are at the future public canonical addresses.  This is a
   label/multiplicity construction, not a finiteChecks certificate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open PacketNormalForm

noncomputable def physicalBank (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (bank : Fin 4) : Finset ℕ :=
  (Finset.univ : Finset (Fin 4)).biUnion fun chain =>
    (bits (M bank chain)).image (chainStart b c d chain + ·)

def terminalLabel (a b c d : ℕ) (chain : Fin 4) : ℕ :=
  chainStart b c d chain + chainLength a b c d chain - 1

noncomputable def physicalPackets (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (order : Fin 4 → Fin 4) : List (Finset ℕ × ℕ) :=
  [(physicalBank a b c d M 0, terminalLabel a b c d (order 0)),
   (physicalBank a b c d M 1, terminalLabel a b c d (order 1)),
   (physicalBank a b c d M 2, terminalLabel a b c d (order 2)),
   (physicalBank a b c d M 3, terminalLabel a b c d (order 3))]

noncomputable def physicalWord (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (order : Fin 4 → Fin 4) : List ℕ :=
  blocksWord (orderedPackets (physicalPackets a b c d M order))

/-- The bank argument is a Fin 4, as in the actual mask matrix. -/
theorem physical_mem (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (bank : Fin 4) (i : ℕ) :
    i ∈ physicalBank a b c d M bank ↔
      ∃ chain : Fin 4, ∃ e ∈ bits (M bank chain), chainStart b c d chain + e = i := by
  classical
  simp [physicalBank, Finset.mem_biUnion, Finset.mem_image]

theorem physical_labels (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain - 1)
      (fun bank => M bank chain)) (bank : Fin 4) (i : ℕ)
    (hi : i ∈ physicalBank a b c d M bank) :
    i < size a b c d ∧ i ∉ negatives a b c d := by
  obtain ⟨chain,e,he,rfl⟩ := (physical_mem a b c d M bank i).mp hi
  have hbit : (M bank chain).testBit e = true := (mem_bits _ _).mp he
  have he' := SecondPeakHighD.bit_below (M bank chain)
    (chainLength a b c d chain-1) e ((hinv chain).capacity bank) hbit
  fin_cases chain <;> simp [chainStart, chainLength, negatives, size] at he' ⊢ <;> omega

theorem physical_bank_unique (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain - 1)
      (fun bank => M bank chain))
    (i : ℕ) (r s : Fin 4) (hr : i ∈ physicalBank a b c d M r)
    (hs : i ∈ physicalBank a b c d M s) : r = s := by
  obtain ⟨cr,er,her,hpr⟩ := (physical_mem a b c d M r i).mp hr
  obtain ⟨cs,es,hes,hps⟩ := (physical_mem a b c d M s i).mp hs
  have hbr := SecondPeakHighD.bit_below (M r cr) _ er ((hinv cr).capacity r)
    ((mem_bits _ _).mp her)
  have hbs := SecondPeakHighD.bit_below (M s cs) _ es ((hinv cs).capacity s)
    ((mem_bits _ _).mp hes)
  have hchain := SecondPeakLowXTail.physical_chain_unique a b c d cr cs er es
    hbr hbs (hpr.trans hps.symm)
  subst cs
  have hoff : er = es := Nat.add_left_cancel (hpr.trans hps.symm)
  subst es
  by_contra hrs
  exact Finset.disjoint_left.mp ((hinv cr).disjoint r s hrs) her hes

theorem physical_cover (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain - 1)
      (fun bank => M bank chain)) (i : ℕ)
    (hi : i < size a b c d) (hn : i ∉ negatives a b c d) :
    ∃ bank : Fin 4, i ∈ physicalBank a b c d M bank := by
  have hcover (chain : Fin 4) (e : ℕ) (he : e < chainLength a b c d chain-1) :
      ∃ bank, e ∈ bits (M bank chain) := by
    have hm : e ∈ bits (M 0 chain) ∪ bits (M 1 chain) ∪
        bits (M 2 chain) ∪ bits (M 3 chain) := by
      rw [(hinv chain).full]
      exact Finset.mem_range.mpr he
    simp only [Finset.mem_union] at hm
    rcases hm with ((h | h) | h) | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
  have hloc : i < d-1 ∨ (d ≤ i ∧ i < d+c-1) ∨
      (d+c ≤ i ∧ i < d+c+b-1) ∨ (d+c+b ≤ i ∧ i < a+b+c+d-1) := by
    simp only [size] at hi
    simp only [negatives, size, List.mem_cons, List.mem_singleton, not_or] at hn
    omega
  rcases hloc with h | h | h | h
  · have he : i < chainLength a b c d 0 - 1 := by simpa [chainLength] using h
    obtain ⟨bank,hebit⟩ := hcover 0 i he
    exact ⟨bank, (physical_mem a b c d M bank i).mpr
      ⟨0,i,hebit,by simp [chainStart]⟩⟩
  · have he : i-d < chainLength a b c d 1 - 1 := by simp [chainLength]; omega
    obtain ⟨bank,hebit⟩ := hcover 1 (i-d) he
    refine ⟨bank, (physical_mem a b c d M bank i).mpr ⟨1,i-d,hebit,?_⟩⟩
    simp [chainStart] <;> omega
  · have he : i-(d+c) < chainLength a b c d 2 - 1 := by simp [chainLength]; omega
    obtain ⟨bank,hebit⟩ := hcover 2 (i-(d+c)) he
    refine ⟨bank, (physical_mem a b c d M bank i).mpr ⟨2,i-(d+c),hebit,?_⟩⟩
    norm_num [chainStart]
    omega
  · have he : i-(d+c+b) < chainLength a b c d 3 - 1 := by simp [chainLength]; omega
    obtain ⟨bank,hebit⟩ := hcover 3 (i-(d+c+b)) he
    refine ⟨bank, (physical_mem a b c d M bank i).mpr ⟨3,i-(d+c+b),hebit,?_⟩⟩
    norm_num [chainStart]
    omega

theorem physical_negative_order (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (order : Fin 4 → Fin 4)
    (horder : ([order 0,order 1,order 2,order 3] : List (Fin 4)).Perm [0,1,2,3]) :
    ((physicalPackets a b c d M order).map Prod.snd).Perm (negatives a b c d) := by
  have ht : ([terminalLabel a b c d 0, terminalLabel a b c d 1,
      terminalLabel a b c d 2, terminalLabel a b c d 3] : List ℕ) = negatives a b c d := by
    simp [terminalLabel, chainStart, chainLength, negatives, size,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  simpa only [physicalPackets, List.map_cons, List.map_nil, ht] using
    horder.map (terminalLabel a b c d)

/-- Each physical label occurs exactly once.  The proof computes multiset
counts, using unique bank ownership for positives and the terminal permutation
for negatives.  Finset equality alone cannot prove this statement. -/
theorem physical_partition (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain - 1)
      (fun bank => M bank chain)) (order : Fin 4 → Fin 4)
    (horder : ([order 0,order 1,order 2,order 3] : List (Fin 4)).Perm [0,1,2,3]) :
    (physicalWord a b c d M order : Multiset ℕ) =
      (List.range (size a b c d) : Multiset ℕ) := by
  classical
  let B := physicalBank a b c d M
  have hlabels := physical_labels a b c d ha hb hc hd M hinv
  have hown := physical_bank_unique a b c d ha hb hc hd M hinv
  have hng : (negatives a b c d : Multiset ℕ).Nodup := by
    change (negatives a b c d).Nodup
    simp [negatives, size] <;> omega
  apply Multiset.ext.mpr
  intro i
  have hcount (P : Finset ℕ) :
      Multiset.count i (P.toList : Multiset ℕ) = if i ∈ P then 1 else 0 := by
    rw [Finset.coe_toList]
    exact Multiset.count_eq_of_nodup P.nodup
  have hncount : Multiset.count i (negatives a b c d : Multiset ℕ) =
      if i ∈ negatives a b c d then 1 else 0 := by
    simpa using Multiset.count_eq_of_nodup (a := i) hng
  have hrange : Multiset.count i (List.range (size a b c d) : Multiset ℕ) =
      if i < size a b c d then 1 else 0 := by
    simpa using Multiset.count_eq_of_nodup (a := i)
      (show (List.range (size a b c d) : Multiset ℕ).Nodup from List.nodup_range)
  have hneg := congrArg (fun xs : Multiset ℕ => Multiset.count i xs)
    (Multiset.coe_eq_coe.mpr (physical_negative_order a b c d M order horder))
  simp only [physicalPackets, List.map_cons, List.map_nil, Prod.snd,
    ← Multiset.cons_coe, Multiset.coe_nil, Multiset.count_cons, Multiset.count_zero] at hneg
  have hw : Multiset.count i (physicalWord a b c d M order : Multiset ℕ) =
      (if i ∈ B 0 then 1 else 0) + (if i ∈ B 1 then 1 else 0) +
      (if i ∈ B 2 then 1 else 0) + (if i ∈ B 3 then 1 else 0) +
      Multiset.count i (negatives a b c d : Multiset ℕ) := by
    simp only [physicalWord, physicalPackets, orderedPackets, blocksWord,
      List.map_cons, List.map_nil, ← Multiset.coe_add, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.count_add, Multiset.count_cons,
      Multiset.count_zero, hcount]
    dsimp only [B]
    omega
  rw [hw, hncount]
  rw [hrange]
  by_cases hi : i < size a b c d
  · by_cases hn : i ∈ negatives a b c d
    · have hempty (r : Fin 4) : i ∉ B r := fun hh => (hlabels r i hh).2 hn
      simp [hempty, hn, hi]
    · obtain ⟨r,hr⟩ := physical_cover a b c d ha hb hc hd M hinv i hi hn
      have hone (s : Fin 4) : i ∈ B s ↔ s = r := by
        constructor
        · intro hs; exact hown i s r hs hr
        · rintro rfl; exact hr
      simp only [hone, hn, hi, ite_false, ite_true, add_zero]
      fin_cases r <;> decide
  · have hempty (r : Fin 4) : i ∉ B r := fun hh => hi (hlabels r i hh).1
    have hn : i ∉ negatives a b c d := by
      dsimp only [size] at hi
      simp [negatives, size] <;> omega
    simp [hempty, hn, hi]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
