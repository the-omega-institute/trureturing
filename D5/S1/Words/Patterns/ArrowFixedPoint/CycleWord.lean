/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/CycleWord
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/CycleWord
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The literal first fundamental permutation equivalence and fixed-point bridge. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.CycleBlocks

/-!
# Literal first-fundamental permutation equivalence

The inverse cuts an actual one-line permutation before its left-to-right
maxima and applies `List.formPerm` separately to every block.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm

noncomputable section

/-- Decode every record block as its own cycle. -/
def decodeBlocks {α : Type*} [DecidableEq α] (blocks : List (List α)) :
    Equiv.Perm α :=
  (blocks.map List.formPerm).prod

/-- Literal inverse first-fundamental map on a one-line permutation. -/
def cyclePermutation {n : ℕ} (word : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  decodeBlocks (recordCuts (List.ofFn word))

private lemma formPerms_pairwise_disjoint {α : Type*} [DecidableEq α] [Finite α]
    {blocks : List (List α)} (hn : blocks.flatten.Nodup) :
    (blocks.map List.formPerm).Pairwise Equiv.Perm.Disjoint := by
  let _ := Fintype.ofFinite α
  have hblocks := (List.nodup_flatten.mp hn).2
  rw [List.pairwise_map]
  refine hblocks.imp ?_
  intro left right hdis
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro x hxLeft hxRight
  have hleft : x ∈ left := by
    exact List.mem_toFinset.mp (List.support_formPerm_le left hxLeft)
  have hright : x ∈ right := by
    exact List.mem_toFinset.mp (List.support_formPerm_le right hxRight)
  exact (List.disjoint_left.mp hdis hleft) hright

/-- Independently decoding all singleton-complete standard blocks recovers the
original permutation. -/
theorem decode_standardCycleBlocks {n : ℕ} (p : Equiv.Perm (Fin n)) :
    decodeBlocks (standardCycleBlocks p) = p := by
  let factors := (standardCycleBlocks p).map List.formPerm
  have hpair : factors.Pairwise Equiv.Perm.Disjoint := by
    apply formPerms_pairwise_disjoint
    simpa only [standardCycleWord] using (standardCycleWord_nodup p)
  have hfactor (m : Fin n) (hm : orbitMaximum p m = m) :
      List.formPerm (standardBlock p m) = p.cycleOf m := by
    by_cases hfix : p m = m
    · simp [standardBlock, hfix, (Equiv.Perm.cycleOf_eq_one_iff p).2 hfix]
    · simpa [standardBlock, hfix] using Equiv.Perm.formPerm_toList p m
  change factors.prod = p
  apply Equiv.ext
  intro x
  by_cases hfix : p x = x
  · have hnot : x ∉ factors.prod.support := by
      intro hxprod
      obtain ⟨f, hf, hxf⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hxprod
      simp only [factors, standardCycleBlocks, List.mem_map] at hf
      obtain ⟨block, ⟨m, hmList, rfl⟩, rfl⟩ := hf
      have hm : orbitMaximum p m = m := by simpa [orbitMaxima] using hmList
      rw [hfactor m hm, Equiv.Perm.mem_support_cycleOf_iff] at hxf
      have hxSupport : x ∈ p.support := hxf.1.mem_support_iff.mp hxf.2
      exact (Equiv.Perm.mem_support.mp hxSupport) hfix
    simpa [hfix] using Equiv.Perm.notMem_support.mp hnot
  · let m := orbitMaximum p x
    have hcycle : p.SameCycle m x := by
      apply Equiv.Perm.SameCycle.symm
      have hmaxMem : orbitMaximum p x ∈ orbit p x := by
        unfold orbitMaximum
        exact Finset.max'_mem _ _
      simpa [m, orbit] using hmaxMem
    have hm : orbitMaximum p m = m := by
      simpa [m] using orbitMaximum_eq_of_sameCycle p hcycle
    have hmList : m ∈ orbitMaxima p := by simpa [orbitMaxima] using hm
    let f := List.formPerm (standardBlock p m)
    have hf : f ∈ factors := by
      unfold factors
      rw [List.mem_map]
      refine ⟨standardBlock p m, ?_, rfl⟩
      rw [standardCycleBlocks, List.mem_map]
      exact ⟨m, hmList, rfl⟩
    have hxf : x ∈ f.support := by
      dsimp only [f]
      rw [hfactor m hm, Equiv.Perm.mem_support_cycleOf_iff]
      exact ⟨hcycle, Equiv.Perm.mem_support.mpr (hcycle.apply_eq_self_iff.not.mpr hfix)⟩
    calc
      factors.prod x = f x :=
        (Equiv.Perm.eq_on_support_mem_disjoint hf hpair x hxf).symm
      _ = p.cycleOf m x := by dsimp only [f]; rw [hfactor m hm]
      _ = p x := hcycle.cycleOf_apply

/-- The actual one-line permutation obtained by erasing the parentheses in the
singleton-complete standard cycle notation. -/
def standardWordPermutation {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  let lengthEq : (standardCycleWord p).length = n := by
    let e := (standardCycleWord_nodup p).getEquivOfForallMemList
      (standardCycleWord p) (standardCycleWord_mem p)
    simpa [e] using Fintype.card_congr e
  (finCongr lengthEq.symm).trans
    ((standardCycleWord_nodup p).getEquivOfForallMemList
      (standardCycleWord p) (standardCycleWord_mem p))

/-- Foata's literal first fundamental transformation: write every cycle with
its maximum first, sort cycles by increasing maxima, then erase parentheses.
Its inverse cuts the one-line word before record maxima and decodes each block
as a separate cycle. -/
def theta {n : ℕ} : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
  let oneLine (p : Equiv.Perm (Fin n)) :
      List.ofFn (standardWordPermutation p) = standardCycleWord p := by
    let lengthEq : (standardCycleWord p).length = n := by
      let e := (standardCycleWord_nodup p).getEquivOfForallMemList
        (standardCycleWord p) (standardCycleWord_mem p)
      simpa [e] using Fintype.card_congr e
    change List.ofFn ((finCongr lengthEq.symm).trans
      ((standardCycleWord_nodup p).getEquivOfForallMemList
        (standardCycleWord p) (standardCycleWord_mem p))) = standardCycleWord p
    rw [List.ofFn_congr lengthEq.symm]
    exact List.ofFn_get (standardCycleWord p)
  {
    toFun := standardWordPermutation
    invFun := cyclePermutation
    left_inv := fun p => by
      rw [cyclePermutation, oneLine p, recordCuts_standardCycleWord,
        decode_standardCycleBlocks]
    right_inv := fun word => by
      apply (Finite.injective_iff_surjective.mpr (fun p =>
        ⟨standardWordPermutation p, by
          rw [cyclePermutation, oneLine p, recordCuts_standardCycleWord,
            decode_standardCycleBlocks]⟩) :
        Function.Injective (@cyclePermutation n))
      rw [cyclePermutation, oneLine (cyclePermutation word),
        recordCuts_standardCycleWord, decode_standardCycleBlocks]
  }

private lemma decodeBlocks_fixed_iff_singleton {α : Type*}
    [DecidableEq α] [Finite α] (blocks : List (List α))
    (hn : blocks.flatten.Nodup) (hne : [] ∉ blocks) (x : α)
    (hx : x ∈ blocks.flatten) :
    decodeBlocks blocks x = x ↔ [x] ∈ blocks := by
  let _ := Fintype.ofFinite α
  let factors := blocks.map List.formPerm
  have hpair : factors.Pairwise Equiv.Perm.Disjoint :=
    formPerms_pairwise_disjoint hn
  have hblockNodup : ∀ block ∈ blocks, block.Nodup :=
    (List.nodup_flatten.mp hn).1
  have hblocksDisjoint : blocks.Pairwise List.Disjoint :=
    (List.nodup_flatten.mp hn).2
  constructor
  · intro hfixed
    obtain ⟨block, hblock, hxblock⟩ := List.mem_flatten.mp hx
    by_contra hnot
    have hnotSingleton : ∀ y, block ≠ [y] := by
      intro y heq
      subst block
      simp only [List.mem_singleton] at hxblock
      subst y
      exact hnot hblock
    have hxsupport : x ∈ (List.formPerm block).support := by
      rw [List.support_formPerm_of_nodup block (hblockNodup block hblock)
        hnotSingleton]
      simpa using hxblock
    have hfactor : List.formPerm block ∈ factors := by
      exact List.mem_map.mpr ⟨block, hblock, rfl⟩
    have hacts :=
      Equiv.Perm.eq_on_support_mem_disjoint hfactor hpair x hxsupport
    have hformFixed : List.formPerm block x = x := hacts.trans hfixed
    exact hnotSingleton x <| by
      have hlen : block.length ≤ 1 :=
        (List.formPerm_apply_mem_eq_self_iff block
          (hblockNodup block hblock) x hxblock).mp hformFixed
      cases block with
      | nil => exact (hne hblock).elim
      | cons y tail =>
          have : tail = [] := by simpa using hlen
          subst tail
          simpa [eq_comm] using hxblock
  · intro hsingleton
    rw [← Equiv.Perm.notMem_support]
    intro hsupport
    obtain ⟨f, hf, hxf⟩ :=
      Equiv.Perm.exists_mem_support_of_mem_support_prod hsupport
    obtain ⟨block, hblock, rfl⟩ := List.mem_map.mp hf
    have hxblock : x ∈ block := by
      exact List.mem_toFinset.mp (List.support_formPerm_le block hxf)
    by_cases heq : block = [x]
    · subst block
      simp at hxf
    · let : Std.Symm (List.Disjoint : List α → List α → Prop) :=
        ⟨fun _ _ h => h.symm⟩
      have hdisjoint : List.Disjoint block [x] :=
        hblocksDisjoint.set_pairwise hblock hsingleton heq
      exact (List.disjoint_left.mp hdisjoint hxblock) (by simp)

/-- A block cut from a one-line word is a singleton exactly when that label is
a fixed point of the inverse first-fundamental permutation. -/
theorem singleton_recordCut_iff_theta_symm_fixed {n : ℕ}
    (word : Equiv.Perm (Fin n)) (x : Fin n) :
    [x] ∈ recordCuts (List.ofFn word) ↔ theta.symm word x = x := by
  change [x] ∈ recordCuts (List.ofFn word) ↔ cyclePermutation word x = x
  rw [cyclePermutation]
  exact (decodeBlocks_fixed_iff_singleton _
    (by simpa using (List.nodup_ofFn.mpr word.injective))
    (nil_not_mem_recordCuts (List.ofFn word)) x
    (by
      rw [flatten_recordCuts, List.mem_ofFn]
      exact ⟨word.symm x, word.apply_symm_apply x⟩)).symm

end


end D5.S1.Words.Patterns.ArrowFixedPoint
