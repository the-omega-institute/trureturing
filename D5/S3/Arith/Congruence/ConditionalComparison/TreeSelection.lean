/- GID: D5/S3/Arith/Congruence/ConditionalComparison/TreeSelection
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Prefix-tree counting and residual selection. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/TreeSelection.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.Cylinders
import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Prefix-tree counting and residual selection

This module supplies the finite combinatorics used to remove pure cylinders.
The first step is an explicit equivalence between extensions of a fixed
prefix and arbitrary suffixes; all descendant counts therefore reduce to
the cardinality of a finite function space.
-/

namespace Erdos7

section PrefixCounting

variable {q a d : ℕ}

/-- Extend a prefix by an arbitrary suffix. -/
noncomputable def extendPrefix (u : Prefix q d) (hda : d ≤ a)
    (v : Word q (a - d)) : Word q a := by
  classical
  intro i
  by_cases hi : (i : ℕ) < d
  · exact u ⟨i, hi⟩
  · exact v ⟨(i : ℕ) - d, by omega⟩

theorem extendPrefix_hasPrefix (u : Prefix q d) (hda : d ≤ a)
    (v : Word q (a - d)) : HasPrefix (extendPrefix u hda v) u hda := by
  intro i
  simp [extendPrefix, i.isLt]

/-- Extract the suffix following a prescribed depth. -/
def suffixAfter (w : Word q a) (hda : d ≤ a) : Word q (a - d) :=
  fun i ↦ w ⟨d + i, by omega⟩

theorem suffixAfter_extendPrefix (u : Prefix q d) (hda : d ≤ a)
    (v : Word q (a - d)) :
    suffixAfter (extendPrefix u hda v) hda = v := by
  classical
  funext i
  simp [suffixAfter, extendPrefix]

theorem extendPrefix_suffixAfter (u : Prefix q d) (hda : d ≤ a)
    (w : Word q a) (hw : HasPrefix w u hda) :
    extendPrefix u hda (suffixAfter w hda) = w := by
  classical
  funext i
  by_cases hi : (i : ℕ) < d
  · simp [extendPrefix, hi]
    exact (hw ⟨i, hi⟩).symm
  · simp [extendPrefix, hi, suffixAfter]
    congr 1
    apply Fin.ext
    exact Nat.add_sub_of_le (Nat.le_of_not_gt hi)

/-- Words extending `u` are in bijection with free suffixes. -/
noncomputable def prefixExtensionEquiv (u : Prefix q d) (hda : d ≤ a) :
    {w : Word q a // HasPrefix w u hda} ≃ Word q (a - d) where
  toFun w := suffixAfter w.1 hda
  invFun v := ⟨extendPrefix u hda v, extendPrefix_hasPrefix u hda v⟩
  left_inv w := by
    apply Subtype.ext
    exact extendPrefix_suffixAfter u hda w.1 w.2
  right_inv v := suffixAfter_extendPrefix u hda v

/-- A depth-`d` prefix in a `q`-ary height-`a` tree has `q^(a-d)` leaves. -/
theorem card_prefix_extensions (u : Prefix q d) (hda : d ≤ a) :
    Nat.card {w : Word q a // HasPrefix w u hda} = q ^ (a - d) := by
  classical
  rw [Nat.card_congr (prefixExtensionEquiv u hda)]
  simp

/-- The finite set of words extending a prefix. -/
noncomputable def prefixWords (u : Prefix q d) (hda : d ≤ a) :
    Finset (Word q a) := by
  classical
  exact Finset.univ.filter fun w ↦ HasPrefix w u hda

@[simp] theorem mem_prefixWords (u : Prefix q d) (hda : d ≤ a)
    (w : Word q a) :
    w ∈ prefixWords u hda ↔ HasPrefix w u hda := by
  classical
  simp [prefixWords]

theorem card_prefixWords (u : Prefix q d) (hda : d ≤ a) :
    (prefixWords u hda).card = q ^ (a - d) := by
  classical
  letI : Fintype {w : Word q a // HasPrefix w u hda} := Fintype.ofFinite _
  calc
    (prefixWords u hda).card =
        Fintype.card {w : Word q a // HasPrefix w u hda} := by
          simpa [prefixWords] using
            (Fintype.card_subtype (fun w : Word q a ↦ HasPrefix w u hda)).symm
    _ = Nat.card {w : Word q a // HasPrefix w u hda} :=
      (Nat.card_eq_fintype_card).symm
    _ = q ^ (a - d) := card_prefix_extensions u hda

end PrefixCounting

section TernarySelection

/-- One (possibly artificial) forbidden ternary prefix at every depth. -/
abbrev ForbiddenPrefixes (a : ℕ) :=
  (d : Fin (a + 1)) → Prefix 3 (d : ℕ)

/-- Canonical proof that an indexed prefix depth fits the ambient height. -/
def indexedDepthLe {a : ℕ} (d : Fin (a + 1)) : (d : ℕ) ≤ a :=
  Nat.le_of_lt_succ d.isLt

theorem forbiddenPrefix_congr {a : ℕ} (f : ForbiddenPrefixes a)
    (w : Word 3 a) {i j : Fin (a + 1)} (hij : i = j)
    (h : HasPrefix w (f j) (indexedDepthLe j)) :
    HasPrefix w (f i) (indexedDepthLe i) := by
  subst j
  exact h

/-- Parents killed by a forbidden prefix of some nonterminal depth. -/
noncomputable def badParents (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    Finset (Word 3 n) := by
  classical
  exact Finset.univ.biUnion fun d : Fin n ↦
    prefixWords (a := n) (f d.succ.castSucc) (Nat.succ_le_of_lt d.isLt)

/-- Union bound for the forbidden parent set. -/
theorem card_badParents_le (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    (badParents n f).card ≤ ∑ i ∈ Finset.range n, 3 ^ i := by
  classical
  calc
    (badParents n f).card ≤
        ∑ d : Fin n, (prefixWords (a := n) (f d.succ.castSucc)
          (Nat.succ_le_of_lt d.isLt)).card := by
      unfold badParents
      exact Finset.card_biUnion_le
    _ = ∑ d : Fin n, 3 ^ (n - ((d : ℕ) + 1)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [card_prefixWords]
      rfl
    _ = ∑ i ∈ Finset.range n, 3 ^ (n - 1 - i) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i ↦ 3 ^ (n - (i + 1))) n]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    _ = ∑ i ∈ Finset.range n, 3 ^ i := Finset.sum_range_reflect _ _

theorem mem_badParents_iff (n : ℕ) (f : ForbiddenPrefixes (n + 1))
    (w : Word 3 n) :
    w ∈ badParents n f ↔ ∃ d : Fin n,
      HasPrefix w (f d.succ.castSucc) (Nat.succ_le_of_lt d.isLt) := by
  classical
  simp [badParents]

/-- Parents not killed by a nonterminal forbidden prefix. -/
noncomputable def goodParents (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    Finset (Word 3 n) := Finset.univ \ badParents n f

theorem card_goodParents_ge (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    (∑ i ∈ Finset.range n, 3 ^ i) + 1 ≤ (goodParents n f).card := by
  classical
  let G : ℕ := ∑ i ∈ Finset.range n, 3 ^ i
  have hbad : (badParents n f).card ≤ G := card_badParents_le n f
  have htotal : (Finset.univ : Finset (Word 3 n)).card = 3 ^ n := by simp
  have hgood : (goodParents n f).card = 3 ^ n - (badParents n f).card := by
    unfold goodParents
    rw [Finset.card_sdiff, Finset.inter_univ, htotal]
  have hgeom := geom_sum_mul_add (2 : ℕ) n
  have hidentity : 3 ^ n = 2 * G + 1 := by
    dsimp [G]
    norm_num at hgeom ⊢
    omega
  rw [hgood, hidentity]
  omega

/-- A bottom-packed choice of exactly one more than the geometric sum of
good parents. -/
noncomputable def selectedParents (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    Finset (Word 3 n) :=
  Classical.choose (Finset.exists_subset_card_eq (card_goodParents_ge n f))

theorem selectedParents_subset_good (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    selectedParents n f ⊆ goodParents n f :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (card_goodParents_ge n f))).1

@[simp] theorem card_selectedParents (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    (selectedParents n f).card = (∑ i ∈ Finset.range n, 3 ^ i) + 1 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (card_goodParents_ge n f))).2

/-- The three children of one ternary parent. -/
def childEmbedding {n : ℕ} (p : Word 3 n) : Fin 3 ↪ Word 3 (n + 1) where
  toFun y := Fin.snoc p y
  inj' := by
    intro y z hyz
    have h := congrFun hyz (Fin.last n)
    simpa using h

noncomputable def children {n : ℕ} (p : Word 3 n) : Finset (Word 3 (n + 1)) :=
  Finset.univ.map (childEmbedding p)

@[simp] theorem card_children {n : ℕ} (p : Word 3 n) : (children p).card = 3 := by
  classical
  simp [children]

theorem mem_children_iff {n : ℕ} (p : Word 3 n) (w : Word 3 (n + 1)) :
    w ∈ children p ↔ Fin.init w = p := by
  classical
  constructor
  · intro hw
    simp only [children, Finset.mem_map, Finset.mem_univ, true_and] at hw
    obtain ⟨y, rfl⟩ := hw
    change Fin.init (Fin.snoc (α := fun _ : Fin (n + 1) ↦ Fin 3) p y) = p
    funext i
    exact @Fin.snoc_castSucc n (fun _ ↦ Fin 3) y p i
  · intro hw
    let y := w (Fin.last n)
    have hsnoc : Fin.snoc p y = w := by
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [y]
      · simpa [Fin.init] using (congrFun hw j).symm
    simp only [children, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨y, hsnoc⟩

/-- The forbidden prefix at terminal depth, cast to the leaf-word type. -/
def terminalForbidden (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    Word 3 (n + 1) :=
  fun i ↦ f (Fin.last (n + 1)) ⟨i, by simpa using i.isLt⟩

/-- Children still available after removing the terminal forbidden word. -/
noncomputable def availableChildren (n : ℕ) (f : ForbiddenPrefixes (n + 1))
    (p : Word 3 n) : Finset (Word 3 (n + 1)) :=
  (children p).erase (terminalForbidden n f)

theorem two_le_card_availableChildren (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (p : Word 3 n) :
    2 ≤ (availableChildren n f p).card := by
  classical
  by_cases ht : terminalForbidden n f ∈ children p
  · rw [availableChildren, Finset.card_erase_of_mem ht, card_children]
  · rw [availableChildren, Finset.erase_eq_of_notMem ht, card_children]
    norm_num

/-- Retain two available children below every selected parent. -/
noncomputable def chosenChildren (n : ℕ) (f : ForbiddenPrefixes (n + 1))
    (p : Word 3 n) : Finset (Word 3 (n + 1)) :=
  Classical.choose
    (Finset.exists_subset_card_eq (two_le_card_availableChildren n f p))

theorem chosenChildren_subset_available (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (p : Word 3 n) :
    chosenChildren n f p ⊆ availableChildren n f p :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (two_le_card_availableChildren n f p))).1

@[simp] theorem card_chosenChildren (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (p : Word 3 n) :
    (chosenChildren n f p).card = 2 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (two_le_card_availableChildren n f p))).2

/-- The bottom-packed selected leaf set. -/
noncomputable def bottomPackedLeaves (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    Finset (Word 3 (n + 1)) :=
  (selectedParents n f).biUnion (chosenChildren n f)

theorem chosenChildren_subset_children (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (p : Word 3 n) :
    chosenChildren n f p ⊆ children p := by
  exact (chosenChildren_subset_available n f p).trans (Finset.erase_subset _ _)

theorem chosenChildren_not_terminal (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (p : Word 3 n) :
    terminalForbidden n f ∉ chosenChildren n f p := by
  intro h
  have := chosenChildren_subset_available n f p h
  simpa [availableChildren] using this

@[simp] theorem mem_bottomPackedLeaves (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (w : Word 3 (n + 1)) :
    w ∈ bottomPackedLeaves n f ↔ ∃ p ∈ selectedParents n f,
      w ∈ chosenChildren n f p := by
  classical
  simp [bottomPackedLeaves]

theorem chosenChildren_pairwiseDisjoint (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) :
    (↑(selectedParents n f) : Set (Word 3 n)).PairwiseDisjoint
      (chosenChildren n f) := by
  intro p hp q hq hpq
  change Disjoint (chosenChildren n f p) (chosenChildren n f q)
  rw [Finset.disjoint_left]
  intro w hwp hwq
  have hpc := chosenChildren_subset_children n f p hwp
  have hqc := chosenChildren_subset_children n f q hwq
  have hip : Fin.init w = p := (mem_children_iff p w).mp hpc
  have hiq : Fin.init w = q := (mem_children_iff q w).mp hqc
  exact hpq (hip.symm.trans hiq)

theorem card_bottomPackedLeaves (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    (bottomPackedLeaves n f).card = 3 ^ n + 1 := by
  classical
  unfold bottomPackedLeaves
  rw [Finset.card_biUnion (chosenChildren_pairwiseDisjoint n f)]
  simp only [card_chosenChildren, Finset.sum_const_nat]
  rw [card_selectedParents]
  have hgeom := geom_sum_mul_add (2 : ℕ) n
  norm_num at hgeom ⊢
  omega

/-- Taking the parent preserves every prefix that ends before the last digit. -/
theorem init_hasPrefix {q n d : ℕ} (w : Word q (n + 1))
    (u : Prefix q d) (hdn : d ≤ n)
    (hw : HasPrefix w u (hdn.trans (Nat.le_succ n))) :
    HasPrefix (Fin.init w) u hdn := by
  intro i
  change w ⟨i, by omega⟩ = u i
  simpa only using hw i

/-- A full-depth prefix condition determines the entire word. -/
theorem hasPrefix_full_eq {q a : ℕ} (w u : Word q a)
    (h : HasPrefix w u (le_refl a)) : w = u := by
  funext i
  simpa only using h i

/-- A terminal forbidden prefix is exactly `terminalForbidden`. -/
theorem hasPrefix_terminal_eq (n : ℕ) (f : ForbiddenPrefixes (n + 1))
    (w : Word 3 (n + 1))
    (h : HasPrefix w (f (Fin.last (n + 1))) (by simp)) :
    w = terminalForbidden n f := by
  funext i
  unfold terminalForbidden
  simpa only using h ⟨i, by simpa using i.isLt⟩

/-- Every selected leaf avoids every positive-depth forbidden prefix. -/
theorem bottomPackedLeaves_avoid (n : ℕ) (f : ForbiddenPrefixes (n + 1))
    (w : Word 3 (n + 1)) (hw : w ∈ bottomPackedLeaves n f)
    (d : Fin (n + 2)) (hd : 0 < (d : ℕ)) :
    ¬HasPrefix w (f d) (indexedDepthLe d) := by
  classical
  intro hprefix
  obtain ⟨p, hpSel, hwp⟩ := (mem_bottomPackedLeaves n f w).mp hw
  have hpChild := chosenChildren_subset_children n f p hwp
  have hinit : Fin.init w = p := (mem_children_iff p w).mp hpChild
  by_cases hdlast : (d : ℕ) = n + 1
  · have deq : d = Fin.last (n + 1) := Fin.ext (by simpa using hdlast)
    subst d
    have hwterm : w = terminalForbidden n f :=
      hasPrefix_terminal_eq n f w hprefix
    exact chosenChildren_not_terminal n f p (hwterm ▸ hwp)
  · have hdle : (d : ℕ) ≤ n := by omega
    let e : Fin n := ⟨(d : ℕ) - 1, by omega⟩
    have heq : e.succ.castSucc = d := by
      apply Fin.ext
      dsimp [e]
      omega
    have hprefix' : HasPrefix w (f e.succ.castSucc)
        (indexedDepthLe e.succ.castSucc) :=
      forbiddenPrefix_congr f w heq hprefix
    have hpPrefix : HasPrefix p (f e.succ.castSucc)
        (Nat.succ_le_of_lt e.isLt) := by
      rw [← hinit]
      exact init_hasPrefix w (f e.succ.castSucc)
        (Nat.succ_le_of_lt e.isLt) hprefix'
    have hpBad : p ∈ badParents n f :=
      (mem_badParents_iff n f p).2 ⟨e, hpPrefix⟩
    have hpGood := selectedParents_subset_good n f hpSel
    have hpNotBad : p ∉ badParents n f := by
      simpa [goodParents] using hpGood
    exact hpNotBad hpBad

/-- A nonterminal prefix contains at most two selected leaves for each of its
depth-`n` descendants. -/
theorem bottomPackedLeaves_prefix_cap {n d : ℕ}
    (f : ForbiddenPrefixes (n + 1)) (u : Prefix 3 d) (hdn : d ≤ n) :
    ((bottomPackedLeaves n f) ∩
      prefixWords (a := n + 1) u (hdn.trans (Nat.le_succ n))).card ≤
        2 * 3 ^ (n - d) := by
  classical
  let P : Finset (Word 3 n) :=
    selectedParents n f ∩ prefixWords (a := n) u hdn
  have hsub :
      (bottomPackedLeaves n f) ∩
          prefixWords (a := n + 1) u (hdn.trans (Nat.le_succ n)) ⊆
        P.biUnion (chosenChildren n f) := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwSel, hwPrefix⟩
    obtain ⟨p, hpSel, hwp⟩ := (mem_bottomPackedLeaves n f w).mp hwSel
    have hpChild := chosenChildren_subset_children n f p hwp
    have hinit : Fin.init w = p := (mem_children_iff p w).mp hpChild
    have hwHas : HasPrefix w u (hdn.trans (Nat.le_succ n)) :=
      (mem_prefixWords u _ w).mp hwPrefix
    have hpHas : HasPrefix p u hdn := by
      rw [← hinit]
      exact init_hasPrefix w u hdn hwHas
    apply Finset.mem_biUnion.mpr
    exact ⟨p, Finset.mem_inter.mpr ⟨hpSel, (mem_prefixWords u hdn p).2 hpHas⟩, hwp⟩
  calc
    ((bottomPackedLeaves n f) ∩
      prefixWords (a := n + 1) u (hdn.trans (Nat.le_succ n))).card
        ≤ (P.biUnion (chosenChildren n f)).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (chosenChildren n f p).card := Finset.card_biUnion_le
    _ = 2 * P.card := by simp [mul_comm]
    _ ≤ 2 * (prefixWords (a := n) u hdn).card := by
      apply Nat.mul_le_mul_left
      exact Finset.card_le_card Finset.inter_subset_right
    _ = 2 * 3 ^ (n - d) := by rw [card_prefixWords]

/-- A full-depth prefix is a singleton, so its selected mass is at most one. -/
theorem bottomPackedLeaves_terminal_cap (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (u : Prefix 3 (n + 1)) :
    ((bottomPackedLeaves n f) ∩
      prefixWords (a := n + 1) u (le_refl _)).card ≤ 1 := by
  calc
    ((bottomPackedLeaves n f) ∩
      prefixWords (a := n + 1) u (le_refl _)).card
        ≤ (prefixWords (a := n + 1) u (le_refl _)).card :=
          Finset.card_le_card Finset.inter_subset_right
    _ = 1 := by simp [card_prefixWords]

/-- The finite sample space carried by the selected leaves. -/
abbrev BottomPackedSample (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :=
  ↥(bottomPackedLeaves n f)

noncomputable instance bottomPackedSampleNonempty (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) : Nonempty (BottomPackedSample n f) := by
  rw [Finset.nonempty_coe_sort]
  apply Finset.card_pos.mp
  rw [card_bottomPackedLeaves]
  positivity

/-- Uniform probability on the bottom-packed leaf set. -/
noncomputable def bottomPackedLaw (n : ℕ) (f : ForbiddenPrefixes (n + 1)) :
    FiniteLaw (BottomPackedSample n f) :=
  FiniteLaw.uniform _

/-- Cardinality of a predicate on a finite-set subtype is an intersection
cardinality. -/
theorem card_subtype_mem_inter {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) :
    Fintype.card {x : ↥S // (x : α) ∈ T} = (S ∩ T).card := by
  classical
  let e : {x : ↥S // (x : α) ∈ T} ≃ ↥(S ∩ T) :=
    { toFun := fun x ↦ ⟨x.1.1, Finset.mem_inter.mpr ⟨x.1.2, x.2⟩⟩
      invFun := fun x ↦ ⟨⟨x.1, (Finset.mem_inter.mp x.2).1⟩,
        (Finset.mem_inter.mp x.2).2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e]
  exact Fintype.card_coe _

/-- Exact nonterminal prefix-mass cap under the selected uniform law. -/
theorem bottomPackedLaw_prefix_prob_le {n d : ℕ}
    (f : ForbiddenPrefixes (n + 1)) (u : Prefix 3 d) (hdn : d ≤ n) :
    (bottomPackedLaw n f).prob
        (fun x ↦ HasPrefix x.1 u (hdn.trans (Nat.le_succ n))) ≤
      (2 * 3 ^ (n - d) : ℚ) / (3 ^ n + 1) := by
  classical
  unfold bottomPackedLaw
  rw [FiniteLaw.uniform_prob_eq_card]
  rw [show Fintype.card
      {x : BottomPackedSample n f //
        HasPrefix x.1 u (hdn.trans (Nat.le_succ n))} =
      ((bottomPackedLeaves n f) ∩
        prefixWords (a := n + 1) u
          (hdn.trans (Nat.le_succ n))).card by
    simpa only [mem_prefixWords] using
      card_subtype_mem_inter (bottomPackedLeaves n f)
        (prefixWords (a := n + 1) u
          (hdn.trans (Nat.le_succ n)))]
  rw [show Fintype.card (BottomPackedSample n f) =
      (bottomPackedLeaves n f).card by simp]
  rw [card_bottomPackedLeaves]
  push_cast
  have hcap := bottomPackedLeaves_prefix_cap f u hdn
  apply (div_le_div_iff_of_pos_right
    (show (0 : ℚ) < 3 ^ n + 1 by positivity)).2
  exact_mod_cast hcap

/-- Exact terminal prefix-mass cap. -/
theorem bottomPackedLaw_terminal_prob_le (n : ℕ)
    (f : ForbiddenPrefixes (n + 1)) (u : Prefix 3 (n + 1)) :
    (bottomPackedLaw n f).prob
        (fun x ↦ HasPrefix x.1 u (le_refl _)) ≤
      (1 : ℚ) / (3 ^ n + 1) := by
  classical
  unfold bottomPackedLaw
  rw [FiniteLaw.uniform_prob_eq_card]
  rw [show Fintype.card
      {x : BottomPackedSample n f // HasPrefix x.1 u (le_refl _)} =
      ((bottomPackedLeaves n f) ∩
        prefixWords (a := n + 1) u (le_refl _)).card by
    simpa only [mem_prefixWords] using
      card_subtype_mem_inter (bottomPackedLeaves n f)
        (prefixWords (a := n + 1) u (le_refl _))]
  rw [show Fintype.card (BottomPackedSample n f) =
      (bottomPackedLeaves n f).card by simp]
  rw [card_bottomPackedLeaves]
  push_cast
  have hcap := bottomPackedLeaves_terminal_cap n f u
  apply (div_le_div_iff_of_pos_right
    (show (0 : ℚ) < 3 ^ n + 1 by positivity)).2
  exact_mod_cast hcap

end TernarySelection

section RegularAvoidance

/-- One forbidden prefix per depth over an arbitrary alphabet. -/
abbrev ForbiddenPrefixesOf (p a : ℕ) :=
  (d : Fin (a + 1)) → Prefix p (d : ℕ)

/-- At coordinate `i`, globally omit the last symbol of the forbidden prefix
at depth `i+1`. -/
def omittedSymbol {q a : ℕ} (f : ForbiddenPrefixesOf (q + 1) a)
    (i : Fin a) : Fin (q + 1) :=
  f i.succ (Fin.last (i : ℕ))

/-- A full `q`-ary product subtree inside a `(q+1)`-ary tree. -/
def regularAvoidMap {q a : ℕ} (f : ForbiddenPrefixesOf (q + 1) a)
    (w : Word q a) : Word (q + 1) a :=
  fun i ↦ (omittedSymbol f i).succAbove (w i)

theorem regularAvoidMap_injective {q a : ℕ}
    (f : ForbiddenPrefixesOf (q + 1) a) :
    Function.Injective (regularAvoidMap f) := by
  intro u v huv
  funext i
  exact Fin.succAbove_right_injective (congrFun huv i)

theorem forbiddenPrefixOf_congr {p a : ℕ} (f : ForbiddenPrefixesOf p a)
    (w : Word p a) {i j : Fin (a + 1)} (hij : i = j)
    (h : HasPrefix w (f j) (indexedDepthLe j)) :
    HasPrefix w (f i) (indexedDepthLe i) := by
  subst j
  exact h

/-- The coordinatewise omitted-symbol subtree avoids every positive-depth
forbidden prefix.  This is a stronger and simpler realization of the complete
avoidance-subtree lemma. -/
theorem regularAvoidMap_avoids {q a : ℕ}
    (f : ForbiddenPrefixesOf (q + 1) a) (w : Word q a)
    (d : Fin (a + 1)) (hd : 0 < (d : ℕ)) :
    ¬HasPrefix (regularAvoidMap f w) (f d) (indexedDepthLe d) := by
  intro hprefix
  let i : Fin a := ⟨(d : ℕ) - 1, by omega⟩
  have heq : i.succ = d := by
    apply Fin.ext
    dsimp [i]
    omega
  have hprefix' : HasPrefix (regularAvoidMap f w) (f i.succ)
      (indexedDepthLe i.succ) :=
    forbiddenPrefixOf_congr f (regularAvoidMap f w) heq hprefix
  have hlast := hprefix' (Fin.last (i : ℕ))
  have hcoord :
      regularAvoidMap f w ⟨i, by omega⟩ = omittedSymbol f i := by
    simpa [omittedSymbol] using hlast
  exact Fin.succAbove_ne (omittedSymbol f i) (w ⟨i, by omega⟩) hcoord

end RegularAvoidance

end Erdos7
