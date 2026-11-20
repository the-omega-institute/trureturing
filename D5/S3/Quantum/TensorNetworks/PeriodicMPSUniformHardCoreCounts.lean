/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Cyclic insertion and hop counts give the weighted row balance, and deletions reach the empty set. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

/-! Cyclic insertion, directed hopping and deletion for the hard-core witness
of Section 6.1. Counts use actual insertions and replacements of occupied sites. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts

open scoped BigOperators

variable {n : ℕ}

abbrev Independent (S : Finset (Fin n)) : Prop :=
  (SimpleGraph.cycleGraph n).IsIndepSet (S : Set (Fin n))

/-- Independent configurations on the full cycle. -/
abbrev Configuration (n : ℕ) := {S : Finset (Fin n) // Independent S}

/-- Empty sites at which a particle can be inserted. -/
def insertionSites (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∉ S ∧ Independent (insert i S)

/-- An occupied source can move to an empty adjacent destination if the new set is independent. -/
def LegalHop (S : Finset (Fin n)) (src dst : Fin n) : Prop :=
  (SimpleGraph.cycleGraph n).Adj src dst ∧
    src ∈ S ∧ dst ∉ S ∧ Independent (insert dst (S.erase src))

instance (S : Finset (Fin n)) (src dst : Fin n) : Decidable (LegalHop S src dst) := by
  unfold LegalHop
  infer_instance

/-- All legal hops as ordered pairs of source and destination. -/
def directedHops (S : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => LegalHop S p.1 p.2

/-- A window starting at `i` indexes a forward hop from `i` into its middle site. -/
def forwardHops (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => LegalHop S i (finRotate n i)

/-- A window starting at `i` indexes a backward hop from its last site into its middle site. -/
def backwardHops (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => LegalHop S (finRotate n (finRotate n i)) (finRotate n i)

/-- The number of legal directed nearest-neighbor hops. -/
def hopCount (S : Finset (Fin n)) : ℕ :=
  (forwardHops S).card + (backwardHops S).card

/-- Start sites of occupied forward distance-two pairs, including across the seam. -/
def distanceTwoStarts (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ∈ S ∧ finRotate n (finRotate n i) ∈ S

theorem cycle_adj_iff (hn : 7 ≤ n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔ i = finRotate n j ∨ j = finRotate n i := by
  let : NeZero n := ⟨by omega⟩
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [SimpleGraph.cycleGraph_adj', ← hone]
  simp only [← Fin.ext_iff, finRotate_apply, sub_eq_iff_eq_add']

private theorem rotate_twice_ne (hn : 7 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let : NeZero n := ⟨by omega⟩
  intro heq
  have hshift : (i + 1) + 1 = i := by simpa only [finRotate_apply] using heq
  have hcancel : i + ((1 : Fin n) + 1) = i + 0 := by
    rw [← add_assoc, hshift, add_zero]
  have hzero : (1 : Fin n) + 1 = 0 := add_left_cancel hcancel
  have hval := congrArg Fin.val hzero
  simp only [Fin.val_add, Fin.val_one', Fin.val_zero,
    Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : 1 + 1 < n)] at hval
  omega

private def forwardPair (n : ℕ) : Fin n ↪ Fin n × Fin n :=
  ⟨fun i => (i, finRotate n i), fun _ _ h => congrArg Prod.fst h⟩

private def backwardPair (n : ℕ) : Fin n ↪ Fin n × Fin n :=
  ⟨fun i => (finRotate n (finRotate n i), finRotate n i),
    fun _ _ h => (finRotate n).injective (congrArg Prod.snd h)⟩

/-- The two orientations enumerate the actual ordered moves without multiplicities. -/
theorem hopCount_eq_card_directedHops (hn : 7 ≤ n) (S : Finset (Fin n)) :
    hopCount S = (directedHops S).card := by
  let fw := (forwardHops S).map (forwardPair n)
  let bw := (backwardHops S).map (backwardPair n)
  have hd : Disjoint fw bw := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hq
    have he : ((i, finRotate n i) : Fin n × Fin n) =
        (finRotate n (finRotate n j), finRotate n j) := hi.trans hj.symm
    have hij : i = j := (finRotate n).injective (congrArg Prod.snd he)
    subst j
    exact rotate_twice_ne hn i (congrArg Prod.fst he).symm
  have hUnion : fw ∪ bw = directedHops S := by
    ext p
    simp only [Finset.mem_union, directedHops, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (hp | hp)
      · obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hp
        have h : LegalHop S (forwardPair n i).1 (forwardPair n i).2 := by
          change LegalHop S i (finRotate n i)
          simpa only [forwardHops, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        exact he ▸ h
      · obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hp
        have h : LegalHop S (backwardPair n i).1 (backwardPair n i).2 := by
          change LegalHop S (finRotate n (finRotate n i)) (finRotate n i)
          simpa only [backwardHops, Finset.mem_filter, Finset.mem_univ, true_and] using hi
        exact he ▸ h
    · intro h
      rcases (cycle_adj_iff hn p.1 p.2).mp h.1 with hb | hf
      · let i := (finRotate n).symm p.2
        have hi : finRotate n i = p.2 := (finRotate n).apply_symm_apply p.2
        have he : backwardPair n i = p := by
          apply Prod.ext
          · change finRotate n (finRotate n i) = p.1
            rw [hi, hb]
          · exact hi
        have hm : LegalHop S (backwardPair n i).1 (backwardPair n i).2 := he.symm ▸ h
        change LegalHop S (finRotate n (finRotate n i)) (finRotate n i) at hm
        have hmem : i ∈ backwardHops S := by
          simpa only [backwardHops, Finset.mem_filter, Finset.mem_univ, true_and] using hm
        exact Or.inr (Finset.mem_map.mpr ⟨i, hmem, he⟩)
      · have he : forwardPair n p.1 = p := Prod.ext rfl hf.symm
        have hm : LegalHop S (forwardPair n p.1).1 (forwardPair n p.1).2 := he.symm ▸ h
        change LegalHop S p.1 (finRotate n p.1) at hm
        have hmem : p.1 ∈ forwardHops S := by
          simpa only [forwardHops, Finset.mem_filter, Finset.mem_univ, true_and] using hm
        exact Or.inl (Finset.mem_map.mpr ⟨p.1, hmem, he⟩)
  rw [← hUnion, Finset.card_union_of_disjoint hd]
  simp only [fw, bw, Finset.card_map, hopCount]

/-- The graph predicate is equivalent to the hard-core constraint on consecutive sites. -/
theorem independent_iff_no_adjacent (hn : 7 ≤ n) (S : Finset (Fin n)) :
    Independent S ↔ ∀ i : Fin n, i ∈ S → finRotate n i ∉ S := by
  constructor
  · intro hS i hi hj
    have hAdj := (cycle_adj_iff hn i (finRotate n i)).mpr (Or.inr rfl)
    exact hS hi hj hAdj.ne hAdj
  · intro h i hi j hj _ hAdj
    rcases (cycle_adj_iff hn i j).mp hAdj with hij | hji
    · exact h j hj (hij ▸ hi)
    · exact h i hi (hji ▸ hj)

/-- The occupied sites of a binary word are independent exactly when its adjacent bits avoid 11. -/
theorem occupied_independent_iff (hn : 7 ≤ n) (w : Fin n → Fin 2) :
    Independent (Finset.univ.filter fun i => w i = 1) ↔
      ∀ i, w i = 1 → w (finRotate n i) ≠ 1 := by
  simp only [independent_iff_no_adjacent hn, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Erasing a vertex preserves independence. -/
theorem independent_erase {S : Finset (Fin n)} (hS : Independent S) (i : Fin n) :
    Independent (S.erase i) := by
  intro u hu v hv hne
  exact hS (Finset.mem_of_mem_erase hu) (Finset.mem_of_mem_erase hv) hne

private theorem independent_insert_iff {S : Finset (Fin n)} (hS : Independent S)
    (v : Fin n) :
    Independent (insert v S) ↔ ∀ w ∈ S, ¬ (SimpleGraph.cycleGraph n).Adj v w := by
  constructor
  · intro h w hw hadj
    exact h (Finset.mem_insert_self v S) (Finset.mem_insert_of_mem hw) hadj.ne hadj
  · intro h x hx y hy hne hadj
    change x ∈ insert v S at hx
    change y ∈ insert v S at hy
    rcases Finset.mem_insert.mp hx with hxv | hxS
    · subst x
      rcases Finset.mem_insert.mp hy with hyv | hyS
      · exact hne hyv.symm
      · exact h y hyS hadj
    · rcases Finset.mem_insert.mp hy with hyv | hyS
      · subst y
        exact h x hxS ((SimpleGraph.cycleGraph n).adj_symm hadj)
      · exact hS hxS hyS hne hadj

private theorem independent_insert_middle_iff (hn : 7 ≤ n) {S : Finset (Fin n)}
    (hS : Independent S) (i : Fin n) :
    Independent (insert (finRotate n i) S) ↔ i ∉ S ∧ finRotate n (finRotate n i) ∉ S := by
  rw [independent_insert_iff hS]
  constructor
  · intro h
    exact ⟨fun hi => h i hi ((cycle_adj_iff hn _ _).mpr (Or.inl rfl)),
      fun hj => h _ hj ((cycle_adj_iff hn _ _).mpr (Or.inr rfl))⟩
  · rintro ⟨hi, hj⟩ w hw hadj
    rcases (cycle_adj_iff hn (finRotate n i) w).mp hadj with heq | heq
    · have hiw : i = w := (finRotate n).injective heq
      exact hi (hiw.symm ▸ hw)
    · exact hj (heq ▸ hw)

theorem mem_insertionSites_iff (hn : 7 ≤ n) {S : Finset (Fin n)}
    (hS : Independent S) (i : Fin n) :
    finRotate n i ∈ insertionSites S ↔
      finRotate n i ∉ S ∧ i ∉ S ∧ finRotate n (finRotate n i) ∉ S := by
  simp only [insertionSites, Finset.mem_filter, Finset.mem_univ, true_and,
    independent_insert_middle_iff hn hS i]

theorem mem_forwardHops_iff (hn : 7 ≤ n) {S : Finset (Fin n)}
    (hS : Independent S) (i : Fin n) :
    i ∈ forwardHops S ↔ i ∈ S ∧ finRotate n (finRotate n i) ∉ S := by
  have hAdj := (cycle_adj_iff hn i (finRotate n i)).mpr (Or.inr rfl)
  have hEmpty := (independent_iff_no_adjacent hn S).mp hS i
  have hOther : finRotate n (finRotate n i) ∈ S.erase i ↔ finRotate n (finRotate n i) ∈ S := by
    rw [Finset.mem_erase, and_iff_right (rotate_twice_ne hn i)]
  rw [forwardHops, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simp only [LegalHop, hAdj, true_and,
    independent_insert_middle_iff hn (independent_erase hS i) i, Finset.notMem_erase,
    hOther]
  tauto

theorem mem_backwardHops_iff (hn : 7 ≤ n) {S : Finset (Fin n)}
    (hS : Independent S) (i : Fin n) :
    i ∈ backwardHops S ↔ finRotate n (finRotate n i) ∈ S ∧ i ∉ S := by
  have hAdj :=
    (cycle_adj_iff hn (finRotate n (finRotate n i)) (finRotate n i)).mpr (Or.inl rfl)
  have hEmpty (h : finRotate n (finRotate n i) ∈ S) : finRotate n i ∉ S :=
    fun hmid => (independent_iff_no_adjacent hn S).mp hS (finRotate n i) hmid h
  have hne : i ≠ finRotate n (finRotate n i) := (rotate_twice_ne hn i).symm
  have hOther : i ∈ S.erase (finRotate n (finRotate n i)) ↔ i ∈ S := by
    rw [Finset.mem_erase, and_iff_right hne]
  rw [backwardHops, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simp only [LegalHop, hAdj, true_and,
    independent_insert_middle_iff hn (independent_erase hS (finRotate n (finRotate n i))) i,
    Finset.notMem_erase, hOther]
  tauto

private theorem sum_mem (S : Finset (Fin n)) :
    (∑ i : Fin n, if i ∈ S then (1 : ℕ) else 0) = S.card :=
  (Finset.card_eq_sum_ite (Finset.subset_univ S)).symm

private theorem sum_mem_rotate (S : Finset (Fin n)) :
    (∑ i : Fin n, if finRotate n i ∈ S then (1 : ℕ) else 0) = S.card :=
  (Equiv.sum_comp (finRotate n) (fun i => if i ∈ S then (1 : ℕ) else 0)).trans (sum_mem S)

private theorem sum_mem_rotate_twice (S : Finset (Fin n)) :
    (∑ i : Fin n, if finRotate n (finRotate n i) ∈ S then (1 : ℕ) else 0) = S.card :=
  (Equiv.sum_comp (finRotate n) (fun i => if finRotate n i ∈ S then (1 : ℕ) else 0)).trans
    (sum_mem_rotate S)

/-- Insertion count in subtraction-free form. -/
theorem insertion_count_balance (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    (insertionSites S).card + 3 * S.card = n + (distanceTwoStarts S).card := by
  have noAdjacent := (independent_iff_no_adjacent hn S).mp hS
  have window (i : Fin n) :
      (if finRotate n i ∈ insertionSites S then (1 : ℕ) else 0) +
        (if i ∈ S then 1 else 0) + (if finRotate n i ∈ S then 1 else 0) +
        (if finRotate n (finRotate n i) ∈ S then 1 else 0) =
      1 + (if i ∈ distanceTwoStarts S then 1 else 0) := by
    have hleft := noAdjacent i
    have hright := noAdjacent (finRotate n i)
    simp only [mem_insertionSites_iff hn hS i, distanceTwoStarts, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hl : i ∈ S <;> by_cases hm : finRotate n i ∈ S <;>
      by_cases hr : finRotate n (finRotate n i) ∈ S <;> simp_all [-finRotate_apply]
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => window i)
  have hOne : (∑ _i : Fin n, (1 : ℕ)) = n := by
    rw [← Finset.card_eq_sum_ones, Finset.card_fin]
  simp only [Finset.sum_add_distrib, sum_mem_rotate, sum_mem_rotate_twice, sum_mem, hOne] at hsum
  omega

/-- Directed hopping count in subtraction-free form. -/
theorem hopping_count_balance (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    hopCount S + 2 * (distanceTwoStarts S).card = 2 * S.card := by
  have window (i : Fin n) :
      (if i ∈ forwardHops S then (1 : ℕ) else 0) +
        (if i ∈ backwardHops S then 1 else 0) +
        2 * (if i ∈ distanceTwoStarts S then 1 else 0) =
      (if i ∈ S then 1 else 0) + (if finRotate n (finRotate n i) ∈ S then 1 else 0) := by
    simp only [mem_forwardHops_iff hn hS i, mem_backwardHops_iff hn hS i,
      distanceTwoStarts, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hl : i ∈ S <;> by_cases hr : finRotate n (finRotate n i) ∈ S <;>
      simp [-finRotate_apply, hl, hr]
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => window i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_mem_rotate_twice, sum_mem] at hsum
  unfold hopCount
  omega

/-- The insertion formula in integers, including when `3 * S.card > n`. -/
theorem insertion_count (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    ((insertionSites S).card : ℤ) =
      (n : ℤ) - 3 * (S.card : ℤ) + ((distanceTwoStarts S).card : ℤ) := by
  have h := insertion_count_balance hn hS
  omega

/-- The number of legal directed hops is twice the number of unblocked occupied ends. -/
theorem hopping_count (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    hopCount S = 2 * S.card - 2 * (distanceTwoStarts S).card := by
  have h := hopping_count_balance hn hS
  omega

/-- The hopping formula on the finset of actual ordered moves. -/
theorem directed_hop_count (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    (directedHops S).card = 2 * S.card - 2 * (distanceTwoStarts S).card :=
  (hopCount_eq_card_directedHops hn S).symm.trans (hopping_count hn hS)

/-- The cancellation of the distance-two term in the compressed row. -/
theorem move_count_row_balance (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) :
    2 * (insertionSites S).card + hopCount S + 4 * S.card = 2 * n := by
  have ha := insertion_count_balance hn hS
  have hh := hopping_count_balance hn hS
  omega

/-- The normalized scalar row expression of Section 6.1. -/
theorem normalized_row_sum (hn : 7 ≤ n) {S : Finset (Fin n)} (hS : Independent S) (lam : ℝ) :
    (lam⁻¹ - 2 * lam) * (S.card : ℝ) - (S.card : ℝ) / lam -
      lam * ((insertionSites S).card : ℝ) - (lam / 2) * (hopCount S : ℝ) =
      -(n : ℝ) * lam := by
  have h : 2 * ((insertionSites S).card : ℝ) + (hopCount S : ℝ) + 4 * (S.card : ℝ) =
      2 * (n : ℝ) := by
    exact_mod_cast move_count_row_balance hn hS
  simp only [div_eq_mul_inv]
  linear_combination (-lam / 2) * h

/-- The empty independent configuration. -/
def emptyConfiguration (n : ℕ) : Configuration n :=
  ⟨∅, by
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)⟩

/-- A deletion step erases one occupied site inside the independent configurations. -/
def DeletionStep (S T : Configuration n) : Prop :=
  ∃ i ∈ S.val, T.val = S.val.erase i

/-- Every independent configuration reaches the empty one by legal deletions. -/
theorem deletion_reaches_empty (S : Configuration n) :
    Relation.ReflTransGen DeletionStep S (emptyConfiguration n) := by
  have chain (A : Finset (Fin n)) (hA : Independent A) :
      Relation.ReflTransGen DeletionStep (⟨A, hA⟩ : Configuration n) (emptyConfiguration n) := by
    revert hA
    refine Finset.eraseInduction (p := fun B => ∀ hB : Independent B,
      Relation.ReflTransGen DeletionStep (⟨B, hB⟩ : Configuration n) (emptyConfiguration n)) ?_ A
    intro B ih hB
    by_cases h : B = ∅
    · subst B
      exact Relation.ReflTransGen.refl
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
      refine Relation.ReflTransGen.head (b := ⟨B.erase i, independent_erase hB i⟩) ?_ ?_
      · exact ⟨i, hi, rfl⟩
      · exact ih i hi (independent_erase hB i)
  exact chain S.val S.property

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreCounts
