/- GID: D5/S3/Combinatorics/UnorderedTrees/OneFork
   generality: G
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/OneFork
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite rooted tree with size one above vertex-height has exactly one off-spine leaf. -/

/-
admission_basis: escape-witness
exists_fork_iso: proof_shape: content; escape_witness: one_off_spine.
The bounded parent iterates of a deepest vertex have distinct depths and a singleton complement. The omitted leaf attaches below the deepest depth.
Live consumers: ForkDecoration.model_surjective.
-/

import D5.S3.Combinatorics.UnorderedTrees.LeafPruning
import Mathlib.Data.Fintype.Sum

/-! Size one above vertex-height forces a single off-spine leaf. -/

namespace D5.S3.Combinatorics.UnorderedTrees.OneFork

open D5.S3.Combinatorics.UnorderedTrees.ParentTree
open D5.S3.Combinatorics.UnorderedTrees.LeafPruning

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem depth_iterate {V : Type u} (T : Tree V) (v : V) (k : ℕ) :
    depth T ((T.parent^[k]) v) = depth T v - k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      by_cases hr : (T.parent^[k]) v = T.root
      · rw [hr, T.fixed_root, depth_root]
        rw [hr, depth_root] at ih
        omega
      · have h := depth_parent T hr
        omega

/-- The original vertices on the parent path from `v` to the root, including both endpoints. -/
def spine {V : Type u} (T : Tree V) (v : V) : Finset V :=
  (Finset.range (depth T v + 1)).image (fun k => (T.parent^[k]) v)

private theorem mem_spine {V : Type u} (T : Tree V) (v : V) : v ∈ spine T v := by
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

private theorem root_mem_spine {V : Type u} (T : Tree V) (v : V) : T.root ∈ spine T v := by
  exact Finset.mem_image.mpr ⟨depth T v, by simp, reaches_depth T v⟩

private theorem parent_mem_spine {V : Type u} (T : Tree V) (v : V) {w : V}
    (hw : w ∈ spine T v) : T.parent w ∈ spine T v := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
  have hk' : k ≤ depth T v := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  by_cases hlt : k < depth T v
  · exact Finset.mem_image.mpr ⟨k + 1, by simpa using hlt,
      Function.iterate_succ_apply' T.parent k v⟩
  · have heq : k = depth T v := by omega
    rw [heq, reaches_depth, T.fixed_root]
    exact root_mem_spine T v

private theorem card_spine {V : Type u} (T : Tree V) (v : V) :
    (spine T v).card = depth T v + 1 := by
  unfold spine
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro i hi j hj heq
    have h := congrArg (depth T) heq
    rw [depth_iterate, depth_iterate] at h
    change i ∈ Finset.range (depth T v + 1) at hi
    change j ∈ Finset.range (depth T v + 1) at hj
    have hi' : i ≤ depth T v := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hj' : j ≤ depth T v := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    omega

/-- The complete one-off-path classification on actual original vertices. -/
theorem one_off_spine {V : Type u} [Fintype V] (T : Tree V)
    (hsize : Fintype.card V = height T + 1) :
    ∃ v w : V,
      (∀ x, depth T x ≤ depth T v) ∧
      w ∉ spine T v ∧
      (∀ x, x ∉ spine T v ↔ x = w) ∧
      ¬ Internal T w ∧
      T.parent w ∈ spine T v ∧ T.parent w ≠ v := by
  have hne : (Finset.univ : Finset V).Nonempty := ⟨T.root, Finset.mem_univ _⟩
  obtain ⟨v, _, hv⟩ := Finset.sup_mem_of_nonempty (f := depth T) hne
  have hmax (x : V) : depth T x ≤ depth T v := by
    rw [hv]
    exact Finset.le_sup (Finset.mem_univ x)
  have hoff : (Finset.univ \ spine T v).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_spine]
    unfold height at hsize
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hoff
  have off_iff (x : V) : x ∉ spine T v ↔ x = w := by
    have h := Finset.ext_iff.mp hw x
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] using h
  have hwout : w ∉ spine T v := (off_iff w).mpr rfl
  have hwroot : w ≠ T.root := by
    intro h
    apply hwout
    rw [h]
    exact root_mem_spine T v
  have hleaf : ¬ Internal T w := by
    rintro ⟨z, hz⟩
    have hzout : z ∉ spine T v := by
      intro hzin
      exact hwout (hz.2 ▸ parent_mem_spine T v hzin)
    have heq := (off_iff z).mp hzout
    subst z
    have hd := depth_parent T hz.1
    rw [hz.2] at hd
    omega
  have hparent : T.parent w ∈ spine T v := by
    by_contra h
    have heq := (off_iff _).mp h
    have hd := depth_parent T hwroot
    rw [heq] at hd
    omega
  have hparent_ne : T.parent w ≠ v := by
    intro heq
    have hd := depth_parent T hwroot
    rw [heq] at hd
    have hm := hmax w
    omega
  exact ⟨v, w, hmax, hwout, off_iff, hleaf, hparent, hparent_ne⟩

/-- The canonical fork uses successive spine nonterminals and two tips.
The Boolean tags `false` and `true` mark the short and long tips, respectively. -/
abbrev Fork (b c : ℕ) := Fin (b + c + 1) ⊕ Bool

def forkPoint (b c : ℕ) : Fin (b + c + 1) := ⟨b, by omega⟩

private def lastParent (b c : ℕ) : Fin (b + c + 1) := ⟨b + c, by omega⟩

private def forkParent (b c : ℕ) : Fork b c → Fork b c
  | .inl i => .inl ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩
  | .inr false => .inl (forkPoint b c)
  | .inr true => .inl (lastParent b c)

private def forkRank (b c : ℕ) : Fork b c → ℕ
  | .inl i => i.val
  | .inr false => b + 1
  | .inr true => b + c + 1

private theorem forkRank_parent (b c : ℕ) (x : Fork b c) (hx : x ≠ Sum.inl 0) :
    forkRank b c x = forkRank b c (forkParent b c x) + 1 := by
  cases x with
  | inl i =>
    have hi : i.val ≠ 0 := fun h => hx (congrArg Sum.inl (Fin.ext h))
    change i.val = i.val - 1 + 1
    omega
  | inr j => cases j <;> rfl

/-- The short tip attaches at depth `b` and the long tip at depth `b+c`. -/
def fork (b c : ℕ) : Tree (Fork b c) where
  parent := forkParent b c
  root := .inl 0
  fixed_root := rfl
  reaches x := by
    induction h : forkRank b c x using Nat.strong_induction_on generalizing x with
    | h r ih =>
      by_cases hx : x = Sum.inl 0
      · exact ⟨0, hx⟩
      · have hd := forkRank_parent b c x hx
        obtain ⟨k, hk⟩ := ih _ (by omega) (forkParent b c x) rfl
        exact ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩

private theorem depth_fork (b c : ℕ) (x : Fork b c) : depth (fork b c) x = forkRank b c x := by
  induction h : forkRank b c x using Nat.strong_induction_on generalizing x with
  | h r ih =>
    by_cases hx : x = (fork b c).root
    · rw [hx, depth_root]
      rw [hx] at h
      exact h
    · have hd := forkRank_parent b c x hx
      rw [depth_parent _ hx]
      change depth (fork b c) (forkParent b c x) + 1 = r
      rw [ih _ (by omega) _ rfl]
      omega

@[simp] private theorem depth_fork_spine (b c : ℕ) (i : Fin (b + c + 1)) :
    depth (fork b c) (.inl i) = i.val := depth_fork b c _

@[simp] private theorem depth_fork_short (b c : ℕ) :
    depth (fork b c) (.inr false) = b + 1 := depth_fork b c _

@[simp] private theorem depth_fork_long (b c : ℕ) :
    depth (fork b c) (.inr true) = b + c + 1 := depth_fork b c _

@[simp] theorem card_fork (b c : ℕ) : Fintype.card (Fork b c) = b + c + 3 := by
  simp [Fork]

@[simp] theorem height_fork (b c : ℕ) : height (fork b c) = b + c + 2 := by
  have hmax : Finset.univ.sup (depth (fork b c)) = b + c + 1 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro x _
      cases x with
      | inl i => simp
      | inr j => cases j <;> simp
    · simpa only [depth_fork_long] using
        Finset.le_sup (f := depth (fork b c)) (Finset.mem_univ (Sum.inr true))
  unfold height
  omega

private def atDepth {V : Type u} (T : Tree V) (v : V) (i : ℕ) : V :=
  (T.parent^[depth T v - i]) v

private theorem depth_atDepth {V : Type u} (T : Tree V) (v : V) {i : ℕ}
    (hi : i ≤ depth T v) : depth T (atDepth T v i) = i := by
  unfold atDepth
  rw [depth_iterate]
  omega

private theorem atDepth_mem {V : Type u} (T : Tree V) (v : V) (i : ℕ) :
    atDepth T v i ∈ spine T v :=
  Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (by omega), rfl⟩

private theorem parent_atDepth {V : Type u} (T : Tree V) (v : V) {i : ℕ}
    (hi : i ≤ depth T v) :
    T.parent (atDepth T v i) = atDepth T v (i - 1) := by
  by_cases hz : i = 0
  · subst i
    simpa [atDepth, reaches_depth] using T.fixed_root
  · unfold atDepth
    rw [show depth T v - (i - 1) = (depth T v - i) + 1 by omega,
      Function.iterate_succ_apply']

/-- The unique off-path vertex gives a canonical fork up to an actual vertex isomorphism. -/
theorem exists_fork_iso {V : Type u} [Fintype V] (T : Tree V)
    (hsize : Fintype.card V = height T + 1) : ∃ b c, Nonempty (Iso (fork b c) T) := by
  obtain ⟨v, w, _, hw, hoff, _, hp, hpne⟩ := one_off_spine T hsize
  obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hp
  have hkD : k ≤ depth T v := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hkpos : 0 < k := by
    by_contra! hz
    have hzero : k = 0 := by omega
    exact hpne (by simpa [hzero] using hkv.symm)
  let b := depth T v - k
  let c := k - 1
  have hD : b + c + 1 = depth T v := by dsimp [b, c]; omega
  have hb : atDepth T v b = T.parent w := by
    simpa only [atDepth, show depth T v - b = k by dsimp [b]; omega] using hkv
  have hlast : atDepth T v (b + c + 1) = v := by simp [atDepth, hD]
  let f : Fork b c → V := fun x =>
    match x with
    | .inl i => atDepth T v i.val
    | .inr false => w
    | .inr true => v
  have hdepth (i : Fin (b + c + 1)) : depth T (f (.inl i)) = i.val :=
    depth_atDepth T v (by have hi := i.isLt; omega)
  have hmem (i : Fin (b + c + 1)) : f (.inl i) ∈ spine T v := atDepth_mem T v i
  have hinj : Function.Injective f := by
    intro x y hxy
    rcases x with i | p <;> rcases y with j | q
    · exact congrArg Sum.inl (Fin.ext ((hdepth i).symm.trans
          ((congrArg (depth T) hxy).trans (hdepth j))))
    · cases q
      · change f (.inl i) = w at hxy
        exact (hw (hxy ▸ hmem i)).elim
      · have hi := i.isLt
        have hd := (hdepth i).symm.trans (congrArg (depth T) hxy)
        change i.val = depth T v at hd
        omega
    · cases p
      · change w = f (.inl j) at hxy
        exact (hw (hxy.symm ▸ hmem j)).elim
      · have hj := j.isLt
        have hd := (hdepth j).symm.trans (congrArg (depth T) hxy.symm)
        change j.val = depth T v at hd
        omega
    · cases p <;> cases q
      · rfl
      · change w = v at hxy
        exact (hw (hxy.symm ▸ mem_spine T v)).elim
      · change v = w at hxy
        exact (hw (hxy ▸ mem_spine T v)).elim
      · rfl
  have hsurj : Function.Surjective f := by
    intro x
    by_cases hx : x ∈ spine T v
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjD : j ≤ depth T v := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      by_cases hjz : j = 0
      · exact ⟨.inr true, by simp [f, hjz]⟩
      · refine ⟨.inl ⟨depth T v - j, by omega⟩, ?_⟩
        change atDepth T v (depth T v - j) = _
        simp [atDepth, Nat.sub_sub_self hjD]
    · exact ⟨.inr false, ((hoff x).mp hx).symm⟩
  refine ⟨b, c, ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩⟩⟩
  · change atDepth T v 0 = T.root
    simpa [atDepth] using reaches_depth T v
  · intro x
    change f (forkParent b c x) = T.parent (f x)
    rcases x with i | j
    · change atDepth T v (i.val - 1) = T.parent (atDepth T v i.val)
      exact (parent_atDepth T v (by have hi := i.isLt; omega)).symm
    · cases j
      · exact hb
      · change atDepth T v (b + c) = T.parent v
        have h := parent_atDepth T v (i := b + c + 1) (by omega)
        rw [hlast] at h
        simpa using h.symm

@[simp] theorem fork_internal_spine (b c : ℕ) (i : Fin (b + c + 1)) :
    Internal (fork b c) (.inl i) := by
  by_cases hi : i.val + 1 < b + c + 1
  · let j : Fin (b + c + 1) := ⟨i.val + 1, hi⟩
    refine ⟨.inl j, ?_, ?_⟩
    · intro h
      have hj := congrArg Fin.val (Sum.inl.inj h)
      change i.val + 1 = 0 at hj
      omega
    · exact congrArg Sum.inl (Fin.ext (Nat.add_sub_cancel _ _))
  · exact ⟨.inr true, by simp [fork], congrArg Sum.inl (Fin.ext (by
      change b + c = i.val
      have hil := i.isLt
      omega))⟩

@[simp] theorem fork_terminal (b c : ℕ) (p : Bool) : ¬ Internal (fork b c) (.inr p) := by
  rintro ⟨x, _, hx⟩
  rcases x with i | q
  · cases hx
  · cases q <;> cases hx

private theorem fork_child_spine_iff (b c : ℕ) (i j : Fin (b + c + 1)) :
    Child (fork b c) (.inl i) (.inl j) ↔ i.val = j.val + 1 := by
  change (Sum.inl i ≠ Sum.inl (0 : Fin (b + c + 1)) ∧
    Sum.inl (⟨i.val - 1, _⟩ : Fin (b + c + 1)) = Sum.inl j) ↔ _
  simp only [ne_eq, Sum.inl.injEq, ← Fin.val_eq_val]
  change (i.val ≠ 0 ∧ i.val - 1 = j.val) ↔ _
  omega

private theorem fork_child_short_iff (b c : ℕ) (i : Fin (b + c + 1)) :
    Child (fork b c) (.inr false) (.inl i) ↔ i.val = b := by
  change (Sum.inr false ≠ Sum.inl (0 : Fin (b + c + 1)) ∧
    Sum.inl (forkPoint b c) = Sum.inl i) ↔ _
  rw [Sum.inl.injEq, ← Fin.val_eq_val]
  simp [forkPoint, eq_comm]

private theorem fork_child_long_iff (b c : ℕ) (i : Fin (b + c + 1)) :
    Child (fork b c) (.inr true) (.inl i) ↔ i.val = b + c := by
  change (Sum.inr true ≠ Sum.inl (0 : Fin (b + c + 1)) ∧
    Sum.inl (lastParent b c) = Sum.inl i) ↔ _
  rw [Sum.inl.injEq, ← Fin.val_eq_val]
  simp [lastParent, eq_comm]

private theorem fork_split_iff (b c : ℕ) (x : Fork b c) :
    (∃ y z, y ≠ z ∧ Child (fork b c) y x ∧ Child (fork b c) z x) ↔
      x = Sum.inl (forkPoint b c) := by
  constructor
  · rintro ⟨y, z, hyz, hy, hz⟩
    rcases x with i | p
    · suffices i.val = b from congrArg Sum.inl (Fin.ext this)
      rcases y with j | q <;> rcases z with k | r
      · rw [fork_child_spine_iff] at hy hz
        exact (hyz (congrArg Sum.inl (Fin.ext (hy.trans hz.symm)))).elim
      · cases r
        · exact (fork_child_short_iff ..).mp hz
        · rw [fork_child_spine_iff] at hy
          have hh := (fork_child_long_iff ..).mp hz
          have hj := j.isLt
          omega
      · cases q
        · exact (fork_child_short_iff ..).mp hy
        · rw [fork_child_spine_iff] at hz
          have hh := (fork_child_long_iff ..).mp hy
          have hk := k.isLt
          omega
      · cases q <;> cases r
        · exact (hyz rfl).elim
        · exact (fork_child_short_iff ..).mp hy
        · exact (fork_child_short_iff ..).mp hz
        · exact (hyz rfl).elim
    · exact (fork_terminal b c p ⟨y, hy⟩).elim
  · rintro rfl
    refine ⟨.inr false, ?_⟩
    by_cases hc : c = 0
    · subst c
      exact ⟨.inr true, by simp,
        (fork_child_short_iff ..).mpr rfl, (fork_child_long_iff ..).mpr rfl⟩
    · exact ⟨.inl ⟨b + 1, by omega⟩, by simp,
        (fork_child_short_iff ..).mpr rfl, (fork_child_spine_iff ..).mpr rfl⟩

/-- The fork depth and the maximum depth determine both parameters. -/
theorem fork_iso_parameters {b c b' c' : ℕ} (e : Iso (fork b c) (fork b' c')) :
    b = b' ∧ c = c' := by
  obtain ⟨y, z, hyz, hy, hz⟩ := (fork_split_iff b c _).mpr rfl
  have hf := (fork_split_iff b' c' _).mp
    ⟨e.equiv y, e.equiv z, e.equiv.injective.ne hyz, (iso_child e _ _).mp hy,
      (iso_child e _ _).mp hz⟩
  have hd := iso_depth e (Sum.inl (forkPoint b c))
  rw [hf, depth_fork_spine, depth_fork_spine] at hd
  change b' = b at hd
  have hh := iso_height e
  simp only [height_fork] at hh
  exact ⟨hd.symm, by omega⟩

/-- Every automorphism fixes each indexed spine nonterminal. -/
theorem fork_iso_spine {b c : ℕ} (e : Iso (fork b c) (fork b c))
    (i : Fin (b + c + 1)) : e.equiv (.inl i) = .inl i := by
  have hd := iso_depth e (Sum.inl i)
  have hi := (iso_internal e _).mp (fork_internal_spine b c i)
  cases h : e.equiv (.inl i) with
  | inl j =>
    rw [h, depth_fork_spine, depth_fork_spine] at hd
    exact congrArg Sum.inl (Fin.ext hd)
  | inr p => exact (fork_terminal b c p (h ▸ hi)).elim

/-- Unequal arms have individually fixed tips. Equal arms can only exchange their tips. -/
theorem fork_iso_tips {b c : ℕ} (e : Iso (fork b c) (fork b c)) :
    (e.equiv (.inr false) = .inr false ∧ e.equiv (.inr true) = .inr true) ∨
      (c = 0 ∧ e.equiv (.inr false) = .inr true ∧ e.equiv (.inr true) = .inr false) := by
  have ht (p : Bool) : ∃ q : Bool, e.equiv (.inr p) = .inr q := by
    have hi := (iso_internal e (.inr p)).not.mp (fork_terminal b c p)
    cases h : e.equiv (.inr p) with
    | inl i => exact (hi (h.symm ▸ fork_internal_spine b c i)).elim
    | inr q => exact ⟨q, rfl⟩
  obtain ⟨p, hp⟩ := ht false
  obtain ⟨q, hq⟩ := ht true
  have hne : p ≠ q := by
    rintro rfl
    exact Bool.false_ne_true (Sum.inr.inj (e.equiv.injective (hp.trans hq.symm)))
  cases p <;> cases q
  · exact (hne rfl).elim
  · exact .inl ⟨hp, hq⟩
  · have hd := iso_depth e (Sum.inr false)
    rw [hp, depth_fork_long, depth_fork_short] at hd
    exact .inr ⟨by omega, hp, hq⟩
  · exact (hne rfl).elim

/-- The tip transposition preserves the parent map of an equal-arm fork. -/
def swapTips (b : ℕ) : Iso (fork b 0) (fork b 0) where
  equiv := Equiv.sumCongr (Equiv.refl _) ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩
  root_eq := rfl
  parent_eq x := by
    rcases x with i | p
    · rfl
    · cases p <;> rfl

#print axioms one_off_spine
#print axioms exists_fork_iso
#print axioms fork_iso_parameters
#print axioms fork_iso_tips

end

end D5.S3.Combinatorics.UnorderedTrees.OneFork
