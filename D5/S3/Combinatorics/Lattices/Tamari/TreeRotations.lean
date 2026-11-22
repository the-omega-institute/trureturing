/- GID: D5/S3/Combinatorics/Lattices/Tamari/TreeRotations
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/TreeRotations
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Contextual right rotations generate the coordinate order on tree brackets. -/

/-
admission_basis: escape-witness (registered contextual rotation bridge)
Direct frozen dependencies: none.
proof_shape: rotationReach_iff_bracket_le: content; escape_witness: rotationReach_iff_bracket_le
-/

import D5.S3.Combinatorics.Lattices.Tamari.BracketRows
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Inorder endpoint coordinates of full binary trees -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.Tamari

open scoped BinaryTree

abbrev FullTree := BinaryTree Unit

/-- There are `m` internal nodes and `m + 1` leaves. -/
abbrev Trees (m : ℕ) := {t : FullTree // t.numNodes = m}

/-- The rightmost internal inorder index of the subtree rooted at index `i`. -/
private def endpoint : FullTree → ℕ → ℕ
  | .nil, _ => 0
  | .node _ l r, i =>
    if i < l.numNodes then endpoint l i
    else if i = l.numNodes then l.numNodes + r.numNodes
    else l.numNodes + 1 + endpoint r (i - (l.numNodes + 1))

@[simp] private theorem endpoint_left (l r : FullTree) {i : ℕ} (hi : i < l.numNodes) :
    endpoint (l △ r) i = endpoint l i := by simp [endpoint, hi]

@[simp] private theorem endpoint_root (l r : FullTree) :
    endpoint (l △ r) l.numNodes = l.numNodes + r.numNodes := by simp [endpoint]

@[simp] private theorem endpoint_right (l r : FullTree) {i : ℕ} (hi : l.numNodes < i) :
    endpoint (l △ r) i = l.numNodes + 1 + endpoint r (i - (l.numNodes + 1)) := by
  simp [endpoint, hi.not_gt, hi.ne']

private theorem endpoint_bounds (t : FullTree) {i : ℕ} (hi : i < t.numNodes) :
    i ≤ endpoint t i ∧ endpoint t i < t.numNodes := by
  induction t using BinaryTree.unitRecOn generalizing i with
  | base => simp at hi
  | ind l r hl hr =>
    simp only [BinaryTree.numNodes] at hi ⊢
    rcases lt_trichotomy i l.numNodes with h | rfl | h
    · rw [endpoint_left l r h]
      obtain ⟨_, _⟩ := hl h
      omega
    · rw [endpoint_root]
      omega
    · rw [endpoint_right l r h]
      obtain ⟨_, _⟩ := hr (show i - (l.numNodes + 1) < r.numNodes by omega)
      omega

private theorem endpoint_nested (t : FullTree) {i j : ℕ} (hi : i < t.numNodes)
    (hij : i ≤ j) (hj : j ≤ endpoint t i) : endpoint t j ≤ endpoint t i := by
  induction t using BinaryTree.unitRecOn generalizing i j with
  | base => simp at hi
  | ind l r hl hr =>
    simp only [BinaryTree.numNodes] at hi
    rcases lt_trichotomy i l.numNodes with h | rfl | h
    · rw [endpoint_left l r h] at hj ⊢
      rw [endpoint_left l r (hj.trans_lt (endpoint_bounds l h).2)]
      exact hl h hij hj
    · rw [endpoint_root] at hj ⊢
      have h := (endpoint_bounds (l △ r) (i := j) (by simp <;> omega)).2
      simp only [BinaryTree.numNodes] at h
      omega
    · rw [endpoint_right l r h] at hj ⊢
      rw [endpoint_right l r (h.trans_le hij)]
      have h' := hr (show i - (l.numNodes + 1) < r.numNodes by omega)
        (j := j - (l.numNodes + 1)) (by omega) (by omega)
      omega

/-- The tree's actual right endpoint vector in the original Fin carrier. -/
def treeBrackets {m : ℕ} (t : Trees m) : BracketingFunctions m :=
  let inSize (i : Fin m) : i.val < t.val.numNodes := by rw [t.property]; exact i.isLt
  ⟨fun i => ⟨endpoint t.val i.val,
    (endpoint_bounds t.val (inSize i)).2.trans_le (Nat.le_of_eq t.property)⟩,
    ⟨fun i => (endpoint_bounds t.val (inSize i)).1,
      fun i _ hij hj => endpoint_nested t.val (inSize i) hij hj⟩⟩

private theorem endpoint_injective_on_size (t u : FullTree) (hs : t.numNodes = u.numNodes)
    (he : ∀ i < t.numNodes, endpoint t i = endpoint u i) : t = u := by
  induction t using BinaryTree.unitRecOn generalizing u with
  | base =>
    cases u using BinaryTree.unitRecOn with
    | base => rfl
    | ind l r => simp at hs
  | ind l r hl hr =>
    cases u using BinaryTree.unitRecOn with
    | base => simp at hs
    | ind l' r' =>
      simp only [BinaryTree.numNodes] at hs he
      have hleft : l.numNodes = l'.numNodes := by
        apply le_antisymm
        · by_contra! h
          have hx := he l'.numNodes (by omega)
          rw [endpoint_left l r h, endpoint_root] at hx
          have hx' := (endpoint_bounds l h).2
          omega
        · by_contra! h
          have hx := he l.numNodes (by omega)
          rw [endpoint_left l' r' h, endpoint_root] at hx
          have hx' := (endpoint_bounds l' h).2
          omega
      have hright : r.numNodes = r'.numNodes := by omega
      have hL : l = l' := hl _ hleft (fun i hi => by
        simpa only [endpoint_left l r hi, endpoint_left l' r' (hleft ▸ hi)] using
          he i (by omega))
      have hR : r = r' := hr _ hright (fun i hi => by
        have hx := he (l.numNodes + 1 + i) (by omega)
        rw [endpoint_right l r (by omega), endpoint_right l' r' (by omega)] at hx
        have h₁ : l.numNodes + 1 + i - (l.numNodes + 1) = i := by omega
        have h₂ : l.numNodes + 1 + i - (l'.numNodes + 1) = i := by omega
        rw [h₁, h₂] at hx
        omega)
      rw [hL, hR]

private theorem treeBrackets_injective (m : ℕ) : Function.Injective (treeBrackets (m := m)) := by
  intro t u he
  apply Subtype.ext
  apply endpoint_injective_on_size _ _ (t.property.trans u.property.symm)
  intro i hi
  let j : Fin m := ⟨i, t.property ▸ hi⟩
  exact congrArg (fun b : BracketingFunctions m => (b.val j).val) he

private def ValidVector (m : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ i < m, i ≤ f i ∧ f i < m) ∧
  (∀ i j, i < m → i ≤ j → j ≤ f i → f j ≤ f i)

private theorem reconstruct (m : ℕ) (f : ℕ → ℕ) (hf : ValidVector m f) :
    ∃ t : FullTree, t.numNodes = m ∧ ∀ i < m, endpoint t i = f i := by
  classical
  induction m using Nat.strong_induction_on generalizing f with
  | h m ih =>
    cases m with
    | zero => exact ⟨.nil, rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n =>
      have ex : ∃ k : ℕ, k < n + 1 ∧ f k = n :=
        ⟨n, by omega, by obtain ⟨_, _⟩ := hf.1 n (by omega); omega⟩
      let k := Nat.find ex
      have hkn : k < n + 1 := (Nat.find_spec ex).1
      have hfk : f k = n := (Nat.find_spec ex).2
      have left_lt (i : ℕ) (hi : i < k) : f i < k := by
        by_contra! h
        have := hf.2 i k (hi.trans hkn) hi.le h
        have := (hf.1 i (hi.trans hkn)).2
        have eq : f i = n := by omega
        exact (Nat.find_min ex hi) ⟨hi.trans hkn, eq⟩
      have hleft : ValidVector k f :=
        ⟨fun i hi => ⟨(hf.1 i (hi.trans hkn)).1, left_lt i hi⟩,
         fun i j hi => hf.2 i j (hi.trans hkn)⟩
      let g (i : ℕ) := f (k + 1 + i) - (k + 1)
      have right_bounds (i : ℕ) (hi : i < n - k) :
          k + 1 + i ≤ f (k + 1 + i) ∧ f (k + 1 + i) < n + 1 :=
        hf.1 _ (by omega)
      have hright : ValidVector (n - k) g := by
        constructor
        · intro i hi
          obtain ⟨_, _⟩ := right_bounds i hi
          dsimp [g]
          omega
        · intro i j hi hij hj
          have hbound := right_bounds i hi
          dsimp [g] at hj ⊢
          have h := hf.2 (k + 1 + i) (k + 1 + j) (by omega) (by omega) (by omega)
          omega
      obtain ⟨l, hl, hlv⟩ := ih k hkn f hleft
      obtain ⟨r, hr, hrv⟩ := ih (n - k) (by omega) g hright
      refine ⟨l △ r, by simp only [BinaryTree.numNodes, hl, hr]; omega, ?_⟩
      intro i hi
      rcases lt_trichotomy i k with h | rfl | h
      · rw [endpoint_left _ _ (by omega), hlv i h]
      · rw [hfk, ← hl, endpoint_root, hl, hr]
        omega
      · rw [endpoint_right _ _ (by omega), hrv _ (by omega)]
        dsimp only [g]
        rw [hl]
        have he : k + 1 + (i - (k + 1)) = i := by omega
        rw [he]
        have := (hf.1 i hi).1
        omega

private theorem treeBrackets_surjective (m : ℕ) : Function.Surjective (treeBrackets (m := m)) := by
  intro b
  let f (i : ℕ) : ℕ := if h : i < m then (b.val ⟨i, h⟩).val else 0
  have hf (i : ℕ) (hi : i < m) : f i = (b.val ⟨i, hi⟩).val := dite_eq_left hi
  have hvalid : ValidVector m f := by
    constructor
    · intro i hi
      rw [hf i hi]
      exact ⟨b.property.1 ⟨i, hi⟩, (b.val ⟨i, hi⟩).isLt⟩
    · intro i j hi hij hj
      rw [hf i hi] at hj ⊢
      have hj' := hj.trans_lt (b.val ⟨i, hi⟩).isLt
      rw [hf j hj']
      exact b.property.2 ⟨i, hi⟩ ⟨j, hj'⟩ hij hj
  obtain ⟨t, ht, htv⟩ := reconstruct m f hvalid
  refine ⟨⟨t, ht⟩, Subtype.ext (funext fun i => Fin.ext ?_)⟩
  exact (htv i.val i.isLt).trans (hf i.val i.isLt)

private noncomputable def treeBracketEquiv (m : ℕ) : Trees m ≃ BracketingFunctions m :=
  Equiv.ofBijective treeBrackets ⟨treeBrackets_injective m, treeBrackets_surjective m⟩

end D5.S3.Combinatorics.Lattices.Tamari

/-! # Contextual right rotations and the bracket order -/

namespace D5.S3.Combinatorics.Lattices.Tamari

open scoped BinaryTree

/- The constructors of RightRotation are adapted from Toshihisa Urahigashi,
HyperTamari/Tetration.lean, commit 6509a80801525ae9b419634246c754dea003306e.
Copyright (c) 2026 Toshihisa Urahigashi. Released under the MIT license in
docs/reports/licenses/garber-boolean-antichains/HyperTamari-MIT-LICENSE.txt.
The constructors use Mathlib's BinaryTree Unit. -/

/-- A right rotation at an arbitrary subtree. -/
inductive RightRotation : FullTree → FullTree → Prop where
  | root (a b c : FullTree) : RightRotation ((a △ b) △ c) (a △ (b △ c))
  | left {l l' : FullTree} (r : FullTree) : RightRotation l l' → RightRotation (l △ r) (l' △ r)
  | right (l : FullTree) {r r' : FullTree} : RightRotation r r' → RightRotation (l △ r) (l △ r')

abbrev RotationReach := Relation.ReflTransGen RightRotation

/-- A rotation changes one coordinate to the old endpoint of its inorder successor subtree. -/
private structure Raises (t u : FullTree) (i : ℕ) : Prop where
  size : t.numNodes = u.numNodes
  next_lt : endpoint t i + 1 < t.numNodes
  change_at : endpoint u i = endpoint t (endpoint t i + 1)
  unchanged : ∀ j < t.numNodes, j ≠ i → endpoint u j = endpoint t j

private theorem root_raises (a b c : FullTree) : Raises ((a △ b) △ c) (a △ (b △ c)) a.numNodes := by
  have old_i : endpoint ((a △ b) △ c) a.numNodes = a.numNodes + b.numNodes := by
    rw [endpoint_left _ _ (by simp <;> omega), endpoint_root]
  have old_next : endpoint ((a △ b) △ c) (a.numNodes + b.numNodes + 1) =
      a.numNodes + b.numNodes + 1 + c.numNodes :=
    endpoint_root (a △ b) c
  refine ⟨by simp <;> omega, by rw [old_i]; simp <;> omega, ?_, ?_⟩
  · rw [old_i, old_next, endpoint_root]
    simp
    omega
  · intro j hj hne
    simp only [BinaryTree.numNodes] at hj
    by_cases hL : j < a.numNodes
    · rw [endpoint_left _ _ hL, endpoint_left _ _ (by simp <;> omega), endpoint_left _ _ hL]
    have hR : a.numNodes < j := by omega
    rw [endpoint_right _ _ hR]
    let k := j - (a.numNodes + 1)
    change a.numNodes + 1 + endpoint (b △ c) k = _
    have hjk : j = a.numNodes + 1 + k := by dsimp [k]; omega
    rcases lt_trichotomy k b.numNodes with hk | hk | hk
    · rw [endpoint_left _ _ hk, endpoint_left _ _ (by simp <;> omega), endpoint_right _ _ hR]
    · rw [hk, endpoint_root]
      have he : j = (a △ b).numNodes := by simp; omega
      rw [he, endpoint_root]
      simp
      omega
    · rw [endpoint_right _ _ hk, endpoint_right _ _ (by simp <;> omega)]
      simp only [BinaryTree.numNodes]
      have hs : j - (a.numNodes + b.numNodes + 1 + 1) = k - (b.numNodes + 1) := by omega
      rw [hs]
      omega

private theorem Raises.left {l l' : FullTree} {i : ℕ} (h : Raises l l' i) (r : FullTree)
    (hi : i < l.numNodes) : Raises (l △ r) (l' △ r) i := by
  have hs := h.size
  have hn := h.next_lt
  refine ⟨by simp [hs], ?_, ?_, ?_⟩
  · rw [endpoint_left _ _ hi]
    simp
    omega
  · rw [endpoint_left l' r (by omega), endpoint_left l r hi, endpoint_left l r hn, h.change_at]
  · intro j hj hjne
    rcases lt_trichotomy j l.numNodes with hj' | hj' | hj'
    · rw [endpoint_left l r hj', endpoint_left l' r (by omega)]
      exact h.unchanged j hj' hjne
    · rw [hj', endpoint_root, hs, endpoint_root]
    · rw [endpoint_right l r hj', endpoint_right l' r (by omega), hs]

private theorem Raises.right {r r' : FullTree} {i : ℕ} (h : Raises r r' i) (l : FullTree)
    : Raises (l △ r) (l △ r') (l.numNodes + 1 + i) := by
  have hs := h.size
  have hn := h.next_lt
  have index_shift : l.numNodes + 1 + i - (l.numNodes + 1) = i := by omega
  have he : endpoint (l △ r) (l.numNodes + 1 + i) =
      l.numNodes + 1 + endpoint r i := by rw [endpoint_right _ _ (by omega), index_shift]
  refine ⟨by simp [hs], ?_, ?_, ?_⟩
  · rw [he]
    simp
    omega
  · rw [he, endpoint_right l r' (by omega), index_shift, endpoint_right l r (by omega)]
    have hsub : l.numNodes + 1 + endpoint r i + 1 - (l.numNodes + 1) = endpoint r i + 1 := by omega
    rw [hsub, h.change_at]
  · intro j hj hjne
    rcases lt_trichotomy j l.numNodes with hj' | rfl | hj'
    · rw [endpoint_left l r hj', endpoint_left l r' hj']
    · rw [endpoint_root, endpoint_root, hs]
    · rw [endpoint_right l r hj', endpoint_right l r' hj', h.unchanged]
      · simp only [BinaryTree.numNodes] at hj
        omega
      · omega

private theorem rotation_raises {t u : FullTree} (h : RightRotation t u) :
    ∃ i < t.numNodes, Raises t u i := by
  induction h with
  | root a b c => exact ⟨a.numNodes, by simp; omega, root_raises a b c⟩
  | left r _ ih =>
    obtain ⟨i, hi, h⟩ := ih
    exact ⟨i, by simp; omega, h.left r hi⟩
  | right l _ ih =>
    obtain ⟨i, hi, h⟩ := ih
    exact ⟨l.numNodes + 1 + i, by simp; omega, h.right l⟩

private theorem local_rotation (t : FullTree) (i : ℕ) (hi : i < t.numNodes)
    (hn : endpoint t i + 1 < t.numNodes)
    (he : ∀ j < i, endpoint t j ≠ endpoint t i) :
    ∃ u, RightRotation t u ∧ Raises t u i := by
  induction t using BinaryTree.unitRecOn generalizing i with
  | base => simp at hi
  | ind l r hl hr =>
    simp only [BinaryTree.numNodes] at hi hn
    rcases lt_trichotomy i l.numNodes with hil | rfl | hil
    · rw [endpoint_left l r hil] at he hn
      have hEarlier : ∀ j < i, endpoint l j ≠ endpoint l i := by
        intro j hj
        simpa only [endpoint_left l r (hj.trans hil)] using he j hj
      by_cases hs : endpoint l i + 1 < l.numNodes
      · obtain ⟨u, hu, h⟩ := hl i hil hs hEarlier
        exact ⟨u △ r, hu.left r, h.left r hil⟩
      · cases l using BinaryTree.unitRecOn with
        | base => simp at hil
        | ind a b =>
          have equal : endpoint (a △ b) i = a.numNodes + b.numNodes := by
            have := (endpoint_bounds (a △ b) hil).2
            simp only [BinaryTree.numNodes] at this hs
            omega
          have hik : i = a.numNodes := by
            rcases lt_trichotomy i a.numNodes with h | h | h
            · rw [endpoint_left a b h] at equal
              have := (endpoint_bounds a h).2
              omega
            · exact h
            · exact (hEarlier a.numNodes h ((endpoint_root a b).trans equal.symm)).elim
          subst i
          exact ⟨a △ (b △ r), .root a b r, root_raises a b r⟩
    · rw [endpoint_root] at hn
      omega
    · rw [endpoint_right l r hil] at hn he
      let j := i - (l.numNodes + 1)
      have hi' : i = l.numNodes + 1 + j := by dsimp [j]; omega
      have hj : j < r.numNodes := by omega
      have hn' : endpoint r j + 1 < r.numNodes := by
        change _ + 1 + endpoint r j + 1 < _ at hn
        omega
      have he' (k : ℕ) (hk : k < j) : endpoint r k ≠ endpoint r j := by
        intro eq
        apply he (l.numNodes + 1 + k) (by omega)
        rw [endpoint_right l r (by omega)]
        have hsub : l.numNodes + 1 + k - (l.numNodes + 1) = k := by omega
        rw [hsub, eq]
      obtain ⟨u, hu, h⟩ := hr j hj hn' he'
      exact ⟨l △ u, hu.right l, hi'.symm ▸ h.right l⟩

private theorem rotation_preserves_size {t u : FullTree} (h : RightRotation t u) :
    t.numNodes = u.numNodes :=
  (rotation_raises h).choose_spec.2.size

private theorem raises_lt {t u : FullTree} {i : ℕ} (h : Raises t u i) :
    endpoint t i < endpoint u i := by
  rw [h.change_at]
  exact (Nat.lt_succ_self _).trans_le (endpoint_bounds t h.next_lt).1

private theorem rotation_bracket_le {m : ℕ} {t u : Trees m} (h : RightRotation t.val u.val) :
    treeBrackets t ≤ treeBrackets u := by
  obtain ⟨i, _, h⟩ := rotation_raises h
  intro j
  change endpoint t.val j.val ≤ endpoint u.val j.val
  by_cases hj : j.val = i
  · rw [hj]
    exact (raises_lt h).le
  · rw [h.unchanged _ (t.property.symm ▸ j.isLt) hj]

private theorem reach_bracket_le {m : ℕ} {t u : Trees m} (h : RotationReach t.val u.val) :
    treeBrackets t ≤ treeBrackets u := by
  have step (v : FullTree) (h : RotationReach t.val v) :
      ∀ hv : v.numNodes = m, treeBrackets t ≤ treeBrackets (⟨v, hv⟩ : Trees m) := by
    induction h with
    | refl => intro _; exact le_rfl
    | tail _ h ih =>
      intro hv
      exact (ih ((rotation_preserves_size h).trans hv)).trans (rotation_bracket_le h)
  exact step u.val h u.property

private theorem bracket_le_reach {m : ℕ} {t u : Trees m} (h : treeBrackets t ≤ treeBrackets u) :
    RotationReach t.val u.val := by
  classical
  let gap (v : Trees m) := ∑ j : Fin m, (endpoint u.val j.val - endpoint v.val j.val)
  generalize hd : gap t = d
  induction d using Nat.strong_induction_on generalizing t with
  | h d ih =>
    by_cases he : treeBrackets t = treeBrackets u
    · rw [treeBrackets_injective m he]
    have ex : ∃ i : ℕ, i < m ∧ endpoint t.val i < endpoint u.val i := by
      by_contra! hall
      apply he
      apply le_antisymm h
      intro i
      exact hall i.val i.isLt
    let i := Nat.find ex
    have hi : i < m := (Nat.find_spec ex).1
    have hlt : endpoint t.val i < endpoint u.val i := (Nat.find_spec ex).2
    have hmin (j : ℕ) (hj : j < i) : endpoint t.val j = endpoint u.val j := by
      have hjm := hj.trans hi
      refine le_antisymm (h ⟨j, hjm⟩) (le_of_not_gt fun h' => ?_)
      exact (Nat.find_min ex hj) ⟨hjm, h'⟩
    have hiT : i < t.val.numNodes := t.property.symm ▸ hi
    have hiU : i < u.val.numNodes := u.property.symm ▸ hi
    have hU := (endpoint_bounds u.val hiU).2
    have hn : endpoint t.val i + 1 < t.val.numNodes := by
      rw [t.property]
      rw [u.property] at hU
      omega
    have hearlier (j : ℕ) (hj : j < i) : endpoint t.val j ≠ endpoint t.val i := by
      rw [hmin j hj]
      intro eq
      have hnest := endpoint_nested u.val (u.property.symm ▸ hj.trans hi) hj.le
        (show i ≤ endpoint u.val j from eq ▸ (endpoint_bounds t.val hiT).1)
      omega
    obtain ⟨v, hv, hra⟩ := local_rotation _ _ hiT hn hearlier
    let v' : Trees m := ⟨v, hra.size.symm.trans t.property⟩
    have hbelow : treeBrackets v' ≤ treeBrackets u := by
      intro j
      change endpoint v j.val ≤ endpoint u.val j.val
      by_cases hj : j.val = i
      · rw [hj, hra.change_at]
        let j : Fin m := ⟨endpoint t.val i + 1, hn.trans_le (Nat.le_of_eq t.property)⟩
        have hj' : endpoint t.val j.val ≤ endpoint u.val j.val := h j
        exact hj'.trans
          (endpoint_nested u.val hiU
            ((endpoint_bounds t.val hiT).1.trans (Nat.le_succ _)) hlt)
      · rw [hra.unchanged _ (t.property.symm ▸ j.isLt) hj]
        exact h j
    have hgap : gap v' < gap t := by
      apply Finset.sum_lt_sum
      · intro j _
        exact Nat.sub_le_sub_left (rotation_bracket_le (t := t) (u := v') hv j) _
      · refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
        have h' : endpoint v i ≤ endpoint u.val i := hbelow ⟨i, hi⟩
        have h'' := raises_lt hra
        change endpoint u.val i - endpoint v i < endpoint u.val i - endpoint t.val i
        omega
    exact (Relation.ReflTransGen.single hv).trans (ih _ (hd ▸ hgap) hbelow rfl)

theorem rotationReach_iff_bracket_le {m : ℕ} (t u : Trees m) :
    RotationReach t.val u.val ↔ treeBrackets t ≤ treeBrackets u :=
  ⟨reach_bracket_le, bracket_le_reach⟩

/-- The Tamari order on full parenthesizations with `m + 1` ordered leaves. -/
instance tamariPartialOrder (m : ℕ) : PartialOrder (Trees m) where
  le t u := RotationReach t.val u.val
  le_refl _ := .refl
  le_trans _ _ _ h g := h.trans g
  le_antisymm t u h g := treeBrackets_injective m
    (le_antisymm (reach_bracket_le h) (reach_bracket_le g))

noncomputable def treeBracketOrderIso (m : ℕ) : Trees m ≃o BracketingFunctions m where
  toEquiv := treeBracketEquiv m
  map_rel_iff' := (rotationReach_iff_bracket_le _ _).symm

end D5.S3.Combinatorics.Lattices.Tamari
