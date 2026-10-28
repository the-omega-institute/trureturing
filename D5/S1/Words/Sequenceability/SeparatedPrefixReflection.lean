/- GID: D5/S1/Words/Sequenceability/SeparatedPrefixReflection
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/SeparatedPrefixReflection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Separated block reversal replaces pref inventory and repairs a prescribed legal pair. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeDrop
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Affine reflection acts on pref values, while the word operation reverses
actual letters. The full zero-sum interval remains exempt. The strict cone and
separated excursion are extra hypotheses, not consequences of compression
existence. The unrestricted sequenceability and adaptive merge questions remain
open. Native source and independent audit supply the mathematical construction;
no specialized finite-group `Good` or `expand` is treated as a generic API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.SeparatedPrefixReflection

variable {G : Type*} [AddCommGroup G]

private noncomputable instance : DecidableEq G := Classical.decEq G

/-- Empty and full prefes are included. -/
def pref (w : List G) (i : ℕ) : G := (w.take i).sum

/-- Every nonempty proper contiguous interval has nonzero sum. -/
def Good (w : List G) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ w.length → (i ≠ 0 ∨ j ≠ w.length) →
    ((w.drop i).take (j - i)).sum ≠ 0

/-- Only addition closure and exclusion of zero are required. -/
structure StrictCone (C : Set G) : Prop where
  add_mem : ∀ {x y}, x ∈ C → y ∈ C → x + y ∈ C
  zero_not_mem : (0 : G) ∉ C

def ConeLE (C : Set G) (x y : G) : Prop := x = y ∨ y - x ∈ C

/-- The actual occurrence block `[h,k)` is reversed. -/
def reverseBlock (w : List G) (h k : ℕ) : List G :=
  w.take h ++ ((w.drop h).take (k - h)).reverse ++ w.drop k

noncomputable def inventory (w : List G) : Finset G := by
  classical
  exact (Finset.range (w.length + 1)).image (pref w)

noncomputable def interior (w : List G) (h k : ℕ) : Finset G := by
  classical
  exact (Finset.Ioo h k).image (pref w)

noncomputable def reflected (w : List G) (h k : ℕ) (lo hi : G) : Finset G := by
  classical
  exact (interior w h k).image (fun x => lo + hi - x)

/-- Both orientations, including coincident full-word endpoints, are admitted. -/
def Separated (C : Set G) (w : List G) (h k : ℕ) (lo hi : G) : Prop :=
  ((pref w h = lo ∧ pref w k = hi) ∨
    (pref w h = hi ∧ pref w k = lo)) ∧
  ConeLE C lo hi ∧
  (∀ i, h < i → i < k → pref w i - hi ∈ C) ∧
  (∀ j, j ≤ w.length → (j ≤ h ∨ k ≤ j) → ConeLE C lo (pref w j))

private theorem interval_eq (w : List G) {i j : ℕ} (hij : i ≤ j) :
    ((w.drop i).take (j - i)).sum = pref w j - pref w i := by
  have hs := List.sum_take_add_sum_drop (w.take j) i
  rw [List.take_take, Nat.min_eq_left hij, List.drop_take] at hs
  change pref w i + ((w.drop i).take (j - i)).sum = pref w j at hs
  rw [← hs]
  abel

theorem good_iff (w : List G) :
    Good w ↔ ∀ i j : ℕ, i < j → j ≤ w.length →
      pref w i = pref w j → i = 0 ∧ j = w.length := by
  constructor
  · intro hw i j hij hj he
    by_contra hn
    have hp : i ≠ 0 ∨ j ≠ w.length := by omega
    apply hw i j hij hj hp
    rw [interval_eq w hij.le, he, sub_self]
  · intro hw i j hij hj hp hz
    have he : pref w i = pref w j := by
      rw [interval_eq w hij.le, sub_eq_zero] at hz
      exact hz.symm
    obtain ⟨rfl, rfl⟩ := hw i j hij hj he
    simp at hp

private theorem internal_unique {w : List G} (hw : Good w)
    {i j : ℕ} (hi0 : 0 < i) (him : i < w.length) (hj : j ≤ w.length)
    (he : pref w i = pref w j) : i = j := by
  by_cases hij : i < j
  · have := (good_iff w).mp hw i j hij hj he
    omega
  · by_cases hji : j < i
    · have := (good_iff w).mp hw j i hji him.le he.symm
      omega
    · omega

private theorem block_split (w : List G) {h k : ℕ} (hhk : h ≤ k) :
    w.take h ++ (w.drop h).take (k - h) ++ w.drop k = w := by
  rw [List.append_assoc, show w.drop k = w.drop (h + (k - h)) by congr 1; omega,
    List.drop_take_append_drop, List.take_append_drop]

private theorem reverse_perm (w : List G) {h k : ℕ} (hhk : h ≤ k) :
    (reverseBlock w h k).Perm w := by
  have hp : (reverseBlock w h k).Perm
      (w.take h ++ (w.drop h).take (k - h) ++ w.drop k) :=
    ((List.Perm.refl _).append (List.reverse_perm _)).append (List.Perm.refl _)
  exact hp.trans (by rw [block_split w hhk])

private theorem reverse_length (w : List G) {h k : ℕ} (hhk : h ≤ k) :
    (reverseBlock w h k).length = w.length := (reverse_perm w hhk).length_eq

theorem pref_append_left (L R : List G) {j : ℕ} (hj : j ≤ L.length) :
    pref (L ++ R) j = pref L j := by
  simp only [pref, List.take_append_of_le_length hj]

theorem pref_append_right (L R : List G) {j : ℕ} (hj : L.length ≤ j) :
    pref (L ++ R) j = L.sum + pref R (j - L.length) := by
  simp only [pref, List.take_append, List.take_of_length_le hj, List.sum_append]

private theorem reverse_pref_left (w : List G) {h k j : ℕ}
    (hh : h ≤ w.length) (hj : j ≤ h) :
    pref (reverseBlock w h k) j = pref w j := by
  rw [reverseBlock, List.append_assoc, pref_append_left _ _ (by simp; omega)]
  simp only [pref, List.take_take, Nat.min_eq_left hj]

private theorem triple_pref (L M R : List G) {j : ℕ} (hj : j ≤ M.length) :
    pref (L ++ M ++ R) (L.length + j) = L.sum + pref M j := by
  rw [List.append_assoc, pref_append_right _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [pref_append_left _ _ hj]

private theorem triple_reflect (L M R : List G) {j : ℕ} (hj : j ≤ M.length) :
    pref (L ++ M.reverse ++ R) (L.length + j) =
      L.sum + M.sum - pref M (M.length - j) := by
  rw [triple_pref L M.reverse R (by simpa using hj)]
  simp only [pref, List.take_reverse, List.sum_reverse]
  have hs := List.sum_take_add_sum_drop M (M.length - j)
  rw [← hs]
  abel

private theorem block_lengths (w : List G) {h k : ℕ} (hhk : h ≤ k)
    (hk : k ≤ w.length) :
    (w.take h).length = h ∧ ((w.drop h).take (k - h)).length = k - h := by
  simp only [List.length_take, List.length_drop]
  constructor <;> omega

private theorem reverse_pref_middle (w : List G) {h k j : ℕ}
    (hhk : h ≤ k) (hk : k ≤ w.length) (hjh : h ≤ j) (hjk : j ≤ k) :
    pref (reverseBlock w h k) j =
      pref w h + pref w k - pref w (h + k - j) := by
  let L := w.take h
  let M := (w.drop h).take (k - h)
  let R := w.drop k
  have hl : L.length = h := (block_lengths w hhk hk).1
  have hm : M.length = k - h := (block_lengths w hhk hk).2
  have hs : L ++ M ++ R = w := block_split w hhk
  have hj : j = L.length + (j - h) := by omega
  have he : h + k - j = L.length + (M.length - (j - h)) := by omega
  have ph : pref w h = L.sum := by simp [pref, L]
  have pk : pref w k = L.sum + M.sum := by
    rw [← hs, show k = L.length + M.length by omega, triple_pref L M R (le_refl _)]
    simp [pref]
  have pr : pref w (h + k - j) = L.sum + pref M (M.length - (j - h)) := by
    rw [← hs, he, triple_pref L M R (by omega)]
  change pref (L ++ M.reverse ++ R) j = _
  have hr := triple_reflect L M R (j := j - h) (by omega)
  rw [← hj] at hr
  rw [hr, ph, pk, pr]
  abel

private theorem reverse_pref_right (w : List G) {h k j : ℕ}
    (hhk : h ≤ k) (hk : k ≤ w.length) (hj : k ≤ j) :
    pref (reverseBlock w h k) j = pref w j := by
  let L := w.take h
  let M := (w.drop h).take (k - h)
  let R := w.drop k
  have hl : L.length = h := (block_lengths w hhk hk).1
  have hm : M.length = k - h := (block_lengths w hhk hk).2
  have hs : L ++ M ++ R = w := block_split w hhk
  have hlen : (L ++ M).length = k := by simp only [List.length_append]; omega
  have hlen' : (L ++ M.reverse).length = k := by simpa using hlen
  change pref ((L ++ M.reverse) ++ R) j = pref w j
  rw [pref_append_right _ _ (by omega), ← hs,
    pref_append_right _ _ (by omega)]
  simp only [hlen, hlen', List.sum_append, List.sum_reverse]

theorem mem_inventory {w : List G} {x : G} :
    x ∈ inventory w ↔ ∃ j ≤ w.length, pref w j = x := by
  classical
  simp only [inventory, Finset.mem_image, Finset.mem_range]
  constructor <;> rintro ⟨j, hj, rfl⟩ <;> exact ⟨j, by omega, rfl⟩

private theorem mem_interior {w : List G} {h k : ℕ} {x : G} :
    x ∈ interior w h k ↔ ∃ j, h < j ∧ j < k ∧ pref w j = x := by
  classical
  simp only [interior, Finset.mem_image, Finset.mem_Ioo]
  aesop

private theorem reflect_injective (lo hi : G) :
    Function.Injective (fun x : G => lo + hi - x) := by
  intro x y he
  exact (sub_right_inj.mp he)

private theorem endpoint_sum {C : Set G} {w : List G} {h k : ℕ} {lo hi : G}
    (hs : Separated C w h k lo hi) : pref w h + pref w k = lo + hi := by
  rcases hs.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> abel

private theorem old_interior_above {C : Set G} (hc : StrictCone C)
    {w : List G} {h k : ℕ} {lo hi : G} (hs : Separated C w h k lo hi)
    {i : ℕ} (hi : h < i) (hik : i < k) : pref w i - lo ∈ C := by
  have hh := hs.2.2.1 i hi hik
  rcases hs.2.1 with he | he
  · simpa [he] using hh
  · have ha := hc.add_mem hh he
    convert ha using 1 <;> abel

private theorem reflected_disjoint {C : Set G} (hc : StrictCone C)
    {w : List G} {h k : ℕ} {lo hi : G} (hk : k ≤ w.length)
    (hs : Separated C w h k lo hi) :
    Disjoint (reflected w h k lo hi) (inventory w) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hy hyold
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨i, hhi, hik, rfl⟩ := mem_interior.mp hx
  obtain ⟨j, hj, he⟩ := mem_inventory.mp hyold
  have hbelow : lo - (lo + hi - pref w i) ∈ C := by
    convert hs.2.2.1 i hhi hik using 1 <;> abel
  have hge : ConeLE C lo (pref w j) := by
    by_cases hjin : h < j ∧ j < k
    · exact Or.inr (old_interior_above hc hs hjin.1 hjin.2)
    · exact hs.2.2.2 j hj (by omega)
  rw [he] at hge
  rcases hge with hzero | hpos
  · apply hc.zero_not_mem
    simpa [← hzero] using hbelow
  · apply hc.zero_not_mem
    have hz := hc.add_mem hbelow hpos
    convert hz using 1 <;> abel

private theorem exterior_not_interior {w : List G} (hw : Good w)
    {h k j : ℕ} (hk : k ≤ w.length) (hj : j ≤ w.length)
    (hext : j ≤ h ∨ k ≤ j) : pref w j ∉ interior w h k := by
  intro hx
  obtain ⟨i, hhi, hik, he⟩ := mem_interior.mp hx
  have := internal_unique hw (by omega) (by omega) hj he
  omega

private theorem reverse_inventory {C : Set G} {w : List G} (hw : Good w)
    {h k : ℕ} (hhk : h ≤ k) (hk : k ≤ w.length) {lo hi : G}
    (hs : Separated C w h k lo hi) :
    inventory (reverseBlock w h k) =
      (inventory w \ interior w h k) ∪ reflected w h k lo hi := by
  classical
  have hlen := reverse_length w hhk
  have hout : ∀ j ≤ w.length, (j ≤ h ∨ k ≤ j) →
      pref (reverseBlock w h k) j = pref w j := by
    intro j hj he
    rcases he with he | he
    · exact reverse_pref_left w (by omega) he
    · exact reverse_pref_right w hhk hk he
  have hin : ∀ j, h < j → j < k → pref (reverseBlock w h k) j =
      lo + hi - pref w (h + k - j) := by
    intro j hjh hjk
    rw [reverse_pref_middle w hhk hk hjh.le hjk.le, endpoint_sum hs]
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := mem_inventory.mp hx
    by_cases hjin : h < j ∧ j < k
    · right
      rw [hin j hjin.1 hjin.2]
      exact Finset.mem_image.mpr ⟨pref w (h + k - j),
        mem_interior.mpr ⟨h + k - j, by omega, by omega, rfl⟩, rfl⟩
    · left
      rw [hout j (by omega) (by omega)]
      exact ⟨mem_inventory.mpr ⟨j, by omega, rfl⟩,
        exterior_not_interior hw hk (by omega) (by omega)⟩
  · rintro (⟨hx, hn⟩ | hx)
    · obtain ⟨j, hj, rfl⟩ := mem_inventory.mp hx
      have he : j ≤ h ∨ k ≤ j := by
        by_contra he
        exact hn (mem_interior.mpr ⟨j, by omega, by omega, rfl⟩)
      exact mem_inventory.mpr ⟨j, by omega, hout j hj he⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨i, hhi, hik, rfl⟩ := mem_interior.mp hy
      refine mem_inventory.mpr ⟨h + k - i, by omega, ?_⟩
      rw [hin _ (by omega) (by omega), show h + k - (h + k - i) = i by omega]

private theorem reverse_good {C : Set G} (hc : StrictCone C)
    {w : List G} (hw : Good w) {h k : ℕ} (hhk : h ≤ k) (hk : k ≤ w.length)
    {lo hi : G} (hs : Separated C w h k lo hi) : Good (reverseBlock w h k) := by
  have hlen := reverse_length w hhk
  have hd := Finset.disjoint_left.mp (reflected_disjoint hc hk hs)
  have hin : ∀ j, h < j → j < k → pref (reverseBlock w h k) j =
      lo + hi - pref w (h + k - j) := by
    intro j hjh hjk
    rw [reverse_pref_middle w hhk hk hjh.le hjk.le, endpoint_sum hs]
  have hout : ∀ j, (j ≤ h ∨ k ≤ j) → pref (reverseBlock w h k) j = pref w j := by
    intro j hj
    rcases hj with hj | hj
    · exact reverse_pref_left w (by omega) hj
    · exact reverse_pref_right w hhk hk hj
  have hnew : ∀ j, h < j → j < k →
      pref (reverseBlock w h k) j ∈ reflected w h k lo hi := by
    intro j hjh hjk
    rw [hin j hjh hjk]
    exact Finset.mem_image.mpr ⟨pref w (h + k - j),
      mem_interior.mpr ⟨h + k - j, by omega, by omega, rfl⟩, rfl⟩
  apply (good_iff _).mpr
  intro i j hij hj he
  by_cases hii : h < i ∧ i < k
  · by_cases hji : h < j ∧ j < k
    · rw [hin i hii.1 hii.2, hin j hji.1 hji.2] at he
      have hp := reflect_injective lo hi he
      have hh := internal_unique hw (i := h + k - i) (j := h + k - j)
        (by omega) (by omega) (by omega) hp
      omega
    · rw [hout j (by omega)] at he
      exact (hd (hnew i hii.1 hii.2) (mem_inventory.mpr ⟨j, by omega, he.symm⟩)).elim
  · by_cases hji : h < j ∧ j < k
    · rw [hout i (by omega)] at he
      exact (hd (hnew j hji.1 hji.2) (mem_inventory.mpr ⟨i, by omega, he⟩)).elim
    · rw [hout i (by omega), hout j (by omega)] at he
      obtain ⟨hi0, hjm⟩ := (good_iff w).mp hw i j hij (by omega) he
      exact ⟨hi0, by omega⟩

private theorem interior_card {w : List G} (hw : Good w) {h k : ℕ}
    (hk : k ≤ w.length) : (interior w h k).card = k - h - 1 := by
  classical
  rw [interior, Finset.card_image_of_injOn]
  · exact Nat.card_Ioo h k
  · intro i hi j hj he
    have hi' := Finset.mem_Ioo.mp hi
    have hj' := Finset.mem_Ioo.mp hj
    exact internal_unique hw (by omega) (by omega) (by omega) he

/-- Reversing a separated upper excursion changes exactly the strict interior
prefix values. No distinctness of letters or nonzero-total premise is imposed. -/
theorem separated_prefix_reflection (C : Set G) (hc : StrictCone C)
    (w : List G) (hw : Good w) (h k : ℕ) (hgap : 2 ≤ k - h)
    (hk : k ≤ w.length) (lo hi : G) (hs : Separated C w h k lo hi) :
    let v := reverseBlock w h k
    v.Perm w ∧ v.length = w.length ∧ v.sum = w.sum ∧
    (∀ j ≤ w.length, (j ≤ h ∨ k ≤ j) → pref v j = pref w j) ∧
    (∀ j, h ≤ j → j ≤ k → pref v j = pref w h + pref w k - pref w (h + k - j)) ∧
    Good v ∧ Disjoint (reflected w h k lo hi) (inventory w) ∧
    inventory v = (inventory w \ interior w h k) ∪ reflected w h k lo hi ∧
    inventory w \ inventory v = interior w h k ∧
    inventory v \ inventory w = reflected w h k lo hi ∧
    (interior w h k).card = k - h - 1 ∧
    (reflected w h k lo hi).card = k - h - 1 ∧ 0 < k - h - 1 := by
  classical
  have hhk : h ≤ k := by omega
  have hp := reverse_perm w hhk
  have hd := reflected_disjoint hc hk hs
  have hv := reverse_inventory hw hhk hk hs
  have hsub : interior w h k ⊆ inventory w := by
    intro x hx
    obtain ⟨i, hhi, hik, rfl⟩ := mem_interior.mp hx
    exact mem_inventory.mpr ⟨i, by omega, rfl⟩
  have hrem : inventory w \ inventory (reverseBlock w h k) = interior w h k := by
    rw [hv]
    apply Finset.ext
    intro x
    have hh := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨ha, hn⟩
      by_contra hni
      exact hn (Or.inl ⟨ha, hni⟩)
    · intro ha
      exact ⟨hsub ha, fun he => he.elim (fun z => z.2 ha) (fun z => hh z (hsub ha))⟩
  have hadd : inventory (reverseBlock w h k) \ inventory w = reflected w h k lo hi := by
    rw [hv]
    apply Finset.ext
    intro x
    have hh := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨ha | ha, hn⟩
      · exact (hn ha.1).elim
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hh ha⟩
  refine ⟨hp, hp.length_eq, hp.sum_eq, ?_, ?_, reverse_good hc hw hhk hk hs,
    hd, hv, hrem, hadd, interior_card hw hk, ?_, by omega⟩
  · intro j hj he
    rcases he with he | he
    · exact reverse_pref_left w (by omega) he
    · exact reverse_pref_right w hhk hk he
  · intro j hjh hjk
    exact reverse_pref_middle w hhk hk hjh hjk
  · rw [reflected, Finset.card_image_of_injective _ (reflect_injective lo hi)]
    exact interior_card hw hk

/-- Positional expansion of a specified occurrence; no other letter changes. -/
def expandAt (w : List G) (t : ℕ) (a b : G) : List G :=
  w.take t ++ a :: b :: w.drop (t + 1)

/-- The original legal compression alphabet, with each original label once. -/
noncomputable def compressed (A : Finset G) (a b : G) : Finset G :=
  insert (a + b) ((A.erase a).erase b)

def Omega (A : Finset G) (a b : G) (w : List G) : Prop :=
  w.Perm (compressed A a b).toList ∧ Good w

private theorem split_at (w : List G) {t : ℕ} (ht : t < w.length) :
    w.take t ++ w[t] :: w.drop (t + 1) = w := by
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

private theorem expansion_pref (L R : List G) (a b : G) (j : ℕ) :
    pref (L ++ a :: b :: R) j =
      if j ≤ L.length then pref (L ++ (a + b) :: R) j
      else if j = L.length + 1 then L.sum + a
      else pref (L ++ (a + b) :: R) (j - 1) := by
  by_cases hj : j ≤ L.length
  · simp only [if_pos hj]
    rw [pref_append_left _ _ hj, pref_append_left _ _ hj]
  · rw [if_neg hj, pref_append_right _ _ (by omega)]
    by_cases he : j = L.length + 1
    · simp [he, pref]
    · rw [if_neg he, pref_append_right _ _ (by omega)]
      have hj2 : j - L.length = (j - L.length - 2) + 2 := by omega
      have hj1 : j - 1 - L.length = (j - L.length - 2) + 1 := by omega
      simp only [pref]
      rw [hj2, hj1]
      simp only [List.take_succ_cons, List.sum_cons]
      abel

theorem expansion_good (L R : List G) (a b : G)
    (hw : Good (L ++ (a + b) :: R))
    (hn : L.sum + a ∉ inventory (L ++ (a + b) :: R)) :
    Good (L ++ a :: b :: R) := by
  let w := L ++ (a + b) :: R
  let v := L ++ a :: b :: R
  have hwlen : w.length = L.length + R.length + 1 := by simp [w]; omega
  have hvlen : v.length = L.length + R.length + 2 := by simp [v]; omega
  have hi : pref v (L.length + 1) = L.sum + a := by
    rw [expansion_pref]
    simp
  have hp : ∀ j, j ≠ L.length + 1 →
      pref v j = pref w (if j ≤ L.length then j else j - 1) := by
    intro j hj
    change pref (L ++ a :: b :: R) j =
      pref (L ++ (a + b) :: R) (if j ≤ L.length then j else j - 1)
    rw [expansion_pref]
    split_ifs <;> simp_all
  apply (good_iff v).mpr
  intro i j hij hj he
  by_cases hit : i = L.length + 1
  · have hjt : j ≠ L.length + 1 := by omega
    rw [hit, hi, hp j hjt] at he
    exact (hn (mem_inventory.mpr
      ⟨if j ≤ L.length then j else j - 1, by change _ ≤ w.length; split_ifs <;> omega, he.symm⟩)).elim
  · by_cases hjt : j = L.length + 1
    · rw [hjt, hi, hp i hit] at he
      exact (hn (mem_inventory.mpr
        ⟨if i ≤ L.length then i else i - 1, by change _ ≤ w.length; split_ifs <;> omega, he⟩)).elim
    · rw [hp i hit, hp j hjt] at he
      obtain ⟨hi0, hjm⟩ := (good_iff w).mp hw
        (if i ≤ L.length then i else i - 1) (if j ≤ L.length then j else j - 1)
        (by split_ifs <;> omega) (by split_ifs <;> omega) he
      constructor <;> split_ifs at hi0 hjm <;> omega

private theorem expansion_at_good (w : List G) (hw : Good w) {t : ℕ}
    (ht : t < w.length) (a b : G) (he : w[t] = a + b)
    (hn : pref w t + a ∉ inventory w) : Good (expandAt w t a b) := by
  have hs : w.take t ++ (a + b) :: w.drop (t + 1) = w := by
    rw [← he, split_at w ht]
  apply expansion_good
  · rwa [hs]
  · simpa only [pref, hs] using hn

theorem expansion_inventory (A : Finset G) (a b : G)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hr : a + b ∉ A)
    (w : List G) (hw : w.Perm (compressed A a b).toList)
    {t : ℕ} (ht : t < w.length) (he : w[t] = a + b) :
    (expandAt w t a b).Perm A.toList := by
  classical
  let L := w.take t
  let R := w.drop (t + 1)
  let D := (A.erase a).erase b
  have hrD : a + b ∉ D := by
    intro hh
    exact hr (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hh))
  have hs : L ++ (a + b) :: R = w := by
    dsimp [L, R]
    rw [← he, split_at w ht]
  have htail : (L ++ R).Perm D.toList := by
    have hp : ((a + b) :: (L ++ R)).Perm (compressed A a b).toList :=
      List.perm_middle.symm.trans (hs ▸ hw)
    have hd : (compressed A a b).toList.Perm ((a + b) :: D.toList) := by
      exact Finset.toList_insert hrD
    exact (hp.trans hd).cons_inv
  have habD : a ∉ D := by simp [D]
  have hbD : b ∉ D := by simp [D]
  have hrestore : insert a (insert b D) = A := by
    ext x
    simp only [Finset.mem_insert, D, Finset.mem_erase]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  have hbase : (a :: b :: D.toList).Perm A.toList := by
    have hp := (List.Perm.cons a (Finset.toList_insert hbD).symm).trans
      (Finset.toList_insert (by simp [hab, habD])).symm
    rw [hrestore] at hp
    exact hp
  have hp : (L ++ a :: b :: R).Perm (a :: b :: (L ++ R)) :=
    List.perm_middle.trans (List.Perm.cons a List.perm_middle)
  exact hp.trans ((List.Perm.cons a (List.Perm.cons b htail)).trans hbase)

/-- The same legal pair and the prescribed orientation succeed after reversing
an input-separated block that avoids the merged occurrence and contains its
inserted collision. No successful output or subset induction is a premise. -/
theorem same_pair_repair (C : Set G) (hc : StrictCone C)
    (A : Finset G) (hA : (0 : G) ∉ A) (a b : G) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hr : a + b ∉ insert 0 A)
    (w : List G) (hw : Omega A a b w) (t : ℕ) (ht : t < w.length)
    (hmerge : w[t] = a + b) (h k : ℕ) (hgap : 2 ≤ k - h) (hk : k ≤ w.length)
    (lo hi : G) (hs : Separated C w h k lo hi) (hout : t < h ∨ k ≤ t)
    (hcollision : ∃ i, h < i ∧ i < k ∧ pref w t + a = pref w i) :
    let v := reverseBlock w h k
    Omega A a b v ∧ v ≠ w ∧
    pref v t = pref w t ∧
    (∃ ht' : t < v.length, v[t] = a + b) ∧
    pref v t + a ∉ inventory v ∧ Good (expandAt v t a b) ∧
    (expandAt v t a b).Perm A.toList ∧
    (expandAt v t a b).sum = w.sum ∧
    (∀ x ∈ expandAt v t a b, x ≠ 0) := by
  classical
  have hhk : h ≤ k := by omega
  obtain ⟨hp, hl, hsum, hext, _, hg, _, _, hremoved, _, _, _, _⟩ :=
    separated_prefix_reflection C hc w hw.2 h k hgap hk lo hi hs
  let v := reverseBlock w h k
  have hvt : t < v.length := by dsimp [v]; omega
  have hpre : pref v t = pref w t := hext t ht.le (by omega)
  have hnext : pref v (t + 1) = pref w (t + 1) := hext (t + 1) (by omega) (by omega)
  have hletter : v[t] = a + b := by
    have hvstep := List.sum_take_succ v t hvt
    have hwstep := List.sum_take_succ w t ht
    change pref v (t + 1) = pref v t + v[t] at hvstep
    change pref w (t + 1) = pref w t + w[t] at hwstep
    rw [hnext, hpre] at hvstep
    rw [hmerge] at hwstep
    exact add_left_cancel (hvstep.symm.trans hwstep)
  obtain ⟨i, hhi, hik, hcol⟩ := hcollision
  have hI : pref w t + a ∈ interior w h k := mem_interior.mpr ⟨i, hhi, hik, hcol.symm⟩
  have hmiss : pref v t + a ∉ inventory v := by
    rw [hpre]
    have hh : pref w t + a ∈ inventory w \ inventory v := by rw [hremoved]; exact hI
    exact (Finset.mem_sdiff.mp hh).2
  have hvperm : v.Perm (compressed A a b).toList := hp.trans hw.1
  have hexperm := expansion_inventory A a b ha hb hab (fun hz => hr (Finset.mem_insert_of_mem hz))
    v hvperm hvt hletter
  have hexsum : (expandAt v t a b).sum = w.sum := by
    have hsplit := split_at v hvt
    rw [hletter] at hsplit
    have hss := congrArg List.sum hsplit
    simp only [List.sum_append, List.sum_cons] at hss
    simp only [expandAt, List.sum_append, List.sum_cons]
    rw [← hsum]
    change _ = v.sum
    rw [← hss]
    abel
  refine ⟨⟨hvperm, hg⟩, ?_, hpre, ⟨hvt, hletter⟩, hmiss,
    expansion_at_good v hg hvt a b hletter hmiss, hexperm, hexsum, ?_⟩
  · intro heq
    have hx := mem_inventory.mpr ⟨i, by omega, hcol.symm⟩
    have hn := hmiss
    rw [hpre] at hn
    change pref w t + a ∉ inventory (reverseBlock w h k) at hn
    rw [heq] at hn
    exact hn hx
  · intro x hx heq
    have hxA := Finset.mem_toList.mp (hexperm.mem_iff.mp hx)
    exact hA (heq ▸ hxA)

end D5.S1.Words.Sequenceability.SeparatedPrefixReflection
