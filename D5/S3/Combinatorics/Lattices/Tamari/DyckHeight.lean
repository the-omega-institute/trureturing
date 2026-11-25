/- GID: D5/S3/Combinatorics/Lattices/Tamari/DyckHeight
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/DyckHeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dyck height dominance has a unique coatom in the ranks with two Tamari coatoms. -/

/-
admission_basis: escape-witness (registered Dyck height comparison boundary)
Direct frozen dependencies: none.
proof_shape: near_ne_top: content; escape_witness: near_count
proof_shape: no_tamari_dyck_height_iso: content; escape_witness: no_tamari_dyck_height_iso
-/

import D5.S3.Combinatorics.Lattices.Tamari.MaximumFamilies
import Mathlib.Combinatorics.Enumerative.DyckWord

/-! # Dyck height dominance and its comparison with Tamari order -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Lattices.Tamari

open DyckStep

/-- Dyck words of the original semilength. -/
@[ext] structure DyckPaths (n : ℕ) where
  val : DyckWord
  property : val.semilength = n

private def upCount (p : DyckWord) (i : ℕ) : ℕ := (p.toList.take i).count U

/-- Vertical height after `i` steps (and height zero after the last step). -/
def dyckHeight (p : DyckWord) (i : ℕ) : ℤ :=
  ((p.toList.take i).count U : ℤ) - ((p.toList.take i).count D : ℤ)

private theorem count_both (l : List DyckStep) : l.count U + l.count D = l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp_all <;> omega

private theorem length_path {n : ℕ} (p : DyckPaths n) : p.val.toList.length = 2 * n :=
  p.val.two_mul_semilength_eq_length.symm.trans (congrArg (2 * ·) p.property)

private theorem dyckHeight_le_iff_upCount {n : ℕ} (p q : DyckPaths n) (i : ℕ) :
    dyckHeight p.val i ≤ dyckHeight q.val i ↔ upCount p.val i ≤ upCount q.val i := by
  have hp := count_both (p.val.toList.take i)
  have hq := count_both (q.val.toList.take i)
  rw [List.length_take, length_path] at hp hq
  unfold dyckHeight upCount
  omega

private theorem upCount_ext {n : ℕ} {p q : DyckPaths n}
    (h : ∀ i, upCount p.val i = upCount q.val i) : p = q := by
  apply DyckPaths.ext
  apply DyckWord.ext
  apply List.ext_getElem ((length_path p).trans (length_path q).symm)
  intro i hp hq
  have hi := h i
  have his := h (i + 1)
  unfold upCount at hi his
  rw [List.take_succ_eq_append_getElem hp, List.take_succ_eq_append_getElem hq,
    List.count_append, List.count_append] at his
  cases hp' : p.val.toList[i] <;> cases hq' : q.val.toList[i] <;>
    simp [hp', hq'] at his ⊢ <;> omega

instance dyckHeightOrder (n : ℕ) : PartialOrder (DyckPaths n) where
  le p q := ∀ i, dyckHeight p.val i ≤ dyckHeight q.val i
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ i := (h₁ i).trans (h₂ i)
  le_antisymm p q h₁ h₂ := upCount_ext fun i =>
    le_antisymm ((dyckHeight_le_iff_upCount p q i).mp (h₁ i))
      ((dyckHeight_le_iff_upCount q p i).mp (h₂ i))

private theorem path_le_iff {n : ℕ} {p q : DyckPaths n} :
    p ≤ q ↔ ∀ i, upCount p.val i ≤ upCount q.val i :=
  forall_congr' (dyckHeight_le_iff_upCount p q)

private theorem upCount_bound {n : ℕ} (p : DyckPaths n) (i : ℕ) :
    upCount p.val i ≤ min i n := by
  apply le_min
  · exact List.count_le_length.trans (by simp)
  · exact ((List.take_sublist i p.val.toList).count_le U).trans_eq p.property

private theorem upCount_mono (p : DyckWord) {i j : ℕ} (h : i ≤ j) :
    upCount p i ≤ upCount p j :=
  (List.take_sublist_take_left h).count_le U

private theorem upCount_growth (p : DyckWord) {i j : ℕ} (h : i ≤ j) :
    upCount p j ≤ upCount p i + (j - i) := by
  let l := p.toList.take j
  have he := l.take_append_drop i
  change l.count U ≤ _
  conv_lhs => rw [← he, List.count_append]
  have hb : (l.drop i).count U ≤ j - i := List.count_le_length.trans (by
    dsimp only [l]
    rw [List.length_drop, List.length_take]
    omega)
  have ht : l.take i = p.toList.take i := by simp [l, List.take_take, min_eq_left h]
  rw [ht]
  exact Nat.add_le_add_left hb _

private def surround (p : DyckWord) (k : ℕ) : DyckWord :=
  match k with
  | 0 => p
  | k + 1 => (surround p k).nest

private theorem surround_list (p : DyckWord) (k : ℕ) :
    (surround p k).toList = List.replicate k U ++ p.toList ++ List.replicate k D := by
  induction k with
  | zero => simp [surround]
  | succ k ih =>
    change [U] ++ (surround p k).toList ++ [D] = _
    rw [ih, List.replicate_succ, List.replicate_succ']
    simp [List.append_assoc]

private theorem surround_size (p : DyckWord) (k : ℕ) :
    (surround p k).semilength = p.semilength + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [surround, DyckWord.semilength_nest, ih, Nat.add_assoc]

/-- The path with all up-steps before all down-steps. -/
private def mountain (n : ℕ) : DyckPaths n :=
  ⟨surround 0 n, by simp [surround_size]⟩

private theorem mountain_count (n i : ℕ) : upCount (mountain n).val i = min i n := by
  change ((surround 0 n).toList.take i).count U = _
  rw [surround_list]
  change ((List.replicate n U ++ [] ++ List.replicate n D).take i).count U = _
  simp [List.take_append, List.count_replicate]

instance dyckOrderTop (n : ℕ) : OrderTop (DyckPaths n) where
  top := mountain n
  le_top p := path_le_iff.mpr fun i => by
    rw [mountain_count]
    exact upCount_bound p i

private def nearBase : DyckWord := (0 : DyckWord).nest + (0 : DyckWord).nest

/-- The mountain with the two central steps exchanged. -/
def nearMountain (k : ℕ) : DyckPaths (k + 2) :=
  ⟨surround nearBase k, by simp [surround_size, nearBase]; omega⟩

private theorem near_list (k : ℕ) :
    (nearMountain k).val.toList =
      List.replicate (k + 1) U ++ [D,U] ++ List.replicate (k + 1) D := by
  change (surround nearBase k).toList = _
  rw [surround_list, List.replicate_succ', List.replicate_succ]
  change List.replicate k U ++ [U,D,U,D] ++ List.replicate k D = _
  simp [List.append_assoc]

private theorem near_count (k i : ℕ) :
    upCount (nearMountain k).val i = if i = k + 2 then k + 1 else min i (k + 2) := by
  have hc (j : ℕ) : (([D,U] ++ List.replicate (k + 1) D).take j).count U =
      if 2 ≤ j then 1 else 0 := by
    rw [List.take_append, List.count_append, List.take_replicate]
    have hz (m : ℕ) : (List.replicate m D).count U = 0 := by simp [List.count_replicate]
    rw [hz, Nat.add_zero]
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j => simp
  unfold upCount
  rw [near_list, List.append_assoc, List.take_append, List.count_append,
    List.take_replicate, List.count_replicate_self, List.length_replicate, hc]
  by_cases h : i ≤ k + 1
  · rw [min_eq_left h, min_eq_left (h.trans (Nat.le_succ _)),
      ite_eq_right (show i ≠ k + 2 by omega), ite_eq_right (show ¬ 2 ≤ i - (k + 1) by omega)]
    omega
  · rw [min_eq_right (show k + 1 ≤ i by omega), min_eq_right (show k + 2 ≤ i by omega)]
    split <;> split <;> omega

theorem near_ne_top (k : ℕ) : nearMountain k ≠ (⊤ : DyckPaths (k + 2)) := by
  intro h
  have he := congrArg (fun p : DyckPaths (k + 2) => upCount p.val (k + 2)) h
  change upCount (nearMountain k).val (k + 2) = upCount (mountain (k + 2)).val (k + 2) at he
  rw [near_count, ite_eq_left rfl, mountain_count, min_self] at he
  omega

private theorem middle_full_eq_top {n : ℕ} {p : DyckPaths n} (h : upCount p.val n = n) :
    p = ⊤ := by
  apply upCount_ext
  intro i
  change upCount p.val i = upCount (mountain n).val i
  rw [mountain_count]
  apply le_antisymm (upCount_bound _ _)
  by_cases hi : i ≤ n
  · rw [min_eq_left hi]
    have hg := upCount_growth p.val hi
    omega
  · rw [min_eq_right (by omega)]
    have hm := upCount_mono p.val (show n ≤ i by omega)
    rwa [h] at hm

private theorem proper_dyck_le_near (k : ℕ) {p : DyckPaths (k + 2)} (h : p ≠ ⊤) :
    p ≤ nearMountain k := by
  apply path_le_iff.mpr
  intro i
  rw [near_count]
  by_cases he : i = k + 2
  · subst i
    rw [ite_eq_left rfl]
    have hb := upCount_bound p (k + 2)
    rw [min_self] at hb
    have hlt : upCount p.val (k + 2) < k + 2 :=
      lt_of_le_of_ne hb (fun he => h (middle_full_eq_top he))
    omega
  · rw [ite_eq_right he]
    exact upCount_bound _ _

private theorem dyck_coatom_eq (k : ℕ) {p : DyckPaths (k + 2)} (hp : IsCoatom p) :
    p = nearMountain k := by
  have hle := proper_dyck_le_near k hp.1
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hp).2 _ (near_ne_top k) hle)

theorem no_tamari_dyck_height_iso (n : ℕ) (hn : 3 ≤ n) :
    ¬ Nonempty (Trees n ≃o DyckPaths n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rintro ⟨e⟩
  obtain ⟨a, b, ha, hb, hne⟩ := tamari_two_coatoms (k + 1) (by omega)
  have ha' := dyck_coatom_eq k ((e.isCoatom_iff a).2 ha)
  have hb' := dyck_coatom_eq k ((e.isCoatom_iff b).2 hb)
  exact hne (e.injective (ha'.trans hb'.symm))

end D5.S3.Combinatorics.Lattices.Tamari
