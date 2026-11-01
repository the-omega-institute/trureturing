/- GID: D5/S3/Geometry/Polygons/PolygonCompressionTrace
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonCompressionTrace
   mirror-E: none(waiver:general-structural-theorem)
   anchors: []
   utility: none
   digest: Actual cyclic ear traces and complete conditioned-fibre deletion partitions. -/

import D5.S3.Geometry.Polygons.PolygonEarSlideCardinality
import D5.S3.Combinatorics.SetFamily.SimultaneousCompression

/-! Complete actual traces under cyclic coordinate deletion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Polygons.PolygonCompressionTrace
open Finset PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual
open D5.S3.Combinatorics.SetFamily.SimultaneousCompression

variable {n : ℕ} [NeZero n]

/-- No consecutive centres in the cyclic order. -/
def Independent (H : Finset (ZMod n)) : Prop := ∀ i ∈ H, i + 1 ∉ H

/-- All independent subsets, including traces with no triangulation completion. -/
noncomputable def feasible (H : Finset (ZMod n)) : Finset (Finset (ZMod n)) := by
  classical
  exact H.powerset.filter Independent

/-- The raw cardinality of the entire conditioned triangulation fibre. -/
noncomputable def weight (P Q H X : Finset (ZMod n)) : ℝ :=
  Nat.card (ConditionFiber P Q H X)

@[simp] theorem mem_feasible {H X : Finset (ZMod n)} :
    X ∈ feasible H ↔ X ⊆ H ∧ Independent X := by
  classical
  simp [feasible]

omit [NeZero n] in
theorem independent_subset {H X : Finset (ZMod n)} (hH : Independent H)
    (hX : X ⊆ H) : Independent X := by
  intro i hi hn
  exact hH i (hX hi) (hX hn)

theorem cross_ear_iff_adjacent (hn : 6 ≤ n) (i j : ZMod n) :
    Cross (ear i) (ear j) ↔ j = i + 1 ∨ i = j + 1 := by
  constructor
  · intro h
    have hshift : Cross (ear (1 : ZMod n)) (ear (j + (1 - i))) := by
      have hs := (cross_ear_shift_iff (i := i) (j := j) (a := 1 - i)).mpr h
      simpa only [show i + (1 - i) = 1 by ring] using hs
    obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn hshift
    change s(j + (1 - i) - 1, j + (1 - i) + 1) = s(1, x) at hx
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨hleft, _⟩ | ⟨_, hright⟩
    · left
      calc
        j = (j + (1 - i) - 1) + i := by ring
        _ = 1 + i := congrArg (fun z : ZMod n => z + i) hleft
        _ = i + 1 := add_comm _ _
    · right
      calc
        i = 1 - (j + (1 - i) + 1) + (j + 1) := by ring
        _ = 1 - 1 + (j + 1) :=
          congrArg (fun z : ZMod n => 1 - z + (j + 1)) hright
        _ = j + 1 := by ring
  · have h01 : Cross (ear (0 : ZMod n)) (ear 1) := by
      simpa only [sEar, e₀] using cross_symm (local_crossings hn).2.2
    have hnext (k : ZMod n) : Cross (ear k) (ear (k + 1)) := by
      have hs := (cross_ear_shift_iff (i := 0) (j := 1) (a := k)).mpr h01
      simpa only [zero_add, add_zero, add_comm] using hs
    rintro (h | h)
    · subst j
      exact hnext i
    · subst i
      exact cross_symm (hnext j)

theorem earCenters_independent (hn : 6 ≤ n)
    {T : Finset (Sym2 (ZMod n))} (hT : IsTriangulation T) :
    Independent (EarCenters T) := by
  intro i hi hnext
  exact hT.noncrossing (ear i) (mem_earCenters.mp hi)
    (ear (i + 1)) (mem_earCenters.mp hnext)
    ((cross_ear_iff_adjacent hn i (i + 1)).mpr (Or.inl rfl))

theorem block_start
    (H : Finset (ZMod n)) (hproper : H ≠ Finset.univ) :
    (∃ b, b ∈ H ∧ b + 1 ∈ H) →
      ∃ a, a ∉ H ∧ a + 1 ∈ H ∧ a + 2 ∈ H := by
  classical
  rintro ⟨b, hb, hb1⟩
  by_contra hnone
  have hpred (a : ZMod n) (ha1 : a + 1 ∈ H) (ha2 : a + 2 ∈ H) : a ∈ H := by
    by_contra ha
    exact hnone ⟨a, ha, ha1, ha2⟩
  have hback : ∀ k : ℕ, b - (k : ZMod n) ∈ H ∧ b + 1 - (k : ZMod n) ∈ H := by
    intro k
    induction k with
    | zero => simpa using And.intro hb hb1
    | succ k ih =>
        have hprev : b - (k : ZMod n) - 1 ∈ H := by
          refine hpred (b - (k : ZMod n) - 1) ?_ ?_
          · have heq : b - (k : ZMod n) - 1 + 1 = b - (k : ZMod n) := by ring
            rw [heq]
            exact ih.1
          · have heq : b - (k : ZMod n) - 1 + 2 = b + 1 - (k : ZMod n) := by ring
            rw [heq]
            exact ih.2
        constructor
        · simpa only [Nat.cast_succ, sub_add_eq_sub_sub] using hprev
        · have heq : b + 1 - ((k + 1 : ℕ) : ZMod n) = b - (k : ZMod n) := by
            rw [Nat.cast_succ]
            ring
          rw [heq]
          exact ih.1
  apply hproper
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  have hz := (hback (b - z).val).1
  have heq : b - ((b - z).val : ZMod n) = z := by
    rw [ZMod.natCast_zmod_val]
    ring
  rwa [heq] at hz

theorem trace_mem_feasible (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (H : Finset (ZMod n)) :
    EarCenters T ∩ H ∈ feasible H :=
  mem_feasible.mpr ⟨inter_subset_right, independent_subset
    (earCenters_independent hn hT) inter_subset_left⟩

theorem weight_zero_of_not_feasible (hn : 6 ≤ n)
    (P Q H X : Finset (ZMod n)) (hX : X ∉ feasible H) : weight P Q H X = 0 := by
  have : IsEmpty (ConditionFiber P Q H X) := ⟨fun T =>
    hX (T.2.2.2.2 ▸ trace_mem_feasible hn T.2.1 H)⟩
  have hz : Nat.card (ConditionFiber P Q H X) = 0 := Nat.card_eq_zero.mpr (Or.inl ‹_›)
  exact_mod_cast hz

theorem feasible_projection (H : Finset (ZMod n)) (t : ZMod n) :
    (feasible H).image (fun X => X.erase t) = feasible (H.erase t) := by
  classical
  ext R
  constructor
  · rintro h
    obtain ⟨X, hX, rfl⟩ := mem_image.mp h
    obtain ⟨hXH, hXI⟩ := mem_feasible.mp hX
    exact mem_feasible.mpr ⟨erase_subset_erase t hXH,
      independent_subset hXI (erase_subset t X)⟩
  · intro hR
    obtain ⟨hRH, hRI⟩ := mem_feasible.mp hR
    have ht : t ∉ R := fun h => (mem_erase.mp (hRH h)).1 rfl
    exact mem_image.mpr ⟨R, mem_feasible.mpr
      ⟨hRH.trans (erase_subset t H), hRI⟩, erase_eq_of_notMem ht⟩

/-- Deleting an observation partitions all original triangulations by that ear. -/
theorem condition_fibre_card_delete (P Q H R : Finset (ZMod n)) (t : ZMod n)
    (htH : t ∈ H) (htR : t ∉ R) :
    Nat.card (ConditionFiber P Q (H.erase t) R) =
      Nat.card (ConditionFiber P Q H R) + Nat.card (ConditionFiber P Q H (insert t R)) := by
  classical
  let F := ConditionFiber P Q (H.erase t) R
  let A := ConditionFiber P Q H R
  let B := ConditionFiber P Q H (insert t R)
  have full (x : F) : EarCenters x.1 ∩ H =
      if t ∈ EarCenters x.1 then insert t R else R := by
    ext i
    have hi := Finset.ext_iff.mp x.2.2.2.2 i
    simp only [mem_inter, mem_erase] at hi
    split_ifs with ht
    · simp only [mem_inter, mem_insert]
      by_cases hit : i = t <;> subst_vars <;> simp_all
    · simp only [mem_inter]
      by_cases hit : i = t <;> subst_vars <;> simp_all
  have reduce (T : Finset (Sym2 (ZMod n)))
      (h : EarCenters T ∩ H = R ∨ EarCenters T ∩ H = insert t R) :
      EarCenters T ∩ H.erase t = R := by
    ext i
    rcases h with h | h
    all_goals
      have hi := Finset.ext_iff.mp h i
      simp only [mem_inter, mem_insert] at hi
      simp only [mem_inter, mem_erase]
      by_cases hit : i = t <;> subst_vars <;> simp_all
  let eA : {x : F // t ∉ EarCenters x.1} ≃ A :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1,
        by simpa [x.2] using full x.1⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
        reduce x.1 (Or.inl x.2.2.2.2)⟩, fun ht =>
          htR (x.2.2.2.2 ▸ mem_inter.mpr ⟨ht, htH⟩)⟩
      left_inv := fun _ => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun _ => Subtype.ext rfl }
  let eB : {x : F // ¬t ∉ EarCenters x.1} ≃ B :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1,
        by simpa [not_not.mp x.2] using full x.1⟩
      invFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
        reduce x.1 (Or.inr x.2.2.2.2)⟩, fun ht => ht
          (mem_inter.mp ((Finset.ext_iff.mp x.2.2.2.2 t).mpr (by simp))).1⟩
      left_inv := fun _ => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun _ => Subtype.ext rfl }
  have : Finite A := by dsimp [A, ConditionFiber]; infer_instance
  have : Finite B := by dsimp [B, ConditionFiber]; infer_instance
  rw [← Nat.card_sum, ← Nat.card_congr (Equiv.sumCongr eA eB)]
  exact (Nat.card_congr (Equiv.sumCompl (fun x : F => t ∉ EarCenters x.1))).symm

/-- The feasible projection fibre has the unchanged trace and its feasible extension. -/
theorem marginal_weight (hn : 6 ≤ n) (P Q H R : Finset (ZMod n)) (t : ZMod n)
    (htH : t ∈ H) (hR : R ∈ feasible (H.erase t)) :
    marginalWeight (feasible H) (weight P Q H) t R = weight P Q (H.erase t) R := by
  classical
  obtain ⟨hRH, hRI⟩ := mem_feasible.mp hR
  have htR : t ∉ R := fun h => (mem_erase.mp (hRH h)).1 rfl
  have hRf : R ∈ feasible H := mem_feasible.mpr
    ⟨hRH.trans (erase_subset t H), hRI⟩
  have hf : (feasible H).filter (fun X => X.erase t = R) =
      insert R (if insert t R ∈ feasible H then {insert t R} else ∅) := by
    ext X
    have cases (he : X.erase t = R) : X = R ∨ X = insert t R := by
      by_cases htX : t ∈ X
      · right
        rw [← he, insert_erase htX]
      · left
        simpa [erase_eq_of_notMem htX] using he
    by_cases hi : insert t R ∈ feasible H
    · simp only [hi, ite_true, mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨_, he⟩
        exact cases he
      · rintro (rfl | rfl)
        · exact ⟨hRf, erase_eq_of_notMem htR⟩
        · exact ⟨hi, by simp [htR]⟩
    · simp only [hi, ite_false, insert_empty_eq, mem_filter, mem_singleton]
      constructor
      · rintro ⟨hX, he⟩
        rcases cases he with h | h
        · exact h
        · exact False.elim (hi (h ▸ hX))
      · rintro rfl
        exact ⟨hRf, erase_eq_of_notMem htR⟩
  unfold marginalWeight
  rw [hf, sum_insert]
  · have hc := condition_fibre_card_delete P Q H R t htH htR
    have hcr : weight P Q (H.erase t) R = weight P Q H R + weight P Q H (insert t R) := by
      unfold weight
      exact_mod_cast hc
    rw [hcr]
    congr 1
    split_ifs with hi
    · simp
    · simp [weight_zero_of_not_feasible hn P Q H (insert t R) hi]
  · split_ifs
    · simp only [mem_singleton]
      intro he
      exact htR (he ▸ mem_insert_self t R)
    · simp

/-- A nonempty excluded set makes every allowed support proper. -/
theorem proper_of_subset_EK {K H : Finset (ZMod n)} (hK : K.Nonempty)
    (hH : H ⊆ E_K K) : H ≠ univ := by
  obtain ⟨k, hk⟩ := hK
  intro he
  have h := (mem_filter.mp (hH (he ▸ mem_univ k))).2.1
  exact h hk

theorem feasible_of_independent {H : Finset (ZMod n)} (hH : Independent H) :
    feasible H = H.powerset := by
  classical
  ext X
  simp only [mem_feasible, mem_powerset]
  exact ⟨And.left, fun h => ⟨h, independent_subset hH h⟩⟩

end D5.S3.Geometry.Polygons.PolygonCompressionTrace
