/- GID: D5/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverUniversalSurvivors
   mirror-E: none(waiver:original-cyclic-universal-survivors)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Universal original-label cyclic noncover survivors follow from exact interval images, actual ordered suffix conjugacy and named critical-face readback. -/
import D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths

/-! UNCOMPILED SOURCE. All q>0, arbitrary finite ambient V and injection s.
The point is original s0. The independent families occur only inside an exact
complement-image calculation; the endpoint is the original remainingFaces. -/
noncomputable section
open Finset
namespace D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors
open FiniteCoordinateGreedyMatching FiniteGreedyFamilyTransport
open FiniteIndependentPathGreedy FiniteCyclicNoncoverCollapse
open FiniteCyclicNoncoverGreedyReduction FiniteCyclicNoncoverGreedyBranches
open FiniteCyclicNoncoverIntervalPaths
variable {V : Type*} [Fintype V] [DecidableEq V]

private def pinsA {n : Nat} (hn : 6 ≤ n) : Finset (Fin n) :=
  {⟨0, by omega⟩, ⟨1, by omega⟩}
private def pinsB {n : Nat} (hn : 6 ≤ n) : Finset (Fin n) :=
  {⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n-1, by omega⟩}

private theorem pinsA_outside {n : Nat} (hn : 6 ≤ n) :
    ∀ i ∈ pinsA hn, i.val < 3 ∨ 3+(n-4) ≤ i.val := by
  intro i hi
  simp only [pinsA, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> left <;> dsimp <;> omega
private theorem pinsB_outside {n : Nat} (hn : 6 ≤ n) :
    ∀ i ∈ pinsB hn, i.val < 4 ∨ 4+(n-6) ≤ i.val := by
  intro i hi
  simp only [pinsB, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> dsimp <;> omega

private theorem label_eq {n : Nat} (s : Fin n ↪ V) (i j : Fin n) :
    s i = s j ↔ i.val = j.val := by
  constructor
  · intro h; exact congrArg Fin.val (s.injective h)
  · intro h; exact congrArg s (Fin.ext h)

/-- C01-I: equality of actual finite families, not a predicate/cardinality
comparison. A's free zero-based indices are exactly 3,...,n-2. -/
private theorem branchA_image {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    branchA hn s = pinnedImage (by omega) s 3 (n-4) (pinsA hn) := by
  classical
  ext a
  rw [branchA_iff, pinnedImage_iff (by omega) s 3 (n-4) (by omega) _ (pinsA_outside hn)]
  constructor
  · rintro ⟨hs, hp, h1, h2, hl, hI⟩
    refine ⟨hs, ?_, ?_⟩
    · intro i hi
      simp only [pinsA, Finset.mem_insert, Finset.mem_singleton]
      have hv := i.isLt
      by_cases hi0 : i.val = 0
      · have he : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
        subst i
        simpa [point, pointIndex] using hp
      · by_cases hi1 : i.val = 1
        · have he : i = (⟨1, by omega⟩ : Fin n) := Fin.ext hi1
          subst i
          simp [h1]
        · have he : i.val = 2 ∨ i.val = n-1 := by omega
          rcases he with he | he
          · have he' : i = (⟨2, by omega⟩ : Fin n) := Fin.ext he
            subst i
            simp [h2]
          · have he' : i = (⟨n-1, by omega⟩ : Fin n) := Fin.ext he
            subst i
            simp [hl, show n-1 ≠ 0 by omega, show n-1 ≠ 1 by omega]
    · intro i hi hib
      exact hI i hi (by omega)
  · rintro ⟨hs, hpins, hI⟩
    have hp := (hpins ⟨0, by omega⟩ (Or.inl (by omega))).mpr (by simp [pinsA])
    have h1 := (hpins ⟨1, by omega⟩ (Or.inl (by omega))).mpr (by simp [pinsA])
    have h2 : s ⟨2, by omega⟩ ∈ a := by
      by_contra hh
      have hm := (hpins ⟨2, by omega⟩ (Or.inl (by omega))).mp hh
      simpa [pinsA] using hm
    have hl : s ⟨n-1, by omega⟩ ∈ a := by
      by_contra hh
      have hm := (hpins ⟨n-1, by omega⟩ (Or.inr (by omega))).mp hh
      simp only [pinsA, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm <;> have hv := congrArg Fin.val hm <;> dsimp at hv <;> omega
    exact ⟨hs, hp, h1, h2, hl, fun i hi hib => hI i hi (by omega)⟩

/-- C01-I: B's free indices are 4,...,n-3; at n=6 this is paths []. -/
private theorem branchB_image {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    branchB hn s = pinnedImage (by omega) s 4 (n-6) (pinsB hn) := by
  classical
  ext a
  rw [branchB_iff, pinnedImage_iff (by omega) s 4 (n-6) (by omega) _ (pinsB_outside hn)]
  constructor
  · rintro ⟨hs, hp, hl, h2, h1, h3, hprev, hI⟩
    refine ⟨hs, ?_, ?_⟩
    · intro i hi
      have hv := i.isLt
      by_cases hi0 : i.val = 0
      · have he : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
        subst i
        simpa [pinsB, point, pointIndex] using hp
      · by_cases hi2 : i.val = 2
        · have he : i = (⟨2, by omega⟩ : Fin n) := Fin.ext hi2
          subst i
          simp [pinsB, h2]
        · by_cases hil : i.val = n-1
          · have he : i = (⟨n-1, by omega⟩ : Fin n) := Fin.ext hil
            subst i
            simp [pinsB, hl]
          · have he : i.val = 1 ∨ i.val = 3 ∨ i.val = n-2 := by omega
            have hia : s i ∈ a := by
              rcases he with he | he | he
              · have he' : i = (⟨1, by omega⟩ : Fin n) := Fin.ext he
                simpa only [he'] using h1
              · have he' : i = (⟨3, by omega⟩ : Fin n) := Fin.ext he
                simpa only [he'] using h3
              · have he' : i = (⟨n-2, by omega⟩ : Fin n) := Fin.ext he
                simpa only [he'] using hprev
            have hin : i ∉ pinsB hn := by
              simp only [pinsB, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨fun hh => hi0 (congrArg Fin.val hh),
                fun hh => hi2 (congrArg Fin.val hh), fun hh => hil (congrArg Fin.val hh)⟩
            simp only [hia, not_true_eq_false, hin]
    · intro i hi hib
      exact hI i hi (by omega)
  · rintro ⟨hs, hpins, hI⟩
    have hp := (hpins ⟨0, by omega⟩ (Or.inl (by omega))).mpr (by simp [pinsB])
    have hl := (hpins ⟨n-1, by omega⟩ (Or.inr (by omega))).mpr (by simp [pinsB])
    have h2 := (hpins ⟨2, by omega⟩ (Or.inl (by omega))).mpr (by simp [pinsB])
    have hpos (i : Fin n) (hi : i.val = 1 ∨ i.val = 3 ∨ i.val = n-2) : s i ∈ a := by
      have hout : i.val < 4 ∨ 4+(n-6) ≤ i.val := by omega
      by_contra hh
      have hm := (hpins i hout).mp hh
      simp only [pinsB, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm <;> have hv := congrArg Fin.val hm <;> dsimp at hv <;> omega
    exact ⟨hs, hp, hl, h2, hpos _ (Or.inl rfl), hpos _ (Or.inr (Or.inl rfl)),
      hpos _ (Or.inr (Or.inr rfl)), fun i hi hib => hI i hi (by omega)⟩

/-- Every original suffix round is computed, not just the final family. -/
private theorem branchA_run {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    survivors (branchA hn s) (((List.finRange n).drop 2).map s) =
      if (n-4)%3 = 1 then ∅ else
        {complementMap s (pinsA hn ∪ pathChosen (intervalList (by omega) 3 (n-4)))} := by
  rw [branchA_image]
  exact survivors_pinnedImage (by omega) s 2 3 (n-4) (by omega) (by omega) _ (pinsA_outside hn)
private theorem branchB_run {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    survivors (branchB hn s) (((List.finRange n).drop 2).map s) =
      if (n-6)%3 = 1 then ∅ else
        {complementMap s (pinsB hn ∪ pathChosen (intervalList (by omega) 4 (n-6)))} := by
  rw [branchB_image]
  exact survivors_pinnedImage (by omega) s 2 4 (n-6) (by omega) (by omega) _ (pinsB_outside hn)

private theorem complement_mem {n : Nat} (s : Fin n ↪ V) (b : Finset (Fin n))
    (i : Fin n) : s i ∈ complementMap s b ↔ i ∉ b := by simp [complementMap]

private theorem supported_ext {n : Nat} (s : Fin n ↪ V) (a b : Finset V)
    (ha : a ⊆ ground s) (hb : b ⊆ ground s) (h : ∀ i, s i ∈ a ↔ s i ∈ b) : a = b := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, he⟩ := Finset.mem_map.mp (ha hv)
    exact he ▸ (h i).mp (he.symm ▸ hv)
  · intro hv
    obtain ⟨i, _, he⟩ := Finset.mem_map.mp (hb hv)
    exact he ▸ (h i).mpr (he.symm ▸ hv)
private theorem comp_supported {n : Nat} (s : Fin n ↪ V) (b : Finset (Fin n)) :
    complementMap s b ⊆ ground s := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
  exact spoke_mem_ground s i

/-- A at 3q reads back to the source's criticalB, not criticalA. -/
private theorem read_A_zero (q : Nat) (hq : 2 ≤ q) (s : Fin (3*q) ↪ V) :
    complementMap s (pinsA (by omega) ∪ pathChosen (intervalList (by omega) 3 (3*q-4))) =
      criticalB q (by omega) s := by
  apply supported_ext s _ _ (comp_supported s _) (criticalB_supported q (by omega) s)
  intro i
  rw [complement_mem, Finset.mem_union, mem_pathChosen_interval (by omega) 3 (3*q-4) (by omega),
    criticalB_formula]
  simp only [pinsA, Finset.mem_insert, Finset.mem_singleton]
  have he0 : i = (⟨0, by omega⟩ : Fin (3*q)) ↔ i.val = 0 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have he1 : i = (⟨1, by omega⟩ : Fin (3*q)) ↔ i.val = 1 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  rw [he0, he1]
  have hi := i.isLt
  constructor
  · intro h
    by_cases hl : i.val+1 = 3*q
    · exact Or.inl hl
    · right
      refine ⟨(i.val+1)/3, by omega, by omega, ?_⟩
      omega
  · rintro (hl | ⟨j, hj, hjq, he⟩) <;> omega

private theorem read_B_zero (q : Nat) (hq : 2 ≤ q) (s : Fin (3*q) ↪ V) :
    complementMap s (pinsB (by omega) ∪ pathChosen (intervalList (by omega) 4 (3*q-6))) =
      criticalA q (by omega) s := by
  apply supported_ext s _ _ (comp_supported s _) (criticalA_supported q (by omega) s)
  intro i
  rw [complement_mem, Finset.mem_union, mem_pathChosen_interval (by omega) 4 (3*q-6) (by omega),
    criticalA_formula]
  simp only [pinsB, Finset.mem_insert, Finset.mem_singleton]
  have he0 : i = (⟨0, by omega⟩ : Fin (3*q)) ↔ i.val = 0 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have he2 : i = (⟨2, by omega⟩ : Fin (3*q)) ↔ i.val = 2 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have hel : i = (⟨3*q-1, by omega⟩ : Fin (3*q)) ↔ i.val = 3*q-1 :=
    ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  rw [he0, he2, hel]
  have hi := i.isLt
  constructor
  · intro h
    by_cases h1 : i.val+1 = 2
    · exact Or.inl h1
    · right
      refine ⟨i.val/3, by omega, by omega, ?_⟩
      omega
  · rintro (h1 | ⟨j, hj, hjq, he⟩) <;> omega

private theorem read_A_one (q : Nat) (hq : 2 ≤ q) (s : Fin (3*q+1) ↪ V) :
    complementMap s (pinsA (by omega) ∪ pathChosen (intervalList (by omega) 3 (3*q+1-4))) =
      criticalOne q s := by
  apply supported_ext s _ _ (comp_supported s _) (criticalOne_supported q s)
  intro i
  rw [complement_mem, Finset.mem_union, mem_pathChosen_interval (by omega) 3 (3*q+1-4) (by omega),
    criticalOne_formula]
  simp only [pinsA, Finset.mem_insert, Finset.mem_singleton]
  have he0 : i = (⟨0, by omega⟩ : Fin (3*q+1)) ↔ i.val = 0 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have he1 : i = (⟨1, by omega⟩ : Fin (3*q+1)) ↔ i.val = 1 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  rw [he0, he1]
  have hi := i.isLt
  constructor
  · intro h
    refine ⟨(i.val+1)/3, by omega, by omega, ?_⟩
    omega
  · rintro ⟨j, hj, hjq, he⟩
    omega

private theorem read_B_two (q : Nat) (hq : 2 ≤ q) (s : Fin (3*q+2) ↪ V) :
    complementMap s (pinsB (by omega) ∪ pathChosen (intervalList (by omega) 4 (3*q+2-6))) =
      criticalTwo q (by omega) s := by
  apply supported_ext s _ _ (comp_supported s _) (criticalTwo_supported q (by omega) s)
  intro i
  rw [complement_mem, Finset.mem_union, mem_pathChosen_interval (by omega) 4 (3*q+2-6) (by omega),
    criticalTwo_formula]
  simp only [pinsB, Finset.mem_insert, Finset.mem_singleton]
  have he0 : i = (⟨0, by omega⟩ : Fin (3*q+2)) ↔ i.val = 0 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have he2 : i = (⟨2, by omega⟩ : Fin (3*q+2)) ↔ i.val = 2 := ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  have hel : i = (⟨3*q+2-1, by omega⟩ : Fin (3*q+2)) ↔ i.val = 3*q+2-1 :=
    ⟨fun h => congrArg Fin.val h, Fin.ext⟩
  rw [he0, he2, hel]
  have hi := i.isLt
  constructor
  · intro h
    by_cases h1 : i.val+1 = 2
    · exact Or.inl h1
    · by_cases hl : i.val+1 = 3*q+1
      · exact Or.inr (Or.inl hl)
      · right; right
        refine ⟨i.val/3, by omega, by omega, ?_⟩
        omega
  · rintro (h1 | hl | ⟨j, hj, hjq, he⟩) <;> omega

private theorem survivors_append (F : Finset (Finset V)) (xs ys : List V) :
    survivors F (xs ++ ys) = survivors (survivors F xs) ys := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => exact ih (remaining F x)

private theorem original_order {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    (List.finRange n).map s = point (by omega) s :: s ⟨1, by omega⟩ ::
      ((List.finRange n).drop 2).map s := by
  have he := List.take_append_drop 2 (List.finRange n)
  have ht : (List.finRange n).take 2 = [⟨0, by omega⟩, ⟨1, by omega⟩] := by
    have hi := (intervalList_source (show 0 < n by omega) 0 2 (by omega)).1
    rw [List.drop_zero] at hi
    rw [← hi, (intervalList_source (show 0 < n by omega) 0 2 (by omega)).2]
    rfl
  rw [← he, List.map_append, ht]
  rfl

private theorem suffix_avoids {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) (j : Fin n)
    (hj : j.val < 2) : s j ∉ ((List.finRange n).drop 2).map s := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
  have hij : i = j := s.injective he
  subst i
  have hlen : ((List.finRange n).drop 2).length = n-2 := by simp
  have hs : (List.finRange n).drop 2 =
      (List.finRange (n-2)).map (intervalEmbedding 2 (n-2) (by omega)) := by
    calc
      (List.finRange n).drop 2 = ((List.finRange n).drop 2).take (n-2) := by
        rw [← hlen, List.take_length]
      _ = intervalList (show 0 < n by omega) 2 (n-2) :=
        (intervalList_source (show 0 < n by omega) 2 (n-2) (by omega)).1.symm
      _ = _ := (intervalList_source (show 0 < n by omega) 2 (n-2) (by omega)).2
  rw [hs] at hi
  obtain ⟨i, _, he⟩ := List.mem_map.mp hi
  have hv := congrArg Fin.val he
  change 2+i.val = j.val at hv
  omega

private theorem singleton_survivors (a : Finset V) (vs : List V) :
    survivors ({a} : Finset (Finset V)) vs = {a} := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change survivors (remaining ({a} : Finset (Finset V)) v) vs = {a}
    have hf : remaining ({a} : Finset (Finset V)) v = {a} := by
      apply remaining_of_fixed
      by_cases hv : v ∈ a
      · left; intro b hb; have he := Finset.mem_singleton.mp hb; simpa only [he] using hv
      · right; intro b hb; have he := Finset.mem_singleton.mp hb; simpa only [he] using hv
    rw [hf, ih]

/-- Literal point plus two branch runs after the first two actual rounds. -/
private theorem split_original {n : Nat} (hn : 6 ≤ n) (s : Fin n ↪ V) :
    remainingFaces (by omega) s = insert {point (by omega) s}
      (survivors (branchA hn s) (((List.finRange n).drop 2).map s) ∪
        survivors (branchB hn s) (((List.finRange n).drop 2).map s)) := by
  classical
  let vs := ((List.finRange n).drop 2).map s
  unfold remainingFaces
  rw [original_order hn s]
  change survivors (remaining (remaining _ (point (by omega) s)) (s ⟨1, by omega⟩)) vs = _
  rw [second_original hn s]
  have hp0 : point (show 3 ≤ n by omega) s ∉ vs := suffix_avoids hn s _ (by dsimp [pointIndex]; omega)
  have h1 : s ⟨1, by omega⟩ ∉ vs := suffix_avoids hn s _ (by dsimp; omega)
  have hab : survivors (branchA hn s ∪ branchB hn s) vs =
      survivors (branchA hn s) vs ∪ survivors (branchB hn s) vs :=
    survivors_by_pin _ _ vs (s ⟨1, by omega⟩)
      (fun a ha => (branchA_fixed hn s ha).2.1)
      (fun a ha => (branchB_fixed hn s ha).2.2.2.1) h1
  have hsingle : survivors ({{point (show 3 ≤ n by omega) s}} : Finset (Finset V)) vs =
      {{point (by omega) s}} := singleton_survivors _ vs
  have hh := survivors_by_pin (branchA hn s ∪ branchB hn s)
    {{point (by omega) s}} vs (point (by omega) s)
    (by intro a ha; rcases Finset.mem_union.mp ha with ha | ha
        · exact (branchA_fixed hn s ha).1
        · exact (branchB_fixed hn s ha).1)
    (by intro a ha; have he := Finset.mem_singleton.mp ha; simp [he]) hp0
  simpa only [Finset.union_singleton, hsingle, hab] using hh

/-- C01 for every positive q in the exact original source telescope. -/
theorem remaining_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    remainingFaces (show 3 ≤ 3*q by omega) s =
      insert {point (by omega) s} {criticalA q hq s, criticalB q hq s} := by
  by_cases hq1 : q = 1
  · subst q; exact survivors_three s
  · have hq2 : 2 ≤ q := by omega
    rw [split_original (by omega) s, branchA_run, branchB_run]
    have ha : (3*q-4)%3 ≠ 1 := by omega
    have hb : (3*q-6)%3 ≠ 1 := by omega
    rw [if_neg ha, if_neg hb, read_A_zero q hq2 s, read_B_zero q hq2 s]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto

/-- C01 at 3q+1 retains the original criticalOne and original point only. -/
theorem remaining_one (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    remainingFaces (show 3 ≤ 3*q+1 by omega) s =
      insert {point (by omega) s} {criticalOne q s} := by
  by_cases hq1 : q = 1
  · subst q; exact survivors_four s
  · have hq2 : 2 ≤ q := by omega
    rw [split_original (by omega) s, branchA_run, branchB_run]
    have ha : (3*q+1-4)%3 ≠ 1 := by omega
    have hb : (3*q+1-6)%3 = 1 := by omega
    rw [if_neg ha, if_pos hb, read_A_one q hq2 s, Finset.union_empty]

/-- C01 at 3q+2 retains the original criticalTwo and original point only. -/
theorem remaining_two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    remainingFaces (show 3 ≤ 3*q+2 by omega) s =
      insert {point (by omega) s} {criticalTwo q hq s} := by
  by_cases hq1 : q = 1
  · subst q; exact survivors_five s
  · have hq2 : 2 ≤ q := by omega
    rw [split_original (by omega) s, branchA_run, branchB_run]
    have ha : (3*q+2-4)%3 = 1 := by omega
    have hb : (3*q+2-6)%3 ≠ 1 := by omega
    rw [if_pos ha, if_neg hb, read_B_two q hq2 s, Finset.empty_union]

end D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors
