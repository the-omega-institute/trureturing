/- GID: D5/S3/Geometry/FiniteCyclicNoncoverIntervalPaths
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverIntervalPaths
   mirror-E: none(waiver:original-cyclic-interval-transport)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Exact original-index interval images and every ordered greedy round commute with fixed pins and original-ground complementation. -/
import D5.S3.Geometry.FiniteCyclicNoncoverGreedyBranches

/-! UNCOMPILED SOURCE. Empty intervals mean the augmented family {∅}.
The index list below is a literal drop/take of the original finRange; neither
ambient vertices nor native faces are added. -/
noncomputable section
open Finset
namespace D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
open FiniteCoordinateGreedyMatching FiniteGreedyFamilyTransport
open FiniteIndependentPathGreedy FiniteCyclicNoncoverCollapse
open FiniteCyclicNoncoverGreedyBranches
variable {V : Type*} [Fintype V] [DecidableEq V]

private def segment {T : Type*} (f : Nat → T) (lo : Nat) : Nat → List T
  | 0 => []
  | m+1 => f lo :: segment f (lo+1) m

private theorem segment_length {T : Type*} (f : Nat → T) (lo m : Nat) :
    (segment f lo m).length = m := by
  induction m generalizing lo with
  | zero => rfl
  | succ m ih => simp only [segment, List.length_cons, ih]

private theorem segment_get {T : Type*} (f : Nat → T) (lo m i : Nat) (hi : i < m) :
    (segment f lo m)[i]'(by rw [segment_length]; exact hi) = f (lo+i) := by
  induction m generalizing lo i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => simp [segment]
    | succ i => simpa only [segment, List.getElem_cons_succ, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih (lo+1) i (by omega)

private theorem segment_mem {T : Type*} (f : Nat → T) (lo m : Nat) (x : T) :
    x ∈ segment f lo m ↔ ∃ j, j < m ∧ f (lo+j) = x := by
  induction m generalizing lo with
  | zero => simp [segment]
  | succ m ih =>
    simp only [segment, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · exact ⟨j+1, by omega, by congr 1 <;> omega⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact Or.inl (by simpa using he.symm)
      | succ j => exact Or.inr ⟨j, by omega, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he⟩

private theorem segment_append {T : Type*} (f : Nat → T) (lo a b : Nat) :
    segment f lo (a+b) = segment f lo a ++ segment f (lo+a) b := by
  induction a generalizing lo with
  | zero => simp [segment]
  | succ a ih => simpa [segment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (List.cons (f lo)) (ih (lo+1))

private theorem segment_drop {T : Type*} (f : Nat → T) (lo m k : Nat) :
    (segment f lo m).drop k = segment f (lo+k) (m-k) := by
  induction k generalizing lo m with
  | zero => simp
  | succ k ih =>
    cases m with
    | zero => simp [segment]
    | succ m => simpa [segment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (lo+1) m

private theorem segment_take {T : Type*} (f : Nat → T) (lo m k : Nat) (hk : k ≤ m) :
    (segment f lo m).take k = segment f lo k := by
  induction k generalizing lo m with
  | zero => simp [segment]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m => simpa only [segment, List.take_succ_cons] using
        congrArg (List.cons (f lo)) (ih (lo+1) m (by omega))

private def index {n : Nat} (hn : 0 < n) (i : Nat) : Fin n :=
  ⟨i % n, Nat.mod_lt _ hn⟩

/-- The actual increasing embedding of a bounded original-index interval. -/
def intervalEmbedding {n : Nat} (lo m : Nat) (h : lo+m ≤ n) : Fin m ↪ Fin n where
  toFun i := ⟨lo+i.val, by have hi := i.isLt; omega⟩
  inj' := by intro i j he; apply Fin.ext; have hh := congrArg Fin.val he; dsimp at hh; omega

/-- Exact original Fin n labels; the m=0 list is empty, with no endpoint. -/
def intervalList {n : Nat} (hn : 0 < n) (lo m : Nat) : List (Fin n) :=
  segment (index hn) lo m

private theorem interval_length {n : Nat} (hn : 0 < n) (lo m : Nat) :
    (intervalList hn lo m).length = m := segment_length _ _ _

private theorem full_interval {n : Nat} (hn : 0 < n) :
    List.finRange n = intervalList hn 0 n := by
  apply List.ext_getElem
  · simp [intervalList, segment_length]
  · intro i hi hj
    have hi' : i < n := by simpa using hi
    simp only [List.getElem_finRange, intervalList, segment_get]
    apply Fin.ext
    simp [index, Nat.mod_eq_of_lt hi']

private theorem interval_mem {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n)
    (i : Fin n) : i ∈ intervalList hn lo m ↔ lo ≤ i.val ∧ i.val < lo+m := by
  rw [intervalList, segment_mem]
  constructor
  · rintro ⟨j, hj, he⟩
    have hjn : lo+j < n := by omega
    have hv := congrArg Fin.val he
    simp only [index, Nat.mod_eq_of_lt hjn] at hv
    omega
  · rintro ⟨hl, hu⟩
    refine ⟨i.val-lo, by omega, ?_⟩
    apply Fin.ext
    have he : lo+(i.val-lo) = i.val := by omega
    simp [index, he, Nat.mod_eq_of_lt i.isLt]

private theorem interval_nodup {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) :
    (intervalList hn lo m).Nodup := by
  induction m generalizing lo with
  | zero => simp [intervalList, segment]
  | succ m ih =>
    change (index hn lo :: intervalList hn (lo+1) m).Nodup
    refine List.nodup_cons.mpr ⟨?_, ih (lo+1) (by omega)⟩
    intro hm
    have hh := (interval_mem hn (lo+1) m (by omega) _).mp hm
    have hv : (index hn lo).val = lo := Nat.mod_eq_of_lt (by omega)
    rw [hv] at hh
    omega

/-- Both exact list representations, including empty tails and n=6. -/
theorem intervalList_source {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n) :
    intervalList hn lo m = ((List.finRange n).drop lo).take m ∧
    intervalList hn lo m = (List.finRange m).map (intervalEmbedding lo m h) := by
  constructor
  · rw [full_interval hn]
    simp only [intervalList, segment_drop, Nat.zero_add]
    exact (segment_take _ lo (n-lo) m (by omega)).symm
  · apply List.ext_getElem
    · simp [interval_length]
    · intro j hj hk
      have hj' : j < m := by simpa [interval_length] using hj
      simp only [intervalList, segment_get, List.getElem_map, List.getElem_finRange]
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)

private theorem independent_segment {T : Type*} [Fintype T] [DecidableEq T]
    (f : Nat → T) (lo m : Nat) (a : Finset T) :
    IndependentAlong (segment f lo m) a ↔
      ∀ j, j+1 < m → f (lo+j) ∉ a ∨ f (lo+j+1) ∉ a := by
  induction m generalizing lo with
  | zero => simp [segment, IndependentAlong]
  | succ m ih =>
    cases m with
    | zero => simp [segment, IndependentAlong]
    | succ m =>
      change ((f lo ∉ a ∨ f (lo+1) ∉ a) ∧
        IndependentAlong (segment f (lo+1) (m+1)) a) ↔ _
      rw [ih]
      constructor
      · rintro ⟨h0, ht⟩ j hj
        cases j with
        | zero => simpa using h0
        | succ j => simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ht j (by omega)
      · intro h
        refine ⟨by simpa using h 0 (by omega), ?_⟩
        intro j hj
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (j+1) (by omega)

private theorem independent_interval {n : Nat} (hn : 0 < n) (lo m : Nat)
    (h : lo+m ≤ n) (a : Finset (Fin n)) :
    IndependentAlong (intervalList hn lo m) a ↔
      ∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m →
        i ∉ a ∨ successor hn i ∉ a := by
  rw [intervalList, independent_segment]
  constructor
  · intro hI i hi hib
    have hh := hI (i.val-lo) (by omega)
    have he : index hn (lo+(i.val-lo)) = i := by
      apply Fin.ext
      have he' : lo+(i.val-lo) = i.val := by omega
      simp [index, he', Nat.mod_eq_of_lt i.isLt]
    have hs : index hn (lo+(i.val-lo)+1) = successor hn i := by
      apply Fin.ext
      have he' : lo+(i.val-lo)+1 = i.val+1 := by omega
      simp only [index, successor, he']
    simpa only [he, hs] using hh
  · intro hI j hj
    have hjn : lo+j < n := by omega
    have hjn' : lo+j+1 < n := by omega
    have hi : (index hn (lo+j)).val = lo+j := Nat.mod_eq_of_lt hjn
    have hs : successor hn (index hn (lo+j)) = index hn (lo+j+1) := by
      apply Fin.ext
      simp only [successor, index, Nat.mod_eq_of_lt hjn, Nat.mod_eq_of_lt hjn']
    simpa only [hs] using hI (index hn (lo+j)) (by rw [hi]; omega) (by rw [hi]; omega)

/-- Support AND actual-successor independence characterize the whole family. -/
theorem mem_paths_interval {n : Nat} (hn : 0 < n) (lo m : Nat) (h : lo+m ≤ n)
    (a : Finset (Fin n)) :
    a ∈ paths (intervalList hn lo m) ↔
      (∀ i ∈ a, lo ≤ i.val ∧ i.val < lo+m) ∧
      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m → i ∉ a ∨ successor hn i ∉ a) := by
  rw [mem_paths_iff _ (interval_nodup hn lo m h), independent_interval hn lo m h]
  exact and_congr (forall_congr' fun i => imp_congr_right fun _ => interval_mem hn lo m h i) Iff.rfl

private theorem chosen_segment {T : Type*} [Fintype T] [DecidableEq T]
    (f : Nat → T) (lo m : Nat) (x : T) :
    x ∈ pathChosen (segment f lo m) ↔ ∃ j, 3*j+1 < m ∧ x = f (lo+3*j+1) := by
  induction m using Nat.strong_induction_on generalizing lo with
  | h m ih =>
    cases m with
    | zero => simp [segment, pathChosen]
    | succ m =>
      cases m with
      | zero => simp [segment, pathChosen]; omega
      | succ m =>
        cases m with
        | zero =>
          simp only [segment, pathChosen, Finset.mem_singleton]
          constructor
          · intro he; exact ⟨0, by omega, by simpa using he⟩
          · rintro ⟨j, hj, he⟩; have : j = 0 := by omega; simpa [this] using he
        | succ m =>
          change x ∈ insert (f (lo+1)) (pathChosen (segment f (lo+3) m)) ↔ _
          rw [Finset.mem_insert, ih m (by omega)]
          constructor
          · rintro (he | ⟨j, hj, he⟩)
            · exact ⟨0, by omega, by simpa using he⟩
            · exact ⟨j+1, by omega, by convert he using 1 <;> congr 1 <;> omega⟩
          · rintro ⟨j, hj, he⟩
            cases j with
            | zero => exact Or.inl (by simpa using he)
            | succ j => exact Or.inr ⟨j, by omega,
                by convert he using 1 <;> congr 1 <;> omega⟩

/-- Readback in original ZERO-based indices, with no congruence assumption. -/
theorem mem_pathChosen_interval {n : Nat} (hn : 0 < n) (lo m : Nat)
    (h : lo+m ≤ n) (i : Fin n) :
    i ∈ pathChosen (intervalList hn lo m) ↔
      lo+1 ≤ i.val ∧ i.val < lo+m ∧ (i.val-lo) % 3 = 1 := by
  rw [intervalList, chosen_segment]
  constructor
  · rintro ⟨j, hj, he⟩
    have hjn : lo+3*j+1 < n := by omega
    have hv := congrArg Fin.val he
    simp only [index, Nat.mod_eq_of_lt hjn] at hv
    omega
  · rintro ⟨hl, hu, hm⟩
    refine ⟨(i.val-lo)/3, by omega, ?_⟩
    apply Fin.ext
    have he : lo+3*((i.val-lo)/3)+1 = i.val := by omega
    simp [index, he, Nat.mod_eq_of_lt i.isLt]

/-- An inserted independent subset followed by ORIGINAL-ground complement. -/
def pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)
    (S : Finset (Fin n)) : Finset (Finset V) :=
  (paths (intervalList hn lo m)).image (fun b => complementMap s (S ∪ b))

private theorem complement_label {n : Nat} (s : Fin n ↪ V) (b : Finset (Fin n))
    (i : Fin n) : s i ∈ complementMap s b ↔ i ∉ b := by
  simp [complementMap]

private theorem complement_supported {n : Nat} (s : Fin n ↪ V) (b : Finset (Fin n)) :
    complementMap s b ⊆ ground s := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
  exact spoke_mem_ground s i

private theorem complement_inverse {n : Nat} (s : Fin n ↪ V) (a : Finset V)
    (ha : a ⊆ ground s) :
    complementMap s (Finset.univ.filter fun i => s i ∉ a) = a := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    have hh := (Finset.mem_sdiff.mp hi).2
    by_contra hn
    exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  · intro hv
    obtain ⟨i, _, he⟩ := Finset.mem_map.mp (ha hv)
    refine Finset.mem_map.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    intro hi
    exact (Finset.mem_filter.mp hi).2 (he.symm ▸ hv)

/-- Exact FAMILY equality criterion. The fixed mask is disjoint from the
free interval; empty free tails require all outside-coordinate equations. -/
theorem pinnedImage_iff {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (lo m : Nat)
    (h : lo+m ≤ n) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) (a : Finset V) :
    a ∈ pinnedImage hn s lo m S ↔ a ⊆ ground s ∧
      (∀ i : Fin n, (i.val < lo ∨ lo+m ≤ i.val) → (s i ∉ a ↔ i ∈ S)) ∧
      (∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m →
        s i ∈ a ∨ s (successor hn i) ∈ a) := by
  classical
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbSupp, hbI⟩ := (mem_paths_interval hn lo m h b).mp hb
    refine ⟨complement_supported s _, ?_, ?_⟩
    · intro i hi
      have hib : i ∉ b := by intro hm; have hh := hbSupp i hm; omega
      simp only [complement_label, Finset.mem_union, hib, or_false, not_not]
    · intro i hi hib
      have his : i ∉ S := by intro hm; have hh := hS i hm; omega
      have hsv : (successor hn i).val = i.val+1 := Nat.mod_eq_of_lt (by omega)
      have hjs : successor hn i ∉ S := by
        intro hm; have hh := hS _ hm; rw [hsv] at hh; omega
      simpa only [complement_label, Finset.mem_union, his, hjs, false_or] using hbI i hi hib
  · rintro ⟨haSupp, haPin, haI⟩
    let c : Finset (Fin n) := Finset.univ.filter fun i => s i ∉ a
    let b := c \ S
    have hc (i : Fin n) : i ∈ c ↔ s i ∉ a := by simp [c]
    have hSc : S ⊆ c := by
      intro i hi
      exact (hc i).mpr ((haPin i (hS i hi)).mpr hi)
    have hbSupp : ∀ i ∈ b, lo ≤ i.val ∧ i.val < lo+m := by
      intro i hi
      obtain ⟨hic, hiS⟩ := Finset.mem_sdiff.mp hi
      have hia := (hc i).mp hic
      by_contra hh
      have hout : i.val < lo ∨ lo+m ≤ i.val := by omega
      exact hiS ((haPin i hout).mp hia)
    have hbI : ∀ i : Fin n, lo ≤ i.val → i.val+1 < lo+m →
        i ∉ b ∨ successor hn i ∉ b := by
      intro i hi hib
      rcases haI i hi hib with hm | hm
      · exact Or.inl (fun ht => (hc i).mp (Finset.mem_sdiff.mp ht).1 hm)
      · exact Or.inr (fun ht => (hc _).mp (Finset.mem_sdiff.mp ht).1 hm)
    have hbc : S ∪ b = c := by
      ext i
      simp only [b, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | ⟨hi, _⟩)
        · exact hSc hi
        · exact hi
      · intro hi; by_cases hs : i ∈ S
        · exact Or.inl hs
        · exact Or.inr ⟨hi, hs⟩
    refine Finset.mem_image.mpr ⟨b, (mem_paths_interval hn lo m h b).mpr ⟨hbSupp, hbI⟩, ?_⟩
    rw [hbc]
    exact complement_inverse s a haSupp

private theorem survivors_append {T : Type*} [Fintype T] [DecidableEq T]
    (F : Finset (Finset T)) (xs ys : List T) :
    survivors F (xs ++ ys) = survivors (survivors F xs) ys := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => exact ih (remaining F x)

private theorem survivors_fixed {T : Type*} [Fintype T] [DecidableEq T]
    (F : Finset (Finset T)) (vs : List T)
    (h : ∀ v ∈ vs, (∀ a ∈ F, v ∈ a) ∨ (∀ a ∈ F, v ∉ a)) :
    survivors F vs = F := by
  revert h
  induction vs with
  | nil => intro _; rfl
  | cons v vs ih =>
    intro h
    change survivors (remaining F v) vs = F
    rw [remaining_of_fixed F v (h v (by simp))]
    exact ih (fun w hw => h w (by simp [hw]))

private theorem survivors_adjoin {T : Type*} [Fintype T] [DecidableEq T]
    (F : Finset (Finset T)) (vs : List T) (S : Finset T)
    (hSF : ∀ w ∈ S, ∀ a ∈ F, w ∉ a) (hSv : ∀ w ∈ S, w ∉ vs) :
    survivors (F.image (fun a => S ∪ a)) vs =
      (survivors F vs).image (fun a => S ∪ a) := by
  classical
  revert hSF hSv
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert w S hw ih =>
    intro hSF hSv
    have he (G : Finset (Finset T)) :
        G.image (fun a => insert w S ∪ a) = (G.image (fun a => S ∪ a)).image (insert w) := by
      simp only [Finset.image_image, Function.comp_def, Finset.insert_union]
    have hwF : ∀ a ∈ F.image (fun b => S ∪ b), w ∉ a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      simp [hw, hSF w (by simp) b hb]
    have hwvs : w ∉ vs := hSv w (by simp)
    rw [he, survivors_insert _ vs w hwF hwvs,
      ih (fun z hz => hSF z (by simp [hz])) (fun z hz => hSv z (by simp [hz]))]
    exact (he _).symm

private theorem suffix_decomposition {n : Nat} (hn : 0 < n) (k lo m : Nat)
    (hk : k ≤ lo) (h : lo+m ≤ n) :
    (List.finRange n).drop k = intervalList hn k (lo-k) ++
      intervalList hn lo m ++ intervalList hn (lo+m) (n-(lo+m)) := by
  rw [full_interval hn]
  simp only [intervalList, segment_drop, Nat.zero_add]
  have he : n-k = (lo-k) + (m + (n-(lo+m))) := by omega
  rw [he, segment_append]
  have he' : k+(lo-k) = lo := by omega
  rw [he', segment_append]

/-- The entire ACTUAL original coordinate suffix, including every discarded
fixed round, is conjugate to the ordered augmented interval run. -/
theorem survivors_pinnedImage {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)
    (k lo m : Nat) (hk : k ≤ lo) (h : lo+m ≤ n) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, i.val < lo ∨ lo+m ≤ i.val) :
    survivors (pinnedImage hn s lo m S) (((List.finRange n).drop k).map s) =
      if m % 3 = 1 then ∅ else
        {complementMap s (S ∪ pathChosen (intervalList hn lo m))} := by
  classical
  let F := (paths (intervalList hn lo m)).image (fun a => S ∪ a)
  have hcomp : pinnedImage hn s lo m S = F.image (complementMap s) := by
    simp only [pinnedImage, F, Finset.image_image, Function.comp_def]
  have hout (i : Fin n) (hi : i.val < lo ∨ lo+m ≤ i.val) :
      (∀ a ∈ F, i ∈ a) ∨ (∀ a ∈ F, i ∉ a) := by
    by_cases hiS : i ∈ S
    · left
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_union_left _ hiS
    · right
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hib : i ∉ b := by
        intro ht
        have hh := ((mem_paths_interval hn lo m h b).mp hb).1 i ht
        omega
      simp [hiS, hib]
  have hpref : survivors F (intervalList hn k (lo-k)) = F := by
    apply survivors_fixed
    intro i hi
    have hh := (interval_mem hn k (lo-k) (by omega) i).mp hi
    exact hout i (Or.inl (by omega))
  have hsuff : survivors (survivors F (intervalList hn lo m))
      (intervalList hn (lo+m) (n-(lo+m))) = survivors F (intervalList hn lo m) := by
    apply survivors_fixed
    intro i hi
    have hh := (interval_mem hn (lo+m) (n-(lo+m)) (by omega) i).mp hi
    rcases hout i (Or.inr hh.1) with hp | hp
    · exact Or.inl (fun a ha => hp a (survivors_subset _ _ ha))
    · exact Or.inr (fun a ha => hp a (survivors_subset _ _ ha))
  rw [hcomp, survivors_complement, suffix_decomposition hn k lo m hk h,
    survivors_append, hpref, survivors_append, hsuff]
  have hadj : survivors F (intervalList hn lo m) =
      (survivors (paths (intervalList hn lo m)) (intervalList hn lo m)).image (fun a => S ∪ a) := by
    apply survivors_adjoin
    · intro i hi a ha hm
      have hh := ((mem_paths_interval hn lo m h a).mp ha).1 i hm
      have ht := hS i hi
      omega
    · intro i hi hm
      have hh := (interval_mem hn lo m h i).mp hm
      have ht := hS i hi
      omega
  rw [hadj, survivors_paths_closed _ (interval_nodup hn lo m h), interval_length]
  split <;> simp [Finset.image_singleton]

end D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
