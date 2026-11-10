/- GID: D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverGreedyReduction
   mirror-E: none(waiver:original-cyclic-greedy-reduction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The original first round has an isolated vertex and an endpoint-constrained independent complement path; true survivor bases retain arbitrary original labels. -/
import D5.S3.Geometry.FiniteCyclicNoncoverCollapse
import D5.S3.Geometry.FiniteIndependentPathGreedy

/-! UNCOMPILED. This module proves source-level reductions and actual survivor
bases, not the missing all-n cyclic survivor equalities. It does not construct
universal CriticalData. No new vertex or ambient label is introduced. -/

noncomputable section
open Finset

namespace D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
open FiniteCoordinateGreedyMatching FiniteGreedyFamilyTransport
open FiniteCyclicNoncoverCollapse
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For y_i := (s_i ∉ a), this says y_2,...,y_n is an independent PATH.
The path does not include the wrap edge or any retired ambient coordinate. -/
def TailIndependent {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) (a : Finset V) : Prop :=
  ∀ i : Fin n, 0 < i.val → i.val + 1 < n →
    s i ∈ a ∨ s (successor (show 0 < n by omega) i) ∈ a

def tailFaces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : Finset (Finset V) :=
  Finset.univ.filter fun a => a.Nonempty ∧ a ⊆ ground s ∧ point hn s ∉ a ∧
    TailIndependent hn s a ∧ (s ⟨1, by omega⟩ ∉ a ∨ s ⟨n-1, by omega⟩ ∉ a)

private theorem successor_internal {n : Nat} {i : Fin n} (h : i.val+1 < n) :
    (successor (show 0 < n by omega) i).val = i.val+1 := Nat.mod_eq_of_lt h

private theorem first_round_native (K : PreAbstractSimplicialComplex V) (p : V)
    (hp : ({p} : Finset V) ∈ K) (a : Finset V) :
    a ∈ remaining (faceSet K) p ↔
      a = {p} ∨ (a ∈ K ∧ p ∉ a ∧ insert p a ∉ K) := by
  simp only [mem_remaining, mem_faceSet]
  by_cases hpa : p ∈ a
  · constructor
    · rintro ⟨ha, hn⟩
      have he : a.erase p = ∅ := by
        by_contra he
        have hmem : a.erase p ∈ K :=
          (K.isRelLowerSet_faces ha).2 (Finset.erase_subset _ _)
            (Finset.nonempty_iff_ne_empty.mpr he)
        exact hn (by simpa [flip, hpa] using hmem)
      exact Or.inl (by rw [← Finset.insert_erase hpa, he])
    · rintro (rfl | ⟨_, hn, _⟩)
      · refine ⟨hp, ?_⟩
        intro he
        have he0 : (∅ : Finset V) ∈ K := by simpa [flip] using he
        exact Finset.not_nonempty_empty ((K.isRelLowerSet_faces he0).1)
      · exact (hn hpa).elim
  · simp only [flip, if_neg hpa]
    constructor
    · rintro ⟨ha, hn⟩; exact Or.inr ⟨ha, hpa, hn⟩
    · rintro (rfl | ⟨ha, _, hn⟩)
      · exact (hpa (by simp)).elim
      · exact ⟨ha, hn⟩

private theorem tail_characterization {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)
    (a : Finset V) :
    (a ∈ noncover (show 0 < n by omega) s ∧ point hn s ∉ a ∧
      insert (point hn s) a ∉ noncover (show 0 < n by omega) s) ↔
        a ∈ tailFaces hn s := by
  have h0 : point hn s ∈ ground s := spoke_mem_ground s (pointIndex hn)
  have hlast : successor (show 0 < n by omega) ⟨n-1, by omega⟩ =
      (⟨0, by omega⟩ : Fin n) := successor_last _
  have hzero : successor (show 0 < n by omega) ⟨0, by omega⟩ =
      (⟨1, by omega⟩ : Fin n) := successor_zero (by omega)
  constructor
  · rintro ⟨ha, hp, hnins⟩
    have hind : TailIndependent hn s a := by
      intro i hi hib
      by_contra h
      have hmiss : s i ∉ a ∧ s (successor (show 0 < n by omega) i) ∉ a :=
        not_or.mp h
      have hip : s i ≠ point hn s := by
        intro he
        have hh := congrArg Fin.val (s.injective he)
        change i.val = 0 at hh
        omega
      have hjp : s (successor (show 0 < n by omega) i) ≠ point hn s := by
        intro he
        have hh := congrArg Fin.val (s.injective he)
        change (successor (show 0 < n by omega) i).val = 0 at hh
        rw [successor_internal hib] at hh
        omega
      exact hnins ⟨Finset.insert_nonempty _ _, Finset.insert_subset h0 ha.2.1,
        i, by simpa [hip] using hmiss.1, by simpa [hjp] using hmiss.2⟩
    have hend : s ⟨1, by omega⟩ ∉ a ∨ s ⟨n-1, by omega⟩ ∉ a := by
      obtain ⟨i, hi, hj⟩ := ha.2.2
      by_cases hi0 : i.val = 0
      · have he : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
        left
        simpa only [he, hzero] using hj
      · by_cases hil : i.val+1 = n
        · right
          have he : i = (⟨n-1, by omega⟩ : Fin n) := Fin.ext (by omega)
          simpa only [he] using hi
        · have he := hind i (by omega) (by have hh := i.isLt; omega)
          exact (he.elim hi hj).elim
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.1, ha.2.1, hp, hind, hend⟩
  · intro ht
    obtain ⟨_, hne, hground, hp, hind, hend⟩ := Finset.mem_filter.mp ht
    refine ⟨?_, hp, ?_⟩
    · rcases hend with h1 | hl
      · exact ⟨hne, hground, ⟨0, by omega⟩, hp, by simpa only [hzero] using h1⟩
      · exact ⟨hne, hground, ⟨n-1, by omega⟩, hl, by simpa only [hlast] using hp⟩
    · rintro ⟨_, _, i, hi, hj⟩
      by_cases hi0 : i.val = 0
      · have he : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
        apply hi
        have he' : s i = point hn s := congrArg s he
        exact Finset.mem_insert.mpr (Or.inl he')
      · by_cases hil : i.val+1 = n
        · have he : i = (⟨n-1, by omega⟩ : Fin n) := Fin.ext (by omega)
          apply hj
          have he' : s (successor (show 0 < n by omega) i) = point hn s := by
            rw [he, hlast]
            rfl
          exact Finset.mem_insert.mpr (Or.inl he')
        · have he := hind i (by omega) (by have hh := i.isLt; omega)
          exact he.elim (fun h => hi (Finset.mem_insert_of_mem h))
            (fun h => hj (Finset.mem_insert_of_mem h))

/-- Equality of the genuine first remaining family on the original ambient V.
The singleton p is separate; every other survivor omits p. -/
theorem first_round {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    remaining (faceSet (noncover (show 0 < n by omega) s)) (point hn s) =
      insert {point hn s} (tailFaces hn s) := by
  ext a
  rw [first_round_native _ _ (point_mem hn s), Finset.mem_insert, tail_characterization]

theorem tail_omits_point {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)
    {a : Finset V} (ha : a ∈ tailFaces hn s) : point hn s ∉ a :=
  (Finset.mem_filter.mp ha).2.2.2.1

theorem first_noBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    ((nativeRelative (noncover (show 0 < n by omega) s)).noBranch (point hn s)).F =
      tailFaces hn s := by
  rw [RelativeFamily.noBranch_faces]
  ext a
  simp only [RelativeFamily.mem_A, nativeRelative_faces]
  change (a ∈ faceSet (noncover (show 0 < n by omega) s) ∧ point hn s ∉ a ∧
    insert (point hn s) a ∉ insert ∅ (faceSet (noncover (show 0 < n by omega) s))) ↔ _
  simp only [Finset.mem_insert, not_or, mem_faceSet]
  have hi : insert (point hn s) a ≠ ∅ := by simp
  constructor
  · rintro ⟨ha, hp, _, hni⟩
    exact (tail_characterization hn s a).mp ⟨ha, hp, hni⟩
  · intro ha
    obtain ⟨haK, hp, hni⟩ := (tail_characterization hn s a).mpr ha
    exact ⟨haK, hp, hi, hni⟩

theorem first_yesBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    ((nativeRelative (noncover (show 0 < n by omega) s)).yesBranch (point hn s)).F =
      {{point hn s}} := by
  rw [RelativeFamily.yesBranch_faces]
  ext a
  simp only [RelativeFamily.mem_B, nativeRelative_faces]
  change (a ∈ faceSet (noncover (show 0 < n by omega) s) ∧ point hn s ∈ a ∧
    a.erase (point hn s) ∈ ({∅} : Finset (Finset V))) ↔ a ∈ {{point hn s}}
  simp only [mem_faceSet, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, hp, he⟩
    rw [← Finset.insert_erase hp, he]
  · rintro rfl
    exact ⟨point_mem hn s, by simp, by simp⟩

/-- Direct finite family on the ORIGINAL index set. Used only as an exact
computational presentation of native faceSet, never as another endpoint. -/
def indexFaces (n : Nat) (hn : 0 < n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun a => a.Nonempty ∧
    ∃ i : Fin n, i ∉ a ∧ successor hn i ∉ a

private theorem mem_indexFaces (n : Nat) (hn : 0 < n) (a : Finset (Fin n)) :
    a ∈ indexFaces n hn ↔ a.Nonempty ∧ ∃ i : Fin n, i ∉ a ∧ successor hn i ∉ a := by
  simp only [indexFaces, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem map_membership {n : Nat} (s : Fin n ↪ V)
    (a : Finset (Fin n)) (i : Fin n) : s i ∈ a.map s ↔ i ∈ a := by
  constructor
  · rintro h
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp h
    exact s.injective he ▸ hj
  · intro h; exact Finset.mem_map.mpr ⟨i, h, rfl⟩

private theorem faceSet_map {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) :
    faceSet (noncover hn s) = (indexFaces n hn).image (Finset.map s) := by
  ext a
  rw [mem_faceSet]
  constructor
  · rintro ⟨hne, hsupp, i, hi, hj⟩
    let b : Finset (Fin n) := Finset.univ.filter fun i => s i ∈ a
    have hba : b.map s = a := by
      ext v
      constructor
      · intro hv
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
        exact (Finset.mem_filter.mp hj).2
      · intro hv
        obtain ⟨j, _, he⟩ := Finset.mem_map.mp (hsupp hv)
        refine Finset.mem_map.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
        exact he.symm ▸ hv
    have hbne : b.Nonempty := by
      obtain ⟨v, hv⟩ := hne
      obtain ⟨j, hj, _⟩ := Finset.mem_map.mp (hba.symm ▸ hv)
      exact ⟨j, hj⟩
    refine Finset.mem_image.mpr ⟨b, (mem_indexFaces n hn b).mpr ⟨hbne, i, ?_, ?_⟩, hba⟩
    · intro h; exact hi ((Finset.mem_filter.mp h).2)
    · intro h; exact hj ((Finset.mem_filter.mp h).2)
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hbne, i, hi, hj⟩ := (mem_indexFaces n hn b).mp hb
    refine ⟨hbne.map s, ?_, i, ?_, ?_⟩
    · intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
      exact spoke_mem_ground s j
    · exact fun h => hi ((map_membership s b i).mp h)
    · exact fun h => hj ((map_membership s b _).mp h)

/-- Exact greedy transport for every n, retaining all original ambient labels.
There is no assumption on any matching, certificate, or survivor equality. -/
theorem remainingFaces_map {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    remainingFaces hn s =
      (computeSurvivors (indexFaces n (show 0 < n by omega)) (List.finRange n)).image
        (Finset.map s) := by
  unfold remainingFaces
  rw [faceSet_map, survivors_map, computeSurvivors_eq]

private theorem map_blocks {n r : Nat} (s : Fin n ↪ V) (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start+3*j.val+b.val < n) :
    (blocks (Function.Embedding.refl (Fin n)) start h).map s = blocks s start h := by
  simpa only [blocks, Finset.map_map]

private theorem map_A (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    (criticalA q hq (Function.Embedding.refl _)).map s = criticalA q hq s := by
  simpa only [criticalA, Finset.map_insert, map_blocks]

private theorem map_B (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    (criticalB q hq (Function.Embedding.refl _)).map s = criticalB q hq s := by
  simpa only [criticalB, Finset.map_insert, map_blocks]

private theorem map_One (q : Nat) (s : Fin (3*q+1) ↪ V) :
    (criticalOne q (Function.Embedding.refl _)).map s = criticalOne q s :=
  map_blocks s _ _

private theorem map_Two (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    (criticalTwo q hq (Function.Embedding.refl _)).map s = criticalTwo q hq s := by
  simpa only [criticalTwo, Finset.map_insert, map_blocks]

private theorem index_three :
    computeSurvivors (indexFaces 3 (by omega)) (List.finRange 3) =
      insert {0} {criticalA 1 (by omega) (Function.Embedding.refl _),
        criticalB 1 (by omega) (Function.Embedding.refl _)} := by decide

private theorem index_four :
    computeSurvivors (indexFaces 4 (by omega)) (List.finRange 4) =
      insert {0} {criticalOne 1 (Function.Embedding.refl _)} := by decide

private theorem index_five :
    computeSurvivors (indexFaces 5 (by omega)) (List.finRange 5) =
      insert {0} {criticalTwo 1 (by omega) (Function.Embedding.refl _)} := by decide

/-- Actual matching-survivor base, universally transported to arbitrary V/s. -/
theorem survivors_three (s : Fin 3 ↪ V) :
    remainingFaces (by omega) s =
      insert {point (by omega) s} {criticalA 1 (by omega) s, criticalB 1 (by omega) s} := by
  rw [remainingFaces_map, index_three]
  simpa only [Finset.image_insert, Finset.image_singleton, map_A, map_B,
    Finset.map_singleton]

theorem survivors_four (s : Fin 4 ↪ V) :
    remainingFaces (by omega) s = insert {point (by omega) s} {criticalOne 1 s} := by
  rw [remainingFaces_map, index_four]
  simpa only [Finset.image_insert, Finset.image_singleton, map_One, Finset.map_singleton]

theorem survivors_five (s : Fin 5 ↪ V) :
    remainingFaces (by omega) s = insert {point (by omega) s} {criticalTwo 1 (by omega) s} := by
  rw [remainingFaces_map, index_five]
  simpa only [Finset.image_insert, Finset.image_singleton, map_Two, Finset.map_singleton]

end D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction
