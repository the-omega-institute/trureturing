/- GID: D5/S3/Geometry/FiniteCyclicNoncoverCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCyclicNoncoverCollapse
   mirror-E: none(waiver:original-label-cyclic-noncover-construction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Cyclic noncovers and their prescribed critical faces retain the original injective spoke labels and ghosts. -/
import D5.S3.Geometry.FiniteAcyclicMatchingCollapse
import D5.S3.Geometry.FiniteGreedyMatchingAcyclicity

/-! UNCOMPILED PARTIAL CONSUMER. The object below is ORIGINAL NC(C_n), not
Ind(C_n). Labels are injected directly into the arbitrary ambient V. The
prescribed critical faces below are the CLI greedy-route faces; they are not
the different expansion/zigzag-route faces. No theorem here asserts that the
greedy survivors equal this list: that universal recurrence is still missing.
Consequently this file does not yet instantiate CriticalData or assert the
all-n native sequences. The generic sequence engine is in its own module.
-/

noncomputable section
open Set Finset
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteCyclicNoncoverCollapse

open FiniteAcyclicFaceMatching FiniteCoordinateGreedyMatching
open FiniteGreedyMatchingAcyclicity
open FiniteConeCollapse FiniteSimplicialJoin
open FiniteCoordinateTruncation

variable {V : Type*} [Fintype V] [DecidableEq V]

def successor {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def ground {n : Nat} (s : Fin n ↪ V) : Finset V := Finset.univ.map s

/-- A face misses the two ORIGINAL endpoints of at least one cyclic rim edge. -/
def noncover {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) : PreAbstractSimplicialComplex V where
  faces := {a | a.Nonempty ∧ a ⊆ ground s ∧
    ∃ i : Fin n, s i ∉ a ∧ s (successor hn i) ∉ a}
  isRelLowerSet_faces := by
    rintro a ⟨ha, hI, i, hi, hj⟩
    refine ⟨ha, ?_⟩
    intro b hba hb
    exact ⟨hb, hba.trans hI, i, fun h => hi (hba h), fun h => hj (hba h)⟩

theorem mem_noncover {n : Nat} (hn : 0 < n) (s : Fin n ↪ V) (a : Finset V) :
    a ∈ noncover hn s ↔ a.Nonempty ∧
      ∃ i : Fin n, a ⊆ ground s \ {s i, s (successor hn i)} := by
  constructor
  · rintro ⟨ha, hI, i, hi, hj⟩
    refine ⟨ha, i, ?_⟩
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨hI hv, ?_⟩
    intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    exact he.elim (fun he => hi (he ▸ hv)) (fun he => hj (he ▸ hv))
  · rintro ⟨ha, i, hi⟩
    refine ⟨ha, fun v hv => (Finset.mem_sdiff.mp (hi hv)).1, i, ?_, ?_⟩
    · intro hv
      exact (Finset.mem_sdiff.mp (hi hv)).2 (by simp)
    · intro hv
      exact (Finset.mem_sdiff.mp (hi hv)).2 (by simp)

def pointIndex {n : Nat} (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩

def point {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : V := s (pointIndex hn)

/-- An actual native vertex, not VOID, UNIT, or a selected point in no space. -/
theorem point_mem {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    ({point hn s} : Finset V) ∈ noncover (by omega) s := by
  let i : Fin n := ⟨1, by omega⟩
  have his : successor (show 0 < n by omega) i = (⟨2, by omega⟩ : Fin n) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨Finset.singleton_nonempty _, ?_, i, ?_, ?_⟩
  · intro v hv
    have hvp : v = point hn s := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_map.mpr ⟨pointIndex hn, Finset.mem_univ _, rfl⟩
  · intro h
    have he := s.injective (Finset.mem_singleton.mp h)
    have hc := congrArg Fin.val he
    change 1 = 0 at hc
    omega
  · intro h
    rw [his] at h
    have he := s.injective (Finset.mem_singleton.mp h)
    have hc := congrArg Fin.val he
    change 2 = 0 at hc
    omega

theorem has_vertex {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    ∃ p : V, ({p} : Finset V) ∈ noncover (by omega) s :=
  ⟨point hn s, point_mem hn s⟩

/-- The cyclic greedy matching uses the given original-label order. -/
def matching {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    Pairing (noncover (show 0 < n by omega) s) :=
  pairing (noncover (show 0 < n by omega) s) ((List.finRange n).map s)

theorem matching_acyclic {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :
    (matching hn s).IsAcyclic := pairing_acyclic _ _

def remainingFaces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : Finset (Finset V) :=
  survivors (FiniteVertexDominationCollapse.faceSet (noncover (show 0 < n by omega) s))
    ((List.finRange n).map s)

theorem unmatched_iff_remaining {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)
    (a : Finset V) (ha : a ∈ noncover (show 0 < n by omega) s) :
    (matching hn s).Unmatched a ↔ a ∈ remainingFaces hn s := by
  have h := mem_survivors
    (FiniteVertexDominationCollapse.faceSet (noncover (show 0 < n by omega) s))
    ((List.finRange n).map s) a
  exact ⟨fun hu => h.mpr ⟨(FiniteVertexDominationCollapse.mem_faceSet _ a).mpr ha, hu⟩,
    fun hs => (h.mp hs).2⟩

/-- Equally spaced two-vertex blocks, expressed by an injective ORIGINAL index
map. The parameter start is zero based; the public membership formula below
adds one to recover exactly s1,...,sn. -/
def blockIndex {n r : Nat} (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :
    (Fin r × Fin 2) ↪ Fin n where
  toFun jb := ⟨start + 3 * jb.1.val + jb.2.val, h jb.1 jb.2⟩
  inj' := by
    intro a b hab
    have he := congrArg Fin.val hab
    have ha := a.2.isLt
    have hb := b.2.isLt
    have hj : a.1.val = b.1.val := by omega
    have hk : a.2.val = b.2.val := by omega
    exact Prod.ext (Fin.ext hj) (Fin.ext hk)

def blocks {n r : Nat} (s : Fin n ↪ V) (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) : Finset V :=
  Finset.univ.map (s.comp (blockIndex start h))

theorem blocks_card {n r : Nat} (s : Fin n ↪ V) (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :
    (blocks s start h).card = 2 * r := by
  simp only [blocks, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  omega

theorem mem_blocks {n r : Nat} (s : Fin n ↪ V) (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) (i : Fin n) :
    s i ∈ blocks s start h ↔
      ∃ j : Fin r, ∃ b : Fin 2, i.val = start + 3 * j.val + b.val := by
  constructor
  · intro hi
    obtain ⟨⟨j,b⟩, _, he⟩ := Finset.mem_map.mp hi
    exact ⟨j, b, (congrArg Fin.val (s.injective he)).symm⟩
  · rintro ⟨j, b, hi⟩
    exact Finset.mem_map.mpr ⟨(j,b), Finset.mem_univ _,
      congrArg s (Fin.ext hi.symm)⟩

theorem blocks_subset_ground {n r : Nat} (s : Fin n ↪ V) (start : Nat)
    (h : ∀ j : Fin r, ∀ b : Fin 2, start + 3 * j.val + b.val < n) :
    blocks s start h ⊆ ground s := by
  intro v hv
  obtain ⟨jb, _, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.mem_map.mpr ⟨blockIndex start h jb, Finset.mem_univ _, rfl⟩

def criticalA (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) : Finset V :=
  insert (s ⟨1, by omega⟩) (blocks (r := q-1) s 3 (by
    intro j b
    have hj := j.isLt
    have hb := b.isLt
    omega))

def criticalB (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) : Finset V :=
  insert (s ⟨3*q-1, by omega⟩) (blocks (r := q-1) s 2 (by
    intro j b
    have hj := j.isLt
    have hb := b.isLt
    omega))

def criticalOne (q : Nat) (s : Fin (3*q+1) ↪ V) : Finset V :=
  blocks (r := q) s 2 (by
    intro j b
    have hj := j.isLt
    have hb := b.isLt
    omega)

def criticalTwo (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) : Finset V :=
  insert (s ⟨1, by omega⟩) (insert (s ⟨3*q, by omega⟩)
    (blocks (r := q-1) s 3 (by
      intro j b
      have hj := j.isLt
      have hb := b.isLt
      omega)))

theorem criticalA_card (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    (criticalA q hq s).card = 2*q-1 := by
  have hn : s ⟨1, by omega⟩ ∉ blocks (r := q-1) s 3 (by
      intro j b; have hj := j.isLt; have hb := b.isLt; omega) := by
    intro hi
    obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
    change 1 = _ at he
    omega
  rw [criticalA, Finset.card_insert_of_notMem hn, blocks_card]
  omega

theorem criticalB_card (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    (criticalB q hq s).card = 2*q-1 := by
  have hn : s ⟨3*q-1, by omega⟩ ∉ blocks (r := q-1) s 2 (by
      intro j b; have hj := j.isLt; have hb := b.isLt; omega) := by
    intro hi
    obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
    have hj := j.isLt
    have hb := b.isLt
    change 3*q-1 = _ at he
    omega
  rw [criticalB, Finset.card_insert_of_notMem hn, blocks_card]
  omega

theorem criticalOne_card (q : Nat) (s : Fin (3*q+1) ↪ V) :
    (criticalOne q s).card = 2*q := blocks_card _ _ _

theorem criticalTwo_card (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    (criticalTwo q hq s).card = 2*q := by
  have hhigh : s ⟨3*q, by omega⟩ ∉ blocks (r := q-1) s 3 (by
      intro j b; have hj := j.isLt; have hb := b.isLt; omega) := by
    intro hi
    obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
    have hj := j.isLt
    have hb := b.isLt
    change 3*q = _ at he
    omega
  have hlow : s ⟨1, by omega⟩ ∉ insert (s ⟨3*q, by omega⟩)
      (blocks (r := q-1) s 3 (by
        intro j b; have hj := j.isLt; have hb := b.isLt; omega)) := by
    intro hi
    rcases Finset.mem_insert.mp hi with he | hi
    · have he' := congrArg Fin.val (s.injective he)
      change 1 = 3*q at he'
      omega
    · obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
      change 1 = _ at he
      omega
  rw [criticalTwo, Finset.card_insert_of_notMem hlow,
    Finset.card_insert_of_notMem hhigh, blocks_card]
  omega

/-- Exact approved ORIGINAL one-based formula, not just a cardinality. -/
theorem criticalA_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)) :
    s i ∈ criticalA q hq s ↔ i.val+1 = 2 ∨
      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2) := by
  rw [criticalA, Finset.mem_insert]
  constructor
  · rintro (he | hi)
    · left; have hc := congrArg Fin.val (s.injective he); change i.val = 1 at hc; omega
    · obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
      refine Or.inr ⟨j.val+1, by omega, by have hj := j.isLt; omega, ?_⟩
      have hb := b.isLt
      omega
  · rintro (he | ⟨j, hj, hjq, he⟩)
    · left; apply congrArg s; apply Fin.ext; change i.val = 1; omega
    · right
      apply (mem_blocks _ _ _ _).mpr
      rcases he with he | he
      · exact ⟨⟨j-1, by omega⟩, ⟨0, by omega⟩, by omega⟩
      · exact ⟨⟨j-1, by omega⟩, ⟨1, by omega⟩, by omega⟩

theorem criticalB_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) (i : Fin (3*q)) :
    s i ∈ criticalB q hq s ↔ i.val+1 = 3*q ∨
      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j ∨ i.val+1 = 3*j+1) := by
  rw [criticalB, Finset.mem_insert]
  constructor
  · rintro (he | hi)
    · left; have hc := congrArg Fin.val (s.injective he); change i.val = 3*q-1 at hc; omega
    · obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
      refine Or.inr ⟨j.val+1, by omega, by have hj := j.isLt; omega, ?_⟩
      have hb := b.isLt
      omega
  · rintro (he | ⟨j, hj, hjq, he⟩)
    · left; apply congrArg s; apply Fin.ext; change i.val = 3*q-1; omega
    · right
      apply (mem_blocks _ _ _ _).mpr
      rcases he with he | he
      · exact ⟨⟨j-1, by omega⟩, ⟨0, by omega⟩, by omega⟩
      · exact ⟨⟨j-1, by omega⟩, ⟨1, by omega⟩, by omega⟩

theorem criticalOne_formula (q : Nat) (s : Fin (3*q+1) ↪ V) (i : Fin (3*q+1)) :
    s i ∈ criticalOne q s ↔
      ∃ j : Nat, 1 ≤ j ∧ j ≤ q ∧ (i.val+1 = 3*j ∨ i.val+1 = 3*j+1) := by
  constructor
  · intro hi
    obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
    refine ⟨j.val+1, by omega, by have hj := j.isLt; omega, ?_⟩
    have hb := b.isLt
    omega
  · rintro ⟨j, hj, hjq, he⟩
    apply (mem_blocks _ _ _ _).mpr
    rcases he with he | he
    · exact ⟨⟨j-1, by omega⟩, ⟨0, by omega⟩, by omega⟩
    · exact ⟨⟨j-1, by omega⟩, ⟨1, by omega⟩, by omega⟩

theorem criticalTwo_formula (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) (i : Fin (3*q+2)) :
    s i ∈ criticalTwo q hq s ↔ i.val+1 = 2 ∨ i.val+1 = 3*q+1 ∨
      ∃ j : Nat, 1 ≤ j ∧ j < q ∧ (i.val+1 = 3*j+1 ∨ i.val+1 = 3*j+2) := by
  rw [criticalTwo, Finset.mem_insert, Finset.mem_insert]
  constructor
  · rintro (he | he | hi)
    · left; have hc := congrArg Fin.val (s.injective he); change i.val = 1 at hc; omega
    · right; left; have hc := congrArg Fin.val (s.injective he); change i.val = 3*q at hc; omega
    · obtain ⟨j, b, he⟩ := (mem_blocks _ _ _ _).mp hi
      refine Or.inr (Or.inr ⟨j.val+1, by omega, by have hj := j.isLt; omega, ?_⟩)
      have hb := b.isLt
      omega
  · rintro (he | he | ⟨j, hj, hjq, he⟩)
    · left; apply congrArg s; apply Fin.ext; change i.val = 1; omega
    · right; left; apply congrArg s; apply Fin.ext; change i.val = 3*q; omega
    · right; right
      apply (mem_blocks _ _ _ _).mpr
      rcases he with he | he
      · exact ⟨⟨j-1, by omega⟩, ⟨0, by omega⟩, by omega⟩
      · exact ⟨⟨j-1, by omega⟩, ⟨1, by omega⟩, by omega⟩

theorem spoke_mem_ground {n : Nat} (s : Fin n ↪ V) (i : Fin n) : s i ∈ ground s :=
  Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem criticalA_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    criticalA q hq s ⊆ ground s :=
  Finset.insert_subset (spoke_mem_ground s _) (blocks_subset_ground _ _ _)

theorem criticalB_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    criticalB q hq s ⊆ ground s :=
  Finset.insert_subset (spoke_mem_ground s _) (blocks_subset_ground _ _ _)

theorem criticalOne_supported (q : Nat) (s : Fin (3*q+1) ↪ V) :
    criticalOne q s ⊆ ground s := blocks_subset_ground _ _ _

theorem criticalTwo_supported (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    criticalTwo q hq s ⊆ ground s :=
  Finset.insert_subset (spoke_mem_ground s _)
    (Finset.insert_subset (spoke_mem_ground s _) (blocks_subset_ground _ _ _))

theorem criticalA_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    s ⟨0, by omega⟩ ∉ criticalA q hq s := by
  intro h
  have he := (criticalA_formula q hq s ⟨0, by omega⟩).mp h
  change 0+1 = 2 ∨ _ at he
  rcases he with he | ⟨j, hj, hjq, he⟩ <;> omega

theorem criticalB_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    s ⟨0, by omega⟩ ∉ criticalB q hq s := by
  intro h
  have he := (criticalB_formula q hq s ⟨0, by omega⟩).mp h
  change 0+1 = 3*q ∨ _ at he
  rcases he with he | ⟨j, hj, hjq, he⟩ <;> omega

theorem criticalOne_avoids_zero (q : Nat) (s : Fin (3*q+1) ↪ V) :
    s ⟨0, by omega⟩ ∉ criticalOne q s := by
  intro h
  obtain ⟨j, hj, hjq, he⟩ := (criticalOne_formula q s ⟨0, by omega⟩).mp h
  change 0+1 = 3*j ∨ 0+1 = 3*j+1 at he
  omega

theorem criticalTwo_avoids_zero (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    s ⟨0, by omega⟩ ∉ criticalTwo q hq s := by
  intro h
  have he := (criticalTwo_formula q hq s ⟨0, by omega⟩).mp h
  change 0+1 = 2 ∨ 0+1 = 3*q+1 ∨ _ at he
  rcases he with he | he | ⟨j, hj, hjq, he⟩ <;> omega

theorem successor_last {n : Nat} (hn : 0 < n) :
    successor hn ⟨n-1, by omega⟩ = (⟨0, hn⟩ : Fin n) := by
  apply Fin.ext
  have he : n-1+1 = n := by omega
  simp only [successor, he, Nat.mod_self]

theorem successor_zero {n : Nat} (hn : 1 < n) :
    successor (show 0 < n by omega) ⟨0, by omega⟩ = (⟨1, hn⟩ : Fin n) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hn

theorem criticalA_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    criticalA q hq s ∈ noncover (by omega) s := by
  refine ⟨Finset.card_pos.mp (by rw [criticalA_card]; omega),
    criticalA_supported q hq s, ⟨3*q-1, by omega⟩, ?_, ?_⟩
  · intro h
    have he := (criticalA_formula q hq s ⟨3*q-1, by omega⟩).mp h
    rcases he with he | ⟨j, hj, hjq, he⟩ <;> dsimp at he <;> omega
  · rw [successor_last]
    exact criticalA_avoids_zero q hq s

theorem criticalB_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    criticalB q hq s ∈ noncover (by omega) s := by
  refine ⟨Finset.card_pos.mp (by rw [criticalB_card]; omega),
    criticalB_supported q hq s, ⟨0, by omega⟩, criticalB_avoids_zero q hq s, ?_⟩
  rw [successor_zero (by omega)]
  intro h
  have he := (criticalB_formula q hq s ⟨1, by omega⟩).mp h
  rcases he with he | ⟨j, hj, hjq, he⟩ <;> dsimp at he <;> omega

theorem criticalOne_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V) :
    criticalOne q s ∈ noncover (by omega) s := by
  refine ⟨Finset.card_pos.mp (by rw [criticalOne_card]; omega),
    criticalOne_supported q s, ⟨0, by omega⟩, criticalOne_avoids_zero q s, ?_⟩
  rw [successor_zero (by omega)]
  intro h
  obtain ⟨j, hj, hjq, he⟩ := (criticalOne_formula q s ⟨1, by omega⟩).mp h
  dsimp at he
  omega

theorem criticalTwo_mem (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V) :
    criticalTwo q hq s ∈ noncover (by omega) s := by
  refine ⟨Finset.card_pos.mp (by rw [criticalTwo_card]; omega),
    criticalTwo_supported q hq s, ⟨3*q+2-1, by omega⟩, ?_, ?_⟩
  · intro h
    have he := (criticalTwo_formula q hq s ⟨3*q+2-1, by omega⟩).mp h
    rcases he with he | he | ⟨j, hj, hjq, he⟩ <;> dsimp at he <;> omega
  · rw [successor_last]
    exact criticalTwo_avoids_zero q hq s

theorem criticalA_ne_B (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    criticalA q hq s ≠ criticalB q hq s := by
  intro heq
  have ha : s ⟨1, by omega⟩ ∈ criticalA q hq s := Finset.mem_insert_self _ _
  have hb := heq ▸ ha
  have he := (criticalB_formula q hq s ⟨1, by omega⟩).mp hb
  rcases he with he | ⟨j, hj, hjq, he⟩ <;> dsimp at he <;> omega

theorem critical_pair_antichain (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V) :
    ¬ criticalA q hq s ⊆ criticalB q hq s ∧ ¬ criticalB q hq s ⊆ criticalA q hq s := by
  constructor
  · intro h
    exact criticalA_ne_B q hq s (Finset.eq_of_subset_of_card_le h
      (by rw [criticalA_card, criticalB_card]))
  · intro h
    exact criticalA_ne_B q hq s (Finset.eq_of_subset_of_card_le h
      (by rw [criticalA_card, criticalB_card])).symm

/-- Small critical-face bases are equations on the actual original labels.
They do not stand in for the missing universal greedy-survivor recurrence. -/
theorem base_three_A (s : Fin 3 ↪ V) (i : Fin 3) :
    s i ∈ criticalA 1 (by omega) s ↔ i.val = 1 := by
  rw [criticalA_formula]
  omega

theorem base_three_B (s : Fin 3 ↪ V) (i : Fin 3) :
    s i ∈ criticalB 1 (by omega) s ↔ i.val = 2 := by
  rw [criticalB_formula]
  omega

theorem base_four (s : Fin 4 ↪ V) (i : Fin 4) :
    s i ∈ criticalOne 1 s ↔ i.val = 2 ∨ i.val = 3 := by
  rw [criticalOne_formula]
  constructor
  · rintro ⟨j, hj, hjq, he⟩; omega
  · intro he; exact ⟨1, by omega, by omega, by omega⟩

theorem base_five (s : Fin 5 ↪ V) (i : Fin 5) :
    s i ∈ criticalTwo 1 (by omega) s ↔ i.val = 1 ∨ i.val = 3 := by
  rw [criticalTwo_formula]
  omega

/-- Explicit ghosts on the original ambient type, never globally retired. -/
theorem ghost_coordinate {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)
    (x : Space (noncover hn s)) (v : V) (hv : v ∉ ground s) : x.val v = 0 := by
  obtain ⟨a, ha, hx⟩ := (realization_mem_iff (noncover hn s) x.val).mp x.property
  exact hx.2.2 v (fun hva => hv (ha.2.1 hva))

theorem inclusion_coordinates {n : Nat} (hn : 0 < n) (s : Fin n ↪ V)
    (L : PreAbstractSimplicialComplex V) (hL : L ≤ noncover hn s)
    (x : Space L) : (realizationInclusion hL x).val = x.val := rfl

end D5.S3.Geometry.FiniteCyclicNoncoverCollapse
