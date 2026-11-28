import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DenseSixRootNormalization

/-! Root-contact stabilizers act on the two occupied direction triples. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9GenericRootAction

open Finset
open BalancedCubeComponentBoundary (directions)
open BalancedCriticalSpectrum (Q)
open Q9FiveAxisMissingContact (Geometry rightRoot)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactCNF (Axis)
open Q9TightDistanceTwoCNF (support)
open Q9TightDistanceTwoNormalized (normalize_minimumDisplacements)
open Q9DenseSixRootNormalization
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private normalize_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private direction_subsets exists_triple root root_even transform_geometry from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DenseSixRootNormalization

abbrev RootPair := Fin 35 × Fin 35

def pairKey (r : RootPair) : Nat := 35 * r.1.val + r.2.val

def rootPoint (t : Bool) : Q 9 := root t

def translation (t : Bool) : Q 9 := rootPoint t

def Preserves (F : Finset (Finset Axis)) (p : Equiv.Perm Axis) : Prop :=
  ({0, 1} : Finset Axis).map p.toEmbedding = {0, 1} ∧
    F.map (Finset.mapEmbedding p.toEmbedding).toEmbedding = F

def Related (F : Finset (Finset Axis)) (r s : RootPair) : Prop :=
  ∃ p : Equiv.Perm Axis, ∃ t : Bool, Preserves F p ∧
    triple s.1 = (triple (if t then r.2 else r.1)).map p.toEmbedding ∧
    triple s.2 = (triple (if t then r.1 else r.2)).map p.toEmbedding

def Canonical (F : Finset (Finset Axis)) (C D : Finset (Q 9)) : Prop :=
  ∃ r : RootPair,
    directions C origin = triple r.1 ∧ directions D rightRoot = triple r.2 ∧
      ∀ s, Related F r s → pairKey r ≤ pairKey s

private theorem map_comp (A : Finset Axis) (p q : Equiv.Perm Axis) :
    (A.map p.toEmbedding).map q.toEmbedding = A.map (p.trans q).toEmbedding := by
  rw [Finset.map_map, ← Equiv.trans_toEmbedding]

private theorem map_family_comp (F : Finset (Finset Axis)) (p q : Equiv.Perm Axis) :
    (F.map (Finset.mapEmbedding p.toEmbedding).toEmbedding).map
        (Finset.mapEmbedding q.toEmbedding).toEmbedding =
      F.map (Finset.mapEmbedding (p.trans q).toEmbedding).toEmbedding := by
  rw [Finset.map_map]
  apply congrArg (fun e : Finset Axis ↪ Finset Axis => F.map e) ?_
  ext A
  simp [Finset.mapEmbedding_apply, Finset.map_map]

theorem preserves_refl (F : Finset (Finset Axis)) : Preserves F (Equiv.refl Axis) := by
  constructor
  · simp
  · have he : (Finset.mapEmbedding (Equiv.refl Axis).toEmbedding).toEmbedding =
        Function.Embedding.refl (Finset Axis) := by
      ext A
      simp [Finset.mapEmbedding_apply]
    rw [he, Finset.map_refl]

theorem preserves_trans {F : Finset (Finset Axis)} {p q : Equiv.Perm Axis}
    (hp : Preserves F p) (hq : Preserves F q) : Preserves F (p.trans q) := by
  refine ⟨?_, ?_⟩
  · calc
      ({0, 1} : Finset Axis).map (p.trans q).toEmbedding =
          (({0, 1} : Finset Axis).map p.toEmbedding).map q.toEmbedding := by
            rw [map_comp]
      _ = {0, 1} := by rw [hp.1, hq.1]
  · calc
      F.map (Finset.mapEmbedding (p.trans q).toEmbedding).toEmbedding =
          (F.map (Finset.mapEmbedding p.toEmbedding).toEmbedding).map
            (Finset.mapEmbedding q.toEmbedding).toEmbedding := by
              rw [map_family_comp]
      _ = F := by rw [hp.2, hq.2]

theorem related_refl (F : Finset (Finset Axis)) (r : RootPair) : Related F r r := by
  refine ⟨Equiv.refl Axis, false, preserves_refl F, ?_, ?_⟩
  · simp
  · simp

theorem related_trans {F : Finset (Finset Axis)} {r s u : RootPair}
    (hrs : Related F r s) (hsu : Related F s u) : Related F r u := by
  obtain ⟨p, t, hp, hs₁, hs₂⟩ := hrs
  obtain ⟨q, v, hq, hu₁, hu₂⟩ := hsu
  refine ⟨p.trans q, Bool.xor t v, preserves_trans hp hq, ?_, ?_⟩
  all_goals
    cases t <;> cases v <;>
      simp [Bool.xor] at hs₁ hs₂ hu₁ hu₂ ⊢ <;>
      simp [hs₁, hs₂, hu₁, hu₂, map_comp]

noncomputable def orbit (F : Finset (Finset Axis)) (r : RootPair) : Finset RootPair :=
  by
    classical
    exact (Finset.univ : Finset RootPair).filter (Related F r)

open Classical in
theorem orbit_nonempty (F : Finset (Finset Axis)) (r : RootPair) : (orbit F r).Nonempty := by
  exact ⟨r, mem_filter.mpr ⟨mem_univ _, related_refl F r⟩⟩

theorem exists_orbit_minimum (F : Finset (Finset Axis)) (r : RootPair) :
    ∃ s ∈ orbit F r, ∀ u ∈ orbit F r, pairKey s ≤ pairKey u := by
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image (orbit F r) pairKey (orbit_nonempty F r)
  exact ⟨s, hs, hmin⟩

open Classical in
theorem canonical_minimum_of_orbit {F : Finset (Finset Axis)} {r s : RootPair}
    (hs : Related F r s) (hmin : ∀ u ∈ orbit F r, pairKey s ≤ pairKey u) :
    ∀ u, Related F s u → pairKey s ≤ pairKey u := by
  intro u hsu
  apply hmin u
  exact mem_filter.mpr ⟨mem_univ _, related_trans hs hsu⟩

theorem reject_forbidden_root_pair {F : Finset (Finset Axis)} {r s : RootPair}
    (hvalid : Related F r s) (hdesc : pairKey s < pairKey r) :
    ¬ (∀ u, Related F r u → pairKey r ≤ pairKey u) := by
  intro hmin
  exact (not_lt_of_ge (hmin s hvalid)) hdesc

private theorem rightRoot_membership (i : Axis) :
    rightRoot i = decide (i ∈ ({0, 1} : Finset Axis)) := by
  fin_cases i <;> decide

private theorem root_permutation (p : Equiv.Perm Axis)
    (hp : ({0, 1} : Finset Axis).map p.toEmbedding = {0, 1}) (i : Axis) :
    p.symm i ∈ ({0, 1} : Finset Axis) ↔ i ∈ ({0, 1} : Finset Axis) := by
  calc
    p.symm i ∈ ({0, 1} : Finset Axis) ↔
        i ∈ ({0, 1} : Finset Axis).map p.toEmbedding := by
          rw [mem_map_equiv]
    _ ↔ i ∈ ({0, 1} : Finset Axis) := by rw [hp]

private theorem normalize_rightRoot (p : Equiv.Perm Axis)
    (hp : ({0, 1} : Finset Axis).map p.toEmbedding = {0, 1}) :
    normalize p.symm origin rightRoot = rightRoot ∧
      normalize p.symm rightRoot origin = rightRoot := by
  have hm := root_permutation p hp
  constructor <;> funext i
  · change (rightRoot (p.symm i) != origin (p.symm i)) = rightRoot i
    simp [origin, rightRoot_membership, hm i]
  · change (origin (p.symm i) != rightRoot (p.symm i)) = rightRoot i
    simp [origin, rightRoot_membership, hm i]

private theorem transform_root_generic (p : Equiv.Perm Axis)
    (hp : ({0, 1} : Finset Axis).map p.toEmbedding = {0, 1}) (t s : Bool) :
    normalize p.symm (rootPoint t) (rootPoint (if t then !s else s)) = rootPoint s := by
  have hr := normalize_rightRoot p hp
  cases t <;> cases s <;>
    simp only [rootPoint, Bool.not_false, Bool.not_true, ite_false, ite_true]
  · exact normalize_center p.symm origin
  · exact hr.1
  · exact normalize_center p.symm rightRoot
  · exact hr.2

open Classical in
theorem normalize_root_neighborhoods_generic
    {F : Finset (Finset Axis)} {C D : Finset (Q 9)}
    (h : Geometry C D) (hf : minimumDisplacements C D false 2 = F) :
    ∃ p : Equiv.Perm Axis, ∃ t : Bool, Preserves F p ∧ parity (translation t) = false ∧
      let e := normalize p.symm (translation t)
      let X := (support C D t).map e.toEmbedding
      let Y := (support C D (!t)).map e.toEmbedding
      Geometry X Y ∧ minimumDisplacements X Y false 2 = F ∧ Canonical F X Y := by
  obtain ⟨hA, hB⟩ := direction_subsets h
  obtain ⟨a, ha⟩ := exists_triple hA (h.left_rules.occupied_degree _ h.left_root)
  obtain ⟨b, hb⟩ := exists_triple hB (h.right_rules.occupied_degree _ h.right_root)
  let r : RootPair := (a, b)
  obtain ⟨s, hsorbit, hmin⟩ := exists_orbit_minimum F r
  have hrs : Related F r s := (mem_filter.mp hsorbit).2
  have hminimum := canonical_minimum_of_orbit hrs hmin
  obtain ⟨p, t, hp, hs₁, hs₂⟩ := hrs
  dsimp [r] at hs₁ hs₂
  let τ := p.symm
  let z := translation t
  let e := normalize τ z
  let X := (support C D t).map e.toEmbedding
  let Y := (support C D (!t)).map e.toEmbedding
  have h0 : e z = origin := normalize_center τ z
  have h3 : e (rootPoint (!t)) = rightRoot := by
    have he : (if t then !true else true) = !t := by cases t <;> rfl
    rw [← he]
    exact transform_root_generic p hp.1 t true
  have hz : parity z = false := by
    simpa only [z, translation, rootPoint] using root_even t
  have hgeom : Geometry X Y := by
    exact transform_geometry h τ z t h0 h3
  have hordered : minimumDisplacements (support C D t) (support C D (!t)) false 2 = F := by
    cases ht : t
    · simpa only [ht, support, Bool.false_eq_true, Bool.not_false, Bool.not_true, ite_false, ite_true] using hf
    · simpa only [ht, support, Bool.false_eq_true, Bool.not_false, Bool.not_true, ite_false, ite_true]
        using (minimumDisplacements_swap_two D C false).trans hf
  have hfamily : minimumDisplacements X Y false 2 = F := by
    have hmap := normalize_minimumDisplacements τ z (support C D t) (support C D (!t)) false 2
    simpa only [hz, show (false : Bool) + false = false from rfl, hordered,
      τ, Equiv.symm_symm, hp.2] using hmap
  have hdir₁ : directions X origin = triple s.1 := by
    rw [← h0]
    change directions ((support C D t).map (normalize τ z).toEmbedding)
      (normalize τ z z) = triple s.1
    rw [normalize_directions]
    change (directions (support C D t) (rootPoint t)).map p.toEmbedding = triple s.1
    cases ht : t
    · simpa only [ht, support, Bool.false_eq_true, ite_false, ite_true, rootPoint, root, ← ha, τ] using hs₁.symm
    · simpa only [ht, support, ite_true, rootPoint, root, ← hb, τ] using hs₁.symm
  have hdir₂ : directions Y rightRoot = triple s.2 := by
    rw [← h3]
    change directions ((support C D (!t)).map (normalize τ z).toEmbedding)
      (normalize τ z (rootPoint (!t))) = triple s.2
    rw [normalize_directions]
    change (directions (support C D (!t)) (rootPoint (!t))).map p.toEmbedding = triple s.2
    cases ht : t
    · simpa only [ht, support, Bool.not_false, ite_true, rootPoint, root, ← hb, τ, Bool.false_eq_true,
        ite_false] using hs₂.symm
    · simpa only [ht, support, Bool.not_true, ite_true, rootPoint, root, ← ha, τ, ite_false,
        Bool.false_eq_true] using hs₂.symm
  refine ⟨p, t, hp, hz, ?_⟩
  exact ⟨hgeom, hfamily, ⟨s, hdir₁, hdir₂, hminimum⟩⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9GenericRootAction
