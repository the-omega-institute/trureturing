/- GID: D5/S3/Combinatorics/MinimalForts/UniversalRoot
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/UniversalRoot
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Minimal forts under adjoining a universal vertex. -/

import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
import D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Universal-root graphs and the source nonempty-fort predicate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.UniversalRoot

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

variable {V : Type*} [Fintype V] [DecidableEq V]

instance fortDecidable (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidablePred (IsFort G) := by
  intro S
  unfold IsFort
  infer_instance

/-- Inclusion-minimality ranges over every subset, including the empty set. -/
def MinimalFort (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  IsFort G S ∧ ∀ T ⊆ S, IsFort G T → S ⊆ T

instance minimalFortDecidable (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidablePred (MinimalFort G) := by
  intro S
  unfold MinimalFort
  infer_instance

/-- The entire finite family of inclusion-minimal forts. -/
def minimalForts (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) := Finset.univ.filter (MinimalFort G)

/-- The graph obtained by adding one vertex adjacent to every original vertex. -/
def cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some v, some w => G.Adj v w
  symm.symm := by intro v w; cases v <;> cases w <;> simp_all; exact G.adj_symm
  loopless.irrefl := by intro v; cases v <;> simp [SimpleGraph.irrefl]

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (cone G).Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [cone] <;> infer_instance

/-- View a base vertex set inside the cone, without the added root. -/
def lift (S : Finset V) : Finset (Option V) :=
  S.map ⟨Option.some, Option.some_injective V⟩

/-- Add the universal root to a base vertex set. -/
def rootSet (S : Finset V) : Finset (Option V) := insert none (lift S)

/-- The base vertices of a vertex set in the cone. -/
def baseSet (F : Finset (Option V)) : Finset V :=
  Finset.univ.filter (fun v => some v ∈ F)

@[simp] private theorem mem_lift (v : V) (S : Finset V) :
    some v ∈ lift S ↔ v ∈ S := by simp [lift]

@[simp] private theorem root_not_mem_lift (S : Finset V) : none ∉ lift S := by
  simp [lift]

@[simp] private theorem card_lift (S : Finset V) : (lift S).card = S.card :=
  Finset.card_map _

@[simp] private theorem mem_baseSet (v : V) (F : Finset (Option V)) :
    v ∈ baseSet F ↔ some v ∈ F := by simp [baseSet]

private theorem lift_baseSet {F : Finset (Option V)} (h : none ∉ F) :
    lift (baseSet F) = F := by
  ext v
  cases v <;> simp [h]

private theorem rootSet_baseSet {F : Finset (Option V)} (h : none ∈ F) :
    rootSet (baseSet F) = F := by
  ext v
  cases v <;> simp [rootSet, h]

private theorem mem_neighbors_cone (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : Option V) : w ∈ finiteNeighbors (cone G) v ↔ (cone G).Adj v w := by
  exact Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])

private theorem neighbors_lift_root (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : finiteNeighbors (cone G) none ∩ lift S = lift S := by
  ext v
  cases v with
  | none => simp only [Finset.mem_inter, root_not_mem_lift, and_false]
  | some v =>
    rw [Finset.mem_inter, mem_neighbors_cone]
    change True ∧ some v ∈ lift S ↔ some v ∈ lift S
    exact and_iff_right trivial

private theorem neighbors_lift_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    finiteNeighbors (cone G) (some v) ∩ lift S =
      lift (finiteNeighbors G v ∩ S) := by
  ext w
  cases w with
  | none => simp only [Finset.mem_inter, root_not_mem_lift, and_false]
  | some w =>
    simp only [Finset.mem_inter, mem_neighbors_cone, mem_lift]
    change G.Adj v w ∧ w ∈ S ↔ w ∈ finiteNeighbors G v ∧ w ∈ S
    rw [show w ∈ finiteNeighbors G v ↔ G.Adj v w from
      Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and])]

private theorem neighbors_rootSet_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    finiteNeighbors (cone G) (some v) ∩ rootSet S =
      insert none (lift (finiteNeighbors G v ∩ S)) := by
  rw [rootSet, Finset.inter_insert_of_mem]
  · rw [neighbors_lift_some]
  · rw [mem_neighbors_cone]
    trivial

/-- Root-free forthood retains the root's cardinality condition. -/
theorem isFort_lift_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsFort (cone G) (lift S) ↔ IsFort G S ∧ S.card ≠ 1 := by
  constructor
  · rintro ⟨hne, hout⟩
    have hs : S.Nonempty := by simpa [lift] using hne
    refine ⟨⟨hs, fun v hv => ?_⟩, ?_⟩
    · have h := hout (some v) (by simpa using hv)
      simpa only [neighbors_lift_some, card_lift] using h
    · have h := hout none (root_not_mem_lift S)
      simpa only [neighbors_lift_root, card_lift] using h
  · rintro ⟨⟨hne, hout⟩, hcard⟩
    refine ⟨by simpa [lift] using hne, ?_⟩
    intro v hv
    cases v with
    | none => simpa only [neighbors_lift_root, card_lift] using hcard
    | some v => simpa only [neighbors_lift_some, card_lift] using hout v (by simpa using hv)

/-- With the root selected, every unselected base vertex needs a selected base neighbor. -/
theorem isFort_rootSet_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsFort (cone G) (rootSet S) ↔ G.IsDominating (S : Set V) := by
  constructor
  · intro hf v
    by_cases hv : v ∈ S
    · exact Or.inl hv
    · right
      have h := hf.2 (some v) (by simpa [rootSet] using hv)
      rw [neighbors_rootSet_some, Finset.card_insert_of_notMem (root_not_mem_lift _),
        card_lift] at h
      have hp : (finiteNeighbors G v ∩ S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨w, hw⟩ := hp
      simp only [Finset.mem_inter, finiteNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      exact ⟨w, hw.2, hw.1⟩
  · intro hd
    refine ⟨⟨none, by simp [rootSet]⟩, ?_⟩
    intro v hv
    cases v with
    | none => exact False.elim (hv (by simp [rootSet]))
    | some v =>
      have hvS : v ∉ S := by simpa [rootSet] using hv
      obtain ⟨w, hw, hadj⟩ := (hd v).resolve_left hvS
      have hp : 0 < (finiteNeighbors G v ∩ S).card := Finset.card_pos.mpr
        ⟨w, Finset.mem_inter.mpr ⟨by simp [finiteNeighbors, hadj], hw⟩⟩
      rw [neighbors_rootSet_some, Finset.card_insert_of_notMem (root_not_mem_lift _),
        card_lift]
      omega

/-- A nonempty fort in a graph without isolated vertices cannot be a singleton. -/
theorem fort_card_ne_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : ∀ v, ∃ w, G.Adj v w) {S : Finset V} (hS : IsFort G S) : S.card ≠ 1 := by
  intro h
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
  obtain ⟨w, hvw⟩ := hn v
  have hwv : w ≠ v := (G.ne_of_adj hvw).symm
  have hbad := hS.2 w (by simpa using hwv)
  simp [finiteNeighbors, G.adj_symm hvw] at hbad

/-- The cone is connected even when the base graph is empty or disconnected. -/
theorem cone_connected (G : SimpleGraph V) : (cone G).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := cone G)).mpr
  refine ⟨none, ?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.refl _
  | some v => exact SimpleGraph.Adj.reachable (by trivial : (cone G).Adj none (some v))


/-- Root-free minimal forts are precisely the minimal forts of the base. -/
theorem minimalFort_lift_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : ∀ v, ∃ w, G.Adj v w) (S : Finset V) :
    MinimalFort (cone G) (lift S) ↔ MinimalFort G S := by
  constructor
  · rintro ⟨hf, hm⟩
    refine ⟨((isFort_lift_iff G S).mp hf).1, ?_⟩
    intro T hTS hT v hv
    have hlT : IsFort (cone G) (lift T) :=
      (isFort_lift_iff G T).mpr ⟨hT, fort_card_ne_one G hn hT⟩
    have hsub : lift T ⊆ lift S := by
      intro w hw
      cases w with
      | none => exact False.elim (root_not_mem_lift T hw)
      | some w => exact (mem_lift w S).mpr (hTS ((mem_lift w T).mp hw))
    have := hm (lift T) hsub hlT (show some v ∈ lift S by simpa using hv)
    simpa using this
  · rintro ⟨hf, hm⟩
    refine ⟨(isFort_lift_iff G S).mpr ⟨hf, fort_card_ne_one G hn hf⟩, ?_⟩
    intro F hF hfort
    have hr : none ∉ F := fun h => root_not_mem_lift S (hF h)
    have hbase : baseSet F ⊆ S := by
      intro v hv
      have := hF (mem_baseSet v F |>.mp hv)
      simpa using this
    have hbf : IsFort G (baseSet F) :=
      ((isFort_lift_iff G _).mp ((lift_baseSet hr).symm ▸ hfort)).1
    have hmin := hm (baseSet F) hbase hbf
    intro w hw
    cases w with
    | none => exact False.elim (root_not_mem_lift S hw)
    | some v => exact (mem_baseSet v F).mp (hmin (by simpa using hw))

/-- Selecting the root gives minimal domination with no contained base fort. -/
theorem minimalFort_rootSet_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : ∀ v, ∃ w, G.Adj v w) (S : Finset V) :
    MinimalFort (cone G) (rootSet S) ↔
      MinimalDominating G (S : Set V) ∧ ∀ T ⊆ S, ¬ IsFort G T := by
  classical
  constructor
  · rintro ⟨hf, hm⟩
    have hd := (isFort_rootSet_iff G S).mp hf
    refine ⟨⟨hd, ?_⟩, ?_⟩
    · intro T hTS hT v hv
      have hsub : rootSet T.toFinset ⊆ rootSet S := by
        intro w hw
        cases w with
        | none => simp [rootSet]
        | some w =>
          have hwT : w ∈ T := by simpa [rootSet] using hw
          simpa [rootSet] using hTS hwT
      have hfT : IsFort (cone G) (rootSet T.toFinset) :=
        (isFort_rootSet_iff G _).mpr (by simpa using hT)
      have hmem := hm _ hsub hfT (show some v ∈ rootSet S by simpa [rootSet] using hv)
      simpa [rootSet] using hmem
    · intro T hTS hT
      have hfT : IsFort (cone G) (lift T) :=
        (isFort_lift_iff G _).mpr ⟨hT, fort_card_ne_one G hn hT⟩
      have hsub : lift T ⊆ rootSet S := by
        intro w hw
        cases w with
        | none => exact False.elim (root_not_mem_lift T hw)
        | some w =>
          have hwT : w ∈ T := by simpa using hw
          simpa [rootSet] using hTS hwT
      exact root_not_mem_lift T (hm _ hsub hfT (by simp [rootSet]))
  · rintro ⟨⟨hd, hm⟩, hfree⟩
    refine ⟨(isFort_rootSet_iff G _).mpr hd, ?_⟩
    intro F hF hfort
    have hbase : baseSet F ⊆ S := by
      intro v hv
      have := hF ((mem_baseSet v F).mp hv)
      simpa [rootSet] using this
    by_cases hr : none ∈ F
    · have hbf : G.IsDominating ((baseSet F : Finset V) : Set V) :=
        (isFort_rootSet_iff G _).mp ((rootSet_baseSet hr).symm ▸ hfort)
      have hmin := hm (baseSet F : Set V) hbase hbf
      intro w hw
      cases w with
      | none => exact hr
      | some v => exact (mem_baseSet v F).mp (hmin (by simpa [rootSet] using hw))
    · have hbf : IsFort G (baseSet F) :=
        ((isFort_lift_iff G _).mp ((lift_baseSet hr).symm ▸ hfort)).1
      exact False.elim (hfree _ hbase hbf)

/-- All base subsets that become minimal forts when joined to the selected root. -/
def rootedChoices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter (fun S => MinimalFort (cone G) (rootSet S))


end D5.S3.Combinatorics.MinimalForts.UniversalRoot
