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

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.UniversalRoot

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inclusion-minimality ranges over every subset, including the empty set. -/
def MinimalFort (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  IsFort G S ∧ ∀ T ⊆ S, IsFort G T → S ⊆ T

/-- The entire finite family of inclusion-minimal forts. -/
noncomputable def minimalForts (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter (MinimalFort G)

/-- The graph obtained by adding one vertex adjacent to every original vertex. -/
def cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some v, some w => G.Adj v w
  symm := by intro v w; cases v <;> cases w <;> simp_all; exact G.adj_symm
  loopless := by intro v; cases v <;> simp [SimpleGraph.irrefl]

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

private theorem neighbors_lift_root (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : finiteNeighbors (cone G) none ∩ lift S = lift S := by
  ext v
  cases v <;> simp [finiteNeighbors, cone]

private theorem neighbors_lift_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    finiteNeighbors (cone G) (some v) ∩ lift S =
      lift (finiteNeighbors G v ∩ S) := by
  ext w
  cases w <;> simp [finiteNeighbors, cone]

private theorem neighbors_rootSet_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    finiteNeighbors (cone G) (some v) ∩ rootSet S =
      insert none (lift (finiteNeighbors G v ∩ S)) := by
  ext w
  cases w <;> simp [finiteNeighbors, cone, rootSet]

/-- Root-free forthood retains the root's cardinality condition. -/
theorem isFort_lift_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    IsFort (cone G) (lift S) ↔ IsFort G S ∧ S.card ≠ 1 := by
  constructor
  · rintro ⟨hne, hout⟩
    have hs : S.Nonempty := by simpa [lift] using hne
    refine ⟨⟨hs, fun v hv => ?_⟩, ?_⟩
    · have h := hout (some v) (by simpa using hv)
      simpa [neighbors_lift_some, lift] using h
    · have h := hout none (root_not_mem_lift S)
      simpa [neighbors_lift_root, lift] using h
  · rintro ⟨⟨hne, hout⟩, hcard⟩
    refine ⟨by simpa [lift] using hne, ?_⟩
    intro v hv
    cases v with
    | none => simpa [neighbors_lift_root, lift] using hcard
    | some v => simpa [neighbors_lift_some, lift] using hout v (by simpa using hv)

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
        Finset.card_map] at h
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
        ⟨w, by simp [finiteNeighbors, hadj, hw]⟩
      rw [neighbors_rootSet_some, Finset.card_insert_of_notMem (root_not_mem_lift _),
        Finset.card_map]
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
  apply SimpleGraph.connected_iff_exists_forall_reachable.mpr
  refine ⟨none, ?_⟩
  intro v
  cases v with
  | none => exact SimpleGraph.Reachable.refl _
  | some v => exact SimpleGraph.Adj.reachable (by trivial : (cone G).Adj none (some v))

end D5.S3.Combinatorics.MinimalForts.UniversalRoot
