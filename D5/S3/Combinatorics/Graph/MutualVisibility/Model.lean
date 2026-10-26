/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/Model
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/Model
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Mutual visibility uses existential shortest paths in the original host and permits addition, removal and host-edge slides. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

/-! Original-host mutual visibility and its finite reconfiguration geometry. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph
open scoped Classical symmDiff

variable {V : Type*} [DecidableEq V]

/-- Selected endpoints admit a shortest original-host path with no other selected vertex. -/
def Visible (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    ∃ p : H.Walk u v, p.length = H.dist u v ∧
      ∀ z ∈ p.support, z ∈ S → z = u ∨ z = v

/-- A single addition/removal or replacement along an actual host edge. -/
def MixedMove (H : SimpleGraph V) (S T : Finset V) : Prop :=
  S ≠ T ∧ ((S ∆ T).card = 1 ∨
    ∃ x y, S \ T = {x} ∧ T \ S = {y} ∧ H.Adj x y)

/-- All feasible subsets, including the empty set and all cardinalities. -/
abbrev Configuration (H : SimpleGraph V) := {S : Finset V // Visible H S}

private theorem mixedMove_symm {H : SimpleGraph V} {S T : Finset V}
    (h : MixedMove H S T) : MixedMove H T S := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with h | ⟨x, y, hxy, hyx, hxyH⟩
  · exact Or.inl (by simpa [symmDiff_comm] using h)
  · exact Or.inr ⟨y, x, hyx, hxy, hxyH.symm⟩

/-- The full mixed reconfiguration graph of the original host. -/
def reconfiguration (H : SimpleGraph V) : SimpleGraph (Configuration H) where
  Adj S T := MixedMove H S.val T.val
  symm := ⟨fun _ _ h => mixedMove_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance configurationDecidableEq (H : SimpleGraph V) :
    DecidableEq (Configuration H) := Classical.decEq _

noncomputable instance configurationFintype [Fintype V] (H : SimpleGraph V) :
    Fintype (Configuration H) := by
  classical
  unfold Configuration
  infer_instance

noncomputable instance reconfigurationDecidableAdj (H : SimpleGraph V) :
    DecidableRel (reconfiguration H).Adj := Classical.decRel _

theorem visible_mono {H : SimpleGraph V} {S T : Finset V}
    (h : S ⊆ T) (hT : Visible H T) : Visible H S := by
  intro u hu v hv huv
  obtain ⟨p, hp, ha⟩ := hT u (h hu) v (h hv) huv
  exact ⟨p, hp, fun z hz hzs => ha z hz (h hzs)⟩

theorem visible_empty (H : SimpleGraph V) : Visible H ∅ := by
  simp [Visible]

theorem visible_singleton (H : SimpleGraph V) (x : V) : Visible H {x} := by
  intro u hu v hv huv
  simp only [Finset.mem_singleton] at hu hv
  exact (huv (hu.trans hv.symm)).elim

theorem visible_pair {H : SimpleGraph V} (hH : H.Connected) (x y : V) :
    Visible H {x, y} := by
  intro u hu v hv huv
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist u v
  refine ⟨p, hp, ?_⟩
  intro z _ hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hz
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv rfl).elim
  · exact hz
  · exact hz.symm
  · exact (huv rfl).elim

theorem mixedMove_insert (H : SimpleGraph V) (S : Finset V)
    {x : V} (hx : x ∉ S) : MixedMove H S (insert x S) := by
  refine ⟨?_, Or.inl ?_⟩
  · intro h
    exact hx (h.symm ▸ Finset.mem_insert_self x S)
  · have hd : S ∆ insert x S = {x} := by
      ext y
      by_cases hxy : y = x <;> by_cases hy : y ∈ S <;> simp_all [Finset.mem_symmDiff]
    rw [hd, Finset.card_singleton]

theorem mixedMove_erase (H : SimpleGraph V) (S : Finset V)
    {x : V} (hx : x ∈ S) : MixedMove H S (S.erase x) := by
  have h := mixedMove_insert H (S.erase x) (Finset.notMem_erase x S)
  rw [Finset.insert_erase hx] at h
  exact mixedMove_symm h

/-- A separator leaves at most one vertex or disconnects the remaining induced graph. -/
def Separates {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (C : Finset W) : Prop :=
  (Finset.univ \ C).card ≤ 1 ∨ ¬ (G.induce {v | v ∉ C}).Preconnected

/-- Standard finite vertex connectivity, with the value q-1 on a complete graph of order q. -/
noncomputable def vertexConnectivity {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) : ℕ :=
  sInf {k | ∃ C : Finset W, C.card = k ∧ Separates G C}

end D5.S3.Combinatorics.Graph.MutualVisibility
