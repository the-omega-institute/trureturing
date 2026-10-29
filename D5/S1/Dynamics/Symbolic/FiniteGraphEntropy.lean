/- GID: D5/S1/Dynamics/Symbolic/FiniteGraphEntropy
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/FiniteGraphEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite graph languages are compact, closed and invariant under the one-sided shift. -/

/- This module records the finite graph to symbolic-dynamics bridge.  The
right-total hypothesis is explicit: without it, a finite vertex path can end
at a dead vertex and need not be the prefix of an infinite graph path. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

noncomputable section

open Classical

open Set Function
open scoped Topology
open SymbolicDynamics
open D5.S1.Dynamics.Shadowing

namespace D5.S1.Dynamics.Symbolic.FiniteGraphEntropy

universe u

variable {V : Type u} [Fintype V] [TopologicalSpace V] [DiscreteTopology V]

/-- The adjacency matrix of a finite directed graph, over the natural numbers. -/
def adjacency (edge : V → V → Prop) : Matrix V V ℕ :=
  fun i j => if edge i j then 1 else 0

/-- Every vertex has an outgoing edge.  This is the finite extension condition
needed when infinite graph paths are identified with all finite edge paths. -/
def RightTotal (edge : V → V → Prop) : Prop :=
  ∀ v, ∃ w, edge v w

/-- The one-sided edge language presented by a directed graph. -/
def edgeLanguage (edge : V → V → Prop) : Set (ℕ → V) :=
  graphLanguage edge id

private def pathSet (edge : V → V → Prop) : Set (ℕ → V) :=
  {p | ∀ n, edge (p n) (p (n + 1))}

private theorem edgeLanguage_eq_pathSet_image (edge : V → V → Prop) :
    edgeLanguage edge = (fun p : ℕ → V => p) '' pathSet edge := by
  ext w
  constructor
  · rintro ⟨p, hp, hl⟩
    refine ⟨w, ?_, rfl⟩
    intro n
    simpa only [edgeLanguage, id_eq] using
      (show edge (w n) (w (n + 1)) from by
        rw [← hl n, ← hl (n + 1)]
        exact hp n)
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun _ => rfl⟩

private theorem isClosed_pathSet (edge : V → V → Prop) :
    IsClosed (pathSet edge) := by
  rw [show pathSet edge = ⋂ n : ℕ, {p : ℕ → V | edge (p n) (p (n + 1))} by
    ext p
    simp only [pathSet, mem_iInter, mem_setOf_eq]]
  apply isClosed_iInter
  intro n
  have hrel : IsClosed {q : V × V | edge q.1 q.2} := isClosed_discrete _
  have hcont : Continuous (fun p : ℕ → V => (p n, p (n + 1))) :=
    (continuous_apply n).prodMk (continuous_apply (n + 1))
  exact hrel.preimage hcont

/-- A finite graph language is compact, hence closed, in the full shift. -/
theorem edgeLanguage_isCompact_isClosed (edge : V → V → Prop) :
    IsCompact (edgeLanguage edge) ∧ IsClosed (edgeLanguage edge) := by
  have hpath : IsCompact (pathSet edge) :=
    isCompact_univ.of_isClosed_subset (isClosed_pathSet edge) (subset_univ _)
  have himage : IsCompact ((fun p : ℕ → V => p) '' pathSet edge) :=
    hpath.image continuous_id
  constructor
  · rw [edgeLanguage_eq_pathSet_image edge]
    exact himage
  · rw [edgeLanguage_eq_pathSet_image edge]
    exact himage.isClosed

/-- Dropping the first symbol of an edge path is again an edge path. -/
theorem edgeLanguage_shift_invariant (edge : V → V → Prop) :
    MapsTo (FullShift.shift (1 : ℕ)) (edgeLanguage edge) (edgeLanguage edge) := by
  intro w hw
  rcases hw with ⟨p, hp, hl⟩
  refine ⟨(fun n => p (n + 1)), ?_, ?_⟩
  · intro n
    exact hp (n + 1)
  · intro n
    simpa only [FullShift.shift_apply, id_eq, Nat.add_comm] using hl (n + 1)

/-- Under right-totality, every nonempty finite edge path can be extended to
an infinite path. -/
private theorem finite_path_extend (edge : V → V → Prop)
    (ht : RightTotal edge) (n : ℕ) (p : Fin (n + 1) → V)
    (hp : ∀ i : Fin n, edge (p i.castSucc) (p i.succ)) :
    ∃ w : ℕ → V, (∀ i, edge (w i) (w (i + 1))) ∧
      ∀ i : Fin (n + 1), w i.val = p i := by
  classical
  let chooseNext : V → V := fun v => Classical.choose (ht v)
  have hchoose (v : V) : edge v (chooseNext v) := Classical.choose_spec (ht v)
  have hiterate_comm : ∀ (m : ℕ) (v : V),
      (chooseNext^[m]) (chooseNext v) = chooseNext ((chooseNext^[m]) v) := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
        intro v
        simp only [Function.iterate_succ_apply']
        rw [ih]
  let w : ℕ → V := fun k =>
    if hk : k ≤ n then p ⟨k, by omega⟩ else
      (chooseNext^[k - n]) (p (Fin.last n))
  refine ⟨w, ?_, ?_⟩
  · intro k
    by_cases hk : k < n
    · have hk' : k ≤ n := by omega
      have hk1' : k + 1 ≤ n := by omega
      simp only [w, dif_pos hk', dif_pos hk1']
      simpa using hp ⟨k, hk⟩
    · by_cases hkn : k = n
      · subst k
        simp only [w, dif_pos le_rfl, dif_neg (by omega)]
        have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := by
          rfl
        simpa [hlast] using hchoose (p (Fin.last n))
      · have hkn' : n < k := by omega
        have hiter : k + 1 - n = (k - n) + 1 := by omega
        have hcomm : (chooseNext^[k - n]) (chooseNext (p (Fin.last n))) =
            chooseNext ((chooseNext^[k - n]) (p (Fin.last n))) :=
          hiterate_comm (k - n) (p (Fin.last n))
        simpa [w, show ¬ k ≤ n by omega, show ¬ k + 1 ≤ n by omega,
          hiter, Function.iterate_succ_apply, Function.iterate_succ_apply', hcomm] using
          hchoose ((chooseNext^[k - n]) (p (Fin.last n)))
  · intro i
    have hi : (i : ℕ) ≤ n := by omega
    simp only [w, dif_pos hi]

end D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
