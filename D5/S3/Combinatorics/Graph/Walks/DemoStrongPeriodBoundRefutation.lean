/- GID: D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.claim; result=D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.result; claim=D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation.claim
   digest: The singleton contradicts the universal strong distance-two period bound. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.DemoStrongPeriodBoundRefutation

/-- Exact shortest distance two, also defined when the input graph is disconnected. -/
noncomputable def distanceTwo {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := G.edist u v = 2
  symm.symm u v h := by
    rw [SimpleGraph.edist_comm]
    exact h
  loopless.irrefl v := by simp

/-- A positive return to the initial graph up to graph isomorphism. -/
def PositiveReturn {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  0 < t ∧ Nonempty ((distanceTwo^[t]) G ≃g G)

/-- The least positive isomorphism return, or zero when there is no return.
The source index is `f = t + 1`, since its first graph has index one. -/
noncomputable def strongPeriod {V : Type*} (G : SimpleGraph V) : ℕ := by
  classical
  exact if h : ∃ t, PositiveReturn G t then Nat.find h else 0

/-- The complete universal integer bound of Demo--Lund--Al-saadi, Conjecture 1.
The vertex universe is fixed, and no lower bound on cardinality is imposed. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    (strongPeriod G : ℤ) ≤ (Fintype.card V : ℤ) - 3

/-- The complete universal bound fails at the connected singleton. -/
theorem result : ¬ claim := by
  classical
  intro hclaim
  let G : SimpleGraph Unit := ⊥
  have hfixed : distanceTwo G = G := by
    ext u v
    have huv : u = v := Subsingleton.elim u v
    subst v
    simp [distanceTwo, G]
  have hreturn : PositiveReturn G 1 := by
    refine ⟨by decide, ?_⟩
    simpa only [Function.iterate_one, hfixed] using
      (show Nonempty (G ≃g G) from ⟨SimpleGraph.Iso.refl⟩)
  have hexists : ∃ t, PositiveReturn G t := ⟨1, hreturn⟩
  have hperiod : strongPeriod G = 1 := by
    rw [strongPeriod, dif_pos hexists]
    have hpositive := (Nat.find_spec hexists).1
    have hupper := Nat.find_min' hexists hreturn
    exact Nat.le_antisymm hupper (Nat.succ_le_of_lt hpositive)
  have hbound := hclaim Unit G SimpleGraph.Connected.of_subsingleton
  rw [hperiod] at hbound
  norm_num at hbound

end D5.S3.Combinatorics.Graph.Walks.DemoStrongPeriodBoundRefutation
