/- GID: D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exhaustive witness chains have a unique core limit and infinitely many primes. -/

import D5.S3.ConceptDynamics.FixedPointPhilosophy.WitnessedLedger
import D5.S3.ConceptDynamics.DagCompletion.DependencyClosedFiltration
import Mathlib.Data.Set.UnionLift
import Mathlib.Data.Set.FiniteExhaustion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.FixedPointPhilosophy.PrimeInfinity

open D5.S3.ConceptDynamics.FixedPointPhilosophy.WitnessedLedger
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
open D5.S3.ConceptDynamics.DagCompletion.DependencyClosedFiltration
open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

variable {system : ProofSystem} (L : Nat → LegalLedger system)

def Extends (L M : LegalLedger system) : Prop :=
  CoreExtends L.toWitnessedCore M.toWitnessedCore

/-- Admissibility is a global property of a total transformation. -/
def Admissible (T : LegalLedger system → LegalLedger system) : Prop :=
  ∀ L, Extends L (T L)

/-- Every extension is realized by a globally admissible total transformation. -/
theorem extends_iff_admissible (L M : LegalLedger system) :
    Extends L M ↔ ∃ T, Admissible T ∧ M = T L := by
  classical
  constructor
  · intro h
    refine ⟨fun X => if X = L then M else X, ?_, by simp⟩
    intro X
    by_cases hx : X = L
    · subst X
      simpa using h
    · simpa [hx, Extends] using CoreExtends.refl X.toWitnessedCore
  · rintro ⟨T, hT, rfl⟩
    exact hT L

/-- Each step is the value of a total transformation admissible on every legal ledger. -/
def GeneratedChain : Prop :=
  ∀ t, ∃ T : LegalLedger system → LegalLedger system,
    Admissible T ∧ L (t + 1) = T (L t)

theorem chain_extends (hchain : GeneratedChain L) {i j : Nat} (hij : i ≤ j) :
    Extends (L i) (L j) := by
  induction j, hij using Nat.le_induction with
  | base => exact CoreExtends.refl _
  | succ j _ ih =>
    obtain ⟨T, hT, heq⟩ := hchain j
    exact ih.trans (by rw [heq]; exact hT (L j))

theorem frozen_monotone (hchain : GeneratedChain L) : Monotone (fun t => (L t).N) :=
  fun _ _ hij => (chain_extends L hchain hij).nodes

theorem witness_coherent (hchain : GeneratedChain L) (i j : Nat) (p : system.P)
    (hi : p ∈ (L i).N) (hj : p ∈ (L j).N) :
    (L i).w ⟨p, hi⟩ = (L j).w ⟨p, hj⟩ := by
  have left := (chain_extends L hchain (Nat.le_max_left i j)).witness ⟨p, hi⟩
  have right := (chain_extends L hchain (Nat.le_max_right i j)).witness ⟨p, hj⟩
  exact left.symm.trans right

def unionNodes : Set system.P := ⋃ t, (L t).N

/-- Coherent source witnesses are glued by the pinned set-union lifting operation. -/
noncomputable def limitWitness (hchain : GeneratedChain L) : unionNodes L → system.Proof :=
  Set.iUnionLift (fun t => (L t).N) (fun t => (L t).w)
    (witness_coherent L hchain) (unionNodes L) Set.Subset.rfl

theorem limit_witness_agrees (hchain : GeneratedChain L) (t : Nat)
    (p : unionNodes L) (hp : p.val ∈ (L t).N) :
    limitWitness L hchain p = (L t).w ⟨p.val, hp⟩ :=
  Set.iUnionLift_of_mem (S := fun t => (L t).N) (f := fun t => (L t).w)
    (hf := witness_coherent L hchain) (hT := Set.Subset.rfl) p hp

/-- This raw relation is defined before acyclicity of the union has been established. -/
def limitEdge (hchain : GeneratedChain L) : system.P → system.P → Prop :=
  referenceEdge (unionNodes L) (limitWitness L hchain)

theorem limit_edge_iff (hchain : GeneratedChain L) (t : Nat)
    {a b : system.P} (hb : b ∈ (L t).N) :
    limitEdge L hchain a b ↔ (L t).E a b := by
  constructor
  · rintro ⟨hbu, href⟩
    exact ⟨hb, by simpa only [limit_witness_agrees L hchain t ⟨b, hbu⟩ hb] using href⟩
  · rintro ⟨_, href⟩
    have hbu : b ∈ unionNodes L := Set.mem_iUnion_of_mem t hb
    refine ⟨hbu, ?_⟩
    rw [limit_witness_agrees L hchain t ⟨b, hbu⟩ hb]
    exact href

/-- The actual witness union makes every old frozen stage predecessor-closed. -/
def toDependencyFiltration (hchain : GeneratedChain L) :
    DependencyFiltration system.P (limitEdge L hchain) where
  stage := fun t => (L t).N
  appendOnly := frozen_monotone L hchain
  prerequisiteClosed t _ _ he hb :=
    (edge_endpoints (L t).toWitnessedCore ((limit_edge_iff L hchain t hb).mp he)).1

private theorem limit_path_mem (hchain : GeneratedChain L) (t : Nat)
    {a b : system.P} (h : StrictReachable (limitEdge L hchain) a b)
    (hb : b ∈ (L t).N) : a ∈ (L t).N := by
  apply prerequisiteClosure_least (targets := {b})
    (closed := (toDependencyFiltration L hchain).stage t)
    (Set.singleton_subset_iff.mpr hb) ((toDependencyFiltration L hchain).prerequisiteClosed t)
  exact ⟨b, Set.mem_singleton b, h.to_reflTransGen⟩

/-- Every nonempty path into an old target reflects into that target's old snapshot. -/
theorem limit_path_iff (hchain : GeneratedChain L) (t : Nat)
    {a b : system.P} (hb : b ∈ (L t).N) :
    StrictReachable (limitEdge L hchain) a b ↔ StrictReachable (L t).E a b := by
  constructor
  · intro h
    revert hb
    induction h with
    | single he =>
      intro hb
      exact Relation.TransGen.single ((limit_edge_iff L hchain t hb).mp he)
    | @tail b c path he ih =>
      intro hc
      have hb := limit_path_mem L hchain t (Relation.TransGen.single he) hc
      exact (ih hb).tail ((limit_edge_iff L hchain t hc).mp he)
  · intro h
    exact Relation.TransGen.lift id (fun _ _ he =>
      (limit_edge_iff L hchain t (edge_endpoints (L t).toWitnessedCore he).2).mpr he) a b h

/-- The lawful limit core is constructed only after raw path reflection. -/
noncomputable def limitCore (hchain : GeneratedChain L) : WitnessedCore system where
  N := unionNodes L
  w := limitWitness L hchain
  accepted p := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp p.property
    rw [limit_witness_agrees L hchain t p ht]
    exact (L t).accepted ⟨p.val, ht⟩
  permitted p := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp p.property
    rw [limit_witness_agrees L hchain t p ht]
    exact (L t).permitted ⟨p.val, ht⟩
  refs_closed p := by
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp p.property
    rw [limit_witness_agrees L hchain t p ht]
    exact fun _ h => Set.mem_iUnion_of_mem t ((L t).refs_closed ⟨p.val, ht⟩ h)
  acyclic p path := by
    obtain ⟨b, _, he⟩ := Relation.TransGen.tail'_iff.mp path
    obtain ⟨hp, _⟩ := he
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
    exact (L t).acyclic p ((limit_path_iff L hchain t ht).mp path)

theorem stage_extends_limit (hchain : GeneratedChain L) (t : Nat) :
    CoreExtends (L t).toWitnessedCore (limitCore L hchain) :=
  ⟨fun _ hp => Set.mem_iUnion_of_mem t hp,
    fun p => limit_witness_agrees L hchain t _ p.property⟩

theorem limit_edges_eq_iUnion (hchain : GeneratedChain L) :
    {e : system.P × system.P | (limitCore L hchain).E e.1 e.2} =
      ⋃ t, {e : system.P × system.P | (L t).E e.1 e.2} := by
  ext e
  constructor
  · intro he
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (edge_endpoints (limitCore L hchain) he).2
    exact Set.mem_iUnion_of_mem t ((limit_edge_iff L hchain t ht).mp he)
  · intro he
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp he
    exact ((stage_extends_limit L hchain t).edge_iff
      (edge_endpoints (L t).toWitnessedCore ht).2).mpr ht

theorem limit_ancestors_eq (hchain : GeneratedChain L) (t : Nat)
    (p : system.P) (hp : p ∈ (L t).N) :
    Anc (limitCore L hchain) p = Anc (L t).toWitnessedCore p :=
  Set.ext fun _ => limit_path_iff L hchain t hp

theorem limit_ancestors_finite (hchain : GeneratedChain L) (p : unionNodes L) :
    (Anc (limitCore L hchain) p.val).Finite := by
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp p.property
  rw [limit_ancestors_eq L hchain t p.val ht]
  exact (L t).finite.subset (ancestors_subset (L t).toWitnessedCore p.val)

/-- Least upper bound in the source's frozen-core order; no frontier order is imposed. -/
def CoreLimit (U : WitnessedCore system) : Prop :=
  (∀ t, CoreExtends (L t).toWitnessedCore U) ∧
    ∀ Q, (∀ t, CoreExtends (L t).toWitnessedCore Q) → CoreExtends U Q

theorem limit_isLeastUpperBound (hchain : GeneratedChain L) (Q : WitnessedCore system) :
    CoreExtends (limitCore L hchain) Q ↔ ∀ t, CoreExtends (L t).toWitnessedCore Q := by
  constructor
  · exact fun h t => (stage_extends_limit L hchain t).trans h
  · intro h
    have hn : unionNodes L ⊆ Q.N := Set.iUnion_subset fun t => (h t).nodes
    refine ⟨hn, ?_⟩
    intro p
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp p.property
    exact ((h t).witness ⟨p.val, ht⟩).trans
      (limit_witness_agrees L hchain t p ht).symm

theorem chain_limit_spec (hchain : GeneratedChain L) : CoreLimit L (limitCore L hchain) :=
  ⟨stage_extends_limit L hchain, fun Q => (limit_isLeastUpperBound L hchain Q).mpr⟩

theorem limit_prime_eq_iUnion (B : ClosureOperator (Set system.P))
    (hchain : GeneratedChain L) :
    Prime B (limitCore L hchain) = ⋃ t, Prime B (L t).toWitnessedCore := by
  ext p
  constructor
  · rintro ⟨hp, hprime⟩
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
    rw [limit_ancestors_eq L hchain t p ht] at hprime
    exact Set.mem_iUnion_of_mem t ⟨ht, hprime⟩
  · intro hp
    obtain ⟨t, ht, hprime⟩ := Set.mem_iUnion.mp hp
    refine ⟨Set.mem_iUnion_of_mem t ht, ?_⟩
    rwa [limit_ancestors_eq L hchain t p ht]

/-- Exhaustion asks each theorem to occur at some finite stage. -/
def Exhausts : Prop := ∀ p ∈ system.Thm, ∃ t, p ∈ (L t).N

theorem exhausts_iff_iUnion_eq : Exhausts L ↔ unionNodes L = system.Thm := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      (Set.iUnion_subset fun t => frozen_subset_theorems (L t).toWitnessedCore)
      (fun p hp => Set.mem_iUnion.mpr (h p hp))
  · intro h p hp
    exact Set.mem_iUnion.mp (show p ∈ unionNodes L from h.symm ▸ hp)

/-- Exhaustive source chains supply finite exhaustions without assuming global countability. -/
def toFiniteExhaustion (hchain : GeneratedChain L) (hexhaust : Exhausts L) :
    system.Thm.FiniteExhaustion where
  toFun := fun t => (L t).N
  finite' t := (L t).finite
  subset_succ' t := frozen_monotone L hchain (Nat.le_succ t)
  iUnion_eq' := (exhausts_iff_iUnion_eq L).mp hexhaust

/-- All four inclusions in the finite-total-prime contradiction, for any family of snapshots. -/
theorem finite_total_primes_bound (B : ClosureOperator (Set system.P))
    (hstrict : ∀ S : Set system.P, S.Finite → S ⊆ system.Thm →
      B S ∩ system.Thm ⊂ system.Thm)
    (hfinite : (⋃ t, Prime B (L t).toWitnessedCore).Finite) :
    let S := ⋃ t, Prime B (L t).toWitnessedCore
    S ⊆ system.Thm ∧ (∀ t, (L t).N ⊆ B S) ∧
      unionNodes L ⊆ B S ∩ system.Thm ∧ B S ∩ system.Thm ⊂ system.Thm := by
  let S := ⋃ t, Prime B (L t).toWitnessedCore
  have hS : S ⊆ system.Thm := Set.iUnion_subset fun t _ hp =>
    frozen_subset_theorems (L t).toWitnessedCore hp.1
  have stages : ∀ t, (L t).N ⊆ B S := fun t =>
    (frozen_subset_bind_prime B (L t)).trans
      (B.monotone (Set.subset_iUnion (fun t => Prime B (L t).toWitnessedCore) t))
  exact ⟨hS, stages, Set.subset_inter (Set.iUnion_subset stages)
    (Set.iUnion_subset fun t => frozen_subset_theorems (L t).toWitnessedCore),
    hstrict S hfinite hS⟩

theorem prime_union_infinite (B : ClosureOperator (Set system.P))
    (hstrict : ∀ S : Set system.P, S.Finite → S ⊆ system.Thm →
      B S ∩ system.Thm ⊂ system.Thm)
    (hexhaust : unionNodes L = system.Thm) :
    (⋃ t, Prime B (L t).toWitnessedCore).Infinite := by
  intro hfinite
  have bound := finite_total_primes_bound L B hstrict hfinite
  obtain ⟨p, hp, hnot⟩ := Set.exists_of_ssubset bound.2.2.2
  apply hnot
  apply bound.2.2.1
  rwa [hexhaust]

theorem primes_infinite_of_exhausts (B : ClosureOperator (Set system.P))
    (hchain : GeneratedChain L)
    (hstrict : ∀ S : Set system.P, S.Finite → S ⊆ system.Thm →
      B S ∩ system.Thm ⊂ system.Thm) (hexhaust : Exhausts L) :
    (⋃ t, Prime B (L t).toWitnessedCore).Infinite :=
  prime_union_infinite L B hstrict (toFiniteExhaustion L hchain hexhaust).iUnion_eq

theorem limit_prime_infinite (B : ClosureOperator (Set system.P))
    (hchain : GeneratedChain L)
    (hstrict : ∀ S : Set system.P, S.Finite → S ⊆ system.Thm →
      B S ∩ system.Thm ⊂ system.Thm) (hexhaust : Exhausts L) :
    (Prime B (limitCore L hchain)).Infinite := by
  rw [limit_prime_eq_iUnion L B hchain]
  exact primes_infinite_of_exhausts L B hchain hstrict hexhaust

/-- Prime infinity together with the unique witnessed core completing the chain. -/
theorem prime_infinity_complete (system : ProofSystem) (B : ClosureOperator (Set system.P))
    (L : Nat → LegalLedger system) (hchain : GeneratedChain L)
    (hstrict : ∀ S : Set system.P, S.Finite → S ⊆ system.Thm →
      B S ∩ system.Thm ⊂ system.Thm)
    (hexhaust : ∀ p ∈ system.Thm, ∃ t, p ∈ (L t).N) :
    (⋃ t, Prime B (L t).toWitnessedCore).Infinite ∧
      ∃! U : WitnessedCore system, CoreLimit L U ∧ U.N = system.Thm ∧
        Prime B U = ⋃ t, Prime B (L t).toWitnessedCore := by
  refine ⟨primes_infinite_of_exhausts L B hchain hstrict hexhaust,
    limitCore L hchain, ⟨chain_limit_spec L hchain,
      (exhausts_iff_iUnion_eq L).mp hexhaust, limit_prime_eq_iUnion L B hchain⟩, ?_⟩
  intro U hU
  exact CoreExtends.antisymm (hU.1.2 _ (chain_limit_spec L hchain).1)
    ((chain_limit_spec L hchain).2 _ hU.1.1)

end D5.S3.ConceptDynamics.FixedPointPhilosophy.PrimeInfinity
