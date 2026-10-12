/- GID: D5/S1/Dynamics/Shadowing/StableCoreObservation
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/StableCoreObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable-core observation periods give uniform exact tails and finite whole names. -/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Discrete
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Order

open Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/-- The intersection of all forward images, including the zeroth image.
No surjectivity of the dynamics is assumed. -/
def stableCore {X : Type u} (f : X → X) : Set X :=
  ⋂ n : ℕ, Set.range (f^[n])

/-- A discrete continuous observation's period on the stable core becomes an
exact uniform period after a finite transient. The alphabet may be infinite,
and the period may be zero. -/
theorem finite_observation_eventually_periodic_of_stable_core_periodic
    {X : Type u} {D : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D]
    (f : X → X) (q : X → D) (hf : Continuous f) (hq : Continuous q) (M : ℕ)
    (hcore : ∀ a ∈ stableCore f, q (f^[M] a) = q a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : X,
      q (f^[n + M] x) = q (f^[n] x) := by
  classical
  let C : Set X := {a | q (f^[M] a) ≠ q a}
  have hC : IsClosed C :=
    (isClosed_discrete {p : D × D | p.1 ≠ p.2}).preimage
      ((hq.comp (hf.iterate M)).prodMk hq)
  let K : ℕ → Set X := fun n => C ∩ Set.range (f^[n])
  have hclosed (n : ℕ) : IsClosed (K n) :=
    hC.inter (isCompact_range (hf.iterate n)).isClosed
  have hnest : ∀ n : ℕ, K (n + 1) ⊆ K n := by
    intro n a ha
    refine ⟨ha.1, ?_⟩
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨f x, by simpa only [iterate_succ_apply] using hx⟩
  have hgood : ∃ N : ℕ, ∀ a ∈ Set.range (f^[N]), q (f^[M] a) = q a := by
    by_contra! hbad
    have hne (n : ℕ) : (K n).Nonempty := by
      obtain ⟨a, ha, hneq⟩ := hbad n
      exact ⟨a, hneq, ha⟩
    obtain ⟨a, ha⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        K hnest hne (hclosed 0).isCompact hclosed
    have hacore : a ∈ stableCore f :=
      Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp ha n).2
    exact (Set.mem_iInter.mp ha 0).1 (hcore a hacore)
  obtain ⟨N, hN⟩ := hgood
  refine ⟨N, fun n hn x => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hmem : f^[N + k] x ∈ Set.range (f^[N]) :=
    ⟨f^[k] x, (iterate_add_apply f N k x).symm⟩
  simpa only [Nat.add_comm (N + k) M, iterate_add_apply] using hN _ hmem

/-- Whole forward names with uniform positive tail period are determined by
the exact prefix of length N+M. All transient names and time zero are retained.
No topology or finiteness assumption is needed for this injectivity. -/
theorem forward_name_prefix_injective_of_eventually_periodic
    {X : Type u} {D : Type v} (f : X → X) (q : X → D) (N M : ℕ)
    (hM : 0 < M)
    (htail : ∀ n : ℕ, N ≤ n → ∀ x : X, q (f^[n + M] x) = q (f^[n] x)) :
    Function.Injective (fun w : Set.range (fun x n => q (f^[n] x)) =>
      fun i : Fin (N + M) => w.1 i) := by
  intro w z hp
  apply Subtype.ext
  obtain ⟨x, hx⟩ := w.2
  obtain ⟨y, hy⟩ := z.2
  have hperiod (n : ℕ) (hn : N ≤ n) :
      w.1 (n + M) = w.1 n ∧ z.1 (n + M) = z.1 n := by
    rw [← hx, ← hy]
    exact ⟨htail n hn x, htail n hn y⟩
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < N + M
    · exact congrFun hp ⟨k, hk⟩
    · have hj : N ≤ k - M := by omega
      have hlt : k - M < k := by omega
      have heq : k - M + M = k := by omega
      obtain ⟨hw, hz⟩ := hperiod (k - M) hj
      rw [heq] at hw hz
      exact hw.trans ((ih (k - M) hlt).trans hz.symm)

/-- A positive observation period on the stable core yields an exact finite
prefix encoding of the entire name range and its cardinal bound. Empty
sources and alphabets are included without a Nonempty assumption. -/
theorem finite_observation_names_of_stable_core_periodic
    {X : Type u} {D : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (f : X → X) (q : X → D) (hf : Continuous f) (hq : Continuous q) (M : ℕ)
    (hM : 0 < M) (hcore : ∀ a ∈ stableCore f, q (f^[M] a) = q a) :
    ∃ N : ℕ,
      (∀ n : ℕ, N ≤ n → ∀ x : X, q (f^[n + M] x) = q (f^[n] x)) ∧
      Function.Injective (fun w : Set.range (fun x n => q (f^[n] x)) =>
        fun i : Fin (N + M) => w.1 i) ∧
      (Set.range (fun x n => q (f^[n] x))).Finite ∧
      Nat.card (Set.range (fun x n => q (f^[n] x))) ≤ Nat.card D ^ (N + M) := by
  obtain ⟨N, htail⟩ :=
    finite_observation_eventually_periodic_of_stable_core_periodic f q hf hq M hcore
  have hinj := forward_name_prefix_injective_of_eventually_periodic f q N M hM htail
  let : Finite (Set.range (fun x n => q (f^[n] x))) := Finite.of_injective _ hinj
  refine ⟨N, htail, hinj, Set.toFinite _, ?_⟩
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective _ hinj

#print axioms finite_observation_eventually_periodic_of_stable_core_periodic
#print axioms forward_name_prefix_injective_of_eventually_periodic
#print axioms finite_observation_names_of_stable_core_periodic

end D5.S1.Dynamics.Shadowing
