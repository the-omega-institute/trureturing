/- GID: D5/S1/Dynamics/Shadowing/StableCoreObservation
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/StableCoreObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable-core periodicity forces an eventual finite-observation tail. -/

import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Compactness.Compact

open Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v

/- The mismatch set is closed and misses the stable image.  Compactness then
   turns this qualitative exclusion into one uniform tail index. -/
theorem finite_observation_eventually_periodic_of_stable_core_periodic
    {X D : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D]
    (f : X → X) (q : X → D)
    (hf : Continuous f) (hq : Continuous q)
    (M : ℕ)
    (hcore : ∀ a ∈ (⋂ n : ℕ, Set.range (f^[n])),
      q (f^[M] a) = q a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : X,
      q (f^[n + M] x) = q (f^[n] x) := by
  classical
  let mismatch : Set X := {x | q (f^[M] x) ≠ q x}
  have hmismatch_closed : IsClosed mismatch := by
    have hpair : Continuous (fun x : X => (q (f^[M] x), q x)) :=
      (hq.comp (hf.iterate M)).prodMk hq
    have hneq : IsClosed {p : D × D | p.1 ≠ p.2} := isClosed_discrete _
    exact hneq.preimage hpair
  have hmismatch_core : ¬ (mismatch ∩ (⋂ n : ℕ, Set.range (f^[n]))).Nonempty := by
    rintro ⟨x, hx⟩
    exact hx.1 (hcore x hx.2)
  by_contra hN
  push Not at hN
  have hfinite_intersections : ∀ s : Finset ℕ,
      (⋂ n ∈ s, mismatch ∩ Set.range (f^[n])).Nonempty := by
    intro s
    have hsource : (⋂ k ∈ s, mismatch ∩ Set.range (f^[k])).Nonempty := by
      by_cases hs : s.Nonempty
      · let N := s.max' hs
        obtain ⟨n, hnN, x, hx⟩ := hN N
        refine ⟨f^[n] x, ?_⟩
        simp only [mem_iInter]
        intro k hk
        have hkN : k ≤ N := Finset.le_max' s k hk
        have hkn : k ≤ n := le_trans hkN hnN
        refine ⟨?_, ⟨f^[n - k] x, ?_⟩⟩
        · change q (f^[M] (f^[n] x)) ≠ q (f^[n] x)
          rw [← Function.iterate_add_apply, Nat.add_comm]
          exact hx
        · rw [← Function.iterate_add_apply, Nat.add_sub_of_le hkn]
      · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst hs'
        obtain ⟨n, _, x, hx⟩ := hN 0
        simpa using (show (Set.univ : Set X).Nonempty from ⟨f^[n] x, Set.mem_univ _⟩)
    exact hsource
  have hclosed : ∀ n : ℕ, IsClosed (mismatch ∩ Set.range (f^[n])) := by
    intro n
    exact hmismatch_closed.inter (isCompact_range (hf.iterate n)).isClosed
  have hstable : (mismatch ∩ ⋂ n : ℕ, Set.range (f^[n])).Nonempty := by
    simpa only [inter_iInter] using
      (CompactSpace.iInter_nonempty hclosed hfinite_intersections)
  exact hmismatch_core hstable

/- Once the tail law is known, a whole observation name is determined by a
   finite prefix. This is the finite-state consequence consumed by the
   stable-core exact-name stages. -/
theorem finite_observation_name_injective_of_eventually_periodic
    {X D : Type*}
    (f : X → X) (q : X → D) (N M : ℕ) (hM : 0 < M)
    (htail : ∀ n : ℕ, N ≤ n → ∀ x : X,
      q (f^[n + M] x) = q (f^[n] x)) :
    Set.InjOn (fun w : ℕ → D => fun k : Fin (N + M) => w k)
      (Set.range (fun x n => q (f^[n] x))) := by
  intro w hw w' hw' hpref
  rcases hw with ⟨x, rfl⟩
  rcases hw' with ⟨y, rfl⟩
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k < N + M
      · simpa using congrFun hpref ⟨k, hk⟩
      · have hNk : N ≤ k - M := by omega
        have hlt : k - M < k := by omega
        change q (f^[k] x) = q (f^[k] y)
        have hxTail := htail (k - M) hNk x
        have hyTail := htail (k - M) hNk y
        rw [show k - M + M = k by omega] at hxTail hyTail
        rw [hxTail, hyTail]
        exact ih (k - M) hlt

/- The finite-prefix injection supplies the exact finite state space of
   complete observation names, including names of transient source points. -/
theorem finite_observation_range_finite_of_stable_core_periodic
    {X D : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (f : X → X) (q : X → D)
    (hf : Continuous f) (hq : Continuous q)
    (M : ℕ) (hM : 0 < M)
    (hcore : ∀ a ∈ (⋂ n : ℕ, Set.range (f^[n])),
      q (f^[M] a) = q a) :
    (Set.range (fun x n => q (f^[n] x))).Finite := by
  obtain ⟨N, htail⟩ :=
    finite_observation_eventually_periodic_of_stable_core_periodic f q hf hq M hcore
  have hinj := finite_observation_name_injective_of_eventually_periodic f q N M hM htail
  let names := Set.range (fun x n => q (f^[n] x))
  let restrict : names → (Fin (N + M) → D) := fun w k => w.val k
  have hr : Injective restrict := by
    intro a b hab
    apply Subtype.ext
    exact hinj a.property b.property hab
  have : Finite names := Finite.of_injective restrict hr
  exact Set.toFinite names

#print axioms finite_observation_eventually_periodic_of_stable_core_periodic
#print axioms finite_observation_name_injective_of_eventually_periodic
#print axioms finite_observation_range_finite_of_stable_core_periodic

end D5.S1.Dynamics.Shadowing
