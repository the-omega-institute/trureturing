/- GID: D5/S3/Observer/ProbabilisticClosure/DiscreteMemoryElimination
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/DiscreteMemoryElimination
   mirror-E: none(waiver:exact-linear-evolution)
   anchors: []
   utility: none
   digest: Elimination of an actual hidden recurrence yields an initial-state term
     and a causal memory sum; silent hidden inputs are the existing eventual kernel. -/

import D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.DiscreteMemoryElimination

variable {R V H : Type*} [Ring R]
  [AddCommGroup V] [Module R V] [AddCommGroup H] [Module R H]

/-- Actual block evolution. The hidden component is propagated, never reset or
replaced by an independently chosen representative between steps. -/
def evolve (A : V →ₗ[R] V) (B : H →ₗ[R] V)
    (C : V →ₗ[R] H) (D : H →ₗ[R] H) : Nat → V × H → V × H
  | 0, x => x
  | n + 1, x =>
      let u := evolve A B C D n x
      (A u.1 + B u.2, C u.1 + D u.2)

/-- A past visible input enters the hidden dynamics through C, spends k steps
there, and returns through B. This is an operator, not the hidden state itself. -/
def memoryKernel (B : H →ₗ[R] V) (C : V →ₗ[R] H)
    (D : H →ₗ[R] H) (k : Nat) : V →ₗ[R] V := B.comp ((D ^ k).comp C)

/-- Exact discrete memory equation for all initial states and all times. The
initial hidden contribution B D^n h0 is kept separately from the history sum. -/
theorem exact_memory_equation
    (A : V →ₗ[R] V) (B : H →ₗ[R] V)
    (C : V →ₗ[R] H) (D : H →ₗ[R] H) (x : V × H) (n : Nat) :
    (evolve A B C D (n + 1) x).1 =
      A (evolve A B C D n x).1 + B ((D ^ n) x.2) +
        ∑ i ∈ Finset.range n,
          memoryKernel B C D (n - 1 - i) (evolve A B C D i x).1 := by
  have stepPower (k : Nat) (u : H) : D ((D ^ k) u) = (D ^ (k + 1)) u := by
    change (D * D ^ k) u = _
    rw [← pow_succ']
  have hidden : ∀ t : Nat, (evolve A B C D t x).2 =
      (D ^ t) x.2 + ∑ i ∈ Finset.range t,
        (D ^ (t - 1 - i)) (C (evolve A B C D i x).1) := by
    intro t
    induction t with
    | zero => simp [evolve]
    | succ t ih =>
      calc
        (evolve A B C D (t + 1) x).2 =
            C (evolve A B C D t x).1 + D (evolve A B C D t x).2 := rfl
        _ = C (evolve A B C D t x).1 +
            (D ((D ^ t) x.2) + ∑ i ∈ Finset.range t,
              D ((D ^ (t - 1 - i)) (C (evolve A B C D i x).1))) := by
          rw [ih, map_add, map_sum]
        _ = C (evolve A B C D t x).1 +
            ((D ^ (t + 1)) x.2 + ∑ i ∈ Finset.range t,
              (D ^ (t - i)) (C (evolve A B C D i x).1)) := by
          rw [stepPower]
          congr 2
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < t := Finset.mem_range.mp hi
          rw [stepPower, show t - 1 - i + 1 = t - i by omega]
        _ = (D ^ (t + 1)) x.2 + ∑ i ∈ Finset.range (t + 1),
              (D ^ (t + 1 - 1 - i)) (C (evolve A B C D i x).1) := by
          rw [Finset.sum_range_succ]
          simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero]
          change _ = (D ^ (t + 1)) x.2 +
            ((∑ i ∈ Finset.range t,
              (D ^ (t - i)) (C (evolve A B C D i x).1)) +
                C (evolve A B C D t x).1)
          abel
  change A (evolve A B C D n x).1 + B (evolve A B C D n x).2 = _
  rw [hidden n, map_add, map_sum]
  simp only [memoryKernel, LinearMap.comp_apply]
  abel

/-- For a zero visible perturbation, every visible future vanishes exactly when
the hidden perturbation belongs to the pre-existing eventual kernel of (B,D).
Thus the actual coupled dynamics ignores precisely those hidden directions,
not all of H and not the complement of one distinguished actual state. -/
theorem zero_visible_iff_eventual_kernel
    (A : V →ₗ[R] V) (B : H →ₗ[R] V)
    (C : V →ₗ[R] H) (D : H →ₗ[R] H) (h : H) :
    (∀ n : Nat, (evolve A B C D n (0, h)).1 = 0) ↔
      h ∈ D5.S3.Observer.LinearMemory.ZeroMemoryCriterion.eventualKernel B D := by
  constructor
  · intro hv
    have hidden : ∀ n : Nat, (evolve A B C D n (0, h)).2 = (D ^ n) h := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change C (evolve A B C D n (0, h)).1 +
          D (evolve A B C D n (0, h)).2 = _
        rw [hv n, map_zero, zero_add, ih]
        change (D * D ^ n) h = _
        rw [← pow_succ']
    intro n
    have hn := hv (n + 1)
    change A (evolve A B C D n (0, h)).1 +
      B (evolve A B C D n (0, h)).2 = 0 at hn
    rw [hv n, map_zero, zero_add, hidden n] at hn
    change B ((D^[n]) h) = 0
    simpa only [Module.End.pow_apply] using hn
  · intro hs
    have coupled : ∀ n : Nat, evolve A B C D n (0, h) = (0, (D ^ n) h) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have hn : B ((D ^ n) h) = 0 := by
          simpa only [Module.End.pow_apply] using hs n
        change (A (evolve A B C D n (0, h)).1 + B (evolve A B C D n (0, h)).2,
          C (evolve A B C D n (0, h)).1 + D (evolve A B C D n (0, h)).2) = _
        rw [ih]
        simp only [map_zero, zero_add, hn]
        apply Prod.ext
        · rfl
        · change (D * D ^ n) h = _
          rw [← pow_succ']
    intro n
    exact congrArg Prod.fst (coupled n)

#print axioms exact_memory_equation
#print axioms zero_visible_iff_eventual_kernel

end D5.S3.Observer.ProbabilisticClosure.DiscreteMemoryElimination
