/- GID: D5/S1/Dynamics/Shadowing/FiniteTreeObstruction
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteTreeObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-terminal history amplification contradicts a strict all-time finite Bowen bound.
-/

import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic

/-! Reusable terminal-history obstruction for strict forward Bowen bounds. -/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing

namespace FiniteTreeObstruction

open IntervalObstruction

variable {X : Type*} [MetricSpace X]
variable {f : X → X} {K : Set X} {η ε : ℝ} {N : ℕ}

/-! A history family is deliberately a statement about actual subsets of the
carrier.  It contains no tree or dynamical conclusion; the tree construction
must supply such families from its own geometry. -/

structure CommonTerminalFamily (f : X → X) (K : Set X) (η : ℝ) (ι : Type*) where
  domain : ι → Set X
  inside : ∀ i, domain i ⊆ K
  disjoint : ∀ i j, i ≠ j → Disjoint (domain i) (domain j)
  time : ℕ
  terminal : Set X
  terminal_nonempty : terminal.Nonempty
  onto : ∀ i, f^[time] '' domain i = terminal
  small : ∀ s ≤ time, ∀ i j, ∀ x ∈ domain i, ∀ y ∈ domain j,
    dist (f^[s] x) (f^[s] y) < η

namespace CommonTerminalFamily

variable {ι : Type*}

/- The proof is the exact finite-cardinal argument used by the interval
obstruction, but it is independent of coordinates, connectedness, or an
invariant subset. -/
theorem card_le [Fintype ι] [Nonempty ι]
    (H : CommonTerminalFamily f K η ι)
    (hε : 0 < ε) (hηε : η ≤ ε)
    (hB : ForwardBowenBound f K ε N) : Fintype.card ι ≤ N := by
  classical
  obtain ⟨z, hz⟩ := H.terminal_nonempty
  have hpre : ∀ i, ∃ x ∈ H.domain i, f^[H.time] x = z := by
    intro i
    exact (H.onto i).symm.subset hz
  choose x hx hT using hpre
  have hxi : Injective x := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (H.disjoint i j hne) (hx i)
      (hij.symm ▸ hx j)
  by_contra! hm
  let e := (Fintype.equivFin ι).symm
  apply no_coalescing_witnesses hB hε hm (fun i => x (e i))
    (hxi.comp e.injective) (fun i => H.inside (e i) (hx (e i)))
  · intro i j s hs
    exact (H.small s hs (e i) (e j) _ (hx (e i)) _ (hx (e j))).trans_le hηε
  · intro i j
    exact (hT (e i)).trans (hT (e j)).symm

end CommonTerminalFamily

/- A witness packages only a finite family of actual disjoint carrier sets.
The type carries no recurrence, fold, covering, or nonexistence premise. -/
structure AmplificationWitness (f : X → X) (K : Set X) (η : ℝ) (N : ℕ) where
  index : Type*
  fintype : Fintype index
  nonempty : Nonempty index
  family : CommonTerminalFamily f K η index
  large : N < @Fintype.card index fintype

/- Any one amplified family already contradicts the proposed uniform bound. -/
theorem amplification_contradiction
    (hε : 0 < ε) (hηε : η ≤ ε)
    (hB : ForwardBowenBound f K ε N)
    (w : AmplificationWitness f K η N) : False := by
  letI := w.fintype
  letI := w.nonempty
  have hcard := CommonTerminalFamily.card_le w.family hε hηε hB
  exact (not_le_of_gt w.large) hcard

/- This is the reusable logical endpoint for the finite-tree argument.  A
 tree carrier must prove the amplification premise from its finite edge
 realization; this theorem does not take that premise as a field of a tree. -/
theorem not_finitelyPositiveExpansive_of_amplification
    (hfam : ∀ (ε : ℝ), 0 < ε → ∀ N : ℕ, 1 ≤ N →
      ∃ w : AmplificationWitness f (univ : Set X) ε N) :
    ¬FinitelyPositiveExpansive f := by
  rintro ⟨ε, hε, N, hN, hB⟩
  obtain ⟨w⟩ := hfam ε hε N hN
  exact amplification_contradiction hε le_rfl hB w

end FiniteTreeObstruction
end D5.S1.Dynamics.Shadowing
