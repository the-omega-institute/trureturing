/- GID: D5/S1/Dynamics/OrbitClosure/WordBallTent
   generality: G
   mirror-B: D5/B/S1/Dynamics/OrbitClosure/WordBallTent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous word-ball tents obstruct uniform invariance for infinite finitely generated actions. -/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.MetricSpace.Defs
public import OmegaBuild.Commands

compile_only_with_mathlib

open Set Function
open scoped Pointwise

namespace D5.S1.Dynamics.OrbitClosure.WordBallTent

universe u v

variable {G : Type u} {X : Type v} [Group G] [MetricSpace X] [CompactSpace X]

def wordBall (S : Finset G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => wordBall S n ∪ S.biUnion (fun s => (wordBall S n).image (fun g => s * g))

theorem one_mem_wordBall (S : Finset G) (n : ℕ) : (1 : G) ∈ wordBall S n := by
  induction n with
  | zero => simp [wordBall]
  | succ n ih => exact Finset.mem_union_left _ ih

theorem finite_wordBall (S : Finset G) (n : ℕ) : (wordBall S n).Finite := by
  exact (wordBall S n).finite_toSet

end D5.S1.Dynamics.OrbitClosure.WordBallTent
