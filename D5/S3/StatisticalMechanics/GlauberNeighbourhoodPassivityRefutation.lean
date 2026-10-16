/- GID: D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim; result=D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result; claim=D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim
   digest: A Petersen-graph Glauber annealing run violates neighbourhood passivity. -/

import D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
import D5.S3.PrimeGaps.ShortTranslateClosure
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation

open scoped BigOperators
open GlauberRelaxationOrderRefutation

/-! The Gibbs weights in neighbourhood passivity are those of the next step,
as in Eq. (41) of arXiv:2311.10424v1. -/

noncomputable def neighbourhoodPassivity {N : ℕ} (_n : ℕ)
    (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (β : ℕ → ℝ) (p : ℕ → Fin N → ℝ)
    (k : ℕ) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => A i j),
    (gibbs E (β (k + 1)) i - gibbs E (β (k + 1)) j) /
      (gibbs E (β (k + 1)) i + gibbs E (β (k + 1)) j) * (p k i - p k j)

def claim : Prop :=
  ∀ (N n : ℕ) (A : Fin N → Fin N → Prop) [DecidableRel A]
    (E : Fin N → ℝ) (β : ℕ → ℝ) (p : ℕ → Fin N → ℝ),
    regularNeighborhood n A → (SimpleGraph.fromRel A).Connected →
    Function.Injective E → StrictMono β → 0 < β 0 → isSARun n A E β p →
    ∀ (k : ℕ) (i : Fin N), 0 ≤ neighbourhoodPassivity n A E β p k i

private def adj (i j : Fin 10) : Prop :=
  j ∈ (![({1, 4, 5} : Finset (Fin 10)), {0, 2, 6}, {1, 3, 7}, {2, 4, 8},
    {0, 3, 9}, {0, 7, 8}, {1, 8, 9}, {2, 5, 9}, {3, 5, 6}, {4, 6, 7}]) i

private instance adjDecidable : DecidableRel adj := fun i j =>
  show Decidable (j ∈ (![({1, 4, 5} : Finset (Fin 10)), {0, 2, 6}, {1, 3, 7},
    {2, 4, 8}, {0, 3, 9}, {0, 7, 8}, {1, 8, 9}, {2, 5, 9}, {3, 5, 6},
    {4, 6, 7}]) i) from inferInstance

private def levels : Fin 10 → ℕ := ![3, 4, 6, 7, 5, 2, 8, 0, 1, 9]

private noncomputable def energy (i : Fin 10) : ℝ := levels i

private noncomputable def q (k : ℕ) : ℝ := if k = 0 then 11 / 10 else 4 * k

private noncomputable def beta (k : ℕ) : ℝ := Real.log (q k)

private noncomputable def run : ℕ → Fin 10 → ℝ :=
  Nat.rec (gibbs energy (beta 0))
    (fun k v => (glauber 3 adj energy (beta (k + 1))).mulVec v)

private theorem adj_regular : regularNeighborhood 3 adj := by
  unfold regularNeighborhood
  decide

private theorem adj_connected : (SimpleGraph.fromRel adj).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, ?_⟩
  intro i
  fin_cases i
  · exact SimpleGraph.Reachable.refl _
  · exact (show (SimpleGraph.fromRel adj).Adj 0 1 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 1 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 1 2 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 4 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 4 3 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 4 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 5 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 1 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 1 6 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 5 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 5 7 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 5 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 5 8 from by decide).reachable
  · exact (show (SimpleGraph.fromRel adj).Adj 0 4 from by decide).reachable.trans
      (show (SimpleGraph.fromRel adj).Adj 4 9 from by decide).reachable

private theorem energy_injective : Function.Injective energy := by
  intro i j h
  have hlevels : levels i = levels j := Nat.cast_injective h
  have hinj : Function.Injective levels := by decide
  exact hinj hlevels

private theorem q_spec : (∀ k, 1 < q k) ∧ StrictMono q := by
  constructor
  · intro k
    rw [q.eq_1]
    split_ifs with hk
    · norm_num
    · have hkpos : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      linarith
  · intro i j hij
    have hj : j ≠ 0 := by omega
    by_cases hi : i = 0
    · subst i
      rw [q.eq_1, q.eq_1, if_pos rfl, if_neg hj]
      have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)
      linarith
    · rw [q.eq_1, q.eq_1, if_neg hi, if_neg hj]
      exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr hij) (by norm_num)

private theorem beta_spec : StrictMono beta ∧ 0 < beta 0 := by
  refine ⟨?_, Real.log_pos (q_spec.1 0)⟩
  intro i j hij
  exact Real.log_lt_log (lt_trans zero_lt_one (q_spec.1 i)) (q_spec.2 hij)

private theorem weights_log (x : ℝ) (hx : 0 < x) (i : Fin 10) :
    Real.exp (-Real.log x * energy i) = 1 / x ^ levels i := by
  rw [energy.eq_1]
  rw [show -Real.log x * (levels i : ℝ) = -(levels i : ℝ) * Real.log x by ring]
  exact LongGapsBetweenPrimes.exp_neg_nat_mul_log hx (levels i)

end D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation
