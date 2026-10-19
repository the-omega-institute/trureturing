/- GID: D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim; result=D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.result; claim=D5/S3/StatisticalMechanics/GlauberNeighbourhoodPassivityRefutation.claim
   digest: A Petersen-graph Glauber annealing run violates neighbourhood passivity. -/

import D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation
import D5.S3.PrimeGaps.ShortTranslateClosure

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

private theorem gibbs_log (x : ℝ) (hx : 0 < x) :
    gibbs energy (Real.log x) =
      fun i => (1 / x ^ levels i) / ∑ j, (1 / x ^ levels j) := by
  funext i
  simp (config := { congrConsts := false }) only [gibbs.eq_1, weights_log x hx]

private theorem gibbs_initial :
    gibbs energy (Real.log (11 / 10)) =
      ![1771561000 / 15937424601, 1610510000 / 15937424601,
        1331000000 / 15937424601, 1210000000 / 15937424601,
        1464100000 / 15937424601, 1948717100 / 15937424601,
        1100000000 / 15937424601, 2357947691 / 15937424601,
        2143588810 / 15937424601, 1000000000 / 15937424601] := by
  rw [gibbs_log _ (by norm_num)]
  funext i
  fin_cases i <;> norm_num (config := { congrConsts := false }) [levels.eq_1, Fin.sum_univ_succ]

private theorem gibbs_four :
    gibbs energy (Real.log 4) =
      ![4096 / 349525, 1024 / 349525, 64 / 349525, 16 / 349525, 256 / 349525,
        16384 / 349525, 4 / 349525, 262144 / 349525, 65536 / 349525, 1 / 349525] := by
  rw [gibbs_log _ (by norm_num)]
  funext i
  fin_cases i <;> norm_num (config := { congrConsts := false }) [levels.eq_1, Fin.sum_univ_succ]

private theorem gibbs_eight :
    gibbs energy (Real.log 8) =
      ![262144 / 153391689, 32768 / 153391689, 512 / 153391689, 64 / 153391689,
        4096 / 153391689, 2097152 / 153391689, 8 / 153391689, 134217728 / 153391689,
        16777216 / 153391689, 1 / 153391689] := by
  rw [gibbs_log _ (by norm_num)]
  funext i
  fin_cases i <;> norm_num (config := { congrConsts := false }) [levels.eq_1, Fin.sum_univ_succ]

private theorem partition_pos (b : ℝ) :
    0 < ∑ i : Fin 10, Real.exp (-b * energy i) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

private theorem gibbs_positive (b : ℝ) (i : Fin 10) : 0 < gibbs energy b i := by
  rw [gibbs.eq_1]
  exact div_pos (Real.exp_pos _) (partition_pos b)

private theorem gibbs_probability (b : ℝ) :
    D5.S3.TotalVariation.CycleSingleCutMinimax.Probability (gibbs energy b) := by
  refine ⟨fun i => (gibbs_positive b i).le, ?_⟩
  simp (config := { congrConsts := false }) only [gibbs.eq_1]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos b))

private theorem edge_bounds (b : ℝ) (i j : Fin 10) :
    0 ≤ edgeWeight 3 adj energy b i j ∧ edgeWeight 3 adj energy b i j ≤ 1 / 3 := by
  rw [edgeWeight.eq_1]
  simp (config := { congrConsts := false }) only [Matrix.of_apply]
  split_ifs
  · have hi := gibbs_positive b i
    have hj := gibbs_positive b j
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ (mul_pos (by norm_num) (add_pos hi hj))).mpr
    linarith
  · norm_num

private theorem outflow_le (b : ℝ) (j : Fin 10) :
    (∑ i, edgeWeight 3 adj energy b i j) ≤ 1 := by
  calc
    (∑ i, edgeWeight 3 adj energy b i j) =
        ∑ i ∈ Finset.univ.filter (fun i => adj i j), edgeWeight 3 adj energy b i j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : adj i j
      · rw [if_pos h]
      · rw [if_neg h]
        simp (config := { congrConsts := false }) only [edgeWeight.eq_1, Matrix.of_apply, if_neg h]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => adj i j), (1 / 3 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (edge_bounds b i j).2)
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, adj_regular.2.2.2 j]
      norm_num

private theorem glauber_stochastic (b : ℝ) :
    (∀ i j, 0 ≤ glauber 3 adj energy b i j) ∧
      (∀ j, (∑ i, glauber 3 adj energy b i j) = 1) := by
  constructor
  · intro i j
    rw [glauber.eq_1]
    simp (config := { congrConsts := false }) only [Matrix.of_apply]
    by_cases h : i = j
    · rw [if_pos h]
      exact sub_nonneg.mpr (outflow_le b j)
    · rw [if_neg h]
      exact (edge_bounds b i j).1
  · intro j
    have hdiag : edgeWeight 3 adj energy b j j = 0 := by
      simp (config := { congrConsts := false }) only [edgeWeight.eq_1, Matrix.of_apply, if_neg (adj_regular.2.2.1 j)]
    calc
      (∑ i, glauber 3 adj energy b i j) =
          glauber 3 adj energy b j j +
            ∑ i ∈ Finset.univ.erase j, glauber 3 adj energy b i j :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      _ = (1 - ∑ i, edgeWeight 3 adj energy b i j) +
          ∑ i ∈ Finset.univ.erase j, edgeWeight 3 adj energy b i j := by
        congr 1
        · simp (config := { congrConsts := false }) only [glauber.eq_1, Matrix.of_apply, ite_true]
        · apply Finset.sum_congr rfl
          intro i hi
          simp (config := { congrConsts := false }) only [glauber.eq_1, Matrix.of_apply, if_neg (Finset.ne_of_mem_erase hi)]
      _ = 1 := by
        rw [Finset.sum_erase (f := fun i => edgeWeight 3 adj energy b i j) _ hdiag]
        ring

private theorem run_isSA : isSARun 3 adj energy beta run := by
  refine ⟨?_, rfl, fun _ => rfl⟩
  intro k
  induction k with
  | zero =>
    rw [run.eq_1]
    exact gibbs_probability (beta 0)
  | succ k ih =>
    exact probability_mulVec (glauber_stochastic (beta (k + 1))).1
      (glauber_stochastic (beta (k + 1))).2 ih

private noncomputable def oneState : Fin 10 → ℝ :=
  ![6495040420 / 47812273803, 1579228369400 / 12287754367371,
    531822026923 / 11522757986523, 160582769930 / 11522757986523,
    442180927000 / 4095918122457, 4048016885 / 47812273803,
    49100916611546 / 1388516243512923, 2707415959783376 / 11662677190645065,
    268789869032696 / 1302071652477099, 782236372623151 / 87058739692823535]

private theorem run_one_formula :
    run 1 = (glauber 3 adj energy (Real.log 4)).mulVec
      (gibbs energy (Real.log (11 / 10))) := by
  change (glauber 3 adj energy (beta 1)).mulVec (gibbs energy (beta 0)) = _
  have hb0 : beta 0 = Real.log (11 / 10) := by norm_num (config := { congrConsts := false }) [beta.eq_1, q.eq_1]
  have hb1 : beta 1 = Real.log 4 := by norm_num (config := { congrConsts := false }) [beta.eq_1, q.eq_1]
  rw [hb0, hb1]

private theorem run_one_0 : run 1 0 = oneState 0 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_1 : run 1 1 = oneState 1 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_2 : run 1 2 = oneState 2 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_3 : run 1 3 = oneState 3 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_4 : run 1 4 = oneState 4 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_5 : run 1 5 = oneState 5 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_6 : run 1 6 = oneState 6 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_7 : run 1 7 = oneState 7 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_8 : run 1 8 = oneState 8 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one_9 : run 1 9 = oneState 9 := by
  rw [run_one_formula, gibbs_initial]
  norm_num (config := { decide := true, congrConsts := false }) [Matrix.mulVec, dotProduct, glauber.eq_1, edgeWeight.eq_1, gibbs_four,
    adj.eq_1, oneState.eq_1, Matrix.cons_val, Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

private theorem run_one : run 1 = oneState := by
  funext i
  fin_cases i
  · exact run_one_0
  · exact run_one_1
  · exact run_one_2
  · exact run_one_3
  · exact run_one_4
  · exact run_one_5
  · exact run_one_6
  · exact run_one_7
  · exact run_one_8
  · exact run_one_9

private theorem passivity_value :
    neighbourhoodPassivity 3 adj energy beta run 1 0 =
      -1454086156987 / 205381037283201 := by
  have hb2 : beta (1 + 1) = Real.log 8 := by norm_num (config := { congrConsts := false }) [beta.eq_1, q.eq_1]
  rw [neighbourhoodPassivity.eq_1, hb2, gibbs_eight, run_one]
  norm_num (config := { decide := true, congrConsts := false }) [adj.eq_1, oneState.eq_1, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.succ, Fin.reduceFinMk, Fin.reduceEq]

theorem result : ¬ claim := by
  intro h
  have hnonneg := h 10 3 adj energy beta run adj_regular adj_connected energy_injective
    beta_spec.1 beta_spec.2 run_isSA 1 0
  rw [passivity_value] at hnonneg
  norm_num at hnonneg

end D5.S3.StatisticalMechanics.GlauberNeighbourhoodPassivityRefutation
