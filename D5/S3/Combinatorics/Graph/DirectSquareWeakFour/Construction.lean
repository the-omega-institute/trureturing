/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every direct-square order at least four has an equality-size landmark construction. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Design

set_option autoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset HammingWeakTwoMetricDimension

/-- The 4-by-4 incidence design. -/
private def block4 : Finset (Fin 4 × Fin 4) :=
  {(0,1), (0,2), (0,3), (1,0), (1,1), (2,0), (2,2), (3,0),
    (3,3)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block4_good : Good block4 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block4]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block4_card : block4.card = 9 := by decide

/-- The 5-by-5 incidence design. -/
private def block5 : Finset (Fin 5 × Fin 5) :=
  {(0,0), (0,2), (0,3), (1,1), (1,2), (1,4), (2,0), (2,1),
    (3,1), (3,3), (4,0), (4,4)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block5_good : Good block5 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block5]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block5_card : block5.card = 12 := by decide

/-- The 6-by-6 incidence design. -/
private def block6 : Finset (Fin 6 × Fin 6) :=
  {(0,0), (0,2), (0,3), (1,2), (1,4), (1,5), (2,0), (2,1),
    (3,1), (3,3), (4,0), (4,4), (5,1), (5,5)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block6_good : Good block6 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block6]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block6_card : block6.card = 14 := by decide

/-- The 7-by-7 incidence design. -/
private def block7 : Finset (Fin 7 × Fin 7) :=
  {(0,2), (0,3), (0,4), (1,2), (1,5), (1,6), (2,0), (2,1),
    (3,0), (3,3), (4,1), (4,4), (5,0), (5,5), (6,1), (6,6)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block7_good : Good block7 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block7]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block7_card : block7.card = 16 := by decide

/-- The 8-by-8 incidence design. -/
private def block8 : Finset (Fin 8 × Fin 8) :=
  {(0,2), (0,4), (0,5), (1,2), (1,6), (1,7), (2,0), (2,3),
    (3,1), (3,3), (4,0), (4,4), (5,1), (5,5), (6,0), (6,6),
    (7,1), (7,7)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block8_good : Good block8 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block8]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block8_card : block8.card = 18 := by decide

/-- The 9-by-9 incidence design. -/
private def block9 : Finset (Fin 9 × Fin 9) :=
  {(0,2), (0,5), (0,6), (1,3), (1,7), (1,8), (2,2), (2,3),
    (3,0), (3,4), (4,1), (4,4), (5,0), (5,5), (6,1), (6,6),
    (7,0), (7,7), (8,1), (8,8)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block9_good : Good block9 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block9]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block9_card : block9.card = 20 := by decide

/-- The 10-by-10 incidence design. -/
private def block10 : Finset (Fin 10 × Fin 10) :=
  {(0,2), (0,4), (0,8), (1,3), (1,5), (1,9), (2,2), (2,3),
    (3,4), (3,5), (4,0), (4,6), (5,1), (5,6), (6,0), (6,7),
    (7,1), (7,7), (8,0), (8,8), (9,1), (9,9)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block10_good : Good block10 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block10]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block10_card : block10.card = 22 := by decide

/-- The 11-by-11 incidence design. -/
private def block11 : Finset (Fin 11 × Fin 11) :=
  {(0,2), (0,4), (0,6), (1,3), (1,5), (1,7), (2,2), (2,3),
    (3,4), (3,5), (4,6), (4,7), (5,0), (5,8), (6,1), (6,8),
    (7,0), (7,9), (8,1), (8,9), (9,0), (9,10), (10,1), (10,10)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block11_good : Good block11 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block11]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block11_card : block11.card = 24 := by decide

/-- The 12-by-12 incidence design. -/
private def block12 : Finset (Fin 12 × Fin 12) :=
  {(0,3), (0,4), (0,6), (1,3), (1,5), (1,7), (2,6), (2,8),
    (2,11), (3,4), (3,5), (4,7), (4,8), (5,0), (5,1), (6,0),
    (6,9), (7,1), (7,9), (8,0), (8,2), (9,1), (9,10), (10,2),
    (10,10), (11,2), (11,11)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block12_good : Good block12 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block12]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block12_card : block12.card = 27 := by decide

/-- The 13-by-13 incidence design. -/
private def block13 : Finset (Fin 13 × Fin 13) :=
  {(0,3), (0,4), (0,6), (1,3), (1,5), (1,7), (2,6), (2,8),
    (2,12), (3,4), (3,5), (4,7), (4,8), (5,0), (5,1), (6,0),
    (6,9), (7,1), (7,9), (8,0), (8,10), (9,2), (9,10), (10,1),
    (10,11), (11,2), (11,11), (12,2), (12,12)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block13_good : Good block13 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block13]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block13_card : block13.card = 29 := by decide

/-- The 14-by-14 incidence design. -/
private def block14 : Finset (Fin 14 × Fin 14) :=
  {(0,3), (0,4), (0,6), (1,3), (1,5), (1,7), (2,6), (2,8),
    (2,13), (3,4), (3,5), (4,7), (4,8), (5,0), (5,9), (6,1),
    (6,9), (7,0), (7,10), (8,1), (8,10), (9,0), (9,11), (10,2),
    (10,11), (11,1), (11,12), (12,2), (12,12), (13,2), (13,13)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block14_good : Good block14 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block14]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block14_card : block14.card = 31 := by decide

/-- The 15-by-15 incidence design. -/
private def block15 : Finset (Fin 15 × Fin 15) :=
  {(0,3), (0,4), (0,6), (1,3), (1,5), (1,8), (2,7), (2,9),
    (2,14), (3,4), (3,5), (4,6), (4,7), (5,8), (5,9), (6,0),
    (6,10), (7,1), (7,10), (8,0), (8,11), (9,1), (9,11), (10,0),
    (10,12), (11,2), (11,12), (12,1), (12,13), (13,2), (13,13), (14,2),
    (14,14)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block15_good : Good block15 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block15]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block15_card : block15.card = 33 := by decide

/-- The 16-by-16 incidence design. -/
private def block16 : Finset (Fin 16 × Fin 16) :=
  {(0,3), (0,5), (0,7), (1,4), (1,6), (1,9), (2,8), (2,10),
    (2,15), (3,3), (3,4), (4,5), (4,6), (5,7), (5,8), (6,9),
    (6,10), (7,0), (7,11), (8,1), (8,11), (9,0), (9,12), (10,1),
    (10,12), (11,0), (11,13), (12,2), (12,13), (13,1), (13,14), (14,2),
    (14,14), (15,2), (15,15)}

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block16_good : Good block16 := by
  unfold Good
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp only [leftCount, rightCount, block16]
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxSynthPendingDepth 64 in
private theorem block16_card : block16.card = 35 := by decide

/-- All base sizes needed by the residue construction have exact good designs. -/
private theorem base_design (n : ℕ) (hn : 4 ≤ n) (hm : n ≤ 16) :
    ∃ S : Finset (Fin n × Fin n), Good S ∧
      S.card = 2*n + (2*n+10)/11 + (if n = 5 then 1 else 0) := by
  interval_cases n
  · exact ⟨block4, block4_good, block4_card⟩
  · exact ⟨block5, block5_good, block5_card⟩
  · exact ⟨block6, block6_good, block6_card⟩
  · exact ⟨block7, block7_good, block7_card⟩
  · exact ⟨block8, block8_good, block8_card⟩
  · exact ⟨block9, block9_good, block9_card⟩
  · exact ⟨block10, block10_good, block10_card⟩
  · exact ⟨block11, block11_good, block11_card⟩
  · exact ⟨block12, block12_good, block12_card⟩
  · exact ⟨block13, block13_good, block13_card⟩
  · exact ⟨block14, block14_good, block14_card⟩
  · exact ⟨block15, block15_good, block15_card⟩
  · exact ⟨block16, block16_good, block16_card⟩


/-- The proposed exact natural-number value; division expresses the ceiling. -/
def target (n : ℕ) : ℕ := 2*n + (2*n+10)/11 + (if n = 5 then 1 else 0)

/-- An eleven-by-eleven block increases order by eleven and cardinality by twenty-four. -/
theorem all_design (n : ℕ) (hn : 4 ≤ n) :
    ∃ S : Finset (Fin n × Fin n), Good S ∧ S.card = target n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 16
    · exact base_design n hn hsmall
    have hn' : 4 ≤ n-11 := by omega
    obtain ⟨S,hS,hcard⟩ := ih (n-11) (by omega) hn'
    obtain ⟨T,hT,ht⟩ := base_design 11 (by omega) (by omega)
    let f : Fin (n-11) ⊕ Fin 11 ≃ Fin n :=
      finSumFinEquiv.trans (finCongr (by omega))
    refine ⟨(join S T).map (f.toEmbedding.prodMap f.toEmbedding),
      good_map f f (good_join hS hT), ?_⟩
    rw [card_map, join_card, hcard, ht]
    simp only [target]
    have hn5 : n ≠ 5 := by omega
    have hn'5 : n-11 ≠ 5 := by omega
    norm_num only [if_neg hn5, if_neg hn'5, show ¬(11 : ℕ) = 5 by decide, if_false]
    have hsum : n-11+11 = n := by omega
    omega

/-- An actual weak-four landmark set attains the proposed value at every order. -/
theorem construction (n : ℕ) (hn : 4 ≤ n) :
    ∃ S : Finset (Fin n × Fin n), IsWeakFour S ∧ S.card = target n := by
  obtain ⟨S,hS,hcard⟩ := all_design n hn
  exact ⟨S, good_resolves (by omega) S hS, hcard⟩

/-- This construction lies strictly below the low-degree escape threshold. -/
theorem target_lt_three (n : ℕ) (hn : 4 ≤ n) : target n < 3*n-2 := by
  unfold target
  split_ifs <;> omega

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
