/- GID: D5/S3/Combinatorics/Graph/Pressure/MeyerovitchYoungQ61FrequencyGap
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MeyerovitchYoungQ61FrequencyGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A three-matrix frequency relaxation gives the wrong original Q6.1 threshold. -/

import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61Complete
import D5.S1.Dynamics.Symbolic.MeyerovitchYoungQ61Subcritical
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
The one-vertex Alice graph has three loops, and the two-vertex Bob graph is complete.
The three edge-cost matrices yield a clipped translation of the difference between
optimal endpoint scores. Average displacement balance on translation branches gives
an exact frequency optimum strictly above the threshold, whereas every four-letter
block incurs a loss in the actual matrix game.
-/

namespace MeyerovitchYoungQ61FrequencyGap

open Maths Set Filter
open MeyerovitchYoungQ61Complete
  (ConnectsAt Legal completeGraph complete_connects matrixCost matrixMinimum matrixMinimum_spec
    wordCost wordCost_append)
open MeyerovitchYoungQ61Subcritical
  (averageScore clip clip_mem minimumScore minimumScore_eq_average normalized overshoot
    overshoot_nonneg)
open scoped Topology

/-- The three self-loops available to Alice. -/
inductive Letter
  | plus | minus | star
  deriving DecidableEq

instance : Fintype Letter where
  elems := {.plus, .minus, .star}
  complete e := by cases e <;> simp

/-- The shift per letter before enforcing the endpoint constraints. -/
noncomputable def shift : Letter → ℝ
  | .plus => Real.sqrt 2 - 1 / 2
  | .minus => -(2 / 3)
  | .star => (Real.sqrt 2 - 1) / 2

/-- The maximal toll covered by the four-step clipping bound. -/
noncomputable def epsilon : ℝ := Real.sqrt 2 - 4 / 3

/-- The centered reward on the branch where clipping is inactive. -/
noncomputable def reward (c ρ : ℝ) (e : Letter) : ℝ :=
  c + ρ / 8 - if e = .star then ρ else 0

/-- Rows index Bob's departure vertex and columns his arrival vertex. -/
noncomputable def matrices (c ρ : ℝ) (e : Letter) : Matrix Bool Bool ℝ :=
  fun i j => match i, j with
  | false, _ => reward c ρ e + shift e / 2
  | true, false => reward c ρ e + 1 - shift e / 2
  | true, true => reward c ρ e - shift e / 2

/-- Alice may choose any sequence of the three loops. -/
def aliceGraph : EdgeGraph Unit Letter := ⟨fun _ => (), fun _ => ()⟩

private noncomputable def endpointStep (c ρ : ℝ) (z : Bool → ℝ) (e : Letter)
    (j : Bool) : ℝ :=
  min (z false + matrices c ρ e false j) (z true + matrices c ρ e true j)

/-- Minimum scores at the two Bob endpoints, starting at either vertex for free. -/
noncomputable def endpointScores (c ρ : ℝ) (a : List Letter) : Bool → ℝ :=
  a.foldl (endpointStep c ρ) (fun _ => 0)

private theorem endpointScores_snoc (c ρ : ℝ) (a : List Letter) (e : Letter) :
    endpointScores c ρ (a ++ [e]) = endpointStep c ρ (endpointScores c ρ a) e := by
  simp [endpointScores, List.foldl_append]

private theorem wordCost_concat (c ρ : ℝ) (a : List Letter) (e : Letter)
    {s i j : Bool} (p : (completeGraph Bool).Walk s i) (hlen : p.length = a.length) :
    wordCost (matrixCost (matrices c ρ)) (a ++ [e]) (p.concat (i, j) rfl).edges =
      wordCost (matrixCost (matrices c ρ)) a p.edges + matrices c ρ e i j := by
  erw [EdgeGraph.Walk.edges_concat]
  rw [wordCost_append _ (by simpa using hlen.symm)]
  simp [wordCost, matrixCost]

private theorem endpointStep_le (c ρ : ℝ) (z : Bool → ℝ) (e : Letter) (i j : Bool) :
    endpointStep c ρ z e j ≤ z i + matrices c ρ e i j := by
  cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

private theorem endpointScores_spec (c ρ : ℝ) (a : List Letter) (j : Bool) :
    (∃ s, ∃ p : (completeGraph Bool).Walk s j, p.length = a.length ∧
      wordCost (matrixCost (matrices c ρ)) a p.edges = endpointScores c ρ a j) ∧
    ∀ s (p : (completeGraph Bool).Walk s j), p.length = a.length →
      endpointScores c ρ a j ≤ wordCost (matrixCost (matrices c ρ)) a p.edges := by
  induction a using List.reverseRecOn generalizing j with
  | nil =>
    exact ⟨⟨j, .nil, rfl, rfl⟩, fun s p h => by cases p <;> simp_all [endpointScores, wordCost]⟩
  | append_singleton a e ih =>
    rw [endpointScores_snoc]
    constructor
    · have hmin : ∃ i, endpointScores c ρ a i + matrices c ρ e i j =
          endpointStep c ρ (endpointScores c ρ a) e j := by
        unfold endpointStep
        rcases le_total (endpointScores c ρ a false + matrices c ρ e false j)
            (endpointScores c ρ a true + matrices c ρ e true j) with h | h
        · exact ⟨false, (min_eq_left h).symm⟩
        · exact ⟨true, (min_eq_right h).symm⟩
      obtain ⟨i, hi⟩ := hmin
      obtain ⟨s, p, hlen, hp⟩ := (ih i).1
      exact ⟨s, p.concat (i, j) rfl, by simp [hlen],
        (wordCost_concat _ _ _ _ p hlen).trans (by rw [hp, hi])⟩
    · intro s p hlen
      cases p with
      | nil => simp at hlen
      | @concat i p edge h =>
        rcases edge with ⟨i', j'⟩
        change i' = i at h
        subst i'
        have hp : p.length = a.length := by simpa using hlen
        erw [wordCost_concat _ _ _ _ p hp]
        exact (endpointStep_le c ρ _ e i j').trans (add_le_add ((ih i).2 s p hp) le_rfl)

private theorem matrixMinimum_eq_min (c ρ : ℝ) (a : List Letter) :
    matrixMinimum (matrices c ρ) a =
      min (endpointScores c ρ a false) (endpointScores c ρ a true) := by
  obtain ⟨⟨b, hb, hbl, hcost⟩, hbound⟩ := matrixMinimum_spec (matrices c ρ) a
  apply le_antisymm
  · apply le_min
    · obtain ⟨s, p, hlen, hp⟩ := (endpointScores_spec c ρ a false).1
      exact (hbound p.edges ⟨s, false, p, rfl⟩ (by simpa using hlen)).trans_eq hp
    · obtain ⟨s, p, hlen, hp⟩ := (endpointScores_spec c ρ a true).1
      exact (hbound p.edges ⟨s, true, p, rfl⟩ (by simpa using hlen)).trans_eq hp
  · obtain ⟨s, j, p, rfl⟩ := hb
    have hp : p.length = a.length := by simpa using hbl
    rw [← hcost]
    apply le_trans _ ((endpointScores_spec c ρ a j).2 s p hp)
    cases j
    · exact min_le_left _ _
    · exact min_le_right _ _

private noncomputable def difference (z : Bool → ℝ) : ℝ := z false - z true

/-- The actual false-endpoint score minus the true-endpoint score. -/
noncomputable def normalizedState (c ρ : ℝ) (a : List Letter) : ℝ :=
  difference (endpointScores c ρ a)

/-- One centered transition on the endpoint difference and average score. -/
noncomputable def centeredStep (c ρ : ℝ) (q : ℝ × ℝ) (e : Letter) : ℝ × ℝ :=
  (clip 1 (q.1 + shift e), q.2 + reward c ρ e - overshoot 1 (q.1 + shift e) / 2)

/-- Average score accumulated by the centered recurrence from two free endpoints. -/
noncomputable def centeredScore (c ρ : ℝ) (a : List Letter) : ℝ :=
  (a.foldl (centeredStep c ρ) (0, 0)).2

private theorem centeredStep_eq (c ρ : ℝ) (z : Bool → ℝ) (e : Letter) :
    (difference (endpointStep c ρ z e), averageScore (endpointStep c ρ z e)) =
      centeredStep c ρ (difference z, averageScore z) e := by
  set y := difference z + shift e with hy
  have h₀ : z false + matrices c ρ e false false = averageScore z + reward c ρ e + y / 2 := by
    simp only [hy, difference, matrices, averageScore]
    ring
  have h₁ : z true + matrices c ρ e true false = averageScore z + reward c ρ e + (1 - y / 2) := by
    simp only [hy, difference, matrices, averageScore]
    ring
  have h₂ : z true + matrices c ρ e true true = averageScore z + reward c ρ e + (-y / 2) := by
    simp only [hy, difference, matrices, averageScore]
    ring
  have h₃ : z false + matrices c ρ e false true = averageScore z + reward c ρ e + y / 2 := h₀
  simp only [difference, averageScore, endpointStep, centeredStep, h₀, h₁, h₂, h₃,
    Prod.mk.injEq]
  change min (_ + y / 2) (_ + (1 - y / 2)) - min (_ + y / 2) (_ + (-y / 2)) =
      clip 1 y ∧ _ = _ - overshoot 1 y / 2
  by_cases hlo : y ≤ 0
  · have hhi : y ≤ 1 := hlo.trans (by norm_num)
    rw [min_eq_left (add_le_add_right (show y / 2 ≤ 1 - y / 2 by linarith) _),
      min_eq_left (add_le_add_right (show y / 2 ≤ -y / 2 by linarith) _)]
    simp only [clip, overshoot, max_eq_left hlo, min_eq_right (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (neg_nonneg.mpr hlo), max_eq_left (sub_nonpos.mpr hhi)]
    constructor <;> ring
  · have hlo' : 0 ≤ y := le_of_not_ge hlo
    rw [min_eq_right (add_le_add_right (show -y / 2 ≤ y / 2 by linarith) _)]
    by_cases hhi : y ≤ 1
    · rw [min_eq_left (add_le_add_right (show y / 2 ≤ 1 - y / 2 by linarith) _)]
      simp only [clip, overshoot, max_eq_right hlo', min_eq_right hhi,
        max_eq_left (neg_nonpos.mpr hlo'), max_eq_left (sub_nonpos.mpr hhi)]
      constructor <;> ring
    · have hhi' : 1 ≤ y := le_of_not_ge hhi
      rw [min_eq_right (add_le_add_right (show 1 - y / 2 ≤ y / 2 by linarith) _)]
      simp only [clip, overshoot, max_eq_right hlo', min_eq_left hhi',
        max_eq_left (neg_nonpos.mpr hlo'), max_eq_right (sub_nonneg.mpr hhi')]
      constructor <;> ring

private theorem centeredFold_eq (c ρ : ℝ) (a : List Letter) :
    (normalizedState c ρ a, averageScore (endpointScores c ρ a)) =
      a.foldl (centeredStep c ρ) (0, 0) := by
  induction a using List.reverseRecOn with
  | nil => simp [normalizedState, difference, endpointScores, averageScore]
  | append_singleton a e ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold normalizedState at *
    rw [endpointScores_snoc, centeredStep_eq, ih]

/-- Both endpoint scores follow the centered recurrence. Minimizing over the
free final endpoint subtracts half the normalized difference from the average. -/
theorem matrixMinimum_eq_centered (c ρ : ℝ) (a : List Letter) :
    (a.foldl (centeredStep c ρ) (0, 0)).1 = normalizedState c ρ a ∧
    normalizedState c ρ a ∈ Icc 0 1 ∧
    matrixMinimum (matrices c ρ) a = centeredScore c ρ a - normalizedState c ρ a / 2 := by
  have hfold := centeredFold_eq c ρ a
  have hd : normalizedState c ρ a ∈ Icc 0 1 := by
    rw [show normalizedState c ρ a = (a.foldl (centeredStep c ρ) (0, 0)).1 from
      congrArg Prod.fst hfold]
    cases a using List.reverseRecOn with
    | nil => simp
    | append_singleton a e =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, centeredStep]
      exact clip_mem (by norm_num) _
  refine ⟨(congrArg Prod.fst hfold).symm, hd, ?_⟩
  have hdiff : normalized 0 (endpointScores c ρ a) - 0 = -normalizedState c ρ a := by
    simp [normalized, normalizedState, difference, neg_sub]
  rw [matrixMinimum_eq_min, centeredScore, ← hfold]
  change minimumScore (endpointScores c ρ a) = _
  rw [minimumScore_eq_average 0, hdiff, abs_neg, abs_of_nonneg hd.1]

private theorem sqrt_two_bounds : (4 : ℝ) / 3 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  constructor
  · by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hn]
  · by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hn]

private noncomputable def nextState (d : ℝ) (e : Letter) : ℝ := clip 1 (d + shift e)

private noncomputable def toll (ρ : ℝ) (e : Letter) : ℝ :=
  if e = .star then ρ else 0

private noncomputable def loss (ρ : ℝ) (d : ℝ) : List Letter → ℝ
  | [] => 0
  | e :: a => toll ρ e + overshoot 1 (d + shift e) / 2 + loss ρ (nextState d e) a

private theorem nextState_mem (d : ℝ) (e : Letter) : nextState d e ∈ Icc 0 1 :=
  clip_mem (by norm_num) _

private theorem fold_state_mem {d : ℝ} (hd : d ∈ Icc 0 1) (a : List Letter) :
    a.foldl nextState d ∈ Icc 0 1 := by
  induction a generalizing d with
  | nil => exact hd
  | cons e a ih => exact ih (nextState_mem d e)

private theorem loss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℝ) (a : List Letter) :
    0 ≤ loss ρ d a := by
  induction a generalizing d with
  | nil => exact le_rfl
  | cons e a ih =>
    have ht : 0 ≤ toll ρ e := by
      unfold toll
      split <;> first | assumption | exact le_rfl
    exact add_nonneg (add_nonneg ht (div_nonneg (overshoot_nonneg _ _) (by norm_num))) (ih _)

private theorem loss_append (ρ d : ℝ) (a b : List Letter) :
    loss ρ d (a ++ b) = loss ρ d a + loss ρ (a.foldl nextState d) b := by
  induction a generalizing d with
  | nil => simp [loss]
  | cons e a ih => simp [loss, ih, add_assoc]

private theorem centeredFold_formula (c ρ d m : ℝ) (a : List Letter) :
    a.foldl (centeredStep c ρ) (d, m) =
      (a.foldl nextState d, m + (a.length : ℝ) * (c + ρ / 8) - loss ρ d a) := by
  induction a generalizing d m with
  | nil => simp [loss]
  | cons e a ih =>
    rw [List.foldl_cons]
    change a.foldl (centeredStep c ρ)
      (nextState d e, m + reward c ρ e - overshoot 1 (d + shift e) / 2) = _
    rw [ih]
    simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one, Prod.mk.injEq,
      true_and, loss, reward, toll]
    ring

private theorem loss_of_star {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℝ) {a : List Letter}
    (ha : .star ∈ a) : ρ ≤ loss ρ d a := by
  induction a generalizing d with
  | nil => simp at ha
  | cons e a ih =>
    have ho := overshoot_nonneg 1 (d + shift e)
    have hl := loss_nonneg hρ (nextState d e) a
    rcases List.mem_cons.mp ha with h | h
    · subst e
      simp only [loss, toll, ite_true]
      linarith
    · have ht : 0 ≤ toll ρ e := by
        unfold toll
        split <;> first | assumption | exact le_rfl
      have := ih (nextState d e) h
      simp only [loss]
      linarith

private theorem abs_clip_error (y : ℝ) : |y - clip 1 y| = overshoot 1 y := by
  rcases le_or_gt y 0 with hlo | hlo
  · have hhi : y ≤ 1 := hlo.trans (by norm_num)
    simp [clip, overshoot, max_eq_left hlo, max_eq_right (neg_nonneg.mpr hlo),
      max_eq_left (sub_nonpos.mpr hhi), abs_of_nonpos hlo]
  · rcases le_or_gt y 1 with hhi | hhi
    · simp [clip, overshoot, max_eq_right hlo.le, min_eq_right hhi,
        max_eq_left (neg_nonpos.mpr hlo.le), max_eq_left (sub_nonpos.mpr hhi)]
    · simp [clip, overshoot, max_eq_right hlo.le, min_eq_left hhi.le,
        max_eq_left (neg_nonpos.mpr hlo.le), max_eq_right (sub_nonneg.mpr hhi.le),
        abs_of_nonneg (sub_nonneg.mpr hhi.le)]

private theorem displacement_le_loss {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℝ) (a : List Letter) :
    |d + (a.map shift).sum - a.foldl nextState d| ≤ 2 * loss ρ d a := by
  induction a generalizing d with
  | nil => simp [loss]
  | cons e a ih =>
    let y := d + shift e
    let z := nextState d e
    have htel : d + ((e :: a).map shift).sum - (e :: a).foldl nextState d =
        (y - z) + (z + (a.map shift).sum - a.foldl nextState z) := by
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      dsimp [y, z]
      ring
    have ht : 0 ≤ toll ρ e := by
      unfold toll
      split <;> first | assumption | exact le_rfl
    have hp := ih z
    rw [htel]
    refine (abs_add_le _ _).trans ?_
    change |y - clip 1 y| + _ ≤ _
    rw [abs_clip_error]
    simp only [loss]
    dsimp [y, z] at *
    linarith

private theorem sum_shift_le_loss {ρ d : ℝ} (hρ : 0 ≤ ρ) (hd : d ∈ Icc 0 1)
    (a : List Letter) : |(a.map shift).sum| - 1 ≤ 2 * loss ρ d a := by
  let z := a.foldl nextState d
  have hz : z ∈ Icc 0 1 := fold_state_mem hd a
  have hwidth : |z - d| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1, hd.2], by linarith [hz.2, hd.1]⟩
  have htel : (a.map shift).sum = (d + (a.map shift).sum - z) + (z - d) := by ring
  have hb : |(a.map shift).sum| ≤ 2 * loss ρ d a + 1 := calc
    _ = |(d + (a.map shift).sum - z) + (z - d)| := congrArg abs htel
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add (displacement_le_loss hρ d a) hwidth)
  linarith

private theorem forcingPattern_loss {ρ d : ℝ} (hρ : ρ ≤ epsilon) (hpos : 0 ≤ ρ)
    (hd : d ∈ Icc 0 1) {p : List Letter}
    (hp : p = [.plus, .plus] ∨ p = [.minus, .minus] ∨ p = [.plus, .minus, .plus]) :
    ρ ≤ loss ρ d p := by
  have hb := sum_shift_le_loss hpos hd p
  have h₀ := sqrt_two_bounds.1
  have h₁ := sqrt_two_bounds.2
  unfold epsilon at hρ
  rcases hp with rfl | rfl | rfl
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, shift, add_zero] at hb
    have h := le_abs_self ((Real.sqrt 2 - 1 / 2) + (Real.sqrt 2 - 1 / 2))
    linarith
  · norm_num [shift] at hb
    linarith
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, shift, add_zero] at hb
    have h := le_abs_self
      ((Real.sqrt 2 - 1 / 2) + (-(2 / 3) + (Real.sqrt 2 - 1 / 2)))
    linarith

private theorem loss_of_pattern {ρ d : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon)
    (hd : d ∈ Icc 0 1) (a p b : List Letter)
    (hp : p = [.plus, .plus] ∨ p = [.minus, .minus] ∨ p = [.plus, .minus, .plus]) :
    ρ ≤ loss ρ d (a ++ (p ++ b)) := by
  rw [loss_append, loss_append]
  have hpre := loss_nonneg hpos d a
  have hpost := loss_nonneg hpos (p.foldl nextState (a.foldl nextState d)) b
  have hpattern := forcingPattern_loss hρ hpos (fold_state_mem hd a) hp
  linarith

private theorem four_loss {ρ d : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon)
    (hd : d ∈ Icc 0 1) (a b e f : Letter) : ρ ≤ loss ρ d [a, b, e, f] := by
  by_cases hs : .star ∈ [a, b, e, f]
  · exact loss_of_star hpos d hs
  have shape :
      a = b ∨ b = e ∨ e = f ∨ a = .plus ∧ b = .minus ∧ e = .plus ∨
        b = .plus ∧ e = .minus ∧ f = .plus := by
    cases a <;> cases b <;> cases e <;> cases f <;> simp_all
  rcases shape with rfl | rfl | rfl | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · cases a
    · exact loss_of_pattern hpos hρ hd [] [.plus, .plus] [e, f] (Or.inl rfl)
    · exact loss_of_pattern hpos hρ hd [] [.minus, .minus] [e, f] (Or.inr (Or.inl rfl))
    · simp at hs
  · cases b
    · exact loss_of_pattern hpos hρ hd [a] [.plus, .plus] [f] (Or.inl rfl)
    · exact loss_of_pattern hpos hρ hd [a] [.minus, .minus] [f] (Or.inr (Or.inl rfl))
    · simp at hs
  · cases e
    · exact loss_of_pattern hpos hρ hd [a, b] [.plus, .plus] [] (Or.inl rfl)
    · exact loss_of_pattern hpos hρ hd [a, b] [.minus, .minus] [] (Or.inr (Or.inl rfl))
    · simp at hs
  · exact loss_of_pattern hpos hρ hd [] [.plus, .minus, .plus] [f] (Or.inr (Or.inr rfl))
  · exact loss_of_pattern hpos hρ hd [a] [.plus, .minus, .plus] [] (Or.inr (Or.inr rfl))

private theorem word_loss {ρ : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon)
    (a : List Letter) {d : ℝ} (hd : d ∈ Icc 0 1) :
    ρ * (↑(a.length / 4) : ℝ) ≤ loss ρ d a := by
  suffices h : ∀ n (u : List Letter), u.length = n → ∀ x ∈ Icc (0 : ℝ) 1,
      ρ * (↑(u.length / 4) : ℝ) ≤ loss ρ x u by
    exact h a.length a rfl d hd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hlen d hd
    match u with
    | [] => simpa using loss_nonneg hpos d []
    | [e] => simpa using loss_nonneg hpos d [e]
    | [e, f] => simpa using loss_nonneg hpos d [e, f]
    | [e, f, g] => simpa using loss_nonneg hpos d [e, f, g]
    | e :: f :: g :: h :: a =>
      let block := [e, f, g, h]
      have hhead := four_loss hpos hρ hd e f g h
      have hlt : a.length < n := by simp at hlen; omega
      have htail := ih a.length hlt a rfl _ (fold_state_mem hd block)
      change ρ * (↑((block ++ a).length / 4) : ℝ) ≤ loss ρ d (block ++ a)
      rw [loss_append]
      have hdiv : (block ++ a).length / 4 = a.length / 4 + 1 := by
        simp [block]
        omega
      rw [hdiv, Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm]
      exact add_le_add hhead htail

private theorem loss_cons_of_mem (ρ d : ℝ) (e : Letter) (a : List Letter)
    (h : d + shift e ∈ Icc (0 : ℝ) 1) :
    loss ρ d (e :: a) = toll ρ e + loss ρ (d + shift e) a := by
  simp [loss, nextState, clip, max_eq_right h.1, min_eq_right h.2,
    (MeyerovitchYoungQ61Subcritical.overshoot_eq_zero_iff 1 _).2 h]

private theorem four_loss_attained (ρ : ℝ) :
    loss ρ (1 / 2) [.star, .minus, .plus, .minus] = ρ := by
  let d₁ : ℝ := 1 / 2 + shift .star
  let d₂ := d₁ + shift .minus
  let d₃ := d₂ + shift .plus
  let d₄ := d₃ + shift .minus
  have hlo := sqrt_two_bounds.1
  have hhi : Real.sqrt 2 < 13 / 9 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg 2
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hn]
  have h₁ : d₁ ∈ Icc 0 1 := ⟨by dsimp [d₁, shift]; linarith, by dsimp [d₁, shift]; linarith⟩
  have h₂ : d₂ ∈ Icc 0 1 := ⟨by dsimp [d₂, d₁, shift]; linarith,
    by dsimp [d₂, d₁, shift]; linarith⟩
  have h₃ : d₃ ∈ Icc 0 1 := ⟨by dsimp [d₃, d₂, d₁, shift]; linarith,
    by dsimp [d₃, d₂, d₁, shift]; linarith⟩
  have h₄ : d₄ ∈ Icc 0 1 := ⟨by dsimp [d₄, d₃, d₂, d₁, shift]; linarith,
    by dsimp [d₄, d₃, d₂, d₁, shift]; linarith⟩
  rw [loss_cons_of_mem ρ _ _ _ h₁, loss_cons_of_mem ρ d₁ _ _ h₂,
    loss_cons_of_mem ρ d₂ _ _ h₃, loss_cons_of_mem ρ d₃ _ _ h₄]
  simp [loss, toll]

/-- Every complete block of four letters costs at least one star toll relative
to the unclipped non-star reward, even when the block starts at a nonzero difference. -/
theorem matrixMinimum_le_four_block (c : ℝ) {ρ : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon)
    (a : List Letter) :
    centeredScore c ρ a ≤ (a.length : ℝ) * (c + ρ / 8) - ρ * (↑(a.length / 4) : ℝ) ∧
    matrixMinimum (matrices c ρ) a + normalizedState c ρ a / 2 ≤
      (a.length : ℝ) * (c + ρ / 8) - ρ * (↑(a.length / 4) : ℝ) ∧
    (∀ d ∈ Icc (0 : ℝ) 1, ∀ u : List Letter, u.length = 4 →
      (u.foldl (centeredStep c ρ) (d, 0)).2 ≤ 4 * (c + ρ / 8) - ρ) ∧
    (([.star, .minus, .plus, .minus] : List Letter).foldl
      (centeredStep c ρ) (1 / 2, 0)).2 = 4 * (c + ρ / 8) - ρ := by
  have h : centeredScore c ρ a ≤
      (a.length : ℝ) * (c + ρ / 8) - ρ * (↑(a.length / 4) : ℝ) := by
    unfold centeredScore
    rw [centeredFold_formula]
    simp only [zero_add]
    exact sub_le_sub_left (word_loss hpos hρ a (by norm_num : (0 : ℝ) ∈ Icc 0 1)) _
  refine ⟨h, ?_, ?_, ?_⟩
  · rwa [(matrixMinimum_eq_centered c ρ a).2.2, sub_add_cancel]
  · intro d hd u hu
    have hl := word_loss hpos hρ u hd
    rw [hu] at hl
    norm_num at hl
    rw [centeredFold_formula, hu]
    simpa only [zero_add, Nat.cast_ofNat] using sub_le_sub_left hl (4 * (c + ρ / 8))
  · rw [centeredFold_formula, four_loss_attained]
    norm_num

/-- Scores attainable against an optimal Bob response at horizon `n`. -/
noncomputable def horizonValues (c ρ : ℝ) (n : ℕ) : Set ℝ :=
  matrixMinimum (matrices c ρ) '' {a : List Letter | a.length = n}

/-- The original finite-horizon maximin with both endpoints free. -/
noncomputable def maximin (c ρ : ℝ) (n : ℕ) : ℝ := sSup (horizonValues c ρ n)

private theorem maximin_spec (c ρ : ℝ) (n : ℕ) :
    IsGreatest (horizonValues c ρ n) (maximin c ρ n) := by
  let words : Set (List Letter) := {a | a.length = n}
  have hf : words.Finite := List.finite_length_eq Letter n
  have hn : words.Nonempty := ⟨List.replicate n .plus, by simp [words]⟩
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image words (matrixMinimum (matrices c ρ)) hf hn
  have hv : IsGreatest (horizonValues c ρ n) (matrixMinimum (matrices c ρ) a) := by
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro v ⟨b, hb, rfl⟩
    exact hmax b hb
  rw [maximin, hv.csSup_eq]
  exact hv

private theorem maximin_le_blocks (c : ℝ) {ρ : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon) (n : ℕ) :
    maximin c ρ n ≤ (n : ℝ) * (c + ρ / 8) - ρ * (↑(n / 4) : ℝ) := by
  obtain ⟨a, ha, hscore⟩ := (maximin_spec c ρ n).1
  change a.length = n at ha
  rw [← hscore, ← ha]
  have hd : 0 ≤ normalizedState c ρ a := (matrixMinimum_eq_centered c ρ a).2.1.1
  have h := (matrixMinimum_le_four_block c hpos hρ a).2.1
  linarith

private theorem endpointFold_lower (c ρ k : ℝ) (a : List Letter) {x y : Bool → ℝ}
    (h : ∀ i, k + x i ≤ y i) (j : Bool) :
    k + (a.foldl (endpointStep c ρ) x) j ≤ (a.foldl (endpointStep c ρ) y) j := by
  induction a generalizing x y with
  | nil => exact h j
  | cons e a ih =>
    simp only [List.foldl_cons]
    apply ih
    intro i
    unfold endpointStep
    rw [add_min]
    apply min_le_min <;> linarith [h false, h true]

private theorem matrixMinimum_superadditive (c ρ : ℝ) (a b : List Letter) :
    matrixMinimum (matrices c ρ) a + matrixMinimum (matrices c ρ) b ≤
      matrixMinimum (matrices c ρ) (a ++ b) := by
  let k := matrixMinimum (matrices c ρ) a
  have hx (i : Bool) : k + (fun _ : Bool => (0 : ℝ)) i ≤ endpointScores c ρ a i := by
    change k + 0 ≤ _
    rw [add_zero]
    dsimp [k]
    rw [matrixMinimum_eq_min]
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have h (j : Bool) : k + endpointScores c ρ b j ≤ endpointScores c ρ (a ++ b) j := by
    simpa only [endpointScores, List.foldl_append] using endpointFold_lower c ρ k b hx j
  rw [matrixMinimum_eq_min c ρ b, matrixMinimum_eq_min c ρ (a ++ b), add_min]
  exact min_le_min (h false) (h true)

private theorem maximin_superadditive (c ρ : ℝ) (m n : ℕ) :
    maximin c ρ m + maximin c ρ n ≤ maximin c ρ (m + n) := by
  obtain ⟨a, ha, hA⟩ := (maximin_spec c ρ m).1
  obtain ⟨b, hb, hB⟩ := (maximin_spec c ρ n).1
  change a.length = m at ha
  change b.length = n at hb
  rw [← hA, ← hB]
  exact (matrixMinimum_superadditive c ρ a b).trans
    ((maximin_spec c ρ (m + n)).2 ⟨a ++ b, by simp [ha, hb], rfl⟩)

private theorem maximin_limit (c : ℝ) {ρ : ℝ} (hpos : 0 ≤ ρ) (hρ : ρ ≤ epsilon) :
    ∃ V : ℝ, Tendsto (fun n : ℕ => maximin c ρ n / (n : ℝ)) atTop (𝓝 V) ∧
      V ≤ c - ρ / 8 := by
  have hsub : Subadditive (fun n => -maximin c ρ n) := by
    intro m n
    linarith [maximin_superadditive c ρ m n]
  have hbdd : BddBelow (range fun n : ℕ => -maximin c ρ n / (n : ℝ)) := by
    refine ⟨min 0 (-(c + ρ / 8)), ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => simp
    | succ n =>
      have hn : (0 : ℝ) < (↑(n + 1) : ℝ) := by positivity
      apply (min_le_right _ _).trans
      apply (le_div_iff₀ hn).2
      have h₁ := maximin_le_blocks c hpos hρ (n + 1)
      have h₂ : 0 ≤ ρ * (↑((n + 1) / 4) : ℝ) := by positivity
      linarith
  let V := -hsub.lim
  have hlim : Tendsto (fun n : ℕ => maximin c ρ n / (n : ℝ)) atTop (𝓝 V) := by
    simpa only [V, neg_div, neg_neg] using (hsub.tendsto_lim hbdd).neg
  refine ⟨V, hlim, ?_⟩
  have hup : Tendsto (fun n : ℕ => c - ρ / 8 + (3 * ρ / 4) / (n : ℝ))
      atTop (𝓝 (c - ρ / 8)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (3 * ρ / 4))
  apply le_of_tendsto_of_tendsto hlim hup
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmod : (↑(n % 4) : ℝ) + 4 * (↑(n / 4) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n 4
  have hr : (↑(n % 4) : ℝ) ≤ 3 := by exact_mod_cast (show n % 4 ≤ 3 by omega)
  have hbound := maximin_le_blocks c hpos hρ n
  have hrem := mul_le_mul_of_nonneg_left hr hpos
  apply (div_le_iff₀ hn').2
  rw [add_mul, div_mul_cancel₀ _ hn'.ne']
  nlinarith [congrArg (ρ * ·) hmod]

/-- Linear rewards of nonnegative translation frequencies of sum one and zero mean shift. -/
def frequencyValues (c ρ : ℝ) : Set ℝ :=
  {v | ∃ x : Letter → ℝ, (∀ e, 0 ≤ x e) ∧
    x .plus + x .minus + x .star = 1 ∧
    x .plus * shift .plus + x .minus * shift .minus + x .star * shift .star = 0 ∧
    x .plus * reward c ρ .plus + x .minus * reward c ρ .minus +
      x .star * reward c ρ .star = v}

private theorem frequency_optimum (c : ℝ) {ρ : ℝ} (hpos : 0 ≤ ρ) :
    IsGreatest (frequencyValues c ρ) (c + ρ / 8) := by
  let α := shift .plus
  let β := -shift .minus
  have ha : 0 < α := by
    dsimp [α, shift]
    linarith [sqrt_two_bounds.1]
  have hb : 0 < β := by norm_num [β, shift]
  have hab : 0 < α + β := add_pos ha hb
  refine ⟨?_, ?_⟩
  · let x : Letter → ℝ
      | .plus => β / (α + β)
      | .minus => α / (α + β)
      | .star => 0
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · intro e
      cases e
      · exact (div_pos hb hab).le
      · exact (div_pos ha hab).le
      · exact le_rfl
    · change β / (α + β) + α / (α + β) + 0 = 1
      field_simp [hab.ne']
      ring
    · change β / (α + β) * α + α / (α + β) * shift .minus + 0 * shift .star = 0
      have hm : shift .minus = -β := (neg_neg _).symm
      rw [hm]
      ring
    · norm_num [x, reward]
      field_simp [hab.ne']
      ring
  · rintro v ⟨x, hx, hsum, _, rfl⟩
    have ht := mul_nonneg (hx .star) hpos
    have hm := congrArg (fun w : ℝ => w * (c + ρ / 8)) hsum
    norm_num [reward] at *
    linarith

private theorem normalizedState_snoc (c ρ : ℝ) (a : List Letter) (e : Letter) :
    normalizedState c ρ (a ++ [e]) = nextState (normalizedState c ρ a) e := by
  have h := congrArg Prod.fst (centeredFold_eq c ρ (a ++ [e]))
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← centeredFold_eq c ρ a] at h
  exact h

private noncomputable def rotationWord (c ρ : ℝ) : ℕ → List Letter
  | 0 => []
  | n + 1 =>
    let a := rotationWord c ρ n
    a ++ [if normalizedState c ρ a < 2 / 3 then .star else .minus]

private theorem rotationWord_state (c ρ : ℝ) (n : ℕ) :
    let d := normalizedState c ρ (rotationWord c ρ n)
    let L := (2 : ℝ) / 3 + shift .star
    d ∈ Ico 0 L ∧ ∃ k : ℤ, d = (k : ℝ) * L - (n : ℝ) * (2 / 3) := by
  let L := (2 : ℝ) / 3 + shift .star
  have hγ : 0 < shift .star := by
    change 0 < (Real.sqrt 2 - 1) / 2
    linarith [sqrt_two_bounds.1]
  have hL : L < 1 := by
    change 2 / 3 + (Real.sqrt 2 - 1) / 2 < (1 : ℝ)
    linarith [sqrt_two_bounds.2]
  induction n with
  | zero =>
    have hzero : normalizedState c ρ (rotationWord c ρ 0) = 0 := by
      simp [rotationWord, normalizedState, difference, endpointScores]
    change normalizedState c ρ (rotationWord c ρ 0) ∈ Ico 0 L ∧
      ∃ k : ℤ, normalizedState c ρ (rotationWord c ρ 0) =
        (k : ℝ) * L - ((0 : ℕ) : ℝ) * (2 / 3)
    rw [hzero]
    exact ⟨⟨le_rfl, by dsimp [L]; linarith⟩, 0, by simp⟩
  | succ n ih =>
    let d := normalizedState c ρ (rotationWord c ρ n)
    obtain ⟨⟨hd₀, hdL⟩, k, hk⟩ := ih
    change d < L at hdL
    change d = (k : ℝ) * L - (n : ℝ) * (2 / 3) at hk
    change normalizedState c ρ (rotationWord c ρ (n + 1)) ∈ Ico 0 L ∧ _
    rw [rotationWord, normalizedState_snoc]
    change nextState d (if d < 2 / 3 then .star else .minus) ∈ Ico 0 L ∧
      ∃ k : ℤ, nextState d (if d < 2 / 3 then .star else .minus) =
        (k : ℝ) * L - ((n + 1 : ℕ) : ℝ) * (2 / 3)
    split_ifs with h
    · have hlo : 0 ≤ d + shift .star := add_nonneg hd₀ hγ.le
      have hhi : d + shift .star < L := add_lt_add_left h _
      simp only [nextState, clip, max_eq_right hlo, min_eq_right (hhi.trans hL).le]
      refine ⟨⟨hlo, hhi⟩, k + 1, ?_⟩
      push_cast
      dsimp [L] at hk ⊢
      linarith
    · have hlo : 0 ≤ d + shift .minus := by
        simpa [shift, sub_eq_add_neg] using sub_nonneg.mpr (le_of_not_gt h)
      have hhi : d + shift .minus < L := by
        dsimp [shift]
        linarith
      simp only [nextState, clip, max_eq_right hlo, min_eq_right (hhi.trans hL).le]
      refine ⟨⟨hlo, hhi⟩, k, ?_⟩
      push_cast
      rw [hk]
      simp only [shift]
      ring

private theorem infinite_normalizedState (c ρ : ℝ) :
    (range (normalizedState c ρ)).Infinite := by
  let L := (2 : ℝ) / 3 + shift .star
  have hγ : Irrational (shift .star) := by
    simpa [shift] using (irrational_sqrt_two.sub_intCast 1).div_natCast (m := 2) (by decide)
  have hL : Irrational L := by
    simpa [L] using hγ.ratCast_add (2 / 3 : ℚ)
  apply (infinite_range_of_injective
    (f := fun n => normalizedState c ρ (rotationWord c ρ n)) ?_).mono
  · rintro _ ⟨n, rfl⟩
    exact ⟨rotationWord c ρ n, rfl⟩
  · intro m n h
    obtain ⟨_, k, hk⟩ := rotationWord_state c ρ m
    obtain ⟨_, l, hl⟩ := rotationWord_state c ρ n
    change normalizedState c ρ (rotationWord c ρ m) = (k : ℝ) * L - (m : ℝ) * (2 / 3) at hk
    change normalizedState c ρ (rotationWord c ρ n) = (l : ℝ) * L - (n : ℝ) * (2 / 3) at hl
    have hkl : k = l := by
      by_contra hne
      apply (hL.intCast_mul (sub_ne_zero.mpr hne)).ne_rat (((m : ℚ) - (n : ℚ)) * (2 / 3))
      push_cast
      linarith
    subst l
    exact_mod_cast (show (m : ℝ) = (n : ℝ) by linarith)

private theorem graphs_connect :
    ConnectsAt aliceGraph 1 ∧ ConnectsAt (completeGraph Bool) 1 := by
  constructor
  · intro i j
    cases i
    cases j
    exact ⟨.concat .nil .plus rfl, rfl⟩
  · exact complete_connects Bool

private theorem alice_legal (a : List Letter) : Legal aliceGraph a := by
  induction a using List.reverseRecOn with
  | nil => exact ⟨(), (), .nil, rfl⟩
  | append_singleton a e ih =>
    obtain ⟨s, t, p, hp⟩ := ih
    cases t
    exact ⟨s, (), p.concat e rfl, by simpa using congrArg (· ++ [e]) hp⟩

/-- The coefficient domain of the original game, embedded in the reals. -/
def quadraticField : Set ℝ :=
  {x | ∃ a b : ℚ, x = (a : ℝ) + (b : ℝ) * Real.sqrt 2}

private theorem matrices_in_field {c ρ : ℝ} (hc : c ∈ quadraticField)
    (hρ : ρ ∈ quadraticField) (e : Letter) (i j : Bool) :
    matrices c ρ e i j ∈ quadraticField := by
  obtain ⟨a, b, rfl⟩ := hc
  obtain ⟨u, v, rfl⟩ := hρ
  obtain ⟨p, q, hshift⟩ : shift e ∈ quadraticField := by
    cases e
    · exact ⟨-1 / 2, 1, by push_cast; simp [shift]; ring⟩
    · exact ⟨-2 / 3, 0, by push_cast; simp [shift, neg_div]⟩
    · exact ⟨-1 / 2, 1 / 2, by push_cast; simp [shift]; ring⟩
  let k : ℚ := if e = .star then -7 / 8 else 1 / 8
  have hk : reward ((a : ℝ) + (b : ℝ) * Real.sqrt 2)
      ((u : ℝ) + (v : ℝ) * Real.sqrt 2) e =
      (↑(a + k * u) : ℝ) + (↑(b + k * v) : ℝ) * Real.sqrt 2 := by
    by_cases he : e = .star <;> simp [reward, k, he] <;> ring
  change shift e = _ at hshift
  cases i
  · exact ⟨a + k * u + p / 2, b + k * v + q / 2, by
      cases j <;> simp only [matrices, hk, hshift] <;> push_cast <;> ring⟩
  · cases j
    · exact ⟨a + k * u + 1 - p / 2, b + k * v - q / 2, by
        simp only [matrices, hk, hshift]; push_cast; ring⟩
    · exact ⟨a + k * u - p / 2, b + k * v - q / 2, by
        simp only [matrices, hk, hshift]; push_cast; ring⟩

/-- The translation-frequency LP and the original normalized maximin lie on
opposite sides of the threshold for the same complete three-matrix input. -/
theorem frequency_threshold_gap (c : ℝ) {ρ : ℝ} (hpos : 0 < ρ) (hρ : ρ ≤ epsilon) :
    ConnectsAt aliceGraph 1 ∧ ConnectsAt (completeGraph Bool) 1 ∧
    (∀ a, Legal aliceGraph a) ∧
    (c ∈ quadraticField → ρ ∈ quadraticField → ∀ e i j, matrices c ρ e i j ∈ quadraticField) ∧
    IsGreatest (frequencyValues c ρ) (c + ρ / 8) ∧ c < c + ρ / 8 ∧
    (∀ n, IsGreatest (horizonValues c ρ n) (maximin c ρ n) ∧
      maximin c ρ n ≤ (n : ℝ) * (c + ρ / 8) - ρ * (↑(n / 4) : ℝ)) ∧
    (range (normalizedState c ρ)).Infinite ∧
    ∃ V : ℝ, Tendsto (fun n : ℕ => maximin c ρ n / (n : ℝ)) atTop (𝓝 V) ∧
      V ≤ c - ρ / 8 ∧ V < c := by
  obtain ⟨V, hV, hbound⟩ := maximin_limit c hpos.le hρ
  exact ⟨graphs_connect.1, graphs_connect.2, alice_legal, matrices_in_field,
    frequency_optimum c hpos.le, by linarith, fun n =>
      ⟨maximin_spec c ρ n, maximin_le_blocks c hpos.le hρ n⟩,
    infinite_normalizedState c ρ, V, hV, hbound, by linarith⟩

end MeyerovitchYoungQ61FrequencyGap
