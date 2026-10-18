/- GID: D5/S3/Geometry/Hyperideal/RegularDegreeAngleStructure
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/RegularDegreeAngleStructure
   mirror-E: none(waiver:uniform-degree-angle-structure)
   anchors: []
   utility: none
   digest: Degree-normalized angles give exact edge sums and a strict local vertex bound. -/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Tactic

/-! Degree-normalized angles form the strict local angle structure used by the
    general minimum-degree-eight argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.RegularDegreeAngleStructure

open D5.S3.Geometry.Hyperideal.ActualCornerTransport

variable {T : Type*} [Fintype T]

/-- The number of local edge occurrences in a global edge class. -/
def degree (q : Pairing T) (e : GlobalEdge q) : ℕ := by
  classical
  exact (Finset.univ.filter (fun o : Occurrence T => P q o = e)).card

/-- The regular angle assigned to an occurrence by the degree of its global edge. -/
def regularAngle (q : Pairing T) (o : Occurrence T) : ℝ :=
  2 * Real.pi / (degree q (P q o) : ℝ)

private theorem degree_pos (q : Pairing T) (hdegree : ∀ e, 8 ≤ degree q e)
    (e : GlobalEdge q) : 0 < degree q e := by
  have h := hdegree e
  omega

private theorem regularAngle_pos (q : Pairing T)
    (hdegree : ∀ e, 8 ≤ degree q e) (o : Occurrence T) :
    0 < regularAngle q o := by
  unfold regularAngle
  have hd : 0 < (degree q (P q o) : ℝ) := by
    exact_mod_cast degree_pos q hdegree (P q o)
  positivity

private theorem regularAngle_le_quarter (q : Pairing T)
    (hdegree : ∀ e, 8 ≤ degree q e) (o : Occurrence T) :
    regularAngle q o ≤ Real.pi / 4 := by
  unfold regularAngle
  have hd : 0 < (degree q (P q o) : ℝ) := by
    exact_mod_cast degree_pos q hdegree (P q o)
  have hdeg : (8 : ℝ) ≤ degree q (P q o) := by
    exact_mod_cast hdegree (P q o)
  apply (div_le_iff₀ hd).2
  nlinarith [Real.pi_pos]

private theorem regular_edge_sum (q : Pairing T)
    (hdegree : ∀ e, 8 ≤ degree q e) (e : GlobalEdge q) :
    M q (regularAngle q) e = 2 * Real.pi := by
  classical
  unfold M
  let S : Finset (Occurrence T) := Finset.univ.filter (fun o => P q o = e)
  have hsum : (∑ o : Occurrence T,
      if P q o = e then regularAngle q o else 0) =
      (∑ o ∈ S, regularAngle q o) := by
    simpa [S] using (Finset.sum_filter (s := (Finset.univ : Finset (Occurrence T)))
      (p := fun o : Occurrence T => P q o = e)
      (f := fun o : Occurrence T => regularAngle q o)).symm
  rw [hsum]
  have hconst : ∀ o ∈ S,
      regularAngle q o = 2 * Real.pi / (degree q e : ℝ) := by
    intro o ho
    have he : P q o = e := (Finset.mem_filter.mp ho).2
    simp [regularAngle, he]
  calc
    (∑ o ∈ S, regularAngle q o) =
        ∑ o ∈ S, 2 * Real.pi / (degree q e : ℝ) := by
      apply Finset.sum_congr rfl
      intro o ho
      exact hconst o ho
    _ = (S.card : ℝ) * (2 * Real.pi / (degree q e : ℝ)) := by simp
    _ = 2 * Real.pi := by
      have hdne : (degree q e : ℝ) ≠ 0 := by
        have hnat : degree q e ≠ 0 := Nat.ne_of_gt (degree_pos q hdegree e)
        exact_mod_cast hnat
      calc
        (degree q e : ℝ) * (2 * Real.pi / (degree q e : ℝ)) =
            2 * Real.pi * ((degree q e : ℝ) / (degree q e : ℝ)) := by ring
        _ = 2 * Real.pi := by rw [div_self hdne]; ring

private theorem regular_corner_sum_le (q : Pairing T)
    (hdegree : ∀ e, 8 ≤ degree q e) (c : Corner T) :
    Q (regularAngle q) c ≤ 3 * Real.pi / 4 := by
  rcases c with ⟨t, v⟩
  fin_cases v <;>
    simp only [Q, endpoints, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk,
      Fin.sum_univ_succ, Finset.sum_insert, Finset.sum_singleton,
      Finset.mem_insert, Finset.mem_singleton, not_false_eq_true,
      Prod.mk.injEq, and_self, or_true, true_or, false_or, or_false,
      Fin.reduceEq, Fin.ext_iff] <;>
    try norm_num
  all_goals
    have h0 := regularAngle_le_quarter q hdegree (t, (0 : Fin 6))
    have h1 := regularAngle_le_quarter q hdegree (t, (1 : Fin 6))
    have h2 := regularAngle_le_quarter q hdegree (t, (2 : Fin 6))
    have h3 := regularAngle_le_quarter q hdegree (t, (3 : Fin 6))
    have h4 := regularAngle_le_quarter q hdegree (t, (4 : Fin 6))
    have h5 := regularAngle_le_quarter q hdegree (t, (5 : Fin 6))
    nlinarith

/-- The degree-normalized assignment is positive, has exact global edge sums,
    and has local vertex sums at most three quarters of pi. -/
theorem regular_degree_angle_structure (q : Pairing T)
    (hdegree : ∀ e, 8 ≤ degree q e) :
    (∀ o, 0 < regularAngle q o) ∧
      (∀ e, M q (regularAngle q) e = 2 * Real.pi) ∧
      (∀ c, Q (regularAngle q) c ≤ 3 * Real.pi / 4) ∧
      (∀ c, Q (regularAngle q) c < Real.pi) := by
  refine ⟨regularAngle_pos q hdegree, regular_edge_sum q hdegree,
    regular_corner_sum_le q hdegree, ?_⟩
  intro c
  have h := regular_corner_sum_le q hdegree c
  nlinarith [Real.pi_pos]

#print axioms regular_degree_angle_structure

end D5.S3.Geometry.Hyperideal.RegularDegreeAngleStructure
