/- GID: D5/S3/Geometry/Hyperideal/StrictAngleTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/StrictAngleTransport
   mirror-E: none(waiver:strict-angle-transport-interface)
   anchors: []
   utility: none
   digest: A bounded actual transport correction preserves edge sums and makes all vertex sums strict. -/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Tactic

/-! A bounded actual transport correction gives a strict angle interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.StrictAngleTransport

open D5.S3.Geometry.Hyperideal.ActualCornerTransport

variable {T S : Type*} [Fintype T] [Fintype S]

local instance cornerDecidableEq : DecidableEq (Corner T) := Classical.decEq _

/-- Add the occurrence lift supplied by an actual paired-corner transport to a base angle vector. -/
def corrected (q : Pairing T) (a₀ : Occurrence T → ℝ)
    (paths : S → List (Slot T)) (w : S → ℝ) : Occurrence T → ℝ :=
  fun o => a₀ o + lift q paths w o

private theorem mass_add (q : Pairing T) (a b : Occurrence T → ℝ) (e : GlobalEdge q) :
    M q (fun o => a o + b o) e = M q a e + M q b e := by
  classical
  simp only [M]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases h : P q o = e <;> simp [h, add_mul]

private theorem corner_add (a b : Occurrence T → ℝ) (c : Corner T) :
    Q (fun o => a o + b o) c = Q a c + Q b c := by
  classical
  simp only [Q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : c.2 = (endpoints j).1 ∨ c.2 = (endpoints j).2 <;> simp [h, add_mul]

/--
A nonnegative, bounded transport correction is a genuine strictification step.
The edge equations are unchanged, every occurrence stays positive when the
transport bound is at most half the base lower bound, and a strictly positive
outgoing deficit at every corner makes every corrected corner sum strict.
The divergence and bound are supplied by `actual_corner_transport`; no
replacement quotient or independent local pairing is introduced.
-/
theorem strict_angle_correction
    (q : Pairing T) (a₀ : Occurrence T → ℝ)
    (u v : S → Corner T) (w : S → ℝ) (B m : ℝ)
    (same : ∀ s, label q (u s) = label q (v s))
    (nonneg : ∀ s, 0 ≤ w s)
    (bounded : ∀ z : Vertex q, mass q u w z ≤ B)
    (base_lower : ∀ o, m ≤ a₀ o)
    (base_corner : ∀ c, Q a₀ c ≤ 1)
    (positive_divergence : ∀ c,
      0 < ∑ s, w s *
        ((if u s = c then (1 : ℝ) else 0) - (if v s = c then 1 else 0)))
    (hm : 0 < m) (hsmall : 3 * B ≤ m / 2) :
    ∃ a : Occurrence T → ℝ,
      (∀ o, 0 < a o) ∧
      (∀ e : GlobalEdge q, M q a e = M q a₀ e) ∧
      (∀ c, Q a c < 1) ∧
      (∀ o, |a o - a₀ o| ≤ 3 * B) := by
  classical
  obtain ⟨paths, _follows, _simple, _nilpath, _counts, _anti, _chi_bound,
      _support, _divergence, _load_anti, _load_bound, zeroM, deficit, local_bound⟩ :=
    actual_corner_transport q u v w same nonneg B bounded
  let a : Occurrence T → ℝ := corrected q a₀ paths w
  have correction_bound (o : Occurrence T) :
      |lift q paths w o| ≤ m / 2 := by
    exact (local_bound o).trans hsmall
  have correction_lower (o : Occurrence T) :
      -(m / 2) ≤ lift q paths w o := by
    exact (neg_le_of_abs_le (correction_bound o))
  have correction_upper (o : Occurrence T) :
      lift q paths w o ≤ m / 2 := by
    exact (le_abs_self _).trans (correction_bound o)
  have positive (o : Occurrence T) : 0 < a o := by
    dsimp [a, corrected]
    have hbase := base_lower o
    have hhalf : 0 < m / 2 := by linarith [hm]
    linarith [hbase, correction_lower o, hhalf]
  have edge_preserved (e : GlobalEdge q) : M q a e = M q a₀ e := by
    rw [show a = (fun o => a₀ o + lift q paths w o) by rfl,
      mass_add, zeroM]
    simp
  have corner_strict (c : Corner T) : Q a c < 1 := by
    have hq := base_corner c
    have hd := deficit c
    have hp := positive_divergence c
    have hneg' : 0 < -Q (lift q paths w) c := by
      rw [hd]
      convert hp using 1
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hu : u s = c <;> by_cases hv : v s = c <;> simp [hu, hv]
    have hneg : Q (lift q paths w) c < 0 := by
      linarith [hneg']
    change Q (fun o => a₀ o + lift q paths w o) c < 1
    calc
      Q (fun o => a₀ o + lift q paths w o) c =
          Q a₀ c + Q (lift q paths w) c := corner_add a₀ (lift q paths w) c
      _ < 1 := by linarith
  have occurrence_bound (o : Occurrence T) : |a o - a₀ o| ≤ 3 * B := by
    dsimp [a, corrected]
    simpa only [add_sub_cancel_left] using local_bound o
  exact ⟨a, positive, edge_preserved, corner_strict, occurrence_bound⟩

#print axioms strict_angle_correction

end D5.S3.Geometry.Hyperideal.StrictAngleTransport
