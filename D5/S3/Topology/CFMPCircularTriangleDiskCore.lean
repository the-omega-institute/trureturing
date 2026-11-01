/- GID: D5/S3/Topology/CFMPCircularTriangleDiskCore
   generality: G
   mirror-B: D5/B/S3/Topology/CFMPCircularTriangleDiskCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation, mathlib/module/Mathlib.Data.Fin.Basic]
   utility: none
   digest: Cyclic fan seams preserve radial size and join all labelled origins. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Core radial and origin facts for the cyclic triangle-fan seam quotient. -/

set_option autoImplicit false

namespace D5.S3.Topology.CFMPCircularTriangleDiskCore

universe u

structure Triangle where
  a : ℝ
  b : ℝ
  nonneg_a : 0 ≤ a
  nonneg_b : 0 ≤ b
  sum_le_one : a + b ≤ 1

namespace Triangle

private def origin : Triangle :=
  ⟨0, 0, le_rfl, le_rfl, by norm_num⟩

private def radial (x : Triangle) : ℝ := x.a + x.b

private theorem radial_nonneg (x : Triangle) : 0 ≤ x.radial := by
  dsimp [radial]
  linarith [x.nonneg_a, x.nonneg_b]

private theorem radial_le_one (x : Triangle) : x.radial ≤ 1 := x.sum_le_one

private theorem radial_eq_zero_iff (x : Triangle) : x.radial = 0 ↔ x = origin := by
  constructor
  · intro h
    dsimp [radial] at h
    have ha : x.a = 0 := by
      nlinarith [x.nonneg_a, x.nonneg_b]
    have hb : x.b = 0 := by
      nlinarith [x.nonneg_a, x.nonneg_b]
    cases x
    simp_all [origin]
  · intro h
    simpa [h, origin, radial]

end Triangle

variable {n : ℕ} (hn : 0 < n)

private abbrev Fan (n : ℕ) := Fin n × Triangle

private def next (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private def edge (i : Fin n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Fan n :=
  (i, ⟨t, 0, ht0, le_rfl, by linarith⟩)

private def seamStep (x y : Fan n) : Prop :=
  ∃ (i : Fin n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    x = edge i t ht0 ht1 ∧ y = edge (next hn i) t (by exact ht0) ht1

private abbrev SeamRel : Fan n → Fan n → Prop := Relation.EqvGen (seamStep hn)

private def radialSize (x : Fan n) : ℝ := x.2.radial

private theorem seamStep_radial {x y : Fan n} (hxy : seamStep hn x y) :
    radialSize x = radialSize y := by
  rcases hxy with ⟨i, t, ht0, ht1, rfl, rfl⟩
  rfl

theorem radialSize_eq_of_seamRel {x y : Fan n} (hxy : SeamRel hn x y) :
    radialSize x = radialSize y := by
  induction hxy with
  | rel x y h => exact seamStep_radial (hn := hn) h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem seam_origin_step (i : Fin n) :
    SeamRel hn (edge i 0 (by norm_num) (by norm_num))
      (edge (next hn i) 0 (by norm_num) (by norm_num)) := by
  apply Relation.EqvGen.rel
  exact ⟨i, 0, by norm_num, by norm_num, rfl, rfl⟩

theorem seam_origin_all (i : Fin n) :
    SeamRel hn (edge ⟨0, Nat.zero_lt_of_lt hn⟩ 0 (by norm_num) (by norm_num))
      (edge i 0 (by norm_num) (by norm_num)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction i using Fin.induction with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
      have hnext : next hn j.castSucc = j.succ := by
        apply Fin.ext
        simp [next]
      rw [← hnext]
      exact Relation.EqvGen.trans _ _ _ ih (seam_origin_step hn j.castSucc)

theorem seam_origin_radial_zero (i : Fin n) :
    radialSize (edge i 0 (by norm_num) (by norm_num)) = 0 := by
  simp [radialSize, edge, Triangle.radial]

end D5.S3.Topology.CFMPCircularTriangleDiskCore
