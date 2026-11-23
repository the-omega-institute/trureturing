/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Forward.structural_certificate
   digest: The registered width-3 two-defect king recurrence. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (external open-problem-resolution)
labelled: proof_shape=content; consumers=bridge
bridge: proof_shape=content; consumers=result, closed_form
result: proof_shape=content; consumers=closed_form (external open-problem-resolution #30655)
closed: proof_shape=bind-only; consumers=closed_step, initial_closed, closed_form
closed_step: proof_shape=bind-only; consumers=closed_form
initial_closed: proof_shape=bind-only; consumers=closed_form
closed_form: proof_shape=content; consumers=none (external open-problem-resolution #30655)
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.GridBridge
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Certificate
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Forward
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Topology.QuandleMarkovColoring
import Mathlib.Algebra.LinearRecurrence

/-! An exact-budget transfer proves the recurrence for every row index at least nine. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229750
open TwoDefectStrips.Width3
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

attribute [local irreducible] Data.T initial terminal W cl

private theorem labelled (m : ℕ) :
    (literalCount (q := 4) horizontal between 2 (m+1) : ℤ) =
    dotProduct initial ((Data.T ^ m).mulVec terminal) := by
  apply lumped_count horizontal between id (bondDefects between) Valid cl
    Data.T initial terminal 2 (fun _ _ => rfl)
  · intro p d h
    exact Forward.structural_certificate.1 p ⟨d, by change d ≤ 2 ∧ _ at h; omega⟩ h
  · intro p d hp r hr
    change d ≤ 2 ∧ _ at hp
    change _ ≤ 2 ∧ _
    dsimp only [id]
    constructor <;> omega
  · exact Certificate.transition_counts
  · intro r hr
    change 2 - _ ≤ 2 ∧ _
    dsimp only [id]
    constructor <;> omega
  · exact Forward.structural_certificate.2.1

private theorem bridge (m : ℕ) (hm : 1 ≤ m) :
    dotProduct initial ((Data.T ^ m).mulVec terminal) =
      24 * (KingTwoGrid.T (m+1) 3 : ℤ) := by
  rw [← labelled, TwoDefectStrips.GridBridge.literal_bridge horizontal between]
  · rw [KingTwoGrid.labelled_eq_twentyFour (m+1) 3 (by omega) (by omega) (by omega)]
    push_cast
    rfl
  · intro r
    unfold bondDefects
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    change (∑ a ∈ Finset.univ.image (fun j : Fin 2 => (j.castSucc, j.succ)),
      if r a.1 = r a.2 then 1 else 0) = _
    rw [Finset.sum_image]
    · simp [horizontal, -Finset.sum_boole, -Finset.sum_const, Fin.sum_univ_succ, KingGrid.lo, KingGrid.hi,
        D5.S3.Topology.QuandleMarkovColoring.leftSlot,
        D5.S3.Topology.QuandleMarkovColoring.rightSlot]
    · intro a ha b hb hab
      apply Fin.ext
      exact congrArg (fun x => x.1.val) hab
  · intro r t
    change bondDefects
      ({(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)} :
        Finset (Fin 3 × Fin 3)) r t = _
    unfold bondDefects
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp [-Finset.sum_boole, -Finset.sum_const, Fin.sum_univ_succ, KingGrid.lo, KingGrid.hi,
      D5.S3.Topology.QuandleMarkovColoring.leftSlot,
      D5.S3.Topology.QuandleMarkovColoring.rightSlot]
    omega

theorem result (n : ℕ) (hn : 9 ≤ n) :
    (KingTwoGrid.T n 3 : ℤ) = 9 * KingTwoGrid.T (n-1) 3 -
      33 * KingTwoGrid.T (n-2) 3 + 63 * KingTwoGrid.T (n-3) 3 -
      66 * KingTwoGrid.T (n-4) 3 + 36 * KingTwoGrid.T (n-5) 3 -
      8 * KingTwoGrid.T (n-6) 3 := by
  have tab (i : Fin 9) : forward Data.T initial i.val = W i := by
    induction i using Fin.induction with
    | zero => exact Forward.structural_certificate.2.2.1.1.symm
    | succ i ih =>
      rw [forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (forward Data.T initial i.val) Data.T = W i.succ
      change forward Data.T initial i.val = W i.castSucc at ih
      rw [ih]
      exact (Forward.structural_certificate.2.2.1.2 i).symm
  have poly : forward Data.T initial (2+6) =
      ∑ j : Fin 6, (![-8,36,-66,63,-33,9] j : ℤ) •
        forward Data.T initial (2+j.val) := by
    rw [tab ⟨8, by omega⟩]
    simp_rw [show ∀ j : Fin 6, forward Data.T initial (2+j.val) = W ⟨2+j.val, by omega⟩
      from fun j => tab ⟨2+j.val, by omega⟩]
    exact Forward.structural_certificate.2.2.2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := forward_shift Data.T initial terminal 6 2 ![-8,36,-66,63,-33,9] poly m
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one] at h
  have h5 := bridge (m+2) (by omega)
  have h6 := bridge (m+3) (by omega)
  have h7 := bridge (m+4) (by omega)
  have h8 := bridge (m+5) (by omega)
  have h9 := bridge (m+6) (by omega)
  have h10 := bridge (m+7) (by omega)
  have h11 := bridge (m+8) (by omega)
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at h h5 h6 h7 h8 h9 h10 h11
  rw [h5, h6, h7, h8, h9, h10, h11] at h
  norm_num only [Nat.reduceAdd, zero_add] at h
  have e1 : 9+m-1 = m+8 := by omega
  have e2 : 9+m-2 = m+7 := by omega
  have e3 : 9+m-3 = m+6 := by omega
  have e4 : 9+m-4 = m+5 := by omega
  have e5 : 9+m-5 = m+4 := by omega
  have e6 : 9+m-6 = m+3 := by omega
  rw [e1,e2,e3,e4,e5,e6]
  have e0 : 9+m = m+9 := by omega
  rw [e0]
  linarith

private def closed (n : ℕ) : ℤ :=
  2 * (1732 + 117 * (2 : ℤ)^n) + (279 * (2 : ℤ)^n - 4084) * (n : ℤ) +
    (9 * (2 : ℤ)^n + 484) * (n : ℤ)^2

private theorem closed_step (n : ℕ) :
    closed (n+6) = -8 * closed n + 36 * closed (n+1) - 66 * closed (n+2) +
      63 * closed (n+3) - 33 * closed (n+4) + 9 * closed (n+5) := by
  simp only [closed, pow_add, Nat.cast_add, Nat.cast_ofNat]
  norm_num
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem initial_closed : ∀ i : Fin 6,
    dotProduct initial ((Data.T ^ (i.val+2)).mulVec terminal) = 3 * closed (i.val+3) := by
  unfold initial Data.T terminal closed
  decide +kernel

theorem closed_form (n : ℕ) (hn : 3 ≤ n) :
    8 * (KingTwoGrid.T n 3 : ℤ) =
      2 * (1732 + 117 * (2 : ℤ)^n) + (279 * (2 : ℤ)^n - 4084) * (n : ℤ) +
        (9 * (2 : ℤ)^n + 484) * (n : ℤ)^2 := by
  let E : LinearRecurrence ℤ := ⟨6, ![-8,36,-66,63,-33,9]⟩
  let u : ℕ → ℤ := fun k => 8 * (KingTwoGrid.T (k+3) 3 : ℤ)
  let v : ℕ → ℤ := fun k => closed (k+3)
  have hu : E.IsSolution u := by
    intro k
    have h := result (k+9) (by omega)
    have e1 : k+9-1 = k+8 := by omega
    have e2 : k+9-2 = k+7 := by omega
    have e3 : k+9-3 = k+6 := by omega
    have e4 : k+9-4 = k+5 := by omega
    have e5 : k+9-5 = k+4 := by omega
    have e6 : k+9-6 = k+3 := by omega
    rw [e1,e2,e3,e4,e5,e6] at h
    simp only [E, u, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one,
      Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, mul_zero, add_zero]
    linarith
  have hv : E.IsSolution v := by
    intro k
    have h := closed_step (k+3)
    simp only [E, v, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
      Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one,
      Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, mul_zero, add_zero]
    simp only [Nat.add_assoc, Nat.reduceAdd] at h
    linarith
  have heq : u = v := (E.eq_iff_eqOn_range_order u v hu hv).2 (by
    intro k hk
    have hk' : k < 6 := Finset.mem_range.mp hk
    have h := bridge (k+2) (by omega)
    have hi := initial_closed ⟨k,hk'⟩
    dsimp only [u,v]
    have e : k+2+1 = k+3 := by omega
    rw [e] at h
    linarith)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa only [u,v,closed,Nat.add_comm] using congrFun heq k

end D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229750
