/- GID: D5/S1/Recurrence/KatzCutoff/Reduction
   generality: I
   mirror-B: D5/B/S1/Recurrence/KatzCutoff/Reduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal Katz crossing reduces to a continuant ratio. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
escape_witness: p1_reduction
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20795
katz: proof_shape: bind-only; escape_witness: none; consumers: katzEntry, katz_step.
katzEntry: proof_shape: bind-only; escape_witness: none; consumers: katz_adj_min, katz_step, katz_two_max, p1, p1_reduction.
p1: proof_shape: bind-only; escape_witness: none; consumers: p1_reduction, claim, p1_zero_iff, result.
katz_step: proof_shape: bind-only; escape_witness: none; consumers: katz_adj_min, katz_two_max.
katz_adj_min: proof_shape: bind-only; escape_witness: none; consumers: p1_reduction.
katz_two_max: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: p1_reduction.
p1_reduction: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: p1_zero_iff.
-/

import D5.S1.Recurrence.KatzCutoff.ProductExtrema

set_option maxHeartbeats 1000000

namespace D5.S1.Recurrence.KatzCutoff.Reduction

open Matrix Finset Filter Topology
open D5.S1.Recurrence.KatzCutoff.ProductExtrema

noncomputable def katz (n : ℕ) (α : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 - α • (SimpleGraph.pathGraph n).adjMatrix ℝ)⁻¹ - 1

noncomputable def katzEntry (n : ℕ) (α : ℝ) (i j : ℕ) : ℝ :=
  if h : i < n ∧ j < n then katz n α ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

noncomputable def p1 (n : ℕ) (α : ℝ) : ℝ :=
  (⨅ i : Fin (n - 1), katzEntry n α i (i + 1)) - ⨆ i : Fin (n - 2), katzEntry n α i (i + 2)

private lemma katz_step (n : ℕ) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    (i k : ℕ) (hk : 0 < k) (hik : i+k < n) :
    katzEntry n α i (i+k) =
      α^k*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-k-1-i)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
  have hi : i < n := Nat.lt_of_add_right_lt hik
  rw [katzEntry,dite_eq_left ⟨hi,hik⟩]
  simp only [katz,Matrix.sub_apply]
  rw [path_inverse_entry n hα hα' ⟨i,hi⟩ ⟨i+k,hik⟩ (by simp)]
  have hne : (⟨i,hi⟩ : Fin n) ≠ ⟨i+k,hik⟩ := by
    intro h
    have he := congrArg Fin.val h
    simp only at he
    omega
  simp only [Fin.val_mk,Matrix.one_apply,hne,ite_false,sub_zero]
  rw [show i+k-i=k by omega,show n-1-(i+k)=n-k-1-i by omega]

private lemma katz_adj_min (n : ℕ) (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    (⨅ i : Fin (n-1), katzEntry n α i (i+1)) = α*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-2)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
  classical
  letI : Nonempty (Fin (n-1)) := ⟨⟨0,by omega⟩⟩
  apply le_antisymm
  · calc
      (⨅ i : Fin (n-1), katzEntry n α i (i+1)) ≤
          katzEntry n α 0 1 := ciInf_le (f := fun i : Fin (n-1) => katzEntry n α i (i+1))
            (Set.finite_range _).bddBelow (⟨0,by omega⟩ : Fin (n-1))
      _ = α*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-2)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
        rw [katz_step n hα hα' 0 1 (by omega) (by omega)]
        simp [d_zero, d_one, d_step,show n-1-1=n-2 by omega]
  · apply le_ciInf
    intro i
    rw [katz_step n hα hα' i.val 1 (by omega) (by omega)]
    simp only [pow_one]
    have hp := product_min hα hα' i.val (n-1-1-i.val)
    rw [show i.val+(n-1-1-i.val)=n-2 by omega] at hp
    apply div_le_div_of_nonneg_right _ (d_pos hα hα' n).le
    nlinarith

private lemma katz_two_max (n : ℕ) (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    (⨆ i : Fin (n-2), katzEntry n α i (i+2)) =
      α^2*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) ((n/2)-1)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (((n-1)/2)-1)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
  classical
  letI : Nonempty (Fin (n-2)) := ⟨⟨0,by omega⟩⟩
  have hidx : ((n-1)/2)-1 < n-2 := by omega
  have heq : n-2-1-(((n-1)/2)-1)=(n/2)-1 := by omega
  apply le_antisymm
  · apply ciSup_le
    intro i
    rw [katz_step n hα hα' i.val 2 (by omega) (by omega)]
    have hp := product_center hα hα' (n-3) i.val (by omega)
    rw [show (n-3)/2=((n-1)/2)-1 by omega,
      show n-3-(((n-1)/2)-1)=(n/2)-1 by omega] at hp
    rw [mul_comm (((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (((n-1)/2)-1)) (((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) ((n/2)-1))] at hp
    have hind : n-3-i.val=n-2-1-i.val := tsub_eq_tsub_of_add_eq_add rfl
    rw [hind] at hp
    apply div_le_div_of_nonneg_right _ (d_pos hα hα' n).le
    nlinarith [sq_nonneg α]
  · calc
      α^2*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) ((n/2)-1)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (((n-1)/2)-1)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n =
          katzEntry n α (((n-1)/2)-1) ((((n-1)/2)-1)+2) := by
        rw [katz_step n hα hα' (((n-1)/2)-1) 2 (by omega) (by omega),heq]
        ring
      _ ≤ (⨆ i : Fin (n-2), katzEntry n α i (i+2)) :=
        le_ciSup (f := fun i : Fin (n-2) => katzEntry n α i (i+2))
          (Set.finite_range _).bddAbove (⟨((n-1)/2)-1,hidx⟩ : Fin (n-2))

lemma p1_reduction (n : ℕ) (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    p1 n α = (α*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-2)/((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n)*(1-RAB α ((n/2)) (((n-1)/2))) := by
  rw [p1,katz_adj_min n hn hα hα',katz_two_max n hn hα hα',RAB]
  rw [show (n/2)+((n-1)/2)-1=n-2 by have := aa_add_bb n; omega]
  have hd := ne_of_gt (d_pos hα hα' (n-2))
  field_simp [hd]

end D5.S1.Recurrence.KatzCutoff.Reduction
