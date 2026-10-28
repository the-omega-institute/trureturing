/- GID: D5/S1/Recurrence/KatzCutoff/Monotone
   generality: I
   mirror-B: D5/B/S1/Recurrence/KatzCutoff/Monotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive continued fractions give strict resolvent monotonicity. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
escape_witness: q_monotoneOn
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20795
q: proof_shape: bind-only; escape_witness: none; consumers: RAB_strictMonoOn, RAB_strict_a, Rden, Rden_eq, q_den, q_den_pos, q_monotoneOn, q_nonneg, q_rec, q_strictMono.
q_nonneg: proof_shape: bind-only; escape_witness: none; consumers: RAB_strictMonoOn, q_monotoneOn.
q_den: proof_shape: bind-only; escape_witness: none; consumers: q_den_pos, q_rec.
q_den_pos: proof_shape: bind-only; escape_witness: none; consumers: q_monotoneOn, q_strictMono.
q_rec: proof_shape: bind-only; escape_witness: none; consumers: q_monotoneOn, q_strictMono.
q_monotoneOn: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn; consumers: RAB_strictMonoOn.
q_strictMono: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_strictMono; consumers: RAB_strict_a.
Rden: proof_shape: bind-only; escape_witness: none; consumers: RAB_eq_div_Rden, RAB_strictMonoOn, RAB_strict_a, Rden_eq, Rden_pos.
Rden_eq: proof_shape: bind-only; escape_witness: none; consumers: RAB_eq_div_Rden, Rden_pos.
Rden_pos: proof_shape: bind-only; escape_witness: none; consumers: RAB_strictMonoOn, RAB_strict_a.
RAB_eq_div_Rden: proof_shape: bind-only; escape_witness: none; consumers: RAB_strictMonoOn, RAB_strict_a.
RAB_strictMonoOn: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_monotoneOn; consumers: R_crossing, result.
RAB_strict_a: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_strictMono; consumers: RAB_strict_b, R_strict_succ.
RAB_comm: proof_shape: bind-only; escape_witness: none; consumers: RAB_strict_b.
RAB_strict_b: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_strictMono; consumers: R_strict_succ.
R_strict_succ: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.Monotone.q_strictMono; consumers: R_root_exists.
-/

import D5.S1.Recurrence.KatzCutoff.ProductExtrema

set_option maxHeartbeats 1000000

namespace D5.S1.Recurrence.KatzCutoff.Monotone

open Matrix Finset Filter Topology
open D5.S1.Recurrence.KatzCutoff.ProductExtrema

private noncomputable def q (α : ℝ) (k : ℕ) : ℝ := α*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) k/(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (k+1)

private lemma q_nonneg {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (k : ℕ) : 0 ≤ q α k := by
  exact div_nonneg (mul_nonneg hα.le (c_nonneg hα hα' k)) (d_pos hα hα' k).le

private lemma q_den {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (k : ℕ) :
    1-α*q α k = (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (k+2)/(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (k+1) := by
  dsimp [q]
  have hr := c_rec α k
  change ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (k + 1) = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k - α ^ 2 * (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) k at hr
  rw [hr]
  have hne : ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k ≠ 0 :=
    ne_of_gt (d_pos hα hα' k)
  field_simp [hne] <;> ring

private lemma q_den_pos {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (k : ℕ) :
    0 < 1-α*q α k := by
  rw [q_den hα hα' k]
  exact div_pos (d_pos hα hα' (k+1)) (d_pos hα hα' k)

private lemma q_rec {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (k : ℕ) :
    q α (k+1) = α/(1-α*q α k) := by
  rw [q_den hα hα' k]
  dsimp [q]
  field_simp [ne_of_gt (d_pos hα hα' k),ne_of_gt (d_pos hα hα' (k+1))]

private lemma q_monotoneOn (k : ℕ) : MonotoneOn (fun α => q α k) (Set.Ioo 0 (1/2)) := by
  induction k with
  | zero => intro x hx y hy hxy; simp [q]
  | succ k ih =>
    intro x hx y hy hxy
    change q x (k+1) ≤ q y (k+1)
    rw [q_rec hx.1 hx.2 k,q_rec hy.1 hy.2 k]
    apply div_le_div₀ hy.1.le hxy (q_den_pos hy.1 hy.2 k)
    have hq := ih hx hy hxy
    have hm := mul_le_mul hxy hq (q_nonneg hx.1 hx.2 k) hy.1.le
    linarith

private lemma q_strictMono {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) : StrictMono (q α) := by
  apply strictMono_nat_of_lt_succ
  intro k
  induction k with
  | zero => simpa [q,Nat.casesOn,d_zero, d_one, d_step] using hα
  | succ k ih =>
    rw [q_rec hα hα' k,q_rec hα hα' (k+1)]
    apply div_lt_div_of_pos_left hα (q_den_pos hα hα' (k+1))
    nlinarith

private noncomputable def Rden (α : ℝ) (a b : ℕ) : ℝ :=
  1-α*q α (a-1)-α*q α (b-1)

private lemma Rden_eq {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Rden α a b = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a+b-1)/(((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a-1)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (b-1)) := by
  have hca : (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) a = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a-1) := by rw [show a=(a-1)+1 by omega]; rfl
  have hcb : (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) b = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (b-1) := by rw [show b=(b-1)+1 by omega]; rfl
  have hcab : (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (a+b) = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a+b-1) := by
    rw [show a+b=(a+b-1)+1 by omega]; rfl
  have hadd := c_add α (a-1) b
  rw [show a-1+b+1=a+b by omega,show a-1+1=a by omega] at hadd
  have hr := c_rec α (b-1)
  rw [show b-1+2=b+1 by omega,show b-1+1=b by omega] at hr
  rw [hr] at hadd
  unfold Rden q
  rw [show a-1+1=a by omega,show b-1+1=b by omega,←hca,←hcb,←hcab,hadd]
  field_simp [hca,hcb,ne_of_gt (d_pos hα hα' (a-1)),ne_of_gt (d_pos hα hα' (b-1))]
  ring

private lemma Rden_pos {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < Rden α a b := by
  rw [Rden_eq hα hα' ha hb]
  exact div_pos (d_pos hα hα' _) (mul_pos (d_pos hα hα' _) (d_pos hα hα' _))

private lemma RAB_eq_div_Rden {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : RAB α a b = α/Rden α a b := by
  rw [Rden_eq hα hα' ha hb,RAB]
  field_simp [ne_of_gt (d_pos hα hα' (a+b-1))]

lemma RAB_strictMonoOn {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (fun α => RAB α a b) (Set.Ioo 0 (1/2)) := by
  intro x hx y hy hxy
  change RAB x a b < RAB y a b
  rw [RAB_eq_div_Rden hx.1 hx.2 ha hb,RAB_eq_div_Rden hy.1 hy.2 ha hb]
  apply div_lt_div₀ hxy _ hy.1.le (Rden_pos hy.1 hy.2 ha hb)
  have hqa := q_monotoneOn (a-1) hx hy hxy.le
  have hqb := q_monotoneOn (b-1) hx hy hxy.le
  have hma := mul_le_mul hxy.le hqa (q_nonneg hx.1 hx.2 (a-1)) hy.1.le
  have hmb := mul_le_mul hxy.le hqb (q_nonneg hx.1 hx.2 (b-1)) hy.1.le
  dsimp [Rden]
  linarith

private lemma RAB_strict_a {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : RAB α a b < RAB α (a+1) b := by
  rw [RAB_eq_div_Rden hα hα' ha hb,RAB_eq_div_Rden hα hα' (by omega : 0 < a+1) hb]
  apply div_lt_div_of_pos_left hα (Rden_pos hα hα' (by omega : 0 < a+1) hb)
  have hq := q_strictMono hα hα' (by omega : a-1 < a)
  dsimp [Rden]
  nlinarith

private lemma RAB_comm (α : ℝ) (a b : ℕ) : RAB α a b = RAB α b a := by
  unfold RAB
  rw [Nat.add_comm a b]
  ring

private lemma RAB_strict_b {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : RAB α a b < RAB α a (b+1) := by
  rw [RAB_comm α a b,RAB_comm α a (b+1)]
  exact RAB_strict_a hα hα' hb ha

lemma R_strict_succ (n : ℕ) (hn : 6 ≤ n) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) :
    RAB α ((n/2)) (((n-1)/2)) < RAB α (((n+1)/2)) ((((n+1)-1)/2)) := by
  have ha : 0 < (n/2) := by omega
  have hb : 0 < ((n-1)/2) := by omega
  have hidx : (((n+1)/2)=(n/2)+1 ∧ (((n+1)-1)/2)=((n-1)/2)) ∨
      (((n+1)/2)=(n/2) ∧ (((n+1)-1)/2)=((n-1)/2)+1) := by
    omega
  rcases hidx with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]; exact RAB_strict_a hα hα' ha hb
  · rw [h1,h2]; exact RAB_strict_b hα hα' ha hb

end D5.S1.Recurrence.KatzCutoff.Monotone
