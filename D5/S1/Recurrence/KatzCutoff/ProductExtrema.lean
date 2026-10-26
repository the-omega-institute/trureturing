/- GID: D5/S1/Recurrence/KatzCutoff/ProductExtrema
   generality: I
   mirror-B: D5/B/S1/Recurrence/KatzCutoff/ProductExtrema
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuant identities control path inverses and extremal products. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
escape_witness: wronskian
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20795
d_zero: proof_shape: bind-only; escape_witness: none; consumers: q_monotoneOn, q_strictMono, c_add, c_rec, wronskian, katz_adj_min, continuous_d.
d_one: proof_shape: bind-only; escape_witness: none; consumers: q_strictMono, c_add, c_rec, wronskian, continuous_d.
d_step: proof_shape: bind-only; escape_witness: none; consumers: c_rec, continuous_d.
rp: proof_shape: bind-only; escape_witness: none; consumers: RAB_closed, RAB_lt_one_c, d_closed, d_pos, rp_add_rm, rp_pos, rp_quad, rp_sub_rm, RAB_t, t, t_bounds.
rm: proof_shape: bind-only; escape_witness: none; consumers: RAB_closed, RAB_lt_one_c, d_closed, d_pos, rm_quad, rp_add_rm, rp_sub_rm, RAB_t, t, t_bounds.
s_sq: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c, c_s_eq_c, d_pos, rm_quad, rp_quad, beta_limit_gt_one, t_bounds.
s_pos: proof_shape: bind-only; escape_witness: none; consumers: RAB_closed, RAB_lt_one_c, c_s_eq_c, d_closed, d_pos, rp_pos, beta_limit_gt_one, t_bounds.
rp_pos: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c, RAB_t, t_bounds.
rp_quad: proof_shape: bind-only; escape_witness: none; consumers: d_closed.
rm_quad: proof_shape: bind-only; escape_witness: none; consumers: d_closed.
rp_add_rm: proof_shape: bind-only; escape_witness: none; consumers: d_closed.
rp_sub_rm: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c, d_closed, d_pos.
d_closed: proof_shape: bind-only; escape_witness: none; consumers: RAB_closed, d_pos.
d_pos: proof_shape: bind-only; escape_witness: none; consumers: RAB_eq_div_Rden, Rden_eq, Rden_pos, q_den, q_den_pos, q_nonneg, q_rec, c_nonneg, path_inverse_entry, katz_adj_min, katz_two_max, p1_reduction, d_pos_le_half, p1_zero_iff.
d_half: proof_shape: bind-only; escape_witness: none; consumers: RAB_half_eq, d_half_pos.
d_half_pos: proof_shape: bind-only; escape_witness: none; consumers: d_pos_le_half.
RAB: proof_shape: bind-only; escape_witness: none; consumers: RAB_comm, RAB_eq_div_Rden, RAB_strictMonoOn, RAB_strict_a, RAB_strict_b, R_strict_succ, RAB_closed, RAB_gt_one_half, RAB_half_eq, RAB_half_gt_one_for_indices, RAB_lt_one_c, p1_reduction, RAB_t, R_continuousOn, R_crossing, R_eventually_gt_one, R_limit, R_root_exists, p1_zero_iff, result.
RAB_closed: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c, RAB_t.
c_bounds: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c, c_s_eq_c, R_continuousOn, R_crossing, R_eventually_gt_one, R_root_exists, beta_limit_gt_one, result.
c_s_eq_c: proof_shape: bind-only; escape_witness: none; consumers: RAB_lt_one_c.
RAB_lt_one_c: proof_shape: bind-only; escape_witness: none; consumers: R_crossing, result.
RAB_half_eq: proof_shape: bind-only; escape_witness: none; consumers: RAB_gt_one_half.
RAB_gt_one_half: proof_shape: bind-only; escape_witness: none; consumers: RAB_half_gt_one_for_indices.
aa_add_bb: proof_shape: bind-only; escape_witness: none; consumers: p1_reduction.
indices_n6: proof_shape: bind-only; escape_witness: none; consumers: RAB_half_gt_one_for_indices.
RAB_half_gt_one_for_indices: proof_shape: bind-only; escape_witness: none; consumers: R_root_exists.
c_rec: proof_shape: bind-only; escape_witness: none; consumers: Rden_eq, q_den, c_add, green_row, wronskian.
c_add: proof_shape: bind-only; escape_witness: none; consumers: Rden_eq, green_row, product_min.
greenNum: proof_shape: bind-only; escape_witness: none; consumers: green, greenNum_of_ge, greenNum_of_le, greenNum_symm, green_left_le, green_right_ge, green_row, path_inverse_entry, path_mul_green.
greenNum_symm: proof_shape: bind-only; escape_witness: none; consumers: greenNum_of_ge.
path_row: proof_shape: bind-only; escape_witness: none; consumers: path_mul_green.
greenNum_of_le: proof_shape: bind-only; escape_witness: none; consumers: greenNum_of_ge, green_left_le, green_row, path_inverse_entry.
greenNum_of_ge: proof_shape: bind-only; escape_witness: none; consumers: green_right_ge, green_row.
green_left_le: proof_shape: bind-only; escape_witness: none; consumers: green_row.
green_right_ge: proof_shape: bind-only; escape_witness: none; consumers: green_row.
green_row: proof_shape: bind-only; escape_witness: none; consumers: path_mul_green.
green: proof_shape: bind-only; escape_witness: none; consumers: path_inverse, path_inverse_entry, path_mul_green.
path_mul_green: proof_shape: bind-only; escape_witness: none; consumers: path_inverse.
path_inverse: proof_shape: bind-only; escape_witness: none; consumers: path_inverse_entry.
path_inverse_entry: proof_shape: bind-only; escape_witness: none; consumers: katz_step.
c_nonneg: proof_shape: bind-only; escape_witness: none; consumers: q_nonneg, product_balance, product_min.
product_min: proof_shape: bind-only; escape_witness: none; consumers: katz_adj_min.
wronskian: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: product_balance.
product_balance: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: product_center_left.
product_center_left: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: product_center.
product_center: proof_shape: content; escape_witness: D5.S1.Recurrence.KatzCutoff.ProductExtrema.wronskian; consumers: katz_two_max.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option maxHeartbeats 1000000

namespace D5.S1.Recurrence.KatzCutoff.ProductExtrema

open Matrix Finset Filter Topology

@[simp] theorem d_zero (α : ℝ) :
    ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) 0 = 1 := by
  exact (LinearRecurrence.mk 2 ![-α^2, 1]).mkSol_eq_init ![1, 1] 0

@[simp] theorem d_one (α : ℝ) :
    ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) 1 = 1 := by
  exact (LinearRecurrence.mk 2 ![-α^2, 1]).mkSol_eq_init ![1, 1] 1

@[simp] theorem d_step (α : ℝ) (k : ℕ) :
    ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) (k+2) =
      ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) (k+1) -
        α^2 * ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) k := by
  have h := (LinearRecurrence.mk 2 ![-α^2, 1]).is_sol_mkSol ![1, 1] k
  change ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) (k+2) =
    ∑ i : Fin 2, ![-α^2, 1] i * ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) (k+i) at h
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, add_zero, one_mul, neg_mul, sub_eq_add_neg, add_comm] using h

noncomputable def rp (α : ℝ) : ℝ := (1 + (Real.sqrt (1 - 4*α^2)))/2

noncomputable def rm (α : ℝ) : ℝ := (1 - (Real.sqrt (1 - 4*α^2)))/2

lemma s_sq {α : ℝ} (h : 0 < α) (h' : α < 1/2) : (Real.sqrt (1 - 4*α^2)) ^ 2 = 1 - 4*α^2 := by
  rw [Real.sq_sqrt]
  nlinarith

lemma s_pos {α : ℝ} (h : 0 < α) (h' : α < 1/2) : 0 < (Real.sqrt (1 - 4*α^2)) := by
  apply Real.sqrt_pos.2
  nlinarith

lemma rp_pos {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) : 0 < rp α := by
  dsimp [rp]
  have := s_pos hα hα'
  linarith

private lemma rp_quad {α : ℝ} (h : 0 < α) (h' : α < 1/2) : rp α ^ 2 = rp α - α^2 := by
  dsimp [rp]
  have hs := s_sq h h'
  ring_nf at hs ⊢
  nlinarith

private lemma rm_quad {α : ℝ} (h : 0 < α) (h' : α < 1/2) : rm α ^ 2 = rm α - α^2 := by
  dsimp [rm]
  have hs := s_sq h h'
  ring_nf at hs ⊢
  nlinarith

private lemma rp_add_rm : ∀ α : ℝ, rp α + rm α = 1 := by intro α; dsimp [rp,rm]; ring

private lemma rp_sub_rm : ∀ α : ℝ, rp α - rm α = (Real.sqrt (1 - 4*α^2)) := by intro α; dsimp [rp,rm]; ring

private lemma d_closed {α : ℝ} (h : 0 < α) (h' : α < 1/2) (k : ℕ) :
    ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k = (rp α ^ (k+1) - rm α ^ (k+1)) / (Real.sqrt (1 - 4*α^2))  := by
  let E : LinearRecurrence ℝ := LinearRecurrence.mk 2 ![-α^2, 1]
  have hs := ne_of_gt (s_pos h h')
  have hrp := rp_quad h h'
  have hrm := rm_quad h h'
  symm
  apply E.eq_mk_of_is_sol_of_eq_init (u := fun j =>
    (rp α ^ (j+1) - rm α ^ (j+1)) / Real.sqrt (1-4*α^2)) ?_ ?_ k
  · intro j
    change (rp α ^ (j+2+1) - rm α ^ (j+2+1)) / Real.sqrt (1-4*α^2) =
      ∑ i : Fin 2, ![-α^2, 1] i *
        ((rp α ^ (j+i.val+1) - rm α ^ (j+i.val+1)) / Real.sqrt (1-4*α^2))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, one_mul]
    rw [show j+2+1=(j+1)+2 by omega, show j+1+1=(j+1)+1 by omega]
    simp only [pow_add, pow_one]
    rw [hrp,hrm]
    field_simp
    ring
  · change ∀ i : Fin 2, (rp α ^ (i.val+1) - rm α ^ (i.val+1)) / Real.sqrt (1-4*α^2) = ![(1 : ℝ),1] i
    intro i
    rcases i with ⟨i, hi⟩
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl
    · norm_num only [Fin.val_mk, zero_add, pow_one, Matrix.cons_val_zero, Matrix.cons_val]
      rw [rp_sub_rm, div_self hs]
      exact (Matrix.cons_val_zero' hi (1 : ℝ) ![1]).symm
    · change (rp α ^ 2 - rm α ^ 2) / Real.sqrt (1-4*α^2) = 1
      have he : rp α ^ 2 - rm α ^ 2 = Real.sqrt (1-4*α^2) := by
        calc
          _ = (rp α - rm α) * (rp α + rm α) := by ring
          _ = _ := by rw [rp_sub_rm, rp_add_rm]; ring
      rw [he, div_self hs]

lemma d_pos {α : ℝ} (h : 0 < α) (h' : α < 1/2) (k : ℕ) : 0 < ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k := by
  rw [d_closed h h' k]
  have hs := s_pos h h'
  have h1 : rm α < rp α := by nlinarith [rp_sub_rm α]
  have hSlt : (Real.sqrt (1 - 4*α^2)) < 1 := by nlinarith [s_sq h h']
  have h0 : 0 ≤ rm α := by dsimp [rm]; nlinarith
  have hpow : rm α ^ (k+1) < rp α ^ (k+1) := by
    exact pow_lt_pow_left₀ h1 h0 (by omega)
  have hnum : 0 < rp α ^ (k+1) - rm α ^ (k+1) := sub_pos.mpr hpow
  exact div_pos hnum hs

private lemma d_half (k : ℕ) : ((LinearRecurrence.mk 2 ![-((1/2 : ℝ))^2, 1]).mkSol ![1, 1]) k = (k+1) / 2^k  := by
  let E : LinearRecurrence ℝ := LinearRecurrence.mk 2 ![-((1/2 : ℝ))^2, 1]
  symm
  apply E.eq_mk_of_is_sol_of_eq_init (u := fun j => (j+1 : ℝ)/2^j) ?_ ?_ k
  · intro j
    change (((j+2 : ℕ) : ℝ)+1)/2^(j+2) =
      ∑ i : Fin 2, ![-((1/2 : ℝ))^2, 1] i * ((((j+i.val : ℕ) : ℝ)+1)/2^(j+i.val))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, Nat.cast_add, Nat.cast_one, one_mul]
    norm_num [pow_add]
    field_simp
    ring
  · intro i
    fin_cases i <;> norm_num

lemma d_half_pos (k : ℕ) : 0 < ((LinearRecurrence.mk 2 ![-((1/2 : ℝ))^2, 1]).mkSol ![1, 1]) k := by
  rw [d_half]
  positivity

noncomputable def RAB (α : ℝ) (a b : ℕ) : ℝ :=
  α * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a-1) * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (b-1) / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (a+b-1)

lemma RAB_closed {α : ℝ} (h : 0 < α) (h' : α < 1/2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    RAB α a b = (α / (Real.sqrt (1 - 4*α^2))) *
      ((rp α ^ a - rm α ^ a) * (rp α ^ b - rm α ^ b)) /
      (rp α ^ (a+b) - rm α ^ (a+b)) := by
  rw [RAB, d_closed h h' (a-1), d_closed h h' (b-1), d_closed h h' (a+b-1)]
  have haa : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have hbb : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hab : a + b - 1 + 1 = a + b := Nat.sub_add_cancel (by omega)
  rw [haa, hbb, hab]
  have hs := s_pos h h'
  field_simp [ne_of_gt hs]

lemma c_bounds : 0 < (1 / Real.sqrt 5 : ℝ) ∧ (1 / Real.sqrt 5 : ℝ) < 1/2 := by
  have hs : 0 < Real.sqrt (5:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt (5:ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  constructor <;> (field_simp; nlinarith)

private lemma c_s_eq_c : (Real.sqrt (1 - 4 * (1 / Real.sqrt 5)^2)) = (1 / Real.sqrt 5 : ℝ) := by
  have hc := c_bounds.1
  have hc' := c_bounds.2
  have hs := s_pos hc hc'
  have hsq := s_sq hc hc'
  have hc2 : (1 / Real.sqrt 5 : ℝ)^2 = 1/5 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  nlinarith

lemma RAB_lt_one_c {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    RAB (1 / Real.sqrt 5) a b < 1 := by
  have hc := c_bounds.1
  have hc' := c_bounds.2
  rw [RAB_closed hc hc' ha hb]
  rw [c_s_eq_c]
  have hrp : 0 < rp (1 / Real.sqrt 5) := rp_pos hc hc'
  have hrm : 0 < rm (1 / Real.sqrt 5) := by
    dsimp [rm]
    have hs := s_pos hc hc'
    have hsl : (Real.sqrt (1 - 4 * (1 / Real.sqrt 5)^2)) < 1 := by nlinarith [s_sq hc hc']
    nlinarith
  have hs := s_pos hc hc'
  have hlt : rm (1 / Real.sqrt 5) < rp (1 / Real.sqrt 5) := by
    have hdiff := rp_sub_rm (1 / Real.sqrt 5)
    nlinarith [hdiff, hs]
  have hpa : rm (1 / Real.sqrt 5) ^ a < rp (1 / Real.sqrt 5) ^ a :=
    pow_lt_pow_left₀ hlt (le_of_lt hrm) (by omega)
  have hpb : rm (1 / Real.sqrt 5) ^ b < rp (1 / Real.sqrt 5) ^ b :=
    pow_lt_pow_left₀ hlt (le_of_lt hrm) (by omega)
  have hpa0 : 0 < rm (1 / Real.sqrt 5) ^ a := pow_pos hrm a
  have hpb0 : 0 < rm (1 / Real.sqrt 5) ^ b := pow_pos hrm b
  have hcross1 : rm (1 / Real.sqrt 5) ^ (a+b) <
      rp (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b := by
    rw [pow_add]
    exact (mul_lt_mul_of_pos_right hpa hpb0)
  have hcross2 : rm (1 / Real.sqrt 5) ^ (a+b) <
      rm (1 / Real.sqrt 5) ^ a * rp (1 / Real.sqrt 5) ^ b := by
    rw [pow_add]
    exact (mul_lt_mul_of_pos_left hpb hpa0)
  have hden : 0 < rp (1 / Real.sqrt 5) ^ (a+b) - rm (1 / Real.sqrt 5) ^ (a+b) := by
    exact sub_pos.mpr (pow_lt_pow_left₀ hlt (le_of_lt hrm) (by omega))
  have hx1 : 0 < rp (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b -
      rm (1 / Real.sqrt 5) ^ (a+b) := sub_pos.mpr hcross1
  have hx2 : 0 < rm (1 / Real.sqrt 5) ^ a * rp (1 / Real.sqrt 5) ^ b -
      rm (1 / Real.sqrt 5) ^ (a+b) := sub_pos.mpr hcross2
  have hdiff : 0 <
      (rp (1 / Real.sqrt 5) ^ (a+b) - rm (1 / Real.sqrt 5) ^ (a+b)) -
      ((rp (1 / Real.sqrt 5) ^ a - rm (1 / Real.sqrt 5) ^ a) *
       (rp (1 / Real.sqrt 5) ^ b - rm (1 / Real.sqrt 5) ^ b)) := by
    calc
      (rp (1 / Real.sqrt 5) ^ (a + b) - rm (1 / Real.sqrt 5) ^ (a + b)) -
          ((rp (1 / Real.sqrt 5) ^ a - rm (1 / Real.sqrt 5) ^ a) *
           (rp (1 / Real.sqrt 5) ^ b - rm (1 / Real.sqrt 5) ^ b)) =
          (rp (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b -
            rm (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b) +
          (rm (1 / Real.sqrt 5) ^ a * rp (1 / Real.sqrt 5) ^ b -
            rm (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b) := by ring
      _ = (rp (1 / Real.sqrt 5) ^ a * rm (1 / Real.sqrt 5) ^ b -
            rm (1 / Real.sqrt 5) ^ (a+b)) +
          (rm (1 / Real.sqrt 5) ^ a * rp (1 / Real.sqrt 5) ^ b -
            rm (1 / Real.sqrt 5) ^ (a+b)) := by rw [pow_add]
      _ > 0 := add_pos hx1 hx2
  have hnum : 0 <
      ((rp (1 / Real.sqrt 5) ^ a - rm (1 / Real.sqrt 5) ^ a) *
       (rp (1 / Real.sqrt 5) ^ b - rm (1 / Real.sqrt 5) ^ b)) := by
    exact mul_pos (sub_pos.mpr hpa) (sub_pos.mpr hpb)
  have hcquot : (1 / Real.sqrt 5) / (1 / Real.sqrt 5) = (1:ℝ) :=
    div_self (ne_of_gt c_bounds.1)
  rw [hcquot]
  apply (div_lt_iff₀ hden).2
  nlinarith [hdiff]

private lemma RAB_half_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    RAB (1/2 : ℝ) a b = (a:ℝ) * b / (a+b) := by
  rw [RAB, d_half, d_half, d_half]
  have haa : a - 1 + 1 = a := Nat.sub_add_cancel ha
  have hbb : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hab : a + b - 1 + 1 = a + b := Nat.sub_add_cancel (by omega)
  have hcasta : ((a - 1 : ℕ) : ℝ) = (a:ℝ) - 1 := Nat.cast_pred ha
  have hcastb : ((b - 1 : ℕ) : ℝ) = (b:ℝ) - 1 := Nat.cast_pred hb
  have hcastab : (((a + b) - 1 : ℕ) : ℝ) = (a:ℝ) + b - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a+b)]
    norm_num
  rw [hcasta, hcastb, hcastab]
  norm_num at *
  have hpow : (2:ℝ) ^ (a+b) = 2^a * 2^b := pow_add 2 a b
  have hpowa : (2:ℝ) ^ a ≠ 0 := Ne.symm (NeZero.ne' (2 ^ a))
  have hpowb : (2:ℝ) ^ b ≠ 0 := Ne.symm (NeZero.ne' (2 ^ b))
  have hpows : (2:ℝ) ^ (a+b-1) ≠ 0 := Ne.symm (NeZero.ne' (2 ^ (a+b-1)))
  have hpowS : (2:ℝ) ^ (a+b-1) = 2 * 2^(a-1) * 2^(b-1) := by
    rw [show a+b-1 = 1 + (a-1) + (b-1) by omega, pow_add, pow_add]
    ring
  field_simp [hpowa, hpowb, hpows]
  rw [hpowS]

private lemma RAB_gt_one_half {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : 4 < a + b) : 1 < RAB (1/2 : ℝ) a b := by
  have ha0 : 0 < a := Nat.zero_lt_of_lt ha
  have hb0 : 0 < b := Nat.zero_lt_of_lt hb
  rw [RAB_half_eq ha0 hb0]
  have hpos : 0 < (a+b : ℝ) := by positivity
  apply (lt_div_iff₀ hpos).2
  have ha' : (2:ℝ) ≤ a := Nat.ofNat_le_cast.mpr ha
  have hb' : (2:ℝ) ≤ b := Nat.ofNat_le_cast.mpr hb
  have hab' : (4:ℝ) < a+b := by exact_mod_cast hab
  have hmul : 0 ≤ ((a:ℝ)-2) * ((b:ℝ)-2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma aa_add_bb (n : ℕ) : (n/2) + ((n-1)/2) = n - 1 := by
  omega

private lemma indices_n6 (n : ℕ) (hn : 6 ≤ n) :
    2 ≤ (n/2) ∧ 2 ≤ ((n-1)/2) ∧ 4 < (n/2) + ((n-1)/2) := by
  omega

lemma RAB_half_gt_one_for_indices (n : ℕ) (hn : 6 ≤ n) :
    1 < RAB (1/2 : ℝ) ((n/2)) (((n-1)/2)) := by
  obtain ⟨ha, hb, hab⟩ := indices_n6 n hn
  exact RAB_gt_one_half ha hb hab

lemma c_rec (α : ℝ) (k : ℕ) :
    (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (k+2) = (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (k+1) - α^2 * (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) k := by
  cases k with
  | zero => simp [Nat.casesOn,d_zero, d_one, d_step]
  | succ k => simp [Nat.casesOn,d_zero, d_one, d_step]

lemma c_add (α : ℝ) (i j : ℕ) :
    (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+1) = (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (j+1) - α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) i*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j  := by
  let C : ℕ → ℝ := fun k => Nat.casesOn k 0
    (fun j => ((LinearRecurrence.mk 2 ![-α^2, 1]).mkSol ![1, 1]) j)
  let E : LinearRecurrence ℝ := LinearRecurrence.mk 2 ![-α^2, 1]
  have hrec (k : ℕ) : C (k+2) = C (k+1) - α^2*C k := c_rec α k
  let U : ℕ → ℝ := fun k => C (i+k+1)
  let V : ℕ → ℝ := fun k => C (i+1)*C (k+1)-α^2*C i*C k
  have hu : E.IsSolution U := by
    intro k
    change C (i+(k+2)+1) = ∑ t : Fin 2, ![-α^2,1] t * C (i+(k+t.val)+1)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, one_mul]
    rw [show i+(k+2)+1=(i+k+1)+2 by omega, hrec]
    rw [show i+(k+1)+1=i+k+1+1 by omega]
    ring
  have hv : E.IsSolution V := by
    intro k
    change C (i+1)*C (k+2+1)-α^2*C i*C (k+2) =
      ∑ t : Fin 2, ![-α^2,1] t * (C (i+1)*C (k+t.val+1)-α^2*C i*C (k+t.val))
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero, one_mul]
    rw [show k+2+1=(k+1)+2 by omega, hrec (k+1), hrec k]
    ring
  have hi : ∀ k : Fin E.order, V k = U k := by
    intro k
    fin_cases k
    · simp [V, U, C, d_zero, d_one, d_step]
    · change C (i+1)*C 2-α^2*C i*C 1 = C (i+2)
      rw [show C 2 = 1 from d_one α, show C 1 = 1 from d_zero α]
      simpa only [mul_one] using (hrec i).symm
  change U j = V j
  exact (E.eq_mk_of_is_sol_of_eq_init hu (fun _ => rfl) j).trans
    (E.eq_mk_of_is_sol_of_eq_init hv hi j).symm

private noncomputable def greenNum (α : ℝ) (n i j : ℕ) : ℝ :=
  if i ≤ j then α^(j-i)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-j)
  else α^(i-j)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (j+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i)

private lemma greenNum_symm (α : ℝ) (n i j : ℕ) :
    greenNum α n i j = greenNum α n j i := by
  unfold greenNum
  split_ifs with h₁ h₂ <;> try rfl
  · have : i = j := Nat.le_antisymm h₁ h₂
    subst j; rfl
  · omega

private lemma path_row (n : ℕ) (α : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((1 - α • (SimpleGraph.pathGraph n).adjMatrix ℝ) * M) i j =
    M i j - α * ((if h : 0 < i.val then M ⟨i.val-1, by omega⟩ j else 0) +
      (if h : i.val+1 < n then M ⟨i.val+1,h⟩ j else 0)) := by
  classical
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  congr 2
  have hadj : ∀ k : Fin n,
      (SimpleGraph.pathGraph n).adjMatrix ℝ i k * M k j =
      (if k.val+1=i.val then M k j else 0) + (if i.val+1=k.val then M k j else 0) := by
    intro k
    simp only [SimpleGraph.adjMatrix, SimpleGraph.pathGraph_adj]
    split_ifs <;> simp_all <;> omega
  simp_rw [hadj]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases h : 0 < i.val
    · rw [dite_eq_left h]
      rw [Finset.sum_eq_single (⟨i.val-1,by omega⟩ : Fin n)]
      · simp [Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
      · intro b hb hne
        simp only [Finset.mem_univ] at hb
        have hnot : ¬ b.val+1=i.val := by
          intro he
          apply hne
          apply Fin.ext
          change b.val = i.val-1
          omega
        simp [hnot]
      · simp
    · rw [dite_eq_right h]
      apply Finset.sum_eq_zero
      intro b hb
      have : ¬ b.val+1=i.val := by omega
      simp [this]
  · by_cases h : i.val+1<n
    · rw [dite_eq_left h]
      rw [Finset.sum_eq_single (⟨i.val+1,h⟩ : Fin n)]
      · simp
      · intro b hb hne
        have hnot : ¬ i.val+1=b.val := by
          intro he
          apply hne
          apply Fin.ext
          change b.val = i.val+1
          omega
        simp [hnot]
      · simp
    · rw [dite_eq_right h]
      apply Finset.sum_eq_zero
      intro b hb
      have : ¬ i.val+1=b.val := by omega
      simp [this]

private lemma greenNum_of_le (α : ℝ) (n i j : ℕ) (h : i ≤ j) :
    greenNum α n i j = α^(j-i)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-j) := by
  simp [greenNum,h]

private lemma greenNum_of_ge (α : ℝ) (n i j : ℕ) (h : j ≤ i) :
    greenNum α n i j = α^(i-j)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (j+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i) := by
  rw [greenNum_symm,greenNum_of_le α n j i h]

private lemma green_left_le (α : ℝ) (n i j : ℕ) (h : i ≤ j) :
    (if 0 < i then greenNum α n (i-1) j else 0) =
      α^(j-i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) i*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-j) := by
  by_cases hi : 0 < i
  · rw [ite_eq_left hi,greenNum_of_le α n (i-1) j (by omega)]
    rw [show i-1+1=i by omega,show j-(i-1)=j-i+1 by omega]
  · have : i=0 := Nat.eq_zero_of_not_pos hi
    subst i
    simp

private lemma green_right_ge (α : ℝ) (n i j : ℕ) (hi : i < n) (h : j ≤ i) :
    (if i+1 < n then greenNum α n (i+1) j else 0) =
      α^(i-j+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (j+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i-1) := by
  by_cases hnext : i+1 < n
  · rw [ite_eq_left hnext,greenNum_of_ge α n (i+1) j (by omega)]
    rw [show i+1-j=i-j+1 by omega,show n-(i+1)=n-i-1 by omega]
  · have : n-i-1=0 := by omega
    simp [hnext,this]

private lemma green_row (α : ℝ) (n i j : ℕ) (hi : i < n) (hj : j < n) :
    greenNum α n i j - α*((if 0 < i then greenNum α n (i-1) j else 0) +
      (if i+1 < n then greenNum α n (i+1) j else 0)) =
      if i=j then (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n+1) else 0 := by
  rcases lt_trichotomy i j with h | h | h
  · rw [ite_eq_right (by omega : i ≠ j), greenNum_of_le α n i j h.le,
      green_left_le α n i j h.le, ite_eq_left (by omega : i+1 < n),
      greenNum_of_le α n (i+1) j (by omega)]
    have hp : α^(j-i) = α^(j-i-1)*α := by
      rw [← pow_succ]; congr 1; omega
    have hp2 : α^(j-i+1) = α^(j-i-1)*α^2 := by
      rw [← pow_add]; congr 1; omega
    rw [hp2,hp, show j-(i+1)=j-i-1 by omega,
      show i+1+1=i+2 by omega, c_rec α i]
    ring
  · subst j
    rw [ite_eq_left rfl, greenNum_of_le α n i i le_rfl,
      green_left_le α n i i le_rfl, green_right_ge α n i i hi le_rfl]
    simp only [Nat.sub_self, pow_zero, one_mul, zero_add, pow_one]
    have hadd := c_add α (i+1) (n-i-1)
    rw [show i+1+(n-i-1)+1=n+1 by omega,
      show n-i-1+1=n-i by omega, show i+1+1=i+2 by omega, c_rec α i] at hadd
    nlinarith [hadd]
  · rw [ite_eq_right (by omega : i ≠ j), greenNum_of_ge α n i j h.le,
      ite_eq_left (by omega : 0 < i), greenNum_of_ge α n (i-1) j (by omega),
      green_right_ge α n i j hi h.le]
    have hp : α^(i-j) = α^(i-j-1)*α := by
      rw [← pow_succ]; congr 1; omega
    have hp2 : α^(i-j+1) = α^(i-j-1)*α^2 := by
      rw [← pow_add]; congr 1; omega
    have hc : (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i+1) = (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i) - α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (n-i-1) := by
      have hx := c_rec α (n-i-1)
      rwa [show n-i-1+2=n-i+1 by omega,show n-i-1+1=n-i by omega] at hx
    rw [hp2,hp,show i-1-j=i-j-1 by omega,
      show n-(i-1)=n-i+1 by omega,hc]
    ring

private noncomputable def green (n : ℕ) (α : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => greenNum α n i.val j.val / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n

private lemma path_mul_green (n : ℕ) {α : ℝ} (hd : ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n ≠ 0) :
    (1 - α • (SimpleGraph.pathGraph n).adjMatrix ℝ) * green n α = 1 := by
  classical
  ext i j
  rw [path_row]
  simp only [green]
  have hleft : (if h : 0 < i.val then greenNum α n (i.val-1) j.val / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n else 0) =
      (if 0 < i.val then greenNum α n (i.val-1) j.val else 0) / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
    split_ifs <;> simp
  have hright : (if h : i.val+1<n then greenNum α n (i.val+1) j.val / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n else 0) =
      (if i.val+1<n then greenNum α n (i.val+1) j.val else 0) / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
    split_ifs <;> simp
  rw [hleft,hright,← add_div,← mul_div_assoc,← sub_div,
    green_row α n i.val j.val i.isLt j.isLt]
  by_cases hij : i=j
  · subst j
    simp [Nat.casesOn,hd]
  · have hv : i.val ≠ j.val := Fin.val_ne_of_ne hij
    simp [hv,Matrix.one_apply,hij]

private lemma path_inverse (n : ℕ) {α : ℝ} (hd : ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n ≠ 0) :
    (1 - α • (SimpleGraph.pathGraph n).adjMatrix ℝ)⁻¹ = green n α :=
  Matrix.inv_eq_right_inv (path_mul_green n hd)

lemma path_inverse_entry (n : ℕ) {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    (i j : Fin n) (hij : i.val ≤ j.val) :
    (1 - α • (SimpleGraph.pathGraph n).adjMatrix ℝ)⁻¹ i j =
      α^(j.val-i.val) * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i.val * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (n-1-j.val) / ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) n := by
  rw [path_inverse n (ne_of_gt (d_pos hα hα' n))]
  simp only [green,greenNum_of_le α n i.val j.val hij]
  rw [show n-j.val=(n-1-j.val)+1 by omega]

lemma c_nonneg {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (k : ℕ) : (0 : ℝ) ≤ (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) k := by
  cases k with
  | zero => simp
  | succ k => exact (d_pos hα hα' k).le

lemma product_min {α : ℝ} (hα : 0 < α) (hα' : α < 1/2) (i j : ℕ) :
    ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (i+j) ≤ ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j := by
  have h := c_add α i j
  change ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (i+j) = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j - α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) i*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j at h
  have hn : 0 ≤ α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) i*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (c_nonneg hα hα' i)) (c_nonneg hα hα' j)
  linarith

private lemma wronskian (α : ℝ) (i j : ℕ) :
    (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+2)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+1)-(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+2) =
      α^(2*(i+1))*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j := by
  induction i with
  | zero =>
    simp only [Nat.zero_add]
    have hr := c_rec α j
    change ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (j + 1) = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j - α ^ 2 * (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j at hr
    change ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) 1 * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j - ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) 0 * ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (j + 1) =
      α ^ 2 * (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j
    simp only [d_zero, d_one, one_mul]
    nlinarith [hr]
  | succ i ih =>
    have hr3 := c_rec α (i+1)
    have hr4 := c_rec α (i+j+1)
    rw [show i+1+2=(i+1)+2 by omega,hr3,
      show i+1+j+1=i+j+2 by omega,
      show i+1+j+2=(i+j+1)+2 by omega,hr4]
    have heq :
        ((fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1+1)-α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1))*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+2) -
          (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1+1)*((fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+1+1)-α^2*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+1)) =
        α^2*((fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+2)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+1)-(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+1)*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (i+j+2)) := by
      rw [show i+1+1=i+2 by omega,show i+j+1+1=i+j+2 by omega]
      ring
    rw [heq,ih]
    rw [show 2*(i+1+1)=2+2*(i+1) by omega,pow_add]
    ring

private lemma product_balance {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    (i j : ℕ) (hij : i < j) :
    ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j ≤ ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (i+1)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (j-1) := by
  have hw := wronskian α i (j-1-i)
  rw [show i+(j-1-i)+1=j by omega,show i+(j-1-i)+2=j+1 by omega] at hw
  have hcj : (fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) j = ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (j-1) := by
    rw [show j=(j-1)+1 by omega]; rfl
  rw [hcj] at hw
  change ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (i+1)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (j-1)-((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) i*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j = _ at hw
  have hn : 0 ≤ α^(2*(i+1))*(fun k : ℕ => Nat.casesOn k (0 : ℝ) (fun j => ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) j)) (j-1-i) :=
    mul_nonneg (pow_nonneg hα.le _) (c_nonneg hα hα' _)
  linarith

private lemma product_center_left {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    (m k : ℕ) (hk : k ≤ m/2) :
    ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m-k) ≤ ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m/2)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m-m/2) := by
  induction hk using Nat.decreasingInduction with
  | self => exact le_rfl
  | of_succ k hk ih =>
    have hs := product_balance hα hα' k (m-k) (by omega)
    rw [show m-k-1=m-(k+1) by omega] at hs
    exact hs.trans ih

lemma product_center {α : ℝ} (hα : 0 < α) (hα' : α < 1/2)
    (m k : ℕ) (hk : k ≤ m) :
    ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m-k) ≤ ((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m/2)*((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m-m/2) := by
  by_cases h : k ≤ m/2
  · exact product_center_left hα hα' m k h
  · have hs := product_center_left hα hα' m (m-k) (by omega)
    rw [show m-(m-k)=k by omega,mul_comm (((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) (m-k)) (((LinearRecurrence.mk 2 ![-(α)^2, 1]).mkSol ![1, 1]) k)] at hs
    exact hs

end D5.S1.Recurrence.KatzCutoff.ProductExtrema
