/- GID: D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every even hypercube of dimension at least four has a nonuniform Grover fixed point. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#14480; Proved)
Direct frozen dependency: D5/S3/Quantum/Dynamics/PositivePauliClockOrder.scalarPhase
  declaration statement_id: sha256:ad00aa5b981da63c8cd690c8d16f88472173b2bb73ff94386201e1774678da4d.
The imported phase supplies the construction parameter; casts and multiplication order
are normalized inside phase_pow and z_re.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: pair_ne: bind-only; consumers: pair_cancel.
proof_shape: pair_distinct: bind-only; consumers: pair_cancel.
proof_shape: mem_flip: bind-only; consumers: bit_flip_self, bit_flip_other, flip_card_mem, flip_card_not_mem, edge_identity.
proof_shape: flip_flip: bind-only; consumers: edge_identity, fixed_point.
proof_shape: bit_flip_self: bind-only; consumers: pair_cancel.
proof_shape: bit_flip_other: bind-only; consumers: pair_cancel.
proof_shape: pair_cancel: bind-only; consumers: neighbour_sum.
proof_shape: neighbour_sum: bind-only; consumers: S_eq_f.
proof_shape: f_card: bind-only; consumers: f_support, transversal_card.
proof_shape: f_support: bind-only; consumers: S_eq_f, edge_identity.
proof_shape: a_mem_transversal: bind-only; consumers: f_transversal, u_at_transversal.
proof_shape: b_not_mem_transversal: bind-only; consumers: f_transversal.
proof_shape: f_transversal: bind-only; consumers: transversal_card, u_at_transversal.
proof_shape: transversal_card: bind-only; consumers: u_at_transversal.
proof_shape: flip_card_mem: bind-only; consumers: S_eq_f, edge_identity.
proof_shape: flip_card_not_mem: bind-only; consumers: S_eq_f, edge_identity.
proof_shape: sum_two_values: bind-only; consumers: S_eq_f.
proof_shape: S_eq_f: bind-only; consumers: fixed_point.
proof_shape: edge_identity: bind-only; consumers: fixed_point.
proof_shape: phase_pow: bind-only; consumers: z_power, fixed_point.
proof_shape: z_power: bind-only; consumers: fixed_point.
proof_shape: z_re: bind-only; consumers: z_re_pos.
proof_shape: z_re_pos: bind-only; consumers: one_add_z_ne_zero.
proof_shape: one_add_z_ne_zero: bind-only; consumers: c_coefficient.
proof_shape: c_coefficient: bind-only; consumers: c_ne_zero, fixed_point.
proof_shape: c_ne_zero: bind-only; consumers: u_nonzero, marginal_nonconstant.
proof_shape: fixed_point: bind-only; consumers: result.
proof_shape: u_at_transversal: bind-only; consumers: u_nonzero, marginal_nonconstant.
proof_shape: u_empty: bind-only; consumers: marginal_nonconstant.
proof_shape: u_nonzero: bind-only; consumers: result.
proof_shape: marginal_nonconstant: bind-only; consumers: result.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder

open scoped BigOperators
open Finset
noncomputable section
namespace D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint

def f (m : ℕ) (σ : Finset (Fin (2*m))) : ℂ :=
  ∏ j : Fin m, ((Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)))) - (Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))))

private theorem pair_ne {m : ℕ} (j : Fin m) : ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ≠ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) := by
  intro h
  have := ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)))).injective h
  have := congrArg Prod.snd this
  exact (by decide : (0 : Fin 2) ≠ 1) this

private theorem pair_distinct {m : ℕ} (i j : Fin m) (h : i ≠ j) :
    ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,0)) ≠ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∧ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,0)) ≠ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) ∧ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,1)) ≠ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∧ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,1)) ≠ ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) := by
  repeat' constructor
  all_goals intro he; apply h; exact congrArg Prod.fst (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)))).injective he)

private theorem mem_flip {d : ℕ} (σ : Finset (Fin d)) (k l : Fin d) :
    l ∈ (symmDiff σ {k}) ↔ if l = k then l ∉ σ else l ∈ σ := by
  by_cases h : l = k <;> simp [mem_symmDiff,h]

private theorem flip_flip {d : ℕ} (σ : Finset (Fin d)) (k : Fin d) : (symmDiff ((symmDiff σ {k})) {k}) = σ := by
  exact symmDiff_symmDiff_cancel_right {k} σ

private theorem bit_flip_self {d : ℕ} (σ : Finset (Fin d)) (k : Fin d) :
    (Set.indicator ((((symmDiff σ {k})) : Finset _) : Set _) (fun _ => (1 : ℂ)) k) = 1 - (Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) k) := by
  by_cases h : k ∈ σ <;> simp only [Set.indicator, mem_coe, mem_flip, h] <;> simp

private theorem bit_flip_other {d : ℕ} (σ : Finset (Fin d)) (k l : Fin d) (h : l ≠ k) :
    (Set.indicator ((((symmDiff σ {k})) : Finset _) : Set _) (fun _ => (1 : ℂ)) l) = (Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) l) := by simp only [Set.indicator, mem_coe, mem_flip, h]; simp

private theorem pair_cancel (m : ℕ) (σ : Finset (Fin (2*m))) (j : Fin m) :
    f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)))})) + f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))})) = 0 := by
  let P := ∏ i ∈ (univ : Finset (Fin m)).erase j, ((Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,0))))-(Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (i,1)))))
  have ha : f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)))})) = (1 - (Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0))))-(Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))))*P := by
    rw [f, ← mul_prod_erase _ _ (mem_univ j)]
    rw [bit_flip_self, bit_flip_other _ _ _ (pair_ne j).symm]
    congr 1
    apply prod_congr rfl
    intro i hi
    have hij : i ≠ j := (mem_erase.mp hi).1
    rcases pair_distinct i j hij with ⟨h1,h2,h3,h4⟩
    rw [bit_flip_other _ _ _ h1, bit_flip_other _ _ _ h3]
  have hb : f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))})) = ((Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0))))-(1-(Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1))))))*P := by
    rw [f, ← mul_prod_erase _ _ (mem_univ j)]
    rw [bit_flip_other _ _ _ (pair_ne j), bit_flip_self]
    congr 1
    apply prod_congr rfl
    intro i hi
    have hij : i ≠ j := (mem_erase.mp hi).1
    rcases pair_distinct i j hij with ⟨h1,h2,h3,h4⟩
    rw [bit_flip_other _ _ _ h2, bit_flip_other _ _ _ h4]
  rw [ha,hb]
  ring

private theorem neighbour_sum (m : ℕ) (σ : Finset (Fin (2*m))) :
    ∑ k, f m ((symmDiff σ {k})) = 0 := by
  rw [← Equiv.sum_comp ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  change ∑ j, (f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)))})) + f m ((symmDiff σ {(((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))}))) = 0
  simp only [pair_cancel, sum_const_zero]

private theorem f_card (m : ℕ) (σ : Finset (Fin (2*m))) (hf : f m σ ≠ 0) : σ.card = m := by
  have hpair (j : Fin m) : (if ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∈ σ then 1 else 0 : ℕ) + (if ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) ∈ σ then 1 else 0 : ℕ) = 1 := by
    have hn : (Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0))))-(Set.indicator ((σ : Finset _) : Set _) (fun _ => (1 : ℂ)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)))) ≠ 0 := (prod_ne_zero_iff.mp hf) j (mem_univ j)
    by_cases ha : ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∈ σ <;> by_cases hb : ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) ∈ σ <;> simp_all [Set.indicator]
  calc
    σ.card = ∑ k : Fin (2*m), (if k ∈ σ then 1 else 0 : ℕ) := by simp
    _ = ∑ p : Fin m × Fin 2, (if (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) p ∈ σ then 1 else 0 : ℕ) :=
      (Equiv.sum_comp ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)))) _).symm
    _ = m := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      change (∑ j, ((if ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∈ σ then 1 else 0 : ℕ) + (if ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) ∈ σ then 1 else 0 : ℕ))) = m
      simp only [hpair]
      simp

private theorem f_support (m : ℕ) (σ : Finset (Fin (2*m))) (h : σ.card ≠ m) : f m σ = 0 := by
  by_contra hf
  exact h (f_card m σ hf)

private def transversal (m : ℕ) : Finset (Fin (2*m)) := univ.image (fun j : Fin m => (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0))

private theorem a_mem_transversal {m : ℕ} (j : Fin m) : ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)) ∈ transversal m := by
  exact mem_image.mpr ⟨j, mem_univ j, rfl⟩
private theorem b_not_mem_transversal {m : ℕ} (j : Fin m) : ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,1)) ∉ transversal m := by
  intro h
  obtain ⟨i,hi,he⟩ := mem_image.mp h
  have hh := ((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2)))).injective he
  have := congrArg Prod.snd hh
  exact (by decide : (0 : Fin 2) ≠ 1) this

private theorem f_transversal (m : ℕ) : f m (transversal m) = 1 := by
  simp only [f, Set.indicator, mem_coe, a_mem_transversal, b_not_mem_transversal, if_true, if_false, sub_zero, prod_const_one]

private theorem transversal_card (m : ℕ) : (transversal m).card = m :=
  f_card _ _ (by rw [f_transversal]; exact one_ne_zero)

private theorem flip_card_mem {d : ℕ} (σ : Finset (Fin d)) (k : Fin d) (h : k ∈ σ) :
    ((symmDiff σ {k})).card+1 = σ.card := by
  have he : (symmDiff σ {k}) = σ.erase k := by
    ext l
    by_cases hl : l = k <;> simp [mem_flip,hl,h]
  rw [he,card_erase_of_mem h]
  exact Nat.sub_add_cancel (card_pos.mpr ⟨k,h⟩)

private theorem flip_card_not_mem {d : ℕ} (σ : Finset (Fin d)) (k : Fin d) (h : k ∉ σ) :
    ((symmDiff σ {k})).card = σ.card+1 := by
  have he : (symmDiff σ {k}) = insert k σ := by
    ext l
    by_cases hl : l = k <;> simp [mem_flip,hl,h]
  rw [he,card_insert_of_notMem h]

def u (m : ℕ) (z c : ℂ) (σ : Finset (Fin (2*m))) (k : Fin (2*m)) : ℂ :=
  if σ.card = m then
    if k ∈ σ then c*f m σ else z*c*f m σ
  else if σ.card = m-1 ∧ k ∉ σ then z^(m+1)*c*f m ((symmDiff σ {k}))
  else if σ.card = m+1 ∧ k ∈ σ then z^m*c*f m ((symmDiff σ {k}))
  else 0

private theorem sum_two_values {d : ℕ} (σ : Finset (Fin d)) (C D : ℂ) :
    ∑ k, (if k ∈ σ then C else D) = (σ.card : ℂ)*C + ((d-σ.card : ℕ) : ℂ)*D := by
  rw [sum_ite]
  have h1 : (univ : Finset (Fin d)).filter (fun k => k ∈ σ) = σ := by ext; simp
  have h2 : (univ : Finset (Fin d)).filter (fun k => k ∉ σ) = univ \ σ := by ext; simp
  rw [h1,h2]
  simp [card_sdiff]

private theorem S_eq_f (m : ℕ) (hm : 2 ≤ m) (z c : ℂ) (hc : (m : ℂ)*(1+z)*c = 1)
    (σ : Finset (Fin (2*m))) : (∑ q, u m z c σ q) = f m σ := by
  by_cases h0 : σ.card = m
  · simp only [u,if_pos h0]
    rw [sum_two_values,h0]
    have hnat : 2*m-m = m := by omega
    rw [hnat]
    calc
      (m : ℂ)*(c*f m σ) + (m : ℂ)*(z*c*f m σ) = ((m : ℂ)*(1+z)*c)*f m σ := by ring
      _ = f m σ := by rw [hc,one_mul]
  · have hf0 := f_support m σ h0
    rw [hf0]
    by_cases hlo : σ.card = m-1
    · have hhi : σ.card ≠ m+1 := by omega
      have hs : ∀ k, u m z c σ k = z^(m+1)*c*f m ((symmDiff σ {k})) := by
        intro k
        by_cases hk : k ∈ σ
        · have hcard := flip_card_mem σ k hk
          have hf := f_support m ((symmDiff σ {k})) (by omega)
          simp only [u,if_neg h0]
          simp [hlo,hk,hf]
        · simp only [u,if_neg h0]
          simp [hlo,hk]
      simp only [hs,← mul_sum,neighbour_sum,mul_zero]
    · by_cases hhi : σ.card = m+1
      · have hs : ∀ k, u m z c σ k = z^m*c*f m ((symmDiff σ {k})) := by
          intro k
          by_cases hk : k ∈ σ
          · simp only [u,if_neg h0]
            simp [hhi,hk]
          · have hcard := flip_card_not_mem σ k hk
            have hf := f_support m ((symmDiff σ {k})) (by omega)
            simp only [u,if_neg h0]
            simp [hhi,hk,hf]
        simp only [hs,← mul_sum,neighbour_sum,mul_zero]
      · simp [u,h0,hlo,hhi]

private theorem edge_identity (m : ℕ) (hm : 2 ≤ m) (z c : ℂ)
    (hz : z^(2*m) = -1) (hc : (m : ℂ)*(1+z)*c=1)
    (σ : Finset (Fin (2*m))) (k : Fin (2*m)) :
    z^σ.card*((1/(m : ℂ))*f m σ-u m z c σ k) = u m z c ((symmDiff σ {k})) k := by
  have hcoef : (1/(m : ℂ)) = (1+z)*c := by
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply (mul_left_cancel₀ hm0)
    rw [mul_one_div_cancel hm0]
    simpa only [mul_assoc] using hc.symm
  by_cases hk : k ∈ σ
  · have hkn : k ∉ (symmDiff σ {k}) := by simp [mem_flip,hk]
    have hcard := flip_card_mem σ k hk
    by_cases hmid : σ.card = m
    · have hl : ((symmDiff σ {k})).card = m-1 := by omega
      have hnm : ((symmDiff σ {k})).card ≠ m := by omega
      simp only [u,if_pos hmid,if_pos hk,if_neg hnm]
      simp only [hl,hkn,not_false_eq_true,and_self,if_true,flip_flip]
      rw [hmid,hcoef,pow_succ]
      ring
    · have hf := f_support m σ hmid
      by_cases hhi : σ.card = m+1
      · have ht : ((symmDiff σ {k})).card = m := by omega
        simp only [u,if_neg hmid]
        have hlo : σ.card ≠ m-1 := by omega
        simp [hhi,hk,ht,hkn,hf]
        rw [show m+1 = 1+m by omega,pow_add,pow_one]
        have hpow : z^m*z^m = -1 := by rw [← pow_add,show m+m=2*m by omega,hz]
        calc
          -(z*z^m*(z^m*c*f m ((symmDiff σ {k})))) = -(z^m*z^m)*(z*c*f m ((symmDiff σ {k}))) := by ring
          _ = z*c*f m ((symmDiff σ {k})) := by rw [hpow]; ring
      · have htm : ((symmDiff σ {k})).card ≠ m := by omega
        simp only [u,if_neg hmid,if_neg htm]
        simp [hk,hkn,hhi,hf]
  · have hkin : k ∈ (symmDiff σ {k}) := by simp [mem_flip,hk]
    have hcard := flip_card_not_mem σ k hk
    by_cases hmid : σ.card = m
    · have hh : ((symmDiff σ {k})).card = m+1 := by omega
      have hnm : ((symmDiff σ {k})).card ≠ m := by omega
      have hnl : ((symmDiff σ {k})).card ≠ m-1 := by omega
      simp only [u,if_pos hmid,if_neg hk,if_neg hnm]
      simp only [hh,hkin,not_true_eq_false,and_false,if_false,and_true,if_true,flip_flip]
      rw [hmid,hcoef]
      ring
    · have hf := f_support m σ hmid
      by_cases hlo : σ.card = m-1
      · have ht : ((symmDiff σ {k})).card = m := by omega
        simp only [u,if_neg hmid]
        simp [hlo,hk,ht,hkin,hf]
        have hpow : z^(m-1)*z^(m+1) = -1 := by
          rw [← pow_add,show m-1+(m+1)=2*m by omega,hz]
        calc
          -(z^(m-1)*(z^(m+1)*c*f m ((symmDiff σ {k})))) = -(z^(m-1)*z^(m+1))*(c*f m ((symmDiff σ {k}))) := by ring
          _ = c*f m ((symmDiff σ {k})) := by rw [hpow]; ring
      · have htm : ((symmDiff σ {k})).card ≠ m := by omega
        simp only [u,if_neg hmid,if_neg htm]
        simp [hk,hkin,hlo,hf]

private theorem phase_pow (d n : ℕ) :
    Complex.exp (-((Real.pi : ℂ)*(n : ℂ)/(d : ℂ))*Complex.I) = (PositivePauliClockOrder.scalarPhase 1 (Real.pi / d) 1) ^ n := by
  simp only [PositivePauliClockOrder.scalarPhase, one_mul, mul_one, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem z_power (d : ℕ) (hd : 0 < d) : (PositivePauliClockOrder.scalarPhase 1 (Real.pi / d) 1) ^ d = -1 := by
  rw [← phase_pow]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [mul_div_cancel_right₀ _ hd0]
  rw [neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
  norm_num

private theorem z_re (d : ℕ) : ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / d) 1)).re = Real.cos (Real.pi/d) := by
  simp only [PositivePauliClockOrder.scalarPhase, one_mul, mul_one]
  simp [Complex.exp_re]

private theorem z_re_pos (d : ℕ) (hd : 4 ≤ d) : 0 < ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / d) 1)).re := by
  rw [z_re]
  apply Real.cos_pos_of_mem_Ioo
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < (d : ℝ) := by linarith
  constructor
  · have hp : 0 < Real.pi/(d : ℝ) := div_pos Real.pi_pos hpos
    linarith [Real.pi_pos]
  · apply (div_lt_iff₀ hpos).mpr
    nlinarith [Real.pi_pos]

private theorem one_add_z_ne_zero (d : ℕ) (hd : 4 ≤ d) : 1+(PositivePauliClockOrder.scalarPhase 1 (Real.pi / d) 1) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hp := z_re_pos d hd
  simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
  linarith

def c (m : ℕ) : ℂ := 1/((m : ℂ)*(1+(PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)))

private theorem c_coefficient (m : ℕ) (hm : 2 ≤ m) : (m : ℂ)*(1+(PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1))*c m = 1 := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz0 := one_add_z_ne_zero (2*m) (by omega)
  exact mul_one_div_cancel (mul_ne_zero hm0 hz0)

private theorem c_ne_zero (m : ℕ) (hm : 2 ≤ m) : c m ≠ 0 := by
  have hc := c_coefficient m hm
  intro h
  rw [h,mul_zero] at hc
  exact zero_ne_one hc

def W (d : ℕ) (v : Finset (Fin d) → Fin d → ℂ) : Finset (Fin d) → Fin d → ℂ :=
  fun τ k => Complex.exp (-(Real.pi * (symmDiff τ {k}).card / d) * Complex.I) *
    ((2 / (d : ℂ)) * ∑ j, v (symmDiff τ {k}) j - v (symmDiff τ {k}) k)

def claim : Prop := ∀ d : ℕ, Even d → 4 ≤ d →
  ∃ v : Finset (Fin d) → Fin d → ℂ,
    v ≠ 0 ∧ W d v = v ∧
      ∃ σ σ', (∑ k, ‖v σ k‖ ^ 2) ≠ ∑ k, ‖v σ' k‖ ^ 2

private theorem fixed_point (m : ℕ) (hm : 2 ≤ m) :
    W (2*m) (u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m)) = u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) := by
  funext τ k
  have he := edge_identity m hm ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m)
    (z_power (2*m) (by omega)) (c_coefficient m hm) ((symmDiff τ {k})) k
  rw [flip_flip] at he
  change Complex.exp (-((Real.pi : ℂ)*(((symmDiff τ {k})).card : ℂ)/(2*m : ℕ))*Complex.I) *
    ((2/(2*m : ℕ))*(∑ q, u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) ((symmDiff τ {k})) q) - u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) ((symmDiff τ {k})) k) = _
  rw [phase_pow, S_eq_f m hm _ _ (c_coefficient m hm)]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : (2/(2*m : ℕ) : ℂ) = 1/(m : ℂ) := by
    push_cast
    field_simp
  rw [hc]
  exact he

private theorem u_at_transversal (m : ℕ) (z c : ℂ) (j : Fin m) :
    u m z c (transversal m) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0))) = c := by
  simp only [u, transversal_card, a_mem_transversal, f_transversal, if_true, mul_one]

private theorem u_empty (m : ℕ) (hm : 2 ≤ m) (z c : ℂ) (k : Fin (2*m)) :
    u m z c ∅ k = 0 := by
  have h0 : (0 : ℕ) ≠ m := by omega
  have hlo : (0 : ℕ) ≠ m-1 := by omega
  have hhi : (0 : ℕ) ≠ m+1 := by omega
  simp [u,h0,hlo]

private theorem u_nonzero (m : ℕ) (hm : 2 ≤ m) : u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) ≠ 0 := by
  intro h
  let j : Fin m := ⟨0,by omega⟩
  have hh := congrFun (congrFun h (transversal m)) (((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)))
  rw [u_at_transversal] at hh
  exact c_ne_zero m hm hh

private theorem marginal_nonconstant (m : ℕ) (hm : 2 ≤ m) :
    (∑ k, ‖u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) (transversal m) k‖ ^ 2) ≠
    ∑ k, ‖u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) ∅ k‖ ^ 2 := by
  have hpos : 0 < ∑ k, ‖u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) (transversal m) k‖ ^ 2 := by
    apply sum_pos'
    · intro k hk
      exact sq_nonneg _
    · let j : Fin m := ⟨0,by omega⟩
      refine ⟨((finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))) (j,0)),mem_univ _,?_⟩
      rw [u_at_transversal]
      exact sq_pos_of_pos (norm_pos_iff.mpr (c_ne_zero m hm))
  have hzero : (∑ k, ‖u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m) ∅ k‖ ^ 2) = 0 := by
    simp [u_empty m hm]
  rw [hzero]
  exact ne_of_gt hpos

theorem result : claim := by
  intro d heven hge
  obtain ⟨m,hd⟩ := heven
  have hd' : d = 2*m := by omega
  rw [hd'] at hge ⊢
  have hm : 2 ≤ m := by omega
  exact ⟨u m ((PositivePauliClockOrder.scalarPhase 1 (Real.pi / (2*m : ℕ)) 1)) (c m),u_nonzero m hm,fixed_point m hm,
    transversal m,∅,marginal_nonconstant m hm⟩

end D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
