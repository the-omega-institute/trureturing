/- GID: D5/S1/Recurrence/Residue/TebniA364822
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/TebniA364822
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral hyperbolic EGF coefficients have residue two at every odd prime. -/

/-
admission_basis: open-problem-resolution (#18643; Proved)
escape_witness: none (the settling result supplies admission).
proof_shape: cosh: bind-only; consumers: eCoeff_cosh, functional_eq, a; escape_witness: none.
Direct frozen dependencies for cosh: none.
proof_shape: sinh: bind-only; consumers: eCoeff_sinh, functional_eq, a; escape_witness: none.
Direct frozen dependencies for sinh: none.
proof_shape: a: bind-only; consumers: claim, a_recurrence, a_integral, num_cast, num_recurrence, TebniA364822PowerOfTwo.claim; escape_witness: none.
Direct frozen dependencies for a: none.
proof_shape: claim: bind-only; consumers: result; escape_witness: none.
Direct frozen dependencies for claim: none.
proof_shape: functional_eq: bind-only; consumers: a_recurrence; escape_witness: none.
Direct frozen dependencies for functional_eq:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: eCoeff_cosh: bind-only; consumers: a_recurrence, a_integral; escape_witness: none.
Direct frozen dependencies for eCoeff_cosh:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: eCoeff_sinh: bind-only; consumers: functional_eq, a_recurrence, a_integral; escape_witness: none.
Direct frozen dependencies for eCoeff_sinh:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: a_recurrence: bind-only; consumers: num_zero, num_recurrence; escape_witness: none.
Direct frozen dependencies for a_recurrence:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: a_integral: bind-only; consumers: num_cast; escape_witness: none.
Direct frozen dependencies for a_integral:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: num_cast: bind-only; consumers: num_zero, num_recurrence, result, TebniA364822PowerOfTwo.result; escape_witness: none.
Direct frozen dependencies for num_cast:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: num_zero: bind-only; consumers: result; escape_witness: none.
Direct frozen dependencies for num_zero:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: num_recurrence: bind-only; consumers: result, TebniA364822PowerOfTwo.result; escape_witness: none.
Direct frozen dependencies for num_recurrence:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
proof_shape: result: bind-only; consumers: external open-problem settlement; escape_witness: none.
Direct frozen dependencies for result:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22441.
The definitions cosh, sinh and a are the coefficient expressions in #18643.
The proof applies IntegralEGFComposition.integral_subst and eCoeff_mul.
The existing eCoeff owner is used without a new factorial-normalization alias.
The rational numerator is used directly, without a new name for Rat.num.
-/

import D5.S1.Recurrence.Residue.IntegralEGFComposition
import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

namespace D5.S1.Recurrence.Residue.TebniA364822

open PowerSeries

/-- `cosh x = ∑ x^(2k)/(2k)!`. -/
noncomputable def cosh : ℚ⟦X⟧ := mk fun n => if Even n then ((n.factorial : ℚ))⁻¹ else 0

/-- `sinh x = ∑ x^(2k+1)/(2k+1)!`. -/
noncomputable def sinh : ℚ⟦X⟧ := mk fun n => if Even n then 0 else ((n.factorial : ℚ))⁻¹

/-- A364822: the e.g.f. `cosh(x)/(1 - 2 sinh(x))`. -/
noncomputable def a (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n (cosh * (1 - 2 * sinh)⁻¹)

/-- A364822 ("Conjectures: For p prime (p > 2), a(p) == 2 (mod p)."). -/
def claim : Prop := ∀ p : ℕ, p.Prime → 2 < p → ∃ z : ℤ, (z : ℚ) = a p ∧ z ≡ 2 [ZMOD p]

end D5.S1.Recurrence.Residue.TebniA364822

namespace D5.S1.Recurrence.Residue.TebniA364822
open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition

private theorem eCoeff_cosh (n : ℕ) : eCoeff cosh n = if Even n then 1 else 0 := by
  simpa only [D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode, cosh, ite_div, one_div, zero_div] using
    (D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode (fun j => if Even j then (1 : ℚ) else 0) n)

private theorem eCoeff_sinh (n : ℕ) : eCoeff sinh n = if Even n then 0 else 1 := by
  simpa only [D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode, sinh, ite_div, one_div, zero_div] using
    (D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode (fun j => if Even j then (0 : ℚ) else 1) n)

private theorem functional_eq : cosh * (1 - 2 * sinh)⁻¹ = cosh + 2 * ((cosh * (1 - 2 * sinh)⁻¹) * sinh) := by
  have hs : constantCoeff sinh = 0 := by
    simpa using eCoeff_sinh 0
  have hc : constantCoeff (1 - 2 * sinh) ≠ 0 := by simp [hs]
  have hh : (cosh * (1 - 2 * sinh)⁻¹) * (1 - 2 * sinh) = cosh := by
    exact (PowerSeries.eq_mul_inv_iff_mul_eq hc).mp rfl
  linear_combination hh

private theorem a_recurrence (n : ℕ) : a n = (if Even n then 1 else 0) +
    2 * ∑ k ∈ range n, (n.choose k : ℚ) * a k * (if Even (n-k) then 0 else 1) := by
  change eCoeff (cosh * (1 - 2 * sinh)⁻¹) n = _
  conv_lhs => rw [functional_eq]
  simp only [eCoeff, map_add, coeff_ofNat_mul, mul_add, mul_left_comm _ (2 : ℚ)]
  change eCoeff cosh n + 2 * eCoeff ((cosh * (1 - 2 * sinh)⁻¹) * sinh) n = _
  rw [eCoeff_cosh, eCoeff_mul, sum_range_succ]
  simp only [eCoeff_sinh]
  change _ + 2 * ((∑ k ∈ range n, (n.choose k : ℚ) * a k *
    (if Even (n-k) then 0 else 1)) + (n.choose n : ℚ) * a n *
    (if Even (n-n) then 0 else 1)) = _
  simp


private theorem a_integral (n : ℕ) : ∃ z : ℤ, (z : ℚ) = a n := by
  classical
  let g : PowerSeries ℚ := 2 * sinh
  have h0 : constantCoeff g = 0 := by
    have hs : constantCoeff sinh = 0 := by simpa using eCoeff_sinh 0
    simp [g, hs]
  have hg : Integral g := by
    intro j
    refine ⟨2 * (if Even j then 0 else 1 : ℤ), ?_⟩
    have he : eCoeff g j = 2 * eCoeff sinh j := by
      simp only [g, eCoeff, coeff_ofNat_mul]
      ring
    rw [he, eCoeff_sinh]
    split_ifs <;> norm_num
  have hf : Integral (mk (1 : ℕ → ℚ)) := by
    intro j
    refine ⟨(j.factorial : ℤ), ?_⟩
    simp [eCoeff]
  have hG : PowerSeries.HasSubst g := .of_constantCoeff_zero h0
  have heq : (mk (1 : ℕ → ℚ)).subst g = (1 - g)⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [h0])).mpr
    rw [← PowerSeries.coe_substAlgHom hG]
    have ht := congrArg (PowerSeries.substAlgHom hG)
      (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)
    simpa only [map_mul, map_sub, map_one, PowerSeries.substAlgHom_X, Pi.one_apply] using ht
  have hi := integral_subst hf hg h0
  rw [heq] at hi
  choose z hz using hi
  refine ⟨∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) *
      (if Even k then 1 else 0) * z (n-k), ?_⟩
  change (_ : ℚ) = eCoeff (cosh * (1 - g)⁻¹) n
  rw [eCoeff_mul]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eCoeff_cosh, hz]


theorem num_cast (n : ℕ) : ((a n).num : ℚ) = a n := by
  obtain ⟨z, hz⟩ := a_integral n
  simp [← hz]

private theorem num_zero : (a 0).num = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [num_cast, a_recurrence]
  simp

theorem num_recurrence (n : ℕ) : (a n).num = (if Even n then 1 else 0) +
    2 * ∑ k ∈ range n, (n.choose k : ℤ) * (a k).num * (if Even (n-k) then 0 else 1) := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_ofNat, Int.cast_ite,
    Int.cast_one, Int.cast_zero, Int.cast_natCast, num_cast]
  exact a_recurrence n

open Finset

theorem result : claim := by
  intro p hp hp2
  refine ⟨(a p).num, num_cast p, ?_⟩
  have ho : ¬ Even p := by
    rw [hp.even_iff]
    omega
  apply (ZMod.intCast_eq_intCast_iff ((a p).num) 2 p).mp
  rw [num_recurrence]
  simp only [ho, ite_false, zero_add, Int.cast_mul, Int.cast_ofNat, Int.cast_sum,
    Int.cast_natCast, Int.cast_ite, Int.cast_zero, Int.cast_one]
  have hs : (∑ k ∈ range p, (p.choose k : ZMod p) * ((a k).num : ZMod p) *
      (if Even (p-k) then 0 else 1)) = 1 := by
    rw [sum_eq_single 0]
    · simp [num_zero, ho]
    · intro k hk hk0
      have hd : p ∣ p.choose k := hp.dvd_choose_self hk0 (mem_range.mp hk)
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd]
      simp
    · intro h
      exact False.elim (h (mem_range.mpr hp.pos))
  rw [hs]
  simp

end D5.S1.Recurrence.Residue.TebniA364822
