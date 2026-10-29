/- GID: D5/S3/Arith/Congruence/BalaA363412Valuation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BalaA363412Valuation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala paired three-adic valuations. -/

/-
admission_basis: open-problem-resolution (#18636; Proved)
Mathematical escape witnesses are named per content declaration below.
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21978.
proof_shape: double_factor: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412Valuation.at_multiple, D5.S3.Arith.Congruence.BalaA363412Valuation.before_multiple.
proof_shape: at_multiple: content; escape_witness: D5.S3.Arith.Congruence.BalaA363412.uniform_shift; consumers: D5.S3.Arith.Congruence.BalaA363412Valuation.result.
proof_shape: before_multiple: content; escape_witness: D5.S3.Arith.Congruence.BalaA363412.uniform_shift; consumers: D5.S3.Arith.Congruence.BalaA363412Valuation.result.
proof_shape: result: content; escape_witness: D5.S3.Arith.Congruence.BalaA363412.uniform_shift; consumers: none (settling result).
The product and sequence definitions retain the source expressions.
-/

import D5.S3.Arith.Congruence.BalaA363411
import D5.S3.Arith.Congruence.BalaA363412

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace D5.S3.Arith.Congruence.BalaA363412Valuation
open D5.S3.Arith.Congruence.BalaA363411
open D5.S3.Arith.Congruence.BalaA363412

private theorem double_factor {z x y : ℤ} (he : 2*z = x*y) (hx : x ≠ 0)
    (hy : ¬ (3:ℤ) ∣ y) : padicValInt 3 z = padicValInt 3 x := by
  have hyn : y ≠ 0 := by intro h; apply hy; simp [h]
  have hz : z ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact mul_ne_zero hx hyn he.symm
  have h := congrArg (padicValInt 3) he
  rw [padicValInt.mul (two_ne_zero : (2:ℤ) ≠ 0) hz,
    padicValInt.mul hx hyn, padicValInt.eq_zero_of_not_dvd (by decide : ¬ (3:ℤ) ∣ 2),
    padicValInt.eq_zero_of_not_dvd hy] at h
  simpa using h

private theorem at_multiple (n : ℕ) (hn : 1 ≤ n) :
    padicValInt 3 (b (3*n)) = padicValInt 3 (3*(n:ℤ)) := by
  obtain ⟨v, hv⟩ := (reflection_congruences (3*n)).1
  have he : 2*b (3*n) = (3*(n:ℤ)) * (3*(n:ℤ)+1+3*v) := by
    push_cast at hv
    linear_combination hv
  apply double_factor he
  · omega
  · omega

private theorem before_multiple (n : ℕ) (hn : 1 ≤ n) :
    padicValInt 3 (b (3*n-1)) = padicValInt 3 (3*(n:ℤ)) := by
  obtain ⟨v, hv⟩ := (reflection_congruences (3*n-1)).2
  have hc : ((3*n-1:ℕ):ℤ) = 3*(n:ℤ)-1 := by omega
  have he : 2*b (3*n-1) = (3*(n:ℤ)) * (3*(n:ℤ)-1+3*v) := by
    rw [hc] at hv
    linear_combination hv
  apply double_factor he
  · omega
  · omega

/-- A363412 ("the 3-adic valuation v_3(a(3*n)) = v_3(a(3*n-1)) for all n"), for `n ≥ 1`. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n → padicValInt 3 (b (3 * n)) = padicValInt 3 (b (3 * n - 1))

theorem result : D5.S3.Arith.Congruence.BalaA363412Valuation.claim := by
  intro n hn
  exact (D5.S3.Arith.Congruence.BalaA363412Valuation.at_multiple n hn).trans (D5.S3.Arith.Congruence.BalaA363412Valuation.before_multiple n hn).symm

end D5.S3.Arith.Congruence.BalaA363412Valuation
