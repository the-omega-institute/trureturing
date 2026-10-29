/- GID: D5/S3/Arith/Congruence/BalaA363412
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BalaA363412
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala imaginary-product nondivisibility and reflection. -/

/-
admission_basis: open-problem-resolution (#18635; Proved)
Mathematical escape witnesses are named per content declaration below.
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21978.
proof_shape: result: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: none (settling result).
proof_shape: uniform_shift: content; escape_witness: D5.S3.Arith.Congruence.BalaA363412.uniform_shift; consumers: D5.S3.Arith.Congruence.BalaA363412.reflection_congruences.
proof_shape: reflect_zero: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412.reflection_congruences.
proof_shape: positive_one: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412.reflect_one, D5.S3.Arith.Congruence.BalaA363412.negative_one.
proof_shape: reflect_one: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412.reflection_congruences.
proof_shape: negative_zero: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412.reflection_congruences.
proof_shape: negative_one: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363412.reflection_congruences.
proof_shape: reflection_congruences: content; escape_witness: D5.S3.Arith.Congruence.BalaA363412.uniform_shift; consumers: D5.S3.Arith.Congruence.BalaA363412Valuation.at_multiple, D5.S3.Arith.Congruence.BalaA363412Valuation.before_multiple.
The product and sequence definitions retain the source expressions.
-/

import D5.S3.Arith.Congruence.BalaA363411
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace D5.S3.Arith.Congruence.BalaA363412
open D5.S3.Arith.Congruence.BalaA363411

/-- A363412 ("Conjectures: 3 does not divide a(3*n+1) for all n"). -/
def claim : Prop := ∀ n : ℕ, ¬ (3 : ℤ) ∣ b (3 * n + 1)

theorem result : D5.S3.Arith.Congruence.BalaA363412.claim := by
  intro n
  have hp : Function.Periodic (D5.S3.Arith.Congruence.BalaA363411.seq (ZMod 3)) 3 :=
    D5.S3.Arith.Congruence.BalaA363411.seq_period _ _ (by decide +kernel) (by decide +kernel)
  have he : D5.S3.Arith.Congruence.BalaA363411.seq (ZMod 3) (3*n+1) = (1,1) := by
    rw [D5.S3.Arith.Congruence.BalaA363411.seq_mod _ _ hp]
    simp [D5.S3.Arith.Congruence.BalaA363411.seq, Nat.add_mod]
  rw [D5.S3.Arith.Congruence.BalaA363411.seq_cast] at he
  have hb := congrArg Prod.snd he
  intro hd
  have hz : (b (3*n+1) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [hz] at hb
  exact (zero_ne_one : (0:ZMod 3) ≠ 1) hb

private def prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) : ℤ√(-3) := ∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))


private theorem uniform_shift {ι : Type*} (s : Finset ι) (f : ι → ℤ) (c : ℤ) :
    ∃ u v : ℤ,
      (prod s (fun i => f i+c)).re = (prod s f).re + 3*c*u ∧
      (prod s (fun i => f i+c)).im = (prod s f).im + c*s.card + 3*c*v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp [prod]⟩
  | @insert i s hi ih =>
    obtain ⟨u, v, ha, hb⟩ := ih
    obtain ⟨w, hw⟩ := D5.S3.Arith.Congruence.BalaA363411.real_one s (fun i => f i+c)
    change (prod s (fun i => f i+c)).re = 1 + 3*w at hw
    have hl : prod (insert i s) (fun i => f i+c) =
        (⟨1, f i+c⟩ : ℤ√(-3)) * prod s (fun i => f i+c) := by simp [prod, hi]
    have hr : prod (insert i s) f = (⟨1, f i⟩ : ℤ√(-3)) * prod s f := by simp [prod, hi]
    refine ⟨u - f i * (s.card + 3*v) - (prod s (fun i => f i+c)).im,
      v + f i*u + w, ?_, ?_⟩
    · rw [hl, hr]
      simp only [Zsqrtd.re_mul, one_mul]
      rw [ha, hb]
      ring
    · rw [hl, hr]
      simp only [Zsqrtd.im_mul, one_mul, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      linear_combination hb + f i * ha + c*hw

private theorem reflect_zero (m : ℕ) :
    prod (Finset.range (m+1)) (fun k => -(k:ℤ)+(m:ℤ)) = P m := by
  have h := Finset.prod_range_reflect (fun k => (⟨1, k⟩ : ℤ√(-3))) (m+1)
  unfold prod P
  rw [← h]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' : k ≤ m := Finset.mem_range_succ_iff.mp hk
  congr 1
  push_cast [Nat.cast_sub hk']
  ring

private theorem positive_one (m : ℕ) :
    P m = prod (Finset.range m) (fun k => (k:ℤ)+1) := by
  rw [P, Finset.prod_range_succ']
  change (prod (Finset.range m) (fun k => (k:ℤ)+1)) * 1 = _
  exact mul_one _

private theorem reflect_one (m : ℕ) :
    prod (Finset.range m) (fun k => -((k:ℤ)+1)+((m:ℤ)+1)) = P m := by
  have h := Finset.prod_range_reflect (fun k => (⟨1, k+1⟩ : ℤ√(-3))) m
  rw [positive_one]
  unfold prod
  rw [← h]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  congr 1
  change -((k:ℤ)+1)+((m:ℤ)+1) = ((m-1-k:ℕ):ℤ)+1
  omega

private theorem negative_zero (m : ℕ) :
    prod (Finset.range (m+1)) (fun k => -(k:ℤ)) = star (P m) := by
  simp [prod, P, star_prod, Zsqrtd.star_mk]

private theorem negative_one (m : ℕ) :
    prod (Finset.range m) (fun k => -((k:ℤ)+1)) = star (P m) := by
  rw [positive_one]
  simp [prod, star_prod, Zsqrtd.star_mk]

theorem reflection_congruences (m : ℕ) :
    (3*(m:ℤ) ∣ 2*b m - (m:ℤ)*(m+1)) ∧
    (3*((m:ℤ)+1) ∣ 2*b m - (m:ℤ)*(m+1)) := by
  obtain ⟨u, v, ha, hb⟩ := uniform_shift (Finset.range (m+1)) (fun k => -(k:ℤ)) (m:ℤ)
  obtain ⟨u', v', ha', hb'⟩ := uniform_shift (Finset.range m) (fun k => -((k:ℤ)+1)) ((m:ℤ)+1)
  rw [reflect_zero, negative_zero] at hb
  rw [reflect_one, negative_one] at hb'
  simp only [Zsqrtd.im_star, Finset.card_range, Nat.cast_add, Nat.cast_one] at hb hb'
  constructor
  · refine ⟨v, ?_⟩
    dsimp [b] at *
    linear_combination hb
  · refine ⟨v', ?_⟩
    dsimp [b] at *
    linear_combination hb'

end D5.S3.Arith.Congruence.BalaA363412
