/- GID: D5/S3/Arith/Congruence/BalaA363411TypeOne
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BalaA363411TypeOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Congruence/BalaA363411TypeOne.result; premises=D5/S3/Arith/Congruence/BalaA363411TypeOne.listed_data,D5/S3/Arith/Congruence/BalaA363411TypeOne.unlisted_data
   digest: Bala type-one primes through 101. -/

/-
admission_basis: open-problem-resolution (#18634; Proved)
Mathematical escape witnesses are named per content declaration below.
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21978.
proof_shape: nonzero_of_block: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411TypeOne.nonzero_of_block; consumers: D5.S3.Arith.Congruence.BalaA363411TypeOne.result.
proof_shape: three_nonzero: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_cast; consumers: D5.S3.Arith.Congruence.BalaA363411TypeOne.result.
proof_shape: listed_data: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411TypeOne.result.
proof_shape: unlisted_data: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411TypeOne.result.
proof_shape: result: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411TypeOne.nonzero_of_block; consumers: none (settling result).
The product and sequence definitions retain the source expressions.
-/

import D5.S3.Arith.Congruence.BalaA363411
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace D5.S3.Arith.Congruence.BalaA363411TypeOne
open D5.S3.Arith.Congruence.BalaA363411

/-- A363411 ("We conjecture that the set of type 1 primes begins {3, 11, 17, 23, 29, 41, 47, 53, 59, 83,
89, 101, ...}"), where a type 1 prime is a prime dividing no term: up to 101, the type 1 primes are
exactly the listed ones. -/
def claim : Prop :=
  ∀ p : ℕ, p ≤ 101 →
    ((p.Prime ∧ ∀ n : ℕ, ¬ (p : ℤ) ∣ a n) ↔
      p ∈ ({3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101} : Finset ℕ))

private def listed : Finset ℕ := {3, 11, 17, 23, 29, 41, 47, 53, 59, 83, 89, 101}

private theorem nonzero_of_block (p : ℕ) [Fact p.Prime]
    (h2 : (2:ZMod p) ≠ 0) (hblock : seq (ZMod p) p = (2,0))
    (hsmall : ∀ r : Fin p, (seq (ZMod p) r).1 ≠ 0) (n : ℕ) :
    (seq (ZMod p) n).1 ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < p
    · exact hsmall ⟨n, hn⟩
    · have hp : 0 < p := Nat.Prime.pos Fact.out
      have he : n = (n-p)+p := by omega
      rw [he, seq_shift _ _ _ (by simp) hblock]
      exact mul_ne_zero h2 (ih (n-p) (by omega))

private theorem three_nonzero (n : ℕ) : (seq (ZMod 3) n).1 = 1 := by
  rw [seq_cast]
  obtain ⟨u, hu⟩ := real_one (Finset.range (n+1)) (fun k => (k:ℤ))
  change a n = 1 + 3*u at hu
  simp [hu, show (3 : ZMod 3) = 0 from ZMod.natCast_self 3]

private theorem listed_data : ∀ p ∈ listed, p.Prime ∧
    (p = 3 ∨ ((2:ZMod p) ≠ 0 ∧ seq (ZMod p) p = (2,0) ∧
      ∀ r : Fin p, (seq (ZMod p) r).1 ≠ 0)) := by
  decide +kernel

private theorem unlisted_data : ∀ p : Fin 102,
    p.val.Prime → p.val ∉ listed → ∃ r : Fin 102, (seq (ZMod p.val) r).1 = 0 := by
  decide +kernel

theorem result : D5.S3.Arith.Congruence.BalaA363411TypeOne.claim := by
  intro p hp
  change (p.Prime ∧ ∀ n : ℕ, ¬ (p:ℤ) ∣ a n) ↔ p ∈ listed
  constructor
  · rintro ⟨hprime, hn⟩
    by_contra hnot
    obtain ⟨r, hr⟩ := unlisted_data ⟨p, by omega⟩ hprime hnot
    rw [seq_cast] at hr
    exact hn r ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr)
  · intro hlist
    obtain ⟨hprime, hcase⟩ := listed_data p hlist
    refine ⟨hprime, ?_⟩
    have : Fact p.Prime := ⟨hprime⟩
    intro n hd
    have hz : (seq (ZMod p) n).1 = 0 := by
      rw [seq_cast]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    rcases hcase with rfl | ⟨h2, hb, hs⟩
    · rw [three_nonzero] at hz
      exact one_ne_zero hz
    · exact nonzero_of_block p h2 hb hs n hz

end D5.S3.Arith.Congruence.BalaA363411TypeOne
