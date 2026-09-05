/- GID: D5/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Erdos-Moser solutions satisfy Moser's local obstruction at every prime dividing m-1. -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/- Library-search audit trail (2026-09-05):
   * Searches on current origin/dev for the theorem and helper names, and for the complete
     squarefree/local-divisibility conclusion shape, found no D5 declaration.
   * Pinned Mathlib has no Erdos-Moser theorem. `FiniteField.sum_pow_units` supplies only the
     finite-field power-sum dichotomy; the block decomposition and both transports below are new.
   * A full-statement `exact?` trial found no declaration that closes the target directly.
-/

open scoped BigOperators

namespace D5.S3.PrimeForms.Obstructions.ErdosMoserLocalObstruction

private lemma sum_pow_blocks_zmod (p q k : Nat) :
    (∑ i ∈ Finset.range (q * p), (i : ZMod p) ^ k) =
      (q : ZMod p) * ∑ a ∈ Finset.range p, (a : ZMod p) ^ k := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp [Nat.cast_add, Nat.cast_mul, Nat.cast_succ, add_mul]

private lemma sum_pow_range_zmod {p k : Nat} (hp : p.Prime) (hk : 0 < k) :
    (∑ a ∈ Finset.range p, (a : ZMod p) ^ k) =
      if p - 1 ∣ k then -1 else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hRange :
      (∑ a ∈ Finset.range p, (a : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := by
    exact Finset.sum_bij'
      (fun a _ => (a : ZMod p))
      (fun x _ => x.val)
      (fun _ _ => Finset.mem_univ _)
      (fun x _ => Finset.mem_range.2 x.val_lt)
      (fun a ha => by simp [ZMod.val_cast_of_lt (Finset.mem_range.mp ha)])
      (fun x _ => ZMod.natCast_zmod_val x)
      (fun _ _ => rfl)
  let unitsEmbedding : (ZMod p)ˣ ↪ ZMod p :=
    ⟨fun x => x, Units.val_injective⟩
  have hImage : Finset.univ.map unitsEmbedding = Finset.univ \ {(0 : ZMod p)} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, unitsEmbedding] using! isUnit_iff_ne_zero
  calc
    (∑ a ∈ Finset.range p, (a : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := hRange
    _ = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ k := by
      rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ,
        Finset.sum_singleton, zero_pow hk.ne', add_zero]
    _ = ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k := by
      simp [unitsEmbedding, ← hImage, Finset.univ.sum_map unitsEmbedding]
    _ = if p - 1 ∣ k then -1 else 0 := by
      simpa [ZMod.card] using FiniteField.sum_pow_units (ZMod p) k

/-- Every Erdos-Moser solution satisfies Moser's local prime obstruction at `m - 1`, and
therefore `m - 1` is squarefree. -/
theorem erdos_moser_local_obstruction {m k : Nat}
    (hm : 1 < m) (hk : 0 < k)
    (hmoser : ∑ i ∈ Finset.range m, i ^ k = m ^ k) :
    (∀ p : Nat, p.Prime → p ∣ m - 1 →
      (p - 1 ∣ k ∧ p ∣ (m - 1) / p + 1 ∧ ¬p ^ 2 ∣ m - 1)) ∧
      Squarefree (m - 1) := by
  have hlocal : ∀ p : Nat, p.Prime → p ∣ m - 1 →
      (p - 1 ∣ k ∧ p ∣ (m - 1) / p + 1 ∧ ¬p ^ 2 ∣ m - 1) := by
    intro p hp hpDvd
    let q := (m - 1) / p
    have hfactor : q * p = m - 1 := Nat.div_mul_cancel hpDvd
    have hmDecomp : m = q * p + 1 := by omega
    letI : Fact p.Prime := ⟨hp⟩
    have hmoserZMod :
        (∑ i ∈ Finset.range m, (i : ZMod p) ^ k) = (m : ZMod p) ^ k := by
      simpa only [Nat.cast_sum, Nat.cast_pow] using
        congrArg (fun n : Nat => (n : ZMod p)) hmoser
    have hblock :
        (q : ZMod p) * (∑ a ∈ Finset.range p, (a : ZMod p) ^ k) = 1 := by
      rw [hmDecomp, Finset.sum_range_succ, sum_pow_blocks_zmod] at hmoserZMod
      simpa [hk.ne'] using hmoserZMod
    have hsum := sum_pow_range_zmod hp hk
    have hdiv : p - 1 ∣ k := by
      by_contra hnot
      rw [hsum, if_neg hnot] at hblock
      exact (zero_ne_one : (0 : ZMod p) ≠ 1) (by simpa using hblock)
    have hqZMod : (q : ZMod p) = -1 := by
      rw [hsum, if_pos hdiv] at hblock
      calc
        (q : ZMod p) = -((q : ZMod p) * (-1)) := by ring
        _ = -1 := congrArg Neg.neg hblock
    have hqAdd : p ∣ q + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp [hqZMod]
    have hnotSq : ¬p ^ 2 ∣ m - 1 := by
      intro hsq
      have hpq : p ∣ q := by
        apply (Nat.dvd_div_iff_mul_dvd hpDvd).2
        simpa [pow_two, mul_comm] using hsq
      exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpq).2 hqAdd)
    exact ⟨hdiv, hqAdd, hnotSq⟩
  refine ⟨hlocal, Nat.squarefree_iff_prime_squarefree.2 ?_⟩
  intro p hp hsq
  exact (hlocal p hp (dvd_trans (dvd_mul_right p p) hsq)).2.2
    (by simpa [pow_two] using hsq)

end D5.S3.PrimeForms.Obstructions.ErdosMoserLocalObstruction
