/- GID: D5/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/TripleDeletionCountComparison
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The no-111 deletion kernel has dimension four times a shifted Tribonacci sum. -/

import D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
import D5.S0.Tower.Tribonacci.Representation
import D5.S0.Tower.Tribonacci.Values

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Representation
open D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
open scoped Classical

local notation "dim₃" => fun k => Module.finrank ℂ
  (SupportedKernel (NoTriple k))

private abbrev shiftedWordCount (k : ℕ) : ℕ :=
  4 * (tribonacci (k + 3) + tribonacci (k + 2))

private theorem shiftedWordCount_recurrence (k : ℕ) :
    shiftedWordCount (k + 3) = shiftedWordCount (k + 2) + shiftedWordCount (k + 1) + shiftedWordCount k := by
  have a : tribonacci (k + 6) = tribonacci (k + 5) + tribonacci (k + 4) +
      tribonacci (k + 3) := tribonacci_add_three (k + 3)
  have b : tribonacci (k + 5) = tribonacci (k + 4) + tribonacci (k + 3) +
      tribonacci (k + 2) := tribonacci_add_three (k + 2)
  simp only [shiftedWordCount]
  change 4 * (tribonacci (k + 6) + tribonacci (k + 5)) =
    4 * (tribonacci (k + 5) + tribonacci (k + 4)) +
    4 * (tribonacci (k + 4) + tribonacci (k + 3)) +
    4 * (tribonacci (k + 3) + tribonacci (k + 2))
  omega

private theorem dimension_exact (k : ℕ) : dim₃ (k + 1) = shiftedWordCount k := by
  suffices h : ∀ n, dim₃ (n + 1) = shiftedWordCount n ∧ dim₃ (n + 2) = shiftedWordCount (n + 1) ∧
      dim₃ (n + 3) = shiftedWordCount (n + 2) from (h k).1
  intro n
  induction n with
  | zero =>
      have t := noTriple_finrank 0
      exact ⟨t.1, t.2.1, t.2.2.1⟩
  | succ n ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      change dim₃ (n + 4) = shiftedWordCount (n + 3)
      dsimp only at ih ⊢
      rw [(noTriple_finrank n).2.2.2, ih.2.2, ih.2.1, ih.1, shiftedWordCount_recurrence]

private def TripleFree {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∀ (i : ℕ) (hi : i + 2 < n),
    ¬ (w ⟨i, by omega⟩ ∧ w ⟨i + 1, by omega⟩ ∧ w ⟨i + 2, hi⟩)

private theorem admissible_of_tripleFree {n : ℕ} (w : Fin n → Bool)
    (h : TripleFree w) : TribonacciAdmissible n w := by
  induction n with
  | zero => trivial
  | succ n ih =>
      match n with
      | 0 => trivial
      | 1 => trivial
      | n + 2 =>
          apply (admissible_add_three_iff n w).2
          refine ⟨h 0 (by omega), ih (Fin.tail w) ?_⟩
          intro i hi
          exact h (i + 1) (by omega)

private theorem noTriple_iff_admissible {k : ℕ} (w : Fin (k + 2) → Bool) :
    NoTriple k w ↔ TribonacciAdmissible (k + 2) w := by
  constructor
  · intro h
    apply admissible_of_tripleFree
    intro i hi hall
    obtain ⟨j, hj, hz⟩ := h _ ⟨⟨i, by omega⟩, rfl⟩
    change j.val = i ∨ j.val = i + 1 ∨ j.val = i + 2 at hj
    rcases hj with hj | hj | hj
    · have he : j = ⟨i, by omega⟩ := Fin.ext hj
      exact Bool.false_ne_true (hz.symm.trans (he.symm ▸ hall.1))
    · have he : j = ⟨i + 1, by omega⟩ := Fin.ext hj
      exact Bool.false_ne_true (hz.symm.trans (he.symm ▸ hall.2.1))
    · have he : j = ⟨i + 2, by omega⟩ := Fin.ext hj
      exact Bool.false_ne_true (hz.symm.trans (he.symm ▸ hall.2.2))
  · intro h
    rintro edge ⟨i, rfl⟩
    let a : Fin (k + 2) := ⟨i.val, by omega⟩
    let b : Fin (k + 2) := ⟨i.val + 1, by omega⟩
    let c : Fin (k + 2) := ⟨i.val + 2, by omega⟩
    have hf : ¬ (w a ∧ w b ∧ w c) := admissible_no_three_at _ i.val w h (by omega)
    by_cases ha : w a = false
    · exact ⟨a, Or.inl rfl, ha⟩
    by_cases hb : w b = false
    · exact ⟨b, Or.inr (Or.inl rfl), hb⟩
    by_cases hc : w c = false
    · exact ⟨c, Or.inr (Or.inr rfl), hc⟩
    exact (hf ⟨Bool.eq_true_of_not_eq_false ha, Bool.eq_true_of_not_eq_false hb,
      Bool.eq_true_of_not_eq_false hc⟩).elim

private theorem legal_count (k : ℕ) :
    Nat.card {w // NoTriple k w} = tribonacci (k + 4) := by
  let e : {w // NoTriple k w} ≃ TribonacciName (k + 2) :=
    Equiv.subtypeEquivRight noTriple_iff_admissible
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, tribonacci_name_card]

private theorem tribonacci_pos_succ (k : ℕ) : 0 < tribonacci (k + 1) := by
  cases k with
  | zero => decide
  | succ k =>
      rw [← tribonacci_name_card k]
      exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => false,
        D5.S0.Tower.Tribonacci.Values.admissible_all_false k⟩⟩

/-- The no-111 chain has a Tribonacci word count and a strictly smaller than twice as large
common single-site deletion kernel. -/
theorem triple_kernel_exact (k : ℕ) :
    dim₃ (k + 1) = 4 * (tribonacci (k + 3) + tribonacci (k + 2)) ∧
    Nat.card {w // NoTriple (k + 1) w} = tribonacci (k + 5) ∧
    dim₃ (k + 1) < 2 * Nat.card {w // NoTriple (k + 1) w} := by
  refine ⟨dimension_exact k, legal_count (k + 1), ?_⟩
  rw [dimension_exact, legal_count]
  have h₄ : tribonacci (k + 4) = tribonacci (k + 3) + tribonacci (k + 2) +
      tribonacci (k + 1) := tribonacci_add_three (k + 1)
  have h₅ : tribonacci (k + 5) = tribonacci (k + 4) + tribonacci (k + 3) +
      tribonacci (k + 2) := tribonacci_add_three (k + 2)
  have hpos := tribonacci_pos_succ k
  simp only [shiftedWordCount]
  change 4 * (tribonacci (k + 3) + tribonacci (k + 2)) < 2 * tribonacci (k + 5)
  omega

end D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison
