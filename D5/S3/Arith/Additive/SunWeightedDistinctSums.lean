/- GID: D5/S3/Arith/Additive/SunWeightedDistinctSums
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/SunWeightedDistinctSums
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Additive/SunWeightedDistinctSums.claim; result=D5/S3/Arith/Additive/SunWeightedDistinctSums.result; claim=D5/S3/Arith/Additive/SunWeightedDistinctSums.claim
   digest: Sun's weighted distinct-sum bound is refuted by the rational set {0, 1, 2} at n = 2. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#16084; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Per-declaration proof shapes and live consumers (definitions have no proof shape):
private pF_rat: bind-only; consumers: char_hyp, result; escape_witness: none.
private a_card: bind-only; consumers: size_hyp, result; escape_witness: none.
private size_hyp: bind-only; consumers: result; escape_witness: none.
private char_hyp: bind-only; consumers: result; escape_witness: none.
private sun_bound: bind-only; consumers: result; escape_witness: none.
private mem_weighted_two: bind-only; consumers: sums_eq; escape_witness: none.
private sums_eq: bind-only; consumers: sums_card; escape_witness: none.
private sums_card: bind-only; consumers: result; escape_witness: none.
The four public definitions reproduce the source conventions literally; the proofs use only their
compiled expressions and pinned Mathlib declarations.
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fin.Tuple.Embedding

open scoped BigOperators

namespace D5.S3.Arith.Additive.SunWeightedDistinctSums

noncomputable section

def pF (F : Type) [Field F] : ℕ∞ :=
  if ringChar F = 0 then ⊤ else (ringChar F : ℕ∞)

def weightedDistinctSums {F : Type} [Field F] [DecidableEq F]
    (A : Finset F) (n : ℕ) : Finset F :=
  (Finset.univ : Finset (Fin n ↪ A)).image
    (fun a => ∑ k : Fin n, ((k : ℕ) + 1 : F) * (a k : F))

def sunBound (m n : ℕ) : ℕ :=
  (m - n) * (n * (n + 1) / 2) + n * (n ^ 2 - 1) / 6 + 1

def claim : Prop :=
  ∀ (F : Type) [Field F] [DecidableEq F] (n : ℕ),
    1 ≤ n → (n : ℕ∞) + 1 < pF F →
    ∀ A : Finset F, n + (if n = 3 then 1 else 0) ≤ A.card →
      min (pF F) (sunBound A.card n : ℕ∞) ≤
        ((weightedDistinctSums A n).card : ℕ∞)

private theorem pF_rat : pF ℚ = ⊤ := by
  simp [pF, ringChar.eq_zero]

private theorem a_card : ({0, 1, 2} : Finset ℚ).card = 3 := by
  exact Finset.card_triple_eq_three_iff.mpr ⟨by norm_num, by norm_num, by norm_num⟩

private theorem size_hyp : 2 + (if 2 = 3 then 1 else 0) ≤
    ({0, 1, 2} : Finset ℚ).card := by
  rw [a_card]
  decide

private theorem char_hyp : (2 : ℕ∞) + 1 < pF ℚ := by
  rw [pF_rat]
  change (3 : ℕ∞) < ⊤
  exact ENat.natCast_lt_top 3

private theorem sun_bound : sunBound 3 2 = 5 := by
  decide

private theorem mem_weighted_two {F : Type} [Field F] [DecidableEq F]
    (A : Finset F) (z : F) :
    z ∈ weightedDistinctSums A 2 ↔
      ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ x + 2 * y = z := by
  simp only [weightedDistinctSums, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a 0 : F), (a 0).property, (a 1 : F), (a 1).property, ?_, ?_⟩
    · intro h
      have h01 : (0 : Fin 2) = 1 := a.injective (Subtype.ext h)
      exact (by decide : (0 : Fin 2) ≠ 1) h01
    · norm_num [Fin.sum_univ_two]
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    let a : Fin 2 ↪ A := Function.Embedding.embFinTwo
      (a := (⟨x, hx⟩ : A)) (b := (⟨y, hy⟩ : A))
      (by intro h; exact hxy (congrArg Subtype.val h))
    refine ⟨a, ?_⟩
    norm_num [Fin.sum_univ_two, a, Function.Embedding.embFinTwo_apply_zero,
      Function.Embedding.embFinTwo_apply_one]

private theorem sums_eq : weightedDistinctSums ({0, 1, 2} : Finset ℚ) 2 =
    {1, 2, 4, 5} := by
  ext z
  simp only [mem_weighted_two, Finset.mem_insert, Finset.mem_singleton]
  norm_num [or_and_left, exists_or]
  constructor
  · intro h
    rcases h.1 with (h | h) | (h | h) | h | h <;> subst z <;> norm_num
  · intro h
    rcases h with h | h | h | h <;> subst z <;> norm_num

private theorem sums_card : (weightedDistinctSums ({0, 1, 2} : Finset ℚ) 2).card = 4 := by
  rw [sums_eq]
  exact Finset.card_eq_four.mpr
    ⟨1, 2, 4, 5, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, rfl⟩

theorem result : ¬ claim := by
  intro h
  have hbad := h ℚ 2 (by decide) char_hyp ({0, 1, 2} : Finset ℚ) size_hyp
  rw [pF_rat, a_card, sun_bound, sums_card] at hbad
  norm_num at hbad
  exact (by decide : ¬ ((5 : ℕ∞) ≤ 4)) hbad


end
end D5.S3.Arith.Additive.SunWeightedDistinctSums
