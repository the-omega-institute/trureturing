/- GID: D5/S3/Observer/SourceJetCyclicTraces
   generality: G
   mirror-B: D5/B/S3/Observer/SourceJetCyclicTraces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The square-free source jet is the normalized sum of all ordered trace words. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Repository searches for square-free source coefficients, permutation sums of trace words,
     cyclic trace jets, and log-determinant coefficients found no exact theorem or owner.
   * `Matrix.trace_mul_cycle` is the pinned Mathlib trace-cyclicity identity. The reindexing below
     uses `Equiv.ofBijective` and `Fintype.sum_equiv`.
   * No determinant logarithm is analytically evaluated here: the source coefficient is modeled
     algebraically by the words surviving the square-zero source rule, exactly as in the proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.SourceJetCyclicTraces

/-- The ordered matrix trace attached to a length-`k` source word. -/
def orderedTraceWord {k n : ℕ} (B : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (word : Fin k → Fin k) : ℂ :=
  Matrix.trace (List.ofFn (fun position => B (word position))).prod

/-- The square-free source condition: every source label occurs at exactly one word position. -/
def wordUsesEverySourceOnce {k : ℕ} (word : Fin k → Fin k) : Prop :=
  ∀ source, ∃! position, word position = source

/-- The square-free coefficient selected from the `k`th trace power. -/
noncomputable def squareFreeTraceCoefficient {k n : ℕ}
    (B : Fin k → Matrix (Fin n) (Fin n) ℂ) : ℂ := by
  classical
  exact ∑ word : {word : Fin k → Fin k // wordUsesEverySourceOnce word},
    orderedTraceWord B word.1

/-- The coefficient selected from the `k`th trace power by square-zero sources, including the
`1/k` factor from the finite formal expansion of `-log det (I-X)`. -/
noncomputable def sourceJetCoefficient {k n : ℕ}
    (B : Fin k → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (k : ℂ)⁻¹ * squareFreeTraceCoefficient B

private theorem word_uses_every_source_once_iff_bijective {k : ℕ} (word : Fin k → Fin k) :
    wordUsesEverySourceOnce word ↔ Function.Bijective word := by
  constructor
  · intro everySource
    constructor
    · intro first second sameImage
      obtain ⟨position, _, uniquePosition⟩ := everySource (word first)
      have hfirst : first = position := uniquePosition first rfl
      have hsecond : second = position := uniquePosition second sameImage.symm
      exact hfirst.trans hsecond.symm
    · intro source
      exact (everySource source).exists
  · rintro ⟨injective, surjective⟩ source
    obtain ⟨position, hposition⟩ := surjective source
    exact ⟨position, hposition, fun other hother =>
      injective (hother.trans hposition.symm)⟩

/-- Square-free words are canonically the permutations of the source labels. -/
private noncomputable def permutationEquivSquareFreeWord (k : ℕ) :
    Equiv.Perm (Fin k) ≃ {word : Fin k → Fin k // wordUsesEverySourceOnce word} where
  toFun permutation :=
    ⟨permutation, (word_uses_every_source_once_iff_bijective permutation).2
      permutation.bijective⟩
  invFun word := Equiv.ofBijective word.1
    ((word_uses_every_source_once_iff_bijective word.1).1 word.2)
  left_inv permutation := Equiv.ext fun _ => rfl
  right_inv word := by
    apply Subtype.ext
    rfl

private theorem square_free_word_sum_eq_permutation_sum {k n : ℕ}
    (B : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    squareFreeTraceCoefficient B =
      ∑ permutation : Equiv.Perm (Fin k), orderedTraceWord B permutation := by
  classical
  unfold squareFreeTraceCoefficient
  calc
    (∑ word : {word : Fin k → Fin k // wordUsesEverySourceOnce word},
        orderedTraceWord B word.1) =
        ∑ permutation : Equiv.Perm (Fin k), orderedTraceWord B permutation := by
      symm
      exact Fintype.sum_equiv (permutationEquivSquareFreeWord k)
        (fun permutation => orderedTraceWord B permutation)
        (fun word => orderedTraceWord B word.1) (fun _ => rfl)

/-- For a nonempty source set, its square-free `-log det` jet coefficient is exactly `1/k`
times the sum of the traces of all ordered products. The other clauses record the square-free
word/permutation identification and the trace cyclicity used to pass to cyclic word classes. -/
theorem source_jet_is_closed_cyclic_traces {k n : ℕ} (hk : 0 < k)
    (B : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    sourceJetCoefficient B =
        (1 / (k : ℂ)) *
          ∑ permutation : Equiv.Perm (Fin k), orderedTraceWord B permutation ∧
      (k : ℂ) ≠ 0 ∧
      (∀ word : Fin k → Fin k,
        wordUsesEverySourceOnce word ↔ Function.Bijective word) ∧
      (∀ A B C : Matrix (Fin n) (Fin n) ℂ,
        Matrix.trace (A * B * C) = Matrix.trace (C * A * B)) := by
  refine ⟨?_, ?_, fun word => word_uses_every_source_once_iff_bijective word, ?_⟩
  · rw [sourceJetCoefficient, square_free_word_sum_eq_permutation_sum]
    congr 1
    rw [one_div]
  · exact_mod_cast hk.ne'
  · exact Matrix.trace_mul_cycle

/-- The normalization is genuinely defined only for a nonempty source family. -/
theorem source_jet_denominator_ne_zero {k : ℕ} (hk : 0 < k) : (k : ℂ) ≠ 0 := by
  exact_mod_cast hk.ne'

#print axioms source_jet_is_closed_cyclic_traces
#print axioms source_jet_denominator_ne_zero

end D5.S3.Observer.SourceJetCyclicTraces
