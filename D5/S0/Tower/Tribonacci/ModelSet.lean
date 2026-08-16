/- GID: D5/S0/Tower/Tribonacci/ModelSet
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/ModelSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decoded Tribonacci names have a bounded Pisot internal window. -/

import D5.S0.Tower.Tribonacci.Binet
import D5.S0.Tower.Tribonacci.Representation

namespace D5.S0.Tower.Tribonacci.ModelSet

/- Library-search audit trail (2026-08-17):
   * Pinned mathlib provides `Delone.DeloneSet`, but searches for Meyer sets and
     cut-and-project schemes found no corresponding definitions.
   * Loogle found 39 declarations containing `Delone`, and zero declarations
     containing `Meyer` or `cut-and-project`.
   * The implementation therefore uses mathlib's `Bornology.IsBounded` and
     geometric-series API without introducing a weaker local model-set label. -/

/-- Evaluate the digit polynomial of a fixed-length admissible name at a complex root. -/
def conjugateCoordinate {Q : Nat} (z : Complex)
    (name : D5.S0.Tower.Tribonacci.Names.TribonacciName Q) : Complex :=
  ∑ i : Fin Q, if name.1 i then z ^ i.1 else 0

/-- Pair the decoded integer label with conjugate evaluation on a fixed name layer. -/
def conjugateEmbedding {Q : Nat} (z : Complex)
    (name : D5.S0.Tower.Tribonacci.Names.TribonacciName Q) : Nat × Complex :=
  (D5.S0.Tower.Tribonacci.Representation.decode name, conjugateCoordinate z name)

/-- The decoded label makes the paired map injective on each fixed layer. -/
theorem conjugate_embedding_injective (Q : Nat) (z : Complex) :
    Function.Injective
      (conjugateEmbedding z :
        D5.S0.Tower.Tribonacci.Names.TribonacciName Q → Nat × Complex) := by
  intro left right heq
  apply D5.S0.Tower.Tribonacci.Representation.decode_injective Q
  exact congrArg Prod.fst heq

/-- A contracting evaluation is bounded by the infinite geometric-series window. -/
theorem conjugate_coordinate_norm_le {Q : Nat} (z : Complex)
    (name : D5.S0.Tower.Tribonacci.Names.TribonacciName Q) (hz : ‖z‖ < 1) :
    ‖conjugateCoordinate z name‖ ≤ (1 - ‖z‖)⁻¹ := by
  have hsum :
      ‖conjugateCoordinate z name‖ ≤ ∑ i ∈ Finset.range Q, ‖z‖ ^ i := by
    rw [conjugateCoordinate]
    calc
      ‖∑ i : Fin Q, if name.1 i then z ^ i.1 else 0‖ ≤
          ∑ i : Fin Q, ‖if name.1 i then z ^ i.1 else 0‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin Q, ‖z‖ ^ i.1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> simp
      _ = ∑ i ∈ Finset.range Q, ‖z‖ ^ i := by
        rw [Fin.sum_univ_eq_sum_range]
  calc
    ‖conjugateCoordinate z name‖ ≤ ∑ i ∈ Finset.range Q, ‖z‖ ^ i := hsum
    _ ≤ ∑' i : Nat, ‖z‖ ^ i :=
      (summable_geometric_of_lt_one (norm_nonneg z) hz).sum_le_tsum
        (Finset.range Q) (fun i hi ↦ pow_nonneg (norm_nonneg z) i)
    _ = (1 - ‖z‖)⁻¹ := tsum_geometric_of_lt_one (norm_nonneg z) hz

/-- All internal coordinates obtained from finite admissible names, over every length. -/
def tribonacciInternalWindow (z : Complex) : Set Complex :=
  {w | ∃ Q, ∃ name : D5.S0.Tower.Tribonacci.Names.TribonacciName Q,
    w = conjugateCoordinate z name}

/-- A non-Perron Tribonacci root gives a uniformly bounded internal window.

This is exactly the bounded-window core of the cut-and-project argument. It does
not construct a lattice or a cut-and-project scheme, and does not prove that the
physical set is Delone, Meyer, uniformly discrete, or relatively dense. -/
theorem tribonacci_internal_window_is_bounded {z : Complex}
    (hz : z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠
      (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex)) :
    Bornology.IsBounded (tribonacciInternalWindow z) := by
  have hz_contract : ‖z‖ < 1 :=
    D5.S0.Tower.Tribonacci.Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  rw [isBounded_iff_forall_norm_le]
  refine ⟨(1 - ‖z‖)⁻¹, ?_⟩
  intro w hw
  obtain ⟨Q, name, rfl⟩ := hw
  exact conjugate_coordinate_norm_le z name hz_contract

end D5.S0.Tower.Tribonacci.ModelSet
