/- GID: D5/S3/Combinatorics/Geometry/PathBlockGamma/SourceNumerator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/PathBlockGamma/SourceNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Trunc]
   utility: none
   digest: Literal path-block counts recover their finite-difference numerator. -/

import D5.S3.Combinatorics.Geometry.PathBlockGamma.SourceBijection
import D5.S3.Combinatorics.Posets.PPartitions.Series
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.PathBlockGamma

open D5.S3.Combinatorics.Posets.PPartitions
noncomputable section

/-- The series of cardinalities of the literal dilated source, for every dilation. -/
def sourceCountSeries (a m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun q => (Nat.card (SourcePoint a m q) : ℤ)

/-- The numerator is recovered from literal counts by finite differences. -/
def sourceNumerator (a m : ℕ) : Polynomial ℤ :=
  PowerSeries.trunc (a * m + 1)
    (sourceCountSeries a m * (1 - PowerSeries.X) ^ (a * m + 1))

/-- All literal counts determine a polynomial numerator, including the zero dilation.
The proof identifies that independently recovered polynomial with the complete
linear-extension descent enumerator. -/
theorem source_numerator_count_identity (a m : ℕ) (ha : 0 < a) (hm : 1 < m) :
    sourceNumerator a m = WPolynomial (naturalLabel : Vertex a m → ℕ) ∧
    sourceCountSeries a m = (sourceNumerator a m : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (a * m + 1)).val := by
  have count_eq (q : ℕ) :
      Nat.card (SourcePoint a m q) =
        Fintype.card (PPartition (naturalLabel : Vertex a m → ℕ) (q + 1)) := by
    let toPartition : PositiveAntitone a m q ≃
        PPartition (naturalLabel : Vertex a m → ℕ) (q + 1) := by
      classical
      exact {
        toFun := fun s => ⟨fun v => ⟨s.1 v - 1, by have h := s.2.1 v; omega⟩, by
          constructor
          · intro x y hxy
            exact Fin.mk_le_mk.mpr (Nat.sub_le_sub_right (s.2.2 hxy) 1)
          · intro x y hxy hlabel
            exact False.elim (Nat.lt_asymm
              ((literal_poset_card_label_order a m ha).2.2.2 hxy) hlabel)⟩
        invFun := fun p => ⟨fun v => (p.1 v).val + 1, by
          constructor
          · intro v
            change 1 ≤ (p.1 v).val + 1 ∧ (p.1 v).val + 1 ≤ q + 1
            have hv := (p.1 v).isLt
            omega
          · intro x y hxy
            exact Nat.add_le_add_right (p.2.1 hxy) 1⟩
        left_inv := by
          intro s
          apply Subtype.ext
          funext v
          change (s.1 v - 1) + 1 = s.1 v
          have h := (s.2.1 v).1
          omega
        right_inv := by
          intro p
          apply Subtype.ext
          funext v
          apply Fin.ext
          change (p.1 v).val + 1 - 1 = (p.1 v).val
          omega }
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr ((sourcePositiveEquiv ha hm).trans toPartition)
  have hlabel := (literal_poset_card_label_order a m ha).2.2.1
  have hseries : sourceCountSeries a m =
      (WPolynomial (naturalLabel : Vertex a m → ℕ) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (a * m + 1)).val := by
    have hp := pPartition_series (naturalLabel : Vertex a m → ℕ) hlabel
    rw [(literal_poset_card_label_order a m ha).1] at hp
    calc
      sourceCountSeries a m =
          PowerSeries.mk (fun q =>
            (Fintype.card (PPartition (naturalLabel : Vertex a m → ℕ) (q + 1)) : ℤ)) := by
              ext q
              simp [sourceCountSeries, count_eq q]
      _ = _ := hp
  have hdegree : (WPolynomial (naturalLabel : Vertex a m → ℕ)).natDegree < a * m + 1 := by
    rw [WPolynomial]
    have hb : (∑ e : EnumeratingExtension (Vertex a m),
        (Polynomial.X : Polynomial ℤ) ^ descentCard naturalLabel e).natDegree ≤ a * m := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro x hx
      simp only [Polynomial.natDegree_X_pow]
      exact le_trans (by simpa [descentCard, (literal_poset_card_label_order a m ha).1]
        using (descentFinset (naturalLabel : Vertex a m → ℕ) x).card_le_univ)
        (Nat.sub_le _ _)
    exact lt_of_le_of_lt hb (Nat.lt_succ_self _)
  have hrecover : sourceNumerator a m =
      WPolynomial (naturalLabel : Vertex a m → ℕ) := by
    unfold sourceNumerator
    rw [hseries, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    rw [Units.val_inv, mul_one]
    exact PowerSeries.trunc_coe_eq_self hdegree
  exact ⟨hrecover, by rw [hrecover]; exact hseries⟩

end
end D5.S3.Combinatorics.Geometry.PathBlockGamma
