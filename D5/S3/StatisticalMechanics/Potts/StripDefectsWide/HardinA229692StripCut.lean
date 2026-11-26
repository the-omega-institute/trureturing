/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
zero_lower: proof_shape=bind-only; consumers=active_cut, leading_counts
active_cut: proof_shape=bind-only; consumers=leading_counts, HardinA229692StripCertificate.structural_certificate
active_table: proof_shape=bind-only; consumers=leading_counts
old_counts: proof_shape=bind-only; consumers=HardinA229692Strip.tail_counts
leading_counts: proof_shape=bind-only; consumers=HardinA229692Strip.finite_certificate
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584Strip

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCut
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229584StripData (Row Boundary horizontal antidiagonal boundary cross)
open HardinA229692StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem zero_lower : ∀ p : Boundary, 32 ≤ (cl p 0).val := by
  decide +kernel

theorem active_cut (r : Row) (c : ℕ) (d : Fin 3) (j : Fin 32) (hd : 0 < d.val) :
    ((c ≤ d.val ∧ cl (boundary r) (d.val - c) = j.castAdd 36) ↔
      c ≤ d.val - 1 ∧ HardinA229584StripData.cl (boundary r) (d.val - 1 - c) = j) := by
  by_cases h : 0 < d.val - c
  · have hc : c ≤ d.val - 1 := by omega
    have he : d.val - c - 1 = d.val - 1 - c := by omega
    simp only [cl, h, ↓reduceIte, Fin.castAdd_inj, he, hc, true_and]
    simp only [show c ≤ d.val by omega, true_and]
    exact (Fin.castAdd_injective 32 36).eq_iff
  · have hc : ¬ c ≤ d.val - 1 := by omega
    -- A zero budget cannot enter the leading block.
    have hn : cl (boundary r) (d.val - c) ≠ j.castAdd 36 := by
      intro he
      have hv := congrArg Fin.val he
      have dz : d.val - c = 0 := by omega
      rw [dz] at hv
      have hl := zero_lower (boundary r)
      simp only [Fin.val_castAdd] at hv
      have := j.isLt
      omega
    simp only [hn, and_false, hc, false_and]

private theorem active_table : ∀ (p : Boundary) (d : Fin 3) (j : Fin 32),
    0 < d.val → HardinA229584StripData.T (HardinA229584StripData.cl p (d.val - 1)) j = T (cl p d.val) (j.castAdd 36) := by
  intro p d j
  fin_cases j <;> decide +revert +kernel

/-- The non-exhausted block is the frozen one-defect transfer. -/
theorem leading_counts (p : Boundary) (d : Fin 3) (hp : Valid p d.val) (j : Fin 32) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = j.castAdd 36
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 36) := by
  by_cases hd : 0 < d.val
  · have hc : ∀ r c, ((c ≤ d.val ∧ cl (boundary r) (d.val - c) = j.castAdd 36) ↔
        c ≤ d.val - 1 ∧ HardinA229584StripData.cl (boundary r) (d.val - 1 - c) = j) := by
      intro r c
      exact active_cut r c d j hd
    simp_rw [hc]
    exact (HardinA229584Strip.finite_certificate.2.2.1 p
      ⟨d.val - 1, by omega⟩ (by
        change d.val - 1 ≤ 1 ∧ _ ≤ 1 - (d.val - 1)
        change d.val ≤ 2 ∧ _ ≤ 2 - d.val at hp
        constructor <;> omega) j).trans (active_table p d j hd)
  · have he : d = 0 := Fin.ext (by simp; omega)
    subst d
    have empty : ∀ (r : Row) (c : ℕ), ¬ (c ≤ 0 ∧ cl (boundary r) (0 - c) = j.castAdd 36) := by
      intro r c h
      have hv := congrArg Fin.val h.2
      simp only [Nat.zero_sub, Fin.val_castAdd] at hv
      have hl := zero_lower (boundary r)
      omega
    have zero : ∀ (p : Boundary) (j : Fin 32), T (cl p 0) (j.castAdd 36) = 0 := by
      decide +kernel
    have zsum : (∑ r : Row,
        if cross p r + bondDefects horizontal r r ≤ 0 ∧
          cl (boundary r) (0 - (cross p r + bondDefects horizontal r r)) = j.castAdd 36
        then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact if_neg (empty r _)
    exact zsum.trans (zero p j).symm

theorem old_counts (p : Boundary) (d : Fin 2)
    (hp : HardinA229584StripData.Valid p d.val) (j : Fin 36) :
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = j.natAdd 32
      then (1 : ℤ) else 0) = T (cl p d.val) (j.natAdd 32) := by
  have rowImage : ∀ (r : Boundary) (b : Fin 2), HardinA229584StripData.Valid r b.val →
      cl r b.val = oldClassImage (HardinA229584StripData.cl r b.val) := by
    decide +kernel
  have table : ∀ (i : Fin 32) (s : Fin 68),
      T (oldClassImage i) s =
        ∑ k : Fin 32, if oldClassImage k = s then HardinA229584StripData.T i k else 0 := by
    decide +kernel
  rw [rowImage p d hp, table]
  calc
    _ = ∑ r : Row, ∑ k : Fin 32,
        if oldClassImage k = j.natAdd 32 then
          (if cross p r + bondDefects horizontal r r ≤ d.val ∧
            HardinA229584StripData.cl (boundary r)
              (d.val - (cross p r + bondDefects horizontal r r)) = k
            then (1 : ℤ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hc : cross p r + bondDefects horizontal r r ≤ d.val
      · have hv := HardinA229584Strip.finite_certificate.2.1 p d hp r hc
        have hi := rowImage (boundary r)
          ⟨d.val - (cross p r + bondDefects horizontal r r), by omega⟩ hv
        simp only [hc, true_and, hi]
        symm
        rw [Finset.sum_eq_single (HardinA229584StripData.cl (boundary r)
          (d.val - (cross p r + bondDefects horizontal r r)))]
        · simp only [ite_true]
        · intro k _ hk
          simp only [Ne.symm hk, ite_false, ite_self]
        · simp
      · simp only [hc, false_and, ite_false, ite_self, Finset.sum_const_zero]
    _ = ∑ k : Fin 32, ∑ r : Row,
        if oldClassImage k = j.natAdd 32 then
          (if cross p r + bondDefects horizontal r r ≤ d.val ∧
            HardinA229584StripData.cl (boundary r)
              (d.val - (cross p r + bondDefects horizontal r r)) = k
            then (1 : ℤ) else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : oldClassImage k = j.natAdd 32
      · simp only [hk, ite_true]
        exact HardinA229584Strip.finite_certificate.2.2.1 p d hp k
      · simp only [hk, ite_false, Finset.sum_const_zero]


end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripCut
