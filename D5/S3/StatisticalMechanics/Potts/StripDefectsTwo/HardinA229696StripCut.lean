/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripCut
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229696Strip.result)
active_numeric: proof_shape=bind-only; consumers=active_cut
tail_numeric: proof_shape=bind-only; consumers=tail_cut
active_cut: proof_shape=bind-only; consumers=leading_counts
tail_cut: proof_shape=bind-only; consumers=tail_counts
active_table: proof_shape=bind-only; consumers=leading_counts
tail_table: proof_shape=bind-only; consumers=tail_counts
leading_counts: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
tail_counts: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
open HardinA229588Strip (Row horizontal between)
open HardinA229696StripData
open DefectTransfer (bondDefects)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem active_numeric : ∀ (r : Row) (c d : Fin 3) (j : Fin 10),
    0 < d.val →
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = j.castAdd 5) ↔
      c.val ≤ d.val - 1 ∧ HardinA229588Strip.cl r (d.val - 1 - c.val) = j) := by
  decide +kernel

private theorem tail_numeric : ∀ (r : Row) (c : Fin 3) (d : Fin 2) (j : Fin 5),
    ((c.val ≤ d.val ∧ cl r (d.val - c.val) = j.natAdd 10) ↔
      c.val ≤ d.val ∧ HardinA229588Strip.cl r (d.val - c.val) = j.natAdd 5) := by
  decide +kernel

private theorem active_cut (r : Row) (c : ℕ) (d : Fin 3) (j : Fin 10)
    (hd : 0 < d.val) :
    ((c ≤ d.val ∧ cl r (d.val - c) = j.castAdd 5) ↔
      c ≤ d.val - 1 ∧ HardinA229588Strip.cl r (d.val - 1 - c) = j) := by
  by_cases hc : c < 3
  · exact active_numeric r ⟨c, hc⟩ d j hd
  · have h0 : ¬ c ≤ d.val := by omega
    have h1 : ¬ c ≤ d.val - 1 := by omega
    simp only [h0, h1, false_and]

private theorem tail_cut (r : Row) (c : ℕ) (d : Fin 2) (j : Fin 5) :
    ((c ≤ d.val ∧ cl r (d.val - c) = j.natAdd 10) ↔
      c ≤ d.val ∧ HardinA229588Strip.cl r (d.val - c) = j.natAdd 5) := by
  by_cases hc : c < 3
  · exact tail_numeric r ⟨c, hc⟩ d j
  · have h0 : ¬ c ≤ d.val := by omega
    simp only [h0, false_and]

private theorem active_table : ∀ (p : Row) (d : Fin 3) (j : Fin 10),
    0 < d.val → HardinA229588Strip.T (HardinA229588Strip.cl p (d.val - 1)) j = T (cl p d.val) (j.castAdd 5) := by
  decide +kernel

private theorem tail_table : ∀ (p : Row) (d : Fin 2) (j : Fin 5),
    HardinA229588Strip.T (HardinA229588Strip.cl p d.val) (j.natAdd 5) = T (cl p d.val) (j.natAdd 10) := by
  decide +kernel

/-- The leading two budget sectors reuse the frozen one-defect certificate. -/
theorem leading_counts (p : Row) (d : Fin 3) (j : Fin 10) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 5
      then (1 : ℤ) else 0) = T (cl p d.val) (j.castAdd 5) := by
  by_cases hd : 0 < d.val
  · simp_rw [active_cut _ _ d j hd]
    exact (HardinA229588Strip.finite_certificate.2.2.1 p
      ⟨d.val - 1, by omega⟩ (by change d.val - 1 ≤ 1; omega) j).trans
        (active_table p d j hd)
  · have he : d = 0 := Fin.ext (by simp; omega)
    subst d
    have empty : ∀ (r : Row) (c : ℕ), ¬ (c ≤ 0 ∧ cl r (0 - c) = j.castAdd 5) := by
      intro r c h
      have hcl := congrArg Fin.val h.2
      simp only [Nat.zero_sub, cl, Nat.lt_irrefl, ↓reduceIte, Fin.val_natAdd,
        Fin.val_castAdd] at hcl
      omega
    have zero : ∀ (p : Row) (j : Fin 10), T (cl p 0) (j.castAdd 5) = 0 := by
      decide +kernel
    have zsum : (∑ r : Row,
        if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
          cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 5
        then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact if_neg (empty r _)
    exact zsum.trans (zero p j).symm

/-- Exhausted and one-unit budgets reuse the frozen final sector. -/
theorem tail_counts (p : Row) (d : Fin 2) (j : Fin 5) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.natAdd 10
      then (1 : ℤ) else 0) = T (cl p d.val) (j.natAdd 10) := by
  simp_rw [tail_cut _ _ d j]
  exact (HardinA229588Strip.finite_certificate.2.2.1 p d (by change d.val ≤ 1; omega)
    (j.natAdd 5)).trans (tail_table p d j)

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
