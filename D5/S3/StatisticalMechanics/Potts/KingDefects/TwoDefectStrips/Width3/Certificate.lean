/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-3 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229750.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
canonical_successors: proof_shape=bind-only; consumers=transition_counts
class_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229750.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Classes8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
/-! Every admissible boundary has the certified successor multiset. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Certificate
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private theorem class_relabel (e : Equiv.Perm (Fin 4)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem bond_relabel (E : Finset (Fin 3 × Fin 3))
    (e : Equiv.Perm (Fin 4)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem canonical_successors (p : Row) (d : Fin 3) (hp : Valid p d.val)
    (hc : Canonical p) : successors p d.val = classList (cl p d.val) := by
  by_cases h0 : cl p d.val = 0
  · rw [h0]; exact Classes0.class_successors p d hp hc h0
  by_cases h1 : cl p d.val = 1
  · rw [h1]; exact Classes1.class_successors p d hp hc h1
  by_cases h2 : cl p d.val = 2
  · rw [h2]; exact Classes2.class_successors p d hp hc h2
  by_cases h3 : cl p d.val = 3
  · rw [h3]; exact Classes3.class_successors p d hp hc h3
  by_cases h4 : cl p d.val = 4
  · rw [h4]; exact Classes4.class_successors p d hp hc h4
  by_cases h5 : cl p d.val = 5
  · rw [h5]; exact Classes5.class_successors p d hp hc h5
  by_cases h6 : cl p d.val = 6
  · rw [h6]; exact Classes6.class_successors p d hp hc h6
  by_cases h7 : cl p d.val = 7
  · rw [h7]; exact Classes7.class_successors p d hp hc h7
  have hh : cl p d.val = 8 := by apply Fin.ext; omega
  rw [hh]; exact Classes8.class_successors p d hp hc hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem class_counts : ∀ c s : Fin 9, ((classList c).count s : ℤ) = T c s := by
  intro c
  fin_cases c <;> decide +kernel

theorem transition_counts (p : Row) (d : ℕ) (hp : Valid p d) (s : Fin 9) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d ∧
      cl r (d - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
  have hv : Valid p' d := by
    rw [he]
    simpa only [Valid, bond_relabel] using hp
  have hd : d < 3 := by change d ≤ 2 ∧ _ at hp; omega
  have hlist := canonical_successors p' ⟨d, hd⟩ hv hnormal
  have hT :
      (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d) s := by
    have h := TableBridge.count_successors
      (fun r : Row => bondDefects between p' r + bondDefects horizontal r r ≤ d)
      (fun r => cl r (d - (bondDefects between p' r + bondDefects horizontal r r))) s
    change (successors p' d).count s = _ at h
    rw [hlist] at h
    have hh : (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = ((classList (cl p' d)).count s : ℤ) := by
      exact_mod_cast h.symm
    exact hh.trans (class_counts _ _)
  rw [he] at hT
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 3 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d ∧
    cl (e ∘ r) (d - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d) s at hT
  simpa only [bond_relabel, class_relabel] using hT

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Certificate
