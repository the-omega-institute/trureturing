/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward.structural_certificate
   digest: Width-six exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229753.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
canonical_successors: proof_shape=content; consumers=transition_counts
transition_counts: proof_shape=content; consumers=HardinA229753.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source43
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
/-! Every admissible boundary has the certified successor multiset. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Certificate
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private theorem class_relabel (e : Equiv.Perm (Fin 4)) (p : Row) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem bond_relabel (E : Finset (Fin 6 × Fin 6))
    (e : Equiv.Perm (Fin 4)) (p r : Row) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem canonical_successors (p : Row) (d : Fin 3) (hp : Valid p d.val)
    (hc : Canonical p) : successors p d.val = classList (cl p d.val) := by
  have h : ∀ (i : Fin 187) (d : Fin 3), Valid (Rows.rows i) d.val →
      Sources.sources (Sources.sourceIndex i d) = (Rows.rows i, d) := by
    decide +kernel
  have hr := Rows.reconstruction p hc
  have hv : Valid (Rows.rows (Rows.rowIndex p)) d.val := by rw [hr]; exact hp
  have hs := h (Rows.rowIndex p) d hv
  rw [hr] at hs
  have hh := Chunks1.Source43.successor_rows (Sources.sourceIndex (Rows.rowIndex p) d)
  simp only [Nat.zero_add] at hh
  rw [hs] at hh
  exact hh

theorem transition_counts (p : Row) (d : ℕ) (hp : Valid p d) (s : Fin 96) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d ∧
      cl r (d - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  by_cases hzero : d = 0 ∧ bondDefects horizontal p p = 0
  · rcases hzero with ⟨rfl, hproper⟩
    exact ZeroTemperature.transition_counts p hproper s
  ·
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
      have hnon : ¬ (d = 0 ∧ bondDefects horizontal p' p' = 0) := by
        rw [he]
        simpa only [bond_relabel] using hzero
      have hcount : ((successors p' d).count s : ℤ) =
          ∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
            cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
            then (1 : ℤ) else 0 := by
        unfold successors
        rw [if_neg hnon]
        exact_mod_cast h
      rw [hlist] at hcount
      have hh : (∑ r : Row, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
          cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
          then (1 : ℤ) else 0) = ((classList (cl p' d)).count s : ℤ) := by
        exact hcount.symm
      exact hh.trans (Counts.Check7.counts _ _)
    rw [he] at hT
    let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
    rw [← E.sum_comp] at hT
    change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d ∧
      cl (e ∘ r) (d - (bondDefects between (e ∘ p) (e ∘ r) +
        bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
        T (cl (e ∘ p) d) s at hT
    simpa only [bond_relabel, class_relabel] using hT

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Certificate
