/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229751.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward.structural_certificate
   digest: Width-4 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229751.result)
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
canonical_successors: proof_shape=content; consumers=transition_counts
class_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=content; consumers=HardinA229751.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes10
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes11
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes13
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes15
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes16
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes17
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes18
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes9
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.ZeroTemperature
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
/-! Every admissible boundary has the certified successor multiset. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Certificate
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip (Boundary proper)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

private theorem class_relabel (e : Equiv.Perm (Fin 4)) (p : Boundary) (d : ℕ) :
    cl (e ∘ p) d = cl p d := by
  simp only [cl, Function.comp_apply, e.injective.eq_iff]

private theorem bond_relabel (E : Finset (Fin 4 × Fin 4))
    (e : Equiv.Perm (Fin 4)) (p r : Boundary) :
    bondDefects E (e ∘ p) (e ∘ r) = bondDefects E p r := by
  simp only [bondDefects, Function.comp_apply, e.injective.eq_iff]

private theorem canonical_successors (p : Boundary) (d : Fin 3) (hp : Valid p d.val)
    (hc : Canonical p) (hd0 : d.val ≠ 0 ∨ ¬ (proper p ∨ cl p 0 = 14)) : successors p d.val = classList (cl p d.val) := by
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
  by_cases h8 : cl p d.val = 8
  · rw [h8]; exact Classes8.class_successors p d hp hc h8
  by_cases h9 : cl p d.val = 9
  · rw [h9]; exact Classes9.class_successors p d hp hc h9
  by_cases h10 : cl p d.val = 10
  · rw [h10]; exact Classes10.class_successors p d hp hc h10
  by_cases h11 : cl p d.val = 11
  · rw [h11]; exact Classes11.class_successors p d hp hc h11
  by_cases h13 : cl p d.val = 13
  · rw [h13]; exact Classes13.class_successors p d hp hc h13
  by_cases h15 : cl p d.val = 15
  · rw [h15]; exact Classes15.class_successors p d hp hc h15
  by_cases h16 : cl p d.val = 16
  · rw [h16]; exact Classes16.class_successors p d hp hc h16
  by_cases h17 : cl p d.val = 17
  · rw [h17]; exact Classes17.class_successors p d hp hc h17
  have hz : cl p d.val ≠ 12 ∧ cl p d.val ≠ 14 := by
    have hh : ∀ p (d : Fin 3), (d.val ≠ 0 ∨ ¬ (proper p ∨ cl p 0 = 14)) →
        cl p d.val ≠ 12 ∧ cl p d.val ≠ 14 := by decide +kernel
    exact hh p d hd0
  have hh : cl p d.val = 18 := by apply Fin.ext; omega
  rw [hh]; exact Classes18.class_successors p d hp hc hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The finite matrix comparison is reduced by the kernel.
private theorem class_counts : ∀ c s : Fin 19, c ≠ 12 → c ≠ 14 → ((classList c).count s : ℤ) = T c s := by
  intro c
  fin_cases c <;> decide +kernel

theorem transition_counts (p : Boundary) (d : ℕ) (hp : Valid p d) (s : Fin 19) :
    (∑ r : Boundary, if bondDefects between p r + bondDefects horizontal r r ≤ d ∧
      cl r (d - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p d) s := by
  by_cases hz : d = 0 ∧ (proper p ∨ cl p 0 = 14)
  · rcases hz with ⟨rfl, hp0⟩
    exact ZeroTemperature.transition_counts p hp0 s
  have hd0 : d ≠ 0 ∨ ¬ (proper p ∨ cl p 0 = 14) := by tauto
  obtain ⟨p', ⟨hnormal, e, he⟩, _⟩ := canonical_exists_unique p
  have hv : Valid p' d := by
    rw [he]
    simpa only [Valid, bond_relabel] using hp
  have hd : d < 3 := by change d ≤ 2 ∧ _ at hp; omega
  have hd0' : d ≠ 0 ∨ ¬ (proper p' ∨ cl p' 0 = 14) := by
    rcases hd0 with h | h
    · exact Or.inl h
    · right
      rw [he]
      simpa only [proper, Function.comp_apply,
        ne_eq, e.injective.eq_iff, class_relabel] using h
  have hlist := canonical_successors p' ⟨d, hd⟩ hv hnormal hd0'
  have hT :
      (∑ r : Boundary, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = T (cl p' d) s := by
    have h := TableBridge.count_successors
      (fun r : Boundary => bondDefects between p' r + bondDefects horizontal r r ≤ d)
      (fun r => cl r (d - (bondDefects between p' r + bondDefects horizontal r r))) s
    change (successors p' d).count s = _ at h
    rw [hlist] at h
    have hh : (∑ r : Boundary, if bondDefects between p' r + bondDefects horizontal r r ≤ d ∧
        cl r (d - (bondDefects between p' r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = ((classList (cl p' d)).count s : ℤ) := by
      exact_mod_cast h.symm
    have hne : cl p' d ≠ 12 ∧ cl p' d ≠ 14 := by
      have h : ∀ p (d : Fin 3), (d.val ≠ 0 ∨ ¬ (proper p ∨ cl p 0 = 14)) →
          cl p d.val ≠ 12 ∧ cl p d.val ≠ 14 := by decide +kernel
      exact h p' ⟨d, hd⟩ hd0'
    exact hh.trans (class_counts _ _ hne.1 hne.2)
  rw [he] at hT
  let E : Boundary ≃ Boundary := Equiv.piCongrRight fun _ : Fin 4 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Boundary, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d ∧
    cl (e ∘ r) (d - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d) s at hT
  simpa only [bond_relabel, class_relabel] using hT

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Certificate
