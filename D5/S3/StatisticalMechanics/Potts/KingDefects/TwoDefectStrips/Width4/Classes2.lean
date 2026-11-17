/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes2
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes2
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229751.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate.transition_counts,D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward.structural_certificate
   digest: Width-4 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed helpers on the live path of HardinA229751.result)
extend: proof_shape=bind-only; consumers=proper_extend,raw_extend,exact_image,class_successors
raw: proof_shape=bind-only; consumers=raw_extend,exact_image,class_successors
proper_extend: proof_shape=bind-only; consumers=exact_image
raw_extend: proof_shape=bind-only; consumers=exact_image
exact_image: proof_shape=bind-only; consumers=class_successors
class_successors: proof_shape=bind-only; consumers=Certificate.canonical_successors
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts
open KingDefects.TwoDefectStrips
open StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes2
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233164KingStrip (Boundary)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def extend (p : Boundary) : Width6.Data.Row := ![p 0,p 1,p 2,p 3,p 2,p 1]
private def raw (p r : Boundary) : Prop :=
  bondDefects Width4.Data.between p r + bondDefects Width4.Data.horizontal r r = 0
private local instance (p r : Boundary) : Decidable (raw p r) := inferInstanceAs (Decidable (_ = 0))
private theorem proper_extend (p : Boundary) :
    bondDefects Width6.Data.horizontal (extend p) (extend p) = 0 ↔
      bondDefects Width4.Data.horizontal p p = 0 := by
  simp only [bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width4.Data.horizontal, Width6.Data.horizontal,
    StripDefects.HardinA229582Strip.horizontal, StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

private theorem raw_extend (p r : Boundary) :
    Width6.ZeroTemperature.raw (extend p) (extend r) ↔ raw p r := by
  simp only [Width6.ZeroTemperature.raw, raw, Nat.add_eq_zero_iff,
    bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width4.Data.between, Width6.Data.between,
    Width4.Data.horizontal, Width6.Data.horizontal,
    StripDefects.HardinA229582Strip.horizontal, StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

private theorem exact_image (p r : Boundary) (hp : bondDefects Width4.Data.horizontal p p = 0) :
    raw p r ↔ ∃ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
      r = fun j => v ^^^ p j := by
  rw [← raw_extend, Width6.ZeroTemperature.raw_iff_shift _ _ ((proper_extend p).mpr hp)]
  constructor
  · rintro ⟨v,hv,he⟩
    refine ⟨v,hv,?_⟩
    funext j
    have h := congrFun he (j.castAdd 2)
    fin_cases j <;> simpa [extend] using h
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v,hv,?_⟩
    funext j
    fin_cases j <;> rfl


theorem class_successors : ∀ p (d : Fin 3), Valid p d.val →
    Canonical p → cl p d.val = (2 : Fin 19) → successors p d.val = classList 2 := by
  intro p d _ _ hc
  have hd : d.val = 0 := by
    have h : ∀ (p : Boundary) (d : Fin 3), cl p d.val = 2 → d.val = 0 := by
      decide +kernel
    exact h p d hc
  rw [hd] at hc ⊢
  have hp : bondDefects horizontal p p = 0 ∧
      offsetChoices (Width6.ZeroTemperature.offsets (extend p)) = ∅ := by
    have h : ∀ p : Boundary, cl p 0 = 2 →
        bondDefects horizontal p p = 0 ∧
          offsetChoices (Width6.ZeroTemperature.offsets (extend p)) = ∅ := by
      decide +kernel
    exact h p hc
  have hn (r : Boundary) : ¬ (bondDefects between p r + bondDefects horizontal r r ≤ 0) := by
    intro h
    have hraw : raw p r := Nat.eq_zero_of_le_zero h
    rw [exact_image p r hp.1, hp.2] at hraw
    simpa using hraw
  simp [successors, hn, classList]
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4.Classes2
