/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Certificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
source_successors: proof_shape=bind-only; consumers=canonical_successors
class_relabel: proof_shape=bind-only; consumers=transition_counts
bond_relabel: proof_shape=bind-only; consumers=transition_counts
canonical_successors: proof_shape=bind-only; consumers=transition_counts
class_counts: proof_shape=bind-only; consumers=transition_counts
transition_counts: proof_shape=bind-only; consumers=HardinA229753.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.TableBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source9
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source10
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source11
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source12
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source13
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source14
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source15
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source16
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source17
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source18
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source19
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source20
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source21
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source22
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source23
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source24
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source25
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source26
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source27
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source28
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source29
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source30
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source31
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source32
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source33
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source34
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source35
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source36
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source37
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source38
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source39
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source40
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source41
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source42
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks1.Source43
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

set_option maxHeartbeats 0 in
private theorem source_successors (i : Fin 313) :
    successors (Sources.sources i).1 (Sources.sources i).2.val =
      classList (cl (Sources.sources i).1 (Sources.sources i).2.val) := by
  fin_cases i
  · exact Chunks0.Source0.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source0.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source0.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source1.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source1.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source1.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source2.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source2.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source2.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source3.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source3.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source3.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source4.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source4.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source4.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source5.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source5.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source5.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source6.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source6.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source6.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source7.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source7.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source7.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source8.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source8.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source8.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source9.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source9.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source9.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source10.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source10.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source10.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source11.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source11.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source11.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source12.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source12.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source12.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source13.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source14.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source15.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source16.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source17.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source18.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source19.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source20.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source21.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source22.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source23.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source24.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source25.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source26.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source27.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source28.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source29.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source30.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source31.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source32.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source33.successor_rows ⟨8, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨0, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨1, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨2, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨3, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨4, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨5, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨6, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨7, by decide⟩
  · exact Chunks0.Source34.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source35.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source36.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source37.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source38.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source39.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source40.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source41.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨3, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨4, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨5, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨6, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨7, by decide⟩
  · exact Chunks1.Source42.successor_rows ⟨8, by decide⟩
  · exact Chunks1.Source43.successor_rows ⟨0, by decide⟩
  · exact Chunks1.Source43.successor_rows ⟨1, by decide⟩
  · exact Chunks1.Source43.successor_rows ⟨2, by decide⟩
  · exact Chunks1.Source43.successor_rows ⟨3, by decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem canonical_successors (p : Row) (d : Fin 3) (hp : Valid p d.val)
    (hc : Canonical p) : successors p d.val = classList (cl p d.val) := by
  have h : ∀ (i : Fin 187) (d : Fin 3), Valid (Rows.rows i) d.val →
      Sources.sources (Sources.sourceIndex i d) = (Rows.rows i, d) := by
    decide +kernel
  have hr := Rows.reconstruction p hc
  have hv : Valid (Rows.rows (Rows.rowIndex p)) d.val := by rw [hr]; exact hp
  have hs := h (Rows.rowIndex p) d hv
  rw [hr] at hs
  have hh := source_successors (Sources.sourceIndex (Rows.rowIndex p) d)
  rw [hs] at hh
  exact hh

private theorem class_counts : ∀ c s : Fin 96, ((classList c).count s : ℤ) = T c s := by
  intro c
  fin_cases c <;> decide +kernel

theorem transition_counts (p : Row) (d : ℕ) (hp : Valid p d) (s : Fin 96) :
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
  let E : Row ≃ Row := Equiv.piCongrRight fun _ : Fin 6 => e
  rw [← E.sum_comp] at hT
  change (∑ r : Row, if bondDefects between (e ∘ p) (e ∘ r) +
    bondDefects horizontal (e ∘ r) (e ∘ r) ≤ d ∧
    cl (e ∘ r) (d - (bondDefects between (e ∘ p) (e ∘ r) +
      bondDefects horizontal (e ∘ r) (e ∘ r))) = s then (1 : ℤ) else 0) =
      T (cl (e ∘ p) d) s at hT
  simpa only [bond_relabel, class_relabel] using hT

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Certificate
