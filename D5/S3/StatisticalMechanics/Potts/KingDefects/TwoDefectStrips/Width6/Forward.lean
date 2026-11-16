/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Forward
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-six exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229753.result)
structural_certificate: proof_shape=bind-only; consumers=HardinA229753.result
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check0
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check2
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check4
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check5
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check6
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check7
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check8
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial9
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check9
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial10
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check10
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial11
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check11
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial12
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check12
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial13
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check13
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial14
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check14
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial15
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check15
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial16
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check16
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial17
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check17
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial18
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check18
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial19
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check19
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial20
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check20
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial21
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check21
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial22
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check22
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial23
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov.Check23
/-! Acceptance, initial weights and the forward polynomial relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Forward
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem structural_certificate :
    (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ s : Fin 96, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 11, W i.succ = Matrix.vecMul (W i.castSucc) T) ∧
    W 11 = ∑ j : Fin 6, (![-8, 36, -66, 63, -33, 9] j : ℤ) • W ⟨5+j.val, by omega⟩ := by
  refine ⟨Pins.Terminal.certificate, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro s
    fin_cases s
    · exact Pins.Initial0.certificate ⟨0, by decide⟩
    · exact Pins.Initial0.certificate ⟨1, by decide⟩
    · exact Pins.Initial0.certificate ⟨2, by decide⟩
    · exact Pins.Initial0.certificate ⟨3, by decide⟩
    · exact Pins.Initial1.certificate ⟨0, by decide⟩
    · exact Pins.Initial1.certificate ⟨1, by decide⟩
    · exact Pins.Initial1.certificate ⟨2, by decide⟩
    · exact Pins.Initial1.certificate ⟨3, by decide⟩
    · exact Pins.Initial2.certificate ⟨0, by decide⟩
    · exact Pins.Initial2.certificate ⟨1, by decide⟩
    · exact Pins.Initial2.certificate ⟨2, by decide⟩
    · exact Pins.Initial2.certificate ⟨3, by decide⟩
    · exact Pins.Initial3.certificate ⟨0, by decide⟩
    · exact Pins.Initial3.certificate ⟨1, by decide⟩
    · exact Pins.Initial3.certificate ⟨2, by decide⟩
    · exact Pins.Initial3.certificate ⟨3, by decide⟩
    · exact Pins.Initial4.certificate ⟨0, by decide⟩
    · exact Pins.Initial4.certificate ⟨1, by decide⟩
    · exact Pins.Initial4.certificate ⟨2, by decide⟩
    · exact Pins.Initial4.certificate ⟨3, by decide⟩
    · exact Pins.Initial5.certificate ⟨0, by decide⟩
    · exact Pins.Initial5.certificate ⟨1, by decide⟩
    · exact Pins.Initial5.certificate ⟨2, by decide⟩
    · exact Pins.Initial5.certificate ⟨3, by decide⟩
    · exact Pins.Initial6.certificate ⟨0, by decide⟩
    · exact Pins.Initial6.certificate ⟨1, by decide⟩
    · exact Pins.Initial6.certificate ⟨2, by decide⟩
    · exact Pins.Initial6.certificate ⟨3, by decide⟩
    · exact Pins.Initial7.certificate ⟨0, by decide⟩
    · exact Pins.Initial7.certificate ⟨1, by decide⟩
    · exact Pins.Initial7.certificate ⟨2, by decide⟩
    · exact Pins.Initial7.certificate ⟨3, by decide⟩
    · exact Pins.Initial8.certificate ⟨0, by decide⟩
    · exact Pins.Initial8.certificate ⟨1, by decide⟩
    · exact Pins.Initial8.certificate ⟨2, by decide⟩
    · exact Pins.Initial8.certificate ⟨3, by decide⟩
    · exact Pins.Initial9.certificate ⟨0, by decide⟩
    · exact Pins.Initial9.certificate ⟨1, by decide⟩
    · exact Pins.Initial9.certificate ⟨2, by decide⟩
    · exact Pins.Initial9.certificate ⟨3, by decide⟩
    · exact Pins.Initial10.certificate ⟨0, by decide⟩
    · exact Pins.Initial10.certificate ⟨1, by decide⟩
    · exact Pins.Initial10.certificate ⟨2, by decide⟩
    · exact Pins.Initial10.certificate ⟨3, by decide⟩
    · exact Pins.Initial11.certificate ⟨0, by decide⟩
    · exact Pins.Initial11.certificate ⟨1, by decide⟩
    · exact Pins.Initial11.certificate ⟨2, by decide⟩
    · exact Pins.Initial11.certificate ⟨3, by decide⟩
    · exact Pins.Initial12.certificate ⟨0, by decide⟩
    · exact Pins.Initial12.certificate ⟨1, by decide⟩
    · exact Pins.Initial12.certificate ⟨2, by decide⟩
    · exact Pins.Initial12.certificate ⟨3, by decide⟩
    · exact Pins.Initial13.certificate ⟨0, by decide⟩
    · exact Pins.Initial13.certificate ⟨1, by decide⟩
    · exact Pins.Initial13.certificate ⟨2, by decide⟩
    · exact Pins.Initial13.certificate ⟨3, by decide⟩
    · exact Pins.Initial14.certificate ⟨0, by decide⟩
    · exact Pins.Initial14.certificate ⟨1, by decide⟩
    · exact Pins.Initial14.certificate ⟨2, by decide⟩
    · exact Pins.Initial14.certificate ⟨3, by decide⟩
    · exact Pins.Initial15.certificate ⟨0, by decide⟩
    · exact Pins.Initial15.certificate ⟨1, by decide⟩
    · exact Pins.Initial15.certificate ⟨2, by decide⟩
    · exact Pins.Initial15.certificate ⟨3, by decide⟩
    · exact Pins.Initial16.certificate ⟨0, by decide⟩
    · exact Pins.Initial16.certificate ⟨1, by decide⟩
    · exact Pins.Initial16.certificate ⟨2, by decide⟩
    · exact Pins.Initial16.certificate ⟨3, by decide⟩
    · exact Pins.Initial17.certificate ⟨0, by decide⟩
    · exact Pins.Initial17.certificate ⟨1, by decide⟩
    · exact Pins.Initial17.certificate ⟨2, by decide⟩
    · exact Pins.Initial17.certificate ⟨3, by decide⟩
    · exact Pins.Initial18.certificate ⟨0, by decide⟩
    · exact Pins.Initial18.certificate ⟨1, by decide⟩
    · exact Pins.Initial18.certificate ⟨2, by decide⟩
    · exact Pins.Initial18.certificate ⟨3, by decide⟩
    · exact Pins.Initial19.certificate ⟨0, by decide⟩
    · exact Pins.Initial19.certificate ⟨1, by decide⟩
    · exact Pins.Initial19.certificate ⟨2, by decide⟩
    · exact Pins.Initial19.certificate ⟨3, by decide⟩
    · exact Pins.Initial20.certificate ⟨0, by decide⟩
    · exact Pins.Initial20.certificate ⟨1, by decide⟩
    · exact Pins.Initial20.certificate ⟨2, by decide⟩
    · exact Pins.Initial20.certificate ⟨3, by decide⟩
    · exact Pins.Initial21.certificate ⟨0, by decide⟩
    · exact Pins.Initial21.certificate ⟨1, by decide⟩
    · exact Pins.Initial21.certificate ⟨2, by decide⟩
    · exact Pins.Initial21.certificate ⟨3, by decide⟩
    · exact Pins.Initial22.certificate ⟨0, by decide⟩
    · exact Pins.Initial22.certificate ⟨1, by decide⟩
    · exact Pins.Initial22.certificate ⟨2, by decide⟩
    · exact Pins.Initial22.certificate ⟨3, by decide⟩
    · exact Pins.Initial23.certificate ⟨0, by decide⟩
    · exact Pins.Initial23.certificate ⟨1, by decide⟩
    · exact Pins.Initial23.certificate ⟨2, by decide⟩
    · exact Pins.Initial23.certificate ⟨3, by decide⟩
  · intro i
    funext s
    fin_cases s
    · exact (Krylov.Check0.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check0.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check0.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check0.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check1.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check1.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check1.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check1.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check2.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check2.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check2.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check2.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check3.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check3.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check3.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check3.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check4.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check4.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check4.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check4.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check5.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check5.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check5.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check5.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check6.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check6.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check6.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check6.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check7.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check7.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check7.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check7.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check8.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check8.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check8.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check8.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check9.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check9.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check9.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check9.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check10.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check10.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check10.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check10.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check11.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check11.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check11.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check11.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check12.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check12.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check12.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check12.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check13.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check13.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check13.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check13.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check14.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check14.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check14.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check14.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check15.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check15.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check15.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check15.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check16.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check16.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check16.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check16.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check17.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check17.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check17.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check17.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check18.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check18.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check18.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check18.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check19.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check19.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check19.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check19.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check20.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check20.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check20.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check20.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check21.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check21.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check21.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check21.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check22.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check22.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check22.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check22.certificate.1 i ⟨3, by decide⟩)
    · exact (Krylov.Check23.certificate.1 i ⟨0, by decide⟩)
    · exact (Krylov.Check23.certificate.1 i ⟨1, by decide⟩)
    · exact (Krylov.Check23.certificate.1 i ⟨2, by decide⟩)
    · exact (Krylov.Check23.certificate.1 i ⟨3, by decide⟩)
  · funext s
    fin_cases s
    · exact (Krylov.Check0.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check0.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check0.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check0.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check1.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check1.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check1.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check1.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check2.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check2.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check2.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check2.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check3.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check3.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check3.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check3.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check4.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check4.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check4.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check4.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check5.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check5.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check5.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check5.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check6.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check6.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check6.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check6.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check7.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check7.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check7.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check7.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check8.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check8.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check8.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check8.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check9.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check9.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check9.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check9.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check10.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check10.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check10.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check10.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check11.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check11.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check11.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check11.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check12.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check12.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check12.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check12.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check13.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check13.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check13.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check13.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check14.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check14.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check14.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check14.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check15.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check15.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check15.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check15.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check16.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check16.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check16.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check16.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check17.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check17.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check17.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check17.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check18.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check18.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check18.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check18.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check19.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check19.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check19.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check19.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check20.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check20.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check20.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check20.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check21.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check21.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check21.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check21.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check22.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check22.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check22.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check22.certificate.2 ⟨3, by decide⟩)
    · exact (Krylov.Check23.certificate.2 ⟨0, by decide⟩)
    · exact (Krylov.Check23.certificate.2 ⟨1, by decide⟩)
    · exact (Krylov.Check23.certificate.2 ⟨2, by decide⟩)
    · exact (Krylov.Check23.certificate.2 ⟨3, by decide⟩)

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Forward
