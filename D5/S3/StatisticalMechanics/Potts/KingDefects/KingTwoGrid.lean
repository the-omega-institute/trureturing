/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Literal canonical two-defect king colourings. -/

/-
TwoDefect: proof_shape=bind-only; consumers=KingTwoGrid.T,KingTwoColumnOne.literal_bridge
T: proof_shape=bind-only; consumers=KingTwoColumnOne.literal_bridge,KingTwoColumnOne.result
-/
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid

open D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

def TwoDefect {n k : ℕ} (f : Cell n k → Fin 4) : Prop :=
  (Finset.univ.filter (fun e : Edge n k => mono f e)).card = 2

noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {f : Cell n k → Fin 4 // TwoDefect f ∧ normal f}

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
