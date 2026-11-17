/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Width-3 exact-budget transfer measurement. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers on the live path of HardinA229750.result)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip
set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip (Boundary)
abbrev horizontal : Finset (Fin 3 × Fin 3) :=
  D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229581Strip.horizontal
abbrev between : Finset (Fin 3 × Fin 3) :=
  D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229536Strip.between
def Valid (p : Boundary) (d : ℕ) : Prop := d ≤ 2 ∧ bondDefects horizontal p p ≤ 2-d
instance (p : Boundary) (d : ℕ) : Decidable (Valid p d) := inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 9 :=
  if p 1 = p 0 then (if p 2 = p 0 then ((![6, 0, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![8, 4, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)) else (if p 2 = p 0 then ((![7, 3, 2] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 2 = p 1 then ((![8, 4, 0] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![5, 0, 1] : Fin 3 → Fin 9) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))
def T : Matrix (Fin 9) (Fin 9) ℤ :=
  ![![1, 0, 0, 0, 0, 7, 0, 5, 2], ![7, 1, 0, 5, 2, 13, 1, 5, 8], ![10, 0, 2, 2, 4, 10, 2, 6, 8], ![0, 0, 0, 2, 0, 10, 0, 2, 4], ![2, 0, 0, 2, 0, 8, 0, 4, 6], (fun s => if s = 5 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip.rate false / 8 else 0), ![0, 0, 0, 0, 0, 6, 0, 6, 0], (fun s => if s = 7 then D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233163KingStrip.rate true / 8 else 0), ![0, 0, 0, 0, 0, 2, 0, 2, 0]]
def initial : Fin 9 → ℤ := ![0, 24, 12, 0, 24, 0, 4, 0, 0]
abbrev terminal : Fin 9 → ℤ :=
  D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229632Strip.terminal
def W : Fin 9 → Fin 9 → ℤ :=
  ![![0, 24, 12, 0, 24, 0, 4, 0, 0], ![336, 24, 24, 192, 96, 648, 48, 312, 432], ![936, 24, 48, 744, 144, 7392, 72, 4488, 2400], ![1872, 24, 96, 1992, 240, 28560, 120, 21360, 6288], ![3480, 24, 192, 4776, 432, 78072, 216, 71016, 14112], ![6432, 24, 384, 10920, 816, 185400, 408, 201504, 30384], ![12072, 24, 768, 24360, 1584, 413520, 792, 525912, 64704], ![23088, 24, 1536, 53544, 3120, 896448, 1560, 1306128, 137424], ![44856, 24, 3072, 116520, 6192, 1918344, 3096, 3140808, 291552]]
def classList : Fin 9 → List (Fin 9) :=
  ![[0, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 8, 8], [0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8], [3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 8, 8, 8, 8], [0, 0, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8], [], [5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7], [], [5, 5, 7, 7]]
def successors (p : Boundary) (d : ℕ) : List (Fin 9) :=
  ((List.ofFn (fun i : Fin (4^3) => finFunctionFinEquiv.symm i)).filterMap
    (fun r => let a := bondDefects between p r + bondDefects horizontal r r
      if a ≤ d then some (cl r (d-a)) else none)).insertionSort (· ≤ ·)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3.Data
