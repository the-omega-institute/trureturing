/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data
   mirror-E: none(waiver:exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate.transition_counts; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data.transition_counts
   digest: Width-five exact-budget transfer data and its zero-budget certificate. -/


/-
admission_basis: escape-witness
escape_witness: ZeroTemperature.owner_matrix connects the width-five classes 15, 17 and 30 to the reflected offset multiplicities 1, 2 and 0, and is used by ZeroTemperature.transition_counts.
Row: proof_shape=bind-only; consumers=Valid,successors
horizontal: proof_shape=bind-only; consumers=Valid,Forward.structural_certificate,HardinA229752.result
between: proof_shape=bind-only; consumers=successors,Certificate.transition_counts,HardinA229752.result
Valid: proof_shape=bind-only; consumers=Certificate.transition_counts,HardinA229752.result
cl: proof_shape=bind-only; consumers=successors,Certificate.transition_counts,HardinA229752.result
T: proof_shape=bind-only; consumers=Certificate.transition_counts,Forward.structural_certificate,HardinA229752.result
initial: proof_shape=bind-only; consumers=Forward.structural_certificate,HardinA229752.result
terminal: proof_shape=bind-only; consumers=Forward.structural_certificate,HardinA229752.result
W: proof_shape=bind-only; consumers=Forward.structural_certificate,HardinA229752.result
classList: proof_shape=bind-only; consumers=Certificate.canonical_successors,Certificate.class_counts
properSuccessors: proof_shape=bind-only; consumers=T,classList,successors
successors: proof_shape=bind-only; consumers=Certificate.canonical_successors,Certificate.transition_counts
ZeroTemperature.extend: proof_shape=bind-only; consumers=proper_extend,raw_extend,raw_iff_owner
ZeroTemperature.raw5: proof_shape=bind-only; consumers=raw_extend,raw_iff_owner,weighted
ZeroTemperature.proper_extend: proof_shape=bind-only; consumers=raw_iff_owner
ZeroTemperature.raw_extend: proof_shape=bind-only; consumers=raw_iff_owner
ZeroTemperature.raw_iff_owner: proof_shape=bind-only; consumers=weighted
ZeroTemperature.weighted: proof_shape=bind-only; consumers=transition_counts
ZeroTemperature.owner_matrix: proof_shape=content; consumers=transition_counts
ZeroTemperature.transition_counts: proof_shape=content; consumers=Width5.Certificate.transition_counts
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.ZeroTemperature
set_option maxRecDepth 100000
/-! Width-five exact-budget transfer data. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
abbrev Row := Fin 5 → Fin 4
abbrev horizontal : Finset (Fin 5 × Fin 5) :=
  D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData.horizontal
def between : Finset (Fin 5 × Fin 5) := {(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (0, 1), (1, 2), (2, 3), (3, 4), (1, 0), (2, 1), (3, 2), (4, 3)}
def Valid (p : Row) (d : ℕ) : Prop := d ≤ 2 ∧ bondDefects horizontal p p ≤ 2-d
instance (p : Row) (d : ℕ) : Decidable (Valid p d) := inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Row) (d : ℕ) : Fin 43 :=
  if p 1 = p 0 then (if p 2 = p 0 then (if p 3 = p 0 then (if p 4 = p 0 then ((![0, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![0, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)) else (if p 4 = p 0 then ((![28, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 3 then ((![0, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![21, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))) else (if p 3 = p 0 then (if p 4 = p 0 then ((![29, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![20, 4, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![16, 38, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 3 = p 2 then (if p 4 = p 0 then ((![20, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![0, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![26, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 4 = p 0 then ((![30, 11, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![16, 39, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 3 then ((![22, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![16, 37, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))))))) else (if p 2 = p 0 then (if p 3 = p 0 then (if p 4 = p 0 then ((![28, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![17, 34, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![19, 42, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 3 = p 1 then (if p 4 = p 0 then ((![17, 34, 3] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![20, 4, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 7, 41] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 4 = p 0 then ((![15, 8, 40] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![30, 6, 31] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 3 then ((![16, 39, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 12, 36] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))))) else (if p 2 = p 1 then (if p 3 = p 0 then (if p 4 = p 0 then ((![20, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![17, 34, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 9, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 3 = p 1 then (if p 4 = p 0 then ((![25, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![0, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![24, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩))) else (if p 4 = p 0 then ((![18, 23, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![19, 42, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 3 then ((![26, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 27, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))))) else (if p 3 = p 0 then (if p 4 = p 0 then ((![30, 11, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![30, 13, 2] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![30, 6, 31] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![30, 14, 5] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))) else (if p 3 = p 1 then (if p 4 = p 0 then ((![15, 0, 35] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![16, 38, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![15, 7, 41] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![30, 10, 32] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))) else (if p 3 = p 2 then (if p 4 = p 0 then ((![18, 23, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![15, 9, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![21, 0, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![15, 27, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))) else (if p 4 = p 0 then ((![15, 1, 33] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 1 then ((![30, 14, 5] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else (if p 4 = p 2 then ((![15, 12, 36] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩) else ((![16, 37, 0] : Fin 3 → Fin 43) ⟨d % 3, Nat.mod_lt _ (by decide)⟩)))))))))

def properSuccessors (p : Row) : List (Fin 43) :=
  (((List.finRange 4).filter (fun v => v ∈
    D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.offsetChoices
      ![0, p 0 ^^^ p 1, p 0 ^^^ p 2, p 0 ^^^ p 3, p 0 ^^^ p 4, p 0 ^^^ p 3])).map (fun v => cl (fun j => v ^^^ p j) 0)).insertionSort (· ≤ ·)

def T : Matrix (Fin 43) (Fin 43) ℤ :=
  ![(fun s => if s = 0 then 1 else if s = 15 then 4 else if s = 16 then 2 else if s = 17 then 1 else if s = 30 then 6 else 0),
    (fun s => if s = 1 then 1 else if s = 15 then 5 else if s = 16 then 2 else if s = 30 then 6 else 0),
    (fun s => if s = 0 then 2 else if s = 15 then 34 else if s = 16 then 4 else if s = 17 then 5 else if s = 18 then 4 else if s = 19 then 4 else if s = 20 then 2 else if s = 25 then 1 else if s = 30 then 20 else if s = 34 then 1 else 0),
    (fun s => if s = 0 then 2 else if s = 3 then 2 else if s = 4 then 4 else if s = 6 then 4 else if s = 7 then 8 else if s = 8 then 4 else if s = 13 then 2 else if s = 15 then 40 else if s = 16 then 16 else if s = 17 then 2 else if s = 18 then 4 else if s = 19 then 12 else if s = 20 then 4 else if s = 25 then 2 else if s = 28 then 4 else if s = 29 then 2 else if s = 30 then 46 else if s = 34 then 4 else 0),
    (fun s => if s = 7 then 2 else if s = 15 then 18 else if s = 16 then 2 else if s = 17 then 4 else if s = 19 then 2 else if s = 20 then 4 else if s = 30 then 12 else if s = 34 then 2 else 0),
    (fun s => if s = 0 then 1 else if s = 1 then 2 else if s = 6 then 1 else if s = 7 then 1 else if s = 8 then 1 else if s = 12 then 1 else if s = 15 then 35 else if s = 16 then 8 else if s = 17 then 3 else if s = 18 then 2 else if s = 19 then 1 else if s = 20 then 1 else if s = 21 then 1 else if s = 23 then 1 else if s = 26 then 1 else if s = 30 then 24 else 0),
    (fun s => if s = 15 then 6 else if s = 17 then 1 else if s = 19 then 1 else if s = 30 then 3 else 0),
    (fun s => if s = 7 then 1 else if s = 15 then 10 else if s = 16 then 1 else if s = 17 then 2 else if s = 19 then 1 else if s = 20 then 1 else if s = 30 then 5 else 0),
    (fun s => if s = 8 then 1 else if s = 15 then 7 else if s = 16 then 2 else if s = 17 then 2 else if s = 19 then 2 else if s = 30 then 7 else 0),
    (fun s => if s = 7 then 1 else if s = 15 then 9 else if s = 16 then 1 else if s = 17 then 2 else if s = 19 then 1 else if s = 20 then 1 else if s = 30 then 6 else 0),
    (fun s => if s = 15 then 9 else if s = 18 then 2 else if s = 30 then 2 else 0),
    (fun s => if s = 15 then 14 else if s = 17 then 2 else if s = 18 then 1 else if s = 19 then 1 else if s = 30 then 4 else 0),
    (fun s => if s = 12 then 1 else if s = 15 then 10 else if s = 16 then 2 else if s = 30 then 3 else 0),
    (fun s => if s = 15 then 2 else if s = 17 then 1 else 0),
    (fun s => if s = 15 then 6 else if s = 18 then 1 else if s = 30 then 1 else 0),
    (fun s => ((properSuccessors ![0, 1, 0, 1, 2]).count s : ℤ)),
    (fun s => if s = 15 then 2 else 0),
    (fun s => ((properSuccessors ![0, 1, 0, 1, 0]).count s : ℤ)),
    (fun s => if s = 30 then 2 else 0),
    (fun s => if s = 15 then 2 else if s = 30 then 1 else 0),
    (fun s => if s = 15 then 2 else if s = 17 then 2 else 0),
    (fun s => if s = 15 then 2 else if s = 30 then 2 else 0),
    (fun s => if s = 15 then 4 else 0),
    (fun s => if s = 10 then 1 else if s = 14 then 1 else if s = 15 then 13 else if s = 16 then 3 else if s = 17 then 1 else if s = 19 then 1 else if s = 30 then 7 else 0),
    (fun s => if s = 15 then 3 else if s = 30 then 2 else 0),
    (fun s => if s = 15 then 2 else if s = 17 then 2 else if s = 30 then 2 else 0),
    (fun s => if s = 15 then 3 else if s = 30 then 3 else 0),
    (fun s => if s = 12 then 1 else if s = 15 then 14 else if s = 16 then 2 else if s = 30 then 9 else 0),
    (fun s => if s = 15 then 4 else if s = 17 then 2 else if s = 30 then 2 else 0),
    (fun s => if s = 15 then 6 else if s = 17 then 2 else 0),
    (fun s => ((properSuccessors ![0, 1, 0, 2, 1]).count s : ℤ)),
    (fun s => if s = 6 then 1 else if s = 7 then 3 else if s = 8 then 2 else if s = 10 then 1 else if s = 12 then 1 else if s = 14 then 1 else if s = 15 then 41 else if s = 16 then 11 else if s = 17 then 5 else if s = 18 then 1 else if s = 19 then 4 else if s = 20 then 3 else if s = 24 then 1 else if s = 26 then 1 else if s = 28 then 1 else if s = 30 then 28 else if s = 34 then 1 else if s = 42 then 1 else 0),
    (fun s => if s = 0 then 2 else if s = 1 then 2 else if s = 6 then 2 else if s = 7 then 2 else if s = 8 then 1 else if s = 12 then 2 else if s = 15 then 47 else if s = 16 then 10 else if s = 17 then 4 else if s = 18 then 2 else if s = 19 then 2 else if s = 20 then 2 else if s = 21 then 2 else if s = 23 then 2 else if s = 26 then 2 else if s = 30 then 32 else 0),
    (fun s => if s = 0 then 2 else if s = 8 then 1 else if s = 10 then 2 else if s = 12 then 2 else if s = 14 then 4 else if s = 15 then 32 else if s = 16 then 10 else if s = 17 then 2 else if s = 18 then 4 else if s = 22 then 1 else if s = 30 then 25 else if s = 33 then 1 else if s = 37 then 2 else 0),
    (fun s => if s = 15 then 14 else if s = 17 then 4 else if s = 20 then 4 else if s = 30 then 6 else if s = 34 then 2 else 0),
    (fun s => if s = 1 then 2 else if s = 7 then 2 else if s = 10 then 2 else if s = 13 then 2 else if s = 14 then 2 else if s = 15 then 41 else if s = 16 then 4 else if s = 17 then 6 else if s = 18 then 6 else if s = 19 then 4 else if s = 20 then 4 else if s = 25 then 1 else if s = 29 then 1 else if s = 30 then 32 else if s = 34 then 1 else if s = 35 then 1 else if s = 38 then 2 else 0),
    (fun s => if s = 1 then 1 else if s = 6 then 1 else if s = 7 then 3 else if s = 8 then 1 else if s = 10 then 1 else if s = 12 then 4 else if s = 14 then 1 else if s = 15 then 35 else if s = 16 then 13 else if s = 17 then 2 else if s = 18 then 2 else if s = 19 then 3 else if s = 20 then 1 else if s = 21 then 1 else if s = 22 then 1 else if s = 26 then 1 else if s = 27 then 1 else if s = 30 then 35 else if s = 36 then 1 else if s = 37 then 1 else if s = 39 then 1 else 0),
    (fun s => if s = 1 then 1 else if s = 12 then 1 else if s = 15 then 13 else if s = 16 then 3 else if s = 18 then 1 else if s = 30 then 6 else 0),
    (fun s => if s = 0 then 1 else if s = 7 then 1 else if s = 15 then 15 else if s = 16 then 2 else if s = 17 then 3 else if s = 18 then 2 else if s = 19 then 1 else if s = 20 then 1 else if s = 30 then 9 else 0),
    (fun s => if s = 8 then 1 else if s = 12 then 1 else if s = 15 then 15 else if s = 16 then 3 else if s = 17 then 1 else if s = 19 then 3 else if s = 30 then 11 else 0),
    (fun s => if s = 1 then 1 else if s = 6 then 4 else if s = 7 then 4 else if s = 10 then 1 else if s = 12 then 2 else if s = 14 then 2 else if s = 15 then 44 else if s = 16 then 14 else if s = 17 then 6 else if s = 18 then 4 else if s = 19 then 2 else if s = 20 then 4 else if s = 22 then 1 else if s = 24 then 1 else if s = 26 then 2 else if s = 28 then 2 else if s = 30 then 36 else if s = 34 then 2 else if s = 39 then 2 else if s = 40 then 1 else if s = 42 then 2 else 0),
    (fun s => if s = 0 then 1 else if s = 4 then 1 else if s = 6 then 3 else if s = 7 then 3 else if s = 8 then 2 else if s = 9 then 1 else if s = 10 then 1 else if s = 12 then 3 else if s = 14 then 1 else if s = 15 then 45 else if s = 16 then 13 else if s = 17 then 6 else if s = 18 then 4 else if s = 19 then 5 else if s = 20 then 4 else if s = 21 then 1 else if s = 24 then 1 else if s = 26 then 1 else if s = 28 then 1 else if s = 29 then 1 else if s = 30 then 34 else if s = 34 then 2 else if s = 38 then 1 else if s = 41 then 1 else if s = 42 then 1 else 0),
    (fun s => if s = 6 then 1 else if s = 7 then 1 else if s = 8 then 1 else if s = 15 then 12 else if s = 16 then 4 else if s = 17 then 3 else if s = 18 then 1 else if s = 19 then 2 else if s = 20 then 1 else if s = 30 then 9 else 0)]

def initial : Fin 43 → ℤ := ![0, 0, 24, 12, 24, 48, 0, 0, 0, 48, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 24, 48, 24, 48, 24, 12, 48, 48, 24, 12, 0, 48, 24, 24, 24, 24, 48, 48, 48, 48, 24, 48, 48]
def terminal : Fin 43 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def W : Fin 12 → Fin 43 → ℤ :=
  ![![0, 0, 24, 12, 24, 48, 0, 0, 0, 48, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 24, 48, 24, 48, 24, 12, 48, 48, 24, 12, 0, 48, 24, 24, 24, 24, 48, 48, 48, 48, 24, 48, 48], ![312, 312, 0, 24, 96, 0, 528, 960, 480, 48, 312, 0, 720, 72, 384, 19176, 4272, 2256, 1200, 1536, 1104, 192, 96, 96, 120, 72, 288, 48, 192, 96, 13560, 0, 0, 24, 384, 24, 48, 96, 96, 96, 24, 48, 144], ![552, 528, 0, 48, 144, 0, 528, 2064, 984, 48, 312, 0, 1392, 96, 384, 90792, 8880, 14928, 2160, 4272, 3696, 96, 96, 0, 72, 72, 144, 48, 192, 120, 37896, 0, 0, 24, 1224, 24, 48, 96, 96, 96, 24, 48, 96], ![840, 744, 0, 96, 240, 0, 576, 3408, 1536, 48, 216, 0, 2064, 144, 288, 216792, 13248, 52344, 2208, 6576, 8400, 96, 96, 0, 72, 120, 144, 48, 288, 168, 61248, 0, 0, 24, 3096, 24, 48, 96, 96, 96, 24, 48, 96], ![1224, 960, 0, 192, 432, 0, 768, 5328, 2280, 48, 216, 0, 2736, 240, 288, 421368, 19008, 149112, 2112, 9840, 17808, 96, 96, 0, 72, 216, 144, 48, 480, 264, 94008, 0, 0, 24, 7224, 24, 48, 96, 96, 96, 24, 48, 96], ![1800, 1176, 0, 384, 816, 0, 1152, 8400, 3408, 48, 216, 0, 3408, 432, 288, 764520, 26880, 385704, 2496, 14976, 37392, 96, 96, 0, 72, 408, 144, 48, 864, 456, 150144, 0, 0, 24, 16248, 24, 48, 96, 96, 96, 24, 48, 96], ![2760, 1392, 0, 768, 1584, 0, 1920, 13776, 5304, 48, 216, 0, 4080, 816, 288, 1368264, 38976, 947160, 3264, 23760, 78864, 96, 96, 0, 72, 792, 144, 48, 1632, 840, 255960, 0, 0, 24, 35832, 24, 48, 96, 96, 96, 24, 48, 96], ![4488, 1608, 0, 1536, 3120, 0, 3456, 23760, 8736, 48, 216, 0, 4752, 1584, 288, 2490264, 59520, 2254920, 4800, 39840, 167184, 96, 96, 0, 72, 1560, 144, 48, 3168, 1608, 464496, 0, 0, 24, 78072, 24, 48, 96, 96, 96, 24, 48, 96], ![7752, 1824, 0, 3072, 6192, 0, 6528, 42960, 15240, 48, 216, 0, 5424, 3120, 288, 4673496, 96960, 5260728, 7872, 70512, 355344, 96, 96, 0, 72, 3096, 144, 48, 6240, 3144, 887688, 0, 0, 24, 168696, 24, 48, 96, 96, 96, 24, 48, 96], ![14088, 2040, 0, 6144, 12336, 0, 12672, 80592, 27888, 48, 216, 0, 6096, 6192, 288, 9059208, 168192, 12098088, 14016, 130368, 755472, 96, 96, 0, 72, 6168, 144, 48, 12384, 6216, 1758624, 0, 0, 24, 362232, 24, 48, 96, 96, 96, 24, 48, 96], ![26568, 2256, 0, 12288, 24624, 0, 24960, 155088, 52824, 48, 216, 0, 6768, 12336, 288, 18040488, 307008, 27518616, 26304, 248592, 1604112, 96, 96, 0, 72, 12312, 144, 48, 24672, 12360, 3561912, 0, 0, 24, 773880, 24, 48, 96, 96, 96, 24, 48, 96], ![51336, 2472, 0, 24576, 49200, 0, 49536, 303312, 102336, 48, 216, 0, 7440, 24624, 288, 36624696, 580992, 62043912, 50880, 483552, 3398928, 96, 96, 0, 72, 24600, 144, 48, 49248, 24648, 7303632, 0, 0, 24, 1646328, 24, 48, 96, 96, 96, 24, 48, 96]]
def classList : Fin 43 → List (Fin 43) :=
  ![[0, 15, 15, 15, 15, 16, 16, 17, 30, 30, 30, 30, 30, 30], [1, 15, 15, 15, 15, 15, 16, 16, 30, 30, 30, 30, 30, 30], [0, 0, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 25, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34], [0, 0, 3, 3, 4, 4, 4, 4, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 13, 13, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 25, 25, 28, 28, 28, 28, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 34, 34, 34], [7, 7, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 17, 17, 17, 17, 19, 19, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 34], [0, 1, 1, 6, 7, 8, 12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 18, 18, 19, 20, 21, 23, 26, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30], [15, 15, 15, 15, 15, 15, 17, 19, 30, 30, 30], [7, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 17, 17, 19, 20, 30, 30, 30, 30, 30], [8, 15, 15, 15, 15, 15, 15, 15, 16, 16, 17, 17, 19, 19, 30, 30, 30, 30, 30, 30, 30], [7, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 17, 17, 19, 20, 30, 30, 30, 30, 30, 30], [15, 15, 15, 15, 15, 15, 15, 15, 15, 18, 18, 30, 30], [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 17, 17, 18, 19, 30, 30, 30, 30], [12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 30, 30, 30], [15, 15, 17], [15, 15, 15, 15, 15, 15, 18, 30], properSuccessors ![0, 1, 0, 1, 2], [15, 15], properSuccessors ![0, 1, 0, 1, 0], [30, 30], [15, 15, 30], [15, 15, 17, 17], [15, 15, 30, 30], [15, 15, 15, 15], [10, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 17, 19, 30, 30, 30, 30, 30, 30, 30], [15, 15, 15, 30, 30], [15, 15, 17, 17, 30, 30], [15, 15, 15, 30, 30, 30], [12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 30, 30, 30, 30, 30, 30, 30, 30, 30], [15, 15, 15, 15, 17, 17, 30, 30], [15, 15, 15, 15, 15, 15, 17, 17], properSuccessors ![0, 1, 0, 2, 1], [6, 7, 7, 7, 8, 8, 10, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 19, 19, 19, 19, 20, 20, 20, 24, 26, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 42], [0, 0, 1, 1, 6, 6, 7, 7, 8, 12, 12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 23, 23, 26, 26, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30], [0, 0, 8, 10, 10, 12, 12, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 18, 18, 18, 18, 22, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 33, 37, 37], [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 17, 17, 17, 17, 20, 20, 20, 20, 30, 30, 30, 30, 30, 30, 34, 34], [1, 1, 7, 7, 10, 10, 13, 13, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20, 25, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 35, 38, 38], [1, 6, 7, 7, 7, 8, 10, 12, 12, 12, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 19, 20, 21, 22, 26, 27, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 36, 37, 39], [1, 12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 18, 30, 30, 30, 30, 30, 30], [0, 7, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 17, 17, 17, 18, 18, 19, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30], [8, 12, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 17, 19, 19, 19, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30], [1, 6, 6, 6, 6, 7, 7, 7, 7, 10, 12, 12, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 20, 20, 20, 20, 22, 24, 26, 26, 28, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 34, 39, 39, 40, 42, 42], [0, 4, 6, 6, 6, 7, 7, 7, 8, 8, 9, 10, 12, 12, 12, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 20, 20, 20, 20, 21, 24, 26, 28, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 34, 34, 38, 41, 42], [6, 7, 8, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 18, 19, 19, 20, 30, 30, 30, 30, 30, 30, 30, 30, 30]]
def successors (p : Row) (d : ℕ) : List (Fin 43) :=
  if d = 0 ∧ bondDefects horizontal p p = 0 then properSuccessors p else
  ((List.ofFn (fun i : Fin (4^5) => finFunctionFinEquiv.symm i)).filterMap
    (fun r => let a := bondDefects between p r + bondDefects horizontal r r
      if a ≤ d then some (cl r (d-a)) else none)).insertionSort (· ≤ ·)
end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data

/- Proper successor rows are exact images of the original zone relation. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.ZeroTemperature
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

set_option maxRecDepth 100000

def extend (p : Row) : Width6.Data.Row := ![p 0, p 1, p 2, p 3, p 4, p 3]

def raw5 (p r : Row) : Prop :=
  bondDefects between p r + bondDefects horizontal r r = 0

private local instance (p r : Row) : Decidable (raw5 p r) :=
  inferInstanceAs (Decidable (_ = 0))

set_option maxHeartbeats 2000000 in
theorem proper_extend (p : Row) :
    bondDefects Width6.Data.horizontal (extend p) (extend p) = 0 ↔
      bondDefects Width5.Data.horizontal p p = 0 := by
  simp only [bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width5.Data.horizontal, Width6.Data.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

set_option maxHeartbeats 2000000 in
theorem raw_extend (p r : Row) :
    Width6.ZeroTemperature.raw (extend p) (extend r) ↔ raw5 p r := by
  simp only [Width6.ZeroTemperature.raw, raw5, Nat.add_eq_zero_iff,
    bondDefects, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [Width5.Data.between, Width6.Data.between,
    Width5.Data.horizontal, Width6.Data.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData.horizontal,
    D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData.horizontal,
    extend, Fin.forall_fin_succ, ne_comm] <;> tauto

theorem raw_iff_owner (p r : Row)
    (hp : bondDefects Width5.Data.horizontal p p = 0) :
    raw5 p r ↔ ∃ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
      r = fun j => v ^^^ p j := by
  rw [← raw_extend, Width6.ZeroTemperature.raw_iff_shift _ _
    ((proper_extend p).mpr hp)]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨v, hv, ?_⟩
    funext j
    have h := congrFun he j.castSucc
    fin_cases j <;> simpa [extend] using h
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    funext j
    fin_cases j <;> rfl

private theorem weighted (p : Row) (hp : bondDefects horizontal p p = 0)
    (w : Row → ℤ) :
    (∑ r : Row, if raw5 p r then w r else 0) =
      ∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
        w (fun j => v ^^^ p j) := by
  classical
  have hi : Function.Injective (fun v : Fin 4 => fun j : Fin 5 => v ^^^ p j) := by
    intro a b hab
    have h := congrFun hab 0
    change a ^^^ p 0 = b ^^^ p 0 at h
    rw [Fin.xor_comm a (p 0), Fin.xor_comm b (p 0)] at h
    exact xor_cancel (p 0) a b |>.mp h
  have hs : Finset.univ.filter (raw5 p) =
      (offsetChoices (Width6.ZeroTemperature.offsets (extend p))).image
        (fun v => fun j => v ^^^ p j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    simpa only [eq_comm] using raw_iff_owner p r hp
  rw [← Finset.sum_filter, hs, Finset.sum_image]
  exact fun _ _ _ _ h => hi h

private theorem owner_matrix (p : Row) (hp : bondDefects horizontal p p = 0)
    (s : Fin 43) :
    (∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
      if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hc (v : Fin 4) : cl (fun j => v ^^^ p j) 0 = cl p 0 := by
    simp only [cl, xor_cancel]
  simp_rw [hc]
  have table :
      (∀ s : Fin 43, T 15 s = if 15 = s then 1 else 0) ∧
      (∀ s : Fin 43, T 17 s = if 17 = s then 2 else 0) ∧
      (∀ s : Fin 43, T 30 s = 0) := by decide +kernel
  let steps (q : Row) : Fin 5 → Fin 4 := fun j =>
    (Width6.ZeroTemperature.offsets (extend q)) j.castSucc ^^^
      (Width6.ZeroTemperature.offsets (extend q)) j.succ
  have shape : ∀ a b c d : Fin 4,
      let q : Row := ![0, a, b, c, d]
      bondDefects horizontal q q = 0 →
      (cl q 0 = 15 ∧ (∀ j, steps q j ≠ 0) ∧
        (∃ v, v ≠ 0 ∧ ∀ j, steps q j ≠ v) ∧ ¬ (∀ j, steps q j = steps q 0)) ∨
      (cl q 0 = 17 ∧ (∀ j, steps q j ≠ 0) ∧
        (∃ v, v ≠ 0 ∧ ∀ j, steps q j ≠ v) ∧ (∀ j, steps q j = steps q 0)) ∨
      (cl q 0 = 30 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 0) := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide +kernel
  have h : ∀ a b c d : Fin 4,
      let q : Row := ![0, a, b, c, d]
      bondDefects horizontal q q = 0 →
      (cl q 0 = 15 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 1) ∨
      (cl q 0 = 17 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 2) ∨
      (cl q 0 = 30 ∧ (offsetChoices (Width6.ZeroTemperature.offsets (extend q))).card = 0) := by
    intro a b c d
    dsimp only
    intro hp
    rcases shape a b c d hp with ⟨hc, hn, hv, he⟩ | ⟨hc, hn, hv, he⟩ | hz
    · left
      refine ⟨hc, ?_⟩
      simpa only [offsetChoices, steps, if_neg he] using
        choices_card (steps ![0, a, b, c, d]) hn hv
    · right; left
      refine ⟨hc, ?_⟩
      simpa only [offsetChoices, steps, if_pos he] using
        choices_card (steps ![0, a, b, c, d]) hn hv
    · exact Or.inr (Or.inr hz)
  let q : Row := fun j => p 0 ^^^ p j
  have heq : q = ![0, q 1, q 2, q 3, q 4] := by
    funext j
    fin_cases j <;> simp [q]
  have hpq : bondDefects horizontal q q = 0 := by
    simpa only [bondDefects, q, xor_cancel] using hp
  have hcl : cl q 0 = cl p 0 := by simp only [q, cl, xor_cancel]
  have hoff : Width6.ZeroTemperature.offsets (extend q) =
      Width6.ZeroTemperature.offsets (extend p) := by
    funext j
    fin_cases j <;> simp [Width6.ZeroTemperature.offsets, extend, q] <;>
      exact (Fin.xor_comm 0 _).trans (Fin.xor_zero _)
  have hh := h (q 1) (q 2) (q 3) (q 4)
  rw [← heq] at hh
  rcases hh hpq with ⟨hc, hn⟩ | ⟨hc, hn⟩ | ⟨hc, hn⟩
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.1]
    simp [hn]
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.2.1]
    simp [hn]
  · rw [hcl] at hc
    rw [hoff] at hn
    rw [hc, table.2.2]
    simp [hn, ← Finset.card_eq_zero]

theorem transition_counts (p : Row) (hp : bondDefects horizontal p p = 0)
    (s : Fin 43) :
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = T (cl p 0) s := by
  have hw := weighted p hp (fun r => if cl r 0 = s then (1 : ℤ) else 0)
  have ho := owner_matrix p hp s
  calc
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 0 ∧
        cl r (0 - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) =
        ∑ r : Row, if raw5 p r then (if cl r 0 = s then (1 : ℤ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : raw5 p r
      · have hz : bondDefects between p r + bondDefects horizontal r r = 0 := h
        simp [hz, h]
      · have hn : ¬ bondDefects between p r + bondDefects horizontal r r ≤ 0 := by
          change ¬ _ = 0 at h
          omega
        simp [hn, h]
    _ = ∑ v ∈ offsetChoices (Width6.ZeroTemperature.offsets (extend p)),
        if cl (fun j => v ^^^ p j) 0 = s then (1 : ℤ) else 0 := hw
    _ = T (cl p 0) s := ho

end D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.ZeroTemperature
