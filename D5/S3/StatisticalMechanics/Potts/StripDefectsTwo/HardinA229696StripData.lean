/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696Strip.finite_certificate
   digest: Block extension for exact two-defect HA strip counts. -/

/-
admission_basis: open-problem-resolution (#31299; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229696Strip.result)
Valid: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
T: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229696Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer

open scoped BigOperators
open D5.S3.Combinatorics.TraceAvoidingArrays
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229588Strip (Row horizontal between)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def Valid (_ : Row) (d : ℕ) : Prop := d ≤ 2
private instance decidableValid (p : Row) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (d ≤ 2))
def cl (p : Row) (d : ℕ) : Fin 15 :=
  if 0 < d then (HardinA229588Strip.cl p (d - 1)).castAdd 5
  else (HardinA233258PairTransfer.cls (p 0, p 1, p 2)).natAdd 10
def T : Matrix (Fin 15) (Fin 15) ℤ :=
  Matrix.reindex (finSumFinEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15)
    (finSumFinEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15)
    (Matrix.fromBlocks HardinA229588Strip.T
      (Fin.append (![![0, 0, 2, 2, 4],
      ![1, 0, 2, 2, 1],
      ![1, 3, 2, 2, 4],
      ![0, 1, 3, 0, 2],
      ![2, 2, 4, 1, 3]])
        (HardinA229588Strip.T.submatrix (fun i : Fin 5 => i.castAdd 5)
          (fun j : Fin 5 => j.natAdd 5)))
      0 HardinA233258PairTransfer.Q)
def initial : Fin 15 → ℤ := Fin.append HardinA229588Strip.initial (![0, 0, 0, 0, 0])
def terminal : Fin 15 → ℤ := Fin.append (fun _ : Fin 10 => 0) (fun _ : Fin 5 => 1)
def W : Fin 11 → Fin 15 → ℤ :=
  Fin.append (fun i => Fin.append (HardinA229588Strip.W i)
    ((![![0, 0, 0, 0, 0],
      ![24, 36, 72, 36, 72],
      ![366, 816, 834, 894, 846],
      ![4224, 7332, 5646, 7218, 6042],
      ![33834, 52350, 38058, 51972, 38736],
      ![236910, 341058, 239400, 335202, 229728],
      ![1527054, 2092122, 1436118, 2038908, 1308276]]) i))
    (![![218736, 218736, 140076, 201492, 61416, 1768404, 2109972, 1353222, 2003550, 1009140, 9318006, 12306282, 8322696, 11917530, 7244400],
      ![997776, 997776, 638964, 919116, 280152, 9266460, 10824540, 6941118, 10244478, 4940100, 54676854, 70181538, 46970190, 67629276, 39274884],
      ![4551408, 4551408, 2914668, 4192596, 1277928, 47742324, 54849588, 35167038, 51772134, 24071172, 311516334, 390787938, 259551624, 375074658, 209417616],
      ![20761488, 20761488, 13295412, 19124748, 5829336, 242743932, 275164092, 176403462, 259158006, 116811444, 1734312126, 2134897578, 1409796150, 2042284812, 1101745716]])

end D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
