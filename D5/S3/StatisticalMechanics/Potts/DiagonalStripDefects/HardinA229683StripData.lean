/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229683StripCertificate.finite_certificate
   digest: The two-defect block of the canonical six-column strip transfer. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229683Strip.result)
cl: proof_shape=bind-only; consumers=HardinA229683Strip.counting_bridge, HardinA229683StripCertificate.cut_inherited, HardinA229683StripCertificate.cut_terminal, HardinA229683StripCertificate.transition_counts, HardinA229683StripCertificate.transition_counts._simp_1, HardinA229683StripData.cl.eq_1
costTwo: proof_shape=bind-only; consumers=HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.forward_two._proof_1, HardinA229683StripCertificate.representative_counts, HardinA229683StripCertificate.two_counts, T
T: proof_shape=bind-only; consumers=HardinA229683Strip.counting_bridge, HardinA229683Strip.result, HardinA229683StripCertificate.finite_certificate, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.transition_counts
initial: proof_shape=bind-only; consumers=HardinA229683Strip.counting_bridge, HardinA229683Strip.result, HardinA229683StripCertificate.finite_certificate, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripData.initial.eq_1
terminal: proof_shape=bind-only; consumers=HardinA229683Strip.counting_bridge, HardinA229683Strip.result, HardinA229683StripData.terminal.eq_1
halfTwo: proof_shape=bind-only; consumers=costTwo
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData

open HardinA203981StripData (boundary)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row)

/-- A zero remaining budget selects the new sector, after both inherited sectors. -/
def cl (p : Row 3 6) (d : ℕ) : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) :=
  if d = 0 then Sum.inr (boundary p) else Sum.inl (HardinA229508StripData.cl p (d - 1))

/-- The half-strip exact-two block with the target triple reversed. -/
def halfTwo : Matrix (Fin 5) (Fin 5) ℤ :=
  D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData.T.submatrix
    (fun i => i.castAdd 10) (fun j => (Equiv.swap 1 3 j).natAdd 10)

/-- Count full-strip transitions of exact cost two by allocating the defects between parities. -/
def costTwo : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => HardinA203981StripData.classProduct HardinA203981StripData.halfZero halfTwo i j +
    HardinA203981StripData.classProduct HardinA229508StripData.halfOne HardinA229508StripData.halfOne i j +
    HardinA203981StripData.classProduct halfTwo HardinA203981StripData.halfZero i j

/-- The inherited block plus a sector for a spent budget of two defects. -/
def T : Matrix ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) ℤ :=
  Matrix.fromBlocks HardinA229508StripData.T (Matrix.fromRows costTwo HardinA229508StripData.costOne) 0 HardinA203981StripData.T

def initial : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) → ℤ := Sum.elim HardinA229508StripData.initial 0

def terminal : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) → ℤ := Sum.elim 0 1

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
