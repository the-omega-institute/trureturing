/- GID: D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508Strip.result; premises=D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripCertificate.finite_certificate
   digest: One-defect block of the canonical six-column strip transfer. -/

/-
admission_basis: open-problem-resolution (#32721; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229508Strip.result)
cl: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229508StripCertificate.transition_counts, HardinA229508StripData.cl.eq_1, HardinA229683Strip.counting_bridge, HardinA229683StripCertificate.cut_inherited, HardinA229683StripCertificate.cut_terminal, HardinA229683StripCertificate.transition_counts, HardinA229683StripData.cl, HardinA229683StripData.cl.eq_1
costOne: proof_shape=bind-only; consumers=HardinA229508StripCertificate.forward_one, HardinA229508StripCertificate.forward_one._proof_1, HardinA229508StripCertificate.forward_zeroth, HardinA229508StripCertificate.one_counts, HardinA229508StripCertificate.representative_counts, HardinA229508StripCertificate.transition_counts, HardinA229508StripData.T.eq_1, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.forward_two._proof_1, HardinA229683StripData.T, T
T: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229508Strip.result, HardinA229508StripCertificate.finite_certificate, HardinA229508StripCertificate.forward_one, HardinA229508StripCertificate.forward_zeroth, HardinA229508StripCertificate.transition_counts, HardinA229508StripData.T.eq_1, HardinA229683StripCertificate.finite_certificate, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.inherited_relation, HardinA229683StripData.T
initial: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229508Strip.result, HardinA229508StripCertificate.finite_certificate, HardinA229508StripCertificate.forward_one, HardinA229508StripCertificate.forward_zeroth, HardinA229508StripData.initial.eq_1, HardinA229683StripCertificate.finite_certificate, HardinA229683StripCertificate.forward_inherited, HardinA229683StripCertificate.forward_two, HardinA229683StripCertificate.inherited_relation, HardinA229683StripData.initial, HardinA229683StripData.initial.eq_1
terminal: proof_shape=bind-only; consumers=HardinA229508Strip.counting_bridge, HardinA229508Strip.result, HardinA229508StripData.terminal.eq_1
halfOne: proof_shape=bind-only; consumers=costOne
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Data.Matrix.Block

namespace D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData

open HardinA203981StripData (boundary)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row)

/-- The first sector allows one more defect. The second permits no more defects. -/
def cl (p : Row 3 6) (d : ℕ) : Fin 15 ⊕ Fin 15 :=
  if d = 0 then Sum.inr (boundary p) else Sum.inl (boundary p)

/-- The half-strip exact-one block with the target triple reversed. -/
def halfOne : Matrix (Fin 5) (Fin 5) ℤ :=
  D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip.T.submatrix
    (fun i => i.castAdd 5) (fun j => (Equiv.swap 1 3 j).natAdd 5)

/-- Count full-strip transitions of exact cost one by allocating the defects between parities. -/
def costOne : Matrix (Fin 15) (Fin 15) ℤ :=
  fun i j => HardinA203981StripData.classProduct HardinA203981StripData.halfZero halfOne i j +
    HardinA203981StripData.classProduct halfOne HardinA203981StripData.halfZero i j

/-- Both diagonal blocks are the zero-defect transfer. -/
def T : Matrix (Fin 15 ⊕ Fin 15) (Fin 15 ⊕ Fin 15) ℤ :=
  Matrix.fromBlocks HardinA203981StripData.T costOne 0 HardinA203981StripData.T

def initial : Fin 15 ⊕ Fin 15 → ℤ := Sum.elim HardinA203981StripData.initial 0

def terminal : Fin 15 ⊕ Fin 15 → ℤ := Sum.elim 0 1

end D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
