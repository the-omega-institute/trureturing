/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip.finite_certificate
   digest: Boundary classes and transfer weights for width-7 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229585Strip.result)
Row: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
Boundary: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
horizontal: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
antidiagonal: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
boundary: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
cross: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
zeroBudgetClass: proof_shape=bind-only; consumers=cl,HardinA229585StripOrbit.images
zeroBudgetTransferRow: proof_shape=bind-only; consumers=transfer_row29,transfer_row30,transfer_row33,transfer_row34,transfer_row37,transfer_row38,transfer_row39,transfer_row41,transfer_row54,transfer_row56,transfer_row57,transfer_row58,transfer_row61,transfer_row62,transfer_row65,transfer_row66
cl: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
transfer_row0: proof_shape=bind-only; consumers=T
transfer_row1: proof_shape=bind-only; consumers=T
transfer_row2: proof_shape=bind-only; consumers=T
transfer_row3: proof_shape=bind-only; consumers=T
transfer_row4: proof_shape=bind-only; consumers=T
transfer_row5: proof_shape=bind-only; consumers=T
transfer_row6: proof_shape=bind-only; consumers=T
transfer_row7: proof_shape=bind-only; consumers=T
transfer_row8: proof_shape=bind-only; consumers=T
transfer_row9: proof_shape=bind-only; consumers=T
transfer_row10: proof_shape=bind-only; consumers=T
transfer_row11: proof_shape=bind-only; consumers=T
transfer_row12: proof_shape=bind-only; consumers=T
transfer_row13: proof_shape=bind-only; consumers=T
transfer_row14: proof_shape=bind-only; consumers=T
transfer_row15: proof_shape=bind-only; consumers=T
transfer_row16: proof_shape=bind-only; consumers=T
transfer_row17: proof_shape=bind-only; consumers=T
transfer_row18: proof_shape=bind-only; consumers=T
transfer_row19: proof_shape=bind-only; consumers=T
transfer_row20: proof_shape=bind-only; consumers=T
transfer_row21: proof_shape=bind-only; consumers=T
transfer_row22: proof_shape=bind-only; consumers=T
transfer_row23: proof_shape=bind-only; consumers=T
transfer_row24: proof_shape=bind-only; consumers=T
transfer_row25: proof_shape=bind-only; consumers=T
transfer_row26: proof_shape=bind-only; consumers=T
transfer_row27: proof_shape=bind-only; consumers=T
transfer_row28: proof_shape=bind-only; consumers=T
transfer_row29: proof_shape=bind-only; consumers=T
transfer_row30: proof_shape=bind-only; consumers=T
transfer_row31: proof_shape=bind-only; consumers=T
transfer_row32: proof_shape=bind-only; consumers=T
transfer_row33: proof_shape=bind-only; consumers=T
transfer_row34: proof_shape=bind-only; consumers=T
transfer_row35: proof_shape=bind-only; consumers=T
transfer_row36: proof_shape=bind-only; consumers=T
transfer_row37: proof_shape=bind-only; consumers=T
transfer_row38: proof_shape=bind-only; consumers=T
transfer_row39: proof_shape=bind-only; consumers=T
transfer_row40: proof_shape=bind-only; consumers=T
transfer_row41: proof_shape=bind-only; consumers=T
transfer_row42: proof_shape=bind-only; consumers=T
transfer_row43: proof_shape=bind-only; consumers=T
transfer_row44: proof_shape=bind-only; consumers=T
transfer_row45: proof_shape=bind-only; consumers=T
transfer_row46: proof_shape=bind-only; consumers=T
transfer_row47: proof_shape=bind-only; consumers=T
transfer_row48: proof_shape=bind-only; consumers=T
transfer_row49: proof_shape=bind-only; consumers=T
transfer_row50: proof_shape=bind-only; consumers=T
transfer_row51: proof_shape=bind-only; consumers=T
transfer_row52: proof_shape=bind-only; consumers=T
transfer_row53: proof_shape=bind-only; consumers=T
transfer_row54: proof_shape=bind-only; consumers=T
transfer_row55: proof_shape=bind-only; consumers=T
transfer_row56: proof_shape=bind-only; consumers=T
transfer_row57: proof_shape=bind-only; consumers=T
transfer_row58: proof_shape=bind-only; consumers=T
transfer_row59: proof_shape=bind-only; consumers=T
transfer_row60: proof_shape=bind-only; consumers=T
transfer_row61: proof_shape=bind-only; consumers=T
transfer_row62: proof_shape=bind-only; consumers=T
transfer_row63: proof_shape=bind-only; consumers=T
transfer_row64: proof_shape=bind-only; consumers=T
transfer_row65: proof_shape=bind-only; consumers=T
transfer_row66: proof_shape=bind-only; consumers=T
transfer_row67: proof_shape=bind-only; consumers=T
transfer_row68: proof_shape=bind-only; consumers=T
transfer_row69: proof_shape=bind-only; consumers=T
transfer_row70: proof_shape=bind-only; consumers=T
transfer_row71: proof_shape=bind-only; consumers=T
T: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229585Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence

set_option profiler true

/-! Exact finite certificates for the width-seven one-defect strip. -/
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry (proper classOf)

abbrev Row := Fin 7 → Fin 3
abbrev Boundary := Fin 6 → Fin 3
def horizontal : Finset (Fin 7 × Fin 7) :=
  Finset.univ.image fun j : Fin 6 => (j.castSucc, j.succ)
def antidiagonal : Finset (Fin 7 × Fin 7) :=
  Finset.univ.image fun j : Fin 6 => (j.succ, j.castSucc)
def boundary (r : Row) : Boundary := Fin.tail r
def cross (p : Boundary) (r : Row) : ℕ :=
  bondDefects antidiagonal (Fin.cons 0 p) r
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 1 ∧ (Finset.univ.filter fun j : Fin 5 => p j.castSucc = p j.succ).card ≤ 1 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def zeroBudgetClass : Fin 16 → Fin 72 :=
  ![29, 30, 33, 34, 37, 38, 39, 41, 54, 56, 57, 58, 61, 62, 65, 66]

def cl (p : Boundary) (d : ℕ) : Fin 72 :=
  if proper p then
    if d = 1 then ⟨(classOf p).val, by omega⟩ else zeroBudgetClass (classOf p)
  else
  if d = 1 then (if p 0 = p 2 then (if p 0 = p 4 then (if p 1 = p 3 then (if p 1 = p 5 then (0) else (1)) else (if p 1 = p 5 then (4) else (5))) else (if p 0 = p 5 then (if p 1 = p 3 then (2) else (6)) else (if p 1 = p 3 then (3) else (7)))) else (if p 0 = p 3 then (if p 0 = p 5 then (if p 1 = p 4 then (8) else (10)) else (if p 1 = p 4 then (9) else (11))) else (if p 0 = p 4 then (if p 1 = p 5 then (12) else (13)) else (if p 0 = p 5 then (14) else (15))))) else (if p 0 = p 2 then (if p 0 = p 5 then (if p 1 = p 3 then (if p 0 = p 4 then (28) else (if p 1 = p 4 then (31) else (33))) else (if p 0 = p 3 then (if p 1 = p 4 then (24) else (26)) else (if p 0 = p 4 then (36) else (if p 1 = p 4 then (39) else (42))))) else (if p 1 = p 5 then (if p 0 = p 4 then (if p 1 = p 3 then (29) else (37)) else (if p 0 = p 3 then (27) else (if p 1 = p 3 then (34) else (if p 1 = p 4 then (40) else (43))))) else (if p 1 = p 3 then (if p 0 = p 4 then (30) else (if p 1 = p 4 then (32) else (35))) else (if p 0 = p 3 then (25) else (if p 0 = p 4 then (38) else (41)))))) else (if p 0 = p 3 then (if p 2 = p 4 then (if p 0 = p 5 then (if p 0 = p 1 then (16) else (if p 1 = p 2 then (44) else (57))) else (if p 0 = p 1 then (17) else (if p 1 = p 2 then (45) else (if p 1 = p 5 then (58) else (59))))) else (if p 1 = p 5 then (if p 0 = p 1 then (18) else (if p 0 = p 4 then (52) else (if p 1 = p 2 then (47) else (55)))) else (if p 0 = p 5 then (if p 1 = p 2 then (46) else (54)) else (if p 0 = p 1 then (19) else (if p 0 = p 4 then (53) else (56)))))) else (if p 0 = p 4 then (if p 2 = p 5 then (if p 0 = p 1 then (20) else (if p 1 = p 2 then (48) else (if p 1 = p 3 then (62) else (69)))) else (if p 1 = p 3 then (if p 0 = p 5 then (60) else (61)) else (if p 0 = p 1 then (21) else (if p 1 = p 2 then (49) else (68))))) else (if p 0 = p 5 then (if p 1 = p 3 then (if p 1 = p 4 then (63) else (65)) else (if p 0 = p 1 then (22) else (if p 1 = p 2 then (50) else (70)))) else (if p 1 = p 3 then (if p 1 = p 4 then (64) else (if p 1 = p 5 then (66) else (67))) else (if p 0 = p 1 then (23) else (if p 1 = p 2 then (51) else (71))))))))

@[noinline]
private def zeroBudgetTransferRow (i : Fin 16) : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 0), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 1), 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 2), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 3), 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 4), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 5), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 6), 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 7), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 8), 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 9), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 10), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 11), 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 12), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 13), 0, 0, (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 14), (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table i 15), 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row0 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 0)
    (![1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 5, 2, 2, 2, 2, 4, 4, 3, 4, 2, 2, 3, 2, 3, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 1, 1, 2, 0, 2, 5, 5, 1, 3, 4, 4, 0, 0, 3, 3, 3, 2, 2, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row1 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 1)
    (![1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 4, 3, 4, 0, 0, 4, 2, 4, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 4, 1, 4, 3, 3, 1, 2, 4, 4, 3, 3, 7, 7, 1, 2, 2, 2, 2] : Fin 56 → ℤ)

@[noinline]
private def transfer_row2 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 2)
    (![0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 4, 4, 1, 5, 5, 3, 3, 4, 4, 2, 1, 5, 5, 4, 3, 4, 2, 2, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0, 4, 2, 4, 2, 2, 2, 1, 4, 4, 3, 3, 1, 1, 2, 1, 1, 1, 1] : Fin 56 → ℤ)

@[noinline]
private def transfer_row3 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 3)
    (![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 5, 0, 0, 2, 2, 3, 3, 5, 5, 2, 2, 2, 1, 1, 2, 2, 0, 0, 2, 2, 2, 2, 2, 2, 5, 0, 5, 2, 2, 2, 3, 2, 2, 0, 0, 2, 2, 3, 1, 1, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row4 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 4)
    (![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 4, 1, 1, 2, 2, 4, 4, 2, 4, 0, 0, 2, 2, 2, 2, 2, 0, 0, 1, 1, 2, 2, 0, 0, 1, 1, 5, 0, 5, 3, 3, 1, 3, 4, 4, 2, 2, 7, 7, 1, 2, 2, 2, 2] : Fin 56 → ℤ)

@[noinline]
private def transfer_row5 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 5)
    (![2, 2, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 4, 1, 1, 2, 2, 4, 4, 2, 4, 0, 0, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 0, 0, 3, 1, 3, 6, 6, 1, 2, 4, 4, 1, 1, 3, 3, 3, 2, 2, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row6 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 6)
    (![1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 0, 3, 3, 2, 2, 2, 2, 2, 0, 4, 4, 4, 2, 4, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3, 4, 4, 4, 2, 0, 5, 5, 2, 2, 1, 1, 2, 1, 1, 1, 1] : Fin 56 → ℤ)

@[noinline]
private def transfer_row7 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 7)
    (![2, 2, 2, 2, 0, 0, 1, 1, 2, 2, 2, 2, 2, 3, 3, 0, 0, 1, 1, 2, 2, 3, 3, 1, 2, 1, 0, 0, 3, 3, 1, 1, 2, 2, 3, 3, 2, 2, 7, 1, 7, 3, 3, 3, 2, 1, 1, 0, 0, 3, 3, 2, 0, 0, 1, 1] : Fin 56 → ℤ)

@[noinline]
private def transfer_row8 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 8)
    (![4, 4, 4, 4, 0, 0, 2, 2, 1, 1, 1, 1, 1, 4, 4, 0, 0, 3, 3, 1, 1, 4, 4, 4, 1, 4, 0, 0, 3, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 4, 4, 4, 3, 1, 3, 3, 0, 0, 7, 7, 1, 0, 0, 2, 2] : Fin 56 → ℤ)

@[noinline]
private def transfer_row9 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 9)
    (![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 1, 1, 3, 3, 1, 0, 4, 4, 6, 1, 6, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3, 3, 7, 7, 1, 0, 6, 6, 1, 1, 4, 4, 1, 2, 2, 2, 2] : Fin 56 → ℤ)

@[noinline]
private def transfer_row10 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 10)
    (![4, 4, 4, 4, 0, 0, 2, 2, 0, 0, 0, 0, 2, 5, 5, 1, 1, 6, 6, 1, 2, 4, 4, 3, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0, 2, 2, 2, 4, 4, 2, 1, 6, 6, 2, 2, 3, 3, 3, 1, 1, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row11 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 11)
    (![2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 2, 6, 6, 1, 1, 6, 6, 1, 2, 4, 4, 3, 1, 3, 1, 1, 0, 0, 2, 2, 1, 1, 0, 0, 2, 2, 6, 0, 6, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3, 2, 1, 1, 1, 1] : Fin 56 → ℤ)

@[noinline]
private def transfer_row12 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 12)
    (![0, 0, 0, 0, 2, 2, 2, 2, 1, 1, 1, 1, 3, 5, 5, 0, 0, 2, 2, 3, 3, 5, 5, 6, 1, 6, 2, 2, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 3, 0, 3, 5, 5, 1, 3, 2, 2, 0, 0, 2, 2, 3, 2, 2, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row13 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 13)
    (![0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 2, 2, 2, 3, 3, 3, 3, 7, 7, 1, 2, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 6, 1, 6, 3, 3, 1, 2, 1, 1, 3, 3, 4, 4, 1, 2, 2, 2, 2] : Fin 56 → ℤ)

@[noinline]
private def transfer_row14 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 14)
    (![2, 2, 2, 2, 0, 0, 2, 2, 2, 2, 2, 2, 2, 6, 6, 3, 3, 3, 3, 3, 2, 4, 4, 7, 1, 7, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1, 2, 1, 6, 6, 3, 3, 3, 3, 2, 1, 1, 1, 1] : Fin 56 → ℤ)

@[noinline]
private def transfer_row15 : Fin 72 → ℤ :=
  Fin.append (D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.table 15)
    (![2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 2, 2, 4, 4, 4, 1, 1, 3, 3, 3, 2, 8, 8, 5, 1, 5, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 0, 3, 2, 2, 2, 3, 3, 3, 0, 0, 3, 3, 3, 1, 1, 0, 0] : Fin 56 → ℤ)

@[noinline]
private def transfer_row16 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row17 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row18 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row19 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row20 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row21 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row22 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row23 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row24 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row25 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row26 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row27 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row28 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 4, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row29 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 0

@[noinline]
private def transfer_row30 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 1

@[noinline]
private def transfer_row31 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row32 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row33 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 2

@[noinline]
private def transfer_row34 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 3

@[noinline]
private def transfer_row35 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 2, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row36 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row37 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 4

@[noinline]
private def transfer_row38 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 5

@[noinline]
private def transfer_row39 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 6

@[noinline]
private def transfer_row40 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row41 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 7

@[noinline]
private def transfer_row42 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row43 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row44 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 3, 0, 0, 1, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row45 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 3, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row46 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row47 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row48 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row49 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row50 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 3, 0, 0, 1, 1, 0, 0, 3, 3, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row51 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 3, 0, 0, 2, 2, 0, 0, 3, 3, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row52 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row53 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row54 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 8

@[noinline]
private def transfer_row55 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row56 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 9

@[noinline]
private def transfer_row57 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 10

@[noinline]
private def transfer_row58 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 11

@[noinline]
private def transfer_row59 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row60 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row61 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 12

@[noinline]
private def transfer_row62 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 13

@[noinline]
private def transfer_row63 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row64 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 2, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row65 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 14

@[noinline]
private def transfer_row66 : Fin 72 → ℤ :=
  zeroBudgetTransferRow 15

@[noinline]
private def transfer_row67 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row68 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row69 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row70 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[noinline]
private def transfer_row71 : Fin 72 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]

def T : Matrix (Fin 72) (Fin 72) ℤ :=
  ![transfer_row0, transfer_row1, transfer_row2, transfer_row3, transfer_row4, transfer_row5, transfer_row6, transfer_row7, transfer_row8, transfer_row9, transfer_row10, transfer_row11, transfer_row12, transfer_row13, transfer_row14, transfer_row15, transfer_row16, transfer_row17, transfer_row18, transfer_row19, transfer_row20, transfer_row21, transfer_row22, transfer_row23, transfer_row24, transfer_row25, transfer_row26, transfer_row27, transfer_row28, transfer_row29, transfer_row30, transfer_row31, transfer_row32, transfer_row33, transfer_row34, transfer_row35, transfer_row36, transfer_row37, transfer_row38, transfer_row39, transfer_row40, transfer_row41, transfer_row42, transfer_row43, transfer_row44, transfer_row45, transfer_row46, transfer_row47, transfer_row48, transfer_row49, transfer_row50, transfer_row51, transfer_row52, transfer_row53, transfer_row54, transfer_row55, transfer_row56, transfer_row57, transfer_row58, transfer_row59, transfer_row60, transfer_row61, transfer_row62, transfer_row63, transfer_row64, transfer_row65, transfer_row66, transfer_row67, transfer_row68, transfer_row69, transfer_row70, transfer_row71]
def initial : Fin 72 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 6, 6, 6, 12, 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 6, 6, 12, 12, 6, 6, 12, 12, 12, 12, 12]
def terminal : Fin 72 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 11 → Fin 72 → ℤ :=
  ![initial,
    ![468, 468, 396, 396, 432, 432, 324, 324, 216, 216, 324, 324, 360, 360, 396, 396, 288, 288, 252, 252, 180, 180, 252, 252, 252, 252, 288, 288, 468, 1422, 1422, 288, 288, 1494, 1494, 396, 432, 1380, 1380, 1518, 324, 1518, 252, 252, 252, 252, 180, 180, 252, 252, 288, 288, 180, 180, 1644, 216, 1644, 1470, 1470, 324, 360, 1428, 1428, 252, 252, 1470, 1470, 396, 252, 252, 180, 180],
    ![15588, 15588, 12708, 12708, 14328, 14328, 10188, 10188, 5868, 5868, 9468, 9468, 11628, 11628, 12348, 12348, 8028, 8028, 6768, 6768, 5328, 5328, 7308, 7308, 7308, 7308, 8568, 8568, 15588, 88158, 88158, 9432, 9432, 84786, 84786, 12708, 14328, 82068, 82068, 76386, 10188, 76386, 8172, 8172, 6624, 6624, 4932, 4932, 7812, 7812, 8064, 8064, 5112, 5112, 67386, 5868, 67386, 73482, 73482, 9468, 11628, 77226, 77226, 7992, 7992, 82722, 82722, 12348, 8028, 8028, 5148, 5148],
    ![502092, 502092, 406404, 406404, 461808, 461808, 325836, 325836, 180684, 180684, 295596, 295596, 372060, 372060, 391284, 391284, 246132, 246132, 205848, 205848, 167400, 167400, 226908, 226908, 230148, 230148, 270432, 270432, 502092, 4165146, 4165146, 302832, 302832, 3811626, 3811626, 406404, 461808, 3857472, 3857472, 3317130, 325836, 3317130, 262548, 262548, 203688, 203688, 151740, 151740, 248508, 248508, 252072, 252072, 158760, 158760, 2613942, 180684, 2613942, 3124530, 3124530, 295596, 372060, 3457494, 3457494, 254448, 254448, 3689838, 3689838, 391284, 257148, 257148, 161460, 161460],
    ![16061652, 16061652, 12983652, 12983652, 14776992, 14776992, 10414332, 10414332, 5729292, 5729292, 9396972, 9396972, 11885292, 11885292, 12474972, 12474972, 7789932, 7789932, 6505272, 6505272, 5325912, 5325912, 7200252, 7200252, 7336332, 7336332, 8620992, 8620992, 16061652, 175783230, 175783230, 9681768, 9681768, 156355650, 156355650, 12983652, 14776992, 162521856, 162521856, 133686882, 10414332, 133686882, 8397108, 8397108, 6461856, 6461856, 4810428, 4810428, 7933788, 7933788, 8023536, 8023536, 5042088, 5042088, 98540334, 5729292, 98540334, 124649658, 124649658, 9396972, 11885292, 141985278, 141985278, 8120088, 8120088, 150989130, 150989130, 12474972, 8217612, 8217612, 5139612, 5139612],
    ![513127548, 513127548, 414696996, 414696996, 472115952, 472115952, 332673804, 332673804, 182738916, 182738916, 299859084, 299859084, 379600020, 379600020, 398289636, 398289636, 248354748, 248354748, 207343152, 207343152, 169963920, 169963920, 229665132, 229665132, 234243252, 234243252, 275254848, 275254848, 513127548, 6976968210, 6976968210, 309274848, 309274848, 6095351898, 6095351898, 414696996, 472115952, 6444450072, 6444450072, 5153350410, 332673804, 5153350410, 268263252, 268263252, 206137872, 206137872, 153425340, 153425340, 253381932, 253381932, 256116168, 256116168, 160866000, 160866000, 3631204242, 182738916, 3631204242, 4776355674, 4776355674, 299859084, 379600020, 5542359714, 5542359714, 259296552, 259296552, 5879579238, 5879579238, 398289636, 262479852, 262479852, 164049300, 164049300],
    ![16389124308, 16389124308, 13244743188, 13244743188, 15079417488, 15079417488, 10625329548, 10625329548, 5834924748, 5834924748, 9575394588, 9575394588, 12123686988, 12123686988, 12719775708, 12719775708, 7929370908, 7929370908, 6619664088, 6619664088, 5427486648, 5427486648, 7333282188, 7333282188, 7480948428, 7480948428, 8790655248, 8790655248, 16389124308, 266337162558, 266337162558, 9877955832, 9877955832, 229834333386, 229834333386, 13244743188, 15079417488, 245852608104, 245852608104, 192794344938, 10625329548, 192794344938, 8568249012, 8568249012, 6582298464, 6582298464, 4898900412, 4898900412, 8092503612, 8092503612, 8179100064, 8179100064, 5136773112, 5136773112, 131454649062, 5834924748, 131454649062, 177959142450, 177959142450, 9575394588, 12123686988, 209192234742, 209192234742, 8281154232, 8281154232, 221544506970, 221544506970, 12719775708, 8383217148, 8383217148, 5238836028, 5238836028],
    ![523440682812, 523440682812, 423011490804, 423011490804, 481612007088, 481612007088, 339354139356, 339354139356, 186347997684, 186347997684, 305810458236, 305810458236, 387206381700, 387206381700, 406239650244, 406239650244, 253233508572, 253233508572, 211404832848, 211404832848, 173338295760, 173338295760, 234200240028, 234200240028, 238924947348, 238924947348, 280753623072, 280753623072, 523440682812, 9895679269794, 9895679269794, 315484057872, 315484057872, 8463282228018, 8463282228018, 423011490804, 481612007088, 9130414020264, 9130414020264, 7058237756130, 339354139356, 7058237756130, 273655382148, 273655382148, 210218079168, 210218079168, 156454349580, 156454349580, 258458444028, 258458444028, 261220126392, 261220126392, 164052818640, 164052818640, 4692984116634, 186347997684, 4692984116634, 6495347614482, 6495347614482, 305810458236, 387206381700, 7708948923978, 7708948923978, 264482010648, 264482010648, 8153973806166, 8153973806166, 406239650244, 267743921148, 267743921148, 167314729140, 167314729140],
    ![16717676084532, 16717676084532, 13510146476772, 13510146476772, 15381756101232, 15381756101232, 10838306510172, 10838306510172, 5951538816012, 5951538816012, 9766927227852, 9766927227852, 12366598031532, 12366598031532, 12974456835612, 12974456835612, 8087689141452, 8087689141452, 6751769158152, 6751769158152, 5536051549992, 5536051549992, 7479830337372, 7479830337372, 7630776902412, 7630776902412, 8966696885712, 8966696885712, 16717676084532, 360422252803134, 360422252803134, 10075940853768, 10075940853768, 306160575184098, 306160575184098, 13510146476772, 15381756101232, 332435249945496, 332435249945496, 254194329418722, 10838306510172, 254194329418722, 8740020870468, 8740020870468, 6713904472416, 6713904472416, 4996801621548, 4996801621548, 8254646750988, 8254646750988, 8342827037136, 8342827037136, 5239488681288, 5239488681288, 165681507777462, 5951538816012, 165681507777462, 233372680728282, 233372680728282, 9766927227852, 12366598031532, 279033190203078, 279033190203078, 8447018289048, 8447018289048, 294859816352730, 294859816352730, 12974456835612, 8551209619692, 8551209619692, 5343680011932, 5343680011932],
    ![533929311396828, 533929311396828, 431487104564196, 431487104564196, 491262721641072, 491262721641072, 346153925052684, 346153925052684, 190080011418516, 190080011418516, 311935870410444, 311935870410444, 394964425083780, 394964425083780, 414378077243076, 414378077243076, 258304163608908, 258304163608908, 215637573853152, 215637573853152, 176810269534560, 176810269534560, 238890511449612, 238890511449612, 243711718220052, 243711718220052, 286378307975808, 286378307975808, 533929311396828, 12928380113605122, 12928380113605122, 321805471987008, 321805471987008, 10923457341345786, 10923457341345786, 431487104564196, 491262721641072, 11921280832853640, 11921280832853640, 9037258549110090, 346153925052684, 9037258549110090, 279138882231252, 279138882231252, 214428464484192, 214428464484192, 159587648077500, 159587648077500, 263636923833612, 263636923833612, 266453102362248, 266453102362248, 167338627276320, 167338627276320, 5796065596688010, 190080011418516, 5796065596688010, 8281429690699242, 8281429690699242, 311935870410444, 394964425083780, 9960119574896250, 9960119574896250, 269780834108952, 269780834108952, 10517119990052310, 10517119990052310, 414378077243076, 273108566091852, 273108566091852, 170666359259220, 170666359259220],
    ![17052635925999828, 17052635925999828, 13780835905428468, 13780835905428468, 15689950460116848, 15689950460116848, 11055464973662508, 11055464973662508, 6070774319860428, 6070774319860428, 9962606796051708, 9962606796051708, 12614374361003148, 12614374361003148, 13234406816623068, 13234406816623068, 8249716162820988, 8249716162820988, 6887030696938008, 6887030696938008, 5646965785698168, 5646965785698168, 7629683707201068, 7629683707201068, 7783664953091148, 7783664953091148, 9146350418974128, 9146350418974128, 17052635925999828, 458169569640111294, 458169569640111294, 10277823943809432, 10277823943809432, 385451978734502298, 385451978734502298, 13780835905428468, 15689950460116848, 422387844561109944, 422387844561109944, 317976584974148538, 11055464973662508, 317976584974148538, 8915138477926452, 8915138477926452, 6848415349713504, 6848415349713504, 5096909368549692, 5096909368549692, 8420036471084412, 8420036471084412, 8509978900980864, 8509978900980864, 5344460371970712, 5344460371970712, 201228444856931094, 6070774319860428, 201228444856931094, 290936129371666146, 290936129371666146, 9962606796051708, 12614374361003148, 351588743122666662, 351588743122666662, 8616260392542072, 8616260392542072, 371023978535390970, 371023978535390970, 13234406816623068, 8722541884811868, 8722541884811868, 5450741864240508, 5450741864240508]]

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
