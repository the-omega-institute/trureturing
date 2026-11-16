/- GID: D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584Strip.finite_certificate
   digest: Boundary classes and transfer weights for width-6 strips. -/

/-
admission_basis: open-problem-resolution (#30580; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229584Strip.result)
Row: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
Boundary: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
horizontal: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
antidiagonal: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
boundary: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
cross: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
Valid: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
decidableValid: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
cl: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
T: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
initial: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
terminal: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
W: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
decidableCanonical: proof_shape=bind-only; consumers=HardinA229584Strip.finite_certificate
-/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
open DefectTransfer (bondDefects)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

abbrev Row := Fin 6 → Fin 3
abbrev Boundary := Fin 5 → Fin 3
def horizontal : Finset (Fin 6 × Fin 6) :=
  Finset.univ.image fun j : Fin 5 => (j.castSucc, j.succ)
def antidiagonal : Finset (Fin 6 × Fin 6) :=
  Finset.univ.image fun j : Fin 5 => (j.succ, j.castSucc)
def boundary (r : Row) : Boundary := Fin.tail r
def cross (p : Boundary) (r : Row) : ℕ :=
  bondDefects antidiagonal (Fin.cons 0 p) r
def Valid (p : Boundary) (d : ℕ) : Prop :=
  d ≤ 1 ∧ (Finset.univ.filter fun j : Fin 4 => p j.castSucc = p j.succ).card ≤ 1 - d
private instance decidableValid (p : Boundary) (d : ℕ) : Decidable (Valid p d) :=
  inferInstanceAs (Decidable (_ ∧ _))
def cl (p : Boundary) (d : ℕ) : Fin 32 :=
  if d = 1 then (if p 0 = p 2 then (if p 0 = p 4 then (if p 1 = p 3 then (0) else (2)) else (if p 1 = p 3 then (1) else (3))) else (if p 0 = p 3 then (if p 1 = p 4 then (4) else (5)) else (if p 0 = p 4 then (6) else (7)))) else (if p 0 = p 3 then (if p 1 = p 4 then (if p 0 = p 2 then (12) else (if p 1 = p 2 then (20) else (25))) else (if p 0 = p 1 then (if p 2 = p 4 then (8) else (9)) else (if p 0 = p 2 then (13) else (if p 0 = p 4 then (24) else (if p 1 = p 2 then (21) else (26)))))) else (if p 0 = p 2 then (if p 1 = p 3 then (if p 0 = p 4 then (14) else (if p 1 = p 4 then (15) else (16))) else (if p 0 = p 4 then (17) else (if p 1 = p 4 then (18) else (19)))) else (if p 0 = p 4 then (if p 0 = p 1 then (10) else (if p 1 = p 2 then (22) else (if p 1 = p 3 then (27) else (30)))) else (if p 1 = p 3 then (if p 1 = p 4 then (28) else (29)) else (if p 0 = p 1 then (11) else (if p 1 = p 2 then (23) else (31)))))))
def T : Matrix (Fin 32) (Fin 32) ℤ :=
  ![![5, 5, 4, 4, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4, 0, 0, 2, 2, 1, 5, 5, 5, 3, 5, 2, 2],
    ![3, 3, 3, 3, 2, 2, 3, 3, 0, 0, 1, 1, 4, 4, 5, 3, 5, 5, 5, 3, 2, 2, 2, 2, 2, 4, 4, 2, 3, 2, 1, 1],
    ![4, 4, 4, 4, 1, 1, 3, 3, 2, 2, 1, 1, 0, 0, 2, 4, 2, 0, 0, 4, 1, 1, 2, 2, 1, 6, 6, 5, 3, 5, 2, 2],
    ![2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 1, 1, 4, 4, 3, 2, 3, 4, 4, 2, 3, 3, 3, 3, 3, 5, 5, 3, 2, 3, 1, 1],
    ![1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2, 2, 2, 2, 4, 1, 4, 6, 6, 1, 3, 3, 3, 3, 3, 5, 5, 7, 1, 7, 2, 2],
    ![2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 2, 2, 0, 0, 7, 2, 7, 4, 4, 2, 2, 2, 1, 1, 2, 4, 4, 4, 3, 4, 1, 1],
    ![3, 3, 3, 3, 1, 1, 3, 3, 0, 0, 2, 2, 2, 2, 5, 3, 5, 5, 5, 3, 1, 1, 1, 1, 1, 6, 6, 2, 3, 2, 2, 2],
    ![4, 4, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 2, 2, 4, 4, 4, 8, 8, 2, 0, 0, 1, 1, 2, 2, 2, 4, 3, 4, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 4, 4, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 4, 4, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 5, 4, 4, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 3, 3, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 3, 3, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 3, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 1, 0, 0]]
def initial : Fin 32 → ℤ := ![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 6, 6, 6, 12, 6, 12, 12]
def terminal : Fin 32 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def W : Fin 8 → Fin 32 → ℤ :=
  ![![12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 6, 12, 6, 6, 6, 12, 12, 12, 12, 12, 12, 6, 6, 6, 12, 6, 12, 12],
    ![288, 288, 252, 252, 180, 180, 252, 252, 180, 180, 144, 144, 180, 180, 804, 288, 804, 834, 834, 252, 144, 144, 180, 180, 180, 954, 954, 810, 252, 810, 144, 144],
    ![6120, 6120, 5328, 5328, 3528, 3528, 5220, 5220, 3240, 3240, 2808, 2808, 3816, 3816, 31812, 6120, 31812, 30540, 30540, 5328, 2736, 2736, 3636, 3636, 3528, 28500, 28500, 29442, 5220, 29442, 2916, 2916],
    ![128052, 128052, 111492, 111492, 72972, 72972, 108792, 108792, 66096, 66096, 57888, 57888, 79848, 79848, 970530, 128052, 970530, 904818, 904818, 111492, 56412, 56412, 75672, 75672, 72972, 769146, 769146, 873804, 108792, 873804, 60588, 60588],
    ![2673828, 2673828, 2328192, 2328192, 1521360, 1521360, 2270412, 2270412, 1375380, 1375380, 1206144, 1206144, 1667340, 1667340, 26634390, 2673828, 26634390, 24439764, 24439764, 2328192, 1175724, 1175724, 1579140, 1579140, 1521360, 19682196, 19682196, 23650482, 2270412, 23650482, 1263924, 1263924],
    ![55816740, 55816740, 48602088, 48602088, 31752288, 31752288, 47391840, 47391840, 28698300, 28698300, 25171128, 25171128, 34806276, 34806276, 688994430, 55816740, 688994430, 625991628, 625991628, 48602088, 24537636, 24537636, 32962536, 32962536, 31752288, 486524004, 486524004, 606623268, 47391840, 606623268, 26381376, 26381376],
    ![1165146192, 1165146192, 1014545772, 1014545772, 662795532, 662795532, 989271072, 989271072, 599027076, 599027076, 525414168, 525414168, 726563988, 726563988, 17158850556, 1165146192, 17158850556, 15484831014, 15484831014, 1014545772, 512195112, 512195112, 688070232, 688070232, 662795532, 11735324790, 11735324790, 15020284764, 989271072, 15020284764, 550688868, 550688868],
    ![24321728268, 24321728268, 21178039932, 21178039932, 13835412540, 13835412540, 20650414572, 20650414572, 12504235680, 12504235680, 10967650344, 10967650344, 15166589400, 15166589400, 416138142246, 24321728268, 416138142246, 373702732554, 373702732554, 21178039932, 10691724204, 10691724204, 14363037900, 14363037900, 13835412540, 277936960938, 277936960938, 362748285894, 20650414572, 362748285894, 11495275704, 11495275704]]

private instance decidableCanonical (p : Boundary) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance


end D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
