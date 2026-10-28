/- GID: D5/S3/Quantum/Matrix/HsfContractionGrams
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfContractionGrams
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: numeric-reduction; basis=consumer; consumer=D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_nonneg
   digest: Four exact integer Gram matrices for the full contraction cubic certificate. -/

/-
admission_basis: escape-witness
proof_shape: grams_posSemidef: content
escape_witness: grams_posSemidef
The exact rational LDL decompositions are reconstructed by kernel-checked arithmetic.
The matrices are used in the arbitrary-dimensional full-contraction trace certificate.
-/

module
public import D5.S3.Quantum.Matrix.WeightedTraceGram

@[expose] public section
noncomputable section
open Matrix
namespace D5.S3.Quantum.Matrix.HsfContractionGrams

/-- Fixed integer matrix in the ordered eight-word basis. -/
def M00 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 526, 265, 130, 178, 96, 155, 164],
  ![0, 265, 276, 32, 7, (-93), 8, (-52)],
  ![0, 130, 32, 300, 68, 82, 174, 108],
  ![0, 178, 7, 68, 182, 138, 96, 184],
  ![0, 96, (-93), 82, 138, 220, 82, 222],
  ![0, 155, 8, 174, 96, 82, 232, 124],
  ![0, 164, (-52), 108, 184, 222, 124, 280]]

private def LM00 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, (265/526), 1, 0, 0, 0, 0, 0],
  ![0, (65/263), (-17618/74951), 1, 0, 0, 0, 0],
  ![0, (89/263), (-43488/74951), (171397/9743538), 1, 0, 0, 0],
  ![0, (48/263), (-74358/74951), (469277/4871769), (112294636/359113417), 1, 0, 0],
  ![0, (155/526), (-36867/74951), (4467709/9743538), (3815692/359113417), (-9894421349/18893799758), 1, 0],
  ![0, (82/263), (-70812/74951), (671243/4871769), (242422042/359113417), (7092344527/9446899879), (2025274462/12710735535), 1]]

private def dM00 : Fin 8 → ℝ := ![0, 526, (74951/526), (19487076/74951), (359113417/4871769), (18893799758/359113417), (1563420470805/18893799758), (133019812452/4236911845)]

private theorem reconstruction_M00 :
    M00 = LM00 * Matrix.diagonal dM00 * (LM00)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M00, LM00, dM00, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem psd_M00 : M00.PosSemidef := by
  rw [reconstruction_M00]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [dM00]

/-- Fixed integer matrix in the ordered eight-word basis. -/
def M01 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![3456, (-263), 2058, 250, (-94), 1675, 135, (-140)],
  ![(-263), 526, (-102), 14, 178, (-57), (-74), 164],
  ![2058, (-102), 1354, 58, (-84), 961, 6, (-130)],
  ![250, 14, 58, 300, 68, 114, 174, 108],
  ![(-94), 178, (-84), 68, 182, 32, 96, 184],
  ![1675, (-57), 961, 114, 32, 1056, 98, 82],
  ![135, (-74), 6, 174, 96, 98, 232, 124],
  ![(-140), 164, (-130), 108, 184, 82, 124, 280]]

private def LM01 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![(-263/3456), 1, 0, 0, 0, 0, 0, 0],
  ![(343/576), (188742/1748687), 1, 0, 0, 0, 0, 0],
  ![(125/1728), (114134/1748687), (-82569521/107190163), 1, 0, 0, 0, 0],
  ![(-47/1728), (590446/1748687), (-40625838/107190163), (298599152/2218998599), 1, 0, 0, 0],
  ![(1675/3456), (243533/1748687), (-77020849/214380326), (-4897899773/22189985990), (47953310003/111391328985), 1, 0, 0],
  ![(5/128), (-220239/1748687), (-59029020/107190163), (6237841498/11094992995), (88693111499/111391328985), (943067038733/21148475779691), 1, 0],
  ![(-35/864), (529964/1748687), (-55243759/107190163), (3186128153/11094992995), (35677127178/37130442995), (8620564236168/21148475779691), (2132383720848/366981353895953), 1]]

private def dM01 : Fin 8 → ℝ := ![3456, (1748687/3456), (214380326/1748687), (22189985990/107190163), (222782657970/2218998599), (21148475779691/111391328985), (1100944061687859/21148475779691), (19809726435730820/366981353895953)]

private theorem reconstruction_M01 :
    M01 = LM01 * Matrix.diagonal dM01 * (LM01)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M01, LM01, dM01, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem psd_M01 : M01.PosSemidef := by
  rw [reconstruction_M01]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [dM01]

/-- Fixed integer matrix in the ordered eight-word basis. -/
def M10 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![864, 948, 492, 316, 472, 576, 358, 484],
  ![948, 1108, 714, 412, 530, 640, 439, 494],
  ![492, 714, 936, 432, 330, 430, 302, 208],
  ![316, 412, 432, 282, 206, 272, 158, 178],
  ![472, 530, 330, 206, 400, 336, 170, 272],
  ![576, 640, 430, 272, 336, 480, 260, 351],
  ![358, 439, 302, 158, 170, 260, 218, 184],
  ![484, 494, 208, 178, 272, 351, 184, 358]]

private def LM10 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![(79/72), 1, 0, 0, 0, 0, 0, 0],
  ![(41/72), (95/37), 1, 0, 0, 0, 0, 0],
  ![(79/216), (1175/1221), (4687/11580), 1, 0, 0, 0, 0],
  ![(59/108), (218/1221), (418/2895), (202152/1473917), 1, 0, 0, 0],
  ![(2/3), (48/407), (1507/3860), (1316093/4421751), (2934487/74246736), 1, 0, 0],
  ![(179/432), (1663/2442), (-284/2895), (-579878/4421751), (-130961729/593973888), (6182609939/12672416248), 1, 0],
  ![(121/216), (-667/1221), (382/2895), (1623944/4421751), (14893135/296986944), (1570255931/6336208124), (473420793582/756765771589), 1]]

private def dM10 : Fin 8 → ℝ := ![864, (407/6), (7720/37), (1473917/21230), (197991296/1473917), (1584052031/27842526), (756765771589/50689664992), (66528901274057/1513531543178)]

private theorem reconstruction_M10 :
    M10 = LM10 * Matrix.diagonal dM10 * (LM10)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M10, LM10, dM10, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem psd_M10 : M10.PosSemidef := by
  rw [reconstruction_M10]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [dM10]

/-- Fixed integer matrix in the ordered eight-word basis. -/
def M11 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![2424, 394, 1688, 462, 372, 1482, 366, 334],
  ![394, 1108, (-2), 296, 530, 72, 210, 494],
  ![1688, (-2), 1356, 326, 130, 1016, 232, 84],
  ![462, 296, 326, 282, 206, 244, 158, 178],
  ![372, 530, 130, 206, 400, 188, 170, 272],
  ![1482, 72, 1016, 244, 188, 1058, 226, 172],
  ![366, 210, 232, 158, 170, 226, 218, 184],
  ![334, 494, 84, 178, 272, 172, 184, 358]]

private def LM11 : Matrix (Fin 8) (Fin 8) ℝ :=
  ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![(197/1212), 1, 0, 0, 0, 0, 0, 0],
  ![(211/303), (-167480/632639), 1, 0, 0, 0, 0, 0],
  ![(77/404), (133869/632639), (9925817/16980675), 1, 0, 0, 0, 0],
  ![(31/202), (284538/632639), (-500681/11320450), (327041229/938322623), 1, 0, 0, 0],
  ![(247/404), (-102345/632639), (-19209901/33961350), (278272003/938322623), (21031438751/110812011767), 1, 0, 0],
  ![(61/404), (91209/632639), (1073813/6792270), (394566455/938322623), (28798158303/110812011767), (918371136479/4226332512717), 1, 0],
  ![(167/1212), (266465/632639), (-3393231/11320450), (340532529/938322623), (7106746287/110812011767), (136591232363/1408777504239), (57923831990733/113302966208759), 1]]

private def dM11 : Fin 8 → ℝ := ![2424, (632639/606), (67922700/632639), (1876645246/16980675), (110812011767/938322623), (8452665025434/110812011767), (453211864835036/4226332512717), (8309911714676948/113302966208759)]

private theorem reconstruction_M11 :
    M11 = LM11 * Matrix.diagonal dM11 * (LM11)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M11, LM11, dM11, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem psd_M11 : M11.PosSemidef := by
  rw [reconstruction_M11]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [dM11]

/-- All four fixed matrices are PSD; the first includes its zero first row and column. -/
theorem grams_posSemidef : M00.PosSemidef ∧ M01.PosSemidef ∧
    M10.PosSemidef ∧ M11.PosSemidef :=
  ⟨psd_M00, psd_M01, psd_M10, psd_M11⟩

end D5.S3.Quantum.Matrix.HsfContractionGrams
