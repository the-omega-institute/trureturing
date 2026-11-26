module

public import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificateDraft
import all D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificateDraft
public import Mathlib.Data.List.OfFn

/-!
# Integral cyclic norm splitting for Nebe's P48q row matrix

The row and column indices, integral coefficients and adjugate entries are
copied in order from the persisted P48q norm-image certificate. All matrix
identities used by the splitting are proved over the integers.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace P48qNormImageCertificateDraft

open P48qFixedRankCertificateDraft

local notation "A" => nebeOrderThree

/-- The integral norm in Nebe's row-vector convention. -/
public def normMatrix : Matrix (Fin 48) (Fin 48) ℤ := 1 + A + A ^ 2

public def minorRows (i : Fin 16) : Fin 48 :=
  #[2, 1, 0, 3, 5, 4, 6, 7, 9, 8, 10, 12, 15, 16, 14, 11].getD i.val 0

public def minorColumns (j : Fin 16) : Fin 48 :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15].getD j.val 0

private def adjugateData : Array (Array ℤ) := #[
  #[545880, -5303920, 2504810, 954260, -604180, 9001480, -818940, 3349130, 262790, 5043450,
    -5693130, 3056750, -6506790, -1136000, -1436200, -1399140],
  #[536480, -3762240, 2061080, 516400, -631600, 6404320, -444560, 2554520, 111400, 3792600,
    -4168600, 2248840, -4705960, -660480, -1204320, -841200],
  #[98728, 2226032, -1266282, -437396, 232980, -4324616, 377340, -1658762, -175750, -1783034,
    2553546, -1197678, 2748198, 661376, 425768, 840548],
  #[514512, -5984032, 2636172, 1194136, -759960, 11009136, -922440, 4125772, 498580, 5849964,
    -6723276, 3600708, -7734868, -1344256, -1656368, -1853688],
  #[-164368, 2150048, -1030268, -419704, 353400, -3856944, 318440, -1401148, -33060, -2271196,
    2528444, -1442452, 2927332, 358144, 630512, 469592],
  #[695664, -1829984, 724644, 108232, -347080, 2412112, -116440, 955364, 51900, 2234948, -1713252,
    1217996, -2307836, -155392, -890256, -159976],
  #[-369128, 2282768, -1136518, -436044, 348620, -3306424, 346020, -1254758, 158710, -2365046,
    2418214, -1536482, 2866282, 260224, 763032, 214012],
  #[262936, -458736, 576186, 91188, -435380, 2044488, 130340, 1178586, 164790, 1115082, -1103898,
    704734, -1357654, -167808, -564584, -277124],
  #[825632, -1251392, 185272, 74096, -534640, 1472096, -134480, 572472, 48520, 2023544, -1280056,
    1118568, -2031368, 152064, -1041888, 199632],
  #[119968, 404672, -804392, 52144, 167760, -1356576, 45040, -685992, 42600, -240744, 822696,
    -22328, 466968, 290816, -52832, 282768],
  #[868136, -7744656, 3807926, 1338028, -976940, 13390968, -1110980, 5065366, 329050, 7579942,
    -8458838, 4471794, -9643194, -1699968, -2095704, -2058204],
  #[-50728, -1669232, 522762, 440276, -38740, 2709896, -263100, 912682, 24550, 1483674, -1758826,
    1175118, -2156678, -210816, -436648, -332708],
  #[-803704, 7451824, -4177314, -1072132, 1337220, -14658152, 977740, -5925954, -793230, -7428338,
    8794242, -4295766, 9833646, 1919872, 2272776, 2562196],
  #[-950104, 6101104, -2390314, -1069332, 895380, -10127112, 1011580, -3575114, -245190, -6509498,
    6735242, -3699886, 7873126, 916352, 2004776, 1279716],
  #[-128136, 8799056, -5047646, -1467388, 1094780, -17549208, 1308340, -6962366, -951410,
    -7725582, 10217598, -4616874, 10837074, 2467968, 1966584, 3574124],
  #[-390568, 365968, -496278, 21396, 309740, -991224, -43260, -634998, -109690, -604166, 565814,
    -370322, 865242, 157824, 502232, 19612]
]

/-- The adjugate of the selected minor, as supplied by the certificate. -/
public def minorAdjugate : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => (adjugateData.getD i.val #[]).getD j.val 0

public def minorDeterminant : ℤ := 463360
public def identityCoefficient : ℤ := (-154453)

public def rowSelector : Matrix (Fin 16) (Fin 48) ℤ :=
  (1 : Matrix (Fin 48) (Fin 48) ℤ).submatrix minorRows id

public def columnSelector : Matrix (Fin 48) (Fin 16) ℤ :=
  (1 : Matrix (Fin 48) (Fin 48) ℤ).submatrix id minorColumns

/-- Place the adjugate at the minor's column indices by row indices and add βI. -/
public def splittingMatrix : Matrix (Fin 48) (Fin 48) ℤ :=
  columnSelector * minorAdjugate * rowSelector + identityCoefficient • 1

private def normEntry (i j : Fin 48) : ℤ :=
  (if i = j then 1 else 0) + nebeOrderThree i j + nebeSquare i j

private theorem normEntry_eq (i j : Fin 48) : normMatrix i j = normEntry i j := by
  simp only [normMatrix, pow_two, nebeSquare_eq, Matrix.add_apply, Matrix.one_apply, normEntry]

private def dotProductRow {m n p : ℕ}
    (X : Matrix (Fin m) (Fin n) ℤ) (Y : Matrix (Fin n) (Fin p) ℤ) (i : Fin m) : List ℤ :=
  List.ofFn fun j : Fin p =>
    (List.zipWith (· * ·) (List.ofFn (X i)) (List.ofFn fun k : Fin n => Y k j)).sum

private theorem mul_eq_of_dotProductRows {m n p : ℕ}
    (X : Matrix (Fin m) (Fin n) ℤ) (Y : Matrix (Fin n) (Fin p) ℤ)
    (Z : Matrix (Fin m) (Fin p) ℤ)
    (h : ∀ i, dotProductRow X Y i = List.ofFn (Z i)) :
    X * Y = Z := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, ← dotOfFn_eq]
  exact congrFun (List.ofFn_injective (h i)) j

private theorem norm_mul_columnSelector :
    normMatrix * columnSelector = normMatrix.submatrix id minorColumns := by
  simpa only [columnSelector, mul_one, Matrix.submatrix_id_id] using
    (Matrix.submatrix_mul normMatrix (1 : Matrix (Fin 48) (Fin 48) ℤ)
      id id minorColumns Function.bijective_id).symm

private theorem rowSelector_mul_norm :
    rowSelector * normMatrix = normMatrix.submatrix minorRows id := by
  simpa only [rowSelector, one_mul, Matrix.submatrix_id_id] using
    (Matrix.submatrix_mul (1 : Matrix (Fin 48) (Fin 48) ℤ) normMatrix
      minorRows id id Function.bijective_id).symm

private def columnProductData : Array (Array ℤ) := #[
  #[0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0, 0],
  #[-579200, 2085120, -550240, -173760, 173760, -1737600, 57920, -550240, 318560, -2172000,
    1476960, -1419040, 1998240, 0, 810880, -57920],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 463360, 0, 0],
  #[-115840, -1158400, 955680, 521280, -57920, 2432640, -173760, 955680, -260640, 724000,
    -1419040, 318560, -1129440, -463360, -115840, -289600],
  #[1158400, -926720, 521280, -347520, -579200, -1621760, 115840, -868800, -521280, 1911360,
    -57920, 637120, -868800, 463360, -695040, 1274240],
  #[695040, 463360, -405440, 115840, -115840, -2548480, 115840, -868800, -521280, 57920, 868800,
    173760, 521280, 463360, -231680, 1274240],
  #[0, 1390080, -810880, 231680, 231680, -3706880, 231680, -1737600, -579200, -810880, 1737600,
    -579200, 1505920, 463360, 463360, 1158400],
  #[926720, -1390080, -115840, 231680, -231680, 463360, -695040, -115840, 115840, 1274240,
    -810880, 579200, -1505920, 0, -463360, 231680],
  #[695040, -3243520, 984640, 115840, -579200, 4401920, -810880, 1448000, 405440, 3301440,
    -3301440, 2027200, -4112320, -463360, -1158400, -579200],
  #[463360, -2316800, 1505920, 231680, -231680, 2780160, -231680, 1042560, -115840, 1969280,
    -1969280, 1274240, -2664320, -463360, -463360, -231680],
  #[-1390080, 3706880, -463360, -463360, 463360, -3243520, 926720, -463360, 0, -3706880, 2780160,
    -1853440, 4170240, 0, 1390080, 0],
  #[-926720, 4170240, -1505920, -695040, 231680, -4633600, 695040, -1505920, 115840, -3822720,
    3359360, -2200960, 4517760, 463360, 1390080, 231680],
  #[347520, -695040, -202720, -405440, -57920, -2664320, -173760, -1592800, -492320, 492320,
    666080, 550240, 28960, 926720, -115840, 1100480],
  #[-579200, 3011840, -1476960, -637120, 637120, -6371200, 57920, -2867040, -608160, -3098720,
    3330400, -1882400, 4315040, 926720, 1274240, 1332160],
  #[-231680, 1390080, -521280, -115840, 115840, -3475200, 347520, -1448000, -868800, -984640,
    1448000, -173760, 1795520, 926720, 695040, 1042560],
  #[-347520, -1621760, 781920, 173760, -173760, 3591040, -521280, 1245280, 376480, 1476960,
    -2172000, 724000, -2229920, -463360, -347520, -868800],
  #[115840, 1621760, -955680, -57920, 57920, -2896000, -289600, -1419040, -202720, -1187360,
    1419040, -781920, 1592800, 463360, 579200, 752960],
  #[347520, -2085120, 1071520, -173760, -752960, 2896000, 57920, 1071520, 86880, 2229920,
    -1998240, 1129440, -2403680, 0, -579200, -57920],
  #[926720, -2780160, 695040, 463360, -926720, 5096960, 0, 2085120, 231680, 3938560, -3011840,
    2548480, -4401920, -463360, -1853440, -463360],
  #[0, 2316800, -1390080, 0, 463360, -3706880, 0, -1390080, 0, -2316800, 2316800, -1390080,
    2780160, 463360, 463360, 463360],
  #[231680, 1853440, -1679680, -115840, 115840, -4401920, 347520, -1679680, -173760, -1216320,
    2606400, -405440, 2027200, 926720, 231680, 1042560],
  #[1621760, -2780160, 289600, 579200, -579200, 2548480, -347520, 752960, -289600, 4459840,
    -2606400, 2722240, -4344000, 0, -1621760, 810880],
  #[579200, -231680, -492320, -57920, 57920, -1505920, -289600, -955680, -202720, 666080, 492320,
    144800, -260640, 0, -347520, 752960],
  #[695040, 926720, -637120, 115840, -115840, -2085120, 115840, -637120, -289600, -173760,
    1100480, -57920, 752960, 463360, -231680, 810880],
  #[231680, -3243520, 1679680, 579200, -579200, 4401920, -347520, 1679680, -289600, 3069760,
    -3533120, 1795520, -3880640, 0, -695040, -115840],
  #[115840, 1621760, -839840, -289600, 289600, -2896000, -57920, -1303200, 144800, -1534880,
    1766560, -1361120, 2172000, 463360, 579200, 521280],
  #[0, 463360, -115840, -231680, 231680, -1853440, 231680, -579200, -347520, -579200, 1042560,
    -347520, 1274240, 463360, 0, 231680],
  #[-695040, 2780160, -1332160, -347520, 347520, -3938560, 579200, -868800, -57920, -2722240,
    2722240, -1216320, 3301440, 926720, 695040, 347520],
  #[-1042560, 1158400, -318560, -173760, 173760, 1505920, -405440, 608160, 1013600, -1940320,
    318560, -1187360, 839840, -463360, 810880, -1448000],
  #[1274240, -5792000, 2461600, 752960, -1216320, 9846400, -868800, 3851680, 550240, 6400160,
    -6168480, 3446240, -7500640, -1390080, -1969280, -1448000],
  #[-579200, 1158400, 376480, -173760, 173760, -347520, -405440, -86880, 318560, -1708640, 550240,
    -1419040, 1534880, -463360, 1274240, -521280],
  #[-347520, 2085120, 86880, -752960, 289600, -2432640, 405440, -376480, 144800, -1998240,
    1766560, -1361120, 2635360, 0, 579200, 57920],
  #[463360, -1853440, 231680, 463360, 0, 1390080, -463360, 231680, -231680, 1621760, -1158400,
    695040, -1621760, -463360, -463360, 0],
  #[-1505920, 3475200, -318560, -637120, 173760, -2664320, 521280, -781920, 550240, -3793760,
    2635360, -2577440, 4083360, 0, 1737600, -521280]
]

private def columnProduct : Matrix (Fin 48) (Fin 16) ℤ :=
  fun i j => (columnProductData.getD i.val #[]).getD j.val 0

private theorem normEntry_matrix : (normEntry : Matrix (Fin 48) (Fin 48) ℤ) = normMatrix :=
  Matrix.ext fun i j => (normEntry_eq i j).symm

private theorem columnProduct_eq :
    normMatrix.submatrix id minorColumns * minorAdjugate = columnProduct := by
  rw [← normEntry_matrix]
  apply mul_eq_of_dotProductRows
  intro i
  fin_cases i <;> decide +kernel

private theorem columnProduct_mul_rows :
    columnProduct * normMatrix.submatrix minorRows id = minorDeterminant • normMatrix := by
  rw [← normEntry_matrix]
  apply mul_eq_of_dotProductRows
  intro i
  fin_cases i <;> decide +kernel

private theorem adjugate_sandwich :
    normMatrix * (columnSelector * minorAdjugate * rowSelector) * normMatrix =
      minorDeterminant • normMatrix := by
  calc
    _ = (normMatrix * columnSelector * minorAdjugate) * (rowSelector * normMatrix) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [norm_mul_columnSelector, rowSelector_mul_norm, columnProduct_eq, columnProduct_mul_rows]

private theorem normMatrix_sq : normMatrix * normMatrix = (3 : ℤ) • normMatrix := by
  have h2 : A * A = A ^ 2 := (pow_two A).symm
  have h12 : A * A ^ 2 = 1 := by
    simpa only [pow_one] using (pow_add A 1 2).symm.trans nebeOrderThree_cube
  have h21 : A ^ 2 * A = 1 := by
    simpa only [pow_one] using (pow_add A 2 1).symm.trans nebeOrderThree_cube
  have h22 : A ^ 2 * A ^ 2 = A := by
    calc
      _ = A ^ 4 := (pow_add A 2 2).symm
      _ = A ^ 3 * A ^ 1 := pow_add A 3 1
      _ = A := by rw [nebeOrderThree_cube, one_mul, pow_one]
  simp only [normMatrix, add_mul, mul_add, one_mul, mul_one, h2, h12, h21, h22]
  rw [show (3 : ℤ) = 1 + 1 + 1 by decide, add_smul, add_smul]
  simp only [one_smul]
  abel

/-- The exact integral cyclic norm splits through the certified integral matrix. -/
public theorem nebeOrderThree_norm_split :
    normMatrix * splittingMatrix * normMatrix = normMatrix := by
  calc
    _ = normMatrix * (columnSelector * minorAdjugate * rowSelector) * normMatrix +
          identityCoefficient • (normMatrix * normMatrix) := by
      simp only [splittingMatrix, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    _ = minorDeterminant • normMatrix + identityCoefficient • ((3 : ℤ) • normMatrix) := by
      rw [adjugate_sandwich, normMatrix_sq]
    _ = normMatrix := by
      rw [smul_smul, ← add_smul,
        show minorDeterminant + identityCoefficient * 3 = 1 by decide +kernel, one_smul]

#check nebeOrderThree_norm_split
#print axioms nebeOrderThree_norm_split

end P48qNormImageCertificateDraft
