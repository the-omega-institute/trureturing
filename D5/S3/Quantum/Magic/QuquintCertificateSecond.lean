/- GID: D5/S3/Quantum/Magic/QuquintCertificateSecond
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintCertificateSecond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=consumer=D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative
   digest: Explicit LDL identities for numerical branches sixteen through thirty-one. -/

import D5.S3.Quantum.Magic.QuquintCertificateData

noncomputable section
open Matrix
open D5.S3.Quantum.Magic.QuquintCertificateData
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Magic.QuquintCertificateSecond
def lower16 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    3*radical ^ 3/88 - 7*radical/22, -radical ^ 3/44 + 8*radical/55, 1, 0;
    -13*radical ^ 3/440 + 29*radical/44, -39*radical ^ 3/440 + 62*radical/55, 7*radical ^ 2/62 - 76/93, 1]
def pivots16 : Fin 4 → ℝ := ![3*radical ^ 2/5 - 2, 5*radical ^ 2/8 - 3, 114*radical ^ 2/55 - 888/55, 542*radical ^ 2/465 - 1120/93]
theorem ldl_16 :
    -branch 16 = lower16 * Matrix.diagonal (pivots16) * (lower16)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower16, pivots16, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_16
def lower17 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    3*radical ^ 3/20 - 2*radical, -3*radical ^ 3/4 + 53*radical/5, 1, 0;
    11*radical ^ 3/40 - 15*radical/4, 37*radical ^ 3/40 - 68*radical/5, 45*radical ^ 2/176 - 127/44, 1]
def pivots17 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 4*radical ^ 2/5 + 16/5, 39*radical ^ 2/110 + 1/11]
theorem ldl_17 :
    -branch 17 = lower17 * Matrix.diagonal (pivots17) * (lower17)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower17, pivots17, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_17
def lower18 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    5*radical ^ 3/8 - 35*radical/4, -7*radical ^ 3/40 + 12*radical/5, radical ^ 2/8 - 1, 1]
def pivots18 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 8*radical ^ 2/5 - 8, 134/5 - 3*radical ^ 2/2]
theorem ldl_18 :
    -branch 18 = lower18 * Matrix.diagonal (pivots18) * (lower18)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower18, pivots18, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_18
def lower19 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, -radical ^ 3/22 + 23*radical/55, 1, 0;
    5*radical ^ 3/88 - 23*radical/44, -7*radical ^ 3/440 + 2*radical/55, radical ^ 2/8 - 1, 1]
def pivots19 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 24*radical ^ 2/11 - 168/11, 17*radical ^ 2/22 - 314/55]
theorem ldl_19 :
    -branch 19 = lower19 * Matrix.diagonal (pivots19) * (lower19)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower19, pivots19, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_19
def lower20 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    -3*radical ^ 3/10 + 9*radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    radical ^ 3/10 - 5*radical/4, 29*radical ^ 3/40 - 53*radical/5, 39/44 - radical ^ 2/176, 1]
def pivots20 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 4*radical ^ 2/5 + 16/5, 39*radical ^ 2/110 + 1/11]
theorem ldl_20 :
    -branch 20 = lower20 * Matrix.diagonal (pivots20) * (lower20)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower20, pivots20, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_20
def lower21 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    3*radical ^ 3/220 - radical/22, -radical ^ 3/22 + 23*radical/55, 1, 0;
    radical ^ 3/440 + 7*radical/44, 27*radical ^ 3/440 - 58*radical/55, 137*radical ^ 2/1448 - 201/362, 1]
def pivots21 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 114*radical ^ 2/55 - 776/55, 1638*radical ^ 2/1991 - 12522/1991]
theorem ldl_21 :
    -branch 21 = lower21 * Matrix.diagonal (pivots21) * (lower21)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower21, pivots21, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_21
def lower22 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/88 + radical/22, 3*radical ^ 3/44 - 62*radical/55, 1, 0;
    17*radical ^ 3/440 - 13*radical/44, -9*radical ^ 3/440 + 12*radical/55, 23*radical ^ 2/242 - 139/242, 1]
def pivots22 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 2*radical ^ 2 - 64/5, 2433*radical ^ 2/2662 - 10248/1331]
theorem ldl_22 :
    -branch 22 = lower22 * Matrix.diagonal (pivots22) * (lower22)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower22, pivots22, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_22
def lower23 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    11*radical ^ 3/380 - 4*radical/19, -radical ^ 3/76 - 3*radical/95, 1, 0;
    2*radical ^ 3/95 - 3*radical/76, -9*radical ^ 3/760 + 3*radical/95, 149*radical ^ 2/1364 - 523/682, 1]
def pivots23 : Fin 4 → ℝ := ![9*radical ^ 2/10 - 8, 5*radical ^ 2/8 - 9/2, 214*radical ^ 2/95 - 1432/95, 3227*radical ^ 2/3410 - 2654/341]
theorem ldl_23 :
    -branch 23 = lower23 * Matrix.diagonal (pivots23) * (lower23)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower23, pivots23, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_23
def lower24 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    3*radical ^ 3/5 - 17*radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    -7*radical ^ 3/40 + 11*radical/4, 3*radical ^ 3/8 - 28*radical/5, 81*radical ^ 2/872 - 115/218, 1]
def pivots24 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 104/5 - 2*radical ^ 2/5, 262*radical ^ 2/545 - 198/109]
theorem ldl_24 :
    -branch 24 = lower24 * Matrix.diagonal (pivots24) * (lower24)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower24, pivots24, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_24
def lower25 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/11 - 25*radical/22, -radical ^ 3/22 + 23*radical/55, 1, 0;
    -radical ^ 3/55 + 21*radical/44, radical ^ 3/40 - 3*radical/5, 23*radical ^ 2/242 - 139/242, 1]
def pivots25 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 2*radical ^ 2 - 64/5, 2433*radical ^ 2/2662 - 10248/1331]
theorem ldl_25 :
    -branch 25 = lower25 * Matrix.diagonal (pivots25) * (lower25)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower25, pivots25, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_25
def lower26 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    39*radical ^ 3/440 - 23*radical/22, 3*radical ^ 3/44 - 62*radical/55, 1, 0;
    radical ^ 3/55 + radical/44, -5*radical ^ 3/88 + 37*radical/55, 75*radical ^ 2/484 - 345/242, 1]
def pivots26 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 2*radical ^ 2 - 64/5, 2433*radical ^ 2/2662 - 10248/1331]
theorem ldl_26 :
    -branch 26 = lower26 * Matrix.diagonal (pivots26) * (lower26)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower26, pivots26, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_26
def lower27 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    27*radical ^ 3/380 - 15*radical/19, -radical ^ 3/76 - 3*radical/95, 1, 0;
    9*radical ^ 3/760 + 9*radical/76, -27*radical ^ 3/760 + 28*radical/95, 48*radical ^ 2/341 - 841/682, 1]
def pivots27 : Fin 4 → ℝ := ![9*radical ^ 2/10 - 8, 5*radical ^ 2/8 - 9/2, 214*radical ^ 2/95 - 1432/95, 3227*radical ^ 2/3410 - 2654/341]
theorem ldl_27 :
    -branch 27 = lower27 * Matrix.diagonal (pivots27) * (lower27)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower27, pivots27, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_27
def lower28 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    23*radical ^ 3/440 - 13*radical/22, 3*radical ^ 3/44 - 62*radical/55, 1, 0;
    -2*radical ^ 3/55 + 31*radical/44, 9*radical ^ 3/440 - 23*radical/55, 225*radical ^ 2/1448 - 523/362, 1]
def pivots28 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 114*radical ^ 2/55 - 776/55, 1638*radical ^ 2/1991 - 12522/1991]
theorem ldl_28 :
    -branch 28 = lower28 * Matrix.diagonal (pivots28) * (lower28)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower28, pivots28, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_28
def lower29 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    9*radical ^ 3/190 - 10*radical/19, -radical ^ 3/76 - 3*radical/95, 1, 0;
    -9*radical ^ 3/380 + 39*radical/76, radical ^ 3/152 - 27*radical/95, 61*radical ^ 2/528 - 115/132, 1]
def pivots29 : Fin 4 → ℝ := ![9*radical ^ 2/10 - 8, 5*radical ^ 2/8 - 9/2, 216*radical ^ 2/95 - 1488/95, 201*radical ^ 2/220 - 238/33]
theorem ldl_29 :
    -branch 29 = lower29 * Matrix.diagonal (pivots29) * (lower29)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower29, pivots29, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_29
def lower30 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, radical ^ 3/19 - 83*radical/95, 1, 0;
    radical/4, -23*radical ^ 3/760 + 33*radical/95, radical ^ 2/8 - 1, 1]
def pivots30 : Fin 4 → ℝ := ![9*radical ^ 2/10 - 8, 5*radical ^ 2/8 - 9/2, 206*radical ^ 2/95 - 272/19, radical ^ 2 - 42/5]
theorem ldl_30 :
    -branch 30 = lower30 * Matrix.diagonal (pivots30) * (lower30)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower30, pivots30, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_30
def lower31 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, -radical/5, 1, 0;
    radical/4, -radical ^ 3/40 + radical/5, radical ^ 2/8 - 1, 1]
def pivots31 : Fin 4 → ℝ := ![radical ^ 2 - 10, 5*radical ^ 2/8 - 5, 12*radical ^ 2/5 - 16, radical ^ 2 - 8]
theorem ldl_31 :
    -branch 31 = lower31 * Matrix.diagonal (pivots31) * (lower31)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower31, pivots31, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_31
end D5.S3.Quantum.Magic.QuquintCertificateSecond
