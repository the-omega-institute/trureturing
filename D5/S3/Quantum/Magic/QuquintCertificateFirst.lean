/- GID: D5/S3/Quantum/Magic/QuquintCertificateFirst
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintCertificateFirst
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=consumer=D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative
   digest: Explicit LDL identities for numerical branches zero through fifteen. -/

import D5.S3.Quantum.Magic.QuquintCertificateData

noncomputable section
open Matrix
open D5.S3.Quantum.Magic.QuquintCertificateData
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Magic.QuquintCertificateFirst
def lower0 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, -radical/5, 1, 0;
    radical/4, -radical ^ 3/40 + radical/5, radical ^ 2/8 - 1, 1]
def pivots0 : Fin 4 → ℝ := ![radical ^ 2/2, 5*radical ^ 2/8 - 5/2, 2*radical ^ 2 - 16, radical ^ 2 - 10]
theorem ldl_0 :
    -branch 0 = lower0 * Matrix.diagonal (pivots0) * (lower0)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower0, pivots0, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_0
def lower1 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, radical ^ 3/11 - 87*radical/55, 1, 0;
    radical/4, -27*radical ^ 3/440 + 37*radical/55, radical ^ 2/8 - 1, 1]
def pivots1 : Fin 4 → ℝ := ![3*radical ^ 2/5 - 2, 5*radical ^ 2/8 - 3, 124*radical ^ 2/55 - 208/11, radical ^ 2 - 48/5]
theorem ldl_1 :
    -branch 1 = lower1 * Matrix.diagonal (pivots1) * (lower1)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower1, pivots1, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_1
def lower2 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    29*radical ^ 3/440 - 15*radical/22, -radical ^ 3/44 + 8*radical/55, 1, 0;
    -3*radical ^ 3/110 + 31*radical/44, 5*radical ^ 3/88 - 53*radical/55, 17*radical ^ 2/124 - 110/93, 1]
def pivots2 : Fin 4 → ℝ := ![3*radical ^ 2/5 - 2, 5*radical ^ 2/8 - 3, 114*radical ^ 2/55 - 888/55, 542*radical ^ 2/465 - 1120/93]
theorem ldl_2 :
    -branch 2 = lower2 * Matrix.diagonal (pivots2) * (lower2)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower2, pivots2, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_2
def lower3 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    -radical ^ 3/20 + radical, -3*radical ^ 3/4 + 53*radical/5, 1, 0;
    7*radical ^ 3/20 - 19*radical/4, -21*radical ^ 3/40 + 37*radical/5, 39/44 - radical ^ 2/176, 1]
def pivots3 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 4*radical ^ 2/5 + 16/5, 39*radical ^ 2/110 + 1/11]
theorem ldl_3 :
    -branch 3 = lower3 * Matrix.diagonal (pivots3) * (lower3)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower3, pivots3, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_3
def lower4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    41*radical ^ 3/440 - 25*radical/22, -radical ^ 3/44 + 8*radical/55, 1, 0;
    3*radical ^ 3/220 + radical/44, -13*radical ^ 3/440 + 17*radical/55, 75*radical ^ 2/698 - 262/349, 1]
def pivots4 : Fin 4 → ℝ := ![3*radical ^ 2/5 - 2, 5*radical ^ 2/8 - 3, 122*radical ^ 2/55 - 992/55, 1814*radical ^ 2/1745 - 3592/349]
theorem ldl_4 :
    -branch 4 = lower4 * Matrix.diagonal (pivots4) * (lower4)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower4, pivots4, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_4
def lower5 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    -2*radical ^ 3/5 + 6*radical, -3*radical ^ 3/4 + 53*radical/5, 1, 0;
    -7*radical ^ 3/40 + 11*radical/4, 3*radical ^ 3/8 - 28*radical/5, 81*radical ^ 2/872 - 115/218, 1]
def pivots5 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 104/5 - 2*radical ^ 2/5, 262*radical ^ 2/545 - 198/109]
theorem ldl_5 :
    -branch 5 = lower5 * Matrix.diagonal (pivots5) * (lower5)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower5, pivots5, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_5
def lower6 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    -radical ^ 3/2 + 15*radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    7*radical ^ 3/40 - 9*radical/4, -29*radical ^ 3/40 + 52*radical/5, 137*radical ^ 2/872 - 321/218, 1]
def pivots6 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 104/5 - 2*radical ^ 2/5, 262*radical ^ 2/545 - 198/109]
theorem ldl_6 :
    -branch 6 = lower6 * Matrix.diagonal (pivots6) * (lower6)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower6, pivots6, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_6
def lower7 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/110 + 3*radical/22, -radical ^ 3/22 + 23*radical/55, 1, 0;
    radical ^ 3/55 + radical/44, -5*radical ^ 3/88 + 37*radical/55, 75*radical ^ 2/484 - 345/242, 1]
def pivots7 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 2*radical ^ 2 - 64/5, 2433*radical ^ 2/2662 - 10248/1331]
theorem ldl_7 :
    -branch 7 = lower7 * Matrix.diagonal (pivots7) * (lower7)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower7, pivots7, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_7
def lower8 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    3*radical ^ 3/440 + 3*radical/22, -radical ^ 3/44 + 8*radical/55, 1, 0;
    19*radical ^ 3/440 - 17*radical/44, -radical ^ 3/440 - 8*radical/55, 199*radical ^ 2/1396 - 436/349, 1]
def pivots8 : Fin 4 → ℝ := ![3*radical ^ 2/5 - 2, 5*radical ^ 2/8 - 3, 122*radical ^ 2/55 - 992/55, 1814*radical ^ 2/1745 - 3592/349]
theorem ldl_8 :
    -branch 8 = lower8 * Matrix.diagonal (pivots8) * (lower8)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower8, pivots8, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_8
def lower9 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/2 - 7*radical, -3*radical ^ 3/4 + 53*radical/5, 1, 0;
    -9*radical ^ 3/20 + 27*radical/4, radical ^ 3/40 - 3*radical/5, 137*radical ^ 2/872 - 321/218, 1]
def pivots9 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 104/5 - 2*radical ^ 2/5, 262*radical ^ 2/545 - 198/109]
theorem ldl_9 :
    -branch 9 = lower9 * Matrix.diagonal (pivots9) * (lower9)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower9, pivots9, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_9
def lower10 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    2*radical ^ 3/5 - 11*radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    -radical ^ 3/10 + 7*radical/4, -43*radical ^ 3/40 + 77*radical/5, 45*radical ^ 2/176 - 127/44, 1]
def pivots10 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 4*radical ^ 2/5 + 16/5, 39*radical ^ 2/110 + 1/11]
theorem ldl_10 :
    -branch 10 = lower10 * Matrix.diagonal (pivots10) * (lower10)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower10, pivots10, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_10
def lower11 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    19*radical ^ 3/220 - 21*radical/22, -radical ^ 3/22 + 23*radical/55, 1, 0;
    -radical ^ 3/440 + 15*radical/44, -41*radical ^ 3/440 + 62*radical/55, 225*radical ^ 2/1448 - 523/362, 1]
def pivots11 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 114*radical ^ 2/55 - 776/55, 1638*radical ^ 2/1991 - 12522/1991]
theorem ldl_11 :
    -branch 11 = lower11 * Matrix.diagonal (pivots11) * (lower11)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower11, pivots11, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_11
def lower12 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, radical ^ 3/2 - 37*radical/5, 1, 0;
    -5*radical ^ 3/8 + 37*radical/4, -7*radical ^ 3/40 + 12*radical/5, radical ^ 2/8 - 1, 1]
def pivots12 : Fin 4 → ℝ := ![7*radical ^ 2/10 - 4, 5*radical ^ 2/8 - 7/2, 8*radical ^ 2/5 - 8, 134/5 - 3*radical ^ 2/2]
theorem ldl_12 :
    -branch 12 = lower12 * Matrix.diagonal (pivots12) * (lower12)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower12, pivots12, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_12
def lower13 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/20 - radical/2, -radical ^ 3/22 + 23*radical/55, 1, 0;
    -5*radical ^ 3/88 + 45*radical/44, -7*radical ^ 3/440 + 2*radical/55, radical ^ 2/8 - 1, 1]
def pivots13 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 24*radical ^ 2/11 - 168/11, 17*radical ^ 2/22 - 314/55]
theorem ldl_13 :
    -branch 13 = lower13 * Matrix.diagonal (pivots13) * (lower13)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower13, pivots13, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_13
def lower14 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    21*radical ^ 3/440 - 9*radical/22, 3*radical ^ 3/44 - 62*radical/55, 1, 0;
    -9*radical ^ 3/440 + 25*radical/44, -43*radical ^ 3/440 + 72*radical/55, 137*radical ^ 2/1448 - 201/362, 1]
def pivots14 : Fin 4 → ℝ := ![4*radical ^ 2/5 - 6, 5*radical ^ 2/8 - 4, 114*radical ^ 2/55 - 776/55, 1638*radical ^ 2/1991 - 12522/1991]
theorem ldl_14 :
    -branch 14 = lower14 * Matrix.diagonal (pivots14) * (lower14)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower14, pivots14, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_14
def lower15 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    3/2 - radical ^ 2/8, 1, 0, 0;
    radical ^ 3/19 - 9*radical/19, -radical ^ 3/76 - 3*radical/95, 1, 0;
    -7*radical ^ 3/760 + 31*radical/76, -41*radical ^ 3/760 + 58*radical/95, 71*radical ^ 2/528 - 149/132, 1]
def pivots15 : Fin 4 → ℝ := ![9*radical ^ 2/10 - 8, 5*radical ^ 2/8 - 9/2, 216*radical ^ 2/95 - 1488/95, 201*radical ^ 2/220 - 238/33]
theorem ldl_15 :
    -branch 15 = lower15 * Matrix.diagonal (pivots15) * (lower15)ᵀ := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [branch, base, zeroQ, lower15, pivots15, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;> grind only
#print axioms ldl_15
end D5.S3.Quantum.Magic.QuquintCertificateFirst
