/- GID: D5/S3/Quantum/Magic/QuquintCertificateData
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintCertificateData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=consumer=D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative
   digest: Exact numerical matrices and radical facts for thirty-two LDL certificates. -/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
noncomputable section
open Matrix
open scoped BigOperators
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Magic.QuquintCertificateData
def radical : ℝ := Real.sqrt (10 + 2 * Real.sqrt 5)
theorem radical_sq : radical ^ 2 = 10 + 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by positivity)
theorem radical_quartic : radical ^ 4 - 20 * radical ^ 2 + 80 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [radical_sq]
theorem radical_bounds : 14 < radical ^ 2 ∧ radical ^ 2 < 15 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg 5
  constructor <;> nlinarith [radical_sq]
def base : Matrix (Fin 4) (Fin 4) ℝ :=
  !![5 - 3*radical ^ 2/4, radical ^ 2/8, -radical ^ 3/8 + radical/2, -3*radical ^ 3/16 + 5*radical/4;
    radical ^ 2/8, 5 - 3*radical ^ 2/4, 3*radical ^ 3/16 - 5*radical/4, radical ^ 3/8 - radical/2;
    -radical ^ 3/8 + radical/2, 3*radical ^ 3/16 - 5*radical/4, 21 - 61*radical ^ 2/20, 10 - 83*radical ^ 2/40;
    -3*radical ^ 3/16 + 5*radical/4, radical ^ 3/8 - radical/2, 10 - 83*radical ^ 2/40, 21 - 61*radical ^ 2/20]
def zeroQ : Fin 5 → Matrix (Fin 4) (Fin 4) ℝ :=
  ![!![1 - radical ^ 2/20, 1 - 3*radical ^ 2/40, radical ^ 3/20 - radical/2, radical ^ 3/80 - radical/20;
    1 - 3*radical ^ 2/40, 1 - radical ^ 2/20, radical ^ 3/80 - 7*radical/20, -radical/10;
    radical ^ 3/20 - radical/2, radical ^ 3/80 - 7*radical/20, 9*radical ^ 2/100 - 1/5, 17*radical ^ 2/200 - 2/5;
    radical ^ 3/80 - radical/20, -radical/10, 17*radical ^ 2/200 - 2/5, 9*radical ^ 2/100 - 1],
    !![1 - radical ^ 2/20, 1 - 3*radical ^ 2/40, radical ^ 3/20 - 7*radical/10, -3*radical ^ 3/80 + 13*radical/20;
    1 - 3*radical ^ 2/40, 1 - radical ^ 2/20, 3*radical ^ 3/80 - 13*radical/20, -radical ^ 3/20 + 7*radical/10;
    radical ^ 3/20 - 7*radical/10, 3*radical ^ 3/80 - 13*radical/20, 7/5 - 11*radical ^ 2/100, 17*radical ^ 2/200 - 7/5;
    -3*radical ^ 3/80 + 13*radical/20, -radical ^ 3/20 + 7*radical/10, 17*radical ^ 2/200 - 7/5, 7/5 - 11*radical ^ 2/100],
    !![1 - radical ^ 2/20, 1 - 3*radical ^ 2/40, radical/10, -radical ^ 3/80 + 7*radical/20;
    1 - 3*radical ^ 2/40, 1 - radical ^ 2/20, -radical ^ 3/80 + radical/20, -radical ^ 3/20 + radical/2;
    radical/10, -radical ^ 3/80 + radical/20, 9*radical ^ 2/100 - 1, 17*radical ^ 2/200 - 2/5;
    -radical ^ 3/80 + 7*radical/20, -radical ^ 3/20 + radical/2, 17*radical ^ 2/200 - 2/5, 9*radical ^ 2/100 - 1/5],
    !![1 - radical ^ 2/20, 1 - 3*radical ^ 2/40, -radical/10, -radical ^ 3/80 + radical/20;
    1 - 3*radical ^ 2/40, 1 - radical ^ 2/20, radical ^ 3/80 - radical/4, -radical ^ 3/40 + 3*radical/10;
    -radical/10, radical ^ 3/80 - radical/4, 3/5 - 11*radical ^ 2/100, 3/5 - 23*radical ^ 2/200;
    -radical ^ 3/80 + radical/20, -radical ^ 3/40 + 3*radical/10, 3/5 - 23*radical ^ 2/200, 1/5 - 11*radical ^ 2/100],
    !![1 - radical ^ 2/20, 1 - 3*radical ^ 2/40, radical ^ 3/40 - 3*radical/10, -radical ^ 3/80 + radical/4;
    1 - 3*radical ^ 2/40, 1 - radical ^ 2/20, radical ^ 3/80 - radical/20, radical/10;
    radical ^ 3/40 - 3*radical/10, radical ^ 3/80 - radical/20, 1/5 - 11*radical ^ 2/100, 3/5 - 23*radical ^ 2/200;
    -radical ^ 3/80 + radical/4, radical/10, 3/5 - 23*radical ^ 2/200, 3/5 - 11*radical ^ 2/100]]
def branch (s : Fin 32) : Matrix (Fin 4) (Fin 4) ℝ :=
  base + ∑ i : Fin 5, (if s.val / 2 ^ (4 - i.val) % 2 = 0 then (-1 : ℝ) else 1) • zeroQ i
#print axioms radical_sq
#print axioms radical_quartic
#print axioms radical_bounds
end D5.S3.Quantum.Magic.QuquintCertificateData
