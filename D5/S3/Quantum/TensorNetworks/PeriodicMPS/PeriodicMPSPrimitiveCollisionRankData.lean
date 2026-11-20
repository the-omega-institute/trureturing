/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionRankData
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSPrimitiveCollisionRankData
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionVariation]
   utility: none
   digest: An exact Jacobian certificate. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSPrimitiveCollisionVariation

/-! Exact Pauli observation rank at the Ising collision. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision

open Matrix
open scoped Matrix Kronecker
open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal)
open PeriodicMPSUniformAntisymmetricTransfer
  (TransferMatrix mixedTransfer mixedRaw conjugateCore)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryTransfer binaryInsertion)

private abbrev Pair := Fin 2 × Fin 2
private abbrev G := GaussianInt
private abbrev GM := TransferMatrix G
private abbrev B2 := Fin 2 → Matrix (Fin 2) (Fin 2) G
private abbrev Direction := Fin 2 × Fin 2 × Fin 2 × Fin 2

private def ig : G := ⟨0, 1⟩

def basisDirection (d : Direction) : B2 :=
  fun k i j => if (k, i, j) = (d.1, d.2.1, d.2.2.1) then
    if d.2.2.2 = 0 then 1 else ig else 0

def directionOf (d : Fin 16) : Direction :=
  let a : Fin 2 × Fin 8 := finProdFinEquiv.symm d
  let b : Fin 2 × Fin 4 := finProdFinEquiv.symm a.2
  let c : Fin 2 × Fin 2 := finProdFinEquiv.symm b.2
  (a.1, b.1, c.1, c.2)

private def pauliG : Fin 3 → Matrix (Fin 2) (Fin 2) G :=
  ![!![0, 1; 1, 0], !![0, -ig; ig, 0], !![1, 0; 0, -1]]

def observableG (j : Fin 9) : GM :=
  let X := pauliG 0
  let Y := pauliG 1
  let Z := pauliG 2
  ![X ⊗ₖ 1, Y ⊗ₖ 1, Z ⊗ₖ 1, X ⊗ₖ X, X ⊗ₖ Y, X ⊗ₖ Z,
    Y ⊗ₖ Y, Y ⊗ₖ Z, Z ⊗ₖ Z] j

def measure25 : Fin 9 → G := ![9, 0, 0, 9, 0, 0, 0, -12, 0]

def tG (b : Bool) : GM := mixedTransfer (coresG b) (braG b)
def insG (b : Bool) (p q : Pair) : GM := binaryInsertion (braG b) (coresG b) q p

def scaledFirstG (b : Bool) (d : Fin 16) : GM :=
  let s : G := collisionScale b
  let A := coresG b
  let B := braG b
  let U := basisDirection (directionOf d)
  let V := fun k => (U k).map star
  let dT := transferVariation A B U V
  let T := tG b
  let P := T ^ 2
  let F := s • (1 : GM) + T
  let E := F * dT * P + P * dT * F
  fun p q => (s ^ 2 • (markedVariation A B U V p q * P) + insG b p q * E).trace

def numeratorRankG (b : Bool) (j : Fin 9) (d : Fin 16) : G :=
  25 * (observableG j * scaledFirstG b d).trace - (scaledFirstG b d).trace * measure25 j

def minorRows : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 8]
def minorCols : Fin 8 → Fin 16 := ![0, 1, 2, 3, 4, 5, 8, 9]

def observedInteger : Bool → Matrix (Fin 9) (Fin 16) ℤ
  | false => !![960, -1920, 960, 1920, 2624, -1408, 2624, 1408, 2624, 1408, 2624, -1408, 960, 1920, 960, -1920;
      -3120, -3360, 0, 0, -1552, -3776, 832, -2336, -832, 2336, 1552, 3776, 0, 0, 3120, 3360;
      4000, 2000, 0, 0, 1600, 2800, 800, 1600, -800, -1600, -1600, -2800, 0, 0, -4000, -2000;
      960, -1920, 960, 1920, 2112, -384, 2112, 384, 2112, 384, 2112, -384, 960, 1920, 960, -1920;
      -1200, -2400, 0, 0, 624, -2688, 576, -288, -576, 288, -624, 2688, 0, 0, 1200, 2400;
      -160, -2480, 0, 0, 1664, -1168, -224, -448, 224, 448, -1664, 1168, 0, 0, 160, 2480;
      -720, -360, 720, -360, -1680, -1560, 1680, -1560, 1680, -1560, -1680, -1560, 720, -360, -720, -360;
      -280, 560, -280, -560, -232, -656, -232, 656, -232, 656, -232, -656, -280, -560, -280, 560;
      2000, 1000, -2000, 1000, 400, 2200, -400, 2200, -400, 2200, 400, 2200, -2000, 1000, 2000, 1000]
  | true => !![-3584, -5632, 18944, -36352, 5632, 3584, 36352, -18944, 36352, -18944, 5632, 3584, 18944, -36352, -3584, -5632;
      -44800, 9600, -22400, -12800, -12800, 22400, -22400, -19200, 22400, 19200, 12800, -22400, 22400, 12800, 44800, -9600;
      43648, -33536, 30208, 12416, 12416, -30208, 20224, 6272, -20224, -6272, -12416, 30208, -30208, -12416, -43648, 33536;
      4608, -1536, 10752, -32256, 1536, -4608, 32256, -10752, 32256, -10752, 1536, -4608, 10752, -32256, 4608, -1536;
      4864, -18048, 9344, -13312, -13312, -9344, 21632, -2304, -21632, 2304, 13312, 9344, -9344, 13312, -4864, 18048;
      11904, -23808, 21504, -4992, -4992, -21504, 14592, 7296, -14592, -7296, 4992, 21504, -21504, 4992, -11904, 23808;
      -1600, -4800, -33600, -11200, -4800, -1600, -11200, -33600, -11200, -33600, -4800, -1600, -33600, -11200, -1600, -4800;
      -7488, -2624, 3008, 6336, 2624, 7488, -6336, -3008, -6336, -3008, 2624, 7488, 3008, 6336, -7488, -2624;
      6720, -10560, 18240, 16320, -10560, 6720, 16320, 18240, 16320, 18240, -10560, 6720, 18240, 16320, 6720, -10560]

def minorInverse : Bool → Matrix (Fin 8) (Fin 8) ℤ
  | false => !![375, 588, 856, -375, -300, 184, 500, 180;
      750, -456, -212, -750, 600, -908, -250, -90;
      375, 948, 632, 25, -1300, -136, -500, -948;
      -750, -264, -236, 1550, 1400, -1652, -250, 294;
      375, -660, -360, -375, 500, 120, -500, -180;
      -750, 120, -180, 750, -1000, 660, -250, -90;
      375, -300, -360, -375, -500, 600, 500, 180;
      750, 600, 180, -750, -1000, 300, -250, -90]
  | true => !![-24750, -38036, 17952, 50750, 58036, -97200, 13050, 28250;
      -42375, -67472, -83796, 45375, -14528, 34100, -30900, -16500;
      48375, -41260, -48240, -49375, -820, 48000, -33540, 5500;
      -8250, -5920, -17580, -28750, -71440, 63500, 12570, 32250;
      51375, 49320, 90420, -51375, -16440, -68500, -24660, -68500;
      102750, -24660, 16440, -102750, 90420, -137000, 12330, 34250;
      -24750, 18408, 6444, 50750, -53208, 26100, 13050, 28250;
      -42375, 42676, 49368, 45375, 39724, -61800, -30900, -16500]

def minorScale (b : Bool) : ℤ := if b then 2104320000 else 1920000

theorem integer_minor_inverse (b : Bool) :
    (observedInteger b).submatrix minorRows minorCols * minorInverse b =
      minorScale b • (1 : Matrix (Fin 8) (Fin 8) ℤ) := by
  cases b <;> funext i j <;> fin_cases i <;> fin_cases j <;> decide +kernel

theorem integer_row_relation (b : Bool) (d : Fin 16) :
    24 * observedInteger b 7 d = 18 * observedInteger b 0 d - 25 * observedInteger b 3 d := by
  cases b <;> fin_cases d <;> decide +kernel

theorem gaussian_observed_integer (b : Bool) (j : Fin 9) (d : Fin 16) :
    numeratorRankG b j d =
      25 * (collisionScale b : G) ^ 2 * (observedInteger b j d : G) := by
  cases b <;> fin_cases j <;> fin_cases d <;> decide +kernel

end D5.S3.Quantum.TensorNetworks.PeriodicMPSPrimitiveCollision
