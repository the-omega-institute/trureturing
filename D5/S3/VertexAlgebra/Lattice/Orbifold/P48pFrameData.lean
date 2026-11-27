/- Lightweight signed frame data shared by the P48p action and certificate. -/

import Mathlib.Data.Matrix.Basic

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate

open scoped Matrix

private def tIndex : Fin 48 → Fin 48 := ![0, 25, 4, 39, 35, 17, 21, 43, 44, 33, 18, 3, 36, 1, 32, 5, 16, 22, 38, 10, 46, 41, 47, 9, 30, 12, 29, 6, 11, 40, 45, 27, 15, 28, 8, 19, 23, 24, 37, 20, 42, 26, 34, 14, 2, 31, 7, 13]
private def tSign : Fin 48 → ℤ := ![1, 1, 1, -1, -1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, -1]
private def uIndex : Fin 48 → Fin 48 := ![19, 1, 29, 17, 30, 36, 2, 22, 6, 32, 10, 46, 47, 20, 15, 3, 13, 7, 0, 41, 14, 24, 9, 43, 40, 16, 18, 26, 5, 4, 34, 44, 12, 11, 38, 31, 39, 21, 35, 23, 45, 42, 8, 33, 37, 27, 25, 28]
private def uSign : Fin 48 → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, 1]

def signedFrameMatrix (index : Fin 48 → Fin 48) (sign : Fin 48 → ℤ) :
    Matrix (Fin 48) (Fin 48) ℤ := fun i j => if index i = j then sign i else 0

def tFrameMatrix : Matrix (Fin 48) (Fin 48) ℤ := signedFrameMatrix tIndex tSign
def uFrameMatrix : Matrix (Fin 48) (Fin 48) ℤ := signedFrameMatrix uIndex uSign

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
