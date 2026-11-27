/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameLatticeAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameLatticeAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed SL(2,23) frame action and the cubic frame generator transport to integral P48p catalogue isometries. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameProjectiveAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameCubicRank
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Integral transport from the P48p frame

Write `F` for the frame rows, `G` for the catalogue Gram matrix, and
`P = G * Fᵀ` for the pairings. The row-action intertwiner is `F * L = O * F`.
The inverse of `F` over ℚ is `(1 / 12) • P`, so this forces
`L = (1 / 12) • (P * O * F)`. The signed transvections and the cubic
generator give exact integral reconstructions.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameLatticeAction

open scoped Matrix
open P48pSyndromeFrame
  (p48pFrameRows p48pGram p48pPairingFrame p48pPairingFrame_eq p48pFrameRows_orthogonal)
open P48pSymmetricCommutantCertificate
  (signedFrameMatrix tFrameMatrix uFrameMatrix J JRat Z1 catalogueFrameMap
    tCatalogueMap uCatalogueMap zCatalogueMap
    tCatalogueMap_isometry uCatalogueMap_isometry zCatalogueMap_isometry)
open P48pFrameProjectiveAction
  (SL23 t u frameAction frameAction_t frameAction_u frameAction_injective generators_generate)
open P48pFrameCubicRank (ARat C rowAction frame_cubic_cube_and_fixedRank16)
open private tIndex tSign uIndex uSign ratCast_smul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate
open private dotOfFn_eq mul_eq_of_dotProductRows from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
open private signed_mul_apply A_cube C_sq C_cube ARat_commute_C from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameCubicRank

abbrev CatalogueMatrix := Matrix (Fin 48) (Fin 48) ℤ
abbrev RationalMatrix := Matrix (Fin 48) (Fin 48) ℚ

local notation "F" => p48pFrameRows
local notation "G" => p48pGram
local notation "P" => p48pPairingFrame

theorem frame_mul_pairing : F * P = (12 : ℤ) • 1 := by
  rw [p48pPairingFrame_eq, ← Matrix.mul_assoc, p48pFrameRows_orthogonal]

private def signedRows (index : Fin 48 → Fin 48) (sign : Fin 48 → ℤ) : CatalogueMatrix :=
  fun i j => sign i * F (index i) j

private theorem signed_mul_frame (index : Fin 48 → Fin 48) (sign : Fin 48 → ℤ) :
    signedFrameMatrix index sign * F = signedRows index sign :=
  Matrix.ext (fun i j => signed_mul_apply index sign F i j)

/-- Table of `Z1 * F / 12` in the catalogue basis. -/
private def cubicRowsData : Array (Array ℤ) := #[
  #[1, 8, -2, 4, -4, -4, -4, 2, 2, -3, 8, 3, 4, -1, -4, 1, 6, -8, -3, -4, -9, 2, 1, 4, 3, 1, 2, -3, 0, 3, 2, 2, 4, -2, 3, 1, -1, 0, -1, -2, -2, -3, 4, 0, 0, -1, 3, 2],
  #[-3, 4, -6, 6, 4, -4, 2, 4, 0, -7, 4, -1, 4, -1, -2, 1, 2, -2, -1, -4, -3, -2, -1, 2, 1, 1, 0, -1, 0, 3, 2, 2, 2, -2, 1, -1, -1, 0, -1, -2, -2, -1, 2, 2, 0, -1, 1, 0],
  #[-9, 2, -4, 10, 4, -6, 4, 8, 0, -9, 2, -1, 2, -3, -8, -1, 4, -2, -3, -4, -5, 0, -1, 2, 3, 5, -2, 1, 0, 3, 2, 2, 0, 0, 1, 1, 1, 2, -1, -2, -2, -1, 2, 2, -2, -1, 1, 0],
  #[3, -4, 0, -2, -8, 0, -6, -18, -2, 15, -4, 9, -2, 3, 6, 1, 0, 0, 5, 2, 5, 4, 3, -4, -3, -5, 0, -1, 2, -3, -6, -2, -2, 0, -3, 1, -1, 0, 1, 4, 4, 3, -6, -2, 4, 3, -1, -4],
  #[5, 8, -6, 4, -4, -6, 0, -2, 4, -3, 4, 3, 10, -1, -4, 3, 10, -6, 1, -4, -9, 2, -3, 2, 3, 3, 0, -3, 0, 5, 2, 4, 2, -2, 3, 3, 1, 0, -1, 0, -2, -1, 2, 2, 0, -1, 1, 0],
  #[-5, -2, 2, -2, 6, -2, 0, 4, 2, 3, -2, -3, -6, 1, 2, -3, -6, 2, -1, 0, 5, 0, 1, -2, -1, -3, 2, 3, 0, -3, -2, -4, 0, 2, -3, -3, -1, 0, -1, -2, 0, 1, -2, -2, 0, 1, -1, -2],
  #[-11, -6, 2, 6, 6, -2, 2, 4, -4, -1, -2, 1, -4, 1, -2, -3, -2, 0, -3, 0, 1, 0, 1, 2, 1, 3, 0, 1, 0, -1, -2, -2, -2, 0, -1, -1, 1, 0, -1, 0, 0, 1, 0, 0, 0, -1, 1, 0],
  #[-3, -4, -6, -2, 4, 4, 4, -4, 0, -3, -8, -3, 6, 5, 4, 3, 0, 4, 3, -2, 3, -2, -1, -4, -5, -1, 0, 1, 0, 1, 0, 0, 0, -2, -1, -1, -1, 0, -1, 0, -2, -1, 0, 0, 2, 1, -1, 0],
  #[1, -8, 2, -4, -4, 6, -2, -8, -4, 5, -2, 3, 0, 1, 6, 3, -2, 2, 5, 4, 3, 2, 3, 0, -3, -3, 2, -3, 0, -3, -2, 0, 0, 0, -1, -1, -1, -2, 1, 2, 2, 1, 0, 0, 0, 1, 1, 0],
  #[-9, -6, -4, 0, 2, 6, 0, -4, -4, -1, -4, -1, 0, 5, 4, 3, -4, 4, 1, 0, 3, -2, 3, -2, -5, -3, 0, -1, 2, -1, 0, -2, 0, -2, -1, -1, -1, 0, -1, 0, 0, 1, -2, 0, 0, 1, -1, 0],
  #[11, 2, 12, -2, -8, -6, 0, 6, 4, 1, 8, 3, 2, -5, -6, 1, 6, -6, -1, 2, -9, 4, -1, 6, 5, 5, 2, -3, 0, 1, 0, 2, 2, 0, 5, 1, 1, -2, -1, 0, -2, -1, 4, 2, 0, -3, 1, 2],
  #[-5, 2, -6, 0, 2, 0, -4, 0, 0, 1, 2, -1, -2, 5, 6, 1, -4, -2, -1, -2, 3, -2, 3, 0, -3, -5, 2, -1, 2, -1, 0, 0, 2, -2, -1, -1, -3, 0, -1, -2, 0, -1, -2, 0, 0, 1, 1, 0],
  #[-7, -2, -6, 6, 6, 0, 6, 2, -2, -9, -4, -3, 6, 1, -2, 1, 2, 2, -1, -2, -1, -2, -3, 0, 1, 5, -2, 1, -2, 3, 2, 2, 0, -2, -1, 1, 1, 0, -1, 0, -2, -1, 2, 2, -2, -1, 1, 0],
  #[1, 2, -8, 4, 6, -4, 6, -4, 2, -3, -4, -3, 8, -3, -2, -1, 2, 4, 3, -4, 1, 0, -5, -6, 1, -1, -2, 1, 0, 3, 0, 0, 0, 0, -1, -1, 1, 0, -1, 0, 0, -1, 0, -2, 0, 1, -1, -2],
  #[1, 6, 6, 0, -6, 0, -4, 6, 0, -1, 6, 3, -4, -3, -4, -3, 2, -4, -3, 0, -5, 2, 1, 4, 3, 3, 0, -1, -2, 1, 0, 2, 0, 0, 3, 1, -1, 2, 1, 0, 0, -1, 2, 0, 0, -1, 1, 2],
  #[-3, 2, -8, 4, 2, 0, -2, -2, -2, -3, 2, -1, 4, 3, 4, 3, 0, -2, 1, -2, -1, -2, 1, 2, -1, -1, 0, -3, 0, 1, 0, 2, 2, -2, 1, 1, -1, 0, -1, -2, 0, -1, 0, 2, 0, 1, 1, 2],
  #[3, -6, 0, -2, 4, 0, 4, -4, 0, 3, -6, -3, 2, -1, 2, 1, -2, 4, 5, 4, 5, 0, -3, -2, 1, 1, -2, 1, -2, -1, -2, 0, -2, 2, -1, -1, 1, -2, -1, 2, 0, 3, -2, 0, 0, -1, -1, -2],
  #[-11, 6, -6, 8, 2, -2, 0, 8, 0, -7, 4, -1, 0, -1, -6, -3, 2, -2, -3, -4, -3, -2, -1, 2, 3, 3, -2, 1, 0, 3, 2, 2, 0, 0, 1, 1, -1, 2, -1, -2, -2, -1, 2, 0, -2, -1, 1, 0],
  #[-1, 0, -8, 4, 6, -4, 0, -4, 0, 1, 0, -1, 2, 3, 4, 1, -2, -2, -1, -2, 1, -2, 1, 0, -1, -3, 0, 1, 2, -1, 2, 0, 2, -2, -1, -1, 1, -2, -1, 0, 0, -1, 0, 0, 0, -1, 1, 0],
  #[9, 8, 4, -2, -4, -2, -2, 2, 4, 3, 4, 1, -2, -5, -4, -3, 2, -2, -1, 2, -3, 2, -3, 0, 5, 3, -2, 1, -2, 1, 0, 0, -2, 4, 1, 1, 1, 0, 3, 0, 0, 1, 0, 0, 0, -1, 1, 0],
  #[7, 10, 6, 4, -6, -6, -2, 6, 2, -3, 8, 5, 0, -5, -8, -3, 8, -6, -3, -2, -9, 2, -3, 4, 7, 7, 0, -1, -4, 3, 0, 4, 0, 0, 3, 3, 1, 2, 1, 0, 0, -1, 4, 2, 0, -1, 1, 2],
  #[-9, -10, 2, -2, 4, 6, 2, -2, -6, 1, -6, -1, -6, 1, 4, -1, -8, 6, 1, 2, 9, -2, 3, -4, -5, -3, 0, 1, 0, -3, -2, -4, -2, 0, -3, -3, -1, 0, 1, 0, 2, 3, -2, -2, 0, 1, -1, -2],
  #[-3, -4, -6, 6, 4, -4, 2, -4, -2, -1, -2, -1, 6, 1, 0, 3, 2, 0, 1, 0, -1, 0, -1, 0, 1, 3, -2, -1, 0, 1, 0, 0, 0, 0, -1, 1, 1, -2, -1, 0, 0, 1, 0, 2, 0, -1, 1, 0],
  #[-1, -4, -6, -6, 2, 10, 0, -4, -2, -3, -6, -5, 2, 3, 6, 3, -4, 6, 3, 2, 5, -2, 1, -4, -5, -3, 0, -1, 0, -1, 2, 0, 0, 0, -1, -1, -1, 0, 1, 0, 0, 1, -2, 0, 0, 1, -1, 0],
  #[-5, 2, -4, 0, 6, 0, 6, 4, 2, -3, -2, -5, 0, -1, -2, -1, -4, 4, -1, -2, 5, -2, -1, -4, -1, -1, -2, 3, 0, 1, 2, -2, -2, 2, -3, -3, 1, 0, 1, -2, -2, 1, 0, -2, -2, -1, -1, -2],
  #[3, 14, -4, 6, 0, -8, 0, 8, 6, -5, 8, 1, 0, -3, -6, -3, 4, -4, -5, -6, -5, -2, -1, 0, 3, 1, 0, 1, 0, 3, 4, 2, 2, 0, 1, -1, 1, 2, 1, -2, -2, -3, 2, 0, -2, -1, 1, 0],
  #[3, -4, -2, 2, 6, -4, 2, -4, 0, 3, -2, -3, 2, -1, 2, 1, -2, 2, 1, 0, 1, 0, -1, -2, 1, -1, 0, 1, 2, -1, 0, -2, 0, 2, -1, -1, 3, -2, -1, 0, 2, -1, 0, 0, 0, -1, 1, 0],
  #[-5, -4, -2, -6, 4, 8, -2, 0, -4, 1, -4, -5, -6, 1, 8, -1, -10, 6, 1, 2, 9, -2, 3, -4, -5, -5, 0, 1, 0, -3, 0, -2, 0, 2, -3, -3, -1, 0, 1, 0, 2, 3, -2, -2, 0, 1, -1, 0],
  #[3, -2, -4, -6, 6, 2, 4, -4, 2, 1, -8, -5, 2, 5, 6, 1, -4, 6, 1, 0, 7, -4, -3, -6, -5, -3, -2, 3, 0, -1, 0, -2, 0, 0, -3, -1, -1, 0, -1, 0, 0, 1, -2, 0, 2, 1, -3, -2],
  #[-3, 2, -14, 6, 4, 0, 0, -8, -2, -3, -2, -1, 10, 3, 2, 5, 2, 0, 1, -2, -1, -2, -1, -2, -1, 1, -2, -3, 0, 3, 2, 2, 0, -2, -1, 1, 1, -2, -1, 0, -2, 1, 0, 0, 0, -1, 1, 0],
  #[3, 2, 4, -6, -2, 6, 0, 2, 0, -1, -2, -3, -2, -3, -2, -3, -2, 4, 1, 2, 1, 0, -3, -2, 1, 1, -2, 1, -2, 1, 0, 0, -2, 2, 1, -1, -1, 0, 1, 0, 0, 1, 0, -2, 0, -1, -1, 0],
  #[5, 2, 0, -4, -6, 2, -4, -2, 2, 3, 2, 1, 0, 1, 0, 3, 2, -2, -1, 0, -3, 2, 3, 0, -1, -3, 2, -1, 2, -1, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 0, -1, 0, 0, 0, 1, -1, 2],
  #[-9, -4, -2, 2, 8, 2, 0, 4, -4, -3, -2, -5, -4, 3, 2, -1, -6, 2, -3, 2, 3, -4, 1, 0, -1, 1, -2, 1, 0, -1, 0, -2, -2, 0, -1, -1, -1, 0, -1, -2, 0, 1, -2, 0, 0, -1, -1, 0],
  #[-3, 4, -6, 6, 6, -6, 2, 4, 0, -7, 2, -3, 6, -1, -2, 1, 2, -2, -1, -4, -3, -2, -1, 2, 1, 1, 0, -1, 2, 5, 2, 2, 2, -2, 1, 1, 1, 0, -3, -2, -2, -1, 2, 2, 0, -1, 1, 0],
  #[-1, -4, -4, 2, 2, 0, 2, -4, -2, -1, -4, -1, 4, 1, 0, 3, 2, 2, 1, 0, 1, 0, -1, -2, -1, 1, -2, 1, 0, -1, 0, 0, 0, 0, -1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, -1, 0],
  #[3, 2, -8, -4, 0, 2, -2, -8, 2, 3, -2, -1, 4, 5, 8, 3, -2, 2, 3, -2, 3, -2, 1, -4, -5, -7, 2, -1, 2, -1, 0, 0, 2, -2, -1, -1, -1, 0, -1, 0, 0, -1, -2, 0, 2, 1, -1, 0],
  #[-11, 6, -8, 8, 0, 2, -4, 2, -4, -5, 4, 3, -2, 1, -2, -1, 0, -2, -3, -4, -1, -2, 3, 0, -1, -1, 0, -1, 0, 1, 2, 2, 0, -2, -1, 1, -1, 2, 1, -2, 0, -1, 0, 0, -2, 1, 1, 0],
  #[-9, -4, 4, 6, 12, -4, 6, 12, -2, -7, -2, -7, -4, -3, -4, -5, -4, 2, -5, 0, 1, -2, -1, 2, 5, 5, -2, 3, -2, 1, 0, -2, -2, 2, -1, -1, 1, 0, -1, -2, 0, -1, 2, 0, -2, -3, 1, 0],
  #[-5, -6, -10, 2, 12, 2, 2, -4, -4, -5, -8, -7, 6, 1, 4, 1, -4, 4, -1, 0, 3, -2, -1, -4, -1, 1, -2, 1, 0, 1, 2, -2, 0, 0, -3, -1, 1, -2, -1, 0, 0, 1, 0, 0, 0, -1, 1, 0],
  #[1, 4, -12, 4, 8, -4, 2, -4, 2, -3, -4, -5, 8, 1, -2, 1, 2, 2, -3, -4, -1, -2, -3, -6, 1, -1, -4, 3, 2, 3, 4, -2, 0, 0, -1, 1, 3, 0, -1, -2, 0, -1, 0, -2, 0, -1, -1, 0],
  #[-1, -2, -6, 6, 6, -6, 2, -4, 0, 1, -2, -1, 6, 1, 0, 1, 2, -2, -1, 0, -1, 0, -3, 0, 3, 3, -2, 1, 0, 1, 0, 0, 0, 0, -1, 1, 1, -2, -1, 0, 0, 1, 0, 0, 0, -1, 1, 0],
  #[-7, 0, -6, 0, 2, 6, -2, -2, -4, -3, -2, -1, -2, 1, 2, -1, -4, 2, -1, 0, 3, -2, 1, -2, -3, -1, -2, 1, 0, -1, 2, 0, 0, 0, -1, -1, -1, 0, 1, 0, 0, 1, 0, -2, 0, -1, -1, 0],
  #[-19, 0, -12, 8, 10, 2, 2, 6, -4, -9, -2, -5, 0, 3, 0, -1, -6, 2, -3, -2, 3, -4, 1, 0, -1, 1, -2, 1, 0, 1, 2, 0, 0, 0, -3, -1, -1, 2, -1, -2, -2, 1, 0, 0, -2, -1, 1, 0],
  #[-3, 2, -2, 2, -4, 4, -4, 2, -2, -3, 4, 1, -2, -1, 0, -1, 0, -2, -1, 0, -1, 0, 1, 2, 1, -1, 0, -1, 0, -1, 2, 2, 2, 0, 1, 1, -1, 2, 1, 0, 2, -1, 2, 0, -2, 1, 1, 2],
  #[-1, -2, 4, -2, -8, 4, -4, -4, -2, 3, 2, 5, -2, 1, 2, 1, 0, -2, 1, 2, -1, 2, 3, 2, -1, -1, 2, -3, 0, -1, -2, 0, 0, 0, 1, 1, -1, 0, 1, 2, 2, 1, 0, 0, 0, 1, 1, 0],
  #[-13, -2, -12, 4, 6, 6, 0, 0, -2, -7, -2, -5, 4, 7, 4, 3, -4, 2, -1, -2, 1, -4, 1, 0, -3, -1, 0, -1, 0, 1, 2, 0, 2, -2, -1, -1, -1, 0, -1, -2, -2, -1, 0, 0, -2, -1, 1, 2],
  #[9, 6, -6, -4, 0, -2, -2, -4, 4, 1, 0, -1, 2, 3, 4, 3, 0, 0, -1, -2, 1, -2, 1, -4, -5, -5, 0, 1, 2, -1, 2, 2, 4, -4, -1, -1, -1, 0, -1, 0, 0, -1, -2, 0, 2, 1, -3, 0],
  #[5, 0, 10, -10, -6, 10, 0, 4, 0, -1, -2, 1, -6, -3, 0, -3, -2, 4, 3, 4, 3, 0, -1, 0, -1, 1, 0, 1, -4, -1, 0, 2, -2, 2, 1, -1, -1, 2, 3, 2, 0, 1, 0, 0, 0, 1, -1, 0]
]

private def cubicRows : CatalogueMatrix :=
  fun i j => (cubicRowsData.getD i.val #[]).getD j.val 0

private theorem cubic_mul_frame : Z1 * F = (12 : ℤ) • cubicRows := by
  apply mul_eq_of_dotProductRows
  intro i
  fin_cases i <;> decide +kernel

private def reconstructionRemainders (B : CatalogueMatrix) (i : Fin 48) : List ℤ :=
  List.ofFn fun j : Fin 48 =>
    (List.zipWith (· * ·) (List.ofFn (P i)) (List.ofFn fun k : Fin 48 => B k j)).sum % 12

private theorem reconstruction_dvd {B : CatalogueMatrix}
    (h : ∀ i, reconstructionRemainders B i = List.ofFn (fun _ : Fin 48 => (0 : ℤ)))
    (i j : Fin 48) : (12 : ℤ) ∣ (P * B) i j := by
  have hrow := h i
  unfold reconstructionRemainders at hrow
  have hentry := congrFun (List.ofFn_injective hrow) j
  rw [Int.dvd_iff_emod_eq_zero, Matrix.mul_apply, ← dotOfFn_eq]
  exact hentry

private theorem tRemainders (i : Fin 48) :
    reconstructionRemainders (signedRows tIndex tSign) i = List.ofFn (fun _ : Fin 48 => (0 : ℤ)) := by
  fin_cases i <;> decide +kernel

private theorem uRemainders (i : Fin 48) :
    reconstructionRemainders (signedRows uIndex uSign) i = List.ofFn (fun _ : Fin 48 => (0 : ℤ)) := by
  fin_cases i <;> decide +kernel

private theorem zRemainders (i : Fin 48) :
    reconstructionRemainders cubicRows i = List.ofFn (fun _ : Fin 48 => (0 : ℤ)) := by
  fin_cases i <;> decide +kernel

theorem t_reconstruction_dvd (i j : Fin 48) : (12 : ℤ) ∣ (P * tFrameMatrix * F) i j := by
  rw [Matrix.mul_assoc, tFrameMatrix, signed_mul_frame]
  exact reconstruction_dvd tRemainders i j

theorem u_reconstruction_dvd (i j : Fin 48) : (12 : ℤ) ∣ (P * uFrameMatrix * F) i j := by
  rw [Matrix.mul_assoc, uFrameMatrix, signed_mul_frame]
  exact reconstruction_dvd uRemainders i j

theorem z_reconstruction_dvd (i j : Fin 48) :
    (144 : ℤ) ∣ (P * Z1 * F) i j := by
  obtain ⟨q, hq⟩ := reconstruction_dvd zRemainders i j
  refine ⟨q, ?_⟩
  rw [Matrix.mul_assoc, cubic_mul_frame, Matrix.mul_smul, Matrix.smul_apply, zsmul_eq_mul, hq]
  ring

private theorem scaled_reconstruction (M : CatalogueMatrix) (n : ℤ)
    (h : ∀ i j, (12 * n) ∣ (P * M * F) i j) :
    (12 * n) • catalogueFrameMap M n = P * M * F := by
  apply Matrix.ext
  intro i j
  rw [Matrix.smul_apply, zsmul_eq_mul, catalogueFrameMap, ← p48pPairingFrame_eq]
  exact Int.mul_ediv_cancel_of_dvd (h i j)

private theorem scaled_intertwiner (M : CatalogueMatrix) (n : ℤ)
    (h : ∀ i j, (12 * n) ∣ (P * M * F) i j) :
    n • (F * catalogueFrameMap M n) = M * F := by
  have hscaled : (12 : ℤ) • (n • (F * catalogueFrameMap M n)) =
      (12 : ℤ) • (M * F) := calc
    _ = F * ((12 * n) • catalogueFrameMap M n) := by
      rw [Matrix.mul_smul, smul_smul]
    _ = (F * P) * (M * F) := by
      rw [scaled_reconstruction M n h]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [frame_mul_pairing, Matrix.smul_mul, Matrix.one_mul]
  apply Matrix.ext
  intro i j
  have hentry := congrFun (congrFun hscaled i) j
  simp only [Matrix.smul_apply, zsmul_eq_mul] at hentry ⊢
  exact mul_left_cancel₀ (by decide : (12 : ℤ) ≠ 0) hentry

theorem t_intertwines : F * tCatalogueMap = tFrameMatrix * F := by
  simpa only [one_smul, tCatalogueMap] using
    scaled_intertwiner tFrameMatrix 1 (fun i j => by simpa using t_reconstruction_dvd i j)

theorem u_intertwines : F * uCatalogueMap = uFrameMatrix * F := by
  simpa only [one_smul, uCatalogueMap] using
    scaled_intertwiner uFrameMatrix 1 (fun i j => by simpa using u_reconstruction_dvd i j)

theorem z_intertwines : (12 : ℤ) • (F * zCatalogueMap) = Z1 * F :=
  scaled_intertwiner Z1 12 (fun i j => by
    simpa only [show (12 : ℤ) * 12 = 144 by decide] using z_reconstruction_dvd i j)

/-- Entrywise extension of catalogue matrices to rational coefficients. -/
abbrev toRational : CatalogueMatrix →+* RationalMatrix := (Int.castRingHom ℚ).mapMatrix

private theorem toRational_smul (n : ℤ) (A : CatalogueMatrix) :
    toRational (n • A) = (n : ℚ) • toRational A :=
  ratCast_smul n A

private theorem toRational_injective : Function.Injective toRational :=
  Matrix.map_injective Int.cast_injective

private def frameInverse : RationalMatrix := (1 / 12 : ℚ) • toRational P

private theorem frame_mul_inverse : toRational F * frameInverse = 1 := by
  have h : toRational F * toRational P = (12 : ℚ) • 1 := by
    simpa only [map_mul, toRational_smul, Int.cast_ofNat, map_one] using
      congrArg toRational frame_mul_pairing
  rw [frameInverse, Matrix.mul_smul, h, smul_smul]
  norm_num

private theorem inverse_mul_frame : frameInverse * toRational F = 1 :=
  mul_eq_one_comm.mp frame_mul_inverse

/-- Change of basis from frame coordinates to catalogue coordinates for row actions. -/
def frameConjugate : RationalMatrix →* RationalMatrix where
  toFun O := frameInverse * O * toRational F
  map_one' := by
    change frameInverse * 1 * toRational F = 1
    rw [mul_one, inverse_mul_frame]
  map_mul' O Q := by
    change frameInverse * (O * Q) * toRational F =
      (frameInverse * O * toRational F) * (frameInverse * Q * toRational F)
    calc
      _ = frameInverse * (O * (toRational F * frameInverse) * Q) * toRational F := by
        rw [frame_mul_inverse, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem frameConjugate_apply (O : RationalMatrix) :
    frameConjugate O = (1 / 12 : ℚ) • (toRational P * O * toRational F) := by
  change ((1 / 12 : ℚ) • toRational P) * O * toRational F = _
  simp only [Matrix.smul_mul]

theorem eq_frameConjugate_iff (L O : RationalMatrix) :
    L = frameConjugate O ↔ toRational F * L = O * toRational F := by
  constructor
  · rintro rfl
    change toRational F * (frameInverse * O * toRational F) = _
    simp only [← Matrix.mul_assoc, frame_mul_inverse, one_mul]
  · intro h
    calc
      L = frameInverse * (toRational F * L) := by
        rw [← Matrix.mul_assoc, inverse_mul_frame, one_mul]
      _ = frameConjugate O := by
        change frameInverse * (toRational F * L) = frameInverse * O * toRational F
        rw [h, Matrix.mul_assoc]

private theorem frameConjugate_injective : Function.Injective frameConjugate := by
  intro O Q h
  have hO := (eq_frameConjugate_iff (frameConjugate O) O).1 rfl
  have hQ := (eq_frameConjugate_iff (frameConjugate Q) Q).1 rfl
  rw [h] at hO
  have heq := congrArg (fun X => X * frameInverse) (hO.symm.trans hQ)
  simpa only [Matrix.mul_assoc, frame_mul_inverse, mul_one] using heq

/-- The integral invertible matrices preserving the catalogue Gram form on rows. -/
def catalogueIsometries : Subgroup CatalogueMatrixˣ where
  carrier := {A | (A : CatalogueMatrix) * G * (A : CatalogueMatrix)ᵀ = G}
  one_mem' := by
    change (1 : CatalogueMatrix) * G * (1 : CatalogueMatrix)ᵀ = G
    rw [Matrix.transpose_one, one_mul, mul_one]
  mul_mem' {A B} hA hB := by
    change (A : CatalogueMatrix) * G * (A : CatalogueMatrix)ᵀ = G at hA
    change (B : CatalogueMatrix) * G * (B : CatalogueMatrix)ᵀ = G at hB
    change ((A : CatalogueMatrix) * B) * G * ((A : CatalogueMatrix) * B)ᵀ = G
    rw [Matrix.transpose_mul]
    calc
      _ = (A : CatalogueMatrix) * ((B : CatalogueMatrix) * G * (B : CatalogueMatrix)ᵀ) *
          (A : CatalogueMatrix)ᵀ := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hB, hA]
  inv_mem' {A} hA := by
    change (A : CatalogueMatrix) * G * (A : CatalogueMatrix)ᵀ = G at hA
    change (↑A⁻¹ : CatalogueMatrix) * G * (↑A⁻¹ : CatalogueMatrix)ᵀ = G
    have hInv : (↑A⁻¹ : CatalogueMatrix) * A = 1 := A.inv_val
    calc
      _ = (↑A⁻¹ : CatalogueMatrix) * ((A : CatalogueMatrix) * G * (A : CatalogueMatrix)ᵀ) *
          (↑A⁻¹ : CatalogueMatrix)ᵀ := by rw [hA]
      _ = ((↑A⁻¹ : CatalogueMatrix) * A) * G * ((↑A⁻¹ : CatalogueMatrix) * A)ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = G := by rw [hInv, Matrix.transpose_one, one_mul, mul_one]

/-- The underlying catalogue matrix of a Gram isometry. -/
def isometryMatrix : catalogueIsometries →* CatalogueMatrix :=
  (Units.coeHom CatalogueMatrix).comp catalogueIsometries.subtype

theorem isometryMatrix_preserves_gram (A : catalogueIsometries) :
    isometryMatrix A * G * (isometryMatrix A)ᵀ = G := A.property

private theorem gram_det_ne_zero : G.det ≠ 0 := by
  intro hz
  have h : (0 : ℤ) = (12 : ℤ) ^ Fintype.card (Fin 48) := by
    simpa only [Matrix.det_mul, hz, mul_zero, zero_mul,
      Matrix.det_smul, Matrix.det_one, mul_one] using
      congrArg Matrix.det p48pFrameRows_orthogonal
  exact (pow_ne_zero _ (by decide : (12 : ℤ) ≠ 0)) h.symm

private theorem isUnit_of_preserves_gram (A : CatalogueMatrix) (hA : A * G * Aᵀ = G) :
    IsUnit A := by
  have hdet := congrArg Matrix.det hA
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hprod : G.det * (A.det * A.det) = G.det * 1 := by
    rw [← mul_assoc, mul_comm G.det A.det, hdet, mul_one]
  have hone := mul_left_cancel₀ gram_det_ne_zero hprod
  exact (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_exists_inv.2 ⟨A.det, hone⟩)

private noncomputable def asCatalogueIsometry
    (A : CatalogueMatrix) (hA : A * G * Aᵀ = G) : catalogueIsometries :=
  ⟨(isUnit_of_preserves_gram A hA).unit, by
    change (↑(isUnit_of_preserves_gram A hA).unit : CatalogueMatrix) * G *
      (↑(isUnit_of_preserves_gram A hA).unit : CatalogueMatrix)ᵀ = G
    rw [IsUnit.unit_spec, hA]⟩

private theorem asCatalogueIsometry_matrix (A : CatalogueMatrix) (hA : A * G * Aᵀ = G) :
    isometryMatrix (asCatalogueIsometry A hA) = A :=
  (isUnit_of_preserves_gram A hA).unit_spec

private theorem isometryMatrix_injective : Function.Injective isometryMatrix :=
  fun _ _ h => Subtype.ext (Units.ext h)

private def catalogueEmbedding : catalogueIsometries →* RationalMatrixˣ :=
  (toRational.toMonoidHom.comp isometryMatrix).toHomUnits

private theorem catalogueEmbedding_injective : Function.Injective catalogueEmbedding := by
  intro A B h
  apply isometryMatrix_injective
  apply toRational_injective
  exact congrArg (fun X : RationalMatrixˣ => (X : RationalMatrix)) h

private def rationalAction : SL23 →* RationalMatrixˣ :=
  (frameConjugate.comp (toRational.toMonoidHom.comp frameAction)).toHomUnits

private theorem generator_lifts (g : SL23) (A : CatalogueMatrix)
    (hA : A * G * Aᵀ = G) (h : F * A = frameAction g * F) :
    rationalAction g ∈ catalogueEmbedding.range := by
  refine ⟨asCatalogueIsometry A hA, Units.ext ?_⟩
  change toRational (isometryMatrix (asCatalogueIsometry A hA)) =
    frameConjugate (toRational (frameAction g))
  rw [asCatalogueIsometry_matrix]
  apply (eq_frameConjugate_iff _ _).2
  simpa only [map_mul] using congrArg toRational h

private theorem all_lift (g : SL23) : rationalAction g ∈ catalogueEmbedding.range := by
  have hclosure : Subgroup.closure ({t, u} : Set SL23) ≤
      catalogueEmbedding.range.comap rationalAction := by
    rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · apply generator_lifts t tCatalogueMap tCatalogueMap_isometry
      rw [frameAction_t]
      exact t_intertwines
    · apply generator_lifts u uCatalogueMap uCatalogueMap_isometry
      rw [frameAction_u]
      exact u_intertwines
  rw [generators_generate] at hclosure
  exact hclosure (show g ∈ (⊤ : Subgroup SL23) from Subgroup.mem_top g)

/-- The actual signed SL(2,23) action in the integral catalogue basis. -/
noncomputable def catalogueAction : SL23 →* catalogueIsometries :=
  (MonoidHom.ofInjective catalogueEmbedding_injective).symm.toMonoidHom.comp
    (rationalAction.codRestrict catalogueEmbedding.range all_lift)

theorem catalogueAction_eq_conjugate (g : SL23) :
    toRational (isometryMatrix (catalogueAction g)) =
      frameConjugate (toRational (frameAction g)) := by
  have h := MonoidHom.apply_ofInjective_symm catalogueEmbedding_injective
    (⟨rationalAction g, all_lift g⟩ : catalogueEmbedding.range)
  exact congrArg (fun X : RationalMatrixˣ => (X : RationalMatrix)) h

theorem catalogueAction_intertwines (g : SL23) :
    F * isometryMatrix (catalogueAction g) = frameAction g * F := by
  apply toRational_injective
  simp only [map_mul]
  exact (eq_frameConjugate_iff _ _).1 (catalogueAction_eq_conjugate g)

theorem catalogueAction_injective : Function.Injective catalogueAction := by
  intro g h heq
  apply frameAction_injective
  apply toRational_injective
  apply frameConjugate_injective
  rw [← catalogueAction_eq_conjugate g, ← catalogueAction_eq_conjugate h, heq]

theorem catalogueAction_t : isometryMatrix (catalogueAction t) = tCatalogueMap := by
  apply toRational_injective
  rw [catalogueAction_eq_conjugate, frameAction_t]
  symm
  exact (eq_frameConjugate_iff _ _).2 (by
    simpa only [map_mul] using congrArg toRational t_intertwines)

theorem catalogueAction_u : isometryMatrix (catalogueAction u) = uCatalogueMap := by
  apply toRational_injective
  rw [catalogueAction_eq_conjugate, frameAction_u]
  symm
  exact (eq_frameConjugate_iff _ _).2 (by
    simpa only [map_mul] using congrArg toRational u_intertwines)

theorem cubic_frame_eq : C = (1 / 12 : ℚ) • toRational Z1 := by
  rw [P48pFrameCubicRank.C, P48pSymmetricCommutantCertificate.Z1_eq_twoJ_sub_sixI,
    map_sub, toRational_smul, toRational_smul, map_one]
  change (1 / 6 : ℚ) • (JRat - (3 : ℚ) • 1) =
    (1 / 12 : ℚ) • ((2 : ℚ) • JRat - (6 : ℚ) • 1)
  module

/-- The cubic generator represented by the integral reconstruction of C. -/
noncomputable def catalogueCubic : catalogueIsometries :=
  asCatalogueIsometry zCatalogueMap zCatalogueMap_isometry

theorem catalogueCubic_matrix : isometryMatrix catalogueCubic = zCatalogueMap :=
  asCatalogueIsometry_matrix _ _

theorem catalogueCubic_eq_conjugate :
    toRational (isometryMatrix catalogueCubic) = frameConjugate C := by
  rw [catalogueCubic_matrix]
  apply (eq_frameConjugate_iff _ _).2
  have h : (12 : ℚ) • (toRational F * toRational zCatalogueMap) =
      toRational Z1 * toRational F := by
    simpa only [map_mul, toRational_smul, Int.cast_ofNat] using congrArg toRational z_intertwines
  calc
    _ = (1 / 12 : ℚ) • ((12 : ℚ) • (toRational F * toRational zCatalogueMap)) := by
      rw [smul_smul]
      norm_num
    _ = C * toRational F := by rw [h, cubic_frame_eq, Matrix.smul_mul]

theorem catalogueCubic_cube : catalogueCubic ^ 3 = 1 := by
  apply isometryMatrix_injective
  apply toRational_injective
  rw [map_pow isometryMatrix, map_pow toRational, map_one isometryMatrix, map_one toRational,
    catalogueCubic_eq_conjugate, ← map_pow frameConjugate, C_cube, map_one]

theorem catalogueCubic_ne_one : catalogueCubic ≠ 1 := by
  intro h
  have hc : frameConjugate C = frameConjugate 1 := by
    rw [← catalogueCubic_eq_conjugate, h, map_one isometryMatrix, map_one toRational, map_one]
  have hEntry := congrFun (congrFun (frameConjugate_injective hc) (0 : Fin 48)) (0 : Fin 48)
  have h00 : C 0 0 = (-1 / 2 : ℚ) := by decide +kernel
  rw [h00, Matrix.one_apply_eq] at hEntry
  norm_num at hEntry

theorem catalogueCubic_order : orderOf catalogueCubic = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime catalogueCubic_cube catalogueCubic_ne_one

private theorem signed_commutes_J (index : Fin 48 → Fin 48) (sign : Fin 48 → ℤ)
    (hinj : Function.Injective index)
    (h : ∀ i j, sign i * J (index i) (index j) = J i j * sign j) :
    Commute (signedFrameMatrix index sign) J := by
  change signedFrameMatrix index sign * J = J * signedFrameMatrix index sign
  apply Matrix.ext
  intro i k
  obtain ⟨j, rfl⟩ := Fintype.injective_iff_surjective.mp hinj k
  rw [signed_mul_apply, Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · simpa only [signedFrameMatrix, if_pos rfl] using h i j
  · intro l _ hl
    simp only [signedFrameMatrix, if_neg (fun he => hl (hinj he)), mul_zero]

private theorem t_commutes_J : Commute tFrameMatrix J := by
  apply signed_commutes_J tIndex tSign
  · intro i
    change ∀ j : Fin 48, tIndex i = tIndex j → i = j
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

private theorem u_commutes_J : Commute uFrameMatrix J := by
  apply signed_commutes_J uIndex uSign
  · intro i
    change ∀ j : Fin 48, uIndex i = uIndex j → i = j
    fin_cases i <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

private theorem generator_commutes_cubic {g : SL23} {M : CatalogueMatrix}
    (h : frameAction g = M) (hJ : Commute M J) :
    Commute (catalogueAction g) catalogueCubic := by
  have hJRat : Commute (toRational M) JRat := hJ.map toRational
  have hC : Commute (toRational M) C := by
    show toRational M * C = C * toRational M
    simp only [P48pFrameCubicRank.C, Matrix.mul_smul, Matrix.smul_mul, mul_sub,
      sub_mul, mul_one, one_mul, hJRat.eq]
  apply Commute.of_map (f := toRational.toMonoidHom.comp isometryMatrix)
    (toRational_injective.comp isometryMatrix_injective)
  change Commute (toRational (isometryMatrix (catalogueAction g)))
    (toRational (isometryMatrix catalogueCubic))
  rw [catalogueAction_eq_conjugate, catalogueCubic_eq_conjugate, h]
  exact hC.map frameConjugate

theorem catalogueAction_commutes_cubic (g : SL23) :
    Commute (catalogueAction g) catalogueCubic := by
  let H := Subgroup.centralizer ({catalogueCubic} : Set catalogueIsometries)
  have hclosure : Subgroup.closure ({t, u} : Set SL23) ≤ H.comap catalogueAction := by
    rw [Subgroup.closure_le]
    intro a ha
    change catalogueAction a ∈ H
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact (generator_commutes_cubic frameAction_t t_commutes_J).eq
    · exact (generator_commutes_cubic frameAction_u u_commutes_J).eq
  rw [generators_generate] at hclosure
  have hg : catalogueAction g ∈ H := hclosure (Subgroup.mem_top g)
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

private theorem cubicPower_ne_action {g : SL23} {k : ℕ}
    (hdiag : (C ^ k) 0 0 = (-1 / 2 : ℚ)) :
    catalogueCubic ^ k ≠ catalogueAction g := by
  intro h
  have hFrames : C ^ k = toRational (frameAction g) := by
    apply frameConjugate_injective
    calc
      _ = toRational (isometryMatrix (catalogueCubic ^ k)) := by
        simp only [map_pow, catalogueCubic_eq_conjugate]
      _ = _ := by rw [h, catalogueAction_eq_conjugate]
  have hEntry := congrFun (congrFun hFrames (0 : Fin 48)) (0 : Fin 48)
  change (C ^ k) 0 0 = (frameAction g 0 0 : ℚ) at hEntry
  have hDen := congrArg Rat.den hEntry
  rw [hdiag, Rat.den_intCast] at hDen
  exact (by decide : ((-1 / 2 : ℚ)).den ≠ 1) hDen

private theorem action_disjoint_cubic :
    Disjoint catalogueAction.range (Subgroup.zpowers catalogueCubic) := by
  classical
  rw [disjoint_iff_inf_le]
  intro a ha
  obtain ⟨g, rfl⟩ := (show a ∈ catalogueAction.range from ha.1)
  have hFin : IsOfFinOrder catalogueCubic :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, catalogueCubic_cube⟩
  have hk := hFin.mem_zpowers_iff_mem_range_orderOf.mp ha.2
  rw [catalogueCubic_order] at hk
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hk
  have hklt := Finset.mem_range.mp hk
  interval_cases k
  · simpa only [pow_zero, Subgroup.mem_bot] using heq.symm
  · exact (cubicPower_ne_action (by rw [pow_one] <;> decide +kernel) heq).elim
  · exact (cubicPower_ne_action (by rw [C_sq] <;> decide +kernel) heq).elim

private theorem catalogueAction_commutes_cubicPowers
    (g : SL23) (c : Subgroup.zpowers catalogueCubic) :
    Commute (catalogueAction g) ((Subgroup.zpowers catalogueCubic).subtype c) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.property
  change Commute (catalogueAction g) (c : catalogueIsometries)
  rw [← hk]
  exact (catalogueAction_commutes_cubic g).zpow_right k

/-- The simultaneous SL(2,23) and C3 action by integral catalogue isometries. -/
noncomputable def catalogueProductAction :
    SL23 × Subgroup.zpowers catalogueCubic →* catalogueIsometries :=
  catalogueAction.noncommCoprod (Subgroup.zpowers catalogueCubic).subtype
    catalogueAction_commutes_cubicPowers

theorem catalogueProductAction_injective : Function.Injective catalogueProductAction := by
  refine (MonoidHom.noncommCoprod_injective _ _ catalogueAction_commutes_cubicPowers).2
    ⟨catalogueAction_injective, (Subgroup.zpowers catalogueCubic).subtype_injective, ?_⟩
  rw [Subgroup.range_subtype]
  exact action_disjoint_cubic

private abbrev extendScalars (K : Type*) [Field K] [CharZero K] :
    RationalMatrix →+* Matrix (Fin 48) (Fin 48) K := (Rat.castHom K).mapMatrix

private def frameCoordinatesToCatalogue (K : Type*) [Field K] [CharZero K] :
    (Fin 48 → K) ≃ₗ[K] (Fin 48 → K) :=
  Matrix.toLinearEquivRight'OfInv
    (M := extendScalars K frameInverse) (M' := extendScalars K (toRational F))
    (by simpa only [map_mul, map_one] using congrArg (extendScalars K) inverse_mul_frame)
    (by simpa only [map_mul, map_one] using congrArg (extendScalars K) frame_mul_inverse)

private theorem rowAction_apply (K : Type*) [Field K] [CharZero K]
    (M : RationalMatrix) (x : Fin 48 → K) :
    rowAction K M x = x ᵥ* extendScalars K M := by
  change (extendScalars K M)ᵀ *ᵥ x = x ᵥ* extendScalars K M
  exact Matrix.mulVec_transpose _ _

private theorem fixedRank_conjugate (K : Type*) [Field K] [CharZero K]
    {O L : RationalMatrix} (h : L = frameConjugate O) :
    Module.finrank K (LinearMap.ker (rowAction K L - 1)) =
      Module.finrank K (LinearMap.ker (rowAction K O - 1)) := by
  let e := frameCoordinatesToCatalogue K
  let FK := extendScalars K (toRational F)
  have hFL : FK * extendScalars K L = extendScalars K O * FK := by
    simpa only [map_mul] using congrArg (extendScalars K) ((eq_frameConjugate_iff L O).1 h)
  have he (x : Fin 48 → K) : e (rowAction K O x) = rowAction K L (e x) := by
    simp only [rowAction_apply]
    change (x ᵥ* extendScalars K O) ᵥ* FK = (x ᵥ* FK) ᵥ* extendScalars K L
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hFL]
  have hker : (LinearMap.ker (rowAction K O - 1)).map
      (e : (Fin 48 → K) →ₗ[K] (Fin 48 → K)) = LinearMap.ker (rowAction K L - 1) := by
    apply Submodule.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← he, e.injective.eq_iff]
  rw [← hker, LinearEquiv.finrank_map_eq]

private theorem neg_preserves_gram {L : CatalogueMatrix} (h : L * G * Lᵀ = G) :
    (-L) * G * (-L)ᵀ = G := by
  rw [Matrix.transpose_neg, neg_mul, neg_mul_neg, h]

private noncomputable def catalogueSignedProduct : catalogueIsometries :=
  asCatalogueIsometry (-(isometryMatrix (catalogueAction (t * u))))
    (neg_preserves_gram (isometryMatrix_preserves_gram _))

private theorem catalogueSignedProduct_eq_conjugate :
    toRational (isometryMatrix catalogueSignedProduct) = frameConjugate ARat := by
  have h : F * (tCatalogueMap * uCatalogueMap) = (tFrameMatrix * uFrameMatrix) * F := by
    rw [← Matrix.mul_assoc, t_intertwines, Matrix.mul_assoc, u_intertwines, ← Matrix.mul_assoc]
  have hneg : F * (-(tCatalogueMap * uCatalogueMap)) =
      P48pFrameCubicRank.A * F := by
    simpa only [P48pFrameCubicRank.A, neg_mul, mul_neg] using congrArg Neg.neg h
  rw [catalogueSignedProduct, asCatalogueIsometry_matrix, map_mul catalogueAction, map_mul isometryMatrix,
    catalogueAction_t, catalogueAction_u]
  apply (eq_frameConjugate_iff _ _).2
  simpa only [map_mul] using congrArg toRational hneg

/-- The three catalogue isometries obtained from the signed product and the powers of C. -/
noncomputable def catalogueMixedCubic (k : Fin 3) : catalogueIsometries :=
  catalogueSignedProduct * catalogueCubic ^ k.val

theorem catalogueMixedCubic_eq_conjugate (k : Fin 3) :
    toRational (isometryMatrix (catalogueMixedCubic k)) =
      frameConjugate (ARat * C ^ k.val) := by
  simp only [catalogueMixedCubic, map_mul, map_pow,
    catalogueSignedProduct_eq_conjugate, catalogueCubic_eq_conjugate]

/-- Each transported mixed cubic has cube one and fixed rank sixteen in characteristic zero. -/
theorem catalogueMixedCubic_cube_and_fixedRank16
    (K : Type*) [Field K] [CharZero K] (k : Fin 3) :
    catalogueMixedCubic k ^ 3 = 1 ∧
      Module.finrank K (LinearMap.ker
        (rowAction K (toRational (isometryMatrix (catalogueMixedCubic k))) - 1)) = 16 := by
  have hset : ARat * C ^ k.val ∈ ({ARat, ARat * C, ARat * C ^ 2} : Set RationalMatrix) := by
    fin_cases k <;> simp [pow_two]
  obtain ⟨_, hRank⟩ := frame_cubic_cube_and_fixedRank16 K _ hset
  refine ⟨?_, (fixedRank_conjugate K (catalogueMixedCubic_eq_conjugate k)).trans hRank⟩
  apply isometryMatrix_injective
  apply toRational_injective
  have hA : ARat ^ 3 = 1 := by
    change (toRational P48pFrameCubicRank.A) ^ 3 = 1
    rw [← map_pow, A_cube, map_one]
  have hOrder : (ARat * C ^ k.val) ^ 3 = 1 := by
    rw [(ARat_commute_C.pow_right k.val).mul_pow, pow_right_comm C k.val 3, hA, C_cube,
      one_pow, one_mul]
  rw [map_pow isometryMatrix, map_pow toRational, map_one isometryMatrix, map_one toRational,
    catalogueMixedCubic_eq_conjugate, ← map_pow frameConjugate, hOrder, map_one]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameLatticeAction
