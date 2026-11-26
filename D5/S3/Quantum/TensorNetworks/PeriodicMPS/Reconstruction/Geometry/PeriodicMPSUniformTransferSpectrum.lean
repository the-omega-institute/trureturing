/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSpectrum
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferSpectrum
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The transfer quartic determines the trace-power recurrence and its spectral form. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTransferTracePowers
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Characteristic polynomial of the trace-aligned mixed transfer

The four literal power traces determine the quartic over ℂ. A simultaneous
reindexing of rows and columns by the swap of the bond indices gives the
same characteristic polynomial in ket-first order.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferSpectrum

open Polynomial
open PeriodicMPSUniformTransferTracePowers (mixedTransfer_trace_powers)
open scoped BigOperators Kronecker

-- The degree-four Newton formula, checked by expanding the determinant of
-- the characteristic matrix along its first row. This works for arbitrary
-- matrices, including those whose characteristic roots have multiplicity.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem charpoly_fin_four_newton (M : Matrix (Fin 4) (Fin 4) ℂ) :
    M.charpoly = X ^ 4 - C M.trace * X ^ 3 +
      C ((M.trace ^ 2 - (M ^ 2).trace) / 2) * X ^ 2 -
      C ((M.trace ^ 3 - 3 * M.trace * (M ^ 2).trace + 2 * (M ^ 3).trace) / 6) * X +
      C ((M.trace ^ 4 - 6 * M.trace ^ 2 * (M ^ 2).trace + 3 * (M ^ 2).trace ^ 2 +
        8 * M.trace * (M ^ 3).trace - 6 * (M ^ 4).trace) / 24) := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num (config := {decide := true}) [Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply, Fin.succAbove,
    Fin.succ, Fin.castSucc, Fin.castAdd, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_four, pow_succ]
  ring!

private theorem charpoly_of_four_traces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι ≃ Fin 4) (T : Matrix ι ι ℂ) (a b c : ℂ)
    (h1 : T.trace = 1) (h2 : (T ^ 2).trace = 1 - 2 * a)
    (h3 : (T ^ 3).trace = 1 - 3 * a + 3 * b)
    (h4 : (T ^ 4).trace = 1 - 4 * a + 2 * a ^ 2 + 4 * b - 4 * c) :
    T.charpoly = X ^ 4 - X ^ 3 + C a * X ^ 2 - C b * X + C c := by
  let reindex := Matrix.reindexAlgEquiv ℂ ℂ index
  have htrace (M : Matrix ι ι ℂ) : (reindex M).trace = M.trace := by
    change (∑ j : Fin 4, M (index.symm j) (index.symm j)) = ∑ i : ι, M i i
    exact Equiv.sum_comp index.symm (fun i => M i i)
  have hpower (j : ℕ) : (reindex T ^ j).trace = (T ^ j).trace := by
    rw [← map_pow reindex T j, htrace]
  have hpoly : (reindex T).charpoly = T.charpoly := Matrix.charpoly_reindex index T
  rw [← hpoly, charpoly_fin_four_newton, htrace T, hpower 2, hpower 3, hpower 4,
    h1, h2, h3, h4]
  have ha : ((1 : ℂ) ^ 2 - (1 - 2 * a)) / 2 = a := by ring
  have hb : ((1 : ℂ) ^ 3 - 3 * 1 * (1 - 2 * a) + 2 * (1 - 3 * a + 3 * b)) / 6 = b := by
    ring
  have hc : ((1 : ℂ) ^ 4 - 6 * 1 ^ 2 * (1 - 2 * a) + 3 * (1 - 2 * a) ^ 2 +
      8 * 1 * (1 - 3 * a + 3 * b) - 6 * (1 - 4 * a + 2 * a ^ 2 + 4 * b - 4 * c)) / 24 = c := by
    ring
  rw [ha, hb, hc, map_one, one_mul]

/-- The literal bra-first mixed transfer on the complex trace-aligned chart
has characteristic polynomial X⁴ − X³ + a X² − b X + c. -/
theorem braFirst_charpoly_trace_aligned
    (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hket0 : (ket 0).trace = 1) (hket1 : (ket 1).trace = 0)
    (hbra0 : (bra 0).trace = 1) (hbra1 : (bra 1).trace = 0)
    (hket01 : (ket 0 * ket 1).trace = k) (hbra01 : (bra 0 * bra 1).trace = k) :
    let d := (ket 0).det
    let db := (bra 0).det
    let e := (ket 1).det
    let eb := (bra 1).det
    let U := d * db
    let a := d + db - 2 * (U + e * eb) - k ^ 2
    let b := U - e * eb
    let c := b ^ 2 + k ^ 2 * (d + eb) * (db + e)
    ((bra 0 ⊗ₖ ket 0) + (bra 1 ⊗ₖ ket 1)).charpoly =
      X ^ 4 - X ^ 3 + C a * X ^ 2 - C b * X + C c := by
  dsimp only
  obtain ⟨h1, h2, h3, h4⟩ :=
    mixedTransfer_trace_powers ket bra k hket0 hket1 hbra0 hbra1 hket01 hbra01
  exact charpoly_of_four_traces (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)
    ((bra 0 ⊗ₖ ket 0) + (bra 1 ⊗ₖ ket 1)) _ _ _ h1 h2 h3 h4

/-- The same quartic for the literal ket-first tensor sum. -/
theorem ketFirst_charpoly_trace_aligned
    (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) (k : ℂ)
    (hket0 : (ket 0).trace = 1) (hket1 : (ket 1).trace = 0)
    (hbra0 : (bra 0).trace = 1) (hbra1 : (bra 1).trace = 0)
    (hket01 : (ket 0 * ket 1).trace = k) (hbra01 : (bra 0 * bra 1).trace = k) :
    let d := (ket 0).det
    let db := (bra 0).det
    let e := (ket 1).det
    let eb := (bra 1).det
    let U := d * db
    let a := d + db - 2 * (U + e * eb) - k ^ 2
    let b := U - e * eb
    let c := b ^ 2 + k ^ 2 * (d + eb) * (db + e)
    ((ket 0 ⊗ₖ bra 0) + (ket 1 ⊗ₖ bra 1)).charpoly =
      X ^ 4 - X ^ 3 + C a * X ^ 2 - C b * X + C c := by
  dsimp only
  let swap := Equiv.prodComm (Fin 2) (Fin 2)
  have hswap :
      Matrix.reindex swap swap ((bra 0 ⊗ₖ ket 0) + (bra 1 ⊗ₖ ket 1)) =
      (ket 0 ⊗ₖ bra 0) + (ket 1 ⊗ₖ bra 1) := by
    apply Matrix.ext
    rintro ⟨i, l⟩ ⟨j, m⟩
    change bra 0 l m * ket 0 i j + bra 1 l m * ket 1 i j =
      ket 0 i j * bra 0 l m + ket 1 i j * bra 1 l m
    rw [mul_comm (bra 0 l m) (ket 0 i j), mul_comm (bra 1 l m) (ket 1 i j)]
  rw [← hswap, Matrix.charpoly_reindex]
  exact braFirst_charpoly_trace_aligned ket bra k hket0 hket1 hbra0 hbra1 hket01 hbra01

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferSpectrum
