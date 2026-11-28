/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pTernaryPaleyGraph
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pTernaryPaleyGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual P48p ternary frame kernel is the graph of its signed Paley conference matrix. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pOddNeighbor
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameProjectiveAction
import OmegaBuild.Commands

/-!
# The P48p ternary Paley graph

Signed projective chart coordinates identify the odd-neighbor syndrome kernel
with the graph of a conference matrix over `ZMod 3`.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pTernaryPaleyGraph

open scoped BigOperators Matrix
open D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameProjectiveAction
  (Direction F23 normalizedRow frameChart chartSign)
open D5.S3.VertexAlgebra.Lattice.Orbifold.P48pOddNeighbor (frameSyndrome)
open D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame (p48pFrameRows)

abbrev F3 := ZMod 3

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

-- The finite index 23 denotes the projective direction at infinity.
private def paleyDirection (d : Fin 24) : Direction :=
  if d.val = 23 then none else some (d.val : F23)

private def directionEquiv : Fin 24 ≃ Direction where
  toFun := paleyDirection
  invFun := fun d => match d with
    | none => ⟨23, by decide⟩
    | some k => ⟨k.val, lt_trans k.val_lt (by decide : 23 < 24)⟩
  left_inv := by
    intro d
    fin_cases d <;> decide +kernel
  right_inv := by
    intro d
    cases d with
    | none => rfl
    | some k =>
      change paleyDirection ⟨k.val, _⟩ = some k
      rw [paleyDirection, if_neg (ne_of_lt k.val_lt), ZMod.natCast_zmod_val]

private def chartIndexEquiv : (Fin 24 × Fin 2) ≃ Fin 48 :=
  (directionEquiv.prodCongr (Equiv.refl (Fin 2))).trans frameChart.symm

private def chartIndex (d : Fin 24) (k : Fin 2) : Fin 48 := chartIndexEquiv (d, k)

/-- The two signed chart blocks of the actual frame rows, reduced modulo three. -/
private def signedFrameBlock (k : Fin 2) : Matrix (Fin 24) (Fin 48) F3 :=
  fun d j =>
    (chartSign (chartIndex d k) : F3) *
      (p48pFrameRows (chartIndex d k) j : F3)

/-- Signed chart coordinates of a ternary word, ordered by slopes
`0, …, 22` followed by infinity. -/
def signedChartWord (u : Fin 48 → F3) (k : Fin 2) : Fin 24 → F3 :=
  fun d => (chartSign (chartIndex d k) : F3) * u (chartIndex d k)

private def normalizedRows (d e : Fin 24) : Matrix (Fin 2) (Fin 2) F23 :=
  fun i j => if i = 0 then normalizedRow (paleyDirection d) j
    else normalizedRow (paleyDirection e) j

/-- The Paley entry is the quadratic character of the determinant of the two
normalized projective rows, with the character reduced to `ZMod 3`. -/
def paleyC : Matrix (Fin 24) (Fin 24) F3 :=
  fun d e =>
    (quadraticChar F23 (Matrix.det (normalizedRows d e)) : F3)

private def characterTable : Fin 23 → ℤ := ![
  0, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1,
  1, 1, -1, -1, 1, -1, 1, -1, -1, -1, -1]

private theorem quadraticChar_eq_table (x : Fin 23) :
    quadraticChar F23 x = characterTable x := by
  have hchar : ringChar F23 ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have table (i : Fin 23) :
      (if (i : F23) = 0 then 0 else if (i : F23) ^ (11 : ℕ) = 1 then 1 else -1 : ℤ) =
        characterTable i := by
    fin_cases i <;> decide +kernel
  by_cases hx : (x : F23) = 0
  · calc
      quadraticChar F23 x = quadraticChar F23 (0 : F23) := congrArg (quadraticChar F23) hx
      _ = 0 := @quadraticChar_zero F23 _ _ _
      _ = characterTable x := by simpa only [if_pos hx] using table x
  · rw [quadraticChar_eq_pow_of_char_ne_two hchar hx, ZMod.card]
    have hhalf : (23 / 2 : ℕ) = 11 := by decide
    rw [hhalf]
    convert table x using 1 <;> simp only [if_neg hx] <;> rfl

private def paleyCComputable : Matrix (Fin 24) (Fin 24) F3 :=
  fun d e =>
    let r := normalizedRow (paleyDirection d)
    let s := normalizedRow (paleyDirection e)
    (characterTable (r 0 * s 1 - r 1 * s 0) : F3)

private theorem paleyC_eq_computable : paleyC = paleyCComputable := by
  apply Matrix.ext
  intro d e
  change (quadraticChar F23 (Matrix.det (normalizedRows d e)) : F3) = _
  rw [Matrix.det_fin_two]
  exact congrArg (fun z : ℤ => (z : F3)) (quadraticChar_eq_table _)

/-- The first twenty-four columns of the second signed chart block. -/
private def pivotColumn (j : Fin 24) : Fin 48 :=
  ⟨j.val, lt_trans j.isLt (by decide : 24 < 48)⟩

private def signedFramePivot : Matrix (Fin 24) (Fin 24) F3 :=
  fun d j => signedFrameBlock 1 d (pivotColumn j)

private def pivotInverseData : Array (Array ℕ) := #[
  #[1, 2, 2, 2, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 1, 2, 1, 0, 0, 2],
  #[1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 2, 1, 2, 1],
  #[2, 2, 0, 0, 2, 0, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 2, 2, 2],
  #[2, 1, 1, 2, 0, 0, 2, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 0, 1, 1, 2, 1, 2, 2],
  #[0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1, 2, 0, 2, 1, 0, 0, 2, 1, 0, 0, 1, 2, 1],
  #[1, 1, 0, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0, 0, 0, 1, 2, 1, 0, 0, 1, 0],
  #[2, 0, 0, 2, 0, 0, 0, 1, 1, 2, 2, 0, 1, 1, 2, 1, 2, 1, 0, 1, 2, 2, 2, 1],
  #[1, 0, 0, 1, 1, 1, 1, 1, 2, 0, 1, 0, 1, 0, 0, 0, 0, 2, 2, 0, 1, 1, 1, 1],
  #[2, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 0, 2, 0, 1, 2, 1, 2, 2, 2, 1, 2, 2],
  #[1, 0, 0, 0, 2, 0, 0, 0, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 0, 2, 1, 0, 0, 0],
  #[0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 0, 0, 2, 0, 2],
  #[1, 1, 1, 1, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 0, 1, 2, 0, 0, 2, 1, 2, 2, 2],
  #[1, 1, 2, 1, 2, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 1, 0, 0],
  #[0, 2, 2, 2, 1, 1, 1, 0, 2, 0, 0, 1, 1, 2, 2, 2, 2, 1, 0, 1, 1, 1, 2, 2],
  #[2, 2, 2, 0, 1, 0, 1, 2, 2, 0, 2, 1, 1, 1, 1, 1, 1, 2, 0, 0, 1, 2, 2, 0],
  #[1, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 2, 2, 1, 0, 0],
  #[0, 0, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 0, 1, 0, 2, 1, 2, 1, 1, 2],
  #[2, 0, 2, 2, 0, 2, 2, 0, 1, 2, 2, 0, 0, 1, 0, 2, 0, 2, 2, 0, 0, 1, 2, 1],
  #[1, 0, 2, 0, 1, 2, 2, 0, 2, 2, 1, 1, 1, 2, 0, 0, 1, 2, 1, 1, 1, 1, 2, 2],
  #[0, 1, 0, 0, 2, 2, 2, 1, 1, 2, 2, 2, 0, 1, 2, 2, 0, 2, 1, 2, 0, 2, 1, 2],
  #[1, 1, 1, 1, 1, 0, 2, 1, 2, 0, 0, 2, 2, 2, 1, 2, 0, 2, 1, 0, 1, 0, 2, 0],
  #[1, 1, 2, 0, 1, 1, 2, 1, 1, 0, 1, 0, 0, 2, 1, 0, 2, 1, 0, 2, 2, 1, 1, 1],
  #[1, 1, 0, 2, 0, 0, 0, 1, 1, 2, 1, 2, 1, 2, 2, 0, 2, 2, 1, 1, 0, 1, 2, 0],
  #[2, 1, 2, 2, 2, 2, 1, 2, 0, 0, 0, 0, 1, 1, 2, 2, 0, 2, 0, 0, 2, 1, 0, 2]
]

private def pivotInverse : Matrix (Fin 24) (Fin 24) F3 :=
  fun i j => (pivotInverseData.getD i.val #[]).getD j.val 0

-- Check one row at a time using lists for the closed dot products.
set_option maxHeartbeats 6000000 in
private theorem signedFrameBlock_graph :
    signedFrameBlock 0 + paleyC * signedFrameBlock 1 = 0 := by
  rw [paleyC_eq_computable]
  apply Matrix.ext
  intro d j
  have row : List.ofFn (fun col : Fin 48 => signedFrameBlock 0 d col +
      (List.ofFn (fun e : Fin 24 => paleyCComputable d e * signedFrameBlock 1 e col)).sum) =
      List.ofFn (fun _ : Fin 48 => (0 : F3)) := by
    fin_cases d <;> decide +kernel
  simpa only [List.sum_ofFn, Matrix.mul_apply, Matrix.add_apply, Matrix.zero_apply] using
    congrFun (List.ofFn_injective row) j

set_option maxHeartbeats 6000000 in
private theorem signedFramePivot_mul_inverse :
    signedFramePivot * pivotInverse = 1 := by
  apply Matrix.ext
  intro d e
  have row : List.ofFn (fun col : Fin 24 =>
      (List.ofFn (fun k : Fin 24 => signedFramePivot d k * pivotInverse k col)).sum) =
      List.ofFn (fun col : Fin 24 => if d = col then (1 : F3) else 0) := by
    fin_cases d <;> decide +kernel
  simpa only [List.sum_ofFn, Matrix.mul_apply, Matrix.one_apply] using
    congrFun (List.ofFn_injective row) e

set_option maxHeartbeats 6000000 in
/-- The conference matrix squares to the identity over the ternary field. -/
theorem paleyC_sq : paleyC * paleyC = 1 := by
  rw [paleyC_eq_computable]
  apply Matrix.ext
  intro d e
  have row : List.ofFn (fun col : Fin 24 =>
      (List.ofFn (fun k : Fin 24 => paleyCComputable d k * paleyCComputable k col)).sum) =
      List.ofFn (fun col : Fin 24 => if d = col then (1 : F3) else 0) := by
    fin_cases d <;> decide +kernel
  simpa only [List.sum_ofFn, Matrix.mul_apply, Matrix.one_apply] using
    congrFun (List.ofFn_injective row) e

private theorem chartSign_sq (i : Fin 48) :
    (chartSign i : F3) * (chartSign i : F3) = 1 := by
  fin_cases i <;> decide +kernel

private theorem frameSyndrome_eq_chart_blocks (u : Fin 48 → F3) :
    frameSyndrome u =
      (signedChartWord u 0) ᵥ* signedFrameBlock 0 +
        (signedChartWord u 1) ᵥ* signedFrameBlock 1 := by
  funext j
  change (((p48pFrameRows.map (Int.castRingHom F3))ᵀ) *ᵥ u) j = _
  rw [Matrix.mulVec_transpose]
  simp only [Pi.add_apply, Matrix.vecMul_apply_eq_sum]
  calc
    _ = ∑ p : Fin 24 × Fin 2, u (chartIndexEquiv p) *
        (p48pFrameRows (chartIndexEquiv p) j : F3) := by
      symm
      exact chartIndexEquiv.sum_comp
        (fun i : Fin 48 => u i * (p48pFrameRows i j : F3))
    _ = ∑ d : Fin 24, ∑ k : Fin 2, signedChartWord u k d * signedFrameBlock k d j := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro k _
      have hindex : chartIndexEquiv (d, k) = chartIndex d k := rfl
      rw [hindex]
      change _ = ((chartSign (chartIndex d k) : F3) * u (chartIndex d k)) *
        ((chartSign (chartIndex d k) : F3) * (p48pFrameRows (chartIndex d k) j : F3))
      rw [mul_mul_mul_comm, chartSign_sq, one_mul]
    _ = _ := by simp only [Fin.sum_univ_two, Finset.sum_add_distrib]

/-- A word in the actual odd-neighbor kernel has second signed half equal to
its first signed half multiplied by the Paley matrix. -/
theorem frameSyndrome_eq_zero_iff_signedChart_graph (u : Fin 48 → F3) :
    frameSyndrome u = 0 ↔
      signedChartWord u 1 = (signedChartWord u 0) ᵥ* paleyC := by
  rw [frameSyndrome_eq_chart_blocks]
  have hrewrite (a : Fin 24 → F3) (b : Fin 24 → F3) :
      a ᵥ* signedFrameBlock 0 + b ᵥ* signedFrameBlock 1 =
        (b - (a ᵥ* paleyC)) ᵥ* signedFrameBlock 1 := by
    have h : a ᵥ* signedFrameBlock 0 + a ᵥ* (paleyC * signedFrameBlock 1) = 0 := by
      rw [← Matrix.vecMul_add, signedFrameBlock_graph, Matrix.vecMul_zero]
    rw [Matrix.sub_vecMul, Matrix.vecMul_vecMul, sub_eq_add_neg, ← eq_neg_of_add_eq_zero_left h]
    exact add_comm _ _
  rw [hrewrite (signedChartWord u 0) (signedChartWord u 1)]
  constructor
  · intro hzero
    have hp : (signedChartWord u 1 - (signedChartWord u 0 ᵥ* paleyC)) ᵥ*
        signedFramePivot = 0 := by
      funext j
      exact congrFun hzero (pivotColumn j)
    have hpi := congrArg (fun v : Fin 24 → F3 => v ᵥ* pivotInverse) hp
    have hz : signedChartWord u 1 - (signedChartWord u 0 ᵥ* paleyC) = 0 := by
      simpa only [Matrix.vecMul_vecMul, signedFramePivot_mul_inverse,
        Matrix.vecMul_one, Matrix.zero_vecMul] using hpi
    exact sub_eq_zero.mp hz
  · intro hgraph
    rw [hgraph, sub_self, Matrix.zero_vecMul]

#print axioms frameSyndrome_eq_zero_iff_signedChart_graph
#print axioms paleyC_sq

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pTernaryPaleyGraph
