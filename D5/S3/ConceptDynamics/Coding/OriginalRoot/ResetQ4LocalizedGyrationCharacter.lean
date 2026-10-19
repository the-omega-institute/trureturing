/- GID: D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The original reset column action carries the fixed localized gyration character and symbolic signed evaluations. -/

/- The symbolic time and I+time evaluations use the original forward column matrix and the exact signed backward factor. Their numerical calibrations are separate identities. -/
import D5.S3.ConceptDynamics.Coding.CountedLocalizedGyrationResidue
import D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResetQ4LocalizedGyrationCharacter

open scoped BigOperators
open CountedOrderTypeGyration
open ResetNumberedHistories
open InertGroupBlockConjugacy

abbrev Dyadic := GyrationDyadic
abbrev Vertex := ResetQ4OriginalLocalizedCubes.VertexIndex
abbrev OriginalMatrix := ResetQ4OriginalLocalizedCubes.DyadicMatrix
abbrev Centralizer := ResetQ4OriginalLocalizedCubes.Centralizer

private theorem dyadicGyration_signed {n m d : ℕ} [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ) :
    dyadicGyration d (R.map (algebraMap ℤ Dyadic)) (S.map (algebraMap ℤ Dyadic)) =
      (integerGyrationValue d R S : ZMod 3) := by
  exact canonicalLocalizedGyration_signed_agreement
    (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)) le_rfl
    (gyrationDyadicReduction d) _ _ R S (by ext i j; simp) (by ext i j; simp)

/-- The original enumeration is (0,false),(0,true),...,(3,true). -/
def vertexAt (k : Fin 8) : Vertex :=
  ⟨⟨k.val / 2, by omega⟩, Multiplicative.ofAdd (decide (k.val % 2 = 1))⟩

private theorem vertexAt_bijective : Function.Bijective vertexAt := by decide

def vertexEquiv : Fin 8 ≃ Vertex := Equiv.ofBijective vertexAt vertexAt_bijective

/-- Transpose the ORIGINAL COLUMN matrix in the explicitly fixed order. -/
def originalRows {R : Type*} (M : Matrix Vertex Vertex R) : Matrix (Fin 8) (Fin 8) R :=
  fun i j => M (vertexEquiv j) (vertexEquiv i)

theorem originalRows_mul {R : Type*} [CommSemiring R]
    (M N : Matrix Vertex Vertex R) :
    originalRows (M*N) = originalRows N * originalRows M := by
  ext i j
  simp only [originalRows, Matrix.mul_apply]
  calc
    (∑ v : Vertex, M (vertexEquiv j) v * N v (vertexEquiv i)) =
        ∑ k : Fin 8, M (vertexEquiv j) (vertexEquiv k) *
          N (vertexEquiv k) (vertexEquiv i) :=
      (vertexEquiv.sum_comp
        (fun v : Vertex => M (vertexEquiv j) v * N v (vertexEquiv i))).symm
    _ = ∑ k : Fin 8, N (vertexEquiv k) (vertexEquiv i) *
        M (vertexEquiv j) (vertexEquiv k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _

theorem originalRows_one {R : Type*} [Semiring R] :
    originalRows (1 : Matrix Vertex Vertex R) = 1 := by
  ext i j
  simp [originalRows, Matrix.one_apply, eq_comm]

private theorem originalRows_add {R : Type*} [Add R]
    (M N : Matrix Vertex Vertex R) :
    originalRows (M+N) = originalRows M + originalRows N := rfl

/-- Literal row adjacency; this is T-transpose, never a replacement time. -/
def originalAdjacency : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  if (j.val / 2 = 0 ∧ j.val % 2 ≠ i.val % 2) ∨
      (j.val / 2 = i.val / 2 + 1 ∧ j.val % 2 = i.val % 2) then 1 else 0

private theorem originalRows_time :
    originalRows ResetQ4OriginalLocalizedCubes.T =
      originalAdjacency.map (algebraMap ℤ Dyadic) := by
  ext i j
  change algebraMap ℤ Dyadic
      ((LinearMap.toMatrix
        (vertexBasis (H := Sign) (n := 4))
        (vertexBasis (H := Sign) (n := 4)) (transition (resetMatrix 4)))
          (vertexEquiv j) (vertexEquiv i)) = _
  rw [LinearMap.toMatrix_apply]
  have hv (v : Vertex) : vertexBasis v = vertex v.1 v.2 := by
    simp only [vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply, vertex]
  rw [hv]
  change algebraMap ℤ Dyadic
      (((transition (resetMatrix 4)
        (vertex (vertexEquiv i).1 (vertexEquiv i).2))
          (vertexEquiv j).1).coeff (vertexEquiv j).2) = _
  rw [actual_expansion_adjacency, matrix_coefficient]
  fin_cases i <;> fin_cases j <;>
    norm_num [originalAdjacency, vertexEquiv, vertexAt,
      ← ofAdd_neg, ← ofAdd_add,
      Bool.add_eq_xor, Bool.zero_eq_false,
      show (-true : Bool) = true from rfl, show (-false : Bool) = false from rfl] <;>
      (intro h; change (false : Bool) = true at h; cases h)

/-- Explicit signed factor for this PARTICULAR I+T. -/
def onePlusSignedFactor : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0,0,1,0,-1,0,1,0;
     0,0,0,1,0,-1,0,1;
     0,1,0,-1,1,1,-1,-1;
     1,0,-1,0,1,1,-1,-1;
     0,0,0,0,0,0,1,0;
     0,0,0,0,0,0,0,1;
     0,1,0,-1,0,1,0,-1;
     1,0,-1,0,1,0,-1,0]

/-- Only 8x8 matrix arithmetic, with no vertex-word enumeration. -/
private theorem onePlus_matrix_certificate :
    (1+originalAdjacency)*(1-onePlusSignedFactor) = 1 ∧
    (1-onePlusSignedFactor)*(1+originalAdjacency) = 1 ∧
    originalAdjacency*(1-onePlusSignedFactor) = onePlusSignedFactor ∧
    (1-onePlusSignedFactor)*originalAdjacency = onePlusSignedFactor := by decide

/-- The actual row polynomial cochain is pulled back along transpose. -/
def columnGyration (d : ℕ) [NeZero d] (M N : OriginalMatrix) : ZMod 3 :=
  dyadicGyration d (originalRows M) (originalRows N)

theorem columnGyration_triangle {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R U V : OriginalMatrix) :
    columnGyration d R (U*V) + columnGyration d U (V*R) =
      columnGyration d (R*U) V := by
  have h := canonicalLocalizedGyration_triangle hd
    (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)) le_rfl
    (gyrationDyadicReduction d) (originalRows U) (originalRows R) (originalRows V)
  simpa only [columnGyration, dyadicGyration, originalRows_mul, add_comm] using h

private theorem columnGyration_centralizer_product {d : ℕ} [NeZero d]
    (hd : 3 ∣ d) (A : OriginalMatrix) (U V : OriginalMatrixˣ)
    (hU : Commute (U : OriginalMatrix) A) :
    columnGyration d ((U*V : OriginalMatrixˣ) : OriginalMatrix) (↑((U*V)⁻¹)*A) =
      columnGyration d (U : OriginalMatrix) (↑U⁻¹*A) +
      columnGyration d (V : OriginalMatrix) (↑V⁻¹*A) :=
  SourceOnlyLocalizedCocycle.centralizer_product A (columnGyration d)
    (columnGyration_triangle hd) U V hU

/-- The target uses Multiplicative solely to encode addition of ZMod 3.
No arbitrary supplied chi occurs in this construction. -/
def gamma (d : ℕ) [NeZero d] (hd : 3 ∣ d) : Centralizer →* Multiplicative (ZMod 3) where
  toFun U := Multiplicative.ofAdd
    (columnGyration d ((U : OriginalMatrixˣ) : OriginalMatrix)
      (↑((U : OriginalMatrixˣ)⁻¹)*ResetQ4OriginalLocalizedCubes.T))
  map_one' := by
    change columnGyration d (1 : OriginalMatrix)
      ((1 : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T) = 0
    rw [one_mul]
    have h : columnGyration d (1 : OriginalMatrix) ResetQ4OriginalLocalizedCubes.T +
        columnGyration d (1 : OriginalMatrix) ResetQ4OriginalLocalizedCubes.T =
        columnGyration d (1 : OriginalMatrix) ResetQ4OriginalLocalizedCubes.T := by
      simpa only [one_mul, mul_one] using
        columnGyration_triangle hd (1 : OriginalMatrix) 1 ResetQ4OriginalLocalizedCubes.T
    exact add_left_cancel (h.trans (add_zero _).symm)
  map_mul' U V := by
    exact congrArg Multiplicative.ofAdd
      (columnGyration_centralizer_product hd ResetQ4OriginalLocalizedCubes.T
        (U : OriginalMatrixˣ) (V : OriginalMatrixˣ)
        (by
          have hUnits :
              (ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ) * (U : OriginalMatrixˣ) =
                (U : OriginalMatrixˣ) * (ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ) :=
            Subgroup.mem_centralizer_iff.mp U.property
              (ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ) (by
                change (ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ) ∈
                  ({(ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ)} : Set OriginalMatrixˣ)
                exact Set.mem_singleton _)
          change ((U : OriginalMatrixˣ) : OriginalMatrix) * ResetQ4OriginalLocalizedCubes.T =
            ResetQ4OriginalLocalizedCubes.T * ((U : OriginalMatrixˣ) : OriginalMatrix)
          simpa only [Units.val_mul, ResetQ4OriginalLocalizedCubes.time_val] using
            congrArg (fun W : OriginalMatrixˣ => (W : OriginalMatrix)) hUnits.symm))

def Gamma : Centralizer →* Multiplicative (ZMod 3) :=
  gamma 3 (by decide) * gamma 6 (by decide)

/-- The residue bridge is consumed at the LITERAL original time unit. -/
theorem gamma_time_signed_evaluation (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    Multiplicative.toAdd (gamma d hd ResetQ4OriginalLocalizedCubes.time) =
      (integerGyrationValue d originalAdjacency 1 : ZMod 3) := by
  have hi :
      (↑((ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ)⁻¹) : OriginalMatrix) *
        ResetQ4OriginalLocalizedCubes.T = 1 := by
    rw [← ResetQ4OriginalLocalizedCubes.time_val]
    exact Units.inv_mul _
  change columnGyration d
    ((ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ) : OriginalMatrix)
    (↑((ResetQ4OriginalLocalizedCubes.time : OriginalMatrixˣ)⁻¹) *
      ResetQ4OriginalLocalizedCubes.T) = _
  rw [ResetQ4OriginalLocalizedCubes.time_val, hi]
  unfold columnGyration
  rw [originalRows_time, originalRows_one]
  simpa only [Matrix.map_one (algebraMap ℤ Dyadic)
    (map_zero (algebraMap ℤ Dyadic)) (map_one (algebraMap ℤ Dyadic))] using
      dyadicGyration_signed (d := d) originalAdjacency 1

/-- This is the new signed consumer at I+T. In particular, zeros and negative
entries are handled by proved residue constancy, not positive agreement alone. -/
theorem gamma_onePlus_signed_evaluation (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    Multiplicative.toAdd (gamma d hd ResetQ4OriginalLocalizedCubes.onePlusTime) =
      (integerGyrationValue d (1+originalAdjacency) onePlusSignedFactor : ZMod 3) := by
  let U : OriginalMatrixˣ := ResetQ4OriginalLocalizedCubes.onePlusTime
  let Q : Matrix (Fin 8) (Fin 8) ℤ := 1-onePlusSignedFactor
  have hU : originalRows (U : OriginalMatrix) =
      (1+originalAdjacency).map (algebraMap ℤ Dyadic) := by
    rw [show (U : OriginalMatrix) = 1+ResetQ4OriginalLocalizedCubes.T from
      ResetQ4OriginalLocalizedCubes.onePlusTime_val]
    rw [originalRows_add, originalRows_one, originalRows_time,
      Matrix.map_add (algebraMap ℤ Dyadic) (map_add (algebraMap ℤ Dyadic)),
      Matrix.map_one (algebraMap ℤ Dyadic)
        (map_zero (algebraMap ℤ Dyadic)) (map_one (algebraMap ℤ Dyadic))]
  have hQ : originalRows (U : OriginalMatrix) * Q.map (algebraMap ℤ Dyadic) = 1 := by
    rw [hU, ← Matrix.map_mul, onePlus_matrix_certificate.1,
      Matrix.map_one (algebraMap ℤ Dyadic)
        (map_zero (algebraMap ℤ Dyadic)) (map_one (algebraMap ℤ Dyadic))]
  have hprod : originalRows ((↑U⁻¹ : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T) *
      originalRows (U : OriginalMatrix) = originalRows ResetQ4OriginalLocalizedCubes.T := by
    rw [← originalRows_mul, Units.mul_inv_cancel_left]
  have hS : originalRows ((↑U⁻¹ : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T) =
      onePlusSignedFactor.map (algebraMap ℤ Dyadic) := by
    calc
      _ = originalRows ((↑U⁻¹ : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T) *
          (originalRows (U : OriginalMatrix) * Q.map (algebraMap ℤ Dyadic)) := by rw [hQ, mul_one]
      _ = (originalRows ((↑U⁻¹ : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T) *
          originalRows (U : OriginalMatrix)) * Q.map (algebraMap ℤ Dyadic) := (mul_assoc _ _ _).symm
      _ = originalAdjacency.map (algebraMap ℤ Dyadic) * Q.map (algebraMap ℤ Dyadic) := by
        rw [hprod, originalRows_time]
      _ = onePlusSignedFactor.map (algebraMap ℤ Dyadic) := by
        rw [← Matrix.map_mul]
        exact congrArg
          (fun M : Matrix (Fin 8) (Fin 8) ℤ => M.map (algebraMap ℤ Dyadic))
          onePlus_matrix_certificate.2.2.1
  change dyadicGyration d (originalRows (U : OriginalMatrix))
    (originalRows ((↑U⁻¹ : OriginalMatrix)*ResetQ4OriginalLocalizedCubes.T)) = _
  rw [hU, hS]
  exact dyadicGyration_signed (d := d) (1+originalAdjacency) onePlusSignedFactor

end D5.S3.ConceptDynamics.Coding.ResetQ4LocalizedGyrationCharacter
