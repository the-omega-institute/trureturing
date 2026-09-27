/- GID: D5/S0/FiniteGeometry/HypercubeInequality
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/HypercubeInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The determinant-defined hypercube inequality in every positive dimension. -/

import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Int.Lemmas

open scoped BigOperators EuclideanSpace MatrixOrder

open Matrix Polynomial

noncomputable section

namespace D5.S0.FiniteGeometry.HypercubeInequality

def augmentedCube (d : ℕ) : Matrix (Fin d ⊕ Unit) (Fin d → Bool) ℤ
  | Sum.inl i, v => v i |>.toNat
  | Sum.inr _, _ => 1

def hypercubeWeight (d : ℕ) (x : (Fin d → Bool) → ℝ) : ℝ :=
  ∑ S : {s : Finset (Fin d → Bool) // s.card = d + 1},
    (Int.natAbs
      (((augmentedCube d).submatrix id (Subtype.val : S.1 → (Fin d → Bool))).submatrix
        (Fintype.equivOfCardEq (by simpa using S.property.symm)).symm id).det : ℝ) *
      ∏ v : S.1, x v

set_option maxHeartbeats 800000 in
-- The direct determinant expansion and PSD bound elaborate in one source theorem.
theorem result (d : ℕ) (hd : 1 ≤ d) (x : (Fin d → Bool) → ℝ)
    (hx : ∀ v, 0 ≤ x v) :
    hypercubeWeight d x * (∑ v, x v) ^ (d - 1) ≤
      ∏ i, (∑ v, if v i = false then x v else 0) *
        (∑ v, if v i = true then x v else 0) := by
  have hExpansion :
      (((augmentedCube d).map (Int.castRingHom ℝ)) *
      (Matrix.diagonal x * ((augmentedCube d).map (Int.castRingHom ℝ)).transpose)).det =
      ∑ S : {s : Finset (Fin d → Bool) // s.card = d + 1},
        (∏ v : S.1, x v) *
          (Int.natAbs
            (((augmentedCube d).submatrix id (Subtype.val : S.1 → (Fin d → Bool))).submatrix
              (Fintype.equivOfCardEq (by simpa using S.property.symm)).symm id).det : ℝ) ^ 2 := by
    let A := (augmentedCube d).map (Int.castRingHom ℝ)
    have rectangularExpansion
        (P : Matrix (Fin d ⊕ Unit) (Fin d → Bool) ℝ)
        (Q : Matrix (Fin d → Bool) (Fin d ⊕ Unit) ℝ) :
        (P * Q).det =
          ∑ s ∈ (Finset.univ : Finset (Fin d → Bool)).powersetCard
              (Fintype.card (Fin d ⊕ Unit)),
            ((Q * P).submatrix (Subtype.val : s → (Fin d → Bool))
              (Subtype.val : s → (Fin d → Bool))).det := by
      have hpoly :
          Matrix.det (1 + (X : ℝ[X]) • (P * Q).map C) =
            Matrix.det (1 + (X : ℝ[X]) • (Q * P).map C) := by
        simpa [Matrix.map_mul, Matrix.mul_smul, Matrix.smul_mul] using
          (Matrix.det_one_add_mul_comm (P.map C) ((X : ℝ[X]) • Q.map C))
      have hcoeff := congrArg (fun p : ℝ[X] =>
        p.coeff (Fintype.card (Fin d ⊕ Unit))) hpoly
      rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
        Matrix.coeff_det_one_add_X_smul_eq_sum_minors] at hcoeff
      have hpowerset :
          (Finset.univ : Finset (Fin d ⊕ Unit)).powersetCard
            (Fintype.card (Fin d ⊕ Unit)) = {Finset.univ} := by
        simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin d ⊕ Unit))
      rw [hpowerset] at hcoeff
      simp only [Finset.sum_singleton] at hcoeff
      let e : {z // z ∈ (Finset.univ : Finset (Fin d ⊕ Unit))} ≃ (Fin d ⊕ Unit) :=
        { toFun := Subtype.val
          invFun := fun z => ⟨z, Finset.mem_univ z⟩
          left_inv := fun z => Subtype.ext (by rfl)
          right_inv := fun _ => rfl }
      have htop :
          (((P * Q).submatrix
            (Subtype.val :
              {z // z ∈ (Finset.univ : Finset (Fin d ⊕ Unit))} → (Fin d ⊕ Unit))
            (Subtype.val :
              {z // z ∈ (Finset.univ : Finset (Fin d ⊕ Unit))} → (Fin d ⊕ Unit))).det) =
            (P * Q).det := by
        simpa [e] using Matrix.det_submatrix_equiv_self e (P * Q)
      rw [htop] at hcoeff
      exact hcoeff
    have weightedTerm
        (P : Matrix (Fin d ⊕ Unit) (Fin d → Bool) ℝ)
        (w : (Fin d → Bool) → ℝ) (s : Finset (Fin d → Bool))
        (e : (Fin d ⊕ Unit) ≃ s) :
        Matrix.det ((((Matrix.diagonal w) * P.transpose) * P).submatrix
          (Subtype.val : s → (Fin d → Bool)) (Subtype.val : s → (Fin d → Bool))) =
          (∏ i : s, w i) *
            (((P.submatrix id (Subtype.val : s → (Fin d → Bool))).submatrix
              e.symm id).det) ^ 2 := by
      let N : Matrix s s ℝ :=
        (P.submatrix id (Subtype.val : s → (Fin d → Bool))).submatrix e.symm id
      have hleft : Matrix.diagonal w * P.transpose =
          fun i j => w i * P j i := by
        ext i j
        simp
      have hright : Matrix.diagonal (w ∘ (Subtype.val : s → (Fin d → Bool))) * N.transpose =
          fun (i j : s) => w (i : Fin d → Bool) * N j i := by
        ext i j
        simp
      have hmatrix :
          (((Matrix.diagonal w) * P.transpose) * P).submatrix
              (Subtype.val : s → (Fin d → Bool)) (Subtype.val : s → (Fin d → Bool)) =
            (Matrix.diagonal (w ∘ (Subtype.val : s → (Fin d → Bool))) * N.transpose) * N := by
        rw [hleft, hright]
        ext i j
        change (∑ z : (Fin d ⊕ Unit),
            (w (i : Fin d → Bool) * P z (i : Fin d → Bool)) * P z (j : Fin d → Bool)) =
          ∑ z : s, (w (i : Fin d → Bool) * P (e.symm z) (i : Fin d → Bool)) *
            P (e.symm z) (j : Fin d → Bool)
        rw [← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
      rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        Matrix.det_transpose]
      simp only [Function.comp_apply]
      ring
    let subsetEquiv (S : {s : Finset (Fin d → Bool) // s.card = d + 1}) :
        (Fin d ⊕ Unit) ≃ S.1 := Fintype.equivOfCardEq (by simpa using S.property.symm)
    calc
      (A * (Matrix.diagonal x * A.transpose)).det =
          ∑ s ∈ (Finset.univ : Finset (Fin d → Bool)).powersetCard (Fintype.card (Fin d ⊕ Unit)),
            (((Matrix.diagonal x * A.transpose) * A).submatrix
              (Subtype.val : s → (Fin d → Bool))
              (Subtype.val : s → (Fin d → Bool))).det :=
        rectangularExpansion A (Matrix.diagonal x * A.transpose)
      _ = ∑ S : {s : Finset (Fin d → Bool) // s.card = d + 1},
            (((Matrix.diagonal x * A.transpose) * A).submatrix
              (Subtype.val : S.1 → (Fin d → Bool))
              (Subtype.val : S.1 → (Fin d → Bool))).det := by
        rw [show Fintype.card (Fin d ⊕ Unit) = d + 1 by simp]
        exact Finset.sum_subtype _ (fun _ => Finset.mem_powersetCard_univ) _
      _ = ∑ S : {s : Finset (Fin d → Bool) // s.card = d + 1},
          (∏ v : S.1, x v) *
            (Int.natAbs
              (((augmentedCube d).submatrix id (Subtype.val : S.1 → (Fin d → Bool))).submatrix
                (Fintype.equivOfCardEq (by simpa using S.property.symm)).symm id).det : ℝ) ^ 2 := by
        apply Fintype.sum_congr
        intro S
        have hterm := weightedTerm A x S.1 (subsetEquiv S)
        rw [hterm]
        congr 1
        let Z : Matrix S.1 S.1 ℤ :=
          ((augmentedCube d).submatrix id
            (Subtype.val : S.1 → (Fin d → Bool))).submatrix
              (subsetEquiv S).symm id
        have hdet :
            (((A.submatrix id (Subtype.val : S.1 → (Fin d → Bool))).submatrix
              (subsetEquiv S).symm id).det) =
              (Z.det : ℤ) := by
          rw [show (A.submatrix id (Subtype.val : S.1 → (Fin d → Bool))).submatrix
              (subsetEquiv S).symm id =
              Z.map (Int.castRingHom ℝ) by
            ext i j
            rfl]
          simpa using (RingHom.map_det (Int.castRingHom ℝ) Z).symm
        rw [hdet]
        change (Z.det : ℝ) ^ 2 = (Int.natAbs Z.det : ℝ) ^ 2
        norm_num [← Int.cast_pow, Int.natAbs_sq]
  let A : Matrix (Fin d ⊕ Unit) (Fin d → Bool) ℝ
    | Sum.inl i, v => (v i).toNat
    | Sum.inr _, _ => 1
  have hAmap : A = (augmentedCube d).map (Int.castRingHom ℝ) := by
    ext i v
    rcases i with i | i
    · cases hvi : v i <;> simp [A, augmentedCube, hvi]
    · simp [A, augmentedCube]
  let s : ℝ := ∑ v, x v
  let a : Fin d → ℝ := fun i => ∑ v, x v * (v i).toNat
  let Q : Matrix (Fin d) (Fin d) ℝ := fun i j =>
    ∑ v, x v * (v i).toNat * (v j).toNat
  let b : Matrix (Fin d) Unit ℝ := fun i _ => a i
  let c : Matrix Unit (Fin d) ℝ := fun _ i => a i
  let D : Matrix Unit Unit ℝ := fun _ _ => s
  let M := (A * Matrix.diagonal x) * A.transpose
  have hExpansionM :
      M.det =
        ∑ S : {t : Finset (Fin d → Bool) // t.card = d + 1},
          (∏ v : S.1, x v) *
            (Int.natAbs
              (((augmentedCube d).submatrix id
                (Subtype.val : S.1 → (Fin d → Bool))).submatrix
                  (Fintype.equivOfCardEq (by simpa using S.property.symm)).symm
                    id).det : ℝ) ^ 2 := by
    rw [show M = (A * Matrix.diagonal x) * A.transpose by rfl, Matrix.mul_assoc, hAmap]
    exact hExpansion
  have hWle : hypercubeWeight d x ≤ M.det := by
    rw [hypercubeWeight, hExpansionM]
    apply Finset.sum_le_sum
    intro S _
    let z : ℤ :=
      (((augmentedCube d).submatrix id
        (Subtype.val : S.1 → (Fin d → Bool))).submatrix
          (Fintype.equivOfCardEq (by simpa using S.property.symm)).symm id).det
    have hcoefficient : (Int.natAbs z : ℝ) ≤ (Int.natAbs z : ℝ) ^ 2 := by
      exact_mod_cast (show Int.natAbs z ≤ Int.natAbs z ^ 2 by
        simpa [pow_two] using Nat.le_mul_self (Int.natAbs z))
    have hproduct : 0 ≤ ∏ v : S.1, x v :=
      Finset.prod_nonneg fun v _ => hx v
    change (Int.natAbs z : ℝ) * (∏ v : S.1, x v) ≤
      (∏ v : S.1, x v) * (Int.natAbs z : ℝ) ^ 2
    rw [mul_comm (Int.natAbs z : ℝ)]
    exact mul_le_mul_of_nonneg_left hcoefficient hproduct
  by_cases hs : s = 0
  · have hxzeroFun : x = 0 := (Fintype.sum_eq_zero_iff_of_nonneg hx).mp hs
    have hxzero : ∀ v, x v = 0 := fun v => congrFun hxzeroFun v
    have hcard (S : {t : Finset (Fin d → Bool) // t.card = d + 1}) : S.1.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hS
      have : d + 1 = 0 := by simpa [hS] using S.property
      omega
    have hWeight : hypercubeWeight d x = 0 := by
      rw [hypercubeWeight]
      apply Fintype.sum_eq_zero
      intro S
      rcases hcard S with ⟨v, hv⟩
      have hprod : (∏ w : S.1, x w) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ ⟨v, hv⟩)
        exact hxzero v
      rw [hprod, mul_zero]
    rw [hWeight]
    simp [hxzero, Nat.ne_of_gt hd]
  have hs_nonneg : 0 ≤ s := Finset.sum_nonneg fun v _ => hx v
  have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs)
  have hAD : A * Matrix.diagonal x = fun i v => A i v * x v := by
    ext i v
    simp
  have hAT : A.transpose = fun v i => A i v := rfl
  have hblock : M = Matrix.fromBlocks Q b c D := by
    apply Matrix.ext_iff_blocks.mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j
      simp only [Matrix.toBlocks_fromBlocks₁₁]
      dsimp [M, Q]
      rw [hAD, hAT]
      apply Finset.sum_congr rfl
      intro v _
      cases hvi : v i <;> cases hvj : v j <;> simp [A, hvi, hvj]
    · ext i j
      simp only [Matrix.toBlocks_fromBlocks₁₂]
      dsimp [M, b, a]
      rw [hAD, hAT]
      apply Finset.sum_congr rfl
      intro v _
      cases hvi : v i <;> simp [A, hvi]
    · ext i j
      simp only [Matrix.toBlocks_fromBlocks₂₁]
      dsimp [M, c, a]
      rw [hAD, hAT]
      apply Finset.sum_congr rfl
      intro v _
      cases hvj : v j <;> simp [A, hvj]
    · ext i j
      change M (Sum.inr i) (Sum.inr j) = D i j
      dsimp [M, D]
      simp_rw [Matrix.mul_apply]
      have hfirst : ∀ v, A (Sum.inr i) v = 1 := by
        intro v
        rfl
      simp [Matrix.diagonal, hfirst, s]
  have hM : M.PosSemidef := by
    have hdiag : (Matrix.diagonal x).PosSemidef :=
      Matrix.PosSemidef.diagonal hx
    simpa [M, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same A
  let E : Matrix Unit Unit ℝ := fun _ _ => s⁻¹
  have hED : E * D = 1 := by
    ext i j
    cases i
    cases j
    simp_rw [Matrix.mul_apply]
    simp [E, D, hs]
  let : Invertible D := invertibleOfLeftInverse D E hED
  have hDinv : ⅟D = E := invOf_eq_left_inv hED
  have hcb : c = bᴴ := by
    ext i j
    change a j = a j
    rfl
  have hDpos : D.PosDef := by
    have hDdiag : D = Matrix.diagonal (fun _ : Unit => s) := by
      ext i j
      cases i
      cases j
      simp [D]
    rw [hDdiag]
    exact Matrix.PosDef.diagonal fun _ => hs_pos
  have hfrom : (Matrix.fromBlocks Q b bᴴ D).PosSemidef := by
    rw [← hcb, ← hblock]
    exact hM
  have hSchur := (Matrix.PosDef.fromBlocks₂₂ Q b hDpos).mp hfrom
  let C : Matrix (Fin d) (Fin d) ℝ := s • (Q - b * D⁻¹ * bᴴ)
  have hCpsd : C.PosSemidef := hSchur.smul hs_nonneg
  have hDinvring : D⁻¹ = E := by
    rw [← Matrix.invOf_eq_nonsing_inv, hDinv]
  have hQdiag (i : Fin d) : Q i i = a i := by
    dsimp [Q, a]
    apply Finset.sum_congr rfl
    intro v _
    cases v i <;> simp
  have hCdiag (i : Fin d) : C i i = a i * (s - a i) := by
    rw [show C i i = s * (Q i i - (b * D⁻¹ * bᴴ) i i) by rfl]
    rw [hQdiag, hDinvring]
    have hbstar (u : Unit) (j : Fin d) : bᴴ u j = a j := by
      rfl
    have hmul : (b * E * bᴴ) i i = a i * s⁻¹ * a i := by
      simp_rw [Matrix.mul_apply]
      simp [b, E, hbstar]
    rw [hmul]
    field_simp
  have hdetle : C.det ≤ ∏ i, C i i := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hCpsd.nonneg
    rw [hB]
    let basis := EuclideanSpace.basisFun (Fin d) ℝ
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) := ⟨by simp⟩
    let orientation := basis.toBasis.orientation
    let vectors : Fin d → EuclideanSpace ℝ (Fin d) :=
      fun j => WithLp.toLp 2 (B.col j)
    have hvol := orientation.abs_volumeForm_apply_le vectors
    rw [orientation.volumeForm_robust' basis, Module.Basis.det_apply] at hvol
    have hmatrix : basis.toBasis.toMatrix vectors = B := by
      ext i j
      simp [basis, vectors, Module.Basis.toMatrix_apply]
    rw [hmatrix] at hvol
    have hsquare : |B.det| ^ 2 ≤ (∏ i, ‖vectors i‖) ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hvol 2
    have hdet : (star B * B).det = |B.det| ^ 2 := by
      simp [Matrix.det_mul, Matrix.star_eq_conjTranspose, pow_two]
    calc
      (star B * B).det ≤ (∏ i, ‖vectors i‖) ^ 2 := hdet ▸ hsquare
      _ = ∏ i, (star B * B) i i := by
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro i _
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [vectors, Matrix.mul_apply, pow_two]
  have hDdet : D.det = s := by
    simpa [D] using Matrix.det_unique D
  have hdetM : M.det = s * (Q - b * D⁻¹ * bᴴ).det := by
    rw [hblock, hcb, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, hDdet]
  have hdetC : C.det = s ^ d * (Q - b * D⁻¹ * bᴴ).det := by
    simp [C]
  have hpowered : s ^ (d - 1) * M.det = C.det := by
    rw [hdetM, hdetC]
    rw [← mul_assoc, pow_sub_one_mul (Nat.ne_of_gt hd)]
  let f0 : Fin d → ℝ := fun i => ∑ v, if v i = false then x v else 0
  let f1 : Fin d → ℝ := fun i => ∑ v, if v i = true then x v else 0
  have ha1 (i : Fin d) : a i = f1 i := by
    dsimp [a, f1]
    apply Finset.sum_congr rfl
    intro v _
    cases v i <;> simp
  have hsplit (i : Fin d) : s = f0 i + f1 i := by
    dsimp [s, f0, f1]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    cases v i <;> simp
  have hCfacet (i : Fin d) : C i i = f0 i * f1 i := by
    rw [hCdiag, ha1, hsplit]
    ring
  have hprod : (∏ i, C i i) = ∏ i, f0 i * f1 i := by
    apply Finset.prod_congr rfl
    intro i _
    exact hCfacet i
  calc
    hypercubeWeight d x * (∑ v, x v) ^ (d - 1) =
        hypercubeWeight d x * s ^ (d - 1) := by rfl
    _ ≤ M.det * s ^ (d - 1) :=
      mul_le_mul_of_nonneg_right hWle (pow_nonneg hs_nonneg _)
    _ = s ^ (d - 1) * M.det := mul_comm _ _
    _ = C.det := hpowered
    _ ≤ ∏ i, C i i := hdetle
    _ = ∏ i, (∑ v, if v i = false then x v else 0) *
        (∑ v, if v i = true then x v else 0) := by
      simpa [f0, f1] using hprod

end D5.S0.FiniteGeometry.HypercubeInequality
