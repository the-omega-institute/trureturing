/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussElimination
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: Binary elimination transports the finite quadratic Gauss sum. -/

import D5.S3.VertexAlgebra.TwistedGround.BinarySchur
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients

/-! Finite coordinate transport for binary quadratic elimination. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.GaussElimination

open BinaryGauss BinarySchur Matrix
open LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign sum of a quadratic coefficient matrix reduced to the charge field. -/
def gauss (Q : Matrix ι ι (ZMod 8)) : ℂ :=
  ∑ x : ι → F₂, complexSign (Q.map residue |>.toBilin' x x)

private theorem map_self (Q : Matrix ι ι (ZMod 8)) (w : ι → ZMod 8) :
    residue (Q.toBilin' w w) =
      (Q.map residue).toBilin' (residue ∘ w) (residue ∘ w) := by
  simp [Matrix.toBilin'_apply, map_sum, map_mul, Matrix.map_apply, Function.comp_apply]

private def coordinateEquiv (P : Matrix ι ι F₂) (hu : IsUnit P.det) :
    (ι → F₂) ≃ (ι → F₂) where
  toFun := P.mulVec
  invFun := P⁻¹.mulVec
  left_inv x := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  right_inv x := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]

private theorem lift_residue (x : F₂) : residue (x.val : ZMod 8) = x := by
  have table : ∀ x : F₂, residue (x.val : ZMod 8) = x := by decide
  exact table x

private theorem reduced_split (a b c : ZMod 8) (hb : residue b = 1)
    (B : Matrix (Fin 2) ι (ZMod 8)) (L : Matrix ι ι (ZMod 8))
    (hu : IsUnit (fromBlocks (gram a b c) B Bᵀ (L + Lᵀ)).det)
    (x : Fin 2 ⊕ ι → F₂) :
    ((fromBlocks (halfGram a b c) B 0 L).map residue).toBilin'
        ((shear a b c B).map residue *ᵥ x) ((shear a b c B).map residue *ᵥ x) =
      ((halfGram a b c).map residue).toBilin' (x ∘ Sum.inl) (x ∘ Sum.inl) +
        ((residual a b c B L).map residue).toBilin' (x ∘ Sum.inr) (x ∘ Sum.inr) := by
  let w : Fin 2 ⊕ ι → ZMod 8 := fun i => (x i).val
  have lift : residue ∘ w = x := by funext i; exact lift_residue (x i)
  have h := congrArg residue ((even_binary_elimination a b c hb B L hu).2.2.2 w)
  simp only [map_add, map_self] at h
  have change : residue ∘ (shear a b c B *ᵥ w) = (shear a b c B).map residue *ᵥ x := by
    funext i
    simpa only [Function.comp_apply, lift] using (residue.map_mulVec (shear a b c B) w i)
  rw [change] at h
  simpa only [← Function.comp_assoc, lift] using h

private theorem binary_coordinates (a b c : ZMod 8) :
    (∑ x : Fin 2 → F₂,
      complexSign (((halfGram a b c).map residue).toBilin' x x)) =
      ∑ x : F₂ × F₂, complexSign (quadratic a b c x) := by
  let e : (Fin 2 → F₂) ≃ F₂ × F₂ :=
    { toFun := fun x => (x 0, x 1)
      invFun := fun x => ![x.1, x.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by intro x; rfl }
  apply Fintype.sum_equiv e
  intro x
  congr 1
  change ((halfGram a b c).map residue).toBilin' x x = quadratic a b c (x 0, x 1)
  simp [Matrix.toBilin'_apply, Fin.sum_univ_two, halfGram, quadratic, pow_two]
  ring

/-- The finite Gauss sum factors through an odd binary Schur elimination.
The residual complement may be empty. -/
private theorem binary_gauss_recurrence (a b c : ZMod 8) (hb : residue b = 1)
    (B : Matrix (Fin 2) ι (ZMod 8)) (L : Matrix ι ι (ZMod 8))
    (hu : IsUnit (fromBlocks (gram a b c) B Bᵀ (L + Lᵀ)).det) :
    gauss (fromBlocks (halfGram a b c) B 0 L) =
      2 * (ZMod.χ₈ (gram a b c).det : ℂ) * gauss (residual a b c B L) := by
  classical
  have detP : ((shear a b c B).map residue).det = 1 := by
    change (residue.mapMatrix (shear a b c B)).det = 1
    rw [← residue.map_det, (even_binary_elimination a b c hb B L hu).1, map_one]
  let e := coordinateEquiv ((shear a b c B).map residue) (detP ▸ isUnit_one)
  unfold gauss
  rw [← e.sum_comp (fun x => complexSign
    (((fromBlocks (halfGram a b c) B 0 L).map residue).toBilin' x x))]
  change (∑ x : Fin 2 ⊕ ι → F₂, complexSign
    (((fromBlocks (halfGram a b c) B 0 L).map residue).toBilin'
      ((shear a b c B).map residue *ᵥ x) ((shear a b c B).map residue *ᵥ x))) = _
  simp_rw [reduced_split a b c hb B L hu,
    complexSign_add]
  have split := (Equiv.sumArrowEquivProdArrow (Fin 2) ι F₂).sum_comp
    (fun x : (Fin 2 → F₂) × (ι → F₂) =>
      complexSign (((halfGram a b c).map residue).toBilin' x.1 x.1) *
      complexSign (((residual a b c B L).map residue).toBilin' x.2 x.2))
  change (∑ x : Fin 2 ⊕ ι → F₂,
    complexSign (((halfGram a b c).map residue).toBilin' (x ∘ Sum.inl) (x ∘ Sum.inl)) *
    complexSign (((residual a b c B L).map residue).toBilin'
      (x ∘ Sum.inr) (x ∘ Sum.inr))) = _ at split
  rw [split, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, binary_coordinates, block_sum a b c hb]

private theorem exists_odd_pivot (Q : Matrix ι ι (ZMod 8))
    (hu : IsUnit (Q + Qᵀ).det) (i : ι) :
    ∃ j : ι, j ≠ i ∧ residue ((Q + Qᵀ) i j) = 1 := by
  by_contra h
  push Not at h
  have row : ∀ j, ((Q + Qᵀ).map residue) i j = 0 := by
    intro j
    by_cases eq : j = i
    · subst j
      simp [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply,
        map_add, CharTwo.add_self_eq_zero]
    · have table : ∀ x : F₂, x ≠ 1 → x = 0 := by decide
      exact table _ (h j eq)
  have unit : IsUnit (((Q + Qᵀ).map residue).det) := by
    change IsUnit ((residue.mapMatrix (Q + Qᵀ)).det)
    rw [← residue.map_det]
    exact hu.map residue
  exact unit.ne_zero (det_eq_zero_of_row_eq_zero i row)

private def pivotEquiv (i j : ι) (hji : j ≠ i) :
    Fin 2 ⊕ {k : ι // k ≠ i ∧ k ≠ j} ≃ ι where
  toFun := Sum.elim (fun p => if p = 0 then i else j) Subtype.val
  invFun k := if hi : k = i then Sum.inl 0 else
    if hj : k = j then Sum.inl 1 else Sum.inr ⟨k, hi, hj⟩
  left_inv z := by
    cases z with
    | inl p => fin_cases p <;> simp [hji]
    | inr k => simp [k.property.1, k.property.2]
  right_inv k := by
    by_cases hi : k = i
    · simp [hi]
    · by_cases hj : k = j
      · simp [hj, hji]
      · simp [hi, hj]

private theorem gauss_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (Q : Matrix ι ι (ZMod 8)) :
    gauss (Q.submatrix e e) = gauss Q := by
  classical
  unfold gauss
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl F₂))
  intro x
  congr 1
  simp only [Matrix.toBilin'_apply, Matrix.map_apply, Matrix.submatrix_apply]
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp [Equiv.arrowCongr]

private theorem upper_binary_self {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    A.toBilin' x x =
      (!![A 0 0, A 0 1 + A 1 0; 0, A 1 1]).toBilin' x x := by
  simp [Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

private theorem normalize_self (A : Matrix (Fin 2) (Fin 2) (ZMod 8))
    (B : Matrix (Fin 2) ι (ZMod 8)) (C : Matrix ι (Fin 2) (ZMod 8))
    (L : Matrix ι ι (ZMod 8)) (w : Fin 2 ⊕ ι → ZMod 8) :
    (fromBlocks A B C L).toBilin' w w =
      (fromBlocks (halfGram (A 0 0) (A 0 1 + A 1 0) (A 1 1)) (B + Cᵀ) 0 L).toBilin' w w := by
  have binary : A.toBilin' (w ∘ Sum.inl) (w ∘ Sum.inl) =
      (halfGram (A 0 0) (A 0 1 + A 1 0) (A 1 1)).toBilin'
        (w ∘ Sum.inl) (w ∘ Sum.inl) := upper_binary_self A (w ∘ Sum.inl)
  have cross : (∑ i : ι, ∑ j : Fin 2, w (Sum.inr i) * C i j * w (Sum.inl j)) =
      ∑ j : Fin 2, ∑ i : ι, w (Sum.inl j) * C i j * w (Sum.inr i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [Matrix.toBilin'_apply, Function.comp_apply] at binary
  simp only [Matrix.toBilin'_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, mul_add, add_mul]
  rw [cross]
  rw [← binary]
  abel

private theorem gauss_congr (Q Q' : Matrix ι ι (ZMod 8))
    (h : ∀ w : ι → ZMod 8, Q.toBilin' w w = Q'.toBilin' w w) :
    gauss Q = gauss Q' := by
  unfold gauss
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  let w : ι → ZMod 8 := fun i => (x i).val
  have lift : residue ∘ w = x := by funext i; exact lift_residue (x i)
  have eq := congrArg residue (h w)
  simpa only [map_self, lift] using eq

universe u

private theorem global_induction (n : ℕ) :
    ∀ (κ : Type u) [Fintype κ] [DecidableEq κ], Fintype.card κ = n →
      ∀ Q : Matrix κ κ (ZMod 8), IsUnit (Q + Qᵀ).det →
        Even (Fintype.card κ) ∧
          gauss Q = (2 : ℂ) ^ (Fintype.card κ / 2) * (ZMod.χ₈ (Q + Qᵀ).det : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro κ finite decidable hc Q hu
    classical
    by_cases hn : n = 0
    · have empty : Fintype.card κ = 0 := hc.trans hn
      have : IsEmpty κ := Fintype.card_eq_zero_iff.mp empty
      constructor
      · exact ⟨0, by simp⟩
      · simp [gauss, Matrix.toBilin'_apply, complexSign]
    · have nonempty : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨i⟩ := nonempty
      obtain ⟨j, hji, odd⟩ := exists_odd_pivot Q hu i
      let K := {k : κ // k ≠ i ∧ k ≠ j}
      let e : Fin 2 ⊕ K ≃ κ := pivotEquiv i j hji
      let Q0 := Q.submatrix e e
      let A := Q0.submatrix Sum.inl Sum.inl
      let B := Q0.submatrix Sum.inl Sum.inr
      let C := Q0.submatrix Sum.inr Sum.inl
      let L := Q0.submatrix Sum.inr Sum.inr
      let a := A 0 0
      let b := A 0 1 + A 1 0
      let c := A 1 1
      let Bn := B + Cᵀ
      let R := residual a b c Bn L
      have blocks : Q0 = fromBlocks A B C L := by
        ext x y
        cases x <;> cases y <;> rfl
      have card : 2 + Fintype.card K = Fintype.card κ := by
        simpa using Fintype.card_congr e
      have oddb : residue b = 1 := by
        change residue (Q i j + Q j i) = 1
        exact odd
      have normalize : Q0 + Q0ᵀ = fromBlocks (gram a b c) Bn Bnᵀ (L + Lᵀ) := by
        rw [blocks, fromBlocks_transpose, fromBlocks_add]
        congr 1
        · ext x y
          fin_cases x <;> fin_cases y <;>
            simp [a, b, c, gram, Matrix.add_apply, Matrix.transpose_apply] <;> ring
        · simp [Bn, transpose_add, add_comm]
      have det0 : (Q0 + Q0ᵀ).det = (Q + Qᵀ).det := by
        change ((Q + Qᵀ).submatrix e e).det = _
        exact det_submatrix_equiv_self e _
      have unit : IsUnit (fromBlocks (gram a b c) Bn Bnᵀ (L + Lᵀ)).det := by
        rw [← normalize, det0]
        exact hu
      have elimination := even_binary_elimination a b c oddb Bn L unit
      have smaller := ih (Fintype.card K) (by omega) K rfl R
        elimination.2.2.1
      have determinant : (Q + Qᵀ).det = (gram a b c).det * (R + Rᵀ).det := by
        have eq := congrArg Matrix.det elimination.2.1
        simpa only [det_mul, det_transpose, elimination.1, one_mul, mul_one,
          det_fromBlocks_zero₁₂, ← normalize, det0] using eq
      have exponent : Fintype.card κ / 2 = Fintype.card K / 2 + 1 := by omega
      constructor
      · obtain ⟨k, hk⟩ := smaller.1
        exact ⟨k + 1, by omega⟩
      · calc
          gauss Q = gauss (fromBlocks (halfGram a b c) Bn 0 L) := by
            rw [← gauss_reindex e Q]
            change gauss Q0 = _
            rw [blocks]
            exact gauss_congr _ _ (normalize_self A B C L)
          _ = 2 * (ZMod.χ₈ (gram a b c).det : ℂ) * gauss R :=
            binary_gauss_recurrence a b c oddb Bn L unit
          _ = _ := by
            rw [smaller.2, determinant, map_mul, Int.cast_mul, exponent, pow_succ]
            ring

/-- The sign of an arbitrary nonsingular even quadratic matrix is determined by
its determinant modulo eight. Its coordinate cardinality is necessarily even. -/
theorem even_quadratic_gauss (Q : Matrix ι ι (ZMod 8))
    (hu : IsUnit (Q + Qᵀ).det) :
    Even (Fintype.card ι) ∧
      gauss Q = (2 : ℂ) ^ (Fintype.card ι / 2) * (ZMod.χ₈ (Q + Qᵀ).det : ℂ) :=
  global_induction (Fintype.card ι) ι rfl Q hu

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeHalfFockChargedTensorCoefficients

/-- The original charge-cocycle Gauss sum is positive for an integral unit determinant.
The rank is the one already selected by the actual ground representation theorem. -/
theorem actual_quadratic_gauss_sum (D : LatticeData) (hu : IsUnit D.G.det) :
    (∑ a : ModTwoCharge D, complexSign (modTwoCocycle D a a)) =
      (2 : ℂ) ^ groundRank D hu := by
  classical
  let Q : Matrix (Fin D.rank) (Fin D.rank) (ZMod 8) :=
    (lowerMatrix D).map (Int.castRingHom (ZMod 8))
  have symmetrization : Q + Qᵀ = D.G.map (Int.castRingHom (ZMod 8)) := by
    ext i j
    have eq := congrArg (Int.castRingHom (ZMod 8))
      (congrFun (congrFun (lower_matrix_symmetrization D) i) j)
    simpa only [Q, Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, map_add] using eq
  have unit : IsUnit (Q + Qᵀ).det := by
    rw [symmetrization]
    change IsUnit (((Int.castRingHom (ZMod 8)).mapMatrix D.G).det)
    rw [← (Int.castRingHom (ZMod 8)).map_det]
    exact hu.map (Int.castRingHom (ZMod 8))
  have character : ZMod.χ₈ (Q + Qᵀ).det = 1 := by
    rw [symmetrization]
    change ZMod.χ₈ (((Int.castRingHom (ZMod 8)).mapMatrix D.G).det) = 1
    rw [← (Int.castRingHom (ZMod 8)).map_det]
    rcases Int.isUnit_iff.mp hu with eq | eq
    · rw [eq]
      rfl
    · rw [eq]
      decide
  have coefficients : Q.map residue = (lowerMatrix D).map (Int.castRingHom F₂) := by
    ext i j
    simp [Q, Matrix.map_apply]
  have rank_eq : D.rank = groundRank D hu + groundRank D hu :=
    (Classical.choose_spec
      (Classical.choose_spec (actual_twisted_ground_representation D hu))).1
  have half : D.rank / 2 = groundRank D hu := by omega
  have result := (even_quadratic_gauss Q unit).2
  rw [character, Int.cast_one, mul_one, Fintype.card_fin, half] at result
  change (∑ a : Fin D.rank → F₂,
    complexSign (((lowerMatrix D).map (Int.castRingHom F₂)).toBilin' a a)) = _
  rw [← coefficients]
  exact result

#print axioms actual_quadratic_gauss_sum

#print axioms even_quadratic_gauss

#print axioms binary_gauss_recurrence

end
end D5.S3.VertexAlgebra.TwistedGround.GaussElimination
