/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedJacobi
   mirror-E: none(waiver:division-free-hankel-condensation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.SymplecticGroup]
   utility: none
   digest: Central-block perturbation proves Hankel condensation even at singular minors. -/

import Mathlib.LinearAlgebra.SymplecticGroup
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs

import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedJacobi

open MetallicHankelDefs Matrix

set_option backward.isDefEq.respectTransparency false in
/-- Division-free condensation for adjacent shifted Hankel determinants. -/
theorem hankel_jacobi (Φ : PowerSeries ℤ) (ℓ j : ℕ) :
    shiftedHankel Φ (ℓ + 1) (j + 1) ^ 2 =
      shiftedHankel Φ ℓ (j + 1) * shiftedHankel Φ (ℓ + 2) (j + 1) -
        shiftedHankel Φ ℓ (j + 2) * shiftedHankel Φ (ℓ + 2) j := by
  classical
  have regular (C : Matrix (Fin j) (Fin j) ℚ) (U : Matrix (Fin j) (Fin 2) ℚ)
      (V : Matrix (Fin 2) (Fin j) ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ)
      (hC : C.det ≠ 0) :
      C.det * (fromBlocks C U V D).det =
        (fromBlocks C (fun i (_ : Fin 1) => U i 0) (fun _ i => V 0 i)
          (fun _ _ : Fin 1 => D 0 0)).det *
        (fromBlocks C (fun i (_ : Fin 1) => U i 1) (fun _ i => V 1 i)
          (fun _ _ : Fin 1 => D 1 1)).det -
        (fromBlocks C (fun i (_ : Fin 1) => U i 1) (fun _ i => V 0 i)
          (fun _ _ : Fin 1 => D 0 1)).det *
        (fromBlocks C (fun i (_ : Fin 1) => U i 0) (fun _ i => V 1 i)
          (fun _ _ : Fin 1 => D 1 0)).det := by
    let := invertibleOfIsUnitDet C (isUnit_iff_ne_zero.mpr hC)
    have border (a b : Fin 2) :
        (fromBlocks C (fun i (_ : Fin 1) => U i b) (fun _ i => V a i)
          (fun _ _ : Fin 1 => D a b)).det = C.det * (D - V * ⅟C * U) a b := by
      rw [det_fromBlocks₁₁, det_eq_elem_of_subsingleton _ (0 : Fin 1)]
      simp only [Matrix.sub_apply, Matrix.mul_apply]
    rw [det_fromBlocks₁₁, det_fin_two, border, border, border, border]
    ring
  have blocks (C : Matrix (Fin j) (Fin j) ℚ) (U : Matrix (Fin j) (Fin 2) ℚ)
      (V : Matrix (Fin 2) (Fin j) ℚ) (D : Matrix (Fin 2) (Fin 2) ℚ) :
      C.det * (fromBlocks C U V D).det =
        (fromBlocks C (fun i (_ : Fin 1) => U i 0) (fun _ i => V 0 i)
          (fun _ _ : Fin 1 => D 0 0)).det *
        (fromBlocks C (fun i (_ : Fin 1) => U i 1) (fun _ i => V 1 i)
          (fun _ _ : Fin 1 => D 1 1)).det -
        (fromBlocks C (fun i (_ : Fin 1) => U i 1) (fun _ i => V 0 i)
          (fun _ _ : Fin 1 => D 0 1)).det *
        (fromBlocks C (fun i (_ : Fin 1) => U i 0) (fun _ i => V 1 i)
          (fun _ _ : Fin 1 => D 1 0)).det := by
    let CP : Matrix (Fin j) (Fin j) (Polynomial ℚ) :=
      (Polynomial.X : Polynomial ℚ) • 1 + C.map Polynomial.C
    let UP := U.map Polynomial.C
    let VP := V.map Polynomial.C
    let DP := D.map Polynomial.C
    let RP (b : Fin 2) : Matrix (Fin j) (Fin 1) (Polynomial ℚ) :=
      Matrix.map (fun (i : Fin j) (_ : Fin 1) => U i b) Polynomial.C
    let LP (a : Fin 2) : Matrix (Fin 1) (Fin j) (Polynomial ℚ) :=
      Matrix.map (fun (_ : Fin 1) (i : Fin j) => V a i) Polynomial.C
    let EP (a b : Fin 2) : Matrix (Fin 1) (Fin 1) (Polynomial ℚ) :=
      Matrix.map (fun (_ _ : Fin 1) => D a b) Polynomial.C
    let defect : (Polynomial ℚ) := CP.det * (fromBlocks CP UP VP DP).det -
      ((fromBlocks CP (RP 0) (LP 0) (EP 0 0)).det *
        (fromBlocks CP (RP 1) (LP 1) (EP 1 1)).det -
        (fromBlocks CP (RP 1) (LP 0) (EP 0 1)).det *
        (fromBlocks CP (RP 0) (LP 1) (EP 1 0)).det)
    have nonzero : CP.det ≠ 0 := by
      intro h
      have hl := Polynomial.leadingCoeff_det_X_one_add_C C
      change CP.det.leadingCoeff = 1 at hl
      rw [h, Polynomial.leadingCoeff_zero] at hl
      exact zero_ne_one hl
    have vanished : CP.det * defect = 0 := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_mul, Polynomial.eval_zero]
      by_cases hx : CP.det.eval x = 0
      · rw [hx, zero_mul]
      · have hreg := regular (CP.map (Polynomial.eval x)) U V D
          (by
            change ((Polynomial.evalRingHom x).mapMatrix CP).det ≠ 0
            rw [← RingHom.map_det]
            exact hx)
        have hev : defect.eval x = 0 := by
          dsimp [defect]
          simp only [← Polynomial.coe_evalRingHom, map_sub, map_mul, RingHom.map_det]
          simpa [UP, VP, DP, RP, LP, EP, Matrix.fromBlocks_map, Matrix.map_map,
            Function.comp_def] using sub_eq_zero.mpr hreg
        rw [hev, mul_zero]
    have identity : defect = 0 := (mul_eq_zero.mp vanished).resolve_left nonzero
    have he := congrArg (Polynomial.eval 0) identity
    dsimp [defect] at he
    simp only [← Polynomial.coe_evalRingHom, map_sub, map_mul, map_zero,
      RingHom.map_det] at he
    have zeroCP : CP.map (Polynomial.eval 0) = C := by
      ext a b
      simp [CP, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
    simpa [zeroCP, UP, VP, DP, RP, LP, EP, Matrix.fromBlocks_map, Matrix.map_map,
      Function.comp_def, sub_eq_zero] using he
  let f (k : ℕ) : ℚ := ((PowerSeries.coeff k Φ : ℤ) : ℚ)
  let H (s d : ℕ) : Matrix (Fin d) (Fin d) ℚ := fun a b => f (s + a + b)
  have castdet (s d : ℕ) : (shiftedHankel Φ s d : ℚ) = (H s d).det := by
    change (Int.castRingHom ℚ)
      (Matrix.of fun a b : Fin d => PowerSeries.coeff (s + a + b) Φ).det = _
    rw [RingHom.map_det]
    rfl
  let edge (a : Fin 2) : ℕ := if a = 0 then 0 else j + 1
  let C : Matrix (Fin j) (Fin j) ℚ := fun a b => f (ℓ + (a + 1) + (b + 1))
  let U : Matrix (Fin j) (Fin 2) ℚ := fun a b => f (ℓ + (a + 1) + edge b)
  let V : Matrix (Fin 2) (Fin j) ℚ := fun a b => f (ℓ + edge a + (b + 1))
  let D : Matrix (Fin 2) (Fin 2) ℚ := fun a b => f (ℓ + edge a + edge b)
  let B (a b : Fin 2) : Matrix (Fin j ⊕ Fin 1) (Fin j ⊕ Fin 1) ℚ :=
    fromBlocks C (fun i _ => U i b) (fun _ i => V a i) (fun _ _ => D a b)
  let e₀ : Fin j ⊕ Fin 1 ≃ Fin (j + 1) := finSumFinEquiv.trans (finRotate (j + 1))
  let e₁ : Fin j ⊕ Fin 1 ≃ Fin (j + 1) := finSumFinEquiv
  have e₀left (i : Fin j) : (e₀ (.inl i)).val = i.val + 1 := by
    change (finRotate (j + 1) (Fin.castSucc i)).val = i.val + 1
    exact congrArg Fin.val (finRotate_of_lt i.isLt)
  have e₀right (i : Fin 1) : (e₀ (.inr i)).val = 0 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (finRotate (j + 1) (Fin.last j)).val = 0
    rw [finRotate_last]
    rfl
  have e₁left (i : Fin j) : (e₁ (.inl i)).val = i.val := rfl
  have e₁right (i : Fin 1) : (e₁ (.inr i)).val = j := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have b₀₀ : B 0 0 = (H ℓ (j + 1)).submatrix e₀ e₀ := by
    ext a b
    cases a <;> cases b <;>
      simp [B, C, U, V, D, H, edge, e₀left, e₀right, Matrix.submatrix_apply]
  have b₁₁ : B 1 1 = (H (ℓ + 2) (j + 1)).submatrix e₁ e₁ := by
    ext a b
    cases a <;> cases b <;>
      simp [B, C, U, V, D, H, edge, e₁left, e₁right, Matrix.submatrix_apply]
    all_goals congr 1 <;> omega
  have b₀₁ : B 0 1 = (H (ℓ + 1) (j + 1)).submatrix e₀ e₁ := by
    ext a b
    cases a <;> cases b <;>
      simp [B, C, U, V, D, H, edge, e₀left, e₀right, e₁left, e₁right,
        Matrix.submatrix_apply]
    all_goals congr 1 <;> omega
  have b₁₀ : B 1 0 = (B 0 1)ᵀ := by
    ext a b
    cases a <;> cases b <;> simp [B, C, U, V, D, edge, Matrix.transpose_apply]
    all_goals congr 1 <;> omega
  have bsquare : (B 0 1).det * (B 1 0).det = (H (ℓ + 1) (j + 1)).det ^ 2 := by
    rw [b₁₀, det_transpose, ← pow_two, b₀₁, ← sq_abs, abs_det_submatrix_equiv_equiv,
      sq_abs]
  let toFin : Fin j ⊕ Fin 2 → Fin (j + 2) := fun a => match a with
    | .inl i => ⟨i + 1, by omega⟩
    | .inr i => ⟨edge i, by dsimp [edge]; split_ifs <;> omega⟩
  have bijective : Function.Bijective toFin := by
    constructor
    · intro a b hab
      have hv := congrArg Fin.val hab
      cases a with
      | inl a =>
          cases b with
          | inl b => congr 1; apply Fin.ext; simpa [toFin] using hv
          | inr b => dsimp [toFin, edge] at hv; split_ifs at hv <;> omega
      | inr a =>
          cases b with
          | inl b => dsimp [toFin, edge] at hv; split_ifs at hv <;> omega
          | inr b =>
              congr 1
              apply Fin.ext
              dsimp [toFin, edge] at hv
              split_ifs at hv <;> simp_all <;> omega
    · intro a
      by_cases ha : a.val = 0
      · refine ⟨.inr 0, ?_⟩; apply Fin.ext; simpa [toFin, edge] using ha.symm
      · by_cases hl : a.val = j + 1
        · refine ⟨.inr 1, ?_⟩; apply Fin.ext; simpa [toFin, edge] using hl.symm
        · refine ⟨.inl ⟨a.val - 1, by omega⟩, ?_⟩
          apply Fin.ext
          dsimp [toFin]
          omega
  let e := Equiv.ofBijective toFin bijective
  have total : fromBlocks C U V D = (H ℓ (j + 2)).submatrix e e := by
    ext a b
    cases a <;> cases b <;> rfl
  have center : C = H (ℓ + 2) j := by
    ext a b
    dsimp [C, H]
    congr 1
    omega
  have identity := blocks C U V D
  change C.det * (fromBlocks C U V D).det =
    (B 0 0).det * (B 1 1).det - (B 0 1).det * (B 1 0).det at identity
  rw [total, det_submatrix_equiv_self, b₀₀, b₁₁,
    det_submatrix_equiv_self, det_submatrix_equiv_self, bsquare, center] at identity
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_pow, Int.cast_sub, Int.cast_mul]
  rw [castdet, castdet, castdet, castdet, castdet]
  calc
    _ = (H ℓ (j + 1)).det * (H (ℓ + 2) (j + 1)).det -
        (H (ℓ + 2) j).det * (H ℓ (j + 2)).det := eq_sub_of_add_eq
      (by rw [add_comm]; exact eq_sub_iff_add_eq.mp identity)
    _ = _ := by ring

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedJacobi
