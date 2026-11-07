/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelCoincident
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelCoincident
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Actual CFC supplier for coincident positive labels and arbitrary multiplicities. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfBalancedCfcBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfThreeLevelSupplier

universe u


/-- O4. Faithful coincident-label reduction. Use the existing actual two-level
supplier via the fiber equivalence and common scale; do not evaluate dualG at
a singular Gram or assume that a level fiber is inhabited. -/
private def CoincidentLevelObligation : Prop :=
  ∀ (n : Type u) [Fintype n] [DecidableEq n]
    (level : n → Fin 3) (p : Fin 3 → ℝ), (∀ i, 0 < p i) →
    ¬ Function.Injective p →
    ∀ (S : Matrix n n ℂ), S.PosSemidef →
    ∀ (Z : Matrix n n ℂ), Z.IsHermitian →
    let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
    let F := fun t : ℝ => P⁻¹*CFC.rpow (P^3+t •
      (CFC.rpow P (3/2 : ℝ)*S*CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ)*P⁻¹
    let B := fun j : ℕ => (j.factorial : ℝ)⁻¹ • iteratedDeriv j F 0
    0 ≤ (B 3+(2 : ℝ) • (Z*B 2)+B 1*Z^2-(5/48 : ℝ) • (B 1)^3).trace.re



/-- Elementary diagonal CFC calculation, including the empty matrix algebra. -/
private theorem coincident_diagonal_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (s : ℝ) (hs : 0 ≤ s) :
    CFC.rpow (diagonal (fun i => (d i : ℂ))) s =
      diagonal (fun i => ((d i ^ s : ℝ) : ℂ)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI : IsEmpty ι := hι
    exact Subsingleton.elim _ _
  · letI : Nonempty ι := hι
    letI : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℂ (ι → ℂ) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    let φ : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
      { toAlgHom := diagonalAlgHom (n := ι) (α := ℂ) ℂ
        map_star' := by
          intro x
          ext i j
          simp [diagonal] <;> split_ifs <;> simp_all }
    have hself : IsSelfAdjoint (fun i => (d i : ℂ)) := by
      change star (fun i => (d i : ℂ)) = _
      ext i
      simp
    have hD : 0 ≤ diagonal (fun i => (d i : ℂ)) := by
      apply Matrix.PosSemidef.nonneg
      apply Matrix.PosSemidef.diagonal
      intro i
      change (0 : ℂ) ≤ (d i : ℂ)
      exact_mod_cast hd i
    have hmap := φ.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint)
      (fun x : ℝ => x ^ s) (fun i => (d i : ℂ))
      (Real.continuous_rpow_const hs).continuousOn
      (show Continuous φ from continuous_id.matrix_diagonal) hself hD.isSelfAdjoint
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hD]
    change cfc (fun x : ℝ => x ^ s) (φ (fun i => (d i : ℂ))) = _
    rw [← hmap, cfc_map_pi (S := ℂ) (p := IsSelfAdjoint)
      (q := fun _ => IsSelfAdjoint) (fun x : ℝ => x ^ s)
      (fun i => (d i : ℂ)) (Real.continuous_rpow_const hs).continuousOn
      hself (by intro i; change star (d i : ℂ) = _; simp)]
    change diagonal (fun i => cfc (fun x : ℝ => x ^ s) (d i : ℂ)) = _
    congr 1
    funext i
    simpa using (cfc_algebraMap (A := ℂ) (d i) (fun x : ℝ => x ^ s))

/-- The two retained values are actual positive labels; they may coincide. -/
private theorem coincident_two_values (p : Fin 3 → ℝ) (hp : ∀ i, 0 < p i)
    (hn : ¬ Function.Injective p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p i = a ∨ p i = b := by
  classical
  by_cases h01 : p 0 = p 1
  · refine ⟨p 0, p 2, hp 0, hp 2, ?_⟩
    intro i
    fin_cases i <;> simp_all
  · by_cases h02 : p 0 = p 2
    · refine ⟨p 0, p 1, hp 0, hp 1, ?_⟩
      intro i
      fin_cases i <;> simp_all
    · have h12 : p 1 = p 2 := by
        by_contra h12
        apply hn
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      refine ⟨p 0, p 1, hp 0, hp 1, ?_⟩
      intro i
      fin_cases i <;> simp_all

/-- Coincident labels in the unchanged actual factorial CFC supplier. -/
private theorem coincidentLevel_proof : CoincidentLevelObligation := by
  classical
  intro n _ _ level p hp hn S hS Z hZ
  obtain ⟨a, b, ha, hb, hab⟩ := coincident_two_values p hp hn
  let L := {i : n // p (level i) = a}
  let R := {i : n // ¬ p (level i) = a}
  -- sumCompl has forward map Sum.elim Subtype.val Subtype.val and inverse
  -- i ↦ if h : p (level i) = a then inl ⟨i,h⟩ else inr ⟨i,h⟩.
  -- Thus neither fiber nor the original carrier needs an inhabitant.
  let q : (L ⊕ R) ≃ n := Equiv.sumCompl (fun i : n => p (level i) = a)
  have hleft (i : L) : p (level (q (Sum.inl i))) = a := i.property
  have hright (i : R) : p (level (q (Sum.inr i))) = b :=
    (hab (level i.val)).resolve_left i.property
  let r : ℝ := b / a
  have hr : 0 < r := div_pos hb ha
  have har : a * r = b := by
    dsimp [r]
    field_simp [ha.ne'] <;> ring
  let e := HsfBalancedCfcBridge.spectralFrame q (1 : unitary (Matrix n n ℂ))
  have he_apply (M : Matrix (L ⊕ R) (L ⊕ R) ℂ) (i j : L ⊕ R) :
      e M (q i) (q j) = M i j := by
    change ((1 : Matrix n n ℂ) * Matrix.reindex q q M *
      star (1 : Matrix n n ℂ)) (q i) (q j) = M i j
    simp [Matrix.reindex_apply]
  have he_back (M : Matrix n n ℂ) : e (M.submatrix q q) = M := by
    ext i j
    obtain ⟨i, rfl⟩ := q.surjective i
    obtain ⟨j, rfl⟩ := q.surjective j
    exact he_apply (M.submatrix q q) i j
  have he_smul (x : ℝ) (M : Matrix (L ⊕ R) (L ⊕ R) ℂ) :
      e (x • M) = x • e M :=
    (e.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul x M
  let S0 : Matrix (L ⊕ R) (L ⊕ R) ℂ := S.submatrix q q
  let Z0 : Matrix (L ⊕ R) (L ⊕ R) ℂ := Z.submatrix q q
  have hS0 : S0.PosSemidef := hS.submatrix q
  have hZ0 : Z0.IsHermitian := hZ.submatrix q
  have hZ_back : (e Z0).IsHermitian := by
    change star (e Z0) = e Z0
    rw [← map_star, show star Z0 = Z0 from hZ0]
  have hZ_actual : Z.IsHermitian := by
    rw [← he_back Z]
    exact hZ_back
  let A : Matrix L L ℂ := S0.toBlocks₁₁
  let C : Matrix L R ℂ := S0.toBlocks₁₂
  let H : Matrix R R ℂ := S0.toBlocks₂₂
  have hdir : HsfBalancedSpectralCertificate.direction A C H = S0 := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact hS0.isHermitian.apply (Sum.inr i) (Sum.inl j)
      | inr j => rfl
  have hdirPSD : (HsfBalancedSpectralCertificate.direction A C H).PosSemidef := by
    rw [hdir]
    exact hS0
  let P : Matrix n n ℂ := diagonal (fun i => (p (level i) : ℂ))
  let Q : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
    HsfBalancedSpectralCertificate.baseRoot r
  have hP_pull : P.submatrix q q = a • Q := by
    change (diagonal (fun i => (p (level i) : ℂ))).submatrix q q = a • Q
    rw [Matrix.submatrix_diagonal_equiv]
    ext i j
    cases i <;> cases j <;>
      simp [Q, Function.comp_def, hleft, hright,
        HsfBalancedSpectralCertificate.baseRoot, HsfBalancedSpectralCertificate.gramDiag,
        diagonal, Matrix.one_apply, RCLike.real_smul_eq_coe_mul, mul_ite,
        ← Complex.ofReal_mul, har]
  have hP_scale : P = a • e Q := by
    calc
      P = e (P.submatrix q q) := (he_back P).symm
      _ = e (a • Q) := congrArg e hP_pull
      _ = a • e Q := he_smul a Q
  let Y : Matrix n n ℂ := (a ^ 3) • e (Q ^ 3)
  have hY_actual : Y = P ^ 3 := by
    dsimp only [Y]
    rw [hP_scale, smul_pow, map_pow]
  have hP_nonneg : 0 ≤ P := by
    apply Matrix.PosSemidef.nonneg
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (p (level i) : ℂ)
    exact_mod_cast (hp (level i)).le
  have hroot_actual : CFC.rpow Y (1/3 : ℝ) = P := by
    rw [hY_actual, ← CFC.rpow_natCast P 3 hP_nonneg]
    change CFC.rpow (CFC.rpow P (3 : ℝ)) (1/3 : ℝ) = P
    calc
      CFC.rpow (CFC.rpow P (3 : ℝ)) (1/3 : ℝ) =
          CFC.rpow P ((3 : ℝ)*(1/3 : ℝ)) :=
        CFC.rpow_rpow_of_exponent_nonneg P (3 : ℝ) (1/3 : ℝ)
          (by norm_num) (by norm_num) hP_nonneg
      _ = P := by norm_num [CFC.rpow_one P hP_nonneg]
  have hr_half : r ^ (3/2 : ℝ) = r * Real.sqrt r := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num,
      Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hb_half : b ^ (3/2 : ℝ) = a ^ (3/2 : ℝ) * (r * Real.sqrt r) := by
    calc
      b ^ (3/2 : ℝ) = (a * r) ^ (3/2 : ℝ) :=
        congrArg (fun x : ℝ => x ^ (3/2 : ℝ)) har.symm
      _ = a ^ (3/2 : ℝ) * (r * Real.sqrt r) := by
        rw [Real.mul_rpow ha.le hr.le, hr_half]
  let D : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
    HsfBalancedSpectralCertificate.gramDiag 1 (r * Real.sqrt r)
  have hD_pull : (CFC.rpow P (3/2 : ℝ)).submatrix q q =
      a ^ (3/2 : ℝ) • D := by
    change (CFC.rpow (diagonal (fun i => (p (level i) : ℂ))) (3/2 : ℝ)).submatrix q q = _
    rw [coincident_diagonal_rpow (fun i => p (level i))
      (fun i => (hp (level i)).le) (3/2 : ℝ) (by norm_num),
      Matrix.submatrix_diagonal_equiv]
    ext i j
    cases i <;> cases j <;>
      simp [D, Function.comp_def, hleft, hright,
        HsfBalancedSpectralCertificate.gramDiag, diagonal, Matrix.one_apply,
        RCLike.real_smul_eq_coe_mul, mul_ite, ← Complex.ofReal_mul, hb_half]
  have hD_scale : CFC.rpow P (3/2 : ℝ) = a ^ (3/2 : ℝ) • e D := by
    calc
      CFC.rpow P (3/2 : ℝ) =
          e ((CFC.rpow P (3/2 : ℝ)).submatrix q q) := (he_back _).symm
      _ = e (a ^ (3/2 : ℝ) • D) := congrArg e hD_pull
      _ = a ^ (3/2 : ℝ) • e D := he_smul _ D
  have hr_square : (r * Real.sqrt r) * (r * Real.sqrt r) = r ^ 3 := by
    calc
      _ = r ^ 2 * (Real.sqrt r) ^ 2 := by ring
      _ = r ^ 3 := by rw [Real.sq_sqrt hr.le]; ring
  have hK_blocks : HsfBalancedSpectralCertificate.baseDirection r A C H = D * S0 * D := by
    rw [← hdir]
    simp only [D, HsfBalancedSpectralCertificate.baseDirection,
      HsfBalancedSpectralCertificate.gramDiag, HsfBalancedSpectralCertificate.direction,
      fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      smul_zero, one_smul, zero_add, add_zero, hr_square]
  have ha_half_square : a ^ (3/2 : ℝ) * a ^ (3/2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_add ha]
    norm_num
  let K : Matrix n n ℂ :=
    (a ^ 3) • e (HsfBalancedSpectralCertificate.baseDirection r A C H)
  have hK_actual : K = CFC.rpow P (3/2 : ℝ) * S * CFC.rpow P (3/2 : ℝ) := by
    dsimp only [K]
    rw [hK_blocks, map_mul, map_mul, he_back S, hD_scale]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha_half_square]
  let F : ℝ → Matrix n n ℂ := fun t => P⁻¹ *
    CFC.rpow (P ^ 3 + t • (CFC.rpow P (3/2 : ℝ) * S *
      CFC.rpow P (3/2 : ℝ))) (2/3 : ℝ) * P⁻¹
  let Ft : ℝ → Matrix n n ℂ := fun t => (CFC.rpow Y (1/3 : ℝ))⁻¹ *
    CFC.rpow (Y + t • K) (2/3 : ℝ) * (CFC.rpow Y (1/3 : ℝ))⁻¹
  -- Global equality, including negative t; no differentiability premise.
  have hcurve_actual : Ft = F := by
    funext t
    dsimp only [Ft, F]
    rw [hroot_actual, hY_actual, hK_actual]
  let B := RpowPencilTaylor.jetCoeff F
  have hjet_actual (j : ℕ) : RpowPencilTaylor.jetCoeff Ft j = B j := by
    rw [hcurve_actual]
  have htransport := HsfBalancedCfcBridge.transported_twoLevel_supplier
    r hr (a ^ 3) (pow_pos ha 3) A C H hdirPSD q
    (1 : unitary (Matrix n n ℂ)) Z hZ_actual
  have hsupplier := le_trans htransport.1 htransport.2
  change 0 ≤ HsfBalancedSpectralCertificate.tr (RpowPencilTaylor.jetCoeff Ft 3) +
    2 * HsfBalancedSpectralCertificate.tr (Z * RpowPencilTaylor.jetCoeff Ft 2) +
    HsfBalancedSpectralCertificate.tr (RpowPencilTaylor.jetCoeff Ft 1 * Z * Z) -
    (5/48 : ℝ) * HsfBalancedSpectralCertificate.tr
      ((RpowPencilTaylor.jetCoeff Ft 1) ^ 3) at hsupplier
  rw [hjet_actual 1, hjet_actual 2, hjet_actual 3] at hsupplier
  have htrace_actual :
      (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
        (5/48 : ℝ) • (B 1) ^ 3).trace.re =
      HsfBalancedSpectralCertificate.tr (B 3) +
        2 * HsfBalancedSpectralCertificate.tr (Z * B 2) +
        HsfBalancedSpectralCertificate.tr (B 1 * Z * Z) -
        (5/48 : ℝ) * HsfBalancedSpectralCertificate.tr ((B 1) ^ 3) := by
    simp [HsfBalancedSpectralCertificate.tr, pow_two, Matrix.mul_assoc]
  change 0 ≤ (B 3 + (2 : ℝ) • (Z * B 2) + B 1 * Z ^ 2 -
    (5/48 : ℝ) • (B 1) ^ 3).trace.re
  rw [htrace_actual]
  exact hsupplier

end D5.S3.Quantum.Matrix.HsfThreeLevelSupplier
