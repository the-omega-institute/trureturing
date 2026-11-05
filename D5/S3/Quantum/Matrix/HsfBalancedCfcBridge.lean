/- GID: D5/S3/Quantum/Matrix/HsfBalancedCfcBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfBalancedCfcBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Actual two-thirds CFC derivatives consume the balanced two-level spectral certificate. -/

/-
The actual CFC root and its factorial-normalized derivatives are identified with
the ordered block recurrences and the finite weighted Gram inequality.
This combines classical spectral calculus with the balanced certificate;
no novelty or full HSF compatibility conclusion is asserted.
-/

module

public import D5.S3.Quantum.Matrix.HsfBalancedSpectralCertificate
public import D5.S3.Quantum.Matrix.RpowPencilTaylor

/-! Actual derivative supplier for a positive two-level center and a PSD balanced
direction, including singular directions and repeated levels. The source-binding
audit is unfinished under https://github.com/the-omega-institute/trureturing/issues/23103.
The full all-alpha, independent-X,Y HSF conjecture remains open. -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfBalancedCfcBridge

open HsfBalancedSpectralCertificate

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype n] in
private theorem baseRoot_diagonal (r : ℝ) :
    baseRoot (m := m) (n := n) r = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (r : ℂ))) := by
  ext i j
  cases i <;> cases j <;> simp [baseRoot, gramDiag, diagonal, Matrix.one_apply]

omit [Fintype m] [Fintype n] in
private theorem baseRoot_posDef (r : ℝ) (hr : 0 < r) :
    (baseRoot (m := m) (n := n) r).PosDef := by
  rw [baseRoot_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · exact zero_lt_one
  · exact_mod_cast hr

private theorem base_cube_posDef (r : ℝ) (hr : 0 < r) :
    ((baseRoot (m := m) (n := n) r)^3).PosDef := by
  have hP := baseRoot_posDef (m := m) (n := n) r hr
  rw [← CFC.rpow_natCast _ 3 hP.posSemidef.nonneg]
  exact (IsStrictlyPositive.rpow _ (3 : ℝ) hP.isStrictlyPositive).posDef

private theorem base_cube_root (r : ℝ) (hr : 0 < r) :
    CFC.rpow ((baseRoot (m := m) (n := n) r)^3) (1/3 : ℝ) = baseRoot r := by
  have hP := baseRoot_posDef (m := m) (n := n) r hr
  simp only [CFC.rpow_eq_pow]
  rw [← CFC.rpow_natCast _ 3 hP.posSemidef.nonneg,
    CFC.rpow_rpow _ _ _ (by norm_num) hP.isStrictlyPositive]
  norm_num [CFC.rpow_one _ hP.posSemidef.nonneg]

private theorem baseRoot_inverse (r : ℝ) (hr : 0 < r) :
    (baseRoot (m := m) (n := n) r)⁻¹ = inverseRoot r := by
  apply Matrix.inv_eq_right_inv
  simp [baseRoot, inverseRoot, gramDiag, fromBlocks_multiply,
    Matrix.mul_smul, smul_smul, hr.ne', ← fromBlocks_one]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
private theorem baseDirection_hermitian (r : ℝ)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hS : (direction A C H).PosSemidef) : (baseDirection r A C H).IsHermitian := by
  have hs := isHermitian_fromBlocks_iff.mp hS.isHermitian
  exact hs.1.fromBlocks (by simp) (hs.2.2.2.smul (IsSelfAdjoint.all _))

/-- The balanced two-level supplier for actual factorial-normalized CFC jets.
The off-diagonal block is arbitrary rectangular complex, S may be singular,
r=1 is included, and no derivative or desired inequality is assumed. -/
theorem actual_twoLevel_supplier (r : ℝ) (hr : 0 < r)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hS : (direction A C H).PosSemidef)
    (Z : Matrix (m ⊕ n) (m ⊕ n) ℂ) (hZ : Z.IsHermitian) :
    let Y := (baseRoot (m := m) (n := n) r)^3
    let K := baseDirection r A C H
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := RpowPencilTaylor.jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹)
    0 ≤ kappa r/6*pairEnergy A C H ∧
      kappa r/6*pairEnergy A C H ≤
        tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3) := by
  let Y := (baseRoot (m := m) (n := n) r)^3
  let K := baseDirection r A C H
  let P := baseRoot (m := m) (n := n) r
  let D := inverseRoot (m := m) (n := n) r
  let J := RpowPencilTaylor.jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
  have hY : Y.PosDef := base_cube_posDef r hr
  have hK : K.IsHermitian := baseDirection_hermitian r A C H hS
  have hp : CFC.rpow Y (1/3 : ℝ) = P := base_cube_root r hr
  have hd : P⁻¹ = D := baseRoot_inverse r hr
  have hc := RpowPencilTaylor.cubeRoot_jet_recurrences hY hK
  change J 0 = _ ∧ _ at hc
  rw [hp] at hc
  have h1 : cubeLinear r (J 1) = K := hc.2.1
  have h2 : cubeLinear r (J 2)+cubeQuadratic r (J 1) = 0 := by
    change RpowPencilTaylor.cubicLinear P (J 2) + _ = 0
    rw [hc.2.2.1]
    simp only [cubeQuadratic]
    change -(P*J 1*J 1+J 1*P*J 1+J 1*J 1*P) + _ = 0
    noncomm_ring
  have h3 : cubeLinear r (J 3)+cubeCubic r (J 1) (J 2) = 0 := by
    change RpowPencilTaylor.cubicLinear P (J 3) + _ = 0
    rw [hc.2.2.2]
    simp only [cubeCubic]
    change -(P*J 1*J 2+P*J 2*J 1+J 1*P*J 2+J 2*P*J 1+
      J 1*J 2*P+J 2*J 1*P+J 1*J 1*J 1) + _ = 0
    noncomm_ring
  have hj (j : ℕ) (hj : j ≤ 3) := RpowPencilTaylor.normalized_twoThirds_jet hY hK j hj
  have hj1 := hj 1 (by omega)
  have hj2 := hj 2 (by omega)
  have hj3 := hj 3 (by omega)
  change RpowPencilTaylor.jetCoeff _ 1 = _ at hj1
  change RpowPencilTaylor.jetCoeff _ 2 = _ at hj2
  change RpowPencilTaylor.jetCoeff _ 3 = _ at hj3
  simp only [hp, hd] at hj1 hj2 hj3
  change _ = D*(∑ a ∈ Finset.range (1+1), J a*J (1-a))*D at hj1
  change _ = D*(∑ a ∈ Finset.range (2+1), J a*J (2-a))*D at hj2
  change _ = D*(∑ a ∈ Finset.range (3+1), J a*J (3-a))*D at hj3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    Nat.reduceSub, hc.1, zero_add] at hj1 hj2 hj3
  rw [show P*J 2+J 1*J 1+J 2*P = P*J 2+J 2*P+J 1*J 1 by abel] at hj2
  rw [show P*J 3+J 1*J 2+J 2*J 1+J 3*P =
    P*J 3+J 3*P+J 1*J 2+J 2*J 1 by abel] at hj3
  dsimp only
  rw [hp, hd, hj1, hj2, hj3]
  exact supplier_of_cubic_recurrence r hr A C H hS (J 1) (J 2) (J 3) Z hZ h1 h2 h3

#print axioms actual_twoLevel_supplier

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem rpow_smul_pos (M : Matrix ι ι ℂ) (hM : 0 ≤ M)
    (c : ℝ) (hc : 0 < c) (p : ℝ) (hp : 0 ≤ p) :
    CFC.rpow (c • M) p = (c^p) • CFC.rpow M p := by
  have hcm : 0 ≤ c • M := by exact smul_nonneg hc.le hM
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hcm, CFC.rpow_eq_cfc_real hM]
  rw [← cfc_comp_smul (R := ℝ) c (fun x : ℝ => x^p) M
    (by exact (Real.continuous_rpow_const hp).continuousOn) hM.isSelfAdjoint,
    ← cfc_smul (c^p) (fun x : ℝ => x^p) M
      (Real.continuous_rpow_const hp).continuousOn]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow hc.le (spectrum_nonneg_of_nonneg hM hx)

private theorem equiv_rpow (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (M : Matrix ι ι ℂ) (hM : 0 ≤ M) (p : ℝ) (hp : 0 ≤ p) :
    e (CFC.rpow M p) = CFC.rpow (e M) p := by
  have hem : 0 ≤ e M := map_nonneg e hM
  let L := (e.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have he : Continuous e := L.continuous
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hM, CFC.rpow_eq_cfc_real hem]
  exact StarAlgHomClass.map_cfc e (fun x : ℝ => x^p) M
    (Real.continuous_rpow_const hp).continuousOn he hM.isSelfAdjoint hem.isSelfAdjoint

private theorem rpow_smul_any (M : Matrix ι ι ℂ)
    (c : ℝ) (hc : 0 < c) (p : ℝ) (hp : 0 ≤ p) :
    CFC.rpow (c • M) p = (c^p) • CFC.rpow M p := by
  by_cases hM : 0 ≤ M
  · exact rpow_smul_pos M hM c hc p hp
  · have hcm : ¬ 0 ≤ c • M := by
      intro h
      apply hM
      have h' := smul_nonneg (inv_pos.mpr hc).le h
      simpa [smul_smul, hc.ne'] using h'
    simp only [CFC.rpow_eq_pow, CFC.rpow_def,
      cfc_apply_of_not_predicate M hM, cfc_apply_of_not_predicate (c • M) hcm, smul_zero]

private theorem equiv_rpow_any (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (M : Matrix ι ι ℂ) (p : ℝ) (hp : 0 ≤ p) :
    e (CFC.rpow M p) = CFC.rpow (e M) p := by
  by_cases hM : 0 ≤ M
  · exact equiv_rpow e M hM p hp
  · have hem : ¬ 0 ≤ e M := by
      intro h
      apply hM
      simpa only [e.symm_apply_apply] using map_nonneg e.symm h
    simp only [CFC.rpow_eq_pow, CFC.rpow_def,
      cfc_apply_of_not_predicate M hM, cfc_apply_of_not_predicate (e M) hem, map_zero]

private theorem jetCoeff_equiv (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (f : ℝ → Matrix ι ι ℂ) (j : ℕ) :
    RpowPencilTaylor.jetCoeff (fun t => e (f t)) j = e (RpowPencilTaylor.jetCoeff f j) := by
  let L := (e.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hd : iteratedDeriv j (fun t => e (f t)) 0 = e (iteratedDeriv j f 0) := by
    simp only [iteratedDeriv]
    change (iteratedFDeriv ℝ j (L ∘ f) 0) (fun _ => 1) =
      L ((iteratedFDeriv ℝ j f 0) (fun _ => 1))
    rw [L.iteratedFDeriv_comp_left]
    rfl
  simp only [RpowPencilTaylor.jetCoeff, hd]
  exact (L.map_smul _ _).symm
private theorem normalized_transport
    (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (Y : Matrix ι ι ℂ) (hY : Y.PosDef) (M : Matrix ι ι ℂ) (c : ℝ) (hc : 0 < c) :
    let P := CFC.rpow Y (1/3 : ℝ)
    let P' := CFC.rpow (c • e Y) (1/3 : ℝ)
    P'⁻¹ * CFC.rpow (c • e M) (2/3 : ℝ) * P'⁻¹ =
      e (P⁻¹ * CFC.rpow M (2/3 : ℝ) * P⁻¹) := by
  let P := CFC.rpow Y (1/3 : ℝ)
  let a := c^(1/3 : ℝ)
  have ha : a ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have hP : P.PosDef := (IsStrictlyPositive.rpow _ _ hY.isStrictlyPositive).posDef
  have hp : CFC.rpow (c • e Y) (1/3 : ℝ) = a • e P := by
    rw [rpow_smul_any _ c hc _ (by norm_num), ← equiv_rpow_any e Y _ (by norm_num)]
  have hi : (a • e P)⁻¹ = a⁻¹ • e (P⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul,
      Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit), map_one]
    simp [ha]
  dsimp only
  rw [hp, hi, rpow_smul_any _ c hc _ (by norm_num),
    ← equiv_rpow_any e M _ (by norm_num)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul]
  have hs : a⁻¹ * c^(2/3 : ℝ) * a⁻¹ = 1 := by
    have hsquare : c^(2/3 : ℝ) = a*a := by
      dsimp [a]
      rw [← Real.rpow_add hc]
      congr 1
      ring
    rw [hsquare]
    field_simp
  rw [← mul_assoc, hs, one_smul]

private theorem conjugate_trace (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    HsfBalancedSpectralCertificate.tr (Unitary.conjStarAlgAut ℂ _ U M) =
      HsfBalancedSpectralCertificate.tr M := by
  unfold HsfBalancedSpectralCertificate.tr
  congr 1
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- A finite reindexing followed by unitary conjugation; it is a star-algebra equivalence. -/
def spectralFrame (q : ι ≃ κ) (U : unitary (Matrix κ κ ℂ)) :
    Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  (show Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ from
    { Matrix.reindexAlgEquiv ℂ ℂ q with
      map_smul' := (Matrix.reindexAlgEquiv ℂ ℂ q).toLinearEquiv.map_smul
      map_star' := fun _ => rfl }).trans
      (Unitary.conjStarAlgAut ℂ _ U)

private theorem frame_trace (q : ι ≃ κ) (U : unitary (Matrix κ κ ℂ))
    (M : Matrix ι ι ℂ) :
    HsfBalancedSpectralCertificate.tr (spectralFrame q U M) =
      HsfBalancedSpectralCertificate.tr M := by
  rw [spectralFrame, StarAlgEquiv.trans_apply, conjugate_trace]
  unfold HsfBalancedSpectralCertificate.tr Matrix.trace Matrix.diag
  congr 1
  exact q.symm.sum_comp (fun i => M i i)


/-- The actual two-level supplier after any finite reindexing, unitary conjugation
and common positive scaling of both the center and direction. -/
theorem transported_twoLevel_supplier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (hr : 0 < r) (c : ℝ) (hc : 0 < c)
    (A : Matrix m m ℂ) (C : Matrix m n ℂ) (H : Matrix n n ℂ)
    (hS : (direction A C H).PosSemidef)
    (q : (m ⊕ n) ≃ ι) (U : unitary (Matrix ι ι ℂ))
    (Z : Matrix ι ι ℂ) (hZ : Z.IsHermitian) :
    let e := spectralFrame q U
    let Y := c • e ((baseRoot (m := m) (n := n) r)^3)
    let K := c • e (baseDirection r A C H)
    let P := CFC.rpow Y (1/3 : ℝ)
    let B := RpowPencilTaylor.jetCoeff
      (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹)
    0 ≤ kappa r/6*pairEnergy A C H ∧
      kappa r/6*pairEnergy A C H ≤
        tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3) := by
  let e := spectralFrame q U
  let Y0 := (baseRoot (m := m) (n := n) r)^3
  let K0 := baseDirection r A C H
  let P0 := CFC.rpow Y0 (1/3 : ℝ)
  let Y := c • e Y0
  let K := c • e K0
  let P := CFC.rpow Y (1/3 : ℝ)
  let F0 := fun t : ℝ => P0⁻¹ * CFC.rpow (Y0+t • K0) (2/3 : ℝ) * P0⁻¹
  let F := fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹
  let B0 := RpowPencilTaylor.jetCoeff F0
  let B := RpowPencilTaylor.jetCoeff F
  let Z0 := e.symm Z
  have hY0 : Y0.PosDef := base_cube_posDef r hr
  have hZ0 : Z0.IsHermitian := by
    change star (e.symm Z) = e.symm Z
    rw [← map_star, show star Z = Z from hZ]
  have hz : e Z0 = Z := e.apply_symm_apply Z
  have hlin (t : ℝ) : c • e (Y0+t • K0) = Y+t • K := by
    have he := (e.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul t K0
    change e (t • K0) = t • e K0 at he
    simp only [map_add, he, smul_add, Y, K]
    rw [smul_comm c t]
  have hf : F = fun t => e (F0 t) := by
    funext t
    have h := normalized_transport e Y0 hY0 (Y0+t • K0) c hc
    change P⁻¹ * CFC.rpow (c • e (Y0+t • K0)) (2/3 : ℝ) * P⁻¹ = e (F0 t) at h
    simpa only [hlin] using h
  have hb (j : ℕ) : B j = e (B0 j) := by
    change RpowPencilTaylor.jetCoeff F j = _
    rw [hf]
    exact jetCoeff_equiv e F0 j
  have ht (M : Matrix (m ⊕ n) (m ⊕ n) ℂ) : tr (e M) = tr M := frame_trace q U M
  have hs := actual_twoLevel_supplier r hr A C H hS Z0 hZ0
  change 0 ≤ kappa r/6*pairEnergy A C H ∧
    kappa r/6*pairEnergy A C H ≤
      tr (B0 3)+2*tr (Z0*B0 2)+tr (B0 1*Z0*Z0)-(5/48 : ℝ)*tr ((B0 1)^3) at hs
  have he : tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3) =
      tr (B0 3)+2*tr (Z0*B0 2)+tr (B0 1*Z0*Z0)-(5/48 : ℝ)*tr ((B0 1)^3) := by
    calc
      _ = tr (e (B0 3))+2*tr (e Z0*e (B0 2))+
          tr (e (B0 1)*e Z0*e Z0)-(5/48 : ℝ)*tr ((e (B0 1))^3) := by
        rw [hb 1, hb 2, hb 3, hz]
      _ = _ := by simp only [← map_mul, ← map_pow, ht]
  change 0 ≤ kappa r/6*pairEnergy A C H ∧
    kappa r/6*pairEnergy A C H ≤
      tr (B 3)+2*tr (Z*B 2)+tr (B 1*Z*Z)-(5/48 : ℝ)*tr ((B 1)^3)
  rw [he]
  exact hs

#print axioms transported_twoLevel_supplier

end D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
