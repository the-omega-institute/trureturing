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

end D5.S3.Quantum.Matrix.HsfBalancedCfcBridge
