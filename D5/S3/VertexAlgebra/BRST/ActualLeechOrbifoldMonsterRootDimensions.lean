/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldMonsterRealPresentation
import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldTraceSeries
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The coefficient real form has the same root multiplicities as the complex
BRST cohomology. Paper weight `(m,n)` has native momentum `(m,-n)`. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldAllWeightDimension (OrbifoldWeight)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldTraceSeries (dimension)
open LatticeGeneratingFieldLocality (Charge)
open MonsterPositiveCocycle (Weight realRoot)
open RelativeCohomology (GradedCohomology GradedCycles ghostOneCohomologyEquivNonzero)
open RealRootBracket (positiveRoot monsterSimpleMomentum)

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => GradedCohomology planeFrame planeBasis
local notation "incl" => DirectSum.lof ℂ Momentum (fun p => H p 1)
local notation "proj" => DirectSum.component ℂ Momentum (fun p => H p 1)
local notation "W" => realMomentumGrade

attribute [local instance] realCartanStateAddCommGroup realCartanShellAddCommGroup
  realCartanCyclesAddCommGroup

private def sumRealParts (p : Momentum) : W p × W p →ₗ[ℝ] MomentumH1 where
  toFun x := momentumRealValue x.1.val + Complex.I • momentumRealValue x.2.val
  map_add' x y := by
    change (momentumRealValue x.1.val + momentumRealValue y.1.val) +
      Complex.I • (momentumRealValue x.2.val + momentumRealValue y.2.val) =
        (momentumRealValue x.1.val + Complex.I • momentumRealValue x.2.val) +
        (momentumRealValue y.1.val + Complex.I • momentumRealValue y.2.val)
    rw [smul_add]
    abel
  map_smul' r x := by
    change (r : ℂ) • momentumRealValue x.1.val +
      Complex.I • ((r : ℂ) • momentumRealValue x.2.val) =
      (r : ℂ) • (momentumRealValue x.1.val + Complex.I • momentumRealValue x.2.val)
    rw [smul_add, smul_comm Complex.I (r : ℂ)]

private theorem sumRealParts_mem (p : Momentum) (x : W p × W p) :
    sumRealParts p x ∈ LinearMap.range (incl p) :=
  Submodule.add_mem _ ((mem_realMomentumWeightSpace p _).mp x.1.property)
    (Submodule.smul_mem _ _ ((mem_realMomentumWeightSpace p _).mp x.2.property))

private theorem incl_proj_sumRealParts (p : Momentum) (x : W p × W p) :
    incl p (proj p (sumRealParts p x)) = sumRealParts p x := by
  obtain ⟨a, ha⟩ := sumRealParts_mem p x
  rw [← ha, DirectSum.component.lof_self]

/-- The actual real Cartan eigenspace has the complex BRST multiplicity. -/
theorem realMomentumGrade_finrank (p : Momentum) :
    Module.finrank ℝ (W p) = Module.finrank ℂ (H p 1) := by
  let : FiniteDimensional ℝ (W p) := realMomentumWeightSpace_finiteDimensional p
  let f : W p × W p →ₗ[ℝ] H p 1 :=
    (proj p).restrictScalars ℝ ∘ₗ sumRealParts p
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      have hsum : sumRealParts p x = sumRealParts p y := by
        rw [← incl_proj_sumRealParts p x, ← incl_proj_sumRealParts p y]
        exact congrArg (incl p) h
      have hp := momentumH1_real_decomposition_unique x.1.val x.2.val y.1.val y.2.val hsum
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
    · intro a
      let z := incl p a
      have hconj : coefficientConjugationMomentum z ∈ LinearMap.range (incl p) := by
        change coefficientConjugationMomentum (incl p a) ∈ _
        rw [coefficientConjugationMomentum_incl]
        exact ⟨_, rfl⟩
      have hre : momentumRealPart z ∈ W p := by
        apply (mem_realMomentumWeightSpace p _).mpr
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ ⟨a, rfl⟩ hconj)
      have him : momentumImaginaryPart z ∈ W p := by
        apply (mem_realMomentumWeightSpace p _).mpr
        exact Submodule.smul_mem _ _ (Submodule.sub_mem _ ⟨a, rfl⟩ hconj)
      refine ⟨(⟨_, hre⟩, ⟨_, him⟩), ?_⟩
      change proj p (momentumRealValue (momentumRealPart z) +
        Complex.I • momentumRealValue (momentumImaginaryPart z)) = a
      rw [← momentumH1_real_decomposition, DirectSum.component.lof_self]

  have h := (LinearEquiv.ofBijective f hbij).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex] at h
  omega

/-- At nonzero momentum the real root multiplicity is the literal assembled VOA dimension. -/
theorem realMomentumGrade_finrank_of_ne_zero (p : Momentum) (hp : p ≠ 0) :
    Module.finrank ℝ (W p) = dimension (1 - p (0 : Fin 2) * p (1 : Fin 2)) := by
  rw [realMomentumGrade_finrank, (ghostOneCohomologyEquivNonzero p hp).finrank_eq]
  rfl

/-- In positive imaginary paper weight the multiplicity is `c(mn)`. -/
theorem monsterImaginaryGrade_finrank (m n : ℕ) (hm : 0 < m) :
    Module.finrank ℝ (W (monsterNativeMomentum (m, n))) = dimension ((↑(m * n) : ℤ) + 1) := by
  have hne : monsterNativeMomentum (m, n) ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    change (m : ℤ) = 0 at h0
    omega
  rw [realMomentumGrade_finrank_of_ne_zero _ hne]
  change dimension (1 - (m : ℤ) * -(n : ℤ)) = _
  push_cast
  congr 1
  ring

/-- The positive native real support consists of the real simple root and the
strictly positive paper quadrant. -/
theorem monsterNativeGrade_eq_bot_of_outside (p : Weight) (hp : 0 < p.1)
    (hreal : p ≠ realRoot) (himag : ¬ 0 < p.2) :
    W (monsterNativeMomentum p) = ⊥ := by
  let q := monsterNativeMomentum p
  have hq : q ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    change p.1 = 0 at h0
    omega
  by_cases hn : p.2 = 0
  · have h := realMomentumWeightSpace_eq_bot_of_null q hq (by
      rw [momentumRealBPZ_momentum_norm]
      change (2 : ℝ) * ((p.1 : ℝ) * ((-p.2 : ℤ) : ℝ)) = 0
      simp [hn])
    exact congrArg LieSubmodule.toSubmodule h
  · apply le_antisymm _ bot_le
    intro x hx
    by_contra hx0
    have h := realMomentumWeight_norm_le_two q x hx (by simpa using hx0)
    rw [momentumRealBPZ_momentum_norm] at h
    change (2 : ℝ) * ((p.1 : ℝ) * ((-p.2 : ℤ) : ℝ)) ≤ 2 at h
    have hle : p.1 * -p.2 ≤ 1 := by
      have h' : ((p.1 : ℝ) * ((-p.2 : ℤ) : ℝ)) ≤ 1 := by linarith
      exact_mod_cast h'
    have hmin : 1 ≤ -p.2 := by omega
    have h1 := mul_le_mul_of_nonneg_left hmin (show 0 ≤ p.1 by omega)
    have h2 := mul_le_mul_of_nonneg_right (show 1 ≤ p.1 by omega) (show 0 ≤ -p.2 by omega)
    apply hreal
    apply Prod.ext
    · change p.1 = 1
      omega
    · change p.2 = -1
      omega

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
