/-
Copyright (c) 2026 trureturing contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldFiniteOppositeTensor
import D5.S3.VertexAlgebra.BRST.GradedLieSplitBracketIdentity
import Mathlib.Algebra.Lie.TransferInstance
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# The native positive BRST tensor bracket identity

This formalizes equation (10) in §3 of the 2026-11-24 direct Monster presentation
oracle derivation. The finite opposite-dual reconstruction supplies the split map,
and the split-bracket coefficient calculation supplies the Cartan defect. The
coordinates are the native `(m, -n)`, with positivity defined by `0 < m`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Classical DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

local notation "Momentum" => (Fin 2 → ℤ)
local notation "L" => momentumRealLie
local notation "W" => realMomentumGrade
local notation "B" => momentumRealBPZ

open D5.S3.VertexAlgebra.GradedLieSplitBracketIdentity (paired_split_bracket)

section RealCoefficient

local notation "sum" => DirectSum.coeLinearMap W

/-- The inverse of the internal direct sum of the native real momentum spaces. -/
def realMomentumDecompose : L ≃ₗ[ℝ] ⨁ p : Momentum, W p :=
  (LinearEquiv.ofBijective sum realMomentumWeightSpace_isInternal).symm

theorem realMomentumDecompose_coe (p : Momentum) (x : W p) :
    realMomentumDecompose (x : L) = DirectSum.lof ℝ Momentum (fun q => ↥(W q)) p x := by
  apply realMomentumDecompose.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (DirectSum.coeLinearMap_lof W p x).symm

/-- Keep the real momentum components satisfying the given predicate. -/
def projectMomentumReal (keep : Momentum → Prop) : L →ₗ[ℝ] L :=
  (DirectSum.toModule ℝ Momentum L fun p => if keep p then (W p).subtype else 0).comp
    realMomentumDecompose.toLinearMap

private theorem realMomentumSum_surjective : Function.Surjective sum :=
  realMomentumWeightSpace_isInternal.surjective

theorem projectMomentumReal_weight (keep : Momentum → Prop) (p : Momentum) (x : W p) :
    projectMomentumReal keep (x : L) = if keep p then (x : L) else 0 := by
  simp only [projectMomentumReal, LinearMap.comp_apply, LinearEquiv.coe_coe,
    realMomentumDecompose_coe, DirectSum.toModule_lof]
  split_ifs <;> rfl

/-- The first-coordinate negative projection on the native real Lie algebra. -/
def projectNegativeMomentumRealByGrade : L →ₗ[ℝ] L :=
  projectMomentumReal fun p => p 0 < 0

local notation "negPart" => projectNegativeMomentumRealByGrade
local notation "zeroPart" => projectMomentumReal (fun p => p = 0)
local notation "posPart" => projectMomentumReal (fun p => 0 < p 0)

private theorem projectMomentumReal_triangular (x : L) :
    negPart x + zeroPart x + posPart x = x := by
  obtain ⟨d, rfl⟩ := realMomentumSum_surjective x
  change (negPart + zeroPart + posPart) (sum d) = sum d
  induction d using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p x =>
    change negPart (sum (DirectSum.lof ℝ Momentum (fun q => ↥(W q)) p x)) +
      zeroPart (sum (DirectSum.lof ℝ Momentum (fun q => ↥(W q)) p x)) +
      posPart (sum (DirectSum.lof ℝ Momentum (fun q => ↥(W q)) p x)) =
      sum (DirectSum.lof ℝ Momentum (fun q => ↥(W q)) p x)
    simp only [DirectSum.coeLinearMap_lof, projectNegativeMomentumRealByGrade, projectMomentumReal_weight]
    by_cases hz : p = 0
    · subst p
      simp
    · rcases lt_trichotomy (p 0) 0 with hp | hp | hp
      · simp [hp, hz, hp.asymm]
      · have hbot := realMomentumWeightSpace_eq_bot_of_null p hz
          (by simp [momentumRealBPZ_momentum_norm, hp])
        have hx := x.property
        change (x : L) ∈ realMomentumWeightSpace p at hx
        rw [hbot, LieSubmodule.mem_bot] at hx
        simp [hp, hx]
      · simp [hp, hz, hp.asymm]
  | add d e hd he => simp only [map_add, hd, he]

private theorem momentumRealBPZ_project_eq_zero (P Q : Momentum → Prop)
    (hOpp : ∀ p q, P p → Q q → q ≠ -p) (a b : L) :
    B (projectMomentumReal P a) (projectMomentumReal Q b) = 0 := by
  obtain ⟨d, rfl⟩ := realMomentumSum_surjective a
  induction d using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [DirectSum.coeLinearMap_of, projectMomentumReal_weight]
    by_cases hp : P p
    · rw [ite_eq_left hp]
      obtain ⟨e, rfl⟩ := realMomentumSum_surjective b
      induction e using DirectSum.induction_on with
      | zero => simp
      | of q y =>
        rw [DirectSum.coeLinearMap_of, projectMomentumReal_weight]
        by_cases hq : Q q
        · rw [ite_eq_left hq]
          exact momentumRealBPZ_momentum_selection x.property y.property (hOpp p q hp hq)
        · rw [ite_eq_right hq, map_zero]
      | add e f he hf => simp only [map_add, he, hf, add_zero]
    · rw [ite_eq_right hp, map_zero, LinearMap.zero_apply]
  | add d e hd he => simp only [map_add, LinearMap.add_apply, hd, he, add_zero]

private theorem projectMomentumReal_zero_lie (p q : Momentum) (x : W p) (y : W q) :
    zeroPart ⁅(x : L), (y : L)⁆ = B x y • (realCartanClass (fun i => (p i : ℝ)) : L) := by
  let z : W (p + q) := ⟨⁅(x : L), (y : L)⁆, realWeight_lie_mem_add p q x y⟩
  change zeroPart (z : L) = _
  rw [projectMomentumReal_weight]
  by_cases h : p + q = 0
  · rw [ite_eq_left h]
    have hq : q = -p := eq_neg_of_add_eq_zero_right h
    exact lie_realMomentumWeightSpace_neg p x y x.property (hq ▸ y.property)
  · have hq : q ≠ -p := fun he => h (he ▸ add_neg_cancel p)
    rw [ite_eq_right h, momentumRealBPZ_momentum_selection x.property y.property hq, zero_smul]

/-- The exact real BPZ split bracket coefficient for native homogeneous inputs. -/
theorem momentumRealBPZ_split_bracket_of_weights (p q r s : Momentum)
    (x : W p) (y : W q) (u : W r) (v : W s) :
    B ⁅(x : L), (y : L)⁆ ⁅(u : L), (v : L)⁆ =
      (B (negPart ⁅(x : L), (u : L)⁆) ⁅(y : L), (v : L)⁆ +
        B ⁅(x : L), (u : L)⁆ (negPart ⁅(y : L), (v : L)⁆)) -
      (B ⁅(y : L), (u : L)⁆ (negPart ⁅(x : L), (v : L)⁆) +
        B (negPart ⁅(y : L), (u : L)⁆) ⁅(x : L), (v : L)⁆) +
      ((p 0 : ℝ) * (q 1 : ℝ) + (p 1 : ℝ) * (q 0 : ℝ)) *
        (B x u * B y v - B x v * B y u) := by
  have hNeg : ∀ a b, B (negPart a) (negPart b) = 0 := by
    apply momentumRealBPZ_project_eq_zero (fun p => p 0 < 0) (fun p => p 0 < 0)
    intro i j hi hj h
    have h0 : j 0 = -(i 0) := congrFun h 0
    omega
  have hPos : ∀ a b, B (posPart a) (posPart b) = 0 := by
    apply momentumRealBPZ_project_eq_zero (fun p => 0 < p 0) (fun p => 0 < p 0)
    intro i j hi hj h
    have h0 : j 0 = -(i 0) := congrFun h 0
    omega
  have hZero (P : Momentum → Prop) (hP : ¬ P 0) :
      ∀ a b, B (zeroPart a) (projectMomentumReal P b) = 0 := by
    apply momentumRealBPZ_project_eq_zero
    rintro i j rfl hj rfl
    exact hP (by simpa only [neg_zero] using hj)
  exact paired_split_bracket B momentumRealBPZ_symmetric momentumRealBPZ_invariant
    negPart zeroPart posPart projectMomentumReal_triangular hNeg hPos
    (hZero (fun p => p 0 < 0) (lt_irrefl (0 : ℤ)))
    (hZero (fun p => 0 < p 0) (lt_irrefl (0 : ℤ)))
    x y u v
    (realCartanClass (fun i => (p i : ℝ))) (realCartanClass (fun i => (q i : ℝ))) _
    (momentumRealBPZ_cartan _ _)
    (projectMomentumReal_zero_lie p r x u) (projectMomentumReal_zero_lie q s y v)
    (projectMomentumReal_zero_lie q r y u) (projectMomentumReal_zero_lie p s x v)

end RealCoefficient

local notation "P" => RealPositiveMomentumSum
local notation "T" => (P ⊗[ℝ] P)
local notation "lof" => realPositiveMomentumLof
local notation "ι₊" => realPositiveMomentumIncl
local notation "Δ" => realPositiveSplitTensor
local notation "eval" => realPositiveTensorEval

local instance (p : Momentum) : FiniteDimensional ℝ (W p) :=
  realMomentumWeightSpace_finiteDimensional p

@[simp]
theorem realPositiveMomentumIncl_lof (p : RealPositiveMomentum) (x : W p.1) :
    ι₊ (lof p x) = (x : L) :=
  DirectSum.toModule_lof _ _ _

private def realPositiveMomentumProject : L →ₗ[ℝ] P :=
  (DirectSum.toModule ℝ Momentum P fun p =>
    if h : 0 < p 0 then lof ⟨p, h⟩ else 0).comp realMomentumDecompose.toLinearMap

theorem realPositiveMomentumIncl_injective : Function.Injective ι₊ := by
  have h : realPositiveMomentumProject.comp ι₊ = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    change realPositiveMomentumProject (ι₊ (lof p x)) = lof p x
    rw [realPositiveMomentumIncl_lof]
    simp only [realPositiveMomentumProject, LinearMap.comp_apply, LinearEquiv.coe_coe,
      realMomentumDecompose_coe, DirectSum.toModule_lof, dite_eq_left p.property]
  exact Function.LeftInverse.injective (g := realPositiveMomentumProject)
    (fun x => LinearMap.congr_fun h x)

/-- Addition preserves positivity of the first native coordinate. -/
def realPositiveMomentumAdd (p q : RealPositiveMomentum) : RealPositiveMomentum :=
  ⟨p.1 + q.1, add_pos p.property q.property⟩

/-- The homogeneous native bracket with its graded codomain. -/
def realMomentumWeightBracket (p q : Momentum) (x : W p) (y : W q) : W (p + q) :=
  ⟨⁅(x : L), (y : L)⁆, realWeight_lie_mem_add p q x y⟩

/-- The positive Lie subalgebra of the native real momentum algebra. -/
def realPositiveMomentumLie : LieSubalgebra ℝ L where
  toSubmodule := ι₊.range
  lie_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    change ⁅ι₊ x, ι₊ y⁆ ∈ ι₊.range
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, zero_lie, Submodule.zero_mem]
    | of p x =>
      change ⁅ι₊ (lof p x), ι₊ y⁆ ∈ ι₊.range
      induction y using DirectSum.induction_on with
      | zero => simp only [map_zero, lie_zero, Submodule.zero_mem]
      | of q y =>
        refine ⟨lof (realPositiveMomentumAdd p q) (realMomentumWeightBracket p.1 q.1 x y), ?_⟩
        simp only [← DirectSum.lof_eq_of ℝ, realPositiveMomentumIncl_lof]
        rfl
      | add y z hy hz =>
        rw [map_add, lie_add]
        exact Submodule.add_mem _ hy hz
    | add x z hx hz =>
      rw [map_add, add_lie]
      exact Submodule.add_mem _ hx hz

/-- The positive direct sum identified with its image in the native algebra. -/
def realPositiveMomentumEquiv : P ≃ₗ[ℝ] realPositiveMomentumLie :=
  LinearEquiv.ofInjective ι₊ realPositiveMomentumIncl_injective

instance realPositiveMomentumLieRing : LieRing P :=
  realPositiveMomentumEquiv.toAddEquiv.lieRing

instance realPositiveMomentumLieAlgebra : LieAlgebra ℝ P :=
  realPositiveMomentumEquiv.lieAlgebra

@[simp]
theorem realPositiveMomentumIncl_lie (x y : P) :
    ι₊ ⁅x, y⁆ = ⁅ι₊ x, ι₊ y⁆ := by
  change (realPositiveMomentumEquiv (realPositiveMomentumEquiv.symm
    ⁅realPositiveMomentumEquiv x, realPositiveMomentumEquiv y⁆) : L) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The inclusion of the positive Lie algebra for use in Lie homomorphism compositions. -/
def realPositiveMomentumLieIncl : P →ₗ⁅ℝ⁆ L :=
  { ι₊ with map_lie' := fun {x y} => realPositiveMomentumIncl_lie x y }

@[simp]
theorem realPositiveMomentum_lie_lof (p q : RealPositiveMomentum) (x : W p.1) (y : W q.1) :
    ⁅lof p x, lof q y⁆ =
      lof (realPositiveMomentumAdd p q) (realMomentumWeightBracket p.1 q.1 x y) := by
  apply realPositiveMomentumIncl_injective
  simp only [realPositiveMomentumIncl_lie, realPositiveMomentumIncl_lof]
  rfl

/-- The diagonal positive adjoint action on the two tensor factors. -/
def realPositiveTensorAd (x : P) : T →ₗ[ℝ] T :=
  TensorProduct.map (LieAlgebra.ad ℝ P x) LinearMap.id +
    TensorProduct.map LinearMap.id (LieAlgebra.ad ℝ P x)

@[simp]
theorem realPositiveTensorAd_tmul (x a b : P) :
    realPositiveTensorAd x (a ⊗ₜ[ℝ] b) = ⁅x, a⁆ ⊗ₜ[ℝ] b + a ⊗ₜ[ℝ] ⁅x, b⁆ := by
  simp [realPositiveTensorAd]

private theorem projectNegativeMomentumRealByGrade_weight (p : Momentum) (x : W p) :
    projectNegativeMomentumRealByGrade (x : L) = if p 0 < 0 then (x : L) else 0 := by
  rw [projectNegativeMomentumRealByGrade, projectMomentumReal_weight]
  split_ifs <;> rfl

private theorem realPositiveBPZ_projectNegative (a : P) (u : L) :
    B (ι₊ a) (projectNegativeMomentumRealByGrade u) = B (ι₊ a) u := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of p a =>
    change B (ι₊ (lof p a)) (projectNegativeMomentumRealByGrade u) = B (ι₊ (lof p a)) u
    rw [realPositiveMomentumIncl_lof]
    have surj : Function.Surjective (DirectSum.coeLinearMap W) :=
      realMomentumWeightSpace_isInternal.surjective
    obtain ⟨d, rfl⟩ := surj u
    induction d using DirectSum.induction_on with
    | zero => simp
    | of q u =>
      rw [DirectSum.coeLinearMap_of, projectNegativeMomentumRealByGrade_weight]
      split_ifs with h
      · rfl
      · rw [map_zero, momentumRealBPZ_momentum_selection a.property u.property]
        intro hq
        apply h
        rw [hq]
        exact neg_neg_of_pos p.property
    | add d e hd he => simp only [map_add, hd, he]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

private theorem realPositiveAd_BPZ (x a : P) (u : L) :
    B (ι₊ ⁅x, a⁆) u = -B (ι₊ a) (projectNegativeMomentumRealByGrade ⁅ι₊ x, u⁆) := by
  rw [realPositiveMomentumIncl_lie, realPositiveBPZ_projectNegative,
    ← lie_skew (ι₊ x) (ι₊ a), momentumRealBPZ.neg_left, momentumRealBPZ_invariant]

private theorem realPositiveTensorEval_tmul (u v : L) (a b : P) :
    eval u v (a ⊗ₜ[ℝ] b) = B (ι₊ a) u * B (ι₊ b) v := by
  simp [realPositiveTensorEval]

/-- BPZ transfers the diagonal adjoint to the two projected negative adjoints with a minus sign.
Both the positive adjoint and the tested tensor may have several momentum components. -/
theorem realPositiveTensorEval_ad (x : P) (z : T) (u v : L) :
    eval u v (realPositiveTensorAd x z) =
      -(eval (projectNegativeMomentumRealByGrade ⁅ι₊ x, u⁆) v z +
        eval u (projectNegativeMomentumRealByGrade ⁅ι₊ x, v⁆) z) := by
  suffices h : (eval u v).comp (realPositiveTensorAd x) =
      -(eval (projectNegativeMomentumRealByGrade ⁅ι₊ x, u⁆) v +
        eval u (projectNegativeMomentumRealByGrade ⁅ι₊ x, v⁆)) from LinearMap.congr_fun h z
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, realPositiveTensorAd_tmul, map_add, LinearMap.neg_apply,
    LinearMap.add_apply, realPositiveTensorEval_tmul, realPositiveAd_BPZ, neg_mul, mul_neg]
  ring

private theorem realSplitTensor_pair_projectNegative_left (p q : Momentum) (x : W p)
    (u : L) (hu : u ∈ realMomentumWeightSpace q) (s : RealPositiveMomentum) (v : W (-s.1)) :
    eval (projectNegativeMomentumRealByGrade u) v (realSplitTensor p x) =
      B x ⁅projectNegativeMomentumRealByGrade u, (v : L)⁆ := by
  rw [show projectNegativeMomentumRealByGrade u = if q 0 < 0 then u else 0 from
    projectNegativeMomentumRealByGrade_weight q ⟨u, hu⟩]
  split_ifs with h
  · let r : RealPositiveMomentum := ⟨-q, neg_pos.mpr h⟩
    have hr : -r.1 = q := neg_neg q
    exact realSplitTensor_pair p x r s ⟨u, hr.symm ▸ hu⟩ v
  · simp [realPositiveTensorEval]

private theorem realSplitTensor_pair_projectNegative_right (p q : Momentum) (x : W p)
    (r : RealPositiveMomentum) (u : W (-r.1)) (v : L) (hv : v ∈ realMomentumWeightSpace q) :
    eval u (projectNegativeMomentumRealByGrade v) (realSplitTensor p x) =
      B x ⁅(u : L), projectNegativeMomentumRealByGrade v⁆ := by
  rw [show projectNegativeMomentumRealByGrade v = if q 0 < 0 then v else 0 from
    projectNegativeMomentumRealByGrade_weight q ⟨v, hv⟩]
  split_ifs with h
  · let s : RealPositiveMomentum := ⟨-q, neg_pos.mpr h⟩
    have hs : -s.1 = q := neg_neg q
    exact realSplitTensor_pair p x r s u ⟨v, hs.symm ▸ hv⟩
  · simp [realPositiveTensorEval]

/-- The native Cartan coefficient of the defect, in the ordered null coordinates. -/
def realPositiveTensorCartanCoefficient (p q : Momentum) : ℝ :=
  (p 0 : ℝ) * (q 1 : ℝ) + (p 1 : ℝ) * (q 0 : ℝ)

private theorem realPositiveTensorEval_ad_split (p q r s : RealPositiveMomentum)
    (x : W p.1) (y : W q.1) (u : W (-r.1)) (v : W (-s.1)) :
    eval u v (realPositiveTensorAd (lof p x) (Δ (lof q y))) =
      B (projectNegativeMomentumRealByGrade ⁅(x : L), (u : L)⁆) ⁅(y : L), (v : L)⁆ -
        B ⁅(y : L), (u : L)⁆ (projectNegativeMomentumRealByGrade ⁅(x : L), (v : L)⁆) := by
  let a := projectNegativeMomentumRealByGrade ⁅(x : L), (u : L)⁆
  let b := projectNegativeMomentumRealByGrade ⁅(x : L), (v : L)⁆
  calc
    _ = -(eval a v (realSplitTensor q.1 y) + eval u b (realSplitTensor q.1 y)) := by
      simpa only [realPositiveMomentumIncl_lof, realPositiveSplitTensor_lof, a, b] using
        (realPositiveTensorEval_ad (lof p x) (Δ (lof q y)) u v)
    _ = -(B (y : L) ⁅a, (v : L)⁆ + B (y : L) ⁅(u : L), b⁆) :=
      congrArg Neg.neg (congrArg₂ (· + ·)
        (realSplitTensor_pair_projectNegative_left q.1 (p.1 + -r.1) y
          ⁅(x : L), (u : L)⁆ (realWeight_lie_mem_add p.1 (-r.1) x u) s v)
        (realSplitTensor_pair_projectNegative_right q.1 (p.1 + -s.1) y r u
          ⁅(x : L), (v : L)⁆ (realWeight_lie_mem_add p.1 (-s.1) x v)))
    _ = B a ⁅(y : L), (v : L)⁆ - B ⁅(y : L), (u : L)⁆ b := by
      have ha : B (y : L) ⁅a, (v : L)⁆ = -B a ⁅(y : L), (v : L)⁆ := by
        calc
          _ = B ⁅(y : L), a⁆ v := (momentumRealBPZ_invariant (y : L) a v).symm
          _ = B (-⁅a, (y : L)⁆) v := congrArg (fun w : L => B w v) (lie_skew (y : L) a).symm
          _ = _ := (momentumRealBPZ.neg_left _ _).trans
            (congrArg Neg.neg (momentumRealBPZ_invariant a (y : L) v))
      have hb := momentumRealBPZ_invariant (y : L) u b
      simp only [ha, ← hb, neg_add_rev, neg_neg, sub_eq_add_neg, add_comm]

/-- Equation (10) after evaluation on any two negative homogeneous tests. -/
theorem realPositiveSplitTensor_lie_pair (p q r s : RealPositiveMomentum)
    (x : W p.1) (y : W q.1) (u : W (-r.1)) (v : W (-s.1)) :
    eval u v (Δ ⁅lof p x, lof q y⁆) =
      eval u v (realPositiveTensorAd (lof p x) (Δ (lof q y)) -
        realPositiveTensorAd (lof q y) (Δ (lof p x)) +
        realPositiveTensorCartanCoefficient p.1 q.1 •
          (lof p x ⊗ₜ[ℝ] lof q y - lof q y ⊗ₜ[ℝ] lof p x)) := by
  calc
    _ = B ⁅(x : L), (y : L)⁆ ⁅(u : L), (v : L)⁆ := by
      rw [realPositiveMomentum_lie_lof, realPositiveSplitTensor_lof,
        realSplitTensor_pair _ _ r s u v]
      rfl
    _ = _ := by
      simp only [map_add, map_sub, map_smul, smul_eq_mul, realPositiveTensorEval_ad_split,
        realPositiveTensorEval_tmul, realPositiveMomentumIncl_lof, realPositiveTensorCartanCoefficient]
      exact (momentumRealBPZ_split_bracket_of_weights p.1 q.1 (-r.1) (-s.1) x y u v).trans
        (by ring)

private abbrev positiveTensorBlock (i : RealPositiveMomentum × RealPositiveMomentum) :=
  W i.1.1 ⊗[ℝ] W i.2.1

private def realPositiveTensorDecompose :
    T ≃ₗ[ℝ] ⨁ i : RealPositiveMomentum × RealPositiveMomentum, positiveTensorBlock i :=
  TensorProduct.directSum ℝ ℝ (fun r : RealPositiveMomentum => ↥(W r.1))
    (fun s : RealPositiveMomentum => ↥(W s.1))

private theorem realPositiveTensorEval_decompose (r s : RealPositiveMomentum)
    (u : W (-r.1)) (v : W (-s.1))
    (d : ⨁ i : RealPositiveMomentum × RealPositiveMomentum, positiveTensorBlock i) :
    eval u v (realPositiveTensorDecompose.symm d) =
      oppositeTensorDual (realOppositeBPZ r.1) (realOppositeBPZ s.1) (d (r, s)) (u ⊗ₜ[ℝ] v) := by
  let ev : Module.Dual ℝ (W (-r.1) ⊗[ℝ] W (-s.1)) →ₗ[ℝ] ℝ :=
    LinearMap.applyₗ (R := ℝ) (u ⊗ₜ[ℝ] v)
  suffices h : (eval u v).comp realPositiveTensorDecompose.symm.toLinearMap =
      ev.comp ((oppositeTensorDual (realOppositeBPZ r.1) (realOppositeBPZ s.1)).toLinearMap.comp
        (DirectSum.component ℝ _ positiveTensorBlock (r, s))) from LinearMap.congr_fun h d
  apply DirectSum.linearMap_ext
  intro i
  by_cases hi : i = (r, s)
  · subst i
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, realPositiveTensorDecompose,
      TensorProduct.directSum_symm_lof_tmul, realPositiveTensorEval_tmul, realPositiveMomentumIncl_lof,
      DirectSum.component.lof_self]
    exact (oppositeTensorDual_tmul (realOppositeBPZ r.1) (realOppositeBPZ s.1) x y u v).symm
  · rcases i with ⟨a, b⟩
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, realPositiveTensorDecompose,
      TensorProduct.directSum_symm_lof_tmul, realPositiveTensorEval_tmul, realPositiveMomentumIncl_lof,
      DirectSum.component.of, dite_eq_right hi, map_zero]
    change B (x : L) u * B (y : L) v = 0
    by_cases ha : a = r
    · have hb : b ≠ s := fun h => hi (Prod.ext ha h)
      have hweight : -s.1 ≠ -b.1 := fun h => hb (Subtype.ext (neg_injective h.symm))
      exact mul_eq_zero.mpr (Or.inr (momentumRealBPZ_momentum_selection y.property v.property hweight))
    · have hweight : -r.1 ≠ -a.1 := fun h => ha (Subtype.ext (neg_injective h.symm))
      exact mul_eq_zero.mpr (Or.inl (momentumRealBPZ_momentum_selection x.property u.property hweight))

/-- All negative homogeneous pure tests jointly detect a positive tensor. -/
theorem realPositiveTensor_ext {z z' : T}
    (h : ∀ (r s : RealPositiveMomentum) (u : W (-r.1)) (v : W (-s.1)),
      eval u v z = eval u v z') : z = z' := by
  apply realPositiveTensorDecompose.injective
  apply DirectSum.ext_component ℝ
  rintro ⟨r, s⟩
  apply oppositeTensorDual_ext (realOppositeBPZ r.1) (realOppositeBPZ s.1)
  intro u v
  have hz := realPositiveTensorEval_decompose r s u v (realPositiveTensorDecompose z)
  have hz' := realPositiveTensorEval_decompose r s u v (realPositiveTensorDecompose z')
  have hleft := congrArg (eval (u : L) (v : L)) (realPositiveTensorDecompose.symm_apply_apply z)
  have hright := congrArg (eval (u : L) (v : L)) (realPositiveTensorDecompose.symm_apply_apply z')
  exact hz.symm.trans (hleft.trans ((h r s u v).trans (hright.symm.trans hz')))

/-- Equation (10) for the native real positive BRST Lie algebra, in the algebraic tensor product. -/
theorem realPositiveSplitTensor_lie (p q : RealPositiveMomentum) (x : W p.1) (y : W q.1) :
    Δ ⁅lof p x, lof q y⁆ =
      realPositiveTensorAd (lof p x) (Δ (lof q y)) -
      realPositiveTensorAd (lof q y) (Δ (lof p x)) +
      realPositiveTensorCartanCoefficient p.1 q.1 •
        (lof p x ⊗ₜ[ℝ] lof q y - lof q y ⊗ₜ[ℝ] lof p x) :=
  realPositiveTensor_ext fun r s u v => realPositiveSplitTensor_lie_pair p q r s x y u v

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
