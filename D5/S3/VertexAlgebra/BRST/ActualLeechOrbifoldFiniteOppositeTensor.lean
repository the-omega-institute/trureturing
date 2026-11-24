/-
Copyright (c) 2026 trureturing contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealCartan
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Finite opposite-dual tensors for the native real Leech-orbifold BRST Lie algebra

Opposite real momentum spaces pair perfectly under BPZ. The transpose of the
negative bracket is an algebraic tensor in the direct sum of the positive
momentum spaces. The native sign convention is `(m, -n)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable section

open scoped BigOperators Classical DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

local notation "Momentum" => (Fin 2 → ℤ)
local notation "L" => momentumRealLie

/-- The underlying real submodule of a homogeneous Cartan weight space. -/
abbrev realMomentumGrade (p : Momentum) : Submodule ℝ L :=
  (realMomentumWeightSpace p).toSubmodule

local notation "W" => realMomentumGrade

local instance (p : Momentum) : FiniteDimensional ℝ (W p) :=
  realMomentumWeightSpace_finiteDimensional p

/-- The real BPZ form pairs a homogeneous vector only with its opposite momentum. -/
theorem momentumRealBPZ_momentum_selection {p q : Momentum} {x y : L}
    (hx : x ∈ realMomentumWeightSpace p) (hy : y ∈ realMomentumWeightSpace q)
    (hq : q ≠ -p) : momentumRealBPZ x y = 0 := by
  obtain ⟨a, ha⟩ := (mem_realMomentumWeightSpace p x).mp hx
  obtain ⟨b, hb⟩ := (mem_realMomentumWeightSpace q y).mp hy
  apply Complex.ofReal_injective
  rw [ofReal_momentumRealBPZ, ← ha, ← hb, Complex.ofReal_zero]
  exact nativeRelativeBPZ_momentum_selection p q a b hq

/-- The restricted BPZ pairing between the real weight spaces at `p` and `-p`. -/
def realOppositeBPZ (p : Momentum) : W p →ₗ[ℝ] W (-p) →ₗ[ℝ] ℝ :=
  momentumRealBPZ.compl₁₂ (W p).subtype (W (-p)).subtype

set_option synthInstance.maxHeartbeats 100000 in
private theorem realWeight_eq_zero_of_oppositeBPZ {p q : Momentum} (hq : q = -p)
    (x : W p) (hx : ∀ y : W q, momentumRealBPZ x y = 0) : x = 0 := by
  apply Subtype.ext
  apply momentumRealBPZ_nondegenerate.1
  intro y
  obtain ⟨d, rfl⟩ := realMomentumWeightSpace_isInternal.surjective y
  induction d using DirectSum.induction_on with
  | zero => simp
  | of r z =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hr : r = q
    · subst r
      exact hx z
    · exact momentumRealBPZ_momentum_selection x.property z.property (hq ▸ hr)
  | add d e hd he => simp only [map_add, hd, he, add_zero]

/-- Global real nondegeneracy, the momentum decomposition and finite dimension give perfection. -/
instance realOppositeBPZ_isPerfPair (p : Momentum) : (realOppositeBPZ p).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot ℝ).mpr ?_
    apply realWeight_eq_zero_of_oppositeBPZ (q := -p) rfl x
    intro y
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
  · apply LinearMap.ker_eq_bot.mp
    refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot ℝ).mpr ?_
    apply realWeight_eq_zero_of_oppositeBPZ (p := -p) (q := p) (neg_neg p).symm x
    intro y
    exact (momentumRealBPZ_symmetric.eq _ _).trans
      (LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y)

section TensorReconstruction

variable {K A B U V : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [FiniteDimensional K U] [FiniteDimensional K V]
  (P : A →ₗ[K] U →ₗ[K] K) (Q : B →ₗ[K] V →ₗ[K] K)
  [P.IsPerfPair] [Q.IsPerfPair]

/-- The product of two perfect pairings identifies a tensor block with the opposite tensor dual. -/
def oppositeTensorDual : A ⊗[K] B ≃ₗ[K] Module.Dual K (U ⊗[K] V) :=
  (TensorProduct.congr P.toPerfPair Q.toPerfPair).trans (TensorProduct.dualDistribEquiv K U V)

@[simp]
theorem oppositeTensorDual_tmul (a : A) (b : B) (u : U) (v : V) :
    oppositeTensorDual P Q (a ⊗ₜ[K] b) (u ⊗ₜ[K] v) = P a u * Q b v := by
  simp [oppositeTensorDual, mul_comm]

/-- Evaluation on pure opposite tensors detects every element of the tensor block. -/
theorem oppositeTensorDual_ext {z z' : A ⊗[K] B}
    (h : ∀ u v, oppositeTensorDual P Q z (u ⊗ₜ[K] v) =
      oppositeTensorDual P Q z' (u ⊗ₜ[K] v)) : z = z' :=
  (oppositeTensorDual P Q).injective (TensorProduct.ext' h)

/-- The inverse product pairing is the finite expansion in the transported dual bases. -/
theorem oppositeTensorDual_symm_eq_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι K U) (c : Module.Basis κ K V)
    (f : Module.Dual K (U ⊗[K] V)) :
    (oppositeTensorDual P Q).symm f =
      ∑ i, ∑ j, f (b i ⊗ₜ[K] c j) •
        (P.toPerfPair.symm (b.dualBasis i) ⊗ₜ[K] Q.toPerfPair.symm (c.dualBasis j)) := by
  apply (oppositeTensorDual P Q).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (b.tensorProduct c).ext
  rintro ⟨k, l⟩
  simp only [Module.Basis.tensorProduct_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, oppositeTensorDual_tmul,
    LinearMap.apply_symm_toPerfPair_self, Module.Basis.dualBasis_apply_self]
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

end TensorReconstruction

attribute [local instance 100] LieRing.ofAssociativeRing in
private def realBracketTensor (r s : Momentum) : W r ⊗[ℝ] W s →ₗ[ℝ] L :=
  TensorProduct.lift
    ((LieAlgebra.ad ℝ L).toLinearMap.compl₁₂ (W r).subtype (W s).subtype)

/-- The tensor block dual to the native bracket on the two opposite real weight spaces. -/
def realSplitTensorBlock (p r s : Momentum) : W p →ₗ[ℝ] W r ⊗[ℝ] W s :=
  (oppositeTensorDual (realOppositeBPZ r) (realOppositeBPZ s)).symm.toLinearMap.comp
    ((LinearMap.lcomp ℝ ℝ (realBracketTensor (-r) (-s))).comp
      (LinearMap.comp momentumRealBPZ (W p).subtype))

/-- The block pairs with every pure opposite tensor by BPZ against the bracket. -/
theorem realSplitTensorBlock_pair (p r s : Momentum) (x : W p) (u : W (-r)) (v : W (-s)) :
    oppositeTensorDual (realOppositeBPZ r) (realOppositeBPZ s)
      (realSplitTensorBlock p r s x) (u ⊗ₜ[ℝ] v) = momentumRealBPZ x ⁅(u : L), (v : L)⁆ := by
  change (oppositeTensorDual (realOppositeBPZ r) (realOppositeBPZ s))
    ((oppositeTensorDual (realOppositeBPZ r) (realOppositeBPZ s)).symm
      ((momentumRealBPZ x).comp (realBracketTensor (-r) (-s)))) (u ⊗ₜ[ℝ] v) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Coefficients of the native block in the two transported dual bases. -/
theorem realSplitTensorBlock_eq_sum (p r s : Momentum) (x : W p)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι ℝ (W (-r))) (c : Module.Basis κ ℝ (W (-s))) :
    realSplitTensorBlock p r s x =
      ∑ i, ∑ j, momentumRealBPZ x ⁅(b i : L), (c j : L)⁆ •
        ((realOppositeBPZ r).toPerfPair.symm (b.dualBasis i) ⊗ₜ[ℝ]
          (realOppositeBPZ s).toPerfPair.symm (c.dualBasis j)) := by
  exact oppositeTensorDual_symm_eq_sum (realOppositeBPZ r) (realOppositeBPZ s) b c
    ((momentumRealBPZ x).comp (realBracketTensor (-r) (-s)))

/-- The real Lie bracket is homogeneous for the Cartan momentum grading. -/
theorem realWeight_lie_mem_add (r s : Momentum) (x : W r) (y : W s) :
    ⁅(x : L), (y : L)⁆ ∈ realMomentumWeightSpace (r + s) := by
  have hx : (x : L) ∈ realMomentumWeightSpace r := x.property
  have hy : (y : L) ∈ realMomentumWeightSpace s := y.property
  simp only [realMomentumWeightSpace, LieModule.mem_weightSpace] at hx hy ⊢
  intro h
  have hw : realMomentumWeight (r + s) h = realMomentumWeight r h + realMomentumWeight s h := by
    obtain ⟨f, rfl⟩ := realCartanEquiv.surjective h
    simp only [realMomentumWeight_coordinates, Pi.add_apply, Int.cast_add]
    ring
  change ⁅(h : L), ⁅(x : L), (y : L)⁆⁆ = _
  rw [leibniz_lie]
  change ⁅⁅h, (x : L)⁆, (y : L)⁆ + ⁅(x : L), ⁅h, (y : L)⁆⁆ = _
  rw [hx h, hy h, smul_lie, lie_smul, hw, add_smul]

set_option synthInstance.maxHeartbeats 100000 in
/-- For a positive first coordinate, second coordinate above one forces the weight space to vanish. -/
theorem realMomentumWeightSpace_eq_bot_of_one_lt_second (p : Momentum)
    (hp : 0 < p 0) (hsecond : 1 < p 1) : realMomentumWeightSpace p = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply (LieSubmodule.mem_bot x).mpr
  by_contra hne
  have hnorm := realMomentumWeight_norm_le_two p x hx hne
  rw [momentumRealBPZ_momentum_norm] at hnorm
  have hprod : (p 0 : ℝ) * (p 1 : ℝ) ≤ 1 := by linarith
  have hprodInt : p 0 * p 1 ≤ 1 := by exact_mod_cast hprod
  have hle := mul_le_mul_of_nonneg_right (show 1 ≤ p 0 by omega) (show 0 ≤ p 1 by omega)
  rw [one_mul] at hle
  omega

/-- Positive native momenta in the ordered null coordinates. -/
abbrev RealPositiveMomentum := {p : Momentum // 0 < p 0}

/-- The two positive tensor factors sum to `p` and obey the native upper bounds on the second
coordinates. Factors at vanishing weights may be included and have zero tensor block. -/
abbrev RealPositiveSplit (p : Momentum) :=
  {rs : RealPositiveMomentum × RealPositiveMomentum //
    rs.1.1 + rs.2.1 = p ∧ rs.1.1 1 ≤ 1 ∧ rs.2.1 1 ≤ 1}

/-- Both factors of a contributing ordered pair lie in the same finite rectangle. -/
theorem realPositiveSplit_bounds {p : Momentum} (i : RealPositiveSplit p) :
    (1 ≤ i.1.1.1 0 ∧ i.1.1.1 0 ≤ p 0 - 1 ∧ p 1 - 1 ≤ i.1.1.1 1 ∧ i.1.1.1 1 ≤ 1) ∧
    (1 ≤ i.1.2.1 0 ∧ i.1.2.1 0 ≤ p 0 - 1 ∧ p 1 - 1 ≤ i.1.2.1 1 ∧ i.1.2.1 1 ≤ 1) := by
  have hfirst := congrFun i.property.1 (0 : Fin 2)
  have hsecond := congrFun i.property.1 (1 : Fin 2)
  change i.1.1.1 0 + i.1.2.1 0 = p 0 at hfirst
  change i.1.1.1 1 + i.1.2.1 1 = p 1 at hsecond
  have hr := i.1.1.property
  have hs := i.1.2.property
  have hr' := i.property.2.1
  have hs' := i.property.2.2
  omega

instance (p : Momentum) : Finite (RealPositiveSplit p) := by
  let rect := (Finset.Icc (1 : ℤ) (p 0 - 1)).product (Finset.Icc (p 1 - 1) 1)
  let f (i : RealPositiveSplit p) : ↥rect :=
    ⟨(i.1.1.1 0, i.1.1.1 1),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨(realPositiveSplit_bounds i).1.1,
        (realPositiveSplit_bounds i).1.2.1⟩,
        Finset.mem_Icc.mpr (realPositiveSplit_bounds i).1.2.2⟩⟩
  apply Finite.of_injective f
  intro i j hij
  have hcoord : (i.1.1.1 0, i.1.1.1 1) = (j.1.1.1 0, j.1.1.1 1) := congrArg Subtype.val hij
  have hr : i.1.1.1 = j.1.1.1 := by
    funext k
    fin_cases k
    · exact congrArg Prod.fst hcoord
    · exact congrArg Prod.snd hcoord
  have hs : i.1.2.1 = j.1.2.1 := by
    apply add_left_cancel (a := i.1.1.1)
    rw [i.property.1, hr, j.property.1]
  exact Subtype.ext (Prod.ext (Subtype.ext hr) (Subtype.ext hs))

noncomputable instance (p : Momentum) : Fintype (RealPositiveSplit p) := Fintype.ofFinite _

/-- The direct sum of the positive real momentum summands. -/
abbrev RealPositiveMomentumSum := ⨁ r : RealPositiveMomentum, W r.1

local notation "L₊" => RealPositiveMomentumSum
/-- The summand injection at a positive momentum. -/
abbrev realPositiveMomentumLof (r : RealPositiveMomentum) : W r.1 →ₗ[ℝ] L₊ :=
  DirectSum.lof ℝ RealPositiveMomentum (fun r : RealPositiveMomentum => ↥(W r.1)) r

/-- The inclusion from the positive momentum sum into the native real algebra. -/
def realPositiveMomentumIncl : L₊ →ₗ[ℝ] L :=
  DirectSum.toModule ℝ RealPositiveMomentum L (fun r => (W r.1).subtype)

/-- Place the homogeneous tensor block at `(r,s)` into the positive tensor product. -/
def realPositiveBlockIncl (r s : RealPositiveMomentum) :
    W r.1 ⊗[ℝ] W s.1 →ₗ[ℝ] L₊ ⊗[ℝ] L₊ :=
  TensorProduct.map (realPositiveMomentumLof r) (realPositiveMomentumLof s)

/-- Evaluate a positive tensor against two arbitrary native real vectors, using product BPZ. -/
def realPositiveTensorEval (u v : L) : L₊ ⊗[ℝ] L₊ →ₗ[ℝ] ℝ :=
  (LinearMap.mul' ℝ ℝ).comp (TensorProduct.map
    ((momentumRealBPZ.flip u).comp realPositiveMomentumIncl)
    ((momentumRealBPZ.flip v).comp realPositiveMomentumIncl))

@[simp]
theorem realPositiveTensorEval_block_tmul (r s : RealPositiveMomentum)
    (x : W r.1) (y : W s.1) (u v : L) :
    realPositiveTensorEval u v (realPositiveBlockIncl r s (x ⊗ₜ[ℝ] y)) =
      momentumRealBPZ x u * momentumRealBPZ y v := by
  simp [realPositiveTensorEval, realPositiveBlockIncl, realPositiveMomentumIncl,
    DirectSum.toModule_lof]

private theorem realWeight_opposite_ne {r a : Momentum} (h : r ≠ a) : -a ≠ -r := by
  intro hneg
  apply h
  simpa only [neg_neg] using (congrArg Neg.neg hneg).symm

private theorem realPositiveTensorEval_block_off (r s a b : RealPositiveMomentum)
    (h : (r, s) ≠ (a, b)) (z : W r.1 ⊗[ℝ] W s.1) (u : W (-a.1)) (v : W (-b.1)) :
    realPositiveTensorEval u v (realPositiveBlockIncl r s z) = 0 := by
  suffices heq : (realPositiveTensorEval u v).comp (realPositiveBlockIncl r s) = 0 by
    exact LinearMap.congr_fun heq z
  apply TensorProduct.ext'
  intro x y
  change realPositiveTensorEval u v (realPositiveBlockIncl r s (x ⊗ₜ[ℝ] y)) = 0
  rw [realPositiveTensorEval_block_tmul]
  by_cases hr : r = a
  · have hs : s ≠ b := fun hs => h (Prod.ext hr hs)
    have hne : s.1 ≠ b.1 := fun hab => hs (Subtype.ext hab)
    rw [momentumRealBPZ_momentum_selection y.property v.property (realWeight_opposite_ne hne),
      mul_zero]
  · have hne : r.1 ≠ a.1 := fun hab => hr (Subtype.ext hab)
    rw [momentumRealBPZ_momentum_selection x.property u.property (realWeight_opposite_ne hne),
      zero_mul]

private theorem realPositiveTensorEval_block_self (r s : RealPositiveMomentum)
    (z : W r.1 ⊗[ℝ] W s.1) (u : W (-r.1)) (v : W (-s.1)) :
    realPositiveTensorEval u v (realPositiveBlockIncl r s z) =
      oppositeTensorDual (realOppositeBPZ r.1) (realOppositeBPZ s.1) z (u ⊗ₜ[ℝ] v) := by
  let ev : Module.Dual ℝ (W (-r.1) ⊗[ℝ] W (-s.1)) →ₗ[ℝ] ℝ :=
    LinearMap.applyₗ (R := ℝ) (u ⊗ₜ[ℝ] v)
  suffices heq : (realPositiveTensorEval u v).comp (realPositiveBlockIncl r s) =
      ev.comp (oppositeTensorDual (realOppositeBPZ r.1) (realOppositeBPZ s.1)).toLinearMap by
    exact LinearMap.congr_fun heq z
  apply TensorProduct.ext'
  intro x y
  change realPositiveTensorEval u v (realPositiveBlockIncl r s (x ⊗ₜ[ℝ] y)) =
    oppositeTensorDual (realOppositeBPZ r.1) (realOppositeBPZ s.1) (x ⊗ₜ[ℝ] y) (u ⊗ₜ[ℝ] v)
  calc
    _ = momentumRealBPZ x u * momentumRealBPZ y v :=
      realPositiveTensorEval_block_tmul r s x y u v
    _ = realOppositeBPZ r.1 x u * realOppositeBPZ s.1 y v := rfl
    _ = _ := (oppositeTensorDual_tmul (realOppositeBPZ r.1) (realOppositeBPZ s.1) x y u v).symm

/-- Assemble a family of supported ordered blocks as an algebraic tensor. -/
def realPositiveTensorAssemble (p : Momentum) :
    (∀ i : RealPositiveSplit p, W i.1.1.1 ⊗[ℝ] W i.1.2.1) →ₗ[ℝ] L₊ ⊗[ℝ] L₊ :=
  ∑ i : RealPositiveSplit p, (realPositiveBlockIncl i.1.1 i.1.2).comp (LinearMap.proj i)

/-- The homogeneous total-degree `p` submodule of supported positive tensors. -/
def realPositiveTensorSupport (p : Momentum) : Submodule ℝ (L₊ ⊗[ℝ] L₊) :=
  (realPositiveTensorAssemble p).range

private theorem realPositiveTensorEval_assemble (p : Momentum)
    (d : ∀ i : RealPositiveSplit p, W i.1.1.1 ⊗[ℝ] W i.1.2.1)
    (r s : RealPositiveMomentum) (u : W (-r.1)) (v : W (-s.1)) :
    realPositiveTensorEval u v (realPositiveTensorAssemble p d) =
      ∑ i : RealPositiveSplit p, realPositiveTensorEval u v (realPositiveBlockIncl i.1.1 i.1.2 (d i)) :=
  by simp only [realPositiveTensorAssemble, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]

private theorem realPositiveTensorEval_assemble_single (p : Momentum)
    (d : ∀ i : RealPositiveSplit p, W i.1.1.1 ⊗[ℝ] W i.1.2.1) (i : RealPositiveSplit p)
    (u : W (-i.1.1.1)) (v : W (-i.1.2.1)) :
    realPositiveTensorEval u v (realPositiveTensorAssemble p d) =
      realPositiveTensorEval u v (realPositiveBlockIncl i.1.1 i.1.2 (d i)) := by
  rw [realPositiveTensorEval_assemble, Finset.sum_eq_single i]
  · intro j _ hji
    exact realPositiveTensorEval_block_off j.1.1 j.1.2 i.1.1 i.1.2
      (fun h => hji (Subtype.ext h)) (d j) u v
  · simp

/-- Oppositely homogeneous pure tensors detect equality in the supported total degree. -/
theorem realPositiveTensorSupport_ext (p : Momentum) {z z' : L₊ ⊗[ℝ] L₊}
    (hz : z ∈ realPositiveTensorSupport p) (hz' : z' ∈ realPositiveTensorSupport p)
    (h : ∀ (i : RealPositiveSplit p) (u : W (-i.1.1.1)) (v : W (-i.1.2.1)),
      realPositiveTensorEval u v z = realPositiveTensorEval u v z') : z = z' := by
  obtain ⟨d, rfl⟩ := hz
  obtain ⟨e, rfl⟩ := hz'
  apply congrArg (realPositiveTensorAssemble p)
  funext i
  apply oppositeTensorDual_ext (realOppositeBPZ i.1.1.1) (realOppositeBPZ i.1.2.1)
  intro u v
  simpa only [realPositiveTensorEval_assemble_single, realPositiveTensorEval_block_self] using h i u v

/-- The homogeneous native split tensor, assembled from the finitely many positive ordered blocks. -/
def realSplitTensor (p : Momentum) : W p →ₗ[ℝ] L₊ ⊗[ℝ] L₊ :=
  (realPositiveTensorAssemble p).comp
    (LinearMap.pi fun i : RealPositiveSplit p => realSplitTensorBlock p i.1.1.1 i.1.2.1)

/-- The native split tensor has total degree `p` with positive bidegrees. -/
theorem realSplitTensor_mem_support (p : Momentum) (x : W p) :
    realSplitTensor p x ∈ realPositiveTensorSupport p :=
  ⟨fun i => realSplitTensorBlock p i.1.1.1 i.1.2.1 x, rfl⟩

/-- The native split tensor vanishes in first coordinate one. -/
theorem realSplitTensor_eq_zero_of_first_eq_one (p : Momentum) (hp : p 0 = 1) :
    realSplitTensor p = 0 := by
  have : IsEmpty (RealPositiveSplit p) :=
    ⟨fun i => by have := (realPositiveSplit_bounds i).1; omega⟩
  simp [realSplitTensor, realPositiveTensorAssemble]

private theorem realSplitTensor_pair_on_split (p : Momentum) (x : W p) (i : RealPositiveSplit p)
    (u : W (-i.1.1.1)) (v : W (-i.1.2.1)) :
    realPositiveTensorEval u v (realSplitTensor p x) = momentumRealBPZ x ⁅(u : L), (v : L)⁆ := by
  change realPositiveTensorEval u v
    (realPositiveTensorAssemble p (fun i => realSplitTensorBlock p i.1.1.1 i.1.2.1 x)) = _
  rw [realPositiveTensorEval_assemble_single, realPositiveTensorEval_block_self]
  exact realSplitTensorBlock_pair p i.1.1.1 i.1.2.1 x u v

set_option synthInstance.maxHeartbeats 100000 in
private theorem realOppositeWeight_eq_zero_of_one_lt_second (r : RealPositiveMomentum)
    (hr : 1 < r.1 1) (u : W (-r.1)) : u = 0 := by
  have hbot := realMomentumWeightSpace_eq_bot_of_one_lt_second r.1 r.property hr
  apply realWeight_eq_zero_of_oppositeBPZ (p := -r.1) (q := r.1) (neg_neg r.1).symm u
  intro y
  have hy : (y : L) ∈ realMomentumWeightSpace r.1 := y.property
  rw [hbot, LieSubmodule.mem_bot] at hy
  rw [hy, map_zero]

set_option synthInstance.maxHeartbeats 100000 in
/-- The finite tensor represents BPZ against the bracket for every pair of negative homogeneous
tests. The labels `r,s` are the positives opposite to the actual test weights. -/
theorem realSplitTensor_pair (p : Momentum) (x : W p) (r s : RealPositiveMomentum)
    (u : W (-r.1)) (v : W (-s.1)) :
    realPositiveTensorEval u v (realSplitTensor p x) = momentumRealBPZ x ⁅(u : L), (v : L)⁆ := by
  by_cases hsum : r.1 + s.1 = p
  · by_cases hr : r.1 1 ≤ 1
    · by_cases hs : s.1 1 ≤ 1
      · exact realSplitTensor_pair_on_split p x ⟨(r, s), hsum, hr, hs⟩ u v
      · rw [realOppositeWeight_eq_zero_of_one_lt_second s (lt_of_not_ge hs) v]
        simp [realPositiveTensorEval]
    · rw [realOppositeWeight_eq_zero_of_one_lt_second r (lt_of_not_ge hr) u]
      simp [realPositiveTensorEval]
  · change realPositiveTensorEval u v
      (realPositiveTensorAssemble p (fun i => realSplitTensorBlock p i.1.1.1 i.1.2.1 x)) = _
    rw [realPositiveTensorEval_assemble]
    have hzero : momentumRealBPZ x ⁅(u : L), (v : L)⁆ = 0 := by
      apply momentumRealBPZ_momentum_selection x.property (realWeight_lie_mem_add _ _ u v)
      rw [← neg_add]
      exact realWeight_opposite_ne (Ne.symm hsum)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    apply realPositiveTensorEval_block_off i.1.1 i.1.2 r s _ _ u v
    intro h
    apply hsum
    exact (congrArg (fun j : RealPositiveMomentum × RealPositiveMomentum => j.1.1 + j.2.1) h).symm.trans i.property.1

/-- Characterize the split tensor uniquely by its supported bidegrees and bracket evaluation. -/
theorem realSplitTensor_unique (p : Momentum) (x : W p) {z : L₊ ⊗[ℝ] L₊}
    (hz : z ∈ realPositiveTensorSupport p)
    (h : ∀ (r s : RealPositiveMomentum) (u : W (-r.1)) (v : W (-s.1)),
      realPositiveTensorEval u v z = momentumRealBPZ x ⁅(u : L), (v : L)⁆) :
    z = realSplitTensor p x :=
  realPositiveTensorSupport_ext p hz (realSplitTensor_mem_support p x)
    (fun i u v => (h i.1.1 i.1.2 u v).trans (realSplitTensor_pair_on_split p x i u v).symm)

/-- The native positive split map, obtained by linear extension from homogeneous inputs. -/
def realPositiveSplitTensor : L₊ →ₗ[ℝ] L₊ ⊗[ℝ] L₊ :=
  DirectSum.toModule ℝ RealPositiveMomentum (L₊ ⊗[ℝ] L₊) (fun p => realSplitTensor p.1)

@[simp]
theorem realPositiveSplitTensor_lof (p : RealPositiveMomentum) (x : W p.1) :
    realPositiveSplitTensor (realPositiveMomentumLof p x) = realSplitTensor p.1 x := by
  rw [realPositiveSplitTensor, realPositiveMomentumLof, DirectSum.toModule_lof]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
