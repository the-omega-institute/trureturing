/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelativeComparison
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelativeComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native joint-zero semirelative BRST comparison with the double-relative complex. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Native semirelative closed BRST comparison

The joint zero-energy shell in the native semirelative complex has two
double-relative coordinates. The off-diagonal entry in the differential
is the half-sum of the two chiral c-zero Ward terms.

Harrison–Paquette–Persson–Volpato, [arXiv:2107.03507](https://arxiv.org/abs/2107.03507),
Appendix B, (B.1), gives the analogous superstring comparison. The identities
here use the zero modes and differential of the original orbifold carrier.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelativeComparison

open D5.S3.Quantum.Fermionic
open D5.S3.HomologicalAlgebra.FinitePerturbation (Cohomology)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent (relativeStates)
open OriginalOrbifoldBRSTZeroEnergy (totalL0)
open OriginalOrbifoldClosedSemirelative
open private parity_square Q_parity b_zero_parity b_square from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private c_zero_parity chiralMixed chiralL0_c chiralL0_parity chiralWard from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev b0 : Module.End ℂ State := b 0
private abbrev c0 : Module.End ℂ State := VirasoroBRST.ghostC matterDatum 0

local notation "ℓ(" T ")" => LinearMap.rTensor State T
local notation "r(" T ")" => LinearMap.lTensor State T
local notation "ρ(" T ")" => TensorProduct.map parity T

abbrev leftEnergy : Module.End ℂ ClosedState := ℓ(totalL0)
abbrev rightEnergy : Module.End ℂ ClosedState := r(totalL0)
abbrev sumEnergy : Module.End ℂ ClosedState := leftEnergy + rightEnergy

def bPlus : Module.End ℂ ClosedState := ℓ(b0) + ρ(b0)
def cPlus : Module.End ℂ ClosedState := (1 / 2 : ℂ) • (ℓ(c0) + ρ(c0))

private lemma chiralL0_b : totalL0 * b0 = b0 * totalL0 := by
  have ward : Q * b0 + b0 * Q = totalL0 := VirasoroBRST.Q_ward_b matterDatum 0
  have hb : b0 * b0 = 0 := by
    apply LinearMap.ext
    intro x
    exact b_square 0 x
  rw [← ward]
  calc
    (Q * b0 + b0 * Q) * b0 = Q * (b0 * b0) + b0 * (Q * b0) := by
      rw [add_mul, mul_assoc, mul_assoc]
    _ = b0 * (Q * b0) + (b0 * b0) * Q := by rw [hb, mul_zero, zero_mul, zero_add, add_zero]
    _ = b0 * (Q * b0 + b0 * Q) :=
      (congrArg (b0 * (Q * b0) + ·) (mul_assoc b0 b0 Q)).trans (mul_add b0 (Q * b0) (b0 * Q)).symm

private lemma left_right (A B : Module.End ℂ State) :
    ℓ(A) * r(B) = r(B) * ℓ(A) := by
  apply TensorProduct.ext'
  intro x y
  rfl

private lemma left_twisted (A B : Module.End ℂ State)
    (h : A * parity = parity * A) : ℓ(A) * ρ(B) = ρ(B) * ℓ(A) := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  rw [show A (parity x) = parity (A x) from LinearMap.congr_fun h x]

private lemma right_twisted (A B : Module.End ℂ State)
    (h : A * B = B * A) : r(A) * ρ(B) = ρ(B) * r(A) := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
  rw [show A (B y) = B (A y) from LinearMap.congr_fun h y]

private lemma leftEnergy_closedQ : leftEnergy * closedQ = closedQ * leftEnergy := by
  have hp : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  change ℓ(totalL0) * (ℓ(Q) + ρ(Q)) = (ℓ(Q) + ρ(Q)) * ℓ(totalL0)
  rw [mul_add, add_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul,
    OriginalOrbifoldBRSTZeroEnergy.Q_totalL0, left_twisted _ _ hp]

private lemma leftEnergy_cPlus : leftEnergy * cPlus = cPlus * leftEnergy := by
  have hp : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  have hc : totalL0 * c0 = c0 * totalL0 := LinearMap.ext chiralL0_c
  unfold cPlus
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul,
    hc, left_twisted _ _ hp]

private lemma LMinus_cPlus : LMinus * cPlus = cPlus * LMinus := by
  have hp : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  have hc : totalL0 * c0 = c0 * totalL0 := LinearMap.ext chiralL0_c
  change (leftEnergy - rightEnergy) * cPlus = cPlus * (leftEnergy - rightEnergy)
  rw [sub_mul, mul_sub, leftEnergy_cPlus]
  congr 1
  unfold cPlus
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, add_mul, ← (left_right c0 totalL0), right_twisted _ _ hc]

private lemma bPlus_tmul (x y : State) :
    bPlus (x ⊗ₜ[ℂ] y) = b0 x ⊗ₜ[ℂ] y + parity x ⊗ₜ[ℂ] b0 y := rfl

private lemma cPlus_tmul (x y : State) :
    cPlus (x ⊗ₜ[ℂ] y) =
      (1 / 2 : ℂ) • (c0 x ⊗ₜ[ℂ] y + parity x ⊗ₜ[ℂ] c0 y) := rfl

/-- The sum Ward identity has both chiral energy terms with positive sign. -/
theorem sum_ward : closedQ * bPlus + bPlus * closedQ = sumEnergy := by
  apply TensorProduct.ext'
  intro x y
  change closedQ (bPlus (x ⊗ₜ[ℂ] y)) + bPlus (closedQ (x ⊗ₜ[ℂ] y)) =
    totalL0 x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] totalL0 y
  have ward (z : State) : Q (b0 z) + b0 (Q z) = totalL0 z := chiralWard z
  simp only [closedQ_tmul, bPlus_tmul, map_add, Q_parity, b_zero_parity, parity_square,
    TensorProduct.neg_tmul]
  calc
    _ = (Q (b0 x) + b0 (Q x)) ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] (Q (b0 y) + b0 (Q y)) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
    _ = _ := by rw [ward, ward]

private lemma bPlus_sq : bPlus * bPlus = 0 := by
  apply TensorProduct.ext'
  intro x y
  change bPlus (bPlus (x ⊗ₜ[ℂ] y)) = 0
  simp only [bPlus_tmul, map_add, b_zero_parity, parity_square, b_square,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, TensorProduct.neg_tmul]
  abel

private lemma bMinus_bPlus : bMinus * bPlus + bPlus * bMinus = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [bPlus, Module.End.mul_apply, LinearMap.add_apply, bMinus_tmul, map_add, map_sub,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, b_zero_parity, parity_square, b_square,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, TensorProduct.neg_tmul,
    LinearMap.zero_apply]
  abel

private lemma leftEnergy_bPlus : leftEnergy * bPlus = bPlus * leftEnergy := by
  have hp : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  unfold bPlus
  rw [mul_add, add_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul,
    chiralL0_b, left_twisted _ _ hp]

private lemma LMinus_bPlus : LMinus * bPlus = bPlus * LMinus := by
  change (leftEnergy - rightEnergy) * bPlus = bPlus * (leftEnergy - rightEnergy)
  rw [sub_mul, mul_sub, leftEnergy_bPlus]
  congr 1
  unfold bPlus
  rw [mul_add, add_mul, ← (left_right b0 totalL0), right_twisted _ _ chiralL0_b]

/-- The difference antighost annihilates the sum ghost insertion on its kernel. -/
theorem bMinus_cPlus : bMinus * cPlus + cPlus * bMinus = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [cPlus, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    bMinus_tmul, map_smul, map_add, map_sub, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
    b_zero_parity, c_zero_parity, parity_square, TensorProduct.neg_tmul, ← smul_sub, ← smul_add]
  calc
    _ = (1 / 2 : ℂ) • ((b0 (c0 x) + c0 (b0 x)) ⊗ₜ[ℂ] y -
          x ⊗ₜ[ℂ] (b0 (c0 y) + c0 (b0 y))) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      congr 1
      abel
    _ = _ := by rw [chiralMixed, chiralMixed, sub_self, smul_zero, LinearMap.zero_apply]

theorem bPlus_cPlus : bPlus * cPlus + cPlus * bPlus = 1 := by
  apply TensorProduct.ext'
  intro x y
  simp only [bPlus, cPlus, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_smul, map_add, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
    b_zero_parity, c_zero_parity, parity_square, TensorProduct.neg_tmul, ← smul_add]
  calc
    _ = (1 / 2 : ℂ) • ((b0 (c0 x) + c0 (b0 x)) ⊗ₜ[ℂ] y +
          x ⊗ₜ[ℂ] (b0 (c0 y) + c0 (b0 y))) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      congr 1
      abel
    _ = _ := by
      rw [chiralMixed, chiralMixed, smul_add, ← add_smul]
      norm_num

def sumConnection : Module.End ℂ ClosedState := closedQ * cPlus + cPlus * closedQ

/-- The full connecting operator has the native chiral Ward terms, including the factor 1/2.
The two parity signs on the right cancel because the chiral Ward term is even. -/
theorem sumConnection_eq :
    sumConnection = (1 / 2 : ℂ) •
      (ℓ(VirasoroBRST.ghostR matterDatum 0) + r(VirasoroBRST.ghostR matterDatum 0)) := by
  have ward (x : State) : Q (c0 x) + c0 (Q x) = VirasoroBRST.ghostR matterDatum 0 x :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_c matterDatum 0) x
  apply TensorProduct.ext'
  intro x y
  change closedQ (cPlus (x ⊗ₜ[ℂ] y)) + cPlus (closedQ (x ⊗ₜ[ℂ] y)) =
    (1 / 2 : ℂ) • (VirasoroBRST.ghostR matterDatum 0 x ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] VirasoroBRST.ghostR matterDatum 0 y)
  simp only [closedQ_tmul, cPlus_tmul, map_smul, map_add, Q_parity, c_zero_parity,
    parity_square, TensorProduct.neg_tmul, ← smul_add]
  rw [← ward x, ← ward y, TensorProduct.add_tmul, TensorProduct.tmul_add]
  congr 1
  abel

private lemma closedQ_sumConnection : closedQ * sumConnection = sumConnection * closedQ := by
  rw [sumConnection, mul_add, add_mul, ← mul_assoc closedQ closedQ cPlus,
    mul_assoc cPlus closedQ closedQ, closedQ_square, zero_mul, mul_zero,
    zero_add, add_zero, mul_assoc]

/-- On level-matched states, left energy zero implies right energy zero. -/
def jointZeroShell : Submodule ℂ ClosedState := semirelativeStates ⊓ LinearMap.ker leftEnergy

theorem mem_jointZeroShell (x : ClosedState) :
    x ∈ jointZeroShell ↔ bMinus x = 0 ∧ leftEnergy x = 0 ∧ rightEnergy x = 0 := by
  change (bMinus x = 0 ∧ leftEnergy x - rightEnergy x = 0) ∧ leftEnergy x = 0 ↔ _
  constructor
  · rintro ⟨⟨hb, hm⟩, hl⟩
    exact ⟨hb, hl, (sub_eq_zero.mp hm).symm.trans hl⟩
  · rintro ⟨hb, hl, hr⟩
    exact ⟨⟨hb, sub_eq_zero.mpr (hl.trans hr.symm)⟩, hl⟩

private lemma sumEnergy_shell (x : jointZeroShell) : sumEnergy x = 0 := by
  obtain ⟨_, hl, hr⟩ := (mem_jointZeroShell _).mp x.property
  change leftEnergy x + rightEnergy x = 0
  rw [hl, hr, add_zero]

private lemma shell_Q_mem (x : ClosedState) (hx : x ∈ jointZeroShell) :
    closedQ x ∈ jointZeroShell := by
  refine ⟨closedQ_mem_semirelativeStates x hx.1, ?_⟩
  have hl : leftEnergy x = 0 := hx.2
  change leftEnergy (closedQ x) = 0
  simpa only [Module.End.mul_apply, hl, map_zero] using LinearMap.congr_fun leftEnergy_closedQ x

private lemma bPlus_semirelative_mem (x : ClosedState) (hx : x ∈ semirelativeStates) :
    bPlus x ∈ semirelativeStates := by
  obtain ⟨hb, hm⟩ := (mem_semirelativeStates _).mp hx
  refine (mem_semirelativeStates _).mpr ⟨?_, ?_⟩
  · simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply, hb, map_zero,
      add_zero] using LinearMap.congr_fun bMinus_bPlus x
  · simpa only [Module.End.mul_apply, hm, map_zero] using LinearMap.congr_fun LMinus_bPlus x

private lemma shell_bPlus_mem (x : ClosedState) (hx : x ∈ jointZeroShell) :
    bPlus x ∈ jointZeroShell := by
  refine ⟨bPlus_semirelative_mem x hx.1, ?_⟩
  have hl : leftEnergy x = 0 := hx.2
  change leftEnergy (bPlus x) = 0
  simpa only [Module.End.mul_apply, hl, map_zero] using LinearMap.congr_fun leftEnergy_bPlus x

private lemma shell_cPlus_mem (x : ClosedState) (hx : x ∈ jointZeroShell) :
    cPlus x ∈ jointZeroShell := by
  obtain ⟨hb, hm⟩ := (mem_semirelativeStates _).mp hx.1
  have hl : leftEnergy x = 0 := hx.2
  refine ⟨(mem_semirelativeStates _).mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply, hb, map_zero,
      add_zero] using LinearMap.congr_fun bMinus_cPlus x
  · simpa only [Module.End.mul_apply, hm, map_zero] using LinearMap.congr_fun LMinus_cPlus x
  · change leftEnergy (cPlus x) = 0
    simpa only [Module.End.mul_apply, hl, map_zero] using LinearMap.congr_fun leftEnergy_cPlus x

def shellDifferential : Module.End ℂ jointZeroShell := closedQ.restrict shell_Q_mem

theorem shellDifferential_square : shellDifferential * shellDifferential = 0 := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (LinearMap.congr_fun closedQ_square (x : ClosedState))

abbrev ShellCohomology := Cohomology shellDifferential shellDifferential_square

local notation "includeRelative" =>
  (semirelativeStates.subtype.comp doubleRelativeInclusion)

section TensorKernel

private lemma includeRelative_injective : Function.Injective includeRelative :=
  semirelativeStates.subtype_injective.comp doubleRelativeInclusion_injective

private lemma includeRelative_chain (x : DoubleRelativeState) :
    includeRelative (doubleRelativeDifferential x) = closedQ (includeRelative x) :=
  congrArg (fun z : semirelativeStates => (z : ClosedState))
    (LinearMap.congr_fun doubleRelativeInclusion_chain x)

private lemma includeRelative_kills (x : DoubleRelativeState) :
    includeRelative x ∈ jointZeroShell ∧ bPlus (includeRelative x) = 0 := by
  have hL : leftEnergy.comp includeRelative = 0 := by
    apply TensorProduct.ext'
    intro u v
    have hu : totalL0 (u : State) = 0 := u.property.2
    change leftEnergy (doubleRelativeInclusion (u ⊗ₜ[ℂ] v) : ClosedState) = 0
    rw [doubleRelativeInclusion_tmul, LinearMap.rTensor_tmul, hu, TensorProduct.zero_tmul]
  have hb : bPlus.comp includeRelative = 0 := by
    apply TensorProduct.ext'
    intro u v
    have hu : b0 (u : State) = 0 := u.property.1
    have hv : b0 (v : State) = 0 := v.property.1
    change bPlus (doubleRelativeInclusion (u ⊗ₜ[ℂ] v) : ClosedState) = 0
    rw [doubleRelativeInclusion_tmul]
    simp only [bPlus, LinearMap.add_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      hu, hv, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  exact ⟨⟨(doubleRelativeInclusion x).property, LinearMap.congr_fun hL x⟩,
    LinearMap.congr_fun hb x⟩

private lemma bFactors_kill (x : ClosedState) (hm : bMinus x = 0) (hp : bPlus x = 0) :
    ℓ(b0) x = 0 ∧ r(b0) x = 0 := by
  change ℓ(b0) x - ρ(b0) x = 0 at hm
  change ℓ(b0) x + ρ(b0) x = 0 at hp
  have hL : ℓ(b0) x = 0 := by
    have htwo : (2 : ℂ) • ℓ(b0) x = 0 := by
      rw [two_smul]
      exact (congrArg (ℓ(b0) x + ·) (sub_eq_zero.mp hm)).trans hp
    have hhalf := congrArg (fun z : ClosedState => (1 / 2 : ℂ) • z) htwo
    simpa only [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul, smul_zero]
      using hhalf
  have hR : ρ(b0) x = 0 := (sub_eq_zero.mp hm).symm.trans hL
  have unTwist : ℓ(parity) * ρ(b0) = r(b0) := by
    apply TensorProduct.ext'
    intro u v
    simp only [Module.End.mul_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      LinearMap.lTensor_tmul, parity_square]
  exact ⟨hL, by rw [← unTwist, Module.End.mul_apply, hR, map_zero]⟩

private def relativeConstraints : State →ₗ[ℂ] State × State :=
  b0.prod totalL0

private lemma relativeConstraints_exact :
    Function.Exact relativeStates.subtype relativeConstraints := by
  rw [LinearMap.exact_iff, Submodule.range_subtype, relativeConstraints, LinearMap.ker_prod]
  rfl

set_option synthInstance.maxHeartbeats 80000 in
-- Flatness synthesis for the product of the two tensor-state spaces.
/-- Simultaneous kernel of both zero energies and both antighosts, expressed
using the sum and difference antighost on the ambient tensor. -/
theorem range_doubleRelative_iff (x : ClosedState) :
    (∃ u : DoubleRelativeState, (doubleRelativeInclusion u : ClosedState) = x) ↔
      x ∈ jointZeroShell ∧ bPlus x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact includeRelative_kills u
  · rintro ⟨hx, hb⟩
    obtain ⟨hm, hl, hr⟩ := (mem_jointZeroShell x).mp hx
    obtain ⟨hbl, hbr⟩ := bFactors_kill x hm hb
    have leftTest :
        (TensorProduct.prodLeft ℂ ℂ State State State).toLinearMap.comp
          (relativeConstraints.rTensor State) = (ℓ(b0)).prod leftEnergy := by
      apply TensorProduct.ext'
      intro u v
      rfl
    have rightTest :
        (TensorProduct.prodRight ℂ ℂ State State State).toLinearMap.comp
          (relativeConstraints.lTensor State) = (r(b0)).prod rightEnergy := by
      apply TensorProduct.ext'
      intro u v
      rfl
    have hLeft : relativeConstraints.rTensor State x = 0 := by
      apply (TensorProduct.prodLeft ℂ ℂ State State State).injective
      rw [(TensorProduct.prodLeft ℂ ℂ State State State).map_zero]
      change ((TensorProduct.prodLeft ℂ ℂ State State State).toLinearMap.comp
        (relativeConstraints.rTensor State)) x = 0
      rw [leftTest]
      change (ℓ(b0) x, leftEnergy x) = 0
      rw [hbl, hl]
      rfl
    have hRight : relativeConstraints.lTensor State x = 0 := by
      apply (TensorProduct.prodRight ℂ ℂ State State State).injective
      rw [(TensorProduct.prodRight ℂ ℂ State State State).map_zero]
      change ((TensorProduct.prodRight ℂ ℂ State State State).toLinearMap.comp
        (relativeConstraints.lTensor State)) x = 0
      rw [rightTest]
      change (r(b0) x, rightEnergy x) = 0
      rw [hbr, hr]
      rfl
    obtain ⟨y, hy⟩ := (Module.Flat.rTensor_exact State relativeConstraints_exact x).mp hLeft
    have commute :
        (relativeStates.subtype.rTensor (State × State)).comp
          (relativeConstraints.lTensor relativeStates) =
        (relativeConstraints.lTensor State).comp (relativeStates.subtype.rTensor State) := by
      apply TensorProduct.ext'
      intro u v
      rfl
    have hyRight : relativeConstraints.lTensor relativeStates y = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap
        relativeStates.subtype relativeStates.subtype_injective
      rw [map_zero]
      change ((relativeStates.subtype.rTensor (State × State)).comp
        (relativeConstraints.lTensor relativeStates)) y = 0
      rw [commute, LinearMap.comp_apply, hy]
      exact hRight
    obtain ⟨u, hu⟩ :=
      (Module.Flat.lTensor_exact relativeStates relativeConstraints_exact y).mp hyRight
    have factor : includeRelative =
        (relativeStates.subtype.rTensor State).comp
          (relativeStates.subtype.lTensor relativeStates) := by
      apply TensorProduct.ext'
      intro a v
      exact doubleRelativeInclusion_tmul a v
    refine ⟨u, ?_⟩
    change includeRelative u = x
    rw [factor, LinearMap.comp_apply, hu, hy]

end TensorKernel

local notation "R" => DoubleRelativeState
local notation "d" => doubleRelativeDifferential

private def shellInclusion : R →ₗ[ℂ] jointZeroShell :=
  LinearMap.codRestrict jointZeroShell includeRelative (fun u => (includeRelative_kills u).1)

private def shellInsertion : R →ₗ[ℂ] jointZeroShell :=
  (cPlus.comp includeRelative).codRestrict _ (fun u =>
    shell_cPlus_mem _ (includeRelative_kills u).1)

private lemma bPlus_i (u : R) : bPlus (includeRelative u) = 0 :=
  (includeRelative_kills u).2

private lemma bPlus_c_of_bPlus_zero (x : ClosedState) (hx : bPlus x = 0) :
    bPlus (cPlus x) = x := by
  simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, hx,
    map_zero, add_zero] using LinearMap.congr_fun bPlus_cPlus x

private lemma bPlus_coordinate (u v : R) :
    bPlus (includeRelative u + cPlus (includeRelative v)) = includeRelative v := by
  rw [map_add, bPlus_i, bPlus_c_of_bPlus_zero _ (bPlus_i v), zero_add]

/-- The forward linear equivalence sends `(u,v)` to `i u + cPlus (i v)`. -/
def shellCoordinates : (R × R) ≃ₗ[ℂ] jointZeroShell :=
  LinearEquiv.ofBijective (shellInclusion.coprod shellInsertion) (by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      have hs := congrArg (fun z : jointZeroShell => (z : ClosedState)) h
      change includeRelative u + cPlus (includeRelative v) =
        includeRelative u' + cPlus (includeRelative v') at hs
      have hv : v = v' := by
        apply includeRelative_injective
        simpa only [bPlus_coordinate] using congrArg bPlus hs
      subst v'
      exact Prod.ext (includeRelative_injective (add_right_cancel hs)) rfl
    · intro z
      have hbb : bPlus (bPlus (z : ClosedState)) = 0 :=
        LinearMap.congr_fun bPlus_sq (z : ClosedState)
      obtain ⟨v, hv⟩ := (range_doubleRelative_iff _).mpr
        ⟨shell_bPlus_mem _ z.property, hbb⟩
      change includeRelative v = bPlus (z : ClosedState) at hv
      have hc := shell_cPlus_mem _ (includeRelative_kills v).1
      obtain ⟨u, hu⟩ := (range_doubleRelative_iff _).mpr
        ⟨jointZeroShell.sub_mem z.property hc, by
          rw [map_sub, bPlus_c_of_bPlus_zero _ (bPlus_i v), hv, sub_self]⟩
      change includeRelative u = (z : ClosedState) - cPlus (includeRelative v) at hu
      refine ⟨(u, v), Subtype.ext ?_⟩
      change includeRelative u + cPlus (includeRelative v) = (z : ClosedState)
      rw [hu, sub_add_cancel])

theorem shellCoordinates_apply (u v : R) :
    (shellCoordinates (u, v) : ClosedState) = includeRelative u + cPlus (includeRelative v) :=
  rfl

/-- The inverse coordinates recover the sum antighost and the corresponding remainder. -/
theorem shellCoordinates_symm_apply (x : jointZeroShell) :
    includeRelative (shellCoordinates.symm x).2 = bPlus (x : ClosedState) ∧
    includeRelative (shellCoordinates.symm x).1 =
      (x : ClosedState) - cPlus (bPlus (x : ClosedState)) := by
  have h := congrArg (fun z : jointZeroShell => (z : ClosedState))
    (shellCoordinates.apply_symm_apply x)
  change includeRelative (shellCoordinates.symm x).1 +
      cPlus (includeRelative (shellCoordinates.symm x).2) = (x : ClosedState) at h
  have hb := congrArg bPlus h
  rw [bPlus_coordinate] at hb
  exact ⟨hb, eq_sub_of_add_eq (by rw [← hb]; exact h)⟩

private lemma sumConnection_bPlus_zero (v : R) :
    bPlus (sumConnection (includeRelative v)) = 0 := by
  have ward (z : ClosedState) (hz : z ∈ jointZeroShell) :
      closedQ (bPlus z) + bPlus (closedQ z) = 0 :=
    (LinearMap.congr_fun sum_ward z).trans (sumEnergy_shell ⟨z, hz⟩)
  have h1 := ward _ (shell_cPlus_mem _ (includeRelative_kills v).1)
  have h2 : bPlus (closedQ (includeRelative v)) = 0 := by
    rw [← includeRelative_chain, bPlus_i]
  rw [bPlus_c_of_bPlus_zero _ (bPlus_i v)] at h1
  change bPlus (closedQ (cPlus (includeRelative v)) + cPlus (closedQ (includeRelative v))) = 0
  rw [map_add, bPlus_c_of_bPlus_zero _ h2, add_comm]
  exact h1

private def connectionIntoShell : R →ₗ[ℂ] jointZeroShell :=
  (sumConnection.comp includeRelative).codRestrict _ (fun v => by
    change closedQ (cPlus (includeRelative v)) + cPlus (closedQ (includeRelative v)) ∈
      jointZeroShell
    exact jointZeroShell.add_mem
      (shell_Q_mem _ (shell_cPlus_mem _ (includeRelative_kills v).1))
      (shell_cPlus_mem _ (shell_Q_mem _ (includeRelative_kills v).1)))

/-- Degree-two connection acting on the original double-relative carrier. -/
def connectingOperator : Module.End ℂ R :=
  (LinearMap.fst ℂ R R).comp (shellCoordinates.symm.toLinearMap.comp connectionIntoShell)

theorem connectingOperator_apply (v : R) :
    includeRelative (connectingOperator v) = sumConnection (includeRelative v) := by
  have h := (shellCoordinates_symm_apply (connectionIntoShell v)).2
  change includeRelative (connectingOperator v) =
    sumConnection (includeRelative v) - cPlus (bPlus (sumConnection (includeRelative v))) at h
  rw [sumConnection_bPlus_zero, map_zero, sub_zero] at h
  exact h

theorem connectingOperator_chain : connectingOperator.comp d = (d).comp connectingOperator := by
  apply LinearMap.ext
  intro v
  apply includeRelative_injective
  change includeRelative (connectingOperator (d v)) = includeRelative (d (connectingOperator v))
  simp only [connectingOperator_apply, includeRelative_chain]
  exact (LinearMap.congr_fun closedQ_sumConnection (includeRelative v)).symm

/-- Matrix identity for the native shell complex, with differential `-d` on
the copy shifted up by one ghost number. -/
theorem shellCoordinates_differential (u v : R) :
    shellDifferential (shellCoordinates (u, v)) =
      shellCoordinates (d u + connectingOperator v, -d v) := by
  apply Subtype.ext
  change closedQ (includeRelative u + cPlus (includeRelative v)) =
    includeRelative (d u + connectingOperator v) + cPlus (includeRelative (-d v))
  simp only [map_add, map_neg, connectingOperator_apply, includeRelative_chain,
    sumConnection, LinearMap.add_apply, Module.End.mul_apply]
  abel

end

end D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelativeComparison
