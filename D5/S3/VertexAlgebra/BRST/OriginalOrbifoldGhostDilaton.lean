/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldGhostDilaton
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldGhostDilaton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute exactness and global semirelative nonexactness of the native ghost dilaton. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeSpectrum
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldChiralZeroModeConnection

/-!
# The original-orbifold ghost dilaton

Bergman–Zwiebach, *The Dilaton Theorem and Closed String Backgrounds*,
https://arxiv.org/abs/hep-th/9411047, §2.1, (2.4)–(2.10), give the ghost
dilaton and its absolute primitive and distinguish its semirelative class.
Here the representative is the ordered tensor difference of the literal
top and bottom states of the original chiral shell. The normalization of
the primitive follows from the chiral Ward coefficient 2 and the factor
1/2 in the native difference insertion.

Harrison–Paquette–Persson–Volpato, https://arxiv.org/abs/2107.03507,
Appendix B, (B.1), give the relative/semirelative comparison. The proof
below uses its sum-mode decomposition on joint energy and momentum zero.
It tests every semirelative boundary by a linear functional on that shell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldGhostDilaton

noncomputable section

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostFock (c)
open OriginalOrbifoldCriticalMatter
  (Orbifold Hyperbolic Matter State Q b matterDatum hyperbolicData)
open OriginalOrbifoldClosedSemirelative
open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries Cohomology boundaryMap)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTZeroEnergy
  (P0 totalL0 fullBasis totalEnergy totalL0_basis totalL0_coeff energyWeight energyWeight_coeff)
open OriginalOrbifoldBRSTMomentum
  (momentumZeroMode mem_fixedMomentum_iff_zero_modes b_mem_fixedMomentum)
open OriginalOrbifoldRelativeMassShell
  (relativeMassShell fixedMomentum differential Q_mem_fixedMomentum)
open LatticeGeneratingFieldLocality (Charge)
open OriginalOrbifoldRelativeNull
  (ShellIndex bottom top shellBasis_coe shellVector)
open OriginalOrbifoldChiralZeroModeConnection
  (zeroBasis chiralAnticommutator chiralAnticommutator_bottom chiralAnticommutator_restrict)

open private raise raise_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldChiralZeroModeConnection
open private shellVector_bottom from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
open private differential_zero from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeSpectrum
open private Q_parity b_zero_parity parity_square b_square from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private b0 c0 c_zero_parity chiralMixed chiralL0_c chiralL0_parity from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
open private energyWeight_basis from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private momentumPart momentumPart_mem momentumPart_of_mem momentumPart_commutes
  momentumPart_commutes_diagonal momentumZeroMode_tensor from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum

local instance : AddCommGroup Matter := TensorProduct.addCommGroup (M := Orbifold) (N := Hyperbolic)
local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)
local instance : AddCommGroup ClosedState := TensorProduct.addCommGroup (M := State)

private abbrev UCharge := Charge hyperbolicData

local notation "ℓ(" A ")" => LinearMap.rTensor State A
local notation "r(" A ")" => LinearMap.lTensor State A
local notation "ρ(" A ")" => TensorProduct.map parity A

abbrev ZeroChiralShell := relativeMassShell (0 : UCharge)
abbrev ZeroRelativeTensor := (↥ZeroChiralShell) ⊗[ℂ] (↥ZeroChiralShell)

private abbrev botState : State := shellVector 0 bottom
private abbrev topState : State := shellVector 0 top

private theorem Q_on_chiralShell (x : ZeroChiralShell) : Q (x : State) = 0 := by
  have h := LinearMap.congr_fun differential_zero x
  exact congrArg (fun y : ZeroChiralShell => (y : State)) h

private theorem zeroBasis_val (i : ShellIndex) : (zeroBasis i : State) = shellVector 0 i :=
  shellBasis_coe 0 _ i

private theorem Q_bottom : Q botState = 0 := by
  change Q (shellVector 0 bottom) = 0
  rw [← zeroBasis_val bottom]
  exact Q_on_chiralShell _

private theorem bottom_parity : parity botState = botState := by
  change parity (shellVector 0 bottom) = shellVector 0 bottom
  rw [shellVector_bottom]
  simp [parity]

/-- The literal ordered ghost dilaton in the original closed state space. -/
def ghostDilaton : ClosedState :=
  topState ⊗ₜ[ℂ] botState - botState ⊗ₜ[ℂ] topState

/-- The normalized absolute primitive obtained using the native difference mode. -/
def absolutePrimitive : ClosedState := cMinus (botState ⊗ₜ[ℂ] botState)

theorem absolute_exact : closedQ absolutePrimitive = ghostDilaton := by
  have h : Q (c0 botState) = (2 : ℂ) • topState := by
    have hv := chiralAnticommutator_bottom
    change Q (c0 botState) + c0 (Q botState) = (2 : ℂ) • topState at hv
    rwa [Q_bottom, map_zero, add_zero] at hv
  simp only [absolutePrimitive, ghostDilaton, cMinus_tmul, map_smul, map_sub,
    closedQ_tmul, Q_bottom, h, bottom_parity,
    TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero, zero_add,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  module

theorem ghostDilaton_closed : closedQ ghostDilaton = 0 := by
  rw [← absolute_exact]
  exact LinearMap.congr_fun closedQ_square absolutePrimitive

/-- The normalized sum ghost insertion conjugate to the sum antighost. -/
def cPlus : Module.End ℂ ClosedState := (1 / 2 : ℂ) • (ℓ(c0) + ρ(c0))

def bPlus : Module.End ℂ ClosedState := ℓ(b0) + ρ(b0)

def sumConnection : Module.End ℂ ClosedState := closedQ * cPlus + cPlus * closedQ

private theorem cPlus_apply (z : ClosedState) :
    cPlus z = (1 / 2 : ℂ) • (ℓ(c0) z + ρ(c0) z) := rfl

theorem sumConnection_eq :
    sumConnection = (1 / 2 : ℂ) • (ℓ(chiralAnticommutator) + r(chiralAnticommutator)) := by
  apply TensorProduct.ext'
  intro x y
  change closedQ (cPlus (x ⊗ₜ[ℂ] y)) + cPlus (closedQ (x ⊗ₜ[ℂ] y)) =
    (1 / 2 : ℂ) • (ℓ(chiralAnticommutator) (x ⊗ₜ[ℂ] y) +
      r(chiralAnticommutator) (x ⊗ₜ[ℂ] y))
  simp only [cPlus_apply, closedQ_tmul, map_smul, map_add, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, TensorProduct.map_tmul, Q_parity, c_zero_parity,
    parity_square, TensorProduct.neg_tmul, ← smul_add]
  change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) •
    ((Q (c0 x) + c0 (Q x)) ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] (Q (c0 y) + c0 (Q y)))
  rw [TensorProduct.add_tmul, TensorProduct.tmul_add]
  congr 1
  abel

private theorem sumConnection_tmul (x y : State) :
    sumConnection (x ⊗ₜ[ℂ] y) = (1 / 2 : ℂ) •
      (chiralAnticommutator x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] chiralAnticommutator y) := by
  rw [sumConnection_eq]
  change (1 / 2 : ℂ) • (ℓ(chiralAnticommutator) (x ⊗ₜ[ℂ] y) +
    r(chiralAnticommutator) (x ⊗ₜ[ℂ] y)) = _
  rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]

private theorem bPlus_square : bPlus * bPlus = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [bPlus, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, map_add, b_zero_parity, parity_square, b_square,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, TensorProduct.neg_tmul,
    LinearMap.zero_apply]
  abel

private theorem bMinus_bPlus : bMinus * bPlus + bPlus * bMinus = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [bPlus, Module.End.mul_apply, LinearMap.add_apply, bMinus_tmul, map_add, map_sub,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, b_zero_parity, parity_square, b_square,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, TensorProduct.neg_tmul,
    LinearMap.zero_apply]
  abel

private theorem bMinus_cPlus : bMinus * cPlus + cPlus * bMinus = 0 := by
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

private theorem bPlus_cPlus : bPlus * cPlus + cPlus * bPlus = 1 := by
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

private theorem energyWeight_commute (weight : ℤ → ℂ) (T : Module.End ℂ State)
    (hT : totalL0 * T = T * totalL0) :
    energyWeight weight * T = T * energyWeight weight := by
  apply fullBasis.ext
  intro i
  change energyWeight weight (T (fullBasis i)) = T (energyWeight weight (fullBasis i))
  rw [energyWeight_basis, map_smul]
  apply fullBasis.repr.injective
  ext j
  rw [energyWeight_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : totalEnergy j = totalEnergy i
  · rw [h]
  · have he : totalL0 (T (fullBasis i)) = (totalEnergy i : ℂ) • T (fullBasis i) := by
      simpa only [Module.End.mul_apply, totalL0_basis, map_smul] using
        LinearMap.congr_fun hT (fullBasis i)
    have hcoeff := congrArg (fun x : State => fullBasis.repr x j) he
    change fullBasis.repr (totalL0 (T (fullBasis i))) j =
      fullBasis.repr ((totalEnergy i : ℂ) • T (fullBasis i)) j at hcoeff
    rw [totalL0_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoeff
    have hz : fullBasis.repr (T (fullBasis i)) j = 0 := by
      by_contra hn
      exact h (Int.cast_injective (mul_right_cancel₀ hn hcoeff))
    rw [hz, mul_zero, mul_zero]

private theorem energy_b : totalL0 * b0 = b0 * totalL0 := by
  have ward : Q * b0 + b0 * Q = totalL0 :=
    OriginalOrbifoldCriticalMatter.Q_ward_b 0
  rw [← ward]
  have hb : b0 * b0 = 0 := LinearMap.ext (b_square 0)
  rw [add_mul (Q * b0) (b0 * Q) b0, mul_add b0 (Q * b0) (b0 * Q),
    mul_assoc Q b0 b0, ← mul_assoc b0 b0 Q,
    hb, mul_zero, zero_mul, zero_add, add_zero, mul_assoc b0 Q b0]

private theorem ghostMap_mem_momentum (G : Module.End ℂ Fock) (a : UCharge) (x : State)
    (hx : x ∈ fixedMomentum a) : TensorProduct.map LinearMap.id G x ∈ fixedMomentum a := by
  let T : Module.End ℂ State := TensorProduct.map LinearMap.id G
  change T x ∈ fixedMomentum a
  apply (mem_fixedMomentum_iff_zero_modes a _).mpr
  intro i
  have h : momentumZeroMode i * T = T * momentumZeroMode i := by
    apply TensorProduct.ext'
    intro u v
    simp only [T, momentumZeroMode_tensor, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply]
  change momentumZeroMode i (T x) = (a i : ℂ) • T x
  rw [show momentumZeroMode i (T x) = T (momentumZeroMode i x) from LinearMap.congr_fun h x,
    (mem_fixedMomentum_iff_zero_modes a x).mp hx i, map_smul]

private theorem c0_mem_momentum (a : UCharge) (x : State) (hx : x ∈ fixedMomentum a) :
    c0 x ∈ fixedMomentum a :=
  ghostMap_mem_momentum (c 0) a x hx

private theorem parity_mem_momentum (a : UCharge) (x : State) (hx : x ∈ fixedMomentum a) :
    parity x ∈ fixedMomentum a :=
  ghostMap_mem_momentum CountableOccupationFock.parity a x hx

/-- Both chiral cuts are native. The momentum label is applied on each factor. -/
private def chiralProjection : Module.End ℂ State := P0 * momentumPart 0

private theorem chiralProjection_energy (x : State) : totalL0 (chiralProjection x) = 0 :=
  OriginalOrbifoldBRSTZeroEnergy.totalL0_P0 (momentumPart 0 x)

private theorem chiralProjection_momentum (x : State) : chiralProjection x ∈ fixedMomentum 0 := by
  have h := momentumPart_commutes_diagonal 0 P0
    (fun i => if totalEnergy i = 0 then 1 else 0)
    (energyWeight_basis (fun e => if e = 0 then 1 else 0))
  change P0 (momentumPart 0 x) ∈ fixedMomentum 0
  rw [← show momentumPart 0 (P0 x) = P0 (momentumPart 0 x) from LinearMap.congr_fun h x]
  exact momentumPart_mem 0 _

private theorem chiralProjection_fixed (x : State) (hm : x ∈ fixedMomentum 0)
    (hL : totalL0 x = 0) : chiralProjection x = x := by
  change P0 (momentumPart 0 x) = x
  rw [momentumPart_of_mem hm]
  exact (OriginalOrbifoldBRSTZeroEnergy.P0_fixed_iff x).mpr hL

private theorem chiralProjection_commutes (T : Module.End ℂ State)
    (hL : totalL0 * T = T * totalL0)
    (hm : ∀ a x, x ∈ fixedMomentum a → T x ∈ fixedMomentum a) :
    chiralProjection * T = T * chiralProjection := by
  have hp : P0 * T = T * P0 := energyWeight_commute _ T hL
  have hM : momentumPart 0 * T = T * momentumPart 0 := momentumPart_commutes 0 T hm
  rw [chiralProjection, mul_assoc, hM, ← mul_assoc, hp, mul_assoc]

private theorem projection_Q : chiralProjection * Q = Q * chiralProjection :=
  chiralProjection_commutes Q OriginalOrbifoldBRSTZeroEnergy.Q_totalL0.symm
    (fun a _ hx => Q_mem_fixedMomentum a hx)

private theorem projection_b : chiralProjection * b0 = b0 * chiralProjection :=
  chiralProjection_commutes b0 energy_b (fun _ _ hx => b_mem_fixedMomentum 0 hx)

private theorem projection_c : chiralProjection * c0 = c0 * chiralProjection :=
  chiralProjection_commutes c0 (LinearMap.ext chiralL0_c) c0_mem_momentum

private theorem projection_parity : chiralProjection * parity = parity * chiralProjection :=
  chiralProjection_commutes parity (LinearMap.ext chiralL0_parity) parity_mem_momentum

/-- Joint energy zero and momentum `(0,0)` via independent left and right cuts. -/
def jointProjection : Module.End ℂ ClosedState :=
  TensorProduct.map chiralProjection chiralProjection

private theorem tensor_commutes (A B : Module.End ℂ State)
    (hA : chiralProjection * A = A * chiralProjection)
    (hB : chiralProjection * B = B * chiralProjection) :
    jointProjection * TensorProduct.map A B = TensorProduct.map A B * jointProjection := by
  apply TensorProduct.ext'
  intro x y
  simp only [jointProjection, Module.End.mul_apply, TensorProduct.map_tmul]
  rw [show chiralProjection (A x) = A (chiralProjection x) from LinearMap.congr_fun hA x,
    show chiralProjection (B y) = B (chiralProjection y) from LinearMap.congr_fun hB y]

private theorem id_commutes :
    chiralProjection * LinearMap.id = LinearMap.id * chiralProjection :=
  (mul_one _).trans (one_mul _).symm

theorem jointProjection_closedQ : jointProjection * closedQ = closedQ * jointProjection := by
  unfold closedQ
  rw [mul_add, add_mul, tensor_commutes _ _ projection_Q id_commutes,
    tensor_commutes _ _ projection_parity projection_Q]

theorem jointProjection_bMinus : jointProjection * bMinus = bMinus * jointProjection := by
  unfold bMinus
  rw [mul_sub, sub_mul, tensor_commutes _ _ projection_b id_commutes,
    tensor_commutes _ _ projection_parity projection_b]

private theorem jointProjection_bPlus : jointProjection * bPlus = bPlus * jointProjection := by
  change jointProjection * (TensorProduct.map b0 LinearMap.id + ρ(b0)) = _
  rw [mul_add, show bPlus = TensorProduct.map b0 LinearMap.id + ρ(b0) from rfl, add_mul,
    tensor_commutes _ _ projection_b id_commutes,
    tensor_commutes _ _ projection_parity projection_b]

private theorem jointProjection_cPlus : jointProjection * cPlus = cPlus * jointProjection := by
  change jointProjection * ((1 / 2 : ℂ) • (TensorProduct.map c0 LinearMap.id + ρ(c0))) =
    ((1 / 2 : ℂ) • (TensorProduct.map c0 LinearMap.id + ρ(c0))) * jointProjection
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    tensor_commutes _ _ projection_c id_commutes,
    tensor_commutes _ _ projection_parity projection_c]

private theorem jointProjection_idempotent :
    jointProjection * jointProjection = jointProjection := by
  apply TensorProduct.ext'
  intro x y
  simp only [jointProjection, Module.End.mul_apply, TensorProduct.map_tmul]
  rw [chiralProjection_fixed _ (chiralProjection_momentum x) (chiralProjection_energy x),
    chiralProjection_fixed _ (chiralProjection_momentum y) (chiralProjection_energy y)]

theorem jointProjection_leftEnergy : ℓ(totalL0) * jointProjection = 0 := by
  apply TensorProduct.ext'
  intro x y
  change totalL0 (chiralProjection x) ⊗ₜ[ℂ] chiralProjection y = 0
  rw [chiralProjection_energy, TensorProduct.zero_tmul]

theorem jointProjection_rightEnergy : r(totalL0) * jointProjection = 0 := by
  apply TensorProduct.ext'
  intro x y
  change chiralProjection x ⊗ₜ[ℂ] totalL0 (chiralProjection y) = 0
  rw [chiralProjection_energy, TensorProduct.tmul_zero]

theorem jointProjection_leftMomentum :
    ℓ(momentumPart 0) * jointProjection = jointProjection := by
  apply TensorProduct.ext'
  intro x y
  simp only [jointProjection, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul]
  rw [momentumPart_of_mem (chiralProjection_momentum x)]

theorem jointProjection_rightMomentum :
    r(momentumPart 0) * jointProjection = jointProjection := by
  apply TensorProduct.ext'
  intro x y
  simp only [jointProjection, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul]
  rw [momentumPart_of_mem (chiralProjection_momentum y)]

private theorem jointProjection_LMinus : LMinus * jointProjection = 0 := by
  change (ℓ(totalL0) - r(totalL0)) * jointProjection = 0
  rw [sub_mul, jointProjection_leftEnergy, jointProjection_rightEnergy, sub_zero]

/-- The native semirelative shell at zero energy and both momenta zero. -/
def zeroMomentumShell : Submodule ℂ ClosedState :=
  LinearMap.ker bMinus ⊓ LinearMap.ker (jointProjection - 1)

theorem mem_zeroMomentumShell (z : ClosedState) :
    z ∈ zeroMomentumShell ↔ bMinus z = 0 ∧ jointProjection z = z := by
  change (bMinus z = 0 ∧ jointProjection z - z = 0) ↔ _
  rw [sub_eq_zero]

private theorem zeroMomentumShell_mem_semirelative (z : ClosedState)
    (hz : z ∈ zeroMomentumShell) : z ∈ semirelativeStates := by
  obtain ⟨hb, hp⟩ := (mem_zeroMomentumShell z).mp hz
  refine (mem_semirelativeStates z).mpr ⟨hb, ?_⟩
  simpa only [Module.End.mul_apply, LinearMap.zero_apply, hp] using
    LinearMap.congr_fun jointProjection_LMinus z

theorem jointProjection_mem_zeroMomentumShell (z : ClosedState)
    (hz : z ∈ semirelativeStates) : jointProjection z ∈ zeroMomentumShell := by
  have hb := (mem_semirelativeStates z).mp hz |>.1
  refine (mem_zeroMomentumShell _).mpr ⟨?_, ?_⟩
  · simpa only [Module.End.mul_apply, hb, map_zero] using
      LinearMap.congr_fun jointProjection_bMinus.symm z
  · exact LinearMap.congr_fun jointProjection_idempotent z

private theorem shell_Q_mem (z : ClosedState) (hz : z ∈ zeroMomentumShell) :
    closedQ z ∈ zeroMomentumShell := by
  refine (mem_zeroMomentumShell _).mpr
    ⟨(mem_semirelativeStates _).mp
      (closedQ_mem_semirelativeStates z (zeroMomentumShell_mem_semirelative z hz)) |>.1, ?_⟩
  simpa only [Module.End.mul_apply, (mem_zeroMomentumShell z).mp hz |>.2] using
    LinearMap.congr_fun jointProjection_closedQ z

def zeroShellDifferential : Module.End ℂ zeroMomentumShell := closedQ.restrict shell_Q_mem

private def relativeInclusion : ZeroRelativeTensor →ₗ[ℂ] ClosedState :=
  TensorProduct.map ZeroChiralShell.subtype ZeroChiralShell.subtype

private theorem include_tmul (x y : ZeroChiralShell) :
    relativeInclusion (x ⊗ₜ[ℂ] y) = (x : State) ⊗ₜ[ℂ] (y : State) :=
  TensorProduct.map_tmul _ _ _ _

private theorem chiralProjection_on_relative (x : ZeroChiralShell) :
    chiralProjection (x : State) = x :=
  chiralProjection_fixed _ x.property.1.1 x.property.2

private theorem relativeInclusion_shell (u : ZeroRelativeTensor) :
    relativeInclusion u ∈ zeroMomentumShell := by
  have hb : bMinus.comp relativeInclusion = 0 := by
    apply TensorProduct.ext'
    intro x y
    have hx : b0 (x : State) = 0 := x.property.1.2
    have hy : b0 (y : State) = 0 := y.property.1.2
    simp only [LinearMap.comp_apply, include_tmul, bMinus_tmul, hx, hy,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, sub_zero, LinearMap.zero_apply]
  have hp : jointProjection.comp relativeInclusion = relativeInclusion := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, include_tmul, jointProjection, TensorProduct.map_tmul,
      chiralProjection_on_relative]
  exact (mem_zeroMomentumShell _).mpr ⟨LinearMap.congr_fun hb u, LinearMap.congr_fun hp u⟩

private theorem relative_Q_zero (u : ZeroRelativeTensor) : closedQ (relativeInclusion u) = 0 := by
  have h : closedQ.comp relativeInclusion = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, include_tmul, closedQ_tmul, Q_on_chiralShell,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun h u

private abbrev relativeFactor : Module.End ℂ State := b0 * c0

private theorem relativeFactor_eq : relativeFactor = 1 - c0 * b0 := by
  apply LinearMap.ext
  intro x
  exact eq_sub_of_add_eq (chiralMixed x)

private def chiralRetraction : State →ₗ[ℂ] ZeroChiralShell :=
  (relativeFactor * chiralProjection).codRestrict _ (by
    intro x
    change (b0 (c0 (chiralProjection x)) ∈ fixedMomentum 0 ∧
      b0 (b0 (c0 (chiralProjection x))) = 0) ∧
      totalL0 (b0 (c0 (chiralProjection x))) = 0
    refine ⟨⟨b_mem_fixedMomentum 0 (c0_mem_momentum 0 _ (chiralProjection_momentum x)),
      b_square 0 _⟩, ?_⟩
    rw [show totalL0 (b0 (c0 (chiralProjection x))) = b0 (totalL0 (c0 (chiralProjection x)))
      from LinearMap.congr_fun energy_b _, chiralL0_c, chiralProjection_energy, map_zero, map_zero])

private theorem chiralRetraction_relative (x : ZeroChiralShell) :
    chiralRetraction (x : State) = x := by
  apply Subtype.ext
  change b0 (c0 (chiralProjection (x : State))) = (x : State)
  rw [chiralProjection_on_relative]
  have hb : b0 (x : State) = 0 := x.property.1.2
  simpa only [hb, map_zero, add_zero] using chiralMixed (x : State)

private def relativeRetraction : ClosedState →ₗ[ℂ] ZeroRelativeTensor :=
  TensorProduct.map chiralRetraction chiralRetraction

private theorem retract_include (u : ZeroRelativeTensor) :
    relativeRetraction (relativeInclusion u) = u := by
  have h : relativeRetraction.comp relativeInclusion = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, include_tmul, relativeRetraction,
      TensorProduct.map_tmul, chiralRetraction_relative, LinearMap.id_apply]
  exact LinearMap.congr_fun h u

private theorem bFactors_kill (z : ClosedState) (hm : bMinus z = 0) (hp : bPlus z = 0) :
    ℓ(b0) z = 0 ∧ r(b0) z = 0 := by
  change ℓ(b0) z - ρ(b0) z = 0 at hm
  change ℓ(b0) z + ρ(b0) z = 0 at hp
  have hL : ℓ(b0) z = 0 := by
    have htwo : (2 : ℂ) • ℓ(b0) z = 0 := by
      rw [two_smul]
      exact (congrArg (ℓ(b0) z + ·) (sub_eq_zero.mp hm)).trans hp
    calc
      ℓ(b0) z = (1 / 2 : ℂ) • ((2 : ℂ) • ℓ(b0) z) := by
        rw [smul_smul]
        norm_num
      _ = 0 := by rw [htwo, smul_zero]
  have hR : ρ(b0) z = 0 := (sub_eq_zero.mp hm).symm.trans hL
  have untwist : ℓ(parity) * ρ(b0) = r(b0) := by
    apply TensorProduct.ext'
    intro x y
    simp only [Module.End.mul_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      LinearMap.lTensor_tmul, parity_square]
  exact ⟨hL, by rw [← untwist, Module.End.mul_apply, hR, map_zero]⟩

private theorem include_retract (z : ClosedState) (hm : bMinus z = 0)
    (hp : bPlus z = 0) (hP : jointProjection z = z) :
    relativeInclusion (relativeRetraction z) = z := by
  obtain ⟨hbL, hbR⟩ := bFactors_kill z hm hp
  have hmap : relativeInclusion.comp relativeRetraction =
      (ℓ(relativeFactor) * r(relativeFactor)) * jointProjection := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, relativeRetraction, TensorProduct.map_tmul,
      include_tmul, jointProjection, Module.End.mul_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul]
    rfl
  have hL : ℓ(relativeFactor) z = z := by
    rw [relativeFactor_eq, LinearMap.rTensor_sub, LinearMap.rTensor_mul,
      show ℓ((1 : Module.End ℂ State)) = 1 from LinearMap.rTensor_id State State]
    change z - ℓ(c0) (ℓ(b0) z) = z
    rw [hbL, map_zero, sub_zero]
  have hR : r(relativeFactor) z = z := by
    rw [relativeFactor_eq, LinearMap.lTensor_sub, LinearMap.lTensor_mul,
      show r((1 : Module.End ℂ State)) = 1 from LinearMap.lTensor_id State State]
    change z - r(c0) (r(b0) z) = z
    rw [hbR, map_zero, sub_zero]
  simpa only [LinearMap.comp_apply, Module.End.mul_apply, hP, hL, hR] using
    LinearMap.congr_fun hmap z

/-- Every state in the fixed shell has a double-relative part and a sum-mode part. -/
theorem zeroShell_decompose (z : zeroMomentumShell) :
    ∃ u v : ZeroRelativeTensor,
      (z : ClosedState) = relativeInclusion u + cPlus (relativeInclusion v) := by
  obtain ⟨hb, hP⟩ := (mem_zeroMomentumShell (z : ClosedState)).mp z.property
  let v : ClosedState := bPlus z
  have hvb : bMinus v = 0 := by
    simpa only [v, Module.End.mul_apply, LinearMap.add_apply, hb, map_zero, add_zero,
      LinearMap.zero_apply] using LinearMap.congr_fun bMinus_bPlus (z : ClosedState)
  have hvp : bPlus v = 0 := LinearMap.congr_fun bPlus_square (z : ClosedState)
  have hvP : jointProjection v = v := by
    simpa only [v, Module.End.mul_apply, hP] using
      LinearMap.congr_fun jointProjection_bPlus (z : ClosedState)
  let u : ClosedState := (z : ClosedState) - cPlus v
  have hcB : bMinus (cPlus v) = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.add_apply, hvb, map_zero, add_zero,
      LinearMap.zero_apply] using LinearMap.congr_fun bMinus_cPlus v
  have hcP : jointProjection (cPlus v) = cPlus v := by
    simpa only [Module.End.mul_apply, hvP] using LinearMap.congr_fun jointProjection_cPlus v
  have hcp : bPlus (cPlus v) = v := by
    simpa only [Module.End.mul_apply, LinearMap.add_apply, hvp, map_zero, add_zero,
      Module.End.one_apply] using LinearMap.congr_fun bPlus_cPlus v
  have hub : bMinus u = 0 := by
    dsimp only [u]
    rw [map_sub, hb, hcB, sub_zero]
  have hup : bPlus u = 0 := by
    dsimp only [u]
    rw [map_sub, hcp, sub_self]
  have huP : jointProjection u = u := by
    dsimp only [u]
    rw [map_sub, hP, hcP]
  refine ⟨relativeRetraction u, relativeRetraction v, ?_⟩
  rw [include_retract u hub hup huP, include_retract v hvb hvp hvP]
  exact (sub_add_cancel _ _).symm

private theorem chiralAnticommutator_shell (x : ZeroChiralShell) :
    chiralAnticommutator (x : State) = (2 : ℂ) • (raise x : State) :=
  LinearMap.congr_fun chiralAnticommutator_restrict x

/-- The degree-two sum connection on the actual double-relative zero shell. -/
def zeroShellConnection : Module.End ℂ ZeroRelativeTensor :=
  TensorProduct.map raise LinearMap.id + TensorProduct.map LinearMap.id raise

theorem sumConnection_on_relative (u : ZeroRelativeTensor) :
    sumConnection (relativeInclusion u) = relativeInclusion (zeroShellConnection u) := by
  have h : sumConnection.comp relativeInclusion =
      relativeInclusion.comp zeroShellConnection := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, include_tmul, zeroShellConnection, LinearMap.add_apply,
      map_add, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [sumConnection_tmul, chiralAnticommutator_shell x, chiralAnticommutator_shell y,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← smul_add, smul_smul]
    norm_num
  exact LinearMap.congr_fun h u

private abbrev zeroTensorBasis : Module.Basis (ShellIndex × ShellIndex) ℂ ZeroRelativeTensor :=
  zeroBasis.tensorProduct zeroBasis

/-- The top–bottom coefficient minus the bottom–top coefficient. -/
def antisymmetricCoordinate : ZeroRelativeTensor →ₗ[ℂ] ℂ :=
  zeroTensorBasis.coord (top, bottom) - zeroTensorBasis.coord (bottom, top)

private theorem antisymmetricCoordinate_basis (i : ShellIndex × ShellIndex) :
    antisymmetricCoordinate (zeroTensorBasis i) =
      (if i = (top, bottom) then 1 else 0) - (if i = (bottom, top) then 1 else 0) := by
  classical
  simp only [antisymmetricCoordinate, LinearMap.sub_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

private theorem antisymmetricCoordinate_tmul (i j : ShellIndex) :
    antisymmetricCoordinate (zeroBasis i ⊗ₜ[ℂ] zeroBasis j) =
      (if (i, j) = (top, bottom) then 1 else 0) - (if (i, j) = (bottom, top) then 1 else 0) := by
  rw [← show zeroTensorBasis (i, j) = zeroBasis i ⊗ₜ[ℂ] zeroBasis j from
    Module.Basis.tensorProduct_apply' _ _ _]
  exact antisymmetricCoordinate_basis (i, j)

theorem antisymmetricCoordinate_kills_connection :
    antisymmetricCoordinate.comp zeroShellConnection = 0 := by
  classical
  apply zeroTensorBasis.ext
  rintro ⟨i, j⟩
  simp only [LinearMap.comp_apply, zeroShellConnection, LinearMap.add_apply,
    Module.Basis.tensorProduct_apply', TensorProduct.map_tmul, LinearMap.id_apply,
    raise_basis, map_add, LinearMap.zero_apply]
  have hbt : bottom ≠ top := by decide
  have htb : top ≠ bottom := hbt.symm
  by_cases hi : i = bottom <;> by_cases hj : j = bottom <;>
    simp [hi, hj, hbt, htb, antisymmetricCoordinate_tmul]

theorem sumConnection_vacuum :
    sumConnection (botState ⊗ₜ[ℂ] botState) =
      topState ⊗ₜ[ℂ] botState + botState ⊗ₜ[ℂ] topState := by
  rw [sumConnection_tmul, show chiralAnticommutator botState = (2 : ℂ) • topState from
    chiralAnticommutator_bottom, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    ← smul_add, smul_smul]
  norm_num

/-- A closed functional on the semirelative zero shell. Its relative part is
the antisymmetric coordinate in the actual tensor basis. -/
def zeroShellFunctional : zeroMomentumShell →ₗ[ℂ] ℂ :=
  antisymmetricCoordinate.comp (relativeRetraction.comp zeroMomentumShell.subtype)

theorem zeroShellFunctional_closed :
    zeroShellFunctional.comp zeroShellDifferential = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨u, v, hz⟩ := zeroShell_decompose z
  have hQ : closedQ (z : ClosedState) = relativeInclusion (zeroShellConnection v) := by
    rw [hz, map_add, relative_Q_zero, zero_add, ← sumConnection_on_relative]
    simp only [sumConnection, LinearMap.add_apply, Module.End.mul_apply,
      relative_Q_zero, map_zero, add_zero]
  change antisymmetricCoordinate (relativeRetraction (closedQ (z : ClosedState))) = 0
  rw [hQ, retract_include]
  exact LinearMap.congr_fun antisymmetricCoordinate_kills_connection v

private def relativeDilaton : ZeroRelativeTensor :=
  zeroTensorBasis (top, bottom) - zeroTensorBasis (bottom, top)

private theorem include_dilaton : relativeInclusion relativeDilaton = ghostDilaton := by
  simp only [relativeDilaton, ghostDilaton, map_sub, Module.Basis.tensorProduct_apply',
    include_tmul, zeroBasis_val]

theorem ghostDilaton_mem_zeroMomentumShell : ghostDilaton ∈ zeroMomentumShell := by
  rw [← include_dilaton]
  exact relativeInclusion_shell relativeDilaton

def shellDilaton : zeroMomentumShell := ⟨ghostDilaton, ghostDilaton_mem_zeroMomentumShell⟩

theorem zeroShellFunctional_dilaton : zeroShellFunctional shellDilaton = 2 := by
  change antisymmetricCoordinate (relativeRetraction ghostDilaton) = 2
  rw [← include_dilaton, retract_include, relativeDilaton, map_sub,
    antisymmetricCoordinate_basis, antisymmetricCoordinate_basis]
  norm_num [bottom, top]

/-- The dilaton as a vector of the full native semirelative complex. -/
def semirelativeDilaton : semirelativeStates :=
  ⟨ghostDilaton, zeroMomentumShell_mem_semirelative _ ghostDilaton_mem_zeroMomentumShell⟩

/-- No primitive anywhere in the full native semirelative complex can give
the literal dilaton. The two independent chiral cuts preserve the equation. -/
theorem semirelative_nonexact (z : semirelativeStates) :
    semirelativeDifferential z ≠ semirelativeDilaton := by
  intro h
  have hQ : closedQ (z : ClosedState) = ghostDilaton :=
    congrArg (fun x : semirelativeStates => (x : ClosedState)) h
  let y : zeroMomentumShell :=
    ⟨jointProjection (z : ClosedState), jointProjection_mem_zeroMomentumShell _ z.property⟩
  have hD : jointProjection ghostDilaton = ghostDilaton :=
    ((mem_zeroMomentumShell _).mp ghostDilaton_mem_zeroMomentumShell).2
  have hy : zeroShellDifferential y = shellDilaton := by
    apply Subtype.ext
    change closedQ (jointProjection (z : ClosedState)) = ghostDilaton
    have hc := LinearMap.congr_fun jointProjection_closedQ (z : ClosedState)
    change jointProjection (closedQ (z : ClosedState)) =
      closedQ (jointProjection (z : ClosedState)) at hc
    rw [← hc, hQ, hD]
  have hclosed := LinearMap.congr_fun zeroShellFunctional_closed y
  change zeroShellFunctional (zeroShellDifferential y) = 0 at hclosed
  rw [hy, zeroShellFunctional_dilaton] at hclosed
  norm_num at hclosed

private theorem semirelativeDilaton_closed :
    semirelativeDifferential semirelativeDilaton = 0 := by
  apply Subtype.ext
  change closedQ ghostDilaton = 0
  exact ghostDilaton_closed

private def dilatonCycle : LinearMap.ker semirelativeDifferential :=
  ⟨semirelativeDilaton, LinearMap.mem_ker.mpr semirelativeDilaton_closed⟩

private def cohomologyClass {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ V) (square : d * d = 0) (z : LinearMap.ker d) :
    Cohomology d square :=
  (Boundaries d square).mkQ z

private theorem cohomologyClass_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d : Module.End ℂ V) (square : d * d = 0) (z : LinearMap.ker d)
    (h : ∀ w : V, d w ≠ (z : V)) : cohomologyClass d square z ≠ 0 := by
  intro hz
  rw [cohomologyClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  change ∃ w : V, boundaryMap d square w = z at hz
  obtain ⟨w, hw⟩ := hz
  exact h w (congrArg Subtype.val hw)

/-- The class defined by the same literal cycle in the native quotient. -/
def ghostDilatonClass : SemirelativeCohomology :=
  cohomologyClass semirelativeDifferential semirelativeDifferential_square dilatonCycle

theorem ghostDilatonClass_ne_zero : ghostDilatonClass ≠ 0 :=
  cohomologyClass_ne_zero semirelativeDifferential semirelativeDifferential_square
    dilatonCycle semirelative_nonexact

#print axioms absolute_exact
#print axioms ghostDilaton_closed
#print axioms jointProjection_closedQ
#print axioms jointProjection_bMinus
#print axioms jointProjection_mem_zeroMomentumShell
#print axioms zeroShellFunctional_closed
#print axioms zeroShellFunctional_dilaton
#print axioms semirelative_nonexact
#print axioms ghostDilatonClass_ne_zero

end
end D5.S3.VertexAlgebra.OriginalOrbifoldGhostDilaton
