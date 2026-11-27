import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundEnergy
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualFixedWeight
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdNormWeightCongruence

/-! The actual oscillator-ground energy follows from the projected integral
fixed lattice and the cubic twisted module identities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

open scoped BigOperators Matrix VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundSpectrum

open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeActualVertexAlgebra (actualVertexAlgebra)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeGeneratingFieldLocality (Charge bilinear)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates)
open P48qCurrentChargedIterate (chargedGround)
open P48qFieldCarrierTransport (InResidueOn TwistedBorcherdsOn)
open P48qFixedRankCertificate (nebeOrderThree rowAction)
open P48qMomentumEnergy (Fixed fixedGram fixedGram_symm fixedGram_nondegenerate physicalMomentum)
open P48qNativeCurrentLocality (currentAlong)
open P48qThirdTwistedField (Cartan chargeVector)
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum norm_row g_apply)
open ThirdEigenspacePairing (p48qAction p48qForm)

open private mem_fixed_iff half_momentum_square from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
open private action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private currentCoefficient from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem represent_joint_character
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (w : W) (hw : w ≠ 0)
    (hzero : ∀ u : Fixed, ∃ c : ℂ, C (Y (currentAlong lattice u)) (-3) w = c • w) :
    ∃ x : Fixed, ∀ u : Fixed, C (Y (currentAlong lattice u)) (-3) w = fixedGram u x • w := by
  classical
  choose c hc using hzero
  let T : Fixed →ₗ[ℂ] W := (LinearMap.applyₗ (R := ℂ) w).comp
    ((currentCoefficient Y 0).comp Fixed.subtype)
  have hT (u : Fixed) : T u = c u • w := hc u
  let χ : Module.Dual ℂ Fixed :=
    { toFun := c
      map_add' := fun u v => smul_left_injective ℂ hw (by
        change c (u + v) • w = (c u + c v) • w
        rw [← hT, add_smul, ← hT, ← hT, map_add])
      map_smul' := fun a u => smul_left_injective ℂ hw (by
        change c (a • u) • w = (a * c u) • w
        rw [← hT, ← smul_smul, ← hT, map_smul]) }
  let e := fixedGram.toDual fixedGram_nondegenerate
  refine ⟨e.symm χ, fun u => ?_⟩
  have h : fixedGram (e.symm χ) u = c u :=
    LinearMap.BilinForm.apply_toDual_symm_apply χ u
  rw [fixedGram_symm.eq u (e.symm χ), h]
  exact hc u

variable
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : C (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n
        (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (hresidue : ∀ v : NativeStates, σ v = v → InResidueOn 0 (Y v))
    (hopposite : ∀ a : Charge lattice, g a = a → ∃ N : ℕ,
      bilinear lattice a a ≤ (N : ℤ) ∧
        TwistedBorcherdsOn Y (chargedGround (-a)) (chargedGround a) 0 0 N)
    (hcurrent : ∀ a : Charge lattice, g a = a → ∃ M : ℕ,
      TwistedBorcherdsOn Y (currentAlong lattice (chargeVector a)) (chargedGround a) 0 0 M)
    (htranslate : ∀ (a : Charge lattice) (j : ℤ),
      C (Y ((actualVertexAlgebra lattice).translation (chargedGround a))) j =
        (((j + 3 : ℤ) : ℂ) / 3) • C (Y (chargedGround a)) (j + 3))
    (w : W) (hw : w ≠ 0)
    (hpositive : ∀ (u : Cartan) (k : ℤ), 0 < k →
      C (Y (currentAlong lattice u)) (-k - 3) w = 0)

include hVac hborcherds hresidue hopposite hcurrent htranslate hw hpositive

set_option maxHeartbeats 1000000 in
-- The proof compares the native field, lattice coordinates and fixed Gram form.
/-- The fixed Cartan character of a nonzero oscillator-ground vector determines
an actual conformal energy in `16 / 9 + ℕ / 3`. -/
theorem actual_ground_energy_congruent (x : Fixed)
    (hx : ∀ u : Fixed, C (Y (currentAlong lattice u)) (-3) w = fixedGram u x • w) :
    ∃ n : ℕ, C (Y (omega lattice (actualInverse lattice))) (-6) w =
      (16 / 9 + (n : ℂ) / 3) • w := by
  have hxFixed : rowAction ℂ nebeOrderThree x.val = x.val := by
    change p48qAction x.val = x.val
    exact (mem_fixed_iff x.val).mp x.property
  have hIntegral (y : Fin 48 → ℤ) (hy : y ᵥ* nebeOrderThree = y) :
      ∃ m : ℤ, p48qForm (Int.castRingHom ℂ ∘ y) x.val = (m : ℂ) := by
    let a : Charge lattice := y
    have ha : g a = a := (g_apply a).trans hy
    let u : Fixed := ⟨chargeVector a, (mem_fixed_iff _).mpr (by rw [action_chargeVector, ha])⟩
    obtain ⟨N, hN, hOpp⟩ := hopposite a ha
    obtain ⟨M, hCurrent⟩ := hcurrent a ha
    have hpos (n : ℤ) (hn : 0 < n) :
        C (Y (currentAlong lattice (chargeVector a))) (3 * (-n - 1)) w = 0 := by
      rw [show 3 * (-n - 1) = -(3 * n) - 3 by omega]
      exact hpositive u (3 * n) (by omega)
    change ∃ m : ℤ, fixedGram u x = (m : ℂ)
    exact P48qActualFixedWeight.fixed_weight_integral Y a ha hresidue N M hN hOpp hCurrent
      hVac (htranslate a) w hw (fixedGram u x) hpos (hx u)
  obtain ⟨a, ha⟩ :=
    (P48qProjectedDual.fixed_dual_iff_projected_charge x.val).mp ⟨hxFixed, hIntegral⟩
  let p : Momentum := ⟨ThirdTwistedChargeAction.N lattice g a, ⟨a, rfl⟩⟩
  have hMomentum : x = physicalMomentum p := by
    apply Subtype.ext
    change x.val = (3 : ℂ)⁻¹ • P48qMomentumEnergy.chargeVector
      (ThirdTwistedChargeAction.N lattice g a)
    rw [norm_row]
    exact ha
  subst x
  have hEnergy := P48qActualGroundEnergy.actual_ground_conformal_eigenvalue Y hVac
    hborcherds w hpositive (physicalMomentum p) hx
  obtain ⟨k, hk⟩ := ThirdNormWeightCongruence.six_dvd_norm_quadratic
    lattice g g_cube g_isometry p
  have hnonneg := P48qTwistedStateEnergy.momentumWeight_nonneg p
  rw [P48qTwistedStateEnergy.momentumWeight, hk] at hnonneg
  have hkReal : (0 : ℝ) ≤ (k : ℝ) := by
    push_cast at hnonneg
    linarith only [hnonneg]
  have hkNonneg : 0 ≤ k := by exact_mod_cast hkReal
  have hScalar : (2 : ℂ)⁻¹ * fixedGram (physicalMomentum p) (physicalMomentum p) + 16 / 9 =
      16 / 9 + (k.toNat : ℂ) / 3 := by
    rw [half_momentum_square, hk, ← Int.cast_natCast, Int.toNat_of_nonneg hkNonneg]
    push_cast
    ring
  exact ⟨k.toNat, hEnergy.trans (congrArg (fun c : ℂ => c • w) hScalar)⟩

/-- Every nonzero oscillator-ground simultaneous eigenvector of the fixed
Cartan zero modes has actual conformal energy `16 / 9 + n / 3` for some `n : ℕ`. -/
theorem actual_ground_energy_congruent_of_joint_eigenvector
    (hzero : ∀ u : Fixed, ∃ c : ℂ, C (Y (currentAlong lattice u)) (-3) w = c • w) :
    ∃ n : ℕ, C (Y (omega lattice (actualInverse lattice))) (-6) w =
      (16 / 9 + (n : ℂ) / 3) • w := by
  obtain ⟨x, hx⟩ := represent_joint_character Y w hw hzero
  exact actual_ground_energy_congruent Y hVac hborcherds hresidue hopposite hcurrent
    htranslate w hw hpositive x hx

run_cmd do
  for name in [``actual_ground_energy_congruent,
      ``actual_ground_energy_congruent_of_joint_eigenvector] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundSpectrum
