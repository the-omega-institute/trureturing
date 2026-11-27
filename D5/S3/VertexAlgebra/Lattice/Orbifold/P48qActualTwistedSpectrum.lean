import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundSpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualWeightDescent

/-!
The cubic twisted conformal spectrum of the standard lift on the P48q
lattice vertex algebra. Each occupied conformal weight descends by a
nonnegative multiple of `1 / 3` to an oscillator-ground weight. The
fixed-charge fields and the ground energy formula determine its residue.
-/

set_option autoImplicit false

open scoped VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedSpectrum

open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeActualConformalState (omega)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeSugawaraConformal (translation)
open NativeStandardThirdLift (standardLift standardLift_fixed_ground standardLift_omega)
open P48qActualChargedFieldKernel (oppositeCharge_vacuum_pole)
open P48qAllJetWickField (NativeStates)
open P48qCurrentChargedIterate (chargedGround)
open P48qFieldCarrierTransport (InResidueOn TwistedBorcherdsOn)
open P48qNativeCurrentLocality (currentAlong)
open P48qThirdTwistedField (Cartan chargeVector)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)

open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private action_chargeVector from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private lift_current from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "Ω" => omega lattice (actualInverse lattice)
local notation "C" => HVertexOperator.coeff
local notation "L[" Y "]" => C (Y Ω) (-6)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
  (hVac : Y (vacuum lattice) =
    (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
  (hresidue : ∀ (a : NativeStates) (s : ℤ), σ a = ζ ^ s • a → InResidueOn s (Y a))
  (hborcherds : ∀ (a b : NativeStates) (s t : ℤ),
    σ a = ζ ^ s • a → σ b = ζ ^ t • b →
    ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice a j b = 0) ∧ TwistedBorcherdsOn Y a b s t N)
  (htranslate : ∀ (a : NativeStates) (j : ℤ),
    C (Y (translation lattice a)) j = (((j + 3 : ℤ) : ℂ) / 3) • C (Y a) (j + 3))
  (b : ℝ) (hlower : ∀ (r : ℂ) (v : W), v ≠ 0 → L[Y] v = r • v → b ≤ r.re)
  (hfinite : ∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace L[Y] r))

include hVac hresidue hborcherds htranslate hlower hfinite

/-- Every occupied weight of a lower-bounded cubic twisted module with finite
conformal eigenspaces belongs to `16 / 9 + ℕ / 3`. -/
theorem actual_twisted_spectrum_inclusion (r : ℂ) (v : W) (hv : v ≠ 0)
    (hr : L[Y] v = r • v) : ∃ n : ℕ, r = 16 / 9 + (n : ℂ) / 3 := by
  have hΩ : σ Ω = ζ ^ (0 : ℤ) • Ω := by
    simpa only [zpow_zero, one_smul] using
      standardLift_omega lattice g g_cube g_isometry (actualInverse lattice)
        (actualInverse_left lattice gram_det_unit)
  have hcurrents (u v : Cartan) (s t : ℤ) :=
    hborcherds (currentAlong lattice u) (currentAlong lattice v) s t
  obtain ⟨d, w, x, hw, hweight, hpositive, hzero⟩ :=
    P48qActualWeightDescent.actual_weight_descent Y hVac
      (fun u s => hresidue (currentAlong lattice u) s) hcurrents
      (fun u s => hborcherds Ω (currentAlong lattice u) 0 s hΩ)
      (fun u => htranslate (currentAlong lattice u)) b hlower hfinite r v hv hr
  have hVacZero : C (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W) := by
    rw [hVac]
    apply LinearMap.ext
    intro w
    change (HahnSeries.single (0 : ℤ) w).coeff 0 = w
    simp only [HahnSeries.coeff_single, if_pos rfl]
  have hfixed (a : Charge lattice) (ha : g a = a) : σ (chargedGround a) = ζ ^ (0 : ℤ) •
      chargedGround a := by
    simpa only [zpow_zero, one_smul] using standardLift_fixed_ground lattice g g_cube g_isometry a ha
  have hopposite (a : Charge lattice) (ha : g a = a) : ∃ N : ℕ,
      bilinear lattice a a ≤ (N : ℤ) ∧
      TwistedBorcherdsOn Y (chargedGround (-a)) (chargedGround a) 0 0 N := by
    have hneg : g (-a) = -a := by rw [map_neg, ha]
    obtain ⟨N, hcut, hB⟩ := hborcherds (chargedGround (-a)) (chargedGround a) 0 0
      (hfixed (-a) hneg) (hfixed a ha)
    refine ⟨N, ?_, hB⟩
    by_contra hN
    obtain ⟨hpole, _, hepsilon⟩ := oppositeCharge_vacuum_pole a
    have hvanish := hcut (bilinear lattice a a - 1) (by omega)
    rw [hpole] at hvanish
    exact (LatticePositiveEnergy.vacuum_nonzero lattice) ((smul_eq_zero.mp hvanish).resolve_left hepsilon)
  have hcurrent (a : Charge lattice) (ha : g a = a) : ∃ N : ℕ,
      TwistedBorcherdsOn Y (currentAlong lattice (chargeVector a)) (chargedGround a) 0 0 N := by
    have hfix : σ (currentAlong lattice (chargeVector a)) =
        ζ ^ (0 : ℤ) • currentAlong lattice (chargeVector a) := by
      rw [lift_current, action_chargeVector, ha, zpow_zero, one_smul]
    obtain ⟨N, _, hB⟩ := hborcherds _ _ 0 0 hfix (hfixed a ha)
    exact ⟨N, hB⟩
  obtain ⟨n, hn⟩ := P48qActualGroundSpectrum.actual_ground_energy_congruent Y hVacZero
    hcurrents (fun a ha => hresidue a 0 (by simpa only [zpow_zero, one_smul] using ha))
    hopposite hcurrent (fun a => htranslate (chargedGround a))
    w hw (fun u k => hpositive k u) x (by simpa only [neg_zero, zero_sub] using hzero)
  have heq : r - (d : ℂ) / 3 = 16 / 9 + (n : ℂ) / 3 :=
    smul_left_injective ℂ hw (hweight.symm.trans hn)
  refine ⟨n + d, ?_⟩
  calc
    r = (r - (d : ℂ) / 3) + (d : ℂ) / 3 := by ring
    _ = 16 / 9 + ((n + d : ℕ) : ℂ) / 3 := by rw [heq, Nat.cast_add]; ring

/-- Nine times any occupied conformal weight is an integer of residue one
modulo three. This applies in particular to an occupied lowest weight. -/
theorem actual_twisted_type_one_residue (r : ℂ) (v : W) (hv : v ≠ 0)
    (hr : L[Y] v = r • v) : ∃ m : ℤ, 9 * r = (m : ℂ) ∧ m % 3 = 1 := by
  obtain ⟨n, hn⟩ := actual_twisted_spectrum_inclusion
    Y hVac hresidue hborcherds htranslate b hlower hfinite r v hv hr
  refine ⟨16 + 3 * (n : ℤ), ?_, ?_⟩
  · rw [hn]
    push_cast
    ring
  · exact (Int.add_mul_emod_self_left 16 3 (n : ℤ)).trans (by decide)

/-- A lower-bounded cubic twisted module with finite conformal eigenspaces
has no conformal eigenvalue in the image of `ℤ` in `ℂ`. -/
theorem actual_twisted_no_integral_eigenvalue (z : ℤ) :
    ¬ ∃ v : W, v ≠ 0 ∧ L[Y] v = (z : ℂ) • v := by
  rintro ⟨v, hv, hz⟩
  obtain ⟨m, hm, hres⟩ := actual_twisted_type_one_residue
    Y hVac hresidue hborcherds htranslate b hlower hfinite (z : ℂ) v hv hz
  have hreal : (9 : ℝ) * (z : ℝ) = (m : ℝ) := by
    simpa [Complex.mul_re] using congrArg Complex.re hm
  have hint : (9 : ℤ) * z = m := by exact_mod_cast hreal
  rw [← hint, show (9 : ℤ) * z = 3 * (3 * z) by ring, Int.mul_emod_right] at hres
  exact zero_ne_one hres

run_cmd do
  for name in [``actual_twisted_spectrum_inclusion, ``actual_twisted_type_one_residue,
      ``actual_twisted_no_integral_eigenvalue] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedSpectrum
