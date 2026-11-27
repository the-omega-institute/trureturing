/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeSpectrumTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qOrderThreeSpectrumTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal conjugacy transports the cubic twisted module law and spectrum. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedSpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.DiagonalCharacterConjugacy
import D5.S3.FiniteGroups.Cyclic.SL47OrderThreeConjugacy

/-! Precomposition by a conformal source equivalence transports the cubic
twisted field identities on the same module carrier. The fixed-charge phase
rigidity of the P48q representative supplies such an equivalence for each
cube-one monomial lift of that representative. A faithful and exhaustive
integral SL₂(F₄₇) realization extends the result to all order-three isometries. -/

set_option autoImplicit false

open scoped VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeSpectrumTransport

open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeActualConformalState (omega)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeSugawaraConformal (translation)
open NativeStandardThirdLift (standardLift standardLift_compatible standardLift_ground_single)
open P48qAllJetWickField (NativeStates)
open P48qFieldCarrierTransport (InResidueOn TwistedBorcherdsOn)
open P48qTwistedChargeAction (lattice g g_cube g_isometry g_order)
open ThirdTwistedChargeAction (nativeStandardEta nativeStandardEta_fixed)

open private inverse_gram_covariance from
  D5.S3.VertexAlgebra.Lattice.InvariantQuadraticConformalState
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "Ω" => omega lattice (actualInverse lattice)
local notation "C" => HVertexOperator.coeff

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The field identities used to control the actual cubic twisted spectrum. -/
structure CubicTwistedModuleLaw (lift : NativeStates ≃ₗ[ℂ] NativeStates)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) : Prop where
  vacuum : Y (vacuum lattice) =
    (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ))
  residue : ∀ (a : NativeStates) (s : ℤ), lift a = ζ ^ s • a → InResidueOn s (Y a)
  borcherds : ∀ (a b : NativeStates) (s t : ℤ),
    lift a = ζ ^ s • a → lift b = ζ ^ t • b →
    ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice a j b = 0) ∧ TwistedBorcherdsOn Y a b s t N
  translation : ∀ (a : NativeStates) (j : ℤ),
    C (Y (translation lattice a)) j = (((j + 3 : ℤ) : ℂ) / 3) • C (Y a) (j + 3)

/-- The conformal zero mode in the cubic cover coordinate. -/
abbrev conformalZeroMode (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) : Module.End ℂ W :=
  C (Y Ω) (-6)

/-- An equivariant conformal source equivalence pulls back the actual cubic
twisted field law with the same source cutoffs and the same conformal zero mode. -/
theorem CubicTwistedModuleLaw.precomp
    {sourceLift targetLift F : NativeStates ≃ₗ[ℂ] NativeStates}
    {Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W}
    (hY : CubicTwistedModuleLaw targetLift Y)
    (hIntertwine : ∀ a, F (sourceLift a) = targetLift (F a))
    (hMode : ∀ (a b : NativeStates) (n : ℤ), F (mu lattice a n b) = mu lattice (F a) n (F b))
    (hVacuum : F (vacuum lattice) = vacuum lattice)
    (hTranslation : ∀ a, F (translation lattice a) = translation lattice (F a))
    (hOmega : F Ω = Ω) :
    CubicTwistedModuleLaw sourceLift (Y.comp F.toLinearMap) ∧
      conformalZeroMode (Y.comp F.toLinearMap) = conformalZeroMode Y := by
  have eigen (a : NativeStates) (s : ℤ) (ha : sourceLift a = ζ ^ s • a) :
      targetLift (F a) = ζ ^ s • F a := by
    rw [← hIntertwine a, ha, map_smul]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · change Y (F (vacuum lattice)) = _
    exact (congrArg Y hVacuum).trans hY.vacuum
  · intro a s ha
    exact hY.residue (F a) s (eigen a s ha)
  · intro a b s t ha hb
    obtain ⟨N, hCut, hBorcherds⟩ := hY.borcherds (F a) (F b) s t (eigen a s ha) (eigen b t hb)
    refine ⟨N, ?_, ?_⟩
    · intro n hn
      apply F.injective
      rw [hMode a b n, hCut n hn, map_zero]
    · simpa only [TwistedBorcherdsOn, LinearMap.comp_apply, LinearEquiv.coe_coe, hMode]
        using hBorcherds
  · intro a j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hTranslation] using hY.translation (F a) j
  · change C (Y (F Ω)) (-6) = C (Y Ω) (-6)
    rw [hOmega]

/-- Pulling back the fields to the standard action gives the spectral inclusion
and the type-one residue for every occupied weight of the other action. -/
theorem actual_twisted_spectrum_of_intertwiner
    {lift F : NativeStates ≃ₗ[ℂ] NativeStates}
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (hY : CubicTwistedModuleLaw lift Y)
    (hIntertwine : ∀ a, F (σ a) = lift (F a))
    (hMode : ∀ (a b : NativeStates) (n : ℤ), F (mu lattice a n b) = mu lattice (F a) n (F b))
    (hVacuum : F (vacuum lattice) = vacuum lattice)
    (hTranslation : ∀ a, F (translation lattice a) = translation lattice (F a))
    (hOmega : F Ω = Ω)
    (lower : ℝ)
    (hLower : ∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Y v = r • v → lower ≤ r.re)
    (hFinite : ∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode Y) r))
    (r : ℂ) (v : W) (hv : v ≠ 0) (hr : conformalZeroMode Y v = r • v) :
    (∃ n : ℕ, r = 16 / 9 + (n : ℂ) / 3) ∧ (∃ m : ℤ, 9 * r = (m : ℂ) ∧ m % 3 = 1) := by
  obtain ⟨hStandard, hL0⟩ := hY.precomp hIntertwine hMode hVacuum hTranslation hOmega
  have hLower' : ∀ (r : ℂ) (v : W), v ≠ 0 →
      conformalZeroMode (Y.comp F.toLinearMap) v = r • v → lower ≤ r.re := by
    rw [hL0]
    exact hLower
  have hFinite' : ∀ r : ℂ,
      FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode (Y.comp F.toLinearMap)) r) := by
    rw [hL0]
    exact hFinite
  have hr' : conformalZeroMode (Y.comp F.toLinearMap) v = r • v := by
    rw [hL0]
    exact hr
  exact ⟨P48qActualTwistedSpectrum.actual_twisted_spectrum_inclusion
      (Y.comp F.toLinearMap) hStandard.vacuum hStandard.residue hStandard.borcherds
      hStandard.translation lower hLower' hFinite' r v hv hr',
    P48qActualTwistedSpectrum.actual_twisted_type_one_residue
      (Y.comp F.toLinearMap) hStandard.vacuum hStandard.residue hStandard.borcherds
      hStandard.translation lower hLower' hFinite' r v hv hr'⟩

open DiagonalCharacterConjugacy (PreservesModes conjugate_of_fixed_ground diagonal diagonal_modes
  diagonal_omega diagonal_translation diagonal_vacuum ground)

/-- Every cube-one lift of the fixed P48q representative that preserves modes
and has the specified action on charged ground lines has the same spectral
inclusion and type-one residue for its ordinary cubic twisted fields. -/
theorem actual_twisted_spectrum_of_order_three_lift
    (lift : NativeStates ≃ₗ[ℂ] NativeStates) (phase : Charge lattice → ℂˣ)
    (hLift : ∀ a, lift (ground lattice a) = (phase a : ℂ) • ground lattice (g a))
    (hMode : PreservesModes lattice lift) (hCube : lift ^ (3 : ℕ) = 1)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (hY : CubicTwistedModuleLaw lift Y)
    (lower : ℝ)
    (hLower : ∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Y v = r • v → lower ≤ r.re)
    (hFinite : ∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode Y) r))
    (r : ℂ) (v : W) (hv : v ≠ 0) (hr : conformalZeroMode Y v = r • v) :
    (∃ n : ℕ, r = 16 / 9 + (n : ℂ) / 3) ∧ (∃ m : ℤ, 9 * r = (m : ℂ) ∧ m % 3 = 1) := by
  have hFixed (a : Charge lattice) (ha : g a = a) : phase a = nativeStandardEta lattice g a :=
    (P48qOrderThreeLiftRigidity.p48q_order_three_lift_standard lift phase hLift hMode hCube a ha).trans
      (nativeStandardEta_fixed lattice g g_isometry a ha).symm
  obtain ⟨η, hConjugacy⟩ := conjugate_of_fixed_ground lattice g σ lift (nativeStandardEta lattice g)
    phase (fun a b n => (standardLift_compatible lattice g g_cube g_isometry).2.1 a n b) hMode
    (standardLift_ground_single lattice g g_cube g_isometry) hLift hFixed
  have hIntertwine (a : NativeStates) : diagonal lattice η (σ a) = lift (diagonal lattice η a) := by
    simpa only [LinearEquiv.trans_apply] using
      congrArg (fun e : NativeStates ≃ₗ[ℂ] NativeStates => e a) hConjugacy
  exact actual_twisted_spectrum_of_intertwiner Y hY hIntertwine (diagonal_modes lattice η)
    (diagonal_vacuum lattice η) (diagonal_translation lattice η)
    (diagonal_omega lattice η (actualInverse lattice)) lower hLower hFinite r v hv hr

/-- Under a faithful, exhaustive integral realization of the lattice isometry
group by `SL₂(F₄₇)`, every occupied cubic twisted weight for an order-three
isometry with a cube-one monomial lift has the type-one residue and is nonintegral. -/
theorem actual_twisted_spectrum_of_order_three_isometry
    (realization : Additive ExtremalC48.SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hPreserves : ∀ s : Additive ExtremalC48.SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    (h : AddAut (Charge lattice))
    (hIsometry : ∀ a b, bilinear lattice (h a) (h b) = bilinear lattice a b)
    (hOrder : addOrderOf h = 3)
    (lift : NativeStates ≃ₗ[ℂ] NativeStates) (phase : Charge lattice → ℂˣ)
    (hLift : ∀ a, lift (ground lattice a) = (phase a : ℂ) • ground lattice (h a))
    (hMode : PreservesModes lattice lift) (hCube : lift ^ (3 : ℕ) = 1)
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (hY : CubicTwistedModuleLaw lift Y)
    (lower : ℝ)
    (hLower : ∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Y v = r • v → lower ≤ r.re)
    (hFinite : ∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode Y) r))
    (weight : ℂ) (v : W) (hv : v ≠ 0) (hWeight : conformalZeroMode Y v = weight • v) :
    (∃ n : ℕ, weight = 16 / 9 + (n : ℂ) / 3) ∧
      (∃ m : ℤ, 9 * weight = (m : ℂ) ∧ m % 3 = 1) ∧ ∀ z : ℤ, weight ≠ (z : ℂ) := by
  obtain ⟨r, hrIsometry, hrCharge⟩ := ExtremalC48.lattice_orderThree_conjugacy lattice
    realization hFaithful hPreserves hExhaustive g h g_isometry hIsometry g_order hOrder
  let F := IsometryLift.lift lattice r
  let conjugated := F⁻¹ * lift * F
  have hIntertwine (a : NativeStates) : F (conjugated a) = lift (F a) :=
    F.apply_symm_apply _
  have hCompatible := IsometryLift.lift_compatible lattice r hrIsometry
  have hFMode (a b : NativeStates) (n : ℤ) :
      F (mu lattice a n b) = mu lattice (F a) n (F b) :=
    hCompatible.2.2.1 a n b
  have hConjugatedMode : PreservesModes lattice conjugated := by
    intro a b n
    change conjugated (mu lattice a n b) = mu lattice (conjugated a) n (conjugated b)
    apply F.injective
    rw [hIntertwine (mu lattice a n b), hFMode a b n,
      hFMode (conjugated a) (conjugated b) n, hIntertwine a, hIntertwine b]
    exact hMode (F a) (F b) n
  have hConjugatedCube : conjugated ^ (3 : ℕ) = 1 := by
    simpa only [conjugated, inv_inv, hCube, mul_one, inv_mul_cancel] using
      (conj_pow (i := 3) (a := F⁻¹) (b := lift))
  let conjugatedPhase (a : Charge lattice) : ℂˣ :=
    IsometryLift.phase lattice r a * phase (r a) / IsometryLift.phase lattice r (g a)
  have hFGround (a : Charge lattice) :
      F (ground lattice a) = (IsometryLift.phase lattice r a : ℂ) • ground lattice (r a) := by
    simpa only [F, ground, map_one] using IsometryLift.lift_single lattice r a 1
  have hConjugatedGround (a : Charge lattice) :
      conjugated (ground lattice a) = (conjugatedPhase a : ℂ) • ground lattice (g a) := by
    apply F.injective
    simp only [hIntertwine, hFGround, map_smul, hLift, ← hrCharge a, smul_smul,
      conjugatedPhase, Units.val_div_eq_div_val, Units.val_mul,
      div_mul_cancel₀ _ (Units.ne_zero (IsometryLift.phase lattice r (g a)))]
  have hFOmega : F Ω = Ω := by
    change IsometryLift.lift lattice r Ω = Ω
    rw [InvariantQuadraticConformalState.lift_omega,
      inverse_gram_covariance lattice (actualInverse lattice)
        (actualInverse_left lattice gram_det_unit) r hrIsometry]
  obtain ⟨hPullback, hL0⟩ := hY.precomp hIntertwine hFMode hCompatible.1 hCompatible.2.2.2 hFOmega
  obtain ⟨hSpectrum, hResidue⟩ := actual_twisted_spectrum_of_order_three_lift
    conjugated conjugatedPhase hConjugatedGround hConjugatedMode hConjugatedCube
    (Y.comp F.toLinearMap) hPullback lower
    (by simpa only [hL0] using hLower) (by simpa only [hL0] using hFinite)
    weight v hv (by simpa only [hL0] using hWeight)
  refine ⟨hSpectrum, hResidue, ?_⟩
  intro z hz
  obtain ⟨m, hm, hmod⟩ := hResidue
  have hmz : (9 * z : ℤ) = m := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_mul, Int.cast_ofNat, hz] using hm
  rw [← hmz, show (9 : ℤ) * z = 3 * (3 * z) by ring, Int.mul_emod_right] at hmod
  exact zero_ne_one hmod

run_cmd do
  for name in [``CubicTwistedModuleLaw.precomp, ``actual_twisted_spectrum_of_intertwiner,
      ``actual_twisted_spectrum_of_order_three_lift, ``actual_twisted_spectrum_of_order_three_isometry] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeSpectrumTransport
