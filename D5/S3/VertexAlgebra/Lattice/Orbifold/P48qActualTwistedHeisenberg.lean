import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

/-!
The cubic twisted Borcherds identity at product index zero gives the
level-one Heisenberg relations for the actual target current coefficients.
-/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedHeisenberg

open SignedFieldResidueLocality (residueField)
open P48qFieldCarrierTransport (InResidueOn stripResidueOn TwistedBorcherdsOn)
open P48qAllJetWickField (NativeStates)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (Cartan Mode creator annihilatorDual fixedDualBases
  annihilatorDual_action pair_modes)
open P48qMomentumEnergy (Fixed)
open P48qNativeCurrentLocality (currentAlong)
open NativeStandardThirdLift (standardLift)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open ThirdEigenspacePairing (p48qForm)
open P48qTwistedHeisenberg (projectAt projectAt_eq_fourier project_of_action scale)
open P48qTwistedGeneratorVacuum (projectAt_action)

open private native_current_product from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private positiveModes from
  D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
open private currentCoefficient_projectAt from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
open private lift_current currentStateLinear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private zeta_zpow_add_three_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum
open private pairing_project root root_cube scale_pos opposite_cover_iff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

attribute [local instance] LieRing.ofAssociativeRing

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C[" Y ", " k ", " u "]" =>
  HVertexOperator.coeff (Y (currentAlong lattice u)) (-k - 3)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem stripResidueOn_ncoeff (s : ℤ) (A : VertexOperator ℂ W) (n : ℤ) :
    (stripResidueOn s A)[[n]] = HVertexOperator.coeff A (3 * (-n - 1) + s) := rfl

private theorem vacuum_coeff (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (m : ℤ) :
    HVertexOperator.coeff (Y (vacuum lattice)) m =
      if m = 0 then (1 : Module.End ℂ W) else 0 := by
  rw [hVac]
  apply LinearMap.ext
  intro w
  change (HahnSeries.single (0 : ℤ) w).coeff m = _
  rw [HahnSeries.coeff_single]
  split_ifs <;> rfl

/-- On residue-aligned cover modes, the zero-product cubic identity retains
only the Gram multiple of the vacuum from the first source product. -/
private theorem current_commutator_aligned
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (u v : Cartan) (s t k l : ℤ) (N : ℕ)
    (hcut : ∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n (currentAlong lattice v) = 0)
    (hB : TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (hk : (-k - 3) % 3 = s % 3) (hl : (-l - 3) % 3 = t % 3) :
    ⁅C[Y, k, u], C[Y, l, v]⁆ =
      if k + l = 0 then ((k : ℂ) / 3 * p48qForm u v) • (1 : Module.End ℂ W) else 0 := by
  let p := (s + k) / 3
  let q := (t + l) / 3
  have hp : 3 * p = s + k := by dsimp [p]; omega
  have hq : 3 * q = t + l := by dsimp [q]; omega
  have hfirst : 3 * (-(0 : ℤ) - 1) + (s - 3 * p) = -k - 3 := by omega
  have hsecond : 3 * (-q - 1) + t = -l - 3 := by omega
  have hcomm :
      ((residueField 1 0 (stripResidueOn (s - 3 * p) (Y (currentAlong lattice u)))
        (stripResidueOn t (Y (currentAlong lattice v)))).operator)[[q]] =
        ⁅C[Y, k, u], C[Y, l, v]⁆ := by
    apply LinearMap.ext
    intro w
    simpa only [Int.natCast_zero, pow_zero, Module.End.one_apply,
      SignedFieldNormalProductLocality.signedComm, one_smul, stripResidueOn_ncoeff,
      hfirst, hsecond, Ring.lie_def] using
      positiveModes 1 (stripResidueOn (s - 3 * p) (Y (currentAlong lattice u)))
        (stripResidueOn t (Y (currentAlong lattice v))) 0 q w
  let term (j : ℕ) := Ring.choose ((p : ℂ) - (s : ℂ) / 3) j •
    HVertexOperator.coeff (Y (mu lattice (currentAlong lattice u) (j : ℤ)
      (currentAlong lattice v))) (s + t - 3 * (p + q - (j : ℤ) + 1))
  have hsum : ⁅C[Y, k, u], C[Y, l, v]⁆ = ∑ j ∈ Finset.range N, term j := by
    rw [← hcomm]
    simpa only [zero_add, sub_zero, Int.toNat_natCast, term] using hB p q 0
  have hsingle : (∑ j ∈ Finset.range N, term j) = term 1 := by
    apply Finset.sum_eq_single 1
    · intro j _ hj
      have hj' : (j : ℤ) ≠ 1 := by omega
      simp only [term, native_current_product u v (j : ℤ) (Int.natCast_nonneg j),
        ite_eq_right hj', map_zero, Pi.zero_apply, smul_zero]
    · intro h
      have hN : N ≤ 1 := by
        have hn : ¬1 < N := fun hn => h (Finset.mem_range.mpr hn)
        omega
      have hz := hcut 1 (by omega : (N : ℤ) ≤ 1)
      simp only [term, Nat.cast_one, hz, map_zero, Pi.zero_apply, smul_zero]
  have hfreq : (p : ℂ) - (s : ℂ) / 3 = (k : ℂ) / 3 := by
    have h := congrArg (fun a : ℤ => (a : ℂ)) hp
    push_cast at h
    linear_combination (1 / 3 : ℂ) * h
  have hdegree : s + t - 3 * (p + q - 1 + 1) = 0 ↔ k + l = 0 := by omega
  rw [hsum, hsingle]
  simp only [term, Nat.cast_one, Ring.choose_one_right, hfreq,
    native_current_product u v 1 (by decide), ite_true, map_smul, Pi.smul_apply,
    vacuum_coeff Y hVac, hdegree]
  split_ifs <;> simp only [smul_smul, smul_zero]

/-- The bracket at cover indices `k,l` for a pair of lift eigen-currents.
Off-residue coefficients vanish. The central term is at physical frequency `k/3`. -/
theorem eigenCurrent_commutator
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (u v : Cartan) (s t k l : ℤ)
    (hresidue : ∀ (w : Cartan) (r : ℤ),
      σ (currentAlong lattice w) = ζ ^ r • currentAlong lattice w →
      InResidueOn r (Y (currentAlong lattice w)))
    (hborcherds : σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (hu : σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u)
    (hv : σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v) :
    ⁅C[Y, k, u], C[Y, l, v]⁆ =
      if (-k - 3) % 3 = s % 3 ∧ (-l - 3) % 3 = t % 3 ∧ k + l = 0
      then ((k : ℂ) / 3 * p48qForm u v) • (1 : Module.End ℂ W) else 0 := by
  by_cases hk : (-k - 3) % 3 = s % 3
  · by_cases hl : (-l - 3) % 3 = t % 3
    · obtain ⟨N, hcut, hB⟩ := hborcherds hu hv
      simpa only [hk, hl, true_and] using
        current_commutator_aligned Y hVac u v s t k l N hcut hB hk hl
    · rw [hresidue v t hv (-l - 3) hl]
      simp only [hl, false_and, and_false, ite_false, lie_zero]
  · rw [hresidue u s hu (-k - 3) hk]
    simp only [hk, false_and, ite_false, zero_lie]

private theorem projectedCurrent_lift_eigen (u : Cartan) (k : ℤ) :
    σ (currentAlong lattice (projectAt k u)) = ζ ^ (-k) • currentAlong lattice (projectAt k u) := by
  rw [lift_current, projectAt_action]
  exact currentStateLinear.map_smul _ _

private theorem pairing_projectAt_opposite (u v : Cartan) (k : ℤ) :
    p48qForm (projectAt k u) (projectAt (-k) v) = p48qForm (projectAt k u) v := by
  have hcast : (((-k % 3).toNat : ℕ) : ℤ) = (-k) % 3 := by omega
  have hroot : ζ ^ ((-k % 3).toNat) = ζ ^ (-k) := by
    rw [← zpow_natCast, hcast,
      ← zeta_zpow_add_three_mul ((-k) % 3) ((-k) / 3), Int.emod_add_mul_ediv]
  rw [formSymmetric.eq (projectAt k u), projectAt_eq_fourier (-k) v, hroot,
    pairing_project _ _ _ (projectAt_action u k), formSymmetric.eq v]

/-- Residue support extends the commutator to every Cartan pair by Fourier projection. -/
theorem current_commutator
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (hresidue : ∀ (w : Cartan) (r : ℤ),
      σ (currentAlong lattice w) = ζ ^ r • currentAlong lattice w →
      InResidueOn r (Y (currentAlong lattice w)))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (u v : Cartan) (k l : ℤ) :
    ⁅C[Y, k, u], C[Y, l, v]⁆ =
      if k + l = 0 then ((k : ℂ) / 3 * p48qForm (projectAt k u) v) • (1 : Module.End ℂ W)
      else 0 := by
  have hu : C[Y, k, projectAt k u] = C[Y, k, u] := currentCoefficient_projectAt Y hresidue k u
  have hv : C[Y, l, projectAt l v] = C[Y, l, v] := currentCoefficient_projectAt Y hresidue l v
  rw [← hu, ← hv]
  have h := eigenCurrent_commutator Y hVac (projectAt k u) (projectAt l v) (-k) (-l) k l
    hresidue (hborcherds _ _ _ _)
    (projectedCurrent_lift_eigen u k) (projectedCurrent_lift_eigen v l)
  simp only [show (-k - 3) % 3 = (-k) % 3 by omega,
    show (-l - 3) % 3 = (-l) % 3 by omega, true_and] at h
  rw [h]
  by_cases hkl : k + l = 0
  · simp only [hkl, ite_true]
    rw [show l = -k by omega, pairing_projectAt_opposite]
  · simp only [hkl, ite_false]

/-- The actual creation, annihilation, and fixed-zero coefficients give the
three current-only commutation hypotheses of Fock recognition. -/
theorem current_fock_relations
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : Y (vacuum lattice) =
      (show VertexOperator ℂ W from HahnSeries.single.linearMap (R := ℂ) (V := W) (0 : ℤ)))
    (hresidue : ∀ (w : Cartan) (r : ℤ),
      σ (currentAlong lattice w) = ζ ^ r • currentAlong lattice w →
      InResidueOn r (Y (currentAlong lattice w)))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N) :
    let A (i : Mode) := C[Y, Int.negSucc i.2, creator fixedDualBases i]
    let B (i : Mode) := C[Y, Int.ofNat (i.2 + 1), annihilatorDual fixedDualBases i]
    let Z (u : Fixed) := C[Y, 0, (u : Cartan)]
    (∀ i j, Commute (A i) (A j)) ∧
      (∀ i j, ⁅B i, A j⁆ = if i = j then scale i.2 • 1 else 0) ∧
      ∀ u i, Commute (Z u) (A i) := by
  dsimp only
  have hcomm := current_commutator Y hVac hresidue hborcherds
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply commute_iff_lie_eq.mpr
    rw [hcomm, ite_eq_right (show Int.negSucc i.2 + Int.negSucc j.2 ≠ 0 by omega)]
  · rintro ⟨a, n⟩ ⟨b, m⟩
    rw [hcomm, scale_pos]
    by_cases hnm : n = m
    · subst m
      rw [ite_eq_left ((opposite_cover_iff n n).mpr rfl)]
      have hproject :
          projectAt (Int.ofNat (n + 1)) (annihilatorDual fixedDualBases (a, n)) =
            annihilatorDual fixedDualBases (a, n) :=
        project_of_action (root n) (root_cube n) _
          (annihilatorDual_action fixedDualBases (a, n))
      rw [hproject, formSymmetric.eq (annihilatorDual fixedDualBases (a, n)), pair_modes]
      simp only [Prod.mk.injEq, and_true, eq_comm (a := b) (b := a)]
      split_ifs <;> simp only [mul_one, mul_zero, zero_smul]
    · rw [ite_eq_right (mt (opposite_cover_iff n m).mp hnm)]
      simp only [Prod.mk.injEq, hnm, and_false, ite_false]
  · intro u i
    apply commute_iff_lie_eq.mpr
    rw [hcomm]
    split_ifs <;> simp

run_cmd do
  for name in [``eigenCurrent_commutator, ``current_commutator, ``current_fock_relations] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedHeisenberg
