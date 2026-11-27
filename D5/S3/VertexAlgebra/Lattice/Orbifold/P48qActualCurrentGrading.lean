import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedHeisenberg
import D5.S3.VertexAlgebra.Modules.FullJacobiConformalGrading

/-!
The conformal Ward law for the actual cubic twisted target in the P48q
central-charge 48 orbifold construction. The commutator uses Bakalov–Kac,
*Twisted modules over lattice vertex algebras*, (3.7), arXiv:math/0402315v3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualCurrentGrading

open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (omega currentState current_state_creation)
open LatticeActualConformalWard (omega_product)
open LatticeSugawaraConformal (translation sugawaraMode_minus_one_eq_translation)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates)
open P48qFieldCarrierTransport (InResidueOn stripResidueOn TwistedBorcherdsOn)
open P48qNativeCurrentLocality (currentAlong)
open P48qThirdTwistedField (Cartan)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedHeisenberg (projectAt)
open SignedFieldResidueLocality (residueField)
open D5.S3.VertexAlgebra.Modules
open D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport (current)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private currentCoefficient_projectAt from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
open private projectedCurrent_lift_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualTwistedHeisenberg
open private positiveModes from
  D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "Ω" => omega lattice (actualInverse lattice)
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff
local notation "L[" Y "]" => C (Y Ω) (-6)
local notation "J[" Y ", " k ", " u "]" => C (Y (currentAlong lattice u)) (-k - 3)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem strip_mode (s : ℤ) (A : VertexOperator ℂ W) (i : ℤ) :
    (stripResidueOn s A)[[i]] = C A (s - 3 * (i + 1)) := by
  change C A (3 * (-i - 1) + s) = _
  rw [show 3 * (-i - 1) + s = s - 3 * (i + 1) by omega]

private theorem zero_residue_mode (A B : VertexOperator ℂ W) (q : ℤ) :
    ((residueField 1 0 A B).operator)[[q]] = A[[0]] * B[[q]] - B[[q]] * A[[0]] := by
  apply LinearMap.ext
  intro w
  have h := positiveModes 1 A B 0 q w
  simpa only [Int.natCast_zero, pow_zero, Module.End.one_apply,
    SignedFieldNormalProductLocality.signedComm, one_smul,
    LinearMap.sub_apply, Module.End.mul_apply] using h

set_option maxHeartbeats 2000000 in
-- The concrete rank-48 lattice and inverse Gram matrix require extra elaboration.
/-- The coefficient of the actual conformal field at cover exponent `-6`
satisfies the zero-mode Ward identity at each physical mode `q - s/3`,
assuming the target translation coefficient law. -/
theorem actual_twisted_conformal_ward
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a : NativeStates) (s : ℤ) (N : ℕ)
    (hcut : ∀ j ≥ (N : ℤ), mu lattice Ω j a = 0)
    (hB : TwistedBorcherdsOn Y Ω a 0 s N)
    (htranslate : ∀ j : ℤ, C (Y (translation lattice a)) j =
      (((j + 3 : ℤ) : ℂ) / 3) • C (Y a) (j + 3)) (q : ℤ) :
    let B := C (Y a) (s - 3 * (q + 1))
    L[Y] * B - B * L[Y] =
      C (Y (sugawaraMode lattice (actualInverse lattice) 0 a)) (s - 3 * (q + 1)) -
        ((q : ℂ) - (s : ℂ) / 3 + 1) • B := by
  intro B
  let term (j : ℕ) : Module.End ℂ W :=
    Ring.choose (1 : ℂ) j •
      C (Y (mu lattice Ω (j : ℤ) a)) (s - 3 * (1 + q - (j : ℤ) + 1))
  have h := hB 1 q 0
  simp only [Int.cast_one, Int.cast_zero, zero_div, sub_zero, zero_add,
    Int.toNat_natCast] at h
  change ((residueField 1 0 (stripResidueOn (-3) (Y Ω))
    (stripResidueOn s (Y a))).operator)[[q]] = ∑ j ∈ Finset.range N, term j at h
  have hsum : (∑ j ∈ Finset.range N, term j) = ∑ j ∈ Finset.range 2, term j := by
    calc
      _ = ∑ j ∈ Finset.range (max N 2), term j := by
        apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
        intro j _ hj
        have hjN : (N : ℤ) ≤ j := by
          exact_mod_cast (Nat.le_of_not_gt (fun hlt => hj (Finset.mem_range.mpr hlt)))
        simp only [term, hcut j hjN, map_zero, Pi.zero_apply, smul_zero]
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
        intro j _ hj
        have hj' : 1 < j := by
          rw [Finset.mem_range, not_lt] at hj
          omega
        have hchoose : Ring.choose (1 : ℂ) j = 0 := by
          rw [show (1 : ℂ) = ((1 : ℕ) : ℂ) by simp, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hj', Nat.cast_zero]
        simp only [term, hchoose, zero_smul]
  have htranslation : mu lattice Ω 0 a = translation lattice a := by
    rw [omega_product, show (0 : ℤ) - 1 = -1 by decide,
      sugawaraMode_minus_one_eq_translation lattice (actualInverse lattice)
        (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)]
  have h0 : term 0 = -((q : ℂ) - (s : ℂ) / 3 + 1) • B := by
    have hindex : s - 3 * (1 + q + 1) + 3 = s - 3 * (q + 1) := by omega
    have hscalar : (((s - 3 * (1 + q + 1) + 3 : ℤ) : ℂ) / 3) =
        -((q : ℂ) - (s : ℂ) / 3 + 1) := by
      push_cast
      ring
    simp only [term, Ring.choose_zero_right, one_smul, Nat.cast_zero, sub_zero,
      htranslation]
    rw [htranslate, hscalar, hindex]
  have h1 : term 1 =
      C (Y (sugawaraMode lattice (actualInverse lattice) 0 a)) (s - 3 * (q + 1)) := by
    simp only [term, Ring.choose_one_right, one_smul, Nat.cast_one, omega_product,
      sub_self, show s - 3 * (1 + q - 1 + 1) = s - 3 * (q + 1) by omega]
  rw [zero_residue_mode, hsum] at h
  simp only [strip_mode, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1,
    neg_smul, neg_add_eq_sub] at h
  exact h

private theorem source_current_weight_one (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Fin D.rank → ℂ) :
    sugawaraMode D H 0 (current D u) = current D u := by
  simp only [current, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have h := FullJacobiConformalGrading.source_omega_one_current D H hHG hGH i
  have hi : mu D (omega D H) 1 (currentState D i) = currentState D i := by
    simpa only [Modules.FullJacobiCurrentTransport.sourceProduct,
      Modules.FullJacobiCurrentTransport.currentState, current_state_creation, mu] using h
  rw [omega_product, sub_self] at hi
  rw [hi]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Instantiating the source current lemma unfolds the concrete lattice and inverse Gram matrix.
/-- The signed cover current mode `k` shifts the actual target conformal
weight by `-k/3`. The source lift and target residue support select the
matching component of each Cartan direction. -/
theorem actual_current_mode_ward
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hresidue : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      InResidueOn s (Y (currentAlong lattice u)))
    (hborcherds : ∀ (u : Cartan) (s : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice Ω j (currentAlong lattice u) = 0) ∧
        TwistedBorcherdsOn Y Ω (currentAlong lattice u) 0 s N)
    (htranslate : ∀ (u : Cartan) (j : ℤ),
      C (Y (translation lattice (currentAlong lattice u))) j =
        (((j + 3 : ℤ) : ℂ) / 3) • C (Y (currentAlong lattice u)) (j + 3))
    (u : Cartan) (k : ℤ) :
    L[Y] * J[Y, k, u] - J[Y, k, u] * L[Y] = -((k : ℂ) / 3) • J[Y, k, u] := by
  have hp : J[Y, k, projectAt k u] = J[Y, k, u] :=
    currentCoefficient_projectAt Y hresidue k u
  obtain ⟨N, hcut, hB⟩ := hborcherds _ _ (projectedCurrent_lift_eigen u k)
  have h := actual_twisted_conformal_ward Y (currentAlong lattice (projectAt k u)) (-k) N
    hcut hB (htranslate (projectAt k u)) 0
  dsimp only at h
  have hweight :
      sugawaraMode lattice (actualInverse lattice) 0 (currentAlong lattice (projectAt k u)) =
        currentAlong lattice (projectAt k u) :=
    source_current_weight_one lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      (projectAt k u)
  have hindex : -k - 3 * (0 + 1) = -k - 3 := by omega
  have hscalar : ((0 : ℤ) : ℂ) - ((-k : ℤ) : ℂ) / 3 + 1 = (k : ℂ) / 3 + 1 := by
    push_cast
    ring
  rw [hweight, hindex, hscalar, hp, add_smul, one_smul] at h
  rw [h, neg_smul]
  abel

/-- Every occupied conformal weight has an oscillator ground in the same
one-third-integer coset at a nonnegative integral cover distance below it. -/
theorem exists_current_ground_below
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hward : ∀ (u : Cartan) (k : ℤ),
      L[Y] * J[Y, k, u] - J[Y, k, u] * L[Y] = -((k : ℂ) / 3) • J[Y, k, u])
    (lower : ℝ) (hlower : ∀ (z : ℂ) (v : W),
      v ≠ 0 → L[Y] v = z • v → lower ≤ z.re)
    (z : ℂ) (w : W) (hw : w ≠ 0) (hz : L[Y] w = z • w) :
    ∃ (d : ℕ) (v : W), v ≠ 0 ∧ L[Y] v = (z - (d : ℂ) / 3) • v ∧
      ∀ (u : Cartan) (k : ℤ), 0 < k → J[Y, k, u] v = 0 := by
  classical
  let occupied (d : ℕ) : Prop := ∃ v : W, v ≠ 0 ∧ L[Y] v = (z - (d : ℂ) / 3) • v
  have hzero : occupied 0 := ⟨w, hw, by simpa using hz⟩
  obtain ⟨bound, hbound⟩ := exists_nat_gt (3 * (z.re - lower))
  have hle {d : ℕ} (hd : occupied d) : d ≤ bound := by
    obtain ⟨v, hv, hweight⟩ := hd
    have h := hlower _ v hv hweight
    have hre : (z - (d : ℂ) / 3).re = z.re - (d : ℝ) / 3 := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.natCast_re]
    rw [hre] at h
    exact_mod_cast (show (d : ℝ) ≤ (bound : ℝ) by linarith)
  let d := Nat.findGreatest occupied bound
  have hd : occupied d := by
    by_cases h : d = 0
    · simpa only [h] using hzero
    · exact Nat.findGreatest_of_ne_zero rfl h
  obtain ⟨v, hv, hweight⟩ := hd
  refine ⟨d, v, hv, hweight, ?_⟩
  intro u k hk
  by_contra hnonzero
  have hkcast : (k.toNat : ℂ) = (k : ℂ) := by
    have h : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℂ)) h
  have hshift : L[Y] (J[Y, k, u] v) = (z - ((d + k.toNat : ℕ) : ℂ) / 3) • J[Y, k, u] v := by
    have h := LinearMap.congr_fun (hward u k) v
    change L[Y] (J[Y, k, u] v) - J[Y, k, u] (L[Y] v) =
      -((k : ℂ) / 3) • J[Y, k, u] v at h
    rw [hweight, map_smul] at h
    calc
      _ = -((k : ℂ) / 3) • J[Y, k, u] v + (z - (d : ℂ) / 3) • J[Y, k, u] v :=
        sub_eq_iff_eq_add.mp h
      _ = _ := by
        rw [neg_smul, neg_add_eq_sub, ← sub_smul, sub_sub, Nat.cast_add, hkcast, add_div]
  have hlater : occupied (d + k.toNat) := ⟨_, hnonzero, hshift⟩
  have hmax : d + k.toNat ≤ d := Nat.le_findGreatest (hle hlater) hlater
  omega

run_cmd do
  for name in [``actual_twisted_conformal_ward, ``actual_current_mode_ward,
      ``exists_current_ground_below] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualCurrentGrading
