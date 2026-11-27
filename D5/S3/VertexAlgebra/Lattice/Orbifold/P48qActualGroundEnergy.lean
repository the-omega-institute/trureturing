import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

/-!
The oscillator-ground conformal coefficient in the actual cubic twisted field.
The current-pair calculation is the product-index `-1` specialization of
Bakalov–Kac, *Twisted modules over lattice vertex algebras*, (3.13),
arXiv:math/0402315v3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundEnergy

open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open P48qFieldCarrierTransport (stripResidueOn TwistedBorcherdsOn)
open P48qAllJetWickField (NativeStates)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (Cartan)
open P48qNativeCurrentLocality (currentAlong)
open NativeStandardThirdLift (standardLift)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (omega)
open HalfFockSpectralFiberSource (actualInverse)
open P48qConformalVectorDecomposition (currentPair currentPair_comm omega_decomposition)
open P48qMomentumEnergy (Fixed fixedBasis fixedGramDual fixedGram)
open P48qMovingCurrentZero (firstDirection secondDirection pair_directions)
open ThirdEigenspacePairing (p48qForm p48qAction p48qBasis p48qOppositeBasis)

open private native_current_product choose_two from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private lift_current currentStateLinear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private zetaPrimitive from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private zeta_zpow_add_three_mul from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum
open private mem_fixed_iff gram_contraction from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C[" Y ", " k ", " u "]" =>
  HVertexOperator.coeff (Y (currentAlong lattice u)) (-k - 3)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem strip_ncoeff (s : ℤ) (A : VertexOperator ℂ W) (n : ℤ) :
    (stripResidueOn s A)[[n]] = HVertexOperator.coeff A (3 * (-n - 1) + s) := rfl

private theorem strip_current (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (u : Cartan) (s n : ℤ) :
    (stripResidueOn s (Y (currentAlong lattice u)))[[n]] =
      C[Y, 3 * n - s, u] := by
  rw [strip_ncoeff, show 3 * (-n - 1) + s = -(3 * n - s) - 3 by omega]

set_option maxHeartbeats 1000000 in
-- Residue evaluation elaborates two vectorwise finite sums.
/-- Evaluation of the two signed residues on a vector killed by positive
current modes. For complementary moving residues both sums vanish, while
for fixed currents the reverse residue retains its two zero modes. -/
private theorem ground_residue
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (w : W)
    (hpositive : ∀ (u : Cartan) (k : ℤ), 0 < k → C[Y, k, u] w = 0)
    (u v : Cartan) (s : ℤ) (hs : -1 ≤ s) (hs' : s ≤ 0) :
    (((residueField 1 (-1) (stripResidueOn s (Y (currentAlong lattice u)))
      (stripResidueOn (-s) (Y (currentAlong lattice v)))).operator)[[1]]) w =
      if s = 0 then C[Y, 0, v] (C[Y, 0, u] w) else 0 := by
  rw [(residueField 1 (-1) _ _).coefficient]
  have hl (j : ℕ) :
      ((stripResidueOn (-s) (Y (currentAlong lattice v)))[[1 + (j : ℤ)]]) w = 0 := by
    rw [strip_current]
    exact hpositive v _ (by omega)
  have hr (j : ℕ) (hj : j ≠ 0) :
      ((stripResidueOn s (Y (currentAlong lattice u)))[[(j : ℤ)]]) w = 0 := by
    rw [strip_current]
    exact hpositive u _ (by omega)
  have hsign : epsilon (-1) * (1 : ℂ) = -1 := by norm_num [epsilon]
  have hbin : (((-1 : ℂ) ^ (0 : ℕ)) * integerBinomial (-1) 0) = 1 := by
    simp [integerBinomial]
  simp only [residueCoefficient, residueLeft, hl, map_zero, smul_zero, finsum_zero,
    residueRight]
  rw [finsum_eq_single _ 0]
  · simp only [hbin, one_smul, hsign, neg_smul, zero_sub, neg_neg, Nat.cast_zero,
      show (-1 : ℤ) + 1 - 0 = 0 by decide]
    rw [strip_current, strip_current]
    by_cases h : s = 0
    · subst s
      simp
    · have hz : C[Y, 3 * 0 - s, u] w = 0 := hpositive u _ (by omega)
      rw [hz, map_zero, ite_eq_right h]
  · intro j hj
    rw [hr j hj, map_zero, smul_zero]

set_option maxHeartbeats 1000000 in
-- Reducing the source product inside the target coefficient requires extra elaboration.
/-- The product-index `-1` Borcherds sum at the ground coefficient contains
only the quadratic state and the Gram multiple of the vacuum. The supplied
cutoff can be any valid source cutoff. -/
private theorem ground_borcherds
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (w : W)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (u v : Cartan) (s : ℤ) (N : ℕ)
    (hcut : ∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n
      (currentAlong lattice v) = 0)
    (hB : TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s (-s) N) :
    (((residueField 1 (-1) (stripResidueOn s (Y (currentAlong lattice u)))
      (stripResidueOn (-s) (Y (currentAlong lattice v)))).operator)[[1]]) w =
      HVertexOperator.coeff (Y (currentPair u v)) (-6) w +
        (Ring.choose (-(s : ℂ) / 3) 2 * p48qForm u v) • w := by
  let term (j : ℕ) : W :=
    Ring.choose (-(s : ℂ) / 3) j •
      HVertexOperator.coeff (Y (mu lattice (currentAlong lattice u) ((j : ℤ) - 1)
        (currentAlong lattice v))) (-6 + 3 * (j : ℤ)) w
  have hsum :
      (((residueField 1 (-1) (stripResidueOn s (Y (currentAlong lattice u)))
        (stripResidueOn (-s) (Y (currentAlong lattice v)))).operator)[[1]]) w =
        ∑ j ∈ Finset.range (N + 1), term j := by
    have h := congrArg (fun f : Module.End ℂ W => f w) (hB 0 1 (-1))
    rw [show s - 3 * (0 : ℤ) = s by omega] at h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Int.cast_zero, zero_sub,
      zero_add, add_neg_cancel] at h
    rw [h]
    have hlen : ((N : ℤ) - (-1)).toNat = N + 1 := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    rw [show -(s : ℂ) / 3 = -( (s : ℂ) / 3) by ring,
      show (-1 : ℤ) + (j : ℤ) = (j : ℤ) - 1 by omega,
      show -(3 * (1 - (j : ℤ) + 1)) = -6 + 3 * (j : ℤ) by omega]
  have hzLarge (j : ℕ) (hj : 3 ≤ j) : term j = 0 := by
    have hne : (j : ℤ) - 1 ≠ 1 := by omega
    simp only [term, native_current_product u v ((j : ℤ) - 1) (by omega), ite_eq_right hne,
      map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have hzCut (j : ℕ) (hj : N + 1 ≤ j) : term j = 0 := by
    simp only [term, hcut _ (by omega : (N : ℤ) ≤ (j : ℤ) - 1),
      map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have hrange : (∑ j ∈ Finset.range (N + 1), term j) =
      ∑ j ∈ Finset.range 3, term j := by
    calc
      _ = ∑ j ∈ Finset.range (max (N + 1) 3), term j := by
        apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
        intro j _ hj
        exact hzCut j (by simpa only [Finset.mem_range, not_lt] using hj)
      _ = _ := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
        intro j _ hj
        exact hzLarge j (by simpa only [Finset.mem_range, not_lt] using hj)
  have h0 : term 0 = HVertexOperator.coeff (Y (currentPair u v)) (-6) w := by
    simp [term, currentPair]
  have h1 : term 1 = 0 := by
    simp [term, native_current_product u v 0 (by decide : (0 : ℤ) ≤ 0)]
  have h2 : term 2 = (Ring.choose (-(s : ℂ) / 3) 2 * p48qForm u v) • w := by
    simp only [term, Nat.cast_ofNat, show (2 : ℤ) - 1 = 1 by decide,
      native_current_product u v 1 (by decide), ite_true, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      show (-6 : ℤ) + 3 * 2 = 0 by decide, hVac, Module.End.one_apply, smul_smul]
  rw [hsum, hrange]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1, h2,
    add_zero]

private theorem lift_eigen (u : Cartan) (s : ℤ) (hu : p48qAction u = ζ ^ s • u) :
    σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u := by
  rw [lift_current u, hu]
  exact currentStateLinear.map_smul _ _

private theorem fixed_lift (u : Fixed) :
    σ (currentAlong lattice u) = ζ ^ (0 : ℤ) • currentAlong lattice u :=
  lift_eigen u 0 (by simpa only [zpow_zero, one_smul] using (mem_fixed_iff u).mp u.property)

private theorem first_lift (i : Fin 16) :
    σ (currentAlong lattice (firstDirection i)) =
      ζ ^ (-1 : ℤ) • currentAlong lattice (firstDirection i) := by
  apply lift_eigen
  rw [← zeta_zpow_add_three_mul (-1) 1, show (-1 : ℤ) + 3 * 1 = 2 by decide,
    show ζ ^ (2 : ℤ) = ζ ^ (2 : ℕ) from zpow_natCast ζ 2]
  exact Module.End.mem_eigenspace_iff.mp (p48qOppositeBasis zetaPrimitive i).property

private theorem second_lift (i : Fin 16) :
    σ (currentAlong lattice (secondDirection i)) =
      ζ ^ (1 : ℤ) • currentAlong lattice (secondDirection i) := by
  apply lift_eigen
  rw [zpow_one]
  exact Module.End.mem_eigenspace_iff.mp (p48qBasis zetaPrimitive i).property

set_option maxHeartbeats 1000000 in
-- The coefficient comparison expands the source conformal vector.
/-- The actual conformal zero mode on any oscillator ground is the
half-weighted fixed-current Casimir plus the sixteen complementary moving
pair contributions, each of size `1/9`. -/
theorem actual_ground_conformal_zero
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n
        (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (w : W) (hpositive : ∀ (u : Cartan) (k : ℤ), 0 < k → C[Y, k, u] w = 0) :
    HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) w =
      (2 : ℂ)⁻¹ • (∑ i : Fin 16,
        C[Y, 0, fixedGramDual fixedBasis i] (C[Y, 0, fixedBasis i] w)) +
      (16 / 9 : ℂ) • w := by
  have hfixed (i : Fin 16) :
      HVertexOperator.coeff (Y (currentPair (fixedBasis i) (fixedGramDual fixedBasis i))) (-6) w =
        C[Y, 0, fixedGramDual fixedBasis i] (C[Y, 0, fixedBasis i] w) := by
    obtain ⟨N, hcut, hB⟩ := hborcherds _ _ 0 0 (fixed_lift _) (fixed_lift _)
    have hr := ground_residue Y w hpositive (fixedBasis i) (fixedGramDual fixedBasis i)
      0 (by decide) (by decide)
    have hb := ground_borcherds Y w hVac (fixedBasis i) (fixedGramDual fixedBasis i)
      0 N hcut hB
    rw [hr] at hb
    simpa [choose_two] using hb.symm
  have hmoving (i : Fin 16) :
      HVertexOperator.coeff (Y (currentPair (firstDirection i) (secondDirection i))) (-6) w =
        (1 / 9 : ℂ) • w := by
    obtain ⟨N, hcut, hB⟩ := hborcherds _ _ (-1) 1 (first_lift i) (second_lift i)
    have hr := ground_residue Y w hpositive (firstDirection i) (secondDirection i)
      (-1) (by decide) (by decide)
    have hb := ground_borcherds Y w hVac (firstDirection i) (secondDirection i)
      (-1) N hcut hB
    rw [hr, ite_eq_right (by decide : (-1 : ℤ) ≠ 0)] at hb
    have hscalar :
        Ring.choose (-((-1 : ℤ) : ℂ) / 3) 2 *
          p48qForm (firstDirection i) (secondDirection i) = -(1 / 9 : ℂ) := by
      rw [pair_directions, ite_eq_left rfl, mul_one, choose_two]
      norm_num
    rw [hscalar, neg_smul] at hb
    exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hb.symm)
  have horder :
      (∑ i : Fin 16, currentPair (p48qBasis zetaPrimitive i) (p48qOppositeBasis zetaPrimitive i)) =
        ∑ i : Fin 16, currentPair (firstDirection i) (secondDirection i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact currentPair_comm _ _
  rw [omega_decomposition zetaPrimitive, horder]
  simp only [map_add, map_smul, map_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, hfixed, hmoving,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  norm_num

set_option maxHeartbeats 1000000 in
-- Contracting the fixed Gram-dual basis requires elaborating the source fields.
/-- A ground vector with fixed-current character given by the Gram pairing
with a fixed momentum has the corresponding quadratic ground energy. -/
theorem actual_ground_conformal_eigenvalue
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (hborcherds : ∀ (u v : Cartan) (s t : ℤ),
      σ (currentAlong lattice u) = ζ ^ s • currentAlong lattice u →
      σ (currentAlong lattice v) = ζ ^ t • currentAlong lattice v →
      ∃ N : ℕ, (∀ n ≥ (N : ℤ), mu lattice (currentAlong lattice u) n
        (currentAlong lattice v) = 0) ∧
        TwistedBorcherdsOn Y (currentAlong lattice u) (currentAlong lattice v) s t N)
    (w : W) (hpositive : ∀ (u : Cartan) (k : ℤ), 0 < k → C[Y, k, u] w = 0)
    (x : Fixed) (hzero : ∀ u : Fixed, C[Y, 0, u] w = fixedGram u x • w) :
    HVertexOperator.coeff (Y (omega lattice (actualInverse lattice))) (-6) w =
      ((2 : ℂ)⁻¹ * fixedGram x x + 16 / 9) • w := by
  rw [actual_ground_conformal_zero Y hVac hborcherds w hpositive]
  have hpair (i : Fin 16) :
      C[Y, 0, fixedGramDual fixedBasis i] (C[Y, 0, fixedBasis i] w) =
        (fixedGram (fixedGramDual fixedBasis i) x * fixedGram (fixedBasis i) x) • w := by
    rw [hzero (fixedBasis i), map_smul, hzero (fixedGramDual fixedBasis i), smul_smul,
      mul_comm]
  simp only [hpair, ← Finset.sum_smul, gram_contraction, smul_smul, ← add_smul]

run_cmd do
  for name in [``ground_residue, ``ground_borcherds, ``actual_ground_conformal_zero,
      ``actual_ground_conformal_eigenvalue] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualGroundEnergy
