import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualChargedFieldKernel

/-!
Fixed Cartan weights on a ground vector of an actual cubic twisted target.
The leading coefficient argument follows Bakalov–Kac, arXiv:math/0402315v3,
Lemma 4.1 and (4.31)–(4.32).
-/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualFixedWeight

open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualVertexAlgebra (actualVertexAlgebra)
open LatticeSugawaraConformal (translation translation_single chargePolynomial)
open NativeStandardThirdLift (standardLift standardLift_fixed_ground)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qThirdTwistedField (chargeVector)
open P48qAllJetWickField (NativeStates)
open P48qCurrentChargedIterate (chargedGround chargedFirst currentAlong source_product_minus_one)
open P48qActualChargedFieldKernel (chargedGround_jointKernel_eq_zero)
open P48qFieldCarrierTransport (InResidueOn stripResidueOn TwistedBorcherdsOn)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (epsilon integerBinomial)

open private currentPolynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "current" a => currentAlong lattice (chargeVector a)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem source_product_eq_translation (a : Charge lattice) :
    mu lattice (current a) (-1) (chargedGround a) =
      (actualVertexAlgebra lattice).translation (chargedGround a) := by
  rw [source_product_minus_one]
  change chargedFirst a (chargeVector a) = translation lattice (chargedGround a)
  simp only [chargedFirst, chargedGround, translation_single, Derivation.map_one_eq_zero,
    zero_add, mul_one, currentPolynomial, chargePolynomial, chargeVector]

private theorem strip_zero_mode (A : VertexOperator ℂ W) (n : ℤ) :
    (stripResidueOn 0 A)[[n]] = HVertexOperator.coeff A (3 * (-n - 1)) := by
  change HVertexOperator.coeff A (3 * (-n - 1) + 0) = _
  rw [add_zero]

private theorem minus_one_residue_at_leading
    (A B : VertexOperator ℂ W) (m : ℤ) (w : W)
    (hbelow : ∀ j < 3 * m, HVertexOperator.coeff B j w = 0)
    (hpositive : ∀ n : ℤ, 0 < n → HVertexOperator.coeff A (3 * (-n - 1)) w = 0) :
    (((residueField 1 (-1) (stripResidueOn 0 A) (stripResidueOn 0 B)).operator)[[-m]]) w =
      HVertexOperator.coeff B (3 * m) (HVertexOperator.coeff A (-3) w) := by
  -- The left summand at offset j reads the charged exponent 3m - 3(j + 1).
  have hleft (j : ℕ) : ((stripResidueOn 0 B)[[-m + (j : ℤ)]]) w = 0 := by
    rw [strip_zero_mode]
    exact hbelow _ (by omega)
  have hright (j : ℕ) (hj : j ≠ 0) : ((stripResidueOn 0 A)[[(j : ℤ)]]) w = 0 := by
    rw [strip_zero_mode]
    exact hpositive _ (by omega)
  rw [(residueField 1 (-1) _ _).coefficient, residueCoefficient]
  simp only [residueLeft, hleft, map_zero, smul_zero, finsum_zero, residueRight]
  rw [finsum_eq_single _ 0]
  · have hB : 3 * (-(-1 + -m - ((0 : ℕ) : ℤ)) - 1) = 3 * m := by omega
    have hA : 3 * (-((0 : ℕ) : ℤ) - 1) = -3 := by decide
    simp only [strip_zero_mode, hA, hB, integerBinomial, Ring.choose_zero_right,
      Int.cast_one, pow_zero, one_mul, one_smul, epsilon]
    norm_num
  · intro j hj
    rw [hright j hj, map_zero, smul_zero]

/-- The zero mode along a fixed lattice charge has integral eigenvalue on a
nonzero vector killed by the positive integral modes of that current. -/
theorem fixed_weight_integral
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a : Charge lattice) (ha : g a = a)
    (hresidue : ∀ v : NativeStates, σ v = v → InResidueOn 0 (Y v))
    (N M : ℕ) (hN : bilinear lattice a a ≤ (N : ℤ))
    (hopposite : TwistedBorcherdsOn Y (chargedGround (-a)) (chargedGround a) 0 0 N)
    (hcurrent : TwistedBorcherdsOn Y (current a) (chargedGround a) 0 0 M)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (htranslate : ∀ j : ℤ,
      HVertexOperator.coeff (Y ((actualVertexAlgebra lattice).translation (chargedGround a))) j =
        (((j + 3 : ℤ) : ℂ) / 3) • HVertexOperator.coeff (Y (chargedGround a)) (j + 3))
    (w : W) (hw : w ≠ 0) (weight : ℂ)
    (hpositive : ∀ n : ℤ, 0 < n →
      HVertexOperator.coeff (Y (current a)) (3 * (-n - 1)) w = 0)
    (hzero : HVertexOperator.coeff (Y (current a)) (-3) w = weight • w) :
    ∃ n : ℤ, weight = (n : ℂ) := by
  let B := Y (chargedGround a)
  obtain ⟨j, hj⟩ : ∃ j : ℤ, HVertexOperator.coeff B j w ≠ 0 := by
    by_contra! hall
    exact hw (chargedGround_jointKernel_eq_zero Y a N hN hopposite hVac w hall)
  let k := ((HahnModule.of ℂ).symm (B w)).order
  have hk : HVertexOperator.coeff B k w ≠ 0 := by
    intro hz
    have hseries : (HahnModule.of ℂ).symm (B w) = 0 := HahnSeries.coeff_order_eq_zero.mp hz
    apply hj
    change ((HahnModule.of ℂ).symm (B w)).coeff j = 0
    rw [hseries, HahnSeries.coeff_zero]
  have hRes : InResidueOn 0 B :=
    hresidue _ (standardLift_fixed_ground lattice g g_cube g_isometry a ha)
  have hmod : k % 3 = 0 := by
    by_contra hn
    exact hk (by rw [hRes k (by simpa using hn), LinearMap.zero_apply])
  let m := k / 3
  have hkm : 3 * m = k := by dsimp [m]; omega
  have hbelow (j : ℤ) (hj : j < 3 * m) : HVertexOperator.coeff B j w = 0 := by
    apply VertexOperator.coeff_eq_zero_of_lt_order
    change j < k
    rwa [← hkm]
  let term (j : ℕ) : Module.End ℂ W :=
    Ring.choose (0 : ℂ) j •
      HVertexOperator.coeff (Y (mu lattice (current a) (-1 + (j : ℤ)) (chargedGround a)))
        (0 + 0 - 3 * (0 + -m - (j : ℤ) + 1))
  have hsum : (∑ j ∈ Finset.range ((M : ℤ) - (-1)).toNat, term j) = term 0 := by
    apply Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))
    intro j _ hj
    simp only [term, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), zero_smul]
  have hiter := hcurrent 0 (-m) (-1)
  change ((residueField 1 (-1) (stripResidueOn (0 - 3 * 0) (Y (current a)))
    (stripResidueOn 0 B)).operator)[[-m]] = _ at hiter
  simp only [sub_zero, Int.cast_zero, zero_div] at hiter
  change _ = ∑ j ∈ Finset.range ((M : ℤ) - (-1)).toNat, term j at hiter
  rw [hsum] at hiter
  have hindex : 0 + 0 - 3 * (0 + -m - ((0 : ℕ) : ℤ) + 1) = 3 * m - 3 := by omega
  have hscale : (((3 * m : ℤ) : ℂ) / 3) = (m : ℂ) := by
    push_cast
    ring
  have hterm : term 0 = (m : ℂ) • HVertexOperator.coeff B (3 * m) := by
    dsimp only [term]
    rw [hindex]
    simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, add_zero,
      source_product_eq_translation, htranslate, sub_add_cancel, hscale, B]
  rw [hterm] at hiter
  have heq := congrArg (fun T : Module.End ℂ W => T w) hiter
  change (((residueField 1 (-1) (stripResidueOn 0 (Y (current a)))
    (stripResidueOn 0 B)).operator)[[-m]]) w =
      (((m : ℂ) • HVertexOperator.coeff B (3 * m)) w) at heq
  rw [minus_one_residue_at_leading _ _ m w hbelow hpositive, hzero, map_smul,
    LinearMap.smul_apply] at heq
  exact ⟨m, smul_left_injective ℂ (by simpa only [hkm] using hk) heq⟩

run_cmd do
  let axioms ← Lean.collectAxioms ``fixed_weight_integral
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for fixed_weight_integral: {axioms}"
  Lean.logInfo m!"fixed_weight_integral depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualFixedWeight
