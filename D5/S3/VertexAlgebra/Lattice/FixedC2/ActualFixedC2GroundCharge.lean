/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2GroundCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed ground charge descent in the intrinsic fixed lattice C₂ quotient. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
import D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite
import D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce

/-!
The fixed ground-orbit charge step uses the actual lattice mode expansion.
The first oscillator step uses neutral quadratic zero modes and translation,
following the approved charge-reduction derivation and the rank-one
calculations of Yamskulna, arXiv:math/0202056, §4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeInvolution LatticeFiniteNegativeGeneration LatticeActualProductKernel
open LatticeSugawaraCurrents LatticeActualConformalState LatticePositiveEnergy
open LatticeSugawaraConformal LatticeActualVertexAlgebra MvPolynomial
open ActualLeechHyperbolic (leechData leech_spec)
open StateFieldResidueReconstruction (integerBinomial)
open scoped VertexOperator

open private E ground creation_zero creation_negative orbit_coefficient mu_add_right
  Gi Gi_neg neutral_ground charge_contract chargePolynomial_neg
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private higher_fixed_product_mem fixed_commutator fixedCommutatorTerm
  from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
open private norm_sub bilinear_sub_right bilinear_unit
  from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

noncomputable section

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The actual paired creation coefficient on the charge orbit of `c`. -/
def fixedCreationOrbit (D : LatticeData) (a c : Charge D) (k : ℤ) : FixedCarrier D :=
  ⟨Finsupp.single c (creationCoeff D a k) +
    Finsupp.single (-c) (creationCoeff D (-a) k), by
    rw [mem_fixedSpace, map_add]
    change thetaLinear D (Finsupp.single c (creationCoeff D a k)) +
      thetaLinear D (Finsupp.single (-c) (creationCoeff D (-a) k)) = _
    simp only [theta_single, sigma_creationCoeff, neg_neg, add_comm]⟩

/-- The actual invariant ground state `e^c + e^(-c)`. -/
def fixedGroundOrbit (D : LatticeData) (c : Charge D) : FixedCarrier D :=
  fixedCreationOrbit D c c 0

private theorem fixedGroundOrbit_val (D : LatticeData) (c : Charge D) :
    (fixedGroundOrbit D c).val = E D c := by
  simp only [fixedGroundOrbit, fixedCreationOrbit, creation_zero, E, ground]

@[simp] theorem fixed_creation_orbit_zero (D : LatticeData) (a c : Charge D) :
    fixedCreationOrbit D a c 0 = fixedGroundOrbit D c := by
  apply Subtype.ext
  simp only [fixedCreationOrbit, fixedGroundOrbit, creation_zero]

theorem fixed_creation_orbit_reverse (D : LatticeData) (a c : Charge D) (k : ℤ) :
    fixedCreationOrbit D a c k = fixedCreationOrbit D (-a) (-c) k := by
  apply Subtype.ext
  simp only [fixedCreationOrbit, neg_neg, add_comm]

theorem fixed_ground_mode_two_orbits (D : LatticeData) (a b : Charge D) (n : ℤ) :
    fixedMode D (fixedGroundOrbit D a) n (fixedGroundOrbit D b) =
      epsilon D a b •
        (fixedCreationOrbit D a (a + b) (-n - 1 - bilinear D a b) +
          fixedCreationOrbit D a (a - b) (-n - 1 + bilinear D a b)) := by
  apply Subtype.ext
  change mu D (fixedGroundOrbit D a).val n (fixedGroundOrbit D b).val = _
  rw [fixedGroundOrbit_val, fixedGroundOrbit_val]
  exact orbit_coefficient D a b n

private theorem fixed_mode_mem_of_le_neg_two (D : LatticeData) (u v : FixedCarrier D)
    (n : ℤ) (hn : n ≤ -2) : fixedMode D u n v ∈ fixedC2 D := by
  let r := (-n - 2).toNat
  have hr : -((r : ℤ) + 2) = n := by dsimp [r]; omega
  rw [← hr]
  exact higher_fixed_product_mem D r u v

private theorem epsilon_ne_zero (D : LatticeData) (a b : Charge D) :
    epsilon D a b ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> norm_num

/-- At mode `-s-1` the upper orbit contributes its ground state and the lower
orbit contributes its actual level-`2s` creation coefficient. -/
theorem fixed_ground_two_orbit_relation (D : LatticeData) (a b : Charge D)
    (hs : 0 < bilinear D a b) :
    (fixedC2 D).mkQ (fixedGroundOrbit D (a + b)) =
      -(fixedC2 D).mkQ (fixedCreationOrbit D a (a - b) (2 * bilinear D a b)) := by
  let s := bilinear D a b
  have hm := fixed_mode_mem_of_le_neg_two D (fixedGroundOrbit D a) (fixedGroundOrbit D b)
    (-s - 1) (by omega)
  rw [fixed_ground_mode_two_orbits, show -(-s - 1) - 1 - s = 0 by omega,
    show -(-s - 1) - 1 + s = 2 * s by omega, fixed_creation_orbit_zero] at hm
  have h := (fixedC2 D).smul_mem (epsilon D a b)⁻¹ hm
  rw [smul_smul, inv_mul_cancel₀ (epsilon_ne_zero D a b), one_smul] at h
  have hq := (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr h
  change (fixedC2 D).mkQ (_ + _) = 0 at hq
  rw [map_add] at hq
  exact eq_neg_of_add_eq_zero_left hq

/-- The lower-orbit coefficients before the first upper-orbit ground term vanish
in the intrinsic quotient. -/
theorem fixed_lower_creation_class_eq_zero (D : LatticeData) (a b : Charge D)
    (k : ℤ) (hlo : bilinear D a b + 1 ≤ k) (hhi : k < 2 * bilinear D a b) :
    (fixedC2 D).mkQ (fixedCreationOrbit D a (a - b) k) = 0 := by
  let s := bilinear D a b
  let n := s - k - 1
  have hm := fixed_mode_mem_of_le_neg_two D (fixedGroundOrbit D a) (fixedGroundOrbit D b)
    n (by dsimp [n, s]; omega)
  have hnegative : -n - 1 - s < 0 := by dsimp [n, s]; omega
  have hz : fixedCreationOrbit D a (a + b) (-n - 1 - s) = 0 := by
    apply Subtype.ext
    simp only [fixedCreationOrbit, creation_negative D _ _ hnegative, Finsupp.single_zero,
      add_zero, Submodule.coe_zero]
  rw [fixed_ground_mode_two_orbits, hz, zero_add, show -n - 1 + s = k by dsimp [n]; omega] at hm
  have h := (fixedC2 D).smul_mem (epsilon D a b)⁻¹ hm
  rw [smul_smul, inv_mul_cancel₀ (epsilon_ne_zero D a b), one_smul] at h
  exact (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr h

theorem ground_orbit_norm_difference (D : LatticeData) (a b : Charge D) :
    bilinear D (a + b) (a + b) - bilinear D (a - b) (a - b) = 4 * bilinear D a b := by
  have hp := norm_sub D a (-b)
  rw [sub_neg_eq_add, bilinear_neg_left, bilinear_neg_neg, bilinear_symmetric D b a] at hp
  rw [hp, norm_sub, bilinear_symmetric D b a]
  ring

theorem ground_orbit_norm_decrease (D : LatticeData) (a b : Charge D)
    (hs : 0 < bilinear D a b) :
    bilinear D (a - b) (a - b) < bilinear D (a + b) (a + b) := by
  have h := ground_orbit_norm_difference D a b
  omega

/-- With representative `γ - 2 • a`, the polynomial at that representative
is the coefficient for `-a`. Its opposite carries the coefficient for `a`. -/
theorem fixed_ground_charge_step (D : LatticeData) (a γ : Charge D)
    (hs : 0 < bilinear D a γ - bilinear D a a) :
    let s := bilinear D a γ - bilinear D a a
    let δ := γ - (2 : ℤ) • a
    (fixedC2 D).mkQ (fixedGroundOrbit D γ) =
      -(fixedC2 D).mkQ (fixedCreationOrbit D (-a) δ (2 * s)) ∧
    bilinear D γ γ - bilinear D δ δ = 4 * s ∧
    bilinear D δ δ < bilinear D γ γ := by
  dsimp only
  have hp : bilinear D a (γ - a) = bilinear D a γ - bilinear D a a :=
    bilinear_sub_right D a γ a
  have hs' : 0 < bilinear D a (γ - a) := hp ▸ hs
  have hplus : a + (γ - a) = γ := by abel
  have hminus : -(a - (γ - a)) = γ - (2 : ℤ) • a := by abel
  have hrel := fixed_ground_two_orbit_relation D a (γ - a) hs'
  rw [fixed_creation_orbit_reverse D a (a - (γ - a)), hplus, hminus, hp] at hrel
  have hnorm := ground_orbit_norm_difference D a (γ - a)
  rw [hplus, ← bilinear_neg_neg D (a - (γ - a)) (a - (γ - a)), hminus, hp] at hnorm
  exact ⟨hrel, hnorm, by omega⟩

/-- Every charge outside the Gram-coordinate box has a signed basis step with
the exact creation coefficient and a strict decrease of the nonnegative energy. -/
theorem fixed_ground_charge_step_outside_short (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (γ : Charge D)
    (hγ : γ ∉ ActualC2Cofinite.shortCharges D) :
    ∃ (i : Fin D.rank) (a : Charge D),
      (a = unitCharge D i ∨ a = -unitCharge D i) ∧
      let s := |bilinear D (unitCharge D i) γ| - D.G i i
      let δ := γ - (2 : ℤ) • a
      0 < s ∧
      (fixedC2 D).mkQ (fixedGroundOrbit D γ) =
        -(fixedC2 D).mkQ (fixedCreationOrbit D (-a) δ (2 * s)) ∧
      chargeEnergy D γ - chargeEnergy D δ = 2 * s ∧
      (chargeEnergy D δ).toNat < (chargeEnergy D γ).toNat := by
  classical
  simp only [ActualC2Cofinite.shortCharges, Set.mem_ofPred_eq, not_forall,
    not_le] at hγ
  obtain ⟨i, hi⟩ := hγ
  let e := unitCharge D i
  have he : bilinear D e e = D.G i i := by
    simp [e, bilinear_unit, unitCharge]
  obtain ⟨a, ha, hpair, hself⟩ : ∃ a : Charge D, (a = e ∨ a = -e) ∧
      bilinear D a γ = |bilinear D e γ| ∧ bilinear D a a = D.G i i := by
    by_cases hn : 0 ≤ bilinear D e γ
    · exact ⟨e, Or.inl rfl, (abs_of_nonneg hn).symm, he⟩
    · refine ⟨-e, Or.inr rfl, ?_, ?_⟩
      · rw [bilinear_neg_left, abs_of_neg (lt_of_not_ge hn)]
      · rw [bilinear_neg_neg, he]
  have hs : 0 < bilinear D a γ - bilinear D a a := by
    rw [hpair, hself]
    exact sub_pos.mpr hi
  obtain ⟨hrel, hnorm, _⟩ := fixed_ground_charge_step D a γ hs
  rw [hpair, hself] at hrel hnorm
  dsimp only [e] at hrel hnorm
  have hγen := two_chargeEnergy D γ
  have hδen := two_chargeEnergy D (γ - (2 : ℤ) • a)
  have hnonneg := chargeEnergy_nonneg D hD (γ - (2 : ℤ) • a)
  exact ⟨i, a, ha, sub_pos.mpr hi, hrel, by omega, by omega⟩

/-- A fixed index-one oscillator on the odd combination of charged grounds. -/
def fixedFirstOscillator (D : LatticeData) (i : Fin D.rank) (c : Charge D) :
    FixedCarrier D :=
  ⟨Finsupp.single c (X (i, 0)) - Finsupp.single (-c) (X (i, 0)), by
    rw [mem_fixedSpace, map_sub]
    change thetaLinear D (Finsupp.single c (X (i, 0))) -
      thetaLinear D (Finsupp.single (-c) (X (i, 0))) = _
    simp only [theta_single, sigma_X, neg_neg, Finsupp.single_neg, neg_sub_neg]⟩

private theorem neutral_create_on_ground (D : LatticeData) (i : Fin D.rank)
    (c : Charge D) :
    neutralMode D i (-1) (ground D c) = Finsupp.single c (X (i, 0)) := by
  rw [ground, neutralMode_single]
  congr 1
  simpa using LinearMap.congr_fun (neutralPolynomialMode_negative D i c 0)
    (1 : Oscillator D)

private theorem quadratic_on_ground_zero (D : LatticeData) (i j : Fin D.rank)
    (c : Charge D) :
    ((quadraticSummand D i j)[[0]]) (ground D c) =
      Gi D j c • Finsupp.single c (X (i, 0)) +
      Gi D i c • Finsupp.single c (X (j, 0)) := by
  classical
  have hm := quadraticSummand_coefficient D i j (-1) (ground D c)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num] at hm
  rw [hm]
  have hbound (a : Fin D.rank) (n : ℤ) (hn : (0 : ℤ) < n) :
      neutralMode D a n (ground D c) = 0 := by
    rw [neutral_ground D a c n hn.le, ite_eq_right (ne_of_gt hn)]
  rw [finsum_eq_sum_of_support_subset _
    (s := ({-1, 0} : Finset ℤ))]
  · rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    simp only [normalSummand, show (-1 : ℤ) < 0 by norm_num, lt_irrefl, ite_true, ite_false,
      Module.End.mul_apply, sub_self, sub_zero, neutral_ground D _ _ 0 le_rfl,
      map_smul, neutral_create_on_ground]
  · intro k hk
    have h := normalSummand_support_of_bound D i j (-1) (ground D c) 0 hbound hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    change min 0 ((-1 : ℤ) - (0 : ℤ)) ≤ k ∧ k ≤ 0 at h
    omega

private theorem ground_pairing (D : LatticeData) (i : Fin D.rank) (c : Charge D) :
    (bilinear D (unitCharge D i) c : ℂ) = Gi D i c := by
  simp only [bilinear_unit, Int.cast_sum, Int.cast_mul, Gi]

/-- The actual zero mode of the neutral quadratic has two single-oscillator
terms, with the zero mode on each charged ground evaluated in its own charge. -/
theorem fixed_quadratic_zero_on_ground (D : LatticeData) (i j : Fin D.rank)
    (c : Charge D) :
    fixedMode D (neutralPair D i j 0 0) 0
        (fixedGroundOrbit D c) =
      (bilinear D (unitCharge D j) c : ℂ) • fixedFirstOscillator D i c +
        (bilinear D (unitCharge D i) c : ℂ) • fixedFirstOscillator D j c := by
  simp only [ground_pairing]
  apply Subtype.ext
  change mu D (neutralPair D i j 0 0).val 0
    (fixedGroundOrbit D c).val = _
  rw [fixedGroundOrbit_val, E, mu_add_right]
  have field : Y D (neutralPair D i j 0 0).val =
      quadraticSummand D i j := by
    exact quadratic_state_field D i j
  simp only [mu, field, quadratic_on_ground_zero, Gi_neg, neg_smul, fixedFirstOscillator,
    Submodule.coe_add, Submodule.coe_smul_of_tower, smul_sub]
  abel

/-- Zero modes of fixed states preserve intrinsic C₂ by the actual commutator. -/
theorem fixed_zero_mode_mem_c2 (D : LatticeData) (u z : FixedCarrier D)
    (hz : z ∈ fixedC2 D) : fixedMode D u 0 z ∈ fixedC2 D := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, w, rfl⟩ := hz
    have h := fixed_commutator D u v w 0 (-2)
    have hchoose : integerBinomial 0 0 = 1 := by simp [integerBinomial]
    rw [finsum_eq_single _ 0] at h
    · simp only [fixedCommutatorTerm, hchoose, one_smul, Nat.cast_zero,
        zero_add, sub_zero] at h
      have h₁ : fixedMode D (fixedMode D u 0 v) (-2) w ∈ fixedC2 D :=
        Submodule.subset_span ⟨fixedMode D u 0 v, w, rfl⟩
      have h₂ : fixedMode D v (-2) (fixedMode D u 0 w) ∈ fixedC2 D :=
        Submodule.subset_span ⟨v, fixedMode D u 0 w, rfl⟩
      rw [← h] at h₁
      simpa only [sub_add_cancel] using (fixedC2 D).add_mem h₁ h₂
    · intro j hj
      simp [fixedCommutatorTerm, integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj)]
  | zero => simp
  | add z w _ _ hz hw => simpa only [map_add] using (fixedC2 D).add_mem hz hw
  | smul t z _ hz => simpa only [map_smul] using (fixedC2 D).smul_mem t hz

/-- Translation of the ground orbit is the charge-direction first oscillator. -/
theorem fixed_ground_translation (D : LatticeData) (c : Charge D) :
    fixedTranslation D (fixedGroundOrbit D c) =
      ∑ j : Fin D.rank, (c j : ℂ) • fixedFirstOscillator D j c := by
  apply Subtype.ext
  change translation D (fixedGroundOrbit D c).val = _
  rw [fixedGroundOrbit_val]
  simp only [E, ground, map_add, translation_single, Derivation.map_one_eq_zero, zero_add,
    mul_one, chargePolynomial_neg, Finsupp.single_neg]
  change _ = (fixedSpace D).subtype (∑ j : Fin D.rank, (c j : ℂ) • fixedFirstOscillator D j c)
  simp only [map_sum, map_smul, Submodule.subtype_apply, fixedFirstOscillator,
    chargePolynomial, Finsupp.single_finsetSum, sub_eq_add_neg]
  simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finsupp.smul_single]

private theorem fixed_ground_translation_class_zero (D : LatticeData) (c : Charge D) :
    (fixedC2 D).mkQ (fixedTranslation D (fixedGroundOrbit D c)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr
  refine Submodule.subset_span ⟨fixedGroundOrbit D c, fixedVacuum D, ?_⟩
  apply Subtype.ext
  exact translation_as_mode D (fixedGroundOrbit D c).val

/-- The weighted neutral zero modes isolate the first oscillator modulo intrinsic C₂. -/
theorem fixed_first_oscillator_class (D : LatticeData) (i : Fin D.rank) (c : Charge D) :
    (∑ j : Fin D.rank, (c j : ℂ) • (fixedC2 D).mkQ
      (fixedMode D (neutralPair D i j 0 0) 0 (fixedGroundOrbit D c))) =
      (bilinear D c c : ℂ) • (fixedC2 D).mkQ (fixedFirstOscillator D i c) := by
  simp_rw [fixed_quadratic_zero_on_ground, ground_pairing, map_add, map_smul,
    smul_add, Finset.sum_add_distrib]
  have hT := fixed_ground_translation_class_zero D c
  rw [fixed_ground_translation, map_sum] at hT
  simp only [map_smul] at hT
  have hleft : (∑ j : Fin D.rank, (c j : ℂ) • Gi D j c •
      (fixedC2 D).mkQ (fixedFirstOscillator D i c)) =
        (bilinear D c c : ℂ) • (fixedC2 D).mkQ (fixedFirstOscillator D i c) := by
    simp_rw [smul_smul, ← Finset.sum_smul, charge_contract]
  have hright : (∑ j : Fin D.rank, (c j : ℂ) • Gi D i c •
      (fixedC2 D).mkQ (fixedFirstOscillator D j c)) = 0 := by
    simp_rw [smul_comm (c _ : ℂ) (Gi D i c), ← Finset.smul_sum, hT, smul_zero]
  rw [hleft, hright, add_zero]

/-- The index-one descendant in the larger orbit reduces to actual neutral
quadratic zero modes on the smaller-orbit signed creation coefficient. -/
theorem fixed_first_oscillator_two_orbit_relation (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (i : Fin D.rank)
    (a b : Charge D) (hs : 0 < bilinear D a b) :
    let c := a + b
    let x := fixedCreationOrbit D a (a - b) (2 * bilinear D a b)
    (fixedC2 D).mkQ (fixedFirstOscillator D i c) =
      -((bilinear D c c : ℂ)⁻¹ • ∑ j : Fin D.rank, (c j : ℂ) •
        (fixedC2 D).mkQ (fixedMode D (neutralPair D i j 0 0) 0 x)) := by
  dsimp only
  let c := a + b
  let x := fixedCreationOrbit D a (a - b) (2 * bilinear D a b)
  have hnorm := ground_orbit_norm_decrease D a b hs
  have hlo : 0 ≤ bilinear D (a - b) (a - b) := by
    have h := chargeEnergy_nonneg D hD (a - b)
    rw [← two_chargeEnergy]
    omega
  have hB : (bilinear D c c : ℂ) ≠ 0 := by
    exact_mod_cast (show bilinear D c c ≠ 0 by dsimp [c]; omega)
  have hrec := fixed_ground_two_orbit_relation D a b hs
  change (fixedC2 D).mkQ (fixedGroundOrbit D c) = -(fixedC2 D).mkQ x at hrec
  have hmem : fixedGroundOrbit D c + x ∈ fixedC2 D := by
    apply (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mp
    change (fixedC2 D).mkQ (fixedGroundOrbit D c + x) = 0
    rw [map_add, hrec, neg_add_cancel]
  have each (j : Fin D.rank) :
      (fixedC2 D).mkQ (fixedMode D (neutralPair D i j 0 0) 0 (fixedGroundOrbit D c)) =
      -(fixedC2 D).mkQ (fixedMode D (neutralPair D i j 0 0) 0 x) := by
    have h := (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr
      (fixed_zero_mode_mem_c2 D (neutralPair D i j 0 0) _ hmem)
    change (fixedC2 D).mkQ
      (fixedMode D (neutralPair D i j 0 0) 0 (fixedGroundOrbit D c + x)) = 0 at h
    rw [map_add, map_add] at h
    exact eq_neg_of_add_eq_zero_left h
  have h := fixed_first_oscillator_class D i c
  simp only [each, smul_neg, Finset.sum_neg_distrib] at h
  have scaled := congrArg (fun v : FixedCarrier D ⧸ fixedC2 D => (bilinear D c c : ℂ)⁻¹ • v) h.symm
  simpa only [smul_smul, inv_mul_cancel₀ hB, one_smul, smul_neg] using scaled

theorem leech_fixed_ground_charge_step_outside_short (γ : Charge leechData)
    (hγ : γ ∉ ActualC2Cofinite.shortCharges leechData) :
    ∃ (i : Fin leechData.rank) (a : Charge leechData),
      (a = unitCharge leechData i ∨ a = -unitCharge leechData i) ∧
      let s := |bilinear leechData (unitCharge leechData i) γ| - leechData.G i i
      let δ := γ - (2 : ℤ) • a
      0 < s ∧
      (fixedC2 leechData).mkQ (fixedGroundOrbit leechData γ) =
        -(fixedC2 leechData).mkQ (fixedCreationOrbit leechData (-a) δ (2 * s)) ∧
      chargeEnergy leechData γ - chargeEnergy leechData δ = 2 * s ∧
      (chargeEnergy leechData δ).toNat < (chargeEnergy leechData γ).toNat :=
  fixed_ground_charge_step_outside_short leechData leech_spec.2.2.1 γ hγ

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2

#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_mode_two_orbits
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_two_orbit_relation
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_lower_creation_class_eq_zero
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.ground_orbit_norm_difference
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.ground_orbit_norm_decrease
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_charge_step
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_charge_step_outside_short
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_quadratic_zero_on_ground
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_zero_mode_mem_c2
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_ground_translation
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_first_oscillator_class
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.fixed_first_oscillator_two_orbit_relation
#print axioms D5.S3.VertexAlgebra.Lattice.ActualFixedC2.leech_fixed_ground_charge_step_outside_short
