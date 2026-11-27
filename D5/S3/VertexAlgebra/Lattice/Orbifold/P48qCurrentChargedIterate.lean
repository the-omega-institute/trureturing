/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCurrentChargedIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The charged ground and first-current iterate in the order-three cover. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHeisenbergCharged
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

/-!
The charged ground and first-oscillator fields of the P48q order-three
twist. The exponent is measured in the cover coordinate x, with z = x³.
Bakalov–Kac, arXiv:math/0402315v3, (3.13) at product index -1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate

open LatticeGeneratingFieldLocality (Carrier Charge Oscillator bilinear unitCharge)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (current_state_field)
open LatticeFiniteNegativeGeneration (neutralField neutralPolynomialMode)
open LatticeSugawaraCurrents (neutralField_ncoeff neutralMode_single)
open ThirdTwistedIterate (currentAlong)
open P48qTwistedChargeAction (lattice g)
open P48qThirdTwistedField (Cartan State fixedDualBases chargeVector fieldCoeff
  concreteChargedField lowerBound fieldCoeff_eq_zero_below)
open P48qTwistedHeisenberg (mode modeLinear projectAt projectAt_eq_fourier project_of_action
  mode_projectAt mode_eq_zero_above_coverBound currentField currentField_coeff
  mode_concreteChargedField_commutator)
open P48qFixedCurrentIterate (coverBound)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open ThirdEigenspacePairing (p48qForm p48qAction)
open scoped BigOperators VertexOperator

open private neutral_negative_single bilinear_unit from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private projection projection_apply projectAt_off_residue root_cube
  basisDirection sum_basisDirection currentPolynomial constant constant_current
  derivative derivative_current constant_C currentAlong_eq_polynomial from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private chargeVector_zero from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum
open private coverFrequency sumModes creationTerm annihilationTerm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedFieldTranslation

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "bShift" => ThirdTwistedChargeAction.bShift lattice g

/-- One summand at cover exponent k. The signed current mode m has exponent -m-3. -/
def orderedTerm (a : Charge lattice) (k m : ℤ) : Cartan →ₗ[ℂ] Module.End ℂ State :=
  let B := fieldCoeff fixedDualBases a (k + 3 + m)
  if m < 0 then (LinearMap.mulRight ℂ B).comp (modeLinear m)
  else (LinearMap.mulLeft ℂ B).comp (modeLinear m)

theorem orderedTerm_fields (a : Charge lattice) (u : Cartan) (k m : ℤ) :
    orderedTerm a k m u =
      if m < 0 then HVertexOperator.coeff (currentField u) (-m - 3) *
        HVertexOperator.coeff (concreteChargedField a) (k + 3 + m)
      else HVertexOperator.coeff (concreteChargedField a) (k + 3 + m) *
        HVertexOperator.coeff (currentField u) (-m - 3) := by
  rw [currentField_coeff, show -(-m - 3) - 3 = m by omega]
  change orderedTerm a k m u = if m < 0 then mode u m * fieldCoeff fixedDualBases a (k + 3 + m)
    else fieldCoeff fixedDualBases a (k + 3 + m) * mode u m
  by_cases h : m < 0 <;> simp only [orderedTerm, h, if_true, if_false, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply] <;> rfl

private theorem orderedTerm_apply_of_neg (a : Charge lattice) (u : Cartan) (k m : ℤ)
    (w : State) (hm : m < 0) :
    orderedTerm a k m u w = mode u m (fieldCoeff fixedDualBases a (k + 3 + m) w) := by
  rw [orderedTerm, if_pos hm] <;> rfl

private theorem orderedTerm_apply_of_nonneg (a : Charge lattice) (u : Cartan) (k m : ℤ)
    (w : State) (hm : 0 ≤ m) :
    orderedTerm a k m u w = fieldCoeff fixedDualBases a (k + 3 + m) (mode u m w) := by
  rw [orderedTerm, if_neg (not_lt.mpr hm)] <;> rfl

theorem orderedTerm_support (a : Charge lattice) (u : Cartan) (k : ℤ) (w : State) :
    Function.support (fun m => orderedTerm a k m u w) ⊆
      (Finset.Icc (min 0 (lowerBound a w - k - 3)) (coverBound w : ℤ) : Set ℤ) := by
  intro m hm
  change orderedTerm a k m u w ≠ 0 at hm
  change m ∈ Finset.Icc (min 0 (lowerBound a w - k - 3)) (coverBound w : ℤ)
  apply Finset.mem_Icc.mpr
  constructor
  · apply le_of_not_gt
    intro h
    have hneg : m < 0 := h.trans_le (min_le_left _ _)
    have hbelow : m < lowerBound a w - k - 3 := h.trans_le (min_le_right _ _)
    exact hm (by rw [orderedTerm_apply_of_neg a u k m w hneg,
      fieldCoeff_eq_zero_below fixedDualBases a w _ (by omega), map_zero])
  · apply le_of_not_gt
    intro h
    exact hm (by rw [orderedTerm_apply_of_nonneg a u k m w (by omega),
      mode_eq_zero_above_coverBound w u m h, map_zero])

private theorem orderedTerm_finite (a : Charge lattice) (u : Cartan) (k : ℤ) (w : State) :
    Function.HasFiniteSupport (fun m => orderedTerm a k m u w) :=
  (Finset.finite_toSet _).subset (orderedTerm_support a u k w)

private def orderedMode (a : Charge lattice) (k : ℤ) (u : Cartan) : Module.End ℂ State where
  toFun w := ∑ᶠ m, orderedTerm a k m u w
  map_add' w v := by
    simp only [map_add]
    exact finsum_add_distrib (orderedTerm_finite a u k w) (orderedTerm_finite a u k v)
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (orderedTerm_finite a u k w)).symm

/-- The actual normal order of an arbitrary current and the concrete charged field. -/
def normalOrderedCurrentCoeff (a : Charge lattice) (k : ℤ) :
    Cartan →ₗ[ℂ] Module.End ℂ State where
  toFun := orderedMode a k
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ m, orderedTerm a k m (u + v) w) =
      (∑ᶠ m, orderedTerm a k m u w) + (∑ᶠ m, orderedTerm a k m v w)
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (orderedTerm_finite a u k w) (orderedTerm_finite a v k w)
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    change (∑ᶠ m, orderedTerm a k m (c • u) w) = c • ∑ᶠ m, orderedTerm a k m u w
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_finsum' c (orderedTerm_finite a u k w)).symm

theorem normalOrderedCurrentCoeff_along_charge (a : Charge lattice) (k : ℤ) :
    normalOrderedCurrentCoeff a k (chargeVector a) =
      P48qChargedFieldTranslation.normalOrderedCurrentCoeff a k := by
  apply LinearMap.ext
  intro w
  let f (m : ℤ) := orderedTerm a k m (chargeVector a) w
  have hf : Function.HasFiniteSupport f := orderedTerm_finite a (chargeVector a) k w
  have hneg (n : ℕ) : f (Int.negSucc n) = creationTerm a (k + 3) n w := by
    dsimp only [f]
    rw [orderedTerm_apply_of_neg a _ k _ w (by omega)]
    have hk : k + 3 + Int.negSucc n = k + 3 - coverFrequency n := by
      rw [Int.negSucc_eq]
      unfold coverFrequency
      omega
    rw [hk] <;> rfl
  have hpos (n : ℕ) : f ((n + 1 : ℕ) : ℤ) = annihilationTerm a (k + 3) n w := by
    dsimp only [f]
    rw [orderedTerm_apply_of_nonneg a _ k _ w (by omega)] <;> rfl
  have cover : Set.range Int.negSucc ∪ Set.range Int.ofNat = Set.univ := by
    ext m
    constructor
    · intro _
      trivial
    · intro _
      cases m with
      | ofNat n => exact Or.inr ⟨n, rfl⟩
      | negSucc n => exact Or.inl ⟨n, rfl⟩
  have disjoint : Disjoint (Set.range Int.negSucc) (Set.range Int.ofNat) := by
    rw [Set.disjoint_left]
    rintro m ⟨n, rfl⟩ ⟨l, h⟩
    simp only [Int.negSucc_eq, Int.ofNat_eq_natCast] at h
    omega
  have hsplit : (∑ᶠ m : ℤ, f m) =
      (∑ᶠ n : ℕ, f (Int.negSucc n)) + ∑ᶠ n : ℕ, f (Int.ofNat n) := by
    rw [← finsum_mem_univ, ← cover, finsum_mem_union' disjoint
      (hf.subset Set.inter_subset_right) (hf.subset Set.inter_subset_right),
      finsum_mem_range (fun m n h => Int.negSucc.inj h), finsum_mem_range Int.ofNat_injective]
  have hrange : Set.range Int.ofNat =
      insert 0 (Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℤ))) := by
    ext m
    constructor
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Set.mem_insert _ _
      | succ n => exact Set.mem_insert_of_mem _ ⟨n, rfl⟩
    · intro hm
      rcases Set.mem_insert_iff.mp hm with h | ⟨n, hn⟩
      · exact ⟨0, h.symm⟩
      · exact ⟨n + 1, hn⟩
  have hnot : (0 : ℤ) ∉ Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
    rintro ⟨n, hn⟩
    change ((n + 1 : ℕ) : ℤ) = 0 at hn
    omega
  have hsucc : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) :=
    Int.ofNat_injective.comp Nat.succ_injective
  have hnonneg : (∑ᶠ n : ℕ, f (Int.ofNat n)) = f 0 + ∑ᶠ n : ℕ, f ((n + 1 : ℕ) : ℤ) := by
    rw [← finsum_mem_range (f := f) Int.ofNat_injective, hrange,
      finsum_mem_insert' f hnot (hf.subset Set.inter_subset_right),
      finsum_mem_range hsucc]
  change (∑ᶠ m : ℤ, f m) = _
  rw [hsplit, hnonneg]
  simp only [hneg, hpos, P48qChargedFieldTranslation.normalOrderedCurrentCoeff,
    LinearMap.add_apply, sumModes, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
  change _ + (f 0 + _) = _
  dsimp only [f]
  rw [orderedTerm_apply_of_nonneg a _ k 0 w le_rfl, add_zero, add_assoc]

/-- The scalar subtracted from the normal order, before shifting the ground field by z⁻¹. -/
def contraction (a : Charge lattice) : Cartan →ₗ[ℂ] ℂ :=
  (1 / 3 : ℂ) • (p48qForm.flip (chargeVector a)).comp (projection 1) +
    (2 / 3 : ℂ) • (p48qForm.flip (chargeVector a)).comp (projection 2)

theorem contraction_apply (a : Charge lattice) (u : Cartan) :
    contraction a u = (1 / 3 : ℂ) * p48qForm (projectAt 1 u) (chargeVector a) +
      (2 / 3 : ℂ) * p48qForm (projectAt 2 u) (chargeVector a) := by
  change (1 / 3 : ℂ) * p48qForm (projection 1 u) (chargeVector a) +
      (2 / 3 : ℂ) * p48qForm (projection 2 u) (chargeVector a) = _
  rw [projection_apply, projection_apply]

private def firstCoeff (a : Charge lattice) (k : ℤ) : Cartan →ₗ[ℂ] Module.End ℂ State :=
  normalOrderedCurrentCoeff a k -
    (contraction a).smulRight (fieldCoeff fixedDualBases a (k + 3))

private theorem firstCoeff_apply (a : Charge lattice) (u : Cartan) (k : ℤ) :
    firstCoeff a k u = normalOrderedCurrentCoeff a k u -
      contraction a u • fieldCoeff fixedDualBases a (k + 3) := by
  simp only [firstCoeff, LinearMap.sub_apply, LinearMap.smulRight_apply]

private theorem firstCoeff_bddBelow (a : Charge lattice) (u : Cartan) (w : State) :
    BddBelow (Function.support (fun k => firstCoeff a k u w)) := by
  let low := lowerBound a w - 3
  let cut := Finset.Icc (0 : ℤ) (coverBound w : ℤ)
  let bound (m : ℤ) := lowerBound a (mode u m w) - 3 - m
  let bounds := insert low (cut.image bound)
  let hne : bounds.Nonempty := Finset.insert_nonempty _ _
  refine ⟨bounds.min' hne, ?_⟩
  intro k hk
  apply le_of_not_gt
  intro h
  have hlow : k < low :=
    h.trans_le (Finset.min'_le bounds _ (Finset.mem_insert_self _ _))
  have hz : fieldCoeff fixedDualBases a (k + 3) w = 0 :=
    fieldCoeff_eq_zero_below fixedDualBases a w _ (by dsimp [low] at hlow; omega)
  have hterm (m : ℤ) : orderedTerm a k m u w = 0 := by
    by_cases hm : m < 0
    · rw [orderedTerm_apply_of_neg a u k m w hm, fieldCoeff_eq_zero_below fixedDualBases a w _
        (by dsimp [low] at hlow; omega), map_zero]
    · rw [orderedTerm_apply_of_nonneg a u k m w (le_of_not_gt hm)]
      by_cases hb : (coverBound w : ℤ) < m
      · rw [mode_eq_zero_above_coverBound w u m hb, map_zero]
      · have hmem : bound m ∈ bounds :=
          Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr
            ⟨le_of_not_gt hm, le_of_not_gt hb⟩))
        have hbelow := h.trans_le (Finset.min'_le bounds _ hmem)
        exact fieldCoeff_eq_zero_below fixedDualBases a _ _ (by dsimp [bound] at hbelow; omega)
  apply hk
  change firstCoeff a k u w = 0
  rw [firstCoeff_apply, LinearMap.sub_apply, LinearMap.smul_apply, hz, smul_zero, sub_zero]
  exact finsum_eq_zero_of_forall_eq_zero hterm

private def firstField (a : Charge lattice) : Cartan →ₗ[ℂ] VertexOperator ℂ State where
  toFun u := VertexOperator.of_coeff (fun k => firstCoeff a k u) (firstCoeff_bddBelow a u)
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext k
    change firstCoeff a k (u + v) = firstCoeff a k u + firstCoeff a k v
    exact map_add (firstCoeff a k) u v
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext k
    change firstCoeff a k (c • u) = c • firstCoeff a k u
    exact map_smul (firstCoeff a k) c u

private theorem firstField_coeff (a : Charge lattice) (u : Cartan) (k : ℤ) :
    HVertexOperator.coeff (firstField a u) k = firstCoeff a k u := rfl

/-- The constant and first-oscillator coordinates of the actual charge polynomial. -/
def polynomialField (a : Charge lattice) : Oscillator lattice →ₗ[ℂ] VertexOperator ℂ State :=
  constant.smulRight (concreteChargedField a) +
    ∑ i : Fin lattice.rank, (constant.comp (derivative i)).smulRight
      (firstField a (basisDirection i))

/-- The field on finite sums of charge ground states and first oscillators,
extended linearly to the carrier by projecting to those polynomial coordinates. -/
def stateField : Carrier lattice →ₗ[ℂ] VertexOperator ℂ State :=
  Finsupp.lsum ℂ polynomialField

/-- The actual lattice state e^a. -/
def chargedGround (a : Charge lattice) : Carrier lattice := Finsupp.single a 1

/-- The actual lattice first-oscillator polynomial in charge a. -/
def chargedFirst (a : Charge lattice) (u : Cartan) : Carrier lattice :=
  Finsupp.single a (currentPolynomial u)

theorem stateField_ground (a : Charge lattice) :
    stateField (chargedGround a) = concreteChargedField a := by
  rw [stateField, chargedGround, Finsupp.lsum_single]
  have hd (i : Fin lattice.rank) : derivative i 1 = 0 := MvPolynomial.pderiv_one
  have hc : constant (1 : Oscillator lattice) = 1 := MvPolynomial.constantCoeff.map_one
  simp only [polynomialField, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, hd, hc, map_zero, zero_smul, one_smul, Finset.sum_const_zero, add_zero]

private theorem stateField_first (a : Charge lattice) (u : Cartan) :
    stateField (chargedFirst a u) = firstField a u := by
  rw [stateField, chargedFirst, Finsupp.lsum_single]
  simp only [polynomialField, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.smulRight_apply, constant_current, derivative_current, constant_C,
    zero_smul, zero_add]
  calc
    _ = firstField a (∑ i : Fin lattice.rank, u i • basisDirection i) := by
      simp only [map_sum, map_smul]
    _ = _ := by rw [sum_basisDirection]

theorem stateField_first_coeff (a : Charge lattice) (u : Cartan) (k : ℤ) :
    HVertexOperator.coeff (stateField (chargedFirst a u)) k =
      normalOrderedCurrentCoeff a k u - contraction a u • fieldCoeff fixedDualBases a (k + 3) := by
  rw [stateField_first, firstField_coeff, firstCoeff_apply]

/-- At charge zero, the first-oscillator field is the existing twisted current. -/
theorem stateField_current (u : Cartan) :
    stateField (currentAlong lattice u) = currentField u := by
  have hsource : currentAlong lattice u = chargedFirst 0 u := currentAlong_eq_polynomial u
  have hpair : contraction 0 u = 0 := by
    simp only [contraction_apply, chargeVector_zero, map_zero, mul_zero, add_zero]
  rw [hsource]
  apply HVertexOperator.coeff_inj
  funext k
  rw [stateField_first_coeff, hpair, zero_smul, sub_zero, currentField_coeff]
  apply LinearMap.ext
  intro w
  change (∑ᶠ m : ℤ, orderedTerm 0 k m u w) = mode u (-k - 3) w
  have hs (m : ℤ) (hm : m ≠ -k - 3) : orderedTerm 0 k m u w = 0 := by
    rw [orderedTerm_fields, concreteChargedField_zero_coeff, if_neg (by omega : k + 3 + m ≠ 0)]
    split <;> simp
  rw [finsum_eq_single _ (-k - 3) hs, orderedTerm_fields,
    concreteChargedField_zero_coeff, if_pos (by omega : k + 3 + (-k - 3) = 0),
    currentField_coeff, show -(-(-k - 3) - 3) - 3 = -k - 3 by omega]
  split <;> simp only [Module.End.mul_apply, LinearMap.id_apply]

private theorem source_modes (a : Charge lattice) (u : Cartan) (n : ℤ) :
    mu lattice (currentAlong lattice u) n (chargedGround a) =
      ∑ i : Fin lattice.rank, u i •
        (VertexOperator.ncoeff (neutralField lattice i) n (chargedGround a)) := by
  simp only [mu, currentAlong, map_sum, map_smul, current_state_field, Finset.sum_apply,
    Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply]

theorem source_product_minus_one (a : Charge lattice) (u : Cartan) :
    mu lattice (currentAlong lattice u) (-1) (chargedGround a) = chargedFirst a u := by
  rw [source_modes]
  have h (i : Fin lattice.rank) :
      VertexOperator.ncoeff (neutralField lattice i) (-1) (chargedGround a) =
        Finsupp.single a (MvPolynomial.X (i, 0)) := by
    simpa only [chargedGround, Nat.cast_zero, neg_zero, zero_sub, mul_one] using
      neutral_negative_single lattice i 0 a (1 : Oscillator lattice)
  simp_rw [h]
  change (∑ i : Fin lattice.rank, u i •
    (Finsupp.lsingle a : Oscillator lattice →ₗ[ℂ] Carrier lattice) (MvPolynomial.X (i, 0))) =
      (Finsupp.lsingle a : Oscillator lattice →ₗ[ℂ] Carrier lattice) (currentPolynomial u)
  simp only [currentPolynomial, map_sum, map_smul]

theorem source_product_zero (a : Charge lattice) (u : Cartan) :
    mu lattice (currentAlong lattice u) 0 (chargedGround a) =
      p48qForm u (chargeVector a) • chargedGround a := by
  have h (i : Fin lattice.rank) :
      VertexOperator.ncoeff (neutralField lattice i) 0 (chargedGround a) =
        (bilinear lattice (unitCharge lattice i) a : ℂ) • chargedGround a := by
    rw [neutralField_ncoeff, chargedGround, neutralMode_single]
    simp only [neutralPolynomialMode, lt_irrefl, if_false, if_true, LinearMap.smul_apply,
      LinearMap.id_apply, Finsupp.smul_single]
  rw [source_modes]
  simp_rw [h, smul_smul]
  rw [← Finset.sum_smul]
  apply congrArg (fun c : ℂ => c • chargedGround a)
  rw [p48qForm, Matrix.toBilin'_apply]
  change (∑ i : Fin lattice.rank, u i * (bilinear lattice (unitCharge lattice i) a : ℂ)) =
    ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank, u i * (lattice.G i j : ℂ) * (a j : ℂ)
  simp only [bilinear_unit, Int.cast_sum, Int.cast_mul, Finset.mul_sum, mul_assoc]

theorem source_product_positive (a : Charge lattice) (u : Cartan) (n : ℤ) (hn : 0 < n) :
    mu lattice (currentAlong lattice u) n (chargedGround a) = 0 := by
  rw [source_modes]
  simp only [neutralField_ncoeff, chargedGround, neutralMode_single, neutralPolynomialMode,
    if_neg (not_lt.mpr hn.le), if_neg (ne_of_gt hn), LinearMap.smul_apply, LinearMap.sum_apply,
    Derivation.coeFn_coe, MvPolynomial.pderiv_one, smul_zero, Finset.sum_const_zero,
    Finsupp.single_zero]

private theorem projectAt_on_residue (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (m : ℤ) (hm : m % 3 = (r : ℤ)) :
    projectAt m u = u := by
  rw [projectAt_eq_fourier, hm, Int.toNat_natCast]
  exact project_of_action _ (root_cube r) u hu

private theorem contraction_on_residue (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) :
    contraction a u = ((r : ℂ) / 3) * p48qForm u (chargeVector a) := by
  rw [contraction_apply]
  interval_cases r
  · rw [projectAt_off_residue u 0 (by decide) hu 1 (by decide),
      projectAt_off_residue u 0 (by decide) hu 2 (by decide)]
    simp
  · rw [projectAt_on_residue u 1 (by decide) hu 1 (by decide),
      projectAt_off_residue u 1 (by decide) hu 2 (by decide)]
    simp
  · rw [projectAt_off_residue u 2 (by decide) hu 1 (by decide),
      projectAt_on_residue u 2 (by decide) hu 2 (by decide)]
    simp

/-- In the matching residue, the mixed commutator is the field of the actual
source zero product, with the exponent shift dictated by the signed mode. -/
theorem mode_commutator_source_zero (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (m l : ℤ) (hm : m % 3 = (r : ℤ)) (w : State) :
    mode u m (HVertexOperator.coeff (concreteChargedField a) l w) -
      HVertexOperator.coeff (concreteChargedField a) l (mode u m w) =
    HVertexOperator.coeff
      (stateField (mu lattice (currentAlong lattice u) 0 (chargedGround a))) (l - m) w := by
  simpa only [source_product_zero, map_smul, stateField_ground, Pi.smul_apply,
    LinearMap.smul_apply, HVertexOperator.coeff_apply_apply,
    projectAt_on_residue u r hr hu m hm] using
    mode_concreteChargedField_commutator u a m l w

/-- The field on the actual negative-one product of a residue-r current
and the charged ground. The shift k+3 is multiplication by z⁻¹. -/
theorem source_minus_one_field (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k : ℤ) :
    HVertexOperator.coeff (stateField (mu lattice (currentAlong lattice u) (-1) (chargedGround a))) k =
      normalOrderedCurrentCoeff a k u -
        (((r : ℂ) / 3) * p48qForm u (chargeVector a)) •
          HVertexOperator.coeff (concreteChargedField a) (k + 3) := by
  rw [source_product_minus_one, stateField_first_coeff, contraction_on_residue a u r hr hu] <;> rfl

/-- BK (3.13) at -1 using the concrete normal order and the actual lattice
source products at j=0 and j=1. Every higher source product vanishes. -/
theorem current_charged_BK_iterate (a : Charge lattice) (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k : ℤ) (w : State) :
    (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, orderedTerm a k m u w) =
      ∑ᶠ j : ℕ, Ring.choose ((r : ℂ) / 3) j • HVertexOperator.coeff
        (stateField (mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (chargedGround a)))
        (k + 3 * (j : ℤ)) w := by
  let f (m : ℤ) := orderedTerm a k m u w
  let I := Finset.Icc (min 0 (lowerBound a w - k - 3)) (coverBound w : ℤ)
  have hI : Function.support f ⊆ (I : Set ℤ) := orderedTerm_support a u k w
  have hr' : Function.support f ⊆ {m : ℤ | m % 3 = (r : ℤ)} := by
    intro m hm
    change m % 3 = (r : ℤ)
    by_contra hoff
    have hz : mode u m = 0 := by
      rw [← mode_projectAt u m, projectAt_off_residue u r hr hu m hoff]
      exact (modeLinear m).map_zero
    apply hm
    change orderedTerm a k m u w = 0
    rw [orderedTerm_fields, currentField_coeff, show -(-m - 3) - 3 = m by omega, hz]
    split <;> simp
  have horder : (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, f m) =
      normalOrderedCurrentCoeff a k u w := by
    change _ = ∑ᶠ m : ℤ, f m
    rw [finsum_eq_sum_of_support_subset f hI]
    apply finsum_mem_eq_sum_of_inter_support_eq
    rw [Set.inter_eq_right.mpr hr', Set.inter_eq_right.mpr hI]
  let term (j : ℕ) := Ring.choose ((r : ℂ) / 3) j • HVertexOperator.coeff
    (stateField (mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (chargedGround a)))
    (k + 3 * (j : ℤ)) w
  have hterm : Function.support term ⊆ (↑({0, 1} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra hout
    have h0 : j ≠ 0 := fun he => hout (by simp [he])
    have h1 : j ≠ 1 := fun he => hout (by simp [he])
    apply hj
    simp only [term, source_product_positive a u _ (by omega : 0 < (j : ℤ) - 1),
      map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have h0 : term 0 = normalOrderedCurrentCoeff a k u w -
      (((r : ℂ) / 3) * p48qForm u (chargeVector a)) •
        HVertexOperator.coeff (concreteChargedField a) (k + 3) w := by
    simp only [term, Nat.cast_zero, zero_sub, mul_zero, add_zero, Ring.choose_zero_right,
      one_smul, source_minus_one_field a u r hr hu, LinearMap.sub_apply, LinearMap.smul_apply]
  have h1 : term 1 = (((r : ℂ) / 3) * p48qForm u (chargeVector a)) •
      HVertexOperator.coeff (concreteChargedField a) (k + 3) w := by
    simp only [term, Nat.cast_one, sub_self, mul_one, Ring.choose_one_right, source_product_zero,
      map_smul, stateField_ground, Pi.smul_apply, LinearMap.smul_apply, smul_smul]
  change (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, f m) = ∑ᶠ j, term j
  rw [horder, finsum_eq_sum_of_support_subset term hterm, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1),
    h0, h1, sub_add_cancel]

/-- For the current along a, the sum of residue corrections is b_a.
The resulting first-oscillator field is the z-derivative of the ground field. -/
theorem stateField_along_charge_translation (a : Charge lattice) (k : ℤ) :
    HVertexOperator.coeff (stateField (chargedFirst a (chargeVector a))) k =
      (((k + 3 : ℤ) : ℂ) / 3) • HVertexOperator.coeff (concreteChargedField a) (k + 3) := by
  rw [stateField_first_coeff, normalOrderedCurrentCoeff_along_charge, contraction_apply,
    P48qChargedFieldTranslation.weighted_projection_pairing_eq_neg_bShift, neg_smul, sub_neg_eq_add]
  exact (P48qChargedFieldTranslation.fieldCoeff_translation a k).symm

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate
