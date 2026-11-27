/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedTwoCurrentIterate
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Twisted charge fields through degree two in the first oscillators. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate

/-!
The P48q twisted field on charge polynomials through degree two in the first
oscillators. The cover coordinate is x, with z = x³. The two orders of
inserting first currents agree by the actual same-sign Heisenberg relations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedTwoCurrentIterate

open LatticeGeneratingFieldLocality (Carrier Charge Oscillator)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (current_state_field)
open LatticeSugawaraCurrents
  (neutralField_ncoeff neutralMode_single neutralMode_heisenberg)
open LatticeFiniteNegativeGeneration (neutralField neutralMode neutralPolynomialMode)
open ThirdTwistedIterate (currentAlong)
open ThirdEigenspacePairing (p48qAction p48qForm)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField
  (Cartan State chargeVector fieldCoeff fixedDualBases concreteChargedField
    lowerBound fieldCoeff_eq_zero_below)
open P48qTwistedHeisenberg (mode modeLinear mode_projectAt mode_eq_zero_above_coverBound)
open P48qFixedCurrentIterate (coverBound normalOrderedTerm)
open P48qCurrentChargedIterate
  (chargedGround chargedFirst contraction normalOrderedCurrentCoeff
    source_product_minus_one source_product_zero source_product_positive)
open P48qQuadraticStateField (correction correction_swap)
open MvPolynomial
open scoped BigOperators VertexOperator

open private basisDirection sum_basisDirection currentPolynomial constant constant_current
  constant_mul constant_C derivative derivative_mul derivative_current derivative_C
  currentAlong_eq_polynomial correction_on_residue mode_mul_comm_of_sign
  projectAt_off_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
open private orderedTerm_finite contraction_on_residue from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCurrentChargedIterate
open private chargeVector_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private def sourceMode (u : Cartan) (n : ℤ) : Module.End ℂ (Carrier lattice) :=
  ∑ i : Fin lattice.rank, u i • neutralMode lattice i n

private theorem sourceMode_apply (u : Cartan) (n : ℤ) (p : Carrier lattice) :
    sourceMode u n p = mu lattice (currentAlong lattice u) n p := by
  simp only [sourceMode, mu, currentAlong, map_sum, map_smul, current_state_field,
    neutralField_ncoeff, Finset.sum_apply, Pi.smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]

private theorem sourceMode_mul (u v : Cartan) (m n : ℤ) :
    sourceMode u m * sourceMode v n =
      ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
        (u i * v j) • (neutralMode lattice i m * neutralMode lattice j n) := by
  change (∑ i : Fin lattice.rank, u i • neutralMode lattice i m) * sourceMode v n = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (u i • neutralMode lattice i m) *
    (∑ j : Fin lattice.rank, v j • neutralMode lattice j n) = _
  rw [Algebra.smul_mul_assoc, Finset.mul_sum, Finset.smul_sum]
  simp only [Algebra.mul_smul_comm, smul_smul]

private theorem sourceMode_commutator (u v : Cartan) (n : ℤ) :
    sourceMode u n * sourceMode v (-1) - sourceMode v (-1) * sourceMode u n =
      (if n = 1 then p48qForm u v else 0) • (1 : Module.End ℂ (Carrier lattice)) := by
  have hrev : sourceMode v (-1) * sourceMode u n =
      ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
        (v j * u i) • (neutralMode lattice j (-1) * neutralMode lattice i n) :=
    (sourceMode_mul v u (-1) n).trans Finset.sum_comm
  have hterm (i j : Fin lattice.rank) :
      (u i * v j) • (neutralMode lattice i n * neutralMode lattice j (-1)) -
        (v j * u i) • (neutralMode lattice j (-1) * neutralMode lattice i n) =
      (u i * v j) • ((if n = 1 then (n : ℂ) * (lattice.G i j : ℂ) else 0) •
        (1 : Module.End ℂ (Carrier lattice))) := by
    rw [mul_comm (v j) (u i), ← smul_sub, neutralMode_heisenberg]
    simp only [show n + -1 = 0 ↔ n = 1 by omega]
  rw [sourceMode_mul, hrev]
  simp_rw [← Finset.sum_sub_distrib, hterm]
  by_cases hn : n = 1
  · subst n
    simp only [ite_true, Int.cast_one, one_mul, smul_smul]
    rw [p48qForm, Matrix.toBilin'_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply congrArg (fun c : ℂ => c • (1 : Module.End ℂ (Carrier lattice)))
    change (u i * v j) * (lattice.G i j : ℂ) =
      u i * (lattice.G i j : ℂ) * v j
    ring
  · simp [hn]

/-- The two nonnegative source products on v(-1)e^a. -/
theorem source_product_nonneg (a : Charge lattice) (u v : Cartan) (n : ℤ) (hn : 0 ≤ n) :
    mu lattice (currentAlong lattice u) n (chargedFirst a v) =
      if n = 0 then p48qForm u (chargeVector a) • chargedFirst a v
      else if n = 1 then p48qForm u v • chargedGround a else 0 := by
  have h := LinearMap.congr_fun (sourceMode_commutator u v n) (chargedGround a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, sourceMode_apply,
    source_product_minus_one, LinearMap.smul_apply, Module.End.one_apply] at h
  by_cases h0 : n = 0
  · subst n
    rw [source_product_zero, ← sourceMode_apply v, map_smul, sourceMode_apply,
      source_product_minus_one, if_neg (by decide : (0 : ℤ) ≠ 1), zero_smul] at h
    simpa only [ite_true] using sub_eq_zero.mp h
  · rw [source_product_positive a u n (lt_of_le_of_ne hn (Ne.symm h0)),
      ← sourceMode_apply v, map_zero, sub_zero] at h
    rw [if_neg h0, h]
    by_cases h1 : n = 1 <;> simp [h1]

/-- The oscillator product in the actual charge sector of the lattice carrier. -/
def chargedSecond (a : Charge lattice) (u v : Cartan) : Carrier lattice :=
  Finsupp.single a (currentPolynomial u * currentPolynomial v)

theorem chargedSecond_swap (a : Charge lattice) (u v : Cartan) :
    chargedSecond a u v = chargedSecond a v u := by
  simp only [chargedSecond, mul_comm]

theorem source_product_second (a : Charge lattice) (u v : Cartan) :
    mu lattice (currentAlong lattice u) (-1) (chargedFirst a v) = chargedSecond a u v := by
  let L : Oscillator lattice →ₗ[ℂ] Carrier lattice := Finsupp.lsingle a
  rw [← sourceMode_apply]
  simp only [sourceMode, LinearMap.sum_apply, LinearMap.smul_apply, chargedFirst,
    neutralMode_single, neutralPolynomialMode, if_pos (by decide : (-1 : ℤ) < 0),
    show (-(-1 : ℤ) - 1).toNat = 0 by decide, LinearMap.mulLeft_apply]
  change (∑ i : Fin lattice.rank, u i • L (X (i, 0) * currentPolynomial v)) =
    L (currentPolynomial u * currentPolynomial v)
  have hu : currentPolynomial u = ∑ i : Fin lattice.rank, u i • X (i, 0) := rfl
  rw [hu, Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul]

private abbrev groundCoeff (a : Charge lattice) (k : ℤ) : Module.End ℂ State :=
  fieldCoeff fixedDualBases a k

private abbrev firstTerm := P48qCurrentChargedIterate.orderedTerm

/-- Place a concrete current mode to the left if it creates, otherwise to the right. -/
private def place (u : Cartan) (m : ℤ) : Module.End ℂ (Module.End ℂ State) :=
  if m < 0 then LinearMap.mulLeft ℂ (mode u m) else LinearMap.mulRight ℂ (mode u m)

private theorem place_apply (u : Cartan) (m : ℤ) (B : Module.End ℂ State) :
    place u m B = if m < 0 then mode u m * B else B * mode u m := by
  by_cases hm : m < 0 <;> simp only [place, hm, if_true, if_false,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]

private theorem firstTerm_eq_place (a : Charge lattice) (k m : ℤ) (u : Cartan) :
    firstTerm a k m u = place u m (groundCoeff a (k + 3 + m)) := by
  rw [P48qCurrentChargedIterate.orderedTerm_fields, P48qTwistedHeisenberg.currentField_coeff,
    show -(-m - 3) - 3 = m by omega, place_apply] <;> rfl

private def doubleTerm (a : Charge lattice) (k : ℤ) (u v : Cartan) (m n : ℤ) :
    Module.End ℂ State :=
  place u m (firstTerm a (k + 3 + m) n v)

private theorem doubleTerm_swap (a : Charge lattice) (k : ℤ) (u v : Cartan) (m n : ℤ) :
    doubleTerm a k u v m n = doubleTerm a k v u n m := by
  simp only [doubleTerm, firstTerm_eq_place, place_apply,
    show k + 3 + n + 3 + m = k + 3 + m + 3 + n by omega]
  by_cases hm : m < 0 <;> by_cases hn : n < 0
  · simp only [hm, hn, if_true, ← mul_assoc]
    rw [mode_mul_comm_of_sign u v m n (Or.inl ⟨hm, hn⟩)]
  · simp only [hm, hn, if_true, if_false, mul_assoc]
  · simp only [hm, hn, if_true, if_false, mul_assoc]
  · simp only [hm, hn, if_false, mul_assoc]
    rw [mode_mul_comm_of_sign v u n m (Or.inr ⟨le_of_not_gt hn, le_of_not_gt hm⟩)]

/-- A lower bound uniform over the mode summands in a one-current normal order. -/
private def firstLower (a : Charge lattice) (v : Cartan) (w : State) : ℤ :=
  let bounds := insert (lowerBound a w - 3) <|
    (Finset.Icc (0 : ℤ) (coverBound w : ℤ)).image
      (fun n => lowerBound a (mode v n w) - 3 - n)
  bounds.min' (Finset.insert_nonempty _ _)

private theorem firstTerm_zero_below (a : Charge lattice) (v : Cartan) (w : State)
    (k n : ℤ) (hk : k < firstLower a v w) : firstTerm a k n v w = 0 := by
  rw [firstTerm_eq_place, place_apply]
  dsimp only [firstLower] at hk
  by_cases hn : n < 0
  · have hlow : k < lowerBound a w - 3 :=
      hk.trans_le (Finset.min'_le _ _ (Finset.mem_insert_self _ _))
    rw [if_pos hn, Module.End.mul_apply,
      fieldCoeff_eq_zero_below fixedDualBases a w (k + 3 + n) (by omega), map_zero]
  · rw [if_neg hn, Module.End.mul_apply]
    by_cases hb : (coverBound w : ℤ) < n
    · rw [mode_eq_zero_above_coverBound w v n hb, map_zero]
    · have hmem : lowerBound a (mode v n w) - 3 - n ∈
          (Finset.Icc (0 : ℤ) (coverBound w : ℤ)).image
            (fun j => lowerBound a (mode v j w) - 3 - j) :=
        Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨le_of_not_gt hn, le_of_not_gt hb⟩)
      have hlow := hk.trans_le (Finset.min'_le _ _ (Finset.mem_insert_of_mem hmem))
      exact fieldCoeff_eq_zero_below fixedDualBases a _ _ (by omega)

private def outerIndices (a : Charge lattice) (k : ℤ) (v : Cartan) (w : State) : Finset ℤ :=
  Finset.Icc (min 0 (firstLower a v w - k - 3)) (coverBound w : ℤ)

private theorem doubleTerm_outerIndices (a : Charge lattice) (k : ℤ) (u v : Cartan)
    (w : State) (m n : ℤ) (h : doubleTerm a k u v m n w ≠ 0) :
    m ∈ outerIndices a k v w := by
  change m ∈ Finset.Icc (min 0 (firstLower a v w - k - 3)) (coverBound w : ℤ)
  apply Finset.mem_Icc.mpr
  constructor
  · apply le_of_not_gt
    intro hm
    have hneg := hm.trans_le (min_le_left _ _)
    have hlow := hm.trans_le (min_le_right _ _)
    exact h (by rw [doubleTerm, place_apply, if_pos hneg, Module.End.mul_apply,
      firstTerm_zero_below a v w _ n (by omega), map_zero])
  · apply le_of_not_gt
    intro hm
    exact h (by rw [doubleTerm, place_apply, if_neg (by omega : ¬ m < 0),
      Module.End.mul_apply, mode_eq_zero_above_coverBound w u m hm, map_zero])

private def doubleRow (a : Charge lattice) (k : ℤ) (u v : Cartan) (m : ℤ) :
    Module.End ℂ State :=
  place u m (normalOrderedCurrentCoeff a (k + 3 + m) v)

private theorem doubleRow_apply (a : Charge lattice) (k : ℤ) (u v : Cartan) (m : ℤ) (w : State) :
    doubleRow a k u v m w = ∑ᶠ n : ℤ, doubleTerm a k u v m n w := by
  by_cases hm : m < 0
  · simp only [doubleRow, doubleTerm, place_apply, if_pos hm, Module.End.mul_apply]
    change mode u m (∑ᶠ n : ℤ, firstTerm a (k + 3 + m) n v w) = _
    exact map_finsum _ (orderedTerm_finite a v _ w)
  · simp only [doubleRow, doubleTerm, place_apply, if_neg hm, Module.End.mul_apply] <;> rfl

private theorem doubleRow_support (a : Charge lattice) (k : ℤ) (u v : Cartan) (w : State) :
    Function.support (fun m => doubleRow a k u v m w) ⊆ (outerIndices a k v w : Set ℤ) := by
  intro m hm
  by_contra hout
  apply hm
  change doubleRow a k u v m w = 0
  rw [doubleRow_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_contra hn
  exact hout (doubleTerm_outerIndices a k u v w m n hn)

private theorem doubleRow_finite (a : Charge lattice) (k : ℤ) (u v : Cartan) (w : State) :
    Function.HasFiniteSupport (fun m => doubleRow a k u v m w) :=
  (Finset.finite_toSet _).subset (doubleRow_support a k u v w)

/-- The finite double normal-order coefficient before the charge and diagonal corrections. -/
def normalOrderedSecondCoeff (a : Charge lattice) (k : ℤ) (u v : Cartan) : Module.End ℂ State where
  toFun w := ∑ᶠ m : ℤ, doubleRow a k u v m w
  map_add' w w' := by
    simp only [map_add]
    exact finsum_add_distrib (doubleRow_finite a k u v w) (doubleRow_finite a k u v w')
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (doubleRow_finite a k u v w)).symm

private theorem normalOrderedSecondCoeff_eq_rectangle (a : Charge lattice) (k : ℤ) (u v : Cartan) (w : State) :
    normalOrderedSecondCoeff a k u v w =
      ∑ m ∈ outerIndices a k v w, ∑ n ∈ outerIndices a k u w, doubleTerm a k u v m n w := by
  change (∑ᶠ m : ℤ, doubleRow a k u v m w) = _
  rw [finsum_eq_sum_of_support_subset _ (doubleRow_support a k u v w)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [doubleRow_apply]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  change doubleTerm a k u v m n w ≠ 0 at hn
  rw [doubleTerm_swap] at hn
  exact doubleTerm_outerIndices a k v u w n m hn

/-- The double normal order is symmetric in its two current directions. -/
theorem normalOrderedSecondCoeff_swap (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    normalOrderedSecondCoeff a k u v = normalOrderedSecondCoeff a k v u := by
  apply LinearMap.ext
  intro w
  rw [normalOrderedSecondCoeff_eq_rectangle, normalOrderedSecondCoeff_eq_rectangle, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  exact DFunLike.congr_fun (doubleTerm_swap a k u v m n) w

private theorem normalOrderedSecondCoeff_add (a : Charge lattice) (k : ℤ) (u v v' : Cartan) :
    normalOrderedSecondCoeff a k u (v + v') =
      normalOrderedSecondCoeff a k u v + normalOrderedSecondCoeff a k u v' := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ m : ℤ, doubleRow a k u (v + v') m w) =
    (∑ᶠ m : ℤ, doubleRow a k u v m w) + ∑ᶠ m : ℤ, doubleRow a k u v' m w
  simp only [doubleRow, map_add, LinearMap.add_apply]
  exact finsum_add_distrib (doubleRow_finite a k u v w) (doubleRow_finite a k u v' w)

private theorem normalOrderedSecondCoeff_smul (a : Charge lattice) (k : ℤ) (u v : Cartan) (c : ℂ) :
    normalOrderedSecondCoeff a k u (c • v) = c • normalOrderedSecondCoeff a k u v := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ m : ℤ, doubleRow a k u (c • v) m w) = c • ∑ᶠ m : ℤ, doubleRow a k u v m w
  simp only [doubleRow, map_smul, LinearMap.smul_apply]
  exact (smul_finsum' c (doubleRow_finite a k u v w)).symm

private def doubleBilinear (a : Charge lattice) (k : ℤ) :
    Cartan →ₗ[ℂ] Cartan →ₗ[ℂ] Module.End ℂ State :=
  LinearMap.mk₂ ℂ (normalOrderedSecondCoeff a k)
    (fun u u' v => by rw [normalOrderedSecondCoeff_swap a k (u + u') v, normalOrderedSecondCoeff_add,
      normalOrderedSecondCoeff_swap a k v u, normalOrderedSecondCoeff_swap a k v u'])
    (fun c u v => by rw [normalOrderedSecondCoeff_swap a k (c • u) v, normalOrderedSecondCoeff_smul,
      normalOrderedSecondCoeff_swap a k v u])
    (normalOrderedSecondCoeff_add a k) (fun c u v => normalOrderedSecondCoeff_smul a k u v c)

private theorem normalOrderedSecondCoeff_below (a : Charge lattice) (u v : Cartan) (w : State) :
    ∃ b : ℤ, ∀ k : ℤ, k < b → normalOrderedSecondCoeff a k u v w = 0 := by
  let bounds := insert (firstLower a v w - 3) <|
    (Finset.Icc (0 : ℤ) (coverBound w : ℤ)).image
      (fun m => firstLower a v (mode u m w) - 3 - m)
  refine ⟨bounds.min' (Finset.insert_nonempty _ _), ?_⟩
  intro k hk
  change (∑ᶠ m : ℤ, doubleRow a k u v m w) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  rw [doubleRow_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [doubleTerm, place_apply]
  by_cases hm : m < 0
  · have hlow : k < firstLower a v w - 3 :=
      hk.trans_le (Finset.min'_le bounds _ (Finset.mem_insert_self _ _))
    rw [if_pos hm, Module.End.mul_apply, firstTerm_zero_below a v w _ n (by omega), map_zero]
  · rw [if_neg hm, Module.End.mul_apply]
    by_cases hb : (coverBound w : ℤ) < m
    · rw [mode_eq_zero_above_coverBound w u m hb, map_zero]
    · have hmem : firstLower a v (mode u m w) - 3 - m ∈ bounds :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
          (Finset.mem_Icc.mpr ⟨le_of_not_gt hm, le_of_not_gt hb⟩))
      have hlow := hk.trans_le (Finset.min'_le bounds _ hmem)
      exact firstTerm_zero_below a v _ _ n (by omega)

private def chargeCorrection (a : Charge lattice) : LinearMap.BilinForm ℂ Cartan :=
  correction + (contraction a).smulRight (contraction a)

private def pairCoeff (a : Charge lattice) (k : ℤ) :
    Cartan →ₗ[ℂ] Cartan →ₗ[ℂ] Module.End ℂ State :=
  let cross := (contraction a).smulRight (normalOrderedCurrentCoeff a (k + 3))
  doubleBilinear a k - cross - cross.flip +
    (chargeCorrection a).compr₂ ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (groundCoeff a (k + 6)))

private theorem pairCoeff_apply (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    pairCoeff a k u v = normalOrderedSecondCoeff a k u v -
      contraction a u • normalOrderedCurrentCoeff a (k + 3) v -
      contraction a v • normalOrderedCurrentCoeff a (k + 3) u +
      (correction u v + contraction a u * contraction a v) • groundCoeff a (k + 6) := by
  simp only [pairCoeff, chargeCorrection, doubleBilinear, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.mk₂_apply, LinearMap.flip_apply, LinearMap.smulRight_apply,
    LinearMap.compr₂_apply, LinearMap.id_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem pairCoeff_swap (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    pairCoeff a k u v = pairCoeff a k v u := by
  rw [pairCoeff_apply, pairCoeff_apply, normalOrderedSecondCoeff_swap a k u v, correction_swap u v,
    mul_comm (contraction a u) (contraction a v)]
  abel

private theorem normalCoeff_zero_below (a : Charge lattice) (k : ℤ) (u : Cartan) (w : State)
    (hk : k < firstLower a u w) : normalOrderedCurrentCoeff a k u w = 0 := by
  change (∑ᶠ m : ℤ, firstTerm a k m u w) = 0
  exact finsum_eq_zero_of_forall_eq_zero (fun m => firstTerm_zero_below a u w k m hk)

private def pairField (a : Charge lattice) (u v : Cartan) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun k => pairCoeff a k u v) (by
    intro w
    obtain ⟨b, hb⟩ := normalOrderedSecondCoeff_below a u v w
    refine ⟨min (min b (firstLower a u w - 3))
      (min (firstLower a v w - 3) (lowerBound a w - 6)), ?_⟩
    intro k hk
    change pairCoeff a k u v w ≠ 0 at hk
    apply le_of_not_gt
    intro h
    have h₁ := h.trans_le (min_le_left _ _)
    have h₂ := h.trans_le (min_le_right _ _)
    apply hk
    simp only [pairCoeff_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      hb k (h₁.trans_le (min_le_left _ _)),
      normalCoeff_zero_below a (k + 3) u w
        (by have := h₁.trans_le (min_le_right _ _); omega),
      normalCoeff_zero_below a (k + 3) v w
        (by have := h₂.trans_le (min_le_left _ _); omega),
      fieldCoeff_eq_zero_below fixedDualBases a w (k + 6)
        (by have := h₂.trans_le (min_le_right _ _); omega),
      smul_zero, sub_zero, add_zero])

private theorem pairField_coeff (a : Charge lattice) (u v : Cartan) (k : ℤ) :
    HVertexOperator.coeff (pairField a u v) k = pairCoeff a k u v := rfl

private def quadraticPart (a : Charge lattice) : Oscillator lattice →ₗ[ℂ] VertexOperator ℂ State :=
  (2 : ℂ)⁻¹ • ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
    (constant.comp ((derivative i).comp (derivative j))).smulRight
      (pairField a (basisDirection i) (basisDirection j))

/-- Extend the existing field by evaluating the second derivatives at the origin
of each actual charge polynomial. This makes the extension linear on the carrier
and intrinsic to the state represented by that polynomial. -/
def stateField : Carrier lattice →ₗ[ℂ] VertexOperator ℂ State :=
  P48qCurrentChargedIterate.stateField + Finsupp.lsum ℂ quadraticPart

theorem stateField_ground (a : Charge lattice) :
    stateField (chargedGround a) = concreteChargedField a := by
  have hd (i : Fin lattice.rank) : derivative i 1 = 0 := pderiv_one
  rw [stateField, LinearMap.add_apply, P48qCurrentChargedIterate.stateField_ground,
    chargedGround, Finsupp.lsum_single]
  simp only [quadraticPart, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, hd, map_zero, zero_smul, smul_zero,
    Finset.sum_const_zero, add_zero]

theorem stateField_first (a : Charge lattice) (u : Cartan) :
    stateField (chargedFirst a u) = P48qCurrentChargedIterate.stateField (chargedFirst a u) := by
  rw [stateField, LinearMap.add_apply, chargedFirst, Finsupp.lsum_single]
  simp only [quadraticPart, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, derivative_current, derivative_C, map_zero,
    zero_smul, smul_zero, Finset.sum_const_zero, add_zero]

private theorem pairCoeff_sum (a : Charge lattice) (k : ℤ) (u v : Cartan) :
    pairCoeff a k u v = ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
      (u i * v j) • pairCoeff a k (basisDirection i) (basisDirection j) := by
  calc
    _ = ∑ i : Fin lattice.rank, u i • pairCoeff a k (basisDirection i) v := by
      conv_lhs => rw [← sum_basisDirection u]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hv : pairCoeff a k (basisDirection i) v =
          ∑ j : Fin lattice.rank, v j • pairCoeff a k (basisDirection i) (basisDirection j) := by
        conv_lhs => rw [← sum_basisDirection v]
        simp only [map_sum, map_smul]
      simp only [hv, Finset.smul_sum, smul_smul]

private theorem previousField_second (a : Charge lattice) (u v : Cartan) :
    P48qCurrentChargedIterate.stateField (chargedSecond a u v) = 0 := by
  have hconst : constant (currentPolynomial u * currentPolynomial v) = 0 := by
    rw [constant_mul, constant_current, constant_current, mul_zero]
  have hlinear (i : Fin lattice.rank) :
      constant (derivative i (currentPolynomial u * currentPolynomial v)) = 0 := by
    rw [derivative_mul, map_add, constant_mul, constant_mul, constant_current, constant_current,
      mul_zero, zero_mul, add_zero]
  simp only [P48qCurrentChargedIterate.stateField, chargedSecond, Finsupp.lsum_single,
    P48qCurrentChargedIterate.polynomialField, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.smulRight_apply, hconst, hlinear, zero_smul, zero_add,
    Finset.sum_const_zero]

private theorem stateField_second_pairCoeff (a : Charge lattice) (u v : Cartan) (k : ℤ) :
    HVertexOperator.coeff (stateField (chargedSecond a u v)) k = pairCoeff a k u v := by
  have hquad (i j : Fin lattice.rank) :
      constant (derivative i (derivative j (currentPolynomial u * currentPolynomial v))) =
        u i * v j + v i * u j := by
    simp only [derivative_mul, derivative_current, map_add, derivative_C, zero_mul, mul_zero,
      zero_add, add_zero, constant_mul, constant_C] <;> ring
  rw [stateField, LinearMap.add_apply, previousField_second, zero_add, chargedSecond,
    Finsupp.lsum_single]
  simp only [quadraticPart, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, hquad, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply,
    pairField_coeff, add_smul, Finset.sum_add_distrib]
  change (2 : ℂ)⁻¹ •
    ((∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
      (u i * v j) • pairCoeff a k (basisDirection i) (basisDirection j)) +
      ∑ i : Fin lattice.rank, ∑ j : Fin lattice.rank,
        (v i * u j) • pairCoeff a k (basisDirection i) (basisDirection j)) = _
  rw [← pairCoeff_sum a k u v, ← pairCoeff_sum a k v u, pairCoeff_swap a k v u,
    ← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- Full charged quadratic coefficient. The two single contractions each use
one copy of the one-current normal order. The coefficient at the ground shift
contains the product of the two charge contractions and the symmetric diagonal. -/
theorem stateField_second_coeff (a : Charge lattice) (u v : Cartan) (k : ℤ) :
    HVertexOperator.coeff (stateField (chargedSecond a u v)) k =
      normalOrderedSecondCoeff a k u v -
      contraction a u • normalOrderedCurrentCoeff a (k + 3) v -
      contraction a v • normalOrderedCurrentCoeff a (k + 3) u +
      (correction u v + contraction a u * contraction a v) • fieldCoeff fixedDualBases a (k + 6) := by
  rw [stateField_second_pairCoeff, pairCoeff_apply]

private theorem contraction_at_zero (u : Cartan) : contraction 0 u = 0 := by
  simp only [P48qCurrentChargedIterate.contraction_apply, chargeVector_zero, map_zero,
    mul_zero, add_zero]

private theorem normalOrderedSecondCoeff_zero_charge (k : ℤ) (u v : Cartan) :
    normalOrderedSecondCoeff 0 k u v = P48qQuadraticStateField.orderedMode (-k - 6) u v := by
  have hfirst (e : ℤ) : normalOrderedCurrentCoeff 0 e v = mode v (-e - 3) := by
    have hv : chargedFirst 0 v = currentAlong lattice v :=
      (currentAlong_eq_polynomial v).symm
    have h := P48qCurrentChargedIterate.stateField_first_coeff 0 v e
    rw [contraction_at_zero, zero_smul, sub_zero] at h
    rw [← h, hv, P48qCurrentChargedIterate.stateField_current,
      P48qTwistedHeisenberg.currentField_coeff]
  apply LinearMap.ext
  intro w
  change (∑ᶠ m : ℤ, doubleRow 0 k u v m w) =
    ∑ᶠ m : ℤ, P48qQuadraticStateField.orderedTerm (-k - 6) u v m w
  apply finsum_congr
  intro m
  simp only [doubleRow, hfirst, place_apply, P48qQuadraticStateField.orderedTerm,
    normalOrderedTerm, show -(k + 3 + m) - 3 = -k - 6 - m by omega]

/-- At charge zero this is the previously constructed field of the neutral
current pair. -/
theorem stateField_zero_second (u v : Cartan) :
    stateField (chargedSecond 0 u v) =
      P48qQuadraticStateField.neutralStateField (P48qQuadraticStateField.currentProduct u v 0) := by
  apply HVertexOperator.coeff_inj
  funext k
  have h := P48qQuadraticStateField.neutralStateField_pair_coeff u v (-k - 6)
  rw [show -(-k - 6) - 6 = k by omega] at h
  rw [stateField_second_coeff, h]
  simp only [contraction_at_zero, zero_smul, sub_zero, zero_mul, add_zero,
    normalOrderedSecondCoeff_zero_charge]
  have he := P48qTwistedGeneratorVacuum.concreteChargedField_zero_coeff (k + 6)
  change fieldCoeff fixedDualBases 0 (k + 6) = _ at he
  rw [he]
  by_cases hk : k + 6 = 0
  · rw [if_pos hk, if_pos (by omega : -k - 6 = 0)] <;> rfl
  · rw [if_neg hk, if_neg (by omega : -k - 6 ≠ 0), smul_zero]

private def orderedFirstTerm (a : Charge lattice) (k : ℤ) (u v : Cartan) (m : ℤ) :
    Module.End ℂ State :=
  place u m (HVertexOperator.coeff
    (P48qCurrentChargedIterate.stateField (chargedFirst a v)) (k + 3 + m))

private theorem orderedFirstTerm_apply (a : Charge lattice) (k : ℤ) (u v : Cartan)
    (m : ℤ) (w : State) :
    orderedFirstTerm a k u v m w =
      doubleRow a k u v m w - contraction a v • firstTerm a (k + 3) m u w := by
  rw [orderedFirstTerm, P48qCurrentChargedIterate.stateField_first_coeff, map_sub, map_smul,
    show k + 3 + m + 3 = (k + 3) + 3 + m by omega, ← firstTerm_eq_place] <;> rfl

private theorem orderedFirst_on_residue (a : Charge lattice) (u v : Cartan) (r : ℕ)
    (hr : r < 3) (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k : ℤ) (w : State) :
    (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, orderedFirstTerm a k u v m w) =
      normalOrderedSecondCoeff a k u v w - contraction a v • normalOrderedCurrentCoeff a (k + 3) u w := by
  let f (m : ℤ) := orderedFirstTerm a k u v m w
  have hfirst := orderedTerm_finite a u (k + 3) w
  have hscaled : Function.HasFiniteSupport
      (fun m => contraction a v • firstTerm a (k + 3) m u w) :=
    hfirst.fun_comp (smul_zero (contraction a v))
  have hf : Function.HasFiniteSupport f := by
    have heq : f =
        (fun m => doubleRow a k u v m w) -
          (fun m => contraction a v • firstTerm a (k + 3) m u w) :=
      funext fun m => orderedFirstTerm_apply a k u v m w
    rw [heq]
    exact (doubleRow_finite a k u v w).sub hscaled
  have hr' : Function.support f ⊆ {m : ℤ | m % 3 = (r : ℤ)} := by
    intro m hm
    by_contra hoff
    change m % 3 ≠ (r : ℤ) at hoff
    have hz : mode u m = 0 := by
      rw [← mode_projectAt u m, projectAt_off_residue u r hr hu m hoff]
      exact (modeLinear m).map_zero
    apply hm
    change orderedFirstTerm a k u v m w = 0
    simp only [orderedFirstTerm, place_apply, hz, zero_mul, mul_zero, ite_self, LinearMap.zero_apply]
  have hfull : (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, f m) = ∑ᶠ m : ℤ, f m := by
    have hI : Function.support f ⊆ (hf.toFinset : Set ℤ) := by
      exact hf.coe_toFinset.ge
    rw [finsum_eq_sum_of_support_subset f hI]
    apply finsum_mem_eq_sum_of_inter_support_eq
    rw [Set.inter_eq_right.mpr hr', Set.inter_eq_right.mpr hI]
  change (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)}, f m) = _
  rw [hfull]
  simp only [f, orderedFirstTerm_apply]
  rw [finsum_sub_distrib (doubleRow_finite a k u v w) hscaled, ← smul_finsum' _ hfirst] <;> rfl

/-- BK (3.13) at product index -1, on the actual source state v(-1)e^a.
The positive source indices in the iterate are precisely the possible
contributions at j = 1 and j = 2. All exponents are cover exponents. -/
theorem current_second_BK_iterate (a : Charge lattice) (u v : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (k : ℤ) (w : State) :
    (∑ᶠ m ∈ {m : ℤ | m % 3 = (r : ℤ)},
      normalOrderedTerm (mode u)
        (fun l => HVertexOperator.coeff (stateField (chargedFirst a v)) (-l - 3)) (-k - 6) m w) =
      ∑ᶠ j : ℕ, Ring.choose ((r : ℂ) / 3) j • HVertexOperator.coeff
        (stateField (mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (chargedFirst a v)))
        (k + 3 * (j : ℤ)) w := by
  let term (j : ℕ) := Ring.choose ((r : ℂ) / 3) j • HVertexOperator.coeff
    (stateField (mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (chargedFirst a v)))
    (k + 3 * (j : ℤ)) w
  have hterm : Function.support term ⊆ (↑({0, 1, 2} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra hout
    have h0 : j ≠ 0 := fun h => hout (by simp [h])
    have h1 : j ≠ 1 := fun h => hout (by simp [h])
    have h2 : j ≠ 2 := fun h => hout (by simp [h])
    apply hj
    simp only [term, source_product_nonneg a u v _ (by omega : 0 ≤ (j : ℤ) - 1),
      if_neg (by omega : (j : ℤ) - 1 ≠ 0), if_neg (by omega : (j : ℤ) - 1 ≠ 1),
      map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have h0 : term 0 = pairCoeff a k u v w := by
    simp only [term, Nat.cast_zero, zero_sub, mul_zero, add_zero, Ring.choose_zero_right,
      one_smul, source_product_second, stateField_second_pairCoeff]
  have h1 : term 1 = contraction a u •
      (normalOrderedCurrentCoeff a (k + 3) v w -
        contraction a v • groundCoeff a (k + 6) w) := by
    simp only [term, Nat.cast_one, sub_self, mul_one, Ring.choose_one_right,
      source_product_nonneg a u v 0 le_rfl, ite_true,
      map_smul, Pi.smul_apply,
      LinearMap.smul_apply, stateField_first, P48qCurrentChargedIterate.stateField_first_coeff,
      LinearMap.sub_apply, smul_smul, contraction_on_residue a u r hr hu,
      show k + 3 + 3 = k + 6 by omega]
  have h2 : term 2 = (-correction u v) • groundCoeff a (k + 6) w := by
    have hground (e : ℤ) :
        HVertexOperator.coeff (concreteChargedField a) e = groundCoeff a e := rfl
    simp only [term, show ((2 : ℕ) : ℤ) - 1 = 1 by decide,
      show k + 3 * ((2 : ℕ) : ℤ) = k + 6 by omega,
      source_product_nonneg a u v 1 (by decide), ite_eq_right (by decide : (1 : ℤ) ≠ 0),
      ite_true,
      map_smul, Pi.smul_apply, LinearMap.smul_apply, stateField_ground, hground,
      smul_smul, correction_on_residue u v r hr hu, neg_neg]
  have horder (m : ℤ) :
      normalOrderedTerm (mode u)
          (fun l => HVertexOperator.coeff (stateField (chargedFirst a v)) (-l - 3))
          (-k - 6) m =
        orderedFirstTerm a k u v m := by
    simp only [normalOrderedTerm, orderedFirstTerm, stateField_first, place_apply,
      show -(-k - 6 - m) - 3 = k + 3 + m by omega]
  simp only [horder]
  change _ = ∑ᶠ j, term j
  rw [orderedFirst_on_residue a u v r hr hu, finsum_eq_sum_of_support_subset term hterm,
    Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1, 2} : Finset ℕ)),
    Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), h0, h1, h2, pairCoeff_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, add_smul,
    smul_sub, ← smul_smul, neg_smul]
  abel

#print axioms source_product_nonneg
#print axioms chargedSecond
#print axioms chargedSecond_swap
#print axioms source_product_second
#print axioms normalOrderedSecondCoeff
#print axioms normalOrderedSecondCoeff_swap
#print axioms stateField
#print axioms stateField_ground
#print axioms stateField_first
#print axioms stateField_second_coeff
#print axioms stateField_zero_second
#print axioms current_second_BK_iterate

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedTwoCurrentIterate
