/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddZhuTopBalance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddZhuTopBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zhu residues of the actual parity-changing mixed coefficients on the literal twisted tops. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
import D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.LatticeActualAnnihilation

/-!
Frenkel–Zhu balancing, in the setting of Abe (arXiv:math/9907120v1,
§2 and §4.2). Here all three residues are specializations of the native
signed coefficient identity. The mode convention is that of
`NativeOddTwistedIntertwiner`.
-/

set_option autoImplicit false

open scoped BigOperators DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockGradedTrace
open HalfFock.LatticeHalfFockParityField (paritySpace)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open StateFieldResidueReconstruction (integerBinomial)
open ActualLeechHyperbolic (leechData)
open private antisymmetrize from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
open private abeState_grade from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
open private theta_gradeProjection ambientGradeReadout_self lowering_kills_top topReadout_raising_zero
    fixedAction_equal_degree_top from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance twistedTopAddCommGroup (D : LatticeData) (hu : IsUnit D.G.det) (t : Bool) :
    AddCommGroup (twistedTop D hu t) :=
  @Submodule.addCommGroup ℂ (Twisted D hu t) _ _ _ (twistedTop D hu t)

private def oddPart (D : LatticeData) : Carrier D →ₗ[ℂ] OddCarrier D :=
  (2 : ℂ)⁻¹ • antisymmetrize D

private theorem oddPart_grade (h : ℤ) (x : grade D h) :
    (oddPart D x.val).val ∈ grade D h := by
  have hx : theta D x.val ∈ grade D h := by
    have he : theta D x.val = gradeProjection D h (theta D x.val) :=
      (congrArg (theta D) (gradeProjection_eq_self_of_mem_grade D h x.val x.property).symm).trans
        (theta_gradeProjection h x.val)
    exact he.symm ▸ gradeProjection_mem D h (theta D x.val)
  change (2 : ℂ)⁻¹ • (x.val - theta D x.val) ∈ grade D h
  exact (grade D h).smul_mem _ ((grade D h).sub_mem x.property hx)

private theorem oddPart_on_odd (b : OddCarrier D) : oddPart D b.val = b := by
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • (b.val - theta D b.val) = b.val
  rw [(mem_eigenspace D (-1) b.val).mp b.property, neg_one_smul, sub_neg_eq_add,
    ← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

private theorem selected_mode_mem_top (F : LawfulMixedField D hu s) (h : ℤ)
    (b : OddCarrier D) (hb : b.val ∈ grade D h) (v : twistedTop D hu s) :
    F.coeff (twistedTopZhuIndex s h) b v.val ∈ twistedTop D hu (!s) := by
  have he := lawfulMixed_signed_grade F (twistedTopZhuIndex s h) h
    (twistedTopGrade s) b v.val hb v.property
  have hi : (twistedTopGrade s : ℤ) + 2*h - 2*twistedTopZhuIndex s h - 3 =
      (twistedTopGrade (!s) : ℤ) := by
    cases s <;> simp [twistedTopGrade, twistedTopZhuIndex] <;> omega
  simpa only [twistedTop, Submodule.mem_comap, actualGrade, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
    Submodule.subtype_apply, hi, Int.cast_natCast] using he

private def homogeneousTopEvaluation (F : LawfulMixedField D hu s) (v : twistedTop D hu s)
    (h : ℤ) : grade D h →ₗ[ℂ] twistedTop D hu (!s) :=
  LinearMap.codRestrict _ (((LinearMap.applyₗ v.val).comp (F.coeff (twistedTopZhuIndex s h))).comp
      ((oddPart D).comp (grade D h).subtype))
    (fun b => selected_mode_mem_top F h (oddPart D b.val) (oddPart_grade h b) v)

/-- The degree-wise selected coefficient, extended linearly over the actual energy direct sum. -/
def zhuTopEvaluation (F : LawfulMixedField D hu s) (v : twistedTop D hu s) :
    OddCarrier D →ₗ[ℂ] twistedTop D hu (!s) :=
  (DirectSum.toModule ℂ ℤ (twistedTop D hu (!s)) (homogeneousTopEvaluation F v)).comp
    ((carrierEnergyDecomposition D).toLinearMap.comp (minusSpace D).subtype)

/-- This is the same homogeneous coefficient used by the top detector. -/
theorem zhuTopEvaluation_homogeneous (F : LawfulMixedField D hu s) (v : twistedTop D hu s)
    (h : ℤ) (b : OddCarrier D) (hb : b.val ∈ grade D h) :
    (zhuTopEvaluation F v b).val = F.coeff (twistedTopZhuIndex s h) b v.val := by
  have he : carrierEnergyDecomposition D b.val =
      DirectSum.lof ℂ ℤ (fun n => grade D n) h ⟨b.val, hb⟩ := by
    apply (carrierEnergyDecomposition D).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change b.val = DirectSum.coeLinearMap (grade D) (DirectSum.lof ℂ ℤ (fun n => grade D n) h ⟨b.val, hb⟩)
    rw [DirectSum.coeLinearMap_lof]
  change (DirectSum.toModule ℂ ℤ (twistedTop D hu (!s)) (homogeneousTopEvaluation F v)
    (carrierEnergyDecomposition D b.val)).val = _
  rw [he, DirectSum.toModule_lof]
  change F.coeff (twistedTopZhuIndex s h) (oddPart D b.val) v.val = _
  rw [oddPart_on_odd]

/-- Fixed zero mode on the literal twisted top. -/
def fixedTopZero (t : Bool) (a : FixedCarrier D) (d : ℕ)
    (ha : a.val ∈ grade D (d : ℤ)) : Module.End ℂ (twistedTop D hu t) :=
  LinearMap.codRestrict _ ((fixedAction t a ((d : ℤ)-1)).comp (twistedTop D hu t).subtype)
    (fun v => fixedAction_equal_degree_top a (d : ℤ) _ ha rfl v.val v.property)

private theorem readout_on_top (t : Bool) (v : twistedTop D hu t) :
    twistedTopReadout D hu t v.val = v.val.val :=
  ambientGradeReadout_self _ _ v.property

/-- The exact fixed-mode products in the mixed Zhu residues. -/
def oddZhuResidue (a : FixedCarrier D) (b : OddCarrier D) (p r : ℤ) : OddCarrier D :=
  ∑ᶠ i : ℕ, integerBinomial p i • oddMode D a (r+i) b

private theorem oddResidue_finite (a : FixedCarrier D) (b : OddCarrier D) (p r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ => integerBinomial p i • oddMode D a (r+i) b) := by
  let A := Y D a.val
  let order := ((HahnModule.of ℂ).symm (A b.val)).order
  refine (Set.finite_lt_nat ((-order-r).toNat)).subset ?_
  intro i hi
  change i < (-order-r).toNat
  by_contra hn
  have hbound : -order-r ≤ (i : ℤ) := by omega
  have hz : oddMode D a (r+i) b = 0 := by
    apply Subtype.ext
    change (A[[(r+i)]]) b.val = 0
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    change -(r+(i : ℤ))-1 < order
    omega
  exact hi (by simp [hz])

/-- Project the signed Jacobi identity in the range where the ordered products can
contribute only their term at index zero. The sign in front of the input action
is `-ε(r)`. -/
theorem zhuTopEvaluation_residue (F : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : twistedTop D hu s)
    (d : ℕ) (h p r : ℤ) (ha : a.val ∈ grade D (d : ℤ)) (hb : b.val ∈ grade D h)
    (hp : (d : ℤ)-1 ≤ p) (hr : p+r ≤ (d : ℤ)-1) :
    zhuTopEvaluation F v (oddZhuResidue a b p r) =
      ((if p+r = (d : ℤ)-1 then fixedTopZero (!s) a d ha (zhuTopEvaluation F v b) else 0) -
        (if p = (d : ℤ)-1 then StateFieldResidueReconstruction.epsilon r •
          zhuTopEvaluation F (fixedTopZero s a d ha v) b else 0) : twistedTop D hu (!s)) := by
  classical
  let k := twistedTopZhuIndex s h
  let q := k+(d : ℤ)-p-r-1
  let P := twistedTopReadout D hu (!s)
  let A := (paritySpace D hu (paritySign (!s))).subtype.comp (twistedTop D hu (!s)).subtype
  let left (i : ℕ) := integerBinomial p i • F.coeff (p+q-i) (oddMode D a (r+i) b) v.val
  let first (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) •
    fixedAction (!s) a (p+r-i) (F.coeff (q+i) b v.val)
  let second (i : ℕ) := (((-1 : ℂ)^i)*integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • F.coeff (q+r-i) b (fixedAction s a (p+i) v.val))
  have law := F.borcherds a b v.val p q r
  change Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
    Function.HasFiniteSupport second ∧
      (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i) at law
  have hj := congrArg P law.2.2.2
  change P (∑ᶠ i, left i) = P ((∑ᶠ i, first i) - (∑ᶠ i, second i)) at hj
  rw [map_sub P, map_finsum P law.1, map_finsum P law.2.1, map_finsum P law.2.2.1] at hj
  have hleft :
      A (zhuTopEvaluation F v (oddZhuResidue a b p r)) = ∑ᶠ i, P (left i) := by
    change (A.comp (zhuTopEvaluation F v)) (oddZhuResidue a b p r) = _
    rw [oddZhuResidue, map_finsum _ (oddResidue_finite a b p r)]
    congr 1
    funext i
    let w := (d : ℤ)+h-(r+i)-1
    have hg : (oddMode D a (r+i) b).val ∈ grade D w :=
      actual_mode_grade D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) (d : ℤ) h (r+i) a.val b.val ha hb
    have hi : twistedTopZhuIndex s w = p+q-i := by
      cases s <;> simp [w, q, k, twistedTopZhuIndex] <;> omega
    simp only [left, map_smul, LinearMap.comp_apply]
    congr 1
    rw [show A (zhuTopEvaluation F v (oddMode D a (r+i) b)) =
        P (zhuTopEvaluation F v (oddMode D a (r+i) b)).val from (readout_on_top _ _).symm,
      zhuTopEvaluation_homogeneous F v w _ hg, hi]
  have hfirst : (∑ᶠ i, P (first i)) = A
      (if p+r = (d : ℤ)-1 then fixedTopZero (!s) a d ha (zhuTopEvaluation F v b) else 0) := by
    rw [finsum_eq_single _ 0]
    · by_cases he : p+r = (d : ℤ)-1
      · have hq : q = k := by dsimp [q]; omega
        rw [ite_eq_left he]
        let u := zhuTopEvaluation F v b
        let weightZero := (d : ℤ) - 1
        have hfirst0 : first 0 = fixedAction (!s) a weightZero (F.coeff k b v.val) := by
          simp only [first, Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul,
            integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul, hq, he, weightZero]
        have huval : u.val = F.coeff k b v.val := zhuTopEvaluation_homogeneous F v h b hb
        rw [hfirst0, ← huval]
        exact readout_on_top (!s) (fixedTopZero (!s) a d ha u)
      · rw [ite_eq_right he, map_zero]
        simp only [first, Nat.cast_zero, sub_zero, add_zero, map_smul]
        rw [topReadout_raising_zero a (d : ℤ) _ ha (by omega), smul_zero]
    · intro i hi
      simp only [first, map_smul]
      rw [topReadout_raising_zero a (d : ℤ) _ ha (by omega), smul_zero]
  have hsecond : (∑ᶠ i, P (second i)) = A
      (if p = (d : ℤ)-1 then StateFieldResidueReconstruction.epsilon r •
        zhuTopEvaluation F (fixedTopZero s a d ha v) b else 0) := by
    rw [finsum_eq_single _ 0]
    · by_cases he : p = (d : ℤ)-1
      · have hq : q+r = k := by dsimp [q]; omega
        rw [ite_eq_left he]
        let u := fixedTopZero s a d ha v
        have hsecond0 : second 0 = StateFieldResidueReconstruction.epsilon r • F.coeff k b u.val := by
          simp only [second, Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul,
            integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul, hq, he]
          rfl
        have huz : (zhuTopEvaluation F u b).val = F.coeff k b u.val :=
          zhuTopEvaluation_homogeneous F u h b hb
        rw [hsecond0, map_smul P, map_smul A, ← huz]
        exact congrArg (fun w : ActualTensor D hu => StateFieldResidueReconstruction.epsilon r • w)
          (readout_on_top (!s) (zhuTopEvaluation F u b))
      · rw [ite_eq_right he, map_zero]
        simp only [second, Nat.cast_zero, sub_zero, add_zero]
        rw [lowering_kills_top a (d : ℤ) p ha (by omega) v.val v.property]
        simp
    · intro i hi
      simp only [second]
      rw [lowering_kills_top a (d : ℤ) (p+i) ha (by omega) v.val v.property]
      simp
  have hinj : Function.Injective A := fun _ _ e => Subtype.ext (Subtype.ext e)
  apply hinj
  rw [map_sub A, hleft, hj, hfirst, hsecond]

/-- The two star actions and the circle relation for the actual odd source.
The three choices of `(p,r)` are `(d,-1)`, `(d-1,-1)`, and `(d,-2)`. -/
theorem zhuTopEvaluation_balanced (F : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : twistedTop D hu s)
    (d : ℕ) (h : ℤ) (ha : a.val ∈ grade D (d : ℤ)) (hb : b.val ∈ grade D h) :
    zhuTopEvaluation F v (oddZhuResidue a b d (-1)) =
        fixedTopZero (!s) a d ha (zhuTopEvaluation F v b) ∧
    zhuTopEvaluation F v (oddZhuResidue a b ((d : ℤ)-1) (-1)) =
        zhuTopEvaluation F (fixedTopZero s a d ha v) b ∧
    zhuTopEvaluation F v (oddZhuResidue a b d (-2)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [zhuTopEvaluation_residue F a b v d h d (-1) ha hb (by omega) (by omega),
      ite_eq_left (show (d : ℤ) + (-1) = (d : ℤ) - 1 by omega),
      ite_eq_right (show (d : ℤ) ≠ (d : ℤ) - 1 by omega)]
    exact sub_zero (fixedTopZero (!s) a d ha (zhuTopEvaluation F v b))
  · rw [zhuTopEvaluation_residue F a b v d h ((d : ℤ)-1) (-1) ha hb (by omega) (by omega),
      ite_eq_right (show (d : ℤ) - 1 + (-1) ≠ (d : ℤ) - 1 by omega), ite_eq_left rfl]
    have heps : StateFieldResidueReconstruction.epsilon (-1) = -1 := by
      norm_num [StateFieldResidueReconstruction.epsilon]
    rw [heps]
    let u := zhuTopEvaluation F (fixedTopZero s a d ha v) b
    change 0 - (-1 : ℂ) • u = u
    rw [neg_one_smul ℂ u, zero_sub (-u), neg_neg]
  · rw [zhuTopEvaluation_residue F a b v d h d (-2) ha hb (by omega) (by omega),
      ite_eq_right (show (d : ℤ) + (-2) ≠ (d : ℤ) - 1 by omega),
      ite_eq_right (show (d : ℤ) ≠ (d : ℤ) - 1 by omega)]
    exact sub_self (0 : twistedTop D hu (!s))

private theorem oddResidue_nat (a : FixedCarrier D) (b : OddCarrier D) (d : ℕ) (r : ℤ) :
    oddZhuResidue a b (d : ℤ) r =
      ∑ i ∈ Finset.range (d+1), (d.choose i : ℂ) • oddMode D a (r+i) b := by
  unfold oddZhuResidue
  simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra! hout
  exact hi (by simp [Nat.choose_eq_zero_of_lt (by omega : d < i)])

/-- The left residue is the existing Zhu star on the original carrier. -/
theorem oddZhuResidue_star_val (a : FixedCarrier D) (b : OddCarrier D) (d : ℕ)
    (ha : a.val ∈ grade D (d : ℤ)) :
    (oddZhuResidue a b d (-1)).val = Lattice.ActualZhuProduct.star D a.val b.val := by
  rw [oddResidue_nat, Lattice.ActualZhuProduct.star_homogeneous D d a.val b.val ha]
  change (minusSpace D).subtype (∑ i ∈ Finset.range (d+1),
    (d.choose i : ℂ) • oddMode D a (-1+i) b) = _
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [show (-1 : ℤ)+(i : ℤ) = (i : ℤ)-1 by omega]; rfl)

/-- The pole-two residue is the existing circle generator on the original carrier. -/
theorem oddZhuResidue_circle_val (a : FixedCarrier D) (b : OddCarrier D) (d : ℕ) :
    (oddZhuResidue a b d (-2)).val = Lattice.NormFourZhuFinite.circle D d a.val b.val := by
  rw [oddResidue_nat, Lattice.NormFourZhuFinite.circle]
  change (minusSpace D).subtype (∑ i ∈ Finset.range (d+1),
    (d.choose i : ℂ) • oddMode D a (-2+i) b) = _
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [show (-2 : ℤ)+(i : ℤ) = (i : ℤ)-2 by omega]; rfl)

private theorem exists_single_charge_zero (x : Carrier D)
    (hx : x ∈ Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))) :
    ∃ p : Oscillator D, x = Finsupp.single 0 p := by
  refine ⟨x 0, Finsupp.ext fun c => ?_⟩
  by_cases hc : c = 0
  · subst c
    rw [Finsupp.single_eq_same]
  · rw [(Finsupp.mem_supported' ℂ x).mp hx c (by simpa using hc),
      Finsupp.single_eq_of_ne hc]

/-- Actual source products by a charge-zero fixed state preserve the neutral odd source. -/
theorem oddMode_mem_chargeZero (a : FixedCarrier D) (b : OddCarrier D) (n : ℤ)
    (ha : a.val ∈ Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D)))
    (hb : b ∈ chargeZeroOdd D) : oddMode D a n b ∈ chargeZeroOdd D := by
  obtain ⟨pa, hpa⟩ := exists_single_charge_zero a.val ha
  obtain ⟨pb, hpb⟩ := exists_single_charge_zero b.val hb
  change ((Y D a.val)[[n]]) b.val ∈ Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))
  rw [hpa, hpb]
  have hm := LatticeSectorIntertwiner.charge_homogeneity D 0 0 pa pb n
  rw [zero_add] at hm
  rw [hm]
  exact Finsupp.single_mem_supported ℂ _ (by simp)

theorem oddZhuResidue_mem_chargeZero (a : FixedCarrier D) (b : OddCarrier D) (p r : ℤ)
    (ha : a.val ∈ Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D)))
    (hb : b ∈ chargeZeroOdd D) : oddZhuResidue a b p r ∈ chargeZeroOdd D := by
  unfold oddZhuResidue
  apply finsum_induction _ (chargeZeroOdd D).zero_mem
    (fun _ _ => (chargeZeroOdd D).add_mem)
  intro i
  exact (chargeZeroOdd D).smul_mem _ (oddMode_mem_chargeZero a b (r+i) ha hb)

/-- Evaluation of the actual charge-zero restriction at the selected mode. -/
theorem zhuTopEvaluation_chargeZero (F : LawfulMixedField D hu s) (v : twistedTop D hu s)
    (h : ℤ) (b : chargeZeroOdd D) (hb : b.val.val ∈ grade D h) :
    (zhuTopEvaluation F v b.val).val =
      restrictChargeZero D hu s F (twistedTopZhuIndex s h) b v.val :=
  zhuTopEvaluation_homogeneous F v h b.val hb

/-- The full top evaluation has the same detection strength as the homogeneous readout. -/
theorem leech_zhuTopEvaluation_injective (s : Bool) :
    Function.Injective (zhuTopEvaluation (D := leechData) (hu := leechUnit) (s := s)) := by
  intro F G he
  apply leech_twistedZhuTopReadout_injective s
  funext h b v
  have hv := congrArg (fun x : twistedTop leechData leechUnit (!s) => x.val)
    (LinearMap.congr_fun (congrFun he v) b.val)
  rw [zhuTopEvaluation_homogeneous F v h b.val b.property,
    zhuTopEvaluation_homogeneous G v h b.val b.property] at hv
  exact congrArg (twistedTopReadout leechData leechUnit (!s)) hv

local notation "R₁" => Lattice.ActualZhuRankOneOdd.datum
local notation "A₁" => Lattice.ActualZhuRankOneOdd.abeState
local notation "b₁" => Lattice.ActualZhuRankOneOdd.oddCurrent
local notation "ℒ" => leechData

open Lattice.ActualZhuRankOneOdd (L abe_zhu_identity) in
/-- Abe (4.2) in the balanced matrix element. The five hypotheses in the mode
row are the precise untwisted rank-one transport needed for this comparison. -/
theorem leech_zhuTopEvaluation_abe_of_mode_transport
    (F : LawfulMixedField leechData leechUnit s) (v : twistedTop leechData leechUnit s)
    (transport : Carrier R₁ →ₗ[ℂ] chargeZeroOdd leechData) (a : FixedCarrier leechData)
    (ha : a.val ∈ grade leechData 4) (hb : (transport b₁).val.val ∈ grade leechData 1)
    (hmode : ∀ i ∈ Finset.range 5,
      (transport (mu R₁ A₁ ((i : ℤ)-1) b₁)).val =
        oddMode leechData a ((i : ℤ)-1) (transport b₁).val) :
    let Z := (zhuTopEvaluation F v).comp ((chargeZeroOdd leechData).subtype.comp transport)
    fixedTopZero (!s) a 4 ha (Z b₁) =
      Z ((3 : ℂ) • b₁ + (12 : ℂ) • L (-1) b₁ +
        (12 : ℂ) • L (-1) (L (-1) b₁) - (8 : ℂ) • L (-3) b₁ +
        (16 : ℂ) • L (-2) (L (-1) b₁) - (1 / 2 : ℂ) • L (-4) b₁ +
        (1 / 4 : ℂ) • L (-3) (L (-1) b₁) +
        (3 / 2 : ℂ) • L (-2) (L (-1) (L (-1) b₁))) := by
  let b := (transport b₁).val
  let T := (chargeZeroOdd leechData).subtype.comp transport
  have hrow : T (Lattice.ActualZhuProduct.star R₁ A₁ b₁) =
      oddZhuResidue a b 4 (-1) := by
    change _ = oddZhuResidue a b ((4 : ℕ) : ℤ) (-1)
    rw [Lattice.ActualZhuProduct.star_homogeneous R₁ 4 A₁ b₁ abeState_grade,
      oddResidue_nat a b 4 (-1)]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (-1 : ℤ)+(i : ℤ) = (i : ℤ)-1 by omega]
    exact congrArg (fun x : OddCarrier leechData => (Nat.choose 4 i : ℂ) • x)
      (hmode i hi)
  change fixedTopZero (!s) a 4 ha (zhuTopEvaluation F v b) = _
  rw [← abe_zhu_identity]
  change _ = zhuTopEvaluation F v (T (Lattice.ActualZhuProduct.star R₁ A₁ b₁))
  rw [hrow]
  exact (zhuTopEvaluation_balanced F a b v 4 1 ha hb).1.symm

section RankOneTransport

open MvPolynomial FieldNormalProduct LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeActualAnnihilation
open private multiplication_recursion from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField
open private abeState_eq oddCurrent_eq normalization lift x
  from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd

local instance rankOneRankNeZero : NeZero (R₁).rank := ⟨by decide⟩

/-- The real multiple of the actual Leech coordinate vector with Gram norm two. -/
def leechRankOneScale (i : Fin (ℒ).rank) : ℝ :=
  Real.sqrt (2 / ((ℒ).G i i : ℝ))

private theorem leechRankOneScale_sq (i : Fin (ℒ).rank) :
    leechRankOneScale i ^ 2 * ((ℒ).G i i : ℝ) = 2 := by
  have hG : (0 : ℝ) < ((ℒ).G i i : ℝ) :=
    ActualLeechHyperbolic.leech_spec.2.2.1.diag_pos (i := i)
  rw [leechRankOneScale, Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hG.le),
    div_mul_cancel₀ _ hG.ne']

local notation "κ[" i "]" => (Complex.ofReal (leechRankOneScale i))

private theorem leechRankOneScale_contract (i : Fin (ℒ).rank) :
    κ[i] * (κ[i] * ((ℒ).G i i : ℂ)) = 2 := by
  have h := congrArg Complex.ofReal (leechRankOneScale_sq i)
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast,
    Complex.ofReal_ofNat, pow_two, mul_assoc] using h

/-- Send each actual rank-one oscillator to the scaled Leech oscillator of the
same mode number. -/
def leechOscillatorSubstitution (i : Fin (ℒ).rank) :
    Oscillator R₁ →ₐ[ℂ] Oscillator ℒ :=
  aeval (fun j : Index R₁ => κ[i] • X (i, j.2))

local notation "S" => leechOscillatorSubstitution

@[simp] theorem leechOscillatorSubstitution_X (i : Fin (ℒ).rank) (j : Index R₁) :
    S i (X j) = κ[i] • X (i, j.2) :=
  aeval_X _ _

private theorem substitution_smul (i : Fin (ℒ).rank) (z : ℂ) (p : Oscillator R₁) :
    S i (z • p) = z • S i p :=
  (S i).toLinearMap.map_smul z p

/-- Creation is multiplication by the corresponding scaled variable. -/
theorem leechOscillatorSubstitution_mul_X (i : Fin (ℒ).rank) (j : Index R₁)
    (p : Oscillator R₁) :
    S i (X j * p) = (κ[i] • X (i, j.2)) * S i p := by
  rw [map_mul, leechOscillatorSubstitution_X]

/-- A Gram-weighted annihilator intertwines with the same scaling as creation.
The contraction on a variable is the actual diagonal Gram entry times the
square of the scale. -/
theorem leechOscillatorSubstitution_annihilate (i : Fin (ℒ).rank) (j : Fin (R₁).rank)
    (k : ℕ) (p : Oscillator R₁) :
    S i (annihilate R₁ j k p) = κ[i] • annihilate ℒ i k (S i p) := by
  classical
  have hX (u : Index R₁) :
      S i (annihilate R₁ j k (X u)) = κ[i] • annihilate ℒ i k (S i (X u)) := by
    rcases u with ⟨l, r⟩
    rw [leechOscillatorSubstitution_X, map_smul, annihilate_X, annihilate_X]
    by_cases hr : k = r
    · have hG : ((R₁).G j l : ℂ) = 2 := by norm_num [show (R₁).G j l = 2 from rfl]
      simp only [ite_eq_left hr, substitution_smul, map_one, smul_smul,
        leechRankOneScale_contract, hG]
    · simp [hr]
  induction p using MvPolynomial.induction_on with
  | C z =>
    have hC₁ : annihilate R₁ j k (C z) = 0 := by
      simp [annihilate, weightedPartial, Derivation.coeFn_coe]
    have hC₂ : annihilate ℒ i k (C z) = 0 := by
      simp [annihilate, weightedPartial, Derivation.coeFn_coe]
    have hS : S i (C z) = C z := by simp [leechOscillatorSubstitution]
    rw [hC₁, hS, hC₂, map_zero, smul_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add]
  | mul_X p u hp =>
    simp only [annihilate_mul, map_add, map_mul, hp, hX, smul_add,
      smul_mul_assoc, mul_smul_comm]

/-- Intertwine the actual neutral polynomial mode at every signed mode index. -/
theorem leechOscillatorSubstitution_neutralMode (i : Fin (ℒ).rank) (j : Fin (R₁).rank)
    (n : ℤ) (p : Oscillator R₁) :
    S i (neutralPolynomialMode R₁ j 0 n p) =
      κ[i] • neutralPolynomialMode ℒ i 0 n (S i p) := by
  cases n with
  | negSucc n =>
    rw [show Int.negSucc n = -(n : ℤ) - 1 by omega,
      neutralPolynomialMode_negative, neutralPolynomialMode_negative]
    simp only [LinearMap.mulLeft_apply, leechOscillatorSubstitution_mul_X, smul_mul_assoc]
  | ofNat n =>
    cases n with
    | zero => simp [neutralPolynomialMode, bilinear]
    | succ k =>
      change S i (neutralPolynomialMode R₁ j 0 ((k : ℤ) + 1) p) =
        κ[i] • neutralPolynomialMode ℒ i 0 ((k : ℤ) + 1) (S i p)
      rw [neutralPolynomialMode_positive, neutralPolynomialMode_positive]
      simp only [LinearMap.smul_apply, substitution_smul,
        leechOscillatorSubstitution_annihilate, smul_smul, mul_comm (k + 1 : ℂ)]

/-- Mode-number weights and total oscillator degrees are both preserved.
Take `w r = r + 1` for conformal weight or `w r = 1` for total degree. -/
theorem leechOscillatorSubstitution_homogeneous (i : Fin (ℒ).rank) (w : ℕ → ℕ)
    {p : Oscillator R₁} {d : ℕ}
    (hp : IsWeightedHomogeneous (fun j : Index R₁ => w j.2) p d) :
    IsWeightedHomogeneous (fun j : Index ℒ => w j.2) (S i p) d := by
  classical
  refine hp.induction_on (motive := fun p _ =>
    IsWeightedHomogeneous (fun j : Index ℒ => w j.2) (S i p) d) ?_ ?_ ?_
  · rw [map_zero]
    exact isWeightedHomogeneous_zero ℂ _ _
  · intro p q _ _ hp hq
    rw [map_add]
    exact hp.add hq
  · intro e z he
    change IsWeightedHomogeneous _ (aeval (fun j : Index R₁ => κ[i] • X (i, j.2))
      (monomial e z)) d
    rw [aeval_monomial, MvPolynomial.algebraMap_eq]
    have hf (j : Index R₁) :
        IsWeightedHomogeneous (fun u : Index ℒ => w u.2)
          ((κ[i] • X (i, j.2) : Oscillator ℒ) ^ e j) (e j • w j.2) := by
      apply IsWeightedHomogeneous.pow
      rw [MvPolynomial.smul_eq_C_mul]
      exact (isWeightedHomogeneous_X ℂ (fun u : Index ℒ => w u.2) (i, j.2)).C_mul _
    have hprod := IsWeightedHomogeneous.prod e.support
      (fun j : Index R₁ => (κ[i] • X (i, j.2) : Oscillator ℒ) ^ e j)
      (fun j => e j • w j.2) (fun j _ => hf j)
    have hd : (∑ j ∈ e.support, e j • w j.2) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum] using he
    simpa only [Finsupp.prod, hd] using hprod.C_mul z

private theorem substitution_sigma (i : Fin (ℒ).rank) (p : Oscillator R₁) :
    sigma ℒ (S i p) = S i (sigma R₁ p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [leechOscillatorSubstitution, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, hp, leechOscillatorSubstitution_X, sigma_smul, sigma_X,
      map_neg, smul_neg]

private def neutralLift (D : LatticeData) : Oscillator D →ₗ[ℂ] Carrier D :=
  Finsupp.lsingle 0

@[simp] private theorem neutralLift_apply (D : LatticeData) (p : Oscillator D) :
    neutralLift D p = Finsupp.single 0 p := rfl

/-- Extend the substitution to the lattice carrier by reading its charge-zero component. -/
def leechNeutralTransport (i : Fin (ℒ).rank) : Carrier R₁ →ₗ[ℂ] Carrier ℒ :=
  (neutralLift ℒ).comp ((S i).toLinearMap.comp (Finsupp.lapply 0))

local notation "T" => leechNeutralTransport

@[simp] private theorem neutralTransport_lift (i : Fin (ℒ).rank) (p : Oscillator R₁) :
    T i (neutralLift R₁ p) = neutralLift ℒ (S i p) := by
  simp [leechNeutralTransport]

private theorem theta_neutralLift (D : LatticeData) (p : Oscillator D) :
    theta D (neutralLift D p) = neutralLift D (sigma D p) := by
  change thetaLinear D (Finsupp.single 0 p) = Finsupp.single 0 (sigma D p)
  simpa only [neg_zero] using theta_single D 0 p

/-- Theta records the parity of total oscillator degree. The substitution
commutes with the generator sign and hence with theta on the neutral sector. -/
theorem leechNeutralTransport_theta (i : Fin (ℒ).rank) (p : Oscillator R₁) :
    theta ℒ (T i (Finsupp.single 0 p)) = T i (theta R₁ (Finsupp.single 0 p)) := by
  change theta ℒ (T i (neutralLift R₁ p)) = T i (theta R₁ (neutralLift R₁ p))
  rw [neutralTransport_lift, theta_neutralLift, theta_neutralLift,
    neutralTransport_lift, substitution_sigma]

private theorem neutralTransport_current (i : Fin (ℒ).rank) (j : Fin (R₁).rank)
    (n : ℤ) (p : Oscillator R₁) :
    T i (neutralMode R₁ j n (neutralLift R₁ p)) =
      κ[i] • neutralMode ℒ i n (T i (neutralLift R₁ p)) := by
  simp only [neutralLift_apply, neutralMode_single]
  change T i (neutralLift R₁ (neutralPolynomialMode R₁ j 0 n p)) =
    κ[i] • neutralMode ℒ i n (T i (neutralLift R₁ p))
  rw [neutralTransport_lift, neutralTransport_lift, leechOscillatorSubstitution_neutralMode,
    map_smul]
  simp only [neutralLift_apply, neutralMode_single]

private theorem neutralTransport_derivative (i : Fin (ℒ).rank) (j : Index R₁)
    (n : ℤ) (p : Oscillator R₁) :
    T i (((dividedDerivative j.2 (neutralField R₁ j.1))[[n]]) (neutralLift R₁ p)) =
      κ[i] • ((dividedDerivative j.2 (neutralField ℒ i))[[n]]) (T i (neutralLift R₁ p)) := by
  rw [derivative_modes R₁ j n, derivative_modes ℒ (i, j.2) n]
  simp only [LinearMap.smul_apply, map_smul, neutralTransport_current,
    smul_smul, mul_comm]

private theorem neutral_derivative_lift (D : LatticeData) (j : Index D)
    (n : ℤ) (p : Oscillator D) :
    ∃ q : Oscillator D,
      ((dividedDerivative j.2 (neutralField D j.1))[[n]]) (neutralLift D p) =
        neutralLift D q := by
  rw [derivative_modes]
  refine ⟨((Ring.choose (-n - 1 + j.2) j.2 : ℤ) : ℂ) •
    neutralPolynomialMode D j.1 0 (n - j.2) p, ?_⟩
  simp only [LinearMap.smul_apply, map_smul, neutralLift_apply, neutralMode_single,
    Finsupp.smul_single]

/-- The substitution intertwines every actual untwisted mode of neutral
polynomial states on neutral polynomial inputs. -/
theorem leechNeutralTransport_mode (i : Fin (ℒ).rank) (a : Oscillator R₁) :
    ∀ (n : ℤ) (p : Oscillator R₁),
    T i (mu R₁ (Finsupp.single 0 a) n (Finsupp.single 0 p)) =
      mu ℒ (T i (Finsupp.single 0 a)) n (T i (Finsupp.single 0 p)) := by
  change ∀ (n : ℤ) (p : Oscillator R₁),
    T i (mu R₁ (neutralLift R₁ a) n (neutralLift R₁ p)) =
      mu ℒ (T i (neutralLift R₁ a)) n (T i (neutralLift R₁ p))
  classical
  induction a using MvPolynomial.induction_on with
  | C z =>
    intro n p
    have hC : (C z : Oscillator R₁) = z • 1 := by rw [smul_eq_C_mul, mul_one]
    rw [hC]
    simp only [mu, map_smul, VertexOperator.ncoeff, Pi.smul_apply, LinearMap.smul_apply,
      neutralTransport_lift, map_one]
    change z • T i (((Y R₁ (vacuum R₁))[[n]]) (neutralLift R₁ p)) =
      z • ((Y ℒ (vacuum ℒ))[[n]]) (neutralLift ℒ (S i p))
    rw [stateField_vacuum, stateField_vacuum, identity_modes, identity_modes]
    split_ifs <;> simp only [LinearMap.id_apply, neutralTransport_lift, LinearMap.zero_apply,
      map_zero, smul_zero]
  | add a b ha hb =>
    intro n p
    simp only [mu, map_add, VertexOperator.ncoeff, Pi.add_apply, LinearMap.add_apply] at ha hb ⊢
    rw [ha, hb]
  | mul_X a j ha =>
    intro n p
    let A := dividedDerivative j.2 (neutralField R₁ j.1)
    let B := Y R₁ (neutralLift R₁ a)
    let A' := dividedDerivative j.2 (neutralField ℒ i)
    let B' := Y ℒ (T i (neutralLift R₁ a))
    let v := neutralLift R₁ p
    have hs : Y R₁ (neutralLift R₁ (a * X j)) = (normalMinusOne A B).1 := by
      rw [mul_comm a (X j)]
      exact multiplication_recursion R₁ j 0 a
    have ht : Y ℒ (T i (neutralLift R₁ (a * X j))) =
        κ[i] • (normalMinusOne A' B').1 := by
      have hstate : T i (neutralLift R₁ (a * X j)) =
          κ[i] • neutralLift ℒ (X (i, j.2) * S i a) := by
        rw [mul_comm a (X j), neutralTransport_lift, leechOscillatorSubstitution_mul_X,
          smul_mul_assoc, map_smul]
      have hm : Y ℒ (neutralLift ℒ (X (i, j.2) * S i a)) = (normalMinusOne A' B').1 := by
        dsimp only [A', B']
        rw [neutralTransport_lift]
        exact multiplication_recursion ℒ (i, j.2) 0 (S i a)
      calc
        Y ℒ (T i (neutralLift R₁ (a * X j))) =
            Y ℒ (κ[i] • neutralLift ℒ (X (i, j.2) * S i a)) := congrArg (Y ℒ) hstate
        _ = κ[i] • Y ℒ (neutralLift ℒ (X (i, j.2) * S i a)) :=
          map_smul (Y ℒ) _ _
        _ = κ[i] • (normalMinusOne A' B').1 :=
          congrArg (fun W : VertexOperator ℂ (Carrier ℒ) => κ[i] • W) hm
    change T i (((Y R₁ (neutralLift R₁ (a * X j)))[[n]]) v) =
      ((Y ℒ (T i (neutralLift R₁ (a * X j))))[[n]]) (T i v)
    rw [hs, ht]
    simp only [VertexOperator.ncoeff, map_smul, Pi.smul_apply, LinearMap.smul_apply]
    change T i (((normalMinusOne A B).1[[n]]) v) =
      κ[i] • ((normalMinusOne A' B').1[[n]]) (T i v)
    rw [(normalMinusOne A B).2, (normalMinusOne A' B').2, map_add,
      map_finsum (T i) (normal_forward_finite R₁ A B n v),
      map_finsum (T i) (normal_reverse_finite R₁ A B n v),
      smul_add, smul_finsum, smul_finsum]
    congr 1
    · apply congrArg (fun f : ℕ → Carrier ℒ => ∑ᶠ k, f k)
      funext k
      have hk : ((B[[n + k]])) v = neutralLift R₁ (((B[[n + k]])) v 0) := by
        simpa only [B, v, neutralLift_apply, zero_add] using
          LatticeSectorIntertwiner.charge_homogeneity R₁ 0 0 a p (n + k)
      have hi := ha (n + k) p
      change T i ((B[[n + k]]) v) = (B'[[n + k]]) (T i v) at hi
      rw [hk]
      change T i ((A[[-(k : ℤ) - 1]]) (neutralLift R₁ _)) =
        κ[i] • (A'[[-(k : ℤ) - 1]]) ((B'[[n + k]]) (T i v))
      rw [neutralTransport_derivative i j, ← hk, hi]
    · apply congrArg (fun f : ℕ → Carrier ℒ => ∑ᶠ k, f k)
      funext k
      obtain ⟨q, hq⟩ := neutral_derivative_lift R₁ j k p
      change (A[[k]]) v = neutralLift R₁ q at hq
      have hd := neutralTransport_derivative i j k p
      change T i ((A[[k]]) v) = κ[i] • (A'[[k]]) (T i v) at hd
      rw [hq]
      have hi := ha (n - k - 1) q
      change T i ((B[[n - k - 1]]) (neutralLift R₁ q)) =
        (B'[[n - k - 1]]) (T i (neutralLift R₁ q)) at hi
      rw [hi, ← hq, hd, map_smul]

private theorem neutralTransport_grade (i : Fin (ℒ).rank) (p : Oscillator R₁) (d : ℕ)
    (hp : IsWeightedHomogeneous (oscillatorWeight R₁) p d) :
    T i (neutralLift R₁ p) ∈ grade ℒ (d : ℤ) := by
  rw [neutralTransport_lift, neutralLift_apply]
  have h := Lattice.ActualZhuCurrentRelations.single_weighted_grade ℒ 0 (S i p) d
    (leechOscillatorSubstitution_homogeneous i (fun r => r + 1) hp)
  simpa only [chargeEnergy_zero, zero_add] using h

private theorem rankOne_abe_lift :
    A₁ = neutralLift R₁ ((1 / 2 : ℂ) • (x 2 * x 0)) := by
  rw [map_smul]
  exact abeState_eq

private theorem rankOne_odd_lift :
    b₁ = neutralLift R₁ (normalization • x 0) := by
  rw [map_smul]
  exact oddCurrent_eq

private theorem rankOne_abe_theta : theta R₁ A₁ = A₁ := by
  rw [rankOne_abe_lift, theta_neutralLift]
  apply congrArg (neutralLift R₁)
  simp [x, sigma_smul, map_mul]

/-- The fixed Leech state obtained from the normalized Abe pair. -/
def leechAbeState (i : Fin (ℒ).rank) : FixedCarrier ℒ :=
  ⟨T i A₁, by
    apply (mem_fixedSpace ℒ _).mpr
    calc
      theta ℒ (T i A₁) = T i (theta R₁ A₁) := by
        rw [rankOne_abe_lift]
        exact leechNeutralTransport_theta i _
      _ = T i A₁ := by rw [rankOne_abe_theta]⟩

/-- The transport used in the balanced evaluation. The existing odd projection
makes it linear on the full source carrier. -/
def leechAbeOddTransport (i : Fin (ℒ).rank) : Carrier R₁ →ₗ[ℂ] chargeZeroOdd ℒ :=
  LinearMap.codRestrict (chargeZeroOdd ℒ) ((oddPart ℒ).comp (T i)) (fun u => by
    change (oddPart ℒ (T i u)).val ∈
      Finsupp.supported (Oscillator ℒ) ℂ ({0} : Set (Charge ℒ))
    let p := S i (u 0)
    change (2 : ℂ)⁻¹ • (neutralLift ℒ p - theta ℒ (neutralLift ℒ p)) ∈ _
    rw [theta_neutralLift, ← map_sub, ← map_smul, neutralLift_apply]
    exact Finsupp.single_mem_supported ℂ _ (by simp))

private theorem leechAbeOddTransport_val (i : Fin (ℒ).rank) (u : Carrier R₁)
    (hneutral : ∃ p : Oscillator R₁, u = neutralLift R₁ p)
    (hodd : theta R₁ u = -u) :
    (leechAbeOddTransport i u).val.val = T i u := by
  have h : theta ℒ (T i u) = -T i u := by
    obtain ⟨p, rfl⟩ := hneutral
    calc
      theta ℒ (T i (neutralLift R₁ p)) = T i (theta R₁ (neutralLift R₁ p)) :=
        leechNeutralTransport_theta i p
      _ = -T i (neutralLift R₁ p) := by rw [hodd, map_neg]
  let b : OddCarrier ℒ := ⟨T i u, (mem_eigenspace ℒ (-1) _).mpr (by simpa using h)⟩
  exact congrArg Subtype.val (oddPart_on_odd b)

theorem leechAbeState_grade (i : Fin (ℒ).rank) : (leechAbeState i).val ∈ grade ℒ 4 := by
  change T i A₁ ∈ grade ℒ 4
  rw [rankOne_abe_lift]
  apply neutralTransport_grade i _ 4
  rw [MvPolynomial.smul_eq_C_mul]
  exact ((isWeightedHomogeneous_X ℂ (oscillatorWeight R₁) ((0 : Fin (R₁).rank), 2)).mul
    (isWeightedHomogeneous_X ℂ (oscillatorWeight R₁) ((0 : Fin (R₁).rank), 0))).C_mul _

theorem leechAbeOddTransport_grade (i : Fin (ℒ).rank) :
    (leechAbeOddTransport i b₁).val.val ∈ grade ℒ 1 := by
  rw [leechAbeOddTransport_val i b₁ ⟨_, rankOne_odd_lift⟩
    Lattice.ActualZhuRankOneOdd.oddCurrent_parity, rankOne_odd_lift]
  apply neutralTransport_grade i _ 1
  rw [MvPolynomial.smul_eq_C_mul]
  exact (isWeightedHomogeneous_X ℂ (oscillatorWeight R₁) ((0 : Fin (R₁).rank), 0)).C_mul _

/-- In particular, this supplies the five modes `-1, 0, 1, 2, 3` of the Zhu row. -/
theorem leechAbeOddTransport_mode (i : Fin (ℒ).rank) (n : ℤ) :
    (leechAbeOddTransport i (mu R₁ A₁ n b₁)).val =
      oddMode ℒ (leechAbeState i) n (leechAbeOddTransport i b₁).val := by
  have hneutral : ∃ p : Oscillator R₁, mu R₁ A₁ n b₁ = neutralLift R₁ p := by
    rw [rankOne_abe_lift, rankOne_odd_lift]
    simp only [mu, neutralLift_apply]
    have hm := LatticeSectorIntertwiner.charge_homogeneity R₁ 0 0
      ((1 / 2 : ℂ) • (x 2 * x 0)) (normalization • x 0) n
    rw [zero_add] at hm
    exact ⟨_, hm⟩
  have hodd := Lattice.ActualZhuRankOneOdd.oddCurrent_parity
  have hout : theta R₁ (mu R₁ A₁ n b₁) = -mu R₁ A₁ n b₁ := by
    simp only [mu, stateField_theta, rankOne_abe_theta, hodd, map_neg]
  apply Subtype.ext
  change (leechAbeOddTransport i (mu R₁ A₁ n b₁)).val.val =
    mu ℒ (T i A₁) n (leechAbeOddTransport i b₁).val.val
  rw [leechAbeOddTransport_val i _ hneutral hout,
    leechAbeOddTransport_val i b₁ ⟨_, rankOne_odd_lift⟩ hodd,
    rankOne_abe_lift, rankOne_odd_lift]
  exact leechNeutralTransport_mode i _ n _

open Lattice.ActualZhuRankOneOdd (L) in
/-- Abe's eight-term identity in the actual balanced Leech top evaluation. -/
theorem leech_zhuTopEvaluation_abe (i : Fin (ℒ).rank)
    (F : LawfulMixedField ℒ leechUnit s) (v : twistedTop ℒ leechUnit s) :
    let Z := (zhuTopEvaluation F v).comp
      ((chargeZeroOdd ℒ).subtype.comp (leechAbeOddTransport i))
    fixedTopZero (!s) (leechAbeState i) 4 (leechAbeState_grade i) (Z b₁) =
      Z ((3 : ℂ) • b₁ + (12 : ℂ) • L (-1) b₁ +
        (12 : ℂ) • L (-1) (L (-1) b₁) - (8 : ℂ) • L (-3) b₁ +
        (16 : ℂ) • L (-2) (L (-1) b₁) - (1 / 2 : ℂ) • L (-4) b₁ +
        (1 / 4 : ℂ) • L (-3) (L (-1) b₁) +
        (3 / 2 : ℂ) • L (-2) (L (-1) (L (-1) b₁))) :=
  leech_zhuTopEvaluation_abe_of_mode_transport F v (leechAbeOddTransport i)
    (leechAbeState i) (leechAbeState_grade i) (leechAbeOddTransport_grade i)
    (fun k _ => leechAbeOddTransport_mode i ((k : ℤ) - 1))

end RankOneTransport

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
