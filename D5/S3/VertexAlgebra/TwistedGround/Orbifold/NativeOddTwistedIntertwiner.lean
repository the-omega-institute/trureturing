/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddTwistedIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two native odd-source parity-changing twisted fields with signed Jacobi, translation, physical grading, and Leech half-mode normalization. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
import D5.S3.VertexAlgebra.HalfFock.ActualEnergyCovariance
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-!
The corrected field of a lattice state in the minus eigenspace of the lattice
involution acts between the two actual twisted parity eigenspaces. In the
physical variable, the mode `n + 1/2` is the coefficient at doubled exponent
`-2*n-3`. The signed Jacobi identity uses the fixed lattice algebra and the
original fixed actions on each twisted parity. The Leech specialization
evaluates both directions on the original twisted ground and one-oscillator
states.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeInvolution
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeHalfFock (tensorCurrent tensorEnd current frequency)
open LatticeHalfFockCurrentBorcherds (current_coeff)
open LatticeHalfFockCorrectedField LatticeHalfFockParityT LatticeHalfFockGradedTrace
open LatticeHalfFockChargedTensorCoefficients LatticePositiveEnergy
open HalfFock.LatticeHalfFockParityField
open StateFieldResidueReconstruction (integerBinomial)
open ActualLeechHyperbolic (leechData leech_spec)

abbrev OddCarrier (D : LatticeData) := ↥(minusSpace D)

private theorem theta_odd (D : LatticeData) (b : OddCarrier D) :
    theta D b.val = -b.val := by
  simpa only [neg_one_smul] using (mem_eigenspace D (-1) b.val).mp b.property

private theorem mem_parity (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (v : ActualTensor D hu) :
    v ∈ paritySpace D hu s ↔ actualParity D hu v = s • v := by
  simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

def paritySign (odd : Bool) : ℂ := if odd then -1 else 1

private theorem paritySign_not (odd : Bool) :
    paritySign (!odd) = -paritySign odd := by
  cases odd <;> simp [paritySign]

abbrev Twisted (D : LatticeData) (hu : IsUnit D.G.det) (odd : Bool) :=
  ↥(paritySpace D hu (paritySign odd))

/-- Every native coefficient of an odd source reverses actual twisted parity. -/
private theorem odd_output (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (e : ℤ) (v : Twisted D hu s) :
    (correctedField D hu b.val).coeff e v.val ∈ paritySpace D hu (paritySign (!s)) := by
  rw [mem_parity, correctedField_target_parity, theta_odd, paritySign_not,
    (mem_parity D hu (paritySign s) v.val).mp v.property]
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply, map_smul]
  rw [smul_neg]
  exact (neg_smul (paritySign s) _).symm

/-- Coordinate monodromy kills every integral physical mode of an odd source. -/
private theorem odd_even_exponent_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (b : OddCarrier D) (e : ℤ) (he : Even e) (v : ActualTensor D hu) :
    (correctedField D hu b.val).coeff e v = 0 := by
  have hc := LinearMap.congr_fun (correctedField_theta D hu b.val e) v
  rw [theta_odd, neg_one_zpow_eq_ite, ite_eq_left he] at hc
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply, one_smul] at hc
  have hz : (2 : ℂ) • (correctedField D hu b.val).coeff e v = 0 := by
    rw [two_smul]
    nth_rw 1 [← hc]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The native coefficient on the two actual parity subspaces, at exponent
`e` in the doubled coordinate. -/
private def raw (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (e : ℤ) :
    OddCarrier D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu (!s) where
  toFun b := ((correctedField D hu b.val).coeff e).restrict
    (fun v hv => odd_output D hu s b e ⟨v, hv⟩)
  map_add' b c := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (correctedField D hu (b.val + c.val)).coeff e v.val =
      (correctedField D hu b.val).coeff e v.val + (correctedField D hu c.val).coeff e v.val
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' z b := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (correctedField D hu (z • b.val)).coeff e v.val =
      z • (correctedField D hu b.val).coeff e v.val
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]

private def fieldFor (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) : HVertexOperator ℤ ℂ (Twisted D hu s) (Twisted D hu (!s)) :=
  HVertexOperator.of_coeff (fun e => raw D hu s e b) (by
    intro v
    apply (((correctedField D hu b.val).isPWO_support_coeff v.val)).mono
    intro e he
    exact fun hz => he (Subtype.ext hz))

/-- The actual parity-changing field with doubled-coordinate Hahn exponents. -/
def field (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    OddCarrier D →ₗ[ℂ] HVertexOperator ℤ ℂ (Twisted D hu s) (Twisted D hu (!s)) where
  toFun := fieldFor D hu s
  map_add' b c := by
    apply HVertexOperator.coeff_inj
    funext e
    simp only [fieldFor, HVertexOperator.coeff_of_coeff, map_add, Pi.add_apply]
  map_smul' z b := by
    apply HVertexOperator.coeff_inj
    funext e
    simp only [fieldFor, HVertexOperator.coeff_of_coeff, map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The coefficient of the typed field is the original native coefficient on
the underlying tensor. -/
@[simp] theorem field_coeff (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (e : ℤ) (v : Twisted D hu s) :
    ((field D hu s b).coeff e v).val = (correctedField D hu b.val).coeff e v.val := rfl

/-- Even doubled exponents vanish, so the physical modes are half-integral. -/
theorem field_even_zero (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (e : ℤ) (he : Even e) (b : OddCarrier D) (v : Twisted D hu s) :
    (field D hu s b).coeff e v = 0 := by
  apply Subtype.ext
  rw [field_coeff]
  exact odd_even_exponent_zero D hu b e he v.val

/-- Physical mode `n + 1/2` has doubled coordinate exponent `-2*n-3`. -/
def J (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) (n : ℤ) :
    OddCarrier D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu (!s) :=
  ((LinearMap.proj (-2*n-3)).comp HVertexOperator.coeff).comp (field D hu s)

private theorem J_val (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n : ℤ) (b : OddCarrier D) (v : Twisted D hu s) :
    (J D hu s n b v).val = (correctedField D hu b.val).coeff (-2*n-3) v.val :=
  field_coeff D hu s b _ v

/-- Lower truncation holds for each pair of actual states. -/
theorem J_truncation (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (v : Twisted D hu s) :
    ∃ N : ℤ, ∀ n ≥ N, J D hu s n b v = 0 := by
  let order := ((HahnModule.of ℂ).symm ((correctedField D hu b.val) v.val)).order
  refine ⟨-(order / 2), fun n hn => Subtype.ext ?_⟩
  change ((HahnModule.of ℂ).symm ((correctedField D hu b.val) v.val)).coeff (-2*n-3) = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  change -2*n-3 < order
  omega

/-- The induced fixed algebra action on the odd actual lattice states. -/
def oddMode (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    Module.End ℂ (OddCarrier D) :=
  (((LatticeAllStateField.Y D a.val)[[n]])).restrict (fun b hb => by
    apply (mem_eigenspace D (-1) _).mpr
    have hf : theta D a.val = (1 : ℂ) • a.val := by
      simpa only [one_smul] using (mem_fixedSpace D a.val).mp a.property
    simpa only [one_mul] using mode_eigenvalue_selection D 1 (-1) a.val b hf
      ((mem_eigenspace D (-1) b).mp hb) n)

private theorem oddMode_val (D : LatticeData) (a : FixedCarrier D) (n : ℤ)
    (b : OddCarrier D) :
    (oddMode D a n b).val = LatticeAllStateReconstruction.mu D a.val n b.val := rfl

private theorem fixedParityMode_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (n : ℤ) (v : paritySpace D hu s) :
    (((fixedParitySlice D hu s a)[[n]]) v).val =
      (correctedField D hu a.val).coeff (-2*n-2) v.val := by
  change (correctedField D hu a.val).coeff (2*(-n-1)) v.val = _
  rw [show 2*(-n-1) = -2*n-2 by omega]

/-- All signed coefficient Jacobi identities for the actual odd-source field.
The fixed modes on the two twisted parities are the native fixed slices.
The physical second index is `q + 1/2`. Each sum is pointwise finite. -/
theorem J_borcherds (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p q r : ℤ) :
    let ρ := fun (t : Bool) (m : ℤ) => (fixedParitySlice D hu (paritySign t) a)[[m]]
    let left := fun i : ℕ => integerBinomial p i •
      J D hu s (p+q-i) (oddMode D a (r+i) b) v
    let first := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      ρ (!s) (p+r-i) (J D hu s (q+i) b v)
    let second := fun i : ℕ => (((-1 : ℂ)^i)*integerBinomial r i) •
      (StateFieldResidueReconstruction.epsilon r • J D hu s (q+r-i) b (ρ s (p+i) v))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i) := by
  have eigen : theta D a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace D a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu a.val 0 eigen b.val 1
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have h := native p q r v.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at h
  have binom (n : ℤ) (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  simp only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode,
    Int.cast_zero, zero_div, add_zero, sub_zero, zero_add, ← binom,
    show ∀ m : ℤ, -2*m-1-2 = -2*m-3 from fun m => by omega] at h
  let incl := (paritySpace D hu (paritySign (!s))).subtype
  have injective : Function.Injective incl := Subtype.val_injective
  have incl_apply (w : paritySpace D hu (paritySign (!s))) : incl w = w.val := rfl
  have finite_lift (f : ℕ → paritySpace D hu (paritySign (!s)))
      (hf : Function.HasFiniteSupport (fun i => incl (f i))) :
      Function.HasFiniteSupport f :=
    hf.subset (fun i hi hz => hi (injective (hz.trans (map_zero incl).symm)))
  have sum_map (f : ℕ → paritySpace D hu (paritySign (!s))) :
      incl (∑ᶠ i, f i) = ∑ᶠ i, incl (f i) :=
    incl.toAddMonoidHom.map_finsum_of_injective injective f
  have coe_sum (f : ℕ → Twisted D hu (!s)) :
      (↑(∑ᶠ i, f i) : ActualTensor D hu) = ∑ᶠ i, (f i).val := sum_map f
  dsimp only
  refine ⟨finite_lift _ ?_, finite_lift _ ?_, finite_lift _ ?_, ?_⟩
  · simpa only [incl_apply, Submodule.coe_smul, J_val, oddMode_val] using h.1
  · obtain ⟨N, hN⟩ := J_truncation D hu s b v
    refine BddAbove.finite (bddAbove_def.mpr ⟨(N-q).toNat, ?_⟩)
    intro i hi
    by_contra hlarge
    have hzero := hN (q+i) (by omega)
    exact hi (by
      dsimp only
      simp only [hzero, map_zero, smul_zero])
  · simpa only [incl_apply, Submodule.coe_smul, J_val, fixedParityMode_val, StateFieldResidueReconstruction.epsilon]
      using h.2.2.1
  · apply injective
    simp only [incl_apply, Submodule.coe_sub, coe_sum, Submodule.coe_smul, J_val,
      oddMode_val, fixedParityMode_val, StateFieldResidueReconstruction.epsilon]
    exact h.2.2.2

/-- Translation of the odd first input is the original lattice translation. -/
def oddTranslation (D : LatticeData) : Module.End ℂ (OddCarrier D) :=
  (LatticeSugawaraConformal.translation D).restrict (fun b hb => by
    rw [LatticeActualVertexAlgebra.translation_as_mode]
    apply (mem_eigenspace D (-1) _).mpr
    have hv : theta D (vacuum D) = (1 : ℂ) • vacuum D := by
      simp only [one_smul, theta_vacuum]
    simpa only [mul_one] using mode_eigenvalue_selection D (-1) 1 b (vacuum D)
      ((mem_eigenspace D (-1) b).mp hb) hv (-2))

/-- Physical translation differentiates the native half-integer field. -/
theorem J_derivative (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (v : Twisted D hu s) (n : ℤ) :
    J D hu s n (oddTranslation D b) v =
      (-((n : ℂ) + 1/2)) • J D hu s (n-1) b v := by
  apply Subtype.ext
  simp only [J_val, Submodule.coe_smul]
  change (correctedField D hu (LatticeSugawaraConformal.translation D b.val)).coeff
    (-2*n-3) v.val = _
  rw [LatticeHalfFockOriginalTranslation.correctedField_translation_physical,
    show -2*n-3+2 = -2*(n-1)-3 by omega]
  congr 1
  push_cast
  ring

/-- Physical translation differentiates every coefficient of the typed Hahn
field. A change of two in the doubled exponent is a shift of one in
the physical exponent. -/
private theorem field_derivative_step (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (v : Twisted D hu s) (e : ℤ) :
    (field D hu s (oddTranslation D b)).coeff e v =
      (((e : ℂ) + 2) / 2) • (field D hu s b).coeff (e+2) v := by
  by_cases he : Even e
  · rw [field_even_zero D hu s e he, field_even_zero D hu s (e+2) (he.add ⟨1, by norm_num⟩),
      smul_zero]
  · obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
    let n := -k-2
    have h₁ : e = -2*n-3 := by dsimp [n]; omega
    have h₂ : e+2 = -2*(n-1)-3 := by omega
    rw [h₂, h₁]
    change J D hu s n (oddTranslation D b) v =
      ((((-2*n-3 : ℤ) : ℂ) + 2) / 2) • J D hu s (n-1) b v
    rw [J_derivative]
    congr 1
    push_cast
    ring

/-- Iterated physical differentiation of the typed field at every signed
doubled exponent. -/
theorem field_derivative (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (b : OddCarrier D) (v : Twisted D hu s) (e : ℤ) (k : ℕ) :
    (field D hu s ((oddTranslation D ^ k) b)).coeff e v =
      (∏ i ∈ Finset.range k, (((e : ℂ) + 2 * ((i : ℂ) + 1)) / 2)) •
        (field D hu s b).coeff (e + 2 * k) v := by
  induction k generalizing b with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Finset.prod_range_zero, one_smul,
      Nat.cast_zero, mul_zero, add_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, field_derivative_step,
      Finset.prod_range_succ, smul_smul]
    have hscalar : ((((e + 2 * (k : ℤ) : ℤ) : ℂ) + 2) / 2) =
        ((e : ℂ) + 2 * ((k : ℂ) + 1)) / 2 := by
      push_cast
      ring
    rw [hscalar, show e + 2 * (k : ℤ) + 2 = e + 2 * ((k + 1 : ℕ) : ℤ) by omega]

/-- Energy covariance on the actual tensor, with the signed doubled output
grade `M + 2*h - 2*n - 3`. -/
private theorem J_energy (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n h : ℤ) (M : ℕ) (b : OddCarrier D) (v : Twisted D hu s)
    (hb : b.val ∈ grade D h) (hv : v.val ∈ actualGrade D hu M) :
    let w := (J D hu s n b v).val
    actualTensorL0 D hu w =
      ((D.rank : ℂ) / 16 + (((M : ℤ) + 2*h - 2*n - 3 : ℤ) : ℂ) / 2) • w := by
  have hv' : actualTensorL0 D hu v.val = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • v.val := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hv
  simpa only [J_val, Int.cast_natCast,
    show (M : ℤ) + (-2*n-3) + 2*h = (M : ℤ) + 2*h - 2*n - 3 by omega] using
    HalfFock.ActualEnergyCovariance.correctedField_signed_output D hu h M
      (-2*n-3) b.val hb v.val (by simpa only [Int.cast_natCast] using hv')

/-- The exact actual output grade when the signed index is nonnegative. -/
theorem J_grade (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n h : ℤ) (M N : ℕ) (b : OddCarrier D) (v : Twisted D hu s)
    (hb : b.val ∈ grade D h) (hv : v.val ∈ actualGrade D hu M)
    (hN : (N : ℤ) = (M : ℤ) + 2*h - 2*n - 3) :
    (J D hu s n b v).val ∈ actualGrade D hu N := by
  have he := J_energy D hu s n h M b v hb hv
  rw [← hN, Int.cast_natCast] at he
  simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using he

/-- A strictly negative signed output index forces the coefficient to vanish. -/
theorem J_negative_grade_zero (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (n h : ℤ) (M : ℕ) (b : OddCarrier D) (v : Twisted D hu s)
    (hb : b.val ∈ grade D h) (hv : v.val ∈ actualGrade D hu M)
    (hneg : (M : ℤ) + 2*h - 2*n - 3 < 0) :
    J D hu s n b v = 0 := by
  let w := (J D hu s n b v).val
  have he := J_energy D hu s n h M b v hb hv
  apply Subtype.ext
  change w = 0
  apply (actualAmbientBasis D hu).repr.injective
  ext ib
  have hc := congrArg (fun x => ((actualAmbientBasis D hu).repr x) ib) he
  change ((actualAmbientBasis D hu).repr (actualTensorL0 D hu w)) ib = _ at hc
  rw [actualTensorL0_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  rw [map_zero, Finsupp.zero_apply]
  by_contra hz
  have hc' := mul_right_cancel₀ hz hc
  have hcast : (oddWeight D ib.1 : ℂ) = (((M : ℤ) + 2*h - 2*n - 3 : ℤ) : ℂ) := by
    linear_combination 2 * hc'
  have hint : (oddWeight D ib.1 : ℤ) = (M : ℤ) + 2*h - 2*n - 3 := by
    exact_mod_cast hcast
  omega

/-- The odd lattice current state `h_i(-1)1` in the genuine source. -/
def oddCurrent (D : LatticeData) (i : Fin D.rank) : OddCarrier D :=
  ⟨neutralMode D i (-1) (vacuum D), (mem_eigenspace D (-1) _).mpr (by
    rw [theta_neutralMode, theta_vacuum, neg_one_smul])⟩

private theorem oddCurrent_grade_one (D : LatticeData) (i : Fin D.rank) :
    (oddCurrent D i).val ∈ grade D 1 := by
  change neutralMode D i (-1) (vacuum D) ∈ grade D 1
  rw [← LatticeSugawaraCurrents.neutralField_ncoeff,
    LatticeActualConformalState.current_state_creation, grade_eq_span]
  apply Submodule.subset_span
  refine ⟨(0, Finsupp.single (i,0) 1), ?_, ?_⟩
  · simp [energy, oscillatorEnergy, Finsupp.weight_single]
  · simp [carrierBasis_apply, LatticeActualConformalState.currentState, MvPolynomial.X]

/-- Each current coefficient of the typed field equals the native twisted
Heisenberg operator. In particular `n = -1, 0` give the two half-modes. -/
private theorem J_current (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool)
    (i : Fin D.rank) (n : ℤ) (v : Twisted D hu s) :
    (J D hu s n (oddCurrent D i) v).val =
      tensorCurrent D (ActualGround D hu) i n v.val :=
  current_coeff D hu i n v.val

private theorem current_half_on_vacuum (D : LatticeData) (i : Fin D.rank) :
    current D i 0 1 = 0 := by
  have h : LatticeActualAnnihilation.annihilate D i 0 1 = 0 := by
    rw [← LatticeActualAnnihilation.annihilation_apply, Derivation.map_one_eq_zero]
  simp [current, h]

/-- The return after creation has the exact Gram coefficient, for every
ground tensor and any two current directions. -/
theorem J_ground_return (D : LatticeData) (hu : IsUnit D.G.det) (i j : Fin D.rank)
    (v : Twisted D hu false) (g : ActualGround D hu)
    (hv : v.val = (1 : Oscillator D) ⊗ₜ[ℂ] g) :
    J D hu true 0 (oddCurrent D i) (J D hu false (-1) (oddCurrent D j) v) =
      ((D.G i j : ℂ) / 2) • v := by
  apply Subtype.ext
  simp only [J_current, Submodule.coe_smul, hv, tensorCurrent, tensorEnd,
    TensorProduct.map_tmul, LinearMap.id_apply]
  have h := LatticeHalfFock.current_heisenberg_apply D i j 0 (-1) (1 : Oscillator D)
  norm_num [current_half_on_vacuum, frequency] at h
  rw [h, TensorProduct.smul_tmul']
  congr 2
  ring

abbrev leechUnit : IsUnit leechData.G.det := leech_spec.2.1
abbrev TwistedEven := Twisted leechData leechUnit false
abbrev TwistedOdd := Twisted leechData leechUnit true

/-- The original odd lattice fields from the even to the odd Leech twisted space. -/
def fieldPlus : OddCarrier leechData →ₗ[ℂ] HVertexOperator ℤ ℂ TwistedEven TwistedOdd :=
  field leechData leechUnit false

/-- The original odd lattice fields from the odd to the even Leech twisted space. -/
def fieldMinus : OddCarrier leechData →ₗ[ℂ] HVertexOperator ℤ ℂ TwistedOdd TwistedEven :=
  field leechData leechUnit true

/-- The physical half-integer modes of `fieldPlus`. -/
def Jplus (n : ℤ) : OddCarrier leechData →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd :=
  ((LinearMap.proj (-2*n-3)).comp HVertexOperator.coeff).comp fieldPlus

/-- The physical half-integer modes of `fieldMinus`. -/
def Jminus (n : ℤ) : OddCarrier leechData →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven :=
  ((LinearMap.proj (-2*n-3)).comp HVertexOperator.coeff).comp fieldMinus

private def groundIndex :
    LatticeTwistedGroundRealization.Half (groundRank leechData leechUnit) := 0

private theorem groundBasis_energy :
    actualAmbientBasis leechData leechUnit (0, groundIndex) ∈ actualGrade leechData leechUnit 0 := by
  have he := actual_basis_eigenvalue leechData leechUnit 0 groundIndex
  simpa only [oddWeight, map_zero, Nat.cast_zero, zero_div, add_zero,
    actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] using he

/-- A specified nonzero vector in the actual Leech twisted ground space. -/
def leechGroundVector : TwistedEven :=
  ⟨actualAmbientBasis leechData leechUnit (0, groundIndex),
    (mem_parity leechData leechUnit 1 _).mpr (by
      simpa only [pow_zero] using
        actualParity_on_actualGrade leechData leechUnit 0 ⟨_, groundBasis_energy⟩)⟩

private theorem leechGroundVector_nonzero : leechGroundVector ≠ 0 := by
  intro hz
  exact (actualAmbientBasis leechData leechUnit).ne_zero (0, groundIndex)
    (congrArg Subtype.val hz)

/-- The actual nonzero creation and return coefficients at physical modes
`-1/2` and `1/2` on a weight-`3/2` Leech twisted ground vector. -/
theorem leech_normalization (i : Fin leechData.rank) :
    let b := oddCurrent leechData i
    let w := Jplus (-1) b leechGroundVector
    w.val = tensorCurrent leechData (ActualGround leechData leechUnit)
        i (-1) leechGroundVector.val ∧
    w.val ∈ actualGrade leechData leechUnit 1 ∧
    w ≠ 0 ∧
    Jminus 0 b w = ((leechData.G i i : ℂ) / 2) • leechGroundVector ∧
    Jminus 0 b w ≠ 0 := by
  dsimp only
  have hret := J_ground_return leechData leechUnit i i leechGroundVector
    (Pi.single groundIndex 1) (by
      change actualAmbientBasis leechData leechUnit (0, groundIndex) =
        (1 : Oscillator leechData) ⊗ₜ[ℂ] Pi.single groundIndex 1
      rw [actual_basis_apply, MvPolynomial.monomial_zero', map_one])
  have hpos : 0 < (leechData.G i i : ℝ) := leech_spec.2.2.1.diag_pos
  have hG : (leechData.G i i : ℂ) ≠ 0 := by
    exact_mod_cast (show leechData.G i i ≠ 0 from by exact_mod_cast hpos.ne')
  have hnonzero := smul_ne_zero (div_ne_zero hG (by norm_num : (2 : ℂ) ≠ 0))
    leechGroundVector_nonzero
  have hout : Jminus 0 (oddCurrent leechData i)
      (Jplus (-1) (oddCurrent leechData i) leechGroundVector) ≠ 0 := by
    exact hret.symm ▸ hnonzero
  refine ⟨J_current leechData leechUnit false i (-1) leechGroundVector, ?_, ?_, hret, hout⟩
  · exact J_grade leechData leechUnit false (-1) 1 0 1 _ _
      (oddCurrent_grade_one leechData i) groundBasis_energy (by norm_num)
  · intro hz
    apply hout
    rw [hz, map_zero]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
