import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairField

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open Complex (I)
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeHalfFockGradedTrace LatticeHalfFockParityT
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open LatticeHalfFockCorrectedField
open ActualChargedAdjoint (actualForm)
open LatticeInvolution (minusSpace)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open NativeOddTwistedIntertwiner
open NativeOddUpperRightSkew
open NativeMixedPairField NativeMixedPairState
open NativeFullMixedField (project)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open OriginalSkewAdjoints (actual_corrected_adjoint_of_grade)
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private mu_pairing_forward lowered_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedInverseBPZ
open private J_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private actualGrade_eigen lowering_pow_val translation_power_pairing
  translation_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lowerOdd from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
open private stress from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private original_l1_grade T lowering_eigen lowering_bracket from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private raising lowering_raising_bracket from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private oddMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private J_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private sourceL1 from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints

local notation "ℒ" => leechData
local notation "B" => actualForm ℒ leechUnit
local notation "P" => sourcePairing ℒ
local notation "L" => lowering ℒ leechUnit
local notation "U" => translation ℒ leechUnit
local notation "J₀" => J ℒ leechUnit
local notation "R₀" => R ℒ leechUnit
local notation "F" => rightField ℒ leechUnit

abbrev Odd := OddCarrier ℒ
abbrev State (s : Bool) := Twisted ℒ leechUnit s

private abbrev invFact (p : ℕ) : ℂ := (p.factorial : ℂ)⁻¹

/-- Forward BPZ with an arbitrary opposite-parity detector, including an
inhomogeneous native right coefficient. -/
theorem mu_pairing_arbitrary_detector (s : Bool) (M : ℕ) (e : ℤ)
    (u : State s) (v : State (!s)) (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (a : Odd) :
    P ((mu s u).coeff e v).val a.val =
      I ^ (-(3 + (M : ℤ))) * ∑ j ∈ Finset.range (M/2+1),
        invFact j * B v.val ((F s ((L s ^ j) u)).coeff
          (-6-2*(M : ℤ)+2*(j : ℤ)-e) a).val := by
  let left : Module.Dual ℂ (State (!s)) :=
    ((LinearMap.flip P a.val).comp (minusSpace ℒ).subtype).comp ((mu s u).coeff e)
  let right : Module.Dual ℂ (State (!s)) :=
    I ^ (-(3 + (M : ℤ))) • ∑ j ∈ Finset.range (M/2+1),
      invFact j • ((LinearMap.flip B ((F s ((L s ^ j) u)).coeff
        (-6-2*(M : ℤ)+2*(j : ℤ)-e) a).val).comp
          (paritySpace ℒ leechUnit (paritySign (!s))).subtype)
  have h : left v = right v := by
    rw [← sum_projectedBasis (!s) v]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    let x := actualAmbientBasis ℒ leechUnit i
    let K := oddWeight ℒ i.1
    have hx : x ∈ actualGrade ℒ leechUnit K :=
      (actualGrade_eigen ℒ leechUnit K x).mpr (actual_basis_eigenvalue ℒ leechUnit i.1 i.2)
    have hproj : (project (!s) x).val ∈ actualGrade ℒ leechUnit K := by
      rw [project_val]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx (Submodule.smul_mem _ _
        (actualParity_preserves_grade ℒ leechUnit _ _ hx)))
    apply congrArg ((actualAmbientBasis ℒ leechUnit).repr v.val i • ·)
    simpa only [left, right, LinearMap.comp_apply, LinearMap.flip_apply, Submodule.subtype_apply,
      LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] using
      mu_pairing_forward s M K e u (project (!s) x) hu hproj a
  simpa only [left, right, LinearMap.comp_apply, LinearMap.flip_apply, Submodule.subtype_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] using h

/-- Exact upper-branch J-mode adjunction on an original homogeneous odd
source, with the physical mode indices shifted by finite source lowering. -/
theorem J_pairing_adjoint (s : Bool) (d n : ℤ) (a : Odd)
    (ha : a.val ∈ grade ℒ d) (x : State s) (y : State (!s)) :
    B (J₀ s n a x).val y.val =
      (-1 : ℂ)^d * ∑ h ∈ Finset.range (d.toNat+1),
        invFact h * B x.val (J₀ (!s) (2*d-n-3-(h : ℤ)) (lowerOdd a h) y).val := by
  rw [J_val, actual_corrected_adjoint_of_grade ℒ leechUnit leech_spec.2.2.1 d _ a.val ha]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [J_val]
  rw [show -(-2*n-3)-4*d+2*(h : ℤ) = -2*(2*d-n-3-(h : ℤ))-3 by ring]
  rfl

private theorem R_pairing_detector (s : Bool) (n : ℤ) (K : ℕ)
    (x : State s) (y : State (!s)) (a : Odd)
    (hy : y.val ∈ actualGrade ℒ leechUnit K) :
    B y.val (R₀ s n x a).val =
      ∑ p ∈ Finset.range (K/2+1),
        (I ^ (-2*(n+(p : ℤ))-3) * invFact p) *
          B ((L (!s)^p) y).val (J₀ s (n+(p : ℤ)) a x).val := by
  rw [R_pairing_finite ℒ leechUnit s n K x a y hy]
  simp only [lowering_pow_val]

/-- The two independent odd doubled coefficients, expanded on both actual
twisted inputs. All three cutoffs come from the homogeneous grades. -/
theorem product_expansion (M K : ℕ) (k l D O : ℤ)
    (b c : State true) (o d : Odd)
    (hb : b.val ∈ actualGrade ℒ leechUnit M)
    (hc : c.val ∈ actualGrade ℒ leechUnit K)
    (ho : o.val ∈ grade ℒ O) (hd : d.val ∈ grade ℒ D) :
    P ((mu true b).coeff (-2*k-3) ((F true c).coeff (-2*l-3) o)).val d.val =
      I ^ (-(3+(M : ℤ))) * ∑ j ∈ Finset.range (M/2+1),
        invFact j * ∑ p ∈ Finset.range (((M : ℤ)+2*D-2*((M : ℤ)-k)-3)/2+1).toNat,
          ∑ q ∈ Finset.range (((K : ℤ)+2*O-2*l-3)/2+1).toNat,
            (I ^ (-2*((M : ℤ)-k-(j : ℤ)+(p : ℤ))-3) * invFact p) *
              (I ^ (-2*(l+(q : ℤ))-3) * invFact q) *
              B ((U false ^ q) (J₀ true (l+(q : ℤ)) o c)).val
                ((U false ^ p) (J₀ true ((M : ℤ)-k-(j : ℤ)+(p : ℤ)) d
                  ((L true ^ j) b))).val := by
  rw [mu_pairing_arbitrary_detector true M _ b _ hb d, rightField_coeff]
  apply congrArg (fun x : ℂ => I ^ (-(3+(M : ℤ))) * x)
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ M/2 := by simpa using hj
  rw [show -6-2*(M : ℤ)+2*(j : ℤ)-(-2*k-3) = -2*((M : ℤ)-k-(j : ℤ))-3 by ring,
    rightField_coeff]
  rw [(R_eq_sum_of_grade ℒ leechUnit true l O K c o ho hc).2,
    (R_eq_sum_of_grade ℒ leechUnit true ((M : ℤ)-k-(j : ℤ)) D (M-2*j)
      ((L true ^ j) b) d hd (lowered_grade hb hj')).2]
  have hbound : ((M-2*j : ℕ) : ℤ)+2*D-2*((M : ℤ)-k-(j : ℤ))-3 =
    (M : ℤ)+2*D-2*((M : ℤ)-k)-3 := by omega
  rw [hbound]
  congr 1
  simp only [Submodule.coe_sum, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [rightTerm, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  let A := I ^ (-2*((M : ℤ)-k-(j : ℤ)+(p : ℤ))-3) * invFact p
  let C := I ^ (-2*(l+(q : ℤ))-3) * invFact q
  let V := B ((U false ^ q) (J₀ true (l+(q : ℤ)) o c)).val
    ((U false ^ p) (J₀ true ((M : ℤ)-k-(j : ℤ)+(p : ℤ)) d ((L true ^ j) b))).val
  change A * (C * V) = A * C * V
  exact (mul_assoc A C V).symm

private theorem source_lower_grade (d : ℤ) (a : Odd) (ha : a.val ∈ grade ℒ d) (j : ℕ) :
    (lowerOdd a j).val ∈ grade ℒ (d-j) :=
  original_l1_grade ℒ leechUnit d a.val ha j

private theorem inverse_eq :
    HalfFockSpectralFiberSource.actualInverse ℒ = (LatticeSugawaraCurrents.gramComplex ℒ)⁻¹ :=
  (Matrix.inv_eq_left_inv (HalfFockSpectralFiberSource.actualInverse_left ℒ leechUnit)).symm

private theorem stress_odd_mode (i : ℤ) (a : Odd) :
    (oddMode ℒ (stress ℒ) i a).val =
      sugawaraMode ℒ (LatticeSugawaraCurrents.gramComplex ℒ)⁻¹ (i-1) a.val := by
  rw [oddMode_val]
  change LatticeAllStateReconstruction.mu ℒ
    (LatticeActualConformalState.omega ℒ (HalfFockSpectralFiberSource.actualInverse ℒ)) i a.val = _
  rw [LatticeActualConformalWard.omega_product, inverse_eq]

private theorem stress_odd_zero (a : Odd) :
    oddMode ℒ (stress ℒ) 0 a = oddTranslation ℒ a := by
  apply Subtype.ext
  rw [stress_odd_mode, ← inverse_eq, show (0-1 : ℤ) = -1 by decide,
    LatticeSugawaraConformal.sugawaraMode_minus_one_eq_translation ℒ _
      (HalfFockSpectralFiberSource.actualInverse_left ℒ leechUnit)
      (HalfFockSpectralFiberSource.actualInverse_right ℒ leechUnit)]
  rfl

private theorem stress_odd_one (d : ℤ) (a : Odd) (ha : a.val ∈ grade ℒ d) :
    oddMode ℒ (stress ℒ) 1 a = (d : ℂ) • a := by
  apply Subtype.ext
  rw [stress_odd_mode, ← inverse_eq, show (1-1 : ℤ) = 0 by decide]
  exact (actualL0_eigen_iff_grade ℒ _
    (HalfFockSpectralFiberSource.actualInverse_left ℒ leechUnit)
    (HalfFockSpectralFiberSource.actualInverse_right ℒ leechUnit) d a.val).mpr ha

private theorem stress_odd_two (a : Odd) :
    oddMode ℒ (stress ℒ) 2 a = lowerOdd a 1 := by
  apply Subtype.ext
  rw [stress_odd_mode]
  change _ = (sourceL1 ℒ ^ (1 : ℕ)) a.val
  rw [pow_one]
  rfl

/-- The L(1) commutator of an arbitrary native odd homogeneous state.
The derivative, L(0) and L(1) contributions have native indices n+1,n+1,n. -/
theorem lowering_J (s : Bool) (d n : ℤ) (a : Odd) (x : State s)
    (ha : a.val ∈ grade ℒ d) :
    L (!s) (J₀ s n a x) =
      J₀ s n a (L s x) +
      (2*(d : ℂ)-(n : ℂ)-5/2) • J₀ s (n+1) a x +
      J₀ s n (lowerOdd a 1) x := by
  classical
  have law := (J_borcherds ℒ leechUnit s (stress ℒ) a x 2 n 0).2.2.2
  dsimp only at law
  let f (i : ℕ) := integerBinomial 2 i •
    J₀ s (2+n-(i : ℤ)) (oddMode ℒ (stress ℒ) (0+(i : ℤ)) a) x
  have hf : (∑ᶠ i, f i) = f 0 + f 1 + f 2 := by
    rw [finsum_eq_sum_of_support_subset f (s := Finset.range 3)]
    · simp [Finset.sum_range_succ]
    · intro i hi
      by_contra hn
      have hgt : 2 < i := Nat.lt_of_not_ge (fun hi => hn (Finset.mem_range.mpr (by omega)))
      have hz : integerBinomial 2 i = 0 := by
        unfold integerBinomial
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Ring.choose_natCast]
        simp [Nat.choose_eq_zero_of_lt hgt]
      exact hi (by simp [f, hz])
  have hz (i : ℕ) (hi : i ≠ 0) : integerBinomial 0 i = 0 := by
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  rw [show (∑ᶠ i, integerBinomial 2 i •
      J₀ s (2+n-(i : ℤ)) (oddMode ℒ (stress ℒ) (0+(i : ℤ)) a) x) =
      f 0 + f 1 + f 2 from hf] at law
  rw [finsum_eq_single _ 0, finsum_eq_single _ 0] at law
  · have h0 : integerBinomial 2 0 = 1 := by norm_num [integerBinomial]
    have h1 : integerBinomial 2 1 = 2 := by norm_num [integerBinomial, Ring.choose_one_right]
    have h2 : integerBinomial 2 2 = 1 := by
      unfold integerBinomial
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Ring.choose_natCast]
      norm_num
    have hz0 : integerBinomial 0 0 = 1 := by norm_num [integerBinomial]
    simp only [f, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, sub_zero,
      h0, h1, h2, one_smul, pow_zero, mul_one, hz0,
      StateFieldResidueReconstruction.epsilon, zpow_zero, add_zero] at law
    rw [stress_odd_zero, stress_odd_one d a ha, stress_odd_two,
      show 2+n-1 = n+1 by ring, show 2+n-2 = n by ring,
      J_derivative ℒ leechUnit s a x (2+n),
      show 2+n-1 = n+1 by ring] at law
    simp only [map_smul, LinearMap.smul_apply, smul_smul] at law
    change _ = L (!s) (J₀ s n a x) - J₀ s n a (L s x) at law
    apply Subtype.ext
    have h := congrArg (fun v : State (!s) => v.val) law
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul] at h ⊢
    have h' := sub_eq_iff_eq_add.mp h.symm
    rw [h']
    push_cast
    module
  · intro i hi
    simp [hz i hi]
  · intro i hi
    simp [hz i hi]

/-- A finite scalar sum of lowered mode positions. Each of the three branches
is one of the three terms of the L(1) commutator. The indices of the
functional are the actual mode, source lowering order and input lowering
order. -/
def loweringSum : ℕ → ℤ → ℤ → (ℤ → ℕ → ℕ → ℂ) → ℂ
  | 0, _, n, f => f n 0 0
  | p+1, d, n, f =>
      loweringSum p d n (fun m h j => f m h (j+1)) +
      (2*(d : ℂ)-(n : ℂ)-5/2) * loweringSum p d (n+1) f +
      loweringSum p (d-1) n (fun m h j => f m (h+1) j)

private theorem lowerOdd_succ (a : Odd) (h : ℕ) :
    lowerOdd (lowerOdd a 1) h = lowerOdd a (h+1) := by
  apply Subtype.ext
  change (sourceL1 ℒ ^ h) ((sourceL1 ℒ ^ (1 : ℕ)) a.val) =
    (sourceL1 ℒ ^ (h+1)) a.val
  rw [pow_add, Module.End.mul_apply]

theorem loweringSum_eq (s : Bool) (p : ℕ) (d n : ℤ) (a : Odd) (x : State s)
    (ha : a.val ∈ grade ℒ d) (F₁ : State (!s) →ₗ[ℂ] ℂ) :
    F₁ ((L (!s) ^ p) (J₀ s n a x)) =
      loweringSum p d n (fun m h j => F₁ (J₀ s m (lowerOdd a h) ((L s ^ j) x))) := by
  induction p generalizing d n a x with
  | zero =>
      have h0 : lowerOdd a 0 = a := by apply Subtype.ext; simp [lowerOdd]
      simp [loweringSum, h0]
  | succ p ih =>
      rw [pow_succ, Module.End.mul_apply, lowering_J s d n a x ha]
      simp only [map_add, map_smul, smul_eq_mul, loweringSum]
      rw [
        ih d n a (L s x) ha, ih d (n+1) a x ha,
        ih (d-1) n (lowerOdd a 1) x (by simpa using source_lower_grade d a ha 1)]
      simp only [pow_succ (L s), Module.End.mul_apply, lowerOdd_succ]

private theorem raise_energy (s : Bool) (H : ℂ) (y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) :
    actualTensorL0 ℒ leechUnit (U s y).val = (H+1) • (U s y).val := by
  rw [translation_val]
  have bracket : actualTensorL0 ℒ leechUnit * raising ℒ leechUnit -
      raising ℒ leechUnit * actualTensorL0 ℒ leechUnit = raising ℒ leechUnit := by
    apply TensorProduct.ext'
    intro p t
    have h := congrArg (fun A : Module.End ℂ (Oscillator ℒ) => A p ⊗ₜ[ℂ] t)
      (L_virasoro ℒ (HalfFockSpectralFiberSource.actualInverse ℒ)
        (HalfFockSpectralFiberSource.actualInverse_left ℒ leechUnit)
        (HalfFockSpectralFiberSource.actualInverse_right ℒ leechUnit) 0 (-1))
    norm_num at h
    simpa only [actualTensorL0, raising, tensorL, tensorEnd, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.neg_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.sub_tmul, TensorProduct.neg_tmul] using h
  have h := LinearMap.congr_fun bracket y.val
  change actualTensorL0 ℒ leechUnit (raising ℒ leechUnit y.val) -
    raising ℒ leechUnit (actualTensorL0 ℒ leechUnit y.val) = raising ℒ leechUnit y.val at h
  rw [hy, map_smul, sub_eq_iff_eq_add, add_comm] at h
  simpa only [add_smul, one_smul] using h

private theorem lower_energy (s : Bool) (H : ℂ) (y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) :
    actualTensorL0 ℒ leechUnit (L s y).val = (H-1) • (L s y).val := by
  have he := lowering_pow_val ℒ leechUnit s 1 y
  simp only [pow_one] at he
  rw [he]
  have h := LinearMap.congr_fun (lowering_bracket ℒ leechUnit) y.val
  change actualTensorL0 ℒ leechUnit (T ℒ leechUnit y.val) -
    T ℒ leechUnit (actualTensorL0 ℒ leechUnit y.val) = -T ℒ leechUnit y.val at h
  rw [hy, map_smul, sub_eq_iff_eq_add, add_comm] at h
  rw [← neg_one_smul ℂ (T ℒ leechUnit y.val), ← add_smul] at h
  simpa only [sub_eq_add_neg] using h

private theorem lower_raise (s : Bool) (H : ℂ) (y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) :
    L s (U s y) = U s (L s y) + (2*H) • y := by
  apply Subtype.ext
  have hv (x : State s) : (L s x).val = T ℒ leechUnit x.val := by
    simpa only [pow_one] using lowering_pow_val ℒ leechUnit s 1 x
  simp only [hv, translation_val, Submodule.coe_add, Submodule.coe_smul]
  have h := lowering_raising_bracket ℒ leechUnit y.val
  rw [hy, smul_smul, sub_eq_iff_eq_add] at h
  exact h.trans (add_comm _ _)

private theorem raise_power_energy (s : Bool) (H : ℂ) (y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) (q : ℕ) :
    actualTensorL0 ℒ leechUnit ((U s ^ q) y).val = (H+(q : ℂ)) • ((U s ^ q) y).val := by
  induction q with
  | zero => simpa using hy
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, raise_energy s _ _ ih]
    congr 1
    push_cast
    ring

private theorem lower_raise_power (s : Bool) (H : ℂ) (y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) (q : ℕ) :
    L s ((U s ^ (q+1)) y) =
      (U s ^ (q+1)) (L s y) + (((q+1 : ℕ) : ℂ)*(2*H+(q : ℂ))) • ((U s ^ q) y) := by
  induction q with
  | zero => simpa using lower_raise s H y hy
  | succ q ih =>
    rw [pow_succ' (U s) (q+1), Module.End.mul_apply,
      lower_raise s _ _ (raise_power_energy s H y hy (q+1)),
      ih, map_add, map_smul]
    simp only [pow_succ' (U s), Module.End.mul_apply]
    push_cast
    module

private theorem transpose_power (s : Bool) (p : ℕ) (x y : State s) :
    B x.val ((U s ^ p) y).val = B ((L s ^ p) x).val y.val := by
  rw [translation_power_pairing, lowering_pow_val]

private theorem pairing_symm (x y : ActualTensor ℒ leechUnit) : B x y = B y x :=
  (ActualPairingSymmetry.actualForm_symmetric ℒ leechUnit).eq x y

/-- Finite normal ordering of the two translation powers inside the
bilinear pairing. The first and second arguments of f count the lowerings
on the left and right mode outputs. Each branch decreases p. -/
def translationSum : ℕ → ℕ → ℂ → (ℕ → ℕ → ℂ) → ℂ
  | 0, q, _, f => f q 0
  | p+1, 0, _, f => f 0 (p+1)
  | p+1, q+1, H, f =>
      translationSum p (q+1) (H-1) (fun a b => f a (b+1)) +
      (((q+1 : ℕ) : ℂ)*(2*H+(q : ℂ))) * translationSum p q H f

theorem translationSum_eq (s : Bool) (p q : ℕ) (H : ℂ) (x y : State s)
    (hy : actualTensorL0 ℒ leechUnit y.val = H • y.val) :
    B ((U s ^ p) x).val ((U s ^ q) y).val =
      translationSum p q H (fun a b => B ((L s ^ a) x).val ((L s ^ b) y).val) := by
  induction p generalizing q H y with
  | zero => simp only [pow_zero, Module.End.one_apply, translationSum, transpose_power]
  | succ p ih =>
    cases q with
    | zero =>
      simp only [pow_zero, Module.End.one_apply, translationSum]
      rw [pairing_symm, transpose_power, pairing_symm]
    | succ q =>
      rw [pow_succ' (U s) p, Module.End.mul_apply, pairing_symm]
      have ht := transpose_power s 1 ((U s ^ (q+1)) y) ((U s ^ p) x)
      simp only [pow_one] at ht
      rw [ht]
      rw [lower_raise_power s H y hy q, Submodule.coe_add, Submodule.coe_smul, map_add,
        LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [pairing_symm ((U s ^ (q+1)) (L s y)).val, ih (q+1) (H-1) (L s y) (lower_energy s H y hy),
        pairing_symm ((U s ^ q) y).val, ih q H y hy, translationSum]
      simp only [pow_succ (L s), Module.End.mul_apply]

/-- Descendants under the original lattice Virasoro lowering mode, on the
actual odd-source carrier. -/
def oddLower (a : Odd) (i : ℕ) : Odd := lowerOdd a i

/-- A pairing of the two right-mode constituents written in consecutive
actual J modes. The contracted translation powers and the two L(1) Ward
sums are finite scalar sums, and the only twisted inputs remaining in the
matrix entry are lowering descendants of the original inputs. -/
def modeComposition (D O n m : ℤ) (p q : ℕ) (H : ℂ)
    (b c : State true) (o d : Odd) : ℂ :=
  translationSum q p H (fun a z =>
    loweringSum a O m (fun m' i u =>
      loweringSum z D n (fun n' j v =>
        (-1 : ℂ)^(O-(i : ℤ)) * ∑ h ∈ Finset.range ((O-(i : ℤ)).toNat+1),
          invFact h * B ((L true ^ u) c).val
            (J₀ false (2*(O-(i : ℤ))-m'-3-(h : ℤ)) (oddLower (oddLower o i) h)
              (J₀ true n' (oddLower d j) ((L true ^ v) b))).val)))

theorem modeComposition_eq (D O n m : ℤ) (p q : ℕ) (H : ℂ)
    (b c : State true) (o d : Odd)
    (ho : o.val ∈ grade ℒ O) (hd : d.val ∈ grade ℒ D)
    (hH : actualTensorL0 ℒ leechUnit (J₀ true n d b).val =
      H • (J₀ true n d b).val) :
    B ((U false ^ q) (J₀ true m o c)).val ((U false ^ p) (J₀ true n d b)).val =
      modeComposition D O n m p q H b c o d := by
  rw [translationSum_eq false q p H _ _ hH, modeComposition]
  congr 1
  funext a z
  let Y := (L false ^ z) (J₀ true n d b)
  let f : State false →ₗ[ℂ] ℂ := (LinearMap.flip B Y.val).comp
    (paritySpace ℒ leechUnit (paritySign false)).subtype
  have hf := loweringSum_eq true a O m o c ho f
  change f ((L false ^ a) (J₀ true m o c)) =
    loweringSum a O m (fun m h j => f (J₀ true m (lowerOdd o h) ((L true ^ j) c))) at hf
  change B ((L false ^ a) (J₀ true m o c)).val Y.val = _
  rw [show B ((L false ^ a) (J₀ true m o c)).val Y.val =
      f ((L false ^ a) (J₀ true m o c)) from rfl, hf]
  congr 1
  funext m' i u
  let X := J₀ true m' (lowerOdd o i) ((L true ^ u) c)
  let g : State false →ₗ[ℂ] ℂ := (B X.val).comp
    (paritySpace ℒ leechUnit (paritySign false)).subtype
  change g ((L false ^ z) (J₀ true n d b)) = _
  have hg := loweringSum_eq true z D n d b hd g
  change g ((L false ^ z) (J₀ true n d b)) =
    loweringSum z D n (fun m h j => g (J₀ true m (lowerOdd d h) ((L true ^ j) b))) at hg
  rw [hg]
  congr 1
  funext n' j v
  change B X.val (J₀ true n' (lowerOdd d j) ((L true ^ v) b)).val = _
  exact J_pairing_adjoint true (O-(i : ℤ)) m' (lowerOdd o i)
    (source_lower_grade O o ho i) ((L true ^ u) c) _

/-- Direct finite BPZ transport of every odd/odd native BBO product
coefficient to the original O,O-on-B action. All independent integer modes
and every homogeneous state on the four actual carriers are admitted. -/
theorem bbo_product_modes (M K : ℕ) (k l D O : ℤ)
    (b c : State true) (o d : Odd)
    (hb : b.val ∈ actualGrade ℒ leechUnit M)
    (hc : c.val ∈ actualGrade ℒ leechUnit K)
    (ho : o.val ∈ grade ℒ O) (hd : d.val ∈ grade ℒ D) :
    P ((mu true b).coeff (-2*k-3) ((F true c).coeff (-2*l-3) o)).val d.val =
      I ^ (-(3+(M : ℤ))) * ∑ j ∈ Finset.range (M/2+1),
        invFact j * ∑ p ∈ Finset.range (((M : ℤ)+2*D-2*((M : ℤ)-k)-3)/2+1).toNat,
          ∑ q ∈ Finset.range (((K : ℤ)+2*O-2*l-3)/2+1).toNat,
            (I ^ (-2*((M : ℤ)-k-(j : ℤ)+(p : ℤ))-3) * invFact p) *
              (I ^ (-2*(l+(q : ℤ))-3) * invFact q) *
              modeComposition D O ((M : ℤ)-k-(j : ℤ)+(p : ℤ)) (l+(q : ℤ)) p q
                ((leechData.rank : ℂ)/16 +
                  (((M : ℤ)+2*D-2*((M : ℤ)-k)-3-2*(p : ℤ) : ℤ) : ℂ)/2)
                ((L true ^ j) b) c o d := by
  rw [product_expansion M K k l D O b c o d hb hc ho hd]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ M/2 := by simpa using hj
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply modeComposition_eq D O _ _ p q _ _ c o d ho hd
  have he := J_energy ℒ leechUnit true ((M : ℤ)-k-(j : ℤ)+(p : ℤ)) D
    (M-2*j) d ((L true ^ j) b) hd (lowered_grade hb hj')
  have heq : ((M-2*j : ℕ) : ℤ)+2*D-2*((M : ℤ)-k-(j : ℤ)+(p : ℤ))-3 =
      (M : ℤ)+2*D-2*((M : ℤ)-k)-3-2*(p : ℤ) := by omega
  simpa only [heq] using he

/-- Even doubled exponents in either factor contribute zero. -/
theorem bbo_product_even_zero (e f : ℤ) (b c : State true) (o d : Odd)
    (h : Even e ∨ Even f) :
    P ((mu true b).coeff e ((F true c).coeff f o)).val d.val = 0 := by
  rcases h with he | hf
  · rw [mu_coeff_even_zero true e _ _ he]
    simp
  · rw [rightField_even_zero ℒ leechUnit true f hf]
    simp

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ
