import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeakAssociativity
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightBorcherds

/-!
The native upper-skew field on the odd lattice sector has the physical
stress weight and state derivative. These laws exchange the order of the
two fields in the signed Borcherds identity on that sector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity

open ActualLeechHyperbolic (leechData)
open LatticeInvolution (FixedCarrier)
open LatticePositiveEnergy (grade)
open LatticeHalfFockGradedTrace (actualGrade)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit paritySign oddMode J J_grade)
open NativeOddUpperRightSkew (R rightField rightField_coeff rightTerm R_eq_sum_of_grade)
open NativeMixedRightBorcherds (rightField_true_borcherds)
open MixedIntertwiner (originalRightCoefficient)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon)
open private stress zero_choose_finsum zero_signed_choose from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private stress_twisted_one choose_step diagonal right_mode_range from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeakAssociativity
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private stress_odd_one stress_odd_zero raise_power_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private projected_basis_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
open private oddGradeProjection oddGradeInclusion sum_oddGradeProjections from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
open private mode_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds
open private divided_succ_right from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private finsum_range epsilon_add epsilon_nat sign_square from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

local notation "ℒ" => leechData
local notation "U" => leechUnit
private abbrev A := FixedCarrier ℒ
private abbrev State (s : Bool) := Twisted ℒ U s
private abbrev B := State true
private abbrev H := State false
private abbrev O := OddCarrier ℒ
private abbrev T : Module.End ℂ B := MixedIntertwiner.translation ℒ U
private abbrev fixMode (s : Bool) (a : A) (n : ℤ) : Module.End ℂ (State s) :=
  (fixedParitySlice ℒ U (paritySign s) a)[[n]]
private abbrev twistedWeight (M : ℕ) : ℂ := (leechData.rank : ℂ) / 16 + (M : ℂ) / 2
private abbrev qMode (n : ℤ) : B →ₗ[ℂ] O →ₗ[ℂ] H := R ℒ U true n
private abbrev Q (b : B) (n : ℤ) : O →ₗ[ℂ] H :=
  (rightField ℒ U true b).coeff (-2*n-3)
local notation "L₀B" => fixMode true (stress ℒ) 1
local notation "L₀H" => fixMode false (stress ℒ) 1
local notation "L₀O" => oddMode ℒ (stress ℒ) 1

private theorem coeff_eq_mode (b : B) (n : ℤ) :
    (rightField ℒ U true b).coeff (-2*n-3) = qMode n b :=
  LinearMap.ext fun o => rightField_coeff ℒ U true n b o

set_option maxHeartbeats 2000000 in
-- The translated summands require reductions through the native parity submodules.
/-- The raised summands all have signed doubled grade `M + 2*d - 2*n - 3`.
A negative signed grade forces the actual right-field coefficient to vanish. -/
theorem rightField_true_signed_grade (b : B) (o : O) (M : ℕ) (d n : ℤ)
    (hb : b.val ∈ actualGrade ℒ U M) (ho : o.val ∈ grade ℒ d) :
    let E : ℤ := (M : ℤ) + 2*d - 2*n - 3
    (0 ≤ E → (Q b n o).val ∈ actualGrade ℒ U E.toNat) ∧
      (E < 0 → Q b n o = 0) := by
  let E : ℤ := (M : ℤ) + 2*d - 2*n - 3
  simp only [Q, coeff_eq_mode]
  change (0 ≤ E → (qMode n b o).val ∈ actualGrade ℒ U E.toNat) ∧ (E < 0 → qMode n b o = 0)
  obtain ⟨tail, hsum⟩ := R_eq_sum_of_grade ℒ U true n d M b o ho hb
  change ∀ ell : ℕ, E < 2 * (ell : ℤ) → J ℒ U true (n + ell) o b = 0 at tail
  change qMode n b o = ∑ ell ∈ Finset.range (E / 2 + 1).toNat,
    rightTerm ℒ U true n b o ell at hsum
  rw [hsum]
  constructor
  · intro hE
    simp only [Submodule.coe_sum]
    apply Submodule.sum_mem
    intro ell _
    simp only [rightTerm, Submodule.coe_smul]
    apply Submodule.smul_mem
    let K : ℤ := E - 2 * (ell : ℤ)
    by_cases hK : 0 ≤ K
    · have hgrade : (K.toNat : ℤ) = (M : ℤ) + 2*d - 2*(n + (ell : ℤ)) - 3 := by
        rw [Int.toNat_of_nonneg hK]
        dsimp only [K, E]
        omega
      let y : H := J ℒ U true (n + ell) o b
      have hJ : y.val ∈ actualGrade ℒ U K.toNat :=
        J_grade ℒ U true (n + ell) d M K.toNat o b ho hb hgrade
      have hpow := raise_power_energy false (twistedWeight K.toNat) y
        ((actualGrade_eigen ℒ U K.toNat y.val).mp hJ) ell
      apply (actualGrade_eigen ℒ U E.toNat _).mpr
      have hindex : (E.toNat : ℤ) = (K.toNat : ℤ) + 2 * (ell : ℤ) := by
        rw [Int.toNat_of_nonneg hE, Int.toNat_of_nonneg hK]
        dsimp only [K]
        omega
      have hcast : (E.toNat : ℂ) = (K.toNat : ℂ) + 2 * (ell : ℂ) := by
        exact_mod_cast hindex
      have hweight : twistedWeight E.toNat = twistedWeight K.toNat + (ell : ℂ) := by
        simp only [twistedWeight, hcast]
        ring
      change _ = twistedWeight E.toNat • _
      rw [hweight]
      exact hpow
    · have hneg : E < 2 * (ell : ℤ) := by
        dsimp only [K] at hK
        omega
      rw [tail ell hneg, map_zero]
      exact Submodule.zero_mem _
  · intro hE
    have hempty : (E / 2 + 1).toNat = 0 := by omega
    rw [hempty, Finset.range_zero, Finset.sum_empty]

set_option maxHeartbeats 2000000 in
-- Computing the stress weights uses the actual lattice and twisted carrier maps.
private theorem homogeneous_covariance (b : B) (o : O) (M : ℕ) (d n : ℤ)
    (hb : b.val ∈ actualGrade ℒ U M) (ho : o.val ∈ grade ℒ d) :
    L₀H (qMode n b o) - qMode n b (L₀O o) =
      qMode n (L₀B b) o - ((n : ℂ) + 3/2) • qMode n b o := by
  let E : ℤ := (M : ℤ) + 2*d - 2*n - 3
  have hg := rightField_true_signed_grade b o M d n hb ho
  simp only [Q, coeff_eq_mode] at hg
  change (0 ≤ E → (qMode n b o).val ∈ actualGrade ℒ U E.toNat) ∧
    (E < 0 → qMode n b o = 0) at hg
  have hb' : L₀B b = twistedWeight M • b := stress_twisted_one true M b hb
  rw [stress_odd_one d o ho, hb']
  simp only [map_smul, LinearMap.smul_apply]
  by_cases hE : 0 ≤ E
  · have hq : L₀H (qMode n b o) = twistedWeight E.toNat • qMode n b o :=
      stress_twisted_one false E.toNat _ (hg.1 hE)
    rw [hq]
    have hcast : (E.toNat : ℂ) = (E : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hE)
    have hweight : twistedWeight E.toNat = twistedWeight M + (d : ℂ) - (n : ℂ) - 3/2 := by
      simp only [twistedWeight, hcast]
      dsimp only [E]
      push_cast
      ring
    rw [hweight]
    module
  · have hzero : qMode n b o = 0 := hg.2 (by omega)
    simp only [hzero, map_zero, smul_zero, sub_self]

set_option maxHeartbeats 2000000 in
-- Both linear expansions use the concrete projected state decompositions.
/-- Stress mode one on the literal upper right field, for arbitrary states. -/
theorem rightField_true_weight_covariance (b : B) (o : O) (n : ℤ) :
    L₀H (Q b n o) - Q b n (L₀O o) =
      Q (L₀B b) n o - ((n : ℂ) + 3/2) • Q b n o := by
  classical
  simp only [Q, coeff_eq_mode]
  let eval (v : O) : B →ₗ[ℂ] H := (LinearMap.applyₗ (R := ℂ) v).comp (qMode n)
  let F := (L₀H).comp (eval o) - eval (L₀O o)
  let G := (eval o).comp L₀B - ((n : ℂ) + 3/2) • eval o
  change F b = G b
  rw [← sum_projectedBasis true b, map_sum F, map_sum G]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  congr 1
  -- Before using the lattice grading, keep the equality linear in the odd input.
  let b' : B := NativeFullMixedField.project true
    (LatticeHalfFockGradedTrace.actualAmbientBasis ℒ U i)
  have hb := projected_basis_grade true i
  let F' := (L₀H).comp (qMode n b') - (qMode n b').comp L₀O
  let G' := qMode n (L₀B b') - ((n : ℂ) + 3/2) • qMode n b'
  change F' o = G' o
  rw [← sum_oddGradeProjections o, map_sum F', map_sum G']
  apply Finset.sum_congr rfl
  intro d _
  exact homogeneous_covariance b' (oddGradeInclusion d (oddGradeProjection d o)) _ d n
    hb (oddGradeProjection d o).property.1

set_option maxHeartbeats 2000000 in
-- The specialization simplifies the three native Jacobi coefficients.
private theorem stress_commutator (b : B) (o : O) (p n : ℤ) :
    fixMode false (stress ℒ) p (Q b n o) - Q b n (oddMode ℒ (stress ℒ) p o) =
      ∑ᶠ j : ℕ, Ring.choose (p : ℂ) j • Q (fixMode true (stress ℒ) j b) (p+n-j) o := by
  obtain ⟨_, _, _, h⟩ := rightField_true_borcherds (stress ℒ) b o p n 0
  simp only [Int.cast_zero, zero_signed_choose, zpow_zero, one_smul, zero_choose_finsum,
    Nat.cast_zero, add_zero, sub_zero, zero_add] at h
  exact h.symm

private theorem choose_one_finsum (f : ℕ → H) :
    (∑ᶠ j : ℕ, Ring.choose (1 : ℂ) j • f j) = f 0 + f 1 := by
  rw [finsum_range (N := 2) (f := fun j => Ring.choose (1 : ℂ) j • f j)]
  · simp [Finset.sum_range_succ]
  · intro j hj
    have hchoose : Ring.choose (1 : ℂ) j = 0 := by
      rw [← Nat.cast_one (R := ℂ), Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hchoose, zero_smul]

set_option maxHeartbeats 2000000 in
-- The fixed stress mode is identified through the native parity maps.
/-- Stress mode zero commutes with the actual right field by translation of its state. -/
theorem rightField_true_translation_commutator (b : B) (o : O) (n : ℤ) :
    NativeOddUpperRightSkew.translation ℒ U false (Q b n o) -
      Q b n (NativeOddTwistedIntertwiner.oddTranslation ℒ o) = Q (T b) n o := by
  change fixMode false (stress ℒ) 0 (Q b n o) -
    Q b n (NativeOddTwistedIntertwiner.oddTranslation ℒ o) = Q (T b) n o
  have h := stress_commutator b o 0 n
  simp only [Int.cast_zero, zero_choose_finsum, Nat.cast_zero, zero_add, sub_zero] at h
  rw [stress_odd_zero] at h
  exact h

set_option maxHeartbeats 2000000 in
-- The two stress identities use concrete twisted and odd carrier maps.
/-- State derivative at physical mode `n + 1/2` of the literal upper right field. -/
theorem rightField_true_derivative (b : B) (o : O) (n : ℤ) :
    Q (T b) n o = -((n : ℂ) + 1/2) • Q b (n-1) o := by
  have h := stress_commutator b o 1 (n-1)
  simp only [Int.cast_one, choose_one_finsum, Nat.cast_zero, Nat.cast_one, sub_zero,
    show 1 + (n-1) = n by omega] at h
  change L₀H (Q b (n-1) o) - Q b (n-1) (L₀O o) =
    Q (T b) n o + Q (L₀B b) (n-1) o at h
  rw [rightField_true_weight_covariance b o (n-1), Int.cast_sub, Int.cast_one] at h
  calc
    _ = (Q (L₀B b) (n-1) o - ((n : ℂ) - 1 + 3/2) • Q b (n-1) o) -
        Q (L₀B b) (n-1) o := by rw [h, add_sub_cancel_right]
    _ = _ := by module

set_option maxHeartbeats 2000000 in
-- The derivative induction rewrites applications of the native bilinear mode.
private theorem divided_derivative (j : ℕ) (b : B) (o : O) (n : ℤ) :
    qMode n (dividedTranslation T j b) o =
      (((-1 : ℂ)^j) * Ring.choose ((n : ℂ) + 1/2) j) • qMode (n-j) b o := by
  induction j generalizing n b with
  | zero => simp [dividedTranslation]
  | succ j ih =>
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    apply (smul_right_inj hj).mp
    rw [← LinearMap.smul_apply, ← map_smul, divided_succ_right]
    change qMode n (dividedTranslation T j (T b)) o = _
    have step : qMode (n-j) (T b) o = -(((n-(j : ℤ) : ℤ) : ℂ)+1/2) •
        qMode (n-j-1) b o := by
      simpa only [Q, coeff_eq_mode] using rightField_true_derivative b o (n-j)
    rw [ih, step]
    simp only [smul_smul, Nat.cast_succ, pow_succ]
    rw [show n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) by omega]
    push_cast
    congr 1
    have hc := choose_step ((n : ℂ) + 1/2) j
    linear_combination ((-1 : ℂ)^j) * hc

private abbrev rightMode (b : B) (a : A) (n : ℤ) : B :=
  originalRightCoefficient ℒ U n b a

private abbrev reversedIterate (b : B) (a : A) (o : O) (q p r : ℤ) (i : ℕ) : H :=
  Ring.choose ((q : ℂ) + 1/2) i • qMode (p+q-i) (rightMode b a (r+i)) o

private abbrev forwardIterate (a : A) (b : B) (o : O) (p q r : ℤ) (i : ℕ) : H :=
  Ring.choose (p : ℂ) i • qMode (p+q-i) (fixMode true a (r+i) b) o

set_option maxHeartbeats 2000000 in
-- The finite triangular convolution rewrites the actual extension modes.
/-- The finite exchange of the two iterates of the literal right field,
using extension skew on B-on-A and the divided derivative of Q. -/
theorem rightField_true_reverse_iterate (b : B) (a : A) (o : O) (q p r : ℤ) :
    let reversed := fun i : ℕ => Ring.choose ((q : ℂ) + 1/2) i •
      Q (originalRightCoefficient ℒ U (r+i) b a) (p+q-i) o
    let forward := fun i : ℕ => Ring.choose (p : ℂ) i •
      Q (fixMode true a (r+i) b) (p+q-i) o
    Function.HasFiniteSupport reversed ∧
      (∑ᶠ i, reversed i) = epsilon (r+1) • ∑ᶠ i, forward i := by
  simp only [Q, coeff_eq_mode]
  change Function.HasFiniteSupport (reversedIterate b a o q p r) ∧
    (∑ᶠ i, reversedIterate b a o q p r i) =
      epsilon (r+1) • ∑ᶠ i, forwardIterate a b o p q r i
  obtain ⟨N, tail⟩ := mode_tail true a b r
  have skew (i : ℕ) : rightMode b a (r+i) = ∑ j ∈ Finset.range (N-i),
      epsilon (r+i+j+1) • dividedTranslation T j (fixMode true a (r+i+j) b) :=
    right_mode_range b a r N tail i
  have out (i : ℕ) (hi : N ≤ i) : rightMode b a (r+i) = 0 := by
    rw [skew i, Nat.sub_eq_zero_of_le hi, Finset.range_zero, Finset.sum_empty]
  have hrev (i : ℕ) (hi : N ≤ i) : reversedIterate b a o q p r i = 0 := by
    simp only [reversedIterate, out i hi, map_zero, LinearMap.zero_apply, smul_zero]
  have hfwd (i : ℕ) (hi : N ≤ i) : forwardIterate a b o p q r i = 0 := by
    simp only [forwardIterate, tail i hi, map_zero, LinearMap.zero_apply, smul_zero]
  refine ⟨(Finset.range N).finite_toSet.subset ?_, ?_⟩
  · intro i hi
    exact Finset.mem_range.mpr (Nat.lt_of_not_ge fun hg => hi (hrev i hg))
  rw [finsum_range (f := reversedIterate b a o q p r) hrev,
    finsum_range (f := forwardIterate a b o p q r) hfwd]
  let x : ℂ := (q : ℂ) + 1/2
  let y : ℂ := p
  let f : ℕ → H := fun l => qMode (p+q-l) (fixMode true a (r+l) b) o
  have termSign (i j : ℕ) :
      epsilon (r+((i : ℤ)+j)+1) * (-1 : ℂ)^j = epsilon (r+1) * (-1 : ℂ)^i := by
    rw [show r+((i : ℤ)+j)+1 = (r+1)+i+j by omega, epsilon_add ((r+1)+i),
      epsilon_add (r+1), epsilon_nat, epsilon_nat, mul_assoc, ← mul_pow]
    norm_num
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N-i),
        (epsilon (r+1) * ((-1 : ℂ)^i * Ring.choose x i *
          Ring.choose (x+y-(i : ℂ)) j)) • f (i+j) := by
      apply Finset.sum_congr rfl
      intro i _
      change Ring.choose x i • qMode (p+q-i) (rightMode b a (r+i)) o = _
      rw [skew i, map_sum, LinearMap.sum_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [divided_derivative, smul_smul]
      simp only [f, Nat.cast_add]
      rw [show p+q-(i : ℤ)-j = p+q-((i : ℤ)+j) by omega, add_assoc r (i : ℤ) (j : ℤ)]
      congr 1
      have hindex : ((p+q-(i : ℤ) : ℤ) : ℂ)+1/2 = x+y-(i : ℂ) := by
        simp only [x, y, Int.cast_add, Int.cast_sub, Int.cast_natCast]
        ring
      rw [hindex]
      calc
        _ = (epsilon (r+((i : ℤ)+j)+1) * (-1 : ℂ)^j) *
            (Ring.choose x i * Ring.choose (x+y-(i : ℂ)) j) := by ring
        _ = _ := by rw [termSign]; ring
    _ = ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range (l+1),
        (epsilon (r+1) * ((-1 : ℂ)^i * Ring.choose x i *
          Ring.choose (x+y-(i : ℂ)) (l-i))) • f l := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    _ = _ := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      simp_rw [mul_smul (epsilon (r+1))]
      rw [← Finset.smul_sum, ← Finset.sum_smul, diagonal]

private abbrev productWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * Ring.choose (r : ℂ) j

set_option maxHeartbeats 2000000 in
-- The signed products are matched against the two native ordered fields.
/-- The signed B,A,O Borcherds coefficients on arbitrary native states.
The two ordered products and the actual B-on-A iterate carry the sign of
the B-on-O block, with physical B mode `q + 1/2`. -/
theorem rightField_true_reversed_borcherds (b : B) (a : A) (o : O) (q p r : ℤ) :
    let iterate := fun j : ℕ => Ring.choose ((q : ℂ)+1/2) j •
      (-Q (originalRightCoefficient ℒ U (r+j) b a) (p+q-j) o)
    let first := fun j : ℕ => productWeight r j •
      (-Q b (q+r-j) (oddMode ℒ a (p+j) o))
    let second := fun j : ℕ => (epsilon r * productWeight r j) •
      ((show Module.End ℂ H from (fixedParitySlice ℒ U 1 a)[[p+r-j]]) (-Q b (q+j) o))
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ j, iterate j) = (∑ᶠ j, first j) - (∑ᶠ j, second j) := by
  obtain ⟨hiter, hit⟩ := rightField_true_reverse_iterate b a o q p r
  obtain ⟨_, hab, hba, heq⟩ := rightField_true_borcherds a b o p q r
  let first : ℕ → H := fun j => productWeight r j • qMode (q+r-j) b (oddMode ℒ a (p+j) o)
  let second : ℕ → H := fun j => productWeight r j • fixMode false a (p+r-j) (qMode (q+j) b o)
  simp only [Q, coeff_eq_mode] at hiter hit
  change Function.HasFiniteSupport (reversedIterate b a o q p r) at hiter
  change (∑ᶠ j, reversedIterate b a o q p r j) =
    epsilon (r+1) • ∑ᶠ j, forwardIterate a b o p q r j at hit
  simp only [coeff_eq_mode] at hab hba heq
  change Function.HasFiniteSupport second at hab
  change Function.HasFiniteSupport (fun j => productWeight r j • (epsilon r •
    qMode (q+r-j) b (oddMode ℒ a (p+j) o))) at hba
  have sign_product (j : ℕ) (v : H) :
      productWeight r j • (epsilon r • v) = epsilon r • (productWeight r j • v) := by
    rw [smul_smul, smul_smul, mul_comm (productWeight r j)]
  simp only [sign_product] at hba
  change Function.HasFiniteSupport (fun j => epsilon r • first j) at hba
  have support_scale (g : ℕ → H) (hg : Function.HasFiniteSupport g) (c : ℂ) :
      Function.HasFiniteSupport (fun j => c • g j) :=
    hg.subset (fun j hj hzero => hj (by simp [hzero]))
  have hs (v : H) : epsilon r • (epsilon r • v) = v := by
    rw [smul_smul, sign_square, one_smul]
  have hf : Function.HasFiniteSupport first := by
    simpa only [hs] using support_scale _ hba (epsilon r)
  have hg : Function.HasFiniteSupport (fun j => epsilon r • second j) :=
    support_scale second hab (epsilon r)
  change (∑ᶠ j, forwardIterate a b o p q r j) = (∑ᶠ j, second j) -
    ∑ᶠ j, productWeight r j • (epsilon r • qMode (q+r-j) b (oddMode ℒ a (p+j) o)) at heq
  simp only [sign_product] at heq
  change (∑ᶠ j, forwardIterate a b o p q r j) =
    (∑ᶠ j, second j) - ∑ᶠ j, epsilon r • first j at heq
  have raw : (∑ᶠ j, reversedIterate b a o q p r j) =
      (∑ᶠ j, first j) - ∑ᶠ j, epsilon r • second j := by
    rw [hit, heq, ← smul_finsum (epsilon r) first, ← smul_finsum (epsilon r) second]
    have hsign : epsilon (r+1) = -epsilon r := by
      rw [epsilon_add, show epsilon 1 = -1 by norm_num [epsilon], mul_neg, mul_one]
    rw [hsign, neg_smul, smul_sub, smul_smul, sign_square, one_smul, neg_sub]
  have support_neg (f : ℕ → H) (hf : Function.HasFiniteSupport f) :
      Function.HasFiniteSupport (fun j => -f j) :=
    hf.subset (fun j hj hzero => hj (by simp [hzero]))
  dsimp only
  simp only [Q, coeff_eq_mode, map_neg, smul_neg, mul_smul (epsilon r)]
  change Function.HasFiniteSupport (fun j => -reversedIterate b a o q p r j) ∧
    Function.HasFiniteSupport (fun j => -first j) ∧
    Function.HasFiniteSupport (fun j => -(epsilon r • second j)) ∧
    (∑ᶠ j, -reversedIterate b a o q p r j) =
      (∑ᶠ j, -first j) - ∑ᶠ j, -(epsilon r • second j)
  refine ⟨support_neg _ hiter, support_neg _ hf, support_neg _ hg, ?_⟩
  simp only [finsum_neg_distrib]
  rw [raw] <;> abel

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_signed_grade' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_signed_grade

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_weight_covariance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_weight_covariance

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_translation_commutator' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_translation_commutator

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_derivative' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_derivative

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_reverse_iterate' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_reverse_iterate

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity.rightField_true_reversed_borcherds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightField_true_reversed_borcherds

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity
