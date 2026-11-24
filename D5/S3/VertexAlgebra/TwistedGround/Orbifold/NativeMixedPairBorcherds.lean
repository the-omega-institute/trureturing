import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

/-!
The mixed BPZ readout uses independent lowering orders on the two twisted
states. For a fixed state of weight `d`, the order `l` of its source lowering
sends the three residues to `r`, `M-q-r-i+j`, and `2*d-p-r-2-l`.
The first mixed product gives the native iterate. The second mixed product
gives the first native product. The mixed iterate gives the signed second
native product. The mode bounds justify each finite change of summation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality (Carrier)
open LatticePositiveEnergy LatticeInvolution LatticeAllStateField
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace ActualChargedAdjoint ActualOddGradeOrthogonality
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit paritySign J J_borcherds oddMode)
open NativeOddUpperRightSkew (lowering mixedPairing_finite mixedPairing_lowering_tail)
open NativeMixedPairField (mu mu_coeff_of_grade mu_lower_truncation)
open NativeMixedPairState (mixedPairState_pairing)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_nondegenerate)
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open private T originalL1 original_l1_grade original_l1_fixed lowering_eigen negative_eigen_zero
  from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private lowering_field_expansion signed_supported_transform rectangle_to_diagonals
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobi
open private lowering_triangle_to_cube twice_signed_transform from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCoefficients
open private original_negative_grade_zero from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private actualGrade_eigen lowering_pow_val
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private fixedParityMode_val oddMode_val J_val
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private minusPart_mem sourcePairing_minusPart_right oddGradeProjection oddGradeInclusion
  sum_oddGradeProjections
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

open private fixedSourceInclusion fixed_source_expansion
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private projected_basis_grade
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
open private sum_projectedBasis
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "U" => leechUnit
private abbrev State (s : Bool) := Twisted ℒ U s
private abbrev A := FixedCarrier ℒ
private abbrev B := State true
private abbrev H := State false
private abbrev O := OddCarrier ℒ
private abbrev tensor := ActualTensor ℒ U
local notation "βₘ" => actualForm ℒ U
local notation "βₒ" => sourcePairing ℒ
private abbrev L := originalL1 ℒ
private abbrev lowered (a : A) (j : ℕ) : A :=
  ⟨(L ^ j) a.val, (mem_fixedSpace ℒ _).mpr
    (original_l1_fixed ℒ U a.val a.property j)⟩

private abbrev fixMode (s : Bool) (a : A) (n : ℤ) : Module.End ℂ (State s) :=
  (fixedParitySlice ℒ U (paritySign s) a)[[n]]

private abbrev P (b : B) (n : ℤ) : H →ₗ[ℂ] O := (mu true b).coeff (-2*n-3)

private abbrev energy (M : ℤ) (x : tensor) : Prop :=
  actualTensorL0 ℒ U x = ((leechData.rank : ℂ) / 16 + (M : ℂ) / 2) • x

private abbrev ia (n : ℕ) : ℂ := (n.factorial : ℂ)⁻¹
private abbrev sg (n : ℕ) : ℂ := (-1 : ℂ)^n
private abbrev eps (n : ℤ) : ℂ := (-1 : ℂ)^n
private abbrev choose (n : ℤ) (j : ℕ) : ℂ := Ring.choose (n : ℂ) j
private abbrev phase (M m : ℤ) : ℂ := Complex.I ^ (M + 2*m + 2)

private theorem phase_shift (t k : ℤ) :
    Complex.I ^ (t + 2*k) = Complex.I ^ t * eps k := by
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul,
    show Complex.I ^ (2 : ℤ) = -1 from (zpow_natCast Complex.I 2).trans Complex.I_sq]

private theorem phase_split (M m : ℤ) (i j : ℕ) :
    Complex.I ^ (-(3 + M)) * Complex.I ^ (-2*(M-m-(i : ℤ)+(j : ℤ))-3) =
      phase M m * sg i * sg j := by
  have he : -(3+M)+(-2*(M-m-(i : ℤ)+(j : ℤ))-3) =
      (M + 2*m + 2 + 2*(i : ℤ) + 2*(j : ℤ)) + 2*(-2*M-4-2*(j : ℤ)) := by ring
  rw [← zpow_add₀ Complex.I_ne_zero, he, phase_shift, phase_shift, phase_shift,
    show -2*M-4-2*(j : ℤ) = 2*(-M-2-(j : ℤ)) by ring,
    show eps (2*(-M-2-(j : ℤ))) = 1 by
      unfold eps
      rw [zpow_mul, show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num, one_zpow], mul_one]
  simp [sg, eps, phase]


private theorem fixed_output (s : Bool) (a : A) (d m M : ℤ) (x : State s)
    (ha : a.val ∈ grade ℒ d) (hx : energy M x.val) :
    energy (M+2*d-2*m-2) (fixMode s a m x).val := by
  rw [fixedParityMode_val]
  convert HalfFock.ActualEnergyCovariance.correctedField_signed_output
    ℒ U d M (-2*m-2) a.val ha x.val hx using 2
  ring

private theorem tensor_lower_zero (s : Bool) (M : ℤ) (x : State s)
    (hx : energy M x.val) (n : ℕ) (hn : M < 2*(n : ℤ)) :
    (lowering ℒ U s ^ n) x = 0 := by
  apply Subtype.ext
  rw [lowering_pow_val]
  exact negative_eigen_zero ℒ U _ (by omega) _ (lowering_eigen ℒ U M x.val hx n)

private theorem fixed_tail_grade (s : Bool) (a : A) (d m M : ℤ) (x : State s)
    (ha : a.val ∈ grade ℒ d) (hx : energy M x.val) (hn : M+2*d-2*m-2 < 0) :
    fixMode s a m x = 0 :=
  Subtype.ext (negative_eigen_zero ℒ U _ hn _ (fixed_output s a d m M x ha hx))

private theorem pair_separates (x y : O)
    (h : ∀ o : O, βₒ x.val o.val = βₒ y.val o.val) : x = y := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate ℒ U).1
  intro a
  change βₒ (x.val-y.val) a = 0
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  let o : O := ⟨minusPart ℒ a, minusPart_mem a⟩
  exact (sourcePairing_minusPart_right x.val a x.property).symm.trans
    ((h o).trans (sourcePairing_minusPart_right y.val a y.property))

/-- Finite BPZ readout in signed oscillator degrees. Padding either range
keeps the same coefficient. This formulation covers zero vectors in negative
output degrees of actual fixed modes. -/
theorem pair_readout (M K m : ℤ) (b : B) (h : H) (o : O)
    (hb : energy M b.val) (hh : energy K h.val) (N : ℕ)
    (hM : M < 2*(N : ℤ)) (hK : K < 2*(N : ℤ)) :
    βₒ (P b m h).val o.val =
      phase M m * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (sg i * ia i * (sg j * ia j)) *
          βₘ ((lowering ℒ U false ^ j) h).val
            (J ℒ U true (M-m-(i : ℤ)+(j : ℤ)) o ((lowering ℒ U true ^ i) b)).val := by
  by_cases hMn : 0 ≤ M
  · by_cases hKn : 0 ≤ K
    · lift M to ℕ using hMn
      lift K to ℕ using hKn
      have hb' : b.val ∈ actualGrade ℒ U M := by
        rw [actualGrade_eigen]
        exact_mod_cast hb
      have hh' : h.val ∈ actualGrade ℒ U K := by
        rw [actualGrade_eigen]
        exact_mod_cast hh
      change βₒ (((mu true b).coeff (-2*m-3) h).val) o.val = _
      rw [mu_coeff_of_grade true M K m b h hb' hh',
        mixedPairState_pairing true M K m b h hb' hh', mixedPairing_finite true M K m b h hh' o]
      simp_rw [Finset.mul_sum]
      have hmN : M/2+1 ≤ N := by omega
      have hkN : K/2+1 ≤ N := by omega
      calc
        _ = ∑ i ∈ Finset.range (M/2+1), ∑ j ∈ Finset.range (K/2+1),
            phase (M : ℤ) m * ((sg i * ia i * (sg j * ia j)) *
              βₘ ((lowering ℒ U false ^ j) h).val
                (J ℒ U true ((M : ℤ)-m-(i : ℤ)+(j : ℤ)) o
                  ((lowering ℒ U true ^ i) b)).val) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [lowering_pow_val]
          have hp := phase_split (M : ℤ) m i j
          linear_combination (ia i * ia j *
            βₘ ((T ℒ U ^ j) h.val)
              (J ℒ U true ((M : ℤ)-m-(i : ℤ)+(j : ℤ)) o
                ((lowering ℒ U true ^ i) b)).val) * hp
        _ = _ := by
          calc
            _ = ∑ i ∈ Finset.range (M/2+1), ∑ j ∈ Finset.range N, _ := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_subset (Finset.range_mono hkN)
              intro j hj hout
              have hj' := Finset.mem_range.not.mp hout
              rw [tensor_lower_zero false (K : ℤ) h hh j (by omega)]
              simp
            _ = _ := by
              apply Finset.sum_subset (Finset.range_mono hmN)
              intro i hi hout
              have hi' := Finset.mem_range.not.mp hout
              simp [tensor_lower_zero true (M : ℤ) b hb i (by omega)]
    · have hz : h = 0 := Subtype.ext (negative_eigen_zero ℒ U K (by omega) h.val hh)
      simp [hz]
  · have hz : b = 0 := Subtype.ext (negative_eigen_zero ℒ U M (by omega) b.val hb)
    have hp : P (0 : B) m h = 0 := by
      change (mu true (0 : B)).coeff (-2*m-3) h = 0
      simp
    simp [hz, hp]


private theorem lowered_grade (a : A) (d : ℤ) (ha : a.val ∈ grade ℒ d) (l : ℕ) :
    (lowered a l).val ∈ grade ℒ (d-l) :=
  original_l1_grade ℒ U d a.val ha l

private theorem source_lower_zero (a : A) (d : ℤ) (ha : a.val ∈ grade ℒ d)
    (l : ℕ) (hl : d < l) : lowered a l = 0 :=
  Subtype.ext (original_negative_grade_zero ℒ leech_spec.2.2.1 _ _ (lowered_grade a d ha l)
    (by omega))

private theorem lower_energy (s : Bool) (M : ℤ) (x : State s)
    (hx : energy M x.val) (i : ℕ) :
    energy (M-2*(i : ℤ)) ((lowering ℒ U s ^ i) x).val := by
  rw [lowering_pow_val]
  exact lowering_eigen ℒ U M x.val hx i

private theorem lower_mode (s : Bool) (a : A) (d m : ℤ)
    (ha : a.val ∈ grade ℒ d) (x : State s) (n : ℕ) :
    ia n • (lowering ℒ U s ^ n) (fixMode s a m x) =
      ∑ i ∈ Finset.range (n+1), ∑ l ∈ Finset.range (n-i+1),
        (ia i * ia l * Ring.choose (2*(d : ℂ)-(m : ℂ)-(l : ℂ)-2) (n-i-l)) •
          fixMode s (lowered a l) (m+((n-i-l : ℕ) : ℤ)) ((lowering ℒ U s ^ i) x) := by
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_sum, lowering_pow_val, fixedParityMode_val]
  rw [lowering_field_expansion ℒ U d a.val ha n (-2*m-2) x.val]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  have hle := Finset.mem_range.mp hl
  have he : -2*m-2-2*((n-i : ℕ) : ℤ)+2*(l : ℤ) =
      -2*(m+((n-i-l : ℕ) : ℤ))-2 := by omega
  rw [he]
  congr 1
  have hc : 2*(d : ℂ)+(((-2*m-2 : ℤ) : ℂ))/2-(l : ℂ)-1 =
      2*(d : ℂ)-(m : ℂ)-(l : ℂ)-2 := by push_cast; ring
  rw [hc]
  simp [ia, div_eq_mul_inv, mul_inv_rev]
  ring

private abbrev sourceCutoff (a : A) : ℕ :=
  a.val.support.sup (fun c =>
    MvPolynomial.weightedTotalDegree (LatticeHalfFockFiniteCorrection.sourceWeight ℒ) (a.val c))

private theorem odd_adjoint (a : A) (d m : ℤ) (ha : a.val ∈ grade ℒ d)
    (x o : O) (N : ℕ) (hcut : sourceCutoff a < N) :
    βₒ (oddMode ℒ a m x).val o.val =
      eps d * ∑ l ∈ Finset.range N, ia l *
        βₒ x.val (oddMode ℒ (lowered a l) (2*d-m-2-l) o).val := by
  have law := SourceBPZ.AllStateTranspose.sourcePairing_allState ℒ U d m a.val ha x.val o.val
  change βₒ (oddMode ℒ a m x).val o.val =
      eps d * ∑ l ∈ Finset.range (sourceCutoff a + 1), ia l *
        βₒ x.val (oddMode ℒ (lowered a l) (2*d-(l : ℤ)-m-2) o).val at law
  rw [law]
  congr 1
  calc
    _ = ∑ l ∈ Finset.range (sourceCutoff a + 1), ia l *
        βₒ x.val (oddMode ℒ (lowered a l) (2*d-m-2-l) o).val := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [show 2*d-(l : ℤ)-m-2 = 2*d-m-2-l by ring]
    _ = _ := by
      have dh (l : ℕ) (hl : sourceCutoff a < l) : lowered a l = 0 := by
        apply Subtype.ext
        exact Module.End.pow_map_zero_of_le (by omega : sourceCutoff a + 1 ≤ l)
          (SourceMobius.actual_sugawara_one_bound ℒ U a.val)
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro l _ hl
      have hz := dh l (by have := Finset.mem_range.not.mp hl; omega)
      rw [hz]
      change ia l * βₒ x.val (((Y ℒ (0 : Carrier ℒ))[[2*d-m-2-l]]) o.val) = 0
      simp

private theorem twisted_adjoint (a : A) (d m : ℤ) (ha : a.val ∈ grade ℒ d)
    (x y : H) (N : ℕ) (hd : d < N) :
    βₘ (fixMode false a m x).val y.val =
      eps d * ∑ l ∈ Finset.range N, ia l *
        βₘ x.val (fixMode false (lowered a l) (2*d-m-2-l) y).val := by
  rw [fixedParityMode_val]
  rw [OriginalSkewAdjoints.actual_corrected_adjoint_of_grade ℒ U leech_spec.2.2.1
    d (-2*m-2) a.val ha x.val y.val]
  congr 1
  by_cases hn : 0 ≤ d
  · calc
      _ = ∑ l ∈ Finset.range (d.toNat + 1), ia l *
          βₘ x.val (fixMode false (lowered a l) (2*d-m-2-l) y).val := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [fixedParityMode_val]
        congr 3
        ring
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro l _ hl
        have hz : lowered a l = 0 := source_lower_zero a d ha l
          (by have := Finset.mem_range.not.mp hl; omega)
        have hz' : fixMode false (lowered a l) (2*d-m-2-l) y = 0 := by
          apply Subtype.ext
          rw [fixedParityMode_val, hz]
          simp
        simp [hz']
  · have hz : a = 0 := Subtype.ext (original_negative_grade_zero ℒ leech_spec.2.2.1 _ _ ha (by omega))
    subst a
    simp [fixedParityMode_val, lowered]


private abbrev down (s : Bool) (x : State s) (n : ℕ) : State s :=
  (lowering ℒ U s ^ n) x

private theorem lower_mode_sum (s : Bool) (a : A) (d m M : ℤ) (x : State s)
    (ha : a.val ∈ grade ℒ d) (hx : energy M x.val) (N : ℕ)
    (hN : M+2*d-2*m-2 < 2*(N : ℤ)) (F : ℕ → State s →ₗ[ℂ] ℂ) :
    (∑ n ∈ Finset.range N, sg n * ia n *
      F n (down s (fixMode s a m x) n)) =
    ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N,
      (sg i * ia i * (sg l * ia l) * sg k *
        Ring.choose (2*(d : ℂ)-(m : ℂ)-(l : ℂ)-2) k) *
          F (i+l+k) (fixMode s (lowered a l) (m+k) (down s x i)) := by
  let f (i l k : ℕ) :=
    (sg i * ia i * (sg l * ia l) * sg k *
      Ring.choose (2*(d : ℂ)-(m : ℂ)-(l : ℂ)-2) k) *
        F (i+l+k) (fixMode s (lowered a l) (m+k) (down s x i))
  change _ = ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N, f i l k
  rw [← lowering_triangle_to_cube N f]
  · apply Finset.sum_congr rfl
    intro n hn
    have law := congrArg (F n) (lower_mode s a d m ha x n)
    simp only [map_smul, map_sum, smul_eq_mul] at law
    rw [mul_assoc]
    rw [law, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hn' : i+l+(n-i-l) = n := by
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hl
      omega
    dsimp only [f]
    rw [hn']
    have hsign : sg i * sg l * sg (n-i-l) = sg n := by
      rw [← pow_add, ← pow_add, hn']
    linear_combination
      (ia i * ia l * Ring.choose (2*(d : ℂ)-(m : ℂ)-(l : ℂ)-2) (n-i-l) *
        F n (fixMode s (lowered a l) (m+(↑(n-i-l) : ℤ)) (down s x i))) * (-hsign)
  · intro i l k h
    have hz := fixed_tail_grade s (lowered a l) (d-l) (m+k) (M-2*(i : ℤ))
      (down s x i) (lowered_grade a d ha l) (lower_energy s M x hx i) (by omega)
    simp [f, hz]

private theorem fixed_slice_zero (s : Bool) (m : ℤ) (v : State s) :
    fixMode s (0 : A) m v = 0 := by
  apply Subtype.ext
  rw [fixedParityMode_val]
  simp

private theorem eps_even (n : ℤ) : eps (2*n) = 1 := by
  unfold eps
  rw [zpow_mul, show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num, one_zpow]

private theorem eps_add (m n : ℤ) : eps (m+n) = eps m * eps n := by
  exact zpow_add₀ (by norm_num) m n

private theorem composition_lowered (a : A) (l z : ℕ) :
    lowered (lowered a l) z = lowered a (l+z) := by
  apply Subtype.ext
  change (L ^ z) ((L ^ l) a.val) = (L ^ (l+z)) a.val
  rw [Nat.add_comm, pow_add, Module.End.mul_apply]

private abbrev residueP (M q r : ℤ) (i j : ℕ) : ℤ := M-q-r-i+j
private abbrev residueR (d p r : ℤ) (l : ℕ) : ℤ := 2*d-p-r-2-l
private abbrev prefactor (M q r d : ℤ) : ℂ := phase M (q+r) * eps d * eps r
private abbrev weight (i j l : ℕ) : ℂ := sg i * ia i * (sg j * ia j) * ia l
private abbrev productWeight (r : ℤ) (k : ℕ) : ℂ := sg k * choose r k

private def nativeIterate (a : A) (b : B) (h : H) (o : O)
    (M d p q r : ℤ) (i j l k : ℕ) : ℂ :=
  βₘ (down false h j).val
    (J ℒ U true (r+residueP M q r i j-k)
      (oddMode ℒ (lowered a l) (residueR d p r l+k) o) (down true b i)).val

private def nativeFirst (a : A) (b : B) (h : H) (o : O)
    (M d p q r : ℤ) (i j l k : ℕ) : ℂ :=
  βₘ (down false h j).val
    (fixMode false (lowered a l) (r+residueR d p r l-k)
      (J ℒ U true (residueP M q r i j+k) o (down true b i))).val

private def nativeSecond (a : A) (b : B) (h : H) (o : O)
    (M d p q r : ℤ) (i j l k : ℕ) : ℂ :=
  βₘ (down false h j).val
    (J ℒ U true (residueP M q r i j+residueR d p r l-k) o
      (fixMode true (lowered a l) (r+k) (down true b i))).val

private theorem phase_product (M q r : ℤ) (k : ℕ) :
    sg k * phase M (q+k) = phase M (q+r) * eps r := by
  have hf : phase M (q+(k : ℤ)) = phase M (q+r) * eps ((k : ℤ)-r) := by
    unfold phase
    rw [← phase_shift]
    congr 1
    ring
  rw [hf]
  unfold sg
  rw [← zpow_natCast]
  change eps (k : ℤ) * (phase M (q+r) * eps ((k : ℤ)-r)) = _
  rw [mul_left_comm, ← eps_add, show (k : ℤ)+((k : ℤ)-r) = r+2*((k : ℤ)-r) by ring,
    eps_add, eps_even, mul_one]

private theorem phase_iterate (M d p q r : ℤ) (k : ℕ) :
    phase (M+2*d-2*(r+k)-2) (p+q-k) =
      phase M (q+r) * eps (d+p-1) := by
  unfold phase
  rw [show M+2*d-2*(r+(k : ℤ))-2+2*(p+q-(k : ℤ))+2 =
      (M+2*(q+r)+2)+2*((d+p-1)+2*(-r-(k : ℤ))) by ring,
    phase_shift, eps_add, eps_even, mul_one]

private theorem phase_second (M q r : ℤ) (k : ℕ) :
    sg k * phase M (q+r-k) = phase M (q+r) := by
  have hf : phase M (q+r-(k : ℤ)) = phase M (q+r) * eps (-(k : ℤ)) := by
    unfold phase
    rw [← phase_shift]
    congr 1
    ring
  rw [hf]
  unfold sg
  rw [← zpow_natCast]
  change eps (k : ℤ) * (phase M (q+r) * eps (-(k : ℤ))) = _
  rw [mul_left_comm, ← eps_add, add_neg_cancel, show eps 0 = 1 by simp [eps], mul_one]

private theorem phase_iterate_weight (d p r : ℤ) (l : ℕ) :
    eps (d+p-1) * sg l = eps d * eps r * (-eps (residueR d p r l)) := by
  have he : d+p-1+(l : ℤ) =
      (d+r+(1+residueR d p r l))+2*(p+(l : ℤ)-d) := by dsimp [residueR]; ring
  unfold sg
  rw [← zpow_natCast]
  change eps (d+p-1) * eps (l : ℤ) = _
  rw [← eps_add, he, eps_add, eps_even, mul_one, eps_add (d+r), eps_add d r, eps_add 1]
  simp [eps]


private def leftTerm (a : A) (b : B) (h : H) (p q r : ℤ) (k : ℕ) : O :=
  choose p k • P (fixMode true a (r+k) b) (p+q-k) h

private def firstTerm (a : A) (b : B) (h : H) (p q r : ℤ) (k : ℕ) : O :=
  productWeight r k • oddMode ℒ a (p+r-k) (P b (q+k) h)

private def secondTerm (a : A) (b : B) (h : H) (p q r : ℤ) (k : ℕ) : O :=
  (eps r * productWeight r k) • P b (q+r-k) (fixMode false a (p+k) h)

private theorem sum_rotate {V : Type*} [AddCommMonoid V] (N : ℕ) (f : ℕ → ℕ → ℕ → V) :
    (∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j k) =
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, f i j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

/-- Transpose the fixed action on the odd lattice output. -/
private theorem first_transport (a : A) (b : B) (h : H) (o : O) (M K d p q r : ℤ)
    (hb : energy M b.val) (hh : energy K h.val) (ha : a.val ∈ grade ℒ d)
    (N : ℕ) (hM : M < 2*(N : ℤ)) (hK : K < 2*(N : ℤ)) (hcut : sourceCutoff a < N) :
    (∑ k ∈ Finset.range N, βₒ (firstTerm a b h p q r k).val o.val) =
      prefactor M q r d * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        weight i j l * ∑ k ∈ Finset.range N, choose r k * nativeIterate a b h o M d p q r i j l k := by
  let f (i j l k : ℕ) := weight i j l * (choose r k * nativeIterate a b h o M d p q r i j l k)
  calc
    _ = ∑ k ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range N,
        ∑ j ∈ Finset.range N, prefactor M q r d * f i j l k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [firstTerm, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [odd_adjoint a d _ ha _ o N hcut]
      simp_rw [pair_readout M K (q+(k : ℤ)) b h _ hb hh N hM hK, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have he : 2*d-(p+r-(k : ℤ))-2-(l : ℤ) = residueR d p r l+k := by ring
      have hf : M-(q+(k : ℤ))-(i : ℤ)+(j : ℤ) = r+residueP M q r i j-k := by ring
      rw [he, hf]
      change productWeight r k * (eps d * (ia l *
        (phase M (q+(k : ℤ)) * ((sg i * ia i * (sg j * ia j)) *
          nativeIterate a b h o M d p q r i j l k)))) = _
      unfold productWeight prefactor f
      rw [show ∀ c x y : ℂ, c*x*y = c*(x*y) from mul_assoc]
      linear_combination (choose r k * eps d * ia l * (sg i * ia i * (sg j * ia j)) *
        nativeIterate a b h o M d p q r i j l k) * phase_product M q r k
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        intro l
        rw [sum_rotate]
      rw [sum_rotate]


/-- Lower the actual iterate on the odd twisted input and collect the signed binomials. -/
private theorem iterate_transport (a : A) (b : B) (h : H) (o : O) (M K d p q r : ℤ)
    (hb : energy M b.val) (hh : energy K h.val) (ha : a.val ∈ grade ℒ d)
    (N : ℕ) (hB : M+2*d-2*r-2 < 2*(N : ℤ)) (hK : K < 2*(N : ℤ)) :
    (∑ k ∈ Finset.range N, βₒ (leftTerm a b h p q r k).val o.val) =
      prefactor M q r d * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        weight i j l * (-eps (residueR d p r l)) *
          ∑ k ∈ Finset.range N, productWeight (residueR d p r l) k *
            nativeSecond a b h o M d p q r i j l k := by
  let f (i j l k t : ℕ) :=
    choose p k * sg t * Ring.choose (2*(d : ℂ)-(r : ℂ)-(l : ℂ)-2-(k : ℂ)) t *
      nativeSecond a b h o M d p q r i j l (k+t)
  let scale (i j l : ℕ) := phase M (q+r) * eps (d+p-1) * weight i j l * sg l
  have transport (k j : ℕ) :
      (∑ n ∈ Finset.range N, sg n * ia n *
        βₘ (down false h j).val
          (J ℒ U true (M+2*d-2*(r+k)-2-(p+q-k)-n+j) o
            (down true (fixMode true a (r+k) b) n)).val) =
      ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ t ∈ Finset.range N,
        ((sg i * ia i * (sg l * ia l)) * sg t *
          Ring.choose (2*(d : ℂ)-(r : ℂ)-(l : ℂ)-2-(k : ℂ)) t) *
          nativeSecond a b h o M d p q r i j l (k+t) := by
    let F (n : ℕ) : B →ₗ[ℂ] ℂ :=
      ((βₘ (down false h j).val).comp (paritySpace ℒ U (paritySign false)).subtype).comp
        (J ℒ U true (M+2*d-2*(r+k)-2-(p+q-k)-n+j) o)
    have law := lower_mode_sum true a d (r+k) M b ha hb N (by omega) F
    change _ = _ at law
    simp_rw [show ∀ l : ℕ, 2*(d : ℂ)-((r+(k : ℤ) : ℤ) : ℂ)-(l : ℂ)-2 =
      2*(d : ℂ)-(r : ℂ)-(l : ℂ)-2-(k : ℂ) by intro l; push_cast; ring] at law
    refine law.trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [F, LinearMap.comp_apply, Submodule.subtype_apply, nativeSecond]
    push_cast
    have e1 : M+2*d-2*(r+(k : ℤ))-2-(p+q-(k : ℤ))-((i : ℤ)+l+t)+j =
        residueP M q r i j+residueR d p r l-((k : ℤ)+t) := by ring
    rw [e1, show r+(k : ℤ)+t = r+((k : ℤ)+t) by ring]
    rfl
  calc
    _ = ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N,
        ∑ l ∈ Finset.range N, ∑ t ∈ Finset.range N, scale i j l * f i j l k t := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [leftTerm, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [pair_readout _ K (p+q-k) _ h o
        (fixed_output true a d (r+k) M b ha hb) hh N (by omega) hK,
        phase_iterate M d p q r k]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have he : ∀ n : ℕ, choose p k *
          ((phase M (q+r) * eps (d+p-1)) *
            (sg n * ia n * (sg j * ia j) *
              βₘ (down false h j).val
                (J ℒ U true (M+2*d-2*(r+k)-2-(p+q-k)-n+j) o
                  (down true (fixMode true a (r+k) b) n)).val)) =
          (choose p k * (phase M (q+r) * eps (d+p-1)) * (sg j * ia j)) *
            (sg n * ia n *
              βₘ (down false h j).val
                (J ℒ U true (M+2*d-2*(r+k)-2-(p+q-k)-n+j) o
                  (down true (fixMode true a (r+k) b) n)).val) := by
        intro n
        ring
      simp_rw [he, ← Finset.mul_sum]
      rw [transport k j]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro t ht
      unfold scale f weight
      ring
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        scale i j l * ∑ k ∈ Finset.range N, ∑ t ∈ Finset.range N, f i j l k t := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        intro j
        rw [sum_rotate]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      simp_rw [← Finset.mul_sum]
      have tail (k : ℕ) (hk : N ≤ k) : nativeSecond a b h o M d p q r i j l k = 0 := by
        unfold nativeSecond
        rw [fixed_tail_grade true (lowered a l) (d-l) (r+k) (M-2*(i : ℤ))
          (down true b i) (lowered_grade a d ha l) (lower_energy true M b hb i) (by omega)]
        simp
      have contract := signed_supported_transform N
        (nativeSecond a b h o M d p q r i j l) tail (p : ℂ)
        (2*(d : ℂ)-(r : ℂ)-(l : ℂ)-2)
      have hcast : 2*(d : ℂ)-(r : ℂ)-(l : ℂ)-2-(p : ℂ) =
          (residueR d p r l : ℂ) := by
        unfold residueR
        push_cast
        ring
      rw [hcast] at contract
      dsimp only [f, choose, sg, productWeight]
      rw [contract]
      unfold scale prefactor
      linear_combination (phase M (q+r) * weight i j l *
        (∑ k ∈ Finset.range N, productWeight (residueR d p r l) k *
          nativeSecond a b h o M d p q r i j l k)) * phase_iterate_weight d p r l


/-- Lower the actual even twisted input and transpose its fixed action. -/
private theorem second_lower_transport (a : A) (b : B) (h : H) (o : O)
    (M K d p q r : ℤ) (hh : energy K h.val) (ha : a.val ∈ grade ℒ d)
    (N : ℕ) (hH : K+2*d-2*p-2 < 2*(N : ℤ)) (hd : d < N) (i k : ℕ) :
    (∑ n ∈ Finset.range N, sg n * ia n *
      βₘ (down false (fixMode false a (p+k) h) n).val
        (J ℒ U true (M-(q+r-k)-i+n) o (down true b i)).val) =
    eps d * ∑ j ∈ Finset.range N, sg j * ia j *
      ∑ l ∈ Finset.range N, ∑ z ∈ Finset.range N, (ia l * ia z) *
        ∑ t ∈ Finset.range N, sg t *
          Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
            nativeFirst a b h o M d p q r i j (l+z) (k+l+t) := by
  let F (n : ℕ) : H →ₗ[ℂ] ℂ :=
    (((βₘ).flip (J ℒ U true (M-(q+r-k)-i+n) o (down true b i)).val).comp
      (paritySpace ℒ U (paritySign false)).subtype)
  have law := lower_mode_sum false a d (p+k) K h ha hh N (by omega) F
  trans ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ t ∈ Finset.range N,
      (sg j * ia j * (sg l * ia l) * sg t *
        Ring.choose (2*(d : ℂ)-((p+(k : ℤ) : ℤ) : ℂ)-(l : ℂ)-2) t) *
      F (j+l+t) (fixMode false (lowered a l) (p+k+t) (down false h j))
  · exact law
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only [F, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.BilinForm.flip_apply]
  rw [twisted_adjoint (lowered a l) (d-l) (p+k+t) (lowered_grade a d ha l) _ _ N (by omega)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [composition_lowered]
  have e1 : 2*(d-(l : ℤ))-(p+(k : ℤ)+(t : ℤ))-2-(z : ℤ) =
      r+residueR d p r (l+z)-((k+l+t : ℕ) : ℤ) := by unfold residueR; push_cast; ring
  have e2 : M-(q+r-(k : ℤ))-(i : ℤ)+((j+l+t : ℕ) : ℤ) =
      residueP M q r i j+((k+l+t : ℕ) : ℤ) := by unfold residueP; push_cast; ring
  rw [e1, e2]
  have hc : 2*(d : ℂ)-((p+(k : ℤ) : ℤ) : ℂ)-(l : ℂ)-2 =
      2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ) := by push_cast; ring
  rw [hc]
  have hs : sg l * eps (d-(l : ℤ)) = eps d := by
    unfold sg
    rw [← zpow_natCast]
    change eps (l : ℤ) * eps (d-(l : ℤ)) = _
    rw [← eps_add, show (l : ℤ)+(d-(l : ℤ)) = d by ring]
  change _ = eps d * (sg j * ia j * (ia l * ia z *
    (sg t * Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
      nativeFirst a b h o M d p q r i j (l+z) (k+l+t))))
  have hs' : (sg l * ia l) * eps (d-(l : ℤ)) = ia l * eps d := by
    rw [mul_comm (sg l) (ia l), mul_assoc, hs]
  change (sg j * ia j * (sg l * ia l) * sg t *
      Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t) *
      (eps (d-(l : ℤ)) * (ia z * nativeFirst a b h o M d p q r i j (l+z) (k+l+t))) =
      _
  linear_combination (sg j * ia j * sg t *
    Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t * ia z *
      nativeFirst a b h o M d p q r i j (l+z) (k+l+t)) * hs'

private theorem second_contract (a : A) (b : B) (h : H) (o : O)
    (M d p q r : ℤ) (ha : a.val ∈ grade ℒ d) (hb : energy M b.val)
    (E : ℤ) (ho : o.val ∈ grade ℒ E)
    (N : ℕ) (hd : d < N) (hJ : -M+2*E+2*(q+r)-3 < 2*(N : ℤ))
    (i j : ℕ) :
    (∑ k ∈ Finset.range N, choose r k * ∑ l ∈ Finset.range N, ∑ z ∈ Finset.range N,
      (ia l * ia z) * ∑ t ∈ Finset.range N, sg t *
        Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
          nativeFirst a b h o M d p q r i j (l+z) (k+l+t)) =
    ∑ Lc ∈ Finset.range N, ia Lc * ∑ k ∈ Finset.range N,
      productWeight (residueR d p r Lc) k * nativeFirst a b h o M d p q r i j Lc k := by
  let F (k l z : ℕ) := ∑ t ∈ Finset.range N, sg t *
    Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
      nativeFirst a b h o M d p q r i j (l+z) (k+l+t)
  change (∑ k ∈ Finset.range N, choose r k * ∑ l ∈ Finset.range N, ∑ z ∈ Finset.range N,
    (ia l * ia z) * F k l z) = _
  have tail (Lx k : ℕ) (hk : N ≤ k) :
      nativeFirst a b h o M d p q r i j Lx k = 0 := by
    unfold nativeFirst
    have hz : J ℒ U true (residueP M q r i j+k) o (down true b i) = 0 := by
      apply Subtype.ext
      rw [J_val]
      apply negative_eigen_zero ℒ U
        (M-2*(i : ℤ)+(-2*(residueP M q r i j+k)-3)+2*E)
      · unfold residueP
        omega
      · exact HalfFock.ActualEnergyCovariance.correctedField_signed_output ℒ U E _ _
          o.val ho _ (lower_energy true M b hb i)
    rw [hz]
    simp
  have ltail (Lc k : ℕ) (hl : N ≤ Lc) :
      nativeFirst a b h o M d p q r i j Lc k = 0 := by
    unfold nativeFirst
    rw [source_lower_zero a d ha Lc (by omega), fixed_slice_zero]
    simp
  have ftail (k l z : ℕ) (h : N ≤ l+z) : F k l z = 0 := by
    unfold F
    simp_rw [ltail (l+z) _ h, mul_zero, Finset.sum_const_zero]
  have hdg (k : ℕ) :
      (∑ l ∈ Finset.range N, ∑ z ∈ Finset.range N, (ia l * ia z) * F k l z) =
      ∑ Lc ∈ Finset.range N, ∑ l ∈ Finset.range (Lc+1),
        (Ring.choose (Lc : ℂ) l / (Lc.factorial : ℂ)) * F k l (Lc-l) := by
    rw [MixedIntertwiner.twice_signed_supported_factorial_contraction N (F k)
      (by intro l z hout; exact ftail k l z (by omega))]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro Lc hLc hout
    apply Finset.sum_eq_zero
    intro l hl
    have hle : l ≤ Lc := by simpa using Finset.mem_range.mp hl
    rw [ftail k l (Lc-l) (by have := Finset.mem_range.not.mp hout; omega), mul_zero]
  simp_rw [hdg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Lc hLc
  have diag : (∑ k ∈ Finset.range N, ∑ l ∈ Finset.range (Lc+1),
      choose r k * (Ring.choose (Lc : ℂ) l / (Lc.factorial : ℂ) * F k l (Lc-l))) =
      ia Lc * ∑ l ∈ Finset.range N, ∑ k ∈ Finset.range N, ∑ t ∈ Finset.range N,
        Ring.choose (Lc : ℂ) l * choose r k * sg t *
          Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
          nativeFirst a b h o M d p q r i j Lc (k+l+t) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ l ∈ Finset.range (Lc+1), ∑ k ∈ Finset.range N, ∑ t ∈ Finset.range N,
          ia Lc * (Ring.choose (Lc : ℂ) l * choose r k * sg t *
            Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
              nativeFirst a b h o M d p q r i j Lc (k+l+t)) := by
        apply Finset.sum_congr rfl
        intro l hl
        have hle : l ≤ Lc := by have := Finset.mem_range.mp hl; omega
        unfold F
        simp_rw [Finset.mul_sum, Nat.add_sub_of_le hle]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro t _
        unfold ia
        ring
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by have := Finset.mem_range.mp hLc; omega))
        intro l _ hl
        have hz : Ring.choose (Lc : ℂ) l = 0 := by
          rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by
            have := Finset.mem_range.not.mp hl
            omega), Nat.cast_zero]
        simp_rw [hz, zero_mul, mul_zero, Finset.sum_const_zero]
  rw [diag]
  have contraction := twice_signed_transform N Lc (r : ℂ) (2*(d : ℂ)-(p : ℂ)-2)
    (nativeFirst a b h o M d p q r i j Lc) (tail Lc)
  have hc : 2*(d : ℂ)-(p : ℂ)-2-(r : ℂ)-(Lc : ℂ) = (residueR d p r Lc : ℂ) := by
    unfold residueR
    push_cast
    ring
  rw [hc] at contraction
  simpa only [Finset.mul_sum, productWeight, choose, sg] using
    congrArg (fun z : ℂ => ia Lc * z) contraction


private theorem second_transport (a : A) (b : B) (h : H) (o : O)
    (M K d p q r E : ℤ) (hb : energy M b.val) (hh : energy K h.val)
    (ha : a.val ∈ grade ℒ d) (ho : o.val ∈ grade ℒ E)
    (N : ℕ) (hM : M < 2*(N : ℤ)) (hH : K+2*d-2*p-2 < 2*(N : ℤ))
    (hd : d < N) (hJ : -M+2*E+2*(q+r)-3 < 2*(N : ℤ)) :
    (∑ k ∈ Finset.range N, βₒ (secondTerm a b h p q r k).val o.val) =
      prefactor M q r d * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        weight i j l * ∑ k ∈ Finset.range N, productWeight (residueR d p r l) k *
          nativeFirst a b h o M d p q r i j l k := by
  let F (i j k : ℕ) := choose r k * ∑ l ∈ Finset.range N, ∑ z ∈ Finset.range N,
    (ia l * ia z) * ∑ t ∈ Finset.range N, sg t *
      Ring.choose (2*(d : ℂ)-(p : ℂ)-2-(k : ℂ)-(l : ℂ)) t *
        nativeFirst a b h o M d p q r i j (l+z) (k+l+t)
  calc
    _ = ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (prefactor M q r d * (sg i * ia i * (sg j * ia j))) * F i j k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [secondTerm, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [pair_readout M _ (q+r-k) b _ o hb
        (fixed_output false a d (p+k) K h ha hh) N hM (by omega)]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have he (n : ℕ) :
          (eps r * productWeight r k) * (phase M (q+r-k) *
            (sg i * ia i * (sg n * ia n) * βₘ
              (down false (fixMode false a (p+k) h) n).val
              (J ℒ U true (M-(q+r-k)-i+n) o (down true b i)).val)) =
          (phase M (q+r) * eps r * choose r k * (sg i * ia i)) *
            (sg n * ia n * βₘ (down false (fixMode false a (p+k) h) n).val
              (J ℒ U true (M-(q+r-k)-i+n) o (down true b i)).val) := by
        unfold productWeight
        linear_combination (eps r * choose r k * (sg i * ia i) * (sg n * ia n) *
          βₘ (down false (fixMode false a (p+k) h) n).val
            (J ℒ U true (M-(q+r-k)-i+n) o (down true b i)).val) * phase_second M q r k
      simp_rw [he, ← Finset.mul_sum]
      rw [second_lower_transport a b h o M K d p q r hh ha N hH hd i k]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      unfold F prefactor
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by
      rw [sum_rotate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
      unfold F
      rw [second_contract a b h o M d p q r ha hb E ho N hd hJ i j]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      unfold weight
      ring

private theorem mode_tail (s : Bool) (a : A) (x : State s) (m : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → fixMode s a (m+k) x = 0 := by
  let F := fixedParitySlice ℒ U (paritySign s) a
  let v : ℤ := ((HahnModule.of ℂ).symm (F x)).order
  refine ⟨(-m-1-v).toNat+1, fun k hk =>
    VertexOperator.ncoeff_eq_zero_of_lt_order F (m+k) x ?_⟩
  change -(m+(k : ℤ))-1 < v
  omega

private theorem pair_tail (b : B) (h : H) (q : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → P b (q+k) h = 0 := by
  let V : ℤ := (ActualEnergyRestrictedDual.maxOddWeight ℒ U b.val : ℤ) +
    (ActualEnergyRestrictedDual.maxOddWeight ℒ U h.val : ℤ) + 6
  refine ⟨(V-q).toNat+2, fun k hk => ?_⟩
  apply mu_lower_truncation true b h
  dsimp [V] at hk
  omega

private theorem term_support {V : Type*} [Zero V] (f : ℕ → V)
    (N : ℕ) (tail : ∀ j, N ≤ j → f j = 0) :
    Function.support f ⊆ (Finset.range N : Set ℕ) := by
  intro j hj
  exact Finset.mem_range.mpr (lt_of_not_ge fun hj' => hj (tail j hj'))

private theorem term_finite (a : A) (b : B) (h : H) (p q r : ℤ) :
    Function.HasFiniteSupport (leftTerm a b h p q r) ∧
    Function.HasFiniteSupport (firstTerm a b h p q r) ∧
    Function.HasFiniteSupport (secondTerm a b h p q r) := by
  obtain ⟨N₁, h₁⟩ := mode_tail true a b r
  obtain ⟨N₂, h₂⟩ := pair_tail b h q
  obtain ⟨N₃, h₃⟩ := mode_tail false a h p
  refine ⟨(Finset.range N₁).finite_toSet.subset (term_support _ N₁ fun j hj => ?_),
    (Finset.range N₂).finite_toSet.subset (term_support _ N₂ fun j hj => ?_),
    (Finset.range N₃).finite_toSet.subset (term_support _ N₃ fun j hj => ?_)⟩
  · have hz : P (0 : B) (p+q-j) h = 0 := by
      change (mu true (0 : B)).coeff _ h = _
      simp
    simp only [leftTerm, h₁ j hj, hz, smul_zero]
  · simp only [firstTerm, h₂ j hj, map_zero, smul_zero]
  · simp only [secondTerm, h₃ j hj, map_zero, smul_zero]

private theorem map_finite_sum {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (F : V →ₗ[ℂ] W) (f : ℕ → V)
    (hf : Function.HasFiniteSupport f) :
    F (∑ᶠ k, f k) = ∑ᶠ k, F (f k) :=
  F.toAddMonoidHom.map_finsum hf

private theorem paired_balance {V : Type*} [AddCommMonoid V] [Module ℂ V] [Sub V]
    (F : V →ₗ[ℂ] ℂ) (mapdiff : ∀ x y : V, F (x-y) = F x - F y) (f g h : ℕ → V)
    (hf : Function.HasFiniteSupport f) (hg : Function.HasFiniteSupport g)
    (hh : Function.HasFiniteSupport h)
    (he : (∑ᶠ k, f k) = (∑ᶠ k, g k) - (∑ᶠ k, h k)) :
    (∑ᶠ k, F (f k)) = (∑ᶠ k, F (g k)) - (∑ᶠ k, F (h k)) := by
  rw [← map_finite_sum F f hf, ← map_finite_sum F g hg, ← map_finite_sum F h hh,
    he, mapdiff]

private theorem native_balance (a : A) (b : B) (h : H) (o : O)
    (M d p q r E : ℤ) (hb : energy M b.val) (ha : a.val ∈ grade ℒ d)
    (ho : o.val ∈ grade ℒ E) (N : ℕ)
    (hJ : -M+2*E+2*(q+r)-3 < 2*(N : ℤ)) (hB : M+2*d-2*r-2 < 2*(N : ℤ))
    (hO : E-d+p+r+1 < N) (i j l : ℕ) :
    (∑ k ∈ Finset.range N, choose r k * nativeIterate a b h o M d p q r i j l k) =
    (∑ k ∈ Finset.range N, productWeight (residueR d p r l) k *
      nativeFirst a b h o M d p q r i j l k) -
      eps (residueR d p r l) * ∑ k ∈ Finset.range N, productWeight (residueR d p r l) k *
        nativeSecond a b h o M d p q r i j l k := by
  let p' := r
  let q' := residueP M q r i j
  let r' := residueR d p r l
  let a' := lowered a l
  let b' := down true b i
  let det : H →ₗ[ℂ] ℂ := ((βₘ (down false h j).val).comp (paritySpace ℒ U (paritySign false)).subtype)
  have law := J_borcherds ℒ U true a' o b' p' q' r'
  dsimp only at law
  have hb' := lower_energy true M b hb i
  have ha' := lowered_grade a d ha l
  have tail₁ (k : ℕ) (hk : N ≤ k) : oddMode ℒ a' (r'+k) o = 0 := by
    apply Subtype.ext
    rw [oddMode_val]
    apply original_negative_grade_zero ℒ leech_spec.2.2.1
      (d-(l : ℤ)+E-(r'+k)-1)
    · exact positive_actual_mode_grade ℒ leech_spec.2.2.1 _ _ _ a'.val o.val ha' ho
    · unfold r' residueR
      omega
  have tail₂ (k : ℕ) (hk : N ≤ k) : J ℒ U true (q'+k) o b' = 0 := by
    apply Subtype.ext
    rw [J_val]
    apply negative_eigen_zero ℒ U (M-2*(i : ℤ)+(-2*(q'+k)-3)+2*E)
    · unfold q' residueP
      omega
    · exact HalfFock.ActualEnergyCovariance.correctedField_signed_output ℒ U E _ _ o.val ho _ hb'
  have tail₃ (k : ℕ) (hk : N ≤ k) : fixMode true a' (p'+k) b' = 0 :=
    fixed_tail_grade true a' _ _ _ b' ha' hb' (by unfold p'; omega)
  have binom (z : ℤ) (k : ℕ) :
      StateFieldResidueReconstruction.integerBinomial z k = choose z k :=
    Ring.map_choose (Int.castRingHom ℂ) z k
  have mapdiff (x y : H) : det (x-y) = det x - det y := LinearMap.map_sub det x y
  have e := paired_balance det mapdiff _ _ _ law.1 law.2.1 law.2.2.1 law.2.2.2
  simp only [det, LinearMap.comp_apply, Submodule.subtype_apply, map_smul,
    smul_eq_mul, binom, StateFieldResidueReconstruction.epsilon] at e
  have ev₁ : Function.support (fun k => choose r k * nativeIterate a b h o M d p q r i j l k) ⊆
      (Finset.range N : Set ℕ) :=
    term_support _ N (by
      intro k hk
      unfold nativeIterate
      rw [tail₁ k hk]
      simp)
  have ev₂ : Function.support
      (fun k => productWeight r' k * nativeFirst a b h o M d p q r i j l k) ⊆
      (Finset.range N : Set ℕ) :=
    term_support _ N (by
      intro k hk
      unfold nativeFirst
      rw [tail₂ k hk]
      simp)
  have ev₃ : Function.support
      (fun k => productWeight r' k * (eps r' * nativeSecond a b h o M d p q r i j l k)) ⊆
      (Finset.range N : Set ℕ) :=
    term_support _ N (by
      intro k hk
      unfold nativeSecond
      rw [tail₃ k hk]
      simp)
  change (∑ᶠ k, choose r k * nativeIterate a b h o M d p q r i j l k) =
    (∑ᶠ k, productWeight r' k * nativeFirst a b h o M d p q r i j l k) -
    (∑ᶠ k, productWeight r' k * (eps r' * nativeSecond a b h o M d p q r i j l k)) at e
  rw [finsum_eq_sum_of_support_subset _ ev₁, finsum_eq_sum_of_support_subset _ ev₂,
    finsum_eq_sum_of_support_subset _ ev₃] at e
  rw [e, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring


private theorem scalar_homogeneous (a : A) (b : B) (h : H) (o : O)
    (M K d E p q r : ℤ) (hb : energy M b.val) (hh : energy K h.val)
    (ha : a.val ∈ grade ℒ d) (ho : o.val ∈ grade ℒ E) :
    (∑ᶠ k, βₒ (leftTerm a b h p q r k).val o.val) =
      (∑ᶠ k, βₒ (firstTerm a b h p q r k).val o.val) -
      (∑ᶠ k, βₒ (secondTerm a b h p q r k).val o.val) := by
  obtain ⟨n, hn⟩ := pair_tail b h q
  let N := n + sourceCutoff a + M.toNat + K.toNat + d.toNat + E.toNat +
    p.natAbs + q.natAbs + r.natAbs + M.natAbs + d.natAbs + 5
  have hM : M < 2*(N : ℤ) := by dsimp [N]; omega
  have hK : K < 2*(N : ℤ) := by dsimp [N]; omega
  have hd : d < N := by dsimp [N]; omega
  have hcut : sourceCutoff a < N := by dsimp [N]; omega
  have hB : M+2*d-2*r-2 < 2*(N : ℤ) := by dsimp [N]; omega
  have hH : K+2*d-2*p-2 < 2*(N : ℤ) := by dsimp [N]; omega
  have hJ : -M+2*E+2*(q+r)-3 < 2*(N : ℤ) := by dsimp [N]; omega
  have hO : E-d+p+r+1 < N := by dsimp [N]; omega
  have ltail (k : ℕ) (hk : N ≤ k) : βₒ (leftTerm a b h p q r k).val o.val = 0 := by
    have hz : P (0 : B) (p+q-k) h = 0 := by
      change (mu true (0 : B)).coeff _ h = _
      simp
    unfold leftTerm
    rw [fixed_tail_grade true a d (r+k) M b ha hb (by omega), hz]
    simp
  have ftail (k : ℕ) (hk : N ≤ k) : βₒ (firstTerm a b h p q r k).val o.val = 0 := by
    have hk' : n ≤ k := by dsimp [N] at hk; omega
    simp [firstTerm, hn k hk']
  have stail (k : ℕ) (hk : N ≤ k) : βₒ (secondTerm a b h p q r k).val o.val = 0 := by
    unfold secondTerm
    rw [fixed_tail_grade false a d (p+k) K h ha hh (by omega)]
    simp
  rw [finsum_eq_sum_of_support_subset _ (term_support _ N ltail),
    finsum_eq_sum_of_support_subset _ (term_support _ N ftail),
    finsum_eq_sum_of_support_subset _ (term_support _ N stail),
    iterate_transport a b h o M K d p q r hb hh ha N hB hK,
    first_transport a b h o M K d p q r hb hh ha N hM hK hcut,
    second_transport a b h o M K d p q r E hb hh ha ho N hM hH hd hJ]
  simp_rw [← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℂ => prefactor M q r d * z)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [native_balance a b h o M d p q r E hb ha ho N hJ hB hO i j l]
  ring


private def coeffPair (o : O) : O →ₗ[ℂ] ℂ :=
  ((βₒ).flip o.val).comp (minusSpace ℒ).subtype

private def JacobiAt (a : A) (b : B) (h : H) (p q r : ℤ) : Prop :=
  ∑ᶠ k, leftTerm a b h p q r k =
    (∑ᶠ k, firstTerm a b h p q r k) - (∑ᶠ k, secondTerm a b h p q r k)

private theorem separates_by_grade (x y : O)
    (equal : ∀ (E : ℤ) (o : O), o.val ∈ grade ℒ E → βₒ x.val o.val = βₒ y.val o.val) :
    x = y := by
  apply pair_separates
  intro o
  let fx : O →ₗ[ℂ] ℂ := (βₒ x.val).comp (minusSpace ℒ).subtype
  let fy : O →ₗ[ℂ] ℂ := (βₒ y.val).comp (minusSpace ℒ).subtype
  change fx o = fy o
  rw [← sum_oddGradeProjections o, map_sum fx, map_sum fy]
  apply Finset.sum_congr rfl
  intro E hE
  exact equal E _ (oddGradeProjection E o).property.1

private theorem pair_finsum (o : O) (f : ℕ → O) (hf : Function.HasFiniteSupport f) :
    βₒ (∑ᶠ k, f k).val o.val = ∑ᶠ k, βₒ (f k).val o.val :=
  map_finite_sum (coeffPair o) f hf

private theorem pair_sub (o x y : O) :
    βₒ (x-y).val o.val = βₒ x.val o.val - βₒ y.val o.val := by
  change coeffPair o (x-y) = coeffPair o x - coeffPair o y
  exact LinearMap.map_sub (coeffPair o) x y

private theorem homogeneous (a : A) (b : B) (h : H)
    (M K d p q r : ℤ) (hb : energy M b.val) (hh : energy K h.val)
    (ha : a.val ∈ grade ℒ d) : JacobiAt a b h p q r := by
  obtain ⟨hl, hf, hs⟩ := term_finite a b h p q r
  unfold JacobiAt
  apply separates_by_grade
  intro E o ho
  rw [pair_sub, pair_finsum o (leftTerm a b h p q r) hl,
    pair_finsum o (firstTerm a b h p q r) hf, pair_finsum o (secondTerm a b h p q r) hs]
  exact scalar_homogeneous a b h o M K d E p q r hb hh ha ho

private def pairMap (n : ℤ) : B →ₗ[ℂ] H →ₗ[ℂ] O :=
  (LinearMap.proj (-2*n-3)).comp (HVertexOperator.coeff.comp (mu true))

private def fixedMap (s : Bool) (n : ℤ) : A →ₗ[ℂ] Module.End ℂ (State s) where
  toFun a := fixMode s a n
  map_add' a b := by
    ext x
    change (fixMode s (a+b) n x).val = (fixMode s a n x + fixMode s b n x).val
    simp only [fixedParityMode_val, Submodule.coe_add, map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' c a := by
    ext x
    change (fixMode s (c • a) n x).val = (c • fixMode s a n x).val
    simp only [fixedParityMode_val, Submodule.coe_smul, map_smul, Pi.smul_apply, LinearMap.smul_apply]

private def oddMap (n : ℤ) : A →ₗ[ℂ] Module.End ℂ O where
  toFun a := oddMode ℒ a n
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (oddMode ℒ (a+b) n x).val = (oddMode ℒ a n x + oddMode ℒ b n x).val
    change ((Y ℒ (a.val+b.val))[[n]]) x.val = ((Y ℒ a.val)[[n]]) x.val + ((Y ℒ b.val)[[n]]) x.val
    simp only [map_add, VertexOperator.ncoeff, Pi.add_apply, LinearMap.add_apply]
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (oddMode ℒ (c • a) n x).val = (c • oddMode ℒ a n x).val
    change ((Y ℒ (c • a.val))[[n]]) x.val = c • ((Y ℒ a.val)[[n]]) x.val
    simp only [map_smul, VertexOperator.ncoeff, Pi.smul_apply,
      LinearMap.smul_apply]

private def seriesMap {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : ℕ → X →ₗ[ℂ] O) (hf : ∀ x, Function.HasFiniteSupport (fun k => f k x)) : X →ₗ[ℂ] O where
  toFun x := ∑ᶠ k, f k x
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib (hf x) (hf y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum c (fun k => f k x)).symm

private def difference {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f g : X →ₗ[ℂ] O) : X →ₗ[ℂ] O where
  toFun x := f x - g x
  map_add' x y := by
    simp only [map_add]
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add]
    abel
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul, smul_sub]

private theorem series_equal {X ι : Type*} [AddCommGroup X] [Module ℂ X]
    (f g h : ℕ → X →ₗ[ℂ] O)
    (hs : ∀ x, Function.HasFiniteSupport (fun k => f k x) ∧
      Function.HasFiniteSupport (fun k => g k x) ∧ Function.HasFiniteSupport (fun k => h k x))
    (x : X) (idx : Finset ι) (v : ι → X) (hv : (∑ i ∈ idx, v i) = x)
    (eqv : ∀ i ∈ idx, ∑ᶠ k, f k (v i) =
      (∑ᶠ k, g k (v i)) - (∑ᶠ k, h k (v i))) :
    ∑ᶠ k, f k x = (∑ᶠ k, g k x) - (∑ᶠ k, h k x) := by
  let F := seriesMap f (fun x => (hs x).1)
  let G := difference (seriesMap g (fun x => (hs x).2.1)) (seriesMap h (fun x => (hs x).2.2))
  change F x = G x
  rw [← hv, map_sum, map_sum]
  exact Finset.sum_congr rfl eqv

private theorem expand_twisted (s : Bool) (x : State s)
    (F G : State s →ₗ[ℂ] O)
    (h : ∀ (M : ℤ) (y : State s), energy M y.val → F y = G y) :
    F x = G x := by
  classical
  let basis := actualAmbientBasis ℒ U
  rw [← sum_projectedBasis s x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, map_smul]
  congr 1
  apply h (oddWeight ℒ i.1 : ℤ)
  have hg := (actualGrade_eigen ℒ U _ _).mp (projected_basis_grade s i)
  simpa only [energy, Int.cast_natCast] using hg

private theorem allA (a : A) (b : B) (h : H) (M K p q r : ℤ)
    (hb : energy M b.val) (hh : energy K h.val) : JacobiAt a b h p q r := by
  let f (k : ℕ) : A →ₗ[ℂ] O := choose p k •
    ((LinearMap.applyₗ (R := ℂ) h).comp (pairMap (p+q-k))).comp
      ((LinearMap.applyₗ (R := ℂ) b).comp (fixedMap true (r+k)))
  let g (k : ℕ) : A →ₗ[ℂ] O := productWeight r k •
    (LinearMap.applyₗ (R := ℂ) (P b (q+k) h)).comp (oddMap (p+r-k))
  let t (k : ℕ) : A →ₗ[ℂ] O := (eps r * productWeight r k) •
    (P b (q+r-k)).comp ((LinearMap.applyₗ (R := ℂ) h).comp (fixedMap false (p+k)))
  exact series_equal f g t (fun a' => term_finite a' b h p q r) a
    (stateEnergies ℒ a.val) (fun d => fixedSourceInclusion ℒ d (fixedProjection ℒ U d a))
    (fixed_source_expansion ℒ U a)
    (fun d _ => homogeneous _ b h M K d p q r hb hh (fixedProjection ℒ U d a).property.1)

private theorem allB (a : A) (b : B) (h : H) (K p q r : ℤ)
    (hh : energy K h.val) : JacobiAt a b h p q r := by
  let f (k : ℕ) : B →ₗ[ℂ] O := choose p k •
    ((LinearMap.applyₗ (R := ℂ) h).comp (pairMap (p+q-k))).comp (fixMode true a (r+k))
  let g (k : ℕ) : B →ₗ[ℂ] O := productWeight r k •
    (oddMode ℒ a (p+r-k)).comp ((LinearMap.applyₗ (R := ℂ) h).comp (pairMap (q+k)))
  let t (k : ℕ) : B →ₗ[ℂ] O := (eps r * productWeight r k) •
    (LinearMap.applyₗ (R := ℂ) (fixMode false a (p+k) h)).comp (pairMap (q+r-k))
  let F := seriesMap f (fun b' => (term_finite a b' h p q r).1)
  let G := difference (seriesMap g (fun b' => (term_finite a b' h p q r).2.1))
    (seriesMap t (fun b' => (term_finite a b' h p q r).2.2))
  change F b = G b
  exact expand_twisted true b F G fun M b' hb => allA a b' h M K p q r hb hh

private theorem all_states (a : A) (b : B) (h : H) (p q r : ℤ) :
    JacobiAt a b h p q r := by
  let f (k : ℕ) : H →ₗ[ℂ] O := choose p k • P (fixMode true a (r+k) b) (p+q-k)
  let g (k : ℕ) : H →ₗ[ℂ] O := productWeight r k •
    (oddMode ℒ a (p+r-k)).comp (P b (q+k))
  let t (k : ℕ) : H →ₗ[ℂ] O := (eps r * productWeight r k) •
    (P b (q+r-k)).comp (fixMode false a (p+k))
  let F := seriesMap f (fun h' => (term_finite a b h' p q r).1)
  let G := difference (seriesMap g (fun h' => (term_finite a b h' p q r).2.1))
    (seriesMap t (fun h' => (term_finite a b h' p q r).2.2))
  change F h = G h
  exact expand_twisted false h F G fun K h' hh => allB a b h' K p q r hh

/-- Signed mode Jacobi for the literal native mixed coefficient on the Leech
carriers. The integer (q) labels physical mode (q+1/2) and doubled exponent
(-2q-3). The three families have pointwise finite support. -/
theorem mu_true_borcherds (a : FixedCarrier ℒ) (b : Twisted ℒ U true)
    (h : Twisted ℒ U false) (p q r : ℤ) :
    let iterate := fun j : ℕ => Ring.choose (p : ℂ) j •
      (mu true (((fixedParitySlice ℒ U (-1) a)[[r+j]]) b)).coeff
        (-2*(p+q-j)-3) h
    let first := fun j : ℕ => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      oddMode ℒ a (p+r-j) ((mu true b).coeff (-2*(q+j)-3) h)
    let second := fun j : ℕ => ((-1 : ℂ)^r * ((-1 : ℂ)^j * Ring.choose (r : ℂ) j)) •
      (mu true b).coeff (-2*(q+r-j)-3) (((fixedParitySlice ℒ U 1 a)[[p+j]]) h)
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ j, iterate j) = (∑ᶠ j, first j) - (∑ᶠ j, second j) := by
  obtain ⟨hi, hf, hs⟩ := term_finite a b h p q r
  exact ⟨hi, hf, hs, all_states a b h p q r⟩


/-- The iterate's fixed mode on (B) is the (B) component of the
actual Leech extension field. -/
theorem fixed_on_B_eq_extension (a : FixedCarrier ℒ) (b : Twisted ℒ U true)
    (n : ℤ) :
    (((fixedParitySlice ℒ U (-1) a)[[n]]) b) =
      ((((OriginalOrbifoldField.Y ℒ U leech_spec.2.2.1 (a, 0))[[n]])
        ((0, b) : OriginalOrbifoldField.Carrier ℒ U))).2 := by
  rw [OriginalOrbifoldField.Y_fixed_ncoeff_apply]

/-- The literal all-mode commutator on the actual odd lattice output. -/
theorem mu_true_commutator (a : FixedCarrier ℒ) (b : Twisted ℒ U true)
    (h : Twisted ℒ U false) (p q : ℤ) :
    let iterate := fun j : ℕ => Ring.choose (p : ℂ) j •
      (mu true (((fixedParitySlice ℒ U (-1) a)[[j]]) b)).coeff
        (-2*(p+q-j)-3) h
    Function.HasFiniteSupport iterate ∧
      oddMode ℒ a p ((mu true b).coeff (-2*q-3) h) -
        (mu true b).coeff (-2*q-3) (((fixedParitySlice ℒ U 1 a)[[p]]) h) =
      ∑ᶠ j, iterate j := by
  obtain ⟨hi, _, _, hj⟩ := mu_true_borcherds a b h p q 0
  have hf : (∑ᶠ j, firstTerm a b h p q 0 j) = oddMode ℒ a p (P b q h) := by
    rw [finsum_eq_single _ 0]
    · simp [firstTerm, productWeight, choose, sg]
    · intro j hj
      simp [firstTerm, productWeight, choose, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  have hs : (∑ᶠ j, secondTerm a b h p q 0 j) = P b q (fixMode false a p h) := by
    rw [finsum_eq_single _ 0]
    · simp [secondTerm, productWeight, choose, sg, eps]
    · intro j hj
      simp [secondTerm, productWeight, choose, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
  change JacobiAt a b h p q 0 at hj
  unfold JacobiAt at hj
  rw [hf, hs] at hj
  dsimp only
  refine ⟨by simpa only [zero_add] using hi, ?_⟩
  have hfun :
      leftTerm a b h p q 0 = (fun j : ℕ => Ring.choose (p : ℂ) j •
        (mu true (((fixedParitySlice ℒ U (-1) a)[[j]]) b)).coeff
          (-2*(p+q-j)-3) h) := by
    funext j
    change choose p j • P (fixMode true a (0+(j : ℤ)) b) (p+q-j) h = _
    rw [zero_add]
    rfl
  rw [← hfun]
  exact hj.symm

/-- The span of all coefficients of the literal (B)-on-(H) field. -/
def mixedImageSpan : Submodule ℂ (OddCarrier ℒ) :=
  Submodule.span ℂ (Set.range (fun x : ℤ × Twisted ℒ U true × Twisted ℒ U false =>
    (mu true x.2.1).coeff (-2*x.1-3) x.2.2))

/-- Every actual fixed mode preserves the span of the mixed coefficients. -/
theorem mixedImageSpan_stable (a : FixedCarrier ℒ) (p : ℤ) (x : OddCarrier ℒ)
    (hx : x ∈ mixedImageSpan) : oddMode ℒ a p x ∈ mixedImageSpan := by
  let F := oddMode ℒ a p
  let S := mixedImageSpan
  have gen (q : ℤ) (b : Twisted ℒ U true) (h : Twisted ℒ U false) :
      P b q h ∈ S := Submodule.subset_span ⟨(q, b, h), rfl⟩
  have invariant : mixedImageSpan ≤ S.comap F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨q, b, h⟩, rfl⟩
    change F (P b q h) ∈ S
    have hc := all_states a b h p q 0
    unfold JacobiAt at hc
    have hf : (∑ᶠ j, firstTerm a b h p q 0 j) = F (P b q h) := by
      rw [finsum_eq_single _ 0]
      · simp [firstTerm, productWeight, choose, sg, F]
      · intro j hj
        simp [firstTerm, productWeight, choose, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
    have hs : (∑ᶠ j, secondTerm a b h p q 0 j) = P b q (fixMode false a p h) := by
      rw [finsum_eq_single _ 0]
      · simp [secondTerm, productWeight, choose, sg, eps]
      · intro j hj
        simp [secondTerm, productWeight, choose, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)]
    rw [hf, hs] at hc
    have ht := (term_finite a b h p q 0).1
    have rhs : (∑ᶠ j, leftTerm a b h p q 0 j) ∈ S := by
      rw [finsum_eq_sum _ ht]
      exact S.sum_mem fun j _ => S.smul_mem _ (gen _ _ _)
    have he : F (P b q h) =
        (∑ᶠ j, leftTerm a b h p q 0 j) + P b q (fixMode false a p h) := by
      apply Subtype.ext
      have hv := congrArg Subtype.val hc.symm
      simp only [Submodule.coe_sub] at hv
      rw [Submodule.coe_add]
      exact sub_eq_iff_eq_add.mp hv
    rw [he]
    exact S.add_mem rhs (gen _ _ _)
  exact invariant hx

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds

#print axioms D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds.mu_true_borcherds
#print axioms D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds.fixed_on_B_eq_extension
#print axioms D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds.mu_true_commutator
#print axioms D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds.mixedImageSpan_stable
