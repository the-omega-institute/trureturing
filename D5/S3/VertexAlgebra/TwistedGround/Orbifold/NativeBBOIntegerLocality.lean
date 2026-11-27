import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Compatibility
import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality

/-! Integer-index fields on the two native module sectors, with the signed
right-skew action and the actual fixed action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIntegerLocality

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd OddCarrier oddMode leechUnit)
open NativeBBOCoefficientTransport (P Q bb ab fixedH mixed_transport)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open FourPoint.NativeBBHHActualVectorJacobi (bbhh_actual_vector_coefficient_jacobi)
open FieldNormalProductLocality (deltaEnd)
open LatticeHalfFockGroundRightCurrentTransport (residueWeight)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R Z Valid R_nat)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private p_tail q_tail bb_tail choose_int bb_hahn_iterate from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport
open private R_mode Z_mode forward_finite reverse_finite ext_modes from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private ordered_residue from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Compatibility

local notation "ℒ" => leechData
local notation "A" => FixedCarrier ℒ
local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier ℒ

abbrev W := H × O

private def bMode (b : B) (n : ℤ) : Module.End ℂ W :=
  ((-(Q b n)).comp (LinearMap.snd ℂ H O)).prod
    ((P b n).comp (LinearMap.fst ℂ H O))

/-- The parity-changing native field with integral Laurent labels. -/
def F (b : B) : VertexOperator ℂ W :=
  VertexOperator.of_coeff (fun e => bMode b (-e-1)) (by
    intro x
    obtain ⟨K, hK⟩ := p_tail b x.1
    obtain ⟨L, hL⟩ := q_tail b x.2
    refine ⟨-max K L, ?_⟩
    intro e he
    by_contra hn
    apply he
    change (-(Q b (-e-1) x.2), P b (-e-1) x.1) = 0
    have heK : K ≤ -e-1 := by omega
    have heL : L ≤ -e-1 := by omega
    simp [hK _ heK, hL _ heL])

@[simp] theorem F_mode (b : B) (n : ℤ) (x : W) :
    ((F b)[[n]]) x = (-(Q b n x.2), P b n x.1) := by
  rw [F, VertexOperator.ncoeff_of_coeff, show -(-n-1)-1 = n by omega]
  rfl

private def aMode (a : A) (n : ℤ) : Module.End ℂ W :=
  ((fixedH a n).comp (LinearMap.fst ℂ H O)).prod
    ((oddMode ℒ a n).comp (LinearMap.snd ℂ H O))

/-- The actual fixed field on both sectors. -/
def G (a : A) : VertexOperator ℂ W :=
  VertexOperator.of_coeff (fun e => aMode a (-e-1)) (by
    intro x
    let K := ((HahnModule.of ℂ).symm ((fixedParitySlice ℒ leechUnit 1 a) x.1)).order
    let L := ((HahnModule.of ℂ).symm ((LatticeAllStateField.Y ℒ a.val) x.2.val)).order
    refine ⟨min K L, ?_⟩
    intro e he
    by_contra hn
    apply he
    change (fixedH a (-e-1) x.1, oddMode ℒ a (-e-1) x.2) = 0
    apply Prod.ext
    · change fixedH a (-e-1) x.1 = 0
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      change -(-e-1)-1 < K
      omega
    · apply Subtype.ext
      change ((LatticeAllStateField.Y ℒ a.val)[[-e-1]]) x.2.val = 0
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      change -(-e-1)-1 < L
      omega)

@[simp] theorem G_mode (a : A) (n : ℤ) (x : W) :
    ((G a)[[n]]) x = (fixedH a n x.1, oddMode ℒ a n x.2) := by
  rw [G, VertexOperator.ncoeff_of_coeff, show -(-n-1)-1 = n by omega]
  rfl

theorem G_zero : G 0 = 0 := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  rw [G_mode]
  simp only [map_zero]
  apply Prod.ext <;> apply Subtype.ext
  · change (((fixedParitySlice ℒ leechUnit 1 (0 : A))[[n]]) x.1).val = 0
    simp [fixedParitySlice, VertexOperator.ncoeff_of_coeff]
  · change ((LatticeAllStateField.Y ℒ 0)[[n]]) x.2.val = 0
    simp

/-- The residue at the shifted first field reads the full collision
polynomial when the collision order is nonnegative. -/
theorem shifted_residue_nat {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X Y : VertexOperator ℂ V) (N : ℕ) (t u : ℤ) (x : V) :
    ((R (Z (-t) X) Y N)[[u]]) x =
      ((deltaEnd ^ N) (FieldNormalProductLocality.commutator X Y)) t u x := by
  rw [R_nat, FieldDeltaBinomial.delta_binomial, FieldDeltaBinomial.delta_binomial]
  simp only [FieldNormalProductLocality.commutator, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, zero_add, Z_mode]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (N : ℤ) - j - -t = t + N - j by omega]

theorem raise_locality {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : ℤ → ℤ → Module.End ℂ V) {K L : ℕ} (hle : K ≤ L)
    (hK : (deltaEnd ^ K) D = 0) : (deltaEnd ^ L) D = 0 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_comm K extra, pow_add, Module.End.mul_apply, hK, map_zero]

/-- Projection of the native BB residue on the complementary twisted sector. -/
theorem bbh_residue (b c : B) (h : H) (t u r : ℤ) :
    ((R (Z (-t) (F b)) (F c) r)[[u]]) (h, 0) =
      (∑ᶠ j : ℕ, Ring.choose ((t : ℂ)+1/2) j •
        fixedH (bb b c (r+j)) (u+t+1-j) h, 0) := by
  have he := bbhh_actual_vector_coefficient_jacobi b c h t u r
  simp only [choose_int,
    show ∀ j : ℕ, -2*(t+r)-3+2*(j : ℤ) = -2*(t+r-j)-3 by intro; ring,
    show ∀ j : ℕ, -2*(u+r)-3+2*(j : ℤ) = -2*(u+r-j)-3 by intro; ring,
    show ∀ j : ℕ, -2*u-3-2*(j : ℤ) = -2*(u+j)-3 by intro; ring,
    show ∀ j : ℕ, -2*t-3-2*(j : ℤ) = -2*(t+j)-3 by intro; ring,
    show ∀ j : ℕ, -2*r-2-2*(j : ℤ) = -2*(r+j)-2 by intro; ring,
    show ∀ j : ℕ, -2*(t+u+1)-2+2*(j : ℤ) = -2*(u+t+1-j)-2 by intro; ring,
    bb_hahn_iterate] at he
  let X := Z (-t) (F b)
  let Y := F c
  let f (j : ℕ) : W := residueWeight r j • (X[[r-j]]) ((Y[[u+j]]) (h,0))
  let g (j : ℕ) : W := residueWeight r j • (Y[[u+r-j]]) ((X[[j]]) (h,0))
  have hf := (forward_finite X Y r u (h,0)).smul_right (residueWeight r)
  have hg := (reverse_finite X Y r u (h,0)).smul_right (residueWeight r)
  change Function.HasFiniteSupport f at hf
  change Function.HasFiniteSupport g at hg
  rw [R_mode]
  change (∑ᶠ j, f j) - (-1 : ℂ)^r • (∑ᶠ j, g j) = _
  apply Prod.ext
  · change (LinearMap.fst ℂ H O) ((∑ᶠ j, f j) - (-1 : ℂ)^r • (∑ᶠ j, g j)) = _
    rw [map_sub, map_smul, map_finsum _ hf, map_finsum _ hg]
    simp only [f, g, X, Y, Z_mode, F_mode, sub_neg_eq_add, map_zero, neg_zero,
      LinearMap.fst_apply, Prod.smul_fst, residueWeight]
    simp only [show ∀ j : ℕ, r-(j:ℤ)+t = t+r-j by intro; omega,
      show ∀ j : ℕ, (j:ℤ)+t = t+j by intro; omega, smul_neg, finsum_neg_distrib,
      smul_neg, sub_neg_eq_add, smul_finsum, smul_smul,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, ← mul_assoc] at he ⊢
    exact he
  · change (LinearMap.snd ℂ H O) ((∑ᶠ j, f j) - (-1 : ℂ)^r • (∑ᶠ j, g j)) = 0
    rw [map_sub, map_smul, map_finsum _ hf, map_finsum _ hg]
    simp [f, g, X, Y, Z_mode, F_mode]

/-- A common cutoff for the literal BB modes and the integer-field
commutator on the entire native carrier. -/
theorem pair_locality (b c : B) : ∃ N : ℕ,
    (∀ r : ℤ, (N : ℤ) ≤ r → bb b c r = 0) ∧
    (deltaEnd ^ N) (FieldNormalProductLocality.commutator (F b) (F c)) = 0 := by
  obtain ⟨K, hK⟩ := bb_tail b c
  obtain ⟨L, hL⟩ := NativeBBOCyclicLocality.locality_on_odd b c
  let N := max K.toNat L
  have tail (r : ℤ) (hr : (N : ℤ) ≤ r) : bb b c r = 0 := by
    apply hK
    dsimp [N] at hr
    omega
  refine ⟨N, tail, ?_⟩
  let D (t u : ℤ) : Module.End ℂ O :=
    (P b t).comp (Q c u) - (P c u).comp (Q b t)
  have hD : (deltaEnd ^ L) D = 0 := by
    funext t u
    apply LinearMap.ext
    intro o
    rw [FieldDeltaBinomial.delta_binomial]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, D, LinearMap.sub_apply,
      LinearMap.comp_apply, Pi.zero_apply, LinearMap.zero_apply]
    exact hL o t u
  have hDN := raise_locality D (le_max_right K.toNat L) hD
  funext t u
  apply LinearMap.ext
  intro x
  let E := ((deltaEnd ^ N) (FieldNormalProductLocality.commutator (F b) (F c))) t u
  have he (h : H) : E (h, 0) = 0 := by
    dsimp [E]
    rw [← shifted_residue_nat, bbh_residue]
    have hz : (∑ᶠ j : ℕ, Ring.choose ((t : ℂ)+1/2) j •
        fixedH (bb b c ((N : ℤ)+j)) (u+t+1-j) h) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      rw [tail _ (by omega)]
      have hh := congrArg (fun V : VertexOperator ℂ W => (((V[[u+t+1-j]]) (h, 0))).1) G_zero
      simp only [G_mode, map_zero, Pi.zero_apply, LinearMap.zero_apply, Prod.fst_zero] at hh
      rw [hh, smul_zero]
    rw [hz]
    rfl
  have ho (o : O) : E (0, o) = 0 := by
    have hh := congrArg (fun V : ℤ → ℤ → Module.End ℂ O => V t u o) hDN
    rw [FieldDeltaBinomial.delta_binomial] at hh
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, D, LinearMap.sub_apply,
      LinearMap.comp_apply, Pi.zero_apply, LinearMap.zero_apply] at hh
    dsimp [E]
    rw [FieldDeltaBinomial.delta_binomial]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply,
      F_mode, map_zero, neg_zero, map_neg, Prod.mk_sub_mk, sub_zero]
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero]
      calc
        _ = -(∑ j ∈ Finset.range (N+1), ((-1 : ℂ)^j * (N.choose j : ℂ)) •
            (P b (t+N-j) (Q c (u+j) o) - P c (u+j) (Q b (t+N-j) o))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [← smul_neg]
          congr 1
          abel
        _ = 0 := by exact neg_eq_zero.mpr hh
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  change E x = 0
  rw [hx, map_add, he, ho, add_zero]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIntegerLocality
