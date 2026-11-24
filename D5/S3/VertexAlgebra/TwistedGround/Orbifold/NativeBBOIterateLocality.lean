import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIntegerLocality

/-! Dong locality of the tilted integer residues, and the fixed field's
mixed commutator on the complementary twisted sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIterateLocality

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd OddCarrier oddMode leechUnit)
open NativeBBOCoefficientTransport (P Q bb ab fixedH mixed_transport)
open NativeBBOIntegerLocality
open FieldNormalProductLocality (deltaEnd)
open LatticeHalfFockGroundRightCurrentTransport (residueWeight)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R Z Valid R_nat)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open SignedFieldNormalProductLocality (signedComm)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private R_mode Z_mode forward_finite reverse_finite ext_modes from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private choose_int extY from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

local notation "ℒ" => leechData
local notation "A" => FixedCarrier ℒ
local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier ℒ
local notation "comm" => FieldNormalProductLocality.commutator
local notation "Tilt" => LatticeHalfFockGroundRightCurrentTransport.Calculus.Q

section Calculus
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The ordinary residue in the finite collision calculus agrees with the
all-integer signed Dong residue at sign one. -/
theorem R_eq_Dong (X Y : VertexOperator ℂ V) (r : ℤ) :
    R X Y r = (residueField 1 r X Y).operator := by
  apply ext_modes
  intro n
  apply LinearMap.ext
  intro x
  rw [R_mode, (residueField 1 r X Y).coefficient]
  simp only [residueCoefficient, residueLeft, residueRight, epsilon, mul_one,
    residueWeight, integerBinomial, choose_int, add_comm n r]

theorem locality_shift (X Y : VertexOperator ℂ V) (K : ℕ) (c : ℤ)
    (h : (deltaEnd ^ K) (comm X Y) = 0) :
    (deltaEnd ^ K) (comm (Z c X) Y) = 0 := by
  funext t u
  have hh := congrFun (congrFun h (t-c)) u
  rw [FieldDeltaBinomial.delta_binomial] at hh ⊢
  simpa only [FieldNormalProductLocality.commutator, Z_mode, Pi.zero_apply,
    show ∀ j : ℕ, t+(K:ℤ)-j-c = t-c+K-j by intro; omega]
    using hh

theorem locality_sum (Y : VertexOperator ℂ V) (S : Finset ℕ)
    (X : ℕ → VertexOperator ℂ V)
    (h : ∀ j ∈ S, ∃ K : ℕ, (deltaEnd ^ K) (comm (X j) Y) = 0) :
    ∃ K : ℕ, (deltaEnd ^ K) (comm (∑ j ∈ S, X j) Y) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp only [Finset.sum_empty, pow_zero, Module.End.one_apply]
    funext t u
    simp [FieldNormalProductLocality.commutator]
  | @insert a S ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨L, hL⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨max K L, ?_⟩
    rw [Finset.sum_insert ha]
    have hadd (J J' : VertexOperator ℂ V) :
        comm (J+J') Y = comm J Y + comm J' Y := by
      funext t u
      simp only [FieldNormalProductLocality.commutator, map_add, Pi.add_apply, add_mul, mul_add]
      abel
    rw [hadd, map_add, raise_locality _ (le_max_left K L) hK,
      raise_locality _ (le_max_right K L) hL, add_zero]

theorem locality_smul (X Y : VertexOperator ℂ V) (K : ℕ) (z : ℂ)
    (h : (deltaEnd ^ K) (comm X Y) = 0) :
    (deltaEnd ^ K) (comm (z • X) Y) = 0 := by
  have hs : comm (z • X) Y = z • comm X Y := by
    funext t u
    simp only [FieldNormalProductLocality.commutator, map_smul, Pi.smul_apply,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hs, map_smul, h, smul_zero]

end Calculus

/-- The finite tilted BB residue. The outer shift restores the fixed
field's integral mode convention. -/
def T (b c : B) (r : ℤ) (N : ℕ) : VertexOperator ℂ W :=
  Z 1 (Tilt (F b) (F c) 1 r N)

/-- Each tilted residue is local with every parity-changing native field. -/
theorem T_locality (b c d : B) (r : ℤ) (N : ℕ) :
    ∃ K : ℕ, (deltaEnd ^ K) (comm (T b c r N) (F d)) = 0 := by
  have sign_one (X Y : VertexOperator ℂ W) : signedComm 1 X Y = comm X Y := by
    funext t u
    simp only [signedComm, FieldNormalProductLocality.commutator, one_smul]
  have get (x y : B) : ∃ K : ℕ, FieldNormalProductLocality.delta^[K] (signedComm 1 (F x) (F y)) = 0 := by
    obtain ⟨K, _, hK⟩ := pair_locality x y
    refine ⟨K, ?_⟩
    rw [sign_one]
    rw [Module.End.pow_apply] at hK
    exact hK
  obtain ⟨K, hK⟩ := locality_sum (F d) (Finset.range ((N : ℤ)-r).toNat)
    (fun ell => Ring.choose (-(1 : ℂ)/2) ell • Z ell (R (F b) (F c) (r+ell))) (by
      intro ell _
      obtain ⟨L, hL⟩ := SignedFieldResidueLocality.residue_locality 1 1 1
        (F b) (F c) (F d) (get b d) (get c d) (get b c) (r+ell)
      rw [← R_eq_Dong] at hL
      have hh : (deltaEnd ^ L) (comm (R (F b) (F c) (r+ell)) (F d)) = 0 := by
        rw [Module.End.pow_apply]
        rw [one_mul, sign_one] at hL
        exact hL
      exact ⟨L, locality_smul _ _ L _ (locality_shift _ _ L ell hh)⟩)
  refine ⟨K, ?_⟩
  apply locality_shift
  simpa only [LatticeHalfFockGroundRightCurrentTransport.Calculus.Q, Int.cast_one] using hK

/-- A uniform ordinary extension cutoff for the mixed state product. -/
theorem ab_tail (a : A) (d : B) : ∃ K : ℕ, ∀ r : ℤ, (K : ℤ) ≤ r → ab a d r = 0 := by
  let J := extY (a, 0)
  let v : NativeBBOCoefficientTransport.Extension := (0, d)
  let order := ((HahnModule.of ℂ).symm (J v)).order
  refine ⟨(-order).toNat, fun r hr => ?_⟩
  have hh : (J[[r]]) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    change -r-1 < order
    omega
  exact congrArg Prod.snd hh

/-- Native ABH at the mixed state-product cutoff gives the ordinary
commutator polynomial on the even twisted inputs. -/
theorem mixed_locality_on_H (a : A) (d : B) (K : ℕ)
    (hK : ∀ r : ℤ, (K : ℤ) ≤ r → ab a d r = 0)
    (t u : ℤ) (h : H) :
    ((deltaEnd ^ K) (comm (G a) (F d))) t u (h, 0) = 0 := by
  rw [← shifted_residue_nat]
  let X := Z (-t) (G a)
  let Y := F d
  let f (j : ℕ) : W := residueWeight K j • (X[[(K:ℤ)-j]]) ((Y[[u+j]]) (h,0))
  let g (j : ℕ) : W := residueWeight K j • (Y[[u+K-j]]) ((X[[j]]) (h,0))
  have hf := (forward_finite X Y K u (h,0)).smul_right (residueWeight K)
  have hg := (reverse_finite X Y K u (h,0)).smul_right (residueWeight K)
  change Function.HasFiniteSupport f at hf
  change Function.HasFiniteSupport g at hg
  have he := (mixed_transport a d h t u K).2.2.2
  dsimp only at he
  have hz : (∑ᶠ j : ℕ, Ring.choose (t : ℂ) j • P (ab a d ((K : ℤ)+j)) (t+u-j) h) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hK _ (by omega)]
    simp [P]
  rw [hz, zero_add] at he
  rw [R_mode]
  change (∑ᶠ j, f j) - (-1 : ℂ)^(K:ℤ) • (∑ᶠ j, g j) = _
  apply Prod.ext
  · change (LinearMap.fst ℂ H O) ((∑ᶠ j, f j) - (-1 : ℂ)^(K:ℤ) • (∑ᶠ j, g j)) = 0
    rw [map_sub, map_smul, map_finsum _ hf, map_finsum _ hg]
    simp [f, g, X, Y, Z_mode, F_mode, G_mode]
  · change (LinearMap.snd ℂ H O) ((∑ᶠ j, f j) - (-1 : ℂ)^(K:ℤ) • (∑ᶠ j, g j)) = 0
    rw [map_sub, map_smul, map_finsum _ hf, map_finsum _ hg]
    simp only [f, g, X, Y, Z_mode, F_mode, G_mode, sub_neg_eq_add, map_zero, neg_zero,
      LinearMap.snd_apply, Prod.smul_snd, residueWeight]
    simp only [show ∀ j : ℕ, (K : ℤ)-j+t = t+K-j by intro; omega,
      show ∀ j : ℕ, (j:ℤ)+t = t+j by intro; omega, smul_finsum, smul_smul]
    rw [he, sub_self]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOIterateLocality
