import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi

/-!
The second off-diagonal Jacobi block follows from the native odd-source law by
exchanging the last two inputs. In this exchange the half-integer shift stays
on the mixed coefficient. Multiplication of the right field by `I` converts
the upper-branch phase to the integer sign used by the finite exchange.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightBorcherds

open ActualLeechHyperbolic (leechData)
open LatticeInvolution (FixedCarrier)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open NativeOddTwistedIntertwiner (OddCarrier Twisted leechUnit paritySign J J_borcherds
  J_truncation oddMode oddTranslation)
open NativeOddUpperRightSkew (R R_truncation rightField rightField_coeff
  rightTerm translation)
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private divided_mode_of_step from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private has_mode_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
open private translation_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private actual_translation_commutator from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

local notation "ℒ" => leechData
local notation "U" => leechUnit
private abbrev A := FixedCarrier ℒ
private abbrev B := Twisted ℒ U true
private abbrev O := OddCarrier ℒ
private abbrev H := Twisted ℒ U false
private abbrev fixedMode (s : Bool) (a : A) (n : ℤ) :=
  (fixedParitySlice ℒ U (paritySign s) a)[[n]]
private abbrev Jmode (n : ℤ) : O →ₗ[ℂ] B →ₗ[ℂ] H := J ℒ U true n
private abbrev Rmode (n : ℤ) : B →ₗ[ℂ] O →ₗ[ℂ] H := R ℒ U true n

private theorem add_of_sub_eq_neg {V : Type*} [AddCommGroup V] {x y z : V}
    (h : x - y = -z) : y = x + z := by
  calc
    y = x - (x - y) := by rw [sub_sub_cancel]
    _ = x + z := by rw [h, sub_neg_eq_add]

private theorem twisted_step (s : Bool) (a : A) (n : ℤ) (v : Twisted ℒ U s) :
    fixedMode s a n (translation ℒ U s v) =
      translation ℒ U s (fixedMode s a n v) + (n : ℂ) • fixedMode s a (n - 1) v := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, translation_val]
  change (LatticeHalfFockCorrectedField.correctedField ℒ U a.val).coeff (2*(-n-1))
      (translation ℒ U s v).val =
    _ + (n : ℂ) • (LatticeHalfFockCorrectedField.correctedField ℒ U a.val).coeff
      (2*(-(n-1)-1)) v.val
  rw [translation_val]
  have h := actual_translation_commutator ℒ U a.val (-n-1) v.val
  rw [show (2*(-n-1)+2 : ℤ) = 2*(-(n-1)-1) by ring,
    show ((-n-1 : ℤ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring] at h
  let z : LatticeHalfFockChargedTensorCoefficients.ActualTensor ℒ U :=
    (LatticeHalfFockCorrectedField.correctedField ℒ U a.val).coeff (2*(-(n-1)-1)) v.val
  change _ - _ = -(n : ℂ) • z at h
  exact add_of_sub_eq_neg (h.trans (neg_smul (n : ℂ) z))

private theorem odd_step (a : A) (n : ℤ) (o : O) :
    oddMode ℒ a n (oddTranslation ℒ o) =
      oddTranslation ℒ (oddMode ℒ a n o) + (n : ℂ) • oddMode ℒ a (n - 1) o := by
  apply Subtype.ext
  have h := LinearMap.congr_fun (LatticeAllStateField.stateField_covariance ℒ a.val n) o.val
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, neg_smul] at h
  rw [Submodule.coe_add, Submodule.coe_smul]
  exact add_of_sub_eq_neg h

-- The scalar coordinate stands for the complex span of the single fixed input.
private abbrev Carrier := ℂ × B × O × H

private def fixedIn : Carrier := (1, 0, 0, 0)
private def bIn (b : B) : Carrier := (0, b, 0, 0)
private def oIn (o : O) : Carrier := (0, 0, o, 0)
private def hIn : H →ₗ[ℂ] Carrier :=
  (0 : H →ₗ[ℂ] ℂ).prod ((0 : H →ₗ[ℂ] B).prod ((0 : H →ₗ[ℂ] O).prod LinearMap.id))

private def T : Module.End ℂ Carrier :=
  (0 : Carrier →ₗ[ℂ] ℂ).prod
    (((translation ℒ U true).comp (LinearMap.fst ℂ B (O × H) ∘ₗ LinearMap.snd ℂ ℂ _)).prod
      (((oddTranslation ℒ).comp
        (LinearMap.fst ℂ O H ∘ₗ LinearMap.snd ℂ B _ ∘ₗ LinearMap.snd ℂ ℂ _)).prod
        ((translation ℒ U false).comp
          (LinearMap.snd ℂ O H ∘ₗ LinearMap.snd ℂ B _ ∘ₗ LinearMap.snd ℂ ℂ _))))

-- These are the five mode entries used in the two ordered identities.
private def act (a : A) (n : ℤ) (x y : Carrier) : Carrier :=
  (0, x.1 • fixedMode true a n y.2.1, x.1 • oddMode ℒ a n y.2.2.1,
    x.1 • fixedMode false a n y.2.2.2 + Jmode n x.2.2.1 y.2.1 +
      Complex.I • Rmode n x.2.1 y.2.2.1)

private def modes (a : A) : Modes Carrier := fun n =>
  LinearMap.mk₂ ℂ (act a n)
    (by intro x y z; simp [act, add_smul, map_add]; abel)
    (by intro c x y; simp [act, map_smul, smul_add, smul_smul, mul_comm c Complex.I])
    (by intro x y z; simp [act, map_add, smul_add]; abel)
    (by intro c x y; simp [act, map_smul, smul_add, smul_smul, mul_comm c])

private theorem mode_apply (a : A) (n : ℤ) (x y : Carrier) :
    modes a n x y = act a n x y := rfl

private theorem fixed_b (a : A) (n : ℤ) (b : B) :
    modes a n fixedIn (bIn b) = bIn (fixedMode true a n b) := by
  simp [mode_apply, act, fixedIn, bIn]

private theorem fixed_o (a : A) (n : ℤ) (o : O) :
    modes a n fixedIn (oIn o) = oIn (oddMode ℒ a n o) := by
  simp [mode_apply, act, fixedIn, oIn]

private theorem fixed_h (a : A) (n : ℤ) (h : H) :
    modes a n fixedIn (hIn h) = hIn (fixedMode false a n h) := by
  simp [mode_apply, act, fixedIn, hIn]

private theorem ob (a : A) (n : ℤ) (o : O) (b : B) :
    modes a n (oIn o) (bIn b) = hIn (Jmode n o b) := by
  simp [mode_apply, act, oIn, bIn, hIn]

private theorem bo (a : A) (n : ℤ) (b : B) (o : O) :
    modes a n (bIn b) (oIn o) = hIn (Complex.I • Rmode n b o) := by
  simp [mode_apply, act, oIn, bIn, hIn]

private theorem truncation (a : A) : LowerTruncated (modes a) := by
  intro x y
  obtain ⟨NB, hB⟩ := has_mode_tail (fixedParitySlice ℒ U (-1) a) y.2.1
  obtain ⟨NO, hO⟩ := has_mode_tail (LatticeAllStateField.Y ℒ a.val) y.2.2.1.val
  obtain ⟨NH, hH⟩ := has_mode_tail (fixedParitySlice ℒ U 1 a) y.2.2.2
  obtain ⟨NJ, hJ⟩ := J_truncation ℒ U true x.2.2.1 y.2.1
  obtain ⟨NR, hR⟩ := R_truncation ℒ U true x.2.1 y.2.2.1
  refine ⟨max (max NB NO) (max NH (max NJ NR)), fun n hn => ?_⟩
  simp only [max_le_iff] at hn
  have ho : oddMode ℒ a n y.2.2.1 = 0 := Subtype.ext (hO n hn.1.2)
  have hb : fixedMode true a n y.2.1 = 0 := hB n hn.1.1
  have hh : fixedMode false a n y.2.2.2 = 0 := hH n hn.2.1
  have hj : Jmode n x.2.2.1 y.2.1 = 0 := hJ n hn.2.2.1
  have hr : Rmode n x.2.1 y.2.2.1 = 0 := hR n hn.2.2.2
  simp [mode_apply, act, hb, ho, hh, hj, hr]

private theorem T_apply (x : Carrier) :
    T x = (0, translation ℒ U true x.2.1, oddTranslation ℒ x.2.2.1,
      translation ℒ U false x.2.2.2) := rfl

private theorem mode_translation (a : A) : DividedModeTranslation (modes a) T fixedIn := by
  apply divided_mode_of_step
  intro n v
  simp only [mode_apply, act, fixedIn, T_apply, one_smul, map_zero, LinearMap.zero_apply,
    add_zero, Prod.smul_mk, Prod.mk_add_mk]
  simp only [twisted_step true, odd_step, twisted_step false, smul_zero, add_zero]

private theorem T_hIn (j : ℕ) (h : H) :
    (T ^ j) (hIn h) = hIn ((translation ℒ U false ^ j) h) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, T_apply]
    simp [hIn]

private theorem phase (n : ℤ) :
    Complex.I * Complex.I ^ (-2*n-3) = epsilon (n+1) := by
  conv_lhs => arg 1; rw [← zpow_one Complex.I]
  rw [← zpow_add₀ Complex.I_ne_zero,
    show (1+(-2*n-3) : ℤ) = 2 * (-(n+1)) by ring,
    zpow_mul, show Complex.I ^ (2 : ℤ) = -1 by
      rw [show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, Complex.I_sq],
    zpow_neg, ← inv_zpow, show (-1 : ℂ)⁻¹ = -1 by norm_num]
  rfl

private theorem hIn_injective : Function.Injective hIn := by
  intro x y h
  exact congrArg (fun w : Carrier => w.2.2.2) h

private theorem sum_h (f : ℕ → H) :
    (∑ᶠ i, hIn (f i)) = hIn (∑ᶠ i, f i) :=
  (hIn.toAddMonoidHom.map_finsum_of_injective hIn_injective f).symm

private theorem skew_bo (a : A) (b : B) (o : O) :
    SkewAt (modes a) T (bIn b) (oIn o) := by
  intro n
  rw [bo]
  let t : ℕ → H := rightTerm ℒ U true n b o
  have ht : Function.HasFiniteSupport t :=
    NativeOddUpperRightSkew.rightTerm_finite ℒ U true n b o
  change hIn (Complex.I • ∑ᶠ j, t j) = _
  rw [smul_finsum' _ ht, ← sum_h (fun j => Complex.I • t j)]
  apply finsum_congr
  intro j
  rw [ob]
  have term : t j = (Complex.I ^ (-2*(n+(j : ℤ))-3) * (j.factorial : ℂ)⁻¹) •
      (translation ℒ U false ^ j) (Jmode (n+j) o b) := rfl
  simp only [dividedTranslation, LinearMap.smul_apply, T_hIn, ← map_smul hIn,
    term, smul_smul, ← mul_assoc, phase, add_assoc]

private theorem jDefect (a : A) (o : O) (b : B) (p q r : ℤ) :
    defect (modes a) fixedIn (oIn o) (bIn b) p q r = 0 := by
  have h := (J_borcherds ℒ U true a o b p q r).2.2.2
  unfold defect product iterate
  simp only [fixed_b, fixed_o, ob, fixed_h, ← map_smul hIn, sum_h, ← map_sub hIn]
  rw [← map_zero hIn]
  apply congrArg hIn
  apply sub_eq_zero.mpr
  rw [smul_finsum (M := H) (epsilon r)]
  simp only [smul_smul, mul_comm (epsilon r)]
  simp only [smul_smul] at h
  exact h.symm

private theorem rightDefect (a : A) (b : B) (o : O) (p q r : ℤ) :
    defect (modes a) fixedIn (bIn b) (oIn o) p q r = 0 := by
  have h := (defect_swap_last (modes a) (truncation a) fixedIn (bIn b) (oIn o)
    p q r (mode_translation a) (skew_bo a b o)
    (fun j => by rw [fixed_b]; exact skew_bo a _ o)
    (fun j => by rw [fixed_o]; exact skew_bo a b _)).2
  rw [h]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [jDefect, map_zero]

private def normalizedIn : H →ₗ[ℂ] Carrier := Complex.I • hIn

private theorem normalizedIn_apply (h : H) : normalizedIn h = hIn (Complex.I • h) := by
  simp only [normalizedIn, LinearMap.smul_apply, map_smul]

private theorem normalizedIn_injective : Function.Injective normalizedIn := by
  intro h k he
  rw [normalizedIn_apply, normalizedIn_apply] at he
  exact (smul_right_inj Complex.I_ne_zero).mp (hIn_injective he)

private theorem finite_of_normalized {f : ℕ → H}
    (hf : Function.HasFiniteSupport (fun j => normalizedIn (f j))) :
    Function.HasFiniteSupport f :=
  hf.subset (fun _j hj hz => hj (normalizedIn_injective (hz.trans (map_zero _).symm)))

private theorem normalized_bo (a : A) (n : ℤ) (b : B) (o : O) :
    modes a n (bIn b) (oIn o) = normalizedIn (Rmode n b o) :=
  (bo a n b o).trans (normalizedIn_apply _).symm

private theorem normalized_first (a : A) (n : ℤ) (h : H) :
    modes a n fixedIn (normalizedIn h) = normalizedIn (fixedMode false a n h) := by
  rw [normalizedIn_apply, fixed_h, map_smul (fixedMode false a n), ← normalizedIn_apply]

private theorem right_modes_borcherds (a : A) (b : B) (o : O) (p q r : ℤ) :
    let left := fun j : ℕ => Ring.choose (p : ℂ) j •
      Rmode (p+q-j) (fixedMode true a (r+j) b) o
    let first := fun j : ℕ => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      fixedMode false a (p+r-j) (Rmode (q+j) b o)
    let second := fun j : ℕ => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      ((-1 : ℂ)^r • Rmode (q+r-j) b (oddMode ℒ a (p+j) o))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ j, left j) = (∑ᶠ j, first j) - (∑ᶠ j, second j) := by
  have law := (defect_eq_zero_iff_borcherds (modes a) (truncation a) fixedIn
    (bIn b) (oIn o) p q r).mp (rightDefect a b o p q r)
  have choose_cast (m : ℤ) (j : ℕ) :
      integerBinomial m j = Ring.choose (m : ℂ) j :=
    Ring.map_choose (Int.castRingHom ℂ) m j
  dsimp only at law ⊢
  simp only [fixed_b, fixed_o, normalized_bo, normalized_first,
    ← map_smul normalizedIn, choose_cast, epsilon] at law
  obtain ⟨fl, ff, fs, he⟩ := law
  have hl := finite_of_normalized fl
  have hf := finite_of_normalized ff
  have hs := finite_of_normalized fs
  refine ⟨hl, hf, hs, normalizedIn_injective ?_⟩
  rw [map_sub normalizedIn, map_finsum normalizedIn hl, map_finsum normalizedIn hf,
    map_finsum normalizedIn hs, ← finsum_sub_distrib ff fs]
  simpa only [smul_sub, ← map_smul normalizedIn] using he

/-- Signed Jacobi for the literal upper right field from the odd lattice
space to the even twisted space, with arbitrary states and integer indices.
A right-field exponent `-2*n-3` denotes physical mode `n+1/2`. -/
theorem rightField_true_borcherds (a : FixedCarrier ℒ) (b : Twisted ℒ U true)
    (o : OddCarrier ℒ) (p q r : ℤ) :
    let left : ℕ → Twisted ℒ U false := fun j => Ring.choose (p : ℂ) j •
      (rightField ℒ U true (((fixedParitySlice ℒ U (-1) a)[[r+j]]) b)).coeff
        (-2*(p+q-j)-3) o
    let first : ℕ → Twisted ℒ U false := fun j => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      ((fixedParitySlice ℒ U 1 a)[[p+r-j]]) ((rightField ℒ U true b).coeff (-2*(q+j)-3) o)
    let second : ℕ → Twisted ℒ U false := fun j => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      ((-1 : ℂ)^r • (rightField ℒ U true b).coeff (-2*(q+r-j)-3) (oddMode ℒ a (p+j) o))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ j, left j) = (∑ᶠ j, first j) - (∑ᶠ j, second j) := by
  simp only [rightField_coeff]
  exact right_modes_borcherds a b o p q r

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightBorcherds
