import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOneGeneration
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.BBHH.NativeBBHHActualVectorJacobi
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open NativeFixedPairField (nu nu_coeff_eq_originalI nu_lower_truncation)
open NativeMixedPairField (mu mu_lower_truncation)
open NativeMixedPairBorcherds (mixedImageSpan mixedImageSpan_stable)
open NativeMixedPairWeightOne (groundCoefficientModeClosure groundCoefficientModeClosure_eq_top)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd OddCarrier oddMode leechUnit leechGroundVector)
open NativeOddUpperRightSkew (rightField rightField_coeff R_truncation)
open OriginalFourMChargeCoset (originalI)

local notation "ℒ" => leechData
local notation "A" => FixedCarrier ℒ
local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier ℒ

/-- The ordinary linear span of the literal mixed coefficients is the entire
odd untwisted carrier. -/
theorem mixedImageSpan_eq_top : mixedImageSpan = ⊤ := by
  have hle : groundCoefficientModeClosure ≤ mixedImageSpan := by
    apply sInf_le
    refine ⟨?_, mixedImageSpan_stable⟩
    intro b
    exact Submodule.subset_span ⟨(1, b.val, leechGroundVector), rfl⟩
  rw [groundCoefficientModeClosure_eq_top] at hle
  exact top_unique hle

/-- Integer label (n) represents physical mode (n+1/2) and doubled Hahn
exponent (-2n-3) in either parity-changing field. -/
abbrev P (b : B) (n : ℤ) : H →ₗ[ℂ] O := (mu true b).coeff (-2*n-3)

/-- The raw native right-skew coefficient from the odd untwisted carrier. -/
abbrev Q (b : B) (n : ℤ) : O →ₗ[ℂ] H := (rightField ℒ leechUnit true b).coeff (-2*n-3)

/-- Integral mode (n) has doubled exponent (-2n-2) in the fixed iterate. -/
abbrev bb (b c : B) (n : ℤ) : A := originalI ℒ leechUnit leech_spec.2.2.1 n b c

private abbrev first (b c : B) (p q r : ℤ) (j : ℕ) : O →ₗ[ℂ] O :=
  ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) • (P b (q+r-j)).comp (Q c (p+j))

private abbrev second (b c : B) (p q r : ℤ) (j : ℕ) : O →ₗ[ℂ] O :=
  ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) • (P c (p+r-j)).comp (Q b (q+j))

private abbrev iterate (b c : B) (p q r : ℤ) (j : ℕ) : O →ₗ[ℂ] O :=
  Ring.choose ((q : ℂ) + 1/2) j • oddMode ℒ (bb b c (r+j)) (p+q+1-j)

private theorem finite_tail {V : Type*} [Zero V] (f : ℕ → V) (N : ℕ)
    (hz : ∀ j ≥ N, f j = 0) : Function.HasFiniteSupport f :=
  (Set.finite_lt_nat N).subset fun j hj => lt_of_not_ge fun h => hj (hz j h)

private theorem q_tail (b : B) (o : O) : ∃ N : ℤ, ∀ n ≥ N, Q b n o = 0 := by
  obtain ⟨N, hN⟩ := R_truncation ℒ leechUnit true b o
  exact ⟨N, fun n hn => (rightField_coeff ℒ leechUnit true n b o).trans (hN n hn)⟩

private theorem bb_tail (b c : B) : ∃ N : ℤ, ∀ n ≥ N, bb b c n = 0 := by
  let m (b : B) : ℤ := ActualEnergyRestrictedDual.maxOddWeight ℒ leechUnit b.val
  refine ⟨m b + m c + 6, fun n hn => ?_⟩
  change originalI ℒ leechUnit leech_spec.2.2.1 n b c = 0
  rw [← nu_coeff_eq_originalI]
  apply nu_lower_truncation
  change -2*n-2 < -m b - m c - 6
  have hb : 0 ≤ m b := Int.natCast_nonneg _
  have hc : 0 ≤ m c := Int.natCast_nonneg _
  omega

/-- Each of the three literal BBO sums has pointwise finite support. -/
theorem bbo_support (b c : B) (o : O) (p q r : ℤ) :
    Function.HasFiniteSupport (fun j => first b c p q r j o) ∧
    Function.HasFiniteSupport (fun j => second b c p q r j o) ∧
    Function.HasFiniteSupport (fun j => iterate b c p q r j o) := by
  obtain ⟨N₁, h₁⟩ := q_tail c o
  obtain ⟨N₂, h₂⟩ := q_tail b o
  obtain ⟨N₃, h₃⟩ := bb_tail b c
  refine ⟨finite_tail _ (N₁-p).toNat ?_, finite_tail _ (N₂-q).toNat ?_,
    finite_tail _ (N₃-r).toNat ?_⟩
  · intro j hj
    simp [first, h₁ (p+j) (by omega)]
  · intro j hj
    simp [second, h₂ (q+j) (by omega)]
  · intro j hj
    simp only [iterate, LinearMap.smul_apply, h₃ (r+j) (by omega)]
    have hz : oddMode ℒ (0 : A) (p+q+1-j) o = 0 := by
      apply Subtype.ext
      change (((LatticeAllStateField.Y ℒ 0)[[p+q+1-j]]) o.val) = 0
      simp
    rw [hz, smul_zero]

private def modeSum (f : ℕ → O →ₗ[ℂ] O)
    (hf : ∀ x, Function.HasFiniteSupport (fun j => f j x)) : O →ₗ[ℂ] O where
  toFun x := ∑ᶠ j, f j x
  map_add' x y := by
    simp only [map_add, finsum_add_distrib (hf x) (hf y)]
  map_smul' z x := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum z (fun j => f j x)).symm

/-- The actual signed BBO difference, with the fixed iterate subtracted. -/
def bboDefect (b c : B) (p q r : ℤ) : O →ₗ[ℂ] O := by
  let F := modeSum (first b c p q r) (fun o => (bbo_support b c o p q r).1)
  let G := modeSum (second b c p q r) (fun o => (bbo_support b c o p q r).2.1)
  let I := modeSum (iterate b c p q r) (fun o => (bbo_support b c o p q r).2.2)
  exact {
    toFun := fun o => -F o + G o - I o
    map_add' := fun x y => by
      simp only [map_add]
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_neg, Submodule.coe_sub]
      abel
    map_smul' := fun z x => by
      simp only [map_smul, RingHom.id_apply]
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_neg, Submodule.coe_sub,
        Submodule.coe_smul, smul_add, smul_sub, smul_neg] }

theorem bboDefect_eq_zero_iff_jacobi (b c : B) (o : O) (p q r : ℤ) :
    bboDefect b c p q r o = 0 ↔
      -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
        (mu true b).coeff (-2*(q+r-j)-3)
          ((rightField ℒ leechUnit true c).coeff (-2*(p+j)-3) o)) +
      (∑ᶠ j : ℕ, ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) •
        (mu true c).coeff (-2*(p+r-j)-3)
          ((rightField ℒ leechUnit true b).coeff (-2*(q+j)-3) o)) =
      ∑ᶠ j : ℕ, Ring.choose ((q : ℂ)+1/2) j •
        oddMode ℒ (originalI ℒ leechUnit leech_spec.2.2.1 (r+j) b c) (p+q+1-j) o := by
  change (-(∑ᶠ j, first b c p q r j o) + (∑ᶠ j, second b c p q r j o)) -
    (∑ᶠ j, iterate b c p q r j o) = 0 ↔
    -(∑ᶠ j, first b c p q r j o) + (∑ᶠ j, second b c p q r j o) =
      (∑ᶠ j, iterate b c p q r j o)
  constructor
  · intro he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    simpa only [Submodule.coe_sub, Submodule.coe_zero, sub_eq_zero] using hv
  · intro he
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_zero, he, sub_self]

/-- It suffices to annihilate the actual mixed-field coefficient vectors,
with no change to the signed sums or to the three independent mode labels. -/
theorem bboDefect_eq_zero_iff_on_coefficients (b c : B) (p q r : ℤ) :
    bboDefect b c p q r = 0 ↔
      ∀ (d : B) (s : ℤ) (h : H), bboDefect b c p q r (P d s h) = 0 := by
  constructor
  · intro he d s h
    rw [he, LinearMap.zero_apply]
  · intro h
    have hle : mixedImageSpan ≤ LinearMap.ker (bboDefect b c p q r) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨s, d, v⟩, rfl⟩
      exact h d s v
    rw [mixedImageSpan_eq_top] at hle
    apply LinearMap.ext
    intro o
    exact hle (Submodule.mem_top (x := o))

open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open FourPoint.NativeBBHHActualVectorJacobi (bbhh_actual_vector_coefficient_jacobi)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open NativeMixedPairBorcherds (mu_true_borcherds fixed_on_B_eq_extension)

/-- The native integral fixed mode on the complementary even twisted states. -/
abbrev fixedH (a : A) (n : ℤ) : H →ₗ[ℂ] H := (fixedParitySlice ℒ leechUnit 1 a)[[n]]

abbrev Extension := OriginalOrbifoldField.Carrier ℒ leechUnit

private abbrev extY := OriginalOrbifoldField.Y ℒ leechUnit leech_spec.2.2.1

/-- The native extension's (A,B)-to-(B) mode. -/
abbrev ab (a : A) (b : B) (n : ℤ) : B := (((extY (a, 0))[[n]]) (0, b)).2

/-- The native extension's (B,A)-to-(B) mode. -/
abbrev ba (b : B) (a : A) (n : ℤ) : B := (((extY (0, b))[[n]]) (a, 0)).2

private theorem ext_bb (b c : B) (n : ℤ) :
    ((extY (0, b))[[n]]) (0, c) = (bb b c n, 0) := by
  rw [OriginalOrbifoldField.Y_ncoeff_apply]
  apply Prod.ext
  · simp [bb]
  · simp only [map_zero, add_zero]
    apply Subtype.ext
    simp [fixedParitySlice, VertexOperator.ncoeff_of_coeff]

private theorem ext_ab (a : A) (b : B) (n : ℤ) :
    ((extY (a, 0))[[n]]) (0, b) = (0, ab a b n) := by
  rw [OriginalOrbifoldField.Y_fixed_ncoeff_apply]
  exact Prod.ext (LinearMap.map_zero _) (fixed_on_B_eq_extension a b n)

private theorem ext_ba (b : B) (a : A) (n : ℤ) :
    ((extY (0, b))[[n]]) (a, 0) = (0, ba b a n) := by
  apply Prod.ext
  · rw [OriginalOrbifoldField.Y_ncoeff_apply]
    simp only [map_zero, add_zero]
    apply Subtype.ext
    change ((LatticeAllStateField.Y ℒ 0)[[n]]) a.val = 0
    simp
  · rfl

private theorem choose_int (n : ℤ) (j : ℕ) :
    (((Ring.choose n j : ℤ) : ℂ)) = Ring.choose (n : ℂ) j :=
  Ring.map_choose (Int.castRingHom ℂ) n j

private theorem p_tail (b : B) (h : H) : ∃ N : ℤ, ∀ n ≥ N, P b n h = 0 := by
  let m (v) : ℤ := ActualEnergyRestrictedDual.maxOddWeight ℒ leechUnit v
  refine ⟨m b.val + m h.val + 6, fun n hn => ?_⟩
  apply mu_lower_truncation
  change -2*n-3 ≤ -m b.val - m h.val - 6
  have hb : 0 ≤ m b.val := Int.natCast_nonneg _
  have hh : 0 ≤ m h.val := Int.natCast_nonneg _
  omega

open private fixed_parity_preserved from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

private theorem bb_hahn_iterate (b c : B) (h : H) (m n : ℤ) :
    (⟨(LatticeHalfFockCorrectedField.correctedField ℒ leechUnit
      ((nu true b).coeff (-2*m-2) c).val).coeff (-2*n-2) h.val,
      fixed_parity_preserved ℒ leechUnit 1 _ _ _ h.property⟩ : H) = fixedH (bb b c m) n h := by
  apply Subtype.ext
  simp only [fixedH, fixedParitySlice, VertexOperator.ncoeff_of_coeff, nu_coeff_eq_originalI,
    show 2*(-n-1) = -2*n-2 by ring]
  rfl

/-- The inner BBH signed sum followed by an arbitrary native mixed mode.
Its iterate is the original extension coefficient acting on the even twisted states. -/
theorem bbhh_after_P (b c d : B) (h : H) (t p q r : ℤ) :
    -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      P b t (Q c (q+r-j) (P d (p+j) h))) +
    (∑ᶠ j : ℕ, ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) •
      P b t (Q d (p+r-j) (P c (q+j) h))) =
    ∑ᶠ j : ℕ, Ring.choose ((q : ℂ)+1/2) j •
      P b t (fixedH (bb c d (r+j)) (p+q+1-j) h) := by
  let f (j : ℕ) : H := ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
    Q c (q+r-j) (P d (p+j) h)
  let g (j : ℕ) : H := ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) •
    Q d (p+r-j) (P c (q+j) h)
  let i (j : ℕ) : H := Ring.choose ((q : ℂ)+1/2) j •
    fixedH (bb c d (r+j)) (p+q+1-j) h
  have law : -(∑ᶠ j, f j) + (∑ᶠ j, g j) = ∑ᶠ j, i j := by
    have he := bbhh_actual_vector_coefficient_jacobi c d h q p r
    simp only [choose_int,
      show ∀ j : ℕ, -2*(q+r)-3+2*(j : ℤ) = -2*(q+r-j)-3 by intro; ring,
      show ∀ j : ℕ, -2*(p+r)-3+2*(j : ℤ) = -2*(p+r-j)-3 by intro; ring,
      show ∀ j : ℕ, -2*p-3-2*(j : ℤ) = -2*(p+j)-3 by intro; ring,
      show ∀ j : ℕ, -2*q-3-2*(j : ℤ) = -2*(q+j)-3 by intro; ring,
      show ∀ j : ℕ, -2*r-2-2*(j : ℤ) = -2*(r+j)-2 by intro; ring,
      show ∀ j : ℕ, -2*(q+p+1)-2+2*(j : ℤ) = -2*(p+q+1-j)-2 by intro; ring,
      bb_hahn_iterate] at he
    exact he
  obtain ⟨N₁, ht₁⟩ := p_tail d h
  obtain ⟨N₂, ht₂⟩ := p_tail c h
  obtain ⟨N₃, ht₃⟩ := bb_tail c d
  have hf : Function.HasFiniteSupport f :=
    finite_tail _ (N₁-p).toNat (fun j hj => by simp [f, ht₁ (p+j) (by omega)])
  have hg : Function.HasFiniteSupport g :=
    finite_tail _ (N₂-q).toNat (fun j hj => by simp [g, ht₂ (q+j) (by omega)])
  have hi : Function.HasFiniteSupport i := finite_tail _ (N₃-r).toNat (fun j hj => by
    simp only [i, ht₃ (r+j) (by omega)]
    apply Subtype.ext
    change _ • (((fixedParitySlice ℒ leechUnit 1 (0 : A))[[p+q+1-j]]) h).val = 0
    simp [fixedParitySlice, VertexOperator.ncoeff_of_coeff])
  have hm := congrArg (P b t) law
  change (P b t) (-(∑ᶠ j, f j) + (∑ᶠ j, g j)) = (P b t) (∑ᶠ j, i j) at hm
  have hneg (x : H) : P b t (-x) = -(P b t x) := by
    have hx : -x + x = (0 : H) := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_neg, Submodule.coe_zero, neg_add_cancel]
    have hy := congrArg (P b t) hx
    simp only [map_add, map_zero] at hy
    apply Subtype.ext
    have hy' := congrArg Subtype.val hy
    simp only [Submodule.coe_add, Submodule.coe_zero] at hy'
    rw [Submodule.coe_neg]
    exact eq_neg_of_add_eq_zero_left hy'
  rw [map_add, hneg, map_finsum (P b t) hf, map_finsum (P b t) hg,
    map_finsum (P b t) hi] at hm
  simpa only [f, g, i, map_smul] using hm

private def applyP (h : H) (t : ℤ) : B →ₗ[ℂ] O :=
  (LinearMap.applyₗ h).comp ((LinearMap.proj (-2*t-3)).comp (HVertexOperator.coeff.comp (mu true)))

private abbrev rebracket (h : H) (t : ℤ) : Extension →ₗ[ℂ] O :=
  (applyP h t).comp (LinearMap.snd ℂ A B)

/-- The ordinary extension rebracketing on three original twisted states,
transported through the (B)-state argument of the actual native mixed field. -/
theorem extension_borcherds_after_P (b c d : B) (h : H) (t u v w : ℤ) :
    (∑ᶠ j : ℕ, Ring.choose (u : ℂ) j •
      P (ab (bb b c (w+j)) d (u+v-j)) t h) =
    (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (w : ℂ) j) •
      P (ba b (bb c d (v+j)) (u+w-j)) t h) -
    (∑ᶠ j : ℕ, ((-1 : ℂ)^(w+(j : ℤ)) * Ring.choose (w : ℂ) j) •
      P (ba c (bb b d (u+j)) (v+w-j)) t h) := by
  obtain ⟨hi, hf, hg, he⟩ :=
    ActualLeechExtensionVertexAlgebra.leechVertexAlgebra.borcherds
      ((0, b) : Extension) (0, c) (0, d) u v w
  have hs (j : ℕ) : (-1 : ℂ)^j * integerBinomial w j * epsilon w =
      (-1 : ℂ)^(w+(j : ℤ)) * Ring.choose (w : ℂ) j := by
    rw [epsilon, integerBinomial, choose_int, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
    ring
  have hs' (j : ℕ) : (-1 : ℂ)^j * Ring.choose (w : ℂ) j * epsilon w =
      (-1 : ℂ)^(w+(j : ℤ)) * Ring.choose (w : ℂ) j := by
    simpa only [integerBinomial, choose_int] using hs j
  simp only [smul_sub] at he
  rw [finsum_sub_distrib hf hg] at he
  have hm := congrArg (rebracket h t) he
  rw [map_sub, map_finsum _ hi, map_finsum _ hf, map_finsum _ hg] at hm
  have hP (x : B) : rebracket h t (0, x) = P x t h := rfl
  simpa only [ActualLeechExtensionVertexAlgebra.stateField_eq, ext_bb, ext_ab, ext_ba,
    map_smul, hP, smul_smul, integerBinomial, choose_int, hs'] using hm

/-- Full mixed transport on the actual coefficient source, with the
extension's fixed action on the (B)-state argument displayed explicitly. -/
theorem mixed_transport (a : A) (d : B) (h : H) (n s u : ℤ) :
    let f (k : ℕ) := ((-1 : ℂ)^k * Ring.choose (u : ℂ) k) •
      oddMode ℒ a (n+u-k) (P d (s+k) h)
    let g (k : ℕ) := ((-1 : ℂ)^u * ((-1 : ℂ)^k * Ring.choose (u : ℂ) k)) •
      P d (s+u-k) (fixedH a (n+k) h)
    let i (k : ℕ) := Ring.choose (n : ℂ) k •
      P (ab a d (u+k)) (n+s-k) h
    Function.HasFiniteSupport f ∧ Function.HasFiniteSupport g ∧ Function.HasFiniteSupport i ∧
      (∑ᶠ k, f k) = (∑ᶠ k, i k) + (∑ᶠ k, g k) := by
  dsimp only
  obtain ⟨hi, hf, hg, he⟩ := mu_true_borcherds a d h n s u
  simp only [fixed_on_B_eq_extension] at hi he
  refine ⟨hf, hg, hi, ?_⟩
  apply Subtype.ext
  have hv := congrArg Subtype.val he
  simp only [Submodule.coe_sub] at hv
  rw [Submodule.coe_add]
  exact sub_eq_iff_eq_add.mp hv.symm

/-- The actual BBO iterate on a mixed coefficient, expanded into acted-on
extension states and fixed modes on the complementary even twisted source.
The outer half-binomial is untouched. -/
theorem bbo_iterate_on_coefficient (b c d : B) (h : H) (p q r s : ℤ) :
    (∑ᶠ j, iterate b c p q r j (P d s h)) =
    ∑ᶠ j : ℕ, Ring.choose ((q : ℂ)+1/2) j •
      ((∑ᶠ k : ℕ, Ring.choose ((p+q+1-j : ℤ) : ℂ) k •
        P (ab (bb b c (r+j)) d k) (p+q+1-j+s-k) h) +
        P d s (fixedH (bb b c (r+j)) (p+q+1-j) h)) := by
  refine congrArg (fun f : ℕ → O => ∑ᶠ j, f j) ?_
  funext j
  let n : ℤ := p+q+1-j
  let a := bb b c (r+j)
  have hmix := (mixed_transport a d h n s 0).2.2.2
  dsimp only at hmix
  have hzero (k : ℕ) (hk : k ≠ 0) : Ring.choose (0 : ℂ) k = 0 :=
    Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hk)
  have hf : (∑ᶠ k : ℕ, ((-1 : ℂ)^k * Ring.choose (0 : ℂ) k) •
      oddMode ℒ a (n+0-k) (P d (s+k) h)) = oddMode ℒ a n (P d s h) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro k hk
      simp [hzero k hk]
  have hg : (∑ᶠ k : ℕ, ((-1 : ℂ)^(0 : ℤ) * ((-1 : ℂ)^k * Ring.choose (0 : ℂ) k)) •
      P d (s+0-k) (fixedH a (n+k) h)) = P d s (fixedH a n h) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro k hk
      simp [hzero k hk]
  have hfg := congrArg (fun x : O => Ring.choose ((q : ℂ)+1/2) j • x) hmix
  rw [Int.cast_zero, hf, hg] at hfg
  change Ring.choose ((q : ℂ)+1/2) j • oddMode ℒ a n (P d s h) = _
  simpa only [zero_add, n, a] using hfg

/-- A single iterated extension coefficient rebracketed under the actual
mixed field. The two sums keep their respective inner truncations. -/
theorem extension_iterate_after_P (b c d : B) (h : H) (t v w : ℤ) :
    P (ab (bb b c w) d v) t h =
    (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (w : ℂ) j) •
      P (ba b (bb c d (v+j)) (w-j)) t h) -
    (∑ᶠ j : ℕ, ((-1 : ℂ)^(w+(j : ℤ)) * Ring.choose (w : ℂ) j) •
      P (ba c (bb b d j) (v+w-j)) t h) := by
  have hB := extension_borcherds_after_P b c d h t 0 v w
  rw [Int.cast_zero, finsum_eq_single _ 0] at hB
  · simpa only [Ring.choose_zero_right, one_smul, Nat.cast_zero, zero_add,
      add_zero, sub_zero] using hB
  · intro j hj
    rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), zero_smul]

/-- The rebracketed BBO iterate on an actual generator, with the complementary
fixed mode displayed separately. The order of the three finite summations is
outer half-binomial, mixed iterate, and extension rebracketing. -/
def rebracketedIterate (b c d : B) (h : H) (p q r s : ℤ) : O :=
  ∑ᶠ j : ℕ, Ring.choose ((q : ℂ)+1/2) j •
    ((∑ᶠ k : ℕ, Ring.choose ((p+q+1-j : ℤ) : ℂ) k •
      ((∑ᶠ i : ℕ, ((-1 : ℂ)^i * Ring.choose ((r+j : ℤ) : ℂ) i) •
        P (ba b (bb c d (k+i)) (r+j-i)) (p+q+1-j+s-k) h) -
       (∑ᶠ i : ℕ, ((-1 : ℂ)^(r+(j : ℤ)+(i : ℤ)) * Ring.choose ((r+j : ℤ) : ℂ) i) •
        P (ba c (bb b d i) (k+r+j-i)) (p+q+1-j+s-k) h))) +
     P d s (fixedH (bb b c (r+j)) (p+q+1-j) h))

/-- Native mixed Jacobi followed by ordinary extension rebracketing proves
the full iterate leg on each actual mixed coefficient. -/
theorem bbo_iterate_eq_rebracketed (b c d : B) (h : H) (p q r s : ℤ) :
    (∑ᶠ j, iterate b c p q r j (P d s h)) = rebracketedIterate b c d h p q r s := by
  rw [bbo_iterate_on_coefficient]
  unfold rebracketedIterate
  refine congrArg (fun f : ℕ → O => ∑ᶠ j, f j) ?_
  funext j
  congr 2
  refine congrArg (fun f : ℕ → O => ∑ᶠ k, f k) ?_
  funext k
  apply congrArg (fun x : O => Ring.choose ((p+q+1-j : ℤ) : ℂ) k • x)
  simpa only [Nat.cast_add, add_assoc] using
    extension_iterate_after_P b c d h (p+q+1-j+s-k) k (r+j)

/-- The residual comparison on the generators is between the two literal
signed BBO products and the explicit rebracketed iterate. -/
theorem bbo_on_coefficient_iff_rebracketed (b c d : B) (h : H) (p q r s : ℤ) :
    bboDefect b c p q r (P d s h) = 0 ↔
      -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
        P b (q+r-j) (Q c (p+j) (P d s h))) +
      (∑ᶠ j : ℕ, ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) •
        P c (p+r-j) (Q b (q+j) (P d s h))) =
        rebracketedIterate b c d h p q r s := by
  rw [bboDefect_eq_zero_iff_jacobi]
  change _ = (∑ᶠ j, iterate b c p q r j (P d s h)) ↔ _
  rw [bbo_iterate_eq_rebracketed]
  rfl

/-- The native BBH iterate appearing when the two innermost fields are
exchanged at fixed half-integral mode labels. -/
def innerBBHIterate (c d : B) (h : H) (v s : ℤ) : H :=
  ∑ᶠ k : ℕ, Ring.choose ((v : ℂ)+1/2) k •
    fixedH (bb c d k) (v+s+1-k) h

private theorem inner_exchange (b c d : B) (h : H) (t v s : ℤ) :
    P b t (Q c v (P d s h)) =
      P b t (Q d s (P c v h)) - P b t (innerBBHIterate c d h v s) := by
  have law := bbhh_after_P b c d h t s v 0
  have hzero (j : ℕ) (hj : j ≠ 0) : Ring.choose (0 : ℂ) j = 0 :=
    Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj)
  have hf : (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (0 : ℂ) j) •
      P b t (Q c (v+0-j) (P d (s+j) h))) = P b t (Q c v (P d s h)) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro j hj
      simp [hzero j hj]
  have hg : (∑ᶠ j : ℕ, ((-1 : ℂ)^((0 : ℤ)+(j : ℤ)) * Ring.choose (0 : ℂ) j) •
      P b t (Q d (s+0-j) (P c (v+j) h))) = P b t (Q d s (P c v h)) := by
    rw [finsum_eq_single _ 0]
    · simp
    · intro j hj
      simp [hzero j hj]
  rw [Int.cast_zero, hf, hg] at law
  have hl : (P b t) (innerBBHIterate c d h v s) =
      ∑ᶠ k : ℕ, Ring.choose ((v : ℂ)+1/2) k •
        (P b t) (fixedH (bb c d k) (s+v+1-k) h) := by
    obtain ⟨N, hN⟩ := bb_tail c d
    unfold innerBBHIterate
    have hfin : Function.HasFiniteSupport (fun k : ℕ =>
        Ring.choose ((v : ℂ)+1/2) k • fixedH (bb c d k) (v+s+1-k) h) :=
      finite_tail _ N.toNat fun k hk => by
        rw [hN (k : ℤ) (by omega)]
        apply Subtype.ext
        change _ • ((HVertexOperator.coeff
          (LatticeHalfFockCorrectedField.correctedField ℒ leechUnit 0)
          (2*(-(v+s+1-k)-1))) h.val) = 0
        simp
    rw [map_finsum _ hfin]
    simp only [map_smul, add_comm v s]
  simp only [zero_add] at law
  rw [← hl] at law
  apply Subtype.ext
  have hv := congrArg Subtype.val law
  simp only [Submodule.coe_add, Submodule.coe_neg, Submodule.coe_sub] at hv ⊢
  calc
    _ = (P b t (Q d s (P c v h))).val -
      (-(P b t (Q c v (P d s h))).val + (P b t (Q d s (P c v h))).val) := by abel
    _ = _ := by rw [hv]

/-- Each raw ordered BBO product on an actual mixed coefficient is the
finite sum of crossed products minus the corresponding BBH iterate terms.
The coefficient weight and all four mode labels are retained. -/
theorem ordered_product_on_coefficient (b c d : B) (h : H) (p q r s : ℤ)
    (weight : ℕ → ℂ) :
    (∑ᶠ j : ℕ, weight j • P b (q+r-j) (Q c (p+j) (P d s h))) =
      (∑ᶠ j : ℕ, weight j • P b (q+r-j) (Q d s (P c (p+j) h))) -
      (∑ᶠ j : ℕ, weight j • P b (q+r-j) (innerBBHIterate c d h (p+j) s)) := by
  let ordered (j : ℕ) := weight j • P b (q+r-j) (Q c (p+j) (P d s h))
  let crossed (j : ℕ) := weight j • P b (q+r-j) (Q d s (P c (p+j) h))
  let iter (j : ℕ) := weight j • P b (q+r-j) (innerBBHIterate c d h (p+j) s)
  have he (j : ℕ) : ordered j = crossed j - iter j := by
    apply Subtype.ext
    unfold ordered crossed iter
    rw [inner_exchange b c d h (q+r-j) (p+j) s]
    simp only [Submodule.coe_smul, Submodule.coe_sub, smul_sub]
  obtain ⟨M, hM⟩ := q_tail c (P d s h)
  obtain ⟨N, hN⟩ := p_tail c h
  have hcross : Function.HasFiniteSupport crossed := finite_tail _ (N-p).toNat fun j hj => by
    simp [crossed, hN (p+j) (by omega)]
  have hiter : Function.HasFiniteSupport iter :=
    finite_tail _ (max M N - p).toNat fun j hj => by
      have hmj : M ≤ p + (j : ℤ) := by omega
      have hnj : N ≤ p + (j : ℤ) := by omega
      have hj' := he j
      simp only [ordered, crossed, hM _ hmj, hN _ hnj, map_zero, smul_zero] at hj'
      apply Subtype.ext
      have hk := congrArg Subtype.val hj'
      simpa only [Submodule.coe_zero, Submodule.coe_sub, Submodule.coe_neg, zero_sub,
        zero_eq_neg] using hk
  have hord : Function.HasFiniteSupport ordered := finite_tail _ (M-p).toNat fun j hj => by
    simp [ordered, hM (p+j) (by omega)]
  change (∑ᶠ j, ordered j) = (∑ᶠ j, crossed j) - (∑ᶠ j, iter j)
  apply Subtype.ext
  change (LatticeInvolution.minusSpace ℒ).subtype (∑ᶠ j, ordered j) =
    (LatticeInvolution.minusSpace ℒ).subtype ((∑ᶠ j, crossed j) - (∑ᶠ j, iter j))
  have hw (j : ℕ) := congrArg (LatticeInvolution.minusSpace ℒ).subtype (he j)
  simp only [Submodule.subtype_apply, Submodule.coe_sub] at hw
  rw [show (LatticeInvolution.minusSpace ℒ).subtype ((∑ᶠ j, crossed j) - (∑ᶠ j, iter j)) =
    (LatticeInvolution.minusSpace ℒ).subtype (∑ᶠ j, crossed j) -
      (LatticeInvolution.minusSpace ℒ).subtype (∑ᶠ j, iter j) from Submodule.coe_sub _ _ _]
  rw [map_finsum _ hord, map_finsum _ hcross, map_finsum _ hiter]
  simp only [Submodule.subtype_apply]
  rw [finsum_congr hw]
  have hc : Function.HasFiniteSupport (fun j => (crossed j).val) :=
    hcross.fun_comp (map_zero (LatticeInvolution.minusSpace ℒ).subtype)
  have hi : Function.HasFiniteSupport (fun j => (iter j).val) :=
    hiter.fun_comp (map_zero (LatticeInvolution.minusSpace ℒ).subtype)
  exact finsum_sub_distrib hc hi

/-- The remaining signed comparison after inner BBH transport in both
products and ordinary extension rebracketing in the iterate. -/
theorem bbo_on_coefficient_iff_crossed (b c d : B) (h : H) (p q r s : ℤ) :
    bboDefect b c p q r (P d s h) = 0 ↔
      (let w (j : ℕ) := (-1 : ℂ)^j * Ring.choose (r : ℂ) j
       let w' (j : ℕ) := (-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j
       (-((∑ᶠ j : ℕ, w j • P b (q+r-j) (Q d s (P c (p+j) h))) -
          (∑ᶠ j : ℕ, w j • P b (q+r-j) (innerBBHIterate c d h (p+j) s))) +
        ((∑ᶠ j : ℕ, w' j • P c (p+r-j) (Q d s (P b (q+j) h))) -
          (∑ᶠ j : ℕ, w' j • P c (p+r-j) (innerBBHIterate b d h (q+j) s)))) =
        rebracketedIterate b c d h p q r s) := by
  rw [bbo_on_coefficient_iff_rebracketed]
  dsimp only
  rw [ordered_product_on_coefficient b c d h p q r s,
    ordered_product_on_coefficient c b d h q p r s]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport
