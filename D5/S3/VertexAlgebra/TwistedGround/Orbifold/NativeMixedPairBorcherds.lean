import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds.HomogeneousModes

/-! Extension of the homogeneous mixed Borcherds identity to all native Leech states. -/

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
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private fixedParityMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private minusPart_mem sourcePairing_minusPart_right oddGradeProjection sum_oddGradeProjections from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

open private fixedSourceInclusion fixed_source_expansion from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private fixedProjection from
  D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private projected_basis_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "U" => leechUnit
private theorem mode_tail (s : Bool) (a : A) (x : State s) (m : ℤ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → fixMode s a (m+k) x = 0 := by
  let F := fixedParitySlice ℒ U (paritySign s) a
  let v : ℤ := ((HahnModule.of ℂ).symm (F x)).order
  refine ⟨(-m-1-v).toNat+1, fun k hk =>
    VertexOperator.ncoeff_eq_zero_of_lt_order F (m+k) x ?_⟩
  change -(m+(k : ℤ))-1 < v
  omega

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
