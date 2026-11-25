/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeComplementBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full signed homogeneous mode Jacobi on the actual Leech complement. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionVertexAlgebra
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOFullIterate
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedRightWeakAssociativity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementBorcherds

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold)
open ActualLeechExtensionVertexAlgebra (leechVertexAlgebra stateField_eq)
open LatticeInvolution (FixedCarrier fixedMode mem_fixedSpace theta)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd OddCarrier oddMode leechUnit paritySign)
open NativeBBOCoefficientTransport (P Q bb ba fixedH bbo_support bboDefect bboDefect_eq_zero_iff_jacobi)
open NativeBBOIntegerLocality (F G F_mode G_mode)
open OriginalOrbifoldField (Y_ncoeff_apply Y_fixed_ncoeff_apply)
open MixedIntertwiner (originalRightCoefficient)
open StateFieldResidueReconstruction (integerBinomial epsilon)

open private fixedParityMode_val oddMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private ext_bb ext_ba bb_hahn_iterate p_tail bb_tail finite_tail choose_int iterate from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

local notation "ℒ" => leechData
local notation "U" => leechUnit
local notation "A" => FixedCarrier ℒ
local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier ℒ

/-- The two homogeneous inclusions into the ordinary Leech extension. -/
def homogeneousState : (s : Bool) → (if s then B else A) → Orbifold
  | false, a => (a, 0)
  | true, b => (0, b)

/-- Mode with doubled physical index `2*n + (if s then 1 else 0)`, acting
through the parity-`s` component of the ordinary Leech state. -/
def modeOnComplement (s : Bool) (a : Orbifold) (n : ℤ) : Module.End ℂ (H × O) :=
  if s then (F a.2)[[n]] else (G a.1)[[n]]

private abbrev forwardWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * Ring.choose (r : ℂ) j

private abbrev reverseWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j

private theorem choose_integer (n : ℤ) (j : ℕ) :
    integerBinomial n j = Ring.choose (n : ℂ) j :=
  Ring.map_choose (Int.castRingHom ℂ) n j

private theorem reverseWeight_eq (r : ℤ) (j : ℕ) :
    (-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j = epsilon r * forwardWeight r j := by
  unfold forwardWeight epsilon
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, mul_assoc]

private theorem signed_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : ℤ) (j : ℕ) (x : V) :
    ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) • ((-1 : ℂ)^r • x) = reverseWeight r j • x := by
  unfold reverseWeight
  rw [reverseWeight_eq, smul_smul, epsilon, mul_comm (forwardWeight r j)]

private abbrev CoefficientLaw {V : Type*} [AddCommGroup V] (I F R : ℕ → V) : Prop :=
  Function.HasFiniteSupport I ∧ Function.HasFiniteSupport F ∧ Function.HasFiniteSupport R ∧
    (∑ᶠ j, I j) = (∑ᶠ j, F j) - (∑ᶠ j, R j)

private theorem restrictLaw {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} {I F R : ℕ → S}
    (h : CoefficientLaw (fun j => (I j).val) (fun j => (F j).val) (fun j => (R j).val)) :
    CoefficientLaw I F R := by
  have support (f : ℕ → S) (hf : Function.HasFiniteSupport (fun j => (f j).val)) :
      Function.HasFiniteSupport f :=
    hf.subset fun j hj hz => hj (Subtype.ext hz)
  let incl := S.subtype.toAddMonoidHom
  have inj : Function.Injective incl := Subtype.val_injective
  refine ⟨support I h.1, support F h.2.1, support R h.2.2.1, inj ?_⟩
  rw [map_sub incl, incl.map_finsum_of_injective inj I, incl.map_finsum_of_injective inj F,
    incl.map_finsum_of_injective inj R]
  exact h.2.2.2

private theorem fixedMode_val (a b : A) (n : ℤ) :
    (fixedMode ℒ a n b).val = LatticeAllStateReconstruction.mu ℒ a.val n b.val := rfl

private theorem even_on_H (a b : A) (h : H) (p q r : ℤ) :
    CoefficientLaw
      (fun j => Ring.choose (p : ℂ) j • fixedH (fixedMode ℒ a (r+j) b) (p+q-j) h)
      (fun j => forwardWeight r j • fixedH a (p+r-j) (fixedH b (q+j) h))
      (fun j => reverseWeight r j • fixedH b (q+r-j) (fixedH a (p+j) h)) := by
  have eigen : theta ℒ a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace ℒ a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    ℒ U a.val 0 eigen b.val 0
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have law := native p q r h.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at law
  have hmode (c : A) (n : ℤ) (v : H) : (fixedH c n v).val =
      (LatticeHalfFockCorrectedField.correctedField ℒ U c.val).coeff
        (-2*n-2) v.val :=
    fixedParityMode_val ℒ U (paritySign false) c n v
  apply restrictLaw
  simpa only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode, Int.cast_zero, zero_div,
    add_zero, sub_zero, signed_smul, Submodule.coe_smul, hmode,
    fixedMode_val, forwardWeight] using law

private theorem even_on_O (a b : A) (o : O) (p q r : ℤ) :
    CoefficientLaw
      (fun j => Ring.choose (p : ℂ) j • oddMode ℒ (fixedMode ℒ a (r+j) b) (p+q-j) o)
      (fun j => forwardWeight r j • oddMode ℒ a (p+r-j) (oddMode ℒ b (q+j) o))
      (fun j => reverseWeight r j • oddMode ℒ b (q+r-j) (oddMode ℒ a (p+j) o)) := by
  have law := LatticeAllStateJacobi.borcherds ℒ a.val b.val o.val p q r
  obtain ⟨hi, hf, hr, he⟩ := law
  simp only [smul_sub] at he
  change (∑ᶠ j, LatticeAllStateJacobi.jacobiLeftTerm ℒ p q r a.val b.val o.val j) =
    ∑ᶠ j, (LatticeAllStateJacobi.jacobiRightFirstTerm ℒ p q r a.val b.val o.val j -
      LatticeAllStateJacobi.jacobiRightSecondTerm ℒ p q r a.val b.val o.val j) at he
  rw [finsum_sub_distrib hf hr] at he
  unfold LatticeAllStateJacobi.jacobiLeftTerm at hi he
  unfold LatticeAllStateJacobi.jacobiRightFirstTerm at hf he
  unfold LatticeAllStateJacobi.jacobiRightSecondTerm at hr he
  apply restrictLaw
  simpa only [CoefficientLaw, Submodule.coe_smul, oddMode_val, fixedMode_val, choose_integer,
    epsilon, signed_smul, forwardWeight] using And.intro hi (And.intro hf (And.intro hr he))

private theorem neg_support {V : Type*} [AddCommGroup V] {f : ℕ → V}
    (hf : Function.HasFiniteSupport f) : Function.HasFiniteSupport (fun j => -f j) :=
  hf.subset fun j hj hzero => hj (by simp [hzero])

private theorem negateLaw {V : Type*} [AddCommGroup V] {I F R : ℕ → V}
    (h : CoefficientLaw I F R) : CoefficientLaw (fun j => -I j) (fun j => -F j) (fun j => -R j) := by
  refine ⟨neg_support h.1, neg_support h.2.1, neg_support h.2.2.1, ?_⟩
  simp only [finsum_neg_distrib]
  rw [h.2.2.2]
  abel

private theorem oddPairLaw {V : Type*} [AddCommGroup V] {I F R : ℕ → V}
    (hf : Function.HasFiniteSupport F) (hr : Function.HasFiniteSupport R)
    (hi : Function.HasFiniteSupport I)
    (he : -(∑ᶠ j, F j) + (∑ᶠ j, R j) = ∑ᶠ j, I j) :
    CoefficientLaw I (fun j => -F j) (fun j => -R j) := by
  refine ⟨hi, neg_support hf, neg_support hr, ?_⟩
  simpa only [finsum_neg_distrib, sub_neg_eq_add] using he.symm

private theorem odd_on_H (b c : B) (h : H) (p q r : ℤ) :
    CoefficientLaw
      (fun j => Ring.choose ((p : ℂ)+1/2) j • fixedH (bb b c (r+j)) (p+q+1-j) h)
      (fun j => -(forwardWeight r j • Q b (p+r-j) (P c (q+j) h)))
      (fun j => -(reverseWeight r j • Q c (q+r-j) (P b (p+j) h))) := by
  apply oddPairLaw
  · obtain ⟨N, hN⟩ := p_tail c h
    refine finite_tail _ (N-q).toNat fun j hj => ?_
    simp only [hN (q+j) (by omega), map_zero, smul_zero]
  · obtain ⟨N, hN⟩ := p_tail b h
    refine finite_tail _ (N-p).toNat fun j hj => ?_
    simp only [hN (p+j) (by omega), map_zero, smul_zero]
  · obtain ⟨N, hN⟩ := bb_tail b c
    refine finite_tail _ (N-r).toNat fun j hj => ?_
    rw [hN (r+j) (by omega)]
    apply Subtype.ext
    change _ • (((fixedParitySlice ℒ U 1 (0 : A))[[p+q+1-j]]) h).val = 0
    simp [fixedParitySlice, VertexOperator.ncoeff_of_coeff]
  · have law := FourPoint.NativeBBHHActualVectorJacobi.bbhh_actual_vector_coefficient_jacobi
      b c h p q r
    simp only [choose_int, paritySign,
      show ∀ j : ℕ, -2*(p+r)-3+2*(j : ℤ) = -2*(p+r-j)-3 by intro; ring,
      show ∀ j : ℕ, -2*(q+r)-3+2*(j : ℤ) = -2*(q+r-j)-3 by intro; ring,
      show ∀ j : ℕ, -2*q-3-2*(j : ℤ) = -2*(q+j)-3 by intro; ring,
      show ∀ j : ℕ, -2*p-3-2*(j : ℤ) = -2*(p+j)-3 by intro; ring,
      show ∀ j : ℕ, -2*r-2-2*(j : ℤ) = -2*(r+j)-2 by intro; ring,
      show ∀ j : ℕ, -2*(p+q+1)-2+2*(j : ℤ) = -2*(p+q+1-j)-2 by intro; ring,
      bb_hahn_iterate] at law
    exact law

private theorem odd_on_O (b c : B) (o : O) (p q r : ℤ) :
    CoefficientLaw
      (fun j => Ring.choose ((p : ℂ)+1/2) j • oddMode ℒ (bb b c (r+j)) (p+q+1-j) o)
      (fun j => -(forwardWeight r j • P b (p+r-j) (Q c (q+j) o)))
      (fun j => -(reverseWeight r j • P c (q+r-j) (Q b (p+j) o))) := by
  obtain ⟨hf, hr, hi⟩ := bbo_support b c o q p r
  have hz : bboDefect b c q p r o = 0 := by
    rw [NativeBBOFullIterate.bboDefect_eq_zero, LinearMap.zero_apply]
  have law := (bboDefect_eq_zero_iff_jacobi b c o q p r).mp hz
  apply oddPairLaw hf hr
  · simpa only [iterate, LinearMap.smul_apply, add_comm q p] using hi
  · simp only [add_comm q p] at law
    exact law

private theorem assemble (I F R : ℕ → H × O)
    (hH : CoefficientLaw (fun j => (I j).1) (fun j => (F j).1) (fun j => (R j).1))
    (hO : CoefficientLaw (fun j => (I j).2) (fun j => (F j).2) (fun j => (R j).2)) :
    CoefficientLaw I F R := by
  classical
  have support (f : ℕ → H × O) (hf : Function.HasFiniteSupport (fun j => (f j).1))
      (hs : Function.HasFiniteSupport (fun j => (f j).2)) : Function.HasFiniteSupport f := by
    refine (hf.union hs).subset fun j hj => ?_
    change (f j).1 ≠ 0 ∨ (f j).2 ≠ 0
    by_contra outside
    apply hj
    apply Prod.ext
    · by_contra hn
      exact outside (Or.inl hn)
    · by_contra hn
      exact outside (Or.inr hn)
  obtain ⟨hIH, hFH, hRH, heH⟩ := hH
  obtain ⟨hIO, hFO, hRO, heO⟩ := hO
  have hi := support I hIH hIO
  have hf := support F hFH hFO
  have hr := support R hRH hRO
  refine ⟨hi, hf, hr, Prod.ext ?_ ?_⟩
  · let π := LinearMap.fst ℂ H O
    change π (∑ᶠ j, I j) = π ((∑ᶠ j, F j) - (∑ᶠ j, R j))
    rw [map_sub π, map_finsum π hi, map_finsum π hf, map_finsum π hr]
    exact heH
  · let π := LinearMap.snd ℂ H O
    change π (∑ᶠ j, I j) = π ((∑ᶠ j, F j) - (∑ᶠ j, R j))
    rw [map_sub π, map_finsum π hi, map_finsum π hf, map_finsum π hr]
    exact heO

/-- The full signed Jacobi coefficients on an arbitrary complementary vector.
The physical product indices are `p + s/2` and `q + t/2`, with the
Booleans read as zero or one. The iterate is the actual ordinary Leech
state-field coefficient and carries to the next integral label for two odd
sources. Each of the three weighted families has finite support. -/
theorem actual_homogeneous_borcherds (s t : Bool)
    (a : if s then B else A) (b : if t then B else A) (x : H × O) (p q r : ℤ) :
    let a' := homogeneousState s a
    let b' := homogeneousState t b
    let I := fun j : ℕ => Ring.choose ((p : ℂ) + (if s then 1/2 else 0)) j •
      modeOnComplement (Bool.xor s t) (((leechVertexAlgebra.stateField a')[[r+j]]) b')
        (p+q+(if s && t then 1 else 0)-j) x
    let F := fun j : ℕ => ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      modeOnComplement s a' (p+r-j) (modeOnComplement t b' (q+j) x)
    let R := fun j : ℕ => ((-1 : ℂ)^(r+(j : ℤ)) * Ring.choose (r : ℂ) j) •
      modeOnComplement t b' (q+r-j) (modeOnComplement s a' (p+j) x)
    Function.HasFiniteSupport I ∧ Function.HasFiniteSupport F ∧ Function.HasFiniteSupport R ∧
      (∑ᶠ j, I j) = (∑ᶠ j, F j) - (∑ᶠ j, R j) := by
  have ordinaryAA (a b : A) (n : ℤ) :
      ((leechVertexAlgebra.stateField (a, 0))[[n]]) (b, 0) = (fixedMode ℒ a n b, 0) := by
    simp only [stateField_eq, Y_fixed_ncoeff_apply, map_zero]
  have ordinaryAB (a : A) (b : B) (n : ℤ) :
      ((leechVertexAlgebra.stateField (a, 0))[[n]]) (0, b) =
        (0, ((fixedParitySlice ℒ U (-1) a)[[n]]) b) := by
    simp only [stateField_eq, Y_fixed_ncoeff_apply, map_zero]
  have ordinaryBA (b : B) (a : A) (n : ℤ) :
      ((leechVertexAlgebra.stateField (0, b))[[n]]) (a, 0) =
        (0, originalRightCoefficient ℒ U n b a) := by
    rw [stateField_eq, ext_ba, ba, Y_ncoeff_apply]
    simp only [map_zero, zero_add]
  have ordinaryBB (b c : B) (n : ℤ) :
      ((leechVertexAlgebra.stateField (0, b))[[n]]) (0, c) = (bb b c n, 0) := by
    rw [stateField_eq, ext_bb]
  cases s <;> cases t <;>
    simp only [homogeneousState, modeOnComplement, Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, add_zero, ordinaryAA, ordinaryAB, ordinaryBA, ordinaryBB] <;>
    apply assemble <;>
    simp only [F_mode, G_mode, Prod.smul_fst, Prod.smul_snd]
  · exact even_on_H a b x.1 p q r
  · exact even_on_O a b x.2 p q r
  · change A at a
    change ↥(HalfFock.LatticeHalfFockParityField.paritySpace ℒ U (-1)) at b
    have law := NativeMixedRightBorcherds.rightField_true_borcherds a b x.2 p q r
    have unsigned : CoefficientLaw
        (fun j => Ring.choose (p : ℂ) j • Q (((fixedParitySlice ℒ U (-1) a)[[r+j]]) b)
          (p+q-j) x.2)
        (fun j => forwardWeight r j • fixedH a (p+r-j) (Q b (q+j) x.2))
        (fun j => reverseWeight r j • Q b (q+r-j) (oddMode ℒ a (p+j) x.2)) := by
      dsimp only at law
      simp only [smul_smul, mul_comm (_ : ℂ) ((-1 : ℂ)^r)] at law
      simp only [reverseWeight_eq, epsilon]
      exact law
    convert negateLaw unsigned using 1 <;> funext j
    · exact smul_neg (Ring.choose (p : ℂ) j) (_ : H)
    · exact (congrArg (fun v : H => forwardWeight r j • v)
        (LinearMap.map_neg (fixedH a (p+r-j)) (Q b (q+j) x.2))).trans
        (smul_neg _ _)
    · exact smul_neg (reverseWeight r j) (_ : H)
  · simp only [reverseWeight_eq, epsilon]
    exact NativeMixedPairBorcherds.mu_true_borcherds a b x.1 p q r
  · have law := NativeMixedRightWeakAssociativity.rightField_true_reversed_borcherds a b x.2 p q r
    dsimp only at law
    simp only [add_comm q p] at law
    simp only [reverseWeight_eq]
    exact law
  · have law := NativeMixedPairWeakAssociativity.mu_true_reversed_borcherds a b x.1 p q r
    dsimp only at law
    simp only [add_comm q p] at law
    simp only [reverseWeight_eq]
    exact law
  · change B at a b
    convert odd_on_H a b x.1 p q r using 1 <;> funext j
    · exact smul_neg (forwardWeight r j) (_ : H)
    · exact smul_neg (reverseWeight r j) (_ : H)
  · change B at a b
    convert odd_on_O a b x.2 p q r using 1 <;> funext j
    · exact (congrArg (fun v : O => forwardWeight r j • v) (LinearMap.map_neg _ _)).trans
        (smul_neg _ _)
    · exact (congrArg (fun v : O => reverseWeight r j • v) (LinearMap.map_neg _ _)).trans
        (smul_neg _ _)

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementBorcherds.actual_homogeneous_borcherds' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms actual_homogeneous_borcherds

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeComplementBorcherds
