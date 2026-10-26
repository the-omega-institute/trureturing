/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-source original-mu current closure from actual nested residues. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi
import D5.S3.VertexAlgebra.ChargedResidue.SourceToQ

/-! Original source Borcherds is mapped to the unchanged actual corrected
fields. The source tail and the complete target residue cutoff are independent.
Classical lattice local-field calculus: Bakalov--Kac, math/0402315.
No positivity, finite charge space, second eigenvector or transport premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockLeftCurrentTransport Calculus
open LatticeHalfFockPhysicalRescaling LatticeHalfFockCorrectedField
open LatticeAllStateReconstruction LatticeAllStateJacobi
open NestedResidues.LatticeHalfFockCollisionJacobi

private theorem native_product_at_locality
    (D : LatticeData) (hu : IsUnit D.G.det) (a b : Carrier D)
    (gamma delta r : ℤ) (K : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0) :
    nativeProduct D hu a b gamma delta r =
      qField gamma r K (targetSlice D hu a gamma) (targetSlice D hu b delta) := by
  let KN := Classical.choose (native_valid_exists D hu a b gamma delta)
  have valid := Classical.choose_spec (native_valid_exists D hu a b gamma delta) 0
  have z0 : Z 0 (targetSlice D hu a gamma) = targetSlice D hu a gamma := by
    apply HVertexOperator.coeff_inj
    funext e
    change (targetSlice D hu a gamma).coeff (e + 0) =
      (targetSlice D hu a gamma).coeff e
    rw [add_zero]
  change Valid (Z 0 (targetSlice D hu a gamma)) (targetSlice D hu b delta) KN at valid
  rw [z0] at valid
  change Q (targetSlice D hu a gamma) (targetSlice D hu b delta) gamma r KN =
    Q (targetSlice D hu a gamma) (targetSlice D hu b delta) gamma r K
  exact Q_cutoff _ _ gamma r KN K valid (valid_of_locality _ _ K locality)

private theorem compatible_at_locality
    (D : LatticeData) (hu : IsUnit D.G.det) (a b : Carrier D)
    (gamma delta r : ℤ) (K : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0)
    (law : OriginalCompatible D hu a b gamma delta) :
    targetSlice D hu (mu D a r b) (gamma+delta) =
      qField gamma r K (targetSlice D hu a gamma) (targetSlice D hu b delta) := by
  have zero := compatible_defect D hu a b gamma delta law r
  change targetSlice D hu (mu D a r b) (gamma+delta) -
    nativeProduct D hu a b gamma delta r = 0 at zero
  exact (sub_eq_zero.mp zero).trans
    (native_product_at_locality D hu a b gamma delta r K locality)

private def sourceSliceLinear (D : LatticeData) (hu : IsUnit D.G.det) (s : ℤ) :
    Carrier D →ₗ[ℂ] VertexOperator ℂ (ActualTensor D hu) where
  toFun := fun a => targetSlice D hu a s
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext e
    simp only [VertexOperator.coeff_eq_ncoeff, targetSlice, physicalSlice_mode,
      map_add, Pi.add_apply]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext e
    simp only [VertexOperator.coeff_eq_ncoeff, targetSlice, physicalSlice_mode,
      map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The original source Borcherds specialization uses an actual vector tail.
The cutoff is not inferred from target locality. -/
private theorem original_current_iterate
    (D : LatticeData) (i : Fin D.rank) (a b : Carrier D) (d r : ℤ)
    (K : ℕ) (tail : ∀ t : ℤ, (K : ℤ) ≤ t → mu D a t b = 0) :
    mu D (neutralMode D i d a) r b =
      (∑ j ∈ Finset.range ((K : ℤ)-r).toNat,
        BinomialKernelDelta.chooseSign d j •
          neutralMode D i (d-j) (mu D a (r+j) b)) -
      StateFieldResidueReconstruction.epsilon d •
        ∑ j ∈ Finset.range (vectorFrequencyBound D b+1),
          BinomialKernelDelta.chooseSign d j •
            mu D a (d+r-j) (neutralMode D i j b) := by
  classical
  let h := neutralMode D i (-1) (LatticeAllStateField.vacuum D)
  have original := borcherds D h a b 0 r d
  have left :
      (∑ᶠ j : ℕ, jacobiLeftTerm D 0 r d h a b j) =
        mu D (neutralMode D i d a) r b := by
    rw [finsum_eq_single _ 0]
    · simp [jacobiLeftTerm, StateFieldResidueReconstruction.integerBinomial,
        h, LatticeHalfFockCurrentBorcherds.source_current]
    · intro j different
      simp [jacobiLeftTerm, StateFieldResidueReconstruction.integerBinomial,
        Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]
  have firstFinite := original.2.1
  have secondFinite := original.2.2.1
  change Function.HasFiniteSupport (fun j : ℕ => jacobiRightFirstTerm D 0 r d h a b j)
    at firstFinite
  change Function.HasFiniteSupport (fun j : ℕ => jacobiRightSecondTerm D 0 r d h a b j)
    at secondFinite
  simp only [jacobiRightFirstTerm, zero_add,
    h, LatticeHalfFockCurrentBorcherds.source_current] at firstFinite
  simp only [jacobiRightSecondTerm, zero_add,
    h, LatticeHalfFockCurrentBorcherds.source_current] at secondFinite
  change Function.HasFiniteSupport (fun j : ℕ =>
    BinomialKernelDelta.chooseSign d j • neutralMode D i (d-j) (mu D a (r+j) b))
    at firstFinite
  change Function.HasFiniteSupport (fun j : ℕ =>
    BinomialKernelDelta.chooseSign d j • (StateFieldResidueReconstruction.epsilon d •
      mu D a (r+d-j) (neutralMode D i j b))) at secondFinite
  have firstSum :
      (∑ᶠ j : ℕ, BinomialKernelDelta.chooseSign d j •
        neutralMode D i (d-j) (mu D a (r+j) b)) =
      ∑ j ∈ Finset.range ((K : ℤ)-r).toNat,
        BinomialKernelDelta.chooseSign d j •
          neutralMode D i (d-j) (mu D a (r+j) b) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra outside
    have zero := tail (r+j) (by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
      omega)
    exact hj (by dsimp only; rw [zero, map_zero, smul_zero])
  have secondSum :
      (∑ᶠ j : ℕ, BinomialKernelDelta.chooseSign d j •
        (StateFieldResidueReconstruction.epsilon d •
          mu D a (r+d-j) (neutralMode D i j b))) =
      StateFieldResidueReconstruction.epsilon d •
        ∑ j ∈ Finset.range (vectorFrequencyBound D b+1),
          BinomialKernelDelta.chooseSign d j •
            mu D a (d+r-j) (neutralMode D i j b) := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (vectorFrequencyBound D b+1)) _ ?_]
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show r+d-(j : ℤ) = d+r-j by omega, smul_comm]
    · intro j hj
      by_contra outside
      have zero := neutralMode_vanish D i b j (by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
        omega)
      exact hj (by simp [zero, mu])
  have law := original.2.2.2
  rw [left] at law
  simp only [zero_add, h, LatticeHalfFockCurrentBorcherds.source_current,
    smul_sub] at law
  change mu D (neutralMode D i d a) r b =
    (∑ᶠ j : ℕ, (BinomialKernelDelta.chooseSign d j •
      neutralMode D i (d-j) (mu D a (r+j) b) -
      BinomialKernelDelta.chooseSign d j •
        (StateFieldResidueReconstruction.epsilon d •
          mu D a (r+d-j) (neutralMode D i j b)))) at law
  rw [finsum_sub_distrib firstFinite secondFinite, firstSum, secondSum] at law
  exact law

/- proof_shape: first_current_step: content
   admission_basis: escape-witness
   escape_witness: Actual source Borcherds and same-numerator nested residues
   agree after the smaller original compatibility identifies the inner
   fields. The source vector tail and target Q support are joined without
   inferring one from the other; vanishing every native defect recovers all
   three finite supports of the full signed law. -/
/-- First-source current closure uses only compatibility of the smaller first
source with every second source and lift. It toggles the first lift once,
independently of the signed current mode. -/
theorem first_current_step
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a : Carrier D) (gamma : ℤ)
    (smaller : ∀ b : Carrier D, ∀ delta : ℤ,
      OriginalCompatible D hu a b gamma delta)
    (d : ℤ) (b : Carrier D) (delta : ℤ) :
    OriginalCompatible D hu (neutralMode D i d a) b (gamma+1) delta := by
  classical
  apply defect_compatible
  intro r
  obtain ⟨KAB, localAB⟩ := source_slice_locality D hu a b
  let KS : ℕ := (-((HahnModule.of ℂ).symm (LatticeAllStateField.Y D a b)).order-1).toNat+1
  let K := max KAB KS
  have tail (t : ℤ) (ht : (K : ℤ) ≤ t) : mu D a t b = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    dsimp [K, KS] at ht
    omega
  have localityAB : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0 := by
    rw [show K = (K-KAB)+KAB by dsimp [K]; omega,
      pow_add, Module.End.mul_apply, localAB gamma delta, map_zero]
  obtain ⟨H₁, local₁⟩ := source_slice_locality D hu (neutralMode D i d a) b
  let H₂ (j : ℕ) := vectorFrequencyBound D (mu D a (r+j) b)+1
  let H₃ (j : ℕ) := Classical.choose
    (source_slice_locality D hu a (neutralMode D i j b))
  have local₃ (j : ℕ) :
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta+1))) = 0 :=
    Classical.choose_spec (source_slice_locality D hu a (neutralMode D i j b))
      gamma (delta+1)
  have inverse (t : ℤ) :
      qField gamma t K (targetSlice D hu a gamma) (targetSlice D hu b delta) =
        targetSlice D hu (mu D a t b) (gamma+delta) :=
    (compatible_at_locality D hu a b gamma delta t K localityAB (smaller b delta)).symm
  have local₂ (j : ℕ) :
      (FieldNormalProductLocality.deltaEnd ^ H₂ j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r+j) K
            (targetSlice D hu a gamma) (targetSlice D hu b delta))) = 0 := by
    rw [inverse]
    exact current_slice_locality D hu i (mu D a (r+j) b) (gamma+delta)
  have nested := actual_nested_iterate D hu i a b K gamma delta d r H₁ H₂ H₃
    localityAB (local₁ (gamma+1) delta) (fun j _ => local₂ j) (fun j _ => local₃ j)
  have third (j : ℕ) :
      qField gamma (d+r-j) (H₃ j) (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta+1)) =
      targetSlice D hu (mu D a (d+r-j) (neutralMode D i j b)) (gamma+(delta+1)) :=
    (compatible_at_locality D hu a (neutralMode D i j b)
      gamma (delta+1) (d+r-j) (H₃ j) (local₃ j)
      (smaller (neutralMode D i j b) (delta+1))).symm
  simp_rw [inverse, third] at nested
  simp only [H₂] at nested
  have inverseCurrent (v : Carrier D) (s t : ℤ) :
      qField 1 t (vectorFrequencyBound D v+1) (targetCurrent D hu i)
        (targetSlice D hu v s) = targetSlice D hu (neutralMode D i t v) (s+1) :=
    (native_current_inverse D hu i v s t).symm
  simp_rw [inverseCurrent] at nested
  rw [show gamma+delta+1 = (gamma+1)+delta by omega,
    show gamma+(delta+1) = (gamma+1)+delta by omega] at nested
  have source := congrArg (sourceSliceLinear D hu ((gamma+1)+delta))
    (original_current_iterate D i a b d r K tail)
  simp only [map_sub, map_sum, map_smul] at source
  have equality :
      targetSlice D hu (mu D (neutralMode D i d a) r b) ((gamma+1)+delta) =
      qField (gamma+1) r H₁
        (targetSlice D hu (neutralMode D i d a) (gamma+1))
        (targetSlice D hu b delta) :=
    source.trans nested.symm
  change targetSlice D hu (mu D (neutralMode D i d a) r b) ((gamma+1)+delta) -
    nativeProduct D hu (neutralMode D i d a) b (gamma+1) delta r = 0
  rw [native_product_at_locality D hu (neutralMode D i d a) b
    (gamma+1) delta r H₁ (local₁ (gamma+1) delta)]
  exact sub_eq_zero.mpr equality

private theorem compatible_add_left
    (D : LatticeData) (hu : IsUnit D.G.det) (a c b : Carrier D)
    (gamma delta : ℤ)
    (ha : OriginalCompatible D hu a b gamma delta)
    (hc : OriginalCompatible D hu c b gamma delta) :
    OriginalCompatible D hu (a+c) b gamma delta := by
  intro p q r x
  have fields : targetSlice D hu (a+c) gamma =
      targetSlice D hu a gamma + targetSlice D hu c gamma :=
    (sourceSliceLinear D hu gamma).map_add a c
  have iterates (t : ℤ) :
      targetSlice D hu (mu D (a+c) t b) (gamma+delta) =
      targetSlice D hu (mu D a t b) (gamma+delta) +
        targetSlice D hu (mu D c t b) (gamma+delta) := by
    have h : mu D (a+c) t b = mu D a t b + mu D c t b := by
      simp [mu]
    rw [h]
    exact (sourceSliceLinear D hu (gamma+delta)).map_add _ _
  have left (j : ℕ) :
      leftTerm (fun t => targetSlice D hu (mu D (a+c) t b) (gamma+delta))
        gamma p q r x j =
      leftTerm (fun t => targetSlice D hu (mu D a t b) (gamma+delta))
        gamma p q r x j +
      leftTerm (fun t => targetSlice D hu (mu D c t b) (gamma+delta))
        gamma p q r x j := by
    simp only [leftTerm, iterates, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  have first (j : ℕ) :
      firstTerm (targetSlice D hu (a+c) gamma) (targetSlice D hu b delta) p q r x j =
      firstTerm (targetSlice D hu a gamma) (targetSlice D hu b delta) p q r x j +
      firstTerm (targetSlice D hu c gamma) (targetSlice D hu b delta) p q r x j := by
    simp only [firstTerm, fields, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  have second (j : ℕ) :
      secondTerm (targetSlice D hu (a+c) gamma) (targetSlice D hu b delta) p q r x j =
      secondTerm (targetSlice D hu a gamma) (targetSlice D hu b delta) p q r x j +
      secondTerm (targetSlice D hu c gamma) (targetSlice D hu b delta) p q r x j := by
    simp only [secondTerm, fields, map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  change Function.HasFiniteSupport
      (leftTerm (fun t => targetSlice D hu (mu D (a+c) t b) (gamma+delta))
        gamma p q r x) ∧
    Function.HasFiniteSupport
      (firstTerm (targetSlice D hu (a+c) gamma) (targetSlice D hu b delta) p q r x) ∧
    Function.HasFiniteSupport
      (secondTerm (targetSlice D hu (a+c) gamma) (targetSlice D hu b delta) p q r x) ∧
    (∑ᶠ j : ℕ, leftTerm
      (fun t => targetSlice D hu (mu D (a+c) t b) (gamma+delta)) gamma p q r x j) =
      (∑ᶠ j : ℕ, firstTerm (targetSlice D hu (a+c) gamma)
        (targetSlice D hu b delta) p q r x j) -
      (∑ᶠ j : ℕ, secondTerm (targetSlice D hu (a+c) gamma)
        (targetSlice D hu b delta) p q r x j)
  rw [funext left, funext first, funext second]
  obtain ⟨hlA, hfA, hsA, eqA⟩ := ha p q r x
  obtain ⟨hlC, hfC, hsC, eqC⟩ := hc p q r x
  refine ⟨hlA.add hlC, hfA.add hfC, hsA.add hsC, ?_⟩
  dsimp only [targetSlice]
  rw [finsum_add_distrib hlA hlC, finsum_add_distrib hfA hfC,
    finsum_add_distrib hsA hsC, eqA, eqC]
  module

private theorem first_word
    (D : LatticeData) (hu : IsUnit D.G.det)
    (word : List (Index D)) (alpha : Charge D)
    (epsilon : Bool) (gamma : ℤ)
    (matching : sectorSign epsilon = (-1 : ℂ) ^ gamma) :
    ∀ b : Carrier D, ∀ delta : ℤ,
      OriginalCompatible D hu
        (rightCurrentWord D word (projectedGround D alpha (wordParity word epsilon)))
        b gamma delta := by
  induction word generalizing epsilon gamma with
  | nil =>
    intro b delta
    exact projectedGround_arbitrary_second D hu
      (LatticeHalfFockChargedResidue.charged_sector_ground_pair D hu)
      alpha epsilon gamma delta b matching
  | cons j word ih =>
    have back : sectorSign (!epsilon) = (-1 : ℂ) ^ (gamma-1) := by
      rw [sectorSign_not, matching]
      have h := zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) (gamma-1) 1
      rw [show gamma-1+1 = gamma by omega, zpow_one, mul_neg_one] at h
      rw [h, neg_neg]
    have smaller := ih (!epsilon) (gamma-1) back
    intro b delta
    have h := first_current_step D hu j.1
      (rightCurrentWord D word
        (projectedGround D alpha (wordParity word (!epsilon))))
      (gamma-1) smaller (-((j.2+1 : ℕ) : ℤ)) b delta
    simpa only [rightCurrentWord, wordParity,
      show gamma-1+1 = gamma by omega] using h

/- proof_shape: first_eigen_arbitrary_second: content
   admission_basis: escape-witness
   escape_witness: The source-current closure is iterated through the actual
   finite theta-sector expansion. Independent finite charge and oscillator
   sums close on the left, retaining the exact matching first eigenvalue.
   No second-source eigenvalue, positivity or finite charge space is assumed. -/
/-- Matching-theta-eigen first source and arbitrary original second source.
This is the original all-signed three-supported coefficient law on the
unchanged actual tensor carrier. -/
theorem first_eigen_arbitrary_second
    (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D) (gamma : ℤ)
    (eigen : LatticeInvolution.theta D a = (-1 : ℂ) ^ gamma • a)
    (b : Carrier D) (delta : ℤ) :
    OriginalCompatible D hu a b gamma delta := by
  classical
  let epsilon : Bool := if Even gamma then false else true
  have matching : sectorSign epsilon = (-1 : ℂ) ^ gamma := by
    rw [neg_one_zpow_eq_ite]
    by_cases h : Even gamma <;> simp [epsilon, sectorSign, h]
  have zero : OriginalCompatible D hu (0 : Carrier D) b gamma delta := by
    have h := first_word D hu [] (0 : Charge D) epsilon gamma matching b delta
    have hs := compatible_smul_left D hu _ b gamma delta (0 : ℂ) h
    simpa only [zero_smul] using hs
  let S : Submodule ℂ (Carrier D) := {
    carrier := {c | OriginalCompatible D hu c b gamma delta}
    zero_mem' := zero
    add_mem' := fun ha hc => compatible_add_left D hu _ _ b gamma delta ha hc
    smul_mem' := fun c _ hc => compatible_smul_left D hu _ b gamma delta c hc }
  have projection : sectorProject D epsilon a = a := by
    change (2 : ℂ)⁻¹ • (a + sectorSign epsilon • LatticeInvolution.theta D a) = a
    rw [eigen, smul_smul, ← matching, sectorSign_square]
    module
  change a ∈ S
  rw [← projection, theta_source_expansion]
  apply S.sum_mem
  intro alpha halpha
  apply S.sum_mem
  intro e he
  apply S.smul_mem
  exact first_word D hu (LatticeAllStateField.occurrences D e)
    alpha epsilon gamma matching b delta

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
