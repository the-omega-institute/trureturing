/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete current/second-source rational field and supported Taylor extraction. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor.LocalResidues

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
open LocalResidues
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.HahnFiberScalar
open CollisionRationalExpansions.FullOrderSpectatorPole
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue
open OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionCoordinates.AdjacentFullOrders
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open LabelledRationalClearing.GlobalRationalCurry
open OrderedCollisionCoordinates.LocalResidueCurrying
open scoped BigOperators VertexOperator RatFunc
noncomputable section

local macro "signed_outer_convolution" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation.finite_signed_outer_convolution))

/-- Joint support includes the fractional inner index, the numerator
monomial, the fractional outer index and the outer mode-convolution index. -/
def secondSourceExpandedJointTerm (backward : Bool) (D : LatticeData)
    (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ)
    (r n : ℤ) (H : ℕ) (p : (ℕ × Exponent 3) × (ℕ × ℕ)) : ℂ :=
  if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
    secondSourceJointTerm backward (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
  else 0

private theorem finite_parameter_fibers {ι κ : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → κ → ℂ)
    (finite : ∀ i, Function.HasFiniteSupport (f i)) :
    Function.HasFiniteSupport (fun p : ι × κ => if p.1 ∈ s then f p.1 p.2 else 0) := by
  classical
  let S := s.biUnion fun i => (finite i).toFinset.image (fun u => (i, u))
  apply S.finite_toSet.subset
  rintro ⟨i, u⟩ nonzero
  change (if i ∈ s then f i u else 0) ≠ 0 at nonzero
  have hi : i ∈ s := by
    by_contra outside
    exact nonzero (ite_eq_right outside)
  have hu : f i u ≠ 0 := by simpa only [ite_eq_left hi] using nonzero
  apply Finset.mem_biUnion.mpr
  exact ⟨i, hi, Finset.mem_image.mpr ⟨u, (finite i).mem_toFinset.mpr hu, rfl⟩⟩

set_option maxHeartbeats 1000000 in
private theorem second_source_expanded_support (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) (r n : ℤ) (H : ℕ) :
    Function.HasFiniteSupport (secondSourceExpandedJointTerm false D a b K P j r n H) ∧
    Function.HasFiniteSupport (secondSourceExpandedJointTerm true D a b K P j r n H) := by
  classical
  constructor
  · change Function.HasFiniteSupport (fun p : (ℕ × Exponent 3) × (ℕ × ℕ) =>
      if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
        secondSourceJointTerm false (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
      else 0)
    exact finite_parameter_fibers
      ((Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support)
      (fun p : ℕ × Exponent 3 =>
        secondSourceJointTerm false (secondSourceTerm D a b K P j p.1 p.2) r n H)
      (fun p => (rational_joint_support
        (secondSourceTerm D a b K P j p.1 p.2) r n H).2.1)
  · change Function.HasFiniteSupport (fun p : (ℕ × Exponent 3) × (ℕ × ℕ) =>
      if p.1 ∈ (Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support then
        secondSourceJointTerm true (secondSourceTerm D a b K P j p.1.1 p.1.2) r n H p.2
      else 0)
    exact finite_parameter_fibers
      ((Finset.range (vectorFrequencyBound D b + 1 - j)) ×ˢ P.coeff.support)
      (fun p : ℕ × Exponent 3 =>
        secondSourceJointTerm true (secondSourceTerm D a b K P j p.1 p.2) r n H)
      (fun p => (rational_joint_support
        (secondSourceTerm D a b K P j p.1 p.2) r n H).2.2)

private theorem finite_rational_outer_readout {ι : Type*} (s : Finset ι)
    (T : ι → SecondSourceField) (gamma r n : ℤ) (H : ℕ) :
    supportedQReadout gamma r H n (secondSourceForward (∑ i ∈ s, T i))
        (secondSourceBackward (∑ i ∈ s, T i)) =
      ∑ i ∈ s, supportedQReadout gamma r H n
        (secondSourceForward (T i)) (secondSourceBackward (T i)) := by
  classical
  have forward (k l : ℤ) :
      secondSourceForward (∑ i ∈ s, T i) k l =
        ∑ i ∈ s, secondSourceForward (T i) k l := by
    simp only [secondSourceForward, map_sum, HahnSeries.coeff_sum]
  have backward (k l : ℤ) :
      secondSourceBackward (∑ i ∈ s, T i) k l =
        ∑ i ∈ s, secondSourceBackward (T i) k l := by
    simp only [secondSourceBackward, map_sum, HahnSeries.coeff_sum]
  unfold supportedQReadout
  calc
    _ = ∑ beta ∈ Finset.range ((H : ℤ) - r).toNat,
        ∑ i ∈ s, Ring.choose (-(gamma : ℂ) / 2) beta *
          ((∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + beta) u *
            secondSourceForward (T i) (r + beta - u) (n - beta + u)) -
           StateFieldResidueReconstruction.epsilon (r + beta) *
            ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + beta) u *
              secondSourceBackward (T i) (r + n - u) u) := by
      apply Finset.sum_congr rfl
      intro beta hbeta
      have finite (i : ι) := (rational_joint_support (T i) r n H).1 beta hbeta
      simp_rw [forward, backward, Finset.mul_sum]
      rw [finsum_sum_comm s _ (fun i _ => (finite i).1),
        finsum_sum_comm s _ (fun i _ => (finite i).2)]
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := Finset.sum_comm

/-- A finite sum of supported complete outer readouts, retaining the actual
numerator monomials rather than interchanging unsupported mode sums. -/
def secondSourceTaylorOuterReadout (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (j : ℕ) (gamma r n : ℤ) (H : ℕ) : ℂ :=
  ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
    ∑ e ∈ P.coeff.support,
      supportedQReadout gamma r H n
        (secondSourceForward (secondSourceTerm D a b K P j alpha e))
        (secondSourceBackward (secondSourceTerm D a b K P j alpha e))

private theorem second_source_outer_expansion (D : LatticeData) (a b : Carrier D)
    (K : ℕ) (P : LabelledPolynomial ℂ 3) (j : ℕ) (gamma r n : ℤ) (H : ℕ) :
    supportedQReadout gamma r H n
        (secondSourceForward (secondSourceTaylorRational D a b K P j))
        (secondSourceBackward (secondSourceTaylorRational D a b K P j)) =
      secondSourceTaylorOuterReadout D a b K P j gamma r n H := by
  have field : secondSourceTaylorRational D a b K P j =
      ∑ alpha ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
        ∑ e ∈ P.coeff.support, secondSourceTerm D a b K P j alpha e := by
    unfold secondSourceTaylorRational secondSourceTerm
    simp_rw [Finset.mul_sum]
  rw [field, finite_rational_outer_readout]
  unfold secondSourceTaylorOuterReadout
  apply Finset.sum_congr rfl
  intro alpha ha
  exact finite_rational_outer_readout _ _ gamma r n H

/- Complete-field padding reuses the finite-tail proof in LeftCurrentTransport. -/
section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
private theorem complete_q_pad (s r : ℤ) (A B : VertexOperator ℂ V) (K L : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator A B) = 0)
    (enlarges : K ≤ L) : qField s r K A B = qField s r L A B := by
  have valid := LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality A B K locality
  exact LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_cutoff A B s r K L
    valid (fun t ht => valid t (by omega))

end

/- proof_shape: actual_current_second_source_rational_field: content
   admission_basis: escape-witness
   escape_witness: Signed Laurent currying at the original J/B diagonal
   computes a finite rational inner field. Both full coefficient maps,
   fractional shifts, supported outer fibers and actual complete-field
   padding are proved together, retaining the supplied P and arbitrary K. -/
/-- The actual complete current/second-source inner field is a single rational
G_j in v,z. Its two ordered mode maps and joint finite mode support agree
with the original nested-Q readout after complete-field padding.
This is the rational-field bridge; the final local outer Taylor contraction
and the full sameNumeratorCollisionBridge are not asserted. -/
theorem actual_current_second_source_rational_field
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H j : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let H' := max H (L + M + K)
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    let G := secondSourceTaylorRational D a b K P j
    (qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)) =
      qField gamma (d + r - j) H' (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1))) ∧
    (secondSourceRational M j R = G) ∧
    (∀ k l : ℤ,
      lastSourceLocalQ 0 true 1 j M l k R = secondSourceForward G k l ∧
      lastSourceLocalQ 0 false 1 j M k l R = secondSourceBackward G k l) ∧
    (∀ ell ∈ Finset.range ((H' : ℤ) - (d + r - j)).toNat,
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((d + r - j) + ell) u *
          secondSourceForward G ((d + r - j) + ell - u) ((n) - ell + u)) ∧
      Function.HasFiniteSupport (fun u : ℕ =>
        BinomialKernelDelta.chooseSign ((d + r - j) + ell) u *
          secondSourceBackward G ((d + r - j) + (n) - u) u)) ∧
    Function.HasFiniteSupport (secondSourceJointTerm false G (d + r - j) n H') ∧
    Function.HasFiniteSupport (secondSourceJointTerm true G (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm false D a b K P j (d + r - j) n H') ∧
    Function.HasFiniteSupport
      (secondSourceExpandedJointTerm true D a b K P j (d + r - j) n H') ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      supportedQReadout gamma (d + r - j) H' n
        (secondSourceForward G) (secondSourceBackward G)) ∧
    (phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n H') ∧
    OuterQCompletion gamma (d + r - j) n H
      (secondSourceForward G) (secondSourceBackward G) := by
  dsimp only
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let H' := max H (L + M + K)
  let R := algebraMap _ (CommonRational ℂ 3) P /
    algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
  let G := secondSourceTaylorRational D a b K P j
  have pad := complete_q_pad gamma (d + r - j)
    (targetSlice D hu a gamma) (targetSlice D hu (neutralMode D i j b) (delta + 1))
    H H' locality (Nat.le_max_left _ _)
  have comparison := LatticeHalfFockSliceQuotient.actual_slice_quotient_compat
    D hu i a b K K gamma delta d r n x phi P P coefficients coefficients
  have original := (comparison.2.2 0 H j).2
  have enlarged := (comparison.2.2 0 H' j).2.1
  have padded_readout :
      phi (((qField gamma (d + r - j) H (targetSlice D hu a gamma)
        (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
      nestedRightLocalReadout 0 gamma 1 j (d + r - j) n M H' R := by
    rw [pad]
    exact enlarged
  have evaluate := second_source_rational_evaluation D a b K P j
  have callbacks (k l : ℤ) :
      lastSourceLocalQ 0 true 1 j M l k R = secondSourceForward G k l ∧
      lastSourceLocalQ 0 false 1 j M k l R = secondSourceBackward G k l := by
    constructor
    · have h := (second_source_coefficients M j R l k).1
      rw [evaluate] at h
      exact h
    · have h := (second_source_coefficients M j R k l).2
      rw [evaluate] at h
      exact h
  have forward : (fun k l => lastSourceLocalQ 0 true 1 j M l k R) =
      secondSourceForward G := by
    funext k l
    exact (callbacks k l).1
  have backward : (fun k l => lastSourceLocalQ 0 false 1 j M k l R) =
      secondSourceBackward G := by
    funext k l
    exact (callbacks k l).2
  have readout :
      nestedRightLocalReadout 0 gamma 1 j (d + r - j) n M H' R =
      supportedQReadout gamma (d + r - j) H' n
        (secondSourceForward G) (secondSourceBackward G) := by
    unfold nestedRightLocalReadout
    rw [forward, backward]
  have completion : OuterQCompletion gamma (d + r - j) n H
      (secondSourceForward G) (secondSourceBackward G) := by
    have h := original.2 locality
    change OuterQCompletion gamma (d + r - j) n H
      (fun k l => lastSourceLocalQ 0 true 1 j M l k R)
      (fun k l => lastSourceLocalQ 0 false 1 j M k l R) at h
    rw [forward, backward] at h
    exact h
  have support := rational_joint_support G (d + r - j) n H'
  have expandedSupport := second_source_expanded_support D a b K P j (d + r - j) n H'
  have expansion := second_source_outer_expansion D a b K P j gamma (d + r - j) n H'
  exact ⟨pad, evaluate, callbacks, support.1, support.2.1, support.2.2,
    expandedSupport.1, expandedSupport.2, padded_readout.trans readout,
    (padded_readout.trans readout).trans expansion, completion⟩

/- The final reverse outer contraction is independent of the lattice carrier.
It consumes the complete-field local evaluation for each original j and keeps
the signed diagonal and origin-pole weights unchanged. -/
theorem second_source_reverse_outer_contraction
    (P : LabelledPolynomial ℂ 3) (gamma d degree : ℤ) (L M : ℕ)
    (T : ℕ → ℂ)
    (hlocal : ∀ j ∈ Finset.range M,
      T j = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range (M - j),
          (if (u : ℤ) ≤ degree then
            collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u))
    (hM : 0 < M) :
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M,
          BinomialKernelDelta.chooseSign d j * T j) =
      StateFieldResidueReconstruction.epsilon (d - L) *
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) ((u : ℤ) - M) := by
  have range_eq : (M - 1) + 1 = M := by omega
  have inner_eq (j : ℕ) (hj : j ∈ Finset.range M) :
      M - 1 - j + 1 = M - j := by
    have hj' := Finset.mem_range.mp hj
    omega
  have reverse (t : ℕ) :
      (∑ j ∈ Finset.range (t + 1), BinomialKernelDelta.chooseSign d j *
        ∑ u ∈ Finset.range (t - j + 1),
          (if (u : ℤ) ≤ degree then collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (t - j - u)) =
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) (u - t - 1) := by
    let F (u : ℕ) : ℂ :=
      if (u : ℤ) ≤ degree then collisionTaylor P gamma u (degree - u).toNat else 0
    have convolution := signed_outer_convolution d (-(L : ℤ)) t F
    rw [show d + -(L : ℤ) = d - L by omega] at convolution
    dsimp only [F] at convolution
    rw [convolution]
    by_cases negative : degree < 0
    · have empty : (degree + 1).toNat = 0 := by omega
      simp only [empty, Finset.range_zero, Finset.sum_empty]
      apply Finset.sum_eq_zero
      intro u member
      rw [if_neg (by omega), zero_mul]
    · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ degree by omega)
      have cutoff : ((N : ℤ) + 1).toNat = N + 1 := by omega
      rw [cutoff]
      calc
        _ = ∑ u ∈ Finset.range (t + 1), if u ≤ N then
            collisionTaylor P gamma u (N - u) *
              BinomialKernelDelta.chooseSign (d - L) (t - u) else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          split_ifs with h h'
          · congr 2
            omega
          · omega
          · omega
          · simp
        _ = ∑ u ∈ Finset.range (N + 1), if u ≤ t then
            collisionTaylor P gamma u (N - u) *
              BinomialKernelDelta.chooseSign (d - L) (t - u) else 0 :=
          finite_rectangle_cut t N _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          have index : ((N : ℤ) - u).toNat = N - u := by omega
          rw [index]
          unfold orderedResidueWeight
          by_cases inside : u ≤ t
          · rw [if_pos inside, if_pos (by omega),
              show (-(↑u - ↑t - 1) - 1 : ℤ).toNat = t - u by omega]
          · rw [if_neg inside, if_neg (by omega), mul_zero]
  have reverse := reverse (M - 1)
  have epsilon_product :
      StateFieldResidueReconstruction.epsilon d *
          StateFieldResidueReconstruction.epsilon (-(L : ℤ)) =
        StateFieldResidueReconstruction.epsilon (d - L) := by
    unfold StateFieldResidueReconstruction.epsilon
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
  have epsilon_mul (j : ℕ) (S : ℂ) :
      StateFieldResidueReconstruction.epsilon d *
          (BinomialKernelDelta.chooseSign d j *
            (StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * S)) =
        StateFieldResidueReconstruction.epsilon (d - L) *
          (BinomialKernelDelta.chooseSign d j * S) := by
    calc
      _ = (StateFieldResidueReconstruction.epsilon d *
          StateFieldResidueReconstruction.epsilon (-(L : ℤ))) *
          (BinomialKernelDelta.chooseSign d j * S) := by ring
      _ = _ := by rw [epsilon_product]
  calc
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M,
          BinomialKernelDelta.chooseSign d j * T j) =
      StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j * T j) := by rw [range_eq]
    _ = ∑ j ∈ Finset.range ((M - 1) + 1),
        StateFieldResidueReconstruction.epsilon d *
          (BinomialKernelDelta.chooseSign d j * T j) := by
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range ((M - 1) + 1),
        StateFieldResidueReconstruction.epsilon (d - L) *
          (BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range (M - j),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ∈ Finset.range M := by simpa only [range_eq] using hj
      rw [hlocal j hjM]
      exact epsilon_mul j _
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range (M - j),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u)) := by
      rw [Finset.mul_sum]
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        (∑ j ∈ Finset.range ((M - 1) + 1),
          BinomialKernelDelta.chooseSign d j *
            ∑ u ∈ Finset.range ((M - 1) - j + 1),
              (if (u : ℤ) ≤ degree then
                collisionTaylor P gamma u (degree - u).toNat else 0) *
                BinomialKernelDelta.chooseSign (-(L : ℤ)) ((M - 1) - j - u)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ∈ Finset.range M := by simpa only [range_eq] using hj
      have hidx : M - j - 1 = M - 1 - j := by
        have hj' := Finset.mem_range.mp hjM
        omega
      rw [inner_eq j hjM, hidx]
    _ = StateFieldResidueReconstruction.epsilon (d - L) *
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) ((u : ℤ) - M) := by
      rw [reverse]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      have hM' : 1 ≤ M := by omega
      have hcast : ((M - 1 : ℕ) : ℤ) + 1 = (M : ℤ) := by
        exact_mod_cast range_eq
      have harg : (u : ℤ) - ((M - 1 : ℕ) : ℤ) - 1 = (u : ℤ) - (M : ℤ) := by
        omega
      rw [harg]

/- The inner finite Taylor index has sharp support before any outer mode
calculation. This is the arithmetic equality used by the complete-field
expansion, including the empty cutoff branch. -/
theorem second_source_inner_sharp_support
    (j M alpha a k : ℕ)
    (ha : a < M - j - alpha)
    (hk : k = M - j - alpha - 1 - a) :
    alpha + a + k = M - j - 1 := by
  omega

/- The two independent Vandermonde contractions used after the sharp support
conditions are imposed. They are stated for arbitrary integer Laurent
exponents, so negative and zero numerator powers remain in scope. -/
theorem second_source_inner_vandermonde (q : ℤ) (u : ℕ) :
    (∑ alpha ∈ Finset.range (u + 1),
      Ring.choose (-(1 : ℂ) / 2) alpha *
        Ring.choose (q : ℂ) (u - alpha)) =
      Ring.choose (q - (1 : ℂ) / 2) u := by
  have h := Ring.add_choose_eq (R := ℂ)
    (r := -(1 : ℂ) / 2) (s := (q : ℂ)) u (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [show q - (1 : ℂ) / 2 = -(1 : ℂ) / 2 + q by ring] using h.symm

theorem second_source_outer_vandermonde (q gamma : ℤ) (u : ℕ) :
    (∑ beta ∈ Finset.range (u + 1),
      Ring.choose (-(gamma : ℂ) / 2) beta *
        Ring.choose (q : ℂ) (u - beta)) =
      Ring.choose ((q : ℂ) - (gamma : ℂ) / 2) u := by
  have h := Ring.add_choose_eq (R := ℂ)
    (r := -(gamma : ℂ) / 2) (s := (q : ℂ)) u (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [show (q : ℂ) - (gamma : ℂ) / 2 =
      -(gamma : ℂ) / 2 + q by ring] using h.symm

private theorem source_monomial_q_readout
    (p q gamma r n : ℤ) (c : ℂ) (N H : ℕ) (bound : N ≤ H)
    (homogeneous : p + q = (N : ℤ) - r - n - 2) :
    supportedQReadout gamma r H n
      (secondSourceForward (sourceMonomial p q c * (vVar - zVar) ^ (-(N : ℤ))))
      (secondSourceBackward (sourceMonomial p q c * (vVar - zVar) ^ (-(N : ℤ)))) =
      c * (if 0 ≤ (N : ℤ) - r - 1 then
        Ring.choose ((p : ℂ) - (gamma : ℂ) / 2) ((N : ℤ) - r - 1).toNat else 0) := by
  classical
  let T := sourceMonomial p q c * (vVar - zVar) ^ (-(N : ℤ))
  have shifted (beta : ℕ) :
      completeOuterResidue r n (secondSourceForward T) (secondSourceBackward T) beta =
      completeOuterResidue (r + beta) (n - beta)
        (secondSourceForward T) (secondSourceBackward T) 0 := by
    simp only [completeOuterResidue, Nat.cast_zero, add_zero, sub_zero,
      show r + (beta : ℤ) + (n - beta) = r + n by omega]
  have expanded :
      supportedQReadout gamma r H n (secondSourceForward T) (secondSourceBackward T) =
      ∑ beta ∈ Finset.range ((H : ℤ) - r).toNat,
        if (beta : ℤ) ≤ (N : ℤ) - r - 1 then
          c * (Ring.choose (-(gamma : ℂ) / 2) beta *
            ((Ring.choose p ((N : ℤ) - r - 1 - beta).toNat : ℤ) : ℂ)) else 0 := by
    unfold supportedQReadout
    apply Finset.sum_congr rfl
    intro beta hb
    change Ring.choose _ beta *
      completeOuterResidue r n (secondSourceForward T) (secondSourceBackward T) beta = _
    rw [shifted]
    dsimp only [T]
    rw [source_monomial_complete_residue]
    rw [if_pos (show p + q = -(r + (beta : ℤ) + -(N : ℤ)) - (n - beta) - 2 by omega)]
    by_cases h : (beta : ℤ) ≤ (N : ℤ) - r - 1
    · rw [if_pos h, if_pos (show r + (beta : ℤ) + -(N : ℤ) < 0 by omega)]
      rw [show -(r + (beta : ℤ) + -(N : ℤ)) - 1 = (N : ℤ) - r - 1 - beta by omega]
      ring
    · rw [if_neg h, if_neg (show ¬ r + (beta : ℤ) + -(N : ℤ) < 0 by omega), mul_zero]
  change supportedQReadout gamma r H n (secondSourceForward T) (secondSourceBackward T) = _
  rw [expanded]
  by_cases positive : 0 ≤ (N : ℤ) - r - 1
  · rw [if_pos positive]
    let v := ((N : ℤ) - r - 1).toNat
    have hv : (v : ℤ) = (N : ℤ) - r - 1 := by dsimp [v]; omega
    have range_bound : v + 1 ≤ ((H : ℤ) - r).toNat := by omega
    have restrict :
        (∑ beta ∈ Finset.range ((H : ℤ) - r).toNat,
          if (beta : ℤ) ≤ (N : ℤ) - r - 1 then
            c * (Ring.choose (-(gamma : ℂ) / 2) beta *
              ((Ring.choose p ((N : ℤ) - r - 1 - beta).toNat : ℤ) : ℂ)) else 0) =
        ∑ beta ∈ Finset.range (v + 1),
          c * (Ring.choose (-(gamma : ℂ) / 2) beta *
            ((Ring.choose p (v - beta) : ℤ) : ℂ)) := by
      rw [← Finset.sum_subset (Finset.range_mono range_bound) (by
        intro beta hbig hsmall
        rw [if_neg (by simp only [Finset.mem_range, not_lt] at hsmall; omega)])]
      apply Finset.sum_congr rfl
      intro beta hb
      have hb' := Finset.mem_range.mp hb
      rw [if_pos (by omega), show ((N : ℤ) - r - 1 - beta).toNat = v - beta by omega]
    rw [restrict, ← Finset.mul_sum]
    congr 1
    have casts (h : ℕ) : ((Ring.choose p h : ℤ) : ℂ) = Ring.choose (p : ℂ) h :=
      Ring.map_choose (Int.castRingHom ℂ) p h
    simp_rw [casts]
    exact second_source_outer_vandermonde p gamma v
  · rw [if_neg positive, mul_zero]
    apply Finset.sum_eq_zero
    intro beta hb
    exact if_neg (by omega)

private theorem source_inner_triangle (q : ℤ) (B : ℕ) (F : ℕ → ℂ) :
    (∑ alpha ∈ Finset.range B,
      ∑ h ∈ Finset.range (B - alpha),
        Ring.choose (-(1 : ℂ) / 2) alpha * ((Ring.choose q h : ℤ) : ℂ) * F (alpha + h)) =
      ∑ u ∈ Finset.range B, Ring.choose ((q : ℂ) - 1 / 2) u * F u := by
  have flip := Finset.sum_range_diag_flip B (fun alpha h =>
    Ring.choose (-(1 : ℂ) / 2) alpha * ((Ring.choose q h : ℤ) : ℂ) * F (alpha + h))
  calc
    _ = ∑ u ∈ Finset.range B,
        ∑ alpha ∈ Finset.range (u + 1),
          Ring.choose (-(1 : ℂ) / 2) alpha *
            ((Ring.choose q (u - alpha) : ℤ) : ℂ) * F u := by
      rw [← flip]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro alpha ha
      have halpha : alpha ≤ u := by simpa using Finset.mem_range.mp ha
      rw [Nat.add_sub_of_le halpha]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_mul]
      congr 1
      have casts (h : ℕ) : ((Ring.choose q h : ℤ) : ℂ) = Ring.choose (q : ℂ) h :=
        Ring.map_choose (Int.castRingHom ℂ) q h
      simp_rw [casts]
      exact second_source_inner_vandermonde q u

private theorem source_epsilon_sub (p : ℤ) (k : ℕ) :
    StateFieldResidueReconstruction.epsilon (p - k) =
      StateFieldResidueReconstruction.epsilon p * (-1 : ℂ) ^ k := by
  unfold StateFieldResidueReconstruction.epsilon
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast,
    div_eq_mul_inv, ← inv_pow, inv_neg_one]

/- The two independent finite Vandermonde contractions expand the exact
collisionTaylor coefficient on the original signed exponent support. This
helper is consumed by the actual third-telescope composition below. -/
private theorem second_source_collision_taylor_sum
    (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) :
    collisionTaylor P gamma u v =
      P.coeff.sum (fun e c =>
        c *
          (∑ alpha ∈ Finset.range (u + 1),
            Ring.choose (-(1 : ℂ) / 2) alpha *
              Ring.choose (e 0 : ℂ) (u - alpha)) *
          (∑ beta ∈ Finset.range (v + 1),
            Ring.choose (-(gamma : ℂ) / 2) beta *
              Ring.choose (e 1 : ℂ) (v - beta))) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp [collisionTaylor, Finsupp.linearCombination_apply]
  | add P Q hP hQ =>
      simp only [collisionTaylor, AddMonoidAlgebra.coeff_add,
        Finsupp.linearCombination_apply, smul_eq_mul]
      conv_rhs =>
        rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
      conv_lhs =>
        rw [Finsupp.sum_add_index (by simp) (by intros; ring)]
      have hP' := hP
      have hQ' := hQ
      simp only [collisionTaylor, Finsupp.linearCombination_apply,
        smul_eq_mul] at hP' hQ'
      rw [hP', hQ']
  | single e c =>
      simp only [collisionTaylor, AddMonoidAlgebra.coeff_single,
        Finsupp.linearCombination_single, smul_eq_mul]
      rw [Finsupp.sum_single_index (by simp)]
      rw [second_source_inner_vandermonde (e 0) u,
        second_source_outer_vandermonde (e 1) gamma v]
      ring_nf


private theorem source_inner_readout_evaluation
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j alpha : ℕ) (e : Exponent 3) (gamma d r n : ℤ) (H : ℕ)
    (bound : vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K ≤ H)
    (homogeneous : totalExponent e =
      (vectorFrequencyBound D a + 1 : ℤ) + (vectorFrequencyBound D b + 1 : ℤ) +
        K - d - r - n - 3) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let degree : ℤ := (L : ℤ) + M + K - d - r - 2
    supportedQReadout gamma (d + r - j) H n
      (secondSourceForward (secondSourceInnerTaylorTerm D a b K P j alpha e))
      (secondSourceBackward (secondSourceInnerTaylorTerm D a b K P j alpha e)) =
      StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * P.coeff e *
        ∑ h ∈ Finset.range (M - j - alpha),
          Ring.choose (-(1 : ℂ) / 2) alpha * ((Ring.choose (e 0) h : ℤ) : ℂ) *
            (if (alpha + h : ℤ) ≤ degree then
              Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) (degree - alpha - h).toNat
             else 0) * BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - alpha - 1 - h) := by
  classical
  dsimp only
  rw [source_inner_monomial_normal_form, finite_rational_outer_readout, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let k := M - j - alpha - 1 - h
  let N := K + L + k
  have hh' : h < M - j - alpha := Finset.mem_range.mp hh
  have sharp : alpha + h + k = M - j - 1 :=
    second_source_inner_sharp_support j M alpha h k hh' rfl
  have castk : (k : ℤ) = (M : ℤ) - j - alpha - 1 - h := by dsimp [k]; omega
  have ht : -(K : ℤ) - (L : ℤ) - k = -(N : ℤ) := by dsimp [N]; push_cast; ring
  have hN : N ≤ H := by dsimp [N, L, M] at *; omega
  have total : totalExponent e = e 0 + e 1 + e 2 := by
    simp only [totalExponent, Fin.sum_univ_succ, Fin.sum_univ_two]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    ring
  have hom : e 1 + (e 0 + e 2 - alpha - h) =
      (N : ℤ) - (d + r - j) - n - 2 := by
    dsimp [N, L, M] at *
    rw [total] at homogeneous
    push_cast
    omega
  change supportedQReadout _ _ _ _
    (secondSourceForward (sourceMonomial _ _ _ * (vVar - zVar) ^
      (-(K : ℤ) - (L : ℤ) - k)))
    (secondSourceBackward (sourceMonomial _ _ _ * (vVar - zVar) ^
      (-(K : ℤ) - (L : ℤ) - k))) = _
  rw [ht, source_monomial_q_readout _ _ _ _ _ _ N H hN hom]
  have idx : (N : ℤ) - (d + r - j) - 1 =
      (L : ℤ) + M + K - d - r - 2 - alpha - h := by
    dsimp [N]; push_cast; omega
  rw [idx, source_epsilon_sub]
  change _ = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * P.coeff e *
    (Ring.choose (-(1 : ℂ) / 2) alpha * ((Ring.choose (e 0) h : ℤ) : ℂ) *
      (if (alpha + h : ℤ) ≤ (L : ℤ) + M + K - d - r - 2 then
        Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2)
          ((L : ℤ) + M + K - d - r - 2 - alpha - h).toNat else 0) *
        BinomialKernelDelta.chooseSign (-(L : ℤ)) k)
  unfold BinomialKernelDelta.chooseSign
  by_cases hv : (alpha + h : ℤ) ≤ (L : ℤ) + M + K - d - r - 2
  · rw [if_pos hv, if_pos (by omega)]
    dsimp only [L, M, k]
    push_cast
    ring
  · rw [if_neg hv, if_neg (by omega)]
    ring

private theorem source_complete_taylor_readout
    (D : LatticeData) (a b : Carrier D) (K : ℕ) (P : LabelledPolynomial ℂ 3)
    (j : ℕ) (gamma d r n : ℤ) (H : ℕ)
    (bound : vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K ≤ H)
    (homogeneous : ∀ e ∈ P.coeff.support, totalExponent e =
      (vectorFrequencyBound D a + 1 : ℤ) + (vectorFrequencyBound D b + 1 : ℤ) +
        K - d - r - n - 3) :
    let L := vectorFrequencyBound D a + 1
    let M := vectorFrequencyBound D b + 1
    let degree : ℤ := (L : ℤ) + M + K - d - r - 2
    secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n H =
      StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range (M - j),
          (if (u : ℤ) ≤ degree then
            collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u) := by
  classical
  dsimp only
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let B := M - j
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  let F (e : Exponent 3) (u : ℕ) : ℂ :=
    (if (u : ℤ) ≤ degree then
      Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) (degree - u).toNat else 0) *
      BinomialKernelDelta.chooseSign (-(L : ℤ)) (B - 1 - u)
  have per_e (e : Exponent 3) (he : e ∈ P.coeff.support) :
      (∑ alpha ∈ Finset.range B,
        supportedQReadout gamma (d + r - j) H n
          (secondSourceForward (secondSourceTerm D a b K P j alpha e))
          (secondSourceBackward (secondSourceTerm D a b K P j alpha e))) =
        StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * P.coeff e *
          ∑ u ∈ Finset.range B, Ring.choose ((e 0 : ℂ) - 1 / 2) u * F e u := by
    calc
      _ = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * P.coeff e *
          ∑ alpha ∈ Finset.range B,
            ∑ h ∈ Finset.range (B - alpha),
              Ring.choose (-(1 : ℂ) / 2) alpha * ((Ring.choose (e 0) h : ℤ) : ℂ) *
                F e (alpha + h) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro alpha ha
        rw [second_source_monomial_taylor_index D a b K P j alpha e
          (Finset.mem_range.mp ha), source_inner_readout_evaluation D a b K P
            j alpha e gamma d r n H bound (homogeneous e he)]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        dsimp only [F, B, degree, L, M]
        rw [show vectorFrequencyBound D b + 1 - j - 1 - (alpha + h) =
          vectorFrequencyBound D b + 1 - j - alpha - 1 - h by omega]
        push_cast
        simp only [sub_add_eq_sub_sub]
        ring
      _ = _ := by rw [source_inner_triangle]
  unfold secondSourceTaylorOuterReadout
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ P.coeff.support,
        StateFieldResidueReconstruction.epsilon (-(L : ℤ)) * P.coeff e *
          ∑ u ∈ Finset.range B, Ring.choose ((e 0 : ℂ) - 1 / 2) u * F e u := by
      apply Finset.sum_congr rfl
      exact per_e
    _ = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range B,
          ∑ e ∈ P.coeff.support, P.coeff e *
            Ring.choose ((e 0 : ℂ) - 1 / 2) u * F e u := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      change (∑ e ∈ P.coeff.support, P.coeff e *
        Ring.choose ((e 0 : ℂ) - 1 / 2) u *
          ((if (u : ℤ) ≤ degree then
            Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (B - 1 - u))) =
        (if (u : ℤ) ≤ degree then collisionTaylor P gamma u (degree - u).toNat else 0) *
          BinomialKernelDelta.chooseSign (-(L : ℤ)) (B - 1 - u)
      by_cases inside : (u : ℤ) ≤ degree
      · simp only [if_pos inside, collisionTaylor, Finsupp.linearCombination_apply,
          Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        ring
      · simp only [if_neg inside, zero_mul, mul_zero, Finset.sum_const_zero]

private theorem second_source_third_conjunct_of_local_taylor
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H₃ : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0)
    (local_taylor : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      secondSourceTaylorOuterReadout D a b K P j gamma (d + r - j) n
        (max (H₃ j) (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K)) =
      StateFieldResidueReconstruction.epsilon
          (-(vectorFrequencyBound D a + 1 : ℤ)) *
        ∑ u ∈ Finset.range (vectorFrequencyBound D b + 1 - j),
          (if (u : ℤ) ≤
              (vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 then
            collisionTaylor P gamma u
              ((vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 - u).toNat
           else 0) *
          BinomialKernelDelta.chooseSign (-(vectorFrequencyBound D a + 1 : ℤ))
            (vectorFrequencyBound D b + 1 - j - 1 - u)) :
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range (vectorFrequencyBound D b + 1),
          BinomialKernelDelta.chooseSign d j *
            phi (((qField gamma (d + r - j) (H₃ j)
              (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x)) =
      StateFieldResidueReconstruction.epsilon
          (d - (vectorFrequencyBound D a + 1 : ℤ)) *
        ∑ u ∈ Finset.range
            ((vectorFrequencyBound D a + 1 : ℤ) +
              (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 + 1).toNat,
          collisionTaylor P gamma u
              ((vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 - u).toNat *
            orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℤ))
              ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℤ)) := by
  let L : ℕ := vectorFrequencyBound D a + 1
  let M : ℕ := vectorFrequencyBound D b + 1
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  let T : ℕ → ℂ := fun j =>
    phi (((qField gamma (d + r - j) (H₃ j)
      (targetSlice D hu a gamma)
      (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x)
  have hlocal (j : ℕ) (hj : j ∈ Finset.range M) :
      T j = StateFieldResidueReconstruction.epsilon (-(L : ℤ)) *
        ∑ u ∈ Finset.range (M - j),
          (if (u : ℤ) ≤ degree then
            collisionTaylor P gamma u (degree - u).toNat else 0) *
            BinomialKernelDelta.chooseSign (-(L : ℤ)) (M - j - 1 - u) := by
    have hbridge := actual_current_second_source_rational_field D hu i a b K
      gamma delta d r n x phi P coefficients (H₃ j) j (locality j hj)
    rcases hbridge with ⟨_, _, _, _, _, _, _, _, _, hreadout, _⟩
    dsimp [T, L, M, degree]
    rw [hreadout]
    simpa only [second_source_collision_taylor_sum] using local_taylor j hj
  have hM : 0 < M := by dsimp [M]; omega
  have contracted := second_source_reverse_outer_contraction P gamma d degree L M T hlocal hM
  simpa only [T, L, M, degree, Nat.cast_add, Nat.cast_one] using contracted


/- proof_shape: actual_second_source_third: content
   admission_basis: escape-witness
   escape_witness: Both ordered Hahn maps of the original inner Taylor field
   are evaluated before taking their signed difference. The complete pole
   support and original numerator degree give the finite double Taylor
   contraction, consumed by the original THIRD telescope. -/
/-- The original current/second-source THIRD identity, with every supplied
numerator, cutoff, signed mode and complete-field locality hypothesis. -/
theorem actual_second_source_third
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H₃ : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0)
 :
    StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range (vectorFrequencyBound D b + 1),
          BinomialKernelDelta.chooseSign d j *
            phi (((qField gamma (d + r - j) (H₃ j)
              (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x)) =
      StateFieldResidueReconstruction.epsilon
          (d - (vectorFrequencyBound D a + 1 : ℤ)) *
        ∑ u ∈ Finset.range
            ((vectorFrequencyBound D a + 1 : ℤ) +
              (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 + 1).toNat,
          collisionTaylor P gamma u
              ((vectorFrequencyBound D a + 1 : ℤ) +
                (vectorFrequencyBound D b + 1 : ℤ) + K - d - r - 2 - u).toNat *
            orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℤ))
              ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℤ)) := by
  apply second_source_third_conjunct_of_local_taylor D hu i a b K
    gamma delta d r n x phi P coefficients H₃ locality
  intro j hj
  apply source_complete_taylor_readout D a b K P j gamma d r n
    (max (H₃ j) (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K))
  · exact le_max_right _ _
  · intro e he
    have nonzero : P.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
    have h := coefficients e
    have degree : totalExponent e =
        (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3 := by
      by_contra hne
      rw [if_neg hne] at h
      exact nonzero h
    have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by decide
    have orders : (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) =
        (vectorFrequencyBound D a + 1 : ℤ) + (vectorFrequencyBound D b + 1 : ℤ) + K := by
      simp [pairs, threeOrders]
      ring
    rw [orders] at degree
    exact degree

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
