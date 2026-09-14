/- GID: D5/S3/Weil/BurnolGram/FrameSeparationParameters
   generality: I
   mirror-B: D5/B/S3/Weil/BurnolGram/FrameSeparationParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derive finite node radii and positive squared gaps from the frame certificate and removal of full target orbits, leaving only arithmetic premises in the sparse negative certificate. -/

import D5.S3.Weil.BurnolGram.WeilFiniteDataNegativeCertificate

/-!
# Separation parameters for every finite even Weil orbit frame

The frame's `nodeEquiv` makes distinct labels distinct nodes; its stored
`signSeparated` field excludes their negatives, for all four plus/minus
combinations. These two facts make the node squares distinct. No inference
of sign separation from `offLine` or `conjugateMove` is needed.

The sparse exception set removes the full four-point target orbits.
Injectivity of `gamma` and its symmetry identities therefore exclude equality
between a node square and an exception square. Finite minima give positive
gaps, with the exception set formed only after choosing the radius and nodal
gap. Empty finite sets impose no constraints and use the positive bound one.

The corollary chooses these parameters before quantifying over the remaining
cutoff and budget arithmetic. It retains the full conclusion, including its
support radius, and does not assert existence of a nonempty off-line frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.BurnolGram.FrameSeparationParameters

open Set MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.InterpolationJets.QuantitativeEvenSeed
open D5.S3.Weil.InterpolationJets.SparseEvenInterpolationJets
open D5.S3.Weil.BurnolGram.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.BurnolGram.FiniteOrbitBurnolPacket
open D5.S3.Weil.BurnolGram.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.BurnolGram.WeilFullGramInertia
open D5.S3.Weil.BurnolGram.WeilMixedHeadTailBudget
open D5.S3.Weil.BurnolGram.BurnolRationalDepthBudget
open D5.S3.Weil.BurnolGram.QuantitativeFiniteWeilPacket
open D5.S3.Weil.BurnolGram.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.BurnolGram.SparseBurnolPacketJets
open D5.S3.Weil.BurnolGram.ExplicitWeilFourthMomentTail
open D5.S3.Weil.BurnolGram.WeilFiniteDataNegativeCertificate
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

variable {Z : ZeroData} {ι : Type*} [Fintype ι]

private theorem node_sq_ne (F : FiniteEvenWeilOrbitFrame Z ι)
    (u v : Sum ι ι) (huv : u ≠ v) :
    (F.nodeEquiv u).1 ^ 2 ≠ (F.nodeEquiv v).1 ^ 2 := by
  have hne : (F.nodeEquiv u).1 ≠ (F.nodeEquiv v).1 :=
    fun h => huv (F.nodeEquiv.injective (Subtype.ext h))
  have hneg := F.signSeparated (F.nodeEquiv u).property
    (F.nodeEquiv v).property hne
  exact fun h => (sq_eq_sq_iff_eq_or_eq_neg.mp h).elim hne hneg

private theorem node_sq_ne_exception [DecidableEq ι]
    (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma : ℝ)
    (u : Sum ι ι) (n : ℕ) (hn : n ∈ sparsePacketExceptions F R sigma) :
    (F.nodeEquiv u).1 ^ 2 ≠ Z.gamma n ^ 2 := by
  have hnot : n ∉ frameTargetIndices F := (Finset.mem_sdiff.mp hn).2
  intro heq
  apply hnot
  cases u with
  | inl i =>
    apply orbit_subset_frameTargetIndices F i
    rw [F.plusNode] at heq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · have hi : n = F.index i := gamma_injective Z h.symm
      simp [zeroOrbit, hi]
    · have hi : n = Z.reflection (F.index i) := by
        apply gamma_injective Z
        simpa only [Z.gamma_reflection, neg_neg] using (congrArg Neg.neg h).symm
      simp [zeroOrbit, hi]
  | inr i =>
    apply orbit_subset_frameTargetIndices F i
    rw [F.minusNode] at heq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · have hi : n = Z.conjugation (Z.reflection (F.index i)) := by
        apply gamma_injective Z
        simpa using h.symm
      simp [zeroOrbit, hi]
    · have hi : n = Z.conjugation (F.index i) := by
        apply gamma_injective Z
        simpa only [Z.gamma_conjugation, neg_neg] using (congrArg Neg.neg h).symm
      simp [zeroOrbit, hi]

private theorem finite_positive_lower_bound {α : Type*}
    (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, 0 < f x) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ s, t ≤ f x := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx, hmin⟩ := s.exists_min_image f hs
    exact ⟨f x, hf x hx, hmin⟩
  · exact ⟨1, zero_lt_one, fun x hx => (hs ⟨x, hx⟩).elim⟩

/-- Every frame supplies its own finite geometric separation parameters. -/
theorem exists_frame_separation_parameters
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ R sigma tau : ℝ, 0 ≤ R ∧ 0 < sigma ∧ 0 < tau ∧
      (∀ u : Sum ι ι, ‖(F.nodeEquiv u).1‖ ≤ R) ∧
      (∀ u v : Sum ι ι, u ≠ v →
        sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖) ∧
      (∀ u : Sum ι ι, ∀ n ∈ sparsePacketExceptions F R sigma,
        tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖) := by
  classical
  let R : ℝ := ∑ u : Sum ι ι, ‖(F.nodeEquiv u).1‖
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hz (u : Sum ι ι) : ‖(F.nodeEquiv u).1‖ ≤ R :=
    Finset.single_le_sum (fun v _ => norm_nonneg (F.nodeEquiv v).1) (Finset.mem_univ u)
  let pairs := (Finset.univ : Finset (Sum ι ι × Sum ι ι)).filter
    (fun uv => uv.1 ≠ uv.2)
  obtain ⟨sigma, hsigma, hgap⟩ := finite_positive_lower_bound pairs
    (fun uv => ‖(F.nodeEquiv uv.1).1 ^ 2 - (F.nodeEquiv uv.2).1 ^ 2‖)
    (fun uv huv => norm_pos_iff.mpr (sub_ne_zero.mpr
      (node_sq_ne F uv.1 uv.2 (Finset.mem_filter.mp huv).2)))
  let cross := (Finset.univ : Finset (Sum ι ι)) ×ˢ sparsePacketExceptions F R sigma
  obtain ⟨tau, htau, hcross⟩ := finite_positive_lower_bound cross
    (fun un => ‖(F.nodeEquiv un.1).1 ^ 2 - Z.gamma un.2 ^ 2‖)
    (fun un hun => norm_pos_iff.mpr (sub_ne_zero.mpr
      (node_sq_ne_exception F R sigma un.1 un.2 (Finset.mem_product.mp hun).2)))
  refine ⟨R, sigma, tau, hR, hsigma, htau, hz, ?_, ?_⟩
  · intro u v huv
    exact hgap (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩)
  · intro u n hn
    exact hcross (u, n) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hn⟩)

/-- Choose all geometry first; only the cutoff and budget arithmetic remain
as premises of the full sparse negative certificate. -/
theorem exists_arithmetic_sparse_negative_certificate
    [DecidableEq ι]
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ R sigma tau : ℝ, 0 ≤ R ∧ 0 < sigma ∧ 0 < tau ∧
      ∀ (T : ℕ), 5 ≤ T →
      (T : ℝ) + 1 ≤ quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma →
      ∀ (c den p q : ℕ), 0 < den → 0 < p → 0 < q → p < 4 * q →
      (let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
        (sparsePacketExceptions F R sigma).card R
        (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
       (Fintype.card ι : ℝ) * (3 * (J 0 + J 2)) ^ 2 *
         (rationalFourthMomentTail T : ℝ) ≤ (c : ℝ) / (den : ℝ)) →
      ∃ P : OrbitBurnolPacket F, ∀ N : ℕ, rationalQuarterDepth c den p q ≤ N →
        (-fullWeilGram Z (burnolBasis F P N)).PosDef ∧
        RHLinalg.negIndex (fullWeilGram_isHermitian Z (burnolBasis F P N)) = Fintype.card ι ∧
        ∀ a : ι → ℂ,
          tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
            Icc (-(((N : ℝ) + 2) * quantitativeSeedRadius R))
              (((N : ℝ) + 2) * quantitativeSeedRadius R) ∧
          (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
            -(4 - (p : ℝ) / (q : ℝ)) * finiteComplexEnergy a := by
  classical
  obtain ⟨R, sigma, tau, hR, hsigma, htau, hz, hgap, hcross⟩ :=
    exists_frame_separation_parameters F
  refine ⟨R, sigma, tau, hR, hsigma, htau, ?_⟩
  intro T hT hcut c den p q hden hp hq hpq hround
  exact finite_data_sparse_negative_certificate F R sigma tau hR hsigma htau
    hz hgap hcross T hT hcut c den p q hden hp hq hpq hround

#print axioms exists_frame_separation_parameters
#print axioms exists_arithmetic_sparse_negative_certificate

end D5.S3.Weil.BurnolGram.FrameSeparationParameters
end
