/- GID: D5/S3/Weil/BurnolGram/InstantiatedSparseCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/BurnolGram/InstantiatedSparseCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Instantiate the sparse negative Weil certificate from a supplied frame with an admissible cutoff, finite geometric witnesses, an integer budget, and explicit depth, support and margin. -/

import D5.S3.Weil.BurnolGram.FrameSeparationParameters

/-!
# Instantiated quantitative sparse negative certificates

`WeilFullGramInertia.exists_actual_full_weil_gram_with_exact_negative_index`
already gives qualitative existence from only a supplied frame, including
injective synthesis, positivity of the negated actual full Gram and exact
negative index, with no remainder or arithmetic hypothesis. The result here
adds the quantitative endpoint: a specified depth, support radius and margin,
with the cutoff and budget premises discharged rather than left conditional.

Fix `R = max 5 (sum of node norms)` first, then choose the nodal gap `sigma`,
form `sparsePacketExceptions F R sigma`, and only then choose its gap `tau`.
Nonnegative interpolation jet budgets give `U >= R + 1 >= 6`, so `T = 5`
is admissible. A natural upper bound of the real budget supplies `c`;
`den = p = q = 1` gives margin `3` at every depth at least
`rationalQuarterDepth c 1 1 1`. The geometric bounds are retained explicitly.

This does not produce a frame. `FiniteEvenWeilOrbitFrame` requires `offLine`
for each indexed orbit: producing a nonempty frame would supply an actual
off-critical-line zero and would itself be an RH counterexample. Everything
here is conditional on a supplied frame; the index type may also be empty.

Finite existence is not numerical certification. The sparse coefficient bound
grows like `(1 + U²)^{e}` and the derivative bound grows with `d + e`;
tiny separation or many exceptions make these enormous. The statement asserts
existence, not a usable size. The zero enumeration is chosen classically;
there is no executable enumeration with certified rational enclosures here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.BurnolGram.InstantiatedSparseCertificate

open Set MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.InterpolationJets.QuantitativeEvenInterpolationJets
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

/-- A supplied frame yields a sparse packet with proved geometry, cutoff and
integer budget, hence explicit depth, support and quadratic margin three. -/
theorem exists_instantiated_sparse_negative_certificate
    {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ (R sigma tau : ℝ) (c : ℕ) (P : OrbitBurnolPacket F),
      5 ≤ R ∧ 0 < sigma ∧ 0 < tau ∧
      (∀ u : Sum ι ι, ‖(F.nodeEquiv u).1‖ ≤ R) ∧
      (∀ u v : Sum ι ι, u ≠ v →
        sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖) ∧
      (∀ u : Sum ι ι, ∀ n ∈ sparsePacketExceptions F R sigma,
        tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖) ∧
      ((5 : ℝ) + 1 ≤ quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) ∧
      (let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
        (sparsePacketExceptions F R sigma).card R
        (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
       (Fintype.card ι : ℝ) * (3 * (J 0 + J 2)) ^ 2 *
         (rationalFourthMomentTail 5 : ℝ) ≤ (c : ℝ)) ∧
      ∀ N : ℕ, rationalQuarterDepth c 1 1 1 ≤ N →
        (-fullWeilGram Z (burnolBasis F P N)).PosDef ∧
        RHLinalg.negIndex (fullWeilGram_isHermitian Z (burnolBasis F P N)) = Fintype.card ι ∧
        ∀ a : ι → ℂ,
          tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
            Icc (-(((N : ℝ) + 2) * quantitativeSeedRadius R))
              (((N : ℝ) + 2) * quantitativeSeedRadius R) ∧
          (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
            -3 * finiteComplexEnergy a := by
  classical
  let R : ℝ := max 5 (∑ u : Sum ι ι, ‖(F.nodeEquiv u).1‖)
  have hR5 : 5 ≤ R := le_max_left _ _
  have hR : 0 ≤ R := le_trans (by norm_num) hR5
  have hz (u : Sum ι ι) : ‖(F.nodeEquiv u).1‖ ≤ R :=
    (Finset.single_le_sum (fun v _ => norm_nonneg (F.nodeEquiv v).1)
      (Finset.mem_univ u)).trans (le_max_right _ _)
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
  have hgapAll (u v : Sum ι ι) (huv : u ≠ v) :
      sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖ :=
    hgap (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩)
  have hcrossAll (u : Sum ι ι) (n : ℕ) (hn : n ∈ sparsePacketExceptions F R sigma) :
      tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖ :=
    hcross (u, n) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hn⟩)
  have hjet (s : ℕ) :
      0 ≤ interpolationJetBudget (Fintype.card (Sum ι ι)) R sigma 1 s := by
    unfold interpolationJetBudget interpolationCoefficientBudget interpolationJetScale
    positivity
  have hcut : (5 : ℝ) + 1 ≤
      quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma := by
    unfold quantitativePeakRadius
    linarith [hjet 0, hjet 2]
  let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
    (sparsePacketExceptions F R sigma).card R
    (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
  obtain ⟨c, hc⟩ := exists_nat_ge
    ((Fintype.card ι : ℝ) * (3 * (J 0 + J 2)) ^ 2 * (rationalFourthMomentTail 5 : ℝ))
  obtain ⟨P, hP⟩ := finite_data_sparse_negative_certificate
    F R sigma tau hR hsigma htau hz hgapAll hcrossAll
    5 (by norm_num) hcut c 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [Nat.cast_one, div_one] using hc)
  refine ⟨R, sigma, tau, c, P, hR5, hsigma, htau, hz, hgapAll, hcrossAll, hcut, hc, ?_⟩
  intro N hN
  simpa only [Nat.cast_one, div_one, show (4 - 1 : ℝ) = 3 by norm_num] using hP N hN

#print axioms exists_instantiated_sparse_negative_certificate

end D5.S3.Weil.BurnolGram.InstantiatedSparseCertificate
end
