/- GID: D5/S3/Weil/ZetaBridge/SparseBurnolPacketJets
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/SparseBurnolPacketJets
   mirror-E: none(waiver:constructed-quantitative-packet)
   anchors: []
   digest: Construct an actual Burnol packet in one target-controlled support window with an explicit peak cutoff and sparse killer jet budgets. -/

import D5.S3.Weil.TestFunctions.SparseEvenInterpolationJets
import D5.S3.Weil.ZetaBridge.QuantitativeFiniteWeilPacket
import D5.S3.Weil.ZetaBridge.WeilBurnolCauchyTailBudget

/-!
# Quantitative packet construction without a circular cutoff

First construct the peak using only the target nodes and its explicit jets.
Those jets determine a finite spectral cutoff. Only then construct the killers,
using the finite exceptional set and the sparse interpolation theorem. The
killer smoothing order can depend on the exception count; the already chosen
peak and its cutoff cannot. Both supports have radius 1/(4(R+1)).

The inputs are certified finite target radii, target-target squared gaps, and
target-to-exception squared gaps. There is no supplied peak, killer, derivative
bound, or eventual-smallness threshold. No mutual exceptional gap is needed.
The independent scalar zero-count tail estimate is outside this finite stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.SparseBurnolPacketJets

open D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets

open D5.S3.Weil.ZetaBridge.QuantitativeFiniteWeilPacket

noncomputable section
open Set MeasureTheory Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.SparseEvenInterpolationJets
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open D5.S3.Weil.ZetaBridge.WeilBurnolCauchyTailBudget
open D5.S3.Weil.ZetaBridge.BurnolRationalDepthBudget
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exception-only indices in the specified spectral window. Target indices
are removed before the annihilator is formed. -/
def sparsePacketExceptions (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma : ℝ) : Finset ℕ :=
  Z.symmetricIndices (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) \
    frameTargetIndices F

/-- Construct all actual packet data with explicit support, cutoff and jet
budgets. Quantitative isolation is required only between targets and exceptions.
The peak is independent of the later killer smoothing order. -/
theorem exists_sparse_burnol_packet_with_jets
    (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma tau : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hz : ∀ u : Sum ι ι, ‖(F.nodeEquiv u).1‖ ≤ R)
    (hgap : ∀ u v : Sum ι ι, u ≠ v →
      sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖)
    (hcross : ∀ u : Sum ι ι, ∀ n ∈ sparsePacketExceptions F R sigma,
      tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖) :
    ∃ P : OrbitBurnolPacket F,
      P.exceptional =
        Z.symmetricIndices (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) ∪
          frameTargetIndices F ∧
      tsupport (P.peak : ℝ → ℂ) ⊆
        Icc (-quantitativeSeedRadius R) (quantitativeSeedRadius R) ∧
      (∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆
        Icc (-quantitativeSeedRadius R) (quantitativeSeedRadius R)) ∧
      (∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (P.peak : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (Fintype.card (Sum ι ι)) R sigma 1 s) ∧
      ∀ i, ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (P.killer i : ℝ → ℂ)) x‖) ≤
          sparseJetBudget (Fintype.card (Sum ι ι))
            (sparsePacketExceptions F R sigma).card R
            (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s := by
  classical
  let d := Fintype.card (Sum ι ι)
  let U := quantitativePeakRadius d R sigma
  let O := frameTargetIndices F
  let E0 := sparsePacketExceptions F R sigma
  let E := Z.symmetricIndices U ∪ O
  let z : Sum ι ι → ℂ := fun u => (F.nodeEquiv u).1
  obtain ⟨b, hb, hbs, hbjets⟩ := exists_even_interpolant_with_explicit_jets
    z (fun _ => 1) R sigma 1 hR hsigma (by norm_num) hz (by simp) hgap
  have hh : 0 < quantitativeSeedRadius R := quantitativeSeedRadius_pos R hR
  have hh1 : quantitativeSeedRadius R ≤ 1 := by
    unfold quantitativeSeedRadius
    apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
    nlinarith
  have hbs1 : tsupport (b : ℝ → ℂ) ⊆ Icc (-1) 1 := by
    intro x hx
    have hs := hbs hx
    exact ⟨(neg_le_neg hh1).trans hs.1, hs.2.trans hh1⟩
  have hJ0 : 0 ≤ interpolationJetBudget d R sigma 1 0 :=
    (integral_nonneg fun x : ℝ => norm_nonneg (((deriv^[0]) (b : ℝ → ℂ)) x)).trans
      (hbjets 0 (by omega))
  have hJ2 : 0 ≤ interpolationJetBudget d R sigma 1 2 :=
    (integral_nonneg fun x : ℝ => norm_nonneg (((deriv^[2]) (b : ℝ → ℂ)) x)).trans
      (hbjets 2 le_rfl)
  have hU : 0 ≤ U := by dsimp [U, quantitativePeakRadius]; positivity
  have hcut : 2 * (3 * (interpolationJetBudget d R sigma 1 0 +
      interpolationJetBudget d R sigma 1 2)) + 1 ≤ U := by
    dsimp [U, quantitativePeakRadius]
    linarith
  have htail := peak_tail_of_two_jet_budget Z b
    (interpolationJetBudget d R sigma 1 0) (interpolationJetBudget d R sigma 1 2)
    U hbs1 (hbjets 0 (by omega)) (hbjets 2 le_rfl) hcut
  let W := {n : ℕ // n ∈ E0}
  let w : W → ℂ := fun n => Z.gamma n.1
  have hw : ∀ n : W, ‖w n‖ ≤ U := by
    intro n
    have hn : n.1 ∈ Z.symmetricIndices U := (Finset.mem_sdiff.mp n.2).1
    exact (Z.mem_symmetricIndices).mp hn
  let v : ι → Sum ι ι → ℂ := fun i u =>
    match u with
    | Sum.inl j => frameDelta i j
    | Sum.inr j => -frameDelta i j
  have hv (i : ι) : ∀ u, ‖v i u‖ ≤ (1 : ℝ) := by
    intro u
    cases u with
    | inl j => by_cases hji : j = i <;> simp [v, frameDelta, hji]
    | inr j => by_cases hji : j = i <;> simp [v, frameDelta, hji]
  have hkexists (i : ι) := exists_sparse_even_interpolant_with_explicit_jets
    z (v i) w R U sigma tau 1 hR hU hsigma htau (by norm_num)
    hz hw (hv i) hgap (fun u n => hcross u n.1 n.2)
  choose k hkvals hkzero hks hkjet using hkexists
  let P : OrbitBurnolPacket F :=
    { peak := b
      killer := k
      exceptional := E
      target_subset := Finset.subset_union_right
      peak_values := by
        intro i
        constructor
        · simpa only [z, F.plusNode i] using hb (Sum.inl i)
        · simpa only [z, F.minusNode i] using hb (Sum.inr i)
      killer_values := by
        intro i j
        constructor
        · simpa only [z, v, F.plusNode j] using hkvals i (Sum.inl j)
        · simpa only [z, v, F.minusNode j] using hkvals i (Sum.inr j)
      kills_exception := by
        intro i n hn hno
        have hnU : n ∈ Z.symmetricIndices U :=
          (Finset.mem_union.mp hn).resolve_right hno
        have hn0 : n ∈ E0 := Finset.mem_sdiff.mpr ⟨hnU, hno⟩
        exact hkzero i ⟨n, hn0⟩
      peak_tail := by
        intro n hn
        apply htail n
        intro hnU
        exact hn (Finset.mem_union_left O hnU) }
  refine ⟨P, rfl, hbs, hks, hbjets, ?_⟩
  intro i s hs
  have h := hkjet i s hs
  have hW : Fintype.card W = E0.card := Fintype.card_of_subtype E0 (fun _ => Iff.rfl)
  simpa only [hW] using h

/-- Compose the constructed finite packet with the scalar spectral certificate
and the exact integer depth selector. No packet or derivative bound is supplied.
Only actual finite geometry and the independent scalar tail remain as inputs. -/
theorem sparse_packet_computed_support_margin_and_inertia
    (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma tau Theta : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hz : ∀ u : Sum ι ι, ‖(F.nodeEquiv u).1‖ ≤ R)
    (hgap : ∀ u v : Sum ι ι, u ≠ v →
      sigma ≤ ‖(F.nodeEquiv u).1 ^ 2 - (F.nodeEquiv v).1 ^ 2‖)
    (hcross : ∀ u : Sum ι ι, ∀ n ∈ sparsePacketExceptions F R sigma,
      tau ≤ ‖(F.nodeEquiv u).1 ^ 2 - Z.gamma n ^ 2‖)
    (hspectral : Summable (fun n : {n : ℕ // n ∉
        Z.symmetricIndices (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) ∪
          frameTargetIndices F} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉
        Z.symmetricIndices (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) ∪
          frameTargetIndices F}, fourthMomentSummand Z n.1) ≤ Theta)
    (c den p q : ℕ) (hden : 0 < den) (hp : 0 < p) (hq : 0 < q) (hpq : p < 4 * q)
    (hround :
      let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
        (sparsePacketExceptions F R sigma).card R
        (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
      (Fintype.card ι : ℝ) * (3 * (J 0 + J 2)) ^ 2 * Theta ≤ (c : ℝ) / (den : ℝ)) :
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
  obtain ⟨P, hPE, hps, hks, _, hkj⟩ :=
    exists_sparse_burnol_packet_with_jets F R sigma tau hR hsigma htau hz hgap hcross
  let J := fun s => sparseJetBudget (Fintype.card (Sum ι ι))
    (sparsePacketExceptions F R sigma).card R
    (quantitativePeakRadius (Fintype.card (Sum ι ι)) R sigma) sigma tau 1 s
  have hradius : quantitativeSeedRadius R ≤ 1 := by
    unfold quantitativeSeedRadius
    apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
    nlinarith
  have hks1 (i : ι) : tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1 := by
    intro x hx
    have h := hks i hx
    exact ⟨(neg_le_neg hradius).trans h.1, h.2.trans hradius⟩
  have hsp : Summable (fun n : {n : ℕ // n ∉ P.exceptional} => fourthMomentSummand Z n.1) := by
    simpa only [hPE] using hspectral
  have htl : (∑' n : {n : ℕ // n ∉ P.exceptional}, fourthMomentSummand Z n.1) ≤ Theta := by
    simpa only [hPE] using htail
  have h0 (i : ι) : (∫ x : ℝ, ‖P.killer i x‖) ≤ J 0 := hkj i 0 (by omega)
  have h2 (i : ι) : (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ J 2 := hkj i 2 le_rfl
  have hc : (∑ _i : ι, (3 * (J 0 + J 2)) ^ 2) * Theta ≤ (c : ℝ) / (den : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hround
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdelta : (p : ℝ) / (q : ℝ) < 4 := by
    apply (div_lt_iff₀ hqR).2
    exact_mod_cast hpq
  refine ⟨P, ?_⟩
  intro N hN
  have hbound := cauchy_budget_full_gram_margin F P (fun _ => J 0) (fun _ => J 2)
    Theta hks1 h0 h2 hsp htl c den p q hden hp hq hc N hN
  have hnegative : ∀ a : ι → ℂ, a ≠ 0 →
      (zeroSum Z (convolutionSquare (finiteWeilLinearCombination a (burnolBasis F P N)))
        (symmetricConvergent_of_zeroData Z
          (convolutionSquare (finiteWeilLinearCombination a (burnolBasis F P N))))).re < 0 := by
    intro a ha
    have h := hbound a
    rw [fullWeilGram_quadratic] at h
    exact lt_of_le_of_lt h (mul_neg_of_neg_of_pos
      (neg_lt_zero.mpr (sub_pos.mpr hdelta)) (finiteComplexEnergy_pos ha))
  refine ⟨neg_fullWeilGram_posDef_of_strictNegative Z (burnolBasis F P N) hnegative,
    fullWeilGram_negIndex_of_strictNegative Z (burnolBasis F P N) hnegative, ?_⟩
  intro a
  refine ⟨?_, hbound a⟩
  have hs := burnolSynthesis_tsupport_subset F P (quantitativeSeedRadius R)
    (quantitativeSeedRadius R) hps hks N a
  simpa only [show ((N : ℝ) + 1) * quantitativeSeedRadius R + quantitativeSeedRadius R =
    ((N : ℝ) + 2) * quantitativeSeedRadius R by ring] using hs

end

/-- Rational arithmetic for the same staged peak cutoff. -/
def rationalSparsePacketCutoff (d : ℕ) (R sigma : ℚ) : ℚ :=
  R + 6 * (rationalInterpolationJetBudget d R sigma 1 0 +
    rationalInterpolationJetBudget d R sigma 1 2) + 1

/-- Exact cast agreement for the cutoff, with no transcendental operation. -/
theorem rationalSparsePacketCutoff_cast (d : ℕ) (R sigma : ℚ) :
    (rationalSparsePacketCutoff d R sigma : ℝ) = quantitativePeakRadius d R sigma := by
  unfold rationalSparsePacketCutoff quantitativePeakRadius
  push_cast
  rw [rationalInterpolationJetBudget_cast, rationalInterpolationJetBudget_cast]

#print axioms exists_sparse_burnol_packet_with_jets
#print axioms rationalSparsePacketCutoff_cast
#print axioms sparse_packet_computed_support_margin_and_inertia

end D5.S3.Weil.ZetaBridge.SparseBurnolPacketJets
