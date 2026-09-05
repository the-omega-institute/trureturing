/- GID: D5/S3/Weil/ZetaBridge/WeilBurnolSupportBudget
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilBurnolSupportBudget
   mirror-E: none(waiver:actual-test-support-budget)
   anchors: []
   digest: Derive additive support radii for convolution, common radii for finite Weil families, and a coefficient-uniform linear support budget for Burnol localization. -/

import D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Support budget of the actual multi-orbit Burnol family

The peak and the finitely many killers have common compact support bounds.
An (N+1)-fold peak convolution followed by a killer has radius at most
(N+1) B + K. The same radius works for every coefficient vector at that
fixed depth. No radius uniform over all depths or all frames is asserted.

The convolution proof reuses the Mathlib support containment used by
ConvolutionPowerAmplification.convolutionSuccPower_tsupport_subset, allowing
arbitrary closed-interval radii instead of only a radius-one open interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget

open Set MeasureTheory
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Fourier.ConvolutionPowerAmplification
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open scoped BigOperators Convolution Pointwise

/-- Closed support radii add under actual Weil convolution. -/
theorem convolve_tsupport_subset_Icc
    (f g : WeilTestFunction) (B K : ℝ)
    (hf : tsupport (f : ℝ → ℂ) ⊆ Icc (-B) B)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Icc (-K) K) :
    tsupport (convolve f g : ℝ → ℂ) ⊆ Icc (-(B + K)) (B + K) := by
  have hclosed : IsClosed (tsupport (f : ℝ → ℂ) + tsupport (g : ℝ → ℂ)) :=
    (f.hasCompactSupport.isCompact.add g.hasCompactSupport.isCompact).isClosed
  refine (closure_minimal ((support_convolution_subset complexMul).trans ?_)
    hclosed).trans ?_
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, subset_tsupport _ ha, b, subset_tsupport _ hb, rfl⟩
  · rintro x ⟨a, ha, b, hb, rfl⟩
    have ha' := hf ha
    have hb' := hg hb
    simp only [mem_Icc] at ha' hb' ⊢
    constructor <;> linarith

/-- Successor convolution powers have radius at most (N+1) times the input radius. -/
theorem convolutionSuccPower_tsupport_subset_Icc
    (g : WeilTestFunction) (B : ℝ)
    (hg : tsupport (g : ℝ → ℂ) ⊆ Icc (-B) B) (N : ℕ) :
    tsupport (convolutionSuccPower g N : ℝ → ℂ) ⊆
      Icc (-(((N : ℝ) + 1) * B)) (((N : ℝ) + 1) * B) := by
  induction N with
  | zero => simpa [convolutionSuccPower] using hg
  | succ N ih =>
      have h := convolve_tsupport_subset_Icc (convolutionSuccPower g N) g
        (((N : ℝ) + 1) * B) B ih hg
      simpa only [convolutionSuccPower, Nat.cast_add, Nat.cast_one,
        show ((N : ℝ) + 1 + 1) * B = ((N : ℝ) + 1) * B + B by ring] using h

/-- Finite linear synthesis preserves a support window shared by its inputs. -/
theorem finiteWeilLinearCombination_tsupport_subset_Icc
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (g : ι → WeilTestFunction)
    (L : ℝ) (hg : ∀ i, tsupport (g i : ℝ → ℂ) ⊆ Icc (-L) L) :
    tsupport (finiteWeilLinearCombination a g : ℝ → ℂ) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra houtside
  have hzero : ∀ i, g i x = 0 := by
    intro i
    by_contra hi
    exact houtside (hg i (subset_tsupport (g i : ℝ → ℂ) hi))
  have hsum : finiteWeilLinearCombination a g x = 0 := by
    change (∑ i, a i * g i x) = 0
    simp [hzero]
  exact hx hsum

/-- A finite family of actual Weil tests admits a positive common support radius. -/
theorem finiteWeilFamily_common_support_radius
    {ι : Type*} [Fintype ι] (g : ι → WeilTestFunction) :
    ∃ L : ℝ, 0 < L ∧ ∀ i, tsupport (g i : ℝ → ℂ) ⊆ Icc (-L) L := by
  classical
  have hex : ∀ i, ∃ r : ℝ, 0 < r ∧
      tsupport (g i : ℝ → ℂ) ⊆ Icc (-r) r := by
    intro i
    obtain ⟨r, hr, hsub⟩ :=
      (g i).hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : ℝ)
    refine ⟨r, hr, ?_⟩
    intro x hx
    have hd : dist x (0 : ℝ) ≤ r := hsub hx
    have habs : |x| ≤ r := by simpa only [Real.dist_eq, sub_zero] using hd
    exact abs_le.mp habs
  choose r hr hsupport using hex
  let L : ℝ := 1 + ∑ i, r i
  have hsum : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => (hr i).le
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨L, hL, ?_⟩
  intro i x hx
  have hi : r i ≤ ∑ j, r j :=
    Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
  have hiL : r i ≤ L := by dsimp [L]; linarith
  have hx' := hsupport i hx
  exact ⟨(neg_le_neg hiL).trans hx'.1, hx'.2.trans hiL⟩

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FiniteEvenWeilOrbitFrame Z ι)

/-- One linear radius budget controls all coefficients of the localized family. -/
theorem burnolSynthesis_tsupport_subset
    (P : OrbitBurnolPacket F) (B K : ℝ)
    (hpeak : tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-B) B)
    (hkill : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-K) K)
    (N : ℕ) (a : ι → ℂ) :
    tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
      Icc (-(((N : ℝ) + 1) * B + K)) (((N : ℝ) + 1) * B + K) := by
  apply finiteWeilLinearCombination_tsupport_subset_Icc
  intro i
  exact convolve_tsupport_subset_Icc (convolutionSuccPower P.peak N) (P.killer i)
    (((N : ℝ) + 1) * B) K
    (convolutionSuccPower_tsupport_subset_Icc P.peak B hpeak N) (hkill i)

/-- The support constants are obtained from the actual packet, not postulated. -/
theorem exists_burnol_linear_support_budget (P : OrbitBurnolPacket F) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-B) B ∧
      (∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-K) K) ∧
      ∀ N : ℕ, ∀ a : ι → ℂ,
        tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
          Icc (-(((N : ℝ) + 1) * B + K)) (((N : ℝ) + 1) * B + K) := by
  obtain ⟨B, hB, hpeak⟩ :=
    finiteWeilFamily_common_support_radius (fun _ : Unit => P.peak)
  obtain ⟨K, hK, hkill⟩ := finiteWeilFamily_common_support_radius P.killer
  exact ⟨B, K, hB, hK, hpeak (), hkill,
    burnolSynthesis_tsupport_subset F P B K (hpeak ()) hkill⟩

#print axioms convolve_tsupport_subset_Icc
#print axioms finiteWeilFamily_common_support_radius
#print axioms burnolSynthesis_tsupport_subset
#print axioms exists_burnol_linear_support_budget

end D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
