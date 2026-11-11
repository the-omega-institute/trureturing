/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square raw correlation errors control total errors over finite shift sets. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ArithmeticTransferDefs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Chan's mean-square weakening applies to raw correlations on a dyadic interval.
The estimates for finite shift sets are used in overlapping mixed-moment sums. -/

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- The unweighted raw correlation error for a finite set of shifts. -/
def correlationError (SS : Finset ℕ → ℝ) (y : ℝ) (D : Finset ℕ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ d ∈ D, ArithmeticFunction.vonMangoldt (n + d)) - y * SS D

/-- Uniform mean-square errors for one to q distinct positive shifts. Only real cutoffs
in the closed dyadic interval are required. -/
def MeanSquareHL (q : ℕ) (SS : Finset ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ r : ℕ, 1 ≤ r → r ≤ q → ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ M * N ^ β →
        ∀ y : ℝ, N ≤ y → y ≤ 2 * N →
          (∑ d ∈ (Fintype.piFinset (fun _ : Fin r => Finset.Ioc 0 K)).filter
              Function.Injective,
            |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
                ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
                y * SS (Finset.univ.image d)| ^ 2) ≤
            C * N ^ (1 + 2 * ε) * (K : ℝ) ^ r

/-- The four-point instance of the order-indexed mean-square hypothesis. -/
abbrev MeanSquareHL4 (SS : Finset ℕ → ℝ) (β : ℝ) : Prop := MeanSquareHL 4 SS β

private lemma ordered_error_eq (SS : Finset ℕ → ℝ) (y : ℝ) {r : ℕ}
    (d : Fin r → ℕ) (hd : Function.Injective d) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
        y * SS (Finset.univ.image d) = correlationError SS y (Finset.univ.image d) := by
  unfold correlationError
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (Finset.prod_image (f := fun e => ArithmeticFunction.vonMangoldt (n + e))
    hd.injOn).symm

private lemma powersetCard_subset_tuple_image (S : Finset ℕ) (r : ℕ) :
    S.powersetCard r ⊆
      ((Fintype.piFinset (fun _ : Fin r => S)).filter Function.Injective).image
        (fun d => Finset.univ.image d) := by
  classical
  intro D hD
  obtain ⟨hDS, hcard⟩ := Finset.mem_powersetCard.mp hD
  subst r
  let e := D.equivFin.symm
  let d : Fin D.card → ℕ := fun i => (e i).val
  have hinj : Function.Injective d := Subtype.val_injective.comp e.injective
  have him : Finset.univ.image d = D := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact (e i).property
    · intro hv
      exact Finset.mem_image.mpr ⟨D.equivFin ⟨v, hv⟩, Finset.mem_univ _, by simp [d, e]⟩
  exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr
    ⟨Fintype.mem_piFinset.mpr (fun i => hDS (e i).property), hinj⟩, him⟩

/-- Cauchy–Schwarz converts the mean-square hypothesis into a total absolute error over
all unordered shift sets of a fixed size. The constant is uniform in the box and the cutoff. -/
theorem meanSquare_correlation_l1 {q : ℕ} (SS : Finset ℕ → ℝ) (β : ℝ)
    (hMS : MeanSquareHL q SS β) (M ε : ℝ) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ N : ℝ in atTop,
      2 ≤ N ∧ ∀ r : ℕ, 1 ≤ r → r ≤ q →
        ∀ K : ℕ, 1 ≤ K → (K : ℝ) ≤ M * N ^ β →
          ∀ y : ℝ, N ≤ y → y ≤ 2 * N →
            (∑ D ∈ (Finset.Ioc 0 K).powersetCard r, |correlationError SS y D|) ≤
              A * N ^ (1 / 2 + ε) * (K : ℝ) ^ r := by
  classical
  obtain ⟨C, hC, N₀, hMS⟩ := hMS ε hε M hM
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 2)] with N hN
  have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hN
  have hN0 : 0 < N := by linarith
  refine ⟨hN2, ?_⟩
  intro r hr hr4 K hK hKN y hy hyN
  let T := (Fintype.piFinset (fun _ : Fin r => Finset.Ioc 0 K)).filter
    Function.Injective
  let S := (Finset.Ioc 0 K).powersetCard r
  have hsub : S ⊆ T.image (fun d => Finset.univ.image d) :=
    powersetCard_subset_tuple_image _ _
  have hcountT : (T.card : ℝ) ≤ (K : ℝ) ^ r := by
    calc
      _ ≤ ((Fintype.piFinset (fun _ : Fin r => Finset.Ioc 0 K)).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
      _ = _ := by simp [Fintype.card_piFinset]
  have hcount : (S.card : ℝ) ≤ (K : ℝ) ^ r := by
    apply le_trans (b := (T.card : ℝ)) _ hcountT
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have herrors : (∑ D ∈ S, |correlationError SS y D| ^ 2) ≤
      C * N ^ (1 + 2 * ε) * (K : ℝ) ^ r := by
    calc
      _ ≤ ∑ D ∈ T.image (fun d => Finset.univ.image d),
          |correlationError SS y D| ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ d ∈ T, |correlationError SS y (Finset.univ.image d)| ^ 2 :=
        Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
      _ = ∑ d ∈ T,
          |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
              ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
              y * SS (Finset.univ.image d)| ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [ordered_error_eq SS y d (Finset.mem_filter.mp hd).2]
      _ ≤ _ := hMS N ((le_max_left N₀ 2).trans hN) r hr hr4 K hK hKN y hy hyN
  have hpow : (N ^ (1 / 2 + ε)) ^ 2 = N ^ (1 + 2 * ε) := by
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    norm_num
    ring
  have hsquare : (∑ D ∈ S, |correlationError SS y D|) ^ 2 ≤
      (Real.sqrt C * N ^ (1 / 2 + ε) * (K : ℝ) ^ r) ^ 2 := by
    calc
      _ ≤ (S.card : ℝ) * ∑ D ∈ S, |correlationError SS y D| ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
          (fun D => |correlationError SS y D|)
      _ ≤ (K : ℝ) ^ r * (C * N ^ (1 + 2 * ε) * (K : ℝ) ^ r) :=
        mul_le_mul hcount herrors (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (by positivity)
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, hpow]; ring
  have hright : 0 ≤ Real.sqrt C * N ^ (1 / 2 + ε) * (K : ℝ) ^ r := by positivity
  change (∑ D ∈ S, |correlationError SS y D|) ≤ _
  nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
