/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedInverseCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-index finite numerator coefficients of the balanced native inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedInverseKernel
import Batteries.Tactic.OpenPrivate

/-! The finite coefficient convolution is reindexed only after both cumulative
guards have been proved. Every signed numerator coordinate remains in scope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldBalancedInverseCoefficients
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldBalancedNativeInverse ThreeFieldBalancedLaurentFiber
open ThreeFieldBalancedInverseKernel
open ThreeFieldFinalCone
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

open private W shiftedChart from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction
open private coeff_mul_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients

variable {R : Type*} [CommRing R] [Algebra ℂ R]

private def box (n m : ℕ) : Finset BalancedIndex :=
  (Finset.range (n + 1)).product
    ((Finset.range (m + 1)).product (Finset.range (n + 1)))

private def weight (k A r j l : ℕ) : ℂ :=
  integerBinomial (-(k : ℤ)) r * integerBinomial (-(A : ℤ)) l *
    (-1 : ℂ) ^ j * integerBinomial (-((2 * k + r : ℕ) : ℤ)) j

private theorem native_inverse_box (G : MvPowerSeries (Fin 3) R)
    (k A n m t : ℕ) :
    MvPowerSeries.coeff (index3 n m t)
      ((↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) * G) =
    ∑ i ∈ (box n m).filter (fun i => i.1 + i.2.2 ≤ n ∧ i.1 + i.2.1 + i.2.2 ≤ m),
      weight k A i.1 i.2.1 i.2.2 •
        MvPowerSeries.coeff (index3 (n - i.1 - i.2.2) (m - i.1 - i.2.1 - i.2.2) t) G := by
  classical
  let term (u v l : ℕ) : R :=
    weight k A (u - l) (v - u) l •
      MvPowerSeries.coeff (index3 (n - u) (m - v) t) G
  have row (u v : ℕ) :
      (∑ w ∈ Finset.range (t + 1),
        MvPowerSeries.coeff (index3 u v w)
          (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) *
            MvPowerSeries.coeff (index3 (n - u) (m - v) (t - w)) G) =
      ∑ l ∈ Finset.range (u + 1), if u ≤ v then term u v l else 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [balanced_inverse_coeff]
      simp only [Nat.sub_zero, Finset.sum_mul, ite_true]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : u ≤ v
      · rw [ite_eq_left h, ite_eq_left h]
        simp only [term, weight, smul_mul_assoc, one_mul]
      · simp [h]
    · intro w hw hne
      rw [balanced_inverse_coeff]
      simp [hne]
    · simp
  have first :
      MvPowerSeries.coeff (index3 n m t)
        ((↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) * G) =
      ∑ i ∈ (box n m).filter (fun i => i.2.2 ≤ i.1 ∧ i.1 ≤ i.2.1),
        term i.1 i.2.1 i.2.2 := by
    rw [coeff_mul_box]
    simp_rw [row]
    simp only [box, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    have hun : u ≤ n := by simpa using Finset.mem_range.mp hu
    apply Finset.sum_congr rfl
    intro v hv
    calc
      _ = ∑ l ∈ Finset.range (u + 1),
          if l ≤ u ∧ u ≤ v then term u v l else 0 := by
        apply Finset.sum_congr rfl
        intro l hl
        have hlu : l ≤ u := by simpa using Finset.mem_range.mp hl
        simp only [hlu, true_and]
      _ = _ := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro l hl hout
        have h : ¬ (l ≤ u ∧ u ≤ v) := by
          simp only [Finset.mem_range, not_lt] at hout
          omega
        rw [ite_eq_right h]
  rw [first]
  refine Finset.sum_bij
    (fun i _ => (i.1 - i.2.2, (i.2.1 - i.1, i.2.2))) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [box, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hi ⊢
    omega
  · intro i hi j hj eq
    have e0 := congrArg (fun i : BalancedIndex => i.1) eq
    have e1 := congrArg (fun i : BalancedIndex => i.2.1) eq
    have e2 := congrArg (fun i : BalancedIndex => i.2.2) eq
    simp only [box, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hi hj
    apply Prod.ext
    · dsimp at e0 e2
      omega
    · apply Prod.ext
      · dsimp at e0 e1 e2
        omega
      · exact e2
  · intro i hi
    simp only [box, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hi
    refine ⟨(i.1 + i.2.2, (i.1 + i.2.1 + i.2.2, i.2.2)), ?_, ?_⟩
    · simp only [box, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
      omega
    · apply Prod.ext
      · dsimp
        omega
      · apply Prod.ext
        · dsimp
          omega
        · rfl
  · intro i hi
    simp only [box, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range] at hi
    dsimp only [term]
    apply congrArg (fun v : R => weight k A (i.1 - i.2.2)
      (i.2.1 - i.1) i.2.2 • v)
    apply congrArg (fun d => MvPowerSeries.coeff d G)
    ext c
    fin_cases c <;> simp [index3] <;> omega

private def decode (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) : Exponent 3 :=
  ![(n 0 : ℤ) - k, (n 2 : ℤ) - n 1 - a 0 - a 1 - 2 * k,
    (n 1 : ℤ) - n 0 - a 2]

omit [Algebra ℂ R] in
private theorem numerator_readout (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) (i : BalancedIndex)
    (hi : i.1 + i.2.2 ≤ n 0 ∧ i.1 + i.2.1 + i.2.2 ≤ n 1) :
    MvPowerSeries.coeff (index3 (n 0 - i.1 - i.2.2) (n 1 - i.1 - i.2.1 - i.2.2) (n 2))
      (nativeChart (balancedSwapSeries P)) =
    signedExtend P (balancedInput k a (decode k a n 0) (decode k a n 1) (decode k a n 2) i) := by
  classical
  let e := balancedInput k a (decode k a n 0) (decode k a n 1) (decode k a n 2) i
  have sorted : n 0 - i.1 - i.2.2 ≤ n 1 - i.1 - i.2.1 - i.2.2 ∧
      n 1 - i.1 - i.2.1 - i.2.2 ≤ n 2 ↔ ∀ c, 0 ≤ e c := by
    constructor
    · intro h c
      fin_cases c <;> dsimp [e, balancedInput, decode] <;> omega
    · intro h
      have h1 := h 1
      have h2 := h 2
      dsimp [e, balancedInput, decode] at h1 h2
      omega
  change _ = signedExtend P e
  have chart (r s t : ℕ) :
      MvPowerSeries.coeff (index3 r s t) (nativeChart (balancedSwapSeries P)) =
      if r ≤ s ∧ s ≤ t then
        MvPowerSeries.coeff (index3 r (t - s) (s - r)) P else 0 := by
    simp [MvPowerSeries.coeff_apply, nativeChart, balancedSwapSeries, index3]
  rw [chart]
  by_cases he : ∀ c, 0 ≤ e c
  · rw [ite_eq_left (sorted.mpr he), signedExtend, ite_eq_left he]
    apply congrArg (fun d => MvPowerSeries.coeff d P)
    ext c
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    fin_cases c <;> simp [index3, signedIndex] <;> dsimp [e, balancedInput, decode] at * <;>
      omega
  · rw [ite_eq_right (fun h => he (sorted.mp h)), signedExtend, ite_eq_right he]

theorem raw_balanced_coefficients (P : MvPowerSeries (Fin 3) R)
    (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) :
    rawBalancedCoefficient P k a e = balancedCoefficient P k a (e 0) (e 1) (e 2) := by
  classical
  let w := W (![e 0, e 2, e 1] : Exponent 3) + balancedShift k a
  by_cases hw : ∀ c, 0 ≤ w c
  · let n : Fin 3 → ℕ := fun c => (w c).toNat
    have hn0 : (n 0 : ℤ) = e 0 + k := Int.toNat_of_nonneg (hw 0)
    have hn1 : (n 1 : ℤ) = e 0 + e 2 + k + a 2 :=
      by
        have h := Int.toNat_of_nonneg (hw 1)
        change (n 1 : ℤ) = w 1 at h
        dsimp [w, W, balancedShift] at h
        omega
    have hn2 : (n 2 : ℤ) = e 0 + e 2 + e 1 + a 0 + a 1 + a 2 + 3 * k :=
      by
        have h := Int.toNat_of_nonneg (hw 2)
        change (n 2 : ℤ) = w 2 at h
        dsimp [w, W, balancedShift] at h
        omega
    have de : decode k a n = e := by
      funext c
      fin_cases c <;> dsimp [decode] <;> omega
    have idx : signedIndex w = index3 (n 0) (n 1) (n 2) := by
      ext c
      fin_cases c <;> simp [signedIndex, index3, n]
    change signedExtend _ w = _
    rw [signedExtend, ite_eq_left hw]
    change MvPowerSeries.coeff (signedIndex w) _ = _
    rw [idx]
    change MvPowerSeries.coeff (index3 (n 0) (n 1) (n 2))
      ((↑((balancedUnit R k (a 0))⁻¹) : MvPowerSeries (Fin 3) R) *
        nativeChart (balancedSwapSeries P)) = _
    rw [native_inverse_box (nativeChart (balancedSwapSeries P)) k (a 0) (n 0) (n 1) (n 2),
      Finset.sum_filter]
    have fiber : balancedFiber k a (e 0) (e 1) (e 2) =
        (box (n 0) (n 1)).filter (BalancedAdmissible k a (e 0) (e 1) (e 2)) := by
      ext i
      rw [mem_balancedFiber_iff, Finset.mem_filter]
      constructor
      · intro hi
        obtain ⟨hrl, hj, hrjl, hs, hz, hsz, he⟩ :=
          balanced_bounds k a (e 0) (e 1) (e 2) i hi
        refine ⟨?_, hi⟩
        simp only [box, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
        omega
      · exact And.right
    rw [balancedCoefficient, fiber, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have wt : weight k (a 0) i.1 i.2.1 i.2.2 = balancedWeight k a i := rfl
    by_cases h : i.1 + i.2.2 ≤ n 0 ∧ i.1 + i.2.1 + i.2.2 ≤ n 1
    · rw [ite_eq_left h, numerator_readout P k a n i h, de, wt]
      by_cases ha : BalancedAdmissible k a (e 0) (e 1) (e 2) i
      · rw [ite_eq_left ha]
      · rw [ite_eq_right ha]
        change ¬ (∀ c, 0 ≤ balancedInput k a (e 0) (e 1) (e 2) i c) at ha
        rw [signedExtend, ite_eq_right ha, smul_zero]
    · rw [ite_eq_right h]
      have ha : ¬ BalancedAdmissible k a (e 0) (e 1) (e 2) i := by
        intro ha
        have hb := balanced_bounds k a (e 0) (e 1) (e 2) i ha
        omega
      rw [ite_eq_right ha]
  · change signedExtend _ w = _
    rw [signedExtend, ite_eq_right hw]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hb := balanced_bounds k a (e 0) (e 1) (e 2) i
      ((mem_balancedFiber_iff k a (e 0) (e 1) (e 2) i).mp hi)
    exfalso
    apply hw
    intro c
    fin_cases c <;> dsimp [w, W, balancedShift] <;> omega

end
end D5.S3.VertexAlgebra.ThreeFieldBalancedInverseCoefficients
