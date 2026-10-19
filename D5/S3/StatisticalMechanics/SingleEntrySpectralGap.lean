/- GID: D5/S3/StatisticalMechanics/SingleEntrySpectralGap
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntrySpectralGap
   mirror-E: none(waiver:single-entry-mode-spectrum)
   anchors: []
   utility: none
   digest: Schur elimination identifies the lowest mode-coordinate eigenvalue. -/

import D5.S3.StatisticalMechanics.SingleEntrySecularRoot
import D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork

/-! # The single-entry secular root in free-mode coordinates

The matrix below is the full rank-one extension of the diagonal free-mode
operator. Its coordinates are free product modes, not configurations. Identifying
this matrix with the configuration generator requires the product change of basis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open SingleEntrySecularRoot

/-- Negative generator in free-mode coordinates, with `none` the attached state.
The coordinate functional `∑ S, x (some S)` reads out the empty configuration. -/
def modeNegativeGenerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) :
    Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ
  | none, none => θ
  | none, some _ => -η
  | some S, none => -θ * modeWeight a b S
  | some S, some T => (if S = T then subsetRate a b S else 0) + η * modeWeight a b S

theorem action_none {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ) :
    (modeNegativeGenerator a b η θ *ᵥ x) none =
      θ * x none - η * ∑ S, x (some S) := by
  simp [mulVec, dotProduct, Fintype.sum_option, modeNegativeGenerator,
    ← Finset.mul_sum]
  ring

theorem action_some {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ) (S : Finset ι) :
    (modeNegativeGenerator a b η θ *ᵥ x) (some S) =
      subsetRate a b S * x (some S) +
        modeWeight a b S * (η * (∑ T, x (some T)) - θ * x none) := by
  simp [mulVec, dotProduct, Fintype.sum_option, modeNegativeGenerator,
    add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem denominators {ι : Type*}
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (l : ℝ) (hl : 0 < l) (hupper : ∀ i, l < siteRate a b i) :
    ∀ S : Finset ι, subsetRate a b S - l ≠ 0 := by
  classical
  intro S
  by_cases hS : S = ∅
  · subst S
    simp [subsetRate, ne_of_gt hl]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hsum : siteRate a b i ≤ subsetRate a b S :=
      Finset.single_le_sum (fun j _ => (add_pos (ha j) (hb j)).le) hi
    exact ne_of_gt (by linarith [hupper i])

private theorem secular_full_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ l : ℝ) (hl : l ≠ 0) :
    secular a b η θ l = θ - l -
      η * l * ∑ S : Finset ι, modeWeight a b S / (subsetRate a b S - l) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset ι))]
  simp only [subsetRate, Finset.sum_empty, zero_sub, div_neg]
  unfold secular
  simp only [subsetRate]
  field_simp
  ring

private theorem schur_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ l : ℝ) (hl : l ≠ 0)
    (hpole : ∀ S : Finset ι, subsetRate a b S - l ≠ 0) :
    (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
      modeNegativeGenerator a b η θ *ᵥ x = l • x) ↔
      secular a b η θ l = 0 := by
  rw [secular_full_sum a b η θ l hl]
  constructor
  · rintro ⟨x, hx, he⟩
    have hR := congrFun he none
    rw [action_none] at hR
    simp only [Pi.smul_apply, smul_eq_mul] at hR
    have hS (S : Finset ι) :
        x (some S) = l * modeWeight a b S * x none / (subsetRate a b S - l) := by
      have hs := congrFun he (some S)
      rw [action_some] at hs
      simp only [Pi.smul_apply, smul_eq_mul] at hs
      apply (eq_div_iff (hpole S)).mpr
      nlinarith [congrArg (fun t : ℝ => modeWeight a b S * t) hR]
    have hxR : x none ≠ 0 := by
      intro hz
      apply hx
      funext i
      cases i with
      | none => exact hz
      | some S => simp [hS S, hz]
    have hsum : (∑ S, x (some S)) =
        l * x none * ∑ S, modeWeight a b S / (subsetRate a b S - l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [hS]
      ring
    rw [hsum] at hR
    have hz : (θ - l - η * l *
        ∑ S, modeWeight a b S / (subsetRate a b S - l)) * x none = 0 := by
      nlinarith [hR]
    exact (mul_eq_zero.mp hz).resolve_right hxR
  · intro hF
    let x : Option (Finset ι) → ℝ
      | none => 1
      | some S => l * modeWeight a b S / (subsetRate a b S - l)
    have hsum : (∑ S, x (some S)) =
        l * ∑ S, modeWeight a b S / (subsetRate a b S - l) := by
      simp only [x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have := congrFun hx none
      norm_num [x] at this
    · funext i
      cases i with
      | none =>
        rw [action_none, hsum]
        simp only [x, Pi.smul_apply, smul_eq_mul, mul_one]
        nlinarith [hF]
      | some S =>
        rw [action_some, hsum]
        simp only [x, Pi.smul_apply, smul_eq_mul, mul_one]
        have hrel : η * (l * ∑ T, modeWeight a b T / (subsetRate a b T - l)) - θ = -l := by
          nlinarith [hF]
        rw [hrel]
        field_simp [hpole S]
        ring

/-- The secular root is the least positive real eigenvalue of the explicitly
defined mode matrix. The existence part constructs its eigenvector; the
minimality part eliminates every proposed smaller positive eigenvector. -/
theorem secular_root_least_mode_eigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (a b : ι → ℝ) (η θ : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hη : 0 < η) (hθ : 0 < θ) :
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < siteRate a b i) ∧ secular a b η θ l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        modeNegativeGenerator a b η θ *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          modeNegativeGenerator a b η θ *ᵥ y = μ • y) → l ≤ μ := by
  obtain ⟨l, hl, huniq⟩ := (secular_unique_root a b η θ ha hb hη hθ).1
  refine ⟨l, hl.1, hl.2.1, hl.2.2, ?_, ?_⟩
  · exact (schur_equivalence a b η θ l (ne_of_gt hl.1)
      (denominators a b ha hb l hl.1 hl.2.1)).mpr hl.2.2
  · intro μ hμ he
    by_contra hnot
    have hlt : μ < l := lt_of_not_ge hnot
    have hupper : ∀ i, μ < siteRate a b i := fun i => hlt.trans (hl.2.1 i)
    have hF := (schur_equivalence a b η θ μ (ne_of_gt hμ)
      (denominators a b ha hb μ hμ hupper)).mp he
    have heq := huniq μ ⟨hμ, hupper, hF⟩
    linarith

#print axioms secular_root_least_mode_eigenvalue


theorem sum_subset_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) :
    (∑ S : Finset ι, ∏ i, if i ∈ S then f i else g i) = ∏ i, (f i + g i) := by
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext i
    simp
  · congr 1
    ext i
    simp

def localBasis (a b : ℝ) : Bool → Bool → ℝ
  | false, _ => 1
  | true, false => a / b
  | true, true => -1

def localInverse (a b : ℝ) : Bool → Bool → ℝ
  | false, _ => b / (a + b)
  | true, false => a / (a + b)
  | true, true => -b / (a + b)

def productBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) : Matrix (Finset ι) (Finset ι) ℝ :=
  fun σ S => ∏ i, localBasis (a i) (b i) (decide (i ∈ σ)) (decide (i ∈ S))

def productInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) : Matrix (Finset ι) (Finset ι) ℝ :=
  fun S σ => ∏ i, localInverse (a i) (b i) (decide (i ∈ S)) (decide (i ∈ σ))

private theorem local_inverse (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (x y : Bool) :
    localBasis a b x true * localInverse a b true y +
      localBasis a b x false * localInverse a b false y = if x = y then 1 else 0 := by
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  cases x <;> cases y <;> simp [localBasis, localInverse] <;>
    field_simp [ne_of_gt hb, hs] <;> ring

private theorem product_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    productBasis a b * productInverse a b = 1 := by
  ext σ τ
  simp only [Matrix.mul_apply, productBasis, productInverse, ← Finset.prod_mul_distrib]
  have hsum :
      (∑ S : Finset ι, ∏ i,
        localBasis (a i) (b i) (decide (i ∈ σ)) (decide (i ∈ S)) *
          localInverse (a i) (b i) (decide (i ∈ S)) (decide (i ∈ τ))) =
      ∏ i, if decide (i ∈ σ) = decide (i ∈ τ) then (1 : ℝ) else 0 := by
    calc
      _ = ∑ S : Finset ι, ∏ i,
          if i ∈ S then
            localBasis (a i) (b i) (decide (i ∈ σ)) true *
              localInverse (a i) (b i) true (decide (i ∈ τ))
          else localBasis (a i) (b i) (decide (i ∈ σ)) false *
              localInverse (a i) (b i) false (decide (i ∈ τ)) := by
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [hi]
      _ = _ := by
        rw [sum_subset_product]
        apply Finset.prod_congr rfl
        intro i _
        exact local_inverse (a i) (b i) (ha i) (hb i) _ _
  rw [hsum]
  by_cases h : σ = τ
  · subst τ
    simp
  · have hi : ∃ i, ¬ (i ∈ σ ↔ i ∈ τ) := by
      by_contra hn
      push Not at hn
      exact h (Finset.ext hn)
    obtain ⟨i, hi⟩ := hi
    have hb : decide (i ∈ σ) ≠ decide (i ∈ τ) := by simpa using hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hb])]
    simp [Matrix.one_apply, h]

def coordinateTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) : Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some S, some σ => productInverse a b S σ

def inverseTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) : Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ
  | none, none => 1
  | none, some _ => 0
  | some _, none => 0
  | some σ, some S => productBasis a b σ S

theorem transform_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    inverseTransform a b * coordinateTransform a b = 1 := by
  have h := product_inverse a b ha hb
  ext x y
  cases x with
  | none => cases y <;> simp [Matrix.mul_apply, Fintype.sum_option,
      inverseTransform, coordinateTransform, Matrix.one_apply]
  | some σ =>
    cases y with
    | none => simp [Matrix.mul_apply, Fintype.sum_option,
        inverseTransform, coordinateTransform, Matrix.one_apply]
    | some τ =>
      have he := congrFun (congrFun h σ) τ
      simpa [Matrix.mul_apply, Fintype.sum_option, inverseTransform,
        coordinateTransform, Matrix.one_apply] using he

theorem transform_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (p : Option (Finset ι) → ℝ) :
    p (some ∅) = ∑ S, (coordinateTransform a b *ᵥ p) (some S) := by
  have h := congrFun (mulVec_mulVec p (inverseTransform a b) (coordinateTransform a b)) (some ∅)
  rw [transform_inverse a b ha hb, one_mulVec] at h
  simpa [mulVec, dotProduct, Fintype.sum_option, inverseTransform, productBasis, localBasis]
    using h.symm

theorem inverse_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (S : Finset ι) :
    productInverse a b S ∅ = modeWeight a b S := by
  unfold productInverse modeWeight
  apply Finset.prod_congr rfl
  intro i _
  have hs : a i + b i ≠ 0 := ne_of_gt (add_pos (ha i) (hb i))
  by_cases hi : i ∈ S
  · simp [hi, localInverse, occupancy, siteRate]
  · simp [hi, localInverse, occupancy, siteRate]
    field_simp
    ring

private theorem site_jump {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (S σ : Finset ι) (i : ι) :
    (if i ∈ σ then b i * (productInverse a b S (σ.erase i) - productInverse a b S σ)
      else a i * (productInverse a b S (insert i σ) - productInverse a b S σ)) =
      -(if i ∈ S then siteRate a b i else 0) * productInverse a b S σ := by
  have hprod (τ : Finset ι) : productInverse a b S τ =
      localInverse (a i) (b i) (decide (i ∈ S)) (decide (i ∈ τ)) *
        ∏ j ∈ Finset.univ.erase i,
          localInverse (a j) (b j) (decide (j ∈ S)) (decide (j ∈ τ)) := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hrest (τ : Finset ι) (hτ : ∀ j, j ≠ i → (j ∈ τ ↔ j ∈ σ)) :
      (∏ j ∈ Finset.univ.erase i,
        localInverse (a j) (b j) (decide (j ∈ S)) (decide (j ∈ τ))) =
      ∏ j ∈ Finset.univ.erase i,
        localInverse (a j) (b j) (decide (j ∈ S)) (decide (j ∈ σ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [hτ j (Finset.mem_erase.mp hj).1]
  have hEr := hrest (σ.erase i) (by intro j hji; simp [hji])
  have hIns := hrest (insert i σ) (by intro j hji; simp [hji])
  rw [hprod (σ.erase i), hprod (insert i σ), hprod σ, hEr, hIns]
  have hs : a i + b i ≠ 0 := ne_of_gt (add_pos (ha i) (hb i))
  by_cases hiS : i ∈ S <;> by_cases hiσ : i ∈ σ <;>
    simp [hiS, hiσ, localInverse, siteRate] <;> field_simp <;> ring

private def modeObservable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (S : Finset ι) : Option (Finset ι) → ℝ
  | none => 0
  | some σ => productInverse a b S σ

private theorem backward_mode {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (S σ : Finset ι) :
    SingleEntryFiniteNetwork.backward k (modeObservable k.a k.b S) (some σ) =
      -(subsetRate k.a k.b S) * productInverse k.a k.b S σ -
        (if σ = ∅ then k.eta * modeWeight k.a k.b S else 0) := by
  have hsum :
      (∑ i, if i ∈ σ then k.b i *
          (productInverse k.a k.b S (σ.erase i) - productInverse k.a k.b S σ)
        else k.a i *
          (productInverse k.a k.b S (insert i σ) - productInverse k.a k.b S σ)) =
      -(subsetRate k.a k.b S) * productInverse k.a k.b S σ := by
    simp_rw [site_jump k.a k.b k.a_pos k.b_pos S σ]
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    simp [subsetRate]
  simp only [SingleEntryFiniteNetwork.backward, modeObservable]
  rw [hsum]
  by_cases hσ : σ = ∅
  · subst σ
    rw [inverse_empty k.a k.b k.a_pos k.b_pos]
    simp
    ring
  · simp [hσ]

theorem transform_generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (p : Option (Finset ι) → ℝ) :
    coordinateTransform k.a k.b *ᵥ (SingleEntryFiniteNetwork.generator k *ᵥ p) =
      -(modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ (coordinateTransform k.a k.b *ᵥ p)) := by
  have hnone : (SingleEntryFiniteNetwork.generator k *ᵥ p) none =
      -k.theta * p none + k.eta * p (some ∅) := by
    have h := SingleEntryFiniteNetwork.dual_backward k (Pi.single none 1) p
    simpa [SingleEntryFiniteNetwork.backward, Pi.single_apply,
      Fintype.sum_option] using h
  funext x
  cases x with
  | none =>
    rw [show (coordinateTransform k.a k.b *ᵥ
        (SingleEntryFiniteNetwork.generator k *ᵥ p)) none =
        (SingleEntryFiniteNetwork.generator k *ᵥ p) none by
      simp [mulVec, dotProduct, coordinateTransform, Fintype.sum_option]]
    rw [hnone, Pi.neg_apply, action_none,
      ← transform_empty k.a k.b k.a_pos k.b_pos]
    simp [mulVec, dotProduct, coordinateTransform, Fintype.sum_option]
    ring
  | some S =>
    have h := SingleEntryFiniteNetwork.dual_backward k (modeObservable k.a k.b S) p
    have hback (σ : Finset ι) := backward_mode k S σ
    have hR : SingleEntryFiniteNetwork.backward k (modeObservable k.a k.b S) none =
        k.theta * modeWeight k.a k.b S := by
      simp [SingleEntryFiniteNetwork.backward, modeObservable,
        inverse_empty k.a k.b k.a_pos k.b_pos]
    have hsum :
        (∑ σ, SingleEntryFiniteNetwork.backward k (modeObservable k.a k.b S) (some σ) * p (some σ)) =
        -subsetRate k.a k.b S * (∑ σ, productInverse k.a k.b S σ * p (some σ)) -
          k.eta * modeWeight k.a k.b S * p (some ∅) := by
      simp_rw [hback, sub_mul]
      rw [Finset.sum_sub_distrib]
      simp only [ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    simp only [Fintype.sum_option, modeObservable, zero_mul, zero_add, hR, hsum] at h
    have hT (v : Option (Finset ι) → ℝ) :
        (coordinateTransform k.a k.b *ᵥ v) (some S) =
          ∑ σ, productInverse k.a k.b S σ * v (some σ) := by
      simp [mulVec, dotProduct, coordinateTransform, Fintype.sum_option]
    have hTR : (coordinateTransform k.a k.b *ᵥ p) none = p none := by
      simp [mulVec, dotProduct, coordinateTransform, Fintype.sum_option]
    rw [Pi.neg_apply, action_some, ← transform_empty k.a k.b k.a_pos k.b_pos]
    rw [hT, hT, hTR]
    nlinarith [h]

private theorem generator_eigenvalue_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : SingleEntryFiniteNetwork.Rates ι) (l : ℝ) :
    (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
      (-SingleEntryFiniteNetwork.generator k) *ᵥ x = l • x) ↔
    (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
      modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ y = l • y) := by
  let T := coordinateTransform k.a k.b
  let P := inverseTransform k.a k.b
  have hPT : P * T = 1 := transform_inverse k.a k.b k.a_pos k.b_pos
  have hTP : T * P = 1 := mul_eq_one_comm.mp hPT
  have hinj : Function.Injective (fun x => T *ᵥ x) := by
    intro x y hxy
    have h := congrArg (fun z => P *ᵥ z) hxy
    simpa [mulVec_mulVec, hPT] using h
  have hconj (x : Option (Finset ι) → ℝ) :
      T *ᵥ ((-SingleEntryFiniteNetwork.generator k) *ᵥ x) =
        modeNegativeGenerator k.a k.b k.eta k.theta *ᵥ (T *ᵥ x) := by
    simpa [T, neg_mulVec, mulVec_neg] using congrArg Neg.neg (transform_generator k x)
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨T *ᵥ x, ?_, ?_⟩
    · intro hzero
      apply hx
      apply hinj
      simpa using hzero
    · rw [← hconj, he, mulVec_smul]
  · rintro ⟨y, hy, he⟩
    refine ⟨P *ᵥ y, ?_, ?_⟩
    · intro hzero
      have h := congrArg (fun z => T *ᵥ z) hzero
      apply hy
      simpa [mulVec_mulVec, hTP] using h
    · apply hinj
      change T *ᵥ ((-SingleEntryFiniteNetwork.generator k) *ᵥ (P *ᵥ y)) =
        T *ᵥ (l • (P *ᵥ y))
      have hTPv : T *ᵥ (P *ᵥ y) = y := by
        rw [mulVec_mulVec, hTP, one_mulVec]
      rw [hconj, mulVec_smul, hTPv]
      exact he

/-- In the independently specified configuration generator, the same secular
root is the least positive real eigenvalue of the full negative generator. -/
theorem secular_root_least_generator_eigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (k : SingleEntryFiniteNetwork.Rates ι) :
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < siteRate k.a k.b i) ∧
      secular k.a k.b k.eta k.theta l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        (-SingleEntryFiniteNetwork.generator k) *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          (-SingleEntryFiniteNetwork.generator k) *ᵥ y = μ • y) → l ≤ μ := by
  obtain ⟨l, hl, hu, hf, he, hmin⟩ :=
    secular_root_least_mode_eigenvalue k.a k.b k.eta k.theta
      k.a_pos k.b_pos k.eta_pos k.theta_pos
  exact ⟨l, hl, hu, hf, (generator_eigenvalue_iff k l).mpr he,
    fun μ hμ h => hmin μ hμ ((generator_eigenvalue_iff k μ).mp h)⟩

#print axioms secular_root_least_generator_eigenvalue
#print axioms action_none
#print axioms action_some
#print axioms sum_subset_product
#print axioms transform_inverse
#print axioms transform_empty
#print axioms inverse_empty
#print axioms transform_generator

end D5.S3.StatisticalMechanics.SingleEntrySpectralGap
