/- GID: D5/S3/StatisticalMechanics/SingleEntryProductMixture
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntryProductMixture
   mirror-E: none(waiver:continuous-product-mixture)
   anchors: []
   utility: none
   digest: Positive ordered mixtures have strictly positive Boolean lattice minors. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # Strict lattice minors of an ordered product mixture

The mixing variable is shared by all actual sites. The result concerns the
integral law and does not presume an identification with a Markov trajectory.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace D5.S3.StatisticalMechanics.SingleEntryProductMixture

private theorem strict_weighted_covariance (h f g : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hh : ContinuousOn h (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hn : ∀ x ∈ Icc a b, 0 ≤ h x)
    (hp : ∀ x ∈ Ioo a b, 0 < h x)
    (hmf : MonotoneOn f (Icc a b)) (hmg : MonotoneOn g (Icc a b))
    (hsf : StrictMonoOn f (Ioo a b)) (hsg : StrictMonoOn g (Ioo a b)) :
    (∫ x in a..b, h x * f x) * (∫ x in a..b, h x * g x) <
      (∫ x in a..b, h x) * (∫ x in a..b, h x * f x * g x) := by
  let H := ∫ x in a..b, h x
  let U := ∫ x in a..b, h x * f x
  let V := ∫ x in a..b, h x * g x
  let W := ∫ x in a..b, h x * f x * g x
  let C := fun x => h x * (f x * g x * H - f x * V - g x * U + W)
  have ih : IntervalIntegrable h volume a b := hh.intervalIntegrable_of_Icc hab.le
  have iU : IntervalIntegrable (fun x => h x * f x) volume a b := (hh.mul hf).intervalIntegrable_of_Icc hab.le
  have iV : IntervalIntegrable (fun x => h x * g x) volume a b := (hh.mul hg).intervalIntegrable_of_Icc hab.le
  have iW : IntervalIntegrable (fun x => h x * f x * g x) volume a b := ((hh.mul hf).mul hg).intervalIntegrable_of_Icc hab.le
  have inner (x : ℝ) :
      (∫ y in a..b, h x * h y * (f x - f y) * (g x - g y)) = C x := by
    calc
      _ = ∫ y in a..b, (h x * (f x * g x) * h y -
          h x * f x * (h y * g y) - h x * g x * (h y * f y) +
          h x * (h y * f y * g y)) := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = C x := by
        rw [intervalIntegral.integral_add,
          intervalIntegral.integral_sub, intervalIntegral.integral_sub]
        · simp only [intervalIntegral.integral_const_mul]
          dsimp [C, H, U, V, W]
          ring
        all_goals
          apply ContinuousOn.intervalIntegrable_of_Icc hab.le
          fun_prop
  have sign (x : ℝ) (hx : x ∈ Icc a b) (y : ℝ) (hy : y ∈ Icc a b) :
      0 ≤ h x * h y * (f x - f y) * (g x - g y) := by
    have hw := mul_nonneg (hn x hx) (hn y hy)
    rcases le_total x y with hxy | hyx
    · have hff := hmf hx hy hxy
      have hgg := hmg hx hy hxy
      nlinarith [mul_nonneg (sub_nonneg.mpr hff) (sub_nonneg.mpr hgg),
        mul_nonneg hw (mul_nonneg (sub_nonneg.mpr hff) (sub_nonneg.mpr hgg))]
    · have hff := hmf hy hx hyx
      have hgg := hmg hy hx hyx
      exact mul_nonneg (mul_nonneg hw (sub_nonneg.mpr hff)) (sub_nonneg.mpr hgg)
  have Cnonneg (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ C x := by
    rw [← inner]
    exact intervalIntegral.integral_nonneg hab.le (fun y hy => sign x hx y hy)
  have Ccont : ContinuousOn C (Icc a b) := by
    dsimp [C]
    fun_prop
  let x := (a + b) / 2
  let y := (a + x) / 2
  have hx : x ∈ Ioo a b := by dsimp [x]; constructor <;> linarith
  have hy : y ∈ Ioo a b := by dsimp [y]; constructor <;> linarith [hx.1, hx.2]
  have hyx : y < x := by dsimp [y]; linarith [hx.1]
  have Cpos : 0 < C x := by
    rw [← inner]
    apply intervalIntegral.integral_pos hab
    · fun_prop
    · intro z hz
      exact sign x ⟨hx.1.le, hx.2.le⟩ z ⟨hz.1.le, hz.2⟩
    · refine ⟨y, ⟨hy.1.le, hy.2.le⟩, ?_⟩
      exact mul_pos (mul_pos (mul_pos (hp x hx) (hp y hy))
        (sub_pos.mpr (hsf hy hx hyx)))
        (sub_pos.mpr (hsg hy hx hyx))
  have totalpos : 0 < ∫ x in a..b, C x :=
    intervalIntegral.integral_pos hab Ccont
      (fun z hz => Cnonneg z ⟨hz.1.le, hz.2⟩)
      ⟨x, ⟨hx.1.le, hx.2.le⟩, Cpos⟩
  have total : (∫ x in a..b, C x) = 2 * (H * W - U * V) := by
    calc
      _ = ∫ x in a..b, (h x * f x * g x * H - (h x * f x) * V -
          (h x * g x) * U + h x * W) := by
        apply intervalIntegral.integral_congr
        intro z _
        dsimp [C]
        ring
      _ = 2 * (H * W - U * V) := by
        rw [intervalIntegral.integral_add,
          intervalIntegral.integral_sub, intervalIntegral.integral_sub]
        · simp only [intervalIntegral.integral_mul_const]
          change W * H - U * V - V * U + H * W = _
          ring
        all_goals
          apply ContinuousOn.intervalIntegrable_of_Icc hab.le
          fun_prop
  rw [total] at totalpos
  change U * V < H * W
  linarith

/-- Unnormalized Boolean product mass at one value of the common variable. -/
def productKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ → ℝ) (S : Finset ι) (u : ℝ) : ℝ :=
  ∏ i, if i ∈ S then g i u else 1 - g i u

/-- A common-variable mixture; normalization is unnecessary for lattice minors. -/
def mixtureMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℝ → ℝ) (g : ι → ℝ → ℝ) (t : ℝ) (S : Finset ι) : ℝ :=
  ∫ u in 0..t, h u * productKernel g S u


private theorem kernel_odds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ → ℝ) (S : Finset ι) (u : ℝ)
    (hg : ∀ i, g i u < 1) :
    productKernel g S u = (∏ i, (1 - g i u)) *
      ∏ i ∈ S, g i u / (1 - g i u) := by
  calc
    _ = ∏ i, (1 - g i u) *
        (if i ∈ S then g i u / (1 - g i u) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, if_pos]
        field_simp [ne_of_gt (sub_pos.mpr (hg i))]
      · simp [hi]
    _ = _ := by rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem]

/-- Every incomparable pair has a strict lattice minor in a positive continuous
mixture of product Bernoulli laws whose site occupancies strictly increase with
the same real variable. The integration interval is nondegenerate. -/
theorem strict_mtp2_product_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℝ → ℝ) (g : ι → ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hh : ContinuousOn h (Icc 0 t))
    (hn : ∀ u ∈ Icc 0 t, 0 ≤ h u) (hp : ∀ u ∈ Ioo 0 t, 0 < h u)
    (hg : ∀ i, ContinuousOn (g i) (Icc 0 t))
    (hb : ∀ i u, u ∈ Icc 0 t → 0 ≤ g i u ∧ g i u < 1)
    (hm : ∀ i, StrictMonoOn (g i) (Icc 0 t))
    (S T : Finset ι) (hST : ¬ S ⊆ T) (hTS : ¬ T ⊆ S) :
    mixtureMass h g t S * mixtureMass h g t T <
      mixtureMass h g t (S ∩ T) * mixtureMass h g t (S ∪ T) := by
  let o := fun i u => g i u / (1 - g i u)
  let P := fun A : Finset ι => fun u => ∏ i ∈ A, o i u
  let w := fun u => h u * (∏ i, (1 - g i u)) * P (S ∩ T) u
  have hden (i : ι) (u : ℝ) (hu : u ∈ Icc 0 t) : 0 < 1 - g i u :=
    sub_pos.mpr (hb i u hu).2
  have ononneg (i : ι) (u : ℝ) (hu : u ∈ Icc 0 t) : 0 ≤ o i u :=
    div_nonneg (hb i u hu).1 (hden i u hu).le
  have opos (i : ι) (u : ℝ) (hu : u ∈ Ioo 0 t) : 0 < o i u := by
    have hzero := (hb i 0 ⟨le_rfl, ht.le⟩).1
    have hinc := hm i ⟨le_rfl, ht.le⟩ ⟨hu.1.le, hu.2.le⟩ hu.1
    exact div_pos (lt_of_le_of_lt hzero hinc) (hden i u ⟨hu.1.le, hu.2.le⟩)
  have omono (i : ι) : StrictMonoOn (o i) (Icc 0 t) := by
    intro x hx y hy hxy
    dsimp [o]
    rw [div_lt_div_iff₀ (hden i x hx) (hden i y hy)]
    nlinarith [hm i hx hy hxy]
  have ocont (i : ι) : ContinuousOn (o i) (Icc 0 t) := by
    exact (hg i).div (continuousOn_const.sub (hg i))
      (fun u hu => ne_of_gt (hden i u hu))
  have Pcont (A : Finset ι) : ContinuousOn (P A) (Icc 0 t) := by
    exact continuousOn_finsetProd A (fun i _ => ocont i)
  have Pnonneg (A : Finset ι) (u : ℝ) (hu : u ∈ Icc 0 t) : 0 ≤ P A u :=
    Finset.prod_nonneg (fun i _ => ononneg i u hu)
  have Ppos (A : Finset ι) (u : ℝ) (hu : u ∈ Ioo 0 t) : 0 < P A u :=
    Finset.prod_pos (fun i _ => opos i u hu)
  have Pmono (A : Finset ι) : MonotoneOn (P A) (Icc 0 t) := by
    intro x hx y hy hxy
    exact Finset.prod_le_prod₀ (fun i _ => ononneg i x hx)
      (fun i _ => (omono i).monotoneOn hx hy hxy)
  have Pstrict (A : Finset ι) (hA : A.Nonempty) : StrictMonoOn (P A) (Ioo 0 t) := by
    intro x hx y hy hxy
    exact Finset.prod_lt_prod_of_nonempty₀ (fun i _ => opos i x hx)
      (fun i _ => omono i ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy) hA
  have hwcont : ContinuousOn w (Icc 0 t) := by
    exact (hh.mul (continuousOn_finsetProd Finset.univ
      (fun i _ => continuousOn_const.sub (hg i)))).mul (Pcont _)
  have hwnonneg (u : ℝ) (hu : u ∈ Icc 0 t) : 0 ≤ w u :=
    mul_nonneg (mul_nonneg (hn u hu)
      (Finset.prod_nonneg (fun i _ => (hden i u hu).le))) (Pnonneg _ u hu)
  have hwpos (u : ℝ) (hu : u ∈ Ioo 0 t) : 0 < w u :=
    mul_pos (mul_pos (hp u hu)
      (Finset.prod_pos (fun i _ => hden i u ⟨hu.1.le, hu.2.le⟩))) (Ppos _ u hu)
  have hA : (S \ T).Nonempty := Finset.sdiff_nonempty.mpr hST
  have hB : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr hTS
  have cov := strict_weighted_covariance w (P (S \ T)) (P (T \ S)) 0 t ht
    hwcont (Pcont _) (Pcont _) hwnonneg hwpos (Pmono _) (Pmono _)
    (Pstrict _ hA) (Pstrict _ hB)
  have pk (A : Finset ι) (u : ℝ) (hu : u ∈ Icc 0 t) :
      h u * productKernel g A u = h u * (∏ i, (1 - g i u)) * P A u := by
    rw [kernel_odds g A u (fun i => (hb i u hu).2)]
    dsimp [P, o]
    ring
  have pS (u : ℝ) : P S u = P (S ∩ T) u * P (S \ T) u :=
    (Finset.prod_inter_mul_prod_sdiff S T (fun i => o i u)).symm
  have pT (u : ℝ) : P T u = P (S ∩ T) u * P (T \ S) u := by
    simpa [P, Finset.inter_comm] using
      (Finset.prod_inter_mul_prod_sdiff T S (fun i => o i u)).symm
  have pU (u : ℝ) : P (S ∪ T) u =
      P (S ∩ T) u * P (S \ T) u * P (T \ S) u := by
    have he : S ∪ T = S ∪ (T \ S) := by ext i; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [he]
    change (∏ i ∈ S ∪ (T \ S), o i u) = _
    rw [Finset.prod_union (by apply Finset.disjoint_left.mpr; intro i hi h; exact (Finset.mem_sdiff.mp h).2 hi)]
    change P S u * P (T \ S) u = _
    rw [pS]
  have eC : mixtureMass h g t (S ∩ T) = ∫ u in 0..t, w u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact pk _ u (by simpa [uIcc_of_le ht.le] using hu)
  have eS : mixtureMass h g t S = ∫ u in 0..t, w u * P (S \ T) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [pk _ u (by simpa [uIcc_of_le ht.le] using hu), pS]
    dsimp [w]
    ring
  have eT : mixtureMass h g t T = ∫ u in 0..t, w u * P (T \ S) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [pk _ u (by simpa [uIcc_of_le ht.le] using hu), pT]
    dsimp [w]
    ring
  have eU : mixtureMass h g t (S ∪ T) =
      ∫ u in 0..t, w u * P (S \ T) u * P (T \ S) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [pk _ u (by simpa [uIcc_of_le ht.le] using hu), pU]
    dsimp [w]
    ring
  rw [eS, eT, eC, eU]
  exact cov

#print axioms strict_mtp2_product_mixture

end D5.S3.StatisticalMechanics.SingleEntryProductMixture
