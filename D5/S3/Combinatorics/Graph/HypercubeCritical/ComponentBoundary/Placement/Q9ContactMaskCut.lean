/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ContactMaskCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Three-mask axis cuts generate translations of contact fibres. Composing the translations from two cuts can force a further mask. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

/-! Axis cuts of the distance-two contact masks in Hong–Wu–Xia,
arXiv:2610.09483v1, §7, Problem 2.

The mixed Huang row has zero sum for each axis cut. For a three-mask cut,
its contact graph has degree two at every incident vertex. Varying the
weight on one distinguishing coordinate rules out the alternating square.
Following the contact edges then realizes the product of the other two
masks as a translation of the fibre. Products of the translations forced
by different cuts of the mask graph can force additional contact masks.
-/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang
  (parity flipSign weightedAction weightedLinear weightedLinear_apply weightedLinear_square)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open private differingAxes parity_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-- The distance-two masks crossing the cut determined by the axis set `A`. -/
def cutMasks (C D : Finset (Q 9)) (b : Bool) (A : Finset (Fin 9)) :
    Finset (Finset (Fin 9)) :=
  (minimumDisplacements C D b 2).filter fun S => (S ∩ A).card = 1

private abbrev AxisPair := Fin 9 × Fin 9

private def cutPairs (A : Finset (Fin 9)) : Finset AxisPair :=
  A.product (Finset.univ \ A)

private def mask (p : AxisPair) : Finset (Fin 9) := {p.1, p.2}

private def translate (p : AxisPair) (x : Q 9) : Q 9 := flip (flip x p.1) p.2

private theorem translate_involution (p : AxisPair) (x : Q 9) :
    translate p (translate p x) = x := by
  unfold translate
  rw [flip_comm (flip x p.1) p.2 p.1,
    BalancedCriticalSpectrum.flip_flip, BalancedCriticalSpectrum.flip_flip]

private theorem translate_comm (p q : AxisPair) (x : Q 9) :
    translate p (translate q x) = translate q (translate p x) := by
  unfold translate
  rw [flip_comm (flip x q.1) q.2 p.1, flip_comm x q.1 p.1,
    flip_comm (flip (flip x p.1) q.1) q.2 p.2,
    flip_comm (flip x p.1) q.1 p.2]

private theorem parity_translate (p : AxisPair) (x : Q 9) :
    parity (translate p x) = parity x := by
  simp only [translate, parity_flip, Bool.not_not]

private theorem axes_of_mem_cutPairs {A : Finset (Fin 9)} {p : AxisPair} (hp : p ∈ cutPairs A) :
    p.1 ∈ A ∧ p.2 ∉ A :=
  ⟨(Finset.mem_product.mp hp).1, (Finset.mem_sdiff.mp (Finset.mem_product.mp hp).2).2⟩

private theorem mask_inter {A : Finset (Fin 9)} {p : AxisPair} (hp : p ∈ cutPairs A) :
    mask p ∩ A = {p.1} := by
  obtain ⟨hi, hj⟩ := axes_of_mem_cutPairs hp
  ext k
  simp only [mask, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hk⟩
    · rfl
    · exact (hj hk).elim
  · rintro rfl
    exact ⟨Or.inl rfl, hi⟩

private theorem mask_injOn (A : Finset (Fin 9)) :
    Set.InjOn mask (cutPairs A : Set AxisPair) := by
  intro p hp q hq he
  have hi : p.1 = q.1 := by
    have he' := congrArg (fun S : Finset (Fin 9) => S ∩ A) he
    rw [mask_inter hp, mask_inter hq] at he'
    exact Finset.mem_singleton.mp (he' ▸ Finset.mem_singleton_self p.1)
  have hm : p.2 ∈ mask q := he ▸ (by simp [mask] : p.2 ∈ mask p)
  have hne : p.2 ≠ q.1 := fun h => (axes_of_mem_cutPairs hp).2 (h.symm ▸ (axes_of_mem_cutPairs hq).1)
  have hj : p.2 = q.2 := by simpa [mask, hne] using hm
  exact Prod.ext hi hj

private theorem exists_cutPair {C D : Finset (Q 9)} {b : Bool} {A S : Finset (Fin 9)}
    (hS : S ∈ cutMasks C D b A) :
    ∃ p ∈ cutPairs A, mask p = S := by
  obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hS
  obtain ⟨x, _, y, _, _, hd, he⟩ := mem_minimumDisplacements.mp hm
  have hcard : S.card = 2 := by
    rw [← he]
    exact hd
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hiS : i ∈ S ∩ A := by rw [hi]; simp
  obtain ⟨j, hjS, hji⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) i
  have hjA : j ∉ A := fun hj =>
    hji (Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨hjS, hj⟩))
  refine ⟨(i, j), Finset.mem_product.mpr
    ⟨(Finset.mem_inter.mp hiS).2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjA⟩⟩, ?_⟩
  apply Finset.eq_of_subset_of_card_le
    (Finset.insert_subset (Finset.mem_inter.mp hiS).1 (Finset.singleton_subset_iff.mpr hjS))
  simpa only [mask, Finset.card_pair hji.symm, hcard] using Nat.le_refl 2

private def cutTerm (w : Fin 9 → ℝ) (g : Q 9 → ℝ) (x : Q 9) (p : AxisPair) : ℝ :=
  w p.1 * (flipSign p.1 x : ℝ) *
    (w p.2 * (flipSign p.2 (flip x p.1) : ℝ) * g (translate p x))

private theorem abs_cutTerm {w : Fin 9 → ℝ} (hw : ∀ i, 0 < w i)
    (g : Q 9 → ℝ) (x : Q 9) (p : AxisPair) :
    |cutTerm w g x p| = (w p.1 * w p.2) * |g (translate p x)| := by
  have hs (z : Q 9) (i : Fin 9) : |(flipSign i z : ℝ)| = 1 := by
    rw [flipSign_cast]
    exact SupportedEigenSaturation.matrix_abs_of_adj (flip_adj z i)
  simp only [cutTerm, abs_mul, abs_of_pos (hw p.1), abs_of_pos (hw p.2), hs, one_mul, mul_assoc]

/-- The mixed part of the weighted operator has zero row on the opposite support. -/
private theorem weighted_cut_row {C D : Finset (Q 9)} (A : Finset (Fin 9))
    {w : Fin 9 → ℝ} {g : Q 9 → ℝ} {x : Q 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hx : x ∈ C) (hg : ∀ z ∉ D, g z = 0)
    (hAg : ∀ z ∉ D, weightedLinear w g z = 0) :
    ∑ p ∈ cutPairs A, cutTerm w g x p = 0 := by
  classical
  let u : Fin 9 → ℝ := fun i => if i ∈ A then w i else 0
  let v : Fin 9 → ℝ := fun i => if i ∈ A then 0 else w i
  have hsplit : weightedLinear w g = weightedLinear u g + weightedLinear v g := by
    funext z
    simp only [weightedLinear_apply, weightedAction, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A <;> simp [u, v, hi]
  have hfull : weightedLinear u (weightedLinear w g) x = 0 := by
    rw [weightedLinear_apply u, weightedAction]
    apply Finset.sum_eq_zero
    intro i _
    have hout : flip x i ∉ D := by
      intro hi
      have h := hsep x hx (flip x i) hi
      rw [show hammingDist x (flip x i) = 1 from flip_adj x i] at h
      omega
    rw [hAg _ hout, mul_zero]
  have hxout : x ∉ D := by
    intro hxD
    have h := hsep x hx x hxD
    simp at h
  have hsq := congrArg (fun L : Module.End ℝ (Q 9 → ℝ) => L g x) (weightedLinear_square u)
  have huu : weightedLinear u (weightedLinear u g) x = (∑ i, u i ^ 2) * g x := by
    simpa only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Pi.smul_apply, smul_eq_mul] using hsq
  have hmix : weightedLinear u (weightedLinear v g) x = 0 := by
    rw [hsplit, map_add, Pi.add_apply, huu, hg x hxout, mul_zero, zero_add] at hfull
    exact hfull
  rw [weightedLinear_apply u, weightedAction] at hmix
  have hrestrict (B : Finset (Fin 9)) (a : Fin 9 → ℝ) :
      (∑ i, if i ∈ B then a i else 0) = ∑ i ∈ B, a i := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hinner (z : Q 9) : weightedLinear v g z =
      ∑ j ∈ (Finset.univ \ A), w j * (flipSign j z : ℝ) * g (flip z j) := by
    rw [weightedLinear_apply, weightedAction,
      ← hrestrict (Finset.univ \ A) (fun j => w j * (flipSign j z : ℝ) * g (flip z j))]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ A <;> simp [v, hj]
  calc
    _ = ∑ i ∈ A, ∑ j ∈ Finset.univ \ A, cutTerm w g x (i, j) :=
      Finset.sum_product A (Finset.univ \ A) (cutTerm w g x)
    _ = ∑ i ∈ A, w i * (flipSign i x : ℝ) * weightedLinear v g (flip x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hinner, Finset.mul_sum]
      rfl
    _ = ∑ i, u i * (flipSign i x : ℝ) * weightedLinear v g (flip x i) := by
      rw [← hrestrict A (fun i => w i * (flipSign i x : ℝ) * weightedLinear v g (flip x i))]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ A <;> simp [u, hi]
    _ = 0 := hmix

private theorem axes_ne {A : Finset (Fin 9)} {p : AxisPair} (hp : p ∈ cutPairs A) :
    p.1 ≠ p.2 := fun h =>
  (axes_of_mem_cutPairs hp).2 (h ▸ (axes_of_mem_cutPairs hp).1)

private theorem mask_mem_of_contact
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {p : AxisPair} {x : Q 9}
    (hp : p ∈ cutPairs A) (hx : x ∈ C) (hxb : parity x = b)
    (hy : translate p x ∈ D) : mask p ∈ cutMasks C D b A := by
  have hdist : hammingDist x (translate p x) = 2 := by
    change (differingAxes x (translate p x)).card = 2
    rw [translate, diff_pair x (axes_ne hp), Finset.card_pair (axes_ne hp)]
  exact Finset.mem_filter.mpr
    ⟨mem_minimumDisplacements.mpr ⟨x, hx, _, hy, hxb, hdist, diff_pair x (axes_ne hp)⟩,
      by rw [mask_inter hp, Finset.card_singleton]⟩

private theorem contact_of_mask
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {p : AxisPair}
    (hp : p ∈ cutPairs A) (hm : mask p ∈ cutMasks C D b A) :
    ∃ x ∈ C, parity x = b ∧ translate p x ∈ D := by
  obtain ⟨x, hx, y, hy, hxb, _, he⟩ :=
    mem_minimumDisplacements.mp (Finset.mem_filter.mp hm).1
  have hxy : y = translate p x :=
    differingAxes_right_inj (he.trans (diff_pair x (axes_ne hp)).symm)
  exact ⟨x, hx, hxb, hxy ▸ hy⟩

private theorem cutMasks_swap (C D : Finset (Q 9)) (b : Bool) (A : Finset (Fin 9)) :
    cutMasks C D b A = cutMasks D C b A := by
  unfold cutMasks
  rw [minimumDisplacements_swap_two C D b]

/-- On parity b, a nonzero term comes from an actual crossing mask. -/
private theorem restricted_cut_row
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    {w : Fin 9 → ℝ} {g : Q 9 → ℝ} {x : Q 9} {P : Finset AxisPair}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hx : x ∈ C) (hxb : parity x = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = b)
    (hAg : ∀ z ∉ D, weightedLinear w g z = 0)
    (hP : P ⊆ cutPairs A)
    (hcover : ∀ p ∈ cutPairs A, mask p ∈ cutMasks C D b A → p ∈ P) :
    ∑ p ∈ P, cutTerm w g x p = 0 := by
  have hgout (z : Q 9) (hz : z ∉ D) : g z = 0 := by
    by_contra hn
    exact hz ((hg z).mp hn).1
  calc
    _ = ∑ p ∈ cutPairs A, cutTerm w g x p := by
      apply Finset.sum_subset hP
      intro p hp hpP
      suffices hz : g (translate p x) = 0 by simp [cutTerm, hz]
      by_contra hn
      exact hpP (hcover p hp (mask_mem_of_contact hp hx hxb ((hg _).mp hn).1))
    _ = 0 := weighted_cut_row A hsep hx hgout hAg

private theorem abs_eq_of_pair_row
    {w : Fin 9 → ℝ} (hw : ∀ i, 0 < w i)
    {g : Q 9 → ℝ} {x : Q 9} {p q : AxisPair}
    (h : cutTerm w g x p + cutTerm w g x q = 0) :
    (w p.1 * w p.2) * |g (translate p x)| =
      (w q.1 * w q.2) * |g (translate q x)| := by
  have he : cutTerm w g x p = -cutTerm w g x q := by linarith only [h]
  simpa only [abs_neg, abs_cutTerm hw] using congrArg (fun r : ℝ => |r|) he

private theorem alternating_square_impossible
    {w : Fin 9 → ℝ} (hw : ∀ i, 0 < w i)
    {g : Q 9 → ℝ} {x : Q 9} {p q : AxisPair}
    (hp : w p.1 * w p.2 = 2) (hq : w q.1 * w q.2 = 1)
    (hcontact : g (translate p x) ≠ 0)
    (hrow : cutTerm w g x p + cutTerm w g x q = 0)
    (hopposite : let x' := translate q (translate p x)
      cutTerm w g x' p + cutTerm w g x' q = 0) : False := by
  let x' := translate q (translate p x)
  have h₁ := abs_eq_of_pair_row hw hrow
  have h₂ := abs_eq_of_pair_row hw
    (show cutTerm w g x' p + cutTerm w g x' q = 0 from hopposite)
  have hp' : translate p x' = translate q x := by
    change translate p (translate q (translate p x)) = translate q x
    rw [translate_comm p q, translate_involution]
  have hq' : translate q x' = translate p x := translate_involution q (translate p x)
  rw [hp, hq, one_mul] at h₁
  rw [hp', hq', hp, hq, one_mul] at h₂
  linarith only [h₁, h₂, abs_pos.mpr hcontact]

private theorem weight_product
    (i : Fin 9) {p : AxisPair} (hp : p.1 ≠ p.2) :
    let w : Fin 9 → ℝ := fun j => if j = i then 2 else 1
    w p.1 * w p.2 = if i ∈ mask p then 2 else 1 := by
  dsimp [mask]
  by_cases h₁ : p.1 = i
  · have h₂ : p.2 ≠ i := fun he => hp (h₁.trans he.symm)
    simp [h₁, h₂, Ne.symm h₂]
  · by_cases h₂ : p.2 = i
    · simp [h₁, h₂, Ne.symm h₁]
    · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]

private theorem cut_card_of_supported
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hker : ∀ w : Fin 9 → ℝ, (∀ i, 0 < w i) →
      ∃ f g : Q 9 → ℝ,
        (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
        (∀ x ∉ C, weightedLinear w f x = 0) ∧
        (∀ x, g x ≠ 0 ↔ x ∈ D ∧ parity x = b) ∧
        (∀ x ∉ D, weightedLinear w g x = 0))
    (hne : (cutMasks C D b A).Nonempty) :
    3 ≤ (cutMasks C D b A).card := by
  classical
  let F := cutMasks C D b A
  have hpos : 0 < F.card := Finset.card_pos.mpr hne
  change 3 ≤ F.card
  by_contra hlarge
  by_cases hone : F.card = 1
  · obtain ⟨S, hS⟩ := Finset.card_eq_one.mp hone
    have hmem : S ∈ F := by rw [hS]; simp
    obtain ⟨p, hp, hm⟩ := exists_cutPair hmem
    obtain ⟨x, hx, hxb, hy⟩ := contact_of_mask hp (hm.symm ▸ hmem)
    let w : Fin 9 → ℝ := fun _ => 1
    have hw (i : Fin 9) : 0 < w i := by norm_num [w]
    obtain ⟨_, g, _, _, hg, hAg⟩ := hker w hw
    have hsub : ({p} : Finset AxisPair) ⊆ cutPairs A := Finset.singleton_subset_iff.mpr hp
    have hcover (r : AxisPair) (hr : r ∈ cutPairs A) (hmr : mask r ∈ F) :
        r ∈ ({p} : Finset AxisPair) := by
      have he : mask r = S := Finset.mem_singleton.mp (hS ▸ hmr)
      exact Finset.mem_singleton.mpr (mask_injOn A hr hp (he.trans hm.symm))
    have hrow := restricted_cut_row hsep hx hxb hg hAg hsub hcover
    have ht : cutTerm w g x p = 0 := by simpa only [Finset.sum_singleton] using hrow
    have hgn : g (translate p x) ≠ 0 :=
      (hg _).mpr ⟨hy, (parity_translate p x).trans hxb⟩
    have hz := abs_cutTerm hw g x p
    rw [ht, abs_zero] at hz
    exact (mul_ne_zero (mul_ne_zero (hw p.1).ne' (hw p.2).ne') (abs_ne_zero.mpr hgn)) hz.symm
  · have htwo : F.card = 2 := by omega
    obtain ⟨S, T, hST, hF⟩ := Finset.card_eq_two.mp htwo
    have hS : S ∈ F := by rw [hF]; simp
    have hT : T ∈ F := by rw [hF]; simp
    obtain ⟨p, hp, hm⟩ := exists_cutPair hS
    obtain ⟨q, hq, hn⟩ := exists_cutPair hT
    have hpq : p ≠ q := fun h => hST (hm.symm.trans ((congrArg mask h).trans hn))
    obtain ⟨x, hx, hxb, hy⟩ := contact_of_mask hp (hm.symm ▸ hS)
    have hcardS : S.card = 2 := by rw [← hm]; exact Finset.card_pair (axes_ne hp)
    have hcardT : T.card = 2 := by rw [← hn]; exact Finset.card_pair (axes_ne hq)
    have hns : ¬ S ⊆ T := fun hs =>
      hST (Finset.eq_of_subset_of_card_le hs (hcardT.trans hcardS.symm).le)
    have hdiff : ∃ i ∈ S, i ∉ T := by
      by_contra h
      apply hns
      intro j hj
      by_contra hj'
      exact h ⟨j, hj, hj'⟩
    obtain ⟨i, hiS, hiT⟩ := hdiff
    let w : Fin 9 → ℝ := fun j => if j = i then 2 else 1
    have hw (j : Fin 9) : 0 < w j := by
      dsimp only [w]
      split <;> norm_num
    obtain ⟨f, g, hf, hAf, hg, hAg⟩ := hker w hw
    have hwP : w p.1 * w p.2 = 2 := by
      simpa only [hm, hiS, ite_true] using weight_product i (axes_ne hp)
    have hwQ : w q.1 * w q.2 = 1 := by
      simpa only [hn, hiT, ite_false] using weight_product i (axes_ne hq)
    have hsub : ({p, q} : Finset AxisPair) ⊆ cutPairs A :=
      Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hq)
    have hcover (r : AxisPair) (hr : r ∈ cutPairs A) (hmr : mask r ∈ F) :
        r ∈ ({p, q} : Finset AxisPair) := by
      rw [hF, Finset.mem_insert, Finset.mem_singleton] at hmr
      rcases hmr with he | he
      · have hrp := mask_injOn A hr hp (he.trans hm.symm)
        simp [hrp]
      · have hrq := mask_injOn A hr hq (he.trans hn.symm)
        simp [hrq]
    have hrowC (z : Q 9) (hz : z ∈ C) (hzb : parity z = b) :
        cutTerm w g z p + cutTerm w g z q = 0 := by
      simpa only [Finset.sum_pair hpq] using
        restricted_cut_row hsep hz hzb hg hAg hsub hcover
    have hsep' (z : Q 9) (hz : z ∈ D) (v : Q 9) (hv : v ∈ C) :
        2 ≤ hammingDist z v := by
      rw [hammingDist_comm z v]
      exact hsep v hv z hz
    have hcover' (r : AxisPair) (hr : r ∈ cutPairs A)
        (hmr : mask r ∈ cutMasks D C b A) : r ∈ ({p, q} : Finset AxisPair) := by
      rw [cutMasks_swap D C b A] at hmr
      exact hcover r hr hmr
    let y := translate p x
    let x' := translate q y
    have hyb : parity y = b := (parity_translate p x).trans hxb
    have hx'b : parity x' = b := (parity_translate q y).trans hyb
    have hgyn : g y ≠ 0 := (hg y).mpr ⟨hy, hyb⟩
    have hyrow := restricted_cut_row hsep' hy hyb hf hAf hsub hcover'
    have hback : translate p y = x := translate_involution p x
    have hfy : (2 : ℝ) * |f x| = |f x'| := by
      have hpair : cutTerm w f y p + cutTerm w f y q = 0 := by
        simpa only [Finset.sum_pair hpq] using hyrow
      have he := abs_eq_of_pair_row hw hpair
      simpa only [hback, hwP, hwQ, one_mul] using he
    have hfx'n : f x' ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hfy
      exact (mul_ne_zero (by norm_num) (abs_ne_zero.mpr ((hf x).mpr ⟨hx, hxb⟩))) hfy
    have hx'C : x' ∈ C := ((hf x').mp hfx'n).1
    exact alternating_square_impossible hw hwP hwQ hgyn
      (hrowC x hx hxb) (hrowC x' hx'C hx'b)

open Classical in
/-- Every axis cut containing a distance-two contact mask contains at least
three distinct masks on the same parity. -/
theorem every_nonempty_axis_cut_has_three_masks
    {C D : Finset (Q 9)} {b : Bool} (A : Finset (Fin 9))
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hne : (cutMasks C D b A).Nonempty) :
    3 ≤ (cutMasks C D b A).card := by
  apply cut_card_of_supported hsep _ hne
  intro w hw
  obtain ⟨f, hf, hAf⟩ :=
    exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  obtain ⟨g, hg, hAg⟩ :=
    exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD w hw (hdetD w) b
  exact ⟨f, g, hf, hAf, hg, hAg⟩

open private signed_sum_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

open Classical in
/-- Every contact endpoint has even degree across an axis cut. At unit
weights, the opposite component's switching vector makes the retained
terms equal to 1 or -1, and the mixed row vanishes. -/
theorem even_crossing_contact_degree {C D : Finset (Q 9)} (A : Finset (Fin 9))
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hregular : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced D) {x : Q 9} (hx : x ∈ C) :
    Even (((A.product (Finset.univ \ A)).filter
      fun p => flip (flip x p.1) p.2 ∈ D).card) := by
  classical
  obtain ⟨σ, hσ⟩ := hbalanced
  let g := BalancedCriticalSpectrum.switchingVector D σ
  let P := (cutPairs A).filter fun p => translate p x ∈ D
  let a : AxisPair → ℝ := cutTerm (fun _ => 1) g x
  have hg (z : Q 9) (hz : z ∉ D) : g z = 0 := by
    simp [g, BalancedCriticalSpectrum.switchingVector, hz]
  have hAg (z : Q 9) (hz : z ∉ D) : weightedLinear (fun _ => 1) g z = 0 := by
    rw [Q9SignedContactCells.unit_weight]
    calc
      _ = (3 : ℝ) * g z :=
        congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) D σ hregular hσ) z
      _ = 0 := by rw [hg z hz, mul_zero]
  have hsum : ∑ p ∈ P, a p = 0 := by
    calc
      _ = ∑ p ∈ cutPairs A, a p := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro p hp hpP
        have hpD : translate p x ∉ D := fun h =>
          hpP (Finset.mem_filter.mpr ⟨hp, h⟩)
        simp [a, cutTerm, hg _ hpD]
      _ = 0 := weighted_cut_row A hsep hx hg hAg
  change Even P.card
  refine signed_sum_even P a ?_ hsum
  intro p hp
  have hpD : translate p x ∈ D := (Finset.mem_filter.mp hp).2
  have habs : |a p| = 1 := by
    change |cutTerm (fun _ => 1) g x p| = 1
    rw [abs_cutTerm (w := fun _ => 1) (fun _ => zero_lt_one)]
    rcases hσ.1 _ hpD with h | h <;>
      simp [g, BalancedCriticalSpectrum.switchingVector, hpD, h]
  rcases le_total 0 (a p) with h | h
  · left
    simpa only [abs_of_nonneg h] using habs
  · right
    rw [abs_of_nonpos h] at habs
    linarith only [habs]

open Classical in
/-- With at most three global crossing masks, every incident endpoint has
exactly two crossing contacts. -/
theorem crossing_contact_degree_two_of_small_cut
    {C D : Finset (Q 9)} {b : Bool} (A : Finset (Fin 9))
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hregular : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced D) {x : Q 9} (hx : x ∈ C) (hxb : parity x = b)
    (hcard : (cutMasks C D b A).card ≤ 3)
    (hcontact : ((A.product (Finset.univ \ A)).filter
      fun p => flip (flip x p.1) p.2 ∈ D).Nonempty) :
    ((A.product (Finset.univ \ A)).filter
      fun p => flip (flip x p.1) p.2 ∈ D).card = 2 := by
  let P := (cutPairs A).filter fun p => translate p x ∈ D
  change P.card = 2
  have hle : P.card ≤ (cutMasks C D b A).card := by
    apply Finset.card_le_card_of_injOn mask
    · intro p hp
      have hm := Finset.mem_filter.mp hp
      exact mask_mem_of_contact hm.1 hx hxb hm.2
    · intro p hp q hq he
      exact mask_injOn A (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have hpositive : 0 < P.card := Finset.card_pos.mpr hcontact
  obtain ⟨k, hk⟩ := even_crossing_contact_degree A hsep hregular hbalanced hx
  change P.card = k + k at hk
  omega

open Classical in
private theorem two_contact_row
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    {w : Fin 9 → ℝ} {g : Q 9 → ℝ} {x : Q 9} {p q : AxisPair}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hregular : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced D) (hx : x ∈ C) (hxb : parity x = b)
    (hcard : (cutMasks C D b A).card ≤ 3)
    (hg : ∀ z ∉ D, g z = 0) (hAg : ∀ z ∉ D, weightedLinear w g z = 0)
    (hp : p ∈ cutPairs A) (hq : q ∈ cutPairs A) (hpq : p ≠ q)
    (hpx : translate p x ∈ D) (hqx : translate q x ∈ D) :
    cutTerm w g x p + cutTerm w g x q = 0 := by
  classical
  let P := (cutPairs A).filter fun r => translate r x ∈ D
  have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hp, hpx⟩
  have hqP : q ∈ P := Finset.mem_filter.mpr ⟨hq, hqx⟩
  have hP : P.card = 2 :=
    crossing_contact_degree_two_of_small_cut A hsep hregular hbalanced hx hxb hcard ⟨p, hpP⟩
  have heq : ({p, q} : Finset AxisPair) = P :=
    Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hpP (Finset.singleton_subset_iff.mpr hqP))
      (by rw [hP, Finset.card_pair hpq])
  have hsum : ∑ r ∈ P, cutTerm w g x r = 0 := by
    calc
      _ = ∑ r ∈ cutPairs A, cutTerm w g x r := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro r hr hrP
        have hrD : translate r x ∉ D := fun hrD =>
          hrP (Finset.mem_filter.mpr ⟨hr, hrD⟩)
        simp [cutTerm, hg _ hrD]
      _ = 0 := weighted_cut_row A hsep hx hg hAg
  simpa only [← heq, Finset.sum_pair hpq] using hsum

open Classical in
private theorem no_alternating_square_of_small_cut
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {x : Q 9} {p q : AxisPair}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hx : x ∈ C) (hxb : parity x = b) (hcard : (cutMasks C D b A).card ≤ 3)
    (hp : p ∈ cutPairs A) (hq : q ∈ cutPairs A) (hpq : p ≠ q)
    (hpx : translate p x ∈ D) (hqx : translate q x ∈ D) :
    translate q (translate p x) ∉ C := by
  classical
  intro hOpp
  have hmask : mask p ≠ mask q := fun he => hpq (mask_injOn A hp hq he)
  have hsub : ¬ mask p ⊆ mask q := by
    intro h
    apply hmask
    exact Finset.eq_of_subset_of_card_le h (by
      simp only [mask, Finset.card_pair (axes_ne hp), Finset.card_pair (axes_ne hq), le_refl])
  have haxis : ∃ i ∈ mask p, i ∉ mask q := by
    by_contra h
    apply hsub
    intro i hi
    by_contra hq'
    exact h ⟨i, hi, hq'⟩
  obtain ⟨i, hi, hi'⟩ := haxis
  let w : Fin 9 → ℝ := fun j => if j = i then 2 else 1
  have hw (j : Fin 9) : 0 < w j := by
    dsimp [w]
    split <;> norm_num
  obtain ⟨g, hg, hAg⟩ :=
    exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD w hw (hdetD w) b
  have hgout (z : Q 9) (hz : z ∉ D) : g z = 0 := by
    by_contra hn
    exact hz ((hg z).mp hn).1
  have hwP : w p.1 * w p.2 = 2 := by
    simpa only [hi, ite_true] using weight_product i (axes_ne hp)
  have hwQ : w q.1 * w q.2 = 1 := by
    simpa only [hi', ite_false] using weight_product i (axes_ne hq)
  let z := translate q (translate p x)
  have hzp : translate p z = translate q x := by
    change translate p (translate q (translate p x)) = translate q x
    rw [translate_comm p q, translate_involution]
  have hzq : translate q z = translate p x := translate_involution q (translate p x)
  have hzb : parity z = b := (parity_translate q _).trans ((parity_translate p _).trans hxb)
  exact alternating_square_impossible hw hwP hwQ
    ((hg _).mpr ⟨hpx, (parity_translate p _).trans hxb⟩)
    (two_contact_row hsep hrD hbD hx hxb hcard hgout hAg hp hq hpq hpx hqx)
    (two_contact_row hsep hrD hbD hOpp hzb hcard hgout hAg hp hq hpq
      (hzp.symm ▸ hqx) (hzq.symm ▸ hpx))

open Classical in
private theorem other_contact_of_three_mask_cut
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {x : Q 9}
    {p q r : AxisPair}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D) (hx : x ∈ C) (hxb : parity x = b)
    (hp : p ∈ cutPairs A) (hq : q ∈ cutPairs A) (hr : r ∈ cutPairs A)
    (hcut : cutMasks C D b A = {mask p, mask q, mask r})
    (hpx : translate p x ∈ D) :
    translate q x ∈ D ∨ translate r x ∈ D := by
  classical
  let P := (cutPairs A).filter fun s => translate s x ∈ D
  have hcard : (cutMasks C D b A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hp, hpx⟩
  have hP : P.card = 2 :=
    crossing_contact_degree_two_of_small_cut A hsep hrD hbD hx hxb hcard ⟨p, hpP⟩
  obtain ⟨s, hs, hsp⟩ := Finset.exists_mem_ne (show 1 < P.card by omega) p
  obtain ⟨hsA, hsD⟩ := Finset.mem_filter.mp hs
  have hsCut := mask_mem_of_contact hsA hx hxb hsD
  rw [hcut, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hsCut
  rcases hsCut with he | he | he
  · exact (hsp (mask_injOn A hsA hp he)).elim
  · exact Or.inl (mask_injOn A hsA hq he ▸ hsD)
  · exact Or.inr (mask_injOn A hsA hr he ▸ hsD)

open Classical in
private theorem transport_from_companion
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {x : Q 9}
    {p q r : AxisPair}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hx : x ∈ C) (hxb : parity x = b)
    (hp : p ∈ cutPairs A) (hq : q ∈ cutPairs A) (hr : r ∈ cutPairs A)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A = {mask p, mask q, mask r})
    (hpx : translate p x ∈ D) (hqx : translate q x ∈ D) :
    translate q (translate r x) ∈ C ∧
      translate p (translate q (translate r x)) ∈ D := by
  have hsep' (u : Q 9) (hu : u ∈ D) (v : Q 9) (hv : v ∈ C) :
      2 ≤ hammingDist u v := by
    rw [hammingDist_comm]
    exact hsep v hv u hu
  have hcut' : cutMasks D C b A = {mask p, mask q, mask r} :=
    (cutMasks_swap D C b A).trans hcut
  have hcard : (cutMasks C D b A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  have hsquare {z : Q 9} {s t : AxisPair} :=
    @no_alternating_square_of_small_cut C D b A z s t hsep hrD hcD hbD hdetD
  let y := translate p x
  have hyb : parity y = b := (parity_translate p _).trans hxb
  have hyp : translate p y ∈ C := translate_involution p x ▸ hx
  have hyr : translate r y ∈ C :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep' hrC hbC hpx hyb hp hq hr hcut' hyp)
      (hsquare hx hxb hcard hp hq hpq hpx hqx)
  let z := translate r y
  have hzb : parity z = b := (parity_translate r _).trans hyb
  have hzr : translate r z ∈ D := translate_involution r y ▸ hpx
  have hzp : translate p z ∉ D := by
    intro h
    exact hsquare hyr hzb hcard hr hp hpr.symm hzr h
      ((congrArg (translate p) (translate_involution r y)).symm ▸ hyp)
  have hcutR : cutMasks C D b A = {mask r, mask p, mask q} := by
    rw [hcut]
    ext s
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hzq : translate q z ∈ D :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep hrD hbD hyr hzb hr hp hq hcutR hzr) hzp
  let v := translate q z
  have hvb : parity v = b := (parity_translate q _).trans hzb
  have hvq : translate q v ∈ C := translate_involution q z ▸ hyr
  have hcutQ : cutMasks D C b A = {mask q, mask p, mask r} := by
    rw [hcut', Finset.insert_comm (mask p) (mask q)]
  have hvp : translate p v ∈ C :=
    Or.resolve_right (other_contact_of_three_mask_cut hsep' hrC hbC hzq hvb hq hp hr hcutQ hvq)
      (hsquare hyr hzb hcard hq hr hqr hzq hzr)
  have hv : v = translate p (translate q (translate r x)) := by
    change translate q (translate r (translate p x)) = _
    rw [translate_comm r p, translate_comm q p]
  rw [hv, translate_involution] at hvp
  exact ⟨hvp, hv ▸ hzq⟩

open Classical in
/-- If an axis cut has precisely the three indicated crossing masks, each contact
fibre is invariant under the product of the other two translations. -/
theorem three_mask_cut_preserves_contact_fibre
    {C D : Finset (Q 9)} {b : Bool} (A : Finset (Fin 9))
    (p q r : Fin 9 × Fin 9)
    (hp : p.1 ∈ A ∧ p.2 ∉ A) (hq : q.1 ∈ A ∧ q.2 ∉ A)
    (hr : r.1 ∈ A ∧ r.2 ∉ A) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    {x : Q 9} (hx : x ∈ C) (hxb : parity x = b) (hpx : flip (flip x p.1) p.2 ∈ D) :
    let y := flip (flip (flip (flip x r.1) r.2) q.1) q.2
    y ∈ C ∧ parity y = b ∧ flip (flip y p.1) p.2 ∈ D := by
  have hpA : p ∈ cutPairs A :=
    Finset.mem_product.mpr ⟨hp.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp.2⟩⟩
  have hqA : q ∈ cutPairs A :=
    Finset.mem_product.mpr ⟨hq.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hq.2⟩⟩
  have hrA : r ∈ cutPairs A :=
    Finset.mem_product.mpr ⟨hr.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hr.2⟩⟩
  change translate q (translate r x) ∈ C ∧ parity (translate q (translate r x)) = b ∧
    translate p (translate q (translate r x)) ∈ D
  have hyb : parity (translate q (translate r x)) = b :=
    (parity_translate q _).trans ((parity_translate r _).trans hxb)
  rcases other_contact_of_three_mask_cut hsep hrD hbD hx hxb hpA hqA hrA hcut hpx with h | h
  · obtain ⟨hy, hpY⟩ := transport_from_companion hsep hrC hrD hcD hbC hbD hdetD
      hx hxb hpA hqA hrA hpq hpr hqr hcut hpx h
    exact ⟨hy, hyb, hpY⟩
  · have hcut' : cutMasks C D b A = {mask p, mask r, mask q} := by
      rw [show cutMasks C D b A = {mask p, mask q, mask r} from hcut,
        Finset.pair_comm (mask q) (mask r)]
    obtain ⟨hy, hpY⟩ := transport_from_companion hsep hrC hrD hcD hbC hbD hdetD
      hx hxb hpA hrA hqA hpr hpq hqr.symm hcut' hpx h
    rw [translate_comm r q] at hy hpY
    exact ⟨hy, hyb, hpY⟩

open Classical in
/-- Two cuts sharing the mask `{i,a}` can force the mask `{i,l}`.
Their shifts are respectively `{j,k}` and `{a,k,l,j}`, so their product
flips exactly `a,l`. Composing with the shared mask cancels `a`. -/
theorem two_three_mask_cuts_force_contact
    {C D : Finset (Q 9)} {b : Bool} {A B : Finset (Fin 9)}
    {i a j k l : Fin 9}
    (hiA : i ∈ A) (haA : a ∉ A) (hjA : j ∉ A) (hkA : k ∉ A)
    (haB : a ∈ B) (hlB : l ∈ B) (hiB : i ∉ B) (hjB : j ∉ B) (hkB : k ∉ B)
    (hjk : j ≠ k)
    (hcutA : cutMasks C D b A = {{i, a}, {i, j}, {i, k}})
    (hcutB : cutMasks C D b B = {{a, i}, {l, j}, {a, k}})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    ({i, l} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  classical
  have hai : i ≠ a := fun h => haA (h ▸ hiA)
  have haj : a ≠ j := fun h => hjB (h ▸ haB)
  have hak : a ≠ k := fun h => hkB (h ▸ haB)
  have hij : i ≠ j := fun h => hjA (h ▸ hiA)
  have hik : i ≠ k := fun h => hkA (h ▸ hiA)
  have hil : i ≠ l := fun h => hiB (h.symm ▸ hlB)
  have hpA : (i, a) ∈ cutPairs A :=
    Finset.mem_product.mpr ⟨hiA, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haA⟩⟩
  obtain ⟨x, hx, hxb, hpx⟩ := contact_of_mask hpA (show mask (i, a) ∈ cutMasks C D b A by
    rw [hcutA]
    simp [mask])
  let y := flip (flip (flip (flip x i) k) i) j
  have hy : y ∈ C ∧ parity y = b ∧ flip (flip y a) i ∈ D := by
    have h := three_mask_cut_preserves_contact_fibre A (i, a) (i, j) (i, k)
      ⟨hiA, haA⟩ ⟨hiA, hjA⟩ ⟨hiA, hkA⟩
      (fun he => haj (congrArg Prod.snd he)) (fun he => hak (congrArg Prod.snd he))
      (fun he => hjk (congrArg Prod.snd he)) hcutA hsep hrC hrD hcD hbC hbD hdetD hx hxb hpx
    exact ⟨h.1, h.2.1, (flip_comm y i a) ▸ h.2.2⟩
  let z := flip (flip (flip (flip y a) k) l) j
  have hz : z ∈ C ∧ parity z = b ∧ flip (flip z a) i ∈ D :=
    three_mask_cut_preserves_contact_fibre B (a, i) (l, j) (a, k)
      ⟨haB, hiB⟩ ⟨hlB, hjB⟩ ⟨haB, hkB⟩
      (fun he => hij (congrArg Prod.snd he)) (fun he => hik (congrArg Prod.snd he))
      (fun he => hjk (congrArg Prod.snd he)) hcutB hsep hrC hrD hcD hbC hbD hdetD hy.1 hy.2.1 hy.2.2
  have hzEq : flip (flip z a) i = flip (flip x i) l := by
    dsimp [z, y]
    rw [flip_comm (flip x i) k i, BalancedCriticalSpectrum.flip_flip,
      flip_comm (flip x k) j a, flip_comm (flip (flip x k) a) j k,
      flip_comm x k a, BalancedCriticalSpectrum.flip_flip,
      flip_comm (flip (flip x a) j) l j, BalancedCriticalSpectrum.flip_flip,
      flip_comm x a l, BalancedCriticalSpectrum.flip_flip, flip_comm x l i]
  have hdiff := diff_pair x hil
  have hdist : hammingDist x (flip (flip x i) l) = 2 := by
    change (differingAxes x (flip (flip x i) l)).card = 2
    rw [hdiff, Finset.card_pair hil]
  exact mem_minimumDisplacements.mpr ⟨x, hx, _, hzEq ▸ hz.2.2, hxb, hdist, hdiff⟩

#print axioms every_nonempty_axis_cut_has_three_masks
#print axioms even_crossing_contact_degree
#print axioms crossing_contact_degree_two_of_small_cut
#print axioms three_mask_cut_preserves_contact_fibre
#print axioms two_three_mask_cuts_force_contact

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut
