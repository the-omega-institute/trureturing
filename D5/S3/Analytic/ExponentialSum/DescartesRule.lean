/- GID: D5/S3/Analytic/ExponentialSum/DescartesRule
   generality: G
   mirror-B: D5/B/S3/Analytic/ExponentialSum/DescartesRule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.DSlope, mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Rolle, mathlib/module/Mathlib.Analysis.SpecialFunctions.ExpDeriv, mathlib/module/Mathlib.Data.List.SignVariations, mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Data.Set.Finite.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Descartes bounds for real exponential sums with decreasing exponents. -/

import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.List.SignVariations
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Real exponential sums and finite zero counting. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset Set Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.ExponentialSum.DescartesRule

/-- A real exponential sum, indexed in decreasing exponent order. -/
def exponentialSum {N : ℕ} (a μ : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ i, a i * Real.exp (μ i * t)

private def value (l : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (l.map fun p => p.1 * Real.exp (p.2 * t)).sum

private def variation (l : List (ℝ × ℝ)) : ℕ := (l.map Prod.fst).signVariations

private def shifted (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * (p.2 - c), p.2 - c)

private lemma shift_sign_pos {c : ℝ} {p : ℝ × ℝ} (h : c < p.2) :
    SignType.sign (shifted c p).1 = SignType.sign p.1 := by
  simp [shifted, sign_mul, sign_pos (sub_pos.mpr h)]

private lemma shift_sign_neg {c : ℝ} {p : ℝ × ℝ} (h : p.2 < c) :
    SignType.sign (shifted c p).1 = -SignType.sign p.1 := by
  rw [shifted, sign_mul, sign_neg (sub_neg.mpr h)]
  cases SignType.sign p.1 <;> rfl

private lemma variation_negative {c : ℝ} {l : List (ℝ × ℝ)}
    (h : ∀ p ∈ l, p.2 < c) : variation (l.map (shifted c)) = variation l := by
  have he : l.map (fun p => SignType.sign (shifted c p).1) =
      (l.map Prod.fst).map (fun a => SignType.sign (-a)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun p hp => by
      simpa only [Function.comp_apply, Left.sign_neg] using shift_sign_neg (h p hp)
  calc
    variation (l.map (shifted c)) = ((l.map Prod.fst).map (fun a => -a)).signVariations := by
      apply List.signVariations_congr
      simpa only [List.map_map, Function.comp_def] using he
    _ = variation l := List.signVariations_map_of_sign_eq_neg Left.sign_neg _

private lemma pivot {l : List (ℝ × ℝ)}
    (hs : l.Pairwise (fun p q => q.2 < p.2))
    (hn : ∀ p ∈ l, p.1 ≠ 0) (hv : 0 < variation l) :
    ∃ c, (∀ p ∈ l, p.2 ≠ c) ∧
      variation (l.map (shifted c)) + 1 = variation l ∧
      (∀ p, l.head? = some p → c < p.2) := by
  induction l with
  | nil => simp [variation] at hv
  | cons p l ih =>
    cases l with
    | nil => simp [variation] at hv
    | cons q l =>
      have hp := hn p (by simp)
      have hq := hn q (by simp)
      have htail := (List.pairwise_cons.mp hs).2
      have hpq : q.2 < p.2 := (List.pairwise_cons.mp hs).1 q (by simp)
      have hrec := List.signVariations_cons_cons_of_ne_zero (l.map Prod.fst) hp hq
      change variation (p :: q :: l) = variation (q :: l) + _ at hrec
      by_cases he : SignType.sign p.1 = SignType.sign q.1
      · have hvt : 0 < variation (q :: l) := by rw [hrec, ite_eq_left he, add_zero] at hv; exact hv
        obtain ⟨c, hc, hcvar, hhead⟩ := ih htail (fun x hx => hn x (by simp [hx])) hvt
        have hcq : c < q.2 := hhead q rfl
        have hcp : c < p.2 := hcq.trans hpq
        refine ⟨c, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ne_of_gt hcp
          · exact hc x hx
        · have hps : (shifted c p).1 ≠ 0 := mul_ne_zero hp (sub_ne_zero.mpr hcp.ne')
          have hqs : (shifted c q).1 ≠ 0 := mul_ne_zero hq (sub_ne_zero.mpr hcq.ne')
          have hes : SignType.sign (shifted c p).1 = SignType.sign (shifted c q).1 := by
            rw [shift_sign_pos hcp, shift_sign_pos hcq, he]
          simp only [variation, List.map_cons] at hrec hcvar ⊢
          rw [List.signVariations_cons_cons_of_ne_zero _ hps hqs, ite_eq_left hes, add_zero,
            hcvar, hrec, ite_eq_left he, add_zero]
        · intro x hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact hcp
      · let c := (p.2 + q.2) / 2
        have hcp : c < p.2 := by dsimp [c]; linarith
        have hcq : q.2 < c := by dsimp [c]; linarith
        have hbelow : ∀ x ∈ q :: l, x.2 < c := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hcq
          · exact ((List.pairwise_cons.mp htail).1 x hx).trans hcq
        refine ⟨c, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hcp.ne'
          · exact (hbelow x hx).ne
        · have hps : (shifted c p).1 ≠ 0 := mul_ne_zero hp (sub_ne_zero.mpr hcp.ne')
          have hqs : (shifted c q).1 ≠ 0 := mul_ne_zero hq (sub_ne_zero.mpr hcq.ne)
          have hes : SignType.sign (shifted c p).1 = SignType.sign (shifted c q).1 := by
            rw [shift_sign_pos hcp, shift_sign_neg hcq]
            exact (sign_eq_sign_or_eq_neg hp hq).resolve_left he
          have ht := variation_negative hbelow
          simp only [variation, List.map_cons] at hrec ht ⊢
          rw [List.signVariations_cons_cons_of_ne_zero _ hps hqs, ite_eq_left hes, add_zero,
            ht, hrec, ite_eq_right he]
        · intro x hx
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          exact hcp

private lemma zero_variation_sign {p : ℝ × ℝ} {l : List (ℝ × ℝ)}
    (hn : ∀ q ∈ p :: l, q.1 ≠ 0) (hv : variation (p :: l) = 0) (t : ℝ) :
    SignType.sign (value (p :: l) t) = SignType.sign p.1 := by
  induction l generalizing p with
  | nil => simp [value, sign_mul, sign_pos (Real.exp_pos _)]
  | cons q l ih =>
    have hp := hn p (by simp)
    have hq := hn q (by simp)
    have he := List.signVariations_cons_cons_of_ne_zero (l.map Prod.fst) hp hq
    change variation (p :: q :: l) = variation (q :: l) + _ at he
    have hsame : SignType.sign p.1 = SignType.sign q.1 := by
      by_contra h
      simp [h, hv] at he
    have hvt : variation (q :: l) = 0 := by simpa [hv, hsame] using he.symm
    have ht := ih (fun x hx => hn x (by simp [hx])) hvt
    have hterm : SignType.sign (p.1 * Real.exp (p.2 * t)) = SignType.sign p.1 := by
      simp [sign_mul, sign_pos (Real.exp_pos _)]
    change SignType.sign (p.1 * Real.exp (p.2 * t) + value (q :: l) t) = _
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hpneg := sign_neg hneg
      have htneg : value (q :: l) t < 0 := sign_eq_neg_one_iff.mp (ht.trans (hsame.symm.trans hpneg))
      exact (sign_neg (add_neg (mul_neg_of_neg_of_pos hneg (Real.exp_pos _)) htneg)).trans hpneg.symm
    · have hppos := sign_pos hpos
      have htpos : 0 < value (q :: l) t := sign_eq_one_iff.mp (ht.trans (hsame.symm.trans hppos))
      exact (sign_pos (add_pos (mul_pos hpos (Real.exp_pos _)) htpos)).trans hppos.symm

private def normalized (c : ℝ) (l : List (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (l.map fun p => p.1 * Real.exp ((p.2 - c) * t)).sum

private lemma normalized_eq (c : ℝ) (l : List (ℝ × ℝ)) (t : ℝ) :
    normalized c l t = Real.exp (-c * t) * value l t := by
  induction l with
  | nil => simp [normalized, value]
  | cons p l ih =>
    simp only [normalized, value, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, show (p.2 - c) * t = -c * t + p.2 * t by ring, Real.exp_add]
    ring

private lemma normalized_deriv (c : ℝ) (l : List (ℝ × ℝ)) (t : ℝ) :
    HasDerivAt (normalized c l) (value (l.map (shifted c)) t) t := by
  induction l with
  | nil =>
    change HasDerivAt (fun _ => (0 : ℝ)) 0 t
    exact hasDerivAt_const t 0
  | cons p l ih =>
    have ht := (((hasDerivAt_id t).const_mul (p.2-c)).exp).const_mul p.1
    have h := ht.add ih
    convert h using 1
    · rfl
    · simp only [value, List.map_cons, List.map_map, List.sum_cons, shifted, id_eq]
      ring

private lemma finite_zeros {f : ℝ → ℝ} {b : ℕ}
    (h : ∀ Z : Finset ℝ, (∀ x ∈ Z, f x = 0) → Z.card ≤ b) :
    {x | f x = 0}.Finite := by
  by_contra hi
  obtain ⟨Z, hZ, hc⟩ := Set.Infinite.exists_subset_card_eq hi (b+1)
  have := h Z (fun x hx => hZ hx)
  omega

private lemma zero_bound_list (l : List (ℝ × ℝ))
    (hs : l.Pairwise (fun p q => q.2 < p.2))
    (hn : ∀ p ∈ l, p.1 ≠ 0) (hne : l ≠ [])
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, value l t = 0) :
    Z.card ≤ variation l := by
  suffices H : ∀ k, ∀ l : List (ℝ × ℝ), variation l = k →
      l.Pairwise (fun p q => q.2 < p.2) →
      (∀ p ∈ l, p.1 ≠ 0) → l ≠ [] →
      ∀ Z : Finset ℝ, (∀ t ∈ Z, value l t = 0) → Z.card ≤ k from
    H _ l rfl hs hn hne Z hZ
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro l hv hs hn hne Z hZ
    by_cases hk : k = 0
    · rw [hk] at hv ⊢
      cases l with
      | nil => exact (hne rfl).elim
      | cons p l =>
        have he : Z = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          have hsign := zero_variation_sign hn hv t
          rw [hZ t ht, sign_zero] at hsign
          exact (hn p (by simp)) (sign_eq_zero_iff.mp hsign.symm)
        simp [he]
    · obtain ⟨c, hc, hcv, _⟩ := pivot hs hn (by omega)
      have hlt : variation (l.map (shifted c)) < k := by omega
      have hsort : (l.map (shifted c)).Pairwise (fun p q => q.2 < p.2) := by
        rw [List.pairwise_map]
        exact hs.imp (fun {_ _} hpq => by dsimp [shifted]; linarith)
      have hn' : ∀ p ∈ l.map (shifted c), p.1 ≠ 0 := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact mul_ne_zero (hn q hq) (sub_ne_zero.mpr (hc q hq))
      have hb := ih _ hlt _ rfl hsort hn' (by simpa using hne)
      have hf := finite_zeros hb
      let D := hf.toFinset
      have hDc : D.card ≤ variation (l.map (shifted c)) := hb D (by simpa [D] using hf.mem_toFinset.mp)
      have hrol : Z.card ≤ D.card + 1 := by
        apply Finset.card_le_of_interleaved
        intro x hx y hy hxy _
        have hz : normalized c l x = normalized c l y := by
          simp [normalized_eq, hZ x hx, hZ y hy]
        have hcont : Continuous (normalized c l) :=
          continuous_iff_continuousAt.mpr fun t => (normalized_deriv c l t).continuousAt
        obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero hxy hcont.continuousOn hz
          (fun t _ => normalized_deriv c l t)
        exact ⟨t, by simpa [D] using hdt, ht⟩
      omega

private lemma value_differentiable (l : List (ℝ × ℝ)) : Differentiable ℝ (value l) := by
  intro t
  have h := (normalized_deriv 0 l t).differentiableAt
  have he : normalized 0 l = value l := by
    ext x
    simp [normalized, value]
  rw [he] at h
  exact h

private lemma weighted_bound_list (l : List (ℝ × ℝ))
    (hs : l.Pairwise (fun p q => q.2 < p.2))
    (hn : ∀ p ∈ l, p.1 ≠ 0) (hne : l ≠ [])
    (Z S : Finset ℝ) (hZ : ∀ t ∈ Z, value l t = 0)
    (hS : S ⊆ Z) (hdS : ∀ t ∈ S, deriv (value l) t = 0) :
    Z.card + S.card ≤ variation l := by
  classical
  by_cases hv : variation l = 0
  · have hcard := zero_bound_list l hs hn hne Z hZ
    have hze : Z = ∅ := Finset.card_eq_zero.mp (by omega)
    have hse : S = ∅ := Finset.subset_empty.mp (hze ▸ hS)
    simp [hze, hse]
  · obtain ⟨c, hc, hcv, _⟩ := pivot hs hn (Nat.pos_of_ne_zero hv)
    have hsort : (l.map (shifted c)).Pairwise (fun p q => q.2 < p.2) := by
      rw [List.pairwise_map]
      exact hs.imp (fun {_ _} hpq => by dsimp [shifted]; linarith)
    have hn' : ∀ p ∈ l.map (shifted c), p.1 ≠ 0 := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact mul_ne_zero (hn q hq) (sub_ne_zero.mpr (hc q hq))
    have hb := zero_bound_list (l.map (shifted c)) hsort hn' (by simpa using hne)
    have hf := finite_zeros hb
    let D := hf.toFinset
    have hDc : D.card ≤ variation (l.map (shifted c)) := hb D (by simp [D])
    have hcont : Continuous (normalized c l) :=
      continuous_iff_continuousAt.mpr fun t => (normalized_deriv c l t).continuousAt
    have hrol : Z.card ≤ (D \ Z).card + 1 := by
      apply Finset.card_le_sdiff_of_interleaved
      intro x hx y hy hxy _
      have hz : normalized c l x = normalized c l y := by
        simp [normalized_eq, hZ x hx, hZ y hy]
      obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero hxy hcont.continuousOn hz
        (fun t _ => normalized_deriv c l t)
      exact ⟨t, by simpa [D] using hdt, ht⟩
    have hsub : S ⊆ D ∩ Z := by
      intro t ht
      refine Finset.mem_inter.mpr ⟨?_, hS ht⟩
      have hd := (((hasDerivAt_id t).const_mul (-c)).exp).mul
        ((value_differentiable l t).hasDerivAt)
      have he : (fun x => Real.exp (-c * id x) * value l x) = normalized c l := by
        ext x
        exact (normalized_eq c l x).symm
      change HasDerivAt (fun x => Real.exp (-c * id x) * value l x) _ t at hd
      rw [he] at hd
      have heq := hd.unique (normalized_deriv c l t)
      simp only [hZ t (hS ht), hdS t ht, mul_zero, add_zero] at heq
      simpa [D] using heq.symm
    have hsc := Finset.card_le_card hsub
    have hpart := Finset.card_sdiff_add_card_inter D Z
    omega

private def nonzeroTerms (l : List (ℝ × ℝ)) : List (ℝ × ℝ) :=
  l.filter (fun p => !decide (p.1 = 0))

private lemma nonzeroTerms_value (l : List (ℝ × ℝ)) (t : ℝ) :
    value (nonzeroTerms l) t = value l t := by
  induction l with
  | nil => simp [nonzeroTerms, value]
  | cons p l ih =>
    by_cases hp : p.1 = 0 <;> simp [nonzeroTerms, value, hp] at ih ⊢ <;> exact ih

private lemma nonzeroTerms_variation (l : List (ℝ × ℝ)) :
    variation (nonzeroTerms l) = variation l := by
  have he : (nonzeroTerms l).map Prod.fst =
      (l.map Prod.fst).filter (fun a => !decide (a = 0)) := by
    rw [List.filter_map]
    rfl
  change ((nonzeroTerms l).map Prod.fst).signVariations = _
  rw [he]
  exact List.signVariations_filter_ne_zero (l.map Prod.fst)

/-- Distinct real zeros are bounded by the sign variations of the coefficients,
with zero coefficients ignored. -/
theorem zero_bound {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (ha : ∃ i, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0) :
    Z.card ≤ (List.ofFn a).signVariations := by
  classical
  let l := List.ofFn (fun i => (a i, μ i))
  have hsort : l.Pairwise (fun p q => q.2 < p.2) :=
    List.pairwise_ofFn.mpr fun _ _ h => hμ h
  have hs : (nonzeroTerms l).Pairwise (fun p q => q.2 < p.2) :=
    hsort.filter _
  have hn : ∀ p ∈ nonzeroTerms l, p.1 ≠ 0 := by
    intro p hp
    simpa [nonzeroTerms] using (List.mem_filter.mp hp).2
  have hne : nonzeroTerms l ≠ [] := by
    obtain ⟨i, hi⟩ := ha
    have hm : (a i, μ i) ∈ nonzeroTerms l := by
      simp only [nonzeroTerms, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
    exact List.ne_nil_of_mem hm
  have he : ∀ t, value l t = exponentialSum a μ t := by
    intro t
    simp [l, value, exponentialSum, List.map_ofFn, List.sum_ofFn]
  have hb := zero_bound_list (nonzeroTerms l) hs hn hne Z
    (fun t ht => by rw [nonzeroTerms_value, he]; exact hZ t ht)
  rw [nonzeroTerms_variation] at hb
  simpa only [variation, l, List.map_ofFn, Function.comp_def] using hb

private lemma weighted_bound {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (ha : ∃ i, a i ≠ 0) (Z S : Finset ℝ)
    (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0)
    (hS : S ⊆ Z) (hdS : ∀ t ∈ S, deriv (exponentialSum a μ) t = 0) :
    Z.card + S.card ≤ (List.ofFn a).signVariations := by
  classical
  let l := List.ofFn (fun i => (a i, μ i))
  have hsort : l.Pairwise (fun p q => q.2 < p.2) :=
    List.pairwise_ofFn.mpr fun _ _ h => hμ h
  have hs : (nonzeroTerms l).Pairwise (fun p q => q.2 < p.2) := hsort.filter _
  have hn : ∀ p ∈ nonzeroTerms l, p.1 ≠ 0 := by
    intro p hp
    simpa [nonzeroTerms] using (List.mem_filter.mp hp).2
  have hne : nonzeroTerms l ≠ [] := by
    obtain ⟨i, hi⟩ := ha
    have hm : (a i, μ i) ∈ nonzeroTerms l := by
      simp only [nonzeroTerms, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
    exact List.ne_nil_of_mem hm
  have he : value (nonzeroTerms l) = exponentialSum a μ := by
    ext t
    rw [nonzeroTerms_value]
    simp [l, value, exponentialSum, List.map_ofFn, List.sum_ofFn]
  have hb := weighted_bound_list (nonzeroTerms l) hs hn hne Z S
    (by simpa only [he] using hZ) hS (by simpa only [he] using hdS)
  rw [nonzeroTerms_variation] at hb
  simpa only [variation, l, List.map_ofFn, Function.comp_def] using hb

/-- A uniform strict sign reversal on the two sides of a zero. -/
def ChangesSign (F : ℝ → ℝ) (z : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Ioo (z-ε) z, ∀ s ∈ Ioo z (z+ε), F t * F s < 0

private lemma changesSign_of_deriv {F : ℝ → ℝ} {z : ℝ}
    (hz : F z = 0) (hd : DifferentiableAt ℝ F z) (hn : deriv F z ≠ 0) :
    ChangesSign F z := by
  have hc := continuousAt_dslope_same.mpr hd
  have hf : ∀ t, (t-z) * dslope F z t = F t := by
    intro t
    simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hz t
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have he : ∀ᶠ t in 𝓝 z, dslope F z t < 0 :=
      hc.eventually (isOpen_Iio.mem_nhds (by simpa using hneg))
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨ε, hε, ?_⟩
    intro t ht u hu
    have ht' : dslope F z t < 0 := he (by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]; linarith [ht.1])
    have hu' : dslope F z u < 0 := he (by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hu.1)]; linarith [hu.2])
    rw [← hf t, ← hf u]
    exact mul_neg_of_pos_of_neg
      (mul_pos_of_neg_of_neg (sub_neg.mpr ht.2) ht')
      (mul_neg_of_pos_of_neg (sub_pos.mpr hu.1) hu')
  · have he : ∀ᶠ t in 𝓝 z, 0 < dslope F z t :=
      hc.eventually (isOpen_Ioi.mem_nhds (by simpa using hpos))
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨ε, hε, ?_⟩
    intro t ht u hu
    have ht' : 0 < dslope F z t := he (by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]; linarith [ht.1])
    have hu' : 0 < dslope F z u := he (by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hu.1)]; linarith [hu.2])
    rw [← hf t, ← hf u]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (sub_neg.mpr ht.2) ht')
      (mul_pos (sub_pos.mpr hu.1) hu')

private lemma exponentialSum_differentiable {N : ℕ} (a μ : Fin N → ℝ) :
    Differentiable ℝ (exponentialSum a μ) := by
  apply Differentiable.fun_sum
  intro i _
  exact (Real.differentiable_exp.comp ((differentiable_id).const_mul (μ i))).const_mul (a i)

/-- Zeros without a strict local sign reversal cost one additional variation. -/
theorem sign_crossing_bound {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (ha : ∃ i, a i ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0) :
    Z.card + (Z.filter (fun z => ¬ ChangesSign (exponentialSum a μ) z)).card ≤
      (List.ofFn a).signVariations := by
  classical
  apply weighted_bound a μ hμ ha Z _ hZ (Finset.filter_subset _ _)
  intro t ht
  have hn := (Finset.mem_filter.mp ht).2
  by_contra hd
  exact hn (changesSign_of_deriv (hZ t (Finset.mem_filter.mp ht).1)
    (exponentialSum_differentiable a μ t) hd)

private lemma sign_eq_prod_of_simple_roots
    (Z : Finset ℝ) (F : ℝ → ℝ) (hc : Continuous F)
    (hz : ∀ x, F x = 0 ↔ x ∈ Z)
    (hs : ∀ x ∈ Z, DifferentiableAt ℝ F x ∧ deriv F x ≠ 0)
    (hp : ∀ᶠ x in atTop, 0 < F x) :
    ∀ t, SignType.sign (F t) = SignType.sign (∏ z ∈ Z, (t-z)) := by
  classical
  induction Z using Finset.induction_on generalizing F with
  | empty =>
    intro t
    have hpos : 0 < F t := by
      by_contra! hnonpos
      obtain ⟨b, hb⟩ := hp.exists
      obtain ⟨x, hx⟩ := intermediate_value_univ₂ hc continuous_const hnonpos hb.le
      simpa using (hz x).mp hx
    simp [sign_pos hpos]
  | @insert z S hzS ih =>
    have hz0 : F z = 0 := (hz z).mpr (Finset.mem_insert_self _ _)
    have hzs := hs z (Finset.mem_insert_self _ _)
    let H := dslope F z
    have hfactor : ∀ t, (t-z) * H t = F t := by
      intro t
      simpa only [H, smul_eq_mul] using sub_smul_dslope_of_zero hz0 t
    have hHcont : Continuous H := continuous_iff_continuousAt.mpr (by
      intro t
      by_cases ht : t = z
      · subst t; exact continuousAt_dslope_same.mpr hzs.1
      · exact (continuousAt_dslope_of_ne ht).mpr hc.continuousAt)
    have hHzeros : ∀ t, H t = 0 ↔ t ∈ S := by
      intro t
      by_cases ht : t = z
      · subst t; simp [H, hzs.2, hzS]
      · have ht0 : t-z ≠ 0 := sub_ne_zero.mpr ht
        constructor
        · intro h
          have hFt : F t = 0 := by rw [← hfactor t, h, mul_zero]
          exact (Finset.mem_insert.mp ((hz t).mp hFt)).resolve_left ht
        · intro h
          have hFt := (hz t).mpr (Finset.mem_insert_of_mem h)
          exact (mul_eq_zero.mp ((hfactor t).trans hFt)).resolve_left ht0
    have hHsimple : ∀ t ∈ S, DifferentiableAt ℝ H t ∧ deriv H t ≠ 0 := by
      intro t ht
      have htz : t ≠ z := by intro h; subst t; exact hzS ht
      have hst := hs t (Finset.mem_insert_of_mem ht)
      have hd : DifferentiableAt ℝ H t :=
        (differentiableAt_dslope_of_ne htz).mpr hst.1
      refine ⟨hd, ?_⟩
      intro hzero
      have hdprod := ((hasDerivAt_id t).sub_const z).mul hd.hasDerivAt
      change HasDerivAt (fun x => (x-z)*H x) _ t at hdprod
      have hfun : (fun x => (x-z)*H x) = F := funext hfactor
      rw [hfun] at hdprod
      apply hst.2
      have htzero := (hHzeros t).mpr ht
      simpa [htzero, hzero] using hdprod.deriv
    have hHpos : ∀ᶠ t in atTop, 0 < H t := by
      filter_upwards [hp, eventually_gt_atTop z] with t ht htz
      have hprod : 0 < (t-z) * H t := by rwa [hfactor t]
      exact (mul_pos_iff_of_pos_left (sub_pos.mpr htz)).mp hprod
    intro t
    have hind := ih H hHcont hHzeros hHsimple hHpos t
    rw [← hfactor t, sign_mul, Finset.prod_insert hzS, sign_mul, hind]

private lemma eventually_positive {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (i : Fin N) (hi : 0 < a i) (hfirst : ∀ j, j < i → a j = 0) :
    ∀ᶠ t in atTop, 0 < exponentialSum a μ t := by
  have hterm : ∀ j : Fin N, Tendsto (fun t : ℝ => a j * Real.exp ((μ j - μ i) * t))
      atTop (𝓝 (if j = i then a i else 0)) := by
    intro j
    rcases lt_trichotomy j i with hj | rfl | hj
    · simp only [hfirst j hj, zero_mul, ite_eq_right (ne_of_lt hj)]
      exact tendsto_const_nhds
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => a i) atTop (𝓝 (a i)))
    · have he := Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr (hμ hj)))
      simpa only [mul_zero, ite_eq_right (ne_of_gt hj), Function.comp_apply, id_eq] using
        he.const_mul (a j)
  have hlim : Tendsto (fun t : ℝ => ∑ j : Fin N, a j * Real.exp ((μ j - μ i) * t))
      atTop (𝓝 (a i)) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => hterm j)
  have hevent := hlim.eventually (isOpen_Ioi.mem_nhds hi)
  filter_upwards [hevent] with t ht
  have he : (∑ j : Fin N, a j * Real.exp ((μ j - μ i) * t)) =
      Real.exp (-μ i * t) * exponentialSum a μ t := by
    rw [exponentialSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (μ j - μ i) * t = -μ i * t + μ j * t by ring, Real.exp_add]
    ring
  rw [he] at ht
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp ht

/-- When prescribed zeros exhaust the variation bound and the leading nonzero
coefficient is positive, the sum has exactly the sign of their monic product. -/
theorem exact_sign {N : ℕ} (a μ : Fin N → ℝ) (hμ : StrictAnti μ)
    (hlead : ∃ i, 0 < a i ∧ ∀ j, j < i → a j = 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, exponentialSum a μ t = 0)
    (hcard : Z.card = (List.ofFn a).signVariations) (t : ℝ) :
    SignType.sign (exponentialSum a μ t) = SignType.sign (∏ z ∈ Z, (t-z)) := by
  classical
  obtain ⟨i, hi, hfirst⟩ := hlead
  have ha : ∃ j, a j ≠ 0 := ⟨i, ne_of_gt hi⟩
  have hzeros : ∀ x, exponentialSum a μ x = 0 ↔ x ∈ Z := by
    intro x
    refine ⟨?_, hZ x⟩
    intro hx
    by_contra hn
    have hb := zero_bound a μ hμ ha (insert x Z) (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hZ y hy)
    rw [Finset.card_insert_of_notMem hn, hcard] at hb
    omega
  have hsimple : ∀ x ∈ Z, DifferentiableAt ℝ (exponentialSum a μ) x ∧
      deriv (exponentialSum a μ) x ≠ 0 := by
    intro x hx
    refine ⟨exponentialSum_differentiable a μ x, ?_⟩
    intro hdx
    have hb := weighted_bound a μ hμ ha Z {x} hZ
      (by simpa using hx) (by simpa using hdx)
    simp only [Finset.card_singleton, hcard] at hb
    omega
  exact sign_eq_prod_of_simple_roots Z (exponentialSum a μ)
    (exponentialSum_differentiable a μ).continuous hzeros hsimple
    (eventually_positive a μ hμ i hi hfirst) t

end D5.S3.Analytic.ExponentialSum.DescartesRule
