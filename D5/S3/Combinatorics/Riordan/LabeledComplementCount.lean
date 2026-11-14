/- GID: D5/S3/Combinatorics/Riordan/LabeledComplementCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Riordan/LabeledComplementCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labeled Riordan complement enumeration. -/

/-
admission_basis: open-problem-resolution (#26688; Proved)
escape_witness: none
Direct frozen dependencies:
  D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport.instCharPPowerSeriesF2OfNatNat
  declaration statement_id: sha256:983162df2ad497e786f8a1356c5ca234f2bb32140e908262f607f5c6fa58c3d2.
  Used by class_complement, classToUnitParams, classToUnitParams_injective,
  classToUnitParams_surjective, count_all, count_sum and result after helper inlining.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27284
The labels i : Fin n represent the source labels i.val + 1.
The parity expressions use the disclosed products 10 * 8^(k-1) and 3 * 8^k.
Coefficients lie in ZMod 2; truncations use AdjoinRoot of a power of Polynomial.X.
first_vector_card: proof_shape: bind-only; consumers: classified_card.
classified_card: proof_shape: bind-only; consumers: doubled_classified_card.
classR_zero: proof_shape: bind-only; consumers: class_complement, classToUnitParams.
classS_zero: proof_shape: bind-only; consumers: class_complement, classToUnitParams.
class_pair_injective: proof_shape: content; consumers: classToUnitParams_injective.
class_complement: proof_shape: content; consumers: classToUnitParams.
classToUnitParams_injective: proof_shape: content; consumers: count_all.
classToUnitParams_surjective: proof_shape: content; consumers: count_all.
doubled_classified_card: proof_shape: bind-only; consumers: count_all.
count_all: proof_shape: content; consumers: count_sum.
count_sum: proof_shape: content; consumers: result.
result: proof_shape: content; consumers: settling conclusion.
-/

import D5.S1.Recurrence.SquareRows.SquareExponentDyadicSupport
import D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra
import D5.S3.Combinatorics.Riordan.LabeledComplementClassification

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.Riordan.LabeledComplementCount

open D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra
open D5.S3.Combinatorics.Riordan.LabeledComplementClassification

open scoped BigOperators

private noncomputable def firstVectorEquiv (L k : ℕ) (hk : k < L) :
    {f : Fin L → (ZMod 2) // (∀ i : Fin L, i.val < k → f i = 0) ∧ f ⟨k, hk⟩ = 1} ≃
      (Fin (L - k - 1) → (ZMod 2)) where
  toFun f i := f.val ⟨k + 1 + i.val, by omega⟩
  invFun f := ⟨fun i => if h : i.val < k then 0 else if h' : i.val = k then 1
      else f ⟨i.val - k - 1, by omega⟩,
    ⟨by intro i hi; simp [hi], by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with hi he
    · exact (f.property.1 i hi).symm
    · have hei : i = ⟨k, hk⟩ := Fin.ext he
      simpa only [hei] using f.property.2.symm
    · have hei : (⟨k + 1 + (i.val - k - 1), by omega⟩ : Fin L) = i := by
        apply Fin.ext
        dsimp
        omega
      exact congrArg f.val hei
  right_inv f := by
    funext i
    dsimp
    simp only [show ¬k + 1 + i.val < k by omega,
      show ¬k + 1 + i.val = k by omega, ↓reduceDIte, ↓reduceIte]
    have hei : (⟨k + 1 + i.val - k - 1, by omega⟩ : Fin (L - k - 1)) = i := by
      apply Fin.ext
      dsimp
      omega
    exact congrArg f hei

private theorem first_vector_card (L k : ℕ) (hk : k < L) :
    Nat.card {f : Fin L → (ZMod 2) //
      (∀ i : Fin L, i.val < k → f i = 0) ∧ f ⟨k, hk⟩ = 1} = 2 ^ (L - k - 1) := by
  rw [Nat.card_congr (firstVectorEquiv L k hk), Nat.card_fun, Nat.card_fin]
  congr 1
  rw [Nat.card_eq_fintype_card, ZMod.card]

private def Classified (N : ℕ) := Unit ⊕
  (Σ d : Fin N,
    {r : Fin (N + 1) → (ZMod 2) //
      (∀ i : Fin (N + 1), i.val < N - d.val → r i = 0) ∧
        r ⟨N - d.val, by omega⟩ = 1} ×
    {s : Fin (N + 1) → (ZMod 2) //
      ∀ i : Fin (N + 1), i.val < N - d.val + (d.val + 2) / 2 → s i = 0})

private theorem classified_card (N : ℕ) :
    Nat.card (Classified N) = 1 + ∑ d ∈ Finset.range N, 2 ^ (d + (d + 1) / 2) := by
  classical
  unfold Classified
  rw [Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_unit, Nat.card_sigma]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.card_prod, first_vector_card, zero_prefix_card]
  · rw [← pow_add]
    congr 1
    have h := d.isLt
    omega
  · have h := d.isLt
    omega

private noncomputable def classR (N : ℕ) : Classified N → (Fin (N + 1) → (ZMod 2))
  | .inl _ => 0
  | .inr ⟨_, r, _⟩ => r.val

private noncomputable def classS (N : ℕ) : Classified N → (Fin (N + 1) → (ZMod 2))
  | .inl _ => 0
  | .inr ⟨_, _, s⟩ => s.val

private theorem classR_zero (N : ℕ) (c : Classified N) : classR N c 0 = 0 := by
  rcases c with c | ⟨d, r, s⟩
  · rfl
  · exact r.property.1 0 (by have h := d.isLt; dsimp; omega)

private theorem classS_zero (N : ℕ) (c : Classified N) : classS N c 0 = 0 := by
  rcases c with c | ⟨d, r, s⟩
  · rfl
  · exact s.property 0 (by have h := d.isLt; dsimp; omega)

private theorem class_pair_injective (N : ℕ) :
    Function.Injective (fun c : Classified N => (classR N c, classS N c)) := by
  intro c c' he
  have hr := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  rcases c with a | ⟨d, r, s⟩ <;> rcases c' with b | ⟨d', r', s'⟩
  · congr 1
  · have h := congrFun hr (⟨N - d'.val, by omega⟩ : Fin (N + 1))
    have hh := r'.property.2
    change 0 = r'.val _ at h
    rw [hh] at h
    exact (zero_ne_one h).elim
  · have h := congrFun hr (⟨N - d.val, by omega⟩ : Fin (N + 1))
    have hh := r.property.2
    change r.val _ = 0 at h
    rw [hh] at h
    exact (one_ne_zero h).elim
  · change r.val = r'.val at hr
    change s.val = s'.val at hs
    have hk : N - d.val = N - d'.val := by
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hgt
      · have h := congrFun hr (⟨N - d.val, by omega⟩ : Fin (N + 1))
        rw [r.property.2, r'.property.1 _ hlt] at h
        exact one_ne_zero h
      · have h := congrFun hr (⟨N - d'.val, by omega⟩ : Fin (N + 1))
        rw [r.property.1 _ hgt, r'.property.2] at h
        exact zero_ne_one h
    have hd : d = d' := by
      apply Fin.ext
      have h1 := d.isLt
      have h2 := d'.isLt
      omega
    subst d'
    have hrr : r = r' := Subtype.ext hr
    have hss : s = s' := Subtype.ext hs
    subst r'
    subst s'
    rfl

private theorem class_complement (N : ℕ) (c : Classified N) :
    IsLabeledRiordan (riordanGraph (N + 2)
      (allOnes + seriesOfVector N (classR N c))
      (PowerSeries.X + seriesOfVector N (classS N c)))ᶜ := by
  let r := seriesOfVector N (classR N c)
  let s := seriesOfVector N (classS N c)
  have hr0 : PowerSeries.constantCoeff r = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa only [Fin.val_zero] using
      (seriesOfVector_coeff N (classR N c) 0).trans (classR_zero N c)
  have hs0 : PowerSeries.constantCoeff s = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa only [Fin.val_zero] using
      (seriesOfVector_coeff N (classS N c) 0).trans (classS_zero N c)
  have hg0 : PowerSeries.constantCoeff (allOnes + r) = 1 := by
    simp only [map_add, allOnes_constant, hr0, add_zero]
  have hf0 : PowerSeries.constantCoeff (PowerSeries.X + s) = 0 := by simp [hs0]
  obtain ⟨g, hg⟩ : IsUnit (allOnes + r) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hg0]; exact isUnit_one)
  have hgr : allOnes + (g : (PowerSeries (ZMod 2))) = r := by
    rw [hg, CharTwo.add_cancel_left]
  rw [← hg]
  rcases c with c | ⟨d, rv, sv⟩
  · apply (graph_complement_criterion N g _ (by rwa [hg]) hf0).mpr
    have hsz : s = 0 := by simp [s, classS, seriesOfVector]
    refine ⟨0, by simp, ?_, by simp⟩
    simp only [hsz, add_zero, map_zero, mul_zero]
  · let k := N - d.val
    have hk : 1 ≤ k := by dsimp [k]; have h := d.isLt; omega
    have hkN : k < N + 1 := Nat.sub_lt_succ N d.val
    have hzero : ∀ i < k, PowerSeries.coeff i r = 0 := by
      intro i hi
      exact (seriesOfVector_coeff N rv.val ⟨i, by omega⟩).trans (rv.property.1 _ hi)
    have hone : PowerSeries.coeff k r = 1 :=
      (seriesOfVector_coeff N rv.val ⟨k, hkN⟩).trans rv.property.2
    obtain ⟨v, hv⟩ := first_degree_factor r k hzero hone
    apply (graph_complement_factor_criterion N k hk hkN g v _ (by rwa [hg]) hf0
      (hgr.trans hv)).mpr
    rw [add_comm PowerSeries.X s, CharTwo.add_cancel_right]
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have hi' : i < N - d.val + (d.val + 2) / 2 := by
      have h := d.isLt
      dsimp [k] at hi
      omega
    exact (seriesOfVector_coeff N sv.val ⟨i, by omega⟩).trans (sv.property _ hi')

private noncomputable def classToUnitParams (N : ℕ) (c : Classified N) : UnitParameters N := by
  let g := allOnes + seriesOfVector N (classR N c)
  let f := PowerSeries.X + seriesOfVector N (classS N c)
  have hr0 : PowerSeries.constantCoeff (seriesOfVector N (classR N c)) = 0 := by
    simpa only [Fin.val_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (seriesOfVector_coeff N (classR N c) 0).trans (classR_zero N c)
  have hs0 : PowerSeries.constantCoeff (seriesOfVector N (classS N c)) = 0 := by
    simpa only [Fin.val_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (seriesOfVector_coeff N (classS N c) 0).trans (classS_zero N c)
  have hg : PowerSeries.constantCoeff g = 1 := by simp [g, hr0, allOnes_constant]
  have hf : PowerSeries.constantCoeff f = 0 := by simp [f, hs0]
  refine ⟨(truncateMap N g, truncateMap N f), ?_, ?_, ?_⟩
  · simpa only [canonical_constant_truncateMap] using hg
  · simpa only [canonical_constant_truncateMap] using hf
  · rw [canonicalGraph_eq N g f hf]
    exact class_complement N c

private theorem classToUnitParams_injective (N : ℕ) : Function.Injective (classToUnitParams N) := by
  intro c c' he
  have hp := congrArg Subtype.val he
  have hgr := congrArg Prod.fst hp
  have hfr := congrArg Prod.snd hp
  apply class_pair_injective N
  apply Prod.ext
  · apply (coefficientEquiv N).symm.injective
    apply add_left_cancel (a := truncateMap N allOnes)
    simpa only [classToUnitParams, map_add, seriesOfVector, truncateMap_canonicalSeries] using hgr
  · apply (coefficientEquiv N).symm.injective
    apply add_left_cancel (a := truncateMap N PowerSeries.X)
    simpa only [classToUnitParams, map_add, seriesOfVector, truncateMap_canonicalSeries] using hfr

private theorem classToUnitParams_surjective (N : ℕ) : Function.Surjective (classToUnitParams N) := by
  intro p
  let H := truncateMap N allOnes
  let T := truncateMap N PowerSeries.X
  let r := H + p.val.1
  let s := T + p.val.2
  let rr := canonicalSeries N r
  let ss := canonicalSeries N s
  let gg := allOnes + rr
  let ff := PowerSeries.X + ss
  have hgtr : truncateMap N gg = p.val.1 := by
    simp only [gg, rr, map_add, truncateMap_canonicalSeries, r, H, CharTwo.add_cancel_left]
  have hftr : truncateMap N ff = p.val.2 := by
    simp only [ff, ss, map_add, truncateMap_canonicalSeries, s, T, CharTwo.add_cancel_left]
  have hg0 : PowerSeries.constantCoeff gg = 1 := by
    have hc := canonical_constant_truncateMap N gg
    rw [hgtr] at hc
    exact hc.symm.trans p.property.1
  have hf0 : PowerSeries.constantCoeff ff = 0 := by
    have hc := canonical_constant_truncateMap N ff
    rw [hftr] at hc
    exact hc.symm.trans p.property.2.1
  have hr0 : PowerSeries.constantCoeff rr = 0 := by
    have hc : (1 : (ZMod 2)) + PowerSeries.constantCoeff rr = 1 + 0 := by
      simpa only [gg, map_add, allOnes_constant, add_zero] using hg0
    exact add_left_cancel hc
  have hs0 : PowerSeries.constantCoeff ss = 0 := by
    simpa only [ff, map_add, PowerSeries.constantCoeff_X, zero_add] using hf0
  have hgraph : riordanGraph (N + 2) gg ff =
      riordanGraph (N + 2) (canonicalSeries N p.val.1) (canonicalSeries N p.val.2) := by
    apply (graph_eq_iff_columns N _ _ _ _ hf0 p.property.2.1).mpr
    intro j hj
    simp only [map_mul, map_pow, truncateMap_canonicalSeries, hgtr, hftr]
  have hcomp : IsLabeledRiordan (riordanGraph (N + 2) gg ff)ᶜ := by
    rw [hgraph]
    exact p.property.2.2
  obtain ⟨g, hgu⟩ : IsUnit gg :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hg0]; exact isUnit_one)
  have hgr : allOnes + (g : (PowerSeries (ZMod 2))) = rr := by
    rw [hgu]
    exact CharTwo.add_cancel_left _ _
  have hc := (graph_complement_criterion N g ff (by rwa [hgu]) hf0).mp
    (by rwa [hgu])
  by_cases hr : r = 0
  · have hrr : rr = 0 := by simp only [rr, hr, canonicalSeries_zero]
    have hsz : s = 0 := by
      obtain ⟨delta, hd, he, hn⟩ := hc
      rw [hgr, hrr, map_zero, zero_mul, zero_mul, add_zero, hftr] at he
      change T + p.val.2 = 0
      rw [he, CharTwo.add_self_eq_zero]
    refine ⟨.inl (), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · have he : p.val.1 = H := by
        apply (CharTwo.add_eq_zero).mp
        simpa only [r, add_comm] using hr
      simpa only [classToUnitParams, classR, classS, seriesOfVector, map_zero,
        canonicalSeries_zero, add_zero, H] using he.symm
    · have he : p.val.2 = T := by
        apply (CharTwo.add_eq_zero).mp
        simpa only [s, add_comm] using hsz
      simpa only [classToUnitParams, classR, classS, seriesOfVector, map_zero,
        canonicalSeries_zero, add_zero, T] using he.symm
  · let rv := coefficientEquiv N r
    let sv := coefficientEquiv N s
    have hex : ∃ k : ℕ, k < N + 1 ∧ PowerSeries.coeff k rr ≠ 0 := by
      by_contra! h
      have hz : rv = 0 := by
        funext i
        rw [show rv i = PowerSeries.coeff i.val rr by exact coefficientEquiv_apply N r i]
        exact h i.val i.isLt
      apply hr
      apply (coefficientEquiv N).injective
      simpa only [map_zero] using hz
    let k := Nat.find hex
    have hkN : k < N + 1 := (Nat.find_spec hex).1
    have hkn : PowerSeries.coeff k rr ≠ 0 := (Nat.find_spec hex).2
    have hzero : ∀ i < k, PowerSeries.coeff i rr = 0 := by
      intro i hi
      by_contra hn
      have hle := Nat.find_min' hex (show i < N + 1 ∧ PowerSeries.coeff i rr ≠ 0 from ⟨by omega, hn⟩)
      omega
    have hk : 1 ≤ k := by
      by_contra h
      have he : k = 0 := Nat.eq_zero_of_not_pos h
      apply hkn
      simpa only [he, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hr0
    have hone : PowerSeries.coeff k rr = 1 := by
      have bit : ∀ a : (ZMod 2), a ≠ 0 → a = 1 := Fin.eq_one_of_ne_zero
      exact bit _ hkn
    obtain ⟨v, hv⟩ := first_degree_factor rr k hzero hone
    have htail : (PowerSeries.X : (PowerSeries (ZMod 2))) ^ (k + (N + 1 - k + 1) / 2) ∣ ss := by
      have hp := (graph_complement_factor_criterion N k hk hkN g v ff
        (by rwa [hgu]) hf0 (hgr.trans hv)).mp (by rwa [hgu])
      simpa only [ff, add_comm PowerSeries.X ss, CharTwo.add_cancel_right] using hp
    let d : Fin N := ⟨N - k, by omega⟩
    have hdk : N - d.val = k := by dsimp [d]; omega
    have hrvec : (∀ i : Fin (N + 1), i.val < N - d.val → rv i = 0) ∧
        rv ⟨N - d.val, by omega⟩ = 1 := by
      constructor
      · intro i hi
        rw [show rv i = PowerSeries.coeff i.val rr by exact coefficientEquiv_apply N r i]
        exact hzero i.val (by omega)
      · rw [show rv ⟨N - d.val, by omega⟩ = PowerSeries.coeff (N - d.val) rr by
          exact coefficientEquiv_apply N r _]
        rwa [hdk]
    have hsvec : ∀ i : Fin (N + 1), i.val < N - d.val + (d.val + 2) / 2 → sv i = 0 := by
      intro i hi
      rw [show sv i = PowerSeries.coeff i.val ss by exact coefficientEquiv_apply N s i]
      apply (PowerSeries.X_pow_dvd_iff.mp htail) i.val
      dsimp [d] at hi
      omega
    refine ⟨.inr ⟨d, ⟨rv, hrvec⟩, ⟨sv, hsvec⟩⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change truncateMap N (allOnes + seriesOfVector N rv) = p.val.1
      simpa only [seriesOfVector, rv, LinearEquiv.symm_apply_apply] using hgtr
    · change truncateMap N (PowerSeries.X + seriesOfVector N sv) = p.val.2
      simpa only [seriesOfVector, sv, LinearEquiv.symm_apply_apply] using hftr

private theorem doubled_classified_card (N : ℕ) :
    2 * Nat.card (Classified N) = prefixCount (N + 1) := by
  rw [classified_card]
  have hs : ∑ d ∈ Finset.range N, (2 : ℕ) ^ (3 * (d + 1) / 2) =
      2 * ∑ d ∈ Finset.range N, (2 : ℕ) ^ (d + (d + 1) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show 3 * (d + 1) / 2 = d + (d + 1) / 2 + 1 by omega, pow_succ]
    ring
  unfold prefixCount
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.zero_div, pow_zero]
  rw [hs]
  ring

private theorem count_all (N : ℕ) : a (N + 2) = prefixCount (N + 1) := by
  have ho := complement_orientation_card
    (fun G : SimpleGraph (Fin (N + 2)) => IsLabeledRiordan G)
    (⟨1, by omega⟩ : Fin (N + 2)) 0 (by simp [Fin.ext_iff])
  change a (N + 2) = 2 * Nat.card (Oriented N) at ho
  have hp := Nat.card_congr (Equiv.ofBijective (unitParametersToGraph N)
    ⟨unitParametersToGraph_injective N, unitParametersToGraph_surjective N⟩)
  have hc := Nat.card_congr (Equiv.ofBijective (classToUnitParams N)
    ⟨classToUnitParams_injective N, classToUnitParams_surjective N⟩)
  rw [ho, ← hp, ← hc]
  exact doubled_classified_card N

private theorem count_sum : ∀ n : ℕ, 1 ≤ n → a n = prefixCount (n - 1) := by
  intro n hn
  rcases n with _ | n
  · omega
  rcases n with _ | N
  · simpa [prefixCount] using count_one
  · simpa using count_all N

theorem result : claim := claim_of_sum count_sum

end D5.S3.Combinatorics.Riordan.LabeledComplementCount
