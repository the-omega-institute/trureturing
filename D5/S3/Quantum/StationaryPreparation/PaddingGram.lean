/- GID: D5/S3/Quantum/StationaryPreparation/PaddingGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Padding Gram entries are minimum-head multiplicities within each tail block. -/

import D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit
import D5.S3.Quantum.StationaryPreparation.NormalizedGram

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingGram

open D5.S3.Quantum.StationaryPreparation.PaddingMemory
open D5.S3.Quantum.StationaryPreparation.ResidualCalculus
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Last-tail weights are the consecutive multiplicity increments, with the
initial multiplicity at head count zero. -/
theorem last_tail_mass_head_slice (head : A) (b : Multiset A)
    (hr : 0 < tailCount head b) (j : ℕ) :
    lastTailMass head (headSlice head b j) =
      if j = 0 then
        (multiplicity (headSlice head b 0).card (headSlice head b 0) : ℝ)
      else
        (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ) -
        (multiplicity (headSlice head b (j - 1)).card (headSlice head b (j - 1)) : ℝ) := by
  have hn : (0 : ℝ) < (headSlice head b j).card := by
    exact_mod_cast (show 0 < (headSlice head b j).card by rw [head_slice_card]; omega)
  by_cases hj : j = 0
  · subst j
    simp only [ite_true, lastTailMass, head_slice_tail_count, head_slice_card, zero_add]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')
  · rw [if_neg hj]
    have hm := erase_multiplicity_real (headSlice head b j) head
      (Multiset.count_pos.mp (by simpa using Nat.pos_of_ne_zero hj))
    rw [head_slice_erase_head, head_slice_count_head] at hm
    have hs : ((headSlice head b j).card : ℝ) = j + (tailCount head b : ℝ) := by
      exact_mod_cast head_slice_card head b j
    unfold lastTailMass
    rw [head_slice_tail_count, div_eq_iff hn.ne']
    nlinarith [congrArg (fun x : ℝ =>
      x * (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ)) hs]

private theorem sum_last_tail_mass (head : A) (b : Multiset A)
    (hr : 0 < tailCount head b) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), lastTailMass head (headSlice head b j)) =
      (multiplicity (headSlice head b n).card (headSlice head b n) : ℝ) := by
  simp_rw [last_tail_mass_head_slice head b hr]
  exact (Finset.eq_sum_range_sub' _ n).symm

private theorem tail_filter_eq_zero (head : A) (b : Multiset A) :
    b.filter (fun i => i ≠ head) = 0 ↔ tailCount head b = 0 := by
  rw [tail_count_zero_iff]
  constructor
  · intro h i hi
    have := congrArg (Multiset.count i) h
    simpa [Multiset.count_filter, hi] using this
  · intro h
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · simp [hi, h i hi]

private theorem tail_free_multiplicity (head : A) (b : Multiset A)
    (hr : tailCount head b = 0) (n : ℕ) :
    multiplicity (headSlice head b n).card (headSlice head b n) = 1 := by
  have hf := (tail_filter_eq_zero head b).mpr hr
  simp only [headSlice, hf, add_zero, Multiset.card_replicate]
  rw [multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
  simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
  simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
  exact Nat.div_self (Nat.factorial_pos n)

private theorem residual_tail_eq_iff (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
    residualPositiveTail head a b hb hr = residualPositiveTail head a c hc hs ↔
      b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · have he := congrArg (fun t : PositiveTail (fun i : TailAlphabet head => a.count i.val) =>
        (t.val ⟨i, hi⟩).val) h
      simpa [residualPositiveTail, residualTail, Multiset.count_filter, hi] using he
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he := congrArg (Multiset.count i.val) h
    simpa [residualPositiveTail, residualTail, Multiset.count_filter, i.property] using he

private theorem padding_residual_none (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : 0 < tailCount head b) : paddingResidual head a b none = 0 := by
  simp [paddingResidual, hb, hr, WithLp.ofLp_sum, Finset.sum_apply,
    basis_apply]

private theorem padding_residual_coordinates (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : 0 < tailCount head b)
    (t : PositiveTail (fun i : TailAlphabet head => a.count i.val))
    (k : Fin (a.count head + 1)) :
    paddingResidual head a b (some (t, k)) =
      if t = residualPositiveTail head a b hb hr ∧ k.val ≤ b.count head then
        (Real.sqrt (lastTailMass head (headSlice head b k.val)) : ℂ) else 0 := by
  classical
  rw [paddingResidual, dif_pos hb, dif_pos hr]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    basis_apply, Option.some.injEq, Prod.mk.injEq]
  by_cases ht : t = residualPositiveTail head a b hb hr
  · subst t
    by_cases hk : k.val ≤ b.count head
    · rw [if_pos ⟨rfl, hk⟩]
      let j : Fin (b.count head + 1) := ⟨k.val, Nat.lt_succ_of_le hk⟩
      rw [Finset.sum_eq_single j]
      · simp [j, residualHeadIndex]
      · intro i _ hij
        have hi : k ≠ residualHeadIndex head a b hb i := by
          intro he
          apply hij
          exact Fin.ext (congrArg Fin.val he).symm
        simp [hi]
      · simp
    · rw [if_neg (by simp [hk])]
      apply Finset.sum_eq_zero
      intro i _
      have hi : k ≠ residualHeadIndex head a b hb i := by
        intro he
        have := congrArg Fin.val he
        have := i.isLt
        simp only [residualHeadIndex] at *
        omega
      simp [hi]
  · simp [ht]

private theorem sum_bounded_mass (head : A) (a b : Multiset A)
    (hr : 0 < tailCount head b) (n : ℕ) (hn : n ≤ a.count head) :
    (∑ k : Fin (a.count head + 1),
      if k.val ≤ n then (lastTailMass head (headSlice head b k.val) : ℂ) else 0) =
      (multiplicity (headSlice head b n).card (headSlice head b n) : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0)]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
      intro k _ hk
      have : ¬ k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      simp [this]
    _ = ∑ k ∈ Finset.range (n + 1),
        (lastTailMass head (headSlice head b k) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = _ := by exact_mod_cast sum_last_tail_mass head b hr n

private theorem padding_residual_inner_positive (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
    inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  classical
  have hg : inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      ∑ x, star (paddingResidual head a b x) * paddingResidual head a c x := by
    calc
      _ = inner ℂ (∑ x, paddingResidual head a b x • basis x)
          (∑ x, paddingResidual head a c x • basis x) :=
        congrArg₂ (inner ℂ) (basis_expansion _) (basis_expansion _)
      _ = _ := (EuclideanSpace.basisFun (OccupationMemory a head) ℂ).orthonormal.inner_sum
        (paddingResidual head a b) (paddingResidual head a c) Finset.univ
  rw [hg, Fintype.sum_option, padding_residual_none head a b hb hr, star_zero,
    zero_mul, zero_add, Fintype.sum_prod_type]
  by_cases ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head)
  · rw [if_pos ht]
    have htt := (residual_tail_eq_iff head a b c hb hc hr hs).mpr ht
    have hslice (j : ℕ) : headSlice head c j = headSlice head b j := by
      simp only [headSlice, ht]
    have hterm (t : PositiveTail (fun i : TailAlphabet head => a.count i.val))
        (k : Fin (a.count head + 1)) :
        star (paddingResidual head a b (some (t, k))) *
          paddingResidual head a c (some (t, k)) =
        if t = residualPositiveTail head a b hb hr ∧
            k.val ≤ min (b.count head) (c.count head) then
          (lastTailMass head (headSlice head b k.val) : ℂ) else 0 := by
      rw [padding_residual_coordinates head a b hb hr,
        padding_residual_coordinates head a c hc hs, ← htt, hslice]
      have hm := (last_tail_mass_pos head (headSlice head b k.val)
        (by simpa only [head_slice_tail_count] using hr)).le
      by_cases htb : t = residualPositiveTail head a b hb hr <;>
        by_cases hkb : k.val ≤ b.count head <;> by_cases hkc : k.val ≤ c.count head <;>
        simp [htb, hkb, hkc, ← Complex.ofReal_mul,
          Real.mul_self_sqrt hm]
    simp_rw [hterm]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sum_bounded_mass head a b hr _
      (le_trans (min_le_left _ _) (Multiset.le_iff_count.mp hb head))
  · rw [if_neg ht]
    have htt : residualPositiveTail head a b hb hr ≠ residualPositiveTail head a c hc hs :=
      fun h => ht ((residual_tail_eq_iff head a b c hb hc hr hs).mp h)
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro k _
    rw [padding_residual_coordinates head a b hb hr,
      padding_residual_coordinates head a c hc hs]
    by_cases htb : t = residualPositiveTail head a b hb hr
    · have htc : t ≠ residualPositiveTail head a c hc hs := by simpa [htb] using htt
      simp [htc]
    · simp [htb]

/-- The Gram entry of the actual padding vectors is the minimum-head
multiplicity when their entire tails coincide, and is zero otherwise. -/
theorem padding_residual_inner (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) :
    inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  classical
  by_cases hr : tailCount head b = 0
  · rw [padding_residual_tail_free head a b hb hr]
    by_cases hs : tailCount head c = 0
    · have ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
        rw [(tail_filter_eq_zero head b).mpr hr, (tail_filter_eq_zero head c).mpr hs]
      rw [padding_residual_tail_free head a c hc hs, if_pos ht]
      dsimp only
      rw [tail_free_multiplicity head b hr]
      simp [basis]
    · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
        intro h
        apply hs
        apply (tail_filter_eq_zero head c).mp
        rw [← h, (tail_filter_eq_zero head b).mpr hr]
      rw [if_neg ht]
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a c hc (Nat.pos_of_ne_zero hs)
  · by_cases hs : tailCount head c = 0
    · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
        intro h
        apply hr
        apply (tail_filter_eq_zero head b).mp
        rw [h, (tail_filter_eq_zero head c).mpr hs]
      rw [padding_residual_tail_free head a c hc hs, if_neg ht]
      apply inner_eq_zero_symm.mp
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a b hb (Nat.pos_of_ne_zero hr)
    · exact padding_residual_inner_positive head a b c hb hc
        (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hs)

open D5.S3.Quantum.StationaryPreparation.NormalizedResiduals

/-- The actual padding residual normalized by its positive word-count scale. -/
def normalizedPadding (head : A) (a b : Multiset A) : Space (OccupationMemory a head) :=
  (residualScale b : ℂ)⁻¹ • paddingResidual head a b

/-- Source moments with the actual common sink, in the source's inner-product order. -/
def paddingMoment (head : A) (a b : Multiset A) : ℂ :=
  inner ℂ (normalizedPadding head a b) (basis none)

theorem normalized_padding_norm (head : A) (a b : Multiset A) (hb : b ≤ a) :
    ‖normalizedPadding head a b‖ = 1 := by
  have hi := padding_residual_inner head a b b hb hb
  simp only [ite_true, min_self, head_slice_self] at hi
  have hn : ‖paddingResidual head a b‖ = residualScale b := by
    have hh : ‖paddingResidual head a b‖ ^ 2 = (multiplicity b.card b : ℝ) := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hi]
      rfl
    nlinarith [scale_sq b, scale_pos b, norm_nonneg (paddingResidual head a b)]
  rw [normalizedPadding, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scale_pos b), hn, inv_mul_cancel₀ (scale_pos b).ne']

theorem normalized_padding_tail_free (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : tailCount head b = 0) : normalizedPadding head a b = basis none := by
  have hm : multiplicity b.card b = 1 := by
    simpa only [head_slice_self] using tail_free_multiplicity head b hr (b.count head)
  simp [normalizedPadding, padding_residual_tail_free head a b hb hr, residualScale, hm]

@[simp] theorem normalized_padding_zero (head : A) (a : Multiset A) :
    normalizedPadding head a 0 = basis none := by
  apply normalized_padding_tail_free head a 0 (Multiset.zero_le _)
  simp [tailCount]

theorem padding_moment (head : A) (a b : Multiset A) (hb : b ≤ a) :
    paddingMoment head a b = if tailCount head b = 0 then 1 else 0 := by
  classical
  by_cases hr : tailCount head b = 0
  · simp [paddingMoment, normalized_padding_tail_free head a b hb hr, hr,
      basis]
  · rw [paddingMoment, normalizedPadding, inner_smul_left, if_neg hr]
    have hz : inner ℂ (paddingResidual head a b) (basis none) = 0 := by
      apply inner_eq_zero_symm.mp
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a b hb (Nat.pos_of_ne_zero hr)
    rw [hz, mul_zero]

theorem normalized_padding_axis (head : A) (a : Multiset A) (j : ℕ)
    (hj : j ≤ a.count head) :
    normalizedPadding head a (Multiset.replicate j head) = basis none := by
  apply normalized_padding_tail_free
  · apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : head = i
    · subst i; simpa only [Multiset.count_replicate_self] using hj
    · simp only [Multiset.count_replicate, if_neg hi]; exact Nat.zero_le _
  · apply (tail_count_zero_iff head _).mpr
    intro i hi
    simp only [Multiset.count_replicate, if_neg (Ne.symm hi)]

theorem padding_moment_axis (head : A) (a : Multiset A) (j : ℕ)
    (hj : j ≤ a.count head) : paddingMoment head a (Multiset.replicate j head) = 1 := by
  classical
  simp [paddingMoment, normalized_padding_axis head a j hj,
    basis]

end D5.S3.Quantum.StationaryPreparation.PaddingGram
