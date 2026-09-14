/- GID: D5/S3/Quantum/StationaryPreparation/HeadGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/HeadGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cumulative head-block vectors realize the occupation kernel in a span with the optimal dimension upper bound. -/

import D5.S3.Quantum.StationaryPreparation.PhysicalGram

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
namespace D5.S3.Quantum.StationaryPreparation.HeadGram
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def decrease (r : σ → ℕ) (i : σ) : σ → ℕ := Function.update r i (r i - 1)

def sameTail (h : σ) (r s : σ → ℕ) : Prop := ∀ i, i ≠ h → r i = s i

open Classical in
def headKernel (h : σ) (r s : σ → ℕ) : ℝ :=
  if sameTail h r s then (M (fun i => min (r i) (s i)) : ℝ) else 0

abbrev Tail (a : σ → ℕ) (h : σ) := ∀ i : {i : σ // i ≠ h}, Fin (a i + 1)
def tail {a : σ → ℕ} (h : σ) (r : Box a) : Tail a h := fun i => r i

def joined (h : σ) (b : {i : σ // i ≠ h} → ℕ) (j : ℕ) : σ → ℕ :=
  fun i => if hi : i = h then j else b ⟨i, hi⟩

def weight {a : σ → ℕ} (h : σ) (b : Tail a h) (j : ℕ) : ℝ :=
  (M (joined h (fun i => (b i).val) j) : ℝ)

def increment {a : σ → ℕ} (h : σ) (b : Tail a h) (j : ℕ) : ℝ :=
  weight h b j - if j = 0 then 0 else weight h b (j - 1)

def raw {a : σ → ℕ} (h : σ) (r : Box a) :
    EuclideanSpace ℂ (Tail a h × Fin (a h + 1)) :=
  WithLp.toLp 2 (fun q => if q.1 = tail h r ∧ q.2.val ≤ (r h).val then
    (Real.sqrt (increment h q.1 q.2.val) : ℂ) else 0)

abbrev memory (a : σ → ℕ) (h : σ) :=
  Submodule.span ℂ (Set.range (raw (a := a) h))

def vector {a : σ → ℕ} (h : σ) (r : Box a) : memory a h :=
  ⟨raw h r, Submodule.subset_span ⟨r, rfl⟩⟩

theorem head_gram_realization (a : σ → ℕ) (h : σ) :
    (∀ r s : Box a, inner ℂ (vector h r) (vector h s) =
      (headKernel h (values r) (values s) : ℂ)) ∧
    (∀ r s : σ → ℕ, r ≠ 0 → s ≠ 0 →
      headKernel h r s = ∑ i, if 0 < r i ∧ 0 < s i then
        headKernel h (decrease r i) (decrease s i) else 0) ∧
    Module.finrank ℂ (memory a h) ≤ (∏ i, (a i + 1)) - a h ∧
    (0 < a h → Submodule.span ℂ
      (Set.range (fun r : {r : Box a // r ≠ 0} => vector h r.val)) = ⊤) := by
  classical
  have raw_inner (r s : Box a) :
      inner ℂ (raw h r) (raw h s) = (headKernel h (values r) (values s) : ℂ) := by
    have hweight (b : Tail a h) (j : ℕ) :
        weight h b j =
        (((j + ∑ i ∈ Finset.univ.erase h, joined h (fun i => (b i).val) 0 i).choose
          (∑ i ∈ Finset.univ.erase h, joined h (fun i => (b i).val) 0 i) : ℕ) : ℝ) *
          (Nat.multinomial (Finset.univ.erase h) (joined h (fun i => (b i).val) 0) : ℝ) := by
      unfold weight
      change (Nat.multinomial Finset.univ (joined h (fun i => (b i).val) j) : ℝ) = _
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ h), Nat.multinomial_insert (Finset.notMem_erase h _)]
      have heq : ∀ i ∈ Finset.univ.erase h,
          joined h (fun i => (b i).val) j i = joined h (fun i => (b i).val) 0 i := by
        intro i hi
        simp [joined, (Finset.mem_erase.mp hi).1]
      rw [Finset.sum_congr rfl heq, Nat.multinomial_congr heq]
      simp only [joined, dite_true, Nat.cast_mul]
      rw [Nat.choose_symm_add]
      rfl
    have hmono (b : Tail a h) : Monotone (weight h b) := by
      intro j k hjk
      rw [hweight, hweight]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.choose_le_choose _ (Nat.add_le_add_right hjk _)
      · positivity
    have hnonneg (b : Tail a h) (j : ℕ) : 0 ≤ increment h b j := by
      unfold increment
      split_ifs with hj
      · simp only [sub_zero]
        unfold weight
        positivity
      · exact sub_nonneg.mpr (hmono b (Nat.sub_le _ _))
    have htel (b : Tail a h) (j : ℕ) :
        ∑ k ∈ Finset.range (j + 1), increment h b k = weight h b j := by
      induction j with
      | zero => simp [increment]
      | succ j ih =>
        rw [Finset.sum_range_succ, ih]
        simp [increment]
    have hsum (b : Tail a h) (j : Fin (a h + 1)) :
        (∑ k : Fin (a h + 1), if k.val ≤ j.val then increment h b k.val else 0) =
          weight h b j.val := by
      rw [Fin.sum_univ_eq_sum_range (f := fun k => if k ≤ j.val then increment h b k else 0)]
      change (∑ k ∈ Finset.range (a h + 1), if k ≤ j.val then increment h b k else 0) = _
      rw [← Finset.sum_filter]
      have hf : (Finset.range (a h + 1)).filter (fun k => k ≤ j.val) =
          Finset.range (j.val + 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hf, htel]
    have ht : tail h r = tail h s ↔ sameTail h (values r) (values s) := by
      constructor
      · intro hh i hi
        exact congrArg Fin.val (congrFun hh ⟨i, hi⟩)
      · intro hh
        funext i
        apply Fin.ext
        exact hh i i.property
    rw [PiLp.inner_apply]
    simp only [Fintype.sum_prod_type, raw, WithLp.ofLp_toLp, RCLike.inner_apply]
    by_cases hrs : tail h r = tail h s
    · have hc : ∀ b : Tail a h, b = tail h r ↔ b = tail h s := by simp only [hrs, implies_true]
      simp_rw [← hc]
      have hcoord (b : Tail a h) (k : Fin (a h + 1)) :
          (if b = tail h r ∧ k.val ≤ (s h).val then (Real.sqrt (increment h b k.val) : ℂ) else 0) *
            star (if b = tail h r ∧ k.val ≤ (r h).val then (Real.sqrt (increment h b k.val) : ℂ) else 0) =
          if b = tail h r then if k.val ≤ min (r h).val (s h).val then
            (increment h b k.val : ℂ) else 0 else 0 := by
        by_cases hb : b = tail h r
        · by_cases hkr : k.val ≤ (r h).val <;> by_cases hks : k.val ≤ (s h).val
          · simp only [hb, hkr, hks, if_true, le_min_iff, and_self,
              Complex.star_def, Complex.conj_ofReal]
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnonneg (tail h r) k.val)]
          all_goals simp [hb, hkr, hks]
        · simp [hb]
      simp only [starRingEnd_apply]
      simp_rw [hcoord]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rw [show (min (r h).val (s h).val) = (min (r h) (s h)).val from rfl]
      have hsumC (b : Tail a h) (j : Fin (a h + 1)) :
          (∑ k : Fin (a h + 1), if k.val ≤ j.val then (increment h b k.val : ℂ) else 0) =
          (weight h b j.val : ℂ) := by
        have hh := congrArg (fun x : ℝ => (x : ℂ)) (hsum b j)
        simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hh
      rw [hsumC]
      rw [headKernel, if_pos (ht.mp hrs)]
      congr 1
      unfold weight
      congr 2
      funext i
      by_cases hi : i = h
      · subst i
        simp [joined, values]
      · simp only [joined, dif_neg hi, tail]
        have hh := ht.mp hrs i hi
        change (r i).val = min (r i).val (s i).val
        rw [show (r i).val = (s i).val from hh, min_self]
    · rw [headKernel, if_neg (fun hh => hrs (ht.mpr hh))]
      simp only [Complex.ofReal_zero]
      apply Finset.sum_eq_zero
      intro b _
      apply Finset.sum_eq_zero
      intro k _
      split_ifs <;> simp_all
  have hrec (r s : σ → ℕ) (hr : r ≠ 0) (hs : s ≠ 0) :
      headKernel h r s = ∑ i, if 0 < r i ∧ 0 < s i then
        headKernel h (decrease r i) (decrease s i) else 0 := by
    have profile_count (b : σ → ℕ) (i : σ) : (profile b).count i = b i := by
      simp [profile, Multiset.count_sum', Multiset.count_replicate]
    have hM (b : σ → ℕ) : M b = multiplicity (mass b) (profile b) := by
      rw [multiplicity_eq_factorial (profile b) (by simp [profile, mass])]
      simp only [profile_count]
      rfl
    have hprof (b : σ → ℕ) (i : σ) :
        profile (decrease b i) = (profile b).erase i := by
      apply Multiset.ext.mpr
      intro j
      rw [profile_count]
      by_cases hj : j = i
      · subst j
        simp [decrease, Multiset.count_erase_self, profile_count]
      · simpa [decrease, hj, profile_count] using
          (Multiset.count_erase_of_ne hj (profile b)).symm
    have hmass (b : σ → ℕ) (i : σ) (hi : 0 < b i) :
        mass (decrease b i) = mass b - 1 := by
      have hh := congrArg Multiset.card (hprof b i)
      have hm : i ∈ profile b := by
        rw [← Multiset.count_pos, profile_count]
        exact hi
      rw [Multiset.card_erase_of_mem hm] at hh
      simpa [profile, mass] using hh
    have hmpos (b : σ → ℕ) (hb : b ≠ 0) : 0 < mass b := by
      by_contra hh
      have hz : ∀ i, b i = 0 := by
        have hh' : (∑ i, b i) = 0 := Nat.eq_zero_of_not_pos hh
        simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (b i))).mp hh'
      exact hb (funext hz)
    have hrec (b : σ → ℕ) (hb : b ≠ 0) :
        (M b : ℝ) = ∑ i, if 0 < b i then (M (decrease b i) : ℝ) else 0 := by
      have hp := hmpos b hb
      have hi (i : σ) (hbi : 0 < b i) :
          mass b * M (decrease b i) = b i * M b := by
        have hm : i ∈ profile b := by
          rw [← Multiset.count_pos, profile_count]
          exact hbi
        have he := multiplicity_erase_mul (a := profile b) (n := mass b - 1)
          (by simpa only [show (profile b).card = mass b by simp [profile, mass]] using (Nat.sub_add_cancel hp).symm) i hm
        rw [Nat.sub_add_cancel hp, profile_count] at he
        simpa [hM, hmass b i hbi, hprof] using he
      apply mul_left_cancel₀ (show (mass b : ℝ) ≠ 0 by positivity)
      rw [Finset.mul_sum]
      calc
        (mass b : ℝ) * M b = ∑ i, (b i : ℝ) * M b := by simp [mass, Finset.sum_mul]
        _ = ∑ i, (mass b : ℝ) * (if 0 < b i then (M (decrease b i) : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hh : 0 < b i
          · simpa [hh] using (show (mass b : ℝ) * M (decrease b i) =
              (b i : ℝ) * M b by exact_mod_cast hi i hh).symm
          · simp [hh, Nat.eq_zero_of_not_pos hh]
    have htdec (i : σ) (hi : 0 < r i ∧ 0 < s i) :
        sameTail h (decrease r i) (decrease s i) ↔ sameTail h r s := by
      constructor
      · intro hh j hj
        have hhj := hh j hj
        by_cases hji : j = i
        · subst j
          simp only [decrease, Function.update_self] at hhj
          omega
        · simpa [decrease, hji] using hhj
      · intro hh j hj
        by_cases hji : j = i
        · subst j
          simp [decrease, hh i hj]
        · simpa [decrease, hji] using hh j hj
    by_cases ht : sameTail h r s
    · let t : σ → ℕ := fun i => min (r i) (s i)
      have htne : t ≠ 0 := by
        intro hz
        have hz' : ∀ i, min (r i) (s i) = 0 := fun i => congrFun hz i
        have hrtail : ∀ i, i ≠ h → r i = 0 := by
          intro i hi
          have := hz' i
          rw [ht i hi, min_self] at this
          exact (ht i hi).trans this
        have hrh : r h ≠ 0 := by
          intro hh
          apply hr
          funext i
          by_cases hi : i = h
          · simpa [hi] using hh
          · exact hrtail i hi
        have hsh : s h ≠ 0 := by
          intro hh
          apply hs
          funext i
          by_cases hi : i = h
          · simpa [hi] using hh
          · exact (ht i hi).symm.trans (hrtail i hi)
        have := hz' h
        omega
      rw [headKernel, if_pos ht, hrec t htne]
      apply Finset.sum_congr rfl
      intro i _
      have hc : 0 < t i ↔ 0 < r i ∧ 0 < s i := by simp [t]
      by_cases hi : 0 < r i ∧ 0 < s i
      · rw [if_pos (hc.mpr hi), if_pos hi, headKernel, if_pos ((htdec i hi).mpr ht)]
        congr 2
        funext j
        by_cases hji : j = i
        · subst j
          simp only [decrease, Function.update_self, t]
          omega
        · simp [decrease, hji, t]
      · rw [if_neg (fun hh => hi (hc.mp hh)), if_neg hi]
    · rw [headKernel, if_neg ht]
      symm
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : 0 < r i ∧ 0 < s i
      · rw [if_pos hi, headKernel, if_neg (fun hh => ht ((htdec i hi).mp hh))]
      · rw [if_neg hi]
  refine ⟨fun r s => raw_inner r s, hrec, ?_⟩
  have hpureM (b : σ → ℕ) (hb : ∀ i, i ≠ h → b i = 0) : M b = 1 := by
    have heq : b = Pi.single h (b h) := by
      funext i
      by_cases hi : i = h
      · subst i; simp
      · simp [hi, hb i hi]
    change Nat.multinomial Finset.univ b = 1
    rw [heq]
    exact Nat.multinomial_single Finset.univ h (b h)
  have hpure (r s : Box a) (hr : tail h r = 0) (hs : tail h s = 0) :
      inner ℂ (raw h r) (raw h s) = 1 := by
    have hr' : ∀ i, i ≠ h → (r i).val = 0 := by
      intro i hi
      exact congrArg Fin.val (congrFun hr ⟨i, hi⟩)
    have hs' : ∀ i, i ≠ h → (s i).val = 0 := by
      intro i hi
      exact congrArg Fin.val (congrFun hs ⟨i, hi⟩)
    rw [raw_inner, headKernel, if_pos (show sameTail h (values r) (values s) from
      fun i hi => (hr' i hi).trans (hs' i hi).symm)]
    rw [hpureM _ (by intro i hi; simp [values, hr' i hi])]
    norm_num
  have hcollapse (r : Box a) (hr : tail h r = 0) : vector h r = vector h 0 := by
    apply Subtype.ext
    change raw h r = raw h 0
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      hpure r r hr hr, hpure r 0 hr rfl, hpure 0 r rfl hr, hpure 0 0 rfl rfl]
    ring
  have hspan (P : Box a → Prop) (hP : ∀ r : Box a,
      ∃ s : Box a, P s ∧ vector h r = vector h s) :
      Submodule.span ℂ (Set.range (fun r : {r : Box a // P r} => vector h r.val)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp x.property
    have hx : (∑ r : Box a, c r • vector h r) = x := by
      apply Subtype.ext
      simpa [vector] using hc
    rw [← hx]
    apply Submodule.sum_mem
    intro r _
    apply Submodule.smul_mem
    obtain ⟨s, hs, heq⟩ := hP r
    rw [heq]
    exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  let discarded : Box a → Prop := fun r => r ≠ 0 ∧ tail h r = 0
  have hheadpos (r : {r : Box a // discarded r}) : 0 < (r.val h).val := by
    by_contra hh
    apply r.property.1
    funext i
    apply Fin.ext
    by_cases hi : i = h
    · subst i
      exact Nat.eq_zero_of_not_pos hh
    · exact congrArg Fin.val (congrFun r.property.2 ⟨i, hi⟩)
  let pure : Fin (a h) ≃ {r : Box a // discarded r} :=
    { toFun := fun j => ⟨Function.update (0 : Box a) h ⟨j.val + 1, by omega⟩,
        ⟨by intro hz; have hh := congrArg Fin.val (congrFun hz h); simp at hh,
         by funext i; simp [tail, i.property]⟩⟩
      invFun := fun r => ⟨(r.val h).val - 1, by have := hheadpos r; have := (r.val h).isLt; omega⟩
      left_inv := by intro j; apply Fin.ext; simp
      right_inv := by
        intro r
        apply Subtype.ext
        funext i
        apply Fin.ext
        by_cases hi : i = h
        · subst i
          simp only [Function.update_self]
          have := hheadpos r
          omega
        · simp only [Function.update_of_ne hi]
          exact (congrArg Fin.val (congrFun r.property.2 ⟨i, hi⟩)).symm }
  have hcard : Fintype.card {r : Box a // ¬ discarded r} =
      (∏ i, (a i + 1)) - a h := by
    rw [Fintype.card_subtype_compl, ← Fintype.card_congr pure]
    simp [Box, D5.S1.Ledger.BoundedTimeSlice.TailBox, Fintype.card_pi]
  constructor
  · have hh := hspan (fun r => ¬ discarded r) (by
      intro r
      by_cases hr : discarded r
      · refine ⟨0, by simp [discarded], hcollapse r hr.2⟩
      · exact ⟨r, hr, rfl⟩)
    exact (finrank_le_of_span_eq_top hh).trans_eq hcard
  · intro ha
    let e : Box a := Function.update 0 h ⟨1, by omega⟩
    have he : e ≠ 0 := by
      intro hz
      have hh := congrArg Fin.val (congrFun hz h)
      simp [e] at hh
    have hetail : tail h e = 0 := by funext i; simp [tail, e, i.property]
    apply hspan
    intro r
    by_cases hr : r = 0
    · exact ⟨e, he, by rw [hr, hcollapse e hetail]⟩
    · exact ⟨r, hr, rfl⟩
end D5.S3.Quantum.StationaryPreparation.HeadGram
