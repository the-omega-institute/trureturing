/- GID: D5/S3/Arith/InterlaceFan/Result
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classification of the minimal interlace fan faces containing nonzero rational points. -/

import D5.S3.Arith.InterlaceFan.Fourier
import D5.S3.Arith.InterlaceFan.Cyclotomic

noncomputable section
open Finset
open scoped BigOperators Classical
namespace D5.S3.Arith.InterlaceFan.Result
open Defs Fourier
open D5.S3.Arith.InterlaceFan.Cyclotomic

private lemma class_of_index (n j : ℕ) (hn : 2 ≤ n) (hj : j ∈ certIdx n) :
    n / n.gcd j ∈ n.divisors ∧ j ∈ orderClass n (n / n.gcd j) := by
  exact ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n j), by omega⟩,
    mem_filter.mpr ⟨hj, rfl⟩⟩

private lemma class_one (n : ℕ) (hn : 2 ≤ n) : orderClass n 1 = {0} := by
  ext j
  simp only [orderClass, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hj, he⟩
    have hm := Nat.div_mul_cancel (Nat.gcd_dvd_left n j)
    rw [he, one_mul] at hm
    have hd : n ∣ j := hm ▸ Nat.gcd_dvd_right n j
    exact Nat.eq_zero_of_dvd_of_lt hd (by simp only [certIdx, mem_range] at hj; omega)
  · rintro rfl
    simp [certIdx, Nat.div_self (by omega : 0 < n)]

private lemma class_nonempty (n d : ℕ) (hn : 2 ≤ n) (hd : d ∈ n.divisors) :
    (orderClass n d).Nonempty := by
  have hdvd := (Nat.mem_divisors.mp hd).1
  by_cases h1 : d = 1
  · subst d
    rw [class_one n hn]
    exact singleton_nonempty _
  · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    refine ⟨n / d, mem_filter.mpr ⟨?_, ?_⟩⟩
    · simp only [certIdx, mem_range]
      have hle : n / d ≤ n / 2 := Nat.div_le_div_left (by omega) (by omega)
      omega
    · rw [Nat.gcd_eq_right_iff_dvd.mpr (Nat.div_dvd_of_dvd hdvd)]
      exact Nat.div_div_self hdvd (by omega)

private lemma complement_nonempty (n d : ℕ) (hn : 2 ≤ n) :
    (certIdx n \ orderClass n d).Nonempty := by
  by_cases hd : d = 1
  · subst d
    refine ⟨1, mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · simp [certIdx]; omega
    · rw [class_one n hn]; simp
  · refine ⟨0, mem_sdiff.mpr ⟨by simp [certIdx], ?_⟩⟩
    simp [orderClass, Nat.div_self (by omega : 0 < n), Ne.symm hd]

private lemma zero_value_rational (n : ℕ) (x : Fin (n / 2) → ℝ)
    (hx : IsRationalPt x) : ∃ q : ℚ, I n 0 x = q := by
  choose q hq using hx
  refine ⟨-∑ k, q k, ?_⟩
  simp [I, hq]

private lemma face_value (n : ℕ) {S : Finset ℕ} (hS : S ⊆ certIdx n)
    {x : Fin (n / 2) → ℝ} (hx : x ∈ face n S) {s : ℕ} (hs : s ∈ S) :
    I n s x = interlaceNumber n x := by
  apply le_antisymm
  · exact Finset.le_sup' (fun j => I n j x) (hS hs)
  · exact Finset.sup'_le _ _ (fun j hj => hx s hs j hj)

private lemma zero_of_meets (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ certIdx n) (hmeet : ∀ d ∈ n.divisors, ∃ s ∈ S, s ∈ orderClass n d)
    (x : Fin (n / 2) → ℝ) (hf : x ∈ face n S) (hx : IsRationalPt x) : x = 0 := by
  obtain ⟨s, hs, hs1⟩ := hmeet 1 (Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩)
  have hs0 : 0 ∈ S := by
    have he : s = 0 := by simpa [class_one n hn] using hs1
    simpa [he] using hs
  obtain ⟨q, hq⟩ := zero_value_rational n x hx
  apply eq_zero_of_I_const n hn x q
  intro j hj
  obtain ⟨hd, hjd⟩ := class_of_index n j hn hj
  obtain ⟨s, hs, hsd⟩ := hmeet _ hd
  apply rational_const_on_orderClass n _ (by omega) (Nat.mem_divisors.mp hd).1 x hx q s j hsd hjd
  rw [face_value n hS hf hs, ← face_value n hS hf hs0, hq]

private lemma face_inclusion_iff (n : ℕ) (hn : 2 ≤ n) (S T : Finset ℕ)
    (hS : S ⊆ certIdx n) (hSne : S.Nonempty) (hSp : S ≠ certIdx n)
    (hT : T ⊆ certIdx n) : face n S ⊆ face n T ↔ T ⊆ S := by
  constructor
  · intro h
    obtain ⟨x, hx, _, he, _⟩ := exists_face_exact n hn S hS hSne hSp
    intro t ht
    exact (he t (hT ht)).mp (face_value n hT (h hx) ht)
  · exact fun h => face_antitone n h

private lemma rational_face_iff (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ certIdx n) (hne : S.Nonempty) :
    HasRatPt n S ↔ ∃ d ∈ n.divisors, Disjoint S (orderClass n d) := by
  constructor
  · rintro ⟨x, hf, hx0, hx⟩
    by_contra h
    apply hx0 (zero_of_meets n hn S hS ?_ x hf hx)
    intro d hd
    have hnd : ¬ Disjoint S (orderClass n d) := fun he => h ⟨d, hd, he⟩
    rw [Finset.disjoint_left] at hnd
    push Not at hnd
    obtain ⟨s, hs, ho⟩ := hnd
    exact ⟨s, hs, ho⟩
  · rintro ⟨d, hd, hdis⟩
    obtain ⟨x, hx, hv⟩ := rational_witness n d hn (Nat.mem_divisors.mp hd).1
    have hnot (s : ℕ) (hs : s ∈ S) : s ∉ orderClass n d :=
      fun h => Finset.disjoint_left.mp hdis hs h
    refine ⟨x, ?_, ?_, hx⟩
    · have hc : certIdx n \ orderClass n d ≠ certIdx n := by
        intro he
        obtain ⟨j, hj⟩ := class_nonempty n d hn hd
        have hmem : j ∈ certIdx n \ orderClass n d := by
          rw [he]
          exact (mem_filter.mp hj).1
        exact (mem_sdiff.mp hmem).2 hj
      apply (face_inclusion_iff n hn _ S sdiff_subset (complement_nonempty n d hn) hc hS).mpr
        (fun s hs => mem_sdiff.mpr ⟨hS hs, hnot s hs⟩)
      intro s hs j hj
      rw [hv s (mem_sdiff.mp hs).1, hv j hj, ite_eq_right (mem_sdiff.mp hs).2]
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      split_ifs <;> norm_num only [mul_one, mul_zero] <;> linarith
    · intro h0
      obtain ⟨s, hs⟩ := hne
      obtain ⟨j, hj⟩ := class_nonempty n d hn hd
      have hvj := hv j (mem_filter.mp hj).1
      have hvs := hv s (hS hs)
      rw [ite_eq_left hj] at hvj
      rw [ite_eq_right (hnot s hs)] at hvs
      simp only [h0, I, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hvj hvs
      norm_num only [mul_one, mul_zero] at hvj hvs
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith

private lemma maximal_iff (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ certIdx n) (hne : S.Nonempty) :
    (HasRatPt n S ∧ ∀ T ⊆ certIdx n, S ⊂ T → ¬ HasRatPt n T) ↔
      ∃ d ∈ n.divisors, S = certIdx n \ orderClass n d := by
  constructor
  · rintro ⟨hr, hm⟩
    obtain ⟨d, hd, hdis⟩ := (rational_face_iff n hn S hS hne).mp hr
    have hsub : S ⊆ certIdx n \ orderClass n d := by
      intro s hs
      exact mem_sdiff.mpr ⟨hS hs, fun ho => Finset.disjoint_left.mp hdis hs ho⟩
    refine ⟨d, hd, ?_⟩
    by_contra hneq
    apply hm _ sdiff_subset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneq⟩)
    exact (rational_face_iff n hn _ sdiff_subset (complement_nonempty n d hn)).mpr
      ⟨d, hd, Finset.sdiff_disjoint⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(rational_face_iff n hn _ sdiff_subset hne).mpr
      ⟨d, hd, Finset.sdiff_disjoint⟩, ?_⟩
    intro T hT hST hrT
    obtain ⟨e, he, hdis⟩ := (rational_face_iff n hn T hT (hne.mono hST.subset)).mp hrT
    obtain ⟨j, hj⟩ := class_nonempty n e hn he
    have hjJ := (mem_filter.mp hj).1
    have hjd : j ∈ orderClass n d := by
      by_contra h
      exact Finset.disjoint_left.mp hdis (hST.subset (mem_sdiff.mpr ⟨hjJ, h⟩)) hj
    have hed : e = d := (mem_filter.mp hj).2.symm.trans (mem_filter.mp hjd).2
    subst e
    have hTS : T ⊆ certIdx n \ orderClass n d := by
      intro t ht
      exact mem_sdiff.mpr ⟨hT ht, fun ho => Finset.disjoint_left.mp hdis ht ho⟩
    exact (not_le_of_gt hST) hTS

private lemma maximum_rational (n d : ℕ) (hn : 2 ≤ n)
    (x : Fin (n / 2) → ℝ) (hf : x ∈ face n (certIdx n \ orderClass n d))
    (hx : IsRationalPt x) : ∃ q : ℚ, interlaceNumber n x = q := by
  obtain ⟨q, hq⟩ := zero_value_rational n x hx
  by_cases hd : d = 1
  · subst d
    have he (j : ℕ) (hj : j ∈ (certIdx n).erase 0) :
        I n j x = interlaceNumber n x := by
      apply face_value n sdiff_subset hf
      exact mem_sdiff.mpr ⟨mem_of_mem_erase hj, by
        rw [class_one n hn]; simpa using (ne_of_mem_erase hj)⟩
    let w : ℕ → ℚ := fun j => if j = 0 ∨ n = 2 * j then 1 else 2
    let W : ℚ := ∑ j ∈ (certIdx n).erase 0, w j
    have hW : 0 < W := by
      apply Finset.sum_pos
      · intro j hj
        dsimp [w]
        split_ifs <;> norm_num
      · refine ⟨1, mem_erase.mpr ⟨by omega, ?_⟩⟩
        simp [certIdx]; omega
    have hw (j : ℕ) : certWeight n j = (w j : ℝ) := by
      dsimp [certWeight, w]
      split_ifs <;> norm_num
    have hm := I_weighted_sum n hn x
    rw [← Finset.sum_erase_add _ _ (by simp [certIdx] : 0 ∈ certIdx n)] at hm
    have hs : (∑ j ∈ (certIdx n).erase 0, certWeight n j * I n j x) =
        (W : ℝ) * interlaceNumber n x := by
      simp only [W, Rat.cast_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro j hj
      rw [he j hj, hw j]
    rw [hs, hq] at hm
    simp only [certWeight, true_or, ite_true, one_mul] at hm
    refine ⟨-q / W, ?_⟩
    push_cast
    apply (eq_div_iff (by exact_mod_cast hW.ne' : (W : ℝ) ≠ 0)).mpr
    linarith
  · refine ⟨q, ?_⟩
    rw [← face_value n sdiff_subset hf (s := 0), hq]
    exact mem_sdiff.mpr ⟨by simp [certIdx], by
      simp [orderClass, Nat.div_self (by omega : 0 < n), Ne.symm hd]⟩

private lemma minimal_face_values (n d : ℕ) (hn : 2 ≤ n) (hd : d ∈ n.divisors)
    (x : Fin (n / 2) → ℝ) (hf : x ∈ face n (certIdx n \ orderClass n d))
    (h0 : x ≠ 0) (hx : IsRationalPt x) :
    (∀ j ∈ orderClass n d, I n j x < interlaceNumber n x) ∧
      ∃ q : ℚ, interlaceNumber n x = q := by
  obtain ⟨q, hq⟩ := maximum_rational n d hn x hf hx
  refine ⟨?_, q, hq⟩
  intro j hj
  have hle : I n j x ≤ interlaceNumber n x :=
    Finset.le_sup' (fun j => I n j x) (mem_filter.mp hj).1
  apply lt_of_le_of_ne hle
  intro heq
  apply h0
  apply eq_zero_of_I_const n hn x q
  intro t ht
  by_cases htd : t ∈ orderClass n d
  · exact rational_const_on_orderClass n d (by omega) (Nat.mem_divisors.mp hd).1
      x hx q j t hj htd (heq.trans hq)
  · exact (face_value n sdiff_subset hf (mem_sdiff.mpr ⟨ht, htd⟩)).trans hq

/-- The rational-face criterion, maximal certificate sets, and rational interlace values. -/
theorem result : claim := by
  intro n hn
  exact ⟨rational_face_iff n hn, maximal_iff n hn, fun d hd x hf h0 hx =>
    minimal_face_values n d hn hd x hf h0 hx⟩

end D5.S3.Arith.InterlaceFan.Result
