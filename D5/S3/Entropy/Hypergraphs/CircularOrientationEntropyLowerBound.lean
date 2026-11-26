/- GID: D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound
   generality: I
   mirror-B: D5/B/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed-uniformity entropy lower bound for circular orientations. -/

import D5.S0.Certificates.Hypergraphs.CircularOrientationEntropy
import D5.S3.Entropy.Hypergraphs.FiniteFiber
import D5.S3.Entropy.Hypergraphs.FiniteFourier
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Circular geometry and the finite orientation law.

whole_theorem_one_two: proof_shape: content;
admission_basis: escape-witness; escape_witness: actual_characteristic_bound.
The witness constructs the actual circular-law coordinate fibres and joint
endpoint-event average, rather than assuming either distributional identity.
The concrete geometric, cardinality and normalization auxiliaries are consumed
by this bound and the final entropy estimate; bind-only auxiliaries supply no
independent admission basis. All private results lie on the main proof path. -/

namespace D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound

open scoped BigOperators
open D5.S0.Certificates.Hypergraphs
open D5.S3.Entropy.Hypergraphs.FiniteFiber
open D5.S3.Entropy.Hypergraphs.FiniteFourier

noncomputable def a (r : ℕ) : ℝ := (1 - 1 / (r : ℝ)) ^ (r - 1)
noncomputable def q (r : ℕ) : ℝ := a r * (1 - a r)
noncomputable def b (r : ℕ) : ℝ := ((r : ℝ) - 1) / (r : ℝ) ^ 2
noncomputable def c (r : ℕ) : ℝ := q r * (1 - Real.exp (-2 * b r))
noncomputable def K (r : ℕ) : ℝ := max (1 / 2) ((1 / 2) * Real.logb 2 (Real.pi / c r))

private theorem circular_mem {n r : ℕ} (hr : r < n) (i v : Fin n) :
    v ∈ CircularOrientationEntropy.circular n r i ↔
      (i.val ≤ v.val ∧ v.val < i.val + r) ∨
      (i.val ≤ v.val + n ∧ v.val + n < i.val + r) := by
  classical
  simp only [CircularOrientationEntropy.circular, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hv⟩
    have he : (i.val + j) % n = v.val := congrArg Fin.val hv
    have hi := i.isLt
    have hv' := v.isLt
    have hsum : i.val + j < n + n := by omega
    have hm := Nat.mod_add_div (i.val + j) n
    have hd : (i.val + j) / n < 2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    have hz : ∀ d : ℕ, d < 2 → d = 0 ∨ d = 1 := by omega
    rcases hz _ hd with h | h
    · simp only [h, Nat.mul_zero, Nat.add_zero] at hm
      left; omega
    · simp only [h, Nat.mul_one] at hm
      right; omega
  · intro h
    rcases h with ⟨hiv, hvr⟩ | ⟨hiv, hvr⟩
    · refine ⟨v.val - i.val, by omega, ?_⟩
      apply Fin.ext
      change (i.val + (v.val - i.val)) % n = v.val
      rw [Nat.add_sub_of_le hiv, Nat.mod_eq_of_lt v.isLt]
    · refine ⟨v.val + n - i.val, by omega, ?_⟩
      apply Fin.ext
      change (i.val + (v.val + n - i.val)) % n = v.val
      rw [Nat.add_sub_of_le hiv, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]

private theorem circular_card {n r : ℕ} (hr : r < n) (i : Fin n) :
    (CircularOrientationEntropy.circular n r i).card = r := by
  classical
  unfold CircularOrientationEntropy.circular
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j hj k hk he
  have hj' : j < r := Finset.mem_range.mp hj
  have hk' : k < r := Finset.mem_range.mp hk
  have hmod : (i.val + j) % n = (i.val + k) % n := congrArg Fin.val he
  have hcancel : j % n = k % n := Nat.ModEq.add_left_cancel' i.val hmod
  simpa [Nat.mod_eq_of_lt (hj'.trans hr), Nat.mod_eq_of_lt (hk'.trans hr)] using hcancel

private theorem selected_edge_no_wrap {n r : ℕ} (hr : 0 < r)
    (j : ℕ) (hj : j < n / (2 * r)) : 2 * r * j + r ≤ n := by
  have h := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * r)).mp (Nat.succ_le_of_lt hj)
  nlinarith

private theorem selected_edges_disjoint {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j k : ℕ) (hj : j < n / (2 * r)) (hk : k < n / (2 * r)) (hjk : j ≠ k) :
    Disjoint (CircularOrientationEntropy.circular n r ⟨2 * r * j, by
      have := selected_edge_no_wrap hr j hj; omega⟩)
      (CircularOrientationEntropy.circular n r ⟨2 * r * k, by
      have := selected_edge_no_wrap hr k hk; omega⟩) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvj hvk
  rw [circular_mem hn] at hvj hvk
  have hnj := selected_edge_no_wrap hr j hj
  have hnk := selected_edge_no_wrap hr k hk
  simp only at hvj hvk
  have hv := v.isLt
  rcases hvj with hjv | hjv <;> rcases hvk with hkv | hkv
  · rcases lt_or_gt_of_ne hjk with h | h <;> nlinarith
  · omega
  · omega
  · omega

private def leftBlock (n r s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val ≠ s ∧
    ((i.val ≤ s ∧ s < i.val + r) ∨ (i.val ≤ s + n ∧ s + n < i.val + r))

private def rightBlock (n r s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => s < i.val ∧ i.val < s + r

private theorem selected_block_end {n r : ℕ} (hr : 0 < r)
    (j : ℕ) (hj : j < n / (2 * r)) : 2 * r * j + 2 * r ≤ n := by
  have h := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * r)).mp (Nat.succ_le_of_lt hj)
  nlinarith

private theorem leftBlock_rightBlock_disjoint {n r s : ℕ} (hn : 2 * r ≤ n)
    (_hs : s + r ≤ n) : Disjoint (leftBlock n r s) (rightBlock n r s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [leftBlock, rightBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rcases hi.2 with h | h <;> omega

private theorem endpoint_left {n r s : ℕ} (hr : r < n) (hs : s < n) (i : Fin n) :
    i ∈ leftBlock n r s ↔ i.val ≠ s ∧
      (⟨s, hs⟩ : Fin n) ∈ CircularOrientationEntropy.circular n r i := by
  simp only [leftBlock, Finset.mem_filter, Finset.mem_univ, true_and, circular_mem hr]

private theorem endpoint_right {n r s : ℕ} (hr : 0 < r) (hn : r < n)
    (hs : s + r ≤ n) (i : Fin n) :
    i ∈ rightBlock n r s ↔ i.val ≠ s ∧
      (⟨s + r - 1, by omega⟩ : Fin n) ∈ CircularOrientationEntropy.circular n r i := by
  simp only [rightBlock, Finset.mem_filter, Finset.mem_univ, true_and, circular_mem hn]
  have hi := i.isLt
  constructor
  · intro h
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  · rintro ⟨hne, h | h⟩ <;> omega

private theorem endpoint_blocks_pairwise_disjoint {n r : ℕ} (hr : 0 < r)
    (j k : ℕ) (hj : j < n / (2 * r)) (hk : k < n / (2 * r)) (hjk : j ≠ k) :
    Disjoint (leftBlock n r (2 * r * j) ∪ rightBlock n r (2 * r * j))
      (leftBlock n r (2 * r * k) ∪ rightBlock n r (2 * r * k)) := by
  have hnj := selected_block_end hr j hj
  have hnk := selected_block_end hr k hk
  apply Finset.disjoint_left.mpr
  intro i hi hk'
  have hi' := i.isLt
  simp only [Finset.mem_union, leftBlock, rightBlock, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi hk'
  have hsep : 2 * r * j + 2 * r ≤ 2 * r * k ∨
      2 * r * k + 2 * r ≤ 2 * r * j := by
    rcases lt_or_gt_of_ne hjk with h | h
    · left; nlinarith
    · right; nlinarith
  rcases hi with ⟨hne, h | h⟩ | h <;>
    rcases hk' with ⟨hne', h' | h'⟩ | h' <;>
    rcases hsep with hsep | hsep <;> omega

private theorem selected_not_in_endpoint_blocks {n r : ℕ} (hr : 0 < r)
    (j k : ℕ) (hj : j < n / (2 * r)) (hk : k < n / (2 * r)) :
    (⟨2 * r * k, by have := selected_block_end hr k hk; omega⟩ : Fin n) ∉
      leftBlock n r (2 * r * j) ∪ rightBlock n r (2 * r * j) := by
  have hnj := selected_block_end hr j hj
  have hnk := selected_block_end hr k hk
  simp only [Finset.mem_union, leftBlock, rightBlock, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases he : j = k
  · subst k; omega
  · have hsep : 2 * r * j + 2 * r ≤ 2 * r * k ∨
        2 * r * k + 2 * r ≤ 2 * r * j := by
      rcases lt_or_gt_of_ne he with h | h
      · left; nlinarith
      · right; nlinarith
    rcases hsep with hsep | hsep <;> omega

private def leftPick (n s d : ℕ) : ℕ :=
  if d < s then s - 1 - d else s + n - 1 - d

private lemma leftPick_lt {n r s d : ℕ} (hr : 0 < r) (hrn : r < n)
    (hs : s + r ≤ n) (_hd : d < r - 1) : leftPick n s d < n := by
  dsimp [leftPick]
  split_ifs <;> omega

private theorem leftBlock_card {n r s : ℕ} (hr : 0 < r) (hrn : r < n)
    (hs : s + r ≤ n) : (leftBlock n r s).card = r - 1 := by
  classical
  have hc : (Finset.range (r - 1)).card = (leftBlock n r s).card := by
    apply Finset.card_bij (fun d hd =>
      (⟨leftPick n s d, leftPick_lt hr hrn hs (Finset.mem_range.mp hd)⟩ : Fin n))
    · intro d hd
      have hd' := Finset.mem_range.mp hd
      simp only [leftBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [leftPick]
      split_ifs <;> omega
    · intro d hd e he hde
      have hd' := Finset.mem_range.mp hd
      have he' := Finset.mem_range.mp he
      have hv := congrArg Fin.val hde
      dsimp [leftPick] at hv
      split_ifs at hv <;> omega
    · intro i hi
      have hin := i.isLt
      simp only [leftBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_cases hbefore : i.val < s
      · have hd : s - 1 - i.val < r - 1 := by omega
        refine ⟨s - 1 - i.val, Finset.mem_range.mpr hd, ?_⟩
        apply Fin.ext
        dsimp [leftPick]
        split_ifs <;> omega
      · have hd : s + n - 1 - i.val < r - 1 := by omega
        refine ⟨s + n - 1 - i.val, Finset.mem_range.mpr hd, ?_⟩
        apply Fin.ext
        dsimp [leftPick]
        split_ifs <;> omega
  simpa only [Finset.card_range] using hc.symm

private theorem rightBlock_card {n r s : ℕ} (hr : 0 < r)
    (hs : s + r ≤ n) : (rightBlock n r s).card = r - 1 := by
  classical
  have hc : (Finset.range (r - 1)).card = (rightBlock n r s).card := by
    apply Finset.card_bij (fun d hd =>
      (⟨s + 1 + d, by have := Finset.mem_range.mp hd; omega⟩ : Fin n))
    · intro d hd
      have := Finset.mem_range.mp hd
      simp only [rightBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro d hd e he hde
      have hv := congrArg Fin.val hde
      dsimp at hv
      omega
    · intro i hi
      simp only [rightBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨i.val - s - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      dsimp
      omega
  simpa only [Finset.card_range] using hc.symm

private theorem constants_pos {r : ℕ} (hr : 3 ≤ r) :
    0 < a r ∧ a r < 1 ∧ 0 < q r ∧ 0 < b r ∧ 0 < c r := by
  have hrR : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hr0 : (0 : ℝ) < r := by positivity
  have hbase0 : 0 < 1 - 1 / (r : ℝ) := by
    have := (div_lt_one hr0).2 hrR
    linarith
  have hbase1 : 1 - 1 / (r : ℝ) < 1 := by
    have : 0 < 1 / (r : ℝ) := by positivity
    linarith
  have ha0 : 0 < a r := pow_pos hbase0 _
  have ha1 : a r < 1 := pow_lt_one₀ hbase0.le hbase1 (by omega)
  have hq : 0 < q r := mul_pos ha0 (sub_pos.mpr ha1)
  have hb : 0 < b r := div_pos (sub_pos.mpr hrR) (sq_pos_of_pos hr0)
  have he : Real.exp (-2 * b r) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  exact ⟨ha0, ha1, hq, hb, mul_pos hq (sub_pos.mpr he)⟩

private theorem variance_lower {r k : ℕ} (hr : 0 < r) (hk : 1 ≤ k) (hkr : k ≤ r - 1) :
    b r ≤ ((k : ℝ) / r) * (1 - (k : ℝ) / r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkrR : (k : ℝ) ≤ r - 1 := by
    have h : (k : ℝ) + 1 ≤ r := by exact_mod_cast (show k + 1 ≤ r by omega)
    linarith
  have hh : 0 ≤ ((k : ℝ) - 1) * ((r : ℝ) - 1 - k) :=
    mul_nonneg (by linarith) (by linarith)
  unfold b
  apply (div_le_iff₀ (sq_pos_of_pos hrR)).2
  field_simp
  nlinarith

private abbrev Orientation {n : ℕ} (E : Fin n → Finset (Fin n)) :=
  ↥(Fintype.piFinset E)

private theorem orientation_card {n r : ℕ} (E : Fin n → Finset (Fin n))
    (hE : ∀ i, (E i).card = r) : Fintype.card (Orientation E) = r ^ n := by
  classical
  simp only [Orientation, Fintype.card_coe, Fintype.card_piFinset, hE,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem orientation_fiber_card {n : ℕ} (E : Fin n → Finset (Fin n)) (k : ℕ) :
    (Finset.univ.filter (fun o : Orientation E => OrientationEntropyBalance.X E o.val = k)).card =
      ((Fintype.piFinset E).filter (fun o => OrientationEntropyBalance.X E o = k)).card := by
  classical
  apply Finset.card_bij (fun o _ => o.val)
  · intro o ho
    exact Finset.mem_filter.mpr ⟨o.property, (Finset.mem_filter.mp ho).2⟩
  · intro o ho p hp he
    exact Subtype.ext he
  · intro o ho
    refine ⟨⟨o, (Finset.mem_filter.mp ho).1⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (Finset.mem_filter.mp ho).2

private theorem orientation_count_bound {n : ℕ} (E : Fin n → Finset (Fin n))
    (o : Fin n → Fin n) : OrientationEntropyBalance.X E o ≤ n := by
  unfold OrientationEntropyBalance.X
  exact (Finset.card_image_le).trans (by simp)

private theorem orientation_entropy_eq {n r : ℕ} (E : Fin n → Finset (Fin n))
    (hE : ∀ i, (E i).card = r) :
    OrientationEntropyBalance.entropyX r E =
      ∑ k ∈ Finset.range (n + 1),
        let p := ((Finset.univ.filter (fun o : Orientation E =>
          OrientationEntropyBalance.X E o.val = k)).card : ℝ) / Fintype.card (Orientation E);
        -p * Real.logb 2 p := by
  classical
  unfold OrientationEntropyBalance.entropyX
  rw [OrientationEntropyBalance.orientations_eq]
  simp_rw [orientation_fiber_card, orientation_card E hE, Nat.cast_pow]

private theorem bernoulli_norm_sq (p t : ℝ) :
    ‖1 - (p : ℂ) + (p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ ^ 2 =
      1 - 4 * p * (1 - p) * Real.sin (t / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, mul_one, zero_add, Real.exp_zero, one_mul, Complex.add_im,
    Complex.sub_im, Complex.one_im, add_zero]
  have ht := Real.sin_sq_add_cos_sq t
  have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    convert Real.cos_two_mul_eq_one_sub (t / 2) using 1; ring_nf
  linear_combination p ^ 2 * ht + (2 * p * (1 - p)) * hc

private theorem bernoulli_norm_bound (p t : ℝ) :
    ‖1 - (p : ℂ) + (p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ ≤
      Real.exp (-2 * p * (1 - p) * Real.sin (t / 2) ^ 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [bernoulli_norm_sq, ← Real.exp_nat_mul]
  have h := Real.add_one_le_exp (-4 * p * (1 - p) * Real.sin (t / 2) ^ 2)
  convert h using 1 <;> ring

private def startIndex {n r : ℕ} (hr : 0 < r) (j : Fin (n / (2 * r))) : Fin n :=
  ⟨2 * r * j.val, by have := selected_block_end hr j.val j.isLt; omega⟩

private def selectedSet {n r : ℕ} (hr : 0 < r) : Finset (Fin n) :=
  Finset.univ.image (startIndex (n := n) hr)

private def revealedImage {n r : ℕ} (hr : 0 < r) (o : Fin n → Fin n) : Finset (Fin n) :=
  (Finset.univ \ selectedSet hr).image o

private def goodEndpoint {n r : ℕ} (hr : 0 < r) (j : Fin (n / (2 * r)))
    (o : Fin n → Fin n) : Prop :=
  (∀ i ∈ leftBlock n r (2 * r * j.val), o i = startIndex hr j → False) ∧
  ∃ i ∈ rightBlock n r (2 * r * j.val),
    o i = (⟨2 * r * j.val + r - 1, by
      have := selected_block_end hr j.val j.isLt; omega⟩ : Fin n)

private theorem endpoint_block_revealed {n r : ℕ} (hr : 0 < r)
    (j : Fin (n / (2 * r))) (i : Fin n)
    (hi : i ∈ leftBlock n r (2 * r * j.val) ∪ rightBlock n r (2 * r * j.val)) :
    i ∈ Finset.univ \ selectedSet hr := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, selectedSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  rintro ⟨k, rfl⟩
  exact selected_not_in_endpoint_blocks hr j.val k.val j.isLt k.isLt hi

private theorem goodEndpoint_absent_present {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : Orientation (CircularOrientationEntropy.circular n r))
    (hg : goodEndpoint hr j o.val) :
    startIndex hr j ∉ revealedImage hr o.val ∧
    (⟨2 * r * j.val + r - 1, by
      have := selected_block_end hr j.val j.isLt; omega⟩ : Fin n) ∈ revealedImage hr o.val := by
  classical
  constructor
  · intro hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hneq : i.val ≠ 2 * r * j.val := by
      intro h
      have hei : i = startIndex hr j := Fin.ext h
      have hsel : i ∈ selectedSet hr := by
        rw [hei]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      exact (Finset.mem_sdiff.mp hi).2 hsel
    have hmem : startIndex hr j ∈ CircularOrientationEntropy.circular n r i := by
      rw [← he]
      exact (Fintype.mem_piFinset.mp o.property) i
    have hl : i ∈ leftBlock n r (2 * r * j.val) :=
      (endpoint_left hn (startIndex hr j).isLt i).2 ⟨hneq, hmem⟩
    exact hg.1 i hl he
  · obtain ⟨i, hi, he⟩ := hg.2
    exact Finset.mem_image.mpr ⟨i,
      endpoint_block_revealed hr j i (Finset.mem_union_right _ hi), he⟩

private theorem goodEndpoint_missing_card {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : Orientation (CircularOrientationEntropy.circular n r))
    (hg : goodEndpoint hr j o.val) :
    1 ≤ ((CircularOrientationEntropy.circular n r (startIndex hr j))
      \ revealedImage hr o.val).card ∧
    ((CircularOrientationEntropy.circular n r (startIndex hr j)) \
      revealedImage hr o.val).card ≤ r - 1 := by
  have hpair := goodEndpoint_absent_present hr hn j o hg
  have he := selected_block_end hr j.val j.isLt
  have hstart : startIndex hr j ∈ CircularOrientationEntropy.circular n r (startIndex hr j) := by
    rw [circular_mem hn]
    left; dsimp [startIndex]; omega
  have hend : (⟨2 * r * j.val + r - 1, by omega⟩ : Fin n) ∈
      CircularOrientationEntropy.circular n r (startIndex hr j) := by
    rw [circular_mem hn]
    left; dsimp [startIndex]; omega
  constructor
  · exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨_, Finset.mem_sdiff.mpr ⟨hstart, hpair.1⟩⟩)
  · have hproper : (CircularOrientationEntropy.circular n r (startIndex hr j))
    \ revealedImage hr o.val ⊂
        CircularOrientationEntropy.circular n r (startIndex hr j) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro h
      have hx := hend
      rw [← h] at hx
      exact (Finset.mem_sdiff.mp hx).2 hpair.2
    have hlt := Finset.card_lt_card hproper
    rw [circular_card hn] at hlt
    omega

private theorem goodEndpoint_variance {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : Orientation (CircularOrientationEntropy.circular n r))
    (hg : goodEndpoint hr j o.val) :
    b r ≤
      ((((CircularOrientationEntropy.circular n r (startIndex hr j))
        \ revealedImage hr o.val).card : ℝ) / r) *
      (1 - (((CircularOrientationEntropy.circular n r (startIndex hr j))
        \ revealedImage hr o.val).card : ℝ) / r) := by
  have h := goodEndpoint_missing_card hr hn j o hg
  exact variance_lower hr h.1 h.2

private theorem all_avoid_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] (v : ∀ i, β i) :
    (Finset.univ.filter (fun f : ∀ i, β i => ∀ i, f i ≠ v i)).card =
      ∏ i, (Fintype.card (β i) - 1) := by
  have he : Finset.univ.filter (fun f : ∀ i, β i => ∀ i, f i ≠ v i) =
      Fintype.piFinset (fun i => Finset.univ.erase (v i)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_erase, and_true]
  rw [he, Fintype.card_piFinset]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

private theorem all_avoid_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] (v : ∀ i, β i)
    (r : ℕ) (hr : 0 < r) (hcard : ∀ i, Fintype.card (β i) = r) :
    (∑ f : ∀ i, β i, if ∀ i, f i ≠ v i then (1 : ℝ) else 0) /
      Fintype.card (∀ i, β i) = (1 - 1 / (r : ℝ)) ^ Fintype.card ι := by
  classical
  rw [Finset.sum_boole, all_avoid_count]
  simp_rw [hcard]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_pi]
  simp_rw [hcard]
  simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  rw [← div_pow]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  field_simp

private theorem exp_chord_bound (B s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - Real.exp (-2 * B)) * s ≤ 1 - Real.exp (-2 * B * s) := by
  have h := convexOn_exp.2 (Set.mem_univ (-2 * B)) (Set.mem_univ 0)
    hs0 (sub_nonneg.mpr hs1) (show s + (1 - s) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have he : s * (-2 * B) = -2 * B * s := by ring
  rw [he] at h
  linarith

private theorem endpoint_generating_bound {r : ℕ} (hr : 3 ≤ r) (m : ℕ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - q r + q r * Real.exp (-2 * b r * s)) ^ m ≤
      Real.exp (-(m : ℝ) * c r * s) := by
  have hpos := constants_pos hr
  have hq : q r ≤ 1 := by dsimp [q]; nlinarith [hpos.1, hpos.2.1]
  have hbase : 0 ≤ 1 - q r + q r * Real.exp (-2 * b r * s) :=
    add_nonneg (sub_nonneg.mpr hq) (mul_nonneg hpos.2.2.1.le (Real.exp_pos _).le)
  have ht : 1 - q r + q r * Real.exp (-2 * b r * s) ≤
      Real.exp (-q r * (1 - Real.exp (-2 * b r * s))) := by
    have h := Real.add_one_le_exp (-q r * (1 - Real.exp (-2 * b r * s)))
    convert h using 1; ring
  calc
    _ ≤ (Real.exp (-q r * (1 - Real.exp (-2 * b r * s)))) ^ m :=
      pow_le_pow_left₀ hbase ht _
    _ = Real.exp ((m : ℝ) * (-q r * (1 - Real.exp (-2 * b r * s)))) := by
      rw [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_chord_bound (b r) s hs0 hs1)
        (mul_nonneg (Nat.cast_nonneg m) hpos.2.2.1.le)
      dsimp [c]
      nlinarith

private theorem circular_entropy_nonneg {n r : ℕ} (hr : 0 < r) (hn : r < n) :
    0 ≤ OrientationEntropyBalance.entropyX r (CircularOrientationEntropy.circular n r) := by
  classical
  let E := CircularOrientationEntropy.circular n r
  let : Nonempty (Orientation E) := ⟨⟨id, Fintype.mem_piFinset.mpr fun i => by
    rw [circular_mem hn]
    left; dsimp; omega⟩⟩
  rw [orientation_entropy_eq E (circular_card hn)]
  have h := finite_entropy_lower (fun o : Orientation E => OrientationEntropyBalance.X E o.val)
    n (fun o => orientation_count_bound E o.val) 1 (by norm_num)
    (fun k => finite_mass_le_one _ k)
  simpa using h

private theorem small_n_entropy_bound {n r : ℕ} (hr : 3 ≤ r) (hn : r < n)
    (hn2 : n < 2 * r) :
    (1 / 2 : ℝ) * Real.logb 2 ((n : ℝ) / r) - K r ≤
      OrientationEntropyBalance.entropyX r (CircularOrientationEntropy.circular n r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (n : ℝ) / r ≤ 2 := by
    apply (div_le_iff₀ hr0).2
    exact_mod_cast (show n ≤ 2 * r by omega)
  have hlog : Real.logb 2 ((n : ℝ) / r) ≤ 1 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (div_pos hn0 hr0) hnr
    rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  have hK : (1 / 2 : ℝ) ≤ K r := le_max_left _ _
  have he := circular_entropy_nonneg (show 0 < r by omega) hn
  linarith

private abbrev Choice (n r : ℕ) (i : Fin n) :=
  ↥(CircularOrientationEntropy.circular n r i)

private def endpointBlocks (n r : ℕ) (j : Fin (n / (2 * r))) : Finset (Fin n) :=
  leftBlock n r (2 * r * j.val) ∪ rightBlock n r (2 * r * j.val)

private def leftTarget {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (i : leftBlock n r (2 * r * j.val)) : Choice n r i.val :=
  ⟨startIndex hr j, ((endpoint_left hn (startIndex hr j).isLt i.val).mp i.property).2⟩

private def rightTarget {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (i : rightBlock n r (2 * r * j.val)) : Choice n r i.val :=
  ⟨⟨2 * r * j.val + r - 1, by have := selected_block_end hr j.val j.isLt; omega⟩,
    ((endpoint_right hr hn (selected_edge_no_wrap hr j.val j.isLt) i.val).mp i.property).2⟩

private def blockEvent {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : ∀ i : endpointBlocks n r j, Choice n r i.val) : Prop :=
  (∀ i : leftBlock n r (2 * r * j.val),
    o ⟨i.val, Finset.mem_union_left _ i.property⟩ ≠ leftTarget hr hn j i) ∧
  ¬ (∀ i : rightBlock n r (2 * r * j.val),
    o ⟨i.val, Finset.mem_union_right _ i.property⟩ ≠ rightTarget hr hn j i)

open scoped Classical in
private theorem block_event_average {n r : ℕ} (hr : 0 < r) (hn : r < n) (hn2 : 2 * r ≤ n)
    (j : Fin (n / (2 * r))) (z : ℝ) :
    (∑ o : ∀ i : endpointBlocks n r j, Choice n r i.val,
      if blockEvent hr hn j o then z else 1) /
      Fintype.card (∀ i : endpointBlocks n r j, Choice n r i.val) = 1 - q r + q r * z := by
  classical
  let : ∀ i : Fin n, Nonempty (Choice n r i) := fun i => ⟨⟨i, by
    rw [circular_mem hn]; left; omega⟩⟩
  have hL := all_avoid_sum (leftTarget hr hn j) r hr (fun i => by
    simp only [Choice, Fintype.card_coe, circular_card hn])
  have hR := all_avoid_sum (rightTarget hr hn j) r hr (fun i => by
    simp only [Choice, Fintype.card_coe, circular_card hn])
  rw [Fintype.card_coe, leftBlock_card hr hn (selected_edge_no_wrap hr j.val j.isLt)] at hL
  rw [Fintype.card_coe, rightBlock_card hr (selected_edge_no_wrap hr j.val j.isLt)] at hR
  have h := two_block_event_average (Choice n r)
    (leftBlock n r (2 * r * j.val)) (rightBlock n r (2 * r * j.val))
    (leftBlock_rightBlock_disjoint hn2 (selected_edge_no_wrap hr j.val j.isLt))
    (leftTarget hr hn j) (rightTarget hr hn j) (a r) (a r) z hL hR
  unfold blockEvent endpointBlocks q
  convert h using 2
  · apply Finset.sum_congr rfl
    intro o ho
    exact (ite_eq_ite _ _ _).2 trivial

private theorem block_event_restrict {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : ∀ i, Choice n r i) :
    blockEvent hr hn j (fun i => o i.val) ↔ goodEndpoint hr j (fun i => (o i).val) := by
  classical
  simp only [blockEvent, goodEndpoint, leftTarget, rightTarget, ne_eq, Subtype.ext_iff,
    Subtype.forall, not_forall, not_not]
  constructor <;> rintro ⟨hl, i, hi, he⟩ <;> exact ⟨hl, i, hi, he⟩

open scoped Classical in
private theorem endpoint_joint_average {n r : ℕ} (hr : 0 < r) (hn : r < n) (hn2 : 2 * r ≤ n)
    (z : ℝ) :
    (∑ o : ∀ i, Choice n r i, ∏ j : Fin (n / (2 * r)),
      if goodEndpoint hr j (fun i => (o i).val) then z else 1) /
      Fintype.card (∀ i, Choice n r i) = (1 - q r + q r * z) ^ (n / (2 * r)) := by
  classical
  let : ∀ i : Fin n, Nonempty (Choice n r i) := fun i => ⟨⟨i, by
    rw [circular_mem hn]; left; omega⟩⟩
  have hD : ∀ j k : Fin (n / (2 * r)), j ≠ k →
      Disjoint (endpointBlocks n r j) (endpointBlocks n r k) := by
    intro j k h
    exact endpoint_blocks_pairwise_disjoint hr j.val k.val j.isLt k.isLt
      (fun he => h (Fin.ext he))
  have h := block_average_product (Choice n r) (endpointBlocks n r) hD
    (fun j o => if blockEvent hr hn j o then z else 1)
  simp_rw [block_event_restrict, block_event_average hr hn hn2] at h
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

private lemma circular_floor_four_mul (r n : ℕ) (hr : 3 ≤ r) (hn : 2 * r ≤ n) :
    n ≤ 4 * r * (n / (2 * r)) := by
  have hd : 0 < 2 * r := by omega
  have hm : 0 < n / (2 * r) := Nat.div_pos hn hd
  have hrem : n % (2 * r) < 2 * r := Nat.mod_lt n hd
  have heq := Nat.mod_add_div n (2 * r)
  have hmul : 2 * r ≤ 2 * r * (n / (2 * r)) := by nlinarith
  nlinarith

private lemma circular_point_constant_bound (r n : ℕ) (hr : 3 ≤ r)
    (hn : 2 * r ≤ n) {c : ℝ} (hc : 0 < c) :
    Real.sqrt Real.pi / (2 * Real.sqrt ((n / (2 * r) : ℕ) * c)) ≤
      Real.sqrt (Real.pi * (r : ℝ) / (c * (n : ℝ))) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmN : 0 < n / (2 * r) := Nat.div_pos hn (by omega)
  have hm : 0 < ((n / (2 * r) : ℕ) : ℝ) := by exact_mod_cast hmN
  have hfloor : (n : ℝ) ≤ 4 * (r : ℝ) * ((n / (2 * r) : ℕ) : ℝ) := by
    exact_mod_cast circular_floor_four_mul r n hr hn
  have hfrac : Real.pi / (4 * ((n / (2 * r) : ℕ) : ℝ) * c) ≤
      Real.pi * (r : ℝ) / (c * (n : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have h := mul_le_mul_of_nonneg_left hfloor
      (mul_nonneg Real.pi_pos.le hc.le)
    nlinarith
  have hshape : Real.sqrt Real.pi /
        (2 * Real.sqrt (((n / (2 * r) : ℕ) : ℝ) * c)) =
      Real.sqrt (Real.pi / (4 * ((n / (2 * r) : ℕ) : ℝ) * c)) := by
    rw [Real.sqrt_div Real.pi_pos.le]
    rw [show 4 * ((n / (2 * r) : ℕ) : ℝ) * c =
      (4 : ℝ) * (((n / (2 * r) : ℕ) : ℝ) * c) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
        Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4]
  rw [hshape]
  exact Real.sqrt_le_sqrt hfrac

private lemma circular_point_log_identity (r n : ℕ) (hr : 3 ≤ r)
    (hn : 2 * r ≤ n) {c : ℝ} (hc : 0 < c) :
    -Real.logb 2 (Real.sqrt (Real.pi * (r : ℝ) / (c * (n : ℝ)))) =
      (1 / 2 : ℝ) * Real.logb 2 ((n : ℝ) / (r : ℝ)) -
        (1 / 2 : ℝ) * Real.logb 2 (Real.pi / c) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hratio : 0 < Real.pi * (r : ℝ) / (c * (n : ℝ)) := by positivity
  rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hratio,
    Real.logb_div (mul_ne_zero Real.pi_ne_zero hr0.ne') (mul_ne_zero hc.ne' hn0.ne'),
    Real.logb_mul Real.pi_ne_zero hr0.ne', Real.logb_mul hc.ne' hn0.ne',
    Real.logb_div hn0.ne' hr0.ne', Real.logb_div Real.pi_ne_zero hc.ne']
  ring

private theorem startIndex_injective {n r : ℕ} (hr : 0 < r) :
    Function.Injective (startIndex (n := n) hr) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [startIndex] at hv
  nlinarith

private theorem selected_set_edges_disjoint {n r : ℕ} (hr : 0 < r) (hn : r < n) :
    ∀ i j : selectedSet (n := n) hr, i ≠ j →
      Disjoint (CircularOrientationEntropy.circular n r i.val)
        (CircularOrientationEntropy.circular n r j.val) := by
  intro i j hne
  obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp i.property
  obtain ⟨b, hb, hbj⟩ := Finset.mem_image.mp j.property
  have hab : a ≠ b := by
    intro h
    apply hne
    apply Subtype.ext
    rw [← hai, ← hbj, h]
  rw [← hai, ← hbj]
  exact selected_edges_disjoint hr hn a.val b.val a.isLt b.isLt
    (fun h => hab (Fin.ext h))

private theorem selected_product {n r : ℕ} (hr : 0 < r) (f : Fin n → ℝ) :
    (∏ i : selectedSet (n := n) hr, f i.val) =
      ∏ j : Fin (n / (2 * r)), f (startIndex hr j) := by
  rw [Finset.prod_coe_sort (selectedSet hr) f]
  unfold selectedSet
  rw [Finset.prod_image]
  exact (startIndex_injective hr).injOn

private theorem actual_revealed_split {n r : ℕ} (hr : 0 < r)
    (a : ∀ i : {i : Fin n // i ∉ selectedSet hr}, Choice n r i.val)
    (b : ∀ i : selectedSet hr, Choice n r i.val) :
    revealedImage hr (fun i => (splitCompletion (CircularOrientationEntropy.circular n r)
      (selectedSet hr) a b i).val) =
      splitRevealedImage (CircularOrientationEntropy.circular n r) (selectedSet hr) a := by
  classical
  ext v
  simp only [revealedImage, splitRevealedImage, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    simpa only [splitCompletion, dite_eq_right hi] using he
  · rintro ⟨i, hi⟩
    refine ⟨i.val, i.property, ?_⟩
    simpa only [splitCompletion, dite_eq_right i.property] using hi

open scoped Classical in
private theorem actual_factor_bound {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (j : Fin (n / (2 * r))) (o : Orientation (CircularOrientationEntropy.circular n r)) (t : ℝ) :
    ‖1 - (((CircularOrientationEntropy.circular n r (startIndex hr j))
      \ revealedImage hr o.val).card : ℂ) / r +
      (((CircularOrientationEntropy.circular n r (startIndex hr j))
        \ revealedImage hr o.val).card : ℂ) / r *
        Complex.exp ((t : ℂ) * Complex.I)‖ ≤
      if goodEndpoint hr j o.val then Real.exp (-2 * b r * Real.sin (t / 2) ^ 2) else 1 := by
  classical
  let k := ((CircularOrientationEntropy.circular n r (startIndex hr j))
    \ revealedImage hr o.val).card
  let p : ℝ := (k : ℝ) / r
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hk : k ≤ r := by
    have h := Finset.card_le_card
      (Finset.sdiff_subset : (CircularOrientationEntropy.circular n r (startIndex hr j))
        \ revealedImage hr o.val ⊆ _)
    simpa only [circular_card hn] using h
  have hp1 : p ≤ 1 := (div_le_one (by exact_mod_cast hr : (0 : ℝ) < r)).2 (by exact_mod_cast hk)
  have hb := bernoulli_norm_bound p t
  have hcast : (p : ℂ) = (k : ℂ) / r := by dsimp [p]; push_cast; rfl
  rw [hcast] at hb
  change ‖1 - (k : ℂ) / r + (k : ℂ) / r * Complex.exp ((t : ℂ) * Complex.I)‖ ≤ _
  by_cases hg : goodEndpoint hr j o.val
  · rw [ite_eq_left hg]
    have hv : b r ≤ p * (1 - p) := goodEndpoint_variance hr hn j o hg
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hv (sq_nonneg (Real.sin (t / 2)))
    nlinarith
  · rw [ite_eq_right hg]
    apply hb.trans
    apply (Real.exp_le_one_iff).2
    have h := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1))
      (sq_nonneg (Real.sin (t / 2)))
    nlinarith

open scoped Classical in
private theorem conditional_norm_bound {n r : ℕ} (hr : 0 < r) (hn : r < n)
    (a : ∀ i : {i : Fin n // i ∉ selectedSet hr}, Choice n r i.val)
    (b : ∀ i : selectedSet hr, Choice n r i.val) (t : ℝ) :
    ‖(∑ b' : ∀ i : selectedSet hr, Choice n r i.val,
      Complex.exp (((t : ℂ) * Complex.I) * (Finset.univ.image
        (fun i => (splitCompletion (CircularOrientationEntropy.circular n r)
          (selectedSet hr) a b' i).val)).card)) /
        (Fintype.card (∀ i : selectedSet hr, Choice n r i.val) : ℂ)‖ ≤
    ∏ j : Fin (n / (2 * r)),
      if goodEndpoint hr j (fun i => (splitCompletion (CircularOrientationEntropy.circular n r)
          (selectedSet hr) a b i).val)
      then Real.exp (-2 * CircularOrientationEntropyLowerBound.b r * Real.sin (t / 2) ^ 2)
      else 1 := by
  classical
  let E := CircularOrientationEntropy.circular n r
  let O := splitRevealedImage E (selectedSet hr) a
  let o : Orientation E := selectedChoiceEquiv E (splitCompletion E (selectedSet hr) a b)
  rw [split_fiber_average E (selectedSet hr) (selected_set_edges_disjoint hr hn) r hr
    (circular_card hn) a ((t : ℂ) * Complex.I), norm_mul]
  have hphase : ‖Complex.exp (((t : ℂ) * Complex.I) * (O.card : ℂ))‖ = 1 := by
    have he : ((t : ℂ) * Complex.I) * (O.card : ℂ) = ((t * (O.card : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  change ‖Complex.exp (((t : ℂ) * Complex.I) * (O.card : ℂ))‖ * _ ≤ _
  rw [hphase, one_mul, norm_prod]
  rw [selected_product hr (fun i => ‖1 - ((E i \ O).card : ℂ) / r +
    ((E i \ O).card : ℂ) / r * Complex.exp ((t : ℂ) * Complex.I)‖)]
  apply Finset.prod_le_prod₀
  · intro j hj; exact norm_nonneg _
  · intro j hj
    have h := actual_factor_bound hr hn j o t
    change ‖1 - (((E (startIndex hr j)) \ revealedImage hr
      (fun i => (splitCompletion E (selectedSet hr) a b i).val)).card : ℂ) / r +
      (((E (startIndex hr j)) \ revealedImage hr
      (fun i => (splitCompletion E (selectedSet hr) a b i).val)).card : ℂ) / r *
      Complex.exp ((t : ℂ) * Complex.I)‖ ≤ _ at h
    rw [actual_revealed_split hr a b] at h
    exact h

open scoped Classical in
private theorem actual_characteristic_bound {n r : ℕ} (hr : 3 ≤ r) (hn2 : 2 * r ≤ n)
    (t : ℝ) :
    ‖(∑ o : ∀ i, Choice n r i,
      Complex.exp (((Finset.univ.image (fun i => (o i).val)).card : ℂ) * Complex.I * (t : ℂ))) /
        (Fintype.card (∀ i, Choice n r i) : ℂ)‖ ≤
      Real.exp (-(n / (2 * r) : ℕ) * c r * Real.sin (t / 2) ^ 2) := by
  classical
  have hr0 : 0 < r := by omega
  have hn : r < n := by omega
  let : ∀ i : Fin n, Nonempty (Choice n r i) := fun i => ⟨⟨i, by
    rw [circular_mem hn]; left; omega⟩⟩
  let E := CircularOrientationEntropy.circular n r
  let S := selectedSet (n := n) hr0
  let A := ∀ i : {i : Fin n // i ∉ S}, Choice n r i.val
  let B := ∀ i : S, Choice n r i.val
  let e : (∀ i, Choice n r i) ≃ A × B := splitChoiceEquiv E S
  let f : A → B → ℂ := fun a b => Complex.exp (((t : ℂ) * Complex.I) *
    (Finset.univ.image (fun i => (splitCompletion E S a b i).val)).card)
  let W : A → B → ℝ := fun a b => ∏ j : Fin (n / (2 * r)),
    if goodEndpoint hr0 j (fun i => (splitCompletion E S a b i).val)
    then Real.exp (-2 * CircularOrientationEntropyLowerBound.b r * Real.sin (t / 2) ^ 2) else 1
  have hm := double_uniform_mean_norm_le f W (fun a b => conditional_norm_bound hr0 hn a b t)
  have hs : (∑ x : A × B, f x.1 x.2) =
      ∑ o : ∀ i, Choice n r i,
        Complex.exp (((Finset.univ.image (fun i => (o i).val)).card : ℂ)
          * Complex.I * (t : ℂ)) := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro o ho
    have he : splitCompletion E S (e o).1 (e o).2 = o := e.symm_apply_apply o
    dsimp only [f]
    rw [he]
    congr 1
    ring
  have hw : (∑ x : A × B, W x.1 x.2) =
      ∑ o : ∀ i, Choice n r i, ∏ j : Fin (n / (2 * r)),
        if goodEndpoint hr0 j (fun i => (o i).val)
        then Real.exp (-2 * CircularOrientationEntropyLowerBound.b r * Real.sin (t / 2) ^ 2)
        else 1 := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro o ho
    have he : splitCompletion E S (e o).1 (e o).2 = o := e.symm_apply_apply o
    dsimp only [W]
    rw [he]
  rw [hs, hw, ← Fintype.card_congr e,
    endpoint_joint_average hr0 hn hn2] at hm
  exact hm.trans (endpoint_generating_bound hr (n / (2 * r)) _
    (sq_nonneg _) (Real.sin_sq_le_one _))

/-- The entropy lower bound for the actual circular orientation model, with the
explicit constant `K`; this includes the small-size regime `r < n < 2 * r`. -/
theorem whole_theorem_one_two (r n : ℕ) (hr : 3 ≤ r) (hn : r < n) :
    (1 / 2 : ℝ) * Real.logb 2 ((n : ℝ) / r) - K r ≤
      OrientationEntropyBalance.entropyX r (CircularOrientationEntropy.circular n r) := by
  classical
  by_cases hn2 : 2 * r ≤ n
  · have hr0 : 0 < r := by omega
    let E := CircularOrientationEntropy.circular n r
    let : ∀ i : Fin n, Nonempty (Choice n r i) := fun i => ⟨⟨i, by
      rw [circular_mem hn]; left; omega⟩⟩
    let e : (∀ i, Choice n r i) ≃ Orientation E := selectedChoiceEquiv E
    let : Nonempty (Orientation E) := ⟨e (fun i => Classical.choice inferInstance)⟩
    let X : Orientation E → ℕ := fun o => OrientationEntropyBalance.X E o.val
    have hc : 0 < c r := (constants_pos hr).2.2.2.2
    have hm : 0 < n / (2 * r) := Nat.div_pos hn2 (by omega)
    have hA : 0 < ((n / (2 * r) : ℕ) : ℝ) * c r := by
      have hm' : (0 : ℝ) < (n / (2 * r) : ℕ) := by exact_mod_cast hm
      exact mul_pos hm' hc
    have hφ (t : ℝ) :
        ‖(∑ o : Orientation E, Complex.exp (((X o : ℤ) : ℂ) * Complex.I * (t : ℂ))) /
          (Fintype.card (Orientation E) : ℂ)‖ ≤
          Real.exp (-((n / (2 * r) : ℕ) : ℝ) * c r * Real.sin (t / 2) ^ 2) := by
      rw [← e.sum_comp, ← Fintype.card_congr e]
      simpa only [e, selectedChoiceEquiv, Equiv.coe_fn_mk, X, OrientationEntropyBalance.X,
        Int.cast_natCast] using actual_characteristic_bound hr hn2 t
    have hmass (k : ℕ) :
        ((Finset.univ.filter (fun o : Orientation E => X o = k)).card : ℝ) /
          Fintype.card (Orientation E) ≤ Real.sqrt (Real.pi * (r : ℝ) / (c r * n)) := by
      have h := finite_uniform_mass_bound (fun o : Orientation E => (X o : ℤ)) (k : ℤ) hA
        (fun t => by simpa only [neg_mul] using hφ t)
      simp only [Int.ofNat_inj] at h
      exact h.trans (circular_point_constant_bound r n hr hn2 hc)
    have hC : 0 < Real.sqrt (Real.pi * (r : ℝ) / (c r * n)) := by
      apply Real.sqrt_pos.mpr
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity
    have he := finite_entropy_lower X n (fun o => orientation_count_bound E o) _ hC hmass
    rw [← orientation_entropy_eq E (circular_card hn)] at he
    rw [circular_point_log_identity r n hr hn2 hc] at he
    have hK : (1 / 2 : ℝ) * Real.logb 2 (Real.pi / c r) ≤ K r := le_max_right _ _
    exact le_trans (sub_le_sub_left hK _) he
  · exact small_n_entropy_bound hr hn (by omega)

end D5.S3.Entropy.Hypergraphs.CircularOrientationEntropyLowerBound
