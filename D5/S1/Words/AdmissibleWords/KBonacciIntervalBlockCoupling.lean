/- GID: D5/S1/Words/AdmissibleWords/KBonacciIntervalBlockCoupling
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciIntervalBlockCoupling
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Reflection of exact conditional fibers and two-sided interval block couplings. -/

import D5.S1.Words.AdmissibleWords.KBonacciRightScanHamming
import D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval

/-! Actual conditional laws are transported by reversal before block restriction. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciIntervalBlockCoupling

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.TerminalSampling
open D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
open D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
open scoped BigOperators ENNReal NNReal Classical

private def reverseWord {n : ℕ} (w : Fin n → Bool) : Fin n → Bool := fun i => w i.rev

private theorem reverse_reverse {n : ℕ} (w : Fin n → Bool) :
    reverseWord (reverseWord w) = w := by
  funext i
  exact congrArg w (Fin.rev_rev i)

private def reverseSet {n : ℕ} (F : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.rev ∈ F

private theorem reverse_legal {k n : ℕ} (hk : 0 < k) (w : Fin n → Bool)
    (hw : DBonacciAdmissible k n w) : DBonacciAdmissible k n (reverseWord w) :=
  (scanner_iff_literal k n hk _).mpr
    (avoid_reverse w ((scanner_iff_literal k n hk w).mp hw))

private theorem reverse_mem {k n : ℕ} (hk : 0 < k) (F : Finset (Fin n))
    (x w : Fin n → Bool) :
    reverseWord w ∈ completions k n (reverseSet F) (reverseWord x) ↔
      w ∈ completions k n F x := by
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hl, hf⟩
    refine ⟨?_, ?_⟩
    · simpa only [reverse_reverse] using reverse_legal hk (reverseWord w) hl
    · intro i hi
      simpa [reverseWord] using hf i.rev (by simpa [reverseSet] using hi)
  · rintro ⟨hl, hf⟩
    refine ⟨reverse_legal hk w hl, ?_⟩
    intro i hi
    exact hf i.rev (by simpa [reverseSet] using hi)

private def reverseFiberEquiv {k n : ℕ} (hk : 0 < k) (F : Finset (Fin n))
    (x : Fin n → Bool) :
    {w // w ∈ completions k n F x} ≃
      {w // w ∈ completions k n (reverseSet F) (reverseWord x)} where
  toFun w := ⟨reverseWord w.val, (reverse_mem hk F x w.val).mpr w.property⟩
  invFun w := ⟨reverseWord w.val, (reverse_mem hk F x (reverseWord w.val)).mp
    (by simpa only [reverse_reverse] using w.property)⟩
  left_inv w := by apply Subtype.ext; funext i; simp [reverseWord]
  right_inv w := by apply Subtype.ext; funext i; simp [reverseWord]

private theorem reflection_law {k n : ℕ} (hk : 0 < k) (F : Finset (Fin n))
    (x : Fin n → Bool) (h : (completions k n F x).Nonempty)
    (hr : (completions k n (reverseSet F) (reverseWord x)).Nonempty) :
    (completionLaw F x h).map reverseWord =
      completionLaw (reverseSet F) (reverseWord x) hr := by
  let e := reverseFiberEquiv hk F x
  letI : Nonempty {w // w ∈ completions k n F x} := ⟨⟨h.choose, h.choose_spec⟩⟩
  letI : Nonempty {w // w ∈ completions k n (reverseSet F) (reverseWord x)} :=
    ⟨⟨hr.choose, hr.choose_spec⟩⟩
  have hu : (uniformPmf {w // w ∈ completions k n F x}).map e =
      uniformPmf {w // w ∈ completions k n (reverseSet F) (reverseWord x)} := by
    apply PMF.ext
    intro w
    simp only [PMF.map_apply, uniformPmf, PMF.ofFintype_apply, ← e.symm_apply_eq]
    simp [Fintype.card_congr e]
  change ((uniformPmf {w // w ∈ completions k n F x}).map Subtype.val).map
    reverseWord = (uniformPmf {w // w ∈ completions k n (reverseSet F)
      (reverseWord x)}).map Subtype.val
  rw [← hu, PMF.map_comp, PMF.map_comp]
  rfl

private theorem scan_sum {n : ℕ} (s : List (Fin n)) (hs : s.Nodup)
    (w : (Fin n → Bool) × (Fin n → Bool)) :
    scanHamming s w = ∑ i ∈ s.toFinset, if w.1 i = w.2 i then 0 else (1 : ℝ≥0∞) := by
  induction s with
  | nil => simp [scanHamming]
  | cons i s ih =>
    rw [scanHamming, ih (List.nodup_cons.mp hs).2]
    simp only [List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using (List.nodup_cons.mp hs).1)]

private def setHamming {n : ℕ} (B : Finset (Fin n))
    (w : (Fin n → Bool) × (Fin n → Bool)) : ℝ≥0∞ :=
  ∑ i ∈ B, if w.1 i = w.2 i then 0 else 1

private theorem increasing_coupling {k n : ℕ} (hk : 0 < k)
    (B : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) (hy : DBonacciAdmissible k n y)
    (hfar : ∀ i ∈ B, ∀ j ∈ Bᶜ, i < j → x j = y j) :
    ∃ J : PMF ((Fin n → Bool) × (Fin n → Bool)),
      J.map Prod.fst = completionLaw Bᶜ x (completion_nonempty Bᶜ x hx) ∧
      J.map Prod.snd = completionLaw Bᶜ y (completion_nonempty Bᶜ y hy) ∧
      mean J (setHamming B) ≤ 1 := by
  let s := B.sort (· ≤ ·)
  have hn : s.Nodup := B.sort_nodup _
  have ho : s.Pairwise (fun i j => i.val < j.val) := (B.sortedLT_sort).pairwise
  have hf : ∀ i ∈ s, i ∉ Bᶜ := by simp [s]
  have hc : ∀ i : Fin n, i ∉ Bᶜ → i ∈ s := by simp [s]
  let J := prefixCoupling s Bᶜ x y (completion_nonempty Bᶜ x hx)
    (completion_nonempty Bᶜ y hy)
  have hm := prefix_coupling_marginals hk s hn Bᶜ hf x y
    (completion_nonempty Bᶜ x hx) (completion_nonempty Bᶜ y hy)
  refine ⟨J, hm.1, hm.2, ?_⟩
  have he : scanHamming s = setHamming B := by
    funext w
    rw [scan_sum s hn]
    simp [s, setHamming]
  have hcost := right_scan_hamming hk s hn ho Bᶜ hf hc x y
    (completion_nonempty Bᶜ x hx) (completion_nonempty Bᶜ y hy)
    (by intro i hi j hj hij; exact hfar i (by simpa [s] using hi) j hj hij)
  simpa only [he, mean, J] using hcost

private theorem reflection_hamming {n : ℕ} (B : Finset (Fin n))
    (w : (Fin n → Bool) × (Fin n → Bool)) :
    setHamming B (reverseWord w.1, reverseWord w.2) = setHamming (reverseSet B) w := by
  unfold setHamming
  apply Finset.sum_bij (fun i _ => i.rev)
  · intro i hi
    simpa [reverseSet] using hi
  · intro i _ j _ he
    exact Fin.rev_injective he
  · intro j hj
    exact ⟨j.rev, by simpa [reverseSet] using hj, by simp⟩
  · intro i _
    rfl

private theorem sided_coupling {k n : ℕ} (hk : 0 < k)
    (B : Finset (Fin n)) (x y : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) (hy : DBonacciAdmissible k n y)
    (u : Fin n) (hsame : ∀ i, i ≠ u → x i = y i)
    (hside : (∀ i ∈ B, u < i) ∨ (∀ i ∈ B, i < u)) :
    ∃ J : PMF ((Fin n → Bool) × (Fin n → Bool)),
      J.map Prod.fst = completionLaw Bᶜ x (completion_nonempty Bᶜ x hx) ∧
      J.map Prod.snd = completionLaw Bᶜ y (completion_nonempty Bᶜ y hy) ∧
      mean J (setHamming B) ≤ 1 := by
  rcases hside with hright | hleft
  · apply increasing_coupling hk B x y hx hy
    intro i hi j _ hij
    exact hsame j (by have := hright i hi; intro he; subst j; exact (lt_asymm this hij))
  · have hxr := reverse_legal hk x hx
    have hyr := reverse_legal hk y hy
    obtain ⟨J, hm, hn, hc⟩ := increasing_coupling hk (reverseSet B)
      (reverseWord x) (reverseWord y) hxr hyr (by
        intro i hi j _ hij
        have hiB : i.rev ∈ B := by simpa [reverseSet] using hi
        have hji : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
        exact hsame j.rev (by have := hleft i.rev hiB; intro he; rw [he] at hji; exact lt_asymm this hji))
    have hF : reverseSet Bᶜ = (reverseSet B)ᶜ := by
      ext i
      simp [reverseSet]
    have hxlaw : (completionLaw Bᶜ x (completion_nonempty Bᶜ x hx)).map reverseWord =
        completionLaw (reverseSet B)ᶜ (reverseWord x)
          (completion_nonempty (reverseSet B)ᶜ (reverseWord x) hxr) := by
      simpa only [hF] using reflection_law hk Bᶜ x (completion_nonempty Bᶜ x hx)
        (completion_nonempty (reverseSet Bᶜ) (reverseWord x) hxr)
    have hylaw : (completionLaw Bᶜ y (completion_nonempty Bᶜ y hy)).map reverseWord =
        completionLaw (reverseSet B)ᶜ (reverseWord y)
          (completion_nonempty (reverseSet B)ᶜ (reverseWord y) hyr) := by
      simpa only [hF] using reflection_law hk Bᶜ y (completion_nonempty Bᶜ y hy)
        (completion_nonempty (reverseSet Bᶜ) (reverseWord y) hyr)
    let R := fun w : (Fin n → Bool) × (Fin n → Bool) =>
      (reverseWord w.1, reverseWord w.2)
    have hrid : reverseWord ∘ reverseWord = (id : (Fin n → Bool) → _) :=
      funext reverse_reverse
    refine ⟨J.map R, ?_, ?_, ?_⟩
    · calc
        (J.map R).map Prod.fst = (J.map Prod.fst).map reverseWord := by
          simp only [PMF.map_comp]; rfl
        _ = _ := by rw [hm, ← hxlaw, PMF.map_comp, hrid]; exact PMF.map_id _
    · calc
        (J.map R).map Prod.snd = (J.map Prod.snd).map reverseWord := by
          simp only [PMF.map_comp]; rfl
        _ = _ := by rw [hn, ← hylaw, PMF.map_comp, hrid]; exact PMF.map_id _
    · rw [mean_map]
      simpa only [R, reflection_hamming] using hc

/-- Boolean assignments on the actual sites of a block. -/
def BlockAssignment {n : ℕ} (B : Finset (Fin n)) := {i // i ∈ B} → Bool

/-- Restrict a full word to the block, retaining its original coordinate labels. -/
def restrictBlock {n : ℕ} (B : Finset (Fin n)) (w : Fin n → Bool) :
    BlockAssignment B := fun i => w i.val

/-- Uniform legal block assignments conditioned on every exterior coordinate. -/
def conditionalBlockLaw {k n : ℕ} (B : Finset (Fin n)) (x : Fin n → Bool)
    (hx : DBonacciAdmissible k n x) : PMF (BlockAssignment B) :=
  (completionLaw Bᶜ x (completion_nonempty Bᶜ x hx)).map (restrictBlock B)

/-- Internal Hamming distance between two actual block assignments. -/
def blockHamming {n : ℕ} (B : Finset (Fin n))
    (w : BlockAssignment B × BlockAssignment B) : ℝ≥0∞ :=
  ∑ i : {i // i ∈ B}, if w.1 i = w.2 i then 0 else 1

private theorem restriction_hamming {n : ℕ} (B : Finset (Fin n))
    (w : (Fin n → Bool) × (Fin n → Bool)) :
    blockHamming B (restrictBlock B w.1, restrictBlock B w.2) = setHamming B w := by
  simp only [blockHamming, restrictBlock, setHamming]
  exact Finset.sum_coe_sort B (fun i => if w.1 i = w.2 i then (0 : ℝ≥0∞) else 1)

/-- Every nonempty interval excluding the sole possible exterior disagreement
has an actual coupling of its full-exterior conditional block laws with expected
internal Hamming distance at most one, for either orientation and all lengths. -/
theorem conditional_interval_block_coupling {k n : ℕ} (hk : 2 ≤ k)
    (x y : Fin n → Bool) (hx : DBonacciAdmissible k n x)
    (hy : DBonacciAdmissible k n y) (a b u : Fin n) (hab : a ≤ b)
    (hu : u ∉ Finset.Icc a b) (hsame : ∀ i, i ≠ u → x i = y i) :
    ∃ J : PMF (BlockAssignment (Finset.Icc a b) × BlockAssignment (Finset.Icc a b)),
      J.map Prod.fst = conditionalBlockLaw (Finset.Icc a b) x hx ∧
      J.map Prod.snd = conditionalBlockLaw (Finset.Icc a b) y hy ∧
      (∑' w, J w * blockHamming (Finset.Icc a b) w) ≤ 1 := by
  have hside : (∀ i ∈ Finset.Icc a b, u < i) ∨
      (∀ i ∈ Finset.Icc a b, i < u) := by
    have hout : u < a ∨ b < u := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hu
    rcases hout with h | h
    · exact Or.inl (fun i hi => lt_of_lt_of_le h (Finset.mem_Icc.mp hi).1)
    · exact Or.inr (fun i hi => lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 h)
  obtain ⟨J, hm, hn, hc⟩ := sided_coupling (by omega : 0 < k)
    (Finset.Icc a b) x y hx hy u hsame hside
  let r := restrictBlock (Finset.Icc a b)
  let R := fun w : (Fin n → Bool) × (Fin n → Bool) => (r w.1, r w.2)
  refine ⟨J.map R, ?_, ?_, ?_⟩
  · change (J.map R).map Prod.fst =
      (completionLaw (Finset.Icc a b)ᶜ x (completion_nonempty _ x hx)).map r
    rw [← hm, PMF.map_comp, PMF.map_comp]
    rfl
  · change (J.map R).map Prod.snd =
      (completionLaw (Finset.Icc a b)ᶜ y (completion_nonempty _ y hy)).map r
    rw [← hn, PMF.map_comp, PMF.map_comp]
    rfl
  · change mean (J.map R) (blockHamming (Finset.Icc a b)) ≤ 1
    rw [mean_map]
    simpa only [R, r, restriction_hamming] using hc

end D5.S1.Words.AdmissibleWords.KBonacciIntervalBlockCoupling
