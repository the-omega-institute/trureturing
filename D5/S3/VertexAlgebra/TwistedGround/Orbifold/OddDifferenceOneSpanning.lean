/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOneSpanning
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOneSpanning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded square-sum descent for difference-one words in the actual odd sector. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddModeStraightening
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-! The word straightening in Miyamoto's Lemma 2.4 (arXiv:math/0209101). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped VertexOperator BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (FixedCarrier fixedMode)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open LatticePositiveEnergy (grade positive_actual_mode_grade)
open OddModeStraightening (swap_mem_iff duplicate_mem_of_shorter_and_larger minusTwo_mem_of_pairs)

variable {D : LatticeData} {hu : IsUnit D.G.det}

structure Homogeneous (D : LatticeData) where
  state : FixedCarrier D
  weight : ℕ
  graded : state.val ∈ grade D (weight : ℤ)

abbrev Word (D : LatticeData) := List (Homogeneous D × ℤ)

private abbrev act (a : FixedCarrier D) (n : ℤ) :=
  (fixedParitySlice D hu (-1) a)[[n]]

private def fixedActionOn (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : ℤ) (u : paritySpace D hu (-1)) :
    FixedCarrier D →ₗ[ℂ] paritySpace D hu (-1) :=
  (LinearMap.snd ℂ (FixedCarrier D) (paritySpace D hu (-1))).comp
    ((LinearMap.applyₗ (R := ℂ) ((0, u) : OriginalOrbifoldField.Carrier D hu)).comp
      ((OriginalOrbifoldField.mode D hu hD n).comp
        (LinearMap.inl ℂ (FixedCarrier D) (paritySpace D hu (-1)))))

private theorem fixedActionOn_apply (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (n : ℤ) (u : paritySpace D hu (-1)) (a : FixedCarrier D) :
    fixedActionOn hD n u a = act a n u := by
  change (OriginalOrbifoldField.mode D hu hD n (a, 0) (0, u)).2 = _
  rw [← OriginalOrbifoldField.Y_ncoeff, OriginalOrbifoldField.Y_fixed_ncoeff_apply]

/-- Apply a word from right to left. -/
def wordMap : Word D → Module.End ℂ (paritySpace D hu (-1))
  | [] => LinearMap.id
  | (a, n) :: t => (act a.state n).comp (wordMap t)

@[simp] private theorem wordMap_nil (u : paritySpace D hu (-1)) :
    wordMap [] u = u := rfl

@[simp] private theorem wordMap_cons (a : Homogeneous D × ℤ) (t : Word D)
    (u : paritySpace D hu (-1)) :
    wordMap (a :: t) u = act a.1.state a.2 (wordMap t u) := rfl

@[simp] private theorem wordMap_append (s t : Word D) (u : paritySpace D hu (-1)) :
    wordMap (s ++ t) u = wordMap s (wordMap t u) := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [List.cons_append, wordMap_cons, ih]

private def weight (t : Word D) : ℕ := (t.map fun a => a.1.weight).sum

private def indexSum (t : Word D) : ℤ := (t.map Prod.snd).sum

private def squareSum (t : Word D) : ℤ := (t.map fun a => a.2 ^ 2).sum

private def lettersIn (X : Finset (Homogeneous D)) (t : Word D) : Prop :=
  ∀ a ∈ t, a.1 ∈ X

private def increasing (t : Word D) : Prop := t.Pairwise fun a b => a.2 < b.2

private def nondecreasing (t : Word D) : Prop := t.Pairwise fun a b => a.2 ≤ b.2

/-- Words in the representatives with strictly increasing integer indices. -/
def strictSpan (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1)) :
    Submodule ℂ (paritySpace D hu (-1)) :=
  Submodule.span ℂ {v | ∃ t : Word D, lettersIn X t ∧ increasing t ∧ v = wordMap t u}

private theorem grade_zero_of_negative
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {e : ℤ} (he : e < 0) {v : LatticeGeneratingFieldLocality.Carrier D}
    (hv : v ∈ grade D e) : v = 0 := by
  rw [← LatticePositiveEnergy.sum_gradeProjections D v]
  apply Finset.sum_eq_zero
  intro n hn
  exact LatticePositiveEnergy.gradeProjection_zero_of_mem_grade_ne D n e
    (by have := LatticePositiveEnergy.stateEnergies_nonneg hD v n hn; omega) v hv

private theorem mode_grade
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a b : Homogeneous D) (n : ℤ) :
    (fixedMode D a.state n b.state).val ∈ grade D (a.weight + b.weight - n - 1) :=
  positive_actual_mode_grade D hD a.weight b.weight n a.state.val b.state.val a.graded b.graded

private theorem correction_mem
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (S : Submodule ℂ (paritySpace D hu (-1))) (u : paritySpace D hu (-1))
    (N : ℕ) (lower : ∀ t : Word D, weight t < N → wordMap t u ∈ S)
    (s t : Word D) (a b : Homogeneous D) (p q : ℤ)
    (hweight : weight (s ++ (a, p) :: (b, q) :: t) ≤ N) (i : ℕ) :
    act (fixedMode D a.state i b.state) (p + q - i) (wordMap t u) ∈
      S.comap (wordMap s) := by
  let e : ℤ := a.weight + b.weight - (i : ℤ) - 1
  by_cases he : 0 ≤ e
  · have he' : (e.toNat : ℤ) = e := Int.toNat_of_nonneg he
    let c : Homogeneous D := ⟨fixedMode D a.state i b.state, e.toNat, by
      rw [he']
      exact mode_grade hD a b i⟩
    have hc : c.weight < a.weight + b.weight := by
      change e.toNat < a.weight + b.weight
      dsimp [e] at he'
      omega
    have ht : weight (s ++ (c, p + q - i) :: t) < N := by
      simp only [weight, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at *
      omega
    simpa only [wordMap_append, wordMap_cons, Submodule.mem_comap] using
      lower (s ++ (c, p + q - i) :: t) ht
  · have hz : fixedMode D a.state i b.state = 0 := Subtype.ext
      (grade_zero_of_negative hD (lt_of_not_ge he) (mode_grade hD a b i))
    rw [← fixedActionOn_apply hD, hz, map_zero]
    exact (S.comap (wordMap s)).zero_mem

private theorem perm_mem_iff
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (S : Submodule ℂ (paritySpace D hu (-1))) (u : paritySpace D hu (-1))
    (N : ℕ) (lower : ∀ t : Word D, weight t < N → wordMap t u ∈ S)
    {t v : Word D} (hperm : t.Perm v) (s : Word D)
    (hweight : weight (s ++ t) ≤ N) :
    wordMap (s ++ t) u ∈ S ↔ wordMap (s ++ v) u ∈ S := by
  induction hperm generalizing s with
  | nil => rfl
  | cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (s ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hweight)
  | swap a b t =>
    simpa only [wordMap_append, wordMap_cons, Submodule.mem_comap] using
      swap_mem_iff (S.comap (wordMap s)) b.1.state a.1.state b.2 a.2 (wordMap t u)
        (correction_mem hD S u N lower s t b.1 a.1 b.2 a.2 hweight)
  | @trans t v w h₁ h₂ ih₁ ih₂ =>
    have hw : weight (s ++ t) = weight (s ++ v) :=
      ((h₁.append_left s).map fun (a : Homogeneous D × ℤ) => a.1.weight).sum_eq
    exact (ih₁ s hweight).trans (ih₂ s (hw ▸ hweight))

private theorem list_sum_le {α : Type*} (f : α → ℤ) (t : List α) (M : ℤ)
    (h : ∀ a ∈ t, f a ≤ M) : (t.map f).sum ≤ (t.length : ℤ) * M := by
  induction t with
  | nil => simp
  | cons a t ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    omega

private theorem square_bound (t : Word D) (L : ℤ) (h : ∀ a ∈ t, a.2 < L) :
    squareSum t ≤ (t.length : ℤ) * (|indexSum t| + (t.length : ℤ) * |L|)^2 := by
  apply list_sum_le
  intro a ha
  obtain ⟨s, v, rfl⟩ := List.append_of_mem ha
  have hs := list_sum_le Prod.snd s |L| fun b hb =>
    (le_of_lt (h b (List.mem_append_left _ hb))).trans (le_abs_self L)
  have hv := list_sum_le Prod.snd v |L| fun b hb =>
    (le_of_lt (h b (List.mem_append_right _ (List.mem_cons_of_mem _ hb)))).trans (le_abs_self L)
  have ha' := (le_of_lt (h a (List.mem_append_right _ (List.mem_cons_self ..)))).trans
    (le_abs_self L)
  let m : ℤ := |indexSum (s ++ a :: v)| + ((s ++ a :: v).length : ℤ) * |L|
  have hm₁ := le_abs_self (indexSum (s ++ a :: v))
  have hm₂ := neg_abs_le (indexSum (s ++ a :: v))
  have hl : 0 ≤ |L| := abs_nonneg L
  have hlen : (1 : ℤ) ≤ (s.length : ℤ) + ((v.length : ℤ) + 1) := by omega
  have hLl := mul_le_mul_of_nonneg_right hlen hl
  have hm₃ : 0 ≤ |(s.map Prod.snd).sum + (a.2 + (v.map Prod.snd).sum)| := abs_nonneg _
  change a.2 ^ 2 ≤ m ^ 2
  apply sq_le_sq' <;>
    simp only [m, indexSum, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one] at hm₁ hm₂ ⊢
  · linarith only [hs, hv, hm₂, hl]
  · linarith only [ha', hLl, hm₃]

private theorem tail_cutoff (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1)) :
    ∃ L : ℤ, ∀ a ∈ X, ∀ k ≥ L, act a.state k u = 0 := by
  classical
  have single (a : Homogeneous D) : ∃ N : ℤ, ∀ k ≥ N, act a.state k u = 0 := by
    let v := fixedParitySlice D hu (-1) a.state
    let e := ((HahnModule.of ℂ).symm (v u)).order
    refine ⟨-e, fun k hk => VertexOperator.ncoeff_eq_zero_of_lt_order v k u ?_⟩
    change -k - 1 < e
    omega
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a X _ ih =>
    obtain ⟨A, hA⟩ := single a
    obtain ⟨B, hB⟩ := ih
    refine ⟨max A B, fun b hb k hk => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hA k ((le_max_left _ _).trans hk)
    · exact hB b hb k ((le_max_right _ _).trans hk)

private theorem sorted_truncate (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1))
    (L : ℤ) (hL : ∀ a ∈ X, ∀ k ≥ L, act a.state k u = 0)
    (t : Word D) (ht : nondecreasing t) (hx : lettersIn X t)
    (ha : ∃ a ∈ t, L ≤ a.2) : wordMap t u = 0 := by
  obtain h | ⟨s, b, rfl⟩ := List.eq_nil_or_concat' t
  · simp [h] at ha
  obtain ⟨a, ha, haL⟩ := ha
  have hb : L ≤ b.2 := by
    rcases List.mem_append.mp ha with hs | hs
    · exact haL.trans ((List.pairwise_append.mp ht).2.2 a hs b (by simp))
    · exact (List.mem_singleton.mp hs) ▸ haL
  have bx : b.1 ∈ X := hx b (List.mem_append_right _ (by simp))
  simp only [wordMap_append, wordMap_cons, wordMap_nil, hL b.1 bx b.2 hb, map_zero]

private theorem duplicate_adjacent (t : Word D) (ht : nondecreasing t) (hs : ¬ increasing t) :
    ∃ (s v : Word D) (a b : Homogeneous D) (j : ℤ), t = s ++ (a, j) :: (b, j) :: v := by
  induction t with
  | nil => exact (hs List.Pairwise.nil).elim
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp ht
    by_cases hi : increasing t
    · cases t with
      | nil => exact (hs (by simp [increasing])).elim
      | cons b v =>
        have hab := ha b (List.mem_cons_self ..)
        have he : a.2 = b.2 := by
          by_contra hne
          have hlt := lt_of_le_of_ne hab hne
          apply hs
          refine List.pairwise_cons.mpr ⟨fun x hx => ?_, hi⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlt
          · exact hlt.trans_le ((List.pairwise_cons.mp ht).1 x hx)
        refine ⟨[], v, a.1, b.1, b.2, ?_⟩
        exact congrArg (fun x => x :: b :: v) (Prod.ext rfl he)
    · obtain ⟨s, v, b, c, j, rfl⟩ := ih ht hi
      exact ⟨a :: s, v, b, c, j, rfl⟩

private def sort (t : Word D) : Word D :=
  t.mergeSort fun a b => decide (a.2 ≤ b.2)

private theorem sort_perm (t : Word D) : (sort t).Perm t := List.mergeSort_perm _ _

private theorem sort_nondecreasing (t : Word D) : nondecreasing (sort t) := by
  have sorted := List.pairwise_mergeSort
    (le := fun (a b : Homogeneous D × ℤ) => decide (a.2 ≤ b.2))
    (fun a b c h₁ h₂ => decide_eq_true
      ((of_decide_eq_true h₁ : a.2 ≤ b.2).trans (of_decide_eq_true h₂ : b.2 ≤ c.2)))
    (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total a.2 b.2)
    t
  simpa only [decide_eq_true_eq, sort, nondecreasing] using sorted

private theorem normal_letter_mem
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (S : Submodule ℂ (paritySpace D hu (-1))) (u : paritySpace D hu (-1))
    (N k : ℕ) (shorter : ∀ t : Word D, weight t ≤ N → t.length < k → wordMap t u ∈ S)
    (s v : Word D) (a b : Homogeneous D) (j : ℤ)
    (hw : weight (s ++ (a, j) :: (b, j) :: v) ≤ N)
    (hl : (s ++ (a, j) :: (b, j) :: v).length = k) :
    act (fixedMode D (if j < 0 then a.state else b.state) (-1)
      (if j < 0 then b.state else a.state)) (2 * j + 1) (wordMap v u) ∈
      S.comap (wordMap s) := by
  by_cases hj : j < 0
  · simp only [ite_eq_left hj]
    let c : Homogeneous D := ⟨fixedMode D a.state (-1) b.state, a.weight + b.weight, by
      convert mode_grade hD a b (-1) using 2
      push_cast
      ring⟩
    change wordMap s (act c.state (2 * j + 1) (wordMap v u)) ∈ S
    rw [← wordMap_cons (c, 2 * j + 1), ← wordMap_append]
    apply shorter
    · simpa only [weight, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        c, add_assoc] using hw
    · simp only [List.length_append, List.length_cons] at hl ⊢
      omega
  · simp only [ite_eq_right hj]
    let c : Homogeneous D := ⟨fixedMode D b.state (-1) a.state, a.weight + b.weight, by
      convert mode_grade hD b a (-1) using 2
      push_cast
      ring⟩
    change wordMap s (act c.state (2 * j + 1) (wordMap v u)) ∈ S
    rw [← wordMap_cons (c, 2 * j + 1), ← wordMap_append]
    apply shorter
    · simpa only [weight, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        c, add_assoc] using hw
    · simp only [List.length_append, List.length_cons] at hl ⊢
      omega

private theorem representative_words_mem
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1))
    (N k : ℕ) (lower : ∀ t : Word D, weight t < N → wordMap t u ∈ strictSpan X u)
    (shorter : ∀ t : Word D, weight t ≤ N → t.length < k → wordMap t u ∈ strictSpan X u)
    (t : Word D) (hw : weight t ≤ N) (hl : t.length = k) (hx : lettersIn X t) :
    wordMap t u ∈ strictSpan X u := by
  obtain ⟨L, hL⟩ := tail_cutoff X u
  let S := strictSpan X u
  let σ := indexSum t
  let B : ℤ := (k : ℤ) * (|σ| + (k : ℤ) * |L|)^2
  let measure (v : Word D) := (B - squareSum v).toNat
  have permute {v w : Word D} (h : v.Perm w) (hv : weight v ≤ N) :
      wordMap v u ∈ S ↔ wordMap w u ∈ S := by
    simpa only [List.nil_append] using perm_mem_iff hD S u N lower h [] (by simpa using hv)
  have sort_letters {v : Word D} (hv : lettersIn X v) : lettersIn X (sort v) :=
    fun a ha => hv a ((sort_perm v).mem_iff.mp ha)
  have cut (v : Word D) (hv : weight v ≤ N) (hx : lettersIn X v)
      (hlarge : ∃ a ∈ v, L ≤ a.2) : wordMap v u ∈ S := by
    apply (permute (sort_perm v).symm hv).mpr
    have hz := sorted_truncate X u L hL (sort v) (sort_nondecreasing v) (sort_letters hx)
      (by obtain ⟨a, ha, hi⟩ := hlarge; exact ⟨a, (sort_perm v).mem_iff.mpr ha, hi⟩)
    rw [hz]
    exact S.zero_mem
  have step (m : ℕ) :
      ∀ v : Word D, measure v = m → weight v ≤ N → v.length = k →
        indexSum v = σ → lettersIn X v → wordMap v u ∈ S := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro v hmeasure hv hlen hsum hx
      by_cases hlarge : ∃ a ∈ v, L ≤ a.2
      · exact cut v hv hx hlarge
      apply (permute (sort_perm v).symm hv).mpr
      have hp := sort_perm v
      have hsorted := sort_nondecreasing v
      have hw' : weight (sort v) ≤ N := by
        unfold weight at hv ⊢
        rwa [(hp.map fun a => a.1.weight).sum_eq]
      have hl' : (sort v).length = k := hp.length_eq.trans hlen
      have hs' : indexSum (sort v) = σ := (hp.map Prod.snd).sum_eq.trans hsum
      have hm' : measure (sort v) = m := by
        dsimp only [measure, squareSum]
        rw [(hp.map fun a => a.2 ^ 2).sum_eq]
        exact hmeasure
      have hx' := sort_letters hx
      by_cases hstrict : increasing (sort v)
      · exact Submodule.subset_span ⟨sort v, hx', hstrict, rfl⟩
      obtain ⟨s, r, a, b, j, he⟩ := duplicate_adjacent (sort v) hsorted hstrict
      rw [he] at hw' hl' hs' hm' hx' ⊢
      simp only [wordMap_append, wordMap_cons]
      change act a.state j (act b.state j (wordMap r u)) ∈ S.comap (wordMap s)
      have hpair (c d : Homogeneous D) (hc : c ∈ X) (hd : d ∈ X)
          (heq : c.weight + d.weight = a.weight + b.weight)
          (p q : ℤ) (hpq : p + q = 2 * j) (hraise : 2 * j^2 < p^2 + q^2) :
          act c.state p (act d.state q (wordMap r u)) ∈ S.comap (wordMap s) := by
        let w := s ++ (c, p) :: (d, q) :: r
        have hw'' : weight w ≤ N := by
          simp only [w, weight, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons] at hw' ⊢
          omega
        have hx'' : lettersIn X w := by
          intro x hh
          rcases List.mem_append.mp hh with hpre | ht
          · exact hx' x (List.mem_append_left _ hpre)
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hc
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hd
          · exact hx' x (List.mem_append_right _ (by simp [ht]))
        have hl'' : w.length = k := by
          simpa only [w, List.length_append, List.length_cons] using hl'
        have hs'' : indexSum w = σ := by
          simp only [w, indexSum, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons] at hs' ⊢
          omega
        have hwMem : wordMap w u ∈ S := by
          by_cases hcut : ∃ e ∈ w, L ≤ e.2
          · exact cut w hw'' hx'' hcut
          have hb := square_bound w L (by push Not at hcut; exact hcut)
          rw [hl'', hs''] at hb
          have hrise : squareSum (s ++ (a, j) :: (b, j) :: r) < squareSum w := by
            simp only [w, squareSum, List.map_append, List.sum_append, List.map_cons,
              List.sum_cons]
            linarith
          have hdec : measure w < m := by
            rw [← hm']
            change (B - squareSum w).toNat <
              (B - squareSum (s ++ (a, j) :: (b, j) :: r)).toNat
            change squareSum w ≤ B at hb
            omega
          exact ih (measure w) hdec w rfl hw'' hl'' hs'' hx''
        simpa only [w, wordMap_append, wordMap_cons, Submodule.mem_comap] using hwMem
      have ha : a ∈ X := hx' (a, j) (by simp)
      have hb : b ∈ X := hx' (b, j) (by simp)
      exact duplicate_mem_of_shorter_and_larger (S.comap (wordMap s)) a.state b.state j
        (wordMap r u) (normal_letter_mem hD S u N k shorter s r a b j hw' hl')
        (hpair a b ha hb rfl) (hpair b a hb ha (Nat.add_comm _ _))
  exact step (measure t) t rfl hw hl rfl hx

/-- The source representatives and the homogeneous C₂ generators of a given weight. -/
def sourceGenerators (X : Finset (Homogeneous D)) (n : ℕ) : Set (FixedCarrier D) :=
  {a | (∃ b ∈ X, b.weight = n ∧ a = b.state) ∨
    ∃ b c : Homogeneous D, b.weight + c.weight + 1 = n ∧ a = fixedMode D b.state (-2) c.state}

private theorem replace_letters_mem
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1))
    (hX : ∀ a : Homogeneous D, a.state ∈ Submodule.span ℂ (sourceGenerators X a.weight))
    (N k : ℕ) (lower : ∀ t : Word D, weight t < N → wordMap t u ∈ strictSpan X u)
    (reps : ∀ t : Word D, weight t ≤ N → t.length = k → lettersIn X t →
      wordMap t u ∈ strictSpan X u)
    (t s : Word D) (hx : lettersIn X s) (hw : weight (s ++ t) ≤ N)
    (hl : (s ++ t).length = k) : wordMap (s ++ t) u ∈ strictSpan X u := by
  let S := strictSpan X u
  induction t generalizing s with
  | nil => exact reps _ hw hl (by simpa only [List.append_nil] using hx)
  | cons a t ih =>
    obtain ⟨a, p⟩ := a
    let T := S.comap (wordMap s)
    let f := fixedActionOn hD p (wordMap t u)
    rw [wordMap_append, wordMap_cons, ← fixedActionOn_apply hD]
    change f a.state ∈ T
    suffices h : Submodule.span ℂ (sourceGenerators X a.weight) ≤ T.comap f from
      h (hX a)
    apply Submodule.span_le.mpr
    intro z hz
    change f z ∈ T
    rcases hz with ⟨b, hbX, hb, rfl⟩ | ⟨b, c, hbc, rfl⟩
    · have hx' : lettersIn X (s ++ [(b, p)]) := by
        intro x hx'
        rcases List.mem_append.mp hx' with h | h
        · exact hx x h
        · obtain rfl := List.mem_singleton.mp h
          exact hbX
      have hw' : weight ((s ++ [(b, p)]) ++ t) ≤ N := by
        simpa [weight, List.append_assoc, List.sum_append, hb] using hw
      have hl' : ((s ++ [(b, p)]) ++ t).length = k := by
        simpa only [List.append_assoc, List.singleton_append, List.length_append,
          List.length_cons] using hl
      change wordMap s (fixedActionOn hD p (wordMap t u) b.state) ∈ S
      rw [fixedActionOn_apply]
      simpa only [List.append_assoc, List.singleton_append, wordMap_append, wordMap_cons]
        using ih (s ++ [(b, p)]) hx' hw' hl'
    · change fixedActionOn hD p (wordMap t u) (fixedMode D b.state (-2) c.state) ∈ T
      rw [fixedActionOn_apply]
      apply minusTwo_mem_of_pairs T b.state c.state p (wordMap t u)
      · intro i j _
        change wordMap s (act b.state i (act c.state j (wordMap t u))) ∈ S
        have hw' : weight (s ++ (b, i) :: (c, j) :: t) < N := by
          simp only [weight, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons] at hw ⊢
          omega
        simpa only [wordMap_append, wordMap_cons] using lower _ hw'
      · intro i j _
        change wordMap s (act c.state i (act b.state j (wordMap t u))) ∈ S
        have hw' : weight (s ++ (c, i) :: (b, j) :: t) < N := by
          simp only [weight, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons] at hw ⊢
          omega
        simpa only [wordMap_append, wordMap_cons] using lower _ hw'

/-- Every homogeneous mode word on the seed belongs to the span of strict
representative words. The three inductions use weight, length, and bounded
square-sum deficit, with high rightmost indices removed by truncation. -/
theorem word_mem_strictSpan
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (X : Finset (Homogeneous D)) (u : paritySpace D hu (-1))
    (hX : ∀ a : Homogeneous D, a.state ∈ Submodule.span ℂ (sourceGenerators X a.weight))
    (t : Word D) : wordMap t u ∈ strictSpan X u := by
  suffices main : ∀ N, ∀ w : Word D, weight w ≤ N → wordMap w u ∈ strictSpan X u from
    main (weight t) t le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have lower (w : Word D) (hw : weight w < N) : wordMap w u ∈ strictSpan X u :=
      ih (weight w) hw w le_rfl
    suffices byLength : ∀ k, ∀ w : Word D, weight w ≤ N → w.length = k →
        wordMap w u ∈ strictSpan X u from
      fun w hw => byLength w.length w hw rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k ihk =>
      intro w hw hl
      have shorter (v : Word D) (hv : weight v ≤ N) (hv' : v.length < k) :
          wordMap v u ∈ strictSpan X u := ihk v.length hv' v hv rfl
      exact replace_letters_mem hD X u hX N k lower
        (representative_words_mem hD X u N k lower shorter) w []
        (by simp [lettersIn]) hw hl

#print axioms word_mem_strictSpan

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning
