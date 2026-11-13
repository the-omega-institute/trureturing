/- GID: D5/S1/Words/LatticePaths/MatharA379464Counting
   generality: I
   mirror-B: D5/B/S1/Words/LatticePaths/MatharA379464Counting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal path counting and optional-letter insertion for OEIS A379464. -/

/-
Public declarations:
  Step: proof_shape: bind-only; escape_witness: none; consumers: a, literal_count_insertion.
  IsPath: proof_shape: bind-only; escape_witness: none; consumers: a, literal_list_bridge, literal_count_insertion.
  a: proof_shape: bind-only; escape_witness: none; consumers: claim, literal_count_insertion, binomial_counting.
  three_positive_rotations: proof_shape: content; escape_witness: three_positive_rotations; consumer: cuts_count.
  binomial_counting: proof_shape: content; escape_witness: three_positive_rotations; consumer: Result.literal_certificate.
  admission_basis: escape-witness: three_positive_rotations.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25538.
Direct frozen dependencies: D5.S1.Words.Compositions.ZeroSumWordCount.prefix_segment_sum.
Private content theorems: hit_level, above_after_last, good_at_level, good_cut_count, above_filter_zero, path_filter_zero, cuts_count, positive_word_count, positive_word_cardinality, insertion_formula, literal_option_bridge, literal_count_insertion, zero_free_multiple, zero_free_formula. Their witnesses are hit_level, above_filter_zero, insertion_formula, or three_positive_rotations on their compiled dependency paths. The remaining private theorems are bind-only and have named live consumers in the compiled dependency inventory. Proposition-valued private definitions GoodCut, Above, ListPath, positive, Strict, and P are consumed by their counting lemmas.
The source definitions and the cyclic count are unbounded symbolic mathematics; utility: none.
-/

import D5.S1.Words.Compositions.ZeroSumWordCount

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace D5.S1.Words.LatticePaths.MatharA379464Counting
open scoped BigOperators

open scoped BigOperators

abbrev Step := {s : ℤ // s ∈ ({1, 0, -3} : Finset ℤ)}

/-- From (0,0) to (n,0), with every prefix on or above y = -2. -/
def IsPath {n : ℕ} (w : Fin n → Step) : Prop :=
  (∑ i : Fin n, (w i).val) = 0 ∧
    ∀ r : ℕ, r ≤ n →
      (-2 : ℤ) ≤ ∑ i : Fin n, if i.val < r then (w i).val else 0

/-- OEIS A379464, offset 0. -/
noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact (Fintype.card {w : Fin n → Step // IsPath w} : ℤ)

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

private theorem hit_level (p : ℕ → ℤ) (N : ℕ) (l : ℤ)
    (step : ∀ i, i < N → p (i+1) ≤ p i+1)
    (lower : p 0 ≤ l) (upper : l ≤ p N) :
    ∃ j, j ≤ N ∧ p j = l := by
  induction N with
  | zero => exact ⟨0, le_rfl, by omega⟩
  | succ N ih =>
    by_cases hN : l ≤ p N
    · obtain ⟨j, hj, he⟩ := ih (fun i hi => step i (by omega)) hN
      exact ⟨j, by omega, he⟩
    · exact ⟨N+1, le_rfl, by have h := step N (by omega); omega⟩

private theorem last_visit (p : ℕ → ℤ) (N : ℕ) (l : ℤ)
    (hex : ∃ i, i ≤ N ∧ p i = l) :
    ∃ j, j ≤ N ∧ p j = l ∧ ∀ i, j < i → i ≤ N → p i ≠ l := by
  classical
  obtain ⟨i, hi, he⟩ := hex
  exact ⟨Nat.findGreatest (fun j => p j = l) N,
    Nat.findGreatest_le N, Nat.findGreatest_spec (P := fun j => p j = l) hi he,
    fun j hj hn => Nat.findGreatest_is_greatest hj hn⟩

private theorem above_after_last (p : ℕ → ℤ) (N j : ℕ) (l : ℤ)
    (step : ∀ i, i < N → p (i+1) ≤ p i+1)
    (ending : l < p N)
    (last : ∀ i, j < i → i ≤ N → p i ≠ l) :
    ∀ i, j < i → i ≤ N → l < p i := by
  intro i hij hiN
  by_contra hlo
  have reach := hit_level (fun t => p (i+t)) (N-i) l
    (fun t ht => by simpa [Nat.add_assoc] using step (i+t) (by omega))
    (by simpa using (show p i ≤ l by omega))
    (by simpa [Nat.add_sub_of_le hiN] using ending.le)
  obtain ⟨t, ht, he⟩ := reach
  exact last (i+t) (by omega) (by omega) he

private def GoodCut (p : ℕ → ℤ) (N j : ℕ) : Prop :=
  (∀ i, j < i → i ≤ N → p j < p i) ∧
    ∀ i, i ≤ j → p j < p i+3

private theorem good_level_unique (p : ℕ → ℤ) (N : ℕ) (j k : Fin N)
    (hj : GoodCut p N j.val) (hk : GoodCut p N k.val)
    (he : p j.val = p k.val) : j = k := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := hj.1 k.val h (Nat.le_of_lt k.isLt)
    omega
  · have hlt := hk.1 j.val h (Nat.le_of_lt j.isLt)
    omega

private theorem good_at_level (p : ℕ → ℤ) (N : ℕ) (m : ℤ)
    (step : ∀ i, i < N → p (i+1) ≤ p i+1)
    (ending : p N = p 0+3)
    (minimal : ∀ i, i ≤ N → m ≤ p i)
    (attains : ∃ i, i ≤ N ∧ p i = m) (c : Fin 3) :
    ∃! j : Fin N, GoodCut p N j.val ∧ p j.val = m+(c.val : ℤ) := by
  have hc := c.isLt
  have hm := minimal 0 (Nat.zero_le _)
  obtain ⟨i, hi, hei⟩ := attains
  have reach := hit_level (fun t => p (i+t)) (N-i) (m+c.val)
    (fun t ht => by simpa [Nat.add_assoc] using step (i+t) (by omega))
    (by simpa [hei] using (show m ≤ m+(c.val : ℤ) by omega))
    (by simpa [Nat.add_sub_of_le hi] using (show m+(c.val : ℤ) ≤ p N by omega))
  obtain ⟨t, ht, het⟩ := reach
  obtain ⟨j, hj, hej, hlast⟩ := last_visit p N (m+c.val) ⟨i+t, by omega, het⟩
  have hEnd : m+(c.val : ℤ) < p N := by omega
  have hjN : j < N := by
    by_contra h
    have je : j = N := by omega
    rw [je] at hej
    omega
  have hgood : GoodCut p N j := by
    refine ⟨?_, ?_⟩
    · intro k hjk hk
      rw [hej]
      exact above_after_last p N j (m+c.val) step hEnd hlast k hjk hk
    · intro k hkj
      have hmk := minimal k (by omega)
      omega
  refine ⟨⟨j, hjN⟩, ⟨hgood, hej⟩, ?_⟩
  intro k hk
  exact good_level_unique p N k ⟨j, hjN⟩ hk.1 hgood (by simpa only [Fin.val_mk] using hk.2.trans hej.symm)

private theorem level_of_good (p : ℕ → ℤ) (N : ℕ) (m : ℤ)
    (minimal : ∀ i, i ≤ N → m ≤ p i)
    (attains : ∃ i, i ≤ N ∧ p i = m)
    (j : Fin N) (hj : GoodCut p N j.val) :
    ∃ c : Fin 3, p j.val = m+(c.val : ℤ) := by
  have hmj := minimal j.val (Nat.le_of_lt j.isLt)
  obtain ⟨i, hi, he⟩ := attains
  have hij : i ≤ j.val := by
    by_contra h
    have hlt := hj.1 i (by omega) hi
    omega
  have hhigh := hj.2 i hij
  have hc : (p j.val-m).toNat < 3 := by omega
  refine ⟨⟨(p j.val-m).toNat, hc⟩, ?_⟩
  simp only [Fin.val_mk]
  omega

private theorem good_cut_count (p : ℕ → ℤ) (N : ℕ) (m : ℤ)
    (step : ∀ i, i < N → p (i+1) ≤ p i+1)
    (ending : p N = p 0+3)
    (minimal : ∀ i, i ≤ N → m ≤ p i)
    (attains : ∃ i, i ≤ N ∧ p i = m) :
    Fintype.card {j : Fin N // GoodCut p N j.val} = 3 := by
  classical
  let readout : {j : Fin N // GoodCut p N j.val} → Fin 3 :=
    fun j => Classical.choose (level_of_good p N m minimal attains j.val j.property)
  have readout_eq (j : {j : Fin N // GoodCut p N j.val}) :
      p j.val.val = m+((readout j).val : ℤ) :=
    Classical.choose_spec (level_of_good p N m minimal attains j.val j.property)
  have injective : Function.Injective readout := by
    intro j k he
    apply Subtype.ext
    apply good_level_unique p N j.val k.val j.property k.property
    have hj := readout_eq j
    have hk := readout_eq k
    rw [he] at hj
    omega
  have surjective : Function.Surjective readout := by
    intro c
    obtain ⟨j, hj, _⟩ := good_at_level p N m step ending minimal attains c
    refine ⟨⟨j, hj.1⟩, ?_⟩
    have he := readout_eq ⟨j, hj.1⟩
    change p j.val = m+((readout ⟨j, hj.1⟩).val : ℤ) at he
    apply Fin.ext
    have hc := hj.2
    omega
  exact (Fintype.card_congr (Equiv.ofBijective readout ⟨injective, surjective⟩)).trans
    (Fintype.card_fin 3)

private theorem finite_minimum (p : ℕ → ℤ) (N : ℕ) :
    ∃ m : ℤ, (∀ i, i ≤ N → m ≤ p i) ∧ ∃ i, i ≤ N ∧ p i = m := by
  classical
  let s := (Finset.range (N+1)).image p
  have hs : s.Nonempty := ⟨p 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · intro i hi
    exact Finset.min'_le s _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    exact ⟨i, by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi, he⟩

private theorem rotation_prefix_short (w : List ℤ) (j r : ℕ)
    (hj : j ≤ w.length) (hr : r ≤ w.length-j) :
    ((w.rotate j).take r).sum = (w.take (j+r)).sum - (w.take j).sum := by
  rw [List.rotate_eq_drop_append_take hj,
    List.take_append_of_le_length (by simpa only [List.length_drop] using hr)]
  have hsum : (w.take (j+r)).sum = (w.take j).sum + ((w.drop j).take r).sum := by
    exact (D5.S1.Words.Compositions.ZeroSumWordCount.prefix_segment_sum w j r).symm
  omega

private theorem rotation_prefix_long (w : List ℤ) (j r : ℕ)
    (hj : j ≤ w.length) (hr : w.length-j ≤ r) (hrn : r ≤ w.length) :
    ((w.rotate j).take r).sum = w.sum - (w.take j).sum +
      (w.take (r-(w.length-j))).sum := by
  rw [List.rotate_eq_drop_append_take hj, List.take_append]
  simp only [List.length_drop]
  rw [List.take_of_length_le (by simpa only [List.length_drop] using hr),
    List.take_take, Nat.min_eq_left (by omega), List.sum_append]
  have hsum := List.sum_take_add_sum_drop w j
  omega

private theorem good_iff_positive (w : List ℤ) (total : w.sum = 3) (j : Fin w.length) :
    GoodCut (fun r => (w.take r).sum) w.length j.val ↔
      ∀ r : ℕ, 0 < r → r ≤ w.length → 0 < ((w.rotate j.val).take r).sum := by
  dsimp only [GoodCut]
  constructor
  · intro hg r hr hrn
    by_cases hs : r ≤ w.length-j.val
    · rw [rotation_prefix_short w j.val r j.isLt.le hs]
      have h := hg.1 (j.val+r) (by omega) (by omega)
      omega
    · rw [rotation_prefix_long w j.val r j.isLt.le (by omega) hrn, total]
      have h := hg.2 (r-(w.length-j.val)) (by omega)
      omega
  · intro hp
    constructor
    · intro i hji hin
      have h := hp (i-j.val) (by omega) (by omega)
      rw [rotation_prefix_short w j.val (i-j.val) j.isLt.le (by omega),
        Nat.add_sub_of_le (by omega : j.val ≤ i)] at h
      omega
    · intro i hij
      have h := hp (w.length-j.val+i) (by omega) (by omega)
      rw [rotation_prefix_long w j.val (w.length-j.val+i) j.isLt.le (by omega) (by omega),
        Nat.add_sub_cancel_left, total] at h
      omega

theorem three_positive_rotations (w : List ℤ)
    (step : ∀ x ∈ w, x ≤ 1) (total : w.sum = 3) :
    Fintype.card {j : Fin w.length //
      ∀ r : ℕ, 0 < r → r ≤ w.length → 0 < ((w.rotate j.val).take r).sum} = 3 := by
  classical
  obtain ⟨m, hmin, hatt⟩ := finite_minimum (fun r => (w.take r).sum) w.length
  have hs : ∀ i, i < w.length → (w.take (i+1)).sum ≤ (w.take i).sum+1 := by
    intro i hi
    rw [List.sum_take_succ w i hi]
    have h := step w[i] (List.getElem_mem hi)
    omega
  have ht : (w.take w.length).sum = (w.take 0).sum+3 := by simpa using total
  have hc := good_cut_count (fun r => (w.take r).sum) w.length m hs ht hmin hatt
  let e : {j : Fin w.length // GoodCut (fun r => (w.take r).sum) w.length j.val} ≃
      {j : Fin w.length // ∀ r : ℕ, 0 < r → r ≤ w.length →
        0 < ((w.rotate j.val).take r).sum} :=
    Equiv.subtypeEquivRight (fun j => good_iff_positive w total j)
  exact (Fintype.card_congr e).symm.trans hc

open scoped BigOperators
private def prefixSum {n : ℕ} (w : Fin n → ℤ) (r : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val < r then w i else 0

private def Above (h : ℤ) (word : List ℤ) : Prop :=
  ∀ r : ℕ, r ≤ word.length → (-2 : ℤ) ≤ h+(word.take r).sum

private theorem above_initial (h : ℤ) (word : List ℤ) (ha : Above h word) :
    (-2 : ℤ) ≤ h := by
  simpa using ha 0 (Nat.zero_le _)

private theorem above_cons (h x : ℤ) (word : List ℤ) :
    Above h (x::word) ↔ (-2 : ℤ) ≤ h ∧ Above (h+x) word := by
  constructor
  · intro ha
    refine ⟨above_initial h (x::word) ha, ?_⟩
    intro r hr
    have hh := ha (r+1) (by simpa using Nat.succ_le_succ hr)
    simpa [List.take_succ_cons, add_assoc] using hh
  · rintro ⟨hh, hw⟩ r hr
    cases r with
    | zero => simpa using hh
    | succ r =>
      have h := hw r (by simpa using hr)
      simpa [List.take_succ_cons, add_assoc] using h

private theorem above_zero_cons (h : ℤ) (word : List ℤ) :
    Above h (0::word) ↔ Above h word := by
  rw [above_cons, add_zero]
  exact ⟨And.right, fun hw => ⟨above_initial h word hw, hw⟩⟩

private theorem above_filter_zero (h : ℤ) (word : List ℤ) :
    Above h (word.filter (· != 0)) ↔ Above h word := by
  induction word generalizing h with
  | nil => rfl
  | cons x word ih =>
    by_cases hx : x = 0
    · subst x
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false]
      rw [above_zero_cons, ih]
    · simp only [List.filter_cons, bne_iff_ne]
      rw [if_pos hx, above_cons, above_cons, ih]

private def ListPath (word : List ℤ) : Prop := word.sum = 0 ∧ Above 0 word

private theorem path_filter_zero (word : List ℤ) :
    ListPath (word.filter (· != 0)) ↔ ListPath word := by
  rw [ListPath, ListPath, List.sum_filter_bne_zero, above_filter_zero]

open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem double_count {W : Type} [Fintype W] (N : ℕ)
    (rotate : Fin N → W ≃ W) (positive : W → Prop)
    (cuts : ∀ w : W, Fintype.card {j : Fin N // positive (rotate j w)} = 3) :
    Fintype.card {w : W // positive w} * N = 3 * Fintype.card W := by
  classical
  let e : (Σ w : W, {j : Fin N // positive (rotate j w)}) ≃
      ({w : W // positive w} × Fin N) :=
    { toFun := fun x => (⟨rotate x.2.val x.1, x.2.property⟩, x.2.val)
      invFun := fun y => ⟨(rotate y.2).symm y.1.val,
        ⟨y.2, by simpa only [Equiv.apply_symm_apply] using y.1.property⟩⟩
      left_inv := by
        rintro ⟨w, j, hj⟩
        dsimp only
        apply Sigma.ext ((rotate j).symm_apply_apply w)
        apply (Subtype.heq_iff_coe_eq (fun k => by
          dsimp only
          rw [(rotate j).symm_apply_apply w])).mpr
        rfl
      right_inv := by
        rintro ⟨⟨w, hw⟩, j⟩
        simp }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, cuts,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at hc
  omega

private def increment (b : Bool) : ℤ := if b then 1 else -3

private def values {N : ℕ} (v : List.Vector Bool N) : List ℤ := v.val.map increment

private abbrev Word (N : ℕ) := {v : List.Vector Bool N // (values v).sum = 3}

private def positive {N : ℕ} (w : Word N) : Prop :=
  ∀ r : ℕ, 0 < r → r ≤ N → 0 < ((values w.val).take r).sum

private def vectorRotate {N : ℕ} (j : Fin N) :
    List.Vector Bool N ≃ List.Vector Bool N where
  toFun v := ⟨v.val.rotate j.val, by simpa using v.property⟩
  invFun v := ⟨v.val.rotate (N-j.val), by simpa using v.property⟩
  left_inv v := by
    apply Subtype.ext
    change (v.val.rotate j.val).rotate (N-j.val) = v.val
    rw [List.rotate_rotate, Nat.add_sub_of_le j.isLt.le]
    simpa only [v.property] using List.rotate_length v.val
  right_inv v := by
    apply Subtype.ext
    change (v.val.rotate (N-j.val)).rotate j.val = v.val
    rw [List.rotate_rotate, Nat.sub_add_cancel j.isLt.le]
    simpa only [v.property] using List.rotate_length v.val

private theorem rotated_values {N : ℕ} (v : List.Vector Bool N) (j : Fin N) :
    values (vectorRotate j v) = (values v).rotate j.val := by
  exact List.map_rotate increment v.val j.val

private def rotateWord {N : ℕ} (j : Fin N) : Word N ≃ Word N :=
  (vectorRotate j).subtypeEquiv (by
    intro v
    rw [rotated_values]
    rw [(List.rotate_perm (values v) j.val).sum_eq])

private theorem cuts_count {N : ℕ} (w : Word N) :
    Fintype.card {j : Fin N // positive (rotateWord j w)} = 3 := by
  have hsteps : ∀ x ∈ values w.val, x ≤ 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    cases b <;> norm_num [increment]
  have hc := three_positive_rotations (values w.val) hsteps w.property
  have hp (j : Fin N) : positive (rotateWord j w) ↔
      ∀ r : ℕ, 0 < r → r ≤ N → 0 < (((values w.val).rotate j.val).take r).sum := by
    change (∀ r : ℕ, 0 < r → r ≤ N → 0 < ((values (vectorRotate j w.val)).take r).sum) ↔ _
    rw [rotated_values]
  simp_rw [hp]
  have hl : (values w.val).length = N := by simp [values]
  let e : {j : Fin N // ∀ r : ℕ, 0 < r → r ≤ N →
      0 < (((values w.val).rotate j.val).take r).sum} ≃
      {j : Fin (values w.val).length // ∀ r : ℕ, 0 < r → r ≤ (values w.val).length →
      0 < (((values w.val).rotate j.val).take r).sum} :=
    { toFun := fun j => ⟨⟨j.val.val, lt_of_lt_of_eq j.val.isLt hl.symm⟩,
        fun r hr hrn => j.property r hr (by omega)⟩
      invFun := fun j => ⟨⟨j.val.val, lt_of_lt_of_eq j.val.isLt hl⟩,
        fun r hr hrn => j.property r hr (by omega)⟩
      left_inv := by intro j; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro j; apply Subtype.ext; apply Fin.ext; rfl }
  exact (Fintype.card_congr e).trans hc

private theorem positive_word_count (N : ℕ) :
    Fintype.card {w : Word N // positive w} * N = 3 * Fintype.card (Word N) :=
  double_count N rotateWord positive cuts_count

private def downset {N : ℕ} (v : List.Vector Bool N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => v.get i = false)

private theorem values_sum {N : ℕ} (v : List.Vector Bool N) :
    (values v).sum = (N : ℤ)-4*(downset v).card := by
  have hv : List.ofFn v.get = v.val := by
    have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
    rw [List.Vector.toList_ofFn] at h
    simpa only [List.Vector.toList] using h
  have hs : (values v).sum = ∑ i : Fin N, increment (v.get i) := by
    unfold values
    rw [← hv, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hs]
  calc
    _ = ∑ i : Fin N, ((1 : ℤ)-4*(if v.get i = false then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases h : v.get i <;> norm_num [increment]
    _ = (N : ℤ)-4*(downset v).card := by
      have hc : (∑ i : Fin N, (if v.get i = false then (1 : ℤ) else 0)) =
          (downset v).card := by simp [downset]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hc]
      simp

private theorem downset_ofFn {N : ℕ} (s : Finset (Fin N)) :
    downset (List.Vector.ofFn (fun i => decide (i ∉ s))) = s := by
  ext i
  simp [downset]

private theorem unrestricted_word_count (k : ℕ) :
    Fintype.card (Word (4*k+3)) = (4*k+3).choose k := by
  classical
  let e : Word (4*k+3) ≃ {s : Finset (Fin (4*k+3)) // s.card = k} :=
    { toFun := fun w => ⟨downset w.val, by
        have h := values_sum w.val
        rw [w.property] at h
        omega⟩
      invFun := fun s => ⟨List.Vector.ofFn (fun i => decide (i ∉ s.val)), by
        rw [values_sum, downset_ofFn, s.property]
        push_cast
        ring⟩
      left_inv := by
        intro w
        apply Subtype.ext
        apply List.Vector.ext
        intro i
        change (List.Vector.ofFn (fun i => decide (i ∉ downset w.val))).get i = w.val.get i
        rw [List.Vector.get_ofFn]
        cases h : w.val.get i <;> simp [downset, h]
      right_inv := by
        intro s
        apply Subtype.ext
        exact downset_ofFn s.val }
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using Fintype.card_congr e

private theorem positive_word_cardinality (k : ℕ) :
    Fintype.card {w : Word (4*k+3) // positive w} * (4*k+3) =
      3 * (4*k+3).choose k := by
  rw [← unrestricted_word_count]
  exact positive_word_count (4*k+3)

open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem prefix_ofFn {n : ℕ} (w : Fin n → ℤ) (r : ℕ) :
    ((List.ofFn w).take r).sum = prefixSum w r := by
  simpa only [prefixSum, Finset.sum_filter] using List.sum_take_ofFn w r

private theorem literal_list_bridge {n : ℕ}
    (w : Fin n → Step) :
    IsPath w ↔
      ListPath (List.ofFn (fun i => (w i).val)) := by
  simp only [IsPath, ListPath,
    Above, List.sum_ofFn, List.length_ofFn,
    prefix_ofFn, zero_add, prefixSum]

noncomputable def count (α : Type) [Fintype α] (n : ℕ) (P : List α → Prop) : ℕ :=
  Fintype.card {w : Fin n → α // P (List.ofFn w)}

private theorem count_succ (α : Type) [Fintype α] (n : ℕ) (P : List α → Prop) :
    count α (n+1) P = ∑ a : α, count α n (fun l => P (a::l)) := by
  classical
  let e : {w : Fin (n+1) → α // P (List.ofFn w)} ≃
      (Σ a : α, {w : Fin n → α // P (a::List.ofFn w)}) :=
    { toFun := fun w => ⟨w.val 0, ⟨fun i => w.val i.succ, by
        simpa only [List.ofFn_succ] using w.property⟩⟩
      invFun := fun p => ⟨Fin.cons p.1 p.2.val, by
        simpa only [List.ofFn_cons] using p.2.property⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      right_inv := by
        intro p
        rcases p with ⟨a, w, hw⟩
        rfl }
  simpa only [count, Fintype.card_sigma] using Fintype.card_congr e

private theorem count_zero (α : Type) [Fintype α] (P : List α → Prop) :
    count α 0 P = if P [] then 1 else 0 := by
  classical
  by_cases hp : P [] <;> simp [count, hp]

private theorem option_count_succ (α : Type) [Fintype α] (n : ℕ) (P : List α → Prop) :
    count (Option α) (n+1) (fun l => P (l.filterMap id)) =
      count (Option α) n (fun l => P (l.filterMap id)) +
      ∑ a : α, count (Option α) n (fun l => P (a::l.filterMap id)) := by
  rw [count_succ, Fintype.sum_option]
  simp only [List.filterMap_cons, id_eq, Option.elim_none, Option.elim_some]

theorem insertion_formula (α : Type) [Fintype α] (n : ℕ) (P : List α → Prop) :
    count (Option α) n (fun l => P (l.filterMap id)) =
      ∑ k ∈ Finset.range (n+1), n.choose k * count α k P := by
  classical
  induction n generalizing P with
  | zero => by_cases hp : P [] <;> simp [count_zero, hp]
  | succ n ih =>
    rw [option_count_succ]
    rw [ih P]
    have ht : (∑ a : α, count (Option α) n (fun l => P (a::l.filterMap id))) =
        ∑ k ∈ Finset.range (n+1), n.choose k * count α (k+1) P := by
      calc
        _ = ∑ a : α, ∑ k ∈ Finset.range (n+1), n.choose k *
            count α k (fun l => P (a::l)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact ih (fun l => P (a::l))
        _ = _ := by
          rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum, ← count_succ]
    rw [ht]
    exact (Finset.sum_choose_succ_mul (fun k _ => count α k P) n).symm

attribute [local instance] Classical.propDecidable
open scoped BigOperators

private def stepEquiv : Option Bool ≃ Step where
  toFun o := match o with
    | none => ⟨0, by simp⟩
    | some true => ⟨1, by simp⟩
    | some false => ⟨-3, by simp⟩
  invFun s := if s.val = 0 then none else if s.val = 1 then some true else some false
  left_inv o := by cases o with
    | none => rfl
    | some b => cases b <;> decide
  right_inv s := by
    apply Subtype.ext
    have hs : s.val = 1 ∨ s.val = 0 ∨ s.val = -3 := by
      have hs := s.property
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      exact hs
    rcases hs with h | h | h <;> simp [h]

private def stepValue (o : Option Bool) : ℤ := (stepEquiv o).val

private theorem erase_step_values (l : List (Option Bool)) :
    (l.map stepValue).filter (· != 0) = (l.filterMap id).map increment := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o with
    | none => simpa [stepValue, stepEquiv] using ih
    | some b => cases b <;> simp [stepValue, stepEquiv, increment, ih]

private theorem literal_option_bridge {n : ℕ} (w : Fin n → Option Bool) :
    IsPath (fun i => stepEquiv (w i)) ↔
      ListPath ((List.ofFn w).filterMap id |>.map increment) := by
  rw [literal_list_bridge]
  change ListPath (List.ofFn (fun i => stepValue (w i))) ↔ _
  rw [List.ofFn_comp' w stepValue, ← path_filter_zero, erase_step_values]

private theorem literal_count_insertion (n : ℕ) :
    a n =
      ((∑ k ∈ Finset.range (n+1), n.choose k *
        count Bool k (fun l => ListPath (l.map increment)) : ℕ) : ℤ) := by
  classical
  let e : (Fin n → Option Bool) ≃ (Fin n → Step) :=
    { toFun := fun w i => stepEquiv (w i)
      invFun := fun w i => stepEquiv.symm (w i)
      left_inv := by intro w; funext i; exact stepEquiv.symm_apply_apply _
      right_inv := by intro w; funext i; exact stepEquiv.apply_symm_apply _ }
  let ep := e.subtypeEquiv (fun w => (literal_option_bridge w).symm)
  have hc : count (Option Bool) n (fun l => ListPath ((l.filterMap id).map increment)) =
      Fintype.card {w : Fin n → Step //
        IsPath w} := Fintype.card_congr ep
  have hi := insertion_formula Bool n
    (fun l => ListPath (l.map increment))
  rw [hc] at hi
  unfold a
  exact_mod_cast hi

attribute [local instance] Classical.propDecidable

private def Strict (l : List ℤ) : Prop :=
  l.sum = 3 ∧ ∀ r : ℕ, 0 < r → r ≤ l.length → 0 < (l.take r).sum

private theorem strict_prepend_three (l : List ℤ) :
    Strict (1::1::1::l) ↔ ListPath l := by
  constructor
  · rintro ⟨ht, hp⟩
    constructor
    · simp only [List.sum_cons] at ht
      omega
    · intro r hr
      have h := hp (r+3) (by omega) (by simpa only [List.length_cons] using Nat.add_le_add_right hr 3)
      have h' : 0 < (1+(1+(1+(l.take r).sum))) := by
        exact Int.lt_of_add_one_le h
      omega
  · rintro ⟨ht, hp⟩
    constructor
    · simp [ht]
    · intro r hr hrn
      cases r with
      | zero => omega
      | succ r =>
        cases r with
        | zero => norm_num
        | succ r =>
          cases r with
          | zero => norm_num
          | succ r =>
            have h := hp r (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hrn)
            simp only [List.take_succ_cons, List.sum_cons]
            omega

private theorem positive_three_heads {n : ℕ} (w : Word (3+n)) (hp : positive w) :
    ∃ l : List Bool, w.val.val = true::true::true::l := by
  rcases w with ⟨⟨l, hlen⟩, ht⟩
  change ∀ r : ℕ, 0 < r → r ≤ 3+n → 0 < ((l.map increment).take r).sum at hp
  cases l with
  | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons b l =>
    cases b with
    | false =>
      have h := hp 1 (by decide) (by omega)
      norm_num [increment] at h
    | true =>
      cases l with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons b l =>
        cases b with
        | false =>
          have h := hp 2 (by decide) (by omega)
          norm_num [increment] at h
        | true =>
          cases l with
          | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
          | cons b l =>
            cases b with
            | false =>
              have h := hp 3 (by decide) (by omega)
              norm_num [increment] at h
            | true => exact ⟨l, rfl⟩

private theorem positive_strict {N : ℕ} (w : Word N) (hp : positive w) :
    Strict (values w.val) := by
  refine ⟨w.property, ?_⟩
  simpa only [positive, values, List.length_map, List.Vector.length_val] using hp

private abbrev Tail (n : ℕ) := {v : List.Vector Bool n // ListPath (values v)}

private def prependTail {n : ℕ} (v : Tail n) : {w : Word (3+n) // positive w} := by
  let l := true::true::true::v.val.val
  have ht : Strict (l.map increment) := by
    apply (strict_prepend_three (values v.val)).mpr
    exact v.property
  refine ⟨⟨⟨l, by simp only [l, List.length_cons, v.val.property]; omega⟩, ht.1⟩, ?_⟩
  simpa only [positive, values, List.length_map,
    show l.length = 3+n by simp only [l, List.length_cons, v.val.property]; omega] using ht.2

private def extractTail {n : ℕ} (w : {w : Word (3+n) // positive w}) : Tail n := by
  refine ⟨⟨w.val.val.val.drop 3, by simp [w.val.val.property]⟩, ?_⟩
  have hs := positive_strict w.val w.property
  obtain ⟨l, hl⟩ := positive_three_heads w.val w.property
  have hpath : ListPath (l.map increment) := by
    apply (strict_prepend_three (l.map increment)).mp
    simpa [values, hl, increment] using hs
  simpa only [values, hl, List.drop_succ_cons, List.drop_zero] using hpath

private theorem tail_cardinality (n : ℕ) :
    Fintype.card {w : Word (3+n) // positive w} = Fintype.card (Tail n) := by
  classical
  let e : {w : Word (3+n) // positive w} ≃ Tail n :=
    { toFun := extractTail
      invFun := prependTail
      left_inv := by
        intro w
        obtain ⟨l, hl⟩ := positive_three_heads w.val w.property
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change true::true::true::(w.val.val.val.drop 3) = w.val.val.val
        simp only [hl, List.drop_succ_cons, List.drop_zero]
      right_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        change (true::true::true::v.val.val).drop 3 = v.val.val
        rfl }
  exact Fintype.card_congr e

open scoped BigOperators
attribute [local instance] Classical.propDecidable

private def P (l : List Bool) : Prop :=
  ListPath (l.map increment)

private theorem tail_count (n : ℕ) : Fintype.card (Tail n) = count Bool n P := by
  classical
  let e := (Equiv.vectorEquivFin Bool n).subtypeEquiv (p := fun v => ListPath (values v))
    (q := fun f => P (List.ofFn f)) (by
      intro v
      have hl : List.ofFn v.get = v.val := by
        have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
        rw [List.Vector.toList_ofFn] at h
        simpa only [List.Vector.toList] using h
      change ListPath (v.val.map increment) ↔
        ListPath ((List.ofFn v.get).map increment)
      rw [hl])
  exact Fintype.card_congr e

private theorem zero_free_count (n : ℕ) :
    count Bool n P = Fintype.card {w : Word (3+n) // positive w} :=
  (tail_count n).symm.trans (tail_cardinality n).symm

private theorem zero_free_multiple (k : ℕ) :
    count Bool (4*k) P * (4*k+3) = 3*(4*k+3).choose k := by
  rw [zero_free_count, show 3+4*k = 4*k+3 by omega]
  exact positive_word_cardinality k

private theorem zero_free_vanish (n : ℕ) (hn : ¬4 ∣ n) : count Bool n P = 0 := by
  classical
  letI : IsEmpty {w : Fin n → Bool // P (List.ofFn w)} := ⟨by
    intro w
    have he := (show ListPath ((List.ofFn w.val).map increment) from w.property).1
    have hs := values_sum (List.Vector.ofFn w.val)
    change ((List.Vector.ofFn w.val).toList.map increment).sum = (n : ℤ)-
      4*(downset (List.Vector.ofFn w.val)).card at hs
    rw [List.Vector.toList_ofFn, he] at hs
    apply hn
    refine ⟨(downset (List.Vector.ofFn w.val)).card, ?_⟩
    omega⟩
  exact Fintype.card_of_isEmpty

private theorem zero_free_formula (k : ℕ) :
    (count Bool (4*k) P : ℚ) = 3*(Nat.factorial (4*k+2) : ℚ) /
      ((Nat.factorial k : ℚ)*(Nat.factorial (3*k+3) : ℚ)) := by
  have hc : (count Bool (4*k) P : ℚ)*(4*k+3) = 3*((4*k+3).choose k : ℚ) := by
    exact_mod_cast zero_free_multiple k
  have hf : ((4*k+3).choose k : ℚ)*(Nat.factorial k : ℚ)*
      (Nat.factorial (3*k+3) : ℚ) = (4*k+3 : ℚ)*(Nat.factorial (4*k+2) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 4*k+3)
    rw [show 4*k+3-k = 3*k+3 by omega] at h
    have hfac : Nat.factorial (4*k+3) = (4*k+3)*Nat.factorial (4*k+2) := by
      exact Nat.factorial_succ (4*k+2)
    rw [hfac] at h
    exact_mod_cast h
  have hd : (Nat.factorial k : ℚ)*(Nat.factorial (3*k+3) : ℚ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (3*k+3))
  apply (eq_div_iff hd).mpr
  have hN : (4*k+3 : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hN
  linear_combination ((Nat.factorial k : ℚ)*(Nat.factorial (3*k+3) : ℚ))*hc + 3*hf

theorem binomial_counting (n : ℕ) :
    (a n : ℚ) =
      ∑ k ∈ Finset.range (n+1), (n.choose (4*k) : ℚ) *
        (3*(Nat.factorial (4*k+2) : ℚ) /
          ((Nat.factorial k : ℚ)*(Nat.factorial (3*k+3) : ℚ))) := by
  classical
  have hc : (a n : ℚ) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℚ)*(count Bool j P : ℚ) := by
    exact_mod_cast literal_count_insertion n
  rw [hc]
  apply Finset.sum_bij_ne_zero (fun j _ _ => j/4)
  · intro j hj hne
    exact Finset.mem_range.mpr (by have h := Finset.mem_range.mp hj; omega)
  · intro j hj hje k hk hke heq
    have hj4 : 4 ∣ j := by
      by_contra h
      rw [zero_free_vanish j h, Nat.cast_zero, mul_zero] at hje
      exact hje rfl
    have hk4 : 4 ∣ k := by
      by_contra h
      rw [zero_free_vanish k h, Nat.cast_zero, mul_zero] at hke
      exact hke rfl
    have hj' := Nat.mod_eq_zero_of_dvd hj4
    have hk' := Nat.mod_eq_zero_of_dvd hk4
    omega
  · intro k hk hne
    have hbound : 4*k ≤ n := by
      by_contra h
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul] at hne
      exact hne rfl
    refine ⟨4*k, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · simpa only [zero_free_formula] using hne
    · omega
  · intro j hj hne
    have hj4 : 4 ∣ j := by
      by_contra h
      rw [zero_free_vanish j h, Nat.cast_zero, mul_zero] at hne
      exact hne rfl
    have hmul : 4*(j/4) = j := Nat.mul_div_cancel' hj4
    calc
      _ = (n.choose (4*(j/4)) : ℚ)*(count Bool (4*(j/4)) P : ℚ) := by simp only [hmul]
      _ = _ := by rw [zero_free_formula]

end D5.S1.Words.LatticePaths.MatharA379464Counting
