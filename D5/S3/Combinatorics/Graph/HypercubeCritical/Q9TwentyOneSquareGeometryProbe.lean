import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCompressionProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCenterProbe

/-! The actual cube geometry of the compressed square in the 21-point slice. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private low_not_three diff_self diff_symm diff_triangle compressed_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private alternating_eight_cycle_geometry hamming_dist_after_external_flips
  far_common_midpoint translated_opposite_midpoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCenterProbe
open private square_cross_diagonal from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCompressionProbe

attribute [local instance] Classical.propDecidable

private lemma expanded_square_geometry {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L : Finset (S : Set (Q n))}
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L) :
    let A : Fin 4 → Q n := fun i => (e i).val.val
    ∃ g : Fin 4 → Fin n, Function.Injective g ∧
      ((diff (A 1) (A 0) = {g 0, g 1} ∧
        diff (A 2) (A 0) = {g 0, g 1, g 2, g 3} ∧
        diff (A 3) (A 0) = {g 2, g 3}) ∨
      ∃ z : Q n, A 0 = flip z (g 1) ∧ A 1 = flip z (g 0) ∧
        A 2 = flip z (g 2) ∧ A 3 = flip z (g 3)) := by
  let V := (S : Set (Q n))
  let G := (hypercube n).induce V
  let A : Fin 4 → V := fun i => (e i).val
  have he (i : Fin 4) : (cycleGraph 4).Adj i (i + 1) := by
    revert i
    decide +kernel
  have hadj (i : Fin 4) : ∃ m : V, G.degree m = 2 ∧ G.Adj (A i) m ∧ G.Adj (A (i + 1)) m := by
    obtain ⟨_, m, hm, hl, hr⟩ := e.map_rel_iff.mpr (he i)
    exact ⟨m, hm, hl, hr⟩
  choose m hm ha hb' using hadj
  have hA : Function.Injective A := fun _ _ h => e.injective (Subtype.ext h)
  have hhigh (i : Fin 4) : G.degree (A i) = 3 := (mem_filter.mp (e i).property).2
  have hne (i j : Fin 4) : A i ≠ m j := by
    intro hij
    have hmj := hm j
    rw [← hij, hhigh i] at hmj
    omega
  have hsides : ∀ i j : Fin 4, i ≠ j →
      ∃ k : Fin 4, (k = j ∨ k = j + 1) ∧ k ≠ i ∧ k ≠ i + 1 := by decide +kernel
  have hnext : ∀ i : Fin 4, i ≠ i + 1 := by decide +kernel
  have hm_inj : Function.Injective m := by
    intro i j hij
    by_contra hdiff
    obtain ⟨k, hk, hki, hkn⟩ := hsides i j hdiff
    have hkm : G.Adj (A k) (m i) := by
      rw [hij]
      rcases hk with he | he
      · exact he.symm ▸ ha j
      · exact he.symm ▸ hb' j
    exact low_not_three (hm i) (hA.ne (hnext i)) (hA.ne (Ne.symm hki))
      (hA.ne (Ne.symm hkn)) (ha i).symm (hb' i).symm hkm.symm
  let v : Fin 8 → V := ![A 0, m 0, A 1, m 1, A 2, m 2, A 3, m 3]
  have hv : Function.Injective v := by
    apply List.nodup_ofFn.mp
    change [A 0, m 0, A 1, m 1, A 2, m 2, A 3, m 3].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first
      | exact not_false
      | exact hne _ _
      | exact Ne.symm (hne _ _)
      | apply hA.ne; decide
      | apply hm_inj.ne; decide
  have hvAdj (i : Fin 8) : G.Adj (v i) (v (i + 1)) := by
    fin_cases i
    · exact ha 0
    · exact (hb' 0).symm
    · exact ha 1
    · exact (hb' 1).symm
    · exact ha 2
    · exact (hb' 2).symm
    · exact ha 3
    · exact (hb' 3).symm
  choose w hw using fun i => adjacent_exists_flip (show
    (hypercube n).Adj (v i).val (v (i + 1)).val from hvAdj i)
  exact alternating_eight_cycle_geometry hb v hv w hw

#print axioms expanded_square_geometry

/-- In a rectangle each of the four used coordinates points from a high vertex
towards another high vertex along one of its two difference pairs. -/
private lemma rectangle_difference_pairs {n : ℕ} (A : Fin 4 → Q n) (g : Fin 4 → Fin n)
    (hg : Function.Injective g)
    (h₁ : diff (A 1) (A 0) = {g 0, g 1})
    (h₂ : diff (A 2) (A 0) = {g 0, g 1, g 2, g 3})
    (h₃ : diff (A 3) (A 0) = {g 2, g 3}) :
    let a : Fin 4 → Fin 4 := ![1, 0, 3, 2]
    let b : Fin 4 → Fin 4 := ![3, 2, 1, 0]
    (∀ i, diff (A i) (A (a i)) = {g 0, g 1}) ∧
      (∀ i, diff (A i) (A (b i)) = {g 2, g 3}) ∧
      (∀ i j, i ≠ j → ¬ (cycleGraph 4).Adj i j →
        diff (A i) (A j) = {g 0, g 1, g 2, g 3}) := by
  classical
  let a : Fin 4 → Fin 4 := ![1, 0, 3, 2]
  let b : Fin 4 → Fin 4 := ![3, 2, 1, 0]
  have distinct (i j : Fin 4) (h : i ≠ j) : g i ≠ g j := hg.ne h
  have p23 : diff (A 2) (A 3) = {g 0, g 1} := by
    rw [diff_triangle (A 2) (A 3) (A 0), h₂, h₃]
    ext k
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    grind
  have p12 : diff (A 1) (A 2) = {g 2, g 3} := by
    rw [diff_triangle (A 1) (A 2) (A 0), h₁, h₂]
    ext k
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    grind
  have p13 : diff (A 1) (A 3) = {g 0, g 1, g 2, g 3} := by
    rw [diff_triangle (A 1) (A 3) (A 0), h₁, h₃]
    ext k
    simp only [mem_union, mem_sdiff, mem_insert, mem_singleton]
    grind
  have hdiag : ∀ i j : Fin 4, i ≠ j → ¬ (cycleGraph 4).Adj i j →
      (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (diff_symm _ _).trans h₁
    · exact h₁
    · exact p23
    · exact (diff_symm _ _).trans p23
  · intro i
    fin_cases i
    · exact (diff_symm _ _).trans h₃
    · exact p12
    · exact (diff_symm _ _).trans p12
    · exact h₃
  · intro i j hne hnon
    rcases hdiag i j hne hnon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (diff_symm _ _).trans h₂
    · exact h₂
    · exact p13
    · exact (diff_symm _ _).trans p13

private lemma rectangle_excludes_cross_diagonal
    {n : ℕ} {S : Finset (Q n)}
    {L R : Finset (S : Set (Q n))}
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (B : Fin 4 ↪ SideHigh ((hypercube n).induce (S : Set (Q n))) R)
    (hB : ∀ i y, ((hypercube n).induce (S : Set (Q n))).Adj (e i).val y.val ↔ y = B i)
    (g : Fin 4 → Fin n) (hg : Function.Injective g)
    (h₁ : diff (e 1).val.val (e 0).val.val = {g 0, g 1})
    (h₂ : diff (e 2).val.val (e 0).val.val = {g 0, g 1, g 2, g 3})
    (h₃ : diff (e 3).val.val (e 0).val.val = {g 2, g 3})
    {i j : Fin 4} (hne : i ≠ j) (hnon : ¬ (cycleGraph 4).Adj i j) :
    ¬ (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj (B i) (B j) := by
  intro hadj
  classical
  let A : Fin 4 → Q n := fun k => (e k).val.val
  let a : Fin 4 → Fin 4 := ![1, 0, 3, 2]
  let b : Fin 4 → Fin 4 := ![3, 2, 1, 0]
  obtain ⟨pa, pb, pd⟩ := rectangle_difference_pairs A g hg h₁ h₂ h₃
  have cardA (k : Fin 4) : (diff (A k) (A (a k))).card = 2 := by
    change (diff (A k) (A (a k))).card = 2
    rw [show diff (A k) (A (a k)) = {g 0, g 1} from pa k]
    simp [hg.eq_iff]
  have cardB (k : Fin 4) : (diff (A k) (A (b k))).card = 2 := by
    rw [show diff (A k) (A (b k)) = {g 2, g 3} from pb k]
    simp [hg.eq_iff]
  have ha_ne : ∀ k : Fin 4, a k ≠ k := by decide +kernel
  have hb_ne : ∀ k : Fin 4, b k ≠ k := by decide +kernel
  obtain ⟨f, hf⟩ := adjacent_exists_flip (show (hypercube n).Adj (A i) (B i).val.val from
    (hB i (B i)).mpr rfl)
  obtain ⟨t, ht⟩ := adjacent_exists_flip (show (hypercube n).Adj (A j) (B j).val.val from
    (hB j (B j)).mpr rfl)
  have houtside (k : Fin 4) (r : Fin n) (hr : (B k).val.val = flip (A k) r) :
      r ∉ ({g 0, g 1, g 2, g 3} : Finset (Fin n)) := by
    intro hm
    have against (l : Fin 4) (hl : l ≠ k) (hc : (diff (A k) (A l)).card = 2)
        (hmem : r ∈ diff (A k) (A l)) : False := by
      have hh : (hypercube n).Adj (B k).val.val (A l) := by
        change (diff (B k).val.val (A l)).card = 1
        rw [hr, diff_flip, ite_eq_left hmem, card_erase_of_mem hmem, hc]
      have he : B k = B l := (hB l (B k)).mp hh.symm
      exact hl (B.injective he).symm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact against (a k) (ha_ne k) (cardA k) (by rw [show diff (A k) (A (a k)) = _ from pa k]; simp)
    · exact against (a k) (ha_ne k) (cardA k) (by rw [show diff (A k) (A (a k)) = _ from pa k]; simp)
    · exact against (b k) (hb_ne k) (cardB k) (by rw [show diff (A k) (A (b k)) = _ from pb k]; simp)
    · exact against (b k) (hb_ne k) (cardB k) (by rw [show diff (A k) (A (b k)) = _ from pb k]; simp)
  have hd : diff (A i) (A j) = {g 0, g 1, g 2, g 3} := pd i j hne hnon
  have hbig : hammingDist (A i) (A j) = 4 := by
    change (diff (A i) (A j)).card = 4
    rw [hd]
    simp [hg.eq_iff]
  have hdist := hamming_dist_after_external_flips (A i) (A j) f t
    (hd.symm ▸ houtside i f hf) (hd.symm ▸ houtside j t ht)
  rw [← hf, ← ht, compressed_distance hadj, hbig] at hdist
  omega

#print axioms rectangle_excludes_cross_diagonal

/-- A compressed square on the four-high side forces four actual neighbors
of one cube vertex. The rectangle geometry conflicts with a matched diagonal. -/
private lemma four_high_side_is_star
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (hcount : ∀ x : SideHigh ((hypercube n).induce (S : Set (Q n))) L,
      (GirthSliceCounting.degreeThree ((hypercube n).induce (S : Set (Q n)))
        (((hypercube n).induce (S : Set (Q n))).neighborFinset x.val)).card = 1)
    (hR : Fintype.card (SideHigh ((hypercube n).induce (S : Set (Q n))) R) = 6) :
    let G := (hypercube n).induce (S : Set (Q n))
    ∃ (z : Q n) (s : Fin 4 → Fin n) (B : Fin 4 ↪ SideHigh G R),
      Function.Injective s ∧ (∀ i, (e i).val.val = flip z (s i)) ∧
      (∀ i y, G.Adj (e i).val y.val ↔ y = B i) ∧
      (∀ y, (compressed G R).degree y = if y ∈ Set.range B then 2 else 3) ∧
      ∃ i j, i ≠ j ∧ ¬ (cycleGraph 4).Adj i j ∧ (compressed G R).Adj (B i) (B j) := by
  obtain ⟨B, hB, hdegrees, i, j, hij, hnon, hadj⟩ :=
    square_cross_diagonal hpart hdeg hlow (BalancedCubeGirth.eight_le_egirth S hb) e hcount hR
  obtain ⟨g, hgi, hr | ⟨z, h0, h1, h2, h3⟩⟩ := expanded_square_geometry hb e
  · exact (rectangle_excludes_cross_diagonal e B hB g hgi hr.1 hr.2.1 hr.2.2 hij hnon hadj).elim
  · refine ⟨z, g ∘ Equiv.swap 0 1, B, hgi.comp (Equiv.swap 0 1).injective,
      ?_, hB, hdegrees, i, j, hij, hnon, hadj⟩
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3

#print axioms four_high_side_is_star

/-- A matched diagonal in the star forces the same outward direction at both
ends, and its actual degree-two middle is the translated center. -/
private lemma star_matched_diagonal_midpoint
    {n : ℕ} {S : Finset (Q n)} (hb : IsBalanced S)
    {L R : Finset (S : Set (Q n))}
    (e : cycleGraph 4 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (B : Fin 4 ↪ SideHigh ((hypercube n).induce (S : Set (Q n))) R)
    (hB : ∀ i y, ((hypercube n).induce (S : Set (Q n))).Adj (e i).val y.val ↔ y = B i)
    (z : Q n) (s : Fin 4 → Fin n) (hs : Function.Injective s)
    (hA : ∀ i, (e i).val.val = flip z (s i))
    {i j : Fin 4} (hnon : ¬ (cycleGraph 4).Adj i j)
    (hadj : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj (B i) (B j)) :
    ∃ f : Fin n, f ∉ Set.range s ∧
      (B i).val.val = flip (flip z f) (s i) ∧
      (B j).val.val = flip (flip z f) (s j) ∧
      ∃ m : (S : Set (Q n)),
        ((hypercube n).induce (S : Set (Q n))).degree m = 2 ∧
        ((hypercube n).induce (S : Set (Q n))).Adj (B i).val m ∧
        ((hypercube n).induce (S : Set (Q n))).Adj (B j).val m ∧ m.val = flip z f := by
  classical
  let G := (hypercube n).induce (S : Set (Q n))
  let A : Fin 4 → (S : Set (Q n)) := fun k => (e k).val
  have hinj : Function.Injective A := fun _ _ h => e.injective (Subtype.ext h)
  have hspoke (k : Fin 4) : (hypercube n).Adj z (A k).val := by
    change (hypercube n).Adj z (e k).val.val
    rw [hA]
    exact BalancedCriticalSpectrum.flip_adj _ _
  have sd (x y : Fin 4) (hxy : x ≠ y) : diff (A x).val (A y).val = {s x, s y} := by
    change diff (e x).val.val (e y).val.val = _
    rw [hA, hA, diff_flip, diff_symm z, diff_flip, diff_self]
    simp [hs.eq_iff, hxy, Finset.pair_comm]
  have hsides (x y : Fin 4) (hxy : x ≠ y) : (diff (A x).val (A y).val).card = 2 := by
    rw [sd x y hxy]
    simp [hs.eq_iff, hxy]
  have hnx : ∀ x : Fin 4, x + 1 ≠ x := by decide +kernel
  have hdirs (x : Fin 4) :
      ∃ f : Fin n, f ∉ Set.range s ∧ (B x).val.val = flip (A x).val f := by
    obtain ⟨f, hf⟩ := adjacent_exists_flip (show
      (hypercube n).Adj (A x).val (B x).val.val from (hB x (B x)).mpr rfl)
    refine ⟨f, ?_, hf⟩
    rintro ⟨k, rfl⟩
    have beyond (y : Fin 4) (hy : y ≠ x) (he : (hypercube n).Adj (B x).val.val (A y).val) :
        False := hy (B.injective ((hB y (B x)).mp he.symm)).symm
    by_cases hk : k = x
    · subst k
      have he : (B x).val.val = z := by
        rw [hf, show (A x).val = flip z (s x) from hA x, BalancedCriticalSpectrum.flip_flip]
      exact beyond (x + 1) (hnx x) (he ▸ hspoke (x + 1))
    · apply beyond k hk
      change (diff (B x).val.val (A k).val).card = 1
      have hm : s k ∈ diff (A x).val (A k).val := by rw [sd x k (Ne.symm hk)]; simp
      rw [hf, diff_flip, ite_eq_left hm, card_erase_of_mem hm, hsides x k (Ne.symm hk)]
  have mid_far (x y : Fin 4) (hxy : (cycleGraph 4).Adj x y) :
      flip (flip z (s x)) (s y) ∈ S := by
    obtain ⟨_, l, hl, hxl, hyl⟩ := e.map_rel_iff.mpr hxy
    have hne : l.val ≠ z := by
      intro he
      have ha (k : Fin 4) : G.Adj l (A k) := by
        change (hypercube n).Adj l.val (A k).val
        rw [he]
        exact hspoke k
      exact low_not_three hl (hinj.ne (by decide : (0 : Fin 4) ≠ 1))
        (hinj.ne (by decide : (0 : Fin 4) ≠ 2)) (hinj.ne (by decide : (1 : Fin 4) ≠ 2))
        (ha 0) (ha 1) (ha 2)
    have hxl' : (hypercube n).Adj (flip z (s x)) l.val := by rw [← hA]; exact hxl
    have hyl' : (hypercube n).Adj (flip z (s y)) l.val := by rw [← hA]; exact hyl
    exact far_common_midpoint (hs.ne hxy.ne) hne hxl' hyl' ▸ l.property
  obtain ⟨f, hfext, hf⟩ := hdirs i
  obtain ⟨t, htext, ht⟩ := hdirs j
  have hij : i ≠ j := fun h => hadj.ne (congrArg B h)
  have hfd : f ∉ diff (A i).val (A j).val := by
    rw [sd i j hij]
    simpa only [mem_insert, mem_singleton, not_or] using
      (show f ≠ s i ∧ f ≠ s j from
        ⟨fun he => hfext ⟨i, he.symm⟩, fun he => hfext ⟨j, he.symm⟩⟩)
  have htd : t ∉ diff (A i).val (A j).val := by
    rw [sd i j hij]
    simpa only [mem_insert, mem_singleton, not_or] using
      (show t ≠ s i ∧ t ≠ s j from
        ⟨fun he => htext ⟨i, he.symm⟩, fun he => htext ⟨j, he.symm⟩⟩)
  have hdist := hamming_dist_after_external_flips (A i).val (A j).val f t hfd htd
  rw [← hf, ← ht, compressed_distance hadj] at hdist
  change 2 = (diff (A i).val (A j).val).card + if f = t then 0 else 2 at hdist
  rw [hsides i j hij] at hdist
  have hsame : f = t := by
    by_contra h
    rw [ite_eq_right h] at hdist
    omega
  subst t
  have hBi : (B i).val.val = flip (flip z f) (s i) := by
    rw [hf, show (A i).val = flip z (s i) from hA i, flip_comm]
  have hBj : (B j).val.val = flip (flip z f) (s j) := by
    rw [ht, show (A j).val = flip z (s j) from hA j, flip_comm]
  have hbetween : ∀ x y : Fin 4, x ≠ y → ¬ (cycleGraph 4).Adj x y →
      ∃ k : Fin 4, (cycleGraph 4).Adj x k ∧ (cycleGraph 4).Adj k y := by decide +kernel
  obtain ⟨k, hik, hkj⟩ := hbetween i j hij hnon
  obtain ⟨_, m, hm, him, hjm⟩ := hadj
  obtain ⟨sigma, hσ⟩ := hb
  have vertex (r : Fin 4) : flip z (s r) ∈ S := hA r ▸ (A r).property
  refine ⟨f, hfext, hBi, hBj, m, hm, him, hjm, ?_⟩
  apply translated_opposite_midpoint hσ z (hs.ne hik.ne) (hs.ne hkj.ne) (hs.ne hij)
    (fun h => hfext ⟨i, h⟩) (fun h => hfext ⟨j, h⟩)
    (vertex i) (vertex k) (vertex j) (mid_far i k hik) (mid_far k j hkj)
    (hBi ▸ (B i).val.property) (hBj ▸ (B j).val.property) m.property
  · rw [← hBi]
    exact him
  · rw [← hBj]
    exact hjm

#print axioms star_matched_diagonal_midpoint
