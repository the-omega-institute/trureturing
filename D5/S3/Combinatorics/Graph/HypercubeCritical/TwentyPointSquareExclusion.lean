/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSquareExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSquareExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Nonembedding of the paired squares with leaves in a balanced actual twenty-point slice. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf

/-! The derived high edges determine two positive cycles sharing a three-step path. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareExclusion

open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private sq crossNbr from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareLeaf
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private positive_eight_word from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_self diff_injective inter_card subset_of_inter_card
  adj_of_diff_subset_card adj_of_diff_pair_single common_middle_diff two_step_distance
  low_not_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

attribute [local instance] Classical.propDecidable

private def armTypes {n : ℕ} (o l x y m : Q n) (a b c d : Fin n) : Prop :=
  let D := fun z => diff z o
  (D l = {d} ∧ D x = {c,d} ∧ D y = {b,c,d} ∧ D m = {a,b,c,d}) ∨
  (D l = {d} ∧ D x = {b,d} ∧ D y = {b,c,d} ∧ D m = {b,c}) ∨
  (D l = {c} ∧ D x = {c,d} ∧ D y = {a,c,d} ∧ D m = {a,b,c,d})

private theorem arm_coordinates {n : ℕ} {S : Finset (Q n)} (hbal : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (hv : Function.Injective v)
    (w : Fin 8 → Fin n) (step : ∀ i, (v (i + 1)).val = flip (v i).val (w i)) :
    ∃ g : Fin 4 → Fin n, Function.Injective g ∧ w 0 = g 0 ∧ w 1 = g 1 ∧ w 2 = g 2 ∧
      armTypes (v 0).val (v 7).val (v 6).val (v 5).val (v 4).val (g 0) (g 1) (g 2) (g 3) := by
  obtain ⟨g, hg, ha, hb, hc, hwords⟩ := positive_eight_word hbal v hv w step
  refine ⟨g, hg, ha, hb, hc, ?_⟩
  have rev (i : Fin 8) : (v i).val = flip (v (i + 1)).val (w i) := by
    rw [step, BalancedCriticalSpectrum.flip_flip]
  have s₇ : (v 7).val = flip (v 0).val (w 7) := rev 7
  have s₆ : (v 6).val = flip (v 7).val (w 6) := rev 6
  have s₅ : (v 5).val = flip (v 6).val (w 5) := rev 5
  have s₄ : (v 4).val = flip (v 5).val (w 4) := rev 4
  have heq (i j : Fin 4) : g i = g j ↔ i = j := hg.eq_iff
  unfold armTypes
  rcases hwords with h | h | h <;>
    simp only [List.cons.injEq, and_true] at h <;>
    obtain ⟨h₇, h₆, h₅, h₄, _⟩ := h
  · left
    simp [s₇, s₆, s₅, s₄, h₇, h₆, h₅, h₄, diff_flip, diff_self, heq]
  · right; left
    simp [s₇, s₆, s₅, s₄, h₇, h₆, h₅, h₄, diff_flip, diff_self, heq,
      Finset.erase_insert_of_ne, Finset.insert_comm]
  · right; right
    simp [s₇, s₆, s₅, s₄, h₇, h₆, h₅, h₄, diff_flip, diff_self, heq]
    have hswap : ({g 3, g 2} : Finset (Fin n)) = {g 2, g 3} := Finset.pair_comm _ _
    rw [hswap, Finset.insert_comm (g 1) (g 0)]
    exact ⟨rfl, rfl, rfl⟩

private theorem disjoint_pair_centers {α : Type*} [DecidableEq α]
    {T : Finset α} {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (h₁ : 2 * (T ∩ {a,b}).card = T.card)
    (h₂ : 2 * (T ∩ {c,d}).card = T.card) :
    T = ∅ ∨ T = {a,b,c,d} ∨ T = {a,c} ∨ T = {a,d} ∨ T = {b,c} ∨ T = {b,d} := by
  let P : Finset α := {a,b}
  let R : Finset α := {c,d}
  have hd : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [P, R, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with he | he <;> contradiction
  have hP : P.card = 2 := by simp [P, hab]
  have hR : R.card = 2 := by simp [R, hcd]
  have hT : T = (T ∩ P) ∪ (T ∩ R) := by
    symm
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left]
    apply subset_of_inter_card
    rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
      (hd.mono Finset.inter_subset_right Finset.inter_subset_right)]
    change 2 * (T ∩ P).card = T.card at h₁
    change 2 * (T ∩ R).card = T.card at h₂
    omega
  have hbound := Finset.card_le_card ((show T ∩ P ⊆ P from Finset.inter_subset_right))
  change 2 * (T ∩ P).card = T.card at h₁
  change 2 * (T ∩ R).card = T.card at h₂
  have hcT : T.card = 0 ∨ T.card = 4 ∨ T.card = 2 := by omega
  rcases hcT with hzero | hfull | htwo
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · right; left
    have hp : T ∩ P = P := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hr : T ∩ R = R := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    nth_rw 1 [hT]
    rw [hp, hr]
    ext j
    simp only [P, R, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show (T ∩ P).card = 1 by omega)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show (T ∩ R).card = 1 by omega)
    have hi' : i = a ∨ i = b := by
      have hm : i ∈ T ∩ P := by rw [hi]; simp
      simpa [P] using (Finset.mem_inter.mp hm).2
    have hj' : j = c ∨ j = d := by
      have hm : j ∈ T ∩ R := by rw [hj]; simp
      simpa [R] using (Finset.mem_inter.mp hm).2
    have hpair : T = {i,j} := by nth_rw 1 [hT]; rw [hi,hj]; rfl
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hpair))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hpair)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpair))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpair))))

private theorem actual_centers {n : ℕ} {o x y z : Q n} {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d)
    (hx : diff x o = {a,b}) (hy : diff y o = {c,d})
    (hzx : hammingDist z x = 2) (hzy : hammingDist z y = 2) :
    diff z o = ∅ ∨ diff z o = {a,b,c,d} ∨ diff z o = {a,c} ∨
      diff z o = {a,d} ∨ diff z o = {b,c} ∨ diff z o = {b,d} := by
  have h₁ := inter_card (o := o) (x := z) (a := (diff z o).card) rfl
    (show (diff x o).card = 2 by simp [hx, hab]) hzx
  have h₂ := inter_card (o := o) (x := z) (a := (diff z o).card) rfl
    (show (diff y o).card = 2 by simp [hy, hcd]) hzy
  rw [hx] at h₁
  rw [hy] at h₂
  exact disjoint_pair_centers hab hcd hac had hbc hbd (by omega) (by omega)

private theorem no_type_one {n : ℕ} {o x y z B m : Q n} {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : diff x o = {a,b}) (hy : diff y o = {c,d})
    (hB : diff B o = {a}) (hm : diff m o = {a,b,c,d})
    (hzx : hammingDist z x = 2) (hzy : hammingDist z y = 2)
    (hzo : z ≠ o) (hzm : z ≠ m)
    (hzB : ¬ (hypercube n).Adj z B)
    {Y : Q n} (hY : diff Y o = {b,c,d}) (hzY : ¬ (hypercube n).Adj z Y) : False := by
  have htwo (e : Fin n) (he : b ≠ e) (he' : e = c ∨ e = d) (hz : diff z o = {b,e}) :
      (hypercube n).Adj z Y := by
    apply adj_of_diff_subset_card (o := o)
    · rw [hz, hY]
      rcases he' with rfl | rfl <;> simp
    · simp [hz, hY, he, hbc, hbd, hcd]
  rcases actual_centers hab hcd hac had hbc hbd hx hy hzx hzy with hz | hz | hz | hz | hz | hz
  · exact hzo (diff_injective o (hz.trans (diff_self o).symm))
  · exact hzm (diff_injective o (hz.trans hm.symm))
  · exact hzB (adj_of_diff_pair_single hac hz hB)
  · exact hzB (adj_of_diff_pair_single had hz hB)
  · exact hzY (htwo c hbc (Or.inl rfl) hz)
  · exact hzY (htwo d hbd (Or.inr rfl) hz)

private theorem mixed_arm_center {n : ℕ} {o x y z B m M : Q n} {a b c e : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e)
    (hx : diff x o = {a,b}) (hy : diff y o = {c,e})
    (hB : diff B o = {a}) (hm : diff m o = {b,c}) (hM : diff M o = {a,b,c,e})
    (hzx : hammingDist z x = 2) (hzy : hammingDist z y = 2)
    (hzo : z ≠ o) (hzm : z ≠ m) (hzM : z ≠ M) (hzB : ¬ (hypercube n).Adj z B) :
    diff z o = {b,e} := by
  rcases actual_centers hab hce hac hae hbc hbe hx hy hzx hzy with hz | hz | hz | hz | hz | hz
  · exact (hzo (diff_injective o (hz.trans (diff_self o).symm))).elim
  · exact (hzM (diff_injective o (hz.trans hM.symm))).elim
  · exact (hzB (adj_of_diff_pair_single hac hz hB)).elim
  · exact (hzB (adj_of_diff_pair_single hae hz hB)).elim
  · exact (hzm (diff_injective o (hz.trans hm.symm))).elim
  · exact hz

private theorem flip_direction_unique {n : ℕ} {x : Q n} {a b : Fin n}
    (he : flip x a = flip x b) : a = b := by
  have h := congrArg (fun y => diff y x) he
  simpa [diff_flip, diff_self] using h

private theorem paired_square_nonembedding {n : ℕ} {S : Finset (Q n)}
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hbal : IsBalanced S)
    (eL : sq ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (eR : sq ≃g compressed ((hypercube n).induce (S : Set (Q n))) R)
    (hcross : ∀ i j, ((hypercube n).induce (S : Set (Q n))).Adj (eL i).val (eR j).val ↔
      j ∈ crossNbr i) : False := by
  let V := (S : Set (Q n))
  let G := (hypercube n).induce V
  let A : Fin 5 → V := fun i => (eL i).val
  let B : Fin 5 → V := fun i => (eR i).val
  let index : Bool → Fin 5 := fun i => if i then 3 else 1
  let D : V → Finset (Fin n) := fun x => diff x.val (A 2).val
  have cubeAdj {x y : V} : G.Adj x y ↔ (hypercube n).Adj x.val y.val := Iff.rfl
  have Ainj : Function.Injective A := fun _ _ h => eL.injective (Subtype.ext h)
  have Binj : Function.Injective B := fun _ _ h => eR.injective (Subtype.ext h)
  have AL (i : Fin 5) : A i ∈ L := (Finset.mem_filter.mp (eL i).property).1
  have BR (i : Fin 5) : B i ∈ R := (Finset.mem_filter.mp (eR i).property).1
  have AD (i : Fin 5) : G.degree (A i) = 3 := (Finset.mem_filter.mp (eL i).property).2
  have BD (i : Fin 5) : G.degree (B i) = 3 := (Finset.mem_filter.mp (eR i).property).2
  have LneR {x y : V} (hx : x ∈ L) (hy : y ∈ R) : x ≠ y :=
    fun he => Set.disjoint_left.mp hpart.disjoint hx (he ▸ hy)
  have right_of_left {x y : V} (hx : x ∈ L) (he : G.Adj x y) : y ∈ R :=
    (hpart.mem_of_adj he).elim And.right (fun h => (LneR hx h.1 rfl).elim)
  have left_of_right {x y : V} (hx : x ∈ R) (he : G.Adj x y) : y ∈ L :=
    (hpart.mem_of_adj he).elim (fun h => (LneR h.1 hx rfl).elim) And.right
  have middleA {i j : Fin 5} (h : sq.Adj i j) :
      ∃ m : V, G.degree m = 2 ∧ G.Adj (A i) m ∧ G.Adj (A j) m := by
    obtain ⟨_, m, hm, h₁, h₂⟩ := eL.map_rel_iff.mpr h
    exact ⟨m, hm, h₁, h₂⟩
  have middleB {i j : Fin 5} (h : sq.Adj i j) :
      ∃ m : V, G.degree m = 2 ∧ G.Adj (B i) m ∧ G.Adj (B j) m := by
    obtain ⟨_, m, hm, h₁, h₂⟩ := eR.map_rel_iff.mpr h
    exact ⟨m, hm, h₁, h₂⟩
  have hidx2 (i : Bool) : index i ≠ 2 := by cases i <;> decide
  have hidx0 (i : Bool) : index i ≠ 0 := by cases i <;> decide
  have idx_inj : Function.Injective index := by
    intro i j he
    cases i <;> cases j <;> first | rfl | exact False.elim (by revert he; decide)
  have hsqA (i : Bool) : sq.Adj 2 (index i) := by cases i <;> decide +kernel
  have hsq0 (i : Bool) : sq.Adj 0 (index i) := by cases i <;> decide +kernel
  choose ell ellD ell2 elli using fun i => middleA (hsqA i)
  choose m mD m2 mi using fun i => middleB (hsqA i)
  have ellR (i : Bool) : ell i ∈ R := right_of_left (AL 2) (ell2 i)
  have mL (i : Bool) : m i ∈ L := left_of_right (BR 2) (m2 i)
  have low_ne_high {x y : V} (hx : G.degree x = 2) (hy : G.degree y = 3) : x ≠ y := by
    intro he
    rw [he, hy] at hx
    omega
  have ellinj : Function.Injective ell := by
    intro i j he
    by_contra hn
    exact low_not_three (ellD i) (Ainj.ne (hidx2 i).symm) (Ainj.ne (hidx2 j).symm)
      (Ainj.ne (idx_inj.ne hn)) (ell2 i).symm (elli i).symm (he ▸ (elli j).symm)
  have minj : Function.Injective m := by
    intro i j he
    by_contra hn
    exact low_not_three (mD i) (Binj.ne (hidx2 i).symm) (Binj.ne (hidx2 j).symm)
      (Binj.ne (idx_inj.ne hn)) (m2 i).symm (mi i).symm (he ▸ (mi j).symm)
  have high₂₄ : G.Adj (A 2) (B 4) := (hcross 2 4).mpr (by decide +kernel)
  have high₄₄ : G.Adj (A 4) (B 4) := (hcross 4 4).mpr (by decide +kernel)
  have high₄₂ : G.Adj (A 4) (B 2) := (hcross 4 2).mpr (by decide +kernel)
  have highii (i : Bool) : G.Adj (A (index i)) (B (index i)) := by
    apply (hcross _ _).mpr
    cases i <;> decide +kernel
  obtain ⟨a, ha⟩ := adjacent_exists_flip (cubeAdj.mp high₂₄)
  obtain ⟨b, hb⟩ := adjacent_exists_flip (cubeAdj.mp high₄₄.symm)
  obtain ⟨c, hc⟩ := adjacent_exists_flip (cubeAdj.mp high₄₂)
  have types (i : Bool) : ∃ d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      armTypes (A 2).val (ell i).val (A (index i)).val (B (index i)).val (m i).val a b c d := by
    let v : Fin 8 → V := ![A 2, B 4, A 4, B 2, m i, B (index i), A (index i), ell i]
    have hv : Function.Injective v := by
      apply List.nodup_ofFn.mp
      change [A 2, B 4, A 4, B 2, m i, B (index i), A (index i), ell i].Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true]
      repeat' apply And.intro
      all_goals first
        | exact not_false
        | exact LneR (AL _) (BR _)
        | exact LneR (AL _) (ellR i)
        | exact LneR (mL i) (BR _)
        | exact LneR (mL i) (ellR i)
        | exact (LneR (AL _) (BR _)).symm
        | exact (LneR (mL i) (BR _)).symm
        | exact low_ne_high (mD i) (AD _)
        | exact (low_ne_high (mD i) (AD _)).symm
        | exact (low_ne_high (ellD i) (BD _)).symm
        | apply Ainj.ne <;> cases i <;> decide
        | apply Binj.ne <;> cases i <;> decide
    have hedge (k : Fin 8) : G.Adj (v k) (v (k + 1)) := by
      fin_cases k
      · exact high₂₄
      · exact high₄₄.symm
      · exact high₄₂
      · exact m2 i
      · exact (mi i).symm
      · exact (highii i).symm
      · exact elli i
      · exact (ell2 i).symm
    choose w hw using fun k => adjacent_exists_flip (cubeAdj.mp (hedge k))
    obtain ⟨g, hg, h₀, h₁, h₂, ht⟩ := arm_coordinates hbal v hv w hw
    have hga : g 0 = a := by
      rw [← h₀]
      exact flip_direction_unique ((hw 0).symm.trans ha)
    have hgb : g 1 = b := by
      rw [← h₁]
      exact flip_direction_unique ((hw 1).symm.trans hb)
    have hgc : g 2 = c := by
      rw [← h₂]
      exact flip_direction_unique ((hw 2).symm.trans hc)
    have ne (i j : Fin 4) (h : i ≠ j) := hg.ne h
    refine ⟨g 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hga, ← hgb]; exact ne 0 1 (by decide)
    · rw [← hga, ← hgc]; exact ne 0 2 (by decide)
    · rw [← hga]; exact ne 0 3 (by decide)
    · rw [← hgb, ← hgc]; exact ne 1 2 (by decide)
    · rw [← hgb]; exact ne 1 3 (by decide)
    · rw [← hgc]; exact ne 2 3 (by decide)
    · change armTypes (A 2).val (ell i).val (A (index i)).val (B (index i)).val
        (m i).val (g 0) (g 1) (g 2) (g 3) at ht
      simpa only [hga, hgb, hgc] using ht
  have hAB (i : Bool) : ¬ (hypercube n).Adj (A 0).val (B (index i)).val :=
    fun h => by
      have hh := (hcross _ _).mp (cubeAdj.mpr h)
      change index i ∈ (∅ : Finset (Fin 5)) at hh
      exact Finset.notMem_empty _ hh
  have hAB₄ : ¬ (hypercube n).Adj (A 0).val (B 4).val :=
    fun h => (by decide +kernel : ¬ (4 : Fin 5) ∈ crossNbr 0) ((hcross _ _).mp (cubeAdj.mpr h))
  have hzo : (A 0).val ≠ (A 2).val := fun he => Ainj.ne (by decide) (Subtype.ext he)
  have hzlow (i : Bool) : (A 0).val ≠ (m i).val :=
    fun he => low_ne_high (mD i) (AD 0) (Subtype.ext he.symm)
  have hdist₄ : hammingDist (A 0).val (A 4).val = 2 := by
    obtain ⟨u, _, h₀, h₄⟩ := middleA (show sq.Adj 0 4 by decide +kernel)
    exact two_step_distance h₀ h₄.symm (fun he => Ainj.ne (by decide : (0 : Fin 5) ≠ 4) (Subtype.ext he))
  have hdisti (i : Bool) : hammingDist (A 0).val (A (index i)).val = 2 := by
    obtain ⟨u, _, h₀, hi⟩ := middleA (hsq0 i)
    exact two_step_distance h₀ hi.symm (fun he => Ainj.ne (hidx0 i).symm (Subtype.ext he))
  have B₄ : D (B 4) = {a} := by
    change diff (B 4).val (A 2).val = _
    rw [ha, diff_flip, diff_self]
    simp
  have A₄ (hab : a ≠ b) : D (A 4) = {a,b} := by
    change diff (A 4).val (A 2).val = _
    rw [hb, ha, diff_flip, diff_flip, diff_self]
    simpa [hab.symm] using (Finset.pair_comm b a)
  have remaining (i : Bool) : ∃ d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ((D (B (index i)) = {b,c,d} ∧ D (m i) = {b,c}) ∨
       (D (ell i) = {c} ∧ D (A (index i)) = {c,d} ∧ D (m i) = {a,b,c,d})) := by
    obtain ⟨d, hab, hac, had, hbc, hbd, hcd, ht⟩ := types i
    refine ⟨d, hab, hac, had, hbc, hbd, hcd, ?_⟩
    rcases ht with ⟨_, hx, hy, hm⟩ | ⟨_, _, hy, hm⟩ | ⟨hl, hx, _, hm⟩
    · exact (no_type_one hab hac had hbc hbd hcd (A₄ hab) hx B₄ hm hdist₄ (hdisti i)
        hzo (hzlow i) hAB₄ hy (hAB i)).elim
    · exact Or.inl ⟨hy, hm⟩
    · exact Or.inr ⟨hl, hx, hm⟩
  have mixed (i j : Bool) (hij : i ≠ j) {d e : Fin n}
      (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
      (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
      (hBi : D (B (index i)) = {b,c,d}) (hmi : D (m i) = {b,c})
      (hAj : D (A (index j)) = {c,e}) (hmj : D (m j) = {a,b,c,e}) : False := by
    by_cases he : d = e
    · have hx : G.Adj (A (index j)) (B (index i)) := cubeAdj.mpr (by
        apply adj_of_diff_subset_card (o := (A 2).val)
        · change D (A (index j)) ⊆ D (B (index i))
          rw [hAj, hBi, he]
          simp
        · change (D (B (index i))).card = (D (A (index j))).card + 1
          simp [hAj, hBi, he, hbc, hbe, hce])
      have hnot : ¬ index i ∈ crossNbr (index j) := by
        cases i <;> cases j <;> first | contradiction | decide +kernel
      exact hnot ((hcross _ _).mp hx)
    have A₀ : D (A 0) = {b,e} :=
      mixed_arm_center hab hac hae hbc hbe hce (A₄ hab) hAj B₄ hmi hmj hdist₄ (hdisti j)
        hzo (hzlow i) (hzlow j) hAB₄
    obtain ⟨u, hu, h₀, hj⟩ := middleA (hsq0 j)
    have hmid := common_middle_diff
      (show (D (A 0)).card = 2 by simp [A₀, hbe])
      (show (D (A (index j))).card = 2 by simp [hAj, hce])
      (hdisti j) (cubeAdj.mp h₀) (cubeAdj.mp hj)
    change D u = D (A 0) ∩ D (A (index j)) ∨ D u = D (A 0) ∪ D (A (index j)) at hmid
    rw [A₀, hAj] at hmid
    have hinter : ({b,e} ∩ {c,e} : Finset (Fin n)) = {e} := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hk | hk, hj | hj⟩
        · exact (hbc (hk.symm.trans hj)).elim
        · exact hj
        · exact hk
        · exact hk
      · intro hk
        exact ⟨Or.inr hk, Or.inr hk⟩
    have hunion : ({b,e} ∪ {c,e} : Finset (Fin n)) = {b,c,e} := by
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hinter, hunion] at hmid
    rcases hmid with hu' | hu'
    · have heq : u.val = flip (A 2).val e := by
        apply diff_injective (A 2).val
        change D u = diff (flip (A 2).val e) (A 2).val
        rw [hu', diff_flip, diff_self]
        simp
      have hnew : G.Adj u (A 2) := cubeAdj.mpr (by
        rw [heq]
        exact (BalancedCriticalSpectrum.flip_adj _ _).symm)
      exact low_not_three hu (Ainj.ne (hidx0 j).symm) (Ainj.ne (by decide : (0 : Fin 5) ≠ 2))
        (Ainj.ne (hidx2 j)) h₀.symm hj.symm hnew
    · have hnew : G.Adj (m i) u := cubeAdj.mpr (by
        apply adj_of_diff_subset_card (o := (A 2).val)
        · change D (m i) ⊆ D u
          rw [hmi, hu']
          simp
        · change (D u).card = (D (m i)).card + 1
          simp [hmi, hu', hbc, hbe, hce])
      exact hlow hnew (mD i) hu
  obtain ⟨d, hab, hac, had, hbc, hbd, hcd, hf⟩ := remaining false
  obtain ⟨e, _, _, hae, _, hbe, hce, ht⟩ := remaining true
  rcases hf with ⟨hfB, hfm⟩ | ⟨hfl, hfA, hfm⟩
  · rcases ht with ⟨_, htm⟩ | ⟨_, htA, htm⟩
    · exact Bool.false_ne_true (minj (Subtype.ext (diff_injective (A 2).val (hfm.trans htm.symm))))
    · exact mixed false true Bool.false_ne_true hab hac hae hbc hbe hce hfB hfm htA htm
  · rcases ht with ⟨htB, htm⟩ | ⟨htl, _, _⟩
    · exact mixed true false Bool.false_ne_true.symm hab hac had hbc hbd hcd htB htm hfA hfm
    · exact Bool.false_ne_true (ellinj (Subtype.ext (diff_injective (A 2).val (hfl.trans htl.symm))))

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSquareExclusion
