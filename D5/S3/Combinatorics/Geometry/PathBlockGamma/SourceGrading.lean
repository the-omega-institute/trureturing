/- GID: D5/S3/Combinatorics/Geometry/PathBlockGamma/SourceGrading
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/PathBlockGamma/SourceGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Grade]
   utility: none
   digest: The literal path-block order has an explicit cover-preserving grade. -/

import D5.S3.Combinatorics.Geometry.PathBlockGamma.LiteralPoset
import D5.S3.Combinatorics.Posets.GradedGamma.SaturatedRuns
import Mathlib.Order.Grade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.PathBlockGamma

open D5.S3.Combinatorics.Posets.PPartitions
open D5.S3.Combinatorics.Posets.GradedGamma

/-- The rank along a full adjacent pair, with odd blocks below even blocks. -/
def sourceGrade {a m : ℕ} (x : Vertex a m) : ℕ :=
  if oddBlock x.block then x.level.val else a + x.level.val

instance {a m : ℕ} : GradeOrder ℕ (Vertex a m) where
  grade := sourceGrade
  grade_strictMono := by
    intro x y hxy
    have hne : x ≠ y := ne_of_lt hxy
    rcases hxy.le with ⟨hsame, hlevel⟩ | ⟨hodd, heven, _⟩
    · have hlt : x.level.val < y.level.val := by
        have hn : x.level ≠ y.level := by
          intro h
          exact hne (Vertex.ext hsame h)
        exact lt_of_le_of_ne hlevel (fun h => hn (Fin.ext h))
      simp only [sourceGrade]
      rw [hsame]
      split_ifs <;> omega
    · simp only [sourceGrade, if_pos hodd, if_neg heven]
      exact x.level.isLt.trans_le (Nat.le_add_right a y.level.val)
  covBy_grade := by
    intro x y hxy
    have hlt : x < y := hxy.lt
    have hno : ∀ z : Vertex a m, ¬ (x < z ∧ z < y) := by
      intro z hz
      exact ((not_covBy_iff hlt).2 ⟨z, hz⟩) hxy
    have hgrade : sourceGrade y = sourceGrade x + 1 := by
      rcases hlt.le with ⟨hsame, hlevel⟩ | ⟨hodd, heven, hadj⟩
      · have hlevel_lt : x.level.val < y.level.val := by
          have hn : x.level ≠ y.level := by
            intro h
            exact hlt.ne (Vertex.ext hsame h)
          exact lt_of_le_of_ne hlevel (fun h => hn (Fin.ext h))
        have hunit : y.level.val = x.level.val + 1 := by
          by_contra hgap
          have hgap' : x.level.val + 1 < y.level.val := by omega
          let z : Vertex a m := ⟨x.block, ⟨x.level.val + 1, by omega⟩⟩
          have hxz : x < z := lt_of_le_of_ne (Or.inl ⟨rfl, by
            change x.level.val ≤ x.level.val + 1
            omega⟩) (by
            intro heq
            have := congrArg (fun v : Vertex a m => v.level.val) heq
            dsimp [z] at this
            omega)
          have hzy : z < y := lt_of_le_of_ne (Or.inl ⟨hsame, by
            change x.level.val + 1 ≤ y.level.val
            omega⟩) (by
            intro heq
            have := congrArg (fun v : Vertex a m => v.level.val) heq
            dsimp [z] at this
            omega)
          exact hno z ⟨hxz, hzy⟩
        simp only [sourceGrade]
        rw [hsame]
        split_ifs <;> omega
      · have hxlast : x.level.val + 1 = a := by
          by_contra hgap
          have hgap' : x.level.val + 1 < a := by omega
          let z : Vertex a m := ⟨x.block, ⟨x.level.val + 1, hgap'⟩⟩
          have hxz : x < z := lt_of_le_of_ne (Or.inl ⟨rfl, by
            change x.level.val ≤ x.level.val + 1
            omega⟩) (by
            intro heq
            have := congrArg (fun v : Vertex a m => v.level.val) heq
            dsimp [z] at this
            omega)
          have hzy : z < y := lt_of_le_of_ne (Or.inr ⟨hodd, heven, hadj⟩)
            (by
              intro heq
              have := congrArg (fun v : Vertex a m => v.block) heq
              rw [this] at hodd
              exact heven hodd)
          exact hno z ⟨hxz, hzy⟩
        have hyfirst : y.level.val = 0 := by
          by_contra hgap
          have hypos : 0 < y.level.val := by omega
          let z : Vertex a m := ⟨y.block, ⟨0, by omega⟩⟩
          have hxz : x < z := lt_of_le_of_ne (Or.inr ⟨hodd, heven, hadj⟩)
            (by
              intro heq
              have := congrArg (fun v : Vertex a m => v.block) heq
              rw [this] at hodd
              exact heven hodd)
          have hzy : z < y := lt_of_le_of_ne (Or.inl ⟨rfl, by
            change (0 : ℕ) ≤ y.level.val
            omega⟩) (by
            intro heq
            have := congrArg (fun v : Vertex a m => v.level.val) heq
            dsimp [z] at this
            omega)
          exact hno z ⟨hxz, hzy⟩
        simp only [sourceGrade, if_pos hodd, if_neg heven]
        omega
    change sourceGrade x ⋖ sourceGrade y
    exact (Nat.covBy_iff_add_one_eq).2 hgrade.symm

/-- The grade is zero at every minimal vertex and `2*a-1` at every maximal vertex. -/
theorem source_grade_extrema (a m : ℕ) (ha : 0 < a) (hm : 1 < m) :
    (∀ x : Vertex a m, IsMin x → sourceGrade x = 0) ∧
      (∀ x : Vertex a m, IsMax x → sourceGrade x = 2 * a - 1) := by
  constructor
  · intro x hmin
    have hlevel : x.level.val = 0 := by
      by_contra h
      have hp : 0 < x.level.val := by omega
      let y : Vertex a m := ⟨x.block, ⟨0, ha⟩⟩
      have hyx : y < x := lt_of_le_of_ne (Or.inl ⟨rfl, by
        change (0 : ℕ) ≤ x.level.val
        omega⟩) (by
        intro heq
        have := congrArg (fun v : Vertex a m => v.level.val) heq
        dsimp [y] at this
        omega)
      exact hmin.not_lt hyx
    by_cases hodd : oddBlock x.block
    · simp [sourceGrade, hodd, hlevel]
    · have hmod : x.block.val % 2 = 1 := by
        have hlt := Nat.mod_lt x.block.val (by omega : 0 < 2)
        simp only [oddBlock] at hodd
        omega
      let b : Fin m := ⟨x.block.val - 1, by omega⟩
      have hbodd : oddBlock b := by
        dsimp [oddBlock, b]
        omega
      have hadj : adjacentBlocks b x.block := by
        dsimp [adjacentBlocks, b]
        omega
      let y : Vertex a m := ⟨b, ⟨0, ha⟩⟩
      have hyx : y < x := lt_of_le_of_ne (Or.inr ⟨hbodd, hodd, hadj⟩) (by
        intro heq
        have := congrArg (fun v : Vertex a m => v.block) heq
        change b = x.block at this
        rw [this] at hbodd
        exact hodd hbodd)
      exact False.elim (hmin.not_lt hyx)
  · intro x hmax
    have hlevel : x.level.val + 1 = a := by
      by_contra h
      have hp : x.level.val + 1 < a := by omega
      let y : Vertex a m := ⟨x.block, ⟨x.level.val + 1, hp⟩⟩
      have hxy : x < y := lt_of_le_of_ne (Or.inl ⟨rfl, by
        change x.level.val ≤ x.level.val + 1
        omega⟩) (by
        intro heq
        have := congrArg (fun v : Vertex a m => v.level.val) heq
        dsimp [y] at this
        omega)
      exact hmax.not_lt hxy
    by_cases hodd : oddBlock x.block
    · have hneighbor : ∃ b : Fin m, ¬ oddBlock b ∧ adjacentBlocks x.block b := by
        by_cases hnext : x.block.val + 1 < m
        · refine ⟨⟨x.block.val + 1, hnext⟩, ?_, ?_⟩
          · change (x.block.val + 1) % 2 ≠ 0
            dsimp [oddBlock] at hodd
            omega
          · change x.block.val + 1 = x.block.val + 1 ∨
              x.block.val + 1 + 1 = x.block.val
            exact Or.inl rfl
        · have hprev : x.block.val - 1 < m := by omega
          refine ⟨⟨x.block.val - 1, hprev⟩, ?_, ?_⟩
          · change (x.block.val - 1) % 2 ≠ 0
            dsimp [oddBlock] at hodd
            omega
          · change x.block.val + 1 = x.block.val - 1 ∨
              x.block.val - 1 + 1 = x.block.val
            right
            omega
      obtain ⟨b, hbnot, hadj⟩ := hneighbor
      let y : Vertex a m := ⟨b, ⟨0, ha⟩⟩
      have hxy : x < y := lt_of_le_of_ne (Or.inr ⟨hodd, hbnot, hadj⟩) (by
        intro heq
        have := congrArg (fun v : Vertex a m => v.block) heq
        change x.block = b at this
        rw [← this] at hbnot
        exact hbnot hodd)
      exact False.elim (hmax.not_lt hxy)
    · simp only [sourceGrade, if_neg hodd]
      omega

/-- A full adjacent-pair chain meets at least `2*a` distinct parity runs in
every linear extension of the literal source order. -/
theorem source_runIndex_lower (a m : ℕ) (ha : 0 < a) (hm : 1 < m)
    (e : EnumeratingExtension (Vertex a m)) :
    2 * a - 1 ≤
      runIndex e ⟨Fintype.card (Vertex a m) - 1, by
        rw [(literal_poset_card_label_order a m ha).1]
        have hp : 0 < a * m := Nat.mul_pos ha (by omega)
        omega⟩ := by
  classical
  let i : Fin (m - 1) := ⟨0, by omega⟩
  let s : Finset (Vertex a m) := (adjacentPair i).toFinset
  have hchain : IsMaxChain (· ≤ ·) (adjacentPair (a := a) i) :=
    ((literal_poset_maximal_chains a m ha hm).1 (adjacentPair i)).2 ⟨i, rfl⟩
  have hs_card : s.card = 2 * a := by
    have hc := ((literal_poset_maximal_chains a m ha hm).2
      (adjacentPair i) hchain).1
    change (adjacentPair i).toFinset.card = 2 * a
    rw [← Set.ncard_eq_toFinset_card' (adjacentPair i)]
    exact hc
  let last : Fin (Fintype.card (Vertex a m)) :=
    ⟨Fintype.card (Vertex a m) - 1, by
      rw [(literal_poset_card_label_order a m ha).1]
      have hp : 0 < a * m := Nat.mul_pos ha (by omega)
      omega⟩
  let f : Vertex a m → ℕ := fun x => runIndex e (e.1.symm x)
  have hmono : Monotone (runIndex e) := by
    intro j k hjk
    unfold runIndex
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨lt_of_lt_of_le ht.1 hjk, ht.2⟩
  have hinj : Set.InjOn f (s : Set (Vertex a m)) := by
    intro x hx y hy hxy
    by_contra hne
    have hxs : x ∈ adjacentPair (a := a) i := by simpa [s] using hx
    have hys : y ∈ adjacentPair (a := a) i := by simpa [s] using hy
    rcases hchain.1 hxs hys hne with hle | hle
    · have hlt : x < y := lt_of_le_of_ne hle hne
      have hr := runLE_extends e hlt
      rcases hr with heq | hstrict
      · exact hne heq
      · exact (Nat.ne_of_lt hstrict) hxy
    · have hlt : y < x := lt_of_le_of_ne hle (Ne.symm hne)
      have hr := runLE_extends e hlt
      rcases hr with heq | hstrict
      · exact hne heq.symm
      · exact (Nat.ne_of_gt hstrict) hxy
  have himage : (s.image f).card = 2 * a := by
    rw [Finset.card_image_iff.mpr hinj, hs_card]
  have hsubset : s.image f ⊆ Finset.range (runIndex e last + 1) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range]
    have hpos : e.1.symm x ≤ last := by
      apply Fin.le_iff_val_le_val.mpr
      have hx := (e.1.symm x).isLt
      have hc := (literal_poset_card_label_order a m ha).1
      dsimp [last]
      omega
    exact Nat.lt_succ_of_le (hmono hpos)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_range, himage] at hcard
  change 2 * a - 1 ≤ runIndex e last
  omega

/-- Every source extension starts at even grade and ends at odd grade, so its
alternating run word has an even number of occupied fibers. -/
theorem source_runIndex_last_odd (a m : ℕ) (ha : 0 < a) (hm : 1 < m)
    (e : EnumeratingExtension (Vertex a m)) :
    runIndex e ⟨Fintype.card (Vertex a m) - 1, by
      rw [(literal_poset_card_label_order a m ha).1]
      have hp : 0 < a * m := Nat.mul_pos ha (by omega)
      omega⟩ % 2 = 1 := by
  have hn : 0 < Fintype.card (Vertex a m) := by
    rw [(literal_poset_card_label_order a m ha).1]
    exact Nat.mul_pos ha (by omega)
  let first : Fin (Fintype.card (Vertex a m)) := ⟨0, hn⟩
  let last : Fin (Fintype.card (Vertex a m)) := ⟨Fintype.card (Vertex a m) - 1, by omega⟩
  have hfirst : IsMin (e first) := by
    intro x hx
    by_contra hnle
    have hne : x ≠ e first := by
      intro heq
      subst x
      exact hnle le_rfl
    have hpos := e.2 (lt_of_le_of_ne hx hne)
    have hzero : e.1.symm (e first) = first := e.1.symm_apply_apply first
    rw [hzero] at hpos
    have hval : (e.1.symm x).val < 0 := hpos
    omega
  have hlast : IsMax (e last) := by
    intro x hx
    by_contra hnle
    have hne : e last ≠ x := by
      intro heq
      subst x
      exact hnle le_rfl
    have hpos := e.2 (lt_of_le_of_ne hx hne)
    have hlast' : e.1.symm (e last) = last := e.1.symm_apply_apply last
    rw [hlast'] at hpos
    have hp := (e.1.symm x).isLt
    have hval : last.val < (e.1.symm x).val := hpos
    dsimp [last] at hval
    omega
  have hpar := runIndex_parity e (fun _ => by
    change sourceGrade (e first) % 2 = 0
    rw [(source_grade_extrema a m ha hm).1 (e first) hfirst]) last
  change runIndex e last % 2 = sourceGrade (e last) % 2 at hpar
  rw [(source_grade_extrema a m ha hm).2 (e last) hlast] at hpar
  dsimp [last] at hpar ⊢
  omega

end D5.S3.Combinatorics.Geometry.PathBlockGamma
