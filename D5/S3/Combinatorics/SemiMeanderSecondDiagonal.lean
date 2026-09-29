/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Source matching and midpoint-crossing structure for the connected semi-meander second diagonal. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

/-- Noncrossing upper arches as a fixed-point-free endpoint involution. -/
structure UpperMatching (n : ℕ) where
  mate : Fin (2 * n) → Fin (2 * n)
  mate_mate : ∀ x, mate (mate x) = x
  mate_ne : ∀ x, mate x ≠ x
  noncrossing : ∀ a b : Fin (2 * n), a.val < b.val →
    b.val < (mate a).val → (mate a).val < (mate b).val → False

/-- Number of upper arches crossing the midpoint. -/
def UpperMatching.winding {n : ℕ} (M : UpperMatching n) : ℕ :=
  (Finset.univ.filter fun x : Fin n =>
    n ≤ (M.mate ⟨x.val, by have := x.isLt; omega⟩).val).card

/-- Connectivity through upper arches and the fixed lower rainbow. -/
def UpperMatching.oneLoop {n : ℕ} (M : UpperMatching n) : Prop :=
  ∀ x y : Fin (2 * n),
    Relation.ReflTransGen (fun x y => M.mate x = y ∨ x.rev = y) x y

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
/-- Exact connected semi-meander second-diagonal count for every n >= 4. -/
theorem result (n : ℕ) (hn : 4 ≤ n) :
    Nat.card {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} =
      (n ^ 2 + 2 * n + n % 2 - 20) / 2 := by
  classical
  -- Cut at the midpoint, then contract the fixed lower rainbow.
  let reflected {n : ℕ} (M : UpperMatching n) : UpperMatching n :=
    {
      mate x := (M.mate x.rev).rev
      mate_mate x := by simp [M.mate_mate]
      mate_ne x := by
        intro h
        apply M.mate_ne x.rev
        have hv := congrArg Fin.rev h
        simpa using hv
      noncrossing a b hab hbetween hends := by
        have h₁ : (M.mate b.rev).val < (M.mate a.rev).val := by
          exact Fin.rev_lt_rev.mp hends
        have h₂ : (M.mate a.rev).val < b.rev.val := by
          exact Fin.lt_rev_iff.mp hbetween
        have h₃ : b.rev.val < a.rev.val := by
          exact Fin.rev_lt_rev.mpr hab
        apply M.noncrossing (M.mate b.rev) (M.mate a.rev) h₁
        · simpa [M.mate_mate] using h₂
        · simpa [M.mate_mate] using h₃
    }

  let leftPoint (n : ℕ) (x : Fin n) : Fin (2 * n) :=
    ⟨x.val, by have := x.isLt; omega⟩

  let rightPoint (n : ℕ) (x : Fin n) : Fin (2 * n) :=
    (leftPoint n x).rev

  let leftCut {n : ℕ} (M : UpperMatching n) (x : Fin n) :
      Option (Fin n) :=
    if h : (M.mate (leftPoint n x)).val < n then
      some ⟨(M.mate (leftPoint n x)).val, h⟩
    else none

  have leftCut_eq_some_iff {n : ℕ} (M : UpperMatching n)
      (x y : Fin n) :
      (leftCut M) x = some y ↔ M.mate (leftPoint n x) = leftPoint n y := by
    unfold leftCut
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · intro heq
        have hv : (M.mate (leftPoint n x)).val = y.val :=
          congrArg (fun z : Fin n => z.val) heq
        exact Fin.ext hv
      · intro heq
        have hv : (M.mate (leftPoint n x)).val = y.val :=
          congrArg (fun z : Fin (2 * n) => z.val) heq
        exact Fin.ext hv
    · constructor
      · intro heq
        cases heq
      · intro heq
        have hv : (M.mate (leftPoint n x)).val = y.val :=
          congrArg (fun z : Fin (2 * n) => z.val) heq
        have hy := y.isLt
        exact (h (by omega)).elim

  have leftCut_symmetric {n : ℕ} (M : UpperMatching n)
      (x y : Fin n) (h : (leftCut M) x = some y) :
      (leftCut M) y = some x := by
    apply (leftCut_eq_some_iff M y x).2
    have hxy := (leftCut_eq_some_iff M x y).1 h
    rw [← hxy, M.mate_mate]

  let rightCut {n : ℕ} (M : UpperMatching n) (x : Fin n) :
      Option (Fin n) :=
    if h : (M.mate (rightPoint n x)).rev.val < n then
      some ⟨(M.mate (rightPoint n x)).rev.val, h⟩
    else none

  have rightCut_eq_some_iff {n : ℕ} (M : UpperMatching n)
      (x y : Fin n) :
      (rightCut M) x = some y ↔ M.mate (rightPoint n x) = rightPoint n y := by
    unfold rightCut
    split_ifs with h
    · simp only [Option.some.injEq]
      constructor
      · intro heq
        have hv : (M.mate (rightPoint n x)).rev.val = y.val :=
          congrArg (fun z : Fin n => z.val) heq
        apply Fin.rev_injective
        apply Fin.ext
        simpa [rightPoint, leftPoint] using hv
      · intro heq
        have hv := congrArg Fin.rev heq
        have hv' : (M.mate (rightPoint n x)).rev.val = y.val := by
          simpa [rightPoint, leftPoint] using congrArg Fin.val hv
        exact Fin.ext hv'
    · constructor
      · intro heq
        cases heq
      · intro heq
        have hv := congrArg Fin.rev heq
        have hv' : (M.mate (rightPoint n x)).rev.val = y.val := by
          simpa [rightPoint, leftPoint] using congrArg Fin.val hv
        exact (h (by have := y.isLt; omega)).elim

  have rightCut_symmetric {n : ℕ} (M : UpperMatching n)
      (x y : Fin n) (h : (rightCut M) x = some y) :
      (rightCut M) y = some x := by
    apply (rightCut_eq_some_iff M y x).2
    have hxy := (rightCut_eq_some_iff M x y).1 h
    rw [← hxy, M.mate_mate]

  let crossingRight {n : ℕ} (M : UpperMatching n)
      (x : Fin n) (h : (leftCut M) x = none) : Fin n :=
    ⟨(M.mate (leftPoint n x)).rev.val, by
      have hc : n ≤ (M.mate (leftPoint n x)).val := by
        simpa [leftCut] using h
      have hb := (M.mate (leftPoint n x)).isLt
      have hr : (M.mate (leftPoint n x)).rev.val =
          2 * n - ((M.mate (leftPoint n x)).val + 1) := by simp
      omega⟩

  let crossingLeft {n : ℕ} (M : UpperMatching n)
      (x : Fin n) (h : (rightCut M) x = none) : Fin n :=
    ⟨(M.mate (rightPoint n x)).val, by
      have hc : n ≤ (M.mate (rightPoint n x)).rev.val := by
        simpa [rightCut] using h
      have hb := (M.mate (rightPoint n x)).isLt
      have hr : (M.mate (rightPoint n x)).rev.val =
          2 * n - ((M.mate (rightPoint n x)).val + 1) := by simp
      omega⟩

  have crossingRight_none {n : ℕ} (M : UpperMatching n)
      (x : Fin n) (h : (leftCut M) x = none) :
      (rightCut M) (crossingRight M x h) = none := by
    have hc : n ≤ (M.mate (rightPoint n (crossingRight M x h))).rev.val := by
      have hpoint : rightPoint n (crossingRight M x h) =
          M.mate (leftPoint n x) := by
        have hv : leftPoint n (crossingRight M x h) =
            (M.mate (leftPoint n x)).rev := by
          apply Fin.ext
          rfl
        simpa [rightPoint] using congrArg Fin.rev hv
      rw [hpoint, M.mate_mate]
      have hx := x.isLt
      have hr : (leftPoint n x).rev.val = 2 * n - (x.val + 1) := by simp [leftPoint]
      omega
    simpa [rightCut] using hc

  have crossingLeft_none {n : ℕ} (M : UpperMatching n)
      (x : Fin n) (h : (rightCut M) x = none) :
      (leftCut M) (crossingLeft M x h) = none := by
    have hc : n ≤ (M.mate (leftPoint n (crossingLeft M x h))).val := by
      have hpoint : leftPoint n (crossingLeft M x h) =
          M.mate (rightPoint n x) := by
        apply Fin.ext
        rfl
      rw [hpoint, M.mate_mate]
      have hx := x.isLt
      have hr : (rightPoint n x).val = 2 * n - (x.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    simpa [leftCut] using hc

  have winding_eq_rightCut_none_card {n : ℕ} (M : UpperMatching n) :
      M.winding = (Finset.univ.filter fun x : Fin n => (rightCut M) x = none).card := by
    have rightPoint_crossingRight (x : Fin n) (h : (leftCut M) x = none) :
        rightPoint n (crossingRight M x h) = M.mate (leftPoint n x) := by
      have hv : leftPoint n (crossingRight M x h) =
          (M.mate (leftPoint n x)).rev := by
        apply Fin.ext
        rfl
      simpa [rightPoint] using congrArg Fin.rev hv
    have leftPoint_crossingLeft (x : Fin n) (h : (rightCut M) x = none) :
        leftPoint n (crossingLeft M x h) = M.mate (rightPoint n x) := by
      apply Fin.ext
      rfl
    have hleft : M.winding =
        (Finset.univ.filter fun x : Fin n => (leftCut M) x = none).card := by
      simp [UpperMatching.winding, leftCut, leftPoint]
    rw [hleft]
    refine Finset.card_bij'
      (fun x hx => crossingRight M x (Finset.mem_filter.mp hx).2)
      (fun x hx => crossingLeft M x (Finset.mem_filter.mp hx).2) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        crossingRight_none M x (Finset.mem_filter.mp hx).2⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        crossingLeft_none M x (Finset.mem_filter.mp hx).2⟩
    · intro x hx
      apply Fin.ext
      have h := leftPoint_crossingLeft (crossingRight M x
        (Finset.mem_filter.mp hx).2) (crossingRight_none M x
        (Finset.mem_filter.mp hx).2)
      rw [rightPoint_crossingRight x (Finset.mem_filter.mp hx).2,
        M.mate_mate] at h
      simpa [leftPoint] using congrArg Fin.val h
    · intro x hx
      have h := rightPoint_crossingRight (crossingLeft M x
        (Finset.mem_filter.mp hx).2) (crossingLeft_none M x
        (Finset.mem_filter.mp hx).2)
      rw [leftPoint_crossingLeft x (Finset.mem_filter.mp hx).2,
        M.mate_mate] at h
      apply Fin.ext
      simpa [rightPoint, leftPoint] using congrArg Fin.val (congrArg Fin.rev h)

  have leftCut_paired_card_four {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4) :
      (Finset.univ.filter fun x : Fin n => (leftCut M) x ≠ none).card = 4 := by
    classical
    have hparts := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun x : Fin n => (leftCut M) x = none)
    have hleft : M.winding =
        (Finset.univ.filter fun x : Fin n => (leftCut M) x = none).card := by
      simp [UpperMatching.winding, leftCut, leftPoint]
    rw [← hleft] at hparts
    rw [hw] at hparts
    simp only [Finset.card_univ, Fintype.card_fin] at hparts
    change n - 4 +
      (Finset.univ.filter fun x : Fin n => (leftCut M) x ≠ none).card = n at hparts
    omega

  have rightCut_paired_card_four {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4) :
      (Finset.univ.filter fun x : Fin n => (rightCut M) x ≠ none).card = 4 := by
    classical
    have hparts := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun x : Fin n => (rightCut M) x = none)
    rw [← winding_eq_rightCut_none_card M] at hparts
    rw [hw] at hparts
    simp only [Finset.card_univ, Fintype.card_fin] at hparts
    change n - 4 +
      (Finset.univ.filter fun x : Fin n => (rightCut M) x ≠ none).card = n at hparts
    omega

  have leftCut_between_paired {n : ℕ} (M : UpperMatching n)
      (x y z : Fin n) (hxy : (leftCut M) x = some y)
      (hxz : x.val < z.val) (hzy : z.val < y.val) :
      (leftCut M) z ≠ none := by
    intro hz
    have harch := (leftCut_eq_some_iff M x y).1 hxy
    have hcross : n ≤ (M.mate (leftPoint n z)).val := by
      simpa [leftCut] using hz
    apply M.noncrossing (leftPoint n x) (leftPoint n z)
    · simpa [leftPoint] using hxz
    · rw [harch]
      simpa [leftPoint] using hzy
    · rw [harch]
      have hy := y.isLt
      simpa [leftPoint] using (show y.val < (M.mate (leftPoint n z)).val by omega)

  have rightCut_between_paired {n : ℕ} (M : UpperMatching n)
      (x y z : Fin n) (hxy : (rightCut M) x = some y)
      (hxz : x.val < z.val) (hzy : z.val < y.val) :
      (rightCut M) z ≠ none := by
    intro hz
    have harch := (rightCut_eq_some_iff M x y).1 hxy
    have harch' : M.mate (rightPoint n y) = rightPoint n x := by
      rw [← harch, M.mate_mate]
    have hcross : n ≤ (M.mate (rightPoint n z)).rev.val := by
      simpa [rightCut] using hz
    have hbound := (M.mate (rightPoint n z)).isLt
    have hrev : (M.mate (rightPoint n z)).rev.val =
        2 * n - ((M.mate (rightPoint n z)).val + 1) := by simp
    have hleft : (M.mate (rightPoint n z)).val < n := by omega
    have hrighty : n ≤ (rightPoint n y).val := by
      have hy := y.isLt
      have hr : (rightPoint n y).val = 2 * n - (y.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    have hyz : (rightPoint n y).val < (rightPoint n z).val := by
      have hry : (rightPoint n y).val = 2 * n - (y.val + 1) := by
        simp [rightPoint, leftPoint]
      have hrz : (rightPoint n z).val = 2 * n - (z.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    have hzx : (rightPoint n z).val < (rightPoint n x).val := by
      have hrz : (rightPoint n z).val = 2 * n - (z.val + 1) := by
        simp [rightPoint, leftPoint]
      have hrx : (rightPoint n x).val = 2 * n - (x.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    apply M.noncrossing (M.mate (rightPoint n z)) (rightPoint n y)
    · omega
    · rw [M.mate_mate]
      exact hyz
    · rw [M.mate_mate, harch']
      exact hzx

  have leftCut_arch_span_le_three {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4)
      (x y : Fin n) (hxy : (leftCut M) x = some y)
      (hord : x.val < y.val) : y.val ≤ x.val + 3 := by
    have hsubset : Finset.Icc x y ⊆
        Finset.univ.filter (fun z : Fin n => (leftCut M) z ≠ none) := by
      intro z hz
      have hxz := (Finset.mem_Icc.mp hz).1
      have hzy := (Finset.mem_Icc.mp hz).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases eq_or_lt_of_le hxz with rfl | hlt
      · simp [hxy]
      rcases eq_or_lt_of_le hzy with rfl | hlt'
      · simp [leftCut_symmetric M x z hxy]
      exact leftCut_between_paired M x y z hxy hlt hlt'
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Icc, leftCut_paired_card_four M hn hw] at hcard
    omega

  have rightCut_arch_span_le_three {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4)
      (x y : Fin n) (hxy : (rightCut M) x = some y)
      (hord : x.val < y.val) : y.val ≤ x.val + 3 := by
    have hsubset : Finset.Icc x y ⊆
        Finset.univ.filter (fun z : Fin n => (rightCut M) z ≠ none) := by
      intro z hz
      have hxz := (Finset.mem_Icc.mp hz).1
      have hzy := (Finset.mem_Icc.mp hz).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases eq_or_lt_of_le hxz with rfl | hlt
      · simp [hxy]
      rcases eq_or_lt_of_le hzy with rfl | hlt'
      · simp [rightCut_symmetric M x z hxy]
      exact rightCut_between_paired M x y z hxy hlt hlt'
    have hcard := Finset.card_le_card hsubset
    rw [Fin.card_Icc, rightCut_paired_card_four M hn hw] at hcard
    omega

  have leftCut_between_mate_inside {n : ℕ} (M : UpperMatching n)
      (x y z w : Fin n) (hxy : (leftCut M) x = some y)
      (hzw : (leftCut M) z = some w)
      (hxz : x.val < z.val) (hzy : z.val < y.val) :
      x.val < w.val ∧ w.val < y.val := by
    have harchX := (leftCut_eq_some_iff M x y).1 hxy
    have harchZ := (leftCut_eq_some_iff M z w).1 hzw
    have harchW := (leftCut_eq_some_iff M w z).1
      (leftCut_symmetric M z w hzw)
    have hwx : w.val ≠ x.val := by
      intro hv
      have heq : w = x := Fin.ext hv
      subst w
      have hs := leftCut_symmetric M z x hzw
      rw [hxy] at hs
      have hyz := Option.some.inj hs
      omega
    have hwy : w.val ≠ y.val := by
      intro hv
      have heq : w = y := Fin.ext hv
      subst w
      have hs := leftCut_symmetric M z y hzw
      rw [leftCut_symmetric M x y hxy] at hs
      have hzx := Option.some.inj hs
      omega
    constructor
    · by_contra h
      have hlt : w.val < x.val := by omega
      apply M.noncrossing (leftPoint n w) (leftPoint n x)
      · simpa [leftPoint] using hlt
      · rw [harchW]
        simpa [leftPoint] using hxz
      · rw [harchW, harchX]
        simpa [leftPoint] using hzy
    · by_contra h
      have hlt : y.val < w.val := by omega
      apply M.noncrossing (leftPoint n x) (leftPoint n z)
      · simpa [leftPoint] using hxz
      · rw [harchX]
        simpa [leftPoint] using hzy
      · rw [harchX, harchZ]
        simpa [leftPoint] using hlt

  have leftCut_arch_span_one_or_three {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4)
      (x y : Fin n) (hxy : (leftCut M) x = some y)
      (hord : x.val < y.val) :
      y.val = x.val + 1 ∨ y.val = x.val + 3 := by
    have hbound := leftCut_arch_span_le_three M hn hw x y hxy hord
    have hnot : y.val ≠ x.val + 2 := by
      intro heq
      let z : Fin n := ⟨x.val + 1, by have hy := y.isLt; omega⟩
      have hxz : x.val < z.val := by dsimp [z]; omega
      have hzy : z.val < y.val := by dsimp [z]; omega
      have hzpair := leftCut_between_paired M x y z hxy hxz hzy
      cases hcut : (leftCut M) z with
      | none => exact hzpair hcut
      | some w =>
        have hins := leftCut_between_mate_inside M x y z w hxy hcut hxz hzy
        have hwz : w = z := Fin.ext (by dsimp [z]; omega)
        subst w
        exact M.mate_ne _ ((leftCut_eq_some_iff M z z).1 hcut)
    omega

  have leftCut_span_three_inner_pair {n : ℕ} (M : UpperMatching n)
      (x y : Fin n) (hxy : (leftCut M) x = some y)
      (hspan : y.val = x.val + 3) :
      (leftCut M) ⟨x.val + 1, by omega⟩ =
        some ⟨x.val + 2, by omega⟩ := by
    let z : Fin n := ⟨x.val + 1, by have hy := y.isLt; omega⟩
    let t : Fin n := ⟨x.val + 2, by have hy := y.isLt; omega⟩
    have hxz : x.val < z.val := by dsimp [z]; omega
    have hzy : z.val < y.val := by dsimp [z]; omega
    have hzpair := leftCut_between_paired M x y z hxy hxz hzy
    cases hcut : (leftCut M) z with
    | none => exact (hzpair hcut).elim
    | some w =>
      have hins := leftCut_between_mate_inside M x y z w hxy hcut hxz hzy
      have hwz : w.val ≠ z.val := by
        intro hv
        have heq : w = z := Fin.ext hv
        subst w
        exact M.mate_ne _ ((leftCut_eq_some_iff M z z).1 hcut)
      have hwt : w = t := Fin.ext (by dsimp [z, t] at hwz ⊢; omega)
      exact congrArg Option.some hwt

  let edge {n : ℕ} (M : UpperMatching n)
      (x y : Fin (2 * n)) : Prop := M.mate x = y ∨ x.rev = y

  let rainbowLabel (n : ℕ) (x : Fin (2 * n)) : Fin n :=
    if h : x.val < n then ⟨x.val, h⟩
    else ⟨x.rev.val, by
      have hx := x.isLt
      have hr : x.rev.val = 2 * n - (x.val + 1) := by simp
      omega⟩

  have rainbowLabel_rev (n : ℕ) (x : Fin (2 * n)) :
      rainbowLabel n x.rev = rainbowLabel n x := by
    unfold rainbowLabel
    split_ifs with h₁ h₂
    · have hx := x.isLt
      have hr : x.rev.val = 2 * n - (x.val + 1) := by simp
      omega
    · apply Fin.ext
      simp
    · apply Fin.ext
      simp
    · have hx := x.isLt
      have hr : x.rev.val = 2 * n - (x.val + 1) := by simp
      omega

  let contractedEdge {n : ℕ} (M : UpperMatching n)
      (i j : Fin n) : Prop :=
    ∃ x y : Fin (2 * n), rainbowLabel n x = i ∧
      rainbowLabel n y = j ∧ M.mate x = y

  have oneLoop_implies_contracted_connected {n : ℕ} (M : UpperMatching n)
      (h : M.oneLoop) (i j : Fin n) :
      Relation.ReflTransGen (contractedEdge M) i j := by
    have hedges : ∀ x y : Fin (2 * n), (edge M) x y →
        Relation.ReflTransGen (contractedEdge M)
          (rainbowLabel n x) (rainbowLabel n y) := by
      intro x y hxy
      rcases hxy with hupper | hrainbow
      · exact Relation.ReflTransGen.single ⟨x, y, rfl, rfl, hupper⟩
      · subst y
        rw [rainbowLabel_rev]
    have hp := h (leftPoint n i) (leftPoint n j)
    have hc := Relation.ReflTransGen.lift' (rainbowLabel n) hedges _ _ hp
    change Relation.ReflTransGen (contractedEdge M)
      (rainbowLabel n (leftPoint n i)) (rainbowLabel n (leftPoint n j)) at hc
    simpa [rainbowLabel, leftPoint] using hc

  have contractedEdge_iff_cut_or_cross {n : ℕ} (M : UpperMatching n)
      (i j : Fin n) : (contractedEdge M) i j ↔
        (leftCut M) i = some j ∨ (rightCut M) i = some j ∨
        M.mate (leftPoint n i) = rightPoint n j ∨
        M.mate (leftPoint n j) = rightPoint n i := by
    have hpoint (z : Fin (2 * n)) (k : Fin n)
        (hz : rainbowLabel n z = k) :
        z = leftPoint n k ∨ z = rightPoint n k := by
      have hf : z = leftPoint n (rainbowLabel n z) ∨
          z.rev = leftPoint n (rainbowLabel n z) := by
        unfold rainbowLabel
        split_ifs
        · left; apply Fin.ext; rfl
        · right; apply Fin.ext; rfl
      rcases hf with hl | hr
      · left; simpa [hz] using hl
      · right
        have hrev := congrArg Fin.rev hr
        simpa [rightPoint, hz] using hrev
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      rcases hpoint x i hx with hxl | hxr
      all_goals rcases hpoint y j hy with hyl | hyr
      · left
        exact (leftCut_eq_some_iff M i j).2 (by simpa [hxl, hyl] using hxy)
      · right; right; left
        simpa [hxl, hyr] using hxy
      · right; right; right
        rw [← hyl, ← hxr, ← hxy, M.mate_mate]
      · right; left
        exact (rightCut_eq_some_iff M i j).2
          (by simpa [hxr, hyr] using hxy)
    · rintro (hl | hr | hc | hc)
      · exact ⟨leftPoint n i, leftPoint n j,
          by simp [rainbowLabel, leftPoint], by simp [rainbowLabel, leftPoint],
          (leftCut_eq_some_iff M i j).1 hl⟩
      · exact ⟨rightPoint n i, rightPoint n j,
          by unfold rightPoint; rw [rainbowLabel_rev]; simp [rainbowLabel, leftPoint],
          by unfold rightPoint; rw [rainbowLabel_rev]; simp [rainbowLabel, leftPoint],
          (rightCut_eq_some_iff M i j).1 hr⟩
      · exact ⟨leftPoint n i, rightPoint n j,
          by simp [rainbowLabel, leftPoint],
          by unfold rightPoint; rw [rainbowLabel_rev]; simp [rainbowLabel, leftPoint], hc⟩
      · refine ⟨rightPoint n i, leftPoint n j,
          by unfold rightPoint; rw [rainbowLabel_rev]; simp [rainbowLabel, leftPoint],
          by simp [rainbowLabel, leftPoint], ?_⟩
        rw [← hc, M.mate_mate]

  have fiber_connected {n : ℕ} (M : UpperMatching n)
      (x : Fin (2 * n)) :
      Relation.ReflTransGen (edge M) x (leftPoint n (rainbowLabel n x)) ∧
      Relation.ReflTransGen (edge M) (leftPoint n (rainbowLabel n x)) x := by
    have hf : x = leftPoint n (rainbowLabel n x) ∨
        x.rev = leftPoint n (rainbowLabel n x) := by
      unfold rainbowLabel
      split_ifs
      · left; apply Fin.ext; rfl
      · right; apply Fin.ext; rfl
    rcases hf with h | h
    · rw [← h]
      exact ⟨.refl, .refl⟩
    · refine ⟨.single (Or.inr h), .single (Or.inr ?_)⟩
      rw [← h, Fin.rev_rev]

  have contractedEdge_lift {n : ℕ} (M : UpperMatching n)
      (i j : Fin n) (h : (contractedEdge M) i j) :
      Relation.ReflTransGen (edge M) (leftPoint n i) (leftPoint n j) := by
    rcases h with ⟨x, y, hx, hy, hxy⟩
    have hxi := (fiber_connected M x).2
    have hyj := (fiber_connected M y).1
    rw [hx] at hxi
    rw [hy] at hyj
    have hmiddle : Relation.ReflTransGen (edge M) x y :=
      .single (Or.inl hxy)
    exact hxi.trans (hmiddle.trans hyj)

  have oneLoop_iff_contracted_connected {n : ℕ} (M : UpperMatching n) :
      M.oneLoop ↔ ∀ i j : Fin n,
        Relation.ReflTransGen (contractedEdge M) i j := by
    constructor
    · exact oneLoop_implies_contracted_connected M
    · intro h x y
      have hpath := h (rainbowLabel n x) (rainbowLabel n y)
      have hlift := Relation.ReflTransGen.lift' (leftPoint n)
        (fun i j hij => contractedEdge_lift M i j hij) _ _ hpath
      change Relation.ReflTransGen (edge M)
        (leftPoint n (rainbowLabel n x))
        (leftPoint n (rainbowLabel n y)) at hlift
      exact (fiber_connected M x).1.trans
        (hlift.trans (fiber_connected M y).2)

  have crossing_rank_order {n : ℕ} (M : UpperMatching n)
      (a b : Fin (2 * n)) (_ha : a.val < n) (hb : b.val < n)
      (hab : a.val < b.val) (hca : n ≤ (M.mate a).val)
      (_hcb : n ≤ (M.mate b).val) :
      (M.mate b).val < (M.mate a).val := by
    have hba : b.val < (M.mate a).val := by omega
    have hne : M.mate a ≠ M.mate b := by
      intro h
      have h' := congrArg M.mate h
      rw [M.mate_mate, M.mate_mate] at h'
      exact (Fin.ne_of_lt hab) h'
    have hv : (M.mate a).val ≠ (M.mate b).val := by
      intro h
      apply hne
      exact Fin.ext h
    by_contra horder
    have hlt : (M.mate a).val < (M.mate b).val := by omega
    exact M.noncrossing a b hab hba hlt

  -- The two closing positions determine each half-prefix.
  let TwoDownPrefix (n : ℕ) :=
    {ab : ℕ × ℕ // 1 ≤ ab.1 ∧ 3 ≤ ab.2 ∧ ab.1 < ab.2 ∧ ab.2 < n}

  let secondOpen {n : ℕ} (p : TwoDownPrefix n) : ℕ :=
    if p.val.2 = p.val.1 + 1 then p.val.1 - 2 else p.val.2 - 1

  let halfMate {n : ℕ} (p : TwoDownPrefix n) (x : ℕ) : ℕ :=
    if x = p.val.1 - 1 then p.val.1
    else if x = p.val.1 then p.val.1 - 1
    else if x = (secondOpen p) then p.val.2
    else if x = p.val.2 then (secondOpen p)
    else x

  have twoDown_endpoints_distinct {n : ℕ} (p : TwoDownPrefix n) :
      p.val.1 - 1 ≠ p.val.1 ∧
      p.val.1 - 1 ≠ (secondOpen p) ∧
      p.val.1 - 1 ≠ p.val.2 ∧
      p.val.1 ≠ (secondOpen p) ∧
      p.val.1 ≠ p.val.2 ∧
      (secondOpen p) ≠ p.val.2 := by
    unfold secondOpen
    split_ifs with h
    · have := p.property.1
      have := p.property.2.1
      have := p.property.2.2.1
      omega
    · have := p.property.1
      have := p.property.2.1
      have := p.property.2.2.1
      omega

  have halfMate_involutive {n : ℕ} (p : TwoDownPrefix n)
      (x : ℕ) : (halfMate p) ((halfMate p) x) = x := by
    obtain ⟨huv, huw, huz, hvw, hvz, hwz⟩ := twoDown_endpoints_distinct p
    unfold halfMate
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ <;> omega

  have halfMate_fixed_iff {n : ℕ} (p : TwoDownPrefix n)
      (x : ℕ) : (halfMate p) x = x ↔
        x ≠ p.val.1 - 1 ∧ x ≠ p.val.1 ∧
        x ≠ (secondOpen p) ∧ x ≠ p.val.2 := by
    obtain ⟨huv, huw, huz, hvw, hvz, hwz⟩ := twoDown_endpoints_distinct p
    constructor
    · intro h
      unfold halfMate at h
      grind
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      simp [halfMate, h₁, h₂, h₃, h₄]

  have four_endpoint_pairing_shape
      {n : ℕ} {cut : Fin n → Option (Fin n)}
      (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
      (hsym : ∀ x y, cut x = some y → cut y = some x)
      (hself : ∀ x, cut x ≠ some x)
      (hcross : ∀ x y z w, cut x = some y → cut z = some w →
        x.val < z.val → z.val < y.val → y.val < w.val → False) :
      let S := Finset.univ.filter (fun x => cut x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
      (cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∨
        (cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) := by
    classical
    dsimp
    let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
    let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
    have he_mem (i : Fin 4) : e i ∈ S := by
      dsimp [e]
      exact Finset.orderEmbOfFin_mem S hcard i
    have he_lt {i j : Fin 4} (hij : i < j) : (e i).val < (e j).val := by
      have h := (S.orderIsoOfFin hcard).strictMono hij
      simpa [e] using h
    have himage : Finset.image e Finset.univ = S := by
      dsimp [e]
      exact Finset.image_orderEmbOfFin_univ S hcard
    have hindex {x : Fin n} (hx : x ∈ S) : ∃ i : Fin 4, e i = x := by
      rw [← himage] at hx
      rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
      exact ⟨i, hi⟩
    have hpair (i : Fin 4) : ∃ j : Fin 4, cut (e i) = some (e j) := by
      have hi := (Finset.mem_filter.mp (he_mem i)).2
      cases hc : cut (e i) with
      | none => exact (hi hc).elim
      | some y =>
        have hy : y ∈ S := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hnone
          have hback := hsym _ _ hc
          rw [hnone] at hback
          cases hback
        obtain ⟨j, hj⟩ := hindex hy
        exact ⟨j, by simp only [hj]⟩
    have hsame {x a b : Fin n} (ha : cut x = some a)
        (hb : cut x = some b) : a = b :=
      Option.some.inj (ha.symm.trans hb)
    obtain ⟨j0, hj0⟩ := hpair 0
    fin_cases j0
    · exact False.elim ((hself (e 0)) (by simpa using hj0))
    · have h10 : cut (e 1) = some (e 0) := by simpa using hsym _ _ hj0
      obtain ⟨j2, hj2⟩ := hpair 2
      fin_cases j2
      · have h20 : cut (e 0) = some (e 2) := by simpa using hsym _ _ hj2
        exact False.elim ((Fin.ne_of_lt (he_lt (show (1 : Fin 4) < 2 by omega)))
          (hsame hj0 h20))
      · have h21 : cut (e 1) = some (e 2) := by simpa using hsym _ _ hj2
        have heq : some (e 0) = some (e 2) := by
          calc
            some (e 0) = cut (e 1) := h10.symm
            _ = some (e 2) := h21
        exact False.elim ((Fin.ne_of_lt (he_lt (show (0 : Fin 4) < 2 by omega)))
          (Option.some.inj heq))
      · exact False.elim ((hself (e 2)) (by simpa using hj2))
      · exact Or.inl ⟨hj0, hj2⟩
    · obtain ⟨j1, hj1⟩ := hpair 1
      fin_cases j1
      · have h10 : cut (e 0) = some (e 1) := by simpa using hsym _ _ hj1
        have heq : some (e 2) = some (e 1) := hj0.symm.trans h10
        exact False.elim ((Fin.ne_of_lt (he_lt (show (1 : Fin 4) < 2 by omega)))
          (Option.some.inj heq).symm)
      · exact False.elim ((hself (e 1)) (by simpa using hj1))
      · have h21 : cut (e 2) = some (e 1) := by simpa using hsym _ _ hj1
        have h20 : cut (e 2) = some (e 0) := by simpa using hsym _ _ hj0
        have heq : some (e 0) = some (e 1) := h20.symm.trans h21
        exact False.elim ((Fin.ne_of_lt (he_lt (show (0 : Fin 4) < 1 by omega)))
          (Option.some.inj heq))
      · exact False.elim (hcross (e 0) (e 2) (e 1) (e 3) hj0 hj1
          (he_lt (show (0 : Fin 4) < 1 by omega))
          (he_lt (show (1 : Fin 4) < 2 by omega))
          (he_lt (show (2 : Fin 4) < 3 by omega)))
    · have h30 : cut (e 3) = some (e 0) := by simpa using hsym _ _ hj0
      obtain ⟨j1, hj1⟩ := hpair 1
      fin_cases j1
      · have h10 : cut (e 0) = some (e 1) := by simpa using hsym _ _ hj1
        have heq : some (e 3) = some (e 1) := hj0.symm.trans h10
        exact False.elim ((Fin.ne_of_lt (he_lt (show (1 : Fin 4) < 3 by omega)))
          (Option.some.inj heq).symm)
      · exact False.elim ((hself (e 1)) (by simpa using hj1))
      · exact Or.inr ⟨hj0, hj1⟩
      · have h31 : cut (e 3) = some (e 1) := by simpa using hsym _ _ hj1
        exact False.elim ((Fin.ne_of_lt (he_lt (show (0 : Fin 4) < 1 by omega)))
          (hsame h30 h31))

  have leftCut_four_endpoint_pairing_shape {n : ℕ} (M : UpperMatching n)
      (hn : 4 ≤ n) (hw : M.winding = n - 4) :
      let S := Finset.univ.filter (fun x : Fin n => (leftCut M) x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin (leftCut_paired_card_four M hn hw)
      ((leftCut M) (e 0) = some (e 1) ∧ (leftCut M) (e 2) = some (e 3)) ∨
        ((leftCut M) (e 0) = some (e 3) ∧ (leftCut M) (e 1) = some (e 2)) := by
    apply four_endpoint_pairing_shape
      (leftCut_paired_card_four M hn hw)
    · exact leftCut_symmetric M
    · intro x hx
      exact M.mate_ne _ ((leftCut_eq_some_iff M x x).1 hx)
    · intro x y z w hxy hzw hxz hzy hyw
      have harchX := (leftCut_eq_some_iff M x y).1 hxy
      have harchZ := (leftCut_eq_some_iff M z w).1 hzw
      apply M.noncrossing (leftPoint n x) (leftPoint n z)
      · simpa [leftPoint] using hxz
      · rw [harchX]
        simpa [leftPoint] using hzy
      · rw [harchX, harchZ]
        simpa [leftPoint] using hyw

  have four_endpoint_adjacent_or_nested
      {n : ℕ} {cut : Fin n → Option (Fin n)}
      (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
      (hbetween : ∀ x y z, cut x = some y → x.val < z.val →
        z.val < y.val → cut z ≠ none)
      (hspan : ∀ x y, cut x = some y → x.val < y.val →
        y.val ≤ x.val + 3)
      (hshape : let S := Finset.univ.filter (fun x => cut x ≠ none)
        let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
        (cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∨
          (cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2))) :
      let S := Finset.univ.filter (fun x => cut x ≠ none)
      let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
      ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
      ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
        (e 3).val = (e 0).val + 3) := by
    classical
    let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
    let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
    change (cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∨
      (cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) at hshape
    change ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
      ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
        (e 3).val = (e 0).val + 3)
    have he_lt {i j : Fin 4} (hij : i < j) : (e i).val < (e j).val := by
      have h := (S.orderIsoOfFin hcard).strictMono hij
      simpa [e] using h
    have himage : Finset.image e Finset.univ = S := by
      dsimp [e]
      exact Finset.image_orderEmbOfFin_univ S hcard
    have hindex {z : Fin n} (hz : cut z ≠ none) : ∃ i : Fin 4, e i = z := by
      have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      rw [← himage] at hzS
      rcases Finset.mem_image.mp hzS with ⟨i, -, hi⟩
      exact ⟨i, hi⟩
    have h01 : (e 0).val < (e 1).val := he_lt (by omega)
    have h12 : (e 1).val < (e 2).val := he_lt (by omega)
    have h23 : (e 2).val < (e 3).val := he_lt (by omega)
    rcases hshape with hsep | hnest
    · have hadj01 : (e 1).val = (e 0).val + 1 := by
        by_contra hne
        let z : Fin n := ⟨(e 0).val + 1, by have := (e 1).isLt; omega⟩
        have hz := hbetween (e 0) (e 1) z hsep.1
          (by dsimp [z]; omega) (by dsimp [z]; omega)
        rcases hindex (hz) with ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        fin_cases i <;> dsimp [z] at hv <;> omega
      have hadj23 : (e 3).val = (e 2).val + 1 := by
        by_contra hne
        let z : Fin n := ⟨(e 2).val + 1, by have := (e 3).isLt; omega⟩
        have hz := hbetween (e 2) (e 3) z hsep.2
          (by dsimp [z]; omega) (by dsimp [z]; omega)
        rcases hindex (hz) with ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        fin_cases i <;> dsimp [z] at hv <;> omega
      exact Or.inl ⟨hsep, hadj01, hadj23⟩
    · have hbound := hspan (e 0) (e 3) hnest.1 (by omega)
      exact Or.inr ⟨hnest, by omega, by omega, by omega⟩

  have halfMate_lt {n : ℕ} (p : TwoDownPrefix n)
      (x : Fin n) : (halfMate p) x.val < n := by
    have hf : p.val.1 < n := lt_trans p.property.2.2.1 p.property.2.2.2
    have hp : p.val.1 - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hf
    have hs : (secondOpen p) < n := by
      unfold secondOpen
      split_ifs
      · exact lt_of_le_of_lt (Nat.sub_le _ _) hf
      · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2
    have hsecond := p.property.2.2.2
    unfold halfMate
    split_ifs <;> have := x.isLt <;> omega

  let halfCut {n : ℕ} (p : TwoDownPrefix n)
      (x : Fin n) : Option (Fin n) :=
    if (halfMate p) x.val = x.val then none
    else some ⟨(halfMate p) x.val, (halfMate_lt p) x⟩

  have halfCut_eq_none_iff {n : ℕ} (p : TwoDownPrefix n)
      (x : Fin n) : (halfCut p) x = none ↔
        x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
        x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by
    unfold halfCut
    split_ifs with h
    · exact ⟨fun _ => ((halfMate_fixed_iff p) x.val).mp h, fun _ => rfl⟩
    · simp only [false_iff]
      exact fun hx => h (((halfMate_fixed_iff p) x.val).mpr hx)

  have halfCut_first_pair {n : ℕ} (p : TwoDownPrefix n) :
      (halfCut p) ⟨p.val.1 - 1, by
        exact lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ =
        some ⟨p.val.1, by have := p.property.2.2.1; have := p.property.2.2.2; omega⟩ := by
    have hd := twoDown_endpoints_distinct p
    simp [halfCut, halfMate, hd.1.symm]

  have halfCut_second_pair {n : ℕ} (p : TwoDownPrefix n) :
      (halfCut p) ⟨(secondOpen p), by
        unfold secondOpen
        split_ifs
        · exact lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)
        · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ =
        some ⟨p.val.2, p.property.2.2.2⟩ := by
    have hd := twoDown_endpoints_distinct p
    simp [halfCut, halfMate,
      hd.2.1.symm, hd.2.2.2.1.symm, hd.2.2.2.2.2.symm]

  have halfCut_first_reverse {n : ℕ} (p : TwoDownPrefix n) :
      (halfCut p) ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ =
        some ⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ := by
    have hd := twoDown_endpoints_distinct p
    simp [halfCut, halfMate,
      hd.1, hd.1.symm]

  have halfCut_second_reverse {n : ℕ} (p : TwoDownPrefix n) :
      (halfCut p) ⟨p.val.2, p.property.2.2.2⟩ =
        some ⟨(secondOpen p), by
          unfold secondOpen
          split_ifs
          · exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)
          · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ := by
    have hd := twoDown_endpoints_distinct p
    simp [halfCut, halfMate,
      hd.2.2.1.symm, hd.2.2.2.2.1.symm,
      hd.2.2.2.2.2, hd.2.2.2.2.2.symm]

  have four_endpoint_cut_eq_halfCut
      {n : ℕ} {cut : Fin n → Option (Fin n)}
      (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
      (p : TwoDownPrefix n)
      (hpositions : let S := Finset.univ.filter (fun x => cut x ≠ none)
        let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
        ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x)
      (hpoints : let S := Finset.univ.filter (fun x => cut x ≠ none)
        let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
        ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)) :
      ∀ x, cut x = (halfCut p) x := by
    classical
    let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
    let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
    change ∀ x, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x at hpositions
    change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i) at hpoints
    have himage : Finset.image e Finset.univ = S := by
      dsimp [e]
      exact Finset.image_orderEmbOfFin_univ S hcard
    intro x
    by_cases hx : ∃ i : Fin 4, e i = x
    · obtain ⟨i, rfl⟩ := hx
      exact hpoints i
    · have hcut : cut x = none := by
        by_contra hn
        have hmem : x ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
        rw [← himage] at hmem
        rcases Finset.mem_image.mp hmem with ⟨i, -, hi⟩
        exact hx ⟨i, hi⟩
      have hp : (halfCut p) x = none := by
        by_contra hn
        exact hx (hpositions x hn)
      rw [hcut, hp]

  have four_endpoint_twoDownPrefix
      {n : ℕ} {cut : Fin n → Option (Fin n)}
      (hcard : (Finset.univ.filter (fun x => cut x ≠ none)).card = 4)
      (hsym : ∀ x y, cut x = some y → cut y = some x)
      (hadj : let S := Finset.univ.filter (fun x => cut x ≠ none)
        let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
        ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
          (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
        ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
          (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
          (e 3).val = (e 0).val + 3)) :
      ∃ p : TwoDownPrefix n, ∀ x, cut x = (halfCut p) x := by
    classical
    let S : Finset (Fin n) := Finset.univ.filter (fun x => cut x ≠ none)
    let e : Fin 4 → Fin n := S.orderEmbOfFin hcard
    change ((cut (e 0) = some (e 1) ∧ cut (e 2) = some (e 3)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 3).val = (e 2).val + 1) ∨
      ((cut (e 0) = some (e 3) ∧ cut (e 1) = some (e 2)) ∧
        (e 1).val = (e 0).val + 1 ∧ (e 2).val = (e 0).val + 2 ∧
        (e 3).val = (e 0).val + 3) at hadj
    have he_lt {i j : Fin 4} (hij : i < j) : (e i).val < (e j).val := by
      have h := (S.orderIsoOfFin hcard).strictMono hij
      simpa [e] using h
    have h01 : (e 0).val < (e 1).val := he_lt (by omega)
    have h12 : (e 1).val < (e 2).val := he_lt (by omega)
    have h23 : (e 2).val < (e 3).val := he_lt (by omega)
    rcases hadj with ⟨⟨hc01, hc23⟩, ha01, ha23⟩ |
        ⟨⟨hc03, hc12⟩, ha01, ha02, ha03⟩
    · let p : TwoDownPrefix n :=
        ⟨((e 1).val, (e 3).val), ⟨by omega, by omega, by omega, (e 3).isLt⟩⟩
      have hso : (secondOpen p) = (e 2).val := by
        dsimp [p, secondOpen]
        split_ifs <;> omega
      have hv0 : (e 0).val = p.val.1 - 1 := by dsimp [p]; omega
      have hv1 : (e 1).val = p.val.1 := rfl
      have hv2 : (e 2).val = (secondOpen p) := hso.symm
      have hv3 : (e 3).val = p.val.2 := rfl
      have hp01 : (halfCut p) (e 0) = some (e 1) := by
        have he0 : e 0 = (⟨p.val.1 - 1, by
            exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv0
        have he1 : e 1 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
          Fin.ext hv1
        rw [he0, he1]
        exact (halfCut_first_pair p)
      have hp10 : (halfCut p) (e 1) = some (e 0) := by
        have he0 : e 0 = (⟨p.val.1 - 1, by
            exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv0
        have he1 : e 1 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
          Fin.ext hv1
        rw [he0, he1]
        exact (halfCut_first_reverse p)
      have hp23 : (halfCut p) (e 2) = some (e 3) := by
        have he2 : e 2 = (⟨(secondOpen p), by rw [hso]; exact (e 2).isLt⟩ : Fin n) :=
          Fin.ext hv2
        have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
        rw [he2, he3]
        exact (halfCut_second_pair p)
      have hp32 : (halfCut p) (e 3) = some (e 2) := by
        have he2 : e 2 = (⟨(secondOpen p), by rw [hso]; exact (e 2).isLt⟩ : Fin n) :=
          Fin.ext hv2
        have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
        rw [he2, he3]
        exact (halfCut_second_reverse p)
      refine ⟨p, four_endpoint_cut_eq_halfCut hcard p ?_ ?_⟩
      · change ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x
        intro x hx
        have hv : x.val = p.val.1 - 1 ∨ x.val = p.val.1 ∨
            x.val = (secondOpen p) ∨ x.val = p.val.2 := by
          by_contra hn
          have hfix : x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
              x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by tauto
          exact hx (((halfCut_eq_none_iff p) x).2 hfix)
        rcases hv with h | h | h | h
        · exact ⟨0, Fin.ext (by omega)⟩
        · exact ⟨1, Fin.ext (by omega)⟩
        · exact ⟨2, Fin.ext (by omega)⟩
        · exact ⟨3, Fin.ext (by omega)⟩
      · change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)
        intro i
        fin_cases i
        · exact hc01.trans hp01.symm
        · exact (hsym _ _ hc01).trans hp10.symm
        · exact hc23.trans hp23.symm
        · exact (hsym _ _ hc23).trans hp32.symm
    · let p : TwoDownPrefix n :=
        ⟨((e 2).val, (e 3).val), ⟨by omega, by omega, h23, (e 3).isLt⟩⟩
      have hso : (secondOpen p) = (e 0).val := by
        dsimp [p, secondOpen]
        split_ifs <;> omega
      have hv0 : (e 0).val = (secondOpen p) := hso.symm
      have hv1 : (e 1).val = p.val.1 - 1 := by dsimp [p]; omega
      have hv2 : (e 2).val = p.val.1 := rfl
      have hv3 : (e 3).val = p.val.2 := rfl
      have hp12 : (halfCut p) (e 1) = some (e 2) := by
        have he1 : e 1 = (⟨p.val.1 - 1, by
            exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv1
        have he2 : e 2 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
          Fin.ext hv2
        rw [he1, he2]
        exact (halfCut_first_pair p)
      have hp21 : (halfCut p) (e 2) = some (e 1) := by
        have he1 : e 1 = (⟨p.val.1 - 1, by
            exact lt_of_le_of_lt (Nat.sub_le _ _)
              (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) := Fin.ext hv1
        have he2 : e 2 = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
          Fin.ext hv2
        rw [he1, he2]
        exact (halfCut_first_reverse p)
      have hp03 : (halfCut p) (e 0) = some (e 3) := by
        have he0 : e 0 = (⟨(secondOpen p), by rw [hso]; exact (e 0).isLt⟩ : Fin n) :=
          Fin.ext hv0
        have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
        rw [he0, he3]
        exact (halfCut_second_pair p)
      have hp30 : (halfCut p) (e 3) = some (e 0) := by
        have he0 : e 0 = (⟨(secondOpen p), by rw [hso]; exact (e 0).isLt⟩ : Fin n) :=
          Fin.ext hv0
        have he3 : e 3 = (⟨p.val.2, p.property.2.2.2⟩ : Fin n) := Fin.ext hv3
        rw [he0, he3]
        exact (halfCut_second_reverse p)
      refine ⟨p, four_endpoint_cut_eq_halfCut hcard p ?_ ?_⟩
      · change ∀ x : Fin n, (halfCut p) x ≠ none → ∃ i : Fin 4, e i = x
        intro x hx
        have hv : x.val = p.val.1 - 1 ∨ x.val = p.val.1 ∨
            x.val = (secondOpen p) ∨ x.val = p.val.2 := by
          by_contra hn
          have hfix : x.val ≠ p.val.1 - 1 ∧ x.val ≠ p.val.1 ∧
              x.val ≠ (secondOpen p) ∧ x.val ≠ p.val.2 := by tauto
          exact hx (((halfCut_eq_none_iff p) x).2 hfix)
        rcases hv with h | h | h | h
        · exact ⟨1, Fin.ext (by omega)⟩
        · exact ⟨2, Fin.ext (by omega)⟩
        · exact ⟨0, Fin.ext (by omega)⟩
        · exact ⟨3, Fin.ext (by omega)⟩
      · change ∀ i : Fin 4, cut (e i) = (halfCut p) (e i)
        intro i
        fin_cases i
        · exact hc03.trans hp03.symm
        · exact hc12.trans hp12.symm
        · exact (hsym _ _ hc12).trans hp21.symm
        · exact (hsym _ _ hc03).trans hp30.symm

  have halfMate_lt_self_iff {n : ℕ} (p : TwoDownPrefix n)
      (x : Fin n) : (halfMate p) x.val < x.val ↔
        x.val = p.val.1 ∨ x.val = p.val.2 := by
    have hso : (secondOpen p) < p.val.2 := by
      unfold secondOpen
      split_ifs
      · exact lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.1
      · have := p.property.2.1
        omega
    have hd := twoDown_endpoints_distinct p
    unfold halfMate
    split_ifs <;> have := p.property.1 <;> omega

  have halfCut_injective {n : ℕ} (p q : TwoDownPrefix n)
      (h : ∀ x, (halfCut p) x = (halfCut q) x) : p = q := by
    have hdown (r : TwoDownPrefix n) (x : Fin n) :
        (∃ y : Fin n, (halfCut r) x = some y ∧ y.val < x.val) ↔
          x.val = r.val.1 ∨ x.val = r.val.2 := by
      rw [← (halfMate_lt_self_iff r) x]
      constructor
      · rintro ⟨y, hy, hlt⟩
        by_cases hr : (halfMate r) x.val = x.val
        · simp [halfCut, hr] at hy
        · have heq : (⟨(halfMate r) x.val, (halfMate_lt r) x⟩ : Fin n) = y := by
            simpa [halfCut, hr] using hy
          rw [← heq] at hlt
          exact hlt
      · intro hlt
        have hne : (halfMate r) x.val ≠ x.val := by omega
        refine ⟨⟨(halfMate r) x.val, (halfMate_lt r) x⟩, ?_, hlt⟩
        simp [halfCut, hne]
    have hfirst : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
      let x : Fin n := ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩
      have hp := (hdown p x).2 (Or.inl rfl)
      rw [h x] at hp
      exact (hdown q x).1 hp
    have hsecond : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
      let x : Fin n := ⟨p.val.2, p.property.2.2.2⟩
      have hp := (hdown p x).2 (Or.inr rfl)
      rw [h x] at hp
      exact (hdown q x).1 hp
    have hvalues : p.val.1 = q.val.1 ∧ p.val.2 = q.val.2 := by
      rcases hfirst with hfirst | hfirst <;>
        rcases hsecond with hsecond | hsecond <;>
        have := p.property.2.2.1 <;> have := q.property.2.2.1 <;> omega
    exact Subtype.ext (Prod.ext hvalues.1 hvalues.2)

  let pairedPositions {n : ℕ} (p : TwoDownPrefix n) :
      Finset (Fin n) :=
    {⟨p.val.1 - 1, by have := p.property.2.2.1; have := p.property.2.2.2; omega⟩,
      ⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩,
      ⟨(secondOpen p), by
        unfold secondOpen
        split_ifs
        · have := p.property.2.2.1; have := p.property.2.2.2; omega
        · have := p.property.2.2.2; omega⟩,
      ⟨p.val.2, p.property.2.2.2⟩}

  let unmatchedPositions {n : ℕ} (p : TwoDownPrefix n) :
      Finset (Fin n) :=
    Finset.univ.filter fun x => (halfCut p) x = none

  have unmatchedPositions_card {n : ℕ} (p : TwoDownPrefix n) :
      (unmatchedPositions p).card = n - 4 := by
    have hc : (unmatchedPositions p) = (pairedPositions p)ᶜ := by
      ext x
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_compl]
      rw [(halfCut_eq_none_iff p)]
      simp only [pairedPositions, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      tauto
    have hpaired : (pairedPositions p).card = 4 := by
      have hd := twoDown_endpoints_distinct p
      simp [pairedPositions, Fin.ext_iff, hd.1, hd.2.1,
        hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2]
    rw [hc, Finset.card_compl, hpaired]
    simp

  let crossingUnmatchedEquiv {n : ℕ} (M : UpperMatching n) :
      {x : Fin n // (leftCut M) x = none} ≃
        {y : Fin n // (rightCut M) y = none} :=
    {
      toFun x := ⟨crossingRight M x.1 x.2, crossingRight_none M x.1 x.2⟩
      invFun y := ⟨crossingLeft M y.1 y.2, crossingLeft_none M y.1 y.2⟩
      left_inv x := by
        apply Subtype.ext
        have h : leftPoint n (crossingLeft M (crossingRight M x.1 x.2)
            (crossingRight_none M x.1 x.2)) =
            M.mate (rightPoint n (crossingRight M x.1 x.2)) := by
          apply Fin.ext
          rfl
        have hpoint : rightPoint n (crossingRight M x.1 x.2) =
            M.mate (leftPoint n x.1) := by
          have hv : leftPoint n (crossingRight M x.1 x.2) =
              (M.mate (leftPoint n x.1)).rev := by
            apply Fin.ext
            rfl
          simpa [rightPoint] using congrArg Fin.rev hv
        rw [hpoint, M.mate_mate] at h
        exact Fin.ext (by simpa [leftPoint] using congrArg Fin.val h)
      right_inv y := by
        apply Subtype.ext
        have h : rightPoint n (crossingRight M (crossingLeft M y.1 y.2)
            (crossingLeft_none M y.1 y.2)) =
            M.mate (leftPoint n (crossingLeft M y.1 y.2)) := by
          have hv : leftPoint n (crossingRight M (crossingLeft M y.1 y.2)
              (crossingLeft_none M y.1 y.2)) =
              (M.mate (leftPoint n (crossingLeft M y.1 y.2))).rev := by
            apply Fin.ext
            rfl
          simpa [rightPoint] using congrArg Fin.rev hv
        have hpoint : leftPoint n (crossingLeft M y.1 y.2) =
            M.mate (rightPoint n y.1) := by
          apply Fin.ext
          rfl
        rw [hpoint, M.mate_mate] at h
        apply Fin.ext
        simpa [rightPoint, leftPoint] using congrArg Fin.val (congrArg Fin.rev h)
    }

  let crossingUnmatchedOrderIso {n : ℕ} (M : UpperMatching n) :
      {x : Fin n // (leftCut M) x = none} ≃o
        {y : Fin n // (rightCut M) y = none} :=
    {
      toEquiv := crossingUnmatchedEquiv M
      map_rel_iff' := by
        have horder (x y : Fin n) (hx : (leftCut M) x = none)
            (hy : (leftCut M) y = none) (hxy : x < y) :
            crossingRight M x hx < crossingRight M y hy := by
          have hmate := crossing_rank_order M (leftPoint n x) (leftPoint n y)
            (by simp [leftPoint, x.isLt])
            (by simp [leftPoint, y.isLt])
            (by simpa [leftPoint] using hxy)
            (by simpa [leftCut] using hx)
            (by simpa [leftCut] using hy)
          have hrx : (crossingRight M x hx).val =
              2 * n - ((M.mate (leftPoint n x)).val + 1) := by
            simp [crossingRight]
          have hry : (crossingRight M y hy).val =
              2 * n - ((M.mate (leftPoint n y)).val + 1) := by
            simp [crossingRight]
          change (crossingRight M x hx).val < (crossingRight M y hy).val
          omega
        intro x y
        constructor
        · intro hxy
          by_contra hnot
          have hyx : y < x := lt_of_not_ge hnot
          have hrev := horder y.1 x.1 y.2 x.2 hyx
          exact (not_lt_of_ge hxy) hrev
        · intro hxy
          rcases eq_or_lt_of_le hxy with heq | hlt
          · subst y
            exact le_refl _
          · exact le_of_lt (horder x.1 y.1 x.2 y.2 hlt)
    }

  let rankJoin {n : ℕ} (p q : TwoDownPrefix n) :
      (unmatchedPositions p) ≃o (unmatchedPositions q) :=
    ((unmatchedPositions p).orderIsoOfFin (unmatchedPositions_card p)).symm.trans
      ((unmatchedPositions q).orderIsoOfFin (unmatchedPositions_card q))

  let unmatchedCutIso {n : ℕ} (p : TwoDownPrefix n) :
      (unmatchedPositions p) ≃o {x : Fin n // (halfCut p) x = none} :=
    OrderIso.setCongr ((unmatchedPositions p) : Set (Fin n))
      {x : Fin n | (halfCut p) x = none} (by
        ext x
        simp [unmatchedPositions])

  have crossing_eq_rankJoin {n : ℕ} (M : UpperMatching n)
      (p q : TwoDownPrefix n)
      (hp : ∀ x, (leftCut M) x = (halfCut p) x)
      (hq : ∀ x, (rightCut M) x = (halfCut q) x)
      (x : Fin n) (hx : (leftCut M) x = none) :
      rightPoint n (((rankJoin p) q ⟨x, by
        simp [unmatchedPositions, ← hp x, hx]⟩).1) =
        M.mate (leftPoint n x) := by
    let left : (unmatchedPositions p) ≃o {x : Fin n // (leftCut M) x = none} :=
      (unmatchedCutIso p) |>.trans
        (OrderIso.setCongr {x : Fin n | (halfCut p) x = none}
          {x : Fin n | (leftCut M) x = none} (by
            ext y
            simp [hp y]))
    let right : {x : Fin n // (rightCut M) x = none} ≃o (unmatchedPositions q) :=
      (OrderIso.setCongr {x : Fin n | (rightCut M) x = none}
        {x : Fin n | (halfCut q) x = none} (by
          ext y
          simp [hq y])).trans (unmatchedCutIso q).symm
    let sourceIso : (unmatchedPositions p) ≃o (unmatchedPositions q) :=
      (left.trans (crossingUnmatchedOrderIso M)).trans right
    have hcanonical : sourceIso = (rankJoin p) q := by
      have hself := StrictMono.eq_id (((rankJoin p) q).trans sourceIso.symm).strictMono
      apply OrderIso.ext
      apply funext
      intro y
      have hy := congrFun hself y
      have hy' := congrArg sourceIso hy
      simpa using hy'.symm
    let xp : (unmatchedPositions p) := ⟨x, by
      simp [unmatchedPositions, ← hp x, hx]⟩
    have hsource : (sourceIso xp).1 = crossingRight M x hx := by
      rfl
    rw [← hcanonical]
    have hpoint : rightPoint n (crossingRight M x hx) =
        M.mate (leftPoint n x) := by
      have hv : leftPoint n (crossingRight M x hx) =
          (M.mate (leftPoint n x)).rev := by
        apply Fin.ext
        rfl
      simpa [rightPoint] using congrArg Fin.rev hv
    exact (congrArg (rightPoint n) hsource).trans hpoint

  let joinedEdge {n : ℕ} (p q : TwoDownPrefix n)
      (i j : Fin n) : Prop :=
    (halfCut p) i = some j ∨ (halfCut q) i = some j ∨
      (∃ hi : i ∈ (unmatchedPositions p),
        ((rankJoin p) q ⟨i, hi⟩).1 = j) ∨
      (∃ hj : j ∈ (unmatchedPositions p),
        ((rankJoin p) q ⟨j, hj⟩).1 = i)

  have contractedEdge_iff_joinedEdge {n : ℕ} (M : UpperMatching n)
      (p q : TwoDownPrefix n)
      (hp : ∀ x, (leftCut M) x = (halfCut p) x)
      (hq : ∀ x, (rightCut M) x = (halfCut q) x)
      (i j : Fin n) : (contractedEdge M) i j ↔ (joinedEdge p) q i j := by
    have hcross (a b : Fin n) :
        M.mate (leftPoint n a) = rightPoint n b ↔
          ∃ ha : a ∈ (unmatchedPositions p),
            ((rankJoin p) q ⟨a, ha⟩).1 = b := by
      constructor
      · intro hab
        have hright : n ≤ (rightPoint n b).val := by
          have hb := b.isLt
          have hv : (rightPoint n b).val = 2 * n - (b.val + 1) := by
            simp [rightPoint, leftPoint]
          omega
        have haNone : (leftCut M) a = none :=
          (by simpa [leftCut] using (show
            n ≤ (M.mate (leftPoint n a)).val by rw [hab]; exact hright))
        have ha : a ∈ (unmatchedPositions p) := by
          simp [unmatchedPositions, ← hp a, haNone]
        refine ⟨ha, ?_⟩
        have hjoin := crossing_eq_rankJoin M p q hp hq a haNone
        rw [hab] at hjoin
        apply Fin.ext
        simpa [rightPoint, leftPoint] using congrArg Fin.val (congrArg Fin.rev hjoin)
      · rintro ⟨ha, hab⟩
        have haNone : (leftCut M) a = none := by
          have hpa : (halfCut p) a = none :=
            (Finset.mem_filter.mp ha).2
          exact (hp a).trans hpa
        have hjoin := crossing_eq_rankJoin M p q hp hq a haNone
        exact hjoin.symm.trans (congrArg (rightPoint n) hab)
    rw [contractedEdge_iff_cut_or_cross]
    change ((leftCut M) i = some j ∨ (rightCut M) i = some j ∨
      M.mate (leftPoint n i) = rightPoint n j ∨
      M.mate (leftPoint n j) = rightPoint n i) ↔
      ((halfCut p) i = some j ∨ (halfCut q) i = some j ∨
        (∃ hi : i ∈ (unmatchedPositions p),
          ((rankJoin p) q ⟨i, hi⟩).1 = j) ∨
        (∃ hj : j ∈ (unmatchedPositions p),
          ((rankJoin p) q ⟨j, hj⟩).1 = i))
    rw [hp i, hq i, hcross i j, hcross j i]

  let halfMateFin {n : ℕ} (p : TwoDownPrefix n)
      (x : Fin n) : Fin n :=
    ⟨(halfMate p) x.val, (halfMate_lt p) x⟩

  have halfMateFin_fixed_iff {n : ℕ}
      (p : TwoDownPrefix n) (x : Fin n) :
      (halfMateFin p) x = x ↔ x ∈ (unmatchedPositions p) := by
    simp only [unmatchedPositions, Finset.mem_filter,
      Finset.mem_univ, true_and, (halfCut_eq_none_iff p),
      ← (halfMate_fixed_iff p)]
    simp [halfMateFin, Fin.ext_iff]

  have halfMate_interval {n : ℕ}
      (p : TwoDownPrefix n) (a b : Fin n)
      (hab : a.val < b.val) (hbetween : b.val < (halfMate p) a.val) :
      (halfMate p) b.val ≠ b.val ∧
        (halfMate p) b.val < (halfMate p) a.val := by
    have hfirst := p.property.1
    have hsecond := p.property.2.1
    have hordered := p.property.2.2.1
    have hd := twoDown_endpoints_distinct p
    unfold halfMate secondOpen at hbetween hd ⊢
    split_ifs at hbetween hd ⊢ <;> omega

  let joinedMate {n : ℕ} (p q : TwoDownPrefix n)
      (x : Fin (2 * n)) : Fin (2 * n) :=
    if x.val < n then
      let i := rainbowLabel n x
      if hi : i ∈ (unmatchedPositions p) then
        rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
      else leftPoint n ((halfMateFin p) i)
    else
      let j := rainbowLabel n x
      if hj : j ∈ (unmatchedPositions q) then
        leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
      else rightPoint n ((halfMateFin q) j)

  have joinedMate_involutive {n : ℕ}
      (p q : TwoDownPrefix n) (x : Fin (2 * n)) :
      (joinedMate p) q ((joinedMate p) q x) = x := by
    have hpoint (z : Fin (2 * n)) :
        z = leftPoint n (rainbowLabel n z) ∨
          z = rightPoint n (rainbowLabel n z) := by
      unfold rainbowLabel
      split_ifs
      · left; apply Fin.ext; rfl
      · right
        apply Fin.ext
        have := z.isLt
        simp [rightPoint, leftPoint]; omega
    have hinv (r : TwoDownPrefix n) (i : Fin n) :
        (halfMateFin r) ((halfMateFin r) i) = i := by
      apply Fin.ext
      exact (halfMate_involutive r) i.val
    have hnonfixed (r : TwoDownPrefix n) (i : Fin n)
        (hi : i ∉ (unmatchedPositions r)) :
        (halfMateFin r) i ∉ (unmatchedPositions r) := by
      intro hmate
      have hfix := ((halfMateFin_fixed_iff r) ((halfMateFin r) i)).2 hmate
      have hback := hinv r i
      have heq : (halfMateFin r) i = i := (hback.symm.trans hfix).symm
      exact hi (((halfMateFin_fixed_iff r) i).1 heq)
    have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
        if hi : i ∈ (unmatchedPositions p) then
          rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
        else leftPoint n ((halfMateFin p) i) := by
      simp [joinedMate, rainbowLabel, leftPoint]
    have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
        if hj : j ∈ (unmatchedPositions q) then
          leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
        else rightPoint n ((halfMateFin q) j) := by
      have hright : ¬ (rightPoint n j).val < n := by
        have hj := j.isLt
        have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have hlabel : rainbowLabel n (rightPoint n j) = j := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp [joinedMate, hright, hlabel]
    rcases hpoint x with hleft | hright
    · rw [hleft]
      let i := rainbowLabel n x
      change (joinedMate p) q ((joinedMate p) q (leftPoint n i)) = leftPoint n i
      by_cases hi : i ∈ (unmatchedPositions p)
      · have hj : ((rankJoin p) q ⟨i, hi⟩).1 ∈ (unmatchedPositions q) :=
          ((rankJoin p) q ⟨i, hi⟩).2
        rw [joinedMate_left, dif_pos hi, joinedMate_right, dif_pos hj]
        simp
      · have hm := hnonfixed p i hi
        rw [joinedMate_left, dif_neg hi, joinedMate_left, dif_neg hm,
          hinv p i]
    · rw [hright]
      let j := rainbowLabel n x
      change (joinedMate p) q ((joinedMate p) q (rightPoint n j)) = rightPoint n j
      by_cases hj : j ∈ (unmatchedPositions q)
      · have hi : (((rankJoin p) q).symm ⟨j, hj⟩).1 ∈ (unmatchedPositions p) :=
          (((rankJoin p) q).symm ⟨j, hj⟩).2
        rw [joinedMate_right, dif_pos hj, joinedMate_left, dif_pos hi]
        simp
      · have hm := hnonfixed q j hj
        rw [joinedMate_right, dif_neg hj, joinedMate_right, dif_neg hm,
          hinv q j]

  have joinedMate_ne {n : ℕ}
      (p q : TwoDownPrefix n) (x : Fin (2 * n)) :
      (joinedMate p) q x ≠ x := by
    have hpoint (z : Fin (2 * n)) :
        z = leftPoint n (rainbowLabel n z) ∨
          z = rightPoint n (rainbowLabel n z) := by
      unfold rainbowLabel
      split_ifs
      · left; apply Fin.ext; rfl
      · right
        apply Fin.ext
        have := z.isLt
        simp [rightPoint, leftPoint]; omega
    have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
        if hi : i ∈ (unmatchedPositions p) then
          rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
        else leftPoint n ((halfMateFin p) i) := by
      simp [joinedMate, rainbowLabel, leftPoint]
    have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
        if hj : j ∈ (unmatchedPositions q) then
          leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
        else rightPoint n ((halfMateFin q) j) := by
      have hright : ¬ (rightPoint n j).val < n := by
        have hj := j.isLt
        have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have hlabel : rainbowLabel n (rightPoint n j) = j := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp [joinedMate, hright, hlabel]
    have right_ge (j : Fin n) : n ≤ (rightPoint n j).val := by
      have hj := j.isLt
      have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
        simp [rightPoint, leftPoint]
      omega
    rcases hpoint x with hleft | hright
    · rw [hleft]
      let i := rainbowLabel n x
      change (joinedMate p) q (leftPoint n i) ≠ leftPoint n i
      by_cases hi : i ∈ (unmatchedPositions p)
      · rw [joinedMate_left, dif_pos hi]
        intro heq
        have hl : (rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)).val < n := by
          rw [heq]
          exact i.isLt
        exact (not_lt_of_ge (right_ge _)) hl
      · rw [joinedMate_left, dif_neg hi]
        intro heq
        have hv := congrArg (rainbowLabel n) heq
        have hfix : (halfMateFin p) i = i := by
          simpa [rainbowLabel, leftPoint] using hv
        exact hi (((halfMateFin_fixed_iff p) i).1 hfix)
    · rw [hright]
      let j := rainbowLabel n x
      change (joinedMate p) q (rightPoint n j) ≠ rightPoint n j
      by_cases hj : j ∈ (unmatchedPositions q)
      · rw [joinedMate_right, dif_pos hj]
        intro heq
        have hv : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
          (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
        rw [heq] at hv
        exact (not_lt_of_ge (right_ge j)) hv
      · rw [joinedMate_right, dif_neg hj]
        intro heq
        have hv := congrArg (rainbowLabel n) heq
        have hlabel (k : Fin n) : rainbowLabel n (rightPoint n k) = k := by
          unfold rightPoint; rw [rainbowLabel_rev]
          simp [rainbowLabel, leftPoint]
        simp only [hlabel] at hv
        exact hj (((halfMateFin_fixed_iff q) j).1 hv)

  have joinedMate_noncrossing {n : ℕ}
      (p q : TwoDownPrefix n) (a b : Fin (2 * n))
      (hab : a.val < b.val)
      (hbetween : b.val < ((joinedMate p) q a).val)
      (hends : ((joinedMate p) q a).val < ((joinedMate p) q b).val) : False := by
    have hpoint (z : Fin (2 * n)) :
        z = leftPoint n (rainbowLabel n z) ∨
          z = rightPoint n (rainbowLabel n z) := by
      unfold rainbowLabel
      split_ifs
      · left; apply Fin.ext; rfl
      · right
        apply Fin.ext
        have := z.isLt
        simp [rightPoint, leftPoint]; omega
    have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
        if hi : i ∈ (unmatchedPositions p) then
          rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
        else leftPoint n ((halfMateFin p) i) := by
      simp [joinedMate, rainbowLabel, leftPoint]
    have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
        if hj : j ∈ (unmatchedPositions q) then
          leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
        else rightPoint n ((halfMateFin q) j) := by
      have hright : ¬ (rightPoint n j).val < n := by
        have hj := j.isLt
        have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have hlabel : rainbowLabel n (rightPoint n j) = j := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp [joinedMate, hright, hlabel]
    have right_val (i : Fin n) :
        (rightPoint n i).val = 2 * n - (i.val + 1) := by
      simp [rightPoint, leftPoint]
    have right_ge (i : Fin n) : n ≤ (rightPoint n i).val := by
      have := i.isLt
      rw [right_val]
      omega
    rcases hpoint a with ha | ha <;>
      rcases hpoint b with hb | hb
    · let i := rainbowLabel n a
      let j := rainbowLabel n b
      rw [ha, hb] at hab hbetween hends
      change (leftPoint n i).val < (leftPoint n j).val at hab
      change (leftPoint n j).val < ((joinedMate p) q (leftPoint n i)).val at hbetween
      change ((joinedMate p) q (leftPoint n i)).val <
        ((joinedMate p) q (leftPoint n j)).val at hends
      have hij : i.val < j.val := by simpa [leftPoint] using hab
      by_cases hi : i ∈ (unmatchedPositions p)
      · rw [joinedMate_left, dif_pos hi] at hbetween hends
        by_cases hj : j ∈ (unmatchedPositions p)
        · rw [joinedMate_left, dif_pos hj] at hends
          have horder : ((rankJoin p) q ⟨i, hi⟩).1.val <
              ((rankJoin p) q ⟨j, hj⟩).1.val := by
            exact ((rankJoin p) q).strictMono hij
          simp only [right_val] at hends
          have hk := ((rankJoin p) q ⟨i, hi⟩).1.isLt
          have hl := ((rankJoin p) q ⟨j, hj⟩).1.isLt
          omega
        · rw [joinedMate_left, dif_neg hj] at hends
          have hl : (leftPoint n ((halfMateFin p) j)).val < n :=
            ((halfMateFin p) j).isLt
          exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
      · rw [joinedMate_left, dif_neg hi] at hbetween hends
        have hinside : j.val < (halfMate p) i.val := by
          simpa [leftPoint, halfMateFin] using hbetween
        have hinterval := (halfMate_interval p) i j hij hinside
        have hj : j ∉ (unmatchedPositions p) := by
          intro hj
          have hfix := ((halfMateFin_fixed_iff p) j).2 hj
          exact hinterval.1 (congrArg Fin.val hfix)
        rw [joinedMate_left, dif_neg hj] at hends
        have hreverse : (halfMate p) i.val < (halfMate p) j.val := by
          simpa [leftPoint, halfMateFin] using hends
        omega
    · let i := rainbowLabel n a
      let j := rainbowLabel n b
      rw [ha, hb] at hab hbetween hends
      change (leftPoint n i).val < (rightPoint n j).val at hab
      change (rightPoint n j).val < ((joinedMate p) q (leftPoint n i)).val at hbetween
      change ((joinedMate p) q (leftPoint n i)).val <
        ((joinedMate p) q (rightPoint n j)).val at hends
      by_cases hi : i ∈ (unmatchedPositions p)
      · rw [joinedMate_left, dif_pos hi] at hbetween hends
        by_cases hj : j ∈ (unmatchedPositions q)
        · rw [joinedMate_right, dif_pos hj] at hends
          have hl : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
            (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
          exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
        · rw [joinedMate_right, dif_neg hj] at hends
          let k : Fin n := ((rankJoin p) q ⟨i, hi⟩).1
          have hk : k ∈ (unmatchedPositions q) :=
            ((rankJoin p) q ⟨i, hi⟩).2
          have hkj : k.val < j.val := by
            simp only [right_val] at hbetween
            have hklt := k.isLt
            have hjlt := j.isLt
            omega
          have hmj : ((halfMateFin q) j).val < k.val := by
            simp only [right_val] at hends
            have hklt := k.isLt
            have hmlt := ((halfMateFin q) j).isLt
            omega
          let u := (halfMateFin q) j
          have hinterval : k.val < (halfMate q) u.val := by
            simpa [u, halfMateFin, (halfMate_involutive q)] using hkj
          have hfixed := ((halfMateFin_fixed_iff q) k).2 hk
          exact ((halfMate_interval q) u k hmj hinterval).1
            (congrArg Fin.val hfixed)
      · rw [joinedMate_left, dif_neg hi] at hbetween
        have hl : (leftPoint n ((halfMateFin p) i)).val < n :=
          ((halfMateFin p) i).isLt
        exact (not_lt_of_ge (right_ge j)) (lt_trans hbetween hl)
    · let i := rainbowLabel n a
      let j := rainbowLabel n b
      rw [ha, hb] at hab
      have hl : (leftPoint n j).val < n := j.isLt
      exact (not_lt_of_ge (right_ge i)) (lt_trans hab hl)
    · let i := rainbowLabel n a
      let j := rainbowLabel n b
      rw [ha, hb] at hab hbetween hends
      change (rightPoint n i).val < (rightPoint n j).val at hab
      change (rightPoint n j).val < ((joinedMate p) q (rightPoint n i)).val at hbetween
      change ((joinedMate p) q (rightPoint n i)).val <
        ((joinedMate p) q (rightPoint n j)).val at hends
      have hji : j.val < i.val := by
        simp only [right_val] at hab
        have hi := i.isLt
        have hj := j.isLt
        omega
      by_cases hi : i ∈ (unmatchedPositions q)
      · rw [joinedMate_right, dif_pos hi] at hbetween
        have hl : (leftPoint n (((rankJoin p) q).symm ⟨i, hi⟩).1).val < n :=
          (((rankJoin p) q).symm ⟨i, hi⟩).1.isLt
        exact (not_lt_of_ge (right_ge j)) (lt_trans hbetween hl)
      · rw [joinedMate_right, dif_neg hi] at hbetween hends
        by_cases hj : j ∈ (unmatchedPositions q)
        · rw [joinedMate_right, dif_pos hj] at hends
          have hl : (leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1).val < n :=
            (((rankJoin p) q).symm ⟨j, hj⟩).1.isLt
          exact (not_lt_of_ge (right_ge _)) (lt_trans hends hl)
        · rw [joinedMate_right, dif_neg hj] at hends
          have huj : ((halfMateFin q) i).val < j.val := by
            simp only [right_val] at hbetween
            have hu := ((halfMateFin q) i).isLt
            have hjlt := j.isLt
            omega
          have hvu : ((halfMateFin q) j).val < ((halfMateFin q) i).val := by
            simp only [right_val] at hends
            have hu := ((halfMateFin q) i).isLt
            have hv := ((halfMateFin q) j).isLt
            omega
          let v := (halfMateFin q) j
          let u := (halfMateFin q) i
          have hbackj : (halfMate q) v.val = j.val := by
            simp [v, halfMateFin, (halfMate_involutive q)]
          have hinterval : u.val < (halfMate q) v.val := by
            rw [hbackj]
            exact huj
          have hnest := ((halfMate_interval q) v u hvu hinterval).2
          have hbacki : (halfMate q) u.val = i.val := by
            simp [u, halfMateFin, (halfMate_involutive q)]
          omega

  -- Join unmatched positions by rank to reconstruct the source involution.
  let fromPrefixes {n : ℕ} (p q : TwoDownPrefix n) :
      UpperMatching n :=
    {
      mate := (joinedMate p) q
      mate_mate := (joinedMate_involutive p) q
      mate_ne := (joinedMate_ne p) q
      noncrossing := (joinedMate_noncrossing p) q
    }

  have fromPrefixes_leftCut {n : ℕ} (p q : TwoDownPrefix n)
      (x : Fin n) : (leftCut (fromPrefixes p q)) x = (halfCut p) x := by
    have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
        if hi : i ∈ (unmatchedPositions p) then
          rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
        else leftPoint n ((halfMateFin p) i) := by
      simp [joinedMate, rainbowLabel, leftPoint]
    by_cases hx : x ∈ (unmatchedPositions p)
    · have hnone : (halfCut p) x = none :=
        (Finset.mem_filter.mp hx).2
      have hright : n ≤ (rightPoint n (((rankJoin p) q ⟨x, hx⟩).1)).val := by
        have hy := (((rankJoin p) q ⟨x, hx⟩).1).isLt
        have hv : (rightPoint n (((rankJoin p) q ⟨x, hx⟩).1)).val =
            2 * n - ((((rankJoin p) q ⟨x, hx⟩).1).val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      rw [hnone]
      have hcross : n ≤ ((fromPrefixes p q).mate (leftPoint n x)).val := by
        change n ≤ ((joinedMate p) q (leftPoint n x)).val
        rw [joinedMate_left, dif_pos hx]
        exact hright
      simpa [leftCut] using hcross
    · have hne : (halfMate p) x.val ≠ x.val := by
        intro hfix
        apply hx
        exact ((halfMateFin_fixed_iff p) x).mp (Fin.ext hfix)
      have hmate : (fromPrefixes p q).mate (leftPoint n x) =
          leftPoint n ((halfMateFin p) x) := by
        exact (joinedMate_left x).trans (dif_neg hx)
      have hcut := (leftCut_eq_some_iff (fromPrefixes p q)
        x ((halfMateFin p) x)).2 hmate
      simpa [halfCut, hne, halfMateFin] using hcut

  have fromPrefixes_rightCut {n : ℕ} (p q : TwoDownPrefix n)
      (x : Fin n) : (rightCut (fromPrefixes p q)) x = (halfCut q) x := by
    have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
        if hj : j ∈ (unmatchedPositions q) then
          leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
        else rightPoint n ((halfMateFin q) j) := by
      have hright : ¬ (rightPoint n j).val < n := by
        have hj := j.isLt
        have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have hlabel : rainbowLabel n (rightPoint n j) = j := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp [joinedMate, hright, hlabel]
    by_cases hx : x ∈ (unmatchedPositions q)
    · have hnone : (halfCut q) x = none :=
        (Finset.mem_filter.mp hx).2
      have hleft : n ≤ (leftPoint n (((rankJoin p) q).symm ⟨x, hx⟩).1).rev.val := by
        have hy := ((((rankJoin p) q).symm ⟨x, hx⟩).1).isLt
        have hv : (leftPoint n ((((rankJoin p) q).symm ⟨x, hx⟩).1)).rev.val =
            2 * n - (((((rankJoin p) q).symm ⟨x, hx⟩).1).val + 1) := by
          simp [leftPoint]
        omega
      rw [hnone]
      have hcross : n ≤ ((fromPrefixes p q).mate (rightPoint n x)).rev.val := by
        change n ≤ ((joinedMate p) q (rightPoint n x)).rev.val
        rw [joinedMate_right, dif_pos hx]
        exact hleft
      simpa [rightCut] using hcross
    · have hne : (halfMate q) x.val ≠ x.val := by
        intro hfix
        apply hx
        exact ((halfMateFin_fixed_iff q) x).mp (Fin.ext hfix)
      have hmate : (fromPrefixes p q).mate (rightPoint n x) =
          rightPoint n ((halfMateFin q) x) := by
        exact (joinedMate_right x).trans (dif_neg hx)
      have hcut := (rightCut_eq_some_iff (fromPrefixes p q)
        x ((halfMateFin q) x)).2 hmate
      simpa [halfCut, hne, halfMateFin] using hcut

  have fromPrefixes_eq_of_cuts {n : ℕ} (M : UpperMatching n)
      (p q : TwoDownPrefix n)
      (hp : ∀ x, (leftCut M) x = (halfCut p) x)
      (hq : ∀ x, (rightCut M) x = (halfCut q) x) :
      fromPrefixes p q = M := by
    have hpoint (z : Fin (2 * n)) :
        z = leftPoint n (rainbowLabel n z) ∨
          z = rightPoint n (rainbowLabel n z) := by
      unfold rainbowLabel
      split_ifs
      · left; apply Fin.ext; rfl
      · right
        apply Fin.ext
        have := z.isLt
        simp [rightPoint, leftPoint]; omega
    have joinedMate_left (i : Fin n) : (joinedMate p) q (leftPoint n i) =
        if hi : i ∈ (unmatchedPositions p) then
          rightPoint n (((rankJoin p) q ⟨i, hi⟩).1)
        else leftPoint n ((halfMateFin p) i) := by
      simp [joinedMate, rainbowLabel, leftPoint]
    have joinedMate_right (j : Fin n) : (joinedMate p) q (rightPoint n j) =
        if hj : j ∈ (unmatchedPositions q) then
          leftPoint n (((rankJoin p) q).symm ⟨j, hj⟩).1
        else rightPoint n ((halfMateFin q) j) := by
      have hright : ¬ (rightPoint n j).val < n := by
        have hj := j.isLt
        have hv : (rightPoint n j).val = 2 * n - (j.val + 1) := by
          simp [rightPoint, leftPoint]
        omega
      have hlabel : rainbowLabel n (rightPoint n j) = j := by
        unfold rightPoint; rw [rainbowLabel_rev]
        simp [rainbowLabel, leftPoint]
      simp [joinedMate, hright, hlabel]
    have hmate (x : Fin (2 * n)) :
        (fromPrefixes p q).mate x = M.mate x := by
      rcases hpoint x with hx | hx
      · rw [hx]
        let i := rainbowLabel n x
        change (joinedMate p) q (leftPoint n i) = M.mate (leftPoint n i)
        by_cases hi : i ∈ (unmatchedPositions p)
        · have hnone : (leftCut M) i = none := by
            rw [hp i]
            exact (Finset.mem_filter.mp hi).2
          rw [joinedMate_left, dif_pos hi]
          exact crossing_eq_rankJoin M p q hp hq i hnone
        · have hne : (halfMate p) i.val ≠ i.val := by
            intro hfix
            apply hi
            exact ((halfMateFin_fixed_iff p) i).mp (Fin.ext hfix)
          have hcut : (halfCut p) i = some ((halfMateFin p) i) := by
            simp [halfCut, hne, halfMateFin]
          have hsource : M.mate (leftPoint n i) =
              leftPoint n ((halfMateFin p) i) := by
            exact (leftCut_eq_some_iff M i ((halfMateFin p) i)).1
              ((hp i).trans hcut)
          rw [joinedMate_left, dif_neg hi]
          exact hsource.symm
      · rw [hx]
        let j := rainbowLabel n x
        change (joinedMate p) q (rightPoint n j) = M.mate (rightPoint n j)
        by_cases hj : j ∈ (unmatchedPositions q)
        · let i : Fin n := (((rankJoin p) q).symm ⟨j, hj⟩).1
          have hi : i ∈ (unmatchedPositions p) :=
            (((rankJoin p) q).symm ⟨j, hj⟩).2
          have hnone : (leftCut M) i = none := by
            rw [hp i]
            exact (Finset.mem_filter.mp hi).2
          have hcross := crossing_eq_rankJoin M p q hp hq i hnone
          have hrank : ((rankJoin p) q ⟨i, hi⟩).1 = j := by
            exact congrArg Subtype.val
              (((rankJoin p) q).apply_symm_apply ⟨j, hj⟩)
          rw [hrank] at hcross
          have hback := congrArg M.mate hcross
          rw [M.mate_mate] at hback
          rw [joinedMate_right, dif_pos hj]
          exact hback.symm
        · have hne : (halfMate q) j.val ≠ j.val := by
            intro hfix
            apply hj
            exact ((halfMateFin_fixed_iff q) j).mp (Fin.ext hfix)
          have hcut : (halfCut q) j = some ((halfMateFin q) j) := by
            simp [halfCut, hne, halfMateFin]
          have hsource : M.mate (rightPoint n j) =
              rightPoint n ((halfMateFin q) j) := by
            exact (rightCut_eq_some_iff M j ((halfMateFin q) j)).1
              ((hq j).trans hcut)
          rw [joinedMate_right, dif_neg hj]
          exact hsource.symm
    cases M with
    | mk mate mate_mate mate_ne noncrossing =>
      cases h : fromPrefixes p q with
      | mk mate' mate_mate' mate_ne' noncrossing' =>
        have heq : mate' = mate := by
          funext x
          simpa only [h] using hmate x
        cases heq
        rfl

  let prefixPairWitness {n : ℕ}
      (M : UpperMatching n) (hn : 4 ≤ n) (hw : M.winding = n - 4) :
      {pq : TwoDownPrefix n × TwoDownPrefix n //
        (∀ x, (leftCut M) x = (halfCut pq.1) x) ∧
        (∀ x, (rightCut M) x = (halfCut pq.2) x)} := by
    classical
    let hleft : ∃ p : TwoDownPrefix n, ∀ x, (leftCut M) x = (halfCut p) x :=
      four_endpoint_twoDownPrefix
      (leftCut_paired_card_four M hn hw)
      (leftCut_symmetric M)
      (four_endpoint_adjacent_or_nested (leftCut_paired_card_four M hn hw)
        (leftCut_between_paired M) (leftCut_arch_span_le_three M hn hw)
        (leftCut_four_endpoint_pairing_shape M hn hw))
    let hright : ∃ q : TwoDownPrefix n, ∀ x, (rightCut M) x = (halfCut q) x :=
      four_endpoint_twoDownPrefix
      (rightCut_paired_card_four M hn hw)
      (rightCut_symmetric M)
      (four_endpoint_adjacent_or_nested (rightCut_paired_card_four M hn hw)
        (rightCut_between_paired M) (rightCut_arch_span_le_three M hn hw)
        (leftCut_four_endpoint_pairing_shape (reflected M) hn
          (by
            have hreflect : (reflected M).winding = M.winding := by
              calc
                (reflected M).winding =
                    (Finset.univ.filter fun x : Fin n =>
                      (leftCut (reflected M)) x = none).card :=
                  by simp [UpperMatching.winding, leftCut, leftPoint]
                _ = (Finset.univ.filter fun x : Fin n =>
                      (rightCut M) x = none).card := by rfl
                _ = M.winding := (winding_eq_rightCut_none_card M).symm
            rw [hreflect, hw])))
    exact ⟨(Classical.choose hleft, Classical.choose hright),
      Classical.choose_spec hleft, Classical.choose_spec hright⟩

  let sourcePrefixEquiv (n : ℕ) (hn : 4 ≤ n) :
      {M : UpperMatching n // M.winding = n - 4} ≃
        TwoDownPrefix n × TwoDownPrefix n :=
    {
      toFun M := ((prefixPairWitness M.1) hn M.2).1
      invFun pq := ⟨fromPrefixes pq.1 pq.2, by
        have hleft : (fromPrefixes pq.1 pq.2).winding =
            (Finset.univ.filter fun x : Fin n =>
              (leftCut (fromPrefixes pq.1 pq.2)) x = none).card := by
          simp [UpperMatching.winding, leftCut, leftPoint]
        rw [hleft]
        simpa [unmatchedPositions, fromPrefixes_leftCut] using
          (unmatchedPositions_card pq.1)⟩
      left_inv M := by
        exact Subtype.ext (fromPrefixes_eq_of_cuts M.1
          ((prefixPairWitness M.1) hn M.2).1.1
          ((prefixPairWitness M.1) hn M.2).1.2
          ((prefixPairWitness M.1) hn M.2).2.1
          ((prefixPairWitness M.1) hn M.2).2.2)
      right_inv pq := by
        have hw : (fromPrefixes pq.1 pq.2).winding = n - 4 := by
          have hleft : (fromPrefixes pq.1 pq.2).winding =
              (Finset.univ.filter fun x : Fin n =>
                (leftCut (fromPrefixes pq.1 pq.2)) x = none).card := by
            simp [UpperMatching.winding, leftCut, leftPoint]
          rw [hleft]
          simpa [unmatchedPositions, fromPrefixes_leftCut] using
            (unmatchedPositions_card pq.1)
        let w := (prefixPairWitness (fromPrefixes pq.1 pq.2))
          hn hw
        change w.1 = pq
        apply Prod.ext
        · exact halfCut_injective w.1.1 pq.1
            (fun x => (w.2.1 x).symm.trans (fromPrefixes_leftCut pq.1 pq.2 x))
        · exact halfCut_injective w.1.2 pq.2
            (fun x => (w.2.2 x).symm.trans (fromPrefixes_rightCut pq.1 pq.2 x))
    }

  let connectedSourcePrefixEquiv (n : ℕ) (hn : 4 ≤ n) :
      {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} ≃
        {pq : TwoDownPrefix n × TwoDownPrefix n //
          ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j} :=
    (sourcePrefixEquiv n hn).subtypeEquiv (by
      intro M
      let w := (prefixPairWitness M.1) hn M.2
      let pq := w.1
      have hp : ∀ x, (leftCut M.1) x = (halfCut pq.1) x := w.2.1
      have hq : ∀ x, (rightCut M.1) x = (halfCut pq.2) x := w.2.2
      change M.1.oneLoop ↔ ∀ i j : Fin n,
        Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j
      rw [oneLoop_iff_contracted_connected]
      constructor
      · intro h i j
        exact (Relation.ReflTransGen.mono
          (fun a b hab =>
            (contractedEdge_iff_joinedEdge M.1 pq.1 pq.2 hp hq a b).1 hab)) i j
          (h i j)
      · intro h i j
        exact (Relation.ReflTransGen.mono
          (fun a b hab =>
            (contractedEdge_iff_joinedEdge M.1 pq.1 pq.2 hp hq a b).2 hab)) i j
          (h i j))

  -- Extreme obstructions lead to the exhaustive A/B/C connectivity split.
  have joinedEdge_fixed_isolated {n : ℕ}
      (p q : TwoDownPrefix n) (x : Fin n)
      (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
      (hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x)
      {y : Fin n} (hxy : (joinedEdge p) q x y) : y = x := by
    have hpnone : (halfCut p) x = none :=
      (Finset.mem_filter.mp hp).2
    have hqnone : (halfCut q) x = none :=
      (Finset.mem_filter.mp hq).2
    rcases hxy with hxy | hxy | ⟨_, hxy⟩ | ⟨hy, hxy⟩
    · rw [hpnone] at hxy
      cases hxy
    · rw [hqnone] at hxy
      cases hxy
    · exact hxy.symm.trans hfix
    · have heq : (⟨y, hy⟩ : (unmatchedPositions p)) = ⟨x, hp⟩ := by
        apply ((rankJoin p) q).injective
        apply Subtype.ext
        exact hxy.trans hfix.symm
      exact congrArg Subtype.val heq

  have not_connected_of_fixed_rankJoin {n : ℕ}
      (p q : TwoDownPrefix n) (x y : Fin n) (hxy : x ≠ y)
      (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
      (hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x) :
      ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
    intro hconn
    have hstay : ∀ z : Fin n,
        Relation.ReflTransGen ((joinedEdge p) q) x z → z = x := by
      intro z hpath
      have preserved : x = x → z = x :=
        Relation.ReflTransGen.head_induction_on
          (motive := fun a _ => a = x → z = x) hpath
          (fun ha => ha)
          (fun hab _ ih ha => by
            cases ha
            exact ih ((joinedEdge_fixed_isolated p) q x hp hq hfix hab))
      exact preserved rfl
    exact hxy (hstay y (hconn x y)).symm

  have rankJoin_least_fixed {n : ℕ}
      (p q : TwoDownPrefix n) (x : Fin n)
      (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
      (hpmin : ∀ y : (unmatchedPositions p), x ≤ y.1)
      (hqmin : ∀ y : (unmatchedPositions q), x ≤ y.1) :
      ((rankJoin p) q ⟨x, hp⟩).1 = x := by
    let xp : (unmatchedPositions p) := ⟨x, hp⟩
    let xq : (unmatchedPositions q) := ⟨x, hq⟩
    obtain ⟨z, hz⟩ := ((rankJoin p) q).surjective xq
    have hle : ((rankJoin p) q) xp ≤ xq := by
      rw [← hz]
      exact ((rankJoin p) q).monotone (hpmin z)
    have hge : xq ≤ ((rankJoin p) q) xp := hqmin _
    exact congrArg Subtype.val (le_antisymm hle hge)

  have rankJoin_greatest_fixed {n : ℕ}
      (p q : TwoDownPrefix n) (x : Fin n)
      (hp : x ∈ (unmatchedPositions p)) (hq : x ∈ (unmatchedPositions q))
      (hpmax : ∀ y : (unmatchedPositions p), y.1 ≤ x)
      (hqmax : ∀ y : (unmatchedPositions q), y.1 ≤ x) :
      ((rankJoin p) q ⟨x, hp⟩).1 = x := by
    let xp : (unmatchedPositions p) := ⟨x, hp⟩
    let xq : (unmatchedPositions q) := ⟨x, hq⟩
    obtain ⟨z, hz⟩ := ((rankJoin p) q).surjective xq
    have hle : ((rankJoin p) q) xp ≤ xq := hqmax _
    have hge : xq ≤ ((rankJoin p) q) xp := by
      rw [← hz]
      exact ((rankJoin p) q).monotone (hpmax z)
    exact congrArg Subtype.val (le_antisymm hle hge)

  have connected_extremes_paired {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 4 ≤ n)
      (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) :
      ¬ (⟨0, by omega⟩ ∈ (unmatchedPositions p) ∧
         ⟨0, by omega⟩ ∈ (unmatchedPositions q)) ∧
      ¬ (⟨n - 1, by omega⟩ ∈ (unmatchedPositions p) ∧
         ⟨n - 1, by omega⟩ ∈ (unmatchedPositions q)) := by
    constructor
    · rintro ⟨hp, hq⟩
      let x : Fin n := ⟨0, by omega⟩
      let y : Fin n := ⟨1, by omega⟩
      have hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x :=
        (rankJoin_least_fixed p) q x hp hq
          (fun z => by change 0 ≤ z.1.val; omega)
          (fun z => by change 0 ≤ z.1.val; omega)
      exact ((not_connected_of_fixed_rankJoin p) q x y
        (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega)
        hp hq hfix) hconn
    · rintro ⟨hp, hq⟩
      let x : Fin n := ⟨n - 1, by omega⟩
      let y : Fin n := ⟨0, by omega⟩
      have hfix : ((rankJoin p) q ⟨x, hp⟩).1 = x :=
        (rankJoin_greatest_fixed p) q x hp hq
          (fun z => by change z.1.val ≤ n - 1; have := z.1.isLt; omega)
          (fun z => by change z.1.val ≤ n - 1; have := z.1.isLt; omega)
      exact ((not_connected_of_fixed_rankJoin p) q x y
        (by intro h; have := congrArg Fin.val h; dsimp [x, y] at this; omega)
        hp hq hfix) hconn

  have connected_endpoint_cases {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 4 ≤ n)
      (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) :
      (p.val.1 = 1 ∨ (p.val.1 = 2 ∧ p.val.2 = 3) ∨
        q.val.1 = 1 ∨ (q.val.1 = 2 ∧ q.val.2 = 3)) ∧
      (p.val.2 = n - 1 ∨ q.val.2 = n - 1) := by
    obtain ⟨hzero, hlast⟩ := (connected_extremes_paired p) q hn hconn
    have hzero_iff (r : TwoDownPrefix n) :
        (⟨0, by have := r.property.2.2.2; omega⟩ : Fin n) ∈ (unmatchedPositions r) ↔
          r.val.1 ≠ 1 ∧ ¬ (r.val.1 = 2 ∧ r.val.2 = 3) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff r)]
      dsimp
      unfold secondOpen
      split_ifs with h
      · have := r.property.1
        have := r.property.2.1
        omega
      · have := r.property.1
        have := r.property.2.1
        have := r.property.2.2.1
        omega
    have hlast_iff (r : TwoDownPrefix n) :
        (⟨n - 1, by have := r.property.2.2.2; omega⟩ : Fin n) ∈
          (unmatchedPositions r) ↔ r.val.2 ≠ n - 1 := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff r)]
      dsimp
      unfold secondOpen
      split_ifs with h <;>
        have := r.property.1 <;>
        have := r.property.2.2.1 <;>
        have := r.property.2.2.2 <;>
        omega
    constructor
    · by_contra h
      have hpq : (p.val.1 ≠ 1 ∧ ¬ (p.val.1 = 2 ∧ p.val.2 = 3)) ∧
          (q.val.1 ≠ 1 ∧ ¬ (q.val.1 = 2 ∧ q.val.2 = 3)) := by tauto
      exact hzero ⟨(hzero_iff p).2 hpq.1,
        (hzero_iff q).2 hpq.2⟩
    · by_contra h
      have hpq : p.val.2 ≠ n - 1 ∧ q.val.2 ≠ n - 1 := by tauto
      exact hlast ⟨(hlast_iff p).2 hpq.1,
        (hlast_iff q).2 hpq.2⟩

  have rankJoin_B_closed_bound {n : ℕ} (p q : TwoDownPrefix n)
      (hp1 : p.val.1 = 1)
      (hsep : q.val.1 + 2 ≤ q.val.2)
      (i : Fin n) (hi : i.val ≤ q.val.1)
      (hpi : i ∈ (unmatchedPositions p)) :
      ((rankJoin p) q ⟨i, hpi⟩).1.val ≤ q.val.1 := by
    have hqfirst : 1 ≤ q.val.1 := q.property.1
    have hqsecond : q.val.2 < n := q.property.2.2.2
    have hpi_none : (halfCut p) i = none := (Finset.mem_filter.mp hpi).2
    have hpnone := ((halfCut_eq_none_iff p) i).1 hpi_none
    have hi2 : 2 ≤ i.val := by
      rw [hp1] at hpnone
      omega
    by_contra hgt'
    have hgt : q.val.1 < ((rankJoin p) q ⟨i, hpi⟩).1.val := by omega
    have hc2 : 2 ≤ q.val.1 := by omega
    let c : ℕ := q.val.1
    let y : (unmatchedPositions q) := (rankJoin p) q ⟨i, hpi⟩
    let f : Fin (c - 1) → Fin (c - 2) := fun k => by
      let qk : (unmatchedPositions q) := ⟨⟨k.val, by have := k.isLt; omega⟩, by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [(halfCut_eq_none_iff q)]
        unfold secondOpen
        split_ifs <;> have hk := k.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
      let z : (unmatchedPositions p) := ((rankJoin p) q).symm qk
      have hzlt : z.1.val < i.val := by
        have hzorder : z < (⟨i, hpi⟩ : (unmatchedPositions p)) := by
          apply ((rankJoin p) q).lt_iff_lt.mp
          have hqk : qk.1.val < y.1.val := by
            dsimp [qk, y, c]
            have hk := k.isLt
            omega
          have hmap : ((rankJoin p) q) z <
              ((rankJoin p) q) (⟨i, hpi⟩ : (unmatchedPositions p)) := by
            simpa [z, y] using hqk
          exact hmap
        change z.1.val < i.val at hzorder
        exact hzorder
      have hz2 : 2 ≤ z.1.val := by
        have hznone : (halfCut p) z.1 = none := (Finset.mem_filter.mp z.2).2
        have hzp := ((halfCut_eq_none_iff p) z.1).1 hznone
        rw [hp1] at hzp
        omega
      exact ⟨z.1.val - 2, by dsimp [c]; omega⟩
    have hf : Function.Injective f := by
      intro k₁ k₂ heq
      dsimp [f] at heq
      let q₁ : (unmatchedPositions q) := ⟨⟨k₁.val, by have := k₁.isLt; omega⟩, by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [(halfCut_eq_none_iff q)]
        unfold secondOpen
        split_ifs <;> have hk := k₁.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
      let q₂ : (unmatchedPositions q) := ⟨⟨k₂.val, by have := k₂.isLt; omega⟩, by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [(halfCut_eq_none_iff q)]
        unfold secondOpen
        split_ifs <;> have hk := k₂.isLt <;> dsimp [c] at hk ⊢ <;> omega⟩
      let z₁ : (unmatchedPositions p) := ((rankJoin p) q).symm q₁
      let z₂ : (unmatchedPositions p) := ((rankJoin p) q).symm q₂
      have hz₁2 : 2 ≤ z₁.1.val := by
        have hznone := ((halfCut_eq_none_iff p) z₁.1).1 (Finset.mem_filter.mp z₁.2).2
        rw [hp1] at hznone
        omega
      have hz₂2 : 2 ≤ z₂.1.val := by
        have hznone := ((halfCut_eq_none_iff p) z₂.1).1 (Finset.mem_filter.mp z₂.2).2
        rw [hp1] at hznone
        omega
      have hz₁eq₂ : z₁.1.val = z₂.1.val := by
        have hv := congrArg Fin.val heq
        dsimp [z₁, z₂, q₁, q₂] at hv
        have hv' : z₁.1.val - 2 = z₂.1.val - 2 := by
          simpa [z₁, z₂, q₁, q₂] using hv
        omega
      have hq₁eq₂ : q₁ = q₂ := by
        have hz : z₁ = z₂ := by
          apply Subtype.ext
          exact Fin.ext hz₁eq₂
        apply ((rankJoin p) q).symm.injective
        simpa [z₁, z₂] using hz
      have hk : k₁.val = k₂.val := by
        have hv : q₁.1 = q₂.1 := congrArg Subtype.val hq₁eq₂
        have hv' := congrArg Fin.val hv
        dsimp [q₁, q₂] at hv'
        exact hv'
      exact Fin.ext hk
    have hcard := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin] at hcard
    omega

  have p_edge_B_closed {n : ℕ} (p q : TwoDownPrefix n)
      (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
      (hsep : q.val.1 + 2 ≤ q.val.2)
      (i : Fin n) (hi : i.val ≤ q.val.1) {j : Fin n}
      (hcut : (halfCut p) i = some j) : j.val ≤ q.val.1 := by
    have hqfirst : 1 ≤ q.val.1 := q.property.1
    have hqbound : q.val.1 + 2 ≤ n - 1 := by
      have hqd := q.property.2.2.2
      omega
    unfold halfCut at hcut
    by_cases hfix : (halfMate p) i.val = i.val
    · simp [hfix] at hcut
    · have hcut' : some (⟨(halfMate p) i.val, (halfMate_lt p) i⟩ : Fin n) = some j := by
        simpa [hfix] using hcut
      have hv : (halfMate p) i.val = j.val := by
        have := Option.some.inj hcut'
        exact congrArg Fin.val this
      unfold halfMate secondOpen at hv
      split_ifs at hv <;> omega

  have q_edge_B_closed {n : ℕ} (q : TwoDownPrefix n)
      (hsep : q.val.1 + 2 ≤ q.val.2)
      (i : Fin n) (hi : i.val ≤ q.val.1) {j : Fin n}
      (hcut : (halfCut q) i = some j) : j.val ≤ q.val.1 := by
    unfold halfCut at hcut
    by_cases hfix : (halfMate q) i.val = i.val
    · simp [hfix] at hcut
    · have hcut' : some (⟨(halfMate q) i.val, (halfMate_lt q) i⟩ : Fin n) = some j := by
        simpa [hfix] using hcut
      have hv : (halfMate q) i.val = j.val := by
        have := Option.some.inj hcut'
        exact congrArg Fin.val this
      unfold halfMate secondOpen at hv
      split_ifs at hv <;> omega

  have rankJoin_B_preimage_closed {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 5 ≤ n)
      (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
      (hsep : q.val.1 + 2 ≤ q.val.2)
      (i : Fin n) (hi : i.val ≤ q.val.1)
      (hqi : i ∈ (unmatchedPositions q))
      (j : Fin n) (hpj : j ∈ (unmatchedPositions p))
      (hr : ((rankJoin p) q ⟨j, hpj⟩).1 = i) :
      j.val ≤ q.val.1 := by
    have hqnone : (halfCut q) i = none := (Finset.mem_filter.mp hqi).2
    have hqparams := ((halfCut_eq_none_iff q) i).1 hqnone
    have hqfirst : 1 ≤ q.val.1 := q.property.1
    have hqsub : q.val.1 - 1 + 1 = q.val.1 := Nat.sub_add_cancel hqfirst
    have hi2 : i.val ≤ q.val.1 - 2 := by
      have hqfirst' : 2 ≤ q.val.1 := by
        by_contra hc
        have : q.val.1 = 1 := by omega
        omega
      have hqfirst2sub : q.val.1 - 2 + 2 = q.val.1 := Nat.sub_add_cancel hqfirst'
      have hne1 := hqparams.1
      have hne2 := hqparams.2
      omega
    by_contra hgt'
    have hgt : q.val.1 < j.val := by omega
    have hc2 : 2 ≤ q.val.1 := by omega
    have hqbound : q.val.1 + 2 ≤ n - 1 := by
      have hqd := q.property.2.2.2
      omega
    let c : ℕ := q.val.1
    let g : Fin (c - 1) → Fin (c - 2) := fun k => by
      let x : Fin n := ⟨k.val + 2, by have := k.isLt; dsimp [c]; omega⟩
      have hxnone : (halfCut p) x = none := by
        rw [(halfCut_eq_none_iff p)]
        unfold secondOpen
        split_ifs <;>
          have hk := k.isLt <;> dsimp [x, c] at hk ⊢ <;> omega
      have hxi : x ∈ (unmatchedPositions p) := by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hxnone
      have hxlt : ((rankJoin p) q ⟨x, hxi⟩).1.val < i.val := by
        have horder : ((rankJoin p) q ⟨x, hxi⟩) <
            ((rankJoin p) q ⟨j, hpj⟩) := by
          apply ((rankJoin p) q).strictMono
          change x.val < j.val
          dsimp [x, c]
          have hk := k.isLt
          omega
        change ((rankJoin p) q ⟨x, hxi⟩).1.val <
          ((rankJoin p) q ⟨j, hpj⟩).1.val at horder
        rw [hr] at horder
        exact horder
      exact ⟨((rankJoin p) q ⟨x, hxi⟩).1.val, by
        dsimp [c]
        omega⟩
    have hg : Function.Injective g := by
      intro k₁ k₂ heq
      dsimp [g] at heq
      let x₁ : Fin n := ⟨k₁.val + 2, by have := k₁.isLt; dsimp [c]; omega⟩
      let x₂ : Fin n := ⟨k₂.val + 2, by have := k₂.isLt; dsimp [c]; omega⟩
      have hx₁none : (halfCut p) x₁ = none := by
        rw [(halfCut_eq_none_iff p)]
        unfold secondOpen
        split_ifs <;>
          have hk := k₁.isLt <;> dsimp [x₁, c] at hk ⊢ <;> omega
      have hx₂none : (halfCut p) x₂ = none := by
        rw [(halfCut_eq_none_iff p)]
        unfold secondOpen
        split_ifs <;>
          have hk := k₂.isLt <;> dsimp [x₂, c] at hk ⊢ <;> omega
      have hxi₁ : x₁ ∈ (unmatchedPositions p) := by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hx₁none
      have hxi₂ : x₂ ∈ (unmatchedPositions p) := by
        simp only [unmatchedPositions, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hx₂none
      have hR : ((rankJoin p) q ⟨x₁, hxi₁⟩).1 =
          ((rankJoin p) q ⟨x₂, hxi₂⟩).1 := by
        apply Fin.ext
        simpa [x₁, x₂] using congrArg Fin.val heq
      have hx : x₁ = x₂ := by
        have hz : (⟨x₁, hxi₁⟩ : (unmatchedPositions p)) =
            ⟨x₂, hxi₂⟩ := ((rankJoin p) q).injective (by simpa using hR)
        have hz' := congrArg Subtype.val hz
        exact hz'
      apply Fin.ext
      have hxv := congrArg Fin.val hx
      dsimp [x₁, x₂] at hxv
      omega
    have hcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hcard
    omega

  have not_connected_of_B_separated {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 5 ≤ n)
      (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
      (hsep : q.val.1 + 2 ≤ q.val.2) :
      ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
    have hqbound : q.val.1 + 2 ≤ n - 1 := by
      have hqd := q.property.2.2.2
      omega
    let xout : Fin n := ⟨q.val.1 + 1, by omega⟩
    have hclosed : ∀ (i j : Fin n), i.val ≤ q.val.1 →
        (joinedEdge p) q i j → j.val ≤ q.val.1 := by
      intro i j hi hxy
      rcases hxy with hxy | hxy | ⟨hiP, hxy⟩ | ⟨hjP, hxy⟩
      · exact (p_edge_B_closed p) q hp1 hp2 hsep i hi hxy
      · exact (q_edge_B_closed q) hsep i hi hxy
      · rw [← hxy]
        exact (rankJoin_B_closed_bound p) q hp1 hsep i hi hiP
      · have hiQ : i ∈ (unmatchedPositions q) := by
          rw [← hxy]
          exact ((rankJoin p) q ⟨j, hjP⟩).2
        exact (rankJoin_B_preimage_closed p) q hn hp1 hp2 hsep i hi hiQ j hjP hxy
    intro hconn
    have hpath := hconn (⟨0, by omega⟩ : Fin n) xout
    have hstay : ∀ z : Fin n,
        Relation.ReflTransGen ((joinedEdge p) q) (⟨0, by omega⟩ : Fin n) z →
          z.val ≤ q.val.1 := by
      intro z hpath'
      have hbound : (⟨0, by omega⟩ : Fin n).val ≤ q.val.1 → z.val ≤ q.val.1 :=
        Relation.ReflTransGen.head_induction_on
          (motive := fun a _ => a.val ≤ q.val.1 → z.val ≤ q.val.1) hpath'
          (fun ha => ha)
          (fun hab _ ih ha => ih (hclosed _ _ ha hab))
      have hzero : (⟨0, by omega⟩ : Fin n).val ≤ q.val.1 := by
        change 0 ≤ q.val.1
        omega
      exact hbound hzero
    have hout := hstay xout hpath
    dsimp [xout] at hout
    omega

  have rankJoin_B_consecutive {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
      (hc : 2 ≤ q.val.1) (hq : q.val.2 = q.val.1 + 1)
      (x : (unmatchedPositions p)) :
      ((rankJoin p) q x).1.val =
        if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2 := by
    have hpu (i : Fin n) :
        i ∈ (unmatchedPositions p) ↔ 2 ≤ i.val ∧ i.val ≤ n - 3 := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      unfold secondOpen
      split_ifs <;>
        have := i.isLt <;> have := p.property.2.1 <;> omega
    have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
        i.val < q.val.1 - 2 ∨ q.val.1 + 1 < i.val := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      simp only [secondOpen, hq, ↓reduceIte]
      omega
    let f : (unmatchedPositions p) → (unmatchedPositions q) := fun x =>
      ⟨⟨if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2, by
        have hx := (hpu x.1).1 x.2
        have hqbound := q.property.2.2.2
        split_ifs <;> omega⟩, by
        rw [hqu]
        have hx := (hpu x.1).1 x.2
        change (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2) <
          q.val.1 - 2 ∨ q.val.1 + 1 <
            (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2)
        split_ifs <;> omega⟩
    have hf : StrictMono f := by
      intro x y hxy
      change x.1.val < y.1.val at hxy
      change (if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2) <
        (if y.1.val < q.val.1 then y.1.val - 2 else y.1.val + 2)
      have hx := (hpu x.1).1 x.2
      have hy := (hpu y.1).1 y.2
      split_ifs <;> omega
    have hs : Function.Surjective f := by
      intro y
      have hy := (hqu y.1).1 y.2
      by_cases hfront : y.1.val < q.val.1 - 2
      · let x : Fin n := ⟨y.1.val + 2, by
          have := q.property.2.2.2
          omega⟩
        have hx : x ∈ (unmatchedPositions p) :=
          (hpu x).2 (by
            dsimp [x]
            have := q.property.2.2.2
            omega)
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        apply Fin.ext
        change (if x.val < q.val.1 then x.val - 2 else x.val + 2) = y.1.val
        dsimp [x]
        split_ifs <;> omega
      · have hback : q.val.1 + 1 < y.1.val := hy.resolve_left hfront
        let x : Fin n := ⟨y.1.val - 2, by have := y.1.isLt; omega⟩
        have hx : x ∈ (unmatchedPositions p) :=
          (hpu x).2 (by
            dsimp [x]
            have := y.1.isLt
            have := q.property.2.2.2
            omega)
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        apply Fin.ext
        change (if x.val < q.val.1 then x.val - 2 else x.val + 2) = y.1.val
        dsimp [x]
        split_ifs <;> omega
    let e : (unmatchedPositions p) ≃o (unmatchedPositions q) :=
      hf.orderIsoOfSurjective f hs
    have he : e = (rankJoin p) q := by
      have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
      apply OrderIso.ext
      apply funext
      intro z
      have hz := congrArg ((rankJoin p) q) (congrFun hid z)
      simpa [OrderIso.trans_apply] using hz
    have hfx : (e x).1.val =
        if x.1.val < q.val.1 then x.1.val - 2 else x.1.val + 2 := by
      change (f x).1.val = _
      rfl
    rwa [he] at hfx

  have halfCut_symmetric {n : ℕ}
      (p : TwoDownPrefix n) (i j : Fin n)
      (hij : (halfCut p) i = some j) : (halfCut p) j = some i := by
    unfold halfCut at hij ⊢
    by_cases hi : (halfMate p) i.val = i.val
    · simp [hi] at hij
    · have hjval : j.val = (halfMate p) i.val := by
        have h : (⟨(halfMate p) i.val, (halfMate_lt p) i⟩ : Fin n) = j := by
          simpa [hi] using hij
        exact congrArg Fin.val h |>.symm
      have hj : (halfMate p) j.val ≠ j.val := by
        rw [hjval, (halfMate_involutive p)]
        exact Ne.symm hi
      simp only [if_neg hj]
      congr 1
      apply Fin.ext
      change (halfMate p) j.val = i.val
      rw [hjval, (halfMate_involutive p)]

  have connected_of_B_consecutive {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1)
      (hc : 2 ≤ q.val.1) (hq : q.val.2 = q.val.1 + 1) :
      ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j := by
    have hpu (i : Fin n) :
        i ∈ (unmatchedPositions p) ↔ 2 ≤ i.val ∧ i.val ≤ n - 3 := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      unfold secondOpen
      split_ifs <;>
        have := i.isLt <;> have := p.property.2.1 <;> omega
    let zero : Fin n := ⟨0, by have := p.property.2.2.2; omega⟩
    let last : Fin n := ⟨n - 1, by have := p.property.2.2.2; omega⟩
    have hsym {i j : Fin n}
        (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
        Relation.ReflTransGen ((joinedEdge p) q) j i := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail mid fin hab hbc ih =>
        have hcb : (joinedEdge p) q fin mid := by
          rcases hbc with hc | hc | hc | hc
          · exact Or.inl ((halfCut_symmetric p) _ _ hc)
          · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
          · exact Or.inr (Or.inr (Or.inr hc))
          · exact Or.inr (Or.inr (Or.inl hc))
        exact (Relation.ReflTransGen.single hcb).trans ih
    have hfront : ∀ k : ℕ, ∀ x : Fin n, x.val = k → x.val < q.val.1 →
        Relation.ReflTransGen ((joinedEdge p) q) x zero := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro x hxk hxc
        by_cases hzero : x.val = 0
        · have hx : x = zero := Fin.ext (by dsimp [zero]; omega)
          subst x
          exact Relation.ReflTransGen.refl
        by_cases hone : x.val = 1
        · have hcut : (halfCut p) x = some zero := by
            have h := (halfCut_first_reverse p)
            have hx : x = (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) :=
              Fin.ext (by change x.val = p.val.1; omega)
            rw [hx]
            have ht : (⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
                (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) = zero :=
              Fin.ext (by dsimp [zero]; omega)
            simpa [ht] using h
          exact Relation.ReflTransGen.single (Or.inl hcut)
        have hx2 : 2 ≤ x.val := by omega
        let y : Fin n := ⟨x.val - 2, by have := x.isLt; omega⟩
        have hxy : (joinedEdge p) q x y := by
          have hpx : x ∈ (unmatchedPositions p) :=
            (hpu x).2 (by
              have := q.property.2.2.2
              constructor <;> omega)
          have hr := (rankJoin_B_consecutive p) q hp1 hp2 hc hq ⟨x, hpx⟩
          have hy : ((rankJoin p) q ⟨x, hpx⟩).1 = y := by
            apply Fin.ext
            rw [hr]
            dsimp [y]
            simp [hxc]
          exact Or.inr (Or.inr (Or.inl ⟨hpx, hy⟩))
        exact (Relation.ReflTransGen.single hxy).trans
          (ih y.val (by dsimp [y]; omega) y rfl (by dsimp [y]; omega))
    have hback : ∀ k : ℕ, ∀ x : Fin n, n - 1 - x.val = k → q.val.1 ≤ x.val →
        Relation.ReflTransGen ((joinedEdge p) q) x last := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro x hxk hcx
        have hxbound := x.isLt
        by_cases hlast : x.val = n - 1
        · have hx : x = last := Fin.ext (by dsimp [last]; omega)
          subst x
          exact Relation.ReflTransGen.refl
        by_cases hpenult : x.val = n - 2
        · have hcut : (halfCut p) x = some last := by
            have h := (halfCut_second_pair p)
            have hsep : p.val.2 ≠ p.val.1 + 1 := by omega
            have hx : x = (⟨(secondOpen p), by
                unfold secondOpen
                split_ifs
                · exact lt_of_le_of_lt (Nat.sub_le _ _)
                    (lt_trans p.property.2.2.1 p.property.2.2.2)
                · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ : Fin n) := by
              apply Fin.ext
              change x.val = (secondOpen p)
              unfold secondOpen
              rw [if_neg hsep, hp2]
              omega
            rw [hx]
            have ht : (⟨p.val.2, p.property.2.2.2⟩ : Fin n) = last :=
              Fin.ext (by dsimp [last]; omega)
            simpa [ht] using h
          exact Relation.ReflTransGen.single (Or.inl hcut)
        have hxle : x.val ≤ n - 3 := by omega
        let y : Fin n := ⟨x.val + 2, by omega⟩
        have hxy : (joinedEdge p) q x y := by
          have hpx : x ∈ (unmatchedPositions p) :=
            (hpu x).2 (by constructor <;> omega)
          have hr := (rankJoin_B_consecutive p) q hp1 hp2 hc hq ⟨x, hpx⟩
          have hy : ((rankJoin p) q ⟨x, hpx⟩).1 = y := by
            apply Fin.ext
            rw [hr]
            dsimp [y]
            simp [show ¬x.val < q.val.1 by omega]
          exact Or.inr (Or.inr (Or.inl ⟨hpx, hy⟩))
        exact (Relation.ReflTransGen.single hxy).trans
          (ih (n - 1 - y.val) (by dsimp [y]; omega) y rfl (by dsimp [y]; omega))
    let a : Fin n := ⟨q.val.1 - 2, by have := q.property.2.2.2; omega⟩
    let b : Fin n := ⟨q.val.1 + 1, by simpa [hq] using q.property.2.2.2⟩
    have hab : (joinedEdge p) q a b := by
      have h := (halfCut_second_pair q)
      have ha : a = (⟨(secondOpen q), by
          unfold secondOpen
          rw [if_pos (by omega)]
          have := q.property.2.2.2
          omega⟩ : Fin n) := by
        apply Fin.ext
        simp [a, secondOpen, hq]
      rw [ha]
      refine Or.inr (Or.inl ?_)
      have ht : (⟨q.val.2, q.property.2.2.2⟩ : Fin n) = b :=
        Fin.ext (by dsimp [b]; omega)
      simpa [ht] using h
    have hbridge : Relation.ReflTransGen ((joinedEdge p) q) zero last :=
      ((hsym (hfront a.val a rfl (by dsimp [a]; omega))).trans
        (Relation.ReflTransGen.single hab)).trans
        (by
          apply hback (n - 1 - b.val) b rfl
          dsimp [b]
          omega)
    have htozero (x : Fin n) :
        Relation.ReflTransGen ((joinedEdge p) q) x zero := by
      by_cases hxc : x.val < q.val.1
      · exact hfront x.val x rfl hxc
      · exact (hback (n - 1 - x.val) x rfl (by omega)).trans (hsym hbridge)
    intro i j
    exact (htozero i).trans (hsym (htozero j))

  have not_connected_of_A_early {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
      (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
      (hearly : q.val.1 + 2 ≤ p.val.2) :
      ¬ (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
    have hn : 5 ≤ n := by have := p.property.2.1; omega
    have hsep : q.val.1 + 2 ≤ q.val.2 := by omega
    have hqfirst := q.property.1
    have hqbound := q.property.2.2.2
    have hpfar : q.val.1 < (secondOpen p) := by
      unfold secondOpen
      have := p.property.2.1
      rw [if_neg (by omega)]
      omega
    have hpreimage (i j : Fin n) (hi : i.val ≤ q.val.1)
        (hqi : i ∈ (unmatchedPositions q)) (hpj : j ∈ (unmatchedPositions p))
        (hr : ((rankJoin p) q ⟨j, hpj⟩).1 = i) : j.val ≤ q.val.1 := by
      have hqparams := ((halfCut_eq_none_iff q) i).1 (Finset.mem_filter.mp hqi).2
      have hi2 : i.val ≤ q.val.1 - 2 := by omega
      by_contra hgt
      have hc2 : 2 ≤ q.val.1 := by have := i.isLt; omega
      let g : Fin (q.val.1 - 1) → Fin (q.val.1 - 2) := fun k => by
        let x : Fin n := ⟨k.val + 2, by have := k.isLt; omega⟩
        have hxi : x ∈ (unmatchedPositions p) := by
          simp only [unmatchedPositions, Finset.mem_filter,
            Finset.mem_univ, true_and]
          rw [(halfCut_eq_none_iff p)]
          dsimp [x]
          rw [hp1]
          have := k.isLt
          omega
        have hxlt : ((rankJoin p) q ⟨x, hxi⟩).1.val < i.val := by
          have ho := ((rankJoin p) q).strictMono
            (show (⟨x, hxi⟩ : (unmatchedPositions p)) < ⟨j, hpj⟩ by
              change x.val < j.val
              dsimp [x]
              have := k.isLt
              omega)
          change ((rankJoin p) q ⟨x, hxi⟩).1.val <
            ((rankJoin p) q ⟨j, hpj⟩).1.val at ho
          rwa [hr] at ho
        exact ⟨((rankJoin p) q ⟨x, hxi⟩).1.val, by omega⟩
      have hg : Function.Injective g := by
        intro a b hab
        have hv := congrArg Fin.val hab
        dsimp [g] at hv
        have hz := ((rankJoin p) q).injective
          (Subtype.ext (Fin.ext hv))
        have hx := congrArg (fun z : (unmatchedPositions p) => z.1.val) hz
        dsimp at hx
        exact Fin.ext (by omega)
      have hc := Fintype.card_le_of_injective g hg
      simp only [Fintype.card_fin] at hc
      omega
    have hclosed (i j : Fin n) (hi : i.val ≤ q.val.1)
        (hij : (joinedEdge p) q i j) : j.val ≤ q.val.1 := by
      rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
      · unfold halfCut at hcut
        by_cases hfix : (halfMate p) i.val = i.val
        · simp [hfix] at hcut
        · simp only [if_neg hfix] at hcut
          have hv := congrArg Fin.val (Option.some.inj hcut)
          change (halfMate p) i.val = j.val at hv
          unfold halfMate at hv
          rw [hp1] at hv
          split_ifs at hv <;> omega
      · exact (q_edge_B_closed q) hsep i hi hcut
      · rw [← hr]
        exact (rankJoin_B_closed_bound p) q hp1 hsep i hi hiP
      · exact hpreimage i j hi (by rw [← hr]; exact ((rankJoin p) q ⟨j, hjP⟩).2)
          hjP hr
    intro hconn
    let zero : Fin n := ⟨0, by omega⟩
    let outside : Fin n := ⟨q.val.1 + 1, by omega⟩
    have hpath := hconn zero outside
    have hb : zero.val ≤ q.val.1 → outside.val ≤ q.val.1 :=
      Relation.ReflTransGen.head_induction_on
        (motive := fun a _ => a.val ≤ q.val.1 → outside.val ≤ q.val.1) hpath
        (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
    have := hb (by dsimp [zero]; omega)
    dsimp [outside] at this
    omega

  have rankJoin_A {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
      (_hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
      (hcover : p.val.2 - 1 ≤ q.val.1) (x : (unmatchedPositions p)) :
      ((rankJoin p) q x).1.val =
        if x.1.val < p.val.2 then x.1.val - 2
        else if q.val.1 + 2 < x.1.val ∧ q.val.1 + 2 ≤ q.val.2
          then x.1.val - 2 else x.1.val - 4 := by
    have hb := p.property.2.1
    have hc := q.property.2.2.1
    have hn := q.property.2.2.2
    have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
    have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔
        2 ≤ i.val ∧ (i.val + 2 ≤ p.val.2 ∨ p.val.2 < i.val) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      rw [show (secondOpen p) = p.val.2 - 1 by
        simp only [secondOpen, if_neg hpsep], hp1]
      omega
    have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
        if q.val.1 + 1 = q.val.2 then i.val + 4 < n
        else (i.val + 2 ≤ q.val.1 ∨ q.val.1 < i.val) ∧ i.val + 2 < n := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      unfold secondOpen
      have := i.isLt
      split_ifs <;> omega
    let f : (unmatchedPositions p) → (unmatchedPositions q) := fun z =>
      ⟨⟨if z.1.val < p.val.2 then z.1.val - 2
         else if q.val.1 + 2 < z.1.val ∧ q.val.1 + 2 ≤ q.val.2
           then z.1.val - 2 else z.1.val - 4, by
        have hz := (hpu z.1).1 z.2
        have := z.1.isLt
        split_ifs <;> omega⟩, by
        rw [hqu]
        have hz := (hpu z.1).1 z.2
        have := z.1.isLt
        change (if q.val.1 + 1 = q.val.2 then _ else _)
        dsimp only
        split_ifs <;> omega⟩
    have hf : StrictMono f := by
      intro z w hzw
      have hz := (hpu z.1).1 z.2
      have hw := (hpu w.1).1 w.2
      change z.1.val < w.1.val at hzw
      change (if z.1.val < p.val.2 then z.1.val - 2 else
        if q.val.1 + 2 < z.1.val ∧ q.val.1 + 2 ≤ q.val.2 then z.1.val - 2
        else z.1.val - 4) <
        (if w.1.val < p.val.2 then w.1.val - 2 else
        if q.val.1 + 2 < w.1.val ∧ q.val.1 + 2 ≤ q.val.2 then w.1.val - 2
        else w.1.val - 4)
      split_ifs <;> omega
    have hs : Function.Surjective f := by
      intro y
      have hy := (hqu y.1).1 y.2
      let z : Fin n := ⟨if y.1.val + 3 < p.val.2 then y.1.val + 2
        else if q.val.1 + 1 = q.val.2 ∨ y.1.val + 2 ≤ q.val.1
          then y.1.val + 4 else y.1.val + 2, by
        have := y.1.isLt
        split_ifs <;> split_ifs at hy <;> omega⟩
      have hz : z ∈ (unmatchedPositions p) := by
        rw [hpu]
        dsimp [z]
        have hq := q.property.2.2.1
        have hq2' := hq2
        split_ifs <;> split_ifs at hy <;> omega
      refine ⟨⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change (if z.val < p.val.2 then z.val - 2 else
        if q.val.1 + 2 < z.val ∧ q.val.1 + 2 ≤ q.val.2 then z.val - 2
        else z.val - 4) = y.1.val
      dsimp [z]
      split_ifs <;> split_ifs at hy <;> omega
    let e := hf.orderIsoOfSurjective f hs
    have he : e = (rankJoin p) q := by
      have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
      apply OrderIso.ext
      funext z
      have hz := congrArg ((rankJoin p) q) (congrFun hid z)
      simpa [OrderIso.trans_apply] using hz
    have hfx : (e x).1.val =
        if x.1.val < p.val.2 then x.1.val - 2
        else if q.val.1 + 2 < x.1.val ∧ q.val.1 + 2 ≤ q.val.2
          then x.1.val - 2 else x.1.val - 4 := rfl
    rwa [he] at hfx

  let aTerminal {n : ℕ} (p q : TwoDownPrefix n) (x : ℕ) : ℕ :=
    if x + 2 ≤ p.val.2 then x % 2 else
      let y := if q.val.1 + 2 < x ∧ q.val.1 + 2 ≤ q.val.2
        then q.val.1 + 1 + (x - (q.val.1 + 1)) % 2 else x
      let r := (y + 3 - p.val.2) % 4
      if r < 2 then (p.val.2 - 3 + r) % 2 else p.val.2 - 3 + r

  have A_terminal_paths {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
      (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1)
      (hcover : p.val.2 - 1 ≤ q.val.1) :
      (∀ x : (unmatchedPositions p),
        (aTerminal p) q ((rankJoin p) q x).1.val = (aTerminal p) q x.1.val) ∧
      (∀ x : Fin n, ∃ z : Fin n,
        z.val = (aTerminal p) q x.val ∧
        (z.val = 0 ∨ z.val = 1 ∨ z.val = p.val.2 - 1 ∨ z.val = p.val.2) ∧
        Relation.ReflTransGen ((joinedEdge p) q) x z) := by
    have hb := p.property.2.1
    have hc := q.property.2.2.1
    have hn := q.property.2.2.2
    have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
    have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔
        2 ≤ i.val ∧ (i.val + 2 ≤ p.val.2 ∨ p.val.2 < i.val) := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      rw [show (secondOpen p) = p.val.2 - 1 by
        simp only [secondOpen, if_neg hpsep], hp1]
      omega
    have hstep (x : (unmatchedPositions p)) :
        (aTerminal p) q ((rankJoin p) q x).1.val = (aTerminal p) q x.1.val := by
      rw [(rankJoin_A p) q hp1 hpbound hq2 hcover x]
      have hx := (hpu x.1).1 x.2
      have := x.1.isLt
      unfold aTerminal
      dsimp only
      split_ifs <;> omega
    refine ⟨hstep, ?_⟩
    have hreach : ∀ k : ℕ, ∀ x : Fin n, x.val = k → ∃ z : Fin n,
        z.val = (aTerminal p) q x.val ∧
        (z.val = 0 ∨ z.val = 1 ∨ z.val = p.val.2 - 1 ∨ z.val = p.val.2) ∧
        Relation.ReflTransGen ((joinedEdge p) q) x z := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro x hxk
        by_cases hpaired : x.val = 0 ∨ x.val = 1 ∨
            x.val = p.val.2 - 1 ∨ x.val = p.val.2
        · refine ⟨x, ?_, hpaired, Relation.ReflTransGen.refl⟩
          unfold aTerminal
          dsimp only
          split_ifs <;> omega
        · have hx : x ∈ (unmatchedPositions p) := (hpu x).2 (by omega)
          let y : Fin n := ((rankJoin p) q ⟨x, hx⟩).1
          have hlt : y.val < k := by
            dsimp [y]
            rw [(rankJoin_A p) q hp1 hpbound hq2 hcover]
            dsimp only
            have hu := (hpu x).1 hx
            split_ifs <;> omega
          obtain ⟨z, hz, hpz, hyz⟩ := ih y.val hlt y rfl
          refine ⟨z, hz.trans (hstep ⟨x, hx⟩), hpz, ?_⟩
          have hxy : (joinedEdge p) q x y := Or.inr (Or.inr (Or.inl ⟨hx, rfl⟩))
          exact (Relation.ReflTransGen.single hxy).trans hyz
    intro x
    exact hreach x.val x rfl

  have connected_iff_A {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 1)
      (hpbound : p.val.2 ≤ n - 2) (hq2 : q.val.2 = n - 1) :
      (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
        p.val.2 - 1 ≤ q.val.1 ∧ q.val.1 % 2 ≠ p.val.2 % 2 := by
    have hb := p.property.2.1
    have hc := q.property.2.2.1
    have hn := q.property.2.2.2
    have hpsep : p.val.2 ≠ p.val.1 + 1 := by omega
    let zero : Fin n := ⟨0, by omega⟩
    let one : Fin n := ⟨1, by omega⟩
    let back : Fin n := ⟨p.val.2, p.property.2.2.2⟩
    let before : Fin n := ⟨p.val.2 - 1, by have := p.property.2.2.2; omega⟩
    have hsym {i j : Fin n}
        (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
        Relation.ReflTransGen ((joinedEdge p) q) j i := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail mid fin hab hbc ih =>
        have hcb : (joinedEdge p) q fin mid := by
          rcases hbc with hc | hc | hc | hc
          · exact Or.inl ((halfCut_symmetric p) _ _ hc)
          · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
          · exact Or.inr (Or.inr (Or.inr hc))
          · exact Or.inr (Or.inr (Or.inl hc))
        exact (Relation.ReflTransGen.single hcb).trans ih
    constructor
    · intro hconn
      have hcover : p.val.2 - 1 ≤ q.val.1 := by
        by_contra h
        exact (not_connected_of_A_early p) q hp1 hpbound hq2 (by omega) hconn
      refine ⟨hcover, ?_⟩
      intro heven
      have ht := (A_terminal_paths p) q hp1 hpbound hq2 hcover
      have hpcolor (i j : Fin n) (hcut : (halfCut p) i = some j) :
          (aTerminal p) q i.val + 2 ≤ p.val.2 ↔
            (aTerminal p) q j.val + 2 ≤ p.val.2 := by
        unfold halfCut at hcut
        by_cases hfix : (halfMate p) i.val = i.val
        · simp [hfix] at hcut
        · simp only [if_neg hfix] at hcut
          have hv := congrArg Fin.val (Option.some.inj hcut)
          change (halfMate p) i.val = j.val at hv
          unfold halfMate at hv
          rw [show (secondOpen p) = p.val.2 - 1 by
            simp only [secondOpen, if_neg hpsep], hp1] at hv
          unfold aTerminal
          dsimp only
          have := i.isLt
          have := j.isLt
          split_ifs at hv <;> split_ifs <;> omega
      have hqcolor (i j : Fin n) (hcut : (halfCut q) i = some j) :
          (aTerminal p) q i.val + 2 ≤ p.val.2 ↔
            (aTerminal p) q j.val + 2 ≤ p.val.2 := by
        unfold halfCut at hcut
        by_cases hfix : (halfMate q) i.val = i.val
        · simp [hfix] at hcut
        · simp only [if_neg hfix] at hcut
          have hv := congrArg Fin.val (Option.some.inj hcut)
          change (halfMate q) i.val = j.val at hv
          unfold halfMate secondOpen at hv
          unfold aTerminal
          dsimp only
          have := i.isLt
          have := j.isLt
          split_ifs at hv <;> split_ifs <;> omega
      have hclosed (i j : Fin n) (hi : (aTerminal p) q i.val + 2 ≤ p.val.2)
          (hij : (joinedEdge p) q i j) : (aTerminal p) q j.val + 2 ≤ p.val.2 := by
        rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
        · exact (hpcolor i j hcut).mp hi
        · exact (hqcolor i j hcut).mp hi
        · rw [← hr, ht.1 ⟨i, hiP⟩]
          exact hi
        · have hm := ht.1 ⟨j, hjP⟩
          rw [hr] at hm
          rwa [← hm]
      have hpath := hconn zero back
      have hstay : (aTerminal p) q zero.val + 2 ≤ p.val.2 →
          (aTerminal p) q back.val + 2 ≤ p.val.2 :=
        Relation.ReflTransGen.head_induction_on
          (motive := fun a _ => (aTerminal p) q a.val + 2 ≤ p.val.2 →
            (aTerminal p) q back.val + 2 ≤ p.val.2) hpath
          (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
      have hz : (aTerminal p) q zero.val = 0 := by
        simp [zero, aTerminal, show 2 ≤ p.val.2 by omega]
      have hback : (aTerminal p) q back.val = p.val.2 := by
        unfold aTerminal
        dsimp [back]
        split_ifs <;> omega
      have hout := hstay (by rw [hz]; omega)
      rw [hback] at hout
      omega
    · rintro ⟨hcover, hodd⟩
      have ht := (A_terminal_paths p) q hp1 hpbound hq2 hcover
      have hfront : Relation.ReflTransGen ((joinedEdge p) q) one zero := by
        have h := (halfCut_first_reverse p)
        have he1 : (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩ : Fin n) = one :=
          Fin.ext (by dsimp [one]; omega)
        have he0 : (⟨p.val.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_trans p.property.2.2.1 p.property.2.2.2)⟩ : Fin n) = zero :=
          Fin.ext (by dsimp [zero]; omega)
        exact Relation.ReflTransGen.single (Or.inl (by simpa [he1, he0] using h))
      have hback : Relation.ReflTransGen ((joinedEdge p) q) before back := by
        have h := (halfCut_second_pair p)
        have he : (⟨(secondOpen p), by
            unfold secondOpen
            split_ifs
            · exact lt_of_le_of_lt (Nat.sub_le _ _)
                (lt_trans p.property.2.2.1 p.property.2.2.2)
            · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.property.2.2.2⟩ : Fin n) = before := by
          apply Fin.ext
          simp only [secondOpen, if_neg hpsep]
          rfl
        exact Relation.ReflTransGen.single (Or.inl (by simpa [he, back] using h))
      have hroots (x : Fin n) :
          ((aTerminal p) q x.val ≤ 1 → Relation.ReflTransGen ((joinedEdge p) q) x zero) ∧
          (p.val.2 - 1 ≤ (aTerminal p) q x.val →
            Relation.ReflTransGen ((joinedEdge p) q) x back) := by
        obtain ⟨z, hz, hpz, hxz⟩ := ht.2 x
        constructor
        · intro hsmall
          have hzsmall : z.val = 0 ∨ z.val = 1 := by omega
          rcases hzsmall with hz0 | hz1
          · have he : z = zero := Fin.ext (by dsimp [zero]; omega)
            simpa [he] using hxz
          · have he : z = one := Fin.ext (by dsimp [one]; omega)
            exact hxz.trans (by simpa [he] using hfront)
        · intro hlarge
          have hzlarge : z.val = p.val.2 - 1 ∨ z.val = p.val.2 := by omega
          rcases hzlarge with hzbefore | hzback
          · have he : z = before := Fin.ext (by dsimp [before]; omega)
            exact hxz.trans (by simpa [he] using hback)
          · have he : z = back := Fin.ext (by dsimp [back]; omega)
            simpa [he] using hxz
      let a : Fin n := ⟨q.val.1 - 1, by have := q.property.1; omega⟩
      let b : Fin n := ⟨q.val.1, by omega⟩
      have hab : Relation.ReflTransGen ((joinedEdge p) q) a b := by
        have h := (halfCut_first_pair q)
        exact Relation.ReflTransGen.single (Or.inr (Or.inl (by simpa [a, b] using h)))
      have hcross :
          ((aTerminal p) q a.val ≤ 1 ∧ p.val.2 - 1 ≤ (aTerminal p) q b.val) ∨
          (p.val.2 - 1 ≤ (aTerminal p) q a.val ∧ (aTerminal p) q b.val ≤ 1) := by
        unfold aTerminal
        dsimp [a, b]
        split_ifs <;> omega
      have hbridge : Relation.ReflTransGen ((joinedEdge p) q) zero back := by
        rcases hcross with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
        · exact ((hsym ((hroots a).1 ha)).trans hab).trans ((hroots b).2 hb')
        · exact ((hsym ((hroots b).1 hb')).trans (hsym hab)).trans ((hroots a).2 ha)
      have htozero (x : Fin n) : Relation.ReflTransGen ((joinedEdge p) q) x zero := by
        by_cases hsmall : (aTerminal p) q x.val ≤ 1
        · exact (hroots x).1 hsmall
        · obtain ⟨z, hz, hpz, _⟩ := ht.2 x
          have hlarge : p.val.2 - 1 ≤ (aTerminal p) q x.val := by omega
          exact ((hroots x).2 hlarge).trans (hsym hbridge)
      intro i j
      exact (htozero i).trans (hsym (htozero j))

  have rankJoin_C {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
      (hc : 2 ≤ q.val.1) (hq2 : q.val.2 = n - 1)
      (x : (unmatchedPositions p)) :
      ((rankJoin p) q x).1.val =
        if x.1.val ≤ q.val.1 + 2 then x.1.val - 4 else x.1.val - 2 := by
    have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔ 4 ≤ i.val := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      have ho : (secondOpen p) = 0 := by
        simp [secondOpen, hp1, hp2]
      rw [ho, hp1, hp2]
      omega
    have hqu (i : Fin n) : i ∈ (unmatchedPositions q) ↔
        if q.val.1 + 1 = q.val.2 then i.val + 4 < n
        else (i.val + 2 ≤ q.val.1 ∨ q.val.1 < i.val) ∧ i.val + 2 < n := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff q)]
      unfold secondOpen
      have := i.isLt
      have := q.property.2.2.2
      split_ifs <;> omega
    let f : (unmatchedPositions p) → (unmatchedPositions q) := fun z =>
      ⟨⟨if z.1.val ≤ q.val.1 + 2 then z.1.val - 4 else z.1.val - 2, by
        have hz := (hpu z.1).1 z.2
        have := z.1.isLt
        split_ifs <;> omega⟩, by
        rw [hqu]
        have hz := (hpu z.1).1 z.2
        have := z.1.isLt
        have := q.property.2.2.2
        change (if q.val.1 + 1 = q.val.2 then _ else _)
        dsimp only
        split_ifs <;> omega⟩
    have hf : StrictMono f := by
      intro z w hzw
      change z.1.val < w.1.val at hzw
      change (if z.1.val ≤ q.val.1 + 2 then z.1.val - 4 else z.1.val - 2) <
        (if w.1.val ≤ q.val.1 + 2 then w.1.val - 4 else w.1.val - 2)
      have hz := (hpu z.1).1 z.2
      have hw := (hpu w.1).1 w.2
      split_ifs <;> omega
    have hs : Function.Surjective f := by
      intro y
      have hy := (hqu y.1).1 y.2
      let z : Fin n := ⟨if y.1.val + 2 ≤ q.val.1 then y.1.val + 4
        else y.1.val + 2, by
        have := y.1.isLt
        have := q.property.2.2.2
        have hq := q.property.2.2.1
        have hq2' := hq2
        split_ifs <;> split_ifs at hy <;> omega⟩
      have hz : z ∈ (unmatchedPositions p) := by
        rw [hpu]
        dsimp [z]
        split_ifs <;> split_ifs at hy <;> omega
      refine ⟨⟨z, hz⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change (if z.val ≤ q.val.1 + 2 then z.val - 4 else z.val - 2) = y.1.val
      dsimp [z]
      have hq := q.property.2.2.1
      have hq2' := hq2
      split_ifs <;> split_ifs at hy <;> omega
    let e := hf.orderIsoOfSurjective f hs
    have he : e = (rankJoin p) q := by
      have hid := StrictMono.eq_id (e.trans ((rankJoin p) q).symm).strictMono
      apply OrderIso.ext
      funext z
      have hz := congrArg ((rankJoin p) q) (congrFun hid z)
      simpa [OrderIso.trans_apply] using hz
    have hfx : (e x).1.val =
        if x.1.val ≤ q.val.1 + 2 then x.1.val - 4 else x.1.val - 2 := rfl
    rwa [he] at hfx

  let cTerminal {n : ℕ} (q : TwoDownPrefix n) (x : ℕ) : ℕ :=
    if x ≤ q.val.1 + 2 then x % 4
    else if (x - (q.val.1 + 3)) % 2 = 0 then (q.val.1 + 1) % 4
    else (q.val.1 + 2) % 4

  have C_terminal_paths {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
      (hc : 2 ≤ q.val.1) (hq2 : q.val.2 = n - 1) :
      (∀ x : (unmatchedPositions p),
        (cTerminal q) ((rankJoin p) q x).1.val = (cTerminal q) x.1.val) ∧
      (∀ x : Fin n, ∃ z : Fin n,
        z.val = (cTerminal q) x.val ∧ z.val < 4 ∧
        Relation.ReflTransGen ((joinedEdge p) q) x z) := by
    have hpu (i : Fin n) : i ∈ (unmatchedPositions p) ↔ 4 ≤ i.val := by
      simp only [unmatchedPositions, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [(halfCut_eq_none_iff p)]
      have ho : (secondOpen p) = 0 := by
        simp [secondOpen, hp1, hp2]
      rw [ho, hp1, hp2]
      omega
    have hstep (x : (unmatchedPositions p)) :
        (cTerminal q) ((rankJoin p) q x).1.val = (cTerminal q) x.1.val := by
      rw [(rankJoin_C p) q hp1 hp2 hc hq2 x]
      have hx := (hpu x.1).1 x.2
      have := x.1.isLt
      unfold cTerminal
      split_ifs <;> omega
    refine ⟨hstep, ?_⟩
    have hreach : ∀ k : ℕ, ∀ x : Fin n, x.val = k →
        ∃ z : Fin n, z.val = (cTerminal q) x.val ∧ z.val < 4 ∧
          Relation.ReflTransGen ((joinedEdge p) q) x z := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro x hxk
        by_cases hroot : x.val < 4
        · refine ⟨x, ?_, hroot, Relation.ReflTransGen.refl⟩
          simp [cTerminal,
            show x.val ≤ q.val.1 + 2 by omega, Nat.mod_eq_of_lt hroot]
        · have hx : x ∈ (unmatchedPositions p) := (hpu x).2 (by omega)
          let y : Fin n := ((rankJoin p) q ⟨x, hx⟩).1
          have hlt : y.val < k := by
            dsimp [y]
            rw [(rankJoin_C p) q hp1 hp2 hc hq2 ⟨x, hx⟩]
            change (if x.val ≤ q.val.1 + 2 then x.val - 4 else x.val - 2) < k
            split_ifs <;> omega
          obtain ⟨z, hz, hsmall, hyz⟩ := ih y.val hlt y rfl
          refine ⟨z, hz.trans (hstep ⟨x, hx⟩), hsmall, ?_⟩
          have hxy : (joinedEdge p) q x y := Or.inr (Or.inr (Or.inl ⟨hx, rfl⟩))
          exact (Relation.ReflTransGen.single hxy).trans hyz
    intro x
    exact hreach x.val x rfl

  have joinedEdge_swap {n : ℕ}
      (p q : TwoDownPrefix n) (i j : Fin n)
      (h : (joinedEdge q) p i j) : (joinedEdge p) q i j := by
    rcases h with h | h | ⟨hi, h⟩ | ⟨hj, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · have hj : j ∈ (unmatchedPositions p) := by
        rw [← h]
        exact ((rankJoin q) p ⟨i, hi⟩).2
      right; right; right
      refine ⟨hj, ?_⟩
      have hz : ((rankJoin q) p ⟨i, hi⟩) = ⟨j, hj⟩ := Subtype.ext h
      rw [← (show ((rankJoin q) p).symm = (rankJoin p) q by
        simp [rankJoin, OrderIso.symm_trans]),
        ← hz, OrderIso.symm_apply_apply]
    · have hi : i ∈ (unmatchedPositions p) := by
        rw [← h]
        exact ((rankJoin q) p ⟨j, hj⟩).2
      right; right; left
      refine ⟨hi, ?_⟩
      have hz : ((rankJoin q) p ⟨j, hj⟩) = ⟨i, hi⟩ := Subtype.ext h
      rw [← (show ((rankJoin q) p).symm = (rankJoin p) q by
        simp [rankJoin, OrderIso.symm_trans]),
        ← hz, OrderIso.symm_apply_apply]

  have C_color_p_edge {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
      (hc : 2 ≤ q.val.1) (i j : Fin n)
      (hcut : (halfCut p) i = some j) :
      ((cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3) ↔
        ((cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3) := by
    unfold halfCut at hcut
    by_cases hfix : (halfMate p) i.val = i.val
    · simp [hfix] at hcut
    · simp only [if_neg hfix] at hcut
      have hv := congrArg Fin.val (Option.some.inj hcut)
      change (halfMate p) i.val = j.val at hv
      have ho : (secondOpen p) = 0 := by
        simp [secondOpen, hp1, hp2]
      unfold halfMate at hv
      rw [hp1, hp2, ho] at hv
      have hroot (x : Fin n) (hx : x.val < 4) : (cTerminal q) x.val = x.val := by
        simp [cTerminal,
          show x.val ≤ q.val.1 + 2 by omega, Nat.mod_eq_of_lt hx]
      have hindex : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
        by_contra h
        have hfixed := ((halfMate_fixed_iff p) i.val).2 (by
          rw [hp1, hp2, ho]
          omega)
        exact hfix hfixed
      have hpair :
          (i.val = 0 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) := by
        split_ifs at hv <;> omega
      have hi : i.val < 4 := by omega
      have hj : j.val < 4 := by omega
      rw [hroot i hi, hroot j hj]
      rcases hpair with h | h | h | h <;> omega

  have C_color_q_edge_even {n : ℕ}
      (q : TwoDownPrefix n) (hc : 2 ≤ q.val.1)
      (hq2 : q.val.2 = n - 1) (heven : q.val.1 % 2 = 0)
      (i j : Fin n) (hcut : (halfCut q) i = some j) :
      ((cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3) ↔
        ((cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3) := by
    unfold halfCut at hcut
    by_cases hfix : (halfMate q) i.val = i.val
    · simp [hfix] at hcut
    · simp only [if_neg hfix] at hcut
      have hv := congrArg Fin.val (Option.some.inj hcut)
      change (halfMate q) i.val = j.val at hv
      have hindex : i.val = q.val.1 - 1 ∨ i.val = q.val.1 ∨
          i.val = (secondOpen q) ∨ i.val = q.val.2 := by
        by_contra h
        exact hfix (((halfMate_fixed_iff q) i.val).2 (by omega))
      unfold halfMate secondOpen at hv
      unfold secondOpen at hindex
      have hb := q.property.2.2.2
      have ho := q.property.2.2.1
      have hq := hq2
      unfold cTerminal
      split_ifs at hv <;> split_ifs <;> omega

  have connected_iff_C {n : ℕ}
      (p q : TwoDownPrefix n) (hp1 : p.val.1 = 2) (hp2 : p.val.2 = 3)
      (hq2 : q.val.2 = n - 1) :
      (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
        q.val.1 % 2 = 1 := by
    by_cases hc1 : q.val.1 = 1
    · have hB : ∀ i j : Fin n,
          Relation.ReflTransGen ((joinedEdge q) p) i j :=
        (connected_of_B_consecutive q) p hc1 hq2 (by omega) (by omega)
      have hinc : (joinedEdge q) p ≤ (joinedEdge p) q := by
        intro i j h
        exact (joinedEdge_swap p) q i j h
      constructor
      · intro _
        omega
      · intro _ i j
        exact Relation.ReflTransGen.mono hinc i j (hB i j)
    have hc : 2 ≤ q.val.1 := by have := q.property.1; omega
    have ht := (C_terminal_paths p) q hp1 hp2 hc hq2
    have hn : 4 ≤ n := by have := p.property.2.2.2; omega
    let r0 : Fin n := ⟨0, by omega⟩
    let r1 : Fin n := ⟨1, by omega⟩
    let r2 : Fin n := ⟨2, by omega⟩
    let r3 : Fin n := ⟨3, by omega⟩
    have hsym {i j : Fin n}
        (h : Relation.ReflTransGen ((joinedEdge p) q) i j) :
        Relation.ReflTransGen ((joinedEdge p) q) j i := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail mid fin hab hbc ih =>
        have hcb : (joinedEdge p) q fin mid := by
          rcases hbc with hc | hc | hc | hc
          · exact Or.inl ((halfCut_symmetric p) _ _ hc)
          · exact Or.inr (Or.inl ((halfCut_symmetric q) _ _ hc))
          · exact Or.inr (Or.inr (Or.inr hc))
          · exact Or.inr (Or.inr (Or.inl hc))
        exact (Relation.ReflTransGen.single hcb).trans ih
    have h03 : Relation.ReflTransGen ((joinedEdge p) q) r0 r3 := by
      have h : (halfCut p) r0 = some r3 := by
        simpa [r0, r3, secondOpen, hp1, hp2] using
          (halfCut_second_pair p)
      exact Relation.ReflTransGen.single (Or.inl h)
    have h12 : Relation.ReflTransGen ((joinedEdge p) q) r1 r2 := by
      have h : (halfCut p) r1 = some r2 := by
        simpa [r1, r2, hp1] using (halfCut_first_pair p)
      exact Relation.ReflTransGen.single (Or.inl h)
    constructor
    · intro hconn
      by_contra hodd
      have heven : q.val.1 % 2 = 0 := by omega
      let hcolor : Fin n → Prop := fun x =>
        (cTerminal q) x.val = 0 ∨ (cTerminal q) x.val = 3
      have hclosed (i j : Fin n) (hi : hcolor i)
          (hij : (joinedEdge p) q i j) : hcolor j := by
        rcases hij with hcut | hcut | ⟨hiP, hr⟩ | ⟨hjP, hr⟩
        · exact ((C_color_p_edge p) q hp1 hp2 hc i j hcut).mp hi
        · exact ((C_color_q_edge_even q) hc hq2 heven i j hcut).mp hi
        · change (cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3
          rw [← hr, ht.1 ⟨i, hiP⟩]
          exact hi
        · change (cTerminal q) j.val = 0 ∨ (cTerminal q) j.val = 3
          have hm := ht.1 ⟨j, hjP⟩
          rw [hr] at hm
          change (cTerminal q) i.val = 0 ∨ (cTerminal q) i.val = 3 at hi
          rwa [← hm]
      have hpath := hconn r0 r1
      have hstay : hcolor r0 → hcolor r1 :=
        Relation.ReflTransGen.head_induction_on
          (motive := fun a _ => hcolor a → hcolor r1) hpath
          (fun ha => ha) (fun hab _ ih ha => ih (hclosed _ _ ha hab))
      have hzero : hcolor r0 := by
        change (cTerminal q) 0 = 0 ∨ (cTerminal q) 0 = 3
        left
        simp [cTerminal]
      have hone : ¬ hcolor r1 := by
        change ¬ ((cTerminal q) 1 = 0 ∨ (cTerminal q) 1 = 3)
        simp [cTerminal,
          show 1 ≤ q.val.1 + 2 by omega]
      exact hone (hstay hzero)
    · intro hodd
      let a : Fin n := ⟨q.val.1 - 1, by
        have := q.property.1
        have := q.property.2.2.1
        have := q.property.2.2.2
        omega⟩
      let b : Fin n := ⟨q.val.1, lt_trans q.property.2.2.1 q.property.2.2.2⟩
      have hab : Relation.ReflTransGen ((joinedEdge p) q) a b := by
        have h : (halfCut q) a = some b := by
          simpa [a, b] using (halfCut_first_pair q)
        exact Relation.ReflTransGen.single (Or.inr (Or.inl h))
      obtain ⟨za, hza, _, hpa⟩ := ht.2 a
      obtain ⟨zb, hzb, _, hpb⟩ := ht.2 b
      have hza' : za.val = (q.val.1 - 1) % 4 := by
        rw [hza]
        simp [cTerminal, a,
          show q.val.1 - 1 ≤ q.val.1 + 2 by omega]
      have hzb' : zb.val = q.val.1 % 4 := by
        rw [hzb]
        simp [cTerminal, b]
      have hcross :
          (za.val = 0 ∧ zb.val = 1) ∨
          (za.val = 2 ∧ zb.val = 3) := by
        omega
      have hzab : Relation.ReflTransGen ((joinedEdge p) q) za zb :=
        ((hsym hpa).trans hab).trans hpb
      have h01 : Relation.ReflTransGen ((joinedEdge p) q) r0 r1 := by
        rcases hcross with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have ea : za = r0 := Fin.ext ha
          have eb : zb = r1 := Fin.ext hb
          simpa [ea, eb] using hzab
        · have ea : za = r2 := Fin.ext ha
          have eb : zb = r3 := Fin.ext hb
          have h23 : Relation.ReflTransGen ((joinedEdge p) q) r2 r3 := by
            simpa [ea, eb] using hzab
          exact h03.trans ((hsym h23).trans (hsym h12))
      have hroot0 (z : Fin n) (hz : z.val < 4) :
          Relation.ReflTransGen ((joinedEdge p) q) z r0 := by
        by_cases h0 : z.val = 0
        · have he : z = r0 := Fin.ext h0
          simpa [he] using (Relation.ReflTransGen.refl :
            Relation.ReflTransGen ((joinedEdge p) q) r0 r0)
        by_cases h1 : z.val = 1
        · have he : z = r1 := Fin.ext h1
          simpa [he] using hsym h01
        by_cases h2 : z.val = 2
        · have he : z = r2 := Fin.ext h2
          simpa [he] using (hsym h12).trans (hsym h01)
        · have he : z = r3 := Fin.ext (by dsimp [r3]; omega)
          simpa [he] using hsym h03
      have htozero (x : Fin n) :
          Relation.ReflTransGen ((joinedEdge p) q) x r0 := by
        obtain ⟨z, _, hz, hxz⟩ := ht.2 x
        exact hxz.trans (hroot0 z hz)
      intro i j
      exact (htozero i).trans (hsym (htozero j))

  have not_connected_B_four
      (p q : TwoDownPrefix 4) (hp1 : p.val.1 = 1) (hp2 : p.val.2 = 3)
      (hq1 : q.val.1 = 1) (hq2 : q.val.2 = 3) :
      ¬ (∀ i j : Fin 4, Relation.ReflTransGen ((joinedEdge p) q) i j) := by
    let t : TwoDownPrefix 4 := ⟨(1, 3), ⟨ by decide, by decide, by decide, by decide⟩⟩
    have hpt : p = t := by
      rcases p with ⟨⟨a, b⟩, _⟩
      change a = 1 at hp1
      change b = 3 at hp2
      subst a
      subst b
      rfl
    have hqt : q = t := by
      rcases q with ⟨⟨a, b⟩, _⟩
      change a = 1 at hq1
      change b = 3 at hq2
      subst a
      subst b
      rfl
    subst p
    subst q
    have hempty : (unmatchedPositions t) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using (unmatchedPositions_card t)
    have hedge (i j : Fin 4) (h : (joinedEdge t) t i j) :
        (i.val < 2 ↔ j.val < 2) := by
      have hcut : ∀ a b : Fin 4, (halfCut t) a = some b →
          (a.val < 2 ↔ b.val < 2) := by
        intro a b hab
        fin_cases a <;> fin_cases b <;>
          simp [halfCut, halfMate, secondOpen, t] at hab ⊢
      rcases h with h | h | ⟨hi, _⟩ | ⟨hj, _⟩
      · exact hcut i j h
      · exact hcut i j h
      · simp [hempty] at hi
      · simp [hempty] at hj
    intro hconn
    have hpath := hconn (0 : Fin 4) (2 : Fin 4)
    have hinv : ∀ j : Fin 4,
        Relation.ReflTransGen ((joinedEdge t) t) (0 : Fin 4) j → j.val < 2 := by
      intro j h
      induction h with
      | refl => decide
      | @tail b c _ hbc ih => exact (hedge b c hbc).mp ih
    exact (by decide : ¬ (2 : Fin 4).val < 2) (hinv 2 hpath)

  let canonicalA {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
    p.val.1 = 1 ∧ p.val.2 ≤ n - 2 ∧ q.val.2 = n - 1 ∧
      p.val.2 - 1 ≤ q.val.1 ∧ q.val.1 % 2 ≠ p.val.2 % 2

  let canonicalB {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
    p.val.1 = 1 ∧ p.val.2 = n - 1 ∧ 2 ≤ q.val.1 ∧
      q.val.2 = q.val.1 + 1

  let canonicalC {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
    p.val.1 = 2 ∧ p.val.2 = 3 ∧ q.val.2 = n - 1 ∧
      3 ≤ q.val.1 ∧ q.val.1 % 2 = 1

  let canonical {n : ℕ} (p q : TwoDownPrefix n) : Prop :=
    canonicalA p q ∨ canonicalB p q ∨ canonicalC p q

  have connected_canonical_of_endpoint {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 4 ≤ n)
      (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j)
      (hp : p.val.1 = 1 ∨ (p.val.1 = 2 ∧ p.val.2 = 3))
      (hq : q.val.2 = n - 1) : canonical p q ∨ canonical q p := by
    rcases hp with hp1 | ⟨hp1, hp2⟩
    · by_cases hplast : p.val.2 = n - 1
      · by_cases hq1 : q.val.1 = 1
        · have hnp : n = 4 := by
            by_contra hne
            have hn5 : 5 ≤ n := by omega
            exact ((not_connected_of_B_separated p) q hn5 hp1 hplast
              (by have := q.property.2.1; omega)) hconn
          subst n
          exact False.elim (((not_connected_B_four p) q hp1 (by omega) hq1 (by omega)) hconn)
        · have hqfirst : 2 ≤ q.val.1 := by have := q.property.1; omega
          have hconsec : q.val.2 = q.val.1 + 1 := by
            by_contra hne
            have hn5 : 5 ≤ n := by
              have := q.property.2.1
              have := q.property.2.2.1
              omega
            exact ((not_connected_of_B_separated p) q hn5 hp1 hplast
              (by have := q.property.2.2.1; omega)) hconn
          exact Or.inl (Or.inr (Or.inl ⟨hp1, hplast, hqfirst, hconsec⟩))
      · have hpbound : p.val.2 ≤ n - 2 := by
          have := p.property.2.2.2
          omega
        have hA := ((connected_iff_A p) q hp1 hpbound hq).mp hconn
        exact Or.inl (Or.inl ⟨hp1, hpbound, hq, hA.1, hA.2⟩)
    · have hC := ((connected_iff_C p) q hp1 hp2 hq).mp hconn
      by_cases hq1 : q.val.1 = 1
      · have hqB : q.val.2 = n - 1 := hq
        have hpB : p.val.2 = p.val.1 + 1 := by omega
        exact Or.inr (Or.inr (Or.inl ⟨hq1, hqB, by omega, hpB⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨hp1, hp2, hq, by
          have := q.property.1
          omega, hC⟩))

  have connected_canonical_of_terminal_B {n : ℕ}
      (p q : TwoDownPrefix n) (hn : 4 ≤ n)
      (hconn : ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j)
      (hp1 : p.val.1 = 1) (hp2 : p.val.2 = n - 1) :
      canonical p q := by
    by_cases hq1 : q.val.1 = 1
    · by_cases hn4 : n = 4
      · subst n
        exact False.elim (((not_connected_B_four p) q hp1 (by omega) hq1 (by
          have := q.property.2.2.2
          have := q.property.2.1
          omega)) hconn)
      · have hn5 : 5 ≤ n := by omega
        exact False.elim (((not_connected_of_B_separated p) q hn5 hp1 hp2
          (by have := q.property.2.1; omega)) hconn)
    · have hqfirst : 2 ≤ q.val.1 := by have := q.property.1; omega
      have hconsec : q.val.2 = q.val.1 + 1 := by
        by_contra hne
        have hn5 : 5 ≤ n := by
          have := q.property.2.2.2
          have := q.property.2.2.1
          omega
        exact ((not_connected_of_B_separated p) q hn5 hp1 hp2
          (by have := q.property.2.2.1; omega)) hconn
      exact Or.inr (Or.inl ⟨hp1, hp2, hqfirst, hconsec⟩)

  have connected_iff_canonical_or_swap {n : ℕ} (p q : TwoDownPrefix n)
      (hn : 4 ≤ n) :
      (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
        canonical p q ∨ canonical q p := by
    have connected_swap :
        (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge p) q) i j) ↔
        (∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge q) p) i j) := by
      constructor <;> intro h i j
      · exact Relation.ReflTransGen.mono ((joinedEdge_swap q) p) i j (h i j)
      · exact Relation.ReflTransGen.mono ((joinedEdge_swap p) q) i j (h i j)
    constructor
    · intro hconn
      obtain ⟨hfirst, hlast⟩ := (connected_endpoint_cases p) q hn hconn
      rcases hfirst with hp1 | hpC | hq1 | hqC
      · rcases hlast with hp2 | hq2
        · exact Or.inl (connected_canonical_of_terminal_B p q hn hconn hp1 hp2)
        · exact connected_canonical_of_endpoint p q hn hconn (Or.inl hp1) hq2
      · rcases hlast with hpLast | hqLast
        · have hn4 : n = 4 := by
            have := p.property.2.2.2
            omega
          have hqLast : q.val.2 = n - 1 := by
            have := q.property.2.2.2
            have := q.property.2.1
            omega
          exact connected_canonical_of_endpoint p q hn hconn (Or.inr hpC) hqLast
        · exact connected_canonical_of_endpoint p q hn hconn (Or.inr hpC) hqLast
      · rcases hlast with hpLast | hqLast
        · have hs := connected_canonical_of_endpoint q p hn
            (connected_swap.mp hconn) (Or.inl hq1) hpLast
          exact hs.symm
        · have hs := connected_canonical_of_terminal_B q p hn
            (connected_swap.mp hconn) hq1 hqLast
          exact Or.inr hs
      · rcases hlast with hpLast | hqLast
        · have hs := connected_canonical_of_endpoint q p hn
            (connected_swap.mp hconn) (Or.inr hqC) hpLast
          exact hs.symm
        · have hn4 : n = 4 := by
            have := q.property.2.2.2
            omega
          have hpLast : p.val.2 = n - 1 := by
            have := p.property.2.2.2
            have := p.property.2.1
            omega
          have hs := connected_canonical_of_endpoint q p hn
            (connected_swap.mp hconn) (Or.inr hqC) hpLast
          exact hs.symm
    · rintro (h | h)
      · rcases h with hA | hB | hC
        · exact ((connected_iff_A p) q hA.1 hA.2.1 hA.2.2.1).2
            ⟨hA.2.2.2.1, hA.2.2.2.2⟩
        · exact (connected_of_B_consecutive p) q hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
        · exact ((connected_iff_C p) q hC.1 hC.2.1 hC.2.2.1).2 hC.2.2.2.2
      · apply connected_swap.mpr
        rcases h with hA | hB | hC
        · exact ((connected_iff_A q) p hA.1 hA.2.1 hA.2.2.1).2
            ⟨hA.2.2.2.1, hA.2.2.2.2⟩
        · exact (connected_of_B_consecutive q) p hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
        · exact ((connected_iff_C q) p hC.1 hC.2.1 hC.2.2.1).2 hC.2.2.2.2

  -- Count the disjoint canonical families and their exchanged copies.
  letI prefixFinite (n : ℕ) : Finite (TwoDownPrefix n) := by
    let f : TwoDownPrefix n → Fin n × Fin n := fun p =>
      (⟨p.val.1, lt_trans p.property.2.2.1 p.property.2.2.2⟩, ⟨p.val.2, p.property.2.2.2⟩)
    apply Finite.of_injective f
    intro p q h
    have hfirst : p.val.1 = q.val.1 := congrArg (fun x : Fin n × Fin n => x.1.val) h
    have hsecond : p.val.2 = q.val.2 := congrArg (fun x : Fin n × Fin n => x.2.val) h
    rcases p with ⟨⟨a, b⟩, _⟩
    rcases q with ⟨⟨c, d⟩, _⟩
    change a = c at hfirst
    change b = d at hsecond
    subst c
    subst d
    rfl

  letI prefixFintype (n : ℕ) : Fintype (TwoDownPrefix n) :=
    Fintype.ofFinite _

  let sourceCount (n : ℕ) (hn : 4 ≤ n) : ℕ :=
    letI : Finite {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop} :=
      Finite.of_injective (connectedSourcePrefixEquiv n hn)
        (connectedSourcePrefixEquiv n hn).injective
    Nat.card {M : {M : UpperMatching n // M.winding = n - 4} // M.1.oneLoop}

  have connected_pair_card_double (n : ℕ) (hn : 4 ≤ n) :
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n //
        ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j} =
        2 * Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n //
          canonical pq.1 pq.2} := by
    classical
    let A : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
      Finset.univ.filter (fun pq => canonical pq.1 pq.2)
    let B : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
      Finset.univ.filter (fun pq => canonical pq.2 pq.1)
    have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro pq ha hb
      have h := (Finset.mem_filter.mp ha).2
      have hs := (Finset.mem_filter.mp hb).2
      rcases h with h | h | h <;>
        rcases hs with hs | hs | hs <;>
        simp only [canonicalA, canonicalB, canonicalC] at h hs <;>
        have hpge := pq.1.property.2.1 <;>
        have hqge := pq.2.property.2.1 <;>
        have hpord := pq.1.property.2.2.1 <;>
        have hqord := pq.2.property.2.2.1 <;>
        omega
    have hconn : (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
        ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j)) = A ∪ B := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, A, B]
      exact connected_iff_canonical_or_swap pq.1 pq.2 hn
    have hswap : A.card = B.card := by
      apply Finset.card_bij (fun pq _ => (pq.2, pq.1))
      · intro pq hpq
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp hpq).2
      · intro a _ b _ hab
        exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
      · intro pq hpq
        refine ⟨(pq.2, pq.1), ?_, rfl⟩
        simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.mem_filter.mp hpq).2
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    change (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
      ∀ i j : Fin n, Relation.ReflTransGen ((joinedEdge pq.1) pq.2) i j)).card =
      2 * A.card
    rw [hconn, Finset.card_union_of_disjoint hdis, ← hswap]
    omega

  let canonicalBEquiv (n : ℕ) (hn : 4 ≤ n) :
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} ≃
        {c : ℕ // c ∈ Finset.Icc 2 (n - 2)} :=
    {
      toFun pq := ⟨pq.1.2.val.1, by
        rcases pq.2 with ⟨_, _, hc, hd⟩
        exact Finset.mem_Icc.mpr ⟨hc, by
          have := pq.1.2.property.2.2.2
          omega⟩⟩
      invFun c := ⟨
        (⟨(1, n - 1), ⟨ by omega, by omega, by omega, by omega⟩⟩,
         ⟨(c.1, c.1 + 1), ⟨ by
           have := (Finset.mem_Icc.mp c.2).1
           omega, by
           have := (Finset.mem_Icc.mp c.2).1
           omega, by omega, by
           have := (Finset.mem_Icc.mp c.2).2
           omega⟩⟩),
        by exact ⟨rfl, rfl, (Finset.mem_Icc.mp c.2).1, rfl⟩⟩
      left_inv pq := by
        have ext_positions (p q : TwoDownPrefix n)
            (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
          rcases p with ⟨⟨a, b⟩, _⟩
          rcases q with ⟨⟨c, d⟩, _⟩
          change a = c at hfirst
          change b = d at hsecond
          subst c
          subst d
          rfl
        apply Subtype.ext
        apply Prod.ext
        · apply ext_positions
          · exact pq.2.1.symm
          · exact pq.2.2.1.symm
        · apply ext_positions
          · rfl
          · exact pq.2.2.2.2.symm
      right_inv c := Subtype.ext rfl
    }

  let canonicalCEquiv (n : ℕ) (hn : 4 ≤ n) :
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} ≃
        {k : ℕ // k ∈ Finset.Icc 1 ((n - 3) / 2)} :=
    {
      toFun pq := ⟨pq.1.2.val.1 / 2, by
        rcases pq.2 with ⟨_, _, _, hc, hd⟩
        have hlt := pq.1.2.property.2.2.2
        have hord := pq.1.2.property.2.2.1
        have hlast := pq.2.2.2.1
        have hmod := hd
        exact Finset.mem_Icc.mpr (by
          constructor <;> omega)⟩
      invFun k := ⟨
        (⟨(2, 3), ⟨ by omega, by omega, by omega, by omega⟩⟩,
         ⟨(2 * k.1 + 1, n - 1), ⟨ by
           have := (Finset.mem_Icc.mp k.2).1
           omega, by
           have := (Finset.mem_Icc.mp k.2).1
           omega, by
           have := (Finset.mem_Icc.mp k.2).2
           omega, by
           have := (Finset.mem_Icc.mp k.2).2
           omega⟩⟩),
        by
          refine ⟨rfl, rfl, rfl, ?_, ?_⟩
          · have := (Finset.mem_Icc.mp k.2).1
            change 3 ≤ 2 * k.1 + 1
            omega
          · change (2 * k.1 + 1) % 2 = 1
            omega⟩
      left_inv pq := by
        have ext_positions (p q : TwoDownPrefix n)
            (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
          rcases p with ⟨⟨a, b⟩, _⟩
          rcases q with ⟨⟨c, d⟩, _⟩
          change a = c at hfirst
          change b = d at hsecond
          subst c
          subst d
          rfl
        apply Subtype.ext
        apply Prod.ext
        · apply ext_positions
          · exact pq.2.1.symm
          · exact pq.2.2.1.symm
        · apply ext_positions
          · have hmod := pq.2.2.2.2
            change 2 * (pq.1.2.val.1 / 2) + 1 = pq.1.2.val.1
            omega
          · exact pq.2.2.2.1.symm
      right_inv k := by
        apply Subtype.ext
        dsimp
        omega
    }

  let canonicalAEquiv (n : ℕ) (hn : 4 ≤ n) :
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} ≃
        Σ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)},
          {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)} :=
    {
      toFun pq := ⟨
        ⟨n - 1 - pq.1.1.val.2, by
          have hpbound := pq.2.2.1
          have hpge := pq.1.1.property.2.1
          have hplt := pq.1.1.property.2.2.2
          exact Finset.mem_Icc.mpr (by constructor <;> omega)⟩,
        ⟨(pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2, by
          rcases pq.2 with ⟨hp1, hpbound, hq2, hlate, hpar⟩
          have hpge := pq.1.1.property.2.1
          have hqord := pq.1.2.property.2.2.1
          have hqlt := pq.1.2.property.2.2.2
          apply Finset.mem_Icc.mpr
          constructor
          · omega
          · change (pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2 ≤
              (n - 1 - pq.1.1.val.2) / 2
            omega⟩⟩
      invFun rk := ⟨
        (⟨(1, n - 1 - rk.1.1), ⟨
          by omega, by
            have hr := (Finset.mem_Icc.mp rk.1.2).2
            omega, by
            have hr := (Finset.mem_Icc.mp rk.1.2).2
            omega, by
            have hr := (Finset.mem_Icc.mp rk.1.2).1
            omega⟩⟩,
         ⟨((n - 1 - rk.1.1) - 1 + 2 * rk.2.1, n - 1), ⟨
           by
             have hr := (Finset.mem_Icc.mp rk.1.2).2
             omega, by
             have hr := (Finset.mem_Icc.mp rk.1.2).2
             omega, by
             have hr := (Finset.mem_Icc.mp rk.1.2).2
             have hk := (Finset.mem_Icc.mp rk.2.2).2
             omega, by omega⟩⟩),
        by
          change 1 = 1 ∧ n - 1 - rk.1.1 ≤ n - 2 ∧ n - 1 = n - 1 ∧
            (n - 1 - rk.1.1) - 1 ≤ (n - 1 - rk.1.1) - 1 + 2 * rk.2.1 ∧
            ((n - 1 - rk.1.1) - 1 + 2 * rk.2.1) % 2 ≠
              (n - 1 - rk.1.1) % 2
          have hr := (Finset.mem_Icc.mp rk.1.2).1
          have hr' := (Finset.mem_Icc.mp rk.1.2).2
          omega⟩
      left_inv pq := by
        have ext_positions (p q : TwoDownPrefix n)
            (hfirst : p.val.1 = q.val.1) (hsecond : p.val.2 = q.val.2) : p = q := by
          rcases p with ⟨⟨a, b⟩, _⟩
          rcases q with ⟨⟨c, d⟩, _⟩
          change a = c at hfirst
          change b = d at hsecond
          subst c
          subst d
          rfl
        apply Subtype.ext
        apply Prod.ext
        · apply ext_positions
          · exact pq.2.1.symm
          · have hpge := pq.1.1.property.2.1
            have hpbound := pq.2.2.1
            change n - 1 - (n - 1 - pq.1.1.val.2) = pq.1.1.val.2
            omega
        · apply ext_positions
          · rcases pq.2 with ⟨_, hpbound, _, hlate, hpar⟩
            have hpge := pq.1.1.property.2.1
            have hqord := pq.1.2.property.2.2.1
            change (n - 1 - (n - 1 - pq.1.1.val.2)) - 1 +
              2 * ((pq.1.2.val.1 - (pq.1.1.val.2 - 1)) / 2) = pq.1.2.val.1
            omega
          · exact pq.2.2.2.1.symm
      right_inv rk := by
        have hrval : n - 1 - (n - 1 - rk.1.1) = rk.1.1 := by
          have hr := (Finset.mem_Icc.mp rk.1.2).2
          omega
        have hr : (⟨n - 1 - (n - 1 - rk.1.1), by
          simpa only [hrval] using rk.1.2⟩ :
          {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}) = rk.1 := Subtype.ext hrval
        apply Sigma.ext hr
        apply (Subtype.heq_iff_coe_eq (by
          intro x
          simp only [Finset.mem_Icc, hrval])).2
        change ((n - 1 - rk.1.1) - 1 + 2 * rk.2.1 -
          ((n - 1 - rk.1.1) - 1)) / 2 = rk.2.1
        have hr' := (Finset.mem_Icc.mp rk.1.2).2
        omega
    }

  have sum_A_fibers (m : ℕ) :
      (∑ r ∈ Finset.Icc 1 m, (1 + r / 2)) = m + (m * m) / 4 := by
    induction m using Nat.twoStepInduction with
    | zero => simp
    | one => norm_num
    | more m ih _ =>
      rw [show m + 2 = (m + 1) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega), ih]
      have hs : (m + 1) / 2 + (m + 2) / 2 = m + 1 := by omega
      have hsq : (m + 2) * (m + 2) = m * m + 4 * (m + 1) := by ring
      rw [hsq]
      omega

  have canonicalA_card (n : ℕ) (hn : 4 ≤ n) :
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} =
        (n - 4) + ((n - 4) * (n - 4)) / 4 := by
    have hfiber (r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}) :
        Nat.card {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)} = 1 + r.1 / 2 := by
      change Nat.card (Finset.Icc 0 (r.1 / 2) : Set ℕ) = 1 + r.1 / 2
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
      omega
    calc
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} =
          Nat.card (Σ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)},
            {k : ℕ // k ∈ Finset.Icc 0 (r.1 / 2)}) :=
        Nat.card_congr (canonicalAEquiv n hn)
      _ = ∑ r : {r : ℕ // r ∈ Finset.Icc 1 (n - 4)}, (1 + r.1 / 2) := by
        rw [Nat.card_sigma]
        apply Finset.sum_congr rfl
        intro r _
        exact hfiber r
      _ = ∑ r ∈ Finset.Icc 1 (n - 4), (1 + r / 2) := by
        exact Finset.sum_coe_sort (Finset.Icc 1 (n - 4)) (fun r => 1 + r / 2)
      _ = (n - 4) + ((n - 4) * (n - 4)) / 4 := sum_A_fibers (n - 4)

  have canonical_card (n : ℕ) (hn : 4 ≤ n) :
      Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonical pq.1 pq.2} =
        (n - 4) + ((n - 4) * (n - 4)) / 4 +
          ((n - 4) + 1) + (((n - 4) + 1) / 2) := by
    have hBresult : Nat.card
        {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} =
        (n - 4) + 1 := by
      rw [Nat.card_congr (canonicalBEquiv n hn)]
      change Nat.card (Finset.Icc 2 (n - 2) : Set ℕ) = (n - 4) + 1
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
      omega
    have hCresult : Nat.card
        {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} =
        ((n - 4) + 1) / 2 := by
      rw [Nat.card_congr (canonicalCEquiv n hn)]
      change Nat.card (Finset.Icc 1 ((n - 3) / 2) : Set ℕ) = ((n - 4) + 1) / 2
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_Icc]
      omega
    classical
    let A : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
      Finset.univ.filter (fun pq => canonicalA pq.1 pq.2)
    let B : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
      Finset.univ.filter (fun pq => canonicalB pq.1 pq.2)
    let C : Finset (TwoDownPrefix n × TwoDownPrefix n) :=
      Finset.univ.filter (fun pq => canonicalC pq.1 pq.2)
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro pq hpA hpB
      have hA := (Finset.mem_filter.mp hpA).2
      have hB := (Finset.mem_filter.mp hpB).2
      simp only [canonicalA, canonicalB] at hA hB
      have hpge := pq.1.property.2.1
      omega
    have hAC : Disjoint A C := by
      apply Finset.disjoint_left.mpr
      intro pq hpA hpC
      have hA := (Finset.mem_filter.mp hpA).2
      have hC := (Finset.mem_filter.mp hpC).2
      simp only [canonicalA, canonicalC] at hA hC
      have hpge := pq.1.property.2.1
      omega
    have hBC : Disjoint B C := by
      apply Finset.disjoint_left.mpr
      intro pq hpB hpC
      have hB := (Finset.mem_filter.mp hpB).2
      have hC := (Finset.mem_filter.mp hpC).2
      simp only [canonicalB, canonicalC] at hB hC
      have hpge := pq.1.property.2.1
      omega
    have hABC : Disjoint (A ∪ B) C := by
      apply Finset.disjoint_left.mpr
      intro pq hpAB hpC
      rcases Finset.mem_union.mp hpAB with hpA | hpB
      · exact (Finset.disjoint_left.mp hAC) hpA hpC
      · exact (Finset.disjoint_left.mp hBC) hpB hpC
    have hcanon : (Finset.univ.filter (fun pq : TwoDownPrefix n × TwoDownPrefix n =>
        canonical pq.1 pq.2)) = (A ∪ B) ∪ C := by
      ext pq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      simp only [A, B, C, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [canonical, or_assoc]
    have hAcard : A.card =
        Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalA pq.1 pq.2} := by
      simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hBcard : B.card =
        Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalB pq.1 pq.2} := by
      simp only [B, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hCcard : C.card =
        Nat.card {pq : TwoDownPrefix n × TwoDownPrefix n // canonicalC pq.1 pq.2} := by
      simp only [C, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hcanon,
      Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB,
      hAcard, hBcard, hCcard, canonicalA_card n hn, hBresult,
      hCresult]

  have canonical_count_arithmetic (m : ℕ) :
      4 * (m + (m * m) / 4 + (m + 1) + (m + 1) / 2) + 20 =
        (m + 4) * (m + 4) + 2 * (m + 4) + (m + 4) % 2 := by
    have hsq : (m * m) % 4 = m % 2 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · have hm : m = 2 * (m / 2) := by omega
        rw [hm]
        ring_nf
        omega
      · have hm : m = 2 * (m / 2) + 1 := by omega
        rw [hm]
        ring_nf
        omega
    have hdiv := Nat.div_add_mod (m * m) 4
    have hhalf : 2 * ((m + 1) / 2) = m + m % 2 := by omega
    have hmod : (m + 4) % 2 = m % 2 := by omega
    rw [hmod]
    nlinarith

  -- Transfer the prefix count to the source model and solve the division step.
  change sourceCount n hn = _
  have hcount : sourceCount n hn = 2 * Nat.card
      {pq : TwoDownPrefix n × TwoDownPrefix n // canonical pq.1 pq.2} := by
    unfold sourceCount
    rw [Nat.card_congr (connectedSourcePrefixEquiv n hn)]
    exact connected_pair_card_double n hn
  have h : 2 * sourceCount n hn + 20 = n ^ 2 + 2 * n + n % 2 := by
    have hm : n - 4 + 4 = n := by omega
    calc
      2 * sourceCount n hn + 20 =
          4 * ((n - 4) + ((n - 4) * (n - 4)) / 4 +
            ((n - 4) + 1) + (((n - 4) + 1) / 2)) + 20 := by
        rw [hcount, canonical_card n hn]
        ring
      _ = (n - 4 + 4) * (n - 4 + 4) +
          2 * (n - 4 + 4) + (n - 4 + 4) % 2 :=
        canonical_count_arithmetic (n - 4)
      _ = n ^ 2 + 2 * n + n % 2 := by rw [hm]; ring
  omega

end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
