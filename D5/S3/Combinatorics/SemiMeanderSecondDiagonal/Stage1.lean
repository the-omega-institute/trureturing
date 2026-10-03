/- GID: D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage1
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Midpoint cuts and local arch pairing structure. -/

import D5.S3.Combinatorics.SemiMeanderSecondDiagonal.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SemiMeanderSecondDiagonal

open Classical

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def reflected {n : ℕ} (M : UpperMatching n) : UpperMatching n :=
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def leftPoint (n : ℕ) (x : Fin n) : Fin (2 * n) :=
  ⟨x.val, by have := x.isLt; omega⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def rightPoint (n : ℕ) (x : Fin n) : Fin (2 * n) :=
  (leftPoint n x).rev

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def leftCut {n : ℕ} (M : UpperMatching n) (x : Fin n) :
    Option (Fin n) :=
  if h : (M.mate (leftPoint n x)).val < n then
    some ⟨(M.mate (leftPoint n x)).val, h⟩
  else none

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_eq_some_iff {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_symmetric {n : ℕ} (M : UpperMatching n)
    (x y : Fin n) (h : (leftCut M) x = some y) :
    (leftCut M) y = some x := by
  apply (leftCut_eq_some_iff M y x).2
  have hxy := (leftCut_eq_some_iff M x y).1 h
  rw [← hxy, M.mate_mate]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def rightCut {n : ℕ} (M : UpperMatching n) (x : Fin n) :
    Option (Fin n) :=
  if h : (M.mate (rightPoint n x)).rev.val < n then
    some ⟨(M.mate (rightPoint n x)).rev.val, h⟩
  else none

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rightCut_eq_some_iff {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rightCut_symmetric {n : ℕ} (M : UpperMatching n)
    (x y : Fin n) (h : (rightCut M) x = some y) :
    (rightCut M) y = some x := by
  apply (rightCut_eq_some_iff M y x).2
  have hxy := (rightCut_eq_some_iff M x y).1 h
  rw [← hxy, M.mate_mate]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def crossingRight {n : ℕ} (M : UpperMatching n)
    (x : Fin n) (h : (leftCut M) x = none) : Fin n :=
  ⟨(M.mate (leftPoint n x)).rev.val, by
    have hc : n ≤ (M.mate (leftPoint n x)).val := by
      simpa [leftCut] using h
    have hb := (M.mate (leftPoint n x)).isLt
    have hr : (M.mate (leftPoint n x)).rev.val =
        2 * n - ((M.mate (leftPoint n x)).val + 1) := by simp
    omega⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def crossingLeft {n : ℕ} (M : UpperMatching n)
    (x : Fin n) (h : (rightCut M) x = none) : Fin n :=
  ⟨(M.mate (rightPoint n x)).val, by
    have hc : n ≤ (M.mate (rightPoint n x)).rev.val := by
      simpa [rightCut] using h
    have hb := (M.mate (rightPoint n x)).isLt
    have hr : (M.mate (rightPoint n x)).rev.val =
        2 * n - ((M.mate (rightPoint n x)).val + 1) := by simp
    omega⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem crossingRight_none {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem crossingLeft_none {n : ℕ} (M : UpperMatching n)
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

theorem winding_eq_leftCut_none_card {n : ℕ} (M : UpperMatching n) :
    M.winding = (Finset.univ.filter fun x : Fin n => (leftCut M) x = none).card := by
  simp only [UpperMatching.winding]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change n ≤ (M.mate (leftPoint n x)).val ↔ leftCut M x = none
  by_cases h : (M.mate (leftPoint n x)).val < n
  · have hnot : ¬n ≤ (M.mate (leftPoint n x)).val := by omega
    simp [leftCut, h, hnot]
  · have hle : n ≤ (M.mate (leftPoint n x)).val := by omega
    simp [leftCut, h, hle]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem winding_eq_rightCut_none_card {n : ℕ} (M : UpperMatching n) :
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
    exact winding_eq_leftCut_none_card M
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_paired_card_four {n : ℕ} (M : UpperMatching n)
    (hn : 4 ≤ n) (hw : M.winding = n - 4) :
    (Finset.univ.filter fun x : Fin n => (leftCut M) x ≠ none).card = 4 := by
  classical
  have hparts := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun x : Fin n => (leftCut M) x = none)
  have hleft : M.winding =
      (Finset.univ.filter fun x : Fin n => (leftCut M) x = none).card := by
    exact winding_eq_leftCut_none_card M
  rw [← hleft] at hparts
  rw [hw] at hparts
  simp only [Finset.card_univ, Fintype.card_fin] at hparts
  change n - 4 +
    (Finset.univ.filter fun x : Fin n => (leftCut M) x ≠ none).card = n at hparts
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rightCut_paired_card_four {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_between_paired {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rightCut_between_paired {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_arch_span_le_three {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rightCut_arch_span_le_three {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_between_mate_inside {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_arch_span_one_or_three {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_span_three_inner_pair {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def edge {n : ℕ} (M : UpperMatching n)
    (x y : Fin (2 * n)) : Prop := M.mate x = y ∨ x.rev = y

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def rainbowLabel (n : ℕ) (x : Fin (2 * n)) : Fin n :=
  if h : x.val < n then ⟨x.val, h⟩
  else ⟨x.rev.val, by
    have hx := x.isLt
    have hr : x.rev.val = 2 * n - (x.val + 1) := by simp
    omega⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem rainbowLabel_rev (n : ℕ) (x : Fin (2 * n)) :
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def contractedEdge {n : ℕ} (M : UpperMatching n)
    (i j : Fin n) : Prop :=
  ∃ x y : Fin (2 * n), rainbowLabel n x = i ∧
    rainbowLabel n y = j ∧ M.mate x = y

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem oneLoop_implies_contracted_connected {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem contractedEdge_iff_cut_or_cross {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem fiber_connected {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem contractedEdge_lift {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem oneLoop_iff_contracted_connected {n : ℕ} (M : UpperMatching n) :
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem crossing_rank_order {n : ℕ} (M : UpperMatching n)
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
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def TwoDownPrefix (n : ℕ) :=
  {ab : ℕ × ℕ // 1 ≤ ab.1 ∧ 3 ≤ ab.2 ∧ ab.1 < ab.2 ∧ ab.2 < n}

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def secondOpen {n : ℕ} (p : TwoDownPrefix n) : ℕ :=
  if p.val.2 = p.val.1 + 1 then p.val.1 - 2 else p.val.2 - 1

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
noncomputable def halfMate {n : ℕ} (p : TwoDownPrefix n) (x : ℕ) : ℕ :=
  if x = p.val.1 - 1 then p.val.1
  else if x = p.val.1 then p.val.1 - 1
  else if x = (secondOpen p) then p.val.2
  else if x = p.val.2 then (secondOpen p)
  else x

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem twoDown_endpoints_distinct {n : ℕ} (p : TwoDownPrefix n) :
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMate_involutive {n : ℕ} (p : TwoDownPrefix n)
    (x : ℕ) : (halfMate p) ((halfMate p) x) = x := by
  obtain ⟨huv, huw, huz, hvw, hvz, hwz⟩ := twoDown_endpoints_distinct p
  unfold halfMate
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ <;> omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem halfMate_fixed_iff {n : ℕ} (p : TwoDownPrefix n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem four_endpoint_pairing_shape
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem leftCut_four_endpoint_pairing_shape {n : ℕ} (M : UpperMatching n)
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

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 8192 in
theorem four_endpoint_adjacent_or_nested
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


end D5.S3.Combinatorics.SemiMeanderSecondDiagonal
