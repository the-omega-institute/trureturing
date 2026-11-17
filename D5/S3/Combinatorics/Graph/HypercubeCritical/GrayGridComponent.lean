/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: The generalized Gray incidence support in the actual Huang-signed Boolean cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-! Points and coordinate lines are encoded with FALSE entries in the literal row-major grid. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsSwitching IsBalanced)
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_zero matrix_flip_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-- Reuse the literal grid rows with explicit Boolean polarity reversal. -/
def falseRows {d : ℕ} (x : Q (d * d)) (b : Fin d) : Finset (Fin d) :=
  GridWedgeComponent.gridRow (fun q => !x q) b

abbrev PointData (d : ℕ) := Fin d → Fin d
abbrev LineData (d : ℕ) := Σ b : Fin d, ({i : Fin d // i ≠ b} → Fin d)

/-- One FALSE coordinate in each row. -/
def point {d : ℕ} (f : PointData d) : Q (d * d) :=
  fun q => !decide ((finProdFinEquiv.symm q).2 = f (finProdFinEquiv.symm q).1)

/-- One empty FALSE row, and one FALSE coordinate in every other row. -/
def line {d : ℕ} (p : LineData d) : Q (d * d) :=
  fun q => let ij := finProdFinEquiv.symm q
    if h : ij.1 = p.1 then true else !decide (ij.2 = p.2 ⟨ij.1, h⟩)

def pointPattern {d : ℕ} (x : Q (d * d)) : Prop :=
  ∀ b, ∃ j, falseRows x b = {j}

def linePattern {d : ℕ} (x : Q (d * d)) : Prop :=
  ∃ b, falseRows x b = ∅ ∧
    GridWedgeComponent.singletonRowsOutside (fun q => !x q) {b}

/-- The finite union of the two genuine incidence layers. -/
def support (d : ℕ) : Finset (Q (d * d)) :=
  (Finset.univ.image point) ∪ (Finset.univ.image line)

def componentGraph (d : ℕ) := (hypercube (d * d)).induce (support d : Set (Q (d * d)))

private theorem falseRows_point {d : ℕ} (f : PointData d) (b : Fin d) :
    falseRows (point f) b = {f b} := by
  ext j
  simp [falseRows, GridWedgeComponent.gridRow, point]

private theorem falseRows_line {d : ℕ} (p : LineData d) (b : Fin d) :
    falseRows (line p) b = if h : b = p.1 then ∅ else {p.2 ⟨b, h⟩} := by
  ext j
  by_cases h : b = p.1 <;> simp [falseRows, GridWedgeComponent.gridRow, line, h]

private theorem falseRows_ext {d : ℕ} {x y : Q (d * d)}
    (h : ∀ b, falseRows x b = falseRows y b) : x = y := by
  have he := GridWedgeComponent.gridRow_ext h
  funext q
  have := congrFun he q
  simpa using this

private theorem point_injective {d : ℕ} : Function.Injective (@point d) := by
  intro f g h
  funext b
  have := congrArg (fun x => falseRows x b) h
  simpa [falseRows_point] using this

private theorem line_injective {d : ℕ} : Function.Injective (@line d) := by
  rintro ⟨b, f⟩ ⟨c, g⟩ h
  have hbc : b = c := by
    by_contra hn
    have := congrArg (fun x => falseRows x b) h
    simp [falseRows_line, hn] at this
  subst c
  have hfg : f = g := by
    funext i
    have := congrArg (fun x => falseRows x i.val) h
    simpa [falseRows_line, i.property] using this
  subst g
  rfl

private theorem point_ne_line {d : ℕ} (f : PointData d) (p : LineData d) :
    point f ≠ line p := by
  intro h
  have := congrArg (fun x => falseRows x p.1) h
  simp [falseRows_point, falseRows_line] at this

private theorem pointPattern_iff {d : ℕ} (x : Q (d * d)) :
    pointPattern x ↔ ∃ f : PointData d, point f = x := by
  constructor
  · intro h
    let f := fun b => Classical.choose (h b)
    refine ⟨f, falseRows_ext fun b => ?_⟩
    simpa [falseRows_point, f] using (Classical.choose_spec (h b)).symm
  · rintro ⟨f, rfl⟩
    exact fun b => ⟨f b, falseRows_point f b⟩

private theorem linePattern_iff {d : ℕ} (x : Q (d * d)) :
    linePattern x ↔ ∃ p : LineData d, line p = x := by
  constructor
  · rintro ⟨b, hb, hs⟩
    let f : {i : Fin d // i ≠ b} → Fin d :=
      fun i => Classical.choose (hs i.val (by simpa using i.property))
    refine ⟨⟨b, f⟩, falseRows_ext fun i => ?_⟩
    by_cases hi : i = b
    · subst i
      simpa [falseRows_line] using hb.symm
    · rw [falseRows_line, dite_eq_right hi]
      exact (Classical.choose_spec (hs i (by simpa using hi))).symm
  · rintro ⟨p, rfl⟩
    refine ⟨p.1, by simp [falseRows_line], ?_⟩
    intro i hi
    have hn : i ≠ p.1 := by simpa using hi
    exact ⟨p.2 ⟨i, hn⟩, by simpa [falseRows, hn] using falseRows_line p i⟩

/-- Membership is exactly the stated singleton/one-empty FALSE-row pattern. -/
theorem mem_support_iff {d : ℕ} (x : Q (d * d)) :
    x ∈ support d ↔ pointPattern x ∨ linePattern x := by
  simp [support, pointPattern_iff, linePattern_iff]

/-- The two disjoint incidence layers each have d^d vertices, including d=1. -/
theorem card_support {d : ℕ} (hd : 1 ≤ d) : (support d).card = 2 * d ^ d := by
  have hdis : Disjoint (Finset.univ.image (@point d)) (Finset.univ.image (@line d)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hy
    exact point_ne_line f p hp.symm
  have hc : Fintype.card (LineData d) = d ^ d := by
    simp only [LineData, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_subtype_compl, Fintype.card_unique, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    have he : d = d - 1 + 1 := by omega
    calc
      d * d ^ (d - 1) = d ^ (d - 1) * d := Nat.mul_comm _ _
      _ = d ^ (d - 1 + 1) := (pow_succ _ _).symm
      _ = d ^ d := by rw [← he]
  rw [support, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ point_injective,
    Finset.card_image_of_injective _ line_injective]
  simp [hc, two_mul]

private theorem neg_flip {d : ℕ} (x : Q (d * d)) (b j : Fin d) :
    (fun q => !flip x (finProdFinEquiv (b, j)) q) =
      GridWedgeComponent.flip (fun q => !x q) b j := by
  funext q
  by_cases h : q = finProdFinEquiv (b, j) <;>
    simp [BalancedCriticalSpectrum.flip, GridWedgeComponent.flip, h]

private theorem falseRows_flip_other {d : ℕ} (x : Q (d * d)) (b j i : Fin d)
    (hi : i ≠ b) : falseRows (flip x (finProdFinEquiv (b, j))) i = falseRows x i := by
  unfold falseRows
  rw [neg_flip]
  exact GridWedgeComponent.gridRow_flip_other _ b j i hi

private theorem falseRows_flip_same {d : ℕ} (x : Q (d * d)) (b j : Fin d) :
    falseRows (flip x (finProdFinEquiv (b, j))) b =
      if x (finProdFinEquiv (b, j)) = false then (falseRows x b).erase j
      else insert j (falseRows x b) := by
  unfold falseRows
  rw [neg_flip, GridWedgeComponent.gridRow_flip_same]
  cases x (finProdFinEquiv (b, j)) <;> simp

private theorem point_flip {d : ℕ} (f : PointData d) (b : Fin d) :
    flip (point f) (finProdFinEquiv (b, f b)) = line ⟨b, fun i => f i.val⟩ := by
  apply falseRows_ext
  intro i
  by_cases hi : i = b
  · subst i
    simp [falseRows_flip_same, point, falseRows_point, falseRows_line]
  · simp [falseRows_flip_other, falseRows_point, falseRows_line, hi]

private def fill {d : ℕ} (p : LineData d) (j : Fin d) : PointData d :=
  fun i => if h : i = p.1 then j else p.2 ⟨i, h⟩

private theorem line_flip {d : ℕ} (p : LineData d) (j : Fin d) :
    flip (line p) (finProdFinEquiv (p.1, j)) = point (fill p j) := by
  apply falseRows_ext
  intro i
  by_cases hi : i = p.1
  · subst i
    simp [falseRows_flip_same, line, falseRows_line, falseRows_point, fill]
  · simp [falseRows_flip_other, falseRows_line, falseRows_point, fill, hi]

private theorem row_card_le {d : ℕ} {x : Q (d * d)} (hx : x ∈ support d) (b : Fin d) :
    (falseRows x b).card ≤ 1 := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    simp [falseRows_point]
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    by_cases hi : b = p.1 <;> simp [falseRows_line, hi]

private theorem point_flip_mem_iff {d : ℕ} (f : PointData d) (b j : Fin d) :
    flip (point f) (finProdFinEquiv (b, j)) ∈ support d ↔ j = f b := by
  constructor
  · intro h
    by_contra hn
    have hc := row_card_le h b
    have hb : point f (finProdFinEquiv (b, j)) = true := by simp [point, hn]
    rw [falseRows_flip_same, ite_eq_right (by simp [hb]), falseRows_point,
      Finset.card_insert_of_notMem (by simpa using hn), Finset.card_singleton] at hc
    omega
  · rintro rfl
    rw [point_flip]
    simp [support]

private theorem line_flip_mem_iff {d : ℕ} (p : LineData d) (b j : Fin d) :
    flip (line p) (finProdFinEquiv (b, j)) ∈ support d ↔ b = p.1 := by
  constructor
  · intro h
    by_contra hn
    have he : falseRows (flip (line p) (finProdFinEquiv (b, j))) p.1 = ∅ := by
      rw [falseRows_flip_other _ _ _ _ (Ne.symm hn)]
      simp [falseRows_line]
    rcases (mem_support_iff _).mp h with hp | hl
    · obtain ⟨k, hk⟩ := hp p.1
      rw [he] at hk
      simp at hk
    · obtain ⟨c, hc, hs⟩ := hl
      have hcp : c = p.1 := by
        by_contra hne
        obtain ⟨k, hk⟩ := hs p.1 (by simpa using Ne.symm hne)
        change falseRows _ p.1 = {k} at hk
        rw [he] at hk
        simp at hk
      subst c
      obtain ⟨k, hk⟩ := hs b (by simpa using hn)
      change falseRows _ b = {k} at hk
      rw [falseRows_flip_same, falseRows_line, dite_eq_right hn] at hk
      by_cases hj : j = p.2 ⟨b, hn⟩
      · subst j
        simp [line, hn] at hk
      · have hb : line p (finProdFinEquiv (b, j)) = true := by simp [line, hn, hj]
        rw [ite_eq_right (by simp [hb])] at hk
        have hcard := congrArg Finset.card hk
        simp [hj] at hcard
  · rintro rfl
    rw [line_flip]
    simp [support]

private theorem flip_injective {n : ℕ} (x : Q n) : Function.Injective (flip x) := by
  intro i j h
  by_contra hn
  have := congrFun h i
  simp [BalancedCriticalSpectrum.flip, hn] at this

private theorem degree_eq_legal {d : ℕ} (x : (support d : Set (Q (d * d)))) :
    (componentGraph d).degree x =
      Fintype.card {q : Fin (d * d) // flip x.val q ∈ support d} := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  let f : {q : Fin (d * d) // flip x.val q ∈ support d} →
      (componentGraph d).neighborSet x :=
    fun q => ⟨⟨flip x.val q.val, q.property⟩, BalancedCriticalSpectrum.flip_adj x.val q.val⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      apply Subtype.ext
      exact flip_injective x.val (congrArg (fun y => y.val.val) h)
    · intro y
      obtain ⟨q, hq⟩ := adjacent_exists_flip y.property
      change y.val.val = flip x.val q at hq
      refine ⟨⟨q, ?_⟩, ?_⟩
      · rw [← hq]
        exact y.val.property
      · exact Subtype.ext (Subtype.ext hq.symm)
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- Every selected vertex has exactly d neighbors in actual induced cube adjacency. -/
theorem component_regular (d : ℕ) : (componentGraph d).IsRegularOfDegree d := by
  intro x
  rw [degree_eq_legal]
  rcases Finset.mem_union.mp x.property with hp | hl
  · obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hp
    let e : Fin d ≃ {q : Fin (d * d) // flip x.val q ∈ support d} :=
      Equiv.ofBijective (fun b => ⟨finProdFinEquiv (b, f b), by
        rw [← hf]; exact (point_flip_mem_iff f b (f b)).mpr rfl⟩) (by
        constructor
        · intro a b h
          exact congrArg Prod.fst (finProdFinEquiv.injective (congrArg Subtype.val h))
        · intro q
          obtain ⟨⟨b, j⟩, hb⟩ := finProdFinEquiv.surjective q.val
          have hj : j = f b := by
            apply (point_flip_mem_iff f b j).mp
            rw [hf, hb]
            exact q.property
          refine ⟨b, Subtype.ext ?_⟩
          simpa [hj] using hb)
    exact (Fintype.card_congr e).symm.trans (Fintype.card_fin d)
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hl
    let e : Fin d ≃ {q : Fin (d * d) // flip x.val q ∈ support d} :=
      Equiv.ofBijective (fun j => ⟨finProdFinEquiv (p.1, j), by
        rw [← hp]; exact (line_flip_mem_iff p p.1 j).mpr rfl⟩) (by
        constructor
        · intro a b h
          exact congrArg Prod.snd (finProdFinEquiv.injective (congrArg Subtype.val h))
        · intro q
          obtain ⟨⟨b, j⟩, hb⟩ := finProdFinEquiv.surjective q.val
          have hj : b = p.1 := by
            apply (line_flip_mem_iff p b j).mp
            rw [hp, hb]
            exact q.property
          refine ⟨j, Subtype.ext ?_⟩
          simpa [hj] using hb)
    exact (Fintype.card_congr e).symm.trans (Fintype.card_fin d)

/-- Closed FALSE-prefix coefficient, derived from Huang's actual recursive matrix. -/
private theorem matrix_flip_prefix {n : ℕ} (x : Q n) (i : Fin n) :
    huangMatrix n x (flip x i) =
      ∏ j : Fin n, (if j < i ∧ x j = false then (-1 : ℝ) else 1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          rw [matrix_flip_zero]
          simp
      | succ i =>
          rw [matrix_flip_succ, Fin.prod_univ_succ, ih]
          simp only [Fin.succ_lt_succ_iff, Sensitivity.π]
          have hzero : (0 : Fin (n + 1)) < i.succ := Fin.succ_pos i
          simp only [hzero, true_and]
          cases x 0 <;> simp

private theorem same_column_lt {d : ℕ} (f : PointData d) (i b : Fin d) :
    finProdFinEquiv (i, f i) < finProdFinEquiv (b, f b) ↔ i < b := by
  change (f i).val + d * i.val < (f b).val + d * b.val ↔ i.val < b.val
  have hi := (f i).isLt
  have hb := (f b).isLt
  constructor
  · intro h
    by_contra hn
    have he : b.val ≤ i.val := by omega
    by_cases heq : i = b
    · subst b; omega
    · have hlt : b.val + 1 ≤ i.val := by
        have hne : i.val ≠ b.val := fun h => heq (Fin.ext h)
        omega
      have hm := Nat.mul_le_mul_left d hlt
      nlinarith
  · intro h
    have hm := Nat.mul_le_mul_left d (show i.val + 1 ≤ b.val by omega)
    nlinarith

private theorem point_edge_sign {d : ℕ} (f : PointData d) (b : Fin d) :
    huangMatrix (d * d) (point f) (line ⟨b, fun i => f i.val⟩) = (-1 : ℝ) ^ b.val := by
  rw [← point_flip, matrix_flip_prefix]
  rw [← Equiv.prod_comp finProdFinEquiv]
  rw [Fintype.prod_prod_type]
  have hrow (i : Fin d) :
      (∏ j : Fin d, (if finProdFinEquiv (i, j) < finProdFinEquiv (b, f b) ∧
          point f (finProdFinEquiv (i, j)) = false then (-1 : ℝ) else 1)) =
        if i < b then -1 else 1 := by
    have he (j : Fin d) :
        (if finProdFinEquiv (i, j) < finProdFinEquiv (b, f b) ∧
          point f (finProdFinEquiv (i, j)) = false then (-1 : ℝ) else 1) =
        if j = f i then (if i < b then -1 else 1) else 1 := by
      by_cases hj : j = f i
      · subst j
        simp [point, same_column_lt]
      · simp [point, hj]
    simp_rw [he]
    simp
  simp_rw [hrow]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  have he : Finset.univ.filter (fun i : Fin d => i < b) = Finset.Iio b := by ext i; simp
  rw [he, Fin.card_Iio]

/-- Points switch by +1; a line switches by the parity of its unique missing row. -/
def switching (d : ℕ) (x : Q (d * d)) : ℝ :=
  if h : ∃ p : LineData d, line p = x then (-1) ^ (Classical.choose h).1.val else 1

private theorem switching_point {d : ℕ} (f : PointData d) : switching d (point f) = 1 := by
  have hn : ¬ ∃ p : LineData d, line p = point f := by
    rintro ⟨p, hp⟩
    exact point_ne_line f p hp.symm
  simp [switching, hn]

private theorem switching_line {d : ℕ} (p : LineData d) :
    switching d (line p) = (-1 : ℝ) ^ p.1.val := by
  have h : ∃ q : LineData d, line q = line p := ⟨p, rfl⟩
  have he : Classical.choose h = p := line_injective (Classical.choose_spec h)
  simp [switching, h, he]

private theorem switching_point_edge {d : ℕ} (f : PointData d) (q : Fin (d * d))
    (hq : flip (point f) q ∈ support d) :
    huangMatrix (d * d) (point f) (flip (point f) q) =
      switching d (point f) * switching d (flip (point f) q) := by
  obtain ⟨⟨b, j⟩, rfl⟩ := finProdFinEquiv.surjective q
  have hj := (point_flip_mem_iff f b j).mp hq
  subst j
  rw [point_flip, switching_point, switching_line, one_mul, point_edge_sign]

/-- An explicit switching function for the fixed FALSE-prefix Huang signing. -/
theorem support_isSwitching (d : ℕ) : IsSwitching (support d) (switching d) := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hp | hl
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hp
      exact Or.inl (switching_point f)
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hl
      rw [switching_line]
      exact neg_one_pow_eq_or ℝ p.1.val
  · intro x hx y hy hxy
    obtain ⟨q, rfl⟩ := adjacent_exists_flip hxy
    rcases Finset.mem_union.mp hx with hp | hl
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hp
      exact switching_point_edge f q hy
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨⟨b, j⟩, rfl⟩ := finProdFinEquiv.surjective q
      have hb := (line_flip_mem_iff p b j).mp hy
      subst b
      have he := switching_point_edge (fill p j) (finProdFinEquiv (p.1, j)) (by
        rw [← line_flip, BalancedCriticalSpectrum.flip_flip]
        simp [support])
      rw [← line_flip, BalancedCriticalSpectrum.flip_flip] at he
      rw [line_flip]
      rw [line_flip] at he
      exact (huangMatrix_symmetric _ _).trans (he.trans (mul_comm _ _))

/-- The exact finite comparison object, with actual induced degree and Huang balance. -/
theorem gray_component {d : ℕ} (hd : 1 ≤ d) :
    (support d).card = 2 * d ^ d ∧
    (componentGraph d).IsRegularOfDegree d ∧ IsBalanced (support d) := by
  exact ⟨card_support hd, component_regular d, switching d, support_isSwitching d⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
