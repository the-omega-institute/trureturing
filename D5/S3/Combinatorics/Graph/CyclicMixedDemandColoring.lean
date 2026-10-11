/- GID: D5/S3/Combinatorics/Graph/CyclicMixedDemandColoring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CyclicMixedDemandColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic demand packing and wrapping slot colorings. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.CyclicMixedDemandColoring

/-- The types at a prefix are indexed by their rank, independently of any raw label. -/
abbrev Vertex {n : Nat} (k : Fin n → Nat) := (t : Fin n) × Fin (k t)

/-- Prefixes whose integer circular distance is strictly less than m. -/
def Near {n : Nat} (m : Nat) (i j : Fin n) : Prop :=
  (i.val < j.val + m ∧ j.val < i.val + m) ∨
    n + i.val < j.val + m ∨ n + j.val < i.val + m

/-- Distinct types at near prefixes must have different colors. -/
def Proper {n : Nat} {Z : Type*} (m : Nat) (k : Fin n → Nat)
    (color : Vertex k → Z) : Prop :=
  ∀ x y, x ≠ y → Near m x.1 y.1 → color x ≠ color y

/-- A color occupies at most floor(n/m) prefixes, also for empty and singleton classes. -/
theorem separated_packing {n m : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (k : Fin n → Nat) (S : Finset (Vertex k))
    (separated : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ Near m x.1 y.1) :
    S.card ≤ n / m := by
  classical
  let f : {x // x ∈ S} × Fin m → Fin n := fun x =>
    ⟨if x.1.val.1.val + x.2.val < n then x.1.val.1.val + x.2.val
      else x.1.val.1.val + x.2.val - n, by
      have hi := x.1.val.1.isLt
      have hr := x.2.isLt
      split_ifs <;> omega⟩
  have inj : Function.Injective f := by
    rintro ⟨x, r⟩ ⟨y, s⟩ equal
    have e := congrArg Fin.val equal
    change (if x.val.1.val + r.val < n then x.val.1.val + r.val
      else x.val.1.val + r.val - n) =
      (if y.val.1.val + s.val < n then y.val.1.val + s.val
      else y.val.1.val + s.val - n) at e
    have hx := x.val.1.isLt
    have hy := y.val.1.isLt
    have hr := r.isLt
    have hs := s.isLt
    have xy : x.val = y.val := by
      by_contra different
      apply separated x.val x.property y.val y.property different
      unfold Near
      split_ifs at e <;> omega
    have prefixes : x.val.1.val = y.val.1.val := congrArg (fun v : Vertex k => v.1.val) xy
    have rs : r = s := by
      apply Fin.ext
      split_ifs at e <;> omega
    exact Prod.ext (Subtype.ext xy) rs
  have bound := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at bound
  exact (Nat.le_div_iff_mul_le hm).mpr bound

/-- Every proper coloring has color classes bounded by the cyclic packing capacity. -/
private theorem color_class_packing {n m c : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (k : Fin n → Nat) (color : Vertex k → Fin c) (proper : Proper m k color)
    (z : Fin c) :
    ((Finset.univ : Finset (Vertex k)).filter (fun x => color x = z)).card ≤ n / m := by
  classical
  apply separated_packing hm hsize k
  intro x hx y hy different near
  exact proper x y different near
    ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)

/-- The total demand cannot exceed the number of colors times the packing capacity. -/
theorem packing_lower_bound {n m c : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (k : Fin n → Nat) (color : Vertex k → Fin c) (proper : Proper m k color) :
    (∑ t : Fin n, k t) ≤ c * (n / m) := by
  classical
  have total : (∑ t : Fin n, k t) = (Finset.univ : Finset (Vertex k)).card := by
    simp only [Finset.card_univ, Fintype.card_sigma, Fintype.card_fin]
  rw [total, Finset.card_eq_sum_card_fiberwise
    (t := (Finset.univ : Finset (Fin c))) (f := color) (by intro x _; exact Finset.mem_univ _)]
  calc
    _ ≤ ∑ _z : Fin c, n / m := Finset.sum_le_sum (fun z _ =>
      color_class_packing hm hsize k color proper z)
    _ = c * (n / m) := by simp

/-- The sum of a wrapping block, expressed by its cumulative slot boundaries. -/
def Window (n m : Nat) (s : Nat → Nat) (i : Nat) : Nat :=
  if i + m ≤ n then s (i + m) - s i
    else s n - s i + s (i + m - n) - s 0

private theorem boundary_mono {n : Nat} (s : Nat → Nat)
    (step : ∀ i, i < n → s i < s (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → s i ≤ s j := by
  intro i j lower upper
  induction j with
  | zero =>
      have eq : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases eq : i = j + 1
      · subst i; exact le_rfl
      · exact (ih (by omega) (by omega)).trans (step j (by omega)).le

private theorem different_residues {c x y : Nat}
    (lt : x < y) (short : y < x + c) : x % c ≠ y % c := by
  intro equal
  have congruent : x ≡ y [MOD c] := equal
  obtain ⟨q, eq⟩ := (Nat.modEq_iff_exists_eq_add lt.le).mp congruent
  have positive : 1 ≤ q := by
    by_contra zero
    have qzero : q = 0 := by omega
    simp only [qzero, Nat.mul_zero, Nat.add_zero] at eq
    omega
  have bound := Nat.mul_le_mul_left c positive
  simp only [Nat.mul_one] at bound
  omega

/-- Positive cumulative blocks with bounded wrapping m-windows give a proper
coloring by selected slot residues. Ranks start at zero even for singleton demand. -/
theorem cyclic_slot_coloring {n m c : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (hc : 0 < c) (k : Fin n → Nat) (s : Nat → Nat)
    (zero : s 0 = 0) (step : ∀ i, i < n → s i < s (i + 1))
    (contains : ∀ t : Fin n, k t ≤ s (t.val + 1) - s t.val)
    (divisible : s n % c = 0)
    (windows : ∀ i, i < n → Window n m s i ≤ c) :
    Proper m k (fun x => (⟨(s x.1.val + x.2.val) % c,
      Nat.mod_lt _ hc⟩ : Fin c)) := by
  intro x y different near equal
  have residues := congrArg Fin.val equal
  have hx := x.1.isLt
  have hy := y.1.isLt
  have rx := x.2.isLt
  have ry := y.2.isLt
  have sx := step x.1.val hx
  have sy := step y.1.val hy
  have kx := contains x.1
  have ky := contains y.1
  have mono := boundary_mono s step
  have xslot : s x.1.val ≤ s x.1.val + x.2.val ∧
      s x.1.val + x.2.val < s (x.1.val + 1) := by omega
  have yslot : s y.1.val ≤ s y.1.val + y.2.val ∧
      s y.1.val + y.2.val < s (y.1.val + 1) := by omega
  have ordered (i j : Fin n) (r : Fin (k i)) (q : Fin (k j))
      (ij : i.val < j.val) (close : j.val < i.val + m) :
      (s i.val + r.val) % c ≠ (s j.val + q.val) % c := by
    have hi := i.isLt
    have hj := j.isLt
    have ri := r.isLt
    have qj := q.isLt
    have ki := contains i
    have kj := contains j
    have si := step i.val hi
    have sj := step j.val hj
    have between := mono (i.val + 1) j.val (by omega) (by omega)
    have before := mono i.val n (by omega) le_rfl
    have window := windows i.val hi
    unfold Window at window
    by_cases nowrap : i.val + m ≤ n
    · rw [if_pos nowrap] at window
      have endBound := mono (j.val + 1) (i.val + m) (by omega) nowrap
      apply different_residues <;> omega
    · rw [if_neg nowrap, zero] at window
      have endBound := mono (j.val + 1) n (by omega) le_rfl
      apply different_residues <;> omega
  have seam (i j : Fin n) (r : Fin (k i)) (q : Fin (k j))
      (ji : j.val < i.val) (close : n + j.val < i.val + m) :
      (s i.val + r.val) % c ≠ (s j.val + q.val) % c := by
    have hi := i.isLt
    have hj := j.isLt
    have ri := r.isLt
    have qj := q.isLt
    have ki := contains i
    have kj := contains j
    have si := step i.val hi
    have sj := step j.val hj
    have top := mono (i.val + 1) n (by omega) le_rfl
    have window := windows i.val hi
    have wraps : ¬ i.val + m ≤ n := by omega
    have endpoint := mono (j.val + 1) (i.val + m - n) (by omega) (by omega)
    have before := mono i.val n (by omega) le_rfl
    unfold Window at window
    rw [if_neg wraps, zero] at window
    have unequal : (s i.val + r.val) % c ≠ (s n + (s j.val + q.val)) % c := by
      apply different_residues <;> omega
    simpa only [Nat.add_mod, divisible, Nat.zero_add, Nat.mod_mod] using unequal
  by_cases same : x.1 = y.1
  · have ranks : x.2.val ≠ y.2.val := by
      intro h
      apply different
      cases x with
      | mk i r =>
          cases y with
          | mk j q =>
              simp only at same h
              subst j
              have rq : r = q := Fin.ext h
              subst q; rfl
    have window := windows x.1.val hx
    unfold Window at window
    have endBound : s (x.1.val + 1) ≤ s x.1.val + c := by
      by_cases nowrap : x.1.val + m ≤ n
      · rw [if_pos nowrap] at window
        have top := mono (x.1.val + 1) (x.1.val + m) (by omega) nowrap
        omega
      · rw [if_neg nowrap, zero] at window
        have top := mono (x.1.val + 1) n (by omega) le_rfl
        have before := mono x.1.val n (by omega) le_rfl
        omega
    have startEq : s x.1.val = s y.1.val := congrArg (fun t : Fin n => s t.val) same
    have endEq : s (x.1.val + 1) = s (y.1.val + 1) :=
      congrArg (fun t : Fin n => s (t.val + 1)) same
    by_cases ranksOrder : x.2.val < y.2.val
    · exact (different_residues (by omega) (by omega)) residues
    · exact (different_residues (by omega) (by omega)) residues.symm
  · have values : x.1.val ≠ y.1.val := fun h => same (Fin.ext h)
    rcases near with plain | seamXY | seamYX
    · by_cases order : x.1.val < y.1.val
      · exact ordered x.1 y.1 x.2 y.2 order plain.2 residues
      · exact ordered y.1 x.1 y.2 x.2 (by omega) plain.1 residues.symm
    · exact seam y.1 x.1 y.2 x.2 (by omega) seamXY residues.symm
    · exact seam x.1 y.1 x.2 y.2 (by omega) seamYX residues

private def countBefore (R : Finset Nat) (i : Nat) : Nat :=
  (R.filter (fun t => t < i)).card

private theorem countBefore_bound (R : Finset Nat) (i : Nat) : countBefore R i ≤ i := by
  apply (Finset.card_le_card (show R.filter (fun t => t < i) ⊆ Finset.range i from
    fun t ht => Finset.mem_range.mpr (Finset.mem_filter.mp ht).2)).trans_eq
  exact Finset.card_range i

private theorem countBefore_mono (R : Finset Nat) {i j : Nat} (h : i ≤ j) :
    countBefore R i ≤ countBefore R j :=
  Finset.card_le_card (fun _ ht => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp ht).1, lt_of_lt_of_le (Finset.mem_filter.mp ht).2 h⟩)

private theorem countBefore_step (R : Finset Nat) (i : Nat) :
    countBefore R (i + 1) = countBefore R i + if i ∈ R then 1 else 0 := by
  classical
  have shape : R.filter (fun t => t < i + 1) =
      if i ∈ R then insert i (R.filter (fun t => t < i)) else R.filter (fun t => t < i) := by
    ext t
    by_cases mem : i ∈ R
    · rw [if_pos mem]
      by_cases equal : t = i
      · subst t; simp [mem]
      · have arithmetic : t < i + 1 ↔ t < i := by omega
        simp only [Finset.mem_filter, Finset.mem_insert, equal, false_or, arithmetic]
    · rw [if_neg mem]
      by_cases equal : t = i
      · subst t; simp [mem]
      · have arithmetic : t < i + 1 ↔ t < i := by omega
        simp only [Finset.mem_filter, arithmetic]
  unfold countBefore
  rw [shape]
  split_ifs <;> simp

private theorem countBefore_total {n : Nat} (R : Finset Nat) (within : R ⊆ Finset.range n) :
    countBefore R n = R.card := by
  unfold countBefore
  congr 1
  exact Finset.filter_eq_self.mpr (fun t ht => Finset.mem_range.mp (within ht))

/-- Shortening selected singleton blocks supplies the 2m-color construction.
The selected set may have any placement around the seam. -/
theorem low_slot_formula_valid {n m a rho : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (decomposition : n = m * a + rho) (k : Fin n → Nat)
    (demands : ∀ t, k t = 1 ∨ k t = 2)
    (R : Finset Nat) (within : R ⊆ Finset.range n) (removed : R.card = 2 * rho)
    (singletons : ∀ t : Fin n, t.val ∈ R → k t = 1) :
    let s : Nat → Nat := fun i => 2 * i - (R.filter (fun t => t < i)).card
    s 0 = 0 ∧ (∀ i, s (i + 1) - s i = if i ∈ R then 1 else 2) ∧
      s n = (2 * m) * a ∧
      Proper m k (fun x => (⟨(s x.1.val + x.2.val) % (2 * m),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 * m))) := by
  classical
  let s : Nat → Nat := fun i => 2 * i - countBefore R i
  have bounds := countBefore_bound R
  have zero : s 0 = 0 := by simp [s, countBefore]
  have steps (i : Nat) : s (i + 1) - s i = if i ∈ R then 1 else 2 := by
    have ci := bounds i
    have cj := bounds (i + 1)
    have increment := countBefore_step R i
    dsimp [s]
    split_ifs at increment ⊢ <;> omega
  have positive (i : Nat) : s i < s (i + 1) := by
    have ci := bounds i
    have cj := bounds (i + 1)
    have increment := countBefore_step R i
    dsimp [s]
    split_ifs at increment <;> omega
  have contains (t : Fin n) : k t ≤ s (t.val + 1) - s t.val := by
    rw [steps]
    by_cases mem : t.val ∈ R
    · rw [if_pos mem, singletons t mem]
    · rw [if_neg mem]; rcases demands t with h | h <;> omega
  have total : s n = (2 * m) * a := by
    have count := countBefore_total R within
    have b := bounds n
    dsimp [s]
    rw [count, removed, decomposition]
    have expansion : 2 * (m * a + rho) = (2 * m) * a + 2 * rho := by ring
    omega
  have windows (i : Nat) (hi : i < n) : Window n m s i ≤ 2 * m := by
    unfold Window
    by_cases nowrap : i + m ≤ n
    · rw [if_pos nowrap]
      have ci := bounds i
      have ce := bounds (i + m)
      have increasing := countBefore_mono R (by omega : i ≤ i + m)
      dsimp [s]
      omega
    · rw [if_neg nowrap, zero]
      have ci := bounds i
      have cn := bounds n
      have ce := bounds (i + m - n)
      have increasing := countBefore_mono R (by omega : i ≤ n)
      dsimp [s]
      omega
  refine ⟨zero, steps, total, ?_⟩
  apply cyclic_slot_coloring hm hsize (by omega) k s zero
    (fun i _ => positive i) contains
  · rw [total]; simp
  · exact windows

/-- The shortened-slot formula supplies the chosen coloring. -/
theorem low_slot_construction {n m a rho : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (decomposition : n = m * a + rho) (k : Fin n → Nat)
    (demands : ∀ t, k t = 1 ∨ k t = 2)
    (R : Finset Nat) (within : R ⊆ Finset.range n) (removed : R.card = 2 * rho)
    (singletons : ∀ t : Fin n, t.val ∈ R → k t = 1) :
    ∃ color : Vertex k → Fin (2 * m), Proper m k color := by
  classical
  let s : Nat → Nat := fun i => 2 * i - (R.filter (fun t => t < i)).card
  have formula := low_slot_formula_valid hm hsize decomposition k demands R within removed singletons
  exact ⟨fun x => ⟨(s x.1.val + x.2.val) % (2 * m), Nat.mod_lt _ (by omega)⟩,
    formula.2.2.2⟩

/-- The low branch selects exactly 2rho of the actual singleton prefixes. -/
theorem low_branch_coloring {n m a rho : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (decomposition : n = m * a + rho) (k : Fin n → Nat)
    (demands : ∀ t, k t = 1 ∨ k t = 2)
    (enough : 2 * rho ≤ ((Finset.univ : Finset (Fin n)).filter (fun t => k t = 1)).card) :
    ∃ color : Vertex k → Fin (2 * m), Proper m k color := by
  classical
  obtain ⟨Q, subset, count⟩ := Finset.exists_subset_card_eq enough
  let R := Q.image Fin.val
  have within : R ⊆ Finset.range n := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr i.isLt
  have removed : R.card = 2 * rho := by
    rw [Finset.card_image_of_injective _ Fin.val_injective, count]
  have singletons (t : Fin n) (ht : t.val ∈ R) : k t = 1 := by
    obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp ht
    have ti : i = t := Fin.ext eq
    subst i
    exact (Finset.mem_filter.mp (subset hi)).2
  exact low_slot_construction hm hsize decomposition k demands R within removed singletons

private theorem spaced_window_count {n m : Nat} (hsize : m ≤ n)
    (R : Finset Nat) (within : R ⊆ Finset.range n)
    (spaced : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      ¬ ((x < y + m ∧ y < x + m) ∨ n + x < y + m ∨ n + y < x + m))
    (i : Nat) (hi : i < n) :
    if i + m ≤ n then countBefore R (i + m) ≤ countBefore R i + 1
      else R.card + countBefore R (i + m - n) ≤ countBefore R i + 1 := by
  classical
  by_cases nowrap : i + m ≤ n
  · rw [if_pos nowrap]
    let W := R.filter (fun t => i ≤ t ∧ t < i + m)
    have atMost : W.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      by_contra different
      obtain ⟨xR, xlow, xhigh⟩ := Finset.mem_filter.mp hx
      obtain ⟨yR, ylow, yhigh⟩ := Finset.mem_filter.mp hy
      exact spaced x xR y yR different (by omega)
    have partition := Finset.card_filter_add_card_filter_not
      (s := R.filter (fun t => t < i + m)) (p := fun t => t < i)
    have first : (R.filter (fun t => t < i + m)).filter (fun t => t < i) =
        R.filter (fun t => t < i) := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨member, _⟩, small⟩; exact ⟨member, small⟩
      · rintro ⟨member, small⟩; exact ⟨⟨member, by omega⟩, small⟩
    have second : (R.filter (fun t => t < i + m)).filter (fun t => ¬ t < i) = W := by
      ext t
      simp only [W, Finset.mem_filter]
      constructor
      · rintro ⟨⟨member, upper⟩, lower⟩; exact ⟨member, by omega, upper⟩
      · rintro ⟨member, lower, upper⟩; exact ⟨⟨member, upper⟩, by omega⟩
    rw [first, second] at partition
    change countBefore R i + W.card = countBefore R (i + m) at partition
    omega
  · rw [if_neg nowrap]
    let e := i + m - n
    let tail := R.filter (fun t => ¬ t < i)
    let head := R.filter (fun t => t < e)
    let W := tail ∪ head
    have endpoint : e ≤ i := by dsimp [e]; omega
    have atMost : W.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      by_contra different
      have mx : x ∈ R ∧ (i ≤ x ∨ x < e) := by
        simpa only [W, tail, head, Finset.mem_union, Finset.mem_filter, not_lt,
          ← and_or_left] using hx
      have my : y ∈ R ∧ (i ≤ y ∨ y < e) := by
        simpa only [W, tail, head, Finset.mem_union, Finset.mem_filter, not_lt,
          ← and_or_left] using hy
      have xn := Finset.mem_range.mp (within mx.1)
      have yn := Finset.mem_range.mp (within my.1)
      apply spaced x mx.1 y my.1 different
      dsimp [e] at mx my
      omega
    have disjoint : Disjoint tail head := by
      apply Finset.disjoint_left.mpr
      intro t ht hh
      have left := (Finset.mem_filter.mp ht).2
      have right := (Finset.mem_filter.mp hh).2
      omega
    have unionCount : W.card = tail.card + head.card := Finset.card_union_of_disjoint disjoint
    have partition := Finset.card_filter_add_card_filter_not (s := R) (p := fun t => t < i)
    change countBefore R i + tail.card = R.card at partition
    change W.card = tail.card + countBefore R e at unionCount
    dsimp [e] at unionCount
    omega

/-- Adding one extra slot at each cyclically m-separated prefix supplies a
(2m+1)-coloring whenever its total slot count is divisible by 2m+1. -/
private theorem spaced_slot_formula_valid {n m : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (k : Fin n → Nat) (demands : ∀ t, k t ≤ 2)
    (R : Finset Nat) (within : R ⊆ Finset.range n)
    (spaced : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      ¬ ((x < y + m ∧ y < x + m) ∨ n + x < y + m ∨ n + y < x + m))
    (divisible : (2 * n + R.card) % (2 * m + 1) = 0) :
    let s : Nat → Nat := fun i => 2 * i + (R.filter (fun t => t < i)).card
    Proper m k (fun x => (⟨(s x.1.val + x.2.val) % (2 * m + 1),
      Nat.mod_lt _ (by omega)⟩ : Fin (2 * m + 1))) := by
  classical
  let s : Nat → Nat := fun i => 2 * i + countBefore R i
  have zero : s 0 = 0 := by simp [s, countBefore]
  have steps (i : Nat) : 2 ≤ s (i + 1) - s i := by
    have increment := countBefore_step R i
    dsimp [s]
    split_ifs at increment <;> omega
  have positive (i : Nat) : s i < s (i + 1) := by have h := steps i; omega
  have contains (t : Fin n) : k t ≤ s (t.val + 1) - s t.val :=
    (demands t).trans (steps t.val)
  have total : s n = 2 * n + R.card := by
    dsimp [s]; rw [countBefore_total R within]
  have windows (i : Nat) (hi : i < n) : Window n m s i ≤ 2 * m + 1 := by
    have count := spaced_window_count hsize R within spaced i hi
    have increasing := countBefore_mono R (by omega : i ≤ n)
    have all := countBefore_total R within
    unfold Window
    by_cases nowrap : i + m ≤ n
    · rw [if_pos nowrap] at count ⊢
      have mono := countBefore_mono R (by omega : i ≤ i + m)
      dsimp [s]; omega
    · rw [if_neg nowrap] at count ⊢
      dsimp [s]
      rw [show countBefore R 0 = 0 by simp [countBefore]]
      omega
  exact cyclic_slot_coloring hm hsize (by omega) k s zero (fun i _ => positive i)
    contains (by rwa [total]) windows

/-- Spaced slots supply the chosen coloring. -/
theorem spaced_slot_construction {n m : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (k : Fin n → Nat) (demands : ∀ t, k t ≤ 2)
    (R : Finset Nat) (within : R ⊆ Finset.range n)
    (spaced : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      ¬ ((x < y + m ∧ y < x + m) ∨ n + x < y + m ∨ n + y < x + m))
    (divisible : (2 * n + R.card) % (2 * m + 1) = 0) :
    ∃ color : Vertex k → Fin (2 * m + 1), Proper m k color := by
  classical
  let s : Nat → Nat := fun i => 2 * i + (R.filter (fun t => t < i)).card
  exact ⟨fun x => ⟨(s x.1.val + x.2.val) % (2 * m + 1), Nat.mod_lt _ (by omega)⟩,
    spaced_slot_formula_valid hm hsize k demands R within spaced divisible⟩

/-- Multiples 0,m,...,(z-1)m with z=(a-2rho) mod (2m+1) are cyclically
m-separated and make the slot total divisible. Actual singleton positions are unrestricted. -/
theorem high_slot_formula_valid {n m a rho : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (decomposition : n = m * a + rho) (slack : 2 * rho ≤ a)
    (k : Fin n → Nat) (demands : ∀ t, k t ≤ 2) :
    let c := 2 * m + 1
    let z := (a - 2 * rho) % c
    let R := (Finset.range z).image (fun q => q * m)
    let s : Nat → Nat := fun i => 2 * i + (R.filter (fun t => t < i)).card
    s 0 = 0 ∧ s n = 2 * n + z ∧
      Proper m k (fun x => (⟨(s x.1.val + x.2.val) % c,
        Nat.mod_lt _ (by omega)⟩ : Fin c)) := by
  classical
  let c := 2 * m + 1
  let z := (a - 2 * rho) % c
  let R := (Finset.range z).image (fun q => q * m)
  have za : z ≤ a := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  have multiplication (q r : Nat) (eq : q * m = r * m) : q = r :=
    Nat.eq_of_mul_eq_mul_right hm eq
  have count : R.card = z := by
    rw [Finset.card_image_of_injective _ (fun q r eq => multiplication q r eq), Finset.card_range]
  have endBound (q : Nat) (hq : q < z) : q * m + m ≤ n := by
    have bound := Nat.mul_le_mul_right m (by omega : q + 1 ≤ a)
    rw [Nat.add_mul, Nat.one_mul] at bound
    have commute : a * m = m * a := Nat.mul_comm _ _
    omega
  have within : R ⊆ Finset.range n := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    have lastBound := endBound q (Finset.mem_range.mp hq)
    exact Finset.mem_range.mpr (by omega)
  have spaced : ∀ x ∈ R, ∀ y ∈ R, x ≠ y →
      ¬ ((x < y + m ∧ y < x + m) ∨ n + x < y + m ∨ n + y < x + m) := by
    intro x hx y hy different close
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have eq : q ≠ r := by intro h; subst r; exact different rfl
    have qend := endBound q (Finset.mem_range.mp hq)
    have rend := endBound r (Finset.mem_range.mp hr)
    have gap : q * m + m ≤ r * m ∨ r * m + m ≤ q * m := by
      rcases lt_or_gt_of_ne eq with order | order
      · left
        have bound := Nat.mul_le_mul_right m (by omega : q + 1 ≤ r)
        simpa only [Nat.add_mul, Nat.one_mul] using bound
      · right
        have bound := Nat.mul_le_mul_right m (by omega : r + 1 ≤ q)
        simpa only [Nat.add_mul, Nat.one_mul] using bound
    omega
  have divisible : (2 * n + R.card) % (2 * m + 1) = 0 := by
    have arithmetic : 2 * n + (a - 2 * rho) = c * a := by
      have expansion : (2 * m + 1) * a = 2 * (m * a) + a := by ring
      dsimp [c]
      omega
    have division := Nat.mod_add_div (a - 2 * rho) c
    change z + c * ((a - 2 * rho) / c) = a - 2 * rho at division
    have balance : 2 * n + z + c * ((a - 2 * rho) / c) = c * a := by omega
    have mod := congrArg (fun t => t % c) balance
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] at mod
    simpa [count, c, Nat.add_mod] using mod
  refine ⟨by simp, ?_, spaced_slot_formula_valid hm hsize k demands R within spaced divisible⟩
  change 2 * n + countBefore R n = 2 * n + z
  rw [countBefore_total R within, count]

/-- The high-slot formula supplies the chosen coloring. -/
theorem high_branch_coloring {n m a rho : Nat} (hm : 0 < m) (hsize : m ≤ n)
    (decomposition : n = m * a + rho) (slack : 2 * rho ≤ a)
    (k : Fin n → Nat) (demands : ∀ t, k t ≤ 2) :
    ∃ color : Vertex k → Fin (2 * m + 1), Proper m k color := by
  classical
  let c := 2 * m + 1
  let z := (a - 2 * rho) % c
  let R := (Finset.range z).image (fun q => q * m)
  let s : Nat → Nat := fun i => 2 * i + (R.filter (fun t => t < i)).card
  have formula := high_slot_formula_valid hm hsize decomposition slack k demands
  exact ⟨fun x => ⟨(s x.1.val + x.2.val) % c, Nat.mod_lt _ (by omega)⟩, formula.2.2⟩

/-- The prefix at a cyclic offset, with at most one crossing of the seam. -/
def cyclicIndex {n m : Nat} (hsize : m ≤ n) (start : Fin n) (i : Fin m) : Fin n :=
  ⟨if start.val + i.val < n then start.val + i.val else start.val + i.val - n, by
    have hs := start.isLt
    have hi := i.isLt
    split_ifs <;> omega⟩

/-- An m-consecutive double-demand window is a clique of 2m live types. -/
theorem double_window_lower_bound {n m c : Nat} (hsize : m ≤ n)
    (k : Fin n → Nat) (start : Fin n)
    (window : ∀ i : Fin m, k (cyclicIndex hsize start i) = 2)
    (color : Vertex k → Fin c) (proper : Proper m k color) : 2 * m ≤ c := by
  let v : Fin m × Fin 2 → Vertex k := fun x =>
    ⟨cyclicIndex hsize start x.1, ⟨x.2.val, by rw [window]; exact x.2.isLt⟩⟩
  have injective : Function.Injective v := by
    intro x y equal
    have indices := congrArg (fun t : Vertex k => t.1.val) equal
    have ranks := congrArg (fun t : Vertex k => t.2.val) equal
    have hs := start.isLt
    have hx := x.1.isLt
    have hy := y.1.isLt
    dsimp [v, cyclicIndex] at indices ranks
    have first : x.1 = y.1 := by
      apply Fin.ext
      split_ifs at indices <;> omega
    exact Prod.ext first (Fin.ext ranks)
  have near (x y : Fin m × Fin 2) : Near m (v x).1 (v y).1 := by
    have hs := start.isLt
    have hx := x.1.isLt
    have hy := y.1.isLt
    dsimp [Near, v, cyclicIndex]
    split_ifs <;> omega
  have colorInj : Function.Injective (fun x => color (v x)) := by
    intro x y equal
    by_contra different
    have vertexDiff : v x ≠ v y := fun h => different (injective h)
    exact proper (v x) (v y) vertexDiff (near x y) equal
  have bound := Fintype.card_le_of_injective (fun x => color (v x)) colorInj
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm m 2] using bound

private theorem demand_total {n : Nat} (k : Fin n → Nat)
    (demands : ∀ t, k t = 1 ∨ k t = 2) :
    (∑ t : Fin n, k t) + ((Finset.univ : Finset (Fin n)).filter (fun t => k t = 1)).card =
      2 * n := by
  classical
  have pointwise (t : Fin n) : k t + (if k t = 1 then (1 : Nat) else 0) = 2 := by
    rcases demands t with h | h <;> simp [h]
  calc
    _ = ∑ t : Fin n, (k t + if k t = 1 then (1 : Nat) else 0) := by
      simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
    _ = ∑ _t : Fin n, (2 : Nat) := Finset.sum_congr rfl (fun t _ => pointwise t)
    _ = 2 * n := by simp [Nat.mul_comm]


private theorem ceiling_formula {n m a rho L : Nat} (hm : 0 < m)
    (large : 2 * m < n) (decomposition : n = m * a + rho)
    (remainder : rho < m) (slack : 2 * rho ≤ a) (count : L ≤ 2 * n) :
    max (2 * m) ((2 * n - L + a - 1) / a) =
      2 * m + if L < 2 * rho then 1 else 0 := by
  have apos : 0 < a := by
    by_contra nope
    have azero : a = 0 := by omega
    rw [azero, Nat.mul_zero] at decomposition
    omega
  have expansion : 2 * n = (2 * m) * a + 2 * rho := by rw [decomposition]; ring
  have upper : 2 * n - L ≤ (2 * m + 1) * a := by
    have product : (2 * m + 1) * a = (2 * m) * a + a := by ring
    omega
  by_cases high : L < 2 * rho
  · rw [if_pos high]
    have lower : (2 * m + 1) * a ≤ 2 * n - L + a - 1 := by
      have product : (2 * m + 1) * a = (2 * m) * a + a := by ring
      omega
    have ceilLower := (Nat.le_div_iff_mul_le apos).mpr lower
    have ceilUpper : (2 * n - L + a - 1) / a < 2 * m + 2 := by
      apply (Nat.div_lt_iff_lt_mul apos).mpr
      have product : (2 * m + 2) * a = (2 * m + 1) * a + a := by ring
      omega
    have value : (2 * n - L + a - 1) / a = 2 * m + 1 := by omega
    rw [value, max_eq_right (by omega)]
  · rw [if_neg high, Nat.add_zero]
    have ceilUpper : (2 * n - L + a - 1) / a < 2 * m + 1 := by
      apply (Nat.div_lt_iff_lt_mul apos).mpr
      have product : (2 * m + 1) * a = (2 * m) * a + a := by ring
      omega
    exact max_eq_left (by omega)

/-- The exact mixed-demand cyclic minimum, with unrestricted singleton placement. -/
theorem mixed_demand_minimum {n m a rho : Nat} (hm : 2 ≤ m)
    (large : 2 * m < n) (decomposition : n = m * a + rho)
    (remainder : rho < m) (slack : 2 * rho ≤ a)
    (k : Fin n → Nat) (demands : ∀ t, k t = 1 ∨ k t = 2)
    (start : Fin n)
    (window : ∀ i : Fin m, k (cyclicIndex (by omega : m ≤ n) start i) = 2) :
    let L := ((Finset.univ : Finset (Fin n)).filter (fun t => k t = 1)).card
    let capacity := max (2 * m) ((2 * n - L + a - 1) / a)
    IsLeast {c : Nat | ∃ color : Vertex k → Fin c, Proper m k color} capacity ∧
      capacity = 2 * m + if L < 2 * rho then 1 else 0 := by
  classical
  let L := ((Finset.univ : Finset (Fin n)).filter (fun t => k t = 1)).card
  have hsize : m ≤ n := by omega
  have quotient : n / m = a := by
    rw [decomposition, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < m),
      Nat.div_eq_of_lt remainder]
    omega
  have total := demand_total k demands
  change (∑ t : Fin n, k t) + L = 2 * n at total
  have formula := ceiling_formula (by omega : 0 < m) large decomposition remainder slack
    (show L ≤ 2 * n by omega)
  change IsLeast {c : Nat | ∃ color : Vertex k → Fin c, Proper m k color}
    (max (2 * m) ((2 * n - L + a - 1) / a)) ∧
    max (2 * m) ((2 * n - L + a - 1) / a) = 2 * m + if L < 2 * rho then 1 else 0
  refine ⟨?_, formula⟩
  rw [formula]
  constructor
  · change ∃ color : Vertex k → Fin (2 * m + if L < 2 * rho then 1 else 0), Proper m k color
    by_cases high : L < 2 * rho
    · rw [if_pos high]
      exact high_branch_coloring (by omega) hsize decomposition slack k
        (fun t => by rcases demands t with h | h <;> omega)
    · rw [if_neg high, Nat.add_zero]
      exact low_branch_coloring (by omega) hsize decomposition k demands (by omega)
  · intro c member
    obtain ⟨color, proper⟩ := member
    have clique := double_window_lower_bound hsize k start window color proper
    have packing := packing_lower_bound (by omega : 0 < m) hsize k color proper
    rw [quotient] at packing
    change 2 * m + (if L < 2 * rho then 1 else 0) ≤ c
    by_cases high : L < 2 * rho
    · rw [if_pos high]
      by_contra tooSmall
      have equal : c = 2 * m := by omega
      rw [equal] at packing
      have expansion : 2 * n = (2 * m) * a + 2 * rho := by rw [decomposition]; ring
      omega
    · rw [if_neg high]; omega

end D5.S3.Combinatorics.Graph.CyclicMixedDemandColoring
