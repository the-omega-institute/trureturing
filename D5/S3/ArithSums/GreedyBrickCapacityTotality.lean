/- GID: D5/S3/ArithSums/GreedyBrickCapacityTotality
   generality: G
   mirror-B: D5/B/S3/ArithSums/GreedyBrickCapacityTotality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Intervals]
   utility: none
   digest: Capacity totality, row conjugacy, and exact supported integer-cell placement. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
Finite capacities are stored from top to bottom. A list of length h stores
c_h,...,c_1; there is no floor capacity and no absent-row birth value.
The transition conjugacy and supported integer-cell geometry are established
below. The A395531 self-composition identity is not asserted.
-/

namespace D5.S3.ArithSums.GreedyBrickCapacityTotality

/-- Scan downwards. The Boolean means that the brick must be received by
the row immediately above this list. The first eligible donor ends the scan;
an empty list is the unbounded floor. -/
def transfer (n : ℕ) : List ℕ → List ℕ × Bool
  | [] => ([], true)
  | c :: cs =>
    if n ≤ c then ((c - n) :: cs, true)
    else
      let t := transfer n cs
      if t.2 then ((c + n) :: t.1, false) else (c :: t.1, false)

/-- One literal brick placement. A carry at the top creates exactly one row. -/
def step (n : ℕ) (cs : List ℕ) : List ℕ :=
  let t := transfer n cs
  if t.2 then n :: t.1 else t.1

/-- Weighted capacity area, with the source's bin indices 1,...,h. -/
def area : List ℕ → ℕ
  | [] => 0
  | c :: cs => (cs.length + 1) * c + area cs

/-- Reconstructed occupied widths, from the top row downwards. The gaps
are the capacities; summing each initial segment recovers a row width. -/
def widths : List ℕ → List ℕ
  | [] => []
  | c :: cs => c :: (widths cs).map (fun w => c + w)

/-- Recover successive gaps from occupied widths. On decreasing geometric
rows the source bin c_i is w_(i-1)-w_i, and the top bin is the top width;
the list is ordered in the reverse direction. -/
def capacities : List ℕ → List ℕ
  | [] => []
  | w :: ws => w :: capacities (ws.map (fun v => v - w))
termination_by ws => ws.length
decreasing_by simp

/-- The published top-down scan over existing rows. The final row is the
floor and is always eligible. Widths are listed from top to bottom. -/
def extendRow (n : ℕ) : List ℕ → List ℕ
  | [] => [n]
  | [w] => [w + n]
  | w :: v :: ws =>
    if w + n ≤ v then (w + n) :: v :: ws
    else w :: extendRow n (v :: ws)

/-- Literal Python source rule: test birth at the top, otherwise scan
existing rows downwards and extend the first supported one. -/
def sourceRowStep (n : ℕ) : List ℕ → List ℕ
  | [] => [n]
  | w :: ws => if n ≤ w then n :: w :: ws else extendRow n (w :: ws)

/-- Exact transition correspondence between capacities and occupied rows. -/
def RowTransitionCorrespondence : Prop :=
  ∀ n cs, 0 < n → widths (step n cs) = sourceRowStep n (widths cs)

/-- The actual deterministic trajectory after N bricks. -/
def trajectory : ℕ → List ℕ
  | 0 => []
  | N + 1 => step (N + 1) (trajectory N)

private theorem transfer_invariants (n : ℕ) (hn : 0 < n) (cs : List ℕ)
    (hc : ∀ c ∈ cs, c ≤ 2 * n - 1) :
    (transfer n cs).1.length = cs.length ∧
    (∀ c ∈ (transfer n cs).1, c ≤ 2 * n - 1) ∧
    area (transfer n cs).1 + (if (transfer n cs).2 then cs.length * n else 0) =
      area cs + (if (transfer n cs).2 then 0 else n) := by
  induction cs with
  | nil => simp [transfer, area]
  | cons c cs ih =>
    have hcs : ∀ d ∈ cs, d ≤ 2 * n - 1 := by
      intro d hd
      exact hc d (List.mem_cons_of_mem c hd)
    have hc' := hc c (by simp)
    obtain ⟨hl, hb, ha⟩ := ih hcs
    by_cases he : n ≤ c
    · simp only [transfer, if_pos he, List.length_cons,
        ↓reduceIte, area]
      refine ⟨by trivial, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · omega
        · exact hcs d hd
      · have hex := Nat.sub_add_cancel he
        nlinarith
    · simp only [transfer, if_neg he]
      cases ht : (transfer n cs).2
      · simp only [ht, Bool.false_eq_true, ↓reduceIte,
          List.length_cons, area] at *
        refine ⟨by omega, ?_, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hc'
          · exact hb d hd
        · rw [hl]
          omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte,
          List.length_cons, area] at *
        refine ⟨by omega, ?_, ?_⟩
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · omega
          · exact hb d hd
        · rw [hl]
          nlinarith

/-- Highest-eligible selection gives the uniform capacity cap and exact area
increment; list length can increase only by one and never decreases. -/
theorem step_invariants (n : ℕ) (hn : 0 < n) (cs : List ℕ)
    (hc : ∀ c ∈ cs, c ≤ 2 * n - 1) :
    cs.length ≤ (step n cs).length ∧
    (step n cs).length ≤ cs.length + 1 ∧
    (∀ c ∈ step n cs, c ≤ 2 * n - 1) ∧
    area (step n cs) = area cs + n := by
  obtain ⟨hl, hb, ha⟩ := transfer_invariants n hn cs hc
  unfold step
  cases ht : (transfer n cs).2
  · simp only [ht, Bool.false_eq_true, ↓reduceIte] at *
    exact ⟨by omega, by omega, hb, by omega⟩
  · simp only [ht, ↓reduceIte, List.length_cons, area] at *
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · exact hb c hc
    · nlinarith

/-- Source-capacity bounds and the exact sum of all brick widths. -/
theorem reachable_invariants (N : ℕ) :
    (∀ c ∈ trajectory N, c ≤ 2 * N - 1) ∧
    area (trajectory N) = ∑ i ∈ Finset.range (N + 1), i ∧
    (trajectory N).length ≤ (trajectory (N + 1)).length ∧
    (trajectory (N + 1)).length ≤ (trajectory N).length + 1 := by
  have base : ∀ N, (∀ c ∈ trajectory N, c ≤ 2 * N - 1) ∧
      area (trajectory N) = ∑ i ∈ Finset.range (N + 1), i := by
    intro N
    induction N with
    | zero => simp [trajectory, area]
    | succ N ih =>
      have hc : ∀ c ∈ trajectory N, c ≤ 2 * (N + 1) - 1 := by
        intro c hc
        have := ih.1 c hc
        omega
      obtain ⟨_, _, hb, ha⟩ := step_invariants (N + 1) (by omega) (trajectory N) hc
      refine ⟨hb, ?_⟩
      change area (step (N + 1) (trajectory N)) = _
      rw [ha, ih.2]
      exact (Finset.sum_range_succ (fun i : ℕ => i) (N + 1)).symm
  obtain ⟨hb, ha⟩ := base N
  have hc : ∀ c ∈ trajectory N, c ≤ 2 * (N + 1) - 1 := by
    intro c hc
    have := hb c hc
    omega
  obtain ⟨hl, hu, _, _⟩ := step_invariants (N + 1) (by omega) (trajectory N) hc
  exact ⟨hb, ha, hl, hu⟩

/-- Reachable reconstructed rows have positive occupied widths, increase
downwards, and their area is the weighted capacity area. This is an algebraic
row representation; geometric placement/source correspondence is not assumed. -/
theorem reachable_rows (N : ℕ) (hN : 0 < N) :
    (widths (trajectory N)).length = (trajectory N).length ∧
    (widths (trajectory N)).Pairwise (· ≤ ·) ∧
    (widths (trajectory N)).sum = area (trajectory N) ∧
    capacities (widths (trajectory N)) = trajectory N ∧
    (∀ w ∈ widths (trajectory N), 0 < w) := by
  have reconstruction : ∀ cs : List ℕ,
      (widths cs).length = cs.length ∧
      (widths cs).Pairwise (· ≤ ·) ∧ (widths cs).sum = area cs := by
    intro cs
    induction cs with
    | nil => simp [widths, area]
    | cons c cs ih =>
      obtain ⟨hl, hp, ha⟩ := ih
      refine ⟨by simp [widths, hl], ?_, ?_⟩
      · rw [widths, List.pairwise_cons]
        constructor
        · intro w hw
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
          omega
        · exact hp.map (fun w => c + w) (fun a b hab => by omega)
      · simp only [widths, List.sum_cons]
        rw [List.sum_map_add (l := widths cs) (f := fun _ => c) (g := fun w => w)]
        simp only [List.map_const', List.sum_replicate, List.map_id',
          nsmul_eq_mul, Nat.cast_id, hl, ha, area, Nat.add_mul, Nat.one_mul]
        omega
  have top_positive : ∀ K, 0 < K →
      ∃ c cs, trajectory K = c :: cs ∧ 0 < c := by
    intro K
    induction K with
    | zero => omega
    | succ K ih =>
      intro _
      by_cases hK : K = 0
      · subst K
        exact ⟨1, [], by simp [trajectory, step, transfer], by omega⟩
      · obtain ⟨c, cs, heq, hc⟩ := ih (by omega)
        rw [trajectory, heq]
        by_cases he : K + 1 ≤ c
        · exact ⟨K + 1, (c - (K + 1)) :: cs, by simp [step, transfer, he], by omega⟩
        · cases ht : (transfer (K + 1) cs).2
          · exact ⟨c, (transfer (K + 1) cs).1, by simp [step, transfer, he, ht], hc⟩
          · exact ⟨c + (K + 1), (transfer (K + 1) cs).1,
              by simp [step, transfer, he, ht], by omega⟩
  obtain ⟨hl, hp, ha⟩ := reconstruction (trajectory N)
  have inverse : ∀ cs : List ℕ, capacities (widths cs) = cs := by
    intro cs
    induction cs with
    | nil => simp [widths, capacities]
    | cons c cs ih => simp [widths, capacities, List.map_map, Function.comp_def, ih]
  refine ⟨hl, hp, ha, inverse _, ?_⟩
  obtain ⟨c, cs, heq, hc⟩ := top_positive N hN
  rw [heq, widths]
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hc
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    omega

/-- Every positive height is attained for the first time at an actual brick,
with the explicit source-capacity bound. Minimality is about the trajectory,
not a default value assigned to a missing row. -/
theorem birth_totality (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : ℕ, 0 < B ∧ (trajectory B).length = m ∧
      (∀ K < B, (trajectory K).length < m) ∧
      B ≤ if m = 1 then 1 else 2 * m * (m - 1) - 1 := by
  have area_bound : ∀ (cs : List ℕ) (cap : ℕ),
      (∀ c ∈ cs, c ≤ cap) →
      area cs ≤ cap * (∑ i ∈ Finset.range (cs.length + 1), i) := by
    intro cs
    induction cs with
    | nil => intro cap hc; simp [area]
    | cons c cs ih =>
      intro cap hc
      have hc' := hc c (by simp)
      have hb := ih cap (fun d hd => hc d (List.mem_cons_of_mem c hd))
      simp only [area, List.length_cons]
      rw [Finset.sum_range_succ (fun i : ℕ => i) (cs.length + 1)]
      nlinarith
  have obstruction : ∀ N, 0 < N →
      N + 1 < 2 * (trajectory N).length * ((trajectory N).length + 1) := by
    intro N hn
    let cs := trajectory N
    let t := ∑ i ∈ Finset.range (cs.length + 1), i
    obtain ⟨hc, ha, _, _⟩ := reachable_invariants N
    have hab := area_bound cs (2 * N - 1) hc
    have har : area cs * 2 = N * (N + 1) := by
      rw [ha]
      have h := Finset.sum_range_id_mul_two (N + 1)
      simpa [Nat.add_sub_cancel, Nat.mul_comm] using h
    have ht : t * 2 = cs.length * (cs.length + 1) := by
      have h := Finset.sum_range_id_mul_two (cs.length + 1)
      simpa [t, Nat.add_sub_cancel, Nat.mul_comm] using h
    have htp : 0 < t := by
      change area cs ≤ (2 * N - 1) * t at hab
      by_contra h
      have hz : t = 0 := by omega
      rw [hz, Nat.mul_zero] at hab
      have hz' : area cs = 0 := by omega
      rw [hz'] at har
      nlinarith
    have hsub : 2 * N - 1 + 1 = 2 * N := by omega
    have has : area cs < (2 * N) * t := by
      change area cs ≤ (2 * N - 1) * t at hab
      nlinarith
    have hs : N * (N + 1) < N * (2 * cs.length * (cs.length + 1)) := by
      nlinarith
    exact (Nat.mul_lt_mul_left hn).mp hs
  let bound := if m = 1 then 1 else 2 * m * (m - 1) - 1
  have crosses : m ≤ (trajectory bound).length := by
    by_cases hm1 : m = 1
    · subst m
      simp [bound, trajectory, step, transfer]
    · have hm2 : 2 ≤ m := by omega
      have hprod : 0 < 2 * m * (m - 1) := by
        have hpred : 0 < m - 1 := by omega
        positivity
      have hp2 : 2 ≤ 2 * m * (m - 1) := by
        have hpred : 1 ≤ m - 1 := by omega
        nlinarith
      have hbound : bound = 2 * m * (m - 1) - 1 := by simp [bound, hm1]
      have hbpos : 0 < bound := by omega
      have ho := obstruction bound hbpos
      by_contra h
      have hh : (trajectory bound).length ≤ m - 1 := by omega
      have hsum : (trajectory bound).length + 1 ≤ m := by omega
      have hmult := Nat.mul_le_mul hh hsum
      have heq : bound + 1 = 2 * m * (m - 1) := by omega
      nlinarith
  have exists_cross : ∃ N, m ≤ (trajectory N).length := ⟨bound, crosses⟩
  let B := Nat.find exists_cross
  have hB := Nat.find_spec exists_cross
  have hmin : ∀ K < B, (trajectory K).length < m := by
    intro K hK
    have h := Nat.find_min exists_cross hK
    omega
  have hpos : 0 < B := by
    by_contra h
    have hb0 : B = 0 := by omega
    change m ≤ (trajectory B).length at hB
    rw [hb0] at hB
    simp [trajectory] at hB
    omega
  have heq : (trajectory B).length = m := by
    have hpre := hmin (B - 1) (by omega)
    have hu := (reachable_invariants (B - 1)).2.2.2
    have hsucc : B - 1 + 1 = B := by omega
    rw [hsucc] at hu
    change m ≤ (trajectory B).length at hB
    omega
  exact ⟨B, hpos, heq, hmin, Nat.find_min' exists_cross crosses⟩

/-- Birth time only exists for a positive height, using the proved existence
certificate. It has no arbitrary value for absent heights. -/
noncomputable def birth (m : ℕ) (hm : 1 ≤ m) : ℕ :=
  Nat.find (birth_totality m hm)

/-- Gap transfer and the published row scan are conjugate on every natural
capacity list, including zero gaps. Positivity is needed for physical bricks,
but no reachability restriction is needed for this algorithmic identity. -/
theorem row_transition_correspondence : RowTransitionCorrespondence := by
  intro n cs _hn
  have scan : ∀ ds : List ℕ, ∀ a : ℕ,
      extendRow n (a :: (widths ds).map (fun w => a + w)) =
        if (transfer n ds).2 then
          (a + n) :: (widths (transfer n ds).1).map (fun w => a + n + w)
        else a :: (widths (transfer n ds).1).map (fun w => a + w) := by
    intro ds
    induction ds with
    | nil => intro a; simp [widths, transfer, extendRow]
    | cons c ds ih =>
      intro a
      have shifted : (widths (c :: ds)).map (fun w => a + w) =
          (a + c) :: (widths ds).map (fun w => a + c + w) := by
        simp [widths, List.map_map, Function.comp_def, Nat.add_assoc]
      rw [shifted]
      by_cases he : n ≤ c
      · have ha : a + n ≤ a + c := by omega
        simp only [extendRow, if_pos ha, transfer, if_pos he, widths,
          List.map_cons, List.map_map, Function.comp_def, ↓reduceIte]
        have hsub : a + n + (c - n) = a + c := by omega
        simp only [hsub, ← Nat.add_assoc]
      · have ha : ¬ a + n ≤ a + c := by omega
        simp only [extendRow, if_neg ha, transfer, if_neg he]
        rw [ih]
        cases ht : (transfer n ds).2 <;>
          simp [widths, List.map_map, Function.comp_def,
            Nat.add_comm, Nat.add_left_comm]
  cases cs with
  | nil => simp [step, transfer, widths, sourceRowStep]
  | cons c cs =>
    by_cases he : n ≤ c
    · simp only [step, transfer, if_pos he, ↓reduceIte, widths,
        List.map_cons, List.map_map, Function.comp_def, sourceRowStep]
      have hsub : n + (c - n) = c := by omega
      simp only [hsub, ← Nat.add_assoc]
    · simp only [step, transfer, if_neg he, widths, sourceRowStep]
      rw [scan cs c]
      cases ht : (transfer n cs).2 <;>
        simp [widths, Nat.add_assoc]

/-- Unit cells in literal contiguous rows. Row zero is on the floor; widths
are stored top first. A row of width w occupies the half-open interval [0,w). -/
def occupied : List ℕ → ℕ → ℕ → Prop
  | [], _, _ => False
  | w :: ws, u, y => (y = ws.length ∧ u < w) ∨ occupied ws u y

/-- All supported end-frontier positions in existing rows, without any
greedy choice. Coordinates are the left endpoint and the floor-based row. -/
def AppendSite (n : ℕ) : List ℕ → ℕ → ℕ → Prop
  | [], _, _ => False
  | [w], x, y => x = w ∧ y = 0
  | w :: v :: ws, x, y =>
      (x = w ∧ y = ws.length + 1 ∧ w + n ≤ v) ∨ AppendSite n (v :: ws) x y

/-- Legal frontier positions include a new top row when it is supported. -/
def PlacementSite (n : ℕ) (ws : List ℕ) (x y : ℕ) : Prop :=
  (x = 0 ∧ y = ws.length ∧
    (ws = [] ∨ ∃ w vs, ws = w :: vs ∧ n ≤ w)) ∨ AppendSite n ws x y

/-- Physical admissibility before a placement: disjointness, support across
the whole bottom interval, and contact with the axis or the existing wall. -/
def LegalBrick (n : ℕ) (ws : List ℕ) (x y : ℕ) : Prop :=
  (∀ u, x ≤ u → u < x + n → ¬ occupied ws u y) ∧
  (y = 0 ∨ ∀ u, x ≤ u → u < x + n → occupied ws u (y - 1)) ∧
  (x = 0 ∨ occupied ws (x - 1) y)

/-- Exact occupied-cell update, disjointness, full bottom support, and left
contact for one width-n brick. Integer endpoints encode literal unit cells. -/
def BrickAddition (ws vs : List ℕ) (n x y : ℕ) : Prop :=
  (∀ u z, occupied vs u z ↔
    occupied ws u z ∨ (z = y ∧ x ≤ u ∧ u < x + n)) ∧
  (∀ u, x ≤ u → u < x + n → ¬ occupied ws u y) ∧
  (y = 0 ∨ ∀ u, x ≤ u → u < x + n → occupied ws u (y - 1)) ∧
  (x = 0 ∨ occupied ws (x - 1) y)

set_option maxHeartbeats 1000000 in
-- The nested interval and selector inductions share one elaboration budget.
/-- On ordered contiguous rows the published scan adds exactly one fully
supported nonoverlapping interval, at the leftmost legal frontier and the
highest such frontier. This specifies the placement relation used by the
capacity conjugacy; it does not assert the self-composition identity. -/
theorem source_row_geometry (n : ℕ) (hn : 0 < n) (ws : List ℕ)
    (hp : ws.Pairwise (· ≤ ·)) :
    ∃ x y, PlacementSite n ws x y ∧
      (∀ x' y', LegalBrick n ws x' y' → x ≤ x' ∧ y' ≤ y) ∧
      BrickAddition ws (sourceRowStep n ws) n x y := by
  have above : ∀ (vs : List ℕ) u y, vs.length ≤ y → ¬ occupied vs u y := by
    intro vs
    induction vs with
    | nil => simp [occupied]
    | cons v vs ih =>
      intro u y hy
      simp only [occupied, not_or]
      exact ⟨by simp only [List.length_cons] at hy; omega,
        ih u y (by simp only [List.length_cons] at hy; omega)⟩
  have top : ∀ w vs u, occupied (w :: vs) u vs.length ↔ u < w := by
    intro w vs u
    simp [occupied, above vs u vs.length (by omega)]
  have complete : ∀ vs x y, LegalBrick n vs x y → PlacementSite n vs x y := by
    intro vs
    induction vs with
    | nil =>
      intro x y hs
      rcases hs with ⟨_, hb, hc⟩
      have hx : x = 0 := by simpa [occupied] using hc
      have hy : y = 0 := by
        rcases hb with hb | hb
        · exact hb
        · have ho := hb x (by omega) (by omega)
          simp [occupied] at ho
      exact Or.inl ⟨hx, hy, Or.inl rfl⟩
    | cons w vs ih =>
      intro x y hs
      rcases hs with ⟨hd, hb, hc⟩
      by_cases hy : y < vs.length
      · have htail : LegalBrick n vs x y := by
          refine ⟨?_, ?_, ?_⟩
          · intro u hu hn' ho; exact hd u hu hn' (Or.inr ho)
          · rcases hb with hb | hb
            · exact Or.inl hb
            · refine Or.inr ?_
              intro u hu hn'
              rcases hb u hu hn' with ⟨hy', _⟩ | ho
              · omega
              · exact ho
          · rcases hc with hc | ⟨hy', _⟩ | ho
            · exact Or.inl hc
            · omega
            · exact Or.inr ho
        rcases ih x y htail with ⟨_, hy', _⟩ | hs'
        · omega
        · cases vs with
          | nil => simp at hy
          | cons v vs => exact Or.inr (Or.inr hs')
      · by_cases heq : y = vs.length
        · subst y
          have hxlow : w ≤ x := by
            have hd' := hd x (by omega) (by omega)
            rw [top] at hd'
            omega
          have hx : x = w := by
            rcases hc with hc | hc
            · omega
            · rw [top] at hc
              omega
          subst x
          cases vs with
          | nil => exact Or.inr ⟨rfl, rfl⟩
          | cons v vs =>
            have hb' : ∀ u, w ≤ u → u < w + n →
                occupied (w :: v :: vs) u ((v :: vs).length - 1) := by
              rcases hb with hb | hb
              · simp at hb
              · exact hb
            have ho := hb' (w + n - 1) (by omega) (by omega)
            have hy' : (v :: vs).length - 1 = vs.length := by simp
            rw [hy'] at ho
            rcases ho with ⟨hy'', _⟩ | ho
            · simp at hy''
            · have hov := (top v vs _).mp ho
              exact Or.inr (Or.inl ⟨rfl, rfl, by omega⟩)
        · have hygt : vs.length < y := by omega
          have hx : x = 0 := by
            rcases hc with hc | hc
            · exact hc
            · exact (above (w :: vs) (x - 1) y (by simp; omega) hc).elim
          subst x
          have hb' : ∀ u, 0 ≤ u → u < n → occupied (w :: vs) u (y - 1) := by
            rcases hb with hb | hb
            · omega
            · simpa using hb
          have ho := hb' (n - 1) (by omega) (by omega)
          have hyl : y - 1 < (w :: vs).length := by
            by_contra h
            exact above _ _ _ (by omega) ho
          have hy' : y = (w :: vs).length := by simp only [List.length_cons] at *; omega
          have hsub : y - 1 = vs.length := by simp only [List.length_cons] at hy'; omega
          rw [hsub, top] at ho
          exact Or.inl ⟨rfl, hy', Or.inr ⟨w, vs, rfl, by omega⟩⟩
  have site_bounds : ∀ vs x y, AppendSite n vs x y → x ∈ vs ∧ y < vs.length := by
    intro vs
    induction vs with
    | nil => simp [AppendSite]
    | cons v vs ih =>
      intro x y hs
      cases vs with
      | nil => simpa [AppendSite] using hs
      | cons w vs =>
        rcases hs with ⟨rfl, rfl, _⟩ | hs
        · simp
        · obtain ⟨hx, hy⟩ := ih x y hs
          exact ⟨List.mem_cons_of_mem v hx, by simpa using Nat.lt_succ_of_lt hy⟩
  have scan_geometry : ∀ vs : List ℕ, vs ≠ [] → vs.Pairwise (· ≤ ·) →
      ∃ x y, AppendSite n vs x y ∧
        (∀ x' y', AppendSite n vs x' y' → x ≤ x' ∧ y' ≤ y) ∧
        (extendRow n vs).length = vs.length ∧
        BrickAddition vs (extendRow n vs) n x y := by
    intro vs
    induction vs with
    | nil => simp
    | cons w vs ih =>
      intro _ hp
      cases vs with
      | nil =>
        refine ⟨w, 0, by simp [AppendSite], ?_, by simp [extendRow], ?_⟩
        · intro x y hs
          rcases hs with ⟨rfl, rfl⟩
          exact ⟨le_rfl, le_rfl⟩
        · simp only [BrickAddition, extendRow, occupied, List.length_nil,
            or_false]
          refine ⟨?_, ?_, Or.inl True.intro, ?_⟩
          · intro u z; omega
          · intro u hu _; omega
          · by_cases hw : w = 0
            · exact Or.inl hw
            · exact Or.inr ⟨True.intro, by omega⟩
      | cons v vs =>
        obtain ⟨hw, htail⟩ := List.pairwise_cons.mp hp
        by_cases he : w + n ≤ v
        · refine ⟨w, vs.length + 1, Or.inl ⟨rfl, rfl, he⟩, ?_, ?_, ?_⟩
          · intro x y hs
            rcases hs with ⟨rfl, rfl, _⟩ | hs
            · exact ⟨le_rfl, le_rfl⟩
            · obtain ⟨hx, hy⟩ := site_bounds _ _ _ hs
              exact ⟨hw x hx, by simpa using Nat.le_of_lt hy⟩
          · simp [extendRow, he]
          · simp only [BrickAddition, extendRow, if_pos he]
            refine ⟨?_, ?_, Or.inr ?_, ?_⟩
            · intro u z
              change ((z = (v :: vs).length ∧ u < w + n) ∨ occupied (v :: vs) u z) ↔
                ((z = (v :: vs).length ∧ u < w) ∨ occupied (v :: vs) u z) ∨
                (z = vs.length + 1 ∧ w ≤ u ∧ u < w + n)
              simp only [List.length_cons]
              by_cases hz : z = vs.length + 1
              · subst z
                have ht := above (v :: vs) u (vs.length + 1) (by simp)
                simp only [ht, or_false, true_and]
                omega
              · simp [hz]
            · intro u hu _
              have ht := top w (v :: vs) u
              simp only [List.length_cons] at ht
              rw [ht]
              omega
            · intro u _ hu
              have hu' : u < v := by omega
              have ho : occupied (v :: vs) u vs.length := (top v vs u).mpr hu'
              have hy : vs.length + 1 - 1 = vs.length := by omega
              rw [hy]
              exact Or.inr ho
            · by_cases hw0 : w = 0
              · exact Or.inl hw0
              · exact Or.inr ((top w (v :: vs) (w - 1)).mpr (by omega))
        · obtain ⟨x, y, hs, hm, hl, hadd⟩ := ih (by simp) htail
          obtain ⟨hx, hy⟩ := site_bounds _ _ _ hs
          refine ⟨x, y, Or.inr hs, ?_, ?_, ?_⟩
          · intro x' y' hs'
            rcases hs' with ⟨_, _, he'⟩ | hs'
            · exact (he he').elim
            · exact hm x' y' hs'
          · simp [extendRow, he, hl]
          · rcases hadd with ⟨hu, hd, hb, hc⟩
            simp only [BrickAddition, extendRow, if_neg he]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro u z
              change ((z = (extendRow n (v :: vs)).length ∧ u < w) ∨
                  occupied (extendRow n (v :: vs)) u z) ↔
                ((z = (v :: vs).length ∧ u < w) ∨ occupied (v :: vs) u z) ∨
                (z = y ∧ x ≤ u ∧ u < x + n)
              rw [hl, hu]
              tauto
            · intro u hu' hn'
              change ¬ ((y = (v :: vs).length ∧ u < w) ∨ occupied (v :: vs) u y)
              exact not_or.mpr ⟨by omega, hd u hu' hn'⟩
            · rcases hb with hb | hb
              · exact Or.inl hb
              · exact Or.inr (fun u hu' hn' => Or.inr (hb u hu' hn'))
            · rcases hc with hc | hc
              · exact Or.inl hc
              · exact Or.inr (Or.inr hc)
  cases ws with
  | nil =>
    refine ⟨0, 0, Or.inl ⟨rfl, rfl, Or.inl rfl⟩, ?_, ?_⟩
    · intro x y hs
      have hs := complete [] x y hs
      rcases (show x = 0 ∧ y = 0 from by simpa [PlacementSite, AppendSite] using hs)
        with ⟨rfl, rfl⟩
      exact ⟨le_rfl, le_rfl⟩
    · simp [BrickAddition, sourceRowStep, occupied]
  | cons w ws =>
    by_cases he : n ≤ w
    · refine ⟨0, ws.length + 1, Or.inl ⟨rfl, rfl, Or.inr ⟨w, ws, rfl, he⟩⟩,
        ?_, ?_⟩
      · intro x y hs
        have hs := complete (w :: ws) x y hs
        rcases hs with ⟨_, rfl, _⟩ | hs
        · exact ⟨Nat.zero_le _, le_rfl⟩
        · obtain ⟨_, hy⟩ := site_bounds _ _ _ hs
          exact ⟨Nat.zero_le _, by simpa using Nat.le_of_lt hy⟩
      · simp only [BrickAddition, sourceRowStep, if_pos he, occupied,
          List.length_cons, Nat.zero_add, Nat.zero_le, true_and]
        refine ⟨?_, ?_, Or.inr ?_, Or.inl True.intro⟩
        · intro u z; tauto
        · intro u _ _; exact above (w :: ws) u (ws.length + 1) (by simp)
        · intro u _ hu
          exact Or.inl ⟨by omega, by omega⟩
    · obtain ⟨x, y, hs, hm, _, hadd⟩ := scan_geometry (w :: ws) (by simp) hp
      refine ⟨x, y, Or.inr hs, ?_, ?_⟩
      · intro x' y' hs'
        have hs' := complete (w :: ws) x' y' hs'
        rcases hs' with ⟨_, _, hempty | ⟨v, vs, hvs, hv⟩⟩ | hs'
        · simp at hempty
        · cases hvs
          exact (he hv).elim
        · exact hm x' y' hs'
      · simpa [sourceRowStep, he] using hadd

end D5.S3.ArithSums.GreedyBrickCapacityTotality
