/- GID: D5/S1/Words/AdmissibleWords/NestedEventGraphBounds
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/NestedEventGraphBounds
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Least downward variation gives sharp event differences from a fixed source. -/

import D5.S1.Words.AdmissibleWords.SourceOverlapCoupling
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! For neighboring events ordered by mass, the least downward variation on a graph
gives a sharp bound on the event difference from a fixed source. -/

open Set MeasureTheory

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.NestedEventGraphBounds

private def leftMass (a q d : ℝ) : ℝ := max 0 (max (a + q - 1) (a - d))

private theorem leftMass_range {a q d : ℝ} (ha : 0 ≤ a ∧ a ≤ 1)
    (hq : 0 ≤ q ∧ q ≤ 1) (hd : 0 ≤ d) (majorizes : a - q ≤ d) :
    0 ≤ leftMass a q d ∧ leftMass a q d ≤ a ∧ leftMass a q d ≤ q ∧
      q - leftMass a q d ≤ 1 - a := by
  unfold leftMass
  refine ⟨le_max_left .., max_le ha.1 (max_le (by linarith [hq.2]) (by linarith)),
    max_le hq.1 (max_le (by linarith [ha.2]) (by linarith)), ?_⟩
  have h := (le_max_left (a + q - 1) (a - d)).trans (le_max_right 0 _)
  linarith

private theorem leftMass_step {a q r d e : ℝ} (mon : q ≤ r)
    (le : e ≤ d) (cap : d ≤ e + (r - q)) :
    leftMass a q d ≤ leftMass a r e ∧
      r - leftMass a r e ≥ q - leftMass a q d := by
  unfold leftMass
  constructor
  · exact max_le_max le_rfl (max_le_max (by linarith) (by linarith))
  · have h₁ : max (a + r - 1) (a - e) - max (a + q - 1) (a - d) ≤ r - q :=
      (max_sub_max_le_max ..).trans (max_le (by linarith) (by linarith))
    have h₂ : max 0 (max (a + r - 1) (a - e)) - max 0 (max (a + q - 1) (a - d))
        ≤ r - q := (max_sub_max_le_max ..).trans (max_le (by linarith) h₁)
    linarith

private theorem attain_from_potential {V : Type*} (q d : V → ℝ) (s : V)
    (bounds : ∀ v, 0 ≤ q v ∧ q v ≤ 1)
    (nonneg : ∀ v, 0 ≤ d v) (anchor : d s = 0)
    (majorizes : ∀ v, q s - q v ≤ d v) :
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ u v, q u ≤ q v → d v ≤ d u → d u ≤ d v + (q v - q u) → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = min (q s) (min (1 - q v) (d v)) := by
  let overlap v := leftMass (q s) (q v) (d v)
  let R u v := q u ≤ q v ∧ d v ≤ d u ∧ d u ≤ d v + (q v - q u)
  have source : overlap s = q s := by
    simp only [overlap, leftMass, anchor, sub_zero]
    rw [max_eq_right (show q s + q s - 1 ≤ q s by linarith [(bounds s).2]),
      max_eq_right (bounds s).1]
  have limits (v : V) := leftMass_range (bounds s) (bounds v) (nonneg v) (majorizes v)
  have left (v : V) : overlap v ∈ Icc 0 (q s) := ⟨(limits v).1, (limits v).2.1⟩
  have right (v : V) : q v - overlap v ∈ Icc 0 (1 - q s) :=
    ⟨sub_nonneg.mpr (limits v).2.2.1, (limits v).2.2.2⟩
  obtain ⟨A, law, nested, value⟩ :=
    SourceOverlapCoupling.exists_nested_events R q overlap s (bounds s) source left right
      (by
        intro u v edge
        exact leftMass_step edge.1 edge.2.1 edge.2.2)
  refine ⟨A, law, fun _ _ h₁ h₂ h₃ => nested ⟨h₁, h₂, h₃⟩, ?_⟩
  intro v
  rw [value]
  simp [overlap, leftMass, ← min_sub_sub_left,
    show q s - (q s + q v - 1) = 1 - q v by linarith]

section Walks

variable {V : Type*} {G : SimpleGraph V}

private def stepCost (q : V → ℝ) (u v : V) : ℝ := max 0 (q u - q v)

private def walkCost (q : V → ℝ) {u v : V} (walk : G.Walk u v) : ℝ :=
  (walk.darts.map fun edge => stepCost q edge.fst edge.snd).sum

private theorem cost_nonneg (q : V → ℝ) {u v : V} (p : G.Walk u v) : 0 ≤ walkCost q p := by
  induction p with
  | nil => rfl
  | cons _ p ih => exact add_nonneg (le_max_left ..) ih

private theorem cost_majorizes (q : V → ℝ) {u v : V} (p : G.Walk u v) :
    q u - q v ≤ walkCost q p := by
  induction p with
  | nil => simp [walkCost]
  | @cons a b _ _ p ih =>
      change _ ≤ stepCost q a b + walkCost q p
      unfold stepCost
      linarith [le_max_right 0 (q a - q b)]

private theorem cost_append (q : V → ℝ) {u v z : V} (p : G.Walk u v) (r : G.Walk v z) :
    walkCost q (p.append r) = walkCost q p + walkCost q r := by
  simp [walkCost, SimpleGraph.Walk.darts_append, List.sum_append]

private def costs (q : V → ℝ) (u v : V) : Set ℝ :=
  Set.range (fun p : G.Walk u v => walkCost q p)

private theorem costs_bdd (q : V → ℝ) (u v : V) : BddBelow (costs (G := G) q u v) :=
  ⟨0, fun _ ⟨p, hp⟩ => hp ▸ cost_nonneg q p⟩

/-- The infimum of cumulative downward variation over walks between two vertices. -/
noncomputable def distance (q : V → ℝ) (u v : V) : ℝ := sInf (costs (G := G) q u v)

private theorem cost_nonempty (q : V → ℝ) {u v : V} (walk : G.Reachable u v) :
    (costs (G := G) q u v).Nonempty := by
  obtain ⟨p⟩ := walk
  exact ⟨walkCost q p, ⟨p, rfl⟩⟩

private theorem distance_self (q : V → ℝ) (u : V) : distance (G := G) q u u = 0 := by
  apply le_antisymm
  · exact csInf_le (costs_bdd q u u) ⟨.nil, rfl⟩
  · exact le_csInf ⟨0, ⟨.nil, rfl⟩⟩ fun _ ⟨p, hp⟩ => hp ▸ cost_nonneg q p

private theorem distance_step (q : V → ℝ) {s u v : V}
    (reachable : G.Reachable s u) (edge : G.Adj u v) :
    distance (G := G) q s v ≤ distance (G := G) q s u + stepCost q u v := by
  apply sub_le_iff_le_add.mp
  apply le_csInf (cost_nonempty q reachable)
  rintro r ⟨p, hp⟩
  change walkCost q p = r at hp
  subst r
  have h : distance (G := G) q s v ≤ walkCost q (p.append edge.toWalk) :=
    csInf_le (costs_bdd q s v) ⟨_, rfl⟩
  simpa [cost_append, walkCost, add_zero, sub_le_iff_le_add] using h

private theorem graph_attainment (q : V → ℝ) (s : V)
    (bounds : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (reachable : ∀ v, G.Reachable s v) :
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ u v, G.Adj u v → q u ≤ q v → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = min (q s) (min (1 - q v) (distance (G := G) q s v)) := by
  let d := distance (G := G) q s
  have nonneg (v : V) : 0 ≤ d v :=
    le_csInf (cost_nonempty q (reachable v)) fun _ ⟨p, hp⟩ => hp ▸ cost_nonneg q p
  have major (v : V) : q s - q v ≤ d v :=
    le_csInf (cost_nonempty q (reachable v)) fun _ ⟨p, hp⟩ => hp ▸ cost_majorizes q p
  obtain ⟨A, probabilities, direction, value⟩ :=
    attain_from_potential q d s bounds nonneg (distance_self q s) major
  refine ⟨A, probabilities, ?_, value⟩
  intro u v adjacency order
  apply direction u v order
  · have h := distance_step q (reachable u) adjacency
    simpa [d, stepCost, max_eq_left (sub_nonpos.mpr order)] using h
  · have h := distance_step q (reachable v) adjacency.symm
    simpa [d, stepCost, max_eq_right (sub_nonneg.mpr order)] using h

private theorem graph_upper_bound (q : V → ℝ) (A : V → Set ℝ)
    (law : ∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v)
    (nested : ∀ u v, G.Adj u v → A u ⊆ A v ∨ A v ⊆ A u)
    {s v : V} (reachable : G.Reachable s v) :
    volume.real (A s \ A v) ≤
      min (q s) (min (1 - q v) (distance (G := G) q s v)) := by
  have unitFinite : volume (Ico (0 : ℝ) 1) ≠ ⊤ := by simp
  have finite {B : Set ℝ} (hB : B ⊆ Ico (0 : ℝ) 1) : volume B ≠ ⊤ :=
    measure_ne_top_of_subset hB unitFinite
  have edgeMass {u w : V} (edge : G.Adj u w) :
      volume.real (A u \ A w) = stepCost q u w := by
    rcases nested u w edge with inc | dec
    · have order := measureReal_mono inc (finite (law w).2.1)
      rw [(law u).2.2, (law w).2.2] at order
      rw [sdiff_eq_empty.mpr inc, measureReal_empty, stepCost,
        max_eq_left (sub_nonpos.mpr order)]
    · have order := measureReal_mono dec (finite (law u).2.1)
      rw [(law w).2.2, (law u).2.2] at order
      rw [measureReal_sdiff dec (law w).1 (finite (law u).2.1), (law u).2.2, (law w).2.2,
        stepCost, max_eq_right (sub_nonneg.mpr order)]
  have alongWalk {u w : V} (p : G.Walk u w) :
      volume.real (A u \ A w) ≤ walkCost q p := by
    induction p with
    | nil => simp [walkCost]
    | @cons a b z edge rest ih =>
        change _ ≤ stepCost q a b + walkCost q rest
        calc
          _ ≤ volume.real ((A a \ A b) ∪ (A b \ A z)) :=
            measureReal_mono (sdiff_triangle ..)
              (finite (union_subset (sdiff_subset.trans (law a).2.1)
                (sdiff_subset.trans (law b).2.1)))
          _ ≤ volume.real (A a \ A b) + volume.real (A b \ A z) :=
            measureReal_union_le _ _
          _ ≤ _ := by
            rw [edgeMass edge]
            exact add_le_add_right ih _
  refine le_min ?_ (le_min ?_ ?_)
  · rw [← (law s).2.2]
    exact measureReal_mono sdiff_subset (finite (law s).2.1)
  · have sub : A s \ A v ⊆ Ico (0 : ℝ) 1 \ A v := sdiff_subset_sdiff_left (law s).2.1
    apply (measureReal_mono sub (finite sdiff_subset)).trans_eq
    rw [measureReal_sdiff (law v).2.1 (law v).1 unitFinite, (law v).2.2]
    norm_num [Real.volume_real_Ico]
  · exact le_csInf (cost_nonempty q reachable) (fun _ ⟨p, hp⟩ => hp ▸ alongWalk p)

/-- For events nested on each edge, the fixed-source difference is bounded by the endpoint
masses and the least downward variation. A single family attains the bound at all vertices
and has the inclusions ordered by mass, including equality at ties. -/
theorem sharp_difference (q : V → ℝ) (s : V)
    (bounds : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (reachable : ∀ v, G.Reachable s v) :
    (∀ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) →
      (∀ u v, G.Adj u v → A u ⊆ A v ∨ A v ⊆ A u) →
      ∀ v, volume.real (A s \ A v) ≤ min (q s) (min (1 - q v) (distance (G := G) q s v))) ∧
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ u v, G.Adj u v → q u ≤ q v → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = min (q s) (min (1 - q v) (distance (G := G) q s v)) :=
  ⟨fun A law nested v => graph_upper_bound q A law nested (reachable v),
    graph_attainment q s bounds reachable⟩

end Walks

end D5.S1.Words.AdmissibleWords.NestedEventGraphBounds
