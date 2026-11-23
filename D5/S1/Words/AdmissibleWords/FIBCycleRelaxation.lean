/- GID: D5/S1/Words/AdmissibleWords/FIBCycleRelaxation
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FIBCycleRelaxation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The cycle relaxation of two oriented event differences is exactly a rectangle. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The exact cycle region for the pair queries on the five-vertex FIB graph. -/

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.FIBCycleRelaxation

/-- The rows are the reference, S, H, K, T, W. The unobserved entries use m and 2b. -/
def completion (q c a b m : ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![0, q, q+c, q+c, q, q],
    ![q, 0, c, c, m, 2*a],
    ![q+c, c, 0, 2*b, c+2*b, c],
    ![q+c, c, 2*b, 0, c, c],
    ![q, m, c+2*b, c, 0, m],
    ![q, 2*a, c, c, m, 0]]

set_option maxHeartbeats 2000000 in
private theorem completion_laws_of_bounds {q c a b m : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hu : q + c ≤ 1)
    (ha : 0 ≤ a) (haq : a ≤ q) (hac : a ≤ c)
    (hb : 0 ≤ b) (hbq : b ≤ q) (hbc : b ≤ c) (hbu : b ≤ 1 - (q + c))
    (hm0 : 0 ≤ m) (hma : a ≤ m) (hmb : 2*b ≤ m) (hmc : m ≤ 2*c)
    (hmq : m ≤ 2*q) (ham : a + m ≤ 1) :
    let d := completion q c a b m
    (∀ u v w, d u w ≤ d u v + d v w) ∧
      (∀ u v w, d u v + d v w + d w u ≤ 2) := by
  constructor
  · intro u v w
    fin_cases u <;> fin_cases v <;> fin_cases w <;> norm_num [completion] <;> linarith
  · intro u v w
    fin_cases u <;> fin_cases v <;> fin_cases w <;> norm_num [completion] <;> linarith

private theorem completion_laws {q c a b : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hu : q + c ≤ 1)
    (ha : 0 ≤ a) (haq : a ≤ q) (hac : a ≤ c)
    (hb : 0 ≤ b) (hbq : b ≤ q) (hbc : b ≤ c) (hbu : b ≤ 1 - (q + c)) :
    let d := completion q c a b (max a (2*b))
    (∀ u v w, d u w ≤ d u v + d v w) ∧
      (∀ u v w, d u v + d v w + d w u ≤ 2) := by
  have hm0 : 0 ≤ max a (2*b) := ha.trans (le_max_left _ _)
  have hma : a ≤ max a (2*b) := le_max_left _ _
  have hmb : 2*b ≤ max a (2*b) := le_max_right _ _
  have hmc : max a (2*b) ≤ 2*c := max_le (by linarith) (by linarith)
  have hmq : max a (2*b) ≤ 2*q := max_le (by linarith) (by linarith)
  have ham : a + max a (2*b) ≤ 1 := by
    rw [add_max]
    exact max_le (by linarith) (by linarith)
  exact completion_laws_of_bounds hc hq hu ha haq hac hb hbq hbc hbu hm0 hma hmb hmc hmq ham

private def signedDistance {V : Type*} (d : V → V → ℝ) (u v : V × Bool) : ℝ :=
  if u.2 = v.2 then d u.1 v.1 else 1 - d u.1 v.1

private theorem signedTriangle {V : Type*} (d : V → V → ℝ)
    (symmetric : ∀ u v, d u v = d v u)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (perimeter : ∀ u v w, d u v + d v w + d w u ≤ 2)
    (u v w : V × Bool) :
    signedDistance d u w ≤ signedDistance d u v + signedDistance d v w := by
  rcases u with ⟨u, uSide⟩
  rcases v with ⟨v, vSide⟩
  rcases w with ⟨w, wSide⟩
  have direct := triangle u v w
  have viaW := triangle u w v
  have viaU := triangle v u w
  have circ := perimeter u v w
  rw [symmetric w v] at viaW
  rw [symmetric v u] at viaU
  rw [symmetric w u] at circ
  cases uSide <;> cases vSide <;> cases wSide <;>
    simp [signedDistance] <;> linarith

private def walkCost {V : Type*} (d : V → V → ℝ) :
    V → List V → V → ℝ
  | u, [], v => d u v
  | u, x :: rest, v => d u x + walkCost d x rest v

private theorem direct_le_walk {V : Type*} (d : V → V → ℝ)
    (triangle : ∀ u v w, d u w ≤ d u v + d v w)
    (u : V) (middle : List V) (v : V) : d u v ≤ walkCost d u middle v := by
  induction middle generalizing u with
  | nil => exact le_rfl
  | cons x rest ih =>
    exact (triangle u x v).trans (add_le_add_right (ih x) (d u x))


/-- The marginal, graph-edge, and queried pairs. -/
def observed : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (5, 2), (5, 3), (4, 3),
    (5, 1), (4, 2)}

/-- Every odd set of marked steps on a closed walk yields a unit lower bound. -/
def CycleConsistent (d : Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ u middle, 1 ≤ walkCost (signedDistance d) (u, false) middle (u, true)

/-- The prescribed pairs extend to symmetric distances that satisfy all cycle inequalities. -/
def HasCycleCompletion (specified : Fin 6 → Fin 6 → ℝ) : Prop :=
  ∃ d : Fin 6 → Fin 6 → ℝ, (∀ u v, d u v = d v u) ∧ CycleConsistent d ∧
    ∀ p ∈ observed, d p.1 p.2 = specified p.1 p.2

private theorem necessary_bounds {q c a b m : ℝ}
    (h : HasCycleCompletion (completion q c a b m)) :
    (0 ≤ a ∧ a ≤ q ∧ a ≤ c) ∧ (0 ≤ b ∧ b ≤ q ∧ b ≤ c ∧ b ≤ 1 - (q + c)) := by
  rcases h with ⟨d, symmetric, valid, agrees⟩
  have edge (u v : Fin 6) (hp : (u, v) ∈ observed) :
      d u v = completion q c a b m u v := agrees (u, v) hp
  have os : d 0 1 = q := edge 0 1 (by decide)
  have oh : d 0 2 = q + c := edge 0 2 (by decide)
  have ot : d 0 4 = q := edge 0 4 (by decide)
  have ow : d 0 5 = q := edge 0 5 (by decide)
  have sh : d 1 2 = c := edge 1 2 (by decide)
  have sk : d 1 3 = c := edge 1 3 (by decide)
  have wh : d 5 2 = c := edge 5 2 (by decide)
  have tk : d 4 3 = c := edge 4 3 (by decide)
  have ws : d 5 1 = 2 * a := edge 5 1 (by decide)
  have th : d 4 2 = c + 2 * b := edge 4 2 (by decide)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · have bound := valid 0 [(5, false), (1, false)]
    norm_num [walkCost, signedDistance, ow, ws, symmetric 1 0, os] at bound
    linarith
  · have bound := valid 0 [(5, false), (1, true)]
    norm_num [walkCost, signedDistance, ow, ws, symmetric 1 0, os] at bound
    linarith
  · have bound := valid 5 [(2, false), (1, false)]
    norm_num [walkCost, signedDistance, wh, symmetric 2 1, sh, symmetric 1 5, ws] at bound
    linarith
  · have bound := valid 0 [(4, false), (2, false)]
    norm_num [walkCost, signedDistance, ot, th, symmetric 2 0, oh] at bound
    linarith
  · have bound := valid 0 [(4, false), (2, true)]
    norm_num [walkCost, signedDistance, ot, th, symmetric 2 0, oh] at bound
    linarith
  · have bound := valid 4 [(3, false), (1, false), (2, false)]
    norm_num [walkCost, signedDistance, tk, symmetric 3 1, sk, sh, symmetric 2 4, th] at bound
    linarith
  · have bound := valid 0 [(4, true), (2, false)]
    norm_num [walkCost, signedDistance, ot, th, symmetric 2 0, oh] at bound
    linarith

private theorem completion_symmetric (q c a b m : ℝ) (u v : Fin 6) :
    completion q c a b m u v = completion q c a b m v u := by
  fin_cases u <;> fin_cases v <;> rfl

private theorem completion_diagonal (q c a b m : ℝ) (u : Fin 6) :
    completion q c a b m u u = 0 := by
  fin_cases u <;> rfl

/-- The cycle inequalities impose the two individual capacities on the queried differences. -/
theorem cycle_completion_iff {q c a b : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) (hu : q + c ≤ 1) :
    HasCycleCompletion (completion q c a b (max a (2 * b))) ↔
      (0 ≤ a ∧ a ≤ q ∧ a ≤ c) ∧ (0 ≤ b ∧ b ≤ q ∧ b ≤ c ∧ b ≤ 1 - (q + c)) := by
  refine ⟨necessary_bounds, ?_⟩
  rintro ⟨⟨ha, haq, hac⟩, ⟨hb, hbq, hbc, hbu⟩⟩
  let d := completion q c a b (max a (2 * b))
  have symmetric := completion_symmetric q c a b (max a (2 * b))
  obtain ⟨triangle, perimeter⟩ := completion_laws hc hq hu ha haq hac hb hbq hbc hbu
  refine ⟨d, symmetric, ?_, fun _ _ => rfl⟩
  intro u middle
  have bound := direct_le_walk (signedDistance d) (signedTriangle d symmetric triangle perimeter)
    (u, false) middle (u, true)
  simpa [signedDistance, d, completion_diagonal] using bound

end D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
