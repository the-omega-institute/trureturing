/- GID: D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch
   mirror-E: none(waiver:pure)
   anchors: []
   utility: none
   digest: Synchronous first-touch dynamics and strict horizons in clipped honeycomb domains. -/

import D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Lucas

/-! First-touch dynamics, the earliest-birth criterion, and comparison across a clipped wall. -/

namespace D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch

open D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex honeycombGraph)
open scoped Finset

section

/-! First-touch dynamics on a finite retained set. -/

universe u

variable {V : Type u} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Time and multiplicity of the first proposals. The seed has data (0, 1). -/
private abbrev TouchData := ℕ × ℕ

/-- Distinct retained neighbors with stored birth time exactly `t`. -/
def sendingNeighbors (D : Finset V) (t : ℕ) (prior : V → Option TouchData) (v : V) :
    Finset V :=
  D.filter fun w => G.Adj v w ∧ prior w = some (t, 1)

/-- State after tick `t`. A positive first proposal count is stored permanently. -/
def state (D : Finset V) (seed : V) : ℕ → V → Option TouchData
  | 0, v => if v ∈ D ∧ v = seed then some (0, 1) else none
  | t + 1, v =>
      match state D seed t v with
      | some data => some data
      | none =>
          if v ∈ D then
            let count := (sendingNeighbors G D t (state D seed t) v).card
            if count = 0 then none else some (t + 1, count)
          else none

variable {G} {D E : Finset V} {seed v : V} {t s μ : ℕ}

/-- The first touch happened this tick, with the indicated multiplicity. -/
def Touch (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (seed : V)
    (t : ℕ) (v : V) (μ : ℕ) : Prop :=
  state G D seed t v = some (t, μ)

/-- Only first touches with multiplicity one give birth. -/
def Born (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (seed : V)
    (t : ℕ) (v : V) : Prop :=
  Touch G D seed t v 1

/-- For a retained vertex, `none` at tick `t` represents intact status after that tick. -/
def Intact (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (seed : V)
    (t : ℕ) (v : V) : Prop :=
  state G D seed t v = none

def senders (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (seed : V)
    (t : ℕ) (v : V) : Finset V :=
  sendingNeighbors G D t (state G D seed t) v

@[simp] theorem mem_senders {w : V} :
    w ∈ senders G D seed t v ↔ w ∈ D ∧ G.Adj v w ∧ Born G D seed t w := by
  simp [senders, sendingNeighbors, Born, Touch]

theorem touch_zero_iff :
    Touch G D seed 0 v μ ↔ v ∈ D ∧ v = seed ∧ μ = 1 := by
  by_cases h : v ∈ D ∧ v = seed
  · simp [Touch, state, h, eq_comm]
  · constructor
    · intro event
      simp [Touch, state, h] at event
    · intro retained
      exact (h ⟨retained.1, retained.2.1⟩).elim

private theorem state_persists {data : TouchData}
    (recorded : state G D seed s v = some data) (hs : s ≤ t) :
    state G D seed t v = some data := by
  induction hs with
  | refl => exact recorded
  | step _ ih => simp [state, ih]

private theorem new_state (h : Intact G D seed t v) :
    state G D seed (t + 1) v =
      if v ∈ D then
        if (senders G D seed t v).card = 0 then none
        else some (t + 1, (senders G D seed t v).card)
      else none := by
  change state G D seed t v = none at h
  simp [state, h, senders]

/-- Every stored pair comes from a genuine event at its recorded time. -/
private theorem state_provenance (h : state G D seed t v = some (s, μ)) :
    s ≤ t ∧ Touch G D seed s v μ := by
  induction t with
  | zero =>
    by_cases hz : v ∈ D ∧ v = seed
    · obtain ⟨hseed, rfl⟩ := hz
      have pairEq : some (0, 1) = some (s, μ) := by
        simpa only [state, hseed, eq_self, and_self, ite_true] using h
      cases Option.some.inj pairEq
      exact ⟨Nat.le_refl _, h⟩
    · simp [state, hz] at h
  | succ t ih =>
    cases hr : state G D seed t v with
    | none =>
      have stored := h
      rw [new_state hr] at h
      split at h
      · split at h
        · contradiction
        · have he := Option.some.inj h
          have ht : t + 1 = s := congrArg Prod.fst he
          subst s
          exact ⟨Nat.le_refl _, stored⟩
      · contradiction
    | some data =>
      have h' : state G D seed t v = some (s, μ) := by
        simpa [state, hr] using h
      exact ⟨Nat.le.step (ih h').1, (ih h').2⟩

private theorem touch_succ_iff :
    Touch G D seed (t + 1) v μ ↔
      Intact G D seed t v ∧ v ∈ D ∧ 0 < μ ∧ (senders G D seed t v).card = μ := by
  cases hr : state G D seed t v with
  | none =>
    change state G D seed (t + 1) v = some (t + 1, μ) ↔ _
    rw [new_state hr]
    by_cases hv : v ∈ D
    · by_cases hc : (senders G D seed t v).card = 0
      · simp [Intact, hr, hv, hc]
        omega
      · have hp : 0 < (senders G D seed t v).card := Nat.pos_of_ne_zero hc
        simp only [Intact, hr, hv, hc, ite_false, ite_true, Option.some.injEq,
          Prod.mk.injEq, true_and]
        exact ⟨fun hm => ⟨hm ▸ hp, hm⟩, And.right⟩
    · simp [Intact, hr, hv]
  | some data =>
    obtain ⟨r, n⟩ := data
    have hle := (state_provenance hr).1
    have hn : r ≠ t + 1 := by omega
    simp [Touch, state, Intact, hr, hn]

private theorem born_succ_iff :
    Born G D seed (t + 1) v ↔
      Intact G D seed t v ∧ v ∈ D ∧ (senders G D seed t v).card = 1 := by
  simp [Born, touch_succ_iff]

theorem touch_retained_and_positive (he : Touch G D seed t v μ) : v ∈ D ∧ 0 < μ := by
  cases t with
  | zero =>
    obtain ⟨hv, _, rfl⟩ := touch_zero_iff.mp he
    exact ⟨hv, by decide⟩
  | succ t =>
    obtain ⟨_, hv, hn, _⟩ := touch_succ_iff.mp he
    exact ⟨hv, hn⟩

theorem intact_iff_no_touch :
    Intact G D seed t v ↔ ∀ s ≤ t, ∀ μ, ¬ Touch G D seed s v μ := by
  constructor
  · intro intact s hs μ event
    have persist := state_persists event hs
    change state G D seed t v = none at intact
    simp [intact] at persist
  · intro noTouch
    cases h : state G D seed t v with
    | none => exact h
    | some data =>
      obtain ⟨s, μ⟩ := data
      have ⟨hs, he⟩ := state_provenance h
      exact (noTouch s hs μ he).elim

theorem touch_unique (he₁ : Touch G D seed s v μ)
    {ν : ℕ} (he₂ : Touch G D seed t v ν) : s = t ∧ μ = ν := by
  have both : some (s, μ) = some (t, ν) :=
    (state_persists he₁ (Nat.le_max_left s t)).symm.trans
      (state_persists he₂ (Nat.le_max_right s t))
  exact Prod.mk.inj (Option.some.inj both)

/-- First-touch agreement through a tick also fixes intact status after that tick. -/
private theorem intact_agrees
    (agree : ∀ s ≤ t, ∀ μ, 0 < μ → (Touch G D seed s v μ ↔ Touch G E seed s v μ)) :
    Intact G D seed t v ↔ Intact G E seed t v := by
  rw [intact_iff_no_touch, intact_iff_no_touch]
  constructor
  · intro intact s hs μ event
    exact intact s hs μ ((agree s hs μ (touch_retained_and_positive event).2).mpr event)
  · intro intact s hs μ event
    exact intact s hs μ ((agree s hs μ (touch_retained_and_positive event).2).mp event)

/-- A potential with unit edge steps bounds the first touch from below. -/
private theorem earliest_touch (level : V → ℕ) (seed_zero : level seed = 0)
    (step : ∀ ⦃v w⦄, v ∈ D → w ∈ D → G.Adj v w → level v ≤ level w + 1)
    (event : Touch G D seed t v μ) : level v ≤ t := by
  induction t generalizing v μ with
  | zero =>
    obtain ⟨_, rfl, _⟩ := touch_zero_iff.mp event
    simp [seed_zero]
  | succ t ih =>
    obtain ⟨_, hv, hp, hc⟩ := touch_succ_iff.mp event
    have nonempty : (senders G D seed t v).Nonempty := Finset.card_pos.mp (hc ▸ hp)
    obtain ⟨w, hw⟩ := nonempty
    obtain ⟨hw, adj, born⟩ := mem_senders.mp hw
    exact (step hv hw adj).trans (Nat.succ_le_succ (ih born))

/-- Both conclusions use the horizon at the vertex being observed. -/
theorem strict_horizon (h : V → ℕ) (sub : D ⊆ E) (seed_mem : seed ∈ D)
    (edge_step : ∀ ⦃v w⦄, G.Adj v w → h v ≤ h w + 1)
    (wall : ∀ ⦃v⦄, v ∈ E → v ∉ D → (∃ w ∈ D, G.Adj v w) →
      ∀ t < h v, ¬ Born G E seed t v) (t : ℕ) :
    (∀ v ∈ D, t < h v → ∀ μ, 0 < μ →
      (Touch G D seed t v μ ↔ Touch G E seed t v μ)) ∧
    (∀ v ∈ E, v ∉ D → t < h v → ¬ Born G E seed t v) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero =>
      constructor
      · intro v hv _ μ _
        simp [touch_zero_iff, hv, sub hv]
      · intro v _ hv _ birth
        exact hv ((touch_zero_iff.mp birth).2.1 ▸ seed_mem)
    | succ t =>
      have previous : ∀ ⦃v w⦄, G.Adj v w → t + 1 < h v → t < h w := by
        intro v w adj short
        have := edge_step adj
        omega
      constructor
      · intro v hv short μ _
        have intact : Intact G D seed t v ↔ Intact G E seed t v :=
          intact_agrees fun s hs μ hp => (ih s (by omega)).1 v hv (by omega) μ hp
        have sameSenders : senders G D seed t v = senders G E seed t v := by
          ext w
          simp only [mem_senders]
          constructor
          · rintro ⟨hw, adj, birth⟩
            exact ⟨sub hw, adj, ((ih t (by omega)).1 w hw (previous adj short) 1
              (by decide)).mp birth⟩
          · rintro ⟨hw, adj, birth⟩
            have shortW := previous adj short
            by_cases hwD : w ∈ D
            · exact ⟨hwD, adj, ((ih t (by omega)).1 w hwD shortW 1 (by decide)).mpr birth⟩
            · exact ((ih t (by omega)).2 w hw hwD shortW birth).elim
        simp only [touch_succ_iff, intact, hv, sub hv, sameSenders, true_and]
      · intro v hv hvD short
        by_cases boundary : ∃ w ∈ D, G.Adj v w
        · exact wall hv hvD boundary (t + 1) short
        · intro birth
          have nonempty : (senders G E seed t v).Nonempty :=
            Finset.card_pos.mp (by simp [(born_succ_iff.mp birth).2.2])
          obtain ⟨w, hw⟩ := nonempty
          obtain ⟨hw, adj, birthW⟩ := mem_senders.mp hw
          have hwD : w ∉ D := fun h => boundary ⟨w, h, adj⟩
          exact (ih t (by omega)).2 w hw hwD (previous adj short) birthW

end

section

/-! Dyadic identities for the two wall parents. -/

private theorem complement_residue {b m a : ℕ}
    (hm : 0 < m) (divides : 2 ^ b ∣ m) (ha : a < 2 ^ b) :
    (m - 1 - a) % 2 ^ b = 2 ^ b - (a + 1) := by
  obtain ⟨q, rfl⟩ := divides
  cases q with
  | zero => simp at hm
  | succ q =>
    have split : 2 ^ b * q.succ - 1 - a = 2 ^ b * q + (2 ^ b - (a + 1)) := by
      rw [Nat.mul_succ]
      omega
    rw [split, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private theorem land_complement_of_multiple {b m a : ℕ}
    (hm : 0 < m) (divides : 2 ^ b ∣ m) (ha : a < 2 ^ b) :
    (m - 1 - a) &&& a = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.zero_testBit]
  by_cases hi : i < b
  · have same : ((m - 1 - a) % 2 ^ b).testBit i = (m - 1 - a).testBit i := by
      simp [Nat.testBit_mod_two_pow, hi]
    rw [← same, complement_residue hm divides ha, Nat.testBit_two_pow_sub_succ ha]
    cases a.testBit i <;> simp [hi]
  · have hpow : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hpow)]
    simp

/-- With `x + y = m`, the two wall parents have disjoint coordinate bits. -/
private theorem wall_parent_bits {b m x y : ℕ} (divides : 2 ^ b ∣ m)
    (sum : x + y = m) (hy₀ : 0 < y) (hy : y < 2 ^ b) :
    (x - 1) &&& y = 0 ∧ x &&& (y - 1) = 0 := by
  have hm : 0 < m := by omega
  have first := land_complement_of_multiple hm divides hy
  have second := land_complement_of_multiple hm divides (a := y - 1) (by omega)
  have hfirst : m - 1 - y = x - 1 := by omega
  have hsecond : m - 1 - (y - 1) = x := by omega
  exact ⟨hfirst ▸ first, hsecond ▸ second⟩

end

section

/-! Honeycomb geometry and the strict horizon for a displaced wall. -/

def A (x y : ℤ) : Vertex := (false, x, y)
def B (x y : ℤ) : Vertex := (true, x, y)

/-- The adjacency interface to discharge by unfolding the repository's graph. -/
structure NeighborLaws (G : SimpleGraph Vertex) : Prop where
  opposite : ∀ {v w : Vertex}, G.Adj v w → v.1 ≠ w.1
  fromA : ∀ x y a b, G.Adj (A x y) (B a b) ↔
    (x = a ∧ y = b) ∨ (x = a + 1 ∧ y = b) ∨ (x = a ∧ y = b + 1)

variable {G : SimpleGraph Vertex}

theorem neighbors_A (laws : NeighborLaws G) (x y : ℤ) (w : Vertex) :
    G.Adj (A x y) w ↔ w = B x y ∨ w = B (x - 1) y ∨ w = B x (y - 1) := by
  obtain ⟨p, a, b⟩ := w
  cases p
  · constructor
    · intro adj
      exact (laws.opposite adj rfl).elim
    · simp [B]
  · rw [show (true, a, b) = B a b from rfl, laws.fromA]
    simp only [B, Prod.mk.injEq, true_and]
    omega

theorem neighbors_B (laws : NeighborLaws G) (x y : ℤ) (w : Vertex) :
    G.Adj (B x y) w ↔ w = A x y ∨ w = A (x + 1) y ∨ w = A x (y + 1) := by
  obtain ⟨p, a, b⟩ := w
  cases p
  · rw [show (false, a, b) = A a b from rfl, G.adj_comm, laws.fromA]
    simp only [A, Prod.mk.injEq, true_and]
  · constructor
    · intro adj
      exact (laws.opposite adj rfl).elim
    · simp [A]

def part (v : Vertex) : ℤ := if v.1 then 1 else 0

def heightSum (v : Vertex) : ℤ := v.2.1 + v.2.2

def g (v : Vertex) : ℤ := 2 * v.2.1 + v.2.2 + part v

def earliest (v : Vertex) : ℕ := (g v + v.2.2).toNat

def horizon (P : ℕ) (v : Vertex) : ℕ := (2 * v.2.1 + part v + 2 * (P : ℤ)).toNat

def domain (a K : ℕ) : Finset Vertex :=
  ((Finset.univ : Finset Bool) ×ˢ
    (Finset.Ico (0 : ℤ) a ×ˢ Finset.Ico (0 : ℤ) a)).filter
      (fun v => heightSum v < a ∧ g v < K)

@[simp] theorem mem_domain {a K : ℕ} {v : Vertex} :
    v ∈ domain a K ↔ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧ heightSum v < a ∧ g v < K := by
  obtain ⟨p, x, y⟩ := v
  unfold domain
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  simp only [Finset.mem_univ, true_and, Finset.mem_Ico, heightSum]
  omega

theorem domain_mono {m N K : ℕ} (le : m ≤ N) : domain m K ⊆ domain N K := by
  intro v hv
  obtain ⟨hx, hy, hs, hg⟩ := mem_domain.mp hv
  exact mem_domain.mpr ⟨hx, hy, by omega, hg⟩

theorem seed_mem {a K : ℕ} (ha : 0 < a) (hK : 0 < K) : A 0 0 ∈ domain a K := by
  simp [A, heightSum, g, part, ha, hK]

private theorem horizon_step (laws : NeighborLaws G) (P : ℕ) {v w : Vertex}
    (adj : G.Adj v w) : horizon P v ≤ horizon P w + 1 := by
  obtain ⟨p, x, y⟩ := v
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [horizon, A, B, part] <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [horizon, A, B, part] <;> omega

private theorem earliest_step (laws : NeighborLaws G) {v w : Vertex}
    (adj : G.Adj v w) : earliest v ≤ earliest w + 1 := by
  obtain ⟨p, x, y⟩ := v
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [earliest, g, A, B, part] <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [earliest, g, A, B, part] <;> omega

private theorem predecessor_closed (laws : NeighborLaws G) {a K : ℕ} {v w : Vertex}
    (hv : v ∈ domain a K) (adj : G.Adj v w)
    (hx : 0 ≤ w.2.1) (hy : 0 ≤ w.2.2) (earlier : earliest w < earliest v) :
    w ∈ domain a K := by
  obtain ⟨hxv, hyv, sum, cut⟩ := mem_domain.mp hv
  apply mem_domain.mpr
  refine ⟨hx, hy, ?_⟩
  obtain ⟨p, x, y⟩ := v
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [earliest, g, heightSum, A, B, part] at * <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [earliest, g, heightSum, A, B, part] at * <;> omega

private theorem crossing_edge (laws : NeighborLaws G) {m N K : ℕ} {v w : Vertex}
    (outer : v ∈ domain N K) (outside : v ∉ domain m K)
    (shared : w ∈ domain m K) (adj : G.Adj v w) :
    v.1 = false ∧ w.1 = true ∧ heightSum v = m ∧ heightSum w = (m : ℤ) - 1 := by
  obtain ⟨hx, hy, _, hg⟩ := mem_domain.mp outer
  have sumOutside : (m : ℤ) ≤ heightSum v := by
    by_contra! below
    exact outside (mem_domain.mpr ⟨hx, hy, below, hg⟩)
  have sumInside := (mem_domain.mp shared).2.2.1
  obtain ⟨p, x, y⟩ := v
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      simp [heightSum, A, B] at * <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      simp [heightSum, A, B] at * <;> omega

variable [DecidableRel G.Adj]

theorem earliest_bound (laws : NeighborLaws G) {D : Finset Vertex}
    {t μ : ℕ} {v : Vertex} (he : Touch G D (A 0 0) t v μ) :
    earliest v ≤ t :=
  earliest_touch earliest rfl (by intro v w hv hw adj; exact earliest_step laws adj) he

/-- The precise positive direction of Lemma 7 used at the two wall parents. -/
def EarliestBirths (G : SimpleGraph Vertex) [DecidableRel G.Adj] (D : Finset Vertex) : Prop :=
  ∀ v ∈ D, v.2.1.toNat &&& v.2.2.toNat = 0 → Born G D (A 0 0) (earliest v) v

/-- The two eligible wall parents send together. Their common child is blocked. -/
private theorem wall_first_touch (laws : NeighborLaws G) {b m N K x y : ℕ}
    (divides : 2 ^ b ∣ m) (sum : x + y = m) (hy₀ : 0 < y) (hy : y < 2 ^ b)
    (retained : A x y ∈ domain N K) (first : EarliestBirths G (domain N K)) :
    Touch G (domain N K) (A 0 0) (2 * m) (A x y) 2 := by
  have hm : 0 < m := by omega
  have hP := Nat.le_of_dvd hm divides
  have hx : 0 < x := by omega
  let t := 2 * m - 1
  let left := B ((x : ℤ) - 1) y
  let down := B x ((y : ℤ) - 1)
  have tNext : t + 1 = 2 * m := by dsimp [t]; omega
  have timeA : earliest (A x y) = 2 * m := by
    dsimp [earliest, g, A, part]
    omega
  have timeLeft : earliest left = t := by
    dsimp [left, earliest, g, B, part, t]
    omega
  have timeDown : earliest down = t := by
    dsimp [down, earliest, g, B, part, t]
    omega
  have adjLeft : G.Adj (A x y) left := (neighbors_A laws x y left).mpr (Or.inr (Or.inl rfl))
  have adjDown : G.Adj (A x y) down := (neighbors_A laws x y down).mpr (Or.inr (Or.inr rfl))
  have memLeft : left ∈ domain N K :=
    predecessor_closed laws retained adjLeft (by dsimp [left, B]; omega)
      (by simp [left, B]) (by omega)
  have memDown : down ∈ domain N K :=
    predecessor_closed laws retained adjDown (by simp [down, B])
      (by dsimp [down, B]; omega) (by omega)
  obtain ⟨bitsLeft, bitsDown⟩ := wall_parent_bits divides sum hy₀ hy
  have toNatX : ((x : ℤ) - 1).toNat = x - 1 := by omega
  have toNatY : ((y : ℤ) - 1).toNat = y - 1 := by omega
  have bornLeft : Born G (domain N K) (A 0 0) t left := by
    rw [← timeLeft]
    exact first left memLeft (by simpa [left, B, toNatX] using bitsLeft)
  have bornDown : Born G (domain N K) (A 0 0) t down := by
    rw [← timeDown]
    exact first down memDown (by simpa [down, B, toNatY] using bitsDown)
  have intact : Intact G (domain N K) (A 0 0) t (A x y) :=
    intact_iff_no_touch.mpr fun s hs μ he => by
      have bound := earliest_bound laws he
      omega
  have thirdTooLate : ¬ Born G (domain N K) (A 0 0) t (B x y) := by
    intro born
    have bound := earliest_bound laws born
    dsimp [earliest, g, B, part, t] at bound
    omega
  have actualSenders : senders G (domain N K) (A 0 0) t (A x y) = {left, down} := by
    ext w
    simp only [mem_senders, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, adj, born⟩
      rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl
      · exact (thirdTooLate born).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨memLeft, adjLeft, bornLeft⟩
      · exact ⟨memDown, adjDown, bornDown⟩
  have distinct : left ≠ down := by
    intro h
    have coord := congrArg (fun v : Vertex => v.2.1) h
    dsimp [left, down, B] at coord
    omega
  rw [← tNext]
  exact touch_succ_iff.mpr ⟨intact, retained, by decide, by
    rw [actualSenders]
    exact Finset.card_pair_eq_two_iff.mpr distinct⟩

private theorem wall_no_birth (laws : NeighborLaws G) {b m N K x y : ℕ}
    (divides : 2 ^ b ∣ m) (sum : x + y = m) (upperCut : K ≤ 2 * m)
    (retained : A x y ∈ domain N K) (first : EarliestBirths G (domain N K))
    {t : ℕ} (short : t < horizon (2 ^ b) (A x y)) :
    ¬ Born G (domain N K) (A 0 0) t (A x y) := by
  intro born
  have gCut := (mem_domain.mp retained).2.2.2
  have hy₀ : 0 < y := by
    dsimp [g, A, part] at gCut
    omega
  by_cases small : y < 2 ^ b
  · have wallTouch := wall_first_touch laws divides sum hy₀ small retained first
    exact (by decide : (1 : ℕ) ≠ 2) (touch_unique born wallTouch).2
  · have earliestLimit := earliest_bound laws born
    generalize hP : (2 ^ b : ℕ) = P at small short
    dsimp [horizon, A, part] at short
    dsimp [earliest, g, A, part] at earliestLimit
    omega

/-- The geometric local lemma, given the adjacency law and Lemma 7 on the larger domain. -/
theorem clipped_first_touch (laws : NeighborLaws G) {b m N K : ℕ}
    (hm : 0 < m) (hN : m < N) (hK : 1 ≤ K) (upperCut : K ≤ 2 * m)
    (divides : 2 ^ b ∣ m) (first : EarliestBirths G (domain N K)) (t : ℕ) :
    (∀ v ∈ domain m K, t < horizon (2 ^ b) v → ∀ μ, 0 < μ →
      (Touch G (domain m K) (A 0 0) t v μ ↔ Touch G (domain N K) (A 0 0) t v μ)) ∧
    (∀ v ∈ domain N K, v ∉ domain m K → t < horizon (2 ^ b) v →
      ¬ Born G (domain N K) (A 0 0) t v) := by
  apply strict_horizon (horizon (2 ^ b)) (domain_mono hN.le) (seed_mem hm hK)
    (by intro v w adj; exact horizon_step laws _ adj)
  intro v outer outside boundary s short
  obtain ⟨w, shared, adj⟩ := boundary
  obtain ⟨color, _, wallSum, _⟩ := crossing_edge laws outer outside shared adj
  obtain ⟨hx, hy, _, _⟩ := mem_domain.mp outer
  obtain ⟨p, x, y⟩ := v
  have asA : (p, x, y) = A x.toNat y.toNat := by
    simp only [A, Prod.mk.injEq]
    exact ⟨color, (Int.toNat_of_nonneg hx).symm, (Int.toNat_of_nonneg hy).symm⟩
  rw [asA] at outer short ⊢
  have sum : x.toNat + y.toNat = m := by
    dsimp [heightSum] at wallSum
    dsimp at hx hy
    omega
  exact wall_no_birth laws divides sum upperCut outer first short

end

section

/-! Cut domains and the earliest-birth law. -/

/-- The domain of §4.1, for positive integral height and the source cut range. -/
def omegaDomain (a d : ℕ) : Finset Vertex := domain a (2 * a - d)

theorem domain_cut_mono {a K K' : ℕ} (le : K ≤ K') : domain a K ⊆ domain a K' := by
  intro v hv
  obtain ⟨hx, hy, hs, hg⟩ := mem_domain.mp hv
  exact mem_domain.mpr ⟨hx, hy, hs, by omega⟩

/-- Both directions of the paper's Lemma 7 on the domains used by Theorem 12. -/
def EarliestBirthIff (G : SimpleGraph Vertex) [DecidableRel G.Adj] : Prop :=
  ∀ a d, 0 < a → d ≤ a → ∀ v ∈ omegaDomain a d,
    Born G (omegaDomain a d) (A 0 0) (earliest v) v ↔
      v.2.1.toNat &&& v.2.2.toNat = 0

end

section

/-! Lucas parity for the earliest Pascal front. -/

private theorem land_zero_iff_half (x y : ℕ) :
    x &&& y = 0 ↔ ¬ (x % 2 = 1 ∧ y % 2 = 1) ∧ (x / 2) &&& (y / 2) = 0 := by
  have firstBit (n : ℕ) : n.testBit 0 = decide (n % 2 = 1) := by
    simp [Nat.testBit_eq_decide_div_mod_eq]
  constructor
  · intro zero
    constructor
    · rintro ⟨hx, hy⟩
      have h := congrArg (fun n : ℕ => n.testBit 0) zero
      simp [firstBit, hx, hy] at h
    · apply Nat.eq_of_testBit_eq
      intro i
      have h := congrArg (fun n : ℕ => n.testBit (i + 1)) zero
      rw [Nat.testBit_land, Nat.testBit_add_one, Nat.testBit_add_one, Nat.zero_testBit] at h
      simpa only [Nat.testBit_land, Nat.zero_testBit] using h
  · rintro ⟨first, higher⟩
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_land, Nat.zero_testBit, firstBit, firstBit]
      by_cases hx : x % 2 = 1
      · have hy : y % 2 ≠ 1 := fun hy => first ⟨hx, hy⟩
        simp [hx, hy]
      · simp [hx]
    | succ i =>
      rw [Nat.testBit_land, Nat.testBit_add_one, Nat.testBit_add_one, Nat.zero_testBit]
      simpa only [Nat.testBit_land, Nat.zero_testBit] using
        congrArg (fun n : ℕ => n.testBit i) higher

/-- The binary Lucas criterion for the Pascal recurrence on quadrant coordinates. -/
private theorem choose_odd_iff_disjoint (x y : ℕ) :
    (x + y).choose x % 2 = 1 ↔ x &&& y = 0 := by
  by_cases hz : x + y = 0
  · obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := by omega
    decide
  rw [land_zero_iff_half]
  have dec : x / 2 + y / 2 < x + y := by omega
  have ih := choose_odd_iff_disjoint (x / 2) (y / 2)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := x + y) (k := x)
  change (x + y).choose x % 2 =
    (((x + y) % 2).choose (x % 2) * ((x + y) / 2).choose (x / 2)) % 2 at lucas
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hx | hx <;>
    rcases (show y % 2 = 0 ∨ y % 2 = 1 by omega) with hy | hy
  · have low : (x + y) % 2 = 0 := by omega
    have high : (x + y) / 2 = x / 2 + y / 2 := by omega
    simpa [lucas, hx, hy, low, high] using ih
  · have high : (x + y) / 2 = x / 2 + y / 2 := by omega
    simpa [lucas, hx, hy, high] using ih
  · have low : (x + y) % 2 = 1 := by omega
    have high : (x + y) / 2 = x / 2 + y / 2 := by omega
    simpa [lucas, hx, hy, low, high] using ih
  · have low : (x + y) % 2 = 0 := by omega
    simp [lucas, hx, hy, low]
termination_by x + y

end

section

/-! Earliest births on both sublattices. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem earliest_A_nat (x y : ℕ) :
    earliest (A x y) = 2 * (x + y) := by
  simp [earliest, g, A, part]
  omega

private theorem earliest_B_nat (x y : ℕ) :
    earliest (B x y) = 2 * (x + y) + 1 := by
  simp [earliest, g, B, part]
  omega

private theorem intact_from_earliest (laws : NeighborLaws G) {D : Finset Vertex}
    {v : Vertex} {t : ℕ} (early : t < earliest v) : Intact G D (A 0 0) t v :=
  intact_iff_no_touch.mpr fun _ ht _ touch =>
    not_lt_of_ge ((earliest_bound laws touch).trans ht) early

private theorem birth_B_at_earliest (laws : NeighborLaws G)
    {a d x y : ℕ} (retained : B x y ∈ omegaDomain a d) :
    Born G (omegaDomain a d) (A 0 0) (earliest (B x y)) (B x y) ↔
      Born G (omegaDomain a d) (A 0 0) (earliest (A x y)) (A x y) := by
  let D := omegaDomain a d
  let t := 2 * (x + y)
  have tA : earliest (A x y) = t := earliest_A_nat _ _
  have tB : earliest (B x y) = t + 1 := earliest_B_nat _ _
  rw [tA, tB, born_succ_iff]
  have hIntact : Intact G D (A 0 0) t (B x y) :=
    intact_from_earliest laws (by rw [tB]; omega)
  change (Intact G D (A 0 0) t (B x y) ∧ B x y ∈ D ∧
    (senders G D (A 0 0) t (B x y)).card = 1) ↔ Born G D (A 0 0) t (A x y)
  have hMem : B x y ∈ D := retained
  simp only [hIntact, hMem, true_and]
  have hSenders : ∀ w ∈ senders G D (A 0 0) t (B x y), w = A x y := by
    intro w hw
    obtain ⟨_, adj, hb⟩ := mem_senders.mp hw
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl
    · rfl
    · have h := earliest_bound laws hb
      simp [earliest, g, A, part, t] at h
      omega
    · have h := earliest_bound laws hb
      simp [earliest, g, A, part, t] at h
      omega
  constructor
  · intro card
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega :
      0 < (senders G D (A 0 0) t (B x y)).card)
    have birth := (mem_senders.mp hw).2.2
    rwa [hSenders w hw] at birth
  · intro birth
    have sender : A x y ∈ senders G D (A 0 0) t (B x y) :=
      mem_senders.mpr ⟨(touch_retained_and_positive birth).1,
        (neighbors_B laws x y _).mpr (Or.inl rfl), birth⟩
    have eq : senders G D (A 0 0) t (B x y) = {A x y} := by
      ext w
      simp only [Finset.mem_singleton]
      exact ⟨hSenders w, fun h => h ▸ sender⟩
    simp [eq]

private theorem card_one_of_two {F : Finset Vertex} {u w : Vertex}
    (ne : u ≠ w) (all : ∀ v ∈ F, v = u ∨ v = w) :
    F.card = 1 ↔ (u ∈ F ∧ w ∉ F) ∨ (u ∉ F ∧ w ∈ F) := by
  constructor
  · intro h
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
    obtain rfl | rfl := all v (Finset.mem_singleton_self v)
    · simp [ne.symm]
    · simp [ne]
  · rintro (⟨hu, hw⟩ | ⟨hu, hw⟩)
    · apply Finset.card_eq_one.mpr
      refine ⟨u, ?_⟩
      ext v
      simp only [Finset.mem_singleton]
      exact ⟨fun hv => (all v hv).resolve_right (fun h => hw (h ▸ hv)), fun h => h ▸ hu⟩
    · apply Finset.card_eq_one.mpr
      refine ⟨w, ?_⟩
      ext v
      simp only [Finset.mem_singleton]
      exact ⟨fun hv => (all v hv).resolve_left (fun h => hu (h ▸ hv)), fun h => h ▸ hw⟩

private theorem birth_A_at_earliest (laws : NeighborLaws G) {a d x y : ℕ}
    (retained : A x y ∈ omegaDomain a d) (pos : 0 < x + y) :
    let D := omegaDomain a d
    let t := 2 * (x + y) - 1
    let left := Born G D (A 0 0) t (B ((x : ℤ) - 1) y)
    let down := Born G D (A 0 0) t (B x ((y : ℤ) - 1))
    Born G D (A 0 0) (earliest (A x y)) (A x y) ↔
      (left ∧ ¬ down) ∨ (¬ left ∧ down) := by
  dsimp only
  let D := omegaDomain a d
  let t := 2 * (x + y) - 1
  let u := B ((x : ℤ) - 1) y
  let w := B x ((y : ℤ) - 1)
  let F := senders G D (A 0 0) t (A x y)
  change Born G D (A 0 0) (earliest (A x y)) (A x y) ↔
    (Born G D (A 0 0) t u ∧ ¬ Born G D (A 0 0) t w) ∨
    (¬ Born G D (A 0 0) t u ∧ Born G D (A 0 0) t w)
  have eTime : earliest (A x y) = t + 1 := by rw [earliest_A_nat]; dsimp [t]; omega
  have hIntact : Intact G D (A 0 0) t (A x y) :=
    intact_from_earliest laws (by rw [eTime]; omega)
  have hMem : A x y ∈ D := retained
  rw [eTime, born_succ_iff]
  simp only [hIntact, hMem, true_and]
  have all : ∀ v ∈ F, v = u ∨ v = w := by
    intro v hv
    obtain ⟨_, adj, hb⟩ := mem_senders.mp hv
    rcases (neighbors_A laws x y v).mp adj with rfl | rfl | rfl
    · have late := earliest_bound laws hb
      rw [earliest_B_nat] at late
      dsimp [t] at late
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  have ne : u ≠ w := by
    intro h
    have coord := congrArg (fun v : Vertex => v.2.1) h
    dsimp [u, w, B] at coord
    omega
  have memIff {v : Vertex} (adj : G.Adj (A x y) v) :
      v ∈ F ↔ Born G D (A 0 0) t v :=
    ⟨fun h => (mem_senders.mp h).2.2,
      fun h => mem_senders.mpr ⟨(touch_retained_and_positive h).1, adj, h⟩⟩
  change F.card = 1 ↔ _
  rw [card_one_of_two ne all, memIff ((neighbors_A laws x y u).mpr (Or.inr (Or.inl rfl))),
    memIff ((neighbors_A laws x y w).mpr (Or.inr (Or.inr rfl)))]

private theorem parity_add_iff (p q : ℕ) :
    (p + q) % 2 = 1 ↔ (p % 2 = 1 ∧ q % 2 ≠ 1) ∨ (p % 2 ≠ 1 ∧ q % 2 = 1) := by
  omega

private theorem earliest_A_iff_choose (laws : NeighborLaws G) {a d : ℕ}
    (x y : ℕ) (retained : A x y ∈ omegaDomain a d) :
    Born G (omegaDomain a d) (A 0 0) (earliest (A x y)) (A x y) ↔
      (x + y).choose x % 2 = 1 := by
  have leftRet (u : ℕ) (hx : x = u + 1) : B u y ∈ omegaDomain a d :=
    predecessor_closed laws retained
      ((neighbors_A laws x y _).mpr (Or.inr (Or.inl (by simp [B, hx]))))
      (by simp [B]) (by simp [B])
      (by rw [earliest_B_nat, earliest_A_nat, hx]; omega)
  have downRet (v : ℕ) (hy : y = v + 1) : B x v ∈ omegaDomain a d :=
    predecessor_closed laws retained
      ((neighbors_A laws x y _).mpr (Or.inr (Or.inr (by simp [B, hy]))))
      (by simp [B]) (by simp [B])
      (by rw [earliest_B_nat, earliest_A_nat, hy]; omega)
  have retainedA {u v : ℕ} (hb : B u v ∈ omegaDomain a d) : A u v ∈ omegaDomain a d :=
    predecessor_closed laws hb ((neighbors_B laws u v _).mpr (Or.inl rfl))
      (by simp [A]) (by simp [A]) (by rw [earliest_B_nat, earliest_A_nat]; omega)
  cases x with
  | zero =>
    cases y with
    | zero =>
      rw [earliest_A_nat]
      have seed : Born G (omegaDomain a d) (A 0 0) 0 (A 0 0) :=
        touch_zero_iff.mpr ⟨retained, rfl, rfl⟩
      simpa using seed
    | succ y =>
      have hb := downRet y rfl
      have ih := earliest_A_iff_choose laws 0 y (retainedA hb)
      have hdown := (birth_B_at_earliest laws hb).mpr (ih.mpr (by simp))
      rw [earliest_B_nat] at hdown
      have recurrence := birth_A_at_earliest laws retained (by omega)
      dsimp only at recurrence
      rw [recurrence]
      have noLeft : ¬ Born G (omegaDomain a d) (A 0 0) (2 * (0 + (y + 1)) - 1)
          (B ((0 : ℤ) - 1) (y + 1 : ℕ)) := by
        intro birth
        have hx := (mem_domain.mp (touch_retained_and_positive birth).1).1
        simp [B] at hx
      have yesDown : Born G (omegaDomain a d) (A 0 0) (2 * (0 + (y + 1)) - 1)
          (B 0 (((y + 1 : ℕ) : ℤ) - 1)) := by
        rwa [show 2 * (0 + (y + 1)) - 1 = 2 * (0 + y) + 1 by omega, show
          (((y + 1 : ℕ) : ℤ) - 1) = y by omega]
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        Nat.zero_add, zero_sub] at noLeft yesDown ⊢
      simp [noLeft, yesDown]
  | succ x =>
    cases y with
    | zero =>
      have hb := leftRet x rfl
      have ih := earliest_A_iff_choose laws x 0 (retainedA hb)
      have hleft := (birth_B_at_earliest laws hb).mpr (ih.mpr (by simp))
      rw [earliest_B_nat] at hleft
      have recurrence := birth_A_at_earliest laws retained (by omega)
      dsimp only at recurrence
      rw [recurrence]
      have noDown : ¬ Born G (omegaDomain a d) (A 0 0) (2 * (x + 1 + 0) - 1)
          (B (x + 1 : ℕ) ((0 : ℤ) - 1)) := by
        intro birth
        have hy := (mem_domain.mp (touch_retained_and_positive birth).1).2.1
        simp [B] at hy
      have yesLeft : Born G (omegaDomain a d) (A 0 0) (2 * (x + 1 + 0) - 1)
          (B ((((x + 1 : ℕ) : ℤ)) - 1) 0) := by
        rwa [show 2 * (x + 1 + 0) - 1 = 2 * (x + 0) + 1 by omega, show
          (((x + 1 : ℕ) : ℤ) - 1) = x by omega]
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        Nat.add_zero, zero_sub] at noDown yesLeft ⊢
      simp [noDown, yesLeft]
    | succ y =>
      have hbL := leftRet x rfl
      have hbD := downRet y rfl
      have left := (birth_B_at_earliest laws hbL).trans
        (earliest_A_iff_choose laws x (y + 1) (retainedA hbL))
      have down := (birth_B_at_earliest laws hbD).trans
        (earliest_A_iff_choose laws (x + 1) y (retainedA hbD))
      rw [earliest_B_nat] at left down
      have recurrence := birth_A_at_earliest laws retained (by omega)
      dsimp only at recurrence
      rw [recurrence]
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      simp only [Nat.cast_add, Nat.cast_one] at left down
      rw [show 2 * (x + (y + 1)) + 1 = 2 * (x + 1 + y) + 1 by omega] at left
      rw [show 2 * (x + 1 + (y + 1)) - 1 = 2 * (x + 1 + y) + 1 by omega, left, down,
        show x + 1 + (y + 1) = (x + 1 + y) + 1 by omega, Nat.choose_succ_succ',
        show x + (y + 1) = x + 1 + y by omega]
      exact (parity_add_iff _ _).symm
termination_by x + y

/-- Lemma 7 on the actual truncated triangles and the compiled synchronous growth. -/
theorem earliestBirthIff_of_neighborLaws (laws : NeighborLaws G) : EarliestBirthIff G := by
  intro a d _ _ v hv
  obtain ⟨hx, hy, _, _⟩ := mem_domain.mp hv
  obtain ⟨p, x, y⟩ := v
  have hi : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx
  have hj : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy
  cases p
  · have hv' : A x.toNat y.toNat ∈ omegaDomain a d := by simpa only [A, hi, hj] using hv
    have eq := (earliest_A_iff_choose laws x.toNat y.toNat hv').trans (choose_odd_iff_disjoint _ _)
    simpa only [A, hi, hj] using eq
  · have hv' : B x.toNat y.toNat ∈ omegaDomain a d := by simpa only [B, hi, hj] using hv
    have ha : A x.toNat y.toNat ∈ omegaDomain a d :=
      predecessor_closed laws hv' ((neighbors_B laws _ _ _).mpr (Or.inl rfl))
        (by simp [A]) (by simp [A]) (by rw [earliest_A_nat, earliest_B_nat]; omega)
    have eq := (birth_B_at_earliest laws hv').trans
      ((earliest_A_iff_choose laws x.toNat y.toNat ha).trans (choose_odd_iff_disjoint _ _))
    simpa only [B, hi, hj] using eq

end

section

/-! Adjacency of the repository honeycomb. -/

private def aToB (x y a b : ℤ) : Prop :=
  (x = a ∧ y = b) ∨ (x = a + 1 ∧ y = b) ∨ (x = a ∧ y = b + 1)

private theorem graph_adj_iff (v w : Vertex) :
    honeycombGraph.Adj v w ↔
      (v.1 = false ∧ w.1 = true ∧ aToB v.2.1 v.2.2 w.2.1 w.2.2) ∨
      (w.1 = false ∧ v.1 = true ∧ aToB w.2.1 w.2.2 v.2.1 v.2.2) :=
  Iff.rfl

@[instance_reducible] def repositoryAdjacency : DecidableRel honeycombGraph.Adj := by
  intro v w
  refine @decidable_of_iff _ _ (graph_adj_iff v w).symm ?_
  unfold aToB
  infer_instance

theorem repositoryNeighborLaws : NeighborLaws honeycombGraph where
  opposite := by
    intro v w adj
    rcases (graph_adj_iff v w).mp adj with ⟨h₁, h₂, _⟩ | ⟨h₁, h₂, _⟩ <;> simp [h₁, h₂]
  fromA := by
    intro x y a b
    rw [graph_adj_iff]
    simp [A, B, aToB]

end

end D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
