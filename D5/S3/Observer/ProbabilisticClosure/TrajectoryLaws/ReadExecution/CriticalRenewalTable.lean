/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete counted renewal rows and the joint duration-increment law of one actual gap. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.GeometricPhaseOccupation
import Mathlib.Data.Int.Interval

/-! The full finite renewal table, its fresh row realization, and complete-gap law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

namespace Phase
abbrev T (J : ℕ) := Fin (J + 1)
def first (J : ℕ) : T J := ⟨0, by omega⟩
def dead (J : ℕ) : T J := ⟨J, by omega⟩
def advance {J : ℕ} (z : T J) : T J := ⟨min (z.val + 1) J, by omega⟩
def step {J : ℕ} (z : T J) (b : Bool) : T J := if b then advance z else z
def coin {J : ℕ} (z : T J) : PMF Bool :=
  PMF.bernoulli (GeometricPhaseOccupation.success z.val)
    (by unfold GeometricPhaseOccupation.success; exact pow_le_one₀ (by norm_num) (by norm_num))
end Phase

abbrev Evidence (H : ℕ) := ↥(Finset.Ioo (-(H : ℤ)) (H : ℤ))
/-- Exactly one wait, two terminal labels, and the full evidence/phase product. -/
abbrev State (H J : ℕ) := Option (Bool ⊕ (Evidence H × Phase.T J))
def wait {H J : ℕ} : State H J := none
def label {H J : ℕ} (b : Bool) : State H J := some (.inl b)
def active {H J : ℕ} (e : Evidence H) (z : Phase.T J) : State H J := some (.inr (e,z))

def initialEvidence {H : ℕ} (hH : 0 < H) : Evidence H :=
  ⟨0, by simp only [Finset.mem_Ioo]; constructor <;> omega⟩

/-- No overshoot value is retained after either threshold is reached. -/
def target (H J : ℕ) (u : ℤ) : State H J :=
  if hupper : (H : ℤ) ≤ u then label true
  else if hlower : u ≤ -(H : ℤ) then label false
  else active ⟨u, by simp only [Finset.mem_Ioo]; omega⟩ (Phase.first J)

/-- These are immutable row entries; this structure is not part of the carrier. -/
structure Tick (J : ℕ) where
  lower : Phase.T J → ℤ
  prob : Phase.T J → ℝ≥0
  prob_le_one : ∀ z, prob z ≤ 1

def Tick.coin {J : ℕ} (t : Tick J) (z : Phase.T J) : PMF Bool :=
  PMF.bernoulli (t.prob z) (t.prob_le_one z)

def Tick.increment {J : ℕ} (t : Tick J) (z : Phase.T J) (b : Bool) : ℤ :=
  t.lower z + if b then 1 else 0

/-- The whole stochastic table. Labels are totalized by self loops. -/
def row {H J : ℕ} (hH : 0 < H) (t : Tick J) : State H J → Bool → PMF (State H J)
  | none, false => PMF.pure wait
  | none, true => PMF.pure (active (initialEvidence hH) (Phase.first J))
  | some (.inl b), _ => PMF.pure (label b)
  | some (.inr (e,z)), false =>
      (GeometricPhaseOccupation.finiteCappedRow J z).map (active e)
  | some (.inr (e,z)), true =>
      (t.coin z).map fun b => target H J (e.val + t.increment z b)


/-- Deterministic realization of a row by one fresh coin; the coin is not retained. -/
def next {H J : ℕ} (hH : 0 < H) (t : Tick J) : State H J → Bool → Bool → State H J
  | none, false, _ => wait
  | none, true, _ => active (initialEvidence hH) (Phase.first J)
  | some (.inl b), _, _ => label b
  | some (.inr (e,z)), false, b => active e (Phase.step z b)
  | some (.inr (e,z)), true, b => target H J (e.val + t.increment z b)

/-- On dead zeros both possible fresh outcomes merge into the same dead state. -/
def coin {H J : ℕ} (t : Tick J) : State H J → Bool → PMF Bool
  | some (.inr (_,z)), false => Phase.coin z
  | some (.inr (_,z)), true => t.coin z
  | _, _ => PMF.pure false

theorem phase_coin_row (J : ℕ) (z : Phase.T J) :
    ((Phase.coin z).map (Phase.step z)) = GeometricPhaseOccupation.finiteCappedRow J z := by
  unfold Phase.coin
  by_cases hz : z.val < J
  · simp only [GeometricPhaseOccupation.finiteCappedRow,
      GeometricPhaseOccupation.cappedRow, hz, ↓reduceIte,
      GeometricPhaseOccupation.zeroRow, PMF.map_comp]
    congr 1
    funext b
    apply Fin.ext
    cases b <;> simp [Function.comp_def, Phase.step, Phase.advance,
      GeometricPhaseOccupation.capState, Nat.min_eq_left (by omega : z.val ≤ J)]
  · have he : z = Phase.dead J := Fin.ext (by dsimp [Phase.dead]; omega)
    subst z
    have hm : Phase.step (Phase.dead J) = Function.const Bool (Phase.dead J) := by
      funext b
      cases b <;> simp [Phase.step, Phase.advance, Phase.dead]
    rw [hm, PMF.map_const]
    simp [GeometricPhaseOccupation.finiteCappedRow,
      GeometricPhaseOccupation.cappedRow, Phase.dead,
      GeometricPhaseOccupation.capState, PMF.map_const, PMF.pure_map]

/-- Every deterministic coin realization has exactly the declared stochastic row. -/
theorem fresh_row {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (s : State H J) (x : Bool) :
    (coin t s x).map (next hH t s x) = row hH t s x := by
  cases s with
  | none => cases x <;> simp [coin, next, row, wait, PMF.pure_map]
  | some s =>
    cases s with
    | inl b => cases x <;> simp [coin, next, row, label, PMF.pure_map]
    | inr ez =>
      rcases ez with ⟨e,z⟩
      cases x with
      | false =>
        change ((Phase.coin z).map fun b => active e (Phase.step z b)) = _
        change ((Phase.coin z).map ((active e) ∘ Phase.step z)) = _
        rw [← PMF.map_comp, phase_coin_row]
        rfl
      | true => rfl

/-- A finite word always charges one transition per actual bit. -/
def wordLaw {H J : ℕ} (hH : 0 < H) (t : Tick J) :
    State H J → List Bool → PMF (State H J)
  | s, [] => PMF.pure s
  | s, b :: w => ((coin t s b).map (next hH t s b)).bind fun s' => wordLaw hH t s' w

private lemma wordLaw_append {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (s : State H J) (v w : List Bool) :
    wordLaw hH t s (v ++ w) = (wordLaw hH t s v).bind fun s' => wordLaw hH t s' w := by
  induction v generalizing s with
  | nil => simp [wordLaw]
  | cons b v ih => simp only [List.cons_append, wordLaw, ih, PMF.bind_bind]

private lemma zeroLaw {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (e : Evidence H) (k : ℕ) :
    wordLaw hH t (active e (Phase.first J)) (List.replicate k false) =
      (GeometricPhaseOccupation.finiteCappedLaw J k).map (active e) := by
  induction k with
  | zero => simp [wordLaw, GeometricPhaseOccupation.finiteCappedLaw, Phase.first, PMF.pure_map]
  | succ k ih =>
    rw [List.replicate_succ', wordLaw_append, ih]
    simp only [PMF.bind_map, Function.comp_def, wordLaw, fresh_row, PMF.bind_pure,
      row, active, GeometricPhaseOccupation.finiteCappedLaw, PMF.map_bind]

/-- The same zero-chain supplies the phase used by the tick, also for k=0. -/
theorem complete_gap_row {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (e : Evidence H) (k : ℕ) :
    wordLaw hH t (active e (Phase.first J)) (List.replicate k false ++ [true]) =
      (GeometricPhaseOccupation.finiteCappedLaw J k).bind fun z =>
        (t.coin z).map fun b => target H J (e.val + t.increment z b) := by
  rw [wordLaw_append, zeroLaw]
  simp only [PMF.bind_map, Function.comp_def, wordLaw, fresh_row, PMF.bind_pure, row, active]

/-- A duration and its own terminal increment are sampled jointly. -/
def pairLaw {J : ℕ} (f : PMF ℕ) (t : Tick J) : PMF (ℕ × ℤ) :=
  f.bind fun k => (GeometricPhaseOccupation.finiteCappedLaw J k).bind fun z =>
    (t.coin z).map fun b => (k, t.increment z b)

/-- The joint potential law drives the literal complete-gap table, with no
    independence assumption between its duration and its increment. -/
theorem random_gap_row {H J : ℕ} (hH : 0 < H) (f : PMF ℕ)
    (t : Tick J) (e : Evidence H) :
    (f.bind fun k => wordLaw hH t (active e (Phase.first J))
      (List.replicate k false ++ [true])) =
        (pairLaw f t).map (fun ku => target H J (e.val + ku.2)) := by
  simp only [complete_gap_row, pairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- All listed configurations count, whether or not a row can reach them. -/
theorem full_state_count (H J : ℕ) (hH : 0 < H) :
    Fintype.card (State H J) = 3 + (2 * H - 1) * (J + 1) := by
  have he : Fintype.card (Evidence H) = 2 * H - 1 := by
    rw [Fintype.card_coe, Int.card_Ioo]
    omega
  simp [State, Fintype.card_option, Fintype.card_sum, Fintype.card_prod, he, Phase.T]
  omega

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable
