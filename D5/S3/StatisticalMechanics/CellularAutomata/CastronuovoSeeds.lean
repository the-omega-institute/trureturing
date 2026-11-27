/- GID: D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: One four-input cellular rule separates complete simple rings and unrestricted line seeds from simple line seeds. -/

import OmegaBuild.Commands
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

compile_only_with_mathlib

/-! Castronuovo–Dennunzio–Margara, arXiv:2610.34096v1, §§2.2–2.5 and p. 24. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds

abbrev Inputs (k : ℕ) := Fin k → Bool
abbrev Letter (k : ℕ) := Inputs k → Bool
abbrev LocalRule (n : ℕ) := (Fin n → Bool) → Bool

def constant {k : ℕ} (b : Bool) : Letter k := fun _ => b
def projection {k : ℕ} (j : Fin k) : Letter k := fun u => u j

-- Section 2.2: for positive n the left radius is (n - 1) / 2,
-- and the right radius is the final offset, n / 2.
def offset {n : ℕ} (j : Fin n) : ℤ :=
  (j.val : ℤ) - ((n - 1) / 2 : ℕ)

def lineMove (i δ : ℤ) : ℤ := i + δ
def ringMove {N : ℕ} (i : ZMod N) (δ : ℤ) : ZMod N := i + (δ : ZMod N)

def step {S : Type} {n : ℕ} (φ : LocalRule n) (move : S → ℤ → S)
    (P : S → Bool) (i : S) : Bool :=
  φ (fun j => P (move i (offset j)))

def evaluate {S : Type} {k : ℕ} (P : S → Letter k) (u : Inputs k) : S → Bool :=
  fun i => P i u

def liftStep {S : Type} {n k : ℕ} (φ : LocalRule n) (move : S → ℤ → S)
    (P : S → Letter k) (i : S) (u : Inputs k) : Bool :=
  step φ move (evaluate P u) i

abbrev lineStep {n k : ℕ} (φ : LocalRule n) := liftStep (k := k) φ lineMove
abbrev ringStep {N n k : ℕ} (φ : LocalRule n) := liftStep (k := k) φ (ringMove (N := N))

def orbit {C : Type} (F : C → C) : ℕ → C → C
  | 0, P => P
  | t + 1, P => F (orbit F t P)

private theorem evaluate_orbit {S : Type} {n k : ℕ} (φ : LocalRule n) (move : S → ℤ → S)
    (t : ℕ) (P : S → Letter k) (u : Inputs k) :
    evaluate (orbit (liftStep φ move) t P) u = orbit (step φ move) t (evaluate P u) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step φ move (evaluate (orbit (liftStep φ move) t P) u) = _
    rw [ih]
    rfl

-- Definitions 2.10 and 2.11.
def InSeedAlphabet {k : ℕ} (f : Letter k) : Prop :=
  f = constant false ∨ f = constant true ∨ ∃ j : Fin k, f = projection j

def SeedAlphabet {S : Type} {k : ℕ} (P : S → Letter k) : Prop :=
  ∀ i, InSeedAlphabet (P i)

def FiniteBackground {k : ℕ} (γ : Bool) (P : ℤ → Letter k) : Prop :=
  {i | P i ≠ constant γ}.Finite

def LineSeed {k : ℕ} (P : ℤ → Letter k) : Prop :=
  SeedAlphabet P ∧ ∃ γ : Bool, FiniteBackground γ P

def CyclicSeed {N k : ℕ} (n : ℕ) (P : ZMod N → Letter k) : Prop :=
  n ≤ N ∧ SeedAlphabet P

def Simple {S : Type} {k : ℕ} (P : S → Letter k) : Prop :=
  ∀ j : Fin k, ∃! i : S, P i = projection j

-- Definition 2.12, allowing a translated origin on the line.
def wordOnLine {L k : ℕ} (w : Fin L → Letter k) (γ : Bool) (origin i : ℤ) : Letter k :=
  if h : 0 ≤ i - origin ∧ i - origin < (L : ℤ) then
    w ⟨(i - origin).toNat, by omega⟩
  else constant γ

def wordOnRing {L N k : ℕ} [NeZero N] (w : Fin L → Letter k)
    (γ : Bool) (i : ZMod N) : Letter k :=
  if h : i.val < L then w ⟨i.val, h⟩ else constant γ

-- Definition 2.13. Time zero is included.
def Realized {S : Type} {k : ℕ} (F : (S → Letter k) → (S → Letter k))
    (P : S → Letter k) : Set (Letter k) :=
  {f | ∃ i : S, ∃ t : ℕ, orbit F t P i = f}

def Complete {S : Type} {k : ℕ} (F : (S → Letter k) → (S → Letter k))
    (P : S → Letter k) : Prop :=
  Realized F P = Set.univ

private theorem complete_iff {S : Type} {k : ℕ} (F : (S → Letter k) → (S → Letter k))
    (P : S → Letter k) :
    Complete F P ↔ ∀ f : Letter k, ∃ i : S, ∃ t : ℕ, orbit F t P i = f := by
  simp only [Complete, Set.eq_univ_iff_forall, Realized, Set.mem_ofPred_eq]

def Universal {n : ℕ} (φ : LocalRule n) (k : ℕ) : Prop :=
  ∃ P : ℤ → Letter k, LineSeed P ∧ Complete (lineStep φ) P

def StronglyUniversal {n : ℕ} (φ : LocalRule n) (k : ℕ) : Prop :=
  ∃ P : ℤ → Letter k, LineSeed P ∧ Simple P ∧ Complete (lineStep φ) P

def StronglyCyclicUniversal {n : ℕ} (φ : LocalRule n) (k : ℕ) : Prop :=
  ∃ (N : ℕ) (P : ZMod N → Letter k), CyclicSeed n P ∧ Simple P ∧ Complete (ringStep φ) P

def rule (a b c d : Bool) : Bool := !a && ((b && !c) || d)

def phi : LocalRule 4 := fun w => rule (w 0) (w 1) (w 2) (w 3)

private theorem phi_line_step (P : ℤ → Bool) (i : ℤ) :
    step phi lineMove P i = rule (P (i - 1)) (P i) (P (i + 1)) (P (i + 2)) := by
  change rule (P (i + (-1))) (P (i + 0)) (P (i + 1)) (P (i + 2)) = _
  rw [add_zero, sub_eq_add_neg]

def assignment (x y : Bool) : Inputs 2 := ![x, y]

private theorem assignment_surjective (u : Inputs 2) : ∃ x y, u = assignment x y := by
  refine ⟨u 0, u 1, ?_⟩
  funext j
  fin_cases j <;> rfl

def decodeMask (m : ℕ) : Letter 2 :=
  fun u => m.testBit (2 * (u 0).toNat + (u 1).toNat)

def maskOf (b00 b01 b10 b11 : Bool) : Fin 16 :=
  ⟨b00.toNat + 2 * b01.toNat + 4 * b10.toNat + 8 * b11.toNat, by
    cases b00 <;> cases b01 <;> cases b10 <;> cases b11 <;> decide⟩

def encodeMask (f : Letter 2) : Fin 16 :=
  maskOf (f (assignment false false)) (f (assignment false true))
    (f (assignment true false)) (f (assignment true true))

private theorem decode_encode (f : Letter 2) : decodeMask (encodeMask f).val = f := by
  funext u
  obtain ⟨x, y, rfl⟩ := assignment_surjective u
  unfold encodeMask
  cases x <;> cases y <;>
    cases f (assignment false false) <;>
    cases f (assignment false true) <;>
    cases f (assignment true false) <;>
    cases f (assignment true true) <;>
    rfl

def ringWord : Fin 5 → Letter 2 :=
  ![projection 0, projection 1, constant false, constant false, constant true]

def ringSeed : ZMod 5 → Letter 2 := wordOnRing ringWord false

private theorem ring_seed_alphabet : SeedAlphabet ringSeed := by
  intro i
  fin_cases i
  · exact Or.inr (Or.inr ⟨0, rfl⟩)
  · exact Or.inr (Or.inr ⟨1, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

private theorem ring_seed_simple : Simple ringSeed := by
  intro j
  fin_cases j
  · refine ⟨0, rfl, ?_⟩
    intro i h
    fin_cases i
    · rfl
    · have bad := congrFun h (assignment true false)
      cases bad
    · have bad := congrFun h (assignment true false)
      cases bad
    · have bad := congrFun h (assignment true false)
      cases bad
    · have bad := congrFun h (assignment false false)
      cases bad
  · refine ⟨1, rfl, ?_⟩
    intro i h
    fin_cases i
    · have bad := congrFun h (assignment false true)
      cases bad
    · rfl
    · have bad := congrFun h (assignment false true)
      cases bad
    · have bad := congrFun h (assignment false true)
      cases bad
    · have bad := congrFun h (assignment false false)
      cases bad

def ringTable : Fin 6 → ZMod 5 → ℕ :=
  ![![12, 10, 0, 0, 15],
    ![0, 2, 5, 12, 11],
    ![4, 14, 9, 0, 3],
    ![8, 2, 1, 4, 15],
    ![0, 6, 13, 8, 3],
    ![12, 10, 1, 0, 7]]

def ringWitness (m : Fin 16) : Fin 6 × ZMod 5 :=
  ![(0, 2), (3, 2), (1, 1), (2, 4), (2, 0), (1, 2), (4, 1), (5, 4),
    (3, 0), (2, 2), (0, 1), (1, 4), (0, 0), (4, 2), (2, 1), (0, 4)] m

private theorem ring_witness_mask (m : Fin 16) :
    ringTable (ringWitness m).1 (ringWitness m).2 = m.val := by
  fin_cases m <;> rfl

private theorem every_letter_in_ring_table (f : Letter 2) :
    ∃ (t : Fin 6) (i : ZMod 5), decodeMask (ringTable t i) = f := by
  let witness := ringWitness (encodeMask f)
  refine ⟨witness.1, witness.2, ?_⟩
  rw [ring_witness_mask (encodeMask f), decode_encode]

-- The negative inputs lie at odd offsets. The positive inputs lie at even offsets.
private theorem rule_signed_monotone (a a' b b' c c' d d' : Bool) :
    a' ≤ a → b ≤ b' → c' ≤ c → d ≤ d' → rule a b c d ≤ rule a' b' c' d' := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    cases c <;> cases c' <;> cases d <;> cases d' <;> decide

def CheckerLE (P Q : ℤ → Bool) : Prop :=
  ∀ i, if i % 2 = 0 then P i ≤ Q i else Q i ≤ P i

private theorem step_checker_mono {P Q : ℤ → Bool} (h : CheckerLE P Q) :
    CheckerLE (step phi lineMove P) (step phi lineMove Q) := by
  intro i
  by_cases even : i % 2 = 0
  · simp only [ite_eq_left even, phi_line_step]
    apply rule_signed_monotone
    · simpa only [ite_eq_right (show (i - 1) % 2 ≠ 0 by omega)] using h (i - 1)
    · simpa only [ite_eq_left even] using h i
    · simpa only [ite_eq_right (show (i + 1) % 2 ≠ 0 by omega)] using h (i + 1)
    · simpa only [ite_eq_left (show (i + 2) % 2 = 0 by omega)] using h (i + 2)
  · simp only [ite_eq_right even, phi_line_step]
    apply rule_signed_monotone
    · simpa only [ite_eq_left (show (i - 1) % 2 = 0 by omega)] using h (i - 1)
    · simpa only [ite_eq_right even] using h i
    · simpa only [ite_eq_left (show (i + 1) % 2 = 0 by omega)] using h (i + 1)
    · simpa only [ite_eq_right (show (i + 2) % 2 ≠ 0 by omega)] using h (i + 2)

private theorem orbit_checker_mono {P Q : ℤ → Bool} (h : CheckerLE P Q) (t : ℕ) :
    CheckerLE (orbit (step phi lineMove) t P) (orbit (step phi lineMove) t Q) := by
  induction t with
  | zero => exact h
  | succ t ih => exact step_checker_mono ih

private theorem evaluations_checker_mono (P : ℤ → Letter 2) (u v : Inputs 2) (t : ℕ)
    (h : CheckerLE (evaluate P u) (evaluate P v)) :
    CheckerLE (evaluate (orbit (lineStep phi) t P) u)
      (evaluate (orbit (lineStep phi) t P) v) := by
  rw [evaluate_orbit, evaluate_orbit]
  exact orbit_checker_mono h t

private theorem checker_of_single_site {P Q : ℤ → Bool} (x : ℤ)
    (agree : ∀ i, i ≠ x → P i = Q i)
    (atSite : if x % 2 = 0 then P x ≤ Q x else Q x ≤ P x) : CheckerLE P Q := by
  intro i
  by_cases hi : i = x
  · simpa only [hi] using atSite
  · rw [agree i hi]
    split <;> exact Bool.le_refl _

private theorem simple_initial_eval_order {P : ℤ → Letter 2} (alphabet : SeedAlphabet P)
    (simple : Simple P) :
    (∀ y, CheckerLE (evaluate P (assignment false y)) (evaluate P (assignment true y))) ∨
    (∀ y, CheckerLE (evaluate P (assignment true y)) (evaluate P (assignment false y))) := by
  obtain ⟨x, atX, uniqueX⟩ := simple 0
  have agree (i : ℤ) (hi : i ≠ x) (y : Bool) :
      evaluate P (assignment false y) i = evaluate P (assignment true y) i := by
    change P i (assignment false y) = P i (assignment true y)
    rcases alphabet i with h | h | ⟨j, h⟩
    · rw [h]
      rfl
    · rw [h]
      rfl
    · fin_cases j
      · exact (hi (uniqueX i h)).elim
      · rw [h]
        rfl
  by_cases even : x % 2 = 0
  · left
    intro y
    apply checker_of_single_site x (fun i hi => agree i hi y)
    simp only [ite_eq_left even, evaluate, atX]
    exact (by decide : false ≤ true)
  · right
    intro y
    apply checker_of_single_site x (fun i hi => (agree i hi y).symm)
    simp only [ite_eq_right even, evaluate, atX]
    exact (by decide : false ≤ true)

def xorLetter : Letter 2 := fun u => Bool.xor (u 0) (u 1)

theorem simple_line_omits_xor {P : ℤ → Letter 2} (alphabet : SeedAlphabet P)
    (simple : Simple P) (i : ℤ) (t : ℕ) :
    orbit (lineStep phi) t P i ≠ xorLetter := by
  intro realized
  rcases simple_initial_eval_order alphabet simple with h | h <;>
    by_cases even : i % 2 = 0
  · have bad := evaluations_checker_mono P _ _ t (h true) i
    simp only [ite_eq_left even, evaluate, realized] at bad
    exact (by decide : ¬ true ≤ false) bad
  · have bad := evaluations_checker_mono P _ _ t (h false) i
    simp only [ite_eq_right even, evaluate, realized] at bad
    exact (by decide : ¬ true ≤ false) bad
  · have bad := evaluations_checker_mono P _ _ t (h false) i
    simp only [ite_eq_left even, evaluate, realized] at bad
    exact (by decide : ¬ true ≤ false) bad
  · have bad := evaluations_checker_mono P _ _ t (h true) i
    simp only [ite_eq_right even, evaluate, realized] at bad
    exact (by decide : ¬ true ≤ false) bad

private theorem simple_line_incomplete {P : ℤ → Letter 2} (alphabet : SeedAlphabet P)
    (simple : Simple P) : ¬ Complete (lineStep phi) P := by
  intro complete
  obtain ⟨i, t, h⟩ := (complete_iff _ _).1 complete xorLetter
  exact simple_line_omits_xor alphabet simple i t h

private theorem phi_not_strongly_universal : ¬ StronglyUniversal phi 2 := by
  rintro ⟨P, ⟨alphabet, _⟩, simple, complete⟩
  exact simple_line_incomplete alphabet simple complete

def periodic {N k : ℕ} (P : ZMod N → Letter k) (i : ℤ) : Letter k :=
  P (i : ZMod N)

private theorem periodic_step {N n k : ℕ} (φ : LocalRule n) (P : ZMod N → Letter k) :
    lineStep φ (periodic P) = periodic (ringStep φ P) := by
  funext i u
  change φ (fun j => P ((i + offset j : ℤ) : ZMod N) u) =
    φ (fun j => P ((i : ZMod N) + (offset j : ZMod N)) u)
  simp only [Int.cast_add]

private theorem periodic_orbit {N n k : ℕ} (φ : LocalRule n) (P : ZMod N → Letter k) (t : ℕ) :
    orbit (lineStep φ) t (periodic P) = periodic (orbit (ringStep φ) t P) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change lineStep φ (orbit (lineStep φ) t (periodic P)) =
      periodic (ringStep φ (orbit (ringStep φ) t P))
    rw [ih, periodic_step]

private theorem offset_four_bounds (j : Fin 4) : -1 ≤ offset j ∧ offset j ≤ 2 := by
  fin_cases j <;> decide

private theorem light_cone {k : ℕ} (φ : LocalRule 4) (P Q : ℤ → Letter k) (t : ℕ) (i : ℤ)
    (agree : ∀ j : ℤ, i - (t : ℤ) ≤ j → j ≤ i + 2 * (t : ℤ) → P j = Q j) :
    orbit (lineStep φ) t P i = orbit (lineStep φ) t Q i := by
  induction t generalizing i with
  | zero => exact agree i (by simp) (by simp)
  | succ t ih =>
    funext u
    change φ (fun j => orbit (lineStep φ) t P (i + offset j) u) =
      φ (fun j => orbit (lineStep φ) t Q (i + offset j) u)
    apply congrArg φ
    funext j
    have ⟨left, right⟩ := offset_four_bounds j
    apply congrFun (ih (i + offset j) ?_) u
    intro p lower upper
    apply agree p <;> omega

-- Four copies of the ring word, starting at -5 and with the same phase at 0.
def lineWord : Fin 20 → Letter 2 := fun j => ringSeed (j.val : ZMod 5)

def lineSeed : ℤ → Letter 2 := wordOnLine lineWord false (-5)

private theorem line_seed_eq (i : ℤ) :
    lineSeed i = if -5 ≤ i ∧ i ≤ 14 then periodic ringSeed i else constant false := by
  have inInterval : (0 ≤ i - (-5) ∧ i - (-5) < ((20 : ℕ) : ℤ)) ↔ -5 ≤ i ∧ i ≤ 14 := by omega
  by_cases hi : -5 ≤ i ∧ i ≤ 14
  · have h := inInterval.mpr hi
    simp only [lineSeed, wordOnLine, dite_eq_left h, ite_eq_left hi]
    have castPhase : (((i - (-5)).toNat : ℕ) : ZMod 5) = (i : ZMod 5) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h.1, Int.cast_sub]
      rw [show ((-5 : ℤ) : ZMod 5) = 0 by rfl, sub_zero]
    exact congrArg ringSeed castPhase
  · simp only [lineSeed, wordOnLine, dite_eq_right (mt inInterval.mp hi), ite_eq_right hi]

private theorem line_seed_zero_background : FiniteBackground false lineSeed := by
  apply (Set.finite_Icc (-5 : ℤ) 14).subset
  intro i hi
  change lineSeed i ≠ constant false at hi
  by_contra outside
  change ¬ (-5 ≤ i ∧ i ≤ 14) at outside
  exact hi (by rw [line_seed_eq, ite_eq_right outside])

private theorem line_seed_is_seed : LineSeed lineSeed := by
  refine ⟨?_, false, line_seed_zero_background⟩
  intro i
  rw [line_seed_eq]
  split
  · exact ring_seed_alphabet (i : ZMod 5)
  · exact Or.inl rfl

private theorem line_seed_matches_ring (t : Fin 6) (i : ZMod 5) :
    orbit (lineStep phi) t.val lineSeed (i.val : ℤ) = orbit (ringStep phi) t.val ringSeed i := by
  have ht := t.isLt
  have hi := ZMod.val_lt i
  calc
    _ = orbit (lineStep phi) t.val (periodic ringSeed) (i.val : ℤ) := by
      apply light_cone
      intro j hjlo hjhi
      rw [line_seed_eq, ite_eq_left (show -5 ≤ j ∧ j ≤ 14 by omega)]
    _ = orbit (ringStep phi) t.val ringSeed i := by
      rw [periodic_orbit]
      change orbit (ringStep phi) t.val ringSeed ((i.val : ℤ) : ZMod 5) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem seeds_complete :
    Complete (ringStep phi) ringSeed ∧ Complete (lineStep phi) lineSeed := by
  have ring_orbit_table (t : Fin 6) (i : ZMod 5) :
      orbit (ringStep phi) t.val ringSeed i = decodeMask (ringTable t i) := by
    funext u
    obtain ⟨x, y, rfl⟩ := assignment_surjective u
    fin_cases t <;> fin_cases i <;> cases x <;> cases y <;> rfl
  constructor
  · apply (complete_iff _ _).2
    intro f
    obtain ⟨t, i, hf⟩ := every_letter_in_ring_table f
    exact ⟨i, t.val, (ring_orbit_table t i).trans hf⟩
  · apply (complete_iff _ _).2
    intro f
    obtain ⟨t, i, hf⟩ := every_letter_in_ring_table f
    exact ⟨(i.val : ℤ), t.val, (line_seed_matches_ring t i).trans ((ring_orbit_table t i).trans hf)⟩

-- Question 5.9.
theorem question_5_9 :
    ∃ (n : ℕ) (φ : LocalRule n) (k : ℕ),
      0 < n ∧ 0 < k ∧ StronglyCyclicUniversal φ k ∧ ¬ StronglyUniversal φ k := by
  refine ⟨4, phi, 2, by decide, by decide, ?_, phi_not_strongly_universal⟩
  exact ⟨5, ringSeed, ⟨by decide, ring_seed_alphabet⟩, ring_seed_simple, seeds_complete.1⟩

-- Question 5.6.
theorem question_5_6 :
    ∃ (n : ℕ) (φ : LocalRule n) (k : ℕ),
      0 < n ∧ 0 < k ∧ Universal φ k ∧ ¬ StronglyUniversal φ k :=
  ⟨4, phi, 2, by decide, by decide, ⟨lineSeed, line_seed_is_seed, seeds_complete.2⟩,
    phi_not_strongly_universal⟩

end D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
