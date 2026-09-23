/- GID: D5/S3/Observer/Budget/CaoChenMillerEggDropRefutation
   generality: I
   mirror-B: D5/B/S3/Observer/Budget/CaoChenMillerEggDropRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: A padded-transcript injection refutes the Cao-Chen-Miller egg-drop bound. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Budget.CaoChenMillerEggDropRefutation

open scoped BigOperators

/-- Hidden critical points, with `Fin (N i)` representing the paper's integer
coordinates `1, ..., N_i` by the zero-based value `x_i - 1`. -/
abbrev Point {d : Nat} (N : Fin d -> Nat) := forall i, Fin (N i)

/-- Query coordinates range over the physical positions `0, ..., N_i`. Real
drop positions have the same outcomes as their coordinatewise floors, so this
discrete carrier also represents every comparison against an integer hidden point. -/
abbrev Query {d : Nat} (N : Fin d -> Nat) := forall i, Fin (N i + 1)

/-- A query value `q_i` encodes the physical coordinate `a_i`, while a hidden
value `h_i` encodes `x_i - 1`. Thus `a_i < x_i` is exactly `q_i <= h_i`.
The value `1` means intact and `0` means broken. -/
def dropOutcome {d : Nat} {N : Fin d -> Nat} (query : Query N) (hidden : Point N) : Fin 2 :=
  if forall i, (query i).val <= (hidden i).val then 1 else 0

/-- A deterministic adaptive strategy indexed by available eggs and remaining
drops. Each drop uses the `Query N` carrier. A terminal leaf may occur under
unused drop budget. On a broken outcome one egg is lost; on an intact outcome
the egg count is preserved. -/
inductive EggStrategy {d : Nat} (N : Fin d -> Nat) : Nat -> Nat -> Type
  | stop {eggs drops : Nat} (guess : Point N) : EggStrategy N eggs drops
  | drop {eggs drops : Nat} (query : Query N)
      (broken : EggStrategy N eggs drops)
      (intact : EggStrategy N (eggs + 1) drops) :
      EggStrategy N (eggs + 1) (drops + 1)

/-- The terminal guess reached by executing the strategy on a hidden point. -/
def prediction {d : Nat} {N : Fin d -> Nat} :
    {eggs drops : Nat} -> EggStrategy N eggs drops -> Point N -> Point N
  | _, _, .stop guess, _ => guess
  | _, _, .drop query broken intact, hidden =>
      if dropOutcome query hidden = 0 then
        prediction broken hidden
      else
        prediction intact hidden

/-- A terminal transcript padded with zeroes to the full drop budget. A leaf can
have unused budget, and every unused coordinate receives the same fixed symbol. -/
def paddedTranscript {d : Nat} {N : Fin d -> Nat} :
    {eggs drops : Nat} -> EggStrategy N eggs drops -> Point N -> Fin drops -> Fin 2
  | _, _, .stop _, _ => fun _ => 0
  | _, _, .drop query broken intact, hidden =>
      fun coordinate =>
        Fin.cases (dropOutcome query hidden)
          (fun tail =>
            if dropOutcome query hidden = 0 then
              paddedTranscript broken hidden tail
            else
              paddedTranscript intact hidden tail)
          coordinate

/-- Exact worst-case recovery by the terminal guess. -/
def Correct {d : Nat} {N : Fin d -> Nat} {eggs drops : Nat}
    (strategy : EggStrategy N eggs drops) : Prop :=
  forall hidden, prediction strategy hidden = hidden

/-- The conjectured ceiling, expressed literally using real `rpow` and natural ceiling. -/
noncomputable def paperBound (d k : Nat) (N : Fin d -> Nat) : Nat :=
  Nat.ceil
    (((k - d + 1 : Nat) : Real) *
      Real.rpow (∑ i, (N i : Real))
        (((k - d + 1 : Nat) : Real)⁻¹))

/-- The universal assertion, weakened from the paper's named strategy to the
existence of any adaptive strategy obeying the same query and egg semantics. -/
def claim : Prop :=
  forall (d k : Nat) (N : Fin d -> Nat),
    1 <= d -> d <= k -> (forall i, 0 < N i) ->
      exists strategy : EggStrategy N k (paperBound d k N), Correct strategy

/-- Cao--Chen--Miller Conjecture 1 is false at `d = 4`, `k = 5`, and
`N = (5, 5, 5, 5)`. -/
theorem result : Not claim := by
  intro conjecture
  let sides : Fin 4 -> Nat := fun _ => 5
  have bound_eq_nine : paperBound 4 5 sides = 9 := by
    rw [paperBound]
    apply (Nat.ceil_eq_iff (by decide)).2
    norm_num [sides]
    rw [← Real.sqrt_eq_rpow]
    have square_root : (Real.sqrt 20) ^ 2 = 20 := by norm_num
    have root_nonnegative : 0 <= Real.sqrt 20 := Real.sqrt_nonneg 20
    constructor <;> nlinarith
  have alleged :
      exists strategy : EggStrategy sides 5 9, Correct strategy := by
    have instantiated :=
      conjecture 4 5 sides (by decide) (by decide) (by intro; decide)
    rw [bound_eq_nine] at instantiated
    exact instantiated
  let strategy := alleged.choose
  have correct := alleged.choose_spec
  have run_determined_by_transcript :
      forall {eggs drops : Nat} (strategy : EggStrategy sides eggs drops)
        {left right : Point sides},
        paddedTranscript strategy left = paddedTranscript strategy right ->
          prediction strategy left = prediction strategy right := by
    intro eggs drops strategy
    induction strategy with
    | stop guess =>
        intro left right same
        rfl
    | @drop eggs drops query broken intact broken_ih intact_ih =>
        intro left right same
        have same_head : dropOutcome query left = dropOutcome query right := by
          simpa only [paddedTranscript, Fin.cases_zero] using congrFun same 0
        by_cases left_broken : dropOutcome query left = 0
        case pos =>
          have right_broken : dropOutcome query right = 0 := by
            rw [same_head.symm]
            exact left_broken
          simp only [prediction, left_broken, right_broken, if_pos]
          apply broken_ih
          funext coordinate
          simpa only [paddedTranscript, Fin.cases_succ, left_broken,
            right_broken, if_pos] using congrFun same coordinate.succ
        case neg =>
          have right_broken : Not (dropOutcome query right = 0) := by
            intro right_zero
            apply left_broken
            rw [same_head]
            exact right_zero
          simp only [prediction, left_broken, right_broken, if_false]
          apply intact_ih
          funext coordinate
          simpa only [paddedTranscript, Fin.cases_succ, left_broken,
            right_broken, if_false] using congrFun same coordinate.succ
  have transcript_injective : Function.Injective (paddedTranscript strategy) := by
    intro left right same
    have same_prediction := run_determined_by_transcript strategy same
    exact (correct left).symm.trans (same_prediction.trans (correct right))
  have cardinal_bound :
      Fintype.card (Point sides) <= Fintype.card (Fin 9 -> Fin 2) :=
    Fintype.card_le_of_injective (paddedTranscript strategy) transcript_injective
  norm_num [Point, sides] at cardinal_bound

#print axioms result

end D5.S3.Observer.Budget.CaoChenMillerEggDropRefutation
