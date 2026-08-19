/- GID: D5/S0/Tower/DBonacciGeneral/ChampionLimit
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/ChampionLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Champion value tends to one third; slack equals deficit over base less one. -/

import D5.S0.Tower.DBonacciGeneral.ChampionValue
import D5.S0.Tower.DBonacci.PerronRoot

/- Library-search audit trail (2026-08-18):
   * Repository search found `championValue`, the Perron-root bounds, and
     `dbonacciPerronRoot_tendsto_two`, but no statement about the limit of the
     champion value or a closed form for the finite-depth slack.
   * Pinned Mathlib supplies `ContinuousAt.div`, `Filter.Tendsto.comp`, and
     `Tendsto.sub`; the composition below uses only those. -/

namespace D5.S0.Tower.DBonacciGeneral.ChampionLimit

open Filter Topology
open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.DBonacci.PerronRoot

/-- The predecessor phase of the champion orbit, as a function of the base. -/
noncomputable def championMidCoordinate (beta : Real) : Real := 1 / (beta ^ 2 - 1)

/-- The slack that powers the finite-depth witness has a closed form: it is the
Perron deficit divided by the base less one.  Positivity is therefore visibly
equivalent to the base lying below two. -/
theorem champion_slack_eq (beta : Real) (hone : 1 < beta) (hlt : beta < 2) :
    championMidCoordinate beta - championValue beta = (2 - beta) / (beta - 1) := by
  have hsub : beta - 1 ≠ 0 := by intro h; linarith [h]
  have hden : beta ^ 2 - 1 ≠ 0 := by
    intro h
    have : (beta - 1) * (beta + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp this with h1 | h2
    · exact hsub h1
    · linarith
  simp only [championMidCoordinate, championValue]
  field_simp
  ring

theorem champion_slack_pos (beta : Real) (hone : 1 < beta) (hlt : beta < 2) :
    0 < championMidCoordinate beta - championValue beta := by
  rw [champion_slack_eq beta hone hlt]
  apply div_pos <;> linarith

/-- The champion value is continuous at the limiting base. -/
theorem championValue_continuousAt_two : ContinuousAt championValue 2 := by
  change ContinuousAt (fun b : Real => (b ^ 2 - b - 1) / (b ^ 2 - 1)) 2
  refine ContinuousAt.div ?_ ?_ (by norm_num)
  · fun_prop
  · fun_prop

theorem championValue_two : championValue 2 = 1 / 3 := by
  simp only [championValue]; norm_num

/-- The champion value of the order-`d` tower tends to one third. -/
theorem championValue_tendsto_one_third :
    Tendsto (fun d : Nat => championValue (dbonacciPerronRoot d)) atTop (nhds (1 / 3)) := by
  rw [← championValue_two]
  exact championValue_continuousAt_two.tendsto.comp dbonacciPerronRoot_tendsto_two

/-- The predecessor coordinate tends to the same value, which is why the slack
vanishes in the limit even though it is positive at every order. -/
theorem championMidCoordinate_continuousAt_two :
    ContinuousAt championMidCoordinate 2 := by
  change ContinuousAt (fun b : Real => 1 / (b ^ 2 - 1)) 2
  refine ContinuousAt.div ?_ ?_ (by norm_num)
  · fun_prop
  · fun_prop

theorem championMidCoordinate_two : championMidCoordinate 2 = 1 / 3 := by
  simp only [championMidCoordinate]; norm_num

theorem championMidCoordinate_tendsto_one_third :
    Tendsto (fun d : Nat => championMidCoordinate (dbonacciPerronRoot d))
      atTop (nhds (1 / 3)) := by
  rw [← championMidCoordinate_two]
  exact championMidCoordinate_continuousAt_two.tendsto.comp dbonacciPerronRoot_tendsto_two

/-- The slack is positive at every order above two yet tends to zero.  Both halves
are needed: positivity is what makes the finite-depth witness exist, and the
limit is what stops it from being uniform in the order. -/
theorem champion_slack_tendsto_zero :
    Tendsto (fun d : Nat =>
        championMidCoordinate (dbonacciPerronRoot d)
          - championValue (dbonacciPerronRoot d)) atTop (nhds 0) := by
  have h := championMidCoordinate_tendsto_one_third.sub championValue_tendsto_one_third
  simpa using h

theorem champion_slack_pos_and_tendsto_zero :
    (∀ d : Nat, 2 ≤ d →
        0 < championMidCoordinate (dbonacciPerronRoot d)
          - championValue (dbonacciPerronRoot d)) ∧
      Tendsto (fun d : Nat =>
          championMidCoordinate (dbonacciPerronRoot d)
            - championValue (dbonacciPerronRoot d)) atTop (nhds 0) :=
  ⟨fun d hd => champion_slack_pos _ (one_lt_dbonacciPerronRoot d hd)
      (dbonacciPerronRoot_lt_two d hd),
    champion_slack_tendsto_zero⟩

end D5.S0.Tower.DBonacciGeneral.ChampionLimit
