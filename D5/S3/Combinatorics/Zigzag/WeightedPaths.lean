/- GID: D5/S3/Combinatorics/Zigzag/WeightedPaths
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/WeightedPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Laurent]
   utility: none
   digest: The labelled five-state transfer satisfies a finite Laurent recurrence. -/

import D5.S3.Combinatorics.Zigzag.PathData
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

open scoped LaurentPolynomial

abbrev Laurent := LaurentPolynomial Nat

/-- The Laurent monomial recording a change of imbalance at `+1`. -/
noncomputable def z (q : Int) : Laurent := LaurentPolynomial.T q

/-- Backward terminal weights before an interior transition is taken. -/
noncomputable def evenTerminalWeight (s : State) : Laurent :=
  if s = State.A then 1 else if s = State.D then z (-1) else 0

/-- One backward application of the explicit positive labelled table.  Each
summand is one distinct labelled transition, including coincident weights. -/
noncomputable def advance (v : State -> Laurent) : State -> Laurent
  | ⟨0, _⟩ => z 1 * v State.A + z 2 * v State.D + v State.E + z (-1) * v State.I
  | ⟨1, _⟩ => v State.A + z 1 * v State.D + z (-1) * v State.E + v State.H
  | ⟨2, _⟩ => z (-1) * v State.A + v State.D
  | ⟨3, _⟩ => z (-1) * v State.D
  | ⟨4, _⟩ => v State.A

/-- Terminal weights after `m` labelled interior retirement steps. -/
noncomputable def terminalWeight : Nat -> State -> Laurent
  | 0 => evenTerminalWeight
  | m + 1 => advance (terminalWeight m)

/-- The two positive-sector starts, with their distinct class-two labels. -/
noncomputable def pathPolynomial (m : Nat) : Laurent :=
  terminalWeight m State.A + z 1 * terminalWeight m State.D

private theorem terminal_vector_seed :
    advance (advance evenTerminalWeight) = fun s =>
      z 1 * 2 * advance evenTerminalWeight s + z (-1) * 3 * evenTerminalWeight s := by
  have hzadd (p q : Int) : z p * z q = z (p + q) := by
    exact (LaurentPolynomial.T_add p q).symm
  have hzzero : z 0 = (1 : Laurent) := by simp [z]
  have hzsq (q : Int) : z q ^ 2 = z (q + q) := by
    simpa [pow_two] using hzadd q q
  funext s
  fin_cases s <;>
    simp [advance, evenTerminalWeight, State.A, State.D, State.E, State.H, State.I] <;>
    ring_nf <;>
    simp [hzadd, hzzero, hzsq] <;>
    norm_num <;>
    ring

/-- The entire five-state terminal vector satisfies the scalar order-two
recurrence, not merely its final projection. -/
theorem terminalWeight_recurrence (m : Nat) :
    terminalWeight (m + 2) = fun s =>
      z 1 * 2 * terminalWeight (m + 1) s + z (-1) * 3 * terminalWeight m s := by
  induction m with
  | zero => simpa [terminalWeight] using terminal_vector_seed
  | succ m ih =>
      calc
        terminalWeight (Nat.succ m + 2) = advance (terminalWeight (m + 2)) := by
          rw [show Nat.succ m + 2 = (m + 2) + 1 by omega, terminalWeight]
        _ = advance (fun s =>
            (z 1 * 2) * terminalWeight (m + 1) s +
              (z (-1) * 3) * terminalWeight m s) := by rw [ih]
        _ = fun s =>
            (z 1 * 2) * terminalWeight (Nat.succ m + 1) s +
              (z (-1) * 3) * terminalWeight (Nat.succ m) s := by
          funext s
          fin_cases s <;> simp [advance, terminalWeight] <;> ring

/-- The source-derived finite Laurent scalar recurrence. -/
theorem pathPolynomial_recurrence (m : Nat) :
    pathPolynomial (m + 2) =
      2 * z 1 * pathPolynomial (m + 1) + 3 * z (-1) * pathPolynomial m := by
  simp only [pathPolynomial, terminalWeight_recurrence]
  ring

/-- The generating polynomial of actual positive even tails. -/
noncomputable def actualEvenTailPolynomial (m : Nat) (s : State) : Laurent :=
  ∑ p : EvenTail .positive m s, z (evenTailCharge p)

/-- The transfer vector counts the actual positive labelled even tails by charge. -/
theorem actualEvenTailPolynomial_eq_terminalWeight (m : Nat) (s : State) :
    actualEvenTailPolynomial m s = terminalWeight m s := by
  induction m generalizing s with
  | zero =>
      fin_cases s
      · change (∑ _ : Fin 1, z 0) = 1
        simp [Fin.sum_univ_succ, z]
      · change (∑ _ : Fin 1, z (-1)) = z (-1)
        simp [Fin.sum_univ_succ]
      · change (∑ _ : Fin 0,
          z (evenTailCharge (h := .positive) (m := 0) (s := State.E) _)) = 0
        simp
      · change (∑ _ : Fin 0,
          z (evenTailCharge (h := .positive) (m := 0) (s := State.H) _)) = 0
        simp
      · change (∑ _ : Fin 0,
          z (evenTailCharge (h := .positive) (m := 0) (s := State.I) _)) = 0
        simp
  | succ m ih =>
      have hzadd (p q : Int) : z p * z q = z (p + q) := by
        exact (LaurentPolynomial.T_add p q).symm
      have hsplit : actualEvenTailPolynomial (m + 1) s =
          ∑ i : StepIndex s,
            z (stepValue (h := .positive) i).charge *
              actualEvenTailPolynomial m (stepValue (h := .positive) i).target := by
        letI sigmaInst : Fintype
            (Sigma fun i : StepIndex s =>
              EvenTail .positive m (stepTarget i)) := Sigma.instFintype
        let e : EvenTail .positive (m + 1) s ≃
            (Sigma fun i : StepIndex s =>
              EvenTail .positive m (stepTarget i)) :=
          (Equiv.refl _).trans (Equiv.psigmaEquivSigma _)
        rw [actualEvenTailPolynomial]
        rw [Fintype.sum_equiv e (fun p => z (evenTailCharge p))
          (fun p => z (evenTailCharge (e.symm p))) (fun _ => rfl)]
        rw [Fintype.sum_sigma]
        apply Fintype.sum_congr
        intro i
        change (∑ p, z ((stepValue (h := .positive) i).charge + evenTailCharge p)) =
          z (stepValue (h := .positive) i).charge * (∑ p, z (evenTailCharge p))
        simp only [hzadd, Finset.mul_sum]
        rfl
      rw [hsplit]
      simp_rw [ih]
      have hstep (v : State -> Laurent) :
          (fun s => ∑ i : StepIndex s,
            z (stepValue (h := .positive) i).charge *
              v (stepValue (h := .positive) i).target) = advance v := by
        funext s
        fin_cases s
        · change (∑ i : Fin 4, z (stepValue (h := .positive) (s := State.A) i).charge *
              v (stepValue (h := .positive) (s := State.A) i).target) = _
          simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance, State.A,
            State.D, State.E, State.H, State.I, Fin.sum_univ_succ, z, add_assoc]
        · change (∑ i : Fin 4, z (stepValue (h := .positive) (s := State.D) i).charge *
              v (stepValue (h := .positive) (s := State.D) i).target) = _
          simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance, State.A,
            State.D, State.E, State.H, State.I, Fin.sum_univ_succ, z, add_assoc]
        · change (∑ i : Fin 2, z (stepValue (h := .positive) (s := State.E) i).charge *
              v (stepValue (h := .positive) (s := State.E) i).target) = _
          simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance, State.A,
            State.D, State.E, State.H, State.I, Fin.sum_univ_succ, z]
        · change (∑ i : Fin 1, z (stepValue (h := .positive) (s := State.H) i).charge *
              v (stepValue (h := .positive) (s := State.H) i).target) = _
          simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance, State.A,
            State.D, State.E, State.H, State.I, Fin.sum_univ_succ, z]
        · change (∑ i : Fin 1, z (stepValue (h := .positive) (s := State.I) i).charge *
              v (stepValue (h := .positive) (s := State.I) i).target) = _
          simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance, State.A,
            State.D, State.E, State.H, State.I, Fin.sum_univ_succ, z]
      exact congrFun (hstep (terminalWeight m)) s

/-- The charge-generating polynomial of complete positive even paths. -/
noncomputable def actualEvenPathPolynomial (m : Nat) : Laurent :=
  ∑ p : EvenPath .positive m, z (evenPathCharge p)

theorem actualEvenPathPolynomial_eq_pathPolynomial (m : Nat) :
    actualEvenPathPolynomial m = pathPolynomial m := by
  have hzadd (p q : Int) : z p * z q = z (p + q) := by
    exact (LaurentPolynomial.T_add p q).symm
  have hsplit : actualEvenPathPolynomial m =
      ∑ i : StartIndex .positive,
        z (startValue i).charge *
          actualEvenTailPolynomial m (startTarget i) := by
    letI sigmaInst : Fintype
        (Sigma fun i : StartIndex .positive =>
          EvenTail .positive m (startTarget i)) := Sigma.instFintype
    let e : EvenPath .positive m ≃
        (Sigma fun i : StartIndex .positive =>
          EvenTail .positive m (startTarget i)) :=
      (Equiv.refl _).trans (Equiv.psigmaEquivSigma _)
    rw [actualEvenPathPolynomial]
    rw [Fintype.sum_equiv e (fun p => z (evenPathCharge p))
      (fun p => z (evenPathCharge (e.symm p))) (fun _ => rfl)]
    rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro i
    change (∑ p, z ((startValue i).charge + evenTailCharge p)) =
      z (startValue i).charge * (∑ p, z (evenTailCharge p))
    simp only [hzadd, Finset.mul_sum]
  rw [hsplit]
  change (∑ i : Fin 2,
      z (startValue (h := .positive) i).charge *
        actualEvenTailPolynomial m (startTarget i)) = _
  simp [startValue, starts, startTarget, startTargets,
    actualEvenTailPolynomial_eq_terminalWeight,
    pathPolynomial, Fin.sum_univ_succ, z, add_assoc]

/-- The coefficient bridge for actual positive labelled even paths. -/
theorem evenPath_zero_charge_card (m : Nat) :
    Fintype.card {p : EvenPath .positive m // evenPathCharge p = 0} =
      (pathPolynomial m).coeff 0 := by
  rw [← actualEvenPathPolynomial_eq_pathPolynomial]
  classical
  have hcoeff :
      (∑ p : EvenPath .positive m, z (evenPathCharge p)).coeff 0 =
        Fintype.card {p : EvenPath .positive m // evenPathCharge p = 0} := by
    rw [Fintype.card_subtype]
    simp [z, LaurentPolynomial.T_apply]
  exact hcoeff.symm

/-- The generating polynomial of actual positive odd tails. -/
noncomputable def actualOddTailPolynomial (m : Nat) (s : State) : Laurent :=
  ∑ p : OddTail .positive m s, z (oddTailCharge p)

/-- The positive odd singleton shifts every path charge by one. -/
theorem actualOddTailPolynomial_eq_shift (m : Nat) (s : State) :
    actualOddTailPolynomial m s = z 1 * terminalWeight m s := by
  induction m generalizing s with
  | zero =>
      fin_cases s
      · change (∑ _ : Fin 1, z 1) = z 1 * 1
        simp
      · change (∑ _ : Fin 1, z 0) = z 1 * z (-1)
        rw [show z 1 * z (-1) = z (1 + -1) by
          exact (LaurentPolynomial.T_add 1 (-1)).symm]
        simp [z]
      · haveI : IsEmpty (OddTail .positive 0 ⟨2, by omega⟩) := by
          constructor
          intro x
          change Fin 0 at x
          exact Fin.elim0 x
        rw [actualOddTailPolynomial, Finset.sum_of_isEmpty]
        simp [terminalWeight, evenTerminalWeight, State.A, State.D]
      · haveI : IsEmpty (OddTail .positive 0 ⟨3, by omega⟩) := by
          constructor
          intro x
          change Fin 0 at x
          exact Fin.elim0 x
        rw [actualOddTailPolynomial, Finset.sum_of_isEmpty]
        simp [terminalWeight, evenTerminalWeight, State.A, State.D]
      · haveI : IsEmpty (OddTail .positive 0 ⟨4, by omega⟩) := by
          constructor
          intro x
          change Fin 0 at x
          exact Fin.elim0 x
        rw [actualOddTailPolynomial, Finset.sum_of_isEmpty]
        simp [terminalWeight, evenTerminalWeight, State.A, State.D]
  | succ m ih =>
      have hzadd (p q : Int) : z p * z q = z (p + q) := by
        exact (LaurentPolynomial.T_add p q).symm
      have hsplit : actualOddTailPolynomial (m + 1) s =
          ∑ i : StepIndex s,
            z (stepValue (h := .positive) i).charge *
              actualOddTailPolynomial m (stepValue (h := .positive) i).target := by
        letI sigmaInst : Fintype
            (Sigma fun i : StepIndex s =>
              OddTail .positive m (stepTarget i)) := Sigma.instFintype
        let e : OddTail .positive (m + 1) s ≃
            (Sigma fun i : StepIndex s =>
              OddTail .positive m (stepTarget i)) :=
          (Equiv.refl _).trans (Equiv.psigmaEquivSigma _)
        rw [actualOddTailPolynomial]
        rw [Fintype.sum_equiv e (fun p => z (oddTailCharge p))
          (fun p => z (oddTailCharge (e.symm p))) (fun _ => rfl)]
        rw [Fintype.sum_sigma]
        apply Fintype.sum_congr
        intro i
        change (∑ p, z ((stepValue (h := .positive) i).charge + oddTailCharge p)) =
          z (stepValue (h := .positive) i).charge * (∑ p, z (oddTailCharge p))
        simp only [hzadd, Finset.mul_sum]
        rfl
      rw [hsplit]
      simp_rw [ih]
      calc
        (∑ i, z (stepValue (h := .positive) i).charge *
            (z 1 * terminalWeight m (stepValue (h := .positive) i).target)) =
            z 1 * (∑ i, z (stepValue (h := .positive) i).charge *
              terminalWeight m (stepValue (h := .positive) i).target) := by
          rw [Finset.mul_sum]
          apply Fintype.sum_congr
          intro i
          ring
        _ = z 1 * advance (terminalWeight m) s := by
          congr 1
          fin_cases s
          · change (∑ i : Fin 4,
              z (stepValue (h := .positive) (s := State.A) i).charge *
                terminalWeight m (stepValue (h := .positive) (s := State.A) i).target) = _
            simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance,
              State.A, State.D, State.E, State.H, State.I,
              Fin.sum_univ_succ, z, add_assoc]
          · change (∑ i : Fin 4,
              z (stepValue (h := .positive) (s := State.D) i).charge *
                terminalWeight m (stepValue (h := .positive) (s := State.D) i).target) = _
            simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance,
              State.A, State.D, State.E, State.H, State.I,
              Fin.sum_univ_succ, z, add_assoc]
          · change (∑ i : Fin 2,
              z (stepValue (h := .positive) (s := State.E) i).charge *
                terminalWeight m (stepValue (h := .positive) (s := State.E) i).target) = _
            simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance,
              State.A, State.D, State.E, State.H, State.I,
              Fin.sum_univ_succ, z]
          · change (∑ i : Fin 1,
              z (stepValue (h := .positive) (s := State.H) i).charge *
                terminalWeight m (stepValue (h := .positive) (s := State.H) i).target) = _
            simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance,
              State.A, State.D, State.E, State.H, State.I,
              Fin.sum_univ_succ, z]
          · change (∑ i : Fin 1,
              z (stepValue (h := .positive) (s := State.I) i).charge *
                terminalWeight m (stepValue (h := .positive) (s := State.I) i).target) = _
            simp [stepValue, positiveStepLabel, stepTarget, stepTargets, advance,
              State.A, State.D, State.E, State.H, State.I,
              Fin.sum_univ_succ, z]
        _ = z 1 * terminalWeight (m + 1) s := rfl

noncomputable def actualOddPathPolynomial (m : Nat) : Laurent :=
  ∑ p : OddPath .positive m, z (oddPathCharge p)

theorem actualOddPathPolynomial_eq_shift (m : Nat) :
    actualOddPathPolynomial m = z 1 * pathPolynomial m := by
  have hzadd (p q : Int) : z p * z q = z (p + q) := by
    exact (LaurentPolynomial.T_add p q).symm
  have hzzero : z 0 = (1 : Laurent) := by simp [z]
  have hsplit : actualOddPathPolynomial m =
      ∑ i : StartIndex .positive,
        z (startValue i).charge *
          actualOddTailPolynomial m (startTarget i) := by
    letI sigmaInst : Fintype
        (Sigma fun i : StartIndex .positive =>
          OddTail .positive m (startTarget i)) := Sigma.instFintype
    let e : OddPath .positive m ≃
        (Sigma fun i : StartIndex .positive =>
          OddTail .positive m (startTarget i)) :=
      (Equiv.refl _).trans (Equiv.psigmaEquivSigma _)
    rw [actualOddPathPolynomial]
    rw [Fintype.sum_equiv e (fun p => z (oddPathCharge p))
      (fun p => z (oddPathCharge (e.symm p))) (fun _ => rfl)]
    rw [Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro i
    change (∑ p, z ((startValue i).charge + oddTailCharge p)) =
      z (startValue i).charge * (∑ p, z (oddTailCharge p))
    simp only [hzadd, Finset.mul_sum]
  rw [hsplit]
  change (∑ i : Fin 2,
      z (startValue (h := .positive) i).charge *
        actualOddTailPolynomial m (startTarget i)) = _
  simp [startValue, starts, startTarget, startTargets,
    actualOddTailPolynomial_eq_shift, pathPolynomial,
    Fin.sum_univ_succ, hzzero]
  ring

/-- The coefficient bridge for actual positive labelled odd paths. -/
theorem oddPath_zero_charge_card (m : Nat) :
    Fintype.card {p : OddPath .positive m // oddPathCharge p = 0} =
      (pathPolynomial m).coeff (-1) := by
  rw [← show (z 1 * pathPolynomial m).coeff 0 =
      (pathPolynomial m).coeff (-1) by
    unfold z LaurentPolynomial.T
    rw [AddMonoidAlgebra.coeff_single_mul_apply]
    norm_num, ← actualOddPathPolynomial_eq_shift]
  classical
  have hcoeff :
      (∑ p : OddPath .positive m, z (oddPathCharge p)).coeff 0 =
        Fintype.card {p : OddPath .positive m // oddPathCharge p = 0} := by
    rw [Fintype.card_subtype]
    simp [z, LaurentPolynomial.T_apply]
  exact hcoeff.symm

end D5.S3.Combinatorics.Zigzag
