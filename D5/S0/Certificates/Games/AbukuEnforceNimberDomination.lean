/- GID: D5/S0/Certificates/Games/AbukuEnforceNimberDomination
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/AbukuEnforceNimberDomination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/AbukuEnforceNimberDomination.claim; result=D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result; claim=D5/S0/Certificates/Games/AbukuEnforceNimberDomination.claim
   digest: Ruleset domination does not imply equality of enforce and ordinary nimbers. -/

/- result: proof_shape: bind-only; escape_witness: none.
   admission_basis: open-problem-resolution (#19251; Refuted)
   Direct frozen dependencies: none (all declarations).
   Private theorems, each proof_shape: bind-only; escape_witness: none:
     mex_eq -> nim_a, nim_enforce; outcome_a -> result;
     outcome_enforce -> result; nim_a -> result; nim_enforce -> result;
     option_decreases -> jointly_short; jointly_short -> result.
   Definitions: Short, JointlyShort, Outcome, IsOutcome, IsEnforceOutcome,
     mex, IsNimValue, IsEnforceNimValue, claim, fA, fB, GA, GE, OA, OE.
   The public result is the designated refutation result (`basis=refutes`)
   and is exempt from four-slot escape registration (CLAUDE.md §3.9).
   Problem 42 and the source definitions are recorded at
   https://github.com/the-omega-institute/trureturing/issues/19251.
   The recursions and claim use the source expressions. D5 Finset-mex owners
   do not define mex on arbitrary sets. Mathlib csInf_eq_iff supplies its
   minimum characterization; no D5 declaration is used. -/

import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Binding conventions for T. Abuku, S. Kimura, H. Kiya, U. Larsson, I. Saha, K. Suetsugu and T. Yamashita,
"Enforce and selective operators of combinatorial games", arXiv:2311.01006v2 (Int. J. Game Theory 53 (2024)
1249–1273): impartial rulesets (Definition 2), short and jointly short rulesets (Definitions 4 and 10), outcomes
(Definition 5), the enforce operator (Definition 13), ruleset domination (Definition 14), nim-values (Definition 29),
enforce nimbers (Definition 33) and Problem 42. -/

namespace D5.S0.Certificates.Games.AbukuEnforceNimberDomination

/-- Definition 4: every play sequence starting in `x`, ignoring alternation, terminates within `T` moves. -/
def Short {X : Type} (f : X → Set X) : Prop :=
  ∀ x : X, ∃ T : ℕ, ∀ s : ℕ → X, s 0 = x → ∃ i ≤ T, s (i + 1) ∉ f (s i)

/-- Definition 10: `A` and `B` are jointly short when the union option map is short. -/
def JointlyShort {X : Type} (fA fB : X → Set X) : Prop :=
  Short fun x => fA x ∪ fB x

/-- Perfect-play outcomes. -/
inductive Outcome
  | P
  | N
  deriving DecidableEq

/-- Definition 5: `O` is the perfect-play outcome of the ruleset `f`. A position is `P` exactly when every option is `N`. -/
def IsOutcome {X : Type} (f : X → Set X) (O : X → Outcome) : Prop :=
  ∀ x, O x = .P ↔ ∀ y ∈ f x, O y = .N

/-- Definition 13: the outcome of `A ⊙ B`. Before each move the opponent enforces `A` or `B`, so a position is `P` exactly when
the opponent can enforce a ruleset all of whose options are `N`. -/
def IsEnforceOutcome {X : Type} (fA fB : X → Set X) (O : X → Outcome) : Prop :=
  ∀ x, O x = .P ↔ ((∀ y ∈ fA x, O y = .N) ∨ (∀ y ∈ fB x, O y = .N))

/-- The least nonnegative integer missing from `s`. -/
noncomputable def mex (s : Set ℕ) : ℕ :=
  sInf sᶜ

/-- Definition 29: `G` is the nim-value function of `f`, `G(x) = mex {G(x') | x' ∈ f(x)}`. -/
def IsNimValue {X : Type} (f : X → Set X) (G : X → ℕ) : Prop :=
  ∀ x, G x = mex (G '' f x)

/-- Definition 33: `G` is the enforce-nimber function of `A ⊙ B`,
`G(x) = mex ({G(x') | x' ∈ fA(x)} ∩ {G(x') | x' ∈ fB(x)})`. -/
def IsEnforceNimValue {X : Type} (fA fB : X → Set X) (G : X → ℕ) : Prop :=
  ∀ x, G x = mex (G '' fA x ∩ G '' fB x)

/-- Problem 42: "If a ruleset dominates another, does it also 'nimber dominate' that ruleset? That is, does it follow that
all nimbers of the combined ruleset are the same as those of the dominating ruleset?" Here `A ⊢ B` (Definition 14) means
`O_{A ⊙ B}(x) = O_A(x)` for every `x`. -/
def claim : Prop :=
  ∀ (X : Type) (fA fB : X → Set X), JointlyShort fA fB →
    ∀ (OA OE : X → Outcome) (GA GE : X → ℕ),
      IsOutcome fA OA → IsEnforceOutcome fA fB OE → IsNimValue fA GA → IsEnforceNimValue fA fB GE →
      (∀ x, OE x = OA x) → ∀ x, GE x = GA x

end D5.S0.Certificates.Games.AbukuEnforceNimberDomination

namespace D5.S0.Certificates.Games.AbukuEnforceNimberDomination

private def fA : Fin 3 → Set (Fin 3) := ![∅, {0}, {0, 1}]
private def fB : Fin 3 → Set (Fin 3) := ![∅, {0}, {0}]
private def GA : Fin 3 → ℕ := ![0, 1, 2]
private def GE : Fin 3 → ℕ := ![0, 1, 1]
private def OA : Fin 3 → Outcome := ![.P, .N, .N]
private def OE : Fin 3 → Outcome := ![.P, .N, .N]

private theorem mex_eq (s : Set ℕ) (n : ℕ) (hn : n ∉ s)
    (hbelow : ∀ k < n, k ∈ s) : mex s = n := by
  change sInf sᶜ = n
  refine (csInf_eq_iff ⟨n, hn⟩ n).2 ⟨hn, ?_⟩
  intro k hk
  by_contra h
  exact hk (hbelow k (Nat.lt_of_not_ge h))

private theorem outcome_a : IsOutcome fA OA := by
  intro x
  fin_cases x <;> simp [fA, OA]

private theorem outcome_enforce : IsEnforceOutcome fA fB OE := by
  intro x
  fin_cases x <;> simp [fA, fB, OE]

private theorem nim_a : IsNimValue fA GA := by
  intro x
  fin_cases x
  · symm
    apply mex_eq
    · simp [fA, GA]
    · intro k hk
      simp [GA] at hk
  · symm
    apply mex_eq
    · simp [fA, GA]
    · intro k hk
      have : k = 0 := Nat.lt_one_iff.mp hk
      simp [fA, GA, this]
  · symm
    apply mex_eq
    · simp [fA, GA]
    · intro k hk
      have : k = 0 ∨ k = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hk)
      rcases this with rfl | rfl <;> simp [fA, GA]

private theorem nim_enforce : IsEnforceNimValue fA fB GE := by
  intro x
  fin_cases x
  · symm
    apply mex_eq
    · simp [fA, fB, GE]
    · intro k hk
      simp [GE] at hk
  · symm
    apply mex_eq
    · simp [fA, fB, GE]
    · intro k hk
      have : k = 0 := Nat.lt_one_iff.mp hk
      simp [fA, fB, GE, this]
  · symm
    apply mex_eq
    · simp [fA, fB, GE]
    · intro k hk
      have : k = 0 := Nat.lt_one_iff.mp hk
      simp [fA, fB, GE, this]

private theorem option_decreases (x y : Fin 3)
    (h : y ∈ fA x ∪ fB x) : y.val < x.val := by
  fin_cases x <;> fin_cases y <;> simp_all [fA, fB]

private theorem jointly_short : JointlyShort fA fB := by
  intro x
  refine ⟨x.val, ?_⟩
  intro s hs
  by_contra h
  have hstep : ∀ i ≤ x.val, (s (i + 1)).val < (s i).val := by
    intro i hi
    apply option_decreases
    by_contra hnot
    exact h ⟨i, hi, hnot⟩
  have hzero := hstep 0 (Nat.zero_le _)
  change (s 1).val < (s 0).val at hzero
  have hstart : (s 0).val = x.val := congrArg Fin.val hs
  by_cases hx0 : x.val = 0
  · omega
  have hone := hstep 1 (Nat.one_le_iff_ne_zero.mpr hx0)
  change (s 2).val < (s 1).val at hone
  by_cases hx1 : x.val = 1
  · omega
  have htwo := hstep 2 (by omega)
  change (s 3).val < (s 2).val at htwo
  have hxlt := x.isLt
  omega

theorem result : ¬ claim := by
  intro h
  have heq := h (Fin 3) fA fB jointly_short OA OE GA GE
    outcome_a outcome_enforce nim_a nim_enforce (fun _ => rfl) 2
  norm_num [GA, GE] at heq

end D5.S0.Certificates.Games.AbukuEnforceNimberDomination
