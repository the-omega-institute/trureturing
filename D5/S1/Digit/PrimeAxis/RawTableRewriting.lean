/- GID: D5/S1/Digit/PrimeAxis/RawTableRewriting
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/RawTableRewriting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A decreasing lexicographic triple terminates raw table carries and makes their legal words finite. -/

import D5.S1.Digit.PrimeAxis.ChargedTableNormalization
import D5.S1.Digit.CarryStepConfluence
import Mathlib.Order.WellFounded
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace D5.S1.Digit.PrimeAxis.RawTableRewriting

open D5.S1.Digit D5.S1.Deficit D5.S0.Conventions
open D5.S1.Digit.PrimeAxis.ChargedTableNormalization

/-- A finitely supported family of prime rows, each with finitely supported natural multiplicities. -/
abbrev RawTable := PrimeAxis →₀ RawDigits

/-- The sum of multiplicities in a row against an index weight. -/
def rowMoment (w : ℕ → ℕ) (r : RawDigits) : ℕ := r.sum fun j n => n * w j

/-- The sum of a row moment over all prime rows. -/
def moment (w : ℕ → ℕ) (t : RawTable) : ℕ := t.sum fun _ r => rowMoment w r

/-- The total Fibonacci weight of the table. -/
def V (t : RawTable) : ℕ := moment wValue t

/-- The total number of tokens in the table, counted with multiplicity. -/
def C (t : RawTable) : ℕ := moment (fun _ => 1) t

/-- The sum of token indices in the table. -/
def I (t : RawTable) : ℕ := moment id t

/-- The sum of squared token indices in the table. -/
def S (t : RawTable) : ℕ := moment (fun j => j^2) t

/-- One directed carry in one prime row, with its charge left unspecified. -/
def Reduces (t u : RawTable) : Prop := ∃ p z, TableStep t u p z

/-- The finite set of indices whose Fibonacci weights do not exceed the given value. -/
def weightIndices (v : ℕ) : Finset ℕ :=
  (Finset.range (v+1)).filter fun j => wValue j ≤ v

/-- The token count, index sum, and bounded complementary square sum. -/
def triple (v J : ℕ) (t : RawTable) : ℕ × ℕ × ℕ := (C t, I t, v*J^2-S t)

/-- The strict lexicographic order on three natural numbers. -/
def TripleLt : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

/-- A finite table sequence with one directed carry between each pair of consecutive states. -/
structure FiniteExecution where
  /-- The number of steps. -/
  length : ℕ
  /-- The tables at successive times. -/
  states : Fin (length+1) → RawTable
  /-- Every consecutive pair is related by a directed carry. -/
  legal : ∀ i : Fin length,
    Reduces (states ⟨i.val, by omega⟩) (states ⟨i.val+1, by omega⟩)

/-- The final table of a finite execution. -/
def FiniteExecution.last (e : FiniteExecution) : RawTable := e.states ⟨e.length, by omega⟩

/-- A table from which no directed table carry is possible. -/
def Irreducible (t : RawTable) : Prop := ∀ u, ¬ Reduces t u

/-- A finite or infinite sequence of actual directed table carries. -/
abbrev Execution := FiniteExecution ⊕ {f : ℕ → RawTable // ∀ n, Reduces (f n) (f (n+1))}

/-- A sequence is maximal when it is infinite or its final table allows no further carry. -/
def Maximal : Execution → Prop
  | .inl e => Irreducible e.last
  | .inr _ => True

/-- The four directed row carries, with a natural index for either variable rule. -/
inductive RuleKind where
  /-- Combine tokens at adjacent indices. -/
  | adjacent : ℕ → RuleKind
  /-- Carry two tokens at index zero. -/
  | doubleZero : RuleKind
  /-- Split two tokens at index one. -/
  | doubleOne : RuleKind
  /-- Split two tokens at an index of at least two. -/
  | doubleSucc : ℕ → RuleKind
  deriving DecidableEq

/-- A directed row carry together with its selected prime. -/
abbrev Rule := PrimeAxis × RuleKind

/-- The multiplicities required to perform a directed row carry. -/
noncomputable def lhs : RuleKind → RawDigits
  | .adjacent j => Finsupp.single j 1 + Finsupp.single (j+1) 1
  | .doubleZero => Finsupp.single 0 2
  | .doubleOne => Finsupp.single 1 2
  | .doubleSucc j => Finsupp.single (j+2) 2

/-- The multiplicities produced by a directed row carry. -/
noncomputable def rhs : RuleKind → RawDigits
  | .adjacent j => Finsupp.single (j+2) 1
  | .doubleZero => Finsupp.single 1 1
  | .doubleOne => Finsupp.single 0 1 + Finsupp.single 2 1
  | .doubleSucc j => Finsupp.single j 1 + Finsupp.single (j+3) 1

/-- The signed charge of a directed row carry. -/
def ruleCharge : RuleKind → ℤ
  | .adjacent _ => 0
  | .doubleZero => 1
  | .doubleOne => -1
  | .doubleSucc _ => 0

/-- A rule is enabled when its required multiplicities are present in the selected row. -/
def Enabled (t : RawTable) (a : Rule) : Prop := lhs a.2 ≤ t a.1

/-- Subtract the required multiplicities, add the produced ones, and preserve every other row. -/
noncomputable def applyRule (t : RawTable) (a : Rule) : RawTable :=
  t.update a.1 (t a.1 - lhs a.2 + rhs a.2)

/-- A rule word is legal when each rule is enabled after all its predecessors have been applied. -/
def LegalWord : RawTable → List Rule → Prop
  | _, [] => True
  | t, a::w => Enabled t a ∧ LegalWord (applyRule t a) w

/-- The tables with the same Fibonacci value at every prime as the given table. -/
def rowFiber (t : RawTable) : Set RawTable :=
  {u | ∀ p, rawValue (u p) = rawValue (t p)}

/-- An index required by the left side of a row carry. -/
def pivot : RuleKind → ℕ
  | .adjacent j => j
  | .doubleZero => 0
  | .doubleOne => 1
  | .doubleSucc j => j+2

/-- A finite set containing every rule enabled at the given table. -/
def ruleCandidates (t : RawTable) : Finset Rule :=
  t.support.product
    (((Finset.range (V t+1)).image RuleKind.adjacent ∪
      (Finset.range (V t+1)).image RuleKind.doubleSucc) ∪
      {RuleKind.doubleZero, RuleKind.doubleOne})

/-- The coefficientwise bound with the given prime support and uniform index and multiplicity bounds. -/
noncomputable def box (t : RawTable) : RawTable :=
  ∑ p ∈ t.support, Finsupp.single p
    (∑ j ∈ Finset.range (V t+1), Finsupp.single j (V t))

/-- The exact changes in token count, index sum, and square sum for the four directed carries. -/
def RuleEffect (t u : RawTable) : RuleKind → Prop
  | .adjacent _ => C u + 1 = C t
  | .doubleZero => C u + 1 = C t
  | .doubleOne => C u = C t ∧ I u = I t ∧ S u = S t + 2
  | .doubleSucc _ => C u = C t ∧ I u + 1 = I t

set_option maxHeartbeats 1600000 in
/-- Every directed table execution terminates. For positive initial value, the largest
admissible Fibonacci index bounds every reachable token and makes the triple
`(C, I, V * J^2 - S)` strictly decrease. Maximal executions end at the unique
rowwise canonical table, with at most one token per index and no adjacent tokens. -/
theorem table_rewriting_terminates :
    WellFounded (fun u t : RawTable => Reduces t u) ∧
    (¬ ∃ f : ℕ → RawTable, ∀ n, Reduces (f n) (f (n+1))) ∧
    WellFounded TripleLt ∧
    (∀ t : RawTable, C t ≤ V t) ∧
    (∀ t : RawTable, V t = 0 ↔ t = 0 ∧ ∀ u p z, ¬ TableStep t u p z) ∧
    (∀ t : RawTable, 0 < V t →
      ∃ J : ℕ, wValue J ≤ V t ∧
        (∀ j, wValue j ≤ V t → j ≤ J) ∧
        ∀ u charge, TablePath t u charge →
          (∀ p j, u p j ≠ 0 → wValue j ≤ V t ∧ j ≤ J) ∧
          S u ≤ V t * J^2 ∧
          ∀ v p z, TableStep u v p z →
            S v ≤ V t * J^2 ∧
            TripleLt (triple (V t) J v) (triple (V t) J u)) ∧
    (∀ t u p z, TableStep t u p z →
      ∃ a : Rule, a.1 = p ∧ Enabled t a ∧ applyRule t a = u ∧ RuleEffect t u a.2) ∧
    (∀ e : Execution, Maximal e →
      ∃ finite : FiniteExecution, e = .inl finite ∧ Irreducible finite.last) ∧
    (∀ t : RawTable, Irreducible t ↔ ∀ p, CanonicalRaw (t p)) ∧
    (∀ t u c, TablePath t u c → Irreducible u →
      (∀ p j, u p j ≤ 1) ∧ (∀ p j, u p j = 1 → u p (j+1) = 0) ∧
      u = rowNormalize t ∧
      ∀ v d, TablePath t v d → Irreducible v → v = u) := by
  sorry

set_option maxHeartbeats 1600000 in
/-- At every raw table the row-value fiber, enabled rules, and all legal finite rule words
are finite. The labelled rules describe exactly the directed table steps, including their
selected prime and signed charge. -/
theorem finite_legal_words (t : RawTable) :
    (rowFiber t).Finite ∧ {a : Rule | Enabled t a}.Finite ∧
    {w : List Rule | LegalWord t w}.Finite ∧
    (∀ u p z, TableStep t u p z ↔
      ∃ k : RuleKind, Enabled t (p,k) ∧ applyRule t (p,k) = u ∧ ruleCharge k = z) := by
  sorry

end D5.S1.Digit.PrimeAxis.RawTableRewriting
