import LeanInformationAuditRegTests.SearchReduction.Baseline

/-! Adversarial presentations and an induction-dependent paired fixture. -/
namespace LeanInformationAudit.Tests.SearchReduction.Candidates
open Baseline

theorem statementAlias (n : Nat) : 0 < tag n := tag_positive n

def wrap (P : Prop) : Prop := P ∧ True

theorem wrapped (n : Nat) : wrap (0 < tag n) := ⟨tag_positive n, trivial⟩

theorem unwrapped (n : Nat) : 0 < tag n := (wrapped n).1

def relocated (n : Nat) : Prop := 0 < tag n

theorem moved (n : Nat) : relocated n := tag_positive n

private theorem helper (n : Nat) : 0 < tag n := tag_positive n

theorem splitHelper (n : Nat) : 0 < tag n := helper n

theorem projection (n : Nat) : tag n % 2 = 1 := (packed n).2

theorem package (n : Nat) : 0 < tag n ∧ tag n % 2 = 1 :=
  ⟨tag_positive n, tag_odd n⟩

theorem specialized : 0 < tag 37 := tag_positive 37

def stair : Nat → Nat
  | 0 => 0
  | n + 1 => 3 + stair n

theorem intermediate (n : Nat) : stair n = n + n + n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stair, ih]; omega

-- Its simp attribute must not enter the baseline probe.
@[simp] theorem answer (n : Nat) : stair n = 3 * n := by
  have h := intermediate n
  omega

theorem content (n : Nat) : stair n = 3 * n := answer n

theorem disguisedAnswer (n : Nat) : stair n = 3 * n ∧ True := ⟨answer n, trivial⟩

theorem contentPair (n : Nat) : stair n = 3 * n ∧ 0 ≤ n :=
  ⟨answer n, Nat.zero_le n⟩

theorem iffAnswer (n : Nat) : stair n = 3 * n ↔ True := by
  constructor
  · exact fun _ => trivial
  · intro _
    have h := intermediate n
    omega

/-- A translation law has two independent parameters; the diagonal target
requires only its specialization. Its proof uses induction, not the target. -/
theorem addition (n m : Nat) : stair (n + m) = stair n + stair m := by
  induction m with
  | zero => simp [stair]
  | succ m ih =>
    change 3 + stair (n + m) = stair n + (3 + stair m)
    rw [ih]
    omega

theorem doubledContent (n : Nat) : stair (n + n) = stair n + stair n := addition n n

theorem additionWithoutOmega (n m : Nat) : stair (n + m) = stair n + stair m := by
  induction m with
  | zero => simp [stair]
  | succ m ih =>
    change 3 + stair (n + m) = stair n + (3 + stair m)
    rw [ih]
    ac_rfl

theorem doubledContentWithoutOmega (n : Nat) : stair (n + n) = stair n + stair n :=
  additionWithoutOmega n n

theorem doubledPair (n : Nat) : stair (n + n) = stair n + stair n ∧ 0 ≤ n :=
  ⟨addition n n, Nat.zero_le n⟩

theorem shiftedAnswer (n : Nat) : stair (n+n) = 3*(n+n) := answer (n+n)

theorem splitTarget (n : Nat) : stair n = 3*n ∧ stair (n+n) = 3*(n+n) :=
  ⟨answer n, shiftedAnswer n⟩

theorem changedPremise (n : Nat) (h : n = 0) : stair n = 3 * n := by
  subst n
  rfl

-- Neither a candidate simp theorem nor a candidate instance is a baseline fact.
instance : Fact (∀ n, stair n = 3 * n) := ⟨answer⟩
register_hint 10000 exact LeanInformationAudit.Tests.SearchReduction.Candidates.answer _

theorem hiddenWitness : ∃ n : Nat, n = 7 := ⟨7, rfl⟩
noncomputable def hiddenData : Nat := Classical.choose hiddenWitness

theorem hiddenTarget : hiddenData = 7 := Classical.choose_spec hiddenWitness

end LeanInformationAudit.Tests.SearchReduction.Candidates
