import Init

/-! Independent native-signature regression inputs. -/
namespace LeanInformationAudit.Tests.SearchReduction.NativeSignatures

inductive Nested where
  | node : List Nested → Nested

theorem nested_impossible (x : Nested) (h : False) : False := h

theorem deep_conjunction : True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True)))))))))))))))))))))))))))))))))))))))) :=
  And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (True.intro))))))))))))))))))))))))))))))))))))))))

end LeanInformationAudit.Tests.SearchReduction.NativeSignatures
