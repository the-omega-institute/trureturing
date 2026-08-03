/- GID: D5/S0/Conventions/TotalCode
   generality: G
   mirror-B: D5/B/S0/Conventions/TotalCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove that total-code-preserving transformations cannot hide object changes. -/

namespace D5.S0.Conventions.TotalCode

universe u v w

/--
The total code of an object, parameterized independently by its data, rules, and ledger.
The total-code identity criterion is semantic: here its kernel-identity reading is carried definitionally
by equality of this structure, rather than presented as a proved ontological criterion.
-/
structure TotalCode (α : Type u) (β : Type v) (γ : Type w) where
  data : α
  rules : β
  ledger : γ

/-- Two total codes with the same data, rules, and ledger are equal. -/
@[ext]
theorem TotalCode.ext {α : Type u} {β : Type v} {γ : Type w}
    {X Y : TotalCode α β γ}
    (hData : X.data = Y.data)
    (hRules : X.rules = Y.rules)
    (hLedger : X.ledger = Y.ledger) : X = Y := by
  cases X
  cases Y
  simp_all

/--
No invisible register: every transformation preserving data, rules, and ledger fixes every
object; dually, every genuine object change changes at least one of those components.
This is the C3a identity pillar and is intended for the identity use announced in 23.4.
-/
theorem no_hidden_register {α : Type u} {β : Type v} {γ : Type w} :
    (∀ f : TotalCode α β γ → TotalCode α β γ,
      (∀ X, (f X).data = X.data) →
      (∀ X, (f X).rules = X.rules) →
      (∀ X, (f X).ledger = X.ledger) →
      ∀ X, f X = X) ∧
    (∀ (f : TotalCode α β γ → TotalCode α β γ) X,
      f X ≠ X →
        (f X).data ≠ X.data ∨ (f X).rules ≠ X.rules ∨ (f X).ledger ≠ X.ledger) := by
  constructor
  · intro f hData hRules hLedger X
    exact TotalCode.ext (hData X) (hRules X) (hLedger X)
  · intro f X hChange
    by_cases hData : (f X).data = X.data
    · by_cases hRules : (f X).rules = X.rules
      · by_cases hLedger : (f X).ledger = X.ledger
        · exact False.elim (hChange (TotalCode.ext hData hRules hLedger))
        · exact Or.inr (Or.inr hLedger)
      · exact Or.inr (Or.inl hRules)
    · exact Or.inl hData

end D5.S0.Conventions.TotalCode
