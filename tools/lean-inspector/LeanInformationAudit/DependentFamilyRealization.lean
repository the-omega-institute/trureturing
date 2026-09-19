import Mathlib.Data.Fintype.Defs

/- A dependent family is a separate registration interface. No finite State,
output enumeration, catalog, or naturality premise is part of this contract. -/
namespace LeanInformationAudit.DependentFamily
universe t s r o a

structure Signature where
  Θ : Type t
  State : Θ → Type s
  Role : Type r
  finiteRole : Fintype Role
  nonemptyRole : Nonempty Role
  Output : Role → Θ → Type o
  Anchor : Type a
  finiteAnchor : Fintype Anchor

structure Realization (S : Signature.{t, s, r, o, a}) where
  readout : ∀ role θ, S.State θ → S.Output role θ
  anchor : ∀ (_ : S.Anchor) θ, S.State θ

structure Arena where
  signature : Signature.{t, s, r, o, a}
  Law : Realization signature → Prop

def GlobalFamilyVariation (A : Arena.{t, s, r, o, a}) : Prop :=
  ∃ good bad, A.Law good ∧ ¬ A.Law bad

def FamilyRoleSensitivity (A : Arena.{t, s, r, o, a}) : Prop :=
  (∀ i : A.signature.Role, ∃ good bad : Realization A.signature,
    (∀ j, j ≠ i → good.readout j = bad.readout j) ∧
    good.anchor = bad.anchor ∧ (A.Law good ↔ ¬ A.Law bad)) ∧
  (∀ i : A.signature.Anchor, ∃ good bad : Realization A.signature,
    good.readout = bad.readout ∧
    (∀ j, j ≠ i → good.anchor j = bad.anchor j) ∧ (A.Law good ↔ ¬ A.Law bad))

/-- Proof fields consume the original theorem and complete-family witnesses.
The producer checks the source theorem separately at its rigid universe levels. -/
structure Registration (A : Arena.{t, s, r, o, a}) (statement : Prop) where
  realization : Realization A.signature
  bridge : statement → A.Law realization
  variation : GlobalFamilyVariation A
  sensitivity : FamilyRoleSensitivity A

end LeanInformationAudit.DependentFamily
