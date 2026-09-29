import D5.S3.Arith.Congruence.PrimePowerAffineBehavior
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Congruence.PrimePowerAffineBehavior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior

@[reducible] def signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := (ℕ × ZMod (q.1 ^ (q.2.1 - q.2.2))) ⊕
    ZMod (q.1 ^ (q.2.1 - q.2.2))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q x => eta q.1 q.2.1 q.2.2 x) (fun z => nomatch z)

def rejected : Realization signature :=
  realize signature (fun _ q _ => eta q.1 q.2.1 q.2.2 2) (fun z => nomatch z)

/-- The complete original telescope and all its clauses. The sole intervention
is the left coordinate in the positive affine classification equivalence. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p h e : ℕ) (_hp : p.Prime) (_he : e ≤ h),
    (∀ x : ℤ, depth p h x ≤ h ∧
      Int.gcd x ((p : ℤ) ^ h) = p ^ depth p h x ∧
      (depth p h x = h ↔ (p : ℤ) ^ h ∣ x) ∧
      (x ≠ 0 → depth p h x = min (padicValInt p x) h) ∧
      (depth p h x < e → IsUnit ((x / (p : ℤ) ^ depth p h x : ℤ) :
        ZMod (p ^ (h - e))))) ∧
    (∀ x y : ℤ, Int.ModEq ((p : ℤ) ^ h) x y →
      depth p h x = depth p h y ∧ eta p h e x = eta p h e y) ∧
    (∀ x : ℤ, ∃ X : ℤ, 0 < X ∧ Int.ModEq ((p : ℤ) ^ h) x X) ∧
    (∀ a b : ℤ, ∃ A B : ℤ, 0 < A ∧ 0 ≤ B ∧
      ∀ x : ℤ, Int.ModEq ((p : ℤ) ^ h)
        (a * x + (p : ℤ) ^ e * b) (A * x + (p : ℤ) ^ e * B)) ∧
    (∀ w : List (ℕ+ ⊕ Unit), ∃ A B : ℕ, 0 < A ∧
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ A B : ℕ, 0 < A → ∃ w : List (ℕ+ ⊕ Unit),
      ∀ x : ℤ, run p e w x = A * x + (p : ℤ) ^ e * B) ∧
    (∀ x y : ℤ, (R.readout () ⟨p, ⟨h, e⟩⟩ x = eta p h e y ↔
      ∀ a b : ℤ, 0 < a → 0 ≤ b →
        depth p h (a * x + (p : ℤ) ^ e * b) =
        depth p h (a * y + (p : ℤ) ^ e * b)) ∧
      (eta p h e x = eta p h e y ↔
        ∀ w : List (ℕ+ ⊕ Unit), depth p h (run p e w x) = depth p h (run p e w y))) ∧
    (e = h → ∀ u v : (ZMod (p ^ (h - e)))ˣ, u = v)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (((h 2 1 0 (by decide) (by omega)).2.2.2.2.2.2.1 1 1).1).mpr
    (fun a b ha hb => rfl)
  change eta 2 1 0 (2 : ℤ) = eta 2 1 0 (1 : ℤ) at bad
  exact (by decide : eta 2 1 0 (2 : ℤ) ≠ eta 2 1 0 (1 : ℤ)) bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨local_classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, ⟨1, 0⟩⟩, 2, 1, ?_⟩
    change eta 2 1 0 (2 : ℤ) ≠ eta 2 1 0 (1 : ℤ)
    decide

register_information_theorem local_classification in arena
  readout via (realize signature
    (fun _ q x => eta q.1 q.2.1 q.2.2 x) (fun z => nomatch z))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Congruence.PrimePowerAffineBehavior
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn",
        "arg", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.Congruence.PrimePowerAffineBehavior
