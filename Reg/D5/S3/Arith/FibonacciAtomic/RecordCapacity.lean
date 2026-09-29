import D5.S3.Arith.FibonacciAtomic.RecordCapacity
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open _root_.D5.S3.Arith.FibonacciAtomic.RecordCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity
universe u

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ _p : ℕ, (Fin d → ℕ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t r => t.2.1 ^ (r * Fintype.card (Defect t.2.1 t.2.2)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T := (∀ {d p : ℕ} (_hp : p.Prime)
    (B : Matrix (Fin d) (Fin d) ℤ)
    (U V : (Matrix (Fin d) (Fin d) ℤ)ˣ) (s : Fin d → ℕ)
    (_hSmith : U.val * B * V.val = diagonal (fun i => (s i : ℤ)))
    {R : ℕ → Type u} [∀ r, Fintype (R r)]
    (η : ∀ r, State d p (r + 1) → R r) (ρ : ∀ r, R (r + 1) → R r)
    (_hjoint : ∀ r, Function.Injective (fun x => (action B p (r + 1) x, η r x)))
    (_haut : ∀ r x, ρ r (η (r + 1) x) = η r (reduce p (r + 1) x)),
    (∀ r, Function.Injective (fun x => η r (defectInput V p (r + 1) s x)) ∧
      T.readout () ⟨d, p, s⟩ (r + 1) ≤ Fintype.card (R r)) ∧
    (∀ r, Function.Injective (fun x =>
      (action B p (r + 1) x, canonicalRecord V p (r + 1) s x)) ∧
      Nat.card (Defect p s → ZMod (p ^ (r + 1))) =
        p ^ ((r + 1) * Fintype.card (Defect p s))) ∧
    (∀ r x, reduce p (r + 1) (canonicalRecord V p (r + 2) s x) =
      canonicalRecord V p (r + 1) s (reduce p (r + 1) x))) ∧
    (∀ (q : ℕ) (hq : q.Prime), ScalarRecordExamples.{u} q hq) ∧
    ThreeNodeRecordExamples.{u}

theorem actual_law : arena.{u}.Law actual := by
  exact @autonomous_record_capacity

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h.1 (d := 0) (p := 2) (by decide) 0 1 1 (fun i => Fin.elim0 i)
    (by ext i; exact Fin.elim0 i) (R := fun _ => ULift.{u} (ZMod 1))
    (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ _ _ => Subsingleton.elim _ _) (fun _ _ => rfl)
  have hb := (hbad.1 0).2
  norm_num [rejected, realize] at hb

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, 2, fun _ => 2⟩, 1, 2, ?_⟩
    norm_num [actual, realize, Defect]

register_information_theorem autonomous_record_capacity in arena
  readout via (realize signature
    (fun _ t r => t.2.1 ^ (r * Fintype.card (Defect t.2.1 t.2.2)))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg", "fn", "arg"]
      stateOperand := some #["arg", "fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity
