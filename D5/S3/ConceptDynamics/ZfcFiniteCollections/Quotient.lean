/- GID: D5/S3/ConceptDynamics/ZfcFiniteCollections/Quotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteCollections/Quotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vorspiel.Quotient for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Matrix

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Quotient.lean, original lines 1-44.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace Quotient
open Matrix
variable {α : Type u} [s : Setoid α] {β : Sort v}

def liftVec : ∀ {n} (f : (Fin n → α) → β),
  (∀ v₁ v₂ : Fin n → α, (∀ n, v₁ n ≈ v₂ n) → f v₁ = f v₂) → (Fin n → Quotient s) → β
| 0,     f, _, _ => f ![]
| n + 1, f, h, v =>
  let ih : α → (Fin n → Quotient s) → β :=
    fun a v => liftVec (n := n) (fun v => f (a :> v))
      (fun v₁ v₂ hv => h (a :> v₁) (a :> v₂) (Fin.cases (by simp [cons_val_zero, Setoid.refl]) hv)) v
  Quot.liftOn (vecHead v) (ih · (vecTail v))
    (fun a b hab => by
      have : ∀ v, f (a :> v) = f (b :> v) := fun v ↦ h _ _ (Fin.cases hab (by simp [cons_val_succ, Setoid.refl]))
      simp [this, ih])

lemma liftVec_mk {n} (f : (Fin n → α) → β) (h) (v : Fin n → α) :
    liftVec f h (Quotient.mk s ∘ v) = f v := by
  induction' n with n ih <;> simp [liftVec, empty_eq]
  simpa using! ih (fun v' => f (vecHead v :> v'))
    (fun v₁ v₂ hv => h (vecHead v :> v₁) (vecHead v :> v₂) (Fin.cases (refl _) hv)) (vecTail v)

end Quotient

end
