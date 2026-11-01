/- GID: D5/S0/Certificates/FiniteLexSymmetry
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteLexSymmetry
   mirror-E: none(waiver:finite-context-symmetry-descent)
   anchors: [D5/S0/Certificates/FiniteSymmetryBoundReplay]
   utility: none
   digest: A checked first differing coordinate makes every compatible finite event strictly smaller under the actual coordinate and value permutations. -/

import D5.S0.Certificates.FiniteSymmetryBoundReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteLexSymmetry
open D5.S0.Certificates.FiniteSymmetryBoundReplay

variable {n k : ℕ}

def act (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (e : Event (Fin n) (Fin k)) : Event (Fin n) (Fin k) := fun i => ν (e (σ i))

/-- The pivot decreases strictly. Earlier coordinates are either fixed by the
whole action, or their equality is checked using actual assigned values. -/
def dominates (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (p : Partial (Fin n) (Fin k)) : Bool :=
  decide (∃ i a b, p (σ i) = some a ∧ p i = some b ∧ ν a < b ∧
    ∀ j, j < i →
      (σ j = j ∧ ∀ v, ν v = v) ∨
      ∃ a b, p (σ j) = some a ∧ p j = some b ∧ ν a = b)

noncomputable def rank (e : Event (Fin n) (Fin k)) : ℕ :=
  ((Fintype.orderIsoFinOfCardEq (Lex (Event (Fin n) (Fin k))) rfl).symm
    (toLex e)).val

/-- A local pivot witness decreases the rank of every compatible complete
event. It cannot justify circular symmetry pruning. -/
theorem dominates_rank_lt (σ : Fin n ≃ Fin n) (ν : Fin k ≃ Fin k)
    (p : Partial (Fin n) (Fin k)) (h : dominates σ ν p = true)
    (e : Event (Fin n) (Fin k)) (hp : Compatible p e) :
    rank (act σ ν e) < rank e := by
  obtain ⟨i, a, b, ha, hb, hab, hprefix⟩ := of_decide_eq_true h
  have hlex : toLex (act σ ν e) < toLex e := by
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      rcases hprefix j hj with ⟨hσ, hν⟩ | ⟨a, b, ha, hb, hab⟩
      · simp [act, hσ, hν]
      · simpa only [act, Pi.toLex_apply, hp _ _ ha, hp _ _ hb] using hab
    · simpa only [act, Pi.toLex_apply, hp _ _ ha, hp _ _ hb] using hab
  exact (Fintype.orderIsoFinOfCardEq (Lex (Event (Fin n) (Fin k))) rfl).symm.strictMono hlex

#print axioms dominates_rank_lt

end D5.S0.Certificates.FiniteLexSymmetry
