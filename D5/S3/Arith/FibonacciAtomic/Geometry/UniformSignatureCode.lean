/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/UniformSignatureCode
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One fixed backward-increment alphabet recovers signatures at every address depth. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
import D5.S0.Rewriting.Quotients.AnswerabilityCriterion

/-! A static code for the truncated ancestor signature of the fixed ordered tree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode

open TrueJumpEndpoints

/-- Alphabet size, independent of both current colour and unbounded depth. -/
def alphabetSize : ℕ → ℕ
  | 0 => 1
  | h + 1 => 3 * 2 ^ h

/-- The first incoming increment and the binary choices in the backward table. -/
def Alphabet : ℕ → Type
  | 0 => Unit
  | h + 1 => Fin 3 × (Fin h → Bool)

instance alphabetFintype (h : ℕ) : Fintype (Alphabet h) := by
  cases h <;> simp only [Alphabet] <;> infer_instance

private theorem alphabet_card (h : ℕ) : Fintype.card (Alphabet h) = alphabetSize h := by
  cases h <;> simp [Alphabet, alphabetSize]

private def incrementIndex : Increment → Fin 3
  | .minus => 0
  | .zero => 1
  | .plus => 2

private theorem incrementIndex_injective : Function.Injective incrementIndex := by
  intro a b he
  cases a <;> cases b <;> simp_all [incrementIndex]

/-- The two possible parent increments, in increasing integer order. -/
private def previousIncrement : Increment → Bool → Increment
  | .zero, false => .minus
  | .zero, true => .plus
  | .plus, false => .zero
  | .plus, true => .plus
  | .minus, false => .minus
  | .minus, true => .zero

private def backwardBit : Increment → Increment → Bool
  | .zero, .plus => true
  | .plus, .plus => true
  | .minus, .zero => true
  | _, _ => false

private theorem previous_child (d : Increment) (b : Bool) :
    previousIncrement (childIncrement d b) (backwardBit (childIncrement d b) d) = d := by
  cases d <;> cases b <;> rfl

private theorem previous_parent (m : ℕ) (p : Address) (hp : p ≠ []) :
    previousIncrement (delta m p) (backwardBit (delta m p) (delta m (parent p))) =
      delta m (parent p) := by
  induction p using List.reverseRecOn with
  | nil => contradiction
  | append_singleton p b _ =>
    change previousIncrement (delta m (child p b))
      (backwardBit (delta m (child p b)) (delta m (parent (child p b)))) =
        delta m (parent (child p b))
    rw [parent_child, delta_child]
    exact previous_child (delta m p) b

private theorem parent_ancestor (p : Address) (k : ℕ) :
    parent (ancestor p k) = ancestor p (k + 1) := by
  calc
    parent (ancestor p k) = ancestor (parent p) k := by
      simp only [parent, ancestor, List.length_take, List.take_take]
      congr 1
      omega
    _ = ancestor p (k + 1) := ancestor_parent p k

private theorem ancestor_nonroot (p : Address) (k : ℕ) (hk : k < p.length) :
    ancestor p k ≠ [] := by
  intro he
  have hh := congrArg List.length he
  simp only [ancestor, List.length_take, List.length_nil] at hh
  omega

/-- The unused positions are false, including every bit at the root. -/
def encode (m h : ℕ) (p : Address) : Alphabet h :=
  match h with
  | 0 => ()
  | _k + 1 => (incrementIndex (delta m p), fun j =>
      if j.val + 1 < p.length then
        backwardBit (delta m (ancestor p j.val)) (delta m (ancestor p (j.val + 1)))
      else false)

private theorem same_increments (m h : ℕ) (p t : Address)
    (hd : p.length = t.length) (he : encode m (h + 1) p = encode m (h + 1) t) :
    ∀ k, k < h + 1 → k < p.length →
      delta m (ancestor p k) = delta m (ancestor t k) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    simp only [ancestor_zero]
    exact incrementIndex_injective (congrArg Prod.fst he)
  | succ k ih =>
    intro hkh hkn
    have hbits := congrArg (fun a : Alphabet (h + 1) => a.2 ⟨k, by omega⟩) he
    have hkn' : k + 1 < t.length := by omega
    simp only [encode, ite_eq_left hkn, ite_eq_left hkn'] at hbits
    have hp := previous_parent m (ancestor p k) (ancestor_nonroot p k (by omega))
    have ht := previous_parent m (ancestor t k) (ancestor_nonroot t k (by omega))
    rw [parent_ancestor] at hp ht
    rw [← hp, ← ht]
    exact congrArg₂ previousIncrement (ih (by omega) (by omega)) hbits

private theorem same_signature (m h : ℕ) (p t : Address)
    (ho : observation m p = observation m t) (he : encode m h p = encode m h t) :
    signature m h p = signature m h t := by
  have hd : p.length = t.length := congrArg Prod.snd ho
  have hq : q m p = q m t := congrArg (fun x : ZMod m × ℕ => x.1) ho
  have hc : ∀ k, k ≤ min h p.length → q m (ancestor p k) = q m (ancestor t k) := by
    intro k
    induction k with
    | zero => intro _; simpa only [ancestor_zero] using hq
    | succ k ih =>
      intro hk
      have hi := incoming m (ancestor p k) (ancestor_nonroot p k (by omega))
      have ht := incoming m (ancestor t k) (ancestor_nonroot t k (by omega))
      rw [parent_ancestor] at hi ht
      have hdlt : delta m (ancestor p k) = delta m (ancestor t k) := by
        cases h with
        | zero => omega
        | succ h => exact same_increments m h p t hd he k (by omega) (by omega)
      have hprev := ih (by omega)
      rw [hi, ht, hdlt] at hprev
      exact add_right_cancel hprev
  apply (signature_eq_iff m h p t).mpr
  refine ⟨hd, fun k hk => ?_⟩
  by_cases hkn : k ≤ p.length
  · exact hc k (by omega)
  · rw [ancestor_past p k (by omega), ancestor_past t k (by omega)]

/-- One finite alphabet and one total static decoder work simultaneously for all finite
addresses, with only the exact current colour and unbounded depth as side information. -/
theorem uniform_signature_code (m : ℕ) (_hm : 3 ≤ m) (h : ℕ) :
    ∃ alpha : Address → Fin (alphabetSize h),
      ∃ D : ((ZMod m × ℕ) × Fin (alphabetSize h)) → (ℕ × List (ZMod m)),
        ∀ p : Address, D (observation m p, alpha p) = signature m h p := by
  classical
  let e : Alphabet h ≃ Fin (alphabetSize h) := Fintype.equivFinOfCardEq (alphabet_card h)
  let alpha : Address → Fin (alphabetSize h) := fun p => e (encode m h p)
  let record : Address → ((ZMod m × ℕ) × Fin (alphabetSize h)) :=
    fun p => (observation m p, alpha p)
  obtain ⟨D, hD⟩ :=
    (D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      ([] : Address) record (signature m h)).1.mpr (by
        intro p t he
        apply same_signature m h p t (congrArg (fun x => x.1) he)
        exact e.injective (congrArg (fun x => x.2) he))
  exact ⟨alpha, D, fun p => (congrFun hD p).symm⟩

#print axioms uniform_signature_code

end D5.S3.Arith.FibonacciAtomic.Geometry.UniformSignatureCode
