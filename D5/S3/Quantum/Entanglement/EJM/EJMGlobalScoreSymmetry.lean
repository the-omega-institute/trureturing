/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalScoreSymmetry
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalScoreSymmetry
   mirror-E: none(waiver:actual-global-inflation-replay)
   anchors: []
   utility: none
   digest: The actual 192 by 24 EJM actions preserve the centered score and checked partial cuts strictly decrease finite lexicographic rank. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
import D5.S3.Quantum.Entanglement.EJM.EJMSourceActionClosure
import D5.S0.Certificates.FiniteLexSymmetry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation (Node)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMSourceActionClosure
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (outcome)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (outcomeEquiv)

/- Node is already Fin 20. The source table and all of its actual block/local
transport witnesses are reused from EJMSourceActionClosure; the 24 outcome maps are
reused from the local producer. No second table or node-order conversion occurs.
The producer orders source maps first, then the 24 lexicographic outcome maps.
-/

abbrev GlobalSym := Fin 192 × Fin 24
abbrev Cut := GlobalSym × Node

/-- Decode the producer's source-major symmetry tag; the pivot is an actual node. -/
def cutOfTag (tag : Fin 4608) (pivot : Node) : Cut :=
  ((⟨tag.val / 24, by have h := tag.isLt; omega⟩,
    ⟨tag.val % 24, Nat.mod_lt _ (by decide)⟩), pivot)

/-- A cut's action uses its exact source-copy map and common outcome permutation. -/
def act (s : Cut) (e : Event Node (Fin 4)) : Event Node (Fin 4) :=
  outcome s.1.2 ∘ e ∘ sourceSymmetry s.1.1

theorem actual_score_invariant (s : Cut) (e : Event Node (Fin 4)) :
    score F1 F2 (act s e) = score F1 F2 e := by
  change score F1 F2 ((outcomeEquiv s.1.2) ∘ (e ∘ sourceSymmetry s.1.1)) = _
  rw [actual_score_relabel, actual_score_sourceSymmetry]

private def prefixEqual (s : GlobalSym) (p : Partial Node (Fin 4)) (j : Node) : Bool :=
  if sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v then true
  else match p (sourceSymmetry s.1 j), p j with
    | some a, some b => decide (outcome s.2 a = b)
    | _, _ => false

private theorem prefixEqual_sound (s : GlobalSym) (p : Partial Node (Fin 4))
    (j : Node) (h : prefixEqual s p j = true) :
    (sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v) ∨
      ∃ a b, p (sourceSymmetry s.1 j) = some a ∧ p j = some b ∧ outcome s.2 a = b := by
  by_cases fixed : sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v
  · exact Or.inl fixed
  · right
    simp only [prefixEqual, fixed, ite_false] at h
    cases ha : p (sourceSymmetry s.1 j) with
    | none => simp only [ha, Bool.false_eq_true] at h
    | some a =>
      cases hb : p j with
      | none => simp only [ha, hb, Bool.false_eq_true] at h
      | some b =>
        simp only [ha, hb] at h
        exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-- The stored pivot checks strict descent and every earlier actual coordinate.
Unknown values are admitted only where the entire action fixes that coordinate. -/
def dominates (s : Cut) (p : Partial Node (Fin 4)) : Bool :=
  match p (sourceSymmetry s.1.1 s.2), p s.2 with
  | some a, some b => decide (outcome s.1.2 a < b ∧
      ∀ j, j < s.2 → prefixEqual s.1 p j = true)
  | _, _ => false

/-- Every accepted cut decreases the rank of every compatible complete event.
This obligation is local to the actual reached partial context of a shared DAG. -/
theorem dominates_rank_lt (s : Cut) (p : Partial Node (Fin 4))
    (h : dominates s p = true) (e : Event Node (Fin 4)) (hp : Compatible p e) :
    FiniteLexSymmetry.rank (act s e) < FiniteLexSymmetry.rank e := by
  have hd : FiniteLexSymmetry.dominates (sourceSymmetryEquiv s.1.1) (outcomeEquiv s.1.2) p = true := by
    unfold FiniteLexSymmetry.dominates
    apply decide_eq_true
    cases ha : p (sourceSymmetry s.1.1 s.2) with
    | none => simp only [dominates, ha, Bool.false_eq_true] at h
    | some a =>
      cases hb : p s.2 with
      | none => simp only [dominates, ha, hb, Bool.false_eq_true] at h
      | some b =>
        simp only [dominates, ha, hb] at h
        obtain ⟨hlt, hprefix⟩ := of_decide_eq_true h
        refine ⟨s.2, a, b, ha, hb, hlt, ?_⟩
        intro j hj
        exact prefixEqual_sound s.1 p j (hprefix j hj)
  exact FiniteLexSymmetry.dominates_rank_lt (sourceSymmetryEquiv s.1.1)
    (outcomeEquiv s.1.2) p hd e hp

#print axioms actual_score_invariant
#print axioms dominates_rank_lt

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry
