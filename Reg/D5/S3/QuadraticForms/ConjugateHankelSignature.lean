import D5.S3.QuadraticForms.ConjugateHankelSignature
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ConjugateHankelSignature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexConjugate

namespace Reg.D5.S3.QuadraticForms.ConjugateHankelSignature
noncomputable section

def signatureFamily : Signature where
  Params := (_ : Finset ℂ) × ℕ
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signatureFamily := realize signatureFamily
  (fun _ p w => (sigPos (weightedHankel p.1 w p.2).toQuadraticForm' : ℤ) -
    (sigNeg (weightedHankel p.1 w p.2).toQuadraticForm' : ℤ)) (fun e => nomatch e)

def rejected : Realization signatureFamily := realize signatureFamily
  (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signatureFamily
  Law R := ∀ (s : Finset ℂ) (_hs : ∀ z ∈ s, conj z ∈ s)
    (d : ℕ) (_hd : s.card ≤ d) (w : s → ℂ)
    (_hw : ∀ z u : s, (u : ℂ) = conj (z : ℂ) → w u = conj (w z)),
    R.readout () ⟨s, d⟩ w =
      ∑ r : {z : s // (z : ℂ).im = 0},
        ((if 0 < (w r.val).re then (1 : ℤ) else 0) -
        (if (w r.val).re < 0 then (1 : ℤ) else 0))

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨weighted_hankel_signature, rejected, ?_⟩
    intro h
    have hh := h ∅ (by simp) 0 (by simp) (fun _ => 0) (by simp)
    simp only [rejected, realize, Finset.sum_const_zero, Complex.zero_re,
      lt_self_iff_false, if_false, sub_self] at hh
    change (1 : ℤ) = 0 at hh
    exact one_ne_zero hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hh := h ∅ (by simp) 0 (by simp) (fun _ => 0) (by simp)
        simp only [rejected, realize, Finset.sum_const_zero, Complex.zero_re,
          lt_self_iff_false, if_false, sub_self] at hh
        change (1 : ℤ) = 0 at hh
        exact one_ne_zero hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    classical
    let s : Finset ℂ := {0}
    let : Unique {z : s // (z : ℂ).im = 0} := {
      default := ⟨⟨0, by simp [s]⟩, by simp⟩
      uniq z := by
        apply Subtype.ext
        apply Subtype.ext
        exact Finset.mem_singleton.mp z.val.property }
    have hs : ∀ z ∈ s, conj z ∈ s := by simp [s]
    have hz := weighted_hankel_signature s hs 1 (by simp [s])
      (fun _ => 0) (by simp)
    have ho := weighted_hankel_signature s hs 1 (by simp [s])
      (fun _ => 1) (by simp)
    refine ⟨⟨s, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change (sigPos (weightedHankel s (fun _ => 0) 1).toQuadraticForm' : ℤ) -
        (sigNeg (weightedHankel s (fun _ => 0) 1).toQuadraticForm' : ℤ) ≠
      (sigPos (weightedHankel s (fun _ => 1) 1).toQuadraticForm' : ℤ) -
        (sigNeg (weightedHankel s (fun _ => 1) 1).toQuadraticForm' : ℤ)
    rw [hz, ho]
    norm_num

register_information_theorem weighted_hankel_signature
  in arena
  readout via (realize signatureFamily
    (fun _ p w => (sigPos (weightedHankel p.1 w p.2).toQuadraticForm' : ℤ) -
      (sigNeg (weightedHankel p.1 w p.2).toQuadraticForm' : ℤ)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.QuadraticForms.ConjugateHankelSignature
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

end
end Reg.D5.S3.QuadraticForms.ConjugateHankelSignature
