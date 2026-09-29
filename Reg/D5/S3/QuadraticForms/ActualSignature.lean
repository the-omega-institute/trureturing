import D5.S3.QuadraticForms.ActualSignature
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ActualSignature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.ActualSignature

noncomputable section

def signatureFamily : Signature where
  Params := ℕ
  State := fun n => Mat ℝ n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signatureFamily := realize signatureFamily
  (fun (_ : Unit) (n : ℕ) (A : Mat ℝ n) => signature A.toQuadraticForm') (fun e => nomatch e)

def rejected : Realization signatureFamily := realize signatureFamily
  (fun (_ : Unit) (n : ℕ) (_ : Mat ℝ n) => (1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signatureFamily
  Law R := ∀ (n : ℕ) (A : Mat ℝ n) (_hs : ∀ r s, A r s = A s r) (z : ℤ),
    Realizes n A z ↔ R.readout () n A = z

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨realizes_iff_signature, rejected, ?_⟩
    intro h
    have hh := (h 0 0 (by simp) 0).mp rfl
    change (1 : ℤ) = 0 at hh
    exact one_ne_zero hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hh := (h 0 0 (by simp) 0).mp rfl
        change (1 : ℤ) = 0 at hh
        exact one_ne_zero hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : Mat ℝ 1), (1 : Mat ℝ 1), ?_⟩
    have hz : signature (0 : Mat ℝ 1).toQuadraticForm' = 0 :=
      (realizes_iff_signature 1 0 (by simp) 0).mp (by
        exact Or.inl ⟨by simp, rfl⟩)
    have ho : signature (1 : Mat ℝ 1).toQuadraticForm' = 1 :=
      (realizes_iff_signature 1 1 (by intro r s; simp [Matrix.one_apply, eq_comm]) 1).mp (by
        refine Or.inr (Or.inl ⟨0, Or.inl ⟨by norm_num, ?_⟩⟩)
        norm_num [Realizes])
    change signature (0 : Mat ℝ 1).toQuadraticForm' ≠
      signature (1 : Mat ℝ 1).toQuadraticForm'
    rw [hz, ho]
    norm_num

register_information_theorem _root_.D5.S3.QuadraticForms.ActualSignature.realizes_iff_signature
  in arena
  readout via (realize signatureFamily
    (fun (_ : Unit) (n : ℕ) (A : Mat ℝ n) => signature A.toQuadraticForm') (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.QuadraticForms.ActualSignature
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end
end Reg.D5.S3.QuadraticForms.ActualSignature
