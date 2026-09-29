import D5.S3.QuadraticForms.PolynomialSignature
import Reg.Support.DependentFamily

open _root_.D5.S3.QuadraticForms.ActualSignature
open _root_.D5.S3.QuadraticForms.PolynomialSignature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.QuadraticForms.PolynomialSignature

noncomputable section
universe u

def signature_family : Signature where
  Params := Σ σ : Type u, Σ n : ℕ, Mat (Poly σ) n
  State := fun p => p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature_family.{u} := realize signature_family
  (fun _ p x => signature (Matrix.toQuadraticForm'
    (fun i j => MvPolynomial.eval x (p.2.2 i j)))) (fun e => nomatch e)

def rejected : Realization signature_family.{u} := realize signature_family
  (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature_family.{u}
  Law R := ∀ {σ : Type u} (n : ℕ) (A : Mat (Poly σ) n) (z : ℤ) (x : σ → ℝ)
    (_hs : ∀ i j, MvPolynomial.eval x (A i j) = MvPolynomial.eval x (A j i)),
    holds x (compile n A z) ↔ R.readout () ⟨σ, n, A⟩ x = z

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨compile_iff_signature, rejected, ?_⟩
    intro h
    have hh := (h 0 (0 : Mat (Poly (ULift.{u} Unit)) 0) 0 (fun _ => 0)
      (by simp)).mp (by simp [compile, truth, holds])
    change (1 : ℤ) = 0 at hh
    exact one_ne_zero hh
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, ?_⟩
      · intro j h
        exact (h (@Subsingleton.elim Unit _ j i)).elim
      · intro h
        have hh := (h 0 (0 : Mat (Poly (ULift.{u} Unit)) 0) 0 (fun _ => 0)
          (by simp)).mp (by simp [compile, truth, holds])
        change (1 : ℤ) = 0 at hh
        exact one_ne_zero hh
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let A : Mat (Poly (ULift.{u} Unit)) 1 := fun _ _ => MvPolynomial.X ⟨()⟩
    refine ⟨⟨ULift.{u} Unit, 1, A⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change signature (Matrix.toQuadraticForm'
      (fun r s => MvPolynomial.eval (fun _ => (0 : ℝ)) (A r s))) ≠
      signature (Matrix.toQuadraticForm'
        (fun r s => MvPolynomial.eval (fun _ => (1 : ℝ)) (A r s)))
    simp only [A, MvPolynomial.eval_X]
    have hz : signature (Matrix.toQuadraticForm' (fun _ _ : Fin 1 => (0 : ℝ))) = 0 :=
      (realizes_iff_signature 1 _ (by simp) 0).mp (by
        exact Or.inl ⟨by simp, rfl⟩)
    have ho : signature (Matrix.toQuadraticForm' (fun _ _ : Fin 1 => (1 : ℝ))) = 1 :=
      (realizes_iff_signature 1 _ (by simp) 1).mp (by
        refine Or.inr (Or.inl ⟨0, Or.inl ⟨by norm_num, ?_⟩⟩)
        norm_num [Realizes])
    rw [hz, ho]
    norm_num

register_information_theorem _root_.D5.S3.QuadraticForms.PolynomialSignature.compile_iff_signature
  in arena
  readout via (realize signature_family.{u}
    (fun _ p x => signature (Matrix.toQuadraticForm'
      (fun i j => MvPolynomial.eval x (p.2.2 i j)))) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.QuadraticForms.PolynomialSignature
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

end
end Reg.D5.S3.QuadraticForms.PolynomialSignature
