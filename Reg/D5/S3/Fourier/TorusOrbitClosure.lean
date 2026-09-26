import D5.S3.Fourier.TorusOrbitClosure
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Fourier.TorusOrbitClosure
open _root_.D5.S3.Fourier.TorusOrbitClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped BigOperators
noncomputable section
universe u

def signature : Signature where
  Params := Type u
  State I := I → Circle
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := ℕ → (I → Circle)
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] (g z : I → Circle),
    z ∈ closure (range (R.readout () I g)) ↔
      ∀ k : I → ℤ, (∏ i, g i ^ k i) = 1 → (∏ i, z i ^ k i) = 1

def actual : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (I : Type u) (g : I → Circle) (n : ℕ) => g ^ n)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature
    (fun (_ : Unit) (I : Type u) (_ : I → Circle) (_ : ℕ) => (1 : I → Circle))
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have hz := (h (I := ULift.{u} Unit) (fun _ => -1) (fun _ => -1)).mpr
    (by intro k hk; exact hk)
  change (fun _ : ULift.{u} Unit => (-1 : Circle)) ∈
    closure (range (fun _ : ℕ => (1 : ULift.{u} Unit → Circle))) at hz
  rw [range_const, isClosed_singleton.closure_eq, mem_singleton_iff] at hz
  have heq := congrArg (fun f : ULift.{u} Unit → Circle => ((f ⟨()⟩ : Circle) : ℂ)) hz
  norm_num at heq

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro I hI g z; exact result g z, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, (fun _ => -1), (fun _ => 1), ?_⟩
    intro h
    have heq := congrArg
      (fun f : ℕ → ULift.{u} Unit → Circle => ((f 1 ⟨()⟩ : Circle) : ℂ)) h
    norm_num [actual, realize] at heq

register_information_theorem result in arena
  readout via (realize signature.{u}
    (fun (_ : Unit) (I : Type u) (g : I → Circle) (n : ℕ) => g ^ n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.TorusOrbitClosure
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration
end

end Reg.D5.S3.Fourier.TorusOrbitClosure
