import D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
universe u v w z

abbrev signature : Signature where
  Params := Type z
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{z} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{z} :=
  realize signature (fun _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{z}
  Law r := ∀ {s : Type u} {t : Type v} {n : Type w} {d : Type z}
    [Fintype s] [DecidableEq s] [Fintype t]
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (E : s → Matrix n d ℂ) (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (A : t → Matrix d n ℂ) (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (v : d) (X : Matrix d d ℂ),
    spectralRecoveryAction E v (∑ a, E a * X * (E a)ᴴ) = r.readout () d X

theorem actual_law : arena.{u,v,w,z}.Law actual := by
  intro s t n d _ _ _ _ _ _ _ E hTP A hA hleft v X
  exact computed_recovery_of_kraus_left_inverse E hTP A hA hleft v X

theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let E : ULift.{u} (Fin 1) → Matrix (ULift.{w} (Fin 1)) (ULift.{z} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  let A : ULift.{v} (Fin 1) → Matrix (ULift.{z} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hTP : (∑ a, (E a)ᴴ * E a) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [E, Matrix.one_apply, Subsingleton.elim i j]
  have hA : (∑ b, (A b)ᴴ * A b) = 1 := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [A, Matrix.one_apply, Subsingleton.elim i j]
  have hleft : ∀ X : Matrix (ULift.{z} (Fin 1)) (ULift.{z} (Fin 1)) ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
    intro X
    ext i j
    have hi : i = ULift.up 0 := Subsingleton.elim _ _
    have hj : j = ULift.up 0 := Subsingleton.elim _ _
    subst i; subst j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [A, E]
    congr 1
  have heq := h E hTP A hA hleft (ULift.up 0) 0
  have hz : (0 : Matrix (ULift.{z} (Fin 1)) (ULift.{z} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [spectralRecoveryAction, rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v,w,z} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{z} (Fin 1), (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

register_information_theorem computed_recovery_of_kraus_left_inverse in arena
  readout via (realize signature.{z} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 17 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
