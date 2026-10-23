import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular
universe u

abbrev signature : Signature where
  Params := Type u
  State C := (Fin 4 → C) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ C := (Fin 4 → C) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [LinearOrder C] [Fintype C] [Nonempty C]
    (p : (Fin 4 → C) → ℝ) (m : C → ℝ)
    (_hp : ∀ x, 0 ≤ p x) (_hn : ∑ x, p x = 1)
    (_hm : ∀ (i : Fin 4) (t : C), (∑ x, if x i = t then p x else 0) = m t)
    (f : (Fin 4 → C) → ℝ)
    (_hf : ∀ x y, f x + f y ≤ f (x ⊓ y) + f (x ⊔ y)),
    (∑ x, p x * R.readout () C f x) ≤ ∑ t, m t * f (fun _ => t)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have bad := h (C := ULift.{u} (Fin 1)) (fun _ => 1) (fun _ => 1)
    (by intro x; norm_num) (by simp)
    (by
      intro i t
      have he : ∀ x : Fin 4 → ULift.{u} (Fin 1), x i = t :=
        fun _ => Subsingleton.elim _ _
      simp [he])
    (fun _ => 0) (by intro x y; simp)
  norm_num [rejected, realize] at bad

def family : Registration arena.{u}
    (type_of% @common_marginal_supermodular_le_diagonal.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_marginal_supermodular_le_diagonal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} (Fin 1), (fun _ => 0), (fun _ => 1), ?_⟩
    intro he
    have impossible := congrFun he (fun _ => ⟨0⟩)
    norm_num [actual, realize] at impossible

#print axioms family

end Reg.D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular
