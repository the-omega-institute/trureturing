import D5.S3.Arith.GoldenMatrixPeriodBridge
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenMatrixPeriodBridge

open scoped Matrix
open _root_.D5.S3.Arith.GoldenApparition
open _root_.D5.S3.Arith.GoldenMatrixPeriodBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ _ m => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ m => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ,
    Function.Injective (goldenMatrixHom m) ∧
      goldenMatrixHom m (GoldenMod.phi : GoldenMod m) = !![1, 1; 1, 0] ∧
      orderOf (GoldenMod.phi : GoldenMod m) =
        r.readout () () m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 2).2.2
  have hgood := (golden_matrix_faithful 2).2.2
  change orderOf (GoldenMod.phi : GoldenMod 2) =
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)) + 1 at hbad
  omega

def registration : Registration arena
    (∀ m : ℕ,
      Function.Injective (goldenMatrixHom m) ∧
        goldenMatrixHom m (GoldenMod.phi : GoldenMod m) = !![1, 1; 1, 0] ∧
        orderOf (GoldenMod.phi : GoldenMod m) =
          orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_matrix_faithful, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    intro h
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 1)) =
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)) at h
    have hmatrix1 :
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 1)) = 1 :=
      Subsingleton.elim _ _
    rw [hmatrix1, orderOf_one] at h
    have hmatrix2 := (orderOf_eq_one_iff.mp h.symm)
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 1) hmatrix2
    norm_num at h01

register_information_theorem _root_.D5.S3.Arith.GoldenMatrixPeriodBridge.golden_matrix_faithful
  in arena
  readout via (realize signature
    (fun _ _ m => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenMatrixPeriodBridge
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end
end Reg.D5.S3.Arith.GoldenMatrixPeriodBridge
