import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ArithUnits.MinacNguyenTanQuestion35
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.ArithUnits.MinacNguyenTanQuestion35
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.ArithUnits.MinacNguyenTanQuestion35
universe u v
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := Σ F : Type u, Σ G : Type v, Σ _ : Field F, Σ _ : Group G, ℕ
  State p := letI := p.2.2.1; Subgroup p.1ˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p U =>
    letI := p.2.2.1
    letI := p.2.2.2.1
    decide (HasNSumProperty (Units.val '' (augmentationUnitSubgroup p.1 p.2.1 U :
      Set (MonoidAlgebra p.1 p.2.1)ˣ)) p.2.2.2.2)) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law A := ∀ (F : Type u) (G : Type v) [field : Field F] [group : Group G]
    [finF : Finite F] [finG : Finite G] (U : Subgroup Fˣ) (_hminus : (-1 : Fˣ) ∈ U)
    (n : ℕ) (_hcard : 2 < Nat.card F) (_hn : 2 ≤ n)
    (_hF : HasNSumProperty (Units.val '' (U : Set Fˣ)) n),
    A.readout () ⟨F, G, field, group, n⟩ U = true

def binding : Registration arena.{u,v}
    (∀ (F : Type u) (G : Type v) [Field F] [Group G] [Finite F] [Finite G]
      (U : Subgroup Fˣ) (_hminus : (-1 : Fˣ) ∈ U)
      (n : ℕ) (_hcard : 2 < Nat.card F) (_hn : 2 ≤ n)
      (_hF : HasNSumProperty (Units.val '' (U : Set Fˣ)) n),
      HasNSumProperty (Units.val '' (augmentationUnitSubgroup F G U :
        Set (MonoidAlgebra F G)ˣ)) n) := by
  let F := ULift.{u} (ZMod 3)
  let G := ULift.{v} Unit
  have hF : HasNSumProperty (Units.val '' ((⊤ : Subgroup Fˣ) : Set Fˣ)) 2 := by
    intro r
    have hr : r.down = 0 ∨ r.down = 1 ∨ r.down = 2 := by
      generalize r.down = z
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hval (x : F) (hx : x ≠ 0) : x ∈ Units.val '' ((⊤ : Subgroup Fˣ) : Set Fˣ) := by
      obtain ⟨w, hw⟩ := isUnit_iff_ne_zero.mpr hx
      exact ⟨w, by simp, hw⟩
    rcases hr with hr | hr | hr
    · refine ⟨![1, -1], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hval, one_ne_zero, neg_ne_zero]
      · apply ULift.down_injective
        simp [Fin.sum_univ_two, hr, F]
    · refine ⟨![-1, -1], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hval, one_ne_zero, neg_ne_zero]
      · apply ULift.down_injective
        simp [Fin.sum_univ_two, hr, F]
        decide
    · refine ⟨![1, 1], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hval, one_ne_zero]
      · apply ULift.down_injective
        simp [Fin.sum_univ_two, hr, F]
        decide
  have hc : 2 < Nat.card F := by simp [F, Nat.card_eq_fintype_card]
  have hgood : arena.Law actual := by
    intro F G _ _ _ _ U hminus n hcard hn hF
    exact decide_eq_true (_root_.D5.S3.ArithUnits.MinacNguyenTanQuestion35.result
      F G U hminus n hcard hn hF)
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hf := h F G ⊤ (by simp) 2 hc (by decide) hF
    exact Bool.noConfusion hf
  have hbot : ¬ HasNSumProperty (Units.val '' (augmentationUnitSubgroup F G ⊥ :
      Set (MonoidAlgebra F G)ˣ)) 2 := by
    intro h
    obtain ⟨a, ha, hs⟩ := h 0
    have haug (i : Fin 2) : augmentation F G (a i) = 1 := by
      obtain ⟨w, hw, hv⟩ := ha i
      have heq : Units.map (augmentation F G).toRingHom.toMonoidHom w = 1 :=
        Subgroup.mem_bot.mp hw
      simpa [← hv] using congrArg Units.val heq
    have hsum := congrArg (augmentation F G) hs
    rw [map_sum, map_zero] at hsum
    simp only [haug, Fin.sum_univ_two] at hsum
    have hz : (1 : ZMod 3) + 1 = 0 := congrArg ULift.down hsum
    exact (by decide : (1 : ZMod 3) + 1 ≠ 0) hz
  refine {
    actual := actual
    bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
    variation := ⟨hgood, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, ?_, hbad⟩
      · intro j hj
        have heq : j = i := by cases i; cases j; rfl
        exact False.elim (hj heq)
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  · intro i
    let p : signature.Params := ⟨F, G, inferInstance, inferInstance, 2⟩
    refine ⟨p, (⊤ : Subgroup Fˣ), (⊥ : Subgroup Fˣ), ?_⟩
    change decide (HasNSumProperty (Units.val '' (augmentationUnitSubgroup F G ⊤ :
      Set (MonoidAlgebra F G)ˣ)) 2) ≠
      decide (HasNSumProperty (Units.val '' (augmentationUnitSubgroup F G ⊥ :
        Set (MonoidAlgebra F G)ˣ)) 2)
    rw [decide_eq_true (_root_.D5.S3.ArithUnits.MinacNguyenTanQuestion35.result
      F G ⊤ (by simp) 2 hc (by decide) hF), decide_eq_false hbot]
    decide

#print axioms binding

end
end Reg.D5.S3.ArithUnits.MinacNguyenTanQuestion35
