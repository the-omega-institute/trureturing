/- GID: D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.claim; result=D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.result; claim=D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.claim
   digest: The Q8 subquandle {±i,±j} refutes Ta's strictness question, Problem 11.7. -/

/- proof_shape: result: bind-only (finite kernel decision on the Q8 witness)
   escape_witness: none
   admission_basis: open-problem-resolution (#9433; Refuted)
   Shared definitions: ConjugationSubquandle; the Q8 certificate is unchanged. -/

import D5.S3.FiniteGroups.Quandles.ConjugationSubquandle
import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace D5.S3.FiniteGroups.Quandles.TaGoodInvolutionBoundRefutation

open ConjugationSubquandle

/-- The strictness reading of Ta, Problem 11.7, restricted to finite groups. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (X : Finset G)
    (h : ConjClosed X),
    2 ≤ Nat.card (Subgroup.center (Subgroup.closure (X : Set G))) →
    2 ≤ orbitCount X →
    Fintype.card (Good X h) < min (Fintype.card (Aut X h))
      (Nat.card (Subgroup.center (Subgroup.closure (X : Set G))) ^ orbitCount X)

private abbrev Q8 := QuaternionGroup 2

private def witness : Finset Q8 :=
  {QuaternionGroup.a 1, QuaternionGroup.a 3, QuaternionGroup.xa 0, QuaternionGroup.xa 2}

/-- In `Q8`, the subquandle `{±i, ±j}` has four good involutions and eight
    automorphisms, and attains the bound `min (8, 2^2) = 4`. -/
theorem result : ¬ claim := by
  intro hc
  have hclosed : ConjClosed witness := by
    unfold ConjClosed witness
    decide
  have htop : Subgroup.closure (witness : Set Q8) = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro g
    have ha : QuaternionGroup.a 1 ∈ Subgroup.closure (witness : Set Q8) :=
      Subgroup.subset_closure (by decide)
    have hx : QuaternionGroup.xa 0 ∈ Subgroup.closure (witness : Set Q8) :=
      Subgroup.subset_closure (by decide)
    have hall : ∀ g : Q8, ∃ n : Fin 4, ∃ b : Bool,
        g = (if b then QuaternionGroup.xa 0 else 1) * QuaternionGroup.a 1 ^ n.val := by
      decide
    obtain ⟨n, b, rfl⟩ := hall g
    apply Subgroup.mul_mem
    · cases b
      · exact Subgroup.one_mem _
      · exact hx
    · exact Subgroup.pow_mem _ ha _
  have hz : Nat.card (Subgroup.center (Subgroup.closure (witness : Set Q8))) = 2 := by
    rw [htop, Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv : (⊤ : Subgroup Q8) ≃* Q8)).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  have hk : orbitCount witness = 2 := by
    have hcalc :
        (witness.image fun x => witness.filter fun y => ∃ g : Q8, g * x * g⁻¹ = y).card = 2 := by
      decide
    simpa only [orbitCount, htop, Subgroup.mem_top, true_and] using hcalc
  have hg : Fintype.card (Good witness hclosed) = 4 := by
    change Fintype.card (Good witness (by unfold ConjClosed witness; decide)) = 4
    decide
  have haut : Fintype.card (Aut witness hclosed) = 8 := by
    change Fintype.card (Aut witness (by unfold ConjClosed witness; decide)) = 8
    decide
  have hlt := hc Q8 witness hclosed (by omega) (by omega)
  rw [hg, haut, hz, hk] at hlt
  norm_num at hlt

#print axioms result

end D5.S3.FiniteGroups.Quandles.TaGoodInvolutionBoundRefutation
