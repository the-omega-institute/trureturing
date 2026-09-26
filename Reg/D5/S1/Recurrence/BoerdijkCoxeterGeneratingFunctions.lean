import D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Point
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => vertex n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => vertex (n + 1)) (fun e => nomatch e)

/-- All nine geometric clauses and all three infinite series identities remain in the law.
Only the first vertex in the adjacent-edge squared distance is intervened on. -/
def arena : Arena where
  signature := signature
  Law r :=
    (∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (r.readout () () n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have edge := (h.1 0).2.1
  norm_num [rejected, realize, sqDist] at edge

def registration : Registration arena
    ((∀ n,
      regular (vertex n) (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) ∧
      sqDist (vertex n) (vertex (n + 1)) = 8 ∧
      vertex n ≠ faceCenter (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      faceNoncollinear (vertex (n + 1)) (vertex (n + 2))
        (vertex (n + 3)) ∧
      vertex (n + 4) = reflected (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 1)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 2)) ∧
      faceOrthogonal (vertex n) (vertex (n + 1))
        (vertex (n + 2)) (vertex (n + 3)) (vertex (n + 3)) ∧
      ∀ i, (vertex n i + vertex (n + 4) i) / 2 =
        faceCenter (vertex (n + 1)) (vertex (n + 2)) (vertex (n + 3)) i) ∧
    PowerSeries.mk (fun n => scaled n (0 : Fin 3)) =
      (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 -
        66 * PowerSeries.X ^ 4 + 23 * PowerSeries.X ^ 3 +
        9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (1 : Fin 3)) =
      (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 -
        90 * PowerSeries.X ^ 4 + 15 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        ((3 * PowerSeries.X - 1) ^ 2 *
          (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) 1 ∧
    PowerSeries.mk (fun n => scaled n (2 : Fin 3)) =
      (18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 -
        24 * PowerSeries.X ^ 3 - 5 * PowerSeries.X ^ 2 + 1 : PowerSeries ℚ) *
      PowerSeries.invOfUnit
        (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 -
          PowerSeries.X - 1) (-1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    have edge := (_root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result.1 0).2.1
    change vertex 0 = vertex 1 at h
    simp only [Nat.zero_add, h, sqDist, sub_self, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero] at edge
    norm_num at edge

register_information_theorem _root_.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result in arena
  readout via (realize signature (fun _ _ n => vertex n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
