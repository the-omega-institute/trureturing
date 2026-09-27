import D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange (normalWord)

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ k => ecc k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k L N =>
    if k = 3 then (L * (N - L) + 1) / 2
    else if k = 4 then formulaFour L N else formulaFive L N) (fun e => nomatch e)

/-- The whole negated disjunction, retaining all three clauses for each reading. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ (conjSixteen (r.readout () ()) ∨ conjSixteen diam)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  left
  constructor
  · intro L N _ _ _
    rfl
  constructor
  · intro L N _ _ _
    rfl
  · exact ⟨0, fun _ _ _ _ => rfl⟩

/-- With a window longer than the word no edge exists, at every reach depth. -/
theorem oversize_reach (m : ℕ) (x y : List Bool) (hx : x.length < 5)
    (h : Reach 5 m x y) : y = x := by
  induction m generalizing y with
  | zero => exact h
  | succ m ih =>
    rcases h with h | ⟨z, hz, i, hi, _⟩
    · exact ih y h
    · have hz := ih z hz
      subst z
      omega

theorem oversize_ecc : ecc 5 2 4 = 0 := by
  have empty : {m | ∀ y, IsVertex 2 4 y → Reach 5 m (normalWord 2 (4 - 2)) y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro m h
    have hreach := h [true, true, false, false] ⟨rfl, rfl⟩
    have equal := oversize_reach m _ _ (by decide) hreach
    have : ([true, true, false, false] : List Bool) = [false, false, true, true] := equal
    contradiction
  simp only [ecc, empty, Nat.sInf_empty]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 3, 5, ?_⟩
  intro h
  have equal := congrFun (congrFun h 2) 4
  change ecc 3 2 4 = ecc 5 2 4 at equal
  rw [oversize_ecc,
    (_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
      2 4 (by decide) (by decide) (by decide)).1] at equal
  contradiction

noncomputable def registration : Registration arena
    (¬ _root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.result in arena
  readout via (realize signature (fun _ _ k => ecc k) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
    «definition» := some {
      owner := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
      name := `D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.ShrunkenGrassmannianConjectureSixteenRefutation
