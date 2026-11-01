import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction

/-! A source-bound matching readout retains all native matroid parameters. -/

namespace Reg.D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction

open Set
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching
open _root_.D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction
open scoped Pointwise

universe u

/-- The original telescope before the specified source set. -/
structure Inputs where
  G : Type u
  group : AddCommGroup G
  torsion : letI := group; IsAddTorsionFree G
  M : Matroid G
  N : Matroid G
  finiteM : M.Finite
  finiteN : N.Finite
  looplessM : M.Loopless
  looplessN : N.Loopless
  r : ℕ
  m : ℕ
  positive : 1 ≤ r
  rankM : M.eRank = r
  rankN : N.eRank = r
  paving : IsSparsePaving N
  zero : letI := group; (0 : G) ∉ N.E
  sizeM : M.E.ncard = m
  sizeN : N.E.ncard = m

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Set P.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def matchingReadout (P : Inputs.{u}) (S : Set P.G) : Prop :=
  letI := P.group
  BasisMatches P.M.E P.N S

def actual : Realization signature.{u} :=
  realize signature (fun _ P S => matchingReadout P S) (fun a => Empty.elim a)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) (S : Set P.G), P.M.IsBase S →
    letI := P.group
    let C := admissibleUnion P.M.E P.N.E S
    let U := P.N.E \ C
    ((¬ R.readout () P S) ↔ P.N.IsCircuit C ∧ P.N.IsFlat C ∧
      P.N.eRk C + 1 = P.r ∧ C.ncard = P.r) ∧
    ((¬ BasisMatches P.M.E P.N S) → 2 ≤ P.r ∧ P.r + 1 ≤ P.m ∧
      U.ncard = P.m - P.r ∧ S + (U ∪ {0}) = P.M.E)

abbrev sourceScope := type_of% (@basiswise_obstruction.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P S hS
    letI := P.group
    letI := P.torsion
    letI := P.finiteM
    letI := P.finiteN
    letI := P.looplessM
    letI := P.looplessN
    exact @h P.G P.group P.torsion P.M P.N P.finiteM P.finiteN
      P.looplessM P.looplessN P.r P.m P.positive P.rankM P.rankN P.paving
      P.zero P.sizeM P.sizeN S hS
  · intro h G group torsion M N finiteM finiteN looplessM looplessN r m
      positive rankM rankN paving zero sizeM sizeN S hS
    exact h ⟨G, group, torsion, M, N, finiteM, finiteN, looplessM, looplessN,
      r, m, positive, rankM, rankN, paving, zero, sizeM, sizeN⟩ S hS

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@basiswise_obstruction.{u})

private lemma free_paving {α : Type*} (E : Set α) : IsSparsePaving (Matroid.freeOn E) := by
  constructor
  · intro X hX _
    exact Matroid.freeOn_indep (by simpa using hX)
  · intro X hX hc
    rw [Matroid.freeOn_dual_eq, Matroid.eRank_loopyOn] at hc
    simp at hc

private lemma free_loopless {α : Type*} (E : Set α) : (Matroid.freeOn E).Loopless := by
  rw [Matroid.loopless_iff_forall_isNonloop]
  intro e he
  exact Matroid.freeOn_isNonloop_iff.mpr he

noncomputable abbrev sample : Inputs.{u} where
  G := ULift.{u} ℤ
  group := inferInstance
  torsion := Function.Injective.isAddTorsionFree
    (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom
    (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).injective
  M := Matroid.freeOn {0}
  N := Matroid.freeOn {1}
  finiteM := ⟨by simp⟩
  finiteN := ⟨by simp⟩
  looplessM := free_loopless _
  looplessN := free_loopless _
  r := 1
  m := 1
  positive := by decide
  rankM := by simp [Matroid.eRank_freeOn]
  rankN := by simp [Matroid.eRank_freeOn]
  paving := free_paving _
  zero := by simp
  sizeM := by simp
  sizeN := by simp

private lemma sample_base : sample.{u}.M.IsBase sample.M.E := by
  simp [sample]

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h sample sample.M.E sample_base
  have hc := (hh.1.mp (show ¬ False from id)).1
  exact hc.not_indep (Matroid.freeOn_indep hc.subset_ground)

private lemma sample_matches : matchingReadout sample.{u} sample.M.E := by
  classical
  by_contra hn
  have hh := actual_positive sample sample.M.E sample_base
  have hc := (hh.1.mp hn).1
  exact hc.not_indep (Matroid.freeOn_indep hc.subset_ground)

private lemma sample_empty_not_matches : ¬ matchingReadout sample.{u} ∅ := by
  rintro ⟨T, hT, f, hf⟩
  have hTeq : T = {(1 : ULift.{u} ℤ)} := Matroid.freeOn_isBase_iff.mp hT
  subst T
  obtain ⟨s, hs⟩ := f.surjective ⟨(1 : ULift.{u} ℤ), by simp⟩
  exact s.property

noncomputable def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    cases i
    refine ⟨sample, sample.M.E, (∅ : Set sample.G), ?_⟩
    intro heq
    change matchingReadout sample sample.M.E = matchingReadout sample ∅ at heq
    exact sample_empty_not_matches (heq.mp sample_matches)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@basiswise_obstruction.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction.basiswise_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ P S => matchingReadout P S) (fun a => Empty.elim a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction
