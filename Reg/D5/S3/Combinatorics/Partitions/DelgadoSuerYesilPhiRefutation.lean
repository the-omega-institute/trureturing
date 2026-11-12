import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation

private def ordinary : NumericalSet := ⟨{1}, by simp, by simp⟩
private def twoGaps : NumericalSet := ⟨{2,3}, by simp, by simp⟩

private theorem ordinary_semigroup : Semigroup ordinary := by
  intro a b ha hb
  change a ≠ 1 at ha
  change b ≠ 1 at hb
  change a + b ≠ 1
  omega

private theorem twoGaps_one : 1 ∈ phi twoGaps := by
  have hF : frobenius twoGaps = 3 := by decide
  have hp : ¬ PseudoFrobenius twoGaps 2 := by
    intro h
    have hc := h.2 1 (by decide) (by simp [members, twoGaps])
    simpa [members, twoGaps] using hc
  have hR : retainedRows twoGaps = twoGaps.gaps := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    simp only [twoGaps, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Or.inr hp
    · exact Or.inl hF.symm
  change 1 ∉ deleteRows twoGaps (retainedRows twoGaps)
  rw [hR]
  simp [deleteRows, twoGaps]

abbrev signature : Signature where
  Params := Unit
  State _ := NumericalSet
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ U => phi U) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law f := ∀ U : NumericalSet, Semigroup U → 1 ∉ f.readout () () U

private theorem bad : ¬ arena.Law rejected := by
  intro h
  exact h ordinary ordinary_semigroup (Set.mem_univ _)

def family : Registration arena (type_of% @phi_omits_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@phi_omits_one, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := by
    intro i
    refine ⟨(), ordinary, twoGaps, ?_⟩
    intro h
    have hmem : 1 ∈ phi ordinary := by
      change phi ordinary = phi twoGaps at h
      rw [h]
      exact twoGaps_one
    exact phi_omits_one ordinary ordinary_semigroup hmem

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phi_omits_one) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.phi_omits_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
