/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Wheel
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Wheel
   mirror-E: none(waiver:original-label-two-sum-wheel)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: The original four-rim-wheel Gamma and two fillings are native evolving free-pair sequences with a separate collar. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates

/-! UNCOMPILED. Labels 1,2,3,4 are the literal right tree labels. Ambient label
0 is outside the ground; it is never silently inserted into any face. Finite
proofs use kernel `decide`, never `native_decide` or a Python theorem oracle. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.Wheel
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
abbrev Label := Fin 5

def Y : Finset Label := {1,2,3,4}
def R : Finset Label := {1,2}
def Z : Finset Label := {3,4}
def E : Family Label := facets {{1,4},{1,2},{2,3}}
def A0 : Family Label := delta {3} ⊔ delta {4}
def A1 : Family Label := E ⊔ delta Z
def B1 : Family Label := A1 ⊔ delta {1,2,3}

private def lowers : List (Finset Label) :=
  [{1,2,4},{2,4},{3,4},{1,3}]
private def apices : List Label := [3,3,1,2]
private def lower (i : Fin 4) : Finset Label := lowers[i.val]'(by
  simp [lowers]; exact i.isLt)
private def apex (i : Fin 4) : Label := apices[i.val]'(by
  simp [apices]; exact i.isLt)
private def state (n : Nat) : Family Label := cut (delta Y) ((lowers.take n).toFinset)

private theorem pairFacts : ∀ i : Fin 4,
    (lower i).Nonempty ∧ apex i ∉ lower i ∧
      insert (apex i) (lower i) ∈ state i.val ∧
        ∀ s ∈ state i.val, lower i ⊆ s →
          s = lower i ∨ s = insert (apex i) (lower i) := by
  decide

private def pair (i : Fin 4) : CollapsePair Label :=
  emitPair (state i.val) (lower i) (apex i) (pairFacts i).1
    (pairFacts i).2.1 (pairFacts i).2.2.1 (pairFacts i).2.2.2

private theorem next : ∀ i : Fin 4,
    (pair i).retained = project (state (i.val+1)) := by
  intro i
  rw [pair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;>
    simp [state,lowers,lower,cut,Finset.mem_insert,Finset.mem_union]

private def step (i : Fin 4) :
    Sequence (project (state i.val)) (project (state (i.val+1))) :=
  (Sequence.step (pair i) (Sequence.refl (pair i).retained)).cast rfl (next i)

private theorem finalState : state 4 = E := by
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ state 4 ↔ s ∈ E)

/-- All four ORIGINAL Gamma pairs, in their actual evolving complexes. -/
def gamma : Sequence (project (delta Y)) (project E) :=
  ((((step 0).append (step 1)).append (step 2)).append (step 3)).cast
    (by simp [state]) (congrArg project finalState)

/-- Ordered extraction uses the real native pairs. -/
theorem gamma_pairs : gamma.pairs.map (fun P => (P.lower,P.upper)) =
    [({1,2,4},{1,2,3,4}),({2,4},{2,3,4}),
      ({3,4},{1,3,4}),({1,3},{1,2,3})] := by
  simp [gamma,step,Sequence.pairs_append,Sequence.pairs_cast,Sequence.pairs,
    pair,emitPair,lower,apex,lowers,apices,CollapsePair.upper]

/-- A0 is E intersect the original Z-simplex; A1 retains the e-row simplex. -/
theorem interface_equations :
    Z = Y \ R ∧ A0 = E ⊓ delta Z ∧ A1 = E ⊔ delta Z := by
  refine ⟨by decide,?_,rfl⟩
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ A0 ↔ s ∈ E ⊓ delta Z)

/-- No pair at all in either list of filling zero. -/
def fill0 : Filling Z A0 where
  empty_mem := by decide
  collar := A0
  critical := {{3,4}}
  contains := le_rfl
  supported := by decide
  critical_supported := by decide
  cells := by constructor <;> decide
  main := (Sequence.refl (project (delta Z))).cast rfl (by
    congr 1
    apply SetLike.ext
    exact (by decide : ∀ s : Finset Label,
      s ∈ delta Z ↔ s ∈ endpoint A0 {{3,4}}))
  separate := Sequence.refl _

private def collarPair : CollapsePair Label :=
  emitPair B1 {1,3} 2 (by decide) (by decide) (by decide) (by decide)

private theorem collarRetained : collarPair.retained = project A1 := by
  rw [collarPair,emitPair_retained]
  congr 1
  apply SetLike.ext
  exact (by decide : ∀ s : Finset Label, s ∈ cut B1 {{1,3}} ↔ s ∈ A1)

/-- The collar pair is on B1 alone, while the main endpoint also contains 134. -/
def fill1 : Filling Y A1 where
  empty_mem := by decide
  collar := B1
  critical := {{1,3,4}}
  contains := le_sup_left
  supported := by decide
  critical_supported := by decide
  cells := by constructor <;> decide
  main := ((step 0).append (step 1)).cast (by simp [state]) (by
    congr 1
    apply SetLike.ext
    exact (by decide : ∀ s : Finset Label,
      s ∈ state 2 ↔ s ∈ endpoint B1 {{1,3,4}}))
  separate := (Sequence.step collarPair (Sequence.refl _)).cast rfl collarRetained

/-- A concrete obstruction to performing the collar pair in the whole endpoint:
two distinct strict cofaces remain there. -/
theorem collar_not_free_in_main :
    ({1,3} : Finset Label) ⊂ {1,2,3} ∧
    ({1,3} : Finset Label) ⊂ {1,3,4} ∧
    ({1,2,3} : Finset Label) ∈ endpoint B1 {{1,3,4}} ∧
    ({1,3,4} : Finset Label) ∈ endpoint B1 {{1,3,4}} ∧
    ({1,2,3} : Finset Label) ≠ {1,3,4} := by decide

private def coreLowers : List (Finset Label) := [{3},{2},{4}]
private def coreApices : List Label := [2,1,1]
private def coreState (n : Nat) : Family Label := cut E (coreLowers.take n).toFinset
private def coreLower (i : Fin 3) := coreLowers[i.val]'(by simp [coreLowers]; exact i.isLt)
private def coreApex (i : Fin 3) := coreApices[i.val]'(by simp [coreApices]; exact i.isLt)
private theorem coreFacts : ∀ i : Fin 3,
    (coreLower i).Nonempty ∧ coreApex i ∉ coreLower i ∧
      insert (coreApex i) (coreLower i) ∈ coreState i.val ∧
        ∀ s ∈ coreState i.val, coreLower i ⊆ s →
          s = coreLower i ∨ s = insert (coreApex i) (coreLower i) := by decide
private def corePair (i : Fin 3) :=
  emitPair (coreState i.val) (coreLower i) (coreApex i) (coreFacts i).1
    (coreFacts i).2.1 (coreFacts i).2.2.1 (coreFacts i).2.2.2
private theorem coreNext : ∀ i : Fin 3,
    (corePair i).retained = project (coreState (i.val+1)) := by
  intro i
  rw [corePair,emitPair_retained]
  congr 1
  fin_cases i <;> apply SetLike.ext <;> intro s <;>
    simp [coreState,coreLowers,coreLower,cut]
private def coreStep (i : Fin 3) :
    Sequence (project (coreState i.val)) (project (coreState (i.val+1))) :=
  (Sequence.step (corePair i) (Sequence.refl _)).cast rfl (coreNext i)

/-- The wheel's absolute certificate is a consumer of the same path E. -/
def certificate : Certificate Y A1 where
  supported := by decide
  core := E
  critical := {{3,4}}
  vertex := 1
  vertex_mem := by decide
  core_supported := by decide
  critical_supported := by decide
  cells := by constructor <;> decide
  main := (Sequence.refl (project A1)).cast rfl (by
    congr 1; apply SetLike.ext
    exact (by decide : ∀ s : Finset Label, s ∈ A1 ↔ s ∈ endpoint E {{3,4}}))
  separate := (((coreStep 0).append (coreStep 1)).append (coreStep 2)).cast
    (by simp [coreState]) (by
      congr 1; apply SetLike.ext
      exact (by decide : ∀ s : Finset Label, s ∈ coreState 3 ↔ s ∈ delta {1}))

end D5.S3.Geometry.OriginalLabelTwoSum.Wheel

namespace D5.S3.Geometry.OriginalLabelTwoSum.K4
open FiniteRelativeSimplicialCollapse
abbrev SeedLabel := Fin 3
/-- p=0,u=1,v=2; no label is globally removed as a ghost. -/
def root : Family SeedLabel := facets {{0},{1},{2}}
def seed : Certificate (Finset.univ : Finset SeedLabel) root where
  supported := by decide
  core := delta {0}
  critical := {{1},{2}}
  vertex := 0
  vertex_mem := by decide
  core_supported := by decide
  critical_supported := by decide
  cells := by constructor <;> decide
  main := (Sequence.refl (project root)).cast rfl (by
    congr 1; apply SetLike.ext
    exact (by decide : ∀ s : Finset SeedLabel,
      s ∈ root ↔ s ∈ endpoint (delta {0}) {{1},{2}}))
  separate := Sequence.refl _
end D5.S3.Geometry.OriginalLabelTwoSum.K4
