/- GID: D5/S3/ConceptDynamics/Coding/FiberBinaryIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiberBinaryIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Arbitrary binary questions identify finite fiber targets at logarithmic depth. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.BitVec
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `Concept` supplies the canonical source readout type
     and is imported rather than redeclared.
   * Exact pinned-Mathlib hits `Nat.le_pow_clog`, `BitVec.equivFin`,
     `Fin.castLE_injective`, `Finset.equivFin`, `Finset.le_sup`, and
     `Fintype.card_coe` construct injective fixed-length codes directly.
   * Searches of D5 and pinned Mathlib found no finite adaptive binary protocol
     with transcript consistency and this per-fiber target-identification bound.
     Mathlib's generic binary trees provide no matching coding theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A finite binary protocol selects each round's binary readout from the
preceding output history and records a transcript consistent with those choices. -/
structure BinaryProtocol (X : Type*) (depth : Nat) where
  transcript : Concept X (BitVec depth)
  question : (round : Fin depth) -> (Fin round.val -> Bool) -> Concept X Bool
  transcript_consistent : forall x round,
    (transcript x).getLsb round =
      question round
        (fun earlier => (transcript x).getLsb
          ⟨earlier.val, earlier.isLt.trans round.isLt⟩) x

/-- Target values realized inside one current concept fiber. -/
noncomputable def fiberTargetValues {X C Target : Type*} [Fintype X]
    (q_C : Concept X C) (target : Concept X Target) (coordinate : C) :
    Finset Target := by
  classical
  exact (Finset.univ.filter fun x => q_C x = coordinate).image target

/-- The number of distinct target values in one current concept fiber. -/
noncomputable def fiberTargetDiversity {X C Target : Type*} [Fintype X]
    (q_C : Concept X C) (target : Concept X Target) (coordinate : C) : Nat :=
  (fiberTargetValues q_C target coordinate).card

/-- The largest target diversity among all current concept fibers. Empty
coordinate carriers have diversity zero. -/
noncomputable def worstFiberDiversity {X C Target : Type*}
    [Fintype X] [Fintype C]
    (q_C : Concept X C) (target : Concept X Target) : Nat := by
  classical
  exact Finset.univ.sup (fiberTargetDiversity q_C target)

/-- A protocol identifies a target given the already-known current concept
when equal current coordinates and equal transcripts force equal targets. -/
def IdentifiesGiven {X C Target : Type*} {depth : Nat}
    (q_C : Concept X C) (target : Concept X Target)
    (protocol : BinaryProtocol X depth) : Prop :=
  forall x y, q_C x = q_C y ->
    protocol.transcript x = protocol.transcript y -> target x = target y

/-- With arbitrary binary questions, per-fiber fixed-length target codes give
an exact-identification protocol at the ceiling binary-logarithm depth. -/
theorem arbitrary_binary_questions_identify_target
    {X C Target : Type*} [Fintype X] [Fintype C] [Fintype Target]
    (q_C : Concept X C) (target : Concept X Target) :
    exists protocol : BinaryProtocol X
        (Nat.clog 2 (worstFiberDiversity q_C target)),
      IdentifiesGiven q_C target protocol := by
  classical
  let depth := Nat.clog 2 (worstFiberDiversity q_C target)
  let values : C -> Finset Target := fiberTargetValues q_C target
  have hcard (coordinate : C) : (values coordinate).card <= 2 ^ depth := by
    calc
      (values coordinate).card = fiberTargetDiversity q_C target coordinate := rfl
      _ <= worstFiberDiversity q_C target :=
        Finset.le_sup (f := fiberTargetDiversity q_C target)
          (Finset.mem_univ coordinate)
      _ <= 2 ^ depth := by
        simpa [depth] using
          Nat.le_pow_clog (b := 2) (by decide) (worstFiberDiversity q_C target)
  let encode : C -> Target -> BitVec depth := fun coordinate value =>
    if member : value ∈ values coordinate then
      BitVec.equivFin.symm
        (Fin.castLE (hcard coordinate)
          ((values coordinate).equivFin ⟨value, member⟩))
    else 0
  have encode_injective_on_values (coordinate : C) :
      Set.InjOn (encode coordinate) (values coordinate) := by
    intro left left_mem right right_mem equalCodes
    change left ∈ values coordinate at left_mem
    change right ∈ values coordinate at right_mem
    dsimp only [encode] at equalCodes
    simp only [dif_pos left_mem, dif_pos right_mem] at equalCodes
    have equalMembers :
        (⟨left, left_mem⟩ : values coordinate) = ⟨right, right_mem⟩ := by
      apply (values coordinate).equivFin.injective
      apply Fin.castLE_injective (hcard coordinate)
      exact BitVec.equivFin.symm.injective equalCodes
    exact congrArg Subtype.val equalMembers
  have target_mem_values (x : X) : target x ∈ values (q_C x) := by
    dsimp only [values, fiberTargetValues]
    apply Finset.mem_image.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩, rfl⟩
  let code : X -> BitVec depth := fun x => encode (q_C x) (target x)
  let protocol : BinaryProtocol X depth :=
    { transcript := code
      question := fun round _history x => (code x).getLsb round
      transcript_consistent := by
        intro x round
        rfl }
  refine ⟨protocol, ?_⟩
  intro x y sameCoordinate sameTranscript
  change code x = code y at sameTranscript
  dsimp only [code] at sameTranscript
  have target_y_mem : target y ∈ values (q_C x) := by
    rw [sameCoordinate]
    exact target_mem_values y
  have sameCode : encode (q_C x) (target x) = encode (q_C x) (target y) := by
    simpa only [sameCoordinate] using sameTranscript
  exact encode_injective_on_values (q_C x)
    (target_mem_values x) target_y_mem sameCode

/-- A two-valued target in one constant current fiber is covered by the general
binary-question construction. -/
example :
    exists protocol : BinaryProtocol Bool
        (Nat.clog 2
          (worstFiberDiversity (fun _ : Bool => ()) (id : Concept Bool Bool))),
      IdentifiesGiven (fun _ : Bool => ()) (id : Concept Bool Bool) protocol := by
  exact arbitrary_binary_questions_identify_target (fun _ : Bool => ()) id

#print axioms arbitrary_binary_questions_identify_target

end D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
