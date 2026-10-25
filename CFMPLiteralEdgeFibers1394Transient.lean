import CFMPLiteralSixPairing1333Transient
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (Occurrence faceEdge)
open D5.S3.Geometry.Gluing.LiteralSixPairingCandidate (literalPairing)

-- Temporary exact applications on the original edge quotient; no canonical admission.
abbrev O := Occurrence (Fin 6)
abbrev Port := (Fin 6 × Fin 4) × Fin 3

def classIndex (o : O) : Fin 3 :=
  (![![0,1,2,2,2,1], ![1,0,2,2,2,0], ![0,1,2,2,2,1],
      ![1,0,2,2,2,0], ![0,1,2,2,2,0], ![1,0,2,2,2,0]] :
      Fin 6 → Fin 6 → Fin 3) o.1 o.2

def representative (o : O) : O := (0,(classIndex o).castLE (by decide))

def paths (o : O) : List Port :=
  (![![[], [], [], [((0,0),0), ((2,2),2), ((1,0),0)], [((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((0,0),2), ((2,3),2)]],
    ![[((1,2),0)], [((1,1),0), ((2,3),0)], [((1,2),1)], [((1,0),0)], [((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((1,0),2)]],
    ![[((2,3),0)], [((2,3),1), ((0,0),2), ((2,3),2)], [((2,2),1), ((1,2),1)], [((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((2,2),2), ((1,0),0)], [((2,3),2)]],
    ![[((3,2),0), ((2,3),1), ((0,0),2), ((2,3),2)], [((3,1),0), ((4,3),0), ((1,1),0), ((2,3),0)], [((3,2),1), ((2,2),1), ((1,2),1)], [((3,1),2), ((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)], [((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((3,3),2), ((5,1),0), ((4,3),2), ((1,0),2)]],
    ![[((4,3),0), ((1,1),0), ((2,3),0)], [((4,3),1), ((1,2),0)], [((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)], [((4,0),0), ((5,0),0), ((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)], [((4,3),2), ((1,0),2)]],
    ![[((5,2),0), ((4,3),1), ((1,2),0)], [((5,1),0), ((4,3),2), ((1,0),2)], [((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)], [((5,0),0), ((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)], [((5,0),1), ((3,1),2), ((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)], [((5,0),2), ((3,3),2), ((5,1),0), ((4,3),2), ((1,0),2)]]] : Fin 6 → Fin 6 → List Port) o.1 o.2

def Follows (o z : O) : List Port → Prop
  | [] => o = z
  | (x,n)::ps => o = (x.1,faceEdge x.2 n) ∧
      Follows ((literalPairing.facePair x).1,
        faceEdge (literalPairing.facePair x).2 (literalPairing.faceMap x n)) z ps

theorem paths_follow (o : O) : Follows o (representative o) (paths o) := by
  rcases o with ⟨t,e⟩
  fin_cases t <;> fin_cases e
  · change Follows (0,0) (0,0) []
    dsimp only [Follows] <;> decide
  · change Follows (0,1) (0,1) []
    dsimp only [Follows] <;> decide
  · change Follows (0,2) (0,2) []
    dsimp only [Follows] <;> decide
  · change Follows (0,3) (0,2) [((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (0,4) (0,2) [((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (0,5) (0,1) [((0,0),2), ((2,3),2)]
    dsimp only [Follows] <;> decide
  · change Follows (1,0) (0,1) [((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows (1,1) (0,0) [((1,1),0), ((2,3),0)]
    dsimp only [Follows] <;> decide
  · change Follows (1,2) (0,2) [((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (1,3) (0,2) [((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (1,4) (0,2) [((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (1,5) (0,0) [((1,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows (2,0) (0,0) [((2,3),0)]
    dsimp only [Follows] <;> decide
  · change Follows (2,1) (0,1) [((2,3),1), ((0,0),2), ((2,3),2)]
    dsimp only [Follows] <;> decide
  · change Follows (2,2) (0,2) [((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (2,3) (0,2) [((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (2,4) (0,2) [((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (2,5) (0,1) [((2,3),2)]
    dsimp only [Follows] <;> decide
  · change Follows (3,0) (0,1) [((3,2),0), ((2,3),1), ((0,0),2), ((2,3),2)]
    dsimp only [Follows] <;> decide
  · change Follows (3,1) (0,0) [((3,1),0), ((4,3),0), ((1,1),0), ((2,3),0)]
    dsimp only [Follows] <;> decide
  · change Follows (3,2) (0,2) [((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (3,3) (0,2) [((3,1),2), ((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (3,4) (0,2) [((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (3,5) (0,0) [((3,3),2), ((5,1),0), ((4,3),2), ((1,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows (4,0) (0,0) [((4,3),0), ((1,1),0), ((2,3),0)]
    dsimp only [Follows] <;> decide
  · change Follows (4,1) (0,1) [((4,3),1), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows (4,2) (0,2) [((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (4,3) (0,2) [((4,0),0), ((5,0),0), ((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (4,4) (0,2) [((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (4,5) (0,0) [((4,3),2), ((1,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows (5,0) (0,1) [((5,2),0), ((4,3),1), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows (5,1) (0,0) [((5,1),0), ((4,3),2), ((1,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows (5,2) (0,2) [((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (5,3) (0,2) [((5,0),0), ((3,2),2), ((2,0),0), ((0,2),2), ((1,2),2), ((0,0),0), ((2,2),2), ((1,0),0)]
    dsimp only [Follows] <;> decide
  · change Follows (5,4) (0,2) [((5,0),1), ((3,1),2), ((4,0),1), ((5,2),1), ((4,2),1), ((3,2),1), ((2,2),1), ((1,2),1)]
    dsimp only [Follows] <;> decide
  · change Follows (5,5) (0,0) [((5,0),2), ((3,3),2), ((5,1),0), ((4,3),2), ((1,0),2)]
    dsimp only [Follows] <;> decide

theorem follows_related {o z : O} {ps : List Port} (h : Follows o z ps) :
    Relation.EqvGen literalPairing.edgeStep o z := by
  induction ps generalizing o with
  | nil =>
    change o = z at h
    subst z
    exact Relation.EqvGen.refl o
  | cons p ps ih =>
    rcases p with ⟨x,n⟩
    have hs : literalPairing.edgeStep o
        ((literalPairing.facePair x).1,
          faceEdge (literalPairing.facePair x).2 (literalPairing.faceMap x n)) :=
      ⟨x,n,h.1,rfl⟩
    exact (Relation.EqvGen.rel _ _ hs).trans _ _ _ (ih h.2)

theorem slot_class : ∀ (x : Fin 6 × Fin 4) (n : Fin 3),
    classIndex (x.1,faceEdge x.2 n) =
      classIndex ((literalPairing.facePair x).1,
        faceEdge (literalPairing.facePair x).2 (literalPairing.faceMap x n)) := by decide

theorem related_class {o z : O} (h : Relation.EqvGen literalPairing.edgeStep o z) :
    classIndex o = classIndex z := by
  induction h with
  | rel o z h =>
    obtain ⟨x,n,rfl,rfl⟩ := h
    exact slot_class x n
  | refl o => rfl
  | symm o z _ ih => exact ih.symm
  | trans o z w _ _ ho hw => exact ho.trans hw

theorem label_normalize (o : O) :
    literalPairing.edgeLabel o.1 o.2 =
      literalPairing.edgeLabel (representative o).1 (representative o).2 :=
  Quotient.sound (follows_related (paths_follow o))

theorem label_eq_iff (o z : O) :
    literalPairing.edgeLabel o.1 o.2 = literalPairing.edgeLabel z.1 z.2 ↔
      classIndex o = classIndex z := by
  constructor
  · intro h
    exact related_class (Quotient.exact h)
  · intro h
    have hr : representative o = representative z := by simp only [representative,h]
    exact (label_normalize o).trans
      ((congrArg (fun x : O => literalPairing.edgeLabel x.1 x.2) hr).trans
        (label_normalize z).symm)

def wholeFiberEquiv (i : Fin 3) :
    {o : O // literalPairing.edgeLabel o.1 o.2 =
      literalPairing.edgeLabel 0 (i.castLE (by decide))} ≃
    {o : O // classIndex o = i} where
  toFun o := ⟨o.val, by
    have hi : classIndex (0,i.castLE (by decide)) = i := by fin_cases i <;> decide
    exact ((label_eq_iff _ _).mp o.property).trans hi⟩
  invFun o := ⟨o.val, by
    apply (label_eq_iff o.val (0,i.castLE (by decide))).mpr
    have hi : classIndex (0,i.castLE (by decide)) = i := by fin_cases i <;> decide
    exact o.property.trans hi.symm⟩
  left_inv o := Subtype.ext rfl
  right_inv o := Subtype.ext rfl

theorem original_fiber_card (i : Fin 3) :
    Nat.card {o : O // literalPairing.edgeLabel o.1 o.2 =
      literalPairing.edgeLabel 0 (i.castLE (by decide))} = (![10,8,18] : Fin 3 → ℕ) i := by
  rw [Nat.card_congr (wholeFiberEquiv i), Nat.card_eq_fintype_card]
  fin_cases i <;> decide

end D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.paths_follow,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.follows_related,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.slot_class,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.related_class,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.label_normalize,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.label_eq_iff,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.wholeFiberEquiv,
      ``D5.S3.Geometry.Gluing.LiteralEdgeFibers1394Candidate.original_fiber_card] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1394 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1394 disallowed {ax}"
    Lean.logInfo m!"CFMP1394 CHECKED {name} axioms={axioms}"
