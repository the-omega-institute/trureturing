import CFMPLiteralSixPairing1333Transient

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate

open D5.S3.Geometry.Gluing.LiteralSixPairingCandidate (literalPairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate (Vertex label cornerPairing)
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
  (Corner Slot b J cornerRel Follows)

-- Transient exact applications on the unchanged original corner quotient.
-- No canonical Lean admission or independent finite-instance result is claimed.

abbrev OriginalCorner := Corner (Fin 6)
abbrev Q := cornerPairing literalPairing

def representative (c : OriginalCorner) : OriginalCorner :=
  if c.2 = 3 then (0,3) else (0,0)

/-- Each entry is a list of actual (tetrahedron, omitted face, increasing corner slot). -/
def paths (c : OriginalCorner) : List (Slot (Fin 6)) :=
  (![![[], [((0,3),1), ((2,2),0), ((1,2),0)],
            [((0,0),1), ((2,3),1)], []],
      ![[((1,2),0)], [((1,2),1), ((0,0),1), ((2,3),1)],
            [((1,0),1)], [((1,2),2)]],
      ![[((2,2),0), ((1,2),0)], [((2,3),1)],
            [((2,3),2), ((0,0),1), ((2,3),1)], [((2,0),2)]],
      ![[((3,2),0), ((2,2),0), ((1,2),0)],
            [((3,3),1), ((5,2),0), ((4,3),0), ((1,2),0)],
            [((3,1),1), ((4,3),1), ((1,0),1)],
            [((3,2),2), ((2,0),2)]],
      ![[((4,3),0), ((1,2),0)], [((4,3),1), ((1,0),1)],
            [((4,3),2), ((1,2),1), ((0,0),1), ((2,3),1)],
            [((4,2),2), ((3,2),2), ((2,0),2)]],
      ![[((5,2),0), ((4,3),0), ((1,2),0)],
            [((5,3),1), ((3,2),0), ((2,2),0), ((1,2),0)],
            [((5,3),2), ((3,1),1), ((4,3),1), ((1,0),1)],
            [((5,0),2), ((3,2),2), ((2,0),2)]]] :
      Fin 6 → Fin 4 → List (Slot (Fin 6))) c.1 c.2

/-- Kernel checks each proposed path against the existing original Follows definition. -/
theorem paths_follow (c : OriginalCorner) : Follows Q c (representative c) (paths c) := by
  rcases c with ⟨t,v⟩
  fin_cases t <;> fin_cases v
  · change Follows Q (0,0) (0,0) []
    dsimp only [Follows] <;> decide
  · change Follows Q (0,1) (0,0) [((0,3),1), ((2,2),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (0,2) (0,0) [((0,0),1), ((2,3),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (0,3) (0,3) []
    dsimp only [Follows] <;> decide
  · change Follows Q (1,0) (0,0) [((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (1,1) (0,0) [((1,2),1), ((0,0),1), ((2,3),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (1,2) (0,0) [((1,0),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (1,3) (0,3) [((1,2),2)]
    dsimp only [Follows] <;> decide
  · change Follows Q (2,0) (0,0) [((2,2),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (2,1) (0,0) [((2,3),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (2,2) (0,0) [((2,3),2), ((0,0),1), ((2,3),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (2,3) (0,3) [((2,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows Q (3,0) (0,0) [((3,2),0), ((2,2),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (3,1) (0,0) [((3,3),1), ((5,2),0), ((4,3),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (3,2) (0,0) [((3,1),1), ((4,3),1), ((1,0),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (3,3) (0,3) [((3,2),2), ((2,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows Q (4,0) (0,0) [((4,3),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (4,1) (0,0) [((4,3),1), ((1,0),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (4,2) (0,0) [((4,3),2), ((1,2),1), ((0,0),1), ((2,3),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (4,3) (0,3) [((4,2),2), ((3,2),2), ((2,0),2)]
    dsimp only [Follows] <;> decide
  · change Follows Q (5,0) (0,0) [((5,2),0), ((4,3),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (5,1) (0,0) [((5,3),1), ((3,2),0), ((2,2),0), ((1,2),0)]
    dsimp only [Follows] <;> decide
  · change Follows Q (5,2) (0,0) [((5,3),2), ((3,1),1), ((4,3),1), ((1,0),1)]
    dsimp only [Follows] <;> decide
  · change Follows Q (5,3) (0,3) [((5,0),2), ((3,2),2), ((2,0),2)]
    dsimp only [Follows] <;> decide

/-- Every actual corner-slot transport preserves the original v=3 distinction. -/
theorem slot_side : ∀ i : Slot (Fin 6),
    (b i).2 = 3 ↔ (b (J Q i)).2 = 3 := by decide

theorem follows_related {c d : OriginalCorner} {is : List (Slot (Fin 6))}
    (h : Follows Q c d is) : Relation.EqvGen (cornerRel Q) c d := by
  induction is generalizing c with
  | nil =>
    change c = d at h
    subst d
    exact Relation.EqvGen.refl c
  | cons i is ih =>
    have hs : cornerRel Q c (b (J Q i)) := ⟨i,h.1,rfl⟩
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hs) (ih h.2)

theorem related_side {c d : OriginalCorner}
    (h : Relation.EqvGen (cornerRel Q) c d) : c.2 = 3 ↔ d.2 = 3 := by
  induction h with
  | rel c d h =>
    obtain ⟨i,rfl,rfl⟩ := h
    exact slot_side i
  | refl c => exact Iff.rfl
  | symm c d _ ih => exact ih.symm
  | trans c d e _ _ hcd hde => exact hcd.trans hde

theorem label_normalize (c : OriginalCorner) :
    label literalPairing c = label literalPairing (representative c) :=
  Quotient.sound (follows_related (paths_follow c))

/-- Exact necessary and sufficient condition on all twenty-four original inputs. -/
theorem label_eq_iff (c d : OriginalCorner) :
    label literalPairing c = label literalPairing d ↔ (c.2 = 3 ↔ d.2 = 3) := by
  constructor
  · intro h
    exact related_side (Quotient.exact h)
  · intro h
    have hr : representative c = representative d := by
      by_cases hc : c.2 = 3 <;> by_cases hd : d.2 = 3 <;>
        simp_all [representative]
    exact (label_normalize c).trans
      ((congrArg (label literalPairing) hr).trans (label_normalize d).symm)

theorem lower_coordinates (c : OriginalCorner) :
    label literalPairing c = label literalPairing (0,0) ↔ c.2.val < 3 := by
  have hfin : ∀ v : Fin 4, (v = 3 ↔ (0 : Fin 4) = 3) ↔ v.val < 3 := by decide
  exact (label_eq_iff c (0,0)).trans (hfin c.2)

theorem upper_coordinates (c : OriginalCorner) :
    label literalPairing c = label literalPairing (0,3) ↔ c.2 = 3 := by
  constructor
  · intro h
    exact ((label_eq_iff c (0,3)).mp h).mpr rfl
  · intro h
    exact (label_eq_iff c (0,3)).mpr ⟨fun _ => rfl, fun _ => h⟩

/-- The entire original lower fibre, retaining the original tetrahedron and vertex. -/
def lowerFiberEquiv :
    {c : OriginalCorner // label literalPairing c = label literalPairing (0,0)} ≃
      Fin 6 × Fin 3 where
  toFun c := (c.val.1, ⟨c.val.2.val, (lower_coordinates c.val).mp c.property⟩)
  invFun z := ⟨(z.1,z.2.castSucc),
    (lower_coordinates (z.1,z.2.castSucc)).mpr z.2.isLt⟩
  left_inv c := Subtype.ext (Prod.ext rfl (Fin.ext rfl))
  right_inv z := Prod.ext rfl (Fin.ext rfl)

/-- The entire original upper fibre, whose actual vertex coordinate is forced to three. -/
def upperFiberEquiv :
    {c : OriginalCorner // label literalPairing c = label literalPairing (0,3)} ≃
      Fin 6 where
  toFun c := c.val.1
  invFun t := ⟨(t,3),(upper_coordinates (t,3)).mpr rfl⟩
  left_inv c := Subtype.ext
    (Prod.ext rfl ((upper_coordinates c.val).mp c.property).symm)
  right_inv t := rfl

theorem representatives_ne :
    label literalPairing (0,0) ≠ label literalPairing (0,3) := by
  intro h
  have hside := (label_eq_iff (0,0) (0,3)).mp h
  exact (by decide : (0 : Fin 4) ≠ 3) (hside.mpr rfl)

/-- Every element of the original Vertex quotient is one of the two actual labels. -/
theorem vertex_two_classes (ν : Vertex literalPairing) :
    ν = label literalPairing (0,0) ∨ ν = label literalPairing (0,3) := by
  refine Quotient.inductionOn ν ?_
  intro c
  change label literalPairing c = label literalPairing (0,0) ∨
    label literalPairing c = label literalPairing (0,3)
  have hn := label_normalize c
  by_cases h : c.2 = 3
  · exact Or.inr (by simpa only [representative,if_pos h] using hn)
  · exact Or.inl (by simpa only [representative,if_neg h] using hn)

end D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.paths_follow,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.slot_side,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.follows_related,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.related_side,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.label_normalize,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.label_eq_iff,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.lower_coordinates,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.upper_coordinates,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.lowerFiberEquiv,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.upperFiberEquiv,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.representatives_ne,
      ``D5.S3.Geometry.Gluing.LiteralCornerFibersCandidate.vertex_two_classes] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1347 original corner fibre target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1347 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1347 CHECKED {name} axioms={axioms}"
