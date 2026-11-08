/- GID: D5/S3/Topology/CupCapComposition
   generality: G
   mirror-B: D5/B/S3/Topology/CupCapComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Explicit generator paths in the literal glued matching network. -/
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition

set_option autoImplicit false
noncomputable section
namespace D5.S3.Topology.CupCapComposition
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition

private theorem _root_.Relation.EqvGen.pathTrans {X : Type*} {r : X → X → Prop} {x y z : X}
    (h : Relation.EqvGen r x y) (k : Relation.EqvGen r y z) : Relation.EqvGen r x z :=
  .trans _ _ _ h k

private theorem _root_.Relation.EqvGen.pathSymm {X : Type*} {r : X → X → Prop} {x y : X}
    (h : Relation.EqvGen r x y) : Relation.EqvGen r y x := .symm _ _ h

variable {n : ℕ} (j : ℕ) (hj : j+1 < n) (d : Matching (Boundary n))

private def leftPort : Boundary n := (false, ⟨j, by omega⟩)
private def rightPort : Boundary n := (false, ⟨j+1, hj⟩)
private abbrev G := halfEdgeStep (cupcapMatching j hj) d

private theorem mate_path (x : Piece n) :
    Relation.EqvGen (G j hj d) x (piecesMate (cupcapMatching j hj) d x) :=
  .rel _ _ (Or.inl rfl)

private theorem seam_path (x : Piece n) :
    Relation.EqvGen (G j hj d) x (seamMate x) := .rel _ _ (Or.inr rfl)

private theorem port_ne : leftPort j hj ≠ rightPort j hj := by
  intro h
  have := congrArg (fun x => x.2.val) h
  dsimp [leftPort, rightPort] at this
  omega

private theorem access (x : Boundary n) (ha : x ≠ leftPort j hj) (hb : x ≠ rightPort j hj) :
    Relation.EqvGen (G j hj d) (outerPiece x) (true,x) := by
  rcases x with ⟨b,i⟩
  cases b
  · have hi : i.val ≠ j := by
      intro h; apply ha; exact Prod.ext rfl (Fin.ext h)
    have hi' : i.val ≠ j+1 := by
      intro h; apply hb; exact Prod.ext rfl (Fin.ext h)
    have hp : Relation.EqvGen (G j hj d) (outerPiece (false,i)) (false,(true,i)) := by
      simpa only [piecesMate, cupcapMatching, cupcapMate, hi, hi',
        ite_false, Bool.not_false, outerPiece] using mate_path j hj d (false,(false,i))
    exact hp.pathTrans (seam_path j hj d (false,(true,i)))
  · exact .refl _

private theorem seam_cap :
    Relation.EqvGen (G j hj d) (true,leftPort j hj) (true,rightPort j hj) := by
  have hp : piecesMate (cupcapMatching j hj) d (false,(true,⟨j,by omega⟩)) =
      (false,(true,⟨j+1,hj⟩)) := by
    simp [piecesMate, cupcapMatching, cupcapMate]
  have hm : Relation.EqvGen (G j hj d) (false,(true,⟨j,by omega⟩))
      (false,(true,⟨j+1,hj⟩)) := by
    simpa only [hp] using mate_path j hj d (false,(true,⟨j,by omega⟩))
  exact (seam_path j hj d (true,leftPort j hj)).pathTrans
    (hm.pathTrans (seam_path j hj d (false,(true,⟨j+1,hj⟩))))

/-- Partner reconnection after adding the generator's top cup. -/
def reconnected (x : Boundary n) : Boundary n :=
  if x = leftPort j hj then rightPort j hj else
  if x = rightPort j hj then leftPort j hj else
  if d.mate x = leftPort j hj then d.mate (rightPort j hj) else
  if d.mate x = rightPort j hj then d.mate (leftPort j hj) else d.mate x

private theorem mate_injective : Function.Injective d.mate := d.involutive.injective

private theorem reconnected_path (x : Boundary n) :
    Relation.EqvGen (G j hj d) (outerPiece x) (outerPiece (reconnected j hj d x)) := by
  unfold reconnected
  split_ifs with ha hb hma hmb
  · subst x
    have hp : piecesMate (cupcapMatching j hj) d (outerPiece (leftPort j hj)) =
        outerPiece (rightPort j hj) := by simp [piecesMate, cupcapMatching, cupcapMate, leftPort, rightPort, outerPiece]
    simpa only [hp] using mate_path j hj d (outerPiece (leftPort j hj))
  · subst x
    have hp : piecesMate (cupcapMatching j hj) d (outerPiece (rightPort j hj)) =
        outerPiece (leftPort j hj) := by simp [piecesMate, cupcapMatching, cupcapMate, leftPort, rightPort, outerPiece]
    simpa only [hp] using mate_path j hj d (outerPiece (rightPort j hj))
  · have hda : d.mate (rightPort j hj) ≠ leftPort j hj := by
      intro h
      apply hb
      exact mate_injective d (hma.trans h.symm)
    have hdb : d.mate (rightPort j hj) ≠ rightPort j hj := d.fixedPointFree _
    have hm : Relation.EqvGen (G j hj d) (true,x) (true,leftPort j hj) := by
      simpa only [piecesMate, hma] using mate_path j hj d (true,x)
    exact (access j hj d x ha hb).pathTrans
      (hm.pathTrans
        ((seam_cap j hj d).pathTrans
          ((mate_path j hj d (true,rightPort j hj)).pathTrans
            (access j hj d _ hda hdb).pathSymm)))
  · have hda : d.mate (leftPort j hj) ≠ leftPort j hj := d.fixedPointFree _
    have hdb : d.mate (leftPort j hj) ≠ rightPort j hj := by
      intro h
      apply ha
      exact mate_injective d (hmb.trans h.symm)
    have hm : Relation.EqvGen (G j hj d) (true,x) (true,rightPort j hj) := by
      simpa only [piecesMate, hmb] using mate_path j hj d (true,x)
    exact (access j hj d x ha hb).pathTrans
      (hm.pathTrans
        ((seam_cap j hj d).pathSymm.pathTrans
          ((mate_path j hj d (true,leftPort j hj)).pathTrans
            (access j hj d _ hda hdb).pathSymm)))
  · exact (access j hj d x ha hb).pathTrans
      ((mate_path j hj d (true,x)).pathTrans (access j hj d _ hma hmb).pathSymm)

private theorem reconnected_free (x : Boundary n) : reconnected j hj d x ≠ x := by
  unfold reconnected
  split_ifs with ha hb hma hmb
  · rw [ha]; exact (port_ne j hj).symm
  · rw [hb]; exact port_ne j hj
  · intro h
    have he := congrArg d.mate h
    rw [d.involutive, hma] at he
    exact port_ne j hj he.symm
  · intro h
    have he := congrArg d.mate h
    rw [d.involutive, hmb] at he
    exact port_ne j hj he
  · exact d.fixedPointFree x

/-- The local rewiring is exactly the path-defined composite, for every matching. -/
theorem composite_cupcap_mate (x : Boundary n) :
    (composite (cupcapMatching j hj) d).mate x = reconnected j hj d x := by
  have h := (composite_component_iff (cupcapMatching j hj) d x
    (reconnected j hj d x)).mp (Quotient.sound (reconnected_path j hj d x))
  exact (h.resolve_left (reconnected_free j hj d x)).symm

private theorem no_loop_access (hn : d.mate (leftPort j hj) ≠ rightPort j hj)
    (x : Boundary n) :
    ∃ a, Relation.EqvGen (G j hj d) (true,x) (outerPiece a) := by
  by_cases ha : x = leftPort j hj
  · subst x
    exact ⟨_,(mate_path j hj d (true,leftPort j hj)).pathTrans
      (access j hj d _ (d.fixedPointFree _) hn).pathSymm⟩
  by_cases hb : x = rightPort j hj
  · subst x
    have hna : d.mate (rightPort j hj) ≠ leftPort j hj := by
      intro h
      apply hn
      exact (congrArg d.mate h).symm.trans (d.involutive _)
    exact ⟨_,(mate_path j hj d (true,rightPort j hj)).pathTrans
      (access j hj d _ hna (d.fixedPointFree _)).pathSymm⟩
  exact ⟨x,(access j hj d x ha hb).pathSymm⟩

/-- A generator creates no internal loop when its two input ports are unpaired. -/
theorem internalLoopCount_cupcap_zero (hn : d.mate (leftPort j hj) ≠ rightPort j hj) :
    internalLoopCount (cupcapMatching j hj) d = 0 := by
  have he : IsEmpty (halfEdgeInternalComponent (cupcapMatching j hj) d) := by
    constructor
    rintro ⟨c,hc⟩
    induction c using Quotient.inductionOn with
    | _ x =>
      obtain ⟨l,b,i⟩ := x
      have h : ∃ a, Relation.EqvGen (G j hj d) (l,(b,i)) (outerPiece a) := by
        cases l
        · cases b
          · exact ⟨(false,i),.refl _⟩
          · obtain ⟨a,ha⟩ := no_loop_access j hj d hn (false,i)
            exact ⟨a,(seam_path j hj d (false,(true,i))).pathTrans ha⟩
        · exact no_loop_access j hj d hn (b,i)
      obtain ⟨a,ha⟩ := h
      exact hc a (Quotient.sound ha).symm
  exact Nat.card_eq_zero.mpr (Or.inl he)

private def patch (x : Piece n) : Prop :=
  if x.1 then x.2 = leftPort j hj ∨ x.2 = rightPort j hj else
    x.2 = (true,⟨j,by omega⟩) ∨ x.2 = (true,⟨j+1,hj⟩)

private theorem paired_invariance (hp : d.mate (leftPort j hj) = rightPort j hj)
    (x : Boundary n) :
    (d.mate x = leftPort j hj ∨ d.mate x = rightPort j hj) ↔
      (x = leftPort j hj ∨ x = rightPort j hj) := by
  have hq : d.mate (rightPort j hj) = leftPort j hj :=
    (congrArg d.mate hp).symm.trans (d.involutive _)
  constructor
  · rintro (h | h)
    · exact Or.inr (d.involutive x |>.symm.trans ((congrArg d.mate h).trans hp))
    · exact Or.inl (d.involutive x |>.symm.trans ((congrArg d.mate h).trans hq))
  · rintro (rfl | rfl)
    · exact Or.inr hp
    · exact Or.inl hq

private def patchColoring (hp : d.mate (leftPort j hj) = rightPort j hj) :
    Coloring (G j hj d) Prop := by
  refine ⟨patch j hj, ?_⟩
  intro x y h
  rcases h with rfl | rfl
  · rcases x with ⟨l,b,i⟩
    cases l
    · by_cases hi : i.val = j
      · cases b <;> simp [patch, piecesPerm, piecesMate, cupcapMatching, cupcapMate,
          hi, leftPort, rightPort, Prod.ext_iff, Fin.ext_iff]
      · by_cases hi' : i.val = j+1
        · cases b <;> simp [patch, piecesPerm, piecesMate, cupcapMatching, cupcapMate,
            hi, hi', leftPort, rightPort, Prod.ext_iff, Fin.ext_iff]
        · cases b <;> simp [patch, piecesPerm, piecesMate, cupcapMatching, cupcapMate,
            hi, hi', leftPort, rightPort, Prod.ext_iff, Fin.ext_iff]
    · exact propext (paired_invariance j hj d hp (b,i)).symm
  · change patch j hj x = patch j hj (seamMate x)
    rcases x with ⟨l,b,i⟩
    cases l <;> cases b <;> simp [patch, seamMate, leftPort, rightPort]

/-- Pairing the two generator inputs creates a closed internal component. -/
theorem internalLoopCount_cupcap_pos (hp : d.mate (leftPort j hj) = rightPort j hj) :
    0 < internalLoopCount (cupcapMatching j hj) d := by
  have hn : Nonempty (halfEdgeInternalComponent (cupcapMatching j hj) d) := by
    refine ⟨⟨component (G j hj d) (true,leftPort j hj), ?_⟩⟩
    intro a h
    have hc := coloring_respects (patchColoring j hj d hp) (Quotient.exact h)
    have ht : patch j hj (true,leftPort j hj) := by simp [patch]
    have hf : ¬ patch j hj (outerPiece a) := by
      rcases a with ⟨b,i⟩
      cases b <;> simp [patch, outerPiece, leftPort, rightPort]
    exact hf (hc.mpr ht)
  exact Nat.card_pos_iff.mpr ⟨hn,inferInstance⟩

/-- The generator creates a loop exactly when its two top inputs are paired. -/
theorem internalLoopCount_cupcap_eq_zero_iff :
    internalLoopCount (cupcapMatching j hj) d = 0 ↔
      d.mate (false,⟨j,by omega⟩) ≠ (false,⟨j+1,hj⟩) := by
  constructor
  · intro h hp
    have := internalLoopCount_cupcap_pos j hj d hp
    omega
  · exact internalLoopCount_cupcap_zero j hj d

end D5.S3.Topology.CupCapComposition
