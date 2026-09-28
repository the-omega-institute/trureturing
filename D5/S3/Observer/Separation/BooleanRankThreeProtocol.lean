/- GID: D5/S3/Observer/Separation/BooleanRankThreeProtocol
   generality: I
   mirror-B: D5/B/S3/Observer/Separation/BooleanRankThreeProtocol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/Separation/BooleanRankThreeProtocol.claim; result=D5/S3/Observer/Separation/BooleanRankThreeProtocol.result; claim=D5/S3/Observer/Separation/BooleanRankThreeProtocol.claim
   digest: A Boolean rank-three task admits three messages per side while all four whole-class deletions remain unbalanced. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace D5.S3.Observer.Separation.BooleanRankThreeProtocol

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

abbrev X := Fin 8
abbrev Y := Fin 6
abbrev Vertex := X ⊕ Y
abbrev Matrix := X → Y → Option Bool

/-- Missing entries are illegal pairs, not a third output value. -/
def Ftheta : Matrix :=
  ![![some false, some false, none, none, none, none],
    ![some true, some true, none, none, none, none],
    ![some true, none, some false, none, none, none],
    ![none, none, some false, some true, none, none],
    ![none, some true, none, some false, none, none],
    ![some false, none, none, none, some true, none],
    ![none, none, none, none, some true, some false],
    ![none, some false, none, none, none, some true]]

/-- The original legal domain. -/
def domain (F : Matrix) : Finset (X × Y) :=
  Finset.univ.filter fun xy => (F xy.1 xy.2).isSome

/-- The bipartite support retains every vertex of the ambient active input sets. -/
def support (F : Matrix) : SimpleGraph Vertex where
  Adj u v := match u, v with
    | .inl x, .inr y => (F x y).isSome = true
    | .inr y, .inl x => (F x y).isSome = true
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

instance (F : Matrix) : DecidableRel (support F).Adj :=
  fun u v => by cases u <;> cases v <;> dsimp [support] <;> infer_instance

/-- Conflicts are computed on the original legal domain and original labels. -/
def conflictA (F : Matrix) : SimpleGraph X where
  Adj x x' := ∃ y, (F x y).isSome = true ∧
    (F x' y).isSome = true ∧ F x y ≠ F x' y
  symm := ⟨by rintro x x' ⟨y, h, h', hn⟩; exact ⟨y, h', h, Ne.symm hn⟩⟩
  loopless := ⟨by rintro x ⟨y, _, _, h⟩; exact h rfl⟩

def conflictB (F : Matrix) : SimpleGraph Y where
  Adj y y' := ∃ x, (F x y).isSome = true ∧
    (F x y').isSome = true ∧ F x y ≠ F x y'
  symm := ⟨by rintro y y' ⟨x, h, h', hn⟩; exact ⟨x, h', h, Ne.symm hn⟩⟩
  loopless := ⟨by rintro y ⟨x, _, _, h⟩; exact h rfl⟩

instance (F : Matrix) : DecidableRel (conflictA F).Adj :=
  fun _ _ => inferInstanceAs (Decidable (Exists _))
instance (F : Matrix) : DecidableRel (conflictB F).Adj :=
  fun _ _ => inferInstanceAs (Decidable (Exists _))

/-- Whole globally monochromatic classes, measured before any deletion. -/
def monoA (F : Matrix) (c : Bool) (x : X) : Prop :=
  ∀ y b, F x y = some b → b = c

def monoB (F : Matrix) (d : Bool) (y : Y) : Prop :=
  ∀ x b, F x y = some b → b = d

instance (F : Matrix) (c : Bool) (x : X) : Decidable (monoA F c x) :=
  inferInstanceAs (Decidable (∀ y b, F x y = some b → b = c))
instance (F : Matrix) (d : Bool) (y : Y) : Decidable (monoB F d y) :=
  inferInstanceAs (Decidable (∀ x b, F x y = some b → b = d))

/-- Survivors are a vertex set, so isolated survivors are not discarded. -/
def survives (F : Matrix) (c d : Bool) : Vertex → Prop
  | .inl x => ¬ monoA F c x
  | .inr y => ¬ monoB F d y

instance (F : Matrix) (c d : Bool) : DecidablePred (survives F c d) :=
  fun v => by cases v <;> dsimp [survives] <;> infer_instance

abbrev ResidualVertex (F : Matrix) (c d : Bool) := {v // survives F c d v}

def residual (F : Matrix) (c d : Bool) : SimpleGraph (ResidualVertex F c d) :=
  (support F).induce {v | survives F c d v}

instance (F : Matrix) (c d : Bool) : DecidableRel (residual F c d).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((support F).Adj _ _))

/-- Symmetric binary edge label; values off the legal support are irrelevant. -/
def pairLabel (F : Matrix) : Vertex → Vertex → ZMod 2
  | .inl x, .inr y => if F x y = some true then 1 else 0
  | .inr y, .inl x => if F x y = some true then 1 else 0
  | _, _ => 0

/-- Restriction of the same original labels along the vertex inclusion. -/
def edgeLabel (F : Matrix) {V : Type} (inc : V → Vertex) (G : SimpleGraph V) :
    G.edgeSet → ZMod 2 :=
  fun e => Sym2.lift ⟨(fun u v => pairLabel F (inc u) (inc v)),
    by intro u v; dsimp only; cases inc u <;> cases inc v <;> rfl⟩ e.val

/-- Balance means even label parity on every actual simple cycle. -/
def Balanced (F : Matrix) (c d : Bool) : Prop :=
  ∀ (v : ResidualVertex F c d) (p : (residual F c d).Walk v v),
    p.IsCycle → walkParity (edgeLabel F Subtype.val (residual F c d)) p = 0

/-- The connected-support cycle rank is an INTEGER, without truncated subtraction. -/
def cycleRank (F : Matrix) : ℤ :=
  (domain F).card - (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) + 1

/-- Protocol alphabets can be arbitrary, including infinite types.
Only the finite reachable images are charged, and only legal inputs are checked. -/
def Protocol {A B : Type} [DecidableEq A] [DecidableEq B]
    (F : Matrix) (p q : ℕ) (alpha : X → A) (beta : Y → B)
    (delta : A → B → Bool) : Prop :=
  (Finset.univ.image alpha).card ≤ p ∧
  (Finset.univ.image beta).card ≤ q ∧
  ∀ x y b, F x y = some b → delta (alpha x) (beta y) = b

def alpha : X → ℕ := ![0, 1, 1, 0, 1, 0, 0, 2]
def beta : Y → ℕ := ![0, 0, 1, 2, 2, 1]

/-- Rows 001/100/010; unused ambient messages receive an arbitrary default. -/
def delta (a b : ℕ) : Bool :=
  match a, b with
  | 0, 2 => true
  | 1, 0 => true
  | 2, 1 => true
  | _, _ => false

def colorA : X → Fin 2 := ![0, 1, 1, 0, 1, 0, 1, 0]
def colorB : Y → Fin 2 := ![0, 1, 1, 0, 1, 0]

/-- Eight distinct cyclic vertices: P_(1-c) followed by reversed Q_(1-d). -/
def cycleVertex (c d : Bool) (i : Fin 8) : ResidualVertex Ftheta c d :=
  ⟨(![Sum.inr 0, Sum.inl (if c then 0 else 1), Sum.inr 1,
      Sum.inl (if d then 4 else 7), Sum.inr (if d then 3 else 5),
      Sum.inl (if d then 3 else 6), Sum.inr (if d then 2 else 4),
      Sum.inl (if d then 2 else 5)] : Fin 8 → Vertex) i,
    by cases c <;> cases d <;> fin_cases i <;> decide⟩

/-- A closed walk in the actual induced residual, using inherited support edges. -/
def cycleWalk (c d : Bool) :
    (residual Ftheta c d).Walk (cycleVertex c d 0) (cycleVertex c d 0) :=
  .cons (v := cycleVertex c d 1) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 2) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 3) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 4) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 5) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 6) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 7) (by cases c <;> cases d <;> decide) <|
  .cons (v := cycleVertex c d 0) (by cases c <;> cases d <;> decide) .nil

/-- The complete concrete graph and message-image data of the counterexample. -/
def TaskData : Prop :=
    (domain Ftheta).card = 16 ∧
    (support Ftheta).edgeFinset.card = 16 ∧
    Fintype.card Vertex = 14 ∧
    (∀ x, ∃ y b, Ftheta x y = some b) ∧
    (∀ y, ∃ x b, Ftheta x y = some b) ∧
    (support Ftheta).Connected ∧
    cycleRank Ftheta = 3 ∧
    (conflictA Ftheta).chromaticNumber = 2 ∧
    (conflictB Ftheta).chromaticNumber = 2 ∧
    (∀ c x, monoA Ftheta c x ↔ x = if c then 1 else 0) ∧
    (∀ d y, monoB Ftheta d y ↔ y = if d then 4 else 2) ∧
    (∀ c d, (cycleWalk c d).IsCycle ∧
      walkParity (edgeLabel Ftheta Subtype.val (residual Ftheta c d))
        (cycleWalk c d) = 1) ∧
    (Finset.univ.image alpha).card = 3 ∧
    (Finset.univ.image beta).card = 3

/-- The whole-class deletion method would be necessary for this actual protocol.
The antecedent records the complete concrete graph data, so negating this
conditional also certifies those data; no task hypotheses are assumed. -/
def claim : Prop :=
  TaskData → Protocol Ftheta 3 3 alpha beta delta → ∃ c d, Balanced Ftheta c d

/-- A concrete refutation of deletion necessity. Classically its type is exactly
TaskData AND correctness of the displayed protocol AND failure of all four
deletions. This negative form exposes the refuted necessity claim directly,
without adding a companion theorem to the certified finite counterexample. -/
theorem result : ¬ claim := by
  have ha : ∀ x, ∃ y b, Ftheta x y = some b := by decide
  have hb : ∀ y, ∃ x b, Ftheta x y = some b := by decide
  have hr : cycleRank Ftheta = 3 := by decide
  have hcolA : ∀ x x', (conflictA Ftheta).Adj x x' → colorA x ≠ colorA x' := by
    decide
  have hcolB : ∀ y y', (conflictB Ftheta).Adj y y' → colorB y ≠ colorB y' := by
    decide
  have hca : (conflictA Ftheta).chromaticNumber = 2 := by
    apply le_antisymm
    · exact (show (conflictA Ftheta).Colorable 2 from
        ⟨Coloring.mk colorA (fun {x x'} h => hcolA x x' h)⟩).chromaticNumber_le
    · exact two_le_chromaticNumber_of_adj (show (conflictA Ftheta).Adj 0 1 by decide)
  have hcb : (conflictB Ftheta).chromaticNumber = 2 := by
    apply le_antisymm
    · exact (show (conflictB Ftheta).Colorable 2 from
        ⟨Coloring.mk colorB (fun {y y'} h => hcolB y y' h)⟩).chromaticNumber_le
    · exact two_le_chromaticNumber_of_adj (show (conflictB Ftheta).Adj 0 2 by decide)
  have hconn : (support Ftheta).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨Sum.inr 0, ?_⟩
    have rX0 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inl 0) :=
      (show (support Ftheta).Adj (Sum.inr 0) (Sum.inl 0) by decide).reachable
    have rY1 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inr 1) :=
      rX0.trans (show (support Ftheta).Adj (Sum.inl 0) (Sum.inr 1) by decide).reachable
    have rX2 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inl 2) :=
      (show (support Ftheta).Adj (Sum.inr 0) (Sum.inl 2) by decide).reachable
    have rY2 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inr 2) :=
      rX2.trans (show (support Ftheta).Adj (Sum.inl 2) (Sum.inr 2) by decide).reachable
    have rX3 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inl 3) :=
      rY2.trans (show (support Ftheta).Adj (Sum.inr 2) (Sum.inl 3) by decide).reachable
    have rY3 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inr 3) :=
      rX3.trans (show (support Ftheta).Adj (Sum.inl 3) (Sum.inr 3) by decide).reachable
    have rX5 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inl 5) :=
      (show (support Ftheta).Adj (Sum.inr 0) (Sum.inl 5) by decide).reachable
    have rY4 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inr 4) :=
      rX5.trans (show (support Ftheta).Adj (Sum.inl 5) (Sum.inr 4) by decide).reachable
    have rX6 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inl 6) :=
      rY4.trans (show (support Ftheta).Adj (Sum.inr 4) (Sum.inl 6) by decide).reachable
    have rY5 : (support Ftheta).Reachable (Sum.inr 0) (Sum.inr 5) :=
      rX6.trans (show (support Ftheta).Adj (Sum.inl 6) (Sum.inr 5) by decide).reachable
    intro v
    rcases v with x | y
    · fin_cases x
      · exact rX0
      · exact (show (support Ftheta).Adj (Sum.inr 0) (Sum.inl 1) by decide).reachable
      · exact rX2
      · exact rX3
      · exact rY1.trans (show (support Ftheta).Adj (Sum.inr 1) (Sum.inl 4) by decide).reachable
      · exact rX5
      · exact rX6
      · exact rY1.trans (show (support Ftheta).Adj (Sum.inr 1) (Sum.inl 7) by decide).reachable
    · fin_cases y
      · exact Reachable.refl _
      · exact rY1
      · exact rY2
      · exact rY3
      · exact rY4
      · exact rY5
  have hcycle : ∀ c d, (cycleWalk c d).IsCycle := by
    intro c d
    rw [cycleWalk, Walk.cons_isCycle_iff]
    constructor
    · apply Walk.IsPath.mk'
      cases c <;> cases d <;> decide
    · cases c <;> cases d <;> decide
  have parity_step {c d : Bool} {u v w : ResidualVertex Ftheta c d}
      (h : (residual Ftheta c d).Adj u v) (p : (residual Ftheta c d).Walk v w) :
      walkParity (edgeLabel Ftheta Subtype.val (residual Ftheta c d)) (.cons h p) =
        pairLabel Ftheta u.val v.val +
          walkParity (edgeLabel Ftheta Subtype.val (residual Ftheta c d)) p := by
    simp [walkParity, Walk.edges_cons, edgeLabel, h]
  have hparity : ∀ c d,
      walkParity (edgeLabel Ftheta Subtype.val (residual Ftheta c d))
        (cycleWalk c d) = 1 := by
    intro c d
    unfold cycleWalk
    rw [parity_step, parity_step, parity_step, parity_step,
      parity_step, parity_step, parity_step, parity_step]
    simp only [walkParity, Walk.edges_nil, List.map_nil, List.sum_nil, add_zero]
    cases c <;> cases d <;> decide
  have hunbalanced : ∀ c d, ¬ Balanced Ftheta c d := by
    intro c d h
    have he := h _ (cycleWalk c d) (hcycle c d)
    rw [hparity c d] at he
    exact one_ne_zero he
  have hp : Protocol Ftheta 3 3 alpha beta delta := by unfold Protocol; decide
  have hdata : TaskData := by
    refine ⟨by decide, by decide, by decide, ha, hb, hconn, hr, hca, hcb,
      by decide, by decide, ?_, by decide, by decide⟩
    intro c d
    exact ⟨hcycle c d, hparity c d⟩
  intro hn
  obtain ⟨c, d, h⟩ := hn hdata hp
  exact hunbalanced c d h

end D5.S3.Observer.Separation.BooleanRankThreeProtocol
