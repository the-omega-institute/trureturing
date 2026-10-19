/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/SplitTowerPositiveAccounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count the signed corrections of every actual split tower. -/

/- Forward corrections count incoming stages; reverse corrections count outgoing stages. Terminal accounting retains both actual counts. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.TypedPositiveSplitWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.SplitTowerPositiveAccounting
open EssentialWordRealization TwoSidedFiniteInduction
open TypedPositiveSplitWord SplitTowerTranslation
open ZeroWindowRelabeling (Relabel)

local instance presentationVertexTopology (F : Presentation) : TopologicalSpace F.V := ⊥
local instance presentationVertexDiscrete (F : Presentation) : DiscreteTopology F.V := ⟨rfl⟩

namespace TowerWord
variable {F K : Presentation}

def inCount : {F K : Presentation} → Tower F K → ℕ
  | _, _, .nil _ => 0
  | _, _, .outgoing _ _ tail => inCount tail
  | _, _, .incoming _ _ tail => inCount tail+1

def outCount : {F K : Presentation} → Tower F K → ℕ
  | _, _, .nil _ => 0
  | _, _, .outgoing _ _ tail => outCount tail+1
  | _, _, .incoming _ _ tail => outCount tail

/-- Literal traversal: first the bottom lift, then the remaining tower. -/
def forward : {F K : Presentation} → Tower F K → Word F K
  | _, _, .nil F => Word.identity F
  | F, _, .outgoing T p tail => .comp (TypedPositiveSplitWord.outgoing F T p) (forward tail)
  | F, _, .incoming T p tail => .comp (TypedPositiveSplitWord.incoming F T p) (forward tail)

/-- Reverse traversal uses opposite POSITIVE letters in reverse order.
It never puts an inverse homeomorphism into the word syntax. -/
def backward : {F K : Presentation} → Tower F K → Word K F
  | _, _, .nil F => Word.identity F
  | F, _, .outgoing T p tail => .comp (backward tail) (outgoingBack F T p)
  | F, _, .incoming T p tail => .comp (backward tail) (incomingBack F T p)

theorem counts_length (t : Tower F K) : inCount t+outCount t = t.length := by
  induction t with
  | nil F => rfl
  | outgoing T p tail ih =>
      simp only [inCount, outCount, Tower.length]
      omega
  | incoming T p tail ih => simp only [inCount,outCount,Tower.length]; omega

theorem forward_letters (t : Tower F K) : (forward t).letters = t.length := by
  induction t with
  | nil F => rfl
  | outgoing T p tail ih => simp only [forward,TypedPositiveSplitWord.outgoing,Word.letters,Tower.length,ih]; omega
  | incoming T p tail ih => simp only [forward,TypedPositiveSplitWord.incoming,Word.letters,Tower.length,ih]; omega

theorem backward_letters (t : Tower F K) : (backward t).letters = t.length := by
  induction t with
  | nil F => rfl
  | outgoing T p tail ih => simp only [backward,outgoingBack,Word.letters,Tower.length,ih]
  | incoming T p tail ih => simp only [backward,incomingBack,Word.letters,Tower.length,ih]

/-- EVERY concrete finite tower has the constructed positive forward word. -/
theorem forward_literal : ∀ {F K : Presentation} (t : Tower F K) (x : Hist F),
    t.toHomeomorph x = time K.graph (-(inCount t : ℤ)) ((forward t).eval x)
  | F, _, .nil _, x => by
      change x = time F.graph 0 x
      exact (StandardBeamHomeomorphisms.translate_zero F.graph x).symm
  | F, K, .outgoing T p tail, x => by
      change tail.toHomeomorph (ActualOutSplit.lift F.graph p x) = _
      rw [forward_literal tail,outgoing_literal]
      rfl
  | F, K, .incoming T p tail, x => by
      change tail.toHomeomorph (ActualInSplit.lift F.graph p x) = _
      rw [forward_literal tail,incoming_literal,Word.eval_time]
      dsimp only [SplitTowerTranslation.time]
      rw [StandardBeamHomeomorphisms.translate_add K.graph]
      change time K.graph (-(inCount tail : ℤ)+(-1)) _ =
        time K.graph (-((inCount tail+1 : ℕ):ℤ)) _
      congr 1 <;> omega

/-- EVERY concrete finite tower also has a positive inverse-traversal word. -/
theorem backward_literal : ∀ {F K : Presentation} (t : Tower F K) (z : Hist K),
    t.toHomeomorph.symm z = time F.graph (-(outCount t : ℤ)) ((backward t).eval z)
  | F, _, .nil _, z => by
      change z = time F.graph 0 z
      exact (StandardBeamHomeomorphisms.translate_zero F.graph z).symm
  | F, K, .outgoing T p tail, z => by
      change ActualOutSplit.forget F.graph p (tail.toHomeomorph.symm z) = _
      rw [backward_literal tail]
      change ActualOutSplit.forget F.graph p
        (time (ActualOutSplit.graph F.graph p) (-(outCount tail : ℤ))
          ((backward tail).eval z)) = _
      rw [outgoing_forget_time,outgoing_inverse_literal]
      dsimp only [SplitTowerTranslation.time]
      rw [StandardBeamHomeomorphisms.translate_add F.graph]
      change time F.graph (-(outCount tail : ℤ)+(-1)) _ =
        time F.graph (-((outCount tail+1 : ℕ):ℤ)) _
      congr 1 <;> omega
  | F, K, .incoming T p tail, z => by
      change ActualInSplit.forget F.graph p (tail.toHomeomorph.symm z) = _
      rw [backward_literal tail]
      change ActualInSplit.forget F.graph p
        (time (ActualInSplit.graph F.graph p) (-(outCount tail : ℤ))
          ((backward tail).eval z)) = _
      rw [incoming_forget_time,incoming_inverse_literal]
      rfl
end TowerWord

/-- All endpoint types here are the actual finite terminal presentations.
The terminal J is finite vertex-and-edge data, not a history-map leaf. -/
def terminalWord {F H : Presentation} {P : Hist F ≃ₜ Hist H} {k : ℕ}
    (r : Terminal F H P k) : Word F H :=
  .comp (TowerWord.forward r.left)
    (.comp (.relabel r.relabel) (TowerWord.backward r.right))

/-- The general formula deliberately keeps BOTH actual counts. Equal lengths
alone would not justify replacing their sum by k. -/
theorem terminal_literal {F H : Presentation} {P : Hist F ≃ₜ Hist H} {k : ℕ}
    (r : Terminal F H P k) (x : Hist F) :
    P x = time H.graph (-(TowerWord.inCount r.left : ℤ)-(TowerWord.outCount r.right : ℤ))
      ((terminalWord r).eval x) := by
  have ho : P x = r.right.toHomeomorph.symm
      (r.relabel.history (r.left.toHomeomorph x)) :=
    (r.right.toHomeomorph.symm_apply_apply (P x)).symm.trans
      (congrArg r.right.toHomeomorph.symm (r.square x))
  rw [ho,TowerWord.backward_literal,
    TowerWord.forward_literal,relabel_time,Word.eval_time]
  dsimp only [SplitTowerTranslation.time]
  rw [StandardBeamHomeomorphisms.translate_add H.graph]
  change time H.graph (-(TowerWord.outCount r.right : ℤ)+(-(TowerWord.inCount r.left : ℤ))) _ =
    time H.graph (-(TowerWord.inCount r.left : ℤ)-(TowerWord.outCount r.right : ℤ)) _
  congr 1 <;> omega

theorem terminal_letters {F H : Presentation} {P : Hist F ≃ₜ Hist H} {k : ℕ}
    (r : Terminal F H P k) : (terminalWord r).letters = 2*k := by
  simp only [terminalWord,Word.letters,TowerWord.forward_letters,
    TowerWord.backward_letters,r.source_depth,r.target_depth]
  omega
end D5.S3.ConceptDynamics.Coding.SplitTowerPositiveAccounting
