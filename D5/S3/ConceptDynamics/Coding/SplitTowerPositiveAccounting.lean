/- SOURCE ONLY. UNCOMPILED. Actual finite tower-to-word construction.
Forward corrections count incoming stages; inverse corrections count outgoing
stages. Neither desired total correction nor a word equality is a hypothesis. -/
import D5.S3.ConceptDynamics.Coding.TypedPositiveSplitWord

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.SplitTowerPositiveAccounting
open EssentialWordRealization TwoSidedFiniteInduction
open TypedPositiveSplitWord SplitTowerTranslation
open ZeroWindowRelabeling (Relabel)

namespace TowerWord
variable {F K : Presentation}

def inCount : Tower F K → ℕ
  | .nil _ => 0
  | .outgoing _ _ tail => inCount tail
  | .incoming _ _ tail => inCount tail+1

def outCount : Tower F K → ℕ
  | .nil _ => 0
  | .outgoing _ _ tail => outCount tail+1
  | .incoming _ _ tail => outCount tail

/-- Literal traversal: first the bottom lift, then the remaining tower. -/
def forward : Tower F K → Word F K
  | .nil F => Word.identity F
  | .outgoing T p tail => .comp (TypedPositiveSplitWord.outgoing F T p) (forward tail)
  | .incoming T p tail => .comp (TypedPositiveSplitWord.incoming F T p) (forward tail)

/-- Reverse traversal uses opposite POSITIVE letters in reverse order.
It never puts an inverse homeomorphism into the word syntax. -/
def backward : Tower F K → Word K F
  | .nil F => Word.identity F
  | .outgoing T p tail => .comp (backward tail) (outgoingBack F T p)
  | .incoming T p tail => .comp (backward tail) (incomingBack F T p)

theorem counts_length (t : Tower F K) : inCount t+outCount t = t.length := by
  induction t with
  | nil F => rfl
  | outgoing T p tail ih => simpa only [inCount,outCount,Tower.length,Nat.add_assoc] using congrArg (fun n => n+1) ih
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
  | F, K, .incoming T p tail, x => by
      change tail.toHomeomorph (ActualInSplit.lift F.graph p x) = _
      rw [forward_literal tail,incoming_literal,Word.eval_time,
        StandardBeamHomeomorphisms.translate_add]
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
      rw [backward_literal tail,outgoing_forget_time,outgoing_inverse_literal,
        StandardBeamHomeomorphisms.translate_add]
      change time F.graph (-(outCount tail : ℤ)+(-1)) _ =
        time F.graph (-((outCount tail+1 : ℕ):ℤ)) _
      congr 1 <;> omega
  | F, K, .incoming T p tail, z => by
      change ActualInSplit.forget F.graph p (tail.toHomeomorph.symm z) = _
      rw [backward_literal tail,incoming_forget_time,incoming_inverse_literal]
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
  rw [TwoSidedFiniteInduction.literal_original r x,TowerWord.backward_literal,
    TowerWord.forward_literal,relabel_time,Word.eval_time,
    StandardBeamHomeomorphisms.translate_add]
  change time H.graph (-(TowerWord.outCount r.right : ℤ)+(-(TowerWord.inCount r.left : ℤ))) _ =
    time H.graph (-(TowerWord.inCount r.left : ℤ)-(TowerWord.outCount r.right : ℤ)) _
  congr 1 <;> omega

theorem terminal_letters {F H : Presentation} {P : Hist F ≃ₜ Hist H} {k : ℕ}
    (r : Terminal F H P k) : (terminalWord r).letters = 2*k := by
  simp only [terminalWord,Word.letters,TowerWord.forward_letters,
    TowerWord.backward_letters,r.source_depth,r.target_depth]
  omega
end D5.S3.ConceptDynamics.Coding.SplitTowerPositiveAccounting
