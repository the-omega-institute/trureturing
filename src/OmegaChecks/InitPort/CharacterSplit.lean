module
public import OmegaChecks.InitPort.CertifiedFunction
public import Init.Data.String.Lemmas.Pattern.Split.Char
import all Init.Data.String.Lemmas.Pattern.Split.Char
import all Init.Data.String.Lemmas.Pattern.Split.Pred
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Order

/-! Splitting on a character test advances by one character in both recursive branches. -/

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model
namespace OmegaChecks.InitPort.CharacterSplit

@[expose] public noncomputable def boolReference (p : Char → Bool) {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) := Model.split p f curr hle

@[expose] public noncomputable def charReference (c : Char) {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) := Model.split c f curr hle

@[expose] public noncomputable def predReference (p : Char → Prop) [DecidablePred p] {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) := Model.split p f curr hle

public noncomputable def split (p : Char → Bool) {s : Slice} (f curr : s.Pos) (hle : f ≤ curr) :
    List s.Subslice :=
  (String.Slice.Pos.wellFounded_gt (s := s)).fix
    (C := fun curr => ∀ f : s.Pos, f ≤ curr → List s.Subslice)
    (fun curr rec f le =>
      if h : curr = s.endPos then [s.subslice f curr le]
      else if p (curr.get h) then
        s.subslice f curr le :: rec (curr.next h) Pos.lt_next _ (Nat.le_refl _)
      else rec (curr.next h) Pos.lt_next f (Nat.le_trans le Pos.le_next)) curr f hle

public theorem splitStep (p : Char → Bool) {s : Slice} (f curr : s.Pos) (hle : f ≤ curr) :
    split p f curr hle =
      if h : curr = s.endPos then [s.subslice f curr hle]
      else if p (curr.get h) then
        s.subslice f curr hle :: split p (curr.next h) (curr.next h) (Nat.le_refl _)
      else split p f (curr.next h) (Nat.le_trans hle Pos.le_next) := by
  unfold split
  rw [WellFounded.fix_eq]

private theorem boolAt (p : Char → Bool) {s : Slice} (f curr : s.Pos) (hle : f ≤ curr) :
    boolReference p f curr hle = split p f curr hle := by
  induction curr using String.Slice.Pos.next_induction generalizing f with
  | endPos =>
    unfold boolReference split
    rw [Model.split_bool_eq_internal, WellFounded.fix_eq]
    simp
  | next curr h ih =>
    unfold boolReference split
    rw [Model.split_bool_eq_internal, WellFounded.fix_eq]
    simp only [dite_eq_right h]
    by_cases accept : p (curr.get h) = true
    · rw [ite_eq_left accept, ite_eq_left accept]
      exact congrArg (List.cons _) (ih _ _)
    · rw [ite_eq_right accept, ite_eq_right accept]
      exact ih _ _

public theorem boolAgreement : @boolReference = @split := by
  funext p s f curr h
  exact boolAt p f curr h

public noncomputable def charSplit (c : Char) {s : Slice} (f curr : s.Pos) (hle : f ≤ curr) :=
  split (· == c) f curr hle

public theorem charAgreement : @charReference = @charSplit := by
  funext c s f curr h
  exact (Model.split_char_eq_split_beq f curr h).trans (boolAt _ f curr h)

public noncomputable def predSplit (p : Char → Prop) [DecidablePred p] {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) := split (decide <| p ·) f curr hle

public theorem predAgreement : @predReference = @predSplit := by
  funext p d s f curr h
  exact (Model.split_eq_split_decide f curr h).trans (boolAt _ f curr h)

end OmegaChecks.InitPort.CharacterSplit
