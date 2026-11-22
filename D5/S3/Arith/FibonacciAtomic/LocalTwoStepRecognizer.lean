/- GID: D5/S3/Arith/FibonacciAtomic/LocalTwoStepRecognizer
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalTwoStepRecognizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Free]
   utility: none
   digest: Exact local two-step substitution decoding in physical and unordered tree order. -/

import Mathlib.Algebra.Free

/-! Exact local two-step recognition for physical Fibonacci substitution trees. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer

abbrev Labelled := FreeMagma Bool
abbrev Shape := FreeMagma Unit

/-- True is α, false is β; multiplication is the old physical child pair. -/
abbrev alpha : Labelled := .of true
abbrev beta : Labelled := .of false
abbrev tip : Shape := .of ()
abbrev cherry : Shape := .mul tip tip

/-- One update of the old leaves. Each β birth may independently take either
physical orientation; an old branch retains its two physical links. -/
inductive Step : Labelled → Labelled → Prop
  | alphaToBeta : Step alpha beta
  | betaLeft : Step beta (.mul beta alpha)
  | betaRight : Step beta (.mul alpha beta)
  | branch : Step a a' → Step b b' → Step (.mul a b) (.mul a' b')

/-- Erase only leaf labels, retaining physical child order and all occurrences. -/
def shape (u : Labelled) : Shape := FreeMagma.map (fun _ => ()) u

/-- Two successive actual updates, followed by label erasure. -/
def Expanded (u : Labelled) (x : Shape) : Prop :=
  ∃ v w, Step u v ∧ Step v w ∧ shape w = x

/-- The four literal productions of the unlabelled grammar. -/
inductive Grammar : Shape → Prop
  | cherry : Grammar cherry
  | betaLeft : Grammar (.mul cherry tip)
  | betaRight : Grammar (.mul tip cherry)
  | branch : Grammar a → Grammar b → Grammar (.mul a b)

private def join : Option Labelled → Option Labelled → Option Labelled
  | some a, some b => some (.mul a b)
  | _, _ => none

private def atBranch (l r : Shape) (dl dr : Option Labelled) : Option Labelled :=
  match l, r with
  | .of _, .of _ => some alpha
  | .mul _ _, .of _ => if l = cherry then some beta else none
  | .of _, .mul _ _ => if r = cherry then some beta else none
  | .mul _ _, .mul _ _ => join dl dr

/-- Structural computation on the two physical subtrees, with exact cherry
tests in the two mixed cases. -/
def decode : Shape → Option Labelled
  | .of _ => none
  | .mul l r => atBranch l r (decode l) (decode r)

private theorem shape_branch (a b : Labelled) : shape (.mul a b) = .mul (shape a) (shape b) := rfl

private inductive Codes : Labelled → Shape → Prop
  | alphaCode : Codes alpha cherry
  | leftCode : Codes beta (.mul cherry tip)
  | rightCode : Codes beta (.mul tip cherry)
  | pairCode : Codes a x → Codes b y → Codes (.mul a b) (.mul x y)

private theorem codes_root {u x} (h : Codes u x) : ∃ l r, x = .mul l r := by
  cases h <;> exact ⟨_, _, rfl⟩

private theorem actual_codes {u v w} (h : Step u v) (j : Step v w) : Codes u (shape w) := by
  induction h generalizing w with
  | alphaToBeta =>
    cases j
    · exact .alphaCode
    · exact .alphaCode
  | betaLeft =>
    cases j with
    | branch j₁ j₂ => cases j₁ <;> cases j₂ <;> exact .leftCode
  | betaRight =>
    cases j with
    | branch j₁ j₂ => cases j₁; cases j₂ <;> exact .rightCode
  | branch _ _ ih₁ ih₂ =>
    cases j with
    | branch j₁ j₂ => exact .pairCode (ih₁ j₁) (ih₂ j₂)

private theorem codes_actual {u x} (h : Codes u x) : Expanded u x := by
  induction h with
  | alphaCode => exact ⟨_, _, .alphaToBeta, .betaLeft, rfl⟩
  | leftCode => exact ⟨_, _, .betaLeft, .branch .betaLeft .alphaToBeta, rfl⟩
  | rightCode => exact ⟨_, _, .betaRight, .branch .alphaToBeta .betaLeft, rfl⟩
  | pairCode _ _ ih₁ ih₂ =>
    obtain ⟨v₁, w₁, a, b, h₁⟩ := ih₁
    obtain ⟨v₂, w₂, c, d, h₂⟩ := ih₂
    exact ⟨_, _, .branch a c, .branch b d,
      (shape_branch w₁ w₂).trans (congrArg₂ FreeMagma.mul h₁ h₂)⟩

private theorem expanded_iff_codes (u : Labelled) (x : Shape) :
    Expanded u x ↔ Codes u x := by
  constructor
  · rintro ⟨v, w, h, j, rfl⟩
    exact actual_codes h j
  · exact codes_actual

private theorem grammar_iff_codes (x : Shape) : Grammar x ↔ ∃ u, Codes u x := by
  constructor
  · intro h
    induction h with
    | cherry => exact ⟨_, .alphaCode⟩
    | betaLeft => exact ⟨_, .leftCode⟩
    | betaRight => exact ⟨_, .rightCode⟩
    | branch _ _ ih₁ ih₂ =>
      obtain ⟨_, ha⟩ := ih₁
      obtain ⟨_, hb⟩ := ih₂
      exact ⟨_, .pairCode ha hb⟩
  · rintro ⟨u, h⟩
    induction h with
    | alphaCode => exact .cherry
    | leftCode => exact .betaLeft
    | rightCode => exact .betaRight
    | pairCode _ _ ih₁ ih₂ => exact .branch ih₁ ih₂

private theorem codes_decode {u x} (h : Codes u x) : decode x = some u := by
  induction h with
  | alphaCode => rfl
  | leftCode => rfl
  | rightCode => rfl
  | pairCode hl hr ih₁ ih₂ =>
    obtain ⟨_, _, rfl⟩ := codes_root hl
    obtain ⟨_, _, rfl⟩ := codes_root hr
    change join (decode (.mul _ _)) (decode (.mul _ _)) = _
    rw [ih₁, ih₂]
    rfl

private theorem decode_codes (x : Shape) : ∀ u, decode x = some u → Codes u x := by
  induction x with
  | of a => simp [decode]
  | mul l r ih₁ ih₂ =>
    intro u h
    cases l with
    | of a =>
      cases r with
      | of b =>
        cases a; cases b
        have hu : alpha = u := Option.some.inj h
        subst u
        exact .alphaCode
      | mul a₁ a₂ =>
        cases a
        simp only [decode, atBranch] at h
        split at h
        · rename_i he
          have hu := Option.some.inj h
          subst u
          rw [he]
          exact .rightCode
        · contradiction
    | mul a₁ a₂ =>
      cases r with
      | of b =>
        cases b
        simp only [decode, atBranch] at h
        split at h
        · rename_i he
          have hu := Option.some.inj h
          subst u
          rw [he]
          exact .leftCode
        · contradiction
      | mul b₁ b₂ =>
        change join (decode (.mul a₁ a₂)) (decode (.mul b₁ b₂)) = some u at h
        cases ha : decode (.mul a₁ a₂) with
        | none => simp only [ha, join, reduceCtorEq] at h
        | some a =>
          cases hb : decode (.mul b₁ b₂) with
          | none => simp only [ha, hb, join, reduceCtorEq] at h
          | some b =>
            simp only [ha, hb, join, Option.some.injEq] at h
            subst u
            exact .pairCode (ih₁ a ha) (ih₂ b hb)

universe u

inductive Unordered {A : Type u} : FreeMagma A → FreeMagma A → Prop
  | leaf (a : A) : Unordered (.of a) (.of a)
  | straight {a b c d : FreeMagma A} : Unordered a c → Unordered b d →
      Unordered (.mul a b) (.mul c d)
  | crossed {a b c d : FreeMagma A} : Unordered a d → Unordered b c →
      Unordered (.mul a b) (.mul c d)

namespace Unordered

variable {A : Type u}

private theorem refl (a : FreeMagma A) : Unordered a a := by
  induction a with
  | ih1 x => exact .leaf x
  | ih2 _ _ ih₁ ih₂ => exact .straight ih₁ ih₂

private theorem symm {a b : FreeMagma A} (h : Unordered a b) : Unordered b a := by
  induction h with
  | leaf x => exact .leaf x
  | straight _ _ ih₁ ih₂ => exact .straight ih₁ ih₂
  | crossed _ _ ih₁ ih₂ => exact .crossed ih₂ ih₁

private theorem trans {a b c : FreeMagma A} (hab : Unordered a b) (hbc : Unordered b c) :
    Unordered a c := by
  induction hab generalizing c with
  | leaf x =>
    cases hbc
    exact .leaf x
  | straight _ _ ih₁ ih₂ =>
    cases hbc with
    | straight h₁ h₂ => exact .straight (ih₁ h₁) (ih₂ h₂)
    | crossed h₁ h₂ => exact .crossed (ih₁ h₁) (ih₂ h₂)
  | crossed _ _ ih₁ ih₂ =>
    cases hbc with
    | straight h₁ h₂ => exact .crossed (ih₁ h₂) (ih₂ h₁)
    | crossed h₁ h₂ => exact .straight (ih₁ h₂) (ih₂ h₁)

private def setoid (A : Type u) : Setoid (FreeMagma A) where
  r := Unordered
  iseqv := ⟨refl, symm, trans⟩

private theorem quotient_eq_iff {a b : FreeMagma A} :
    Quotient.mk (setoid A) a = Quotient.mk (setoid A) b ↔ Unordered a b :=
  ⟨fun h => @Quotient.exact _ (setoid A) _ _ h,
    fun h => @Quotient.sound _ (setoid A) _ _ h⟩

end Unordered


private theorem codes_forward {u v : Labelled} {x y : Shape}
    (h : Unordered u v) (hx : Codes u x) (hy : Codes v y) : Unordered x y := by
  induction h generalizing x y with
  | leaf a =>
    cases hx <;> cases hy
    · exact Unordered.refl _
    · exact Unordered.refl _
    · exact .crossed (Unordered.refl _) (Unordered.refl _)
    · exact .crossed (Unordered.refl _) (Unordered.refl _)
    · exact Unordered.refl _
  | straight _ _ ih₁ ih₂ =>
    cases hx with
    | pairCode xa xb =>
      cases hy with
      | pairCode ya yb => exact .straight (ih₁ xa ya) (ih₂ xb yb)
  | crossed _ _ ih₁ ih₂ =>
    cases hx with
    | pairCode xa xb =>
      cases hy with
      | pairCode ya yb => exact .crossed (ih₁ xa yb) (ih₂ xb ya)

private theorem tip_fixed {x : Shape} (h : Unordered tip x) : x = tip := by
  cases h
  rfl

private theorem cherry_fixed {x : Shape} (h : Unordered cherry x) : x = cherry := by
  cases h with
  | straight hl hr => rw [tip_fixed hl, tip_fixed hr]
  | crossed hl hr => rw [tip_fixed hl, tip_fixed hr]

private theorem codes_transport {u : Labelled} {x y : Shape}
    (hx : Codes u x) (h : Unordered x y) : ∃ v, Codes v y ∧ Unordered u v := by
  induction hx generalizing y with
  | alphaCode =>
    rw [cherry_fixed h]
    exact ⟨_, .alphaCode, .leaf _⟩
  | leftCode =>
    cases h with
    | straight hl hr =>
      rw [cherry_fixed hl, tip_fixed hr]
      exact ⟨_, .leftCode, .leaf _⟩
    | crossed hl hr =>
      rw [cherry_fixed hl, tip_fixed hr]
      exact ⟨_, .rightCode, .leaf _⟩
  | rightCode =>
    cases h with
    | straight hl hr =>
      rw [tip_fixed hl, cherry_fixed hr]
      exact ⟨_, .rightCode, .leaf _⟩
    | crossed hl hr =>
      rw [tip_fixed hl, cherry_fixed hr]
      exact ⟨_, .leftCode, .leaf _⟩
  | pairCode _ _ ih₁ ih₂ =>
    cases h with
    | straight hl hr =>
      obtain ⟨v₁, h₁, r₁⟩ := ih₁ hl
      obtain ⟨v₂, h₂, r₂⟩ := ih₂ hr
      exact ⟨_, .pairCode h₁ h₂, .straight r₁ r₂⟩
    | crossed hl hr =>
      obtain ⟨v₁, h₁, r₁⟩ := ih₁ hl
      obtain ⟨v₂, h₂, r₂⟩ := ih₂ hr
      exact ⟨_, .pairCode h₂ h₁, .crossed r₁ r₂⟩

private theorem codes_backward {u v : Labelled} {x y : Shape}
    (hx : Codes u x) (hy : Codes v y) (h : Unordered x y) : Unordered u v := by
  obtain ⟨w, hw, huw⟩ := codes_transport hx h
  have he : w = v := Option.some.inj ((codes_decode hw).symm.trans (codes_decode hy))
  exact he ▸ huw

private theorem decode_exact (x : Shape) (u : Labelled) :
    decode x = some u ↔ Expanded u x :=
  ⟨fun h => codes_actual (decode_codes x u h),
    fun h => codes_decode ((expanded_iff_codes u x).mp h)⟩

private theorem classes_iff (u v : Labelled) (x y : Shape)
    (hx : Expanded u x) (hy : Expanded v y) :
    Unordered x y ↔ Unordered u v := by
  have a := (expanded_iff_codes u x).mp hx
  have b := (expanded_iff_codes v y).mp hy
  exact ⟨codes_backward a b, fun h => codes_forward h a b⟩

private def canonicalShape : Labelled → Shape
  | .of true => cherry
  | .of false => .mul cherry tip
  | .mul a b => .mul (canonicalShape a) (canonicalShape b)

private theorem canonical_codes (u : Labelled) : Codes u (canonicalShape u) := by
  induction u with
  | of b =>
    cases b
    · exact .leftCode
    · exact .alphaCode
  | mul _ _ ih₁ ih₂ => exact .pairCode ih₁ ih₂

/-- Rooted non-plane classes, retaining every leaf label and branching occurrence. -/
abbrev Classes (A : Type) := Quotient (Unordered.setoid A)

/-- Class of an actual ordered representative after forgetting local child order. -/
def treeClass {A : Type} (t : FreeMagma A) : Classes A :=
  Quotient.mk (Unordered.setoid A) t

/-- A canonical representative computes the actual two-step shape class.
The theorem below proves that all orientations give this same class. -/
def unorderedImage : Classes Bool → Classes Unit :=
  Quotient.map canonicalShape (fun u v h =>
    codes_forward h (canonical_codes u) (canonical_codes v))

/-- The executable decoder and the independent actual two-update relation agree.
It classifies the grammar, returns a unique physical predecessor, and descends
to an injective map even when any of the local newborn orientations vary. -/
theorem exact_local_two_step :
    (∀ x u, decode x = some u ↔ Expanded u x) ∧
    (∀ x, Grammar x ↔ ∃! u, Expanded u x) ∧
    (∀ x y u, Unordered x y → decode x = some u →
      ∃ v, decode y = some v ∧ Unordered u v) ∧
    (∀ x y, Unordered x y → (decode x = none ↔ decode y = none)) ∧
    (∀ u v x y, Expanded u x → Expanded v y → (Unordered x y ↔ Unordered u v)) ∧
    (∀ u x, Expanded u x →
      unorderedImage (treeClass u) = treeClass x) ∧
    Function.Injective unorderedImage := by
  refine ⟨decode_exact, ?_, ?_, ?_, classes_iff, ?_, ?_⟩
  · intro x
    constructor
    · intro hg
      obtain ⟨u, hu⟩ := (grammar_iff_codes x).mp hg
      refine ⟨u, codes_actual hu, fun v hv => ?_⟩
      exact Option.some.inj (((decode_exact x v).mpr hv).symm.trans (codes_decode hu))
    · rintro ⟨u, h, _⟩
      exact (grammar_iff_codes x).mpr ⟨u, (expanded_iff_codes u x).mp h⟩
  · intro x y u h hu
    obtain ⟨v, hv, huv⟩ := codes_transport (decode_codes x u hu) h
    exact ⟨v, codes_decode hv, huv⟩
  · intro x y h
    have forward : ∀ a b : Shape, Unordered a b → decode a = none → decode b = none := by
      intro a b hab ha
      cases hb : decode b with
      | none => rfl
      | some v =>
        obtain ⟨u, hu, _⟩ := codes_transport (decode_codes b v hb) (Unordered.symm hab)
        exact False.elim (Option.some_ne_none u ((codes_decode hu).symm.trans ha))
    exact ⟨forward x y h, forward y x (Unordered.symm h)⟩
  · intro u x h
    exact (Unordered.quotient_eq_iff).mpr <|
      (classes_iff u u (canonicalShape u) x (codes_actual (canonical_codes u)) h).mpr
        (Unordered.refl u)
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro u v h
    have he := (Unordered.quotient_eq_iff).mp h
    exact (Unordered.quotient_eq_iff).mpr <|
      (classes_iff u v _ _ (codes_actual (canonical_codes u))
        (codes_actual (canonical_codes v))).mp he

#print axioms exact_local_two_step

end D5.S3.Arith.FibonacciAtomic.LocalTwoStepRecognizer
