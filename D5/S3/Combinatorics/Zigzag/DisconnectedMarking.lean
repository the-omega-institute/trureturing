/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedMarking
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedMarking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Actual monochromatic class pairs and exact separated successor words. -/

import D5.S3.Combinatorics.Zigzag.DisconnectedEncoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- Marks of the actual positive-sector frontier while semitones remain separate. -/
inductive SupportMark where
  | Am | Ap | Dm | Dp | Em | Ep | Ex | Hm | Ip
  deriving DecidableEq, Repr

private def markState : SupportMark → State
  | .Am | .Ap => State.A
  | .Dm | .Dp => State.D
  | .Em | .Ep | .Ex => State.E
  | .Hm => State.H
  | .Ip => State.I

/-- None denotes an unused frontier, not merely zero imbalance. -/
private def frontierMark : SupportMark → Option Bool × Option Bool
  | .Am => (some false, none)
  | .Ap => (some true, none)
  | .Dm => (none, some false)
  | .Dp => (none, some true)
  | .Em => (some false, some false)
  | .Ep => (some true, some true)
  | .Ex => (some false, some true)
  | .Hm => (some false, none)
  | .Ip => (none, some true)

/-- Original StepIndex labels are retained; none indicates a joining edge pair. -/
private def separatedStep : (s : SupportMark) → StepIndex (markState s) → Option SupportMark
  | .Am, i => [none, none, some .Em, none].get i
  | .Ap, i => [some .Am, some .Dp, some .Ex, some .Ip].get i
  | .Dm, i => [some .Am, some .Dp, some .Ex, some .Hm].get i
  | .Dp, i => [none, none, some .Ep, none].get i
  | .Em, i => [none, some .Dm].get i
  | .Ep, i => [some .Ap, none].get i
  | .Ex, i => [none, none].get i
  | .Hm, i => [none].get i
  | .Ip, i => [none].get i

private def lowEndpointRoles : Form → Fin 6 × Fin 6
  | ⟨0, _⟩ => (0, 2)
  | ⟨1, _⟩ => (4, 3)
  | ⟨2, _⟩ => (1, 4)
  | ⟨3, _⟩ => (2, 5)
  | ⟨4, _⟩ => (5, 0)
  | ⟨5, _⟩ => (3, 1)

private def highEndpointRoles : Form → Fin 6 × Fin 6
  | ⟨0, _⟩ => (0, 5)
  | ⟨1, _⟩ => (3, 4)
  | ⟨2, _⟩ => (1, 3)
  | ⟨3, _⟩ => (5, 2)
  | ⟨4, _⟩ => (2, 0)
  | ⟨5, _⟩ => (4, 1)

private def roleVertex (n j : Nat) : Fin 6 → ZMod n := frontierVertex n j

private theorem low_roles_actual (n j : Nat) (f : Form) :
    formPair n j f =
      (roleVertex n j (lowEndpointRoles f).1, roleVertex n j (lowEndpointRoles f).2) := by
  fin_cases f <;> rfl

private theorem high_roles_actual (n j : Nat) (hj : j ≤ n+1) (f : Form) :
    formPair n (highClass n j) f =
      (roleVertex n j (highEndpointRoles f).1, roleVertex n j (highEndpointRoles f).2) := by
  have hh : (highClass n j : ZMod n) = 1 - (j : ZMod n) := by
    simp only [highClass, Nat.cast_sub hj, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add]
  fin_cases f <;> simp [formPair, roleVertex, frontierVertex, highEndpointRoles, hh] <;> ring

private def localColors (old fresh : SupportMark) : Fin 6 → Option Bool
  | ⟨0, _⟩ => some true
  | ⟨1, _⟩ => some false
  | ⟨2, _⟩ => (frontierMark old).1
  | ⟨3, _⟩ => (frontierMark old).2
  | ⟨4, _⟩ => (frontierMark fresh).1
  | ⟨5, _⟩ => (frontierMark fresh).2

private def edgeMonochrome (colors : Fin 6 → Option Bool) (e : Fin 6 × Fin 6) : Prop :=
  ∃ b : Bool, colors e.1 = some b ∧ colors e.2 = some b

private def separatedAttachment (s fresh : SupportMark) (i : StepIndex (markState s)) : Prop :=
  edgeMonochrome (localColors s fresh) (lowEndpointRoles (stepValue (h := .positive) i).low) ∧
  edgeMonochrome (localColors s fresh) (highEndpointRoles (stepValue (h := .positive) i).high)

private instance (s fresh : SupportMark) (i : StepIndex (markState s)) :
    Decidable (separatedAttachment s fresh i) := by
  unfold separatedAttachment edgeMonochrome
  infer_instance

/-- Exact two-color attachment, with absent frontier vertices excluded. -/
private theorem separatedStep_iff (s fresh : SupportMark) (i : StepIndex (markState s)) :
    separatedStep s i = some fresh ↔
      markState fresh = stepTarget i ∧ separatedAttachment s fresh i := by
  cases s <;> cases fresh <;> fin_cases i <;> decide

/-- The attachment relation evaluates the actual two chosen endpoint pairs. -/
private theorem attachment_actual (n j : Nat) (hj : j ≤ n+1)
    (s fresh : SupportMark) (i : StepIndex (markState s))
    (color : ZMod n → Option Bool)
    (hc : ∀ a, color (roleVertex n j a) = localColors s fresh a) :
    separatedAttachment s fresh i ↔
      (∃ b : Bool,
        color (formPair n j (stepValue (h := .positive) i).low).1 = some b ∧
        color (formPair n j (stepValue (h := .positive) i).low).2 = some b) ∧
      (∃ b : Bool,
        color (formPair n (highClass n j) (stepValue (h := .positive) i).high).1 = some b ∧
        color (formPair n (highClass n j) (stepValue (h := .positive) i).high).2 = some b) := by
  rw [low_roles_actual, high_roles_actual n j hj]
  simp only [Prod.fst, Prod.snd, hc]
  rfl

/-- The intended global invariant uses actual support reachability, not charge alone. -/
private structure ActualMarkInvariant (n j : Nat) (R : Setoid (ZMod n))
    (active : ZMod n → Prop) (mark : SupportMark) : Prop where
  distinct : Function.Injective (roleVertex n j)
  semitones_separate : ¬ R.r 1 (-1)
  positive_unused : (frontierMark mark).1 = none ↔ ¬ active ((j-1 : Nat) : ZMod n)
  negative_unused : (frontierMark mark).2 = none ↔ ¬ active (-((j-1 : Nat) : ZMod n))
  positive_component : ∀ b, (frontierMark mark).1 = some b →
    active ((j-1 : Nat) : ZMod n) ∧
      R.r ((j-1 : Nat) : ZMod n) (if b then 1 else -1)
  negative_component : ∀ b, (frontierMark mark).2 = some b →
    active (-((j-1 : Nat) : ZMod n)) ∧
      R.r (-((j-1 : Nat) : ZMod n)) (if b then 1 else -1)
  no_hidden_component : ∀ v, active v → R.r v 1 ∨ R.r v (-1)


private instance : Fintype SupportMark where
  elems := {.Am, .Ap, .Dm, .Dp, .Em, .Ep, .Ex, .Hm, .Ip}
  complete m := by cases m <;> simp

/-- Constraints only on used frontier vertices; unused vertices have no color obligation. -/
private def markColors (s : SupportMark) (cp cn : Bool) : Prop :=
  (∀ b, (frontierMark s).1 = some b → cp = b) ∧
  (∀ b, (frontierMark s).2 = some b → cn = b)

private def boolRoles (cp cn xp xn : Bool) : Fin 6 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => cp
  | ⟨3, _⟩ => cn
  | ⟨4, _⟩ => xp
  | ⟨5, _⟩ => xn

private def boolAttachment (s : SupportMark) (i : StepIndex (markState s))
    (cp cn xp xn : Bool) : Prop :=
  let colors := boolRoles cp cn xp xn
  let low := lowEndpointRoles (stepValue (h := .positive) i).low
  let high := highEndpointRoles (stepValue (h := .positive) i).high
  colors low.1 = colors low.2 ∧ colors high.1 = colors high.2

private instance (s : SupportMark) (cp cn : Bool) : Decidable (markColors s cp cn) := by
  unfold markColors
  infer_instance

private instance (s : SupportMark) (i : StepIndex (markState s))
    (cp cn xp xn : Bool) : Decidable (boolAttachment s i cp cn xp xn) := by
  unfold boolAttachment
  infer_instance

private theorem transition_color_mark (s : SupportMark) (i : StepIndex (markState s))
    (cp cn xp xn : Bool) (hold : markColors s cp cn)
    (he : boolAttachment s i cp cn xp xn) :
    ∃ fresh, separatedStep s i = some fresh ∧ markState fresh = stepTarget i ∧
      markColors fresh xp xn := by
  revert cp cn xp xn
  revert s
  decide

/-- A single actual monochromatic class pair forces one of the exact separated transitions. -/
private theorem actual_transition_color_mark (n j : Nat) (hj : 1 ≤ j)
    (hjn : j ≤ n+1) (s : SupportMark) (i : StepIndex (markState s))
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (hold : markColors s (color ((j-1 : Nat) : ZMod n))
      (color (-((j-1 : Nat) : ZMod n))))
    (hl : color (formPair n j (stepValue (h := .positive) i).low).1 =
      color (formPair n j (stepValue (h := .positive) i).low).2)
    (hh : color (formPair n (highClass n j) (stepValue (h := .positive) i).high).1 =
      color (formPair n (highClass n j) (stepValue (h := .positive) i).high).2) :
    ∃ fresh, separatedStep s i = some fresh ∧ markState fresh = stepTarget i ∧
      markColors fresh (color (j : ZMod n)) (color (-(j : ZMod n))) := by
  apply transition_color_mark s i _ _ _ _ hold
  have hsub : ((j-1 : Nat) : ZMod n) = (j : ZMod n)-1 := by
    rw [Nat.cast_sub hj]; simp
  have hroles : ∀ a : Fin 6, color (roleVertex n j a) =
      boolRoles (color ((j-1 : Nat) : ZMod n))
        (color (-((j-1 : Nat) : ZMod n)))
        (color (j : ZMod n)) (color (-(j : ZMod n))) a := by
    intro a
    fin_cases a <;> simp [roleVertex, frontierVertex, boolRoles, hp, hm, hsub]
  rw [low_roles_actual n j _] at hl
  rw [high_roles_actual n j hjn _] at hh
  simpa only [boolAttachment, Prod.fst, Prod.snd, hroles] using And.intro hl hh

private inductive EvenSeparated : (m : Nat) → (s : SupportMark) →
    EvenTail .positive m (markState s) → Prop where
  | capMinus (p : EvenTail .positive 0 State.A) : EvenSeparated 0 .Am p
  | capPlus (p : EvenTail .positive 0 State.D) : EvenSeparated 0 .Dp p
  | step {m : Nat} (s fresh : SupportMark) (i : StepIndex (markState s))
      (hs : markState fresh = stepTarget i)
      (p : EvenTail .positive m (markState fresh))
      (he : separatedStep s i = some fresh) (hp : EvenSeparated m fresh p) :
      EvenSeparated (m+1) s ⟨i, hs ▸ p⟩

private inductive OddSeparated : (m : Nat) → (s : SupportMark) →
    OddTail .positive m (markState s) → Prop where
  | capPlus (p : OddTail .positive 0 State.A) : OddSeparated 0 .Ap p
  | capMinus (p : OddTail .positive 0 State.D) : OddSeparated 0 .Dm p
  | step {m : Nat} (s fresh : SupportMark) (i : StepIndex (markState s))
      (hs : markState fresh = stepTarget i)
      (p : OddTail .positive m (markState fresh))
      (he : separatedStep s i = some fresh) (hp : OddSeparated m fresh p) :
      OddSeparated (m+1) s ⟨i, hs ▸ p⟩

private def monochrome {n : Nat} (color : ZMod n → Bool)
    (e : ZMod n × ZMod n) : Prop := color e.1 = color e.2

/-- Every recursive constraint names the actual selected low and high class pair. -/
def EvenColorTail (n : Nat) (color : ZMod n → Bool) :
    {m : Nat} → {s : State} → EvenTail .positive m s → Nat → Prop
  | 0, _, p, j =>
      monochrome color (formPair n j (evenTerminalValue p).low) ∧
      monochrome color (formPair n (highClass n j) (evenTerminalValue p).high)
  | _+1, _, ⟨i, p⟩, j =>
      monochrome color (formPair n j (stepValue (h := .positive) i).low) ∧
      monochrome color (formPair n (highClass n j) (stepValue (h := .positive) i).high) ∧
      EvenColorTail n color p (j+1)

def OddColorTail (n : Nat) (color : ZMod n → Bool) :
    {m : Nat} → {s : State} → OddTail .positive m s → Nat → Prop
  | 0, _, p, j => monochrome color (formPair n j (oddTerminalValue p).label)
  | _+1, _, ⟨i, p⟩, j =>
      monochrome color (formPair n j (stepValue (h := .positive) i).low) ∧
      monochrome color (formPair n (highClass n j) (stepValue (h := .positive) i).high) ∧
      OddColorTail n color p (j+1)

private theorem even_color_cap (n j : Nat) (hj : 1 ≤ j) (hn : n = 2*j)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (s : SupportMark) (p : EvenTail .positive 0 (markState s))
    (hold : markColors s (color ((j-1 : Nat) : ZMod n))
      (color (-((j-1 : Nat) : ZMod n))))
    (he : EvenColorTail n color p j) : EvenSeparated 0 s p := by
  have hsub : ((j-1 : Nat) : ZMod n) = (j : ZMod n)-1 := by
    rw [Nat.cast_sub hj]; simp
  have hhigh : (highClass n j : ZMod n) = 1-(j : ZMod n) := by
    simp only [highClass, Nat.cast_sub (by omega : j ≤ n+1), Nat.cast_add,
      ZMod.natCast_self, Nat.cast_one, zero_add]
  have hanti : (j : ZMod n) = -(j : ZMod n) := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
    have h : j+j=n := by omega
    rw [h]; exact ZMod.natCast_self n
  have hnegHigh : -(highClass n j : ZMod n) = (j : ZMod n)-1 := by
    rw [hhigh]; ring
  have hnegSub : -((j : ZMod n)-1) = 1-(j : ZMod n) := by ring
  have hh1 : (highClass n j : ZMod n)-1 = -(j : ZMod n) := by rw [hhigh]; ring
  have hh2 : -(highClass n j : ZMod n) = (j : ZMod n)-1 := by rw [hhigh]; ring
  have hh3 : 1-(highClass n j : ZMod n) = (j : ZMod n) := by rw [hhigh]; ring
  cases s
  · exact EvenSeparated.capMinus p
  · fin_cases p
    have hold' : color ((j-1 : Nat) : ZMod n) = true := by
      simpa [markColors, frontierMark] using hold
    change (color (-1) = color (j : ZMod n)) ∧
      color ((highClass n j : ZMod n)-1) = color (-(highClass n j : ZMod n)) at he
    rw [hh1, hh2, ← hsub] at he
    have hs := he.1.trans ((congrArg color hanti).trans he.2)
    rw [hm, hold'] at hs
    cases hs
  · fin_cases p
    have hold' : color (-((j-1 : Nat) : ZMod n)) = false := by
      simpa [markColors, frontierMark] using hold
    change color (-(j : ZMod n)) = color 1 ∧
      color (highClass n j : ZMod n) = color (1-(highClass n j : ZMod n)) at he
    rw [hh3, hhigh, ← hnegSub, ← hsub] at he
    have hs := he.2.trans ((congrArg color hanti).trans he.1)
    rw [hold', hp] at hs
    cases hs
  · exact EvenSeparated.capPlus p
  all_goals exact Fin.elim0 p

private theorem odd_color_cap (n j : Nat) (hj : 1 ≤ j) (hn : n+1=2*j)
    (color : ZMod n → Bool) (hp : color 1 = true) (hm : color (-1) = false)
    (s : SupportMark) (p : OddTail .positive 0 (markState s))
    (hold : markColors s (color ((j-1 : Nat) : ZMod n))
      (color (-((j-1 : Nat) : ZMod n))))
    (he : OddColorTail n color p j) : OddSeparated 0 s p := by
  have hsub : ((j-1 : Nat) : ZMod n) = (j : ZMod n)-1 := by
    rw [Nat.cast_sub hj]; simp
  cases s
  · fin_cases p
    simp [markColors, frontierMark, OddColorTail, monochrome, oddTerminalValue,
      markState, State.A, formPair, Form.I, hsub] at hold he
    rw [hp, hold] at he
    cases he
  · exact OddSeparated.capPlus p
  · exact OddSeparated.capMinus p
  · fin_cases p
    simp [markColors, frontierMark, OddColorTail, monochrome, oddTerminalValue,
      markState, State.D, formPair, Form.VI, hsub] at hold he
    rw [hold, hm] at he
    cases he
  all_goals exact Fin.elim0 p

private theorem transport_cancel {α : Type} (F : α → Type) {a b : α}
    (h : a = b) (p : F b) : h ▸ (h.symm ▸ p) = p := by
  cases h
  rfl

private theorem even_color_transport {n m j : Nat} {s s' : State}
    (color : ZMod n → Bool) (h : s = s') (p : EvenTail .positive m s) :
    EvenColorTail n color (h ▸ p) j ↔ EvenColorTail n color p j := by
  cases h
  rfl

private theorem odd_color_transport {n m j : Nat} {s s' : State}
    (color : ZMod n → Bool) (h : s = s') (p : OddTail .positive m s) :
    OddColorTail n color (h ▸ p) j ↔ OddColorTail n color p j := by
  cases h
  rfl

private theorem even_colored_separated (n : Nat) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false) :
    {m : Nat} → (s : SupportMark) → (p : EvenTail .positive m (markState s)) →
    (j : Nat) → 3 ≤ j → n=2*(j+m) →
    markColors s (color ((j-1 : Nat) : ZMod n)) (color (-((j-1 : Nat) : ZMod n))) →
    EvenColorTail n color p j → EvenSeparated m s p
  | 0, s, p, j, hj, hn, hold, he => even_color_cap n j (by omega) (by omega)
      color hp hm s p hold he
  | m+1, s, ⟨i, p⟩, j, hj, hn, hold, he => by
      obtain ⟨fresh, hf, hs, hc⟩ := actual_transition_color_mark n j (by omega)
        (by omega) s i color hp hm hold he.1 he.2.1
      have htail : EvenColorTail n color (hs.symm ▸ p) (j+1) := by
        exact (even_color_transport color hs.symm p).mpr he.2.2
      have ht := even_colored_separated n color hp hm fresh (hs.symm ▸ p)
        (j+1) (by omega) (by omega) (by simpa using hc) htail
      have hout := EvenSeparated.step s fresh i hs (hs.symm ▸ p) hf ht
      simpa only [transport_cancel] using hout

private theorem odd_colored_separated (n : Nat) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false) :
    {m : Nat} → (s : SupportMark) → (p : OddTail .positive m (markState s)) →
    (j : Nat) → 3 ≤ j → n+1=2*(j+m) →
    markColors s (color ((j-1 : Nat) : ZMod n)) (color (-((j-1 : Nat) : ZMod n))) →
    OddColorTail n color p j → OddSeparated m s p
  | 0, s, p, j, hj, hn, hold, he => odd_color_cap n j (by omega) (by omega)
      color hp hm s p hold he
  | m+1, s, ⟨i, p⟩, j, hj, hn, hold, he => by
      obtain ⟨fresh, hf, hs, hc⟩ := actual_transition_color_mark n j (by omega)
        (by omega) s i color hp hm hold he.1 he.2.1
      have htail : OddColorTail n color (hs.symm ▸ p) (j+1) := by
        exact (odd_color_transport color hs.symm p).mpr he.2.2
      have ht := odd_colored_separated n color hp hm fresh (hs.symm ▸ p)
        (j+1) (by omega) (by omega) (by simpa using hc) htail
      have hout := OddSeparated.step s fresh i hs (hs.symm ▸ p) hf ht
      simpa only [transport_cancel] using hout

private theorem even_separated_uncons {m : Nat} {s : SupportMark}
    (i : StepIndex (markState s)) (p : EvenTail .positive m (stepTarget i))
    (h : EvenSeparated (m+1) s ⟨i, p⟩) :
    ∃ (fresh : SupportMark) (hs : markState fresh = stepTarget i),
      separatedStep s i = some fresh ∧ EvenSeparated m fresh (hs.symm ▸ p) := by
  cases h with
  | step s fresh i hs p he hp =>
      exact ⟨fresh, hs, he, by simpa only [transport_cancel] using hp⟩

private theorem odd_separated_uncons {m : Nat} {s : SupportMark}
    (i : StepIndex (markState s)) (p : OddTail .positive m (stepTarget i))
    (h : OddSeparated (m+1) s ⟨i, p⟩) :
    ∃ (fresh : SupportMark) (hs : markState fresh = stepTarget i),
      separatedStep s i = some fresh ∧ OddSeparated m fresh (hs.symm ▸ p) := by
  cases h with
  | step s fresh i hs p he hp =>
      exact ⟨fresh, hs, he, by simpa only [transport_cancel] using hp⟩

private def bitMark : Bool → SupportMark
  | false => .Am
  | true => .Dp

private theorem bit_mark_state (b : Bool) : markState (bitMark b) = bitState b := by
  cases b <;> rfl

private theorem even_separated_live {m : Nat} {s : SupportMark}
    {p : EvenTail .positive m (markState s)} (h : EvenSeparated m s p) :
    s ≠ .Ex ∧ s ≠ .Hm ∧ s ≠ .Ip := by
  cases h with
  | capMinus => decide
  | capPlus => decide
  | step s fresh i hs p he hp =>
      cases s <;> fin_cases i <;> simp_all [separatedStep]
      all_goals cases he

private theorem odd_separated_live {m : Nat} {s : SupportMark}
    {p : OddTail .positive m (markState s)} (h : OddSeparated m s p) :
    s ≠ .Ex ∧ s ≠ .Hm ∧ s ≠ .Ip := by
  cases h with
  | capMinus => decide
  | capPlus => decide
  | step s fresh i hs p he hp =>
      cases s <;> fin_cases i <;> simp_all [separatedStep]
      all_goals cases he

private theorem even_separated_three {m : Nat} (b : Bool)
    (p : EvenTail .positive (m+3) (markState (bitMark b)))
    (h : EvenSeparated (m+3) (bitMark b) p) :
    ∃ (b' : Bool) (q : EvenTail .positive m (bitState b')),
      (bit_mark_state b ▸ p) = prependEvenBlock b b' q ∧
      EvenSeparated m (bitMark b') ((bit_mark_state b').symm ▸ q) := by
  cases b
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      even_separated_uncons (s := .Am) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change EvenSeparated (m+2) .Em p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hmiddle⟩ :=
      even_separated_uncons (s := .Em) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change EvenSeparated (m+1) .Dm p at hmiddle
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      even_separated_uncons (s := .Dm) i p hmiddle
    fin_cases i <;> simp [separatedStep] at he
    all_goals cases he
    all_goals first
      | exact False.elim ((even_separated_live hlast).1 rfl)
      | exact False.elim ((even_separated_live hlast).2.1 rfl)
      | exact False.elim ((even_separated_live hlast).2.2 rfl)
      | exact ⟨false, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
      | exact ⟨true, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      even_separated_uncons (s := .Dp) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change EvenSeparated (m+2) .Ep p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hmiddle⟩ :=
      even_separated_uncons (s := .Ep) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change EvenSeparated (m+1) .Ap p at hmiddle
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      even_separated_uncons (s := .Ap) i p hmiddle
    fin_cases i <;> simp [separatedStep] at he
    all_goals cases he
    all_goals first
      | exact False.elim ((even_separated_live hlast).1 rfl)
      | exact False.elim ((even_separated_live hlast).2.1 rfl)
      | exact False.elim ((even_separated_live hlast).2.2 rfl)
      | exact ⟨false, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
      | exact ⟨true, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩

private theorem odd_separated_three {m : Nat} (b : Bool)
    (p : OddTail .positive (m+3) (markState (bitMark b)))
    (h : OddSeparated (m+3) (bitMark b) p) :
    ∃ (b' : Bool) (q : OddTail .positive m (bitState b')),
      (bit_mark_state b ▸ p) = prependOddBlock b b' q ∧
      OddSeparated m (bitMark b') ((bit_mark_state b').symm ▸ q) := by
  cases b
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      odd_separated_uncons (s := .Am) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated (m+2) .Em p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hmiddle⟩ :=
      odd_separated_uncons (s := .Em) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated (m+1) .Dm p at hmiddle
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      odd_separated_uncons (s := .Dm) i p hmiddle
    fin_cases i <;> simp [separatedStep] at he
    all_goals cases he
    all_goals first
      | exact False.elim ((odd_separated_live hlast).1 rfl)
      | exact False.elim ((odd_separated_live hlast).2.1 rfl)
      | exact False.elim ((odd_separated_live hlast).2.2 rfl)
      | exact ⟨false, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
      | exact ⟨true, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      odd_separated_uncons (s := .Dp) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated (m+2) .Ep p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hmiddle⟩ :=
      odd_separated_uncons (s := .Ep) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated (m+1) .Ap p at hmiddle
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      odd_separated_uncons (s := .Ap) i p hmiddle
    fin_cases i <;> simp [separatedStep] at he
    all_goals cases he
    all_goals first
      | exact False.elim ((odd_separated_live hlast).1 rfl)
      | exact False.elim ((odd_separated_live hlast).2.1 rfl)
      | exact False.elim ((odd_separated_live hlast).2.2 rfl)
      | exact ⟨false, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩
      | exact ⟨true, p, rfl, by
          simpa only [bitMark, bit_mark_state] using hlast⟩

private theorem odd_separated_two (b : Bool)
    (p : OddTail .positive 2 (markState (bitMark b)))
    (h : OddSeparated 2 (bitMark b) p) :
    (bit_mark_state b ▸ p) = oddWordTail 0 b (fun i => Fin.elim0 i) := by
  cases b
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      odd_separated_uncons (s := .Am) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated 1 .Em p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      odd_separated_uncons (s := .Em) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated 0 .Dm p at hlast
    fin_cases p
    rfl
  · rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hfirst⟩ :=
      odd_separated_uncons (s := .Dp) i p h
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated 1 .Ep p at hfirst
    rcases p with ⟨i, p⟩
    obtain ⟨fresh, hs, he, hlast⟩ :=
      odd_separated_uncons (s := .Ep) i p hfirst
    fin_cases i <;> simp [separatedStep] at he <;> cases he
    change OddSeparated 0 .Ap p at hlast
    fin_cases p
    rfl

private theorem even_separated_word (l : Nat) (b : Bool)
    (p : EvenTail .positive (evenWordLength l) (bitState b))
    (h : EvenSeparated (evenWordLength l) (bitMark b) ((bit_mark_state b).symm ▸ p)) :
    ∃ w : Fin l → Bool, p = evenWordTail l b w := by
  induction l generalizing b with
  | zero =>
      cases b <;> fin_cases p <;> exact ⟨fun i => Fin.elim0 i, rfl⟩
  | succ l ih =>
      obtain ⟨b', q, hq, hsep⟩ := even_separated_three (m := evenWordLength l) b
        ((bit_mark_state b).symm ▸ p) h
      have eqp : p = prependEvenBlock b b' q := by
        have hc := transport_cancel (fun s => EvenTail .positive
          (evenWordLength (l+1)) s) (bit_mark_state b) p
        exact hc.symm.trans hq
      obtain ⟨w, hw⟩ := ih b' q hsep
      rw [hw] at eqp
      refine ⟨Fin.cases b' w, ?_⟩
      simpa only [evenWordTail, Fin.cases_zero, Fin.cases_succ] using eqp

private theorem odd_separated_word (l : Nat) (b : Bool)
    (p : OddTail .positive (oddWordLength l) (bitState b))
    (h : OddSeparated (oddWordLength l) (bitMark b) ((bit_mark_state b).symm ▸ p)) :
    ∃ w : Fin l → Bool, p = oddWordTail l b w := by
  induction l generalizing b with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      have hc := transport_cancel (fun s => OddTail .positive 2 s) (bit_mark_state b) p
      exact hc.symm.trans (odd_separated_two b ((bit_mark_state b).symm ▸ p) h)
  | succ l ih =>
      obtain ⟨b', q, hq, hsep⟩ := odd_separated_three (m := oddWordLength l) b
        ((bit_mark_state b).symm ▸ p) h
      have eqp : p = prependOddBlock b b' q := by
        have hc := transport_cancel (fun s => OddTail .positive
          (oddWordLength (l+1)) s) (bit_mark_state b) p
        exact hc.symm.trans hq
      obtain ⟨w, hw⟩ := ih b' q hsep
      rw [hw] at eqp
      refine ⟨Fin.cases b' w, ?_⟩
      simpa only [oddWordTail, Fin.cases_zero, Fin.cases_succ] using eqp

private theorem even_block_separated {m : Nat} (b b' : Bool)
    (p : EvenTail .positive m (bitState b'))
    (hp : EvenSeparated m (bitMark b') ((bit_mark_state b').symm ▸ p)) :
    EvenSeparated (m+3) (bitMark b)
      ((bit_mark_state b).symm ▸ prependEvenBlock b b' p) := by
  cases b <;> cases b'
  · change EvenSeparated m .Am p at hp
    have hlast := EvenSeparated.step (m := m) .Dm .Am (0 : Fin 4)
      rfl p rfl hp
    have hmiddle := EvenSeparated.step (m := m+1) .Em .Dm (1 : Fin 2)
      rfl ⟨(0 : Fin 4), p⟩ rfl hlast
    have hfirst := EvenSeparated.step (m := m+2) .Am .Em (2 : Fin 4)
      rfl ⟨(1 : Fin 2), ⟨(0 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change EvenSeparated m .Dp p at hp
    have hlast := EvenSeparated.step (m := m) .Dm .Dp (1 : Fin 4)
      rfl p rfl hp
    have hmiddle := EvenSeparated.step (m := m+1) .Em .Dm (1 : Fin 2)
      rfl ⟨(1 : Fin 4), p⟩ rfl hlast
    have hfirst := EvenSeparated.step (m := m+2) .Am .Em (2 : Fin 4)
      rfl ⟨(1 : Fin 2), ⟨(1 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change EvenSeparated m .Am p at hp
    have hlast := EvenSeparated.step (m := m) .Ap .Am (0 : Fin 4)
      rfl p rfl hp
    have hmiddle := EvenSeparated.step (m := m+1) .Ep .Ap (0 : Fin 2)
      rfl ⟨(0 : Fin 4), p⟩ rfl hlast
    have hfirst := EvenSeparated.step (m := m+2) .Dp .Ep (2 : Fin 4)
      rfl ⟨(0 : Fin 2), ⟨(0 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change EvenSeparated m .Dp p at hp
    have hlast := EvenSeparated.step (m := m) .Ap .Dp (1 : Fin 4)
      rfl p rfl hp
    have hmiddle := EvenSeparated.step (m := m+1) .Ep .Ap (0 : Fin 2)
      rfl ⟨(1 : Fin 4), p⟩ rfl hlast
    have hfirst := EvenSeparated.step (m := m+2) .Dp .Ep (2 : Fin 4)
      rfl ⟨(0 : Fin 2), ⟨(1 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst

private theorem even_word_separated (l : Nat) (b : Bool) (w : Fin l → Bool) :
    EvenSeparated (evenWordLength l) (bitMark b)
      ((bit_mark_state b).symm ▸ evenWordTail l b w) := by
  induction l generalizing b with
  | zero =>
      cases b
      · exact EvenSeparated.capMinus _
      · exact EvenSeparated.capPlus _
  | succ l ih =>
      simpa only [evenWordTail, evenWordLength] using
        even_block_separated b (w 0) (evenWordTail l (w 0) (fun i => w i.succ))
          (ih (w 0) (fun i => w i.succ))

private theorem even_separated_word_unique (l : Nat) (b : Bool)
    (p : EvenTail .positive (evenWordLength l) (bitState b)) :
    EvenSeparated (evenWordLength l) (bitMark b) ((bit_mark_state b).symm ▸ p) ↔
      ∃! w : Fin l → Bool, p = evenWordTail l b w := by
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := even_separated_word l b p hp
    refine ⟨w, hw, ?_⟩
    intro w' hw'
    exact even_word_tail_injective l b (hw'.symm.trans hw)
  · rintro ⟨w, rfl, _⟩
    exact even_word_separated l b w

private theorem odd_block_separated {m : Nat} (b b' : Bool)
    (p : OddTail .positive m (bitState b'))
    (hp : OddSeparated m (bitMark b') ((bit_mark_state b').symm ▸ p)) :
    OddSeparated (m+3) (bitMark b)
      ((bit_mark_state b).symm ▸ prependOddBlock b b' p) := by
  cases b <;> cases b'
  · change OddSeparated m .Am p at hp
    have hlast := OddSeparated.step (m := m) .Dm .Am (0 : Fin 4)
      rfl p rfl hp
    have hmiddle := OddSeparated.step (m := m+1) .Em .Dm (1 : Fin 2)
      rfl ⟨(0 : Fin 4), p⟩ rfl hlast
    have hfirst := OddSeparated.step (m := m+2) .Am .Em (2 : Fin 4)
      rfl ⟨(1 : Fin 2), ⟨(0 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change OddSeparated m .Dp p at hp
    have hlast := OddSeparated.step (m := m) .Dm .Dp (1 : Fin 4)
      rfl p rfl hp
    have hmiddle := OddSeparated.step (m := m+1) .Em .Dm (1 : Fin 2)
      rfl ⟨(1 : Fin 4), p⟩ rfl hlast
    have hfirst := OddSeparated.step (m := m+2) .Am .Em (2 : Fin 4)
      rfl ⟨(1 : Fin 2), ⟨(1 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change OddSeparated m .Am p at hp
    have hlast := OddSeparated.step (m := m) .Ap .Am (0 : Fin 4)
      rfl p rfl hp
    have hmiddle := OddSeparated.step (m := m+1) .Ep .Ap (0 : Fin 2)
      rfl ⟨(0 : Fin 4), p⟩ rfl hlast
    have hfirst := OddSeparated.step (m := m+2) .Dp .Ep (2 : Fin 4)
      rfl ⟨(0 : Fin 2), ⟨(0 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst
  · change OddSeparated m .Dp p at hp
    have hlast := OddSeparated.step (m := m) .Ap .Dp (1 : Fin 4)
      rfl p rfl hp
    have hmiddle := OddSeparated.step (m := m+1) .Ep .Ap (0 : Fin 2)
      rfl ⟨(1 : Fin 4), p⟩ rfl hlast
    have hfirst := OddSeparated.step (m := m+2) .Dp .Ep (2 : Fin 4)
      rfl ⟨(0 : Fin 2), ⟨(1 : Fin 4), p⟩⟩ rfl hmiddle
    exact hfirst

private theorem odd_word_separated (l : Nat) (b : Bool) (w : Fin l → Bool) :
    OddSeparated (oddWordLength l) (bitMark b)
      ((bit_mark_state b).symm ▸ oddWordTail l b w) := by
  induction l generalizing b with
  | zero =>
      cases b
      · exact OddSeparated.step (m := 1) .Am .Em (2 : Fin 4) rfl _ rfl
          (OddSeparated.step (m := 0) .Em .Dm (1 : Fin 2) rfl _ rfl
            (OddSeparated.capMinus _))
      · exact OddSeparated.step (m := 1) .Dp .Ep (2 : Fin 4) rfl _ rfl
          (OddSeparated.step (m := 0) .Ep .Ap (0 : Fin 2) rfl _ rfl
            (OddSeparated.capPlus _))
  | succ l ih =>
      simpa only [oddWordTail, oddWordLength] using
        odd_block_separated b (w 0) (oddWordTail l (w 0) (fun i => w i.succ))
          (ih (w 0) (fun i => w i.succ))

private theorem odd_separated_word_unique (l : Nat) (b : Bool)
    (p : OddTail .positive (oddWordLength l) (bitState b)) :
    OddSeparated (oddWordLength l) (bitMark b) ((bit_mark_state b).symm ▸ p) ↔
      ∃! w : Fin l → Bool, p = oddWordTail l b w := by
  constructor
  · intro hp
    obtain ⟨w, hw⟩ := odd_separated_word l b p hp
    refine ⟨w, hw, ?_⟩
    intro w' hw'
    exact odd_word_tail_injective l b (hw'.symm.trans hw)
  · rintro ⟨w, rfl, _⟩
    exact odd_word_separated l b w


theorem even_color_edges (n : Nat) (color : ZMod n → Bool) :
    {m : Nat} → {s : State} → (p : EvenTail .positive m s) → (j : Nat) →
    n = 2 * (j + m) →
    (EvenColorTail n color p j ↔
      ∀ e ∈ formsEdges n j (evenTailLowForms p ++ (evenTailHighForms p).reverse),
        monochrome color e)
  | 0, s, p, j, hn => by
      have hk : highClass n j = j + 1 := by simp only [highClass]; omega
      simp [EvenColorTail, evenTailLowForms, evenTailHighForms, formsEdges, hk]
  | m+1, s, ⟨i, p⟩, j, hn => by
      rw [even_edges_peel i p (by omega)]
      constructor
      · intro he e hmem
        simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hmem
        rcases hmem with rfl | hmem | rfl
        · exact he.1
        · exact (even_color_edges n color p (j+1) (by omega)).mp he.2.2 e hmem
        · exact he.2.1
      · intro he
        refine ⟨he _ (by simp), he _ (by simp), ?_⟩
        apply (even_color_edges n color p (j+1) (by omega)).mpr
        intro e hm
        exact he e (by simp [hm])

theorem odd_color_edges (n : Nat) (color : ZMod n → Bool) :
    {m : Nat} → {s : State} → (p : OddTail .positive m s) → (j : Nat) →
    n + 1 = 2 * (j + m) →
    (OddColorTail n color p j ↔
      ∀ e ∈ formsEdges n j (oddTailLowForms p ++ (oddTailHighForms p).reverse),
        monochrome color e)
  | 0, s, p, j, hn => by
      simp [OddColorTail, oddTailLowForms, oddTailHighForms, formsEdges]
  | m+1, s, ⟨i, p⟩, j, hn => by
      rw [odd_edges_peel i p (by omega)]
      constructor
      · intro he e hmem
        simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hmem
        rcases hmem with rfl | hmem | rfl
        · exact he.1
        · exact (odd_color_edges n color p (j+1) (by omega)).mp he.2.2 e hmem
        · exact he.2.1
      · intro he
        refine ⟨he _ (by simp), he _ (by simp), ?_⟩
        apply (odd_color_edges n color p (j+1) (by omega)).mpr
        intro e hm
        exact he e (by simp [hm])

private theorem start_color_mark (n : Nat) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false) (b : Bool)
    (he : monochrome color (formPair n 2
      (startValue (h := .positive) (if b then 1 else 0)).label)) :
    markColors (bitMark b) (color 2) (color (-2)) := by
  have htwo : (2 : ZMod n) - 1 = 1 := by ring
  have htwo' : 1 - (2 : ZMod n) = -1 := by ring
  cases b <;>
    simpa [monochrome, startValue, starts, bitMark, markColors, frontierMark,
      formPair, Form.II, Form.IV, htwo, htwo', hp, hm] using he

private def evenBitPath {m : Nat} : (b : Bool) →
    EvenTail .positive m (bitState b) → EvenPath .positive m
  | false, p => ⟨0, p⟩
  | true, p => ⟨1, p⟩

private def oddBitPath {m : Nat} : (b : Bool) →
    OddTail .positive m (bitState b) → OddPath .positive m
  | false, p => ⟨0, p⟩
  | true, p => ⟨1, p⟩

/-- A native class-order coloring forces a unique absolute successor word. -/
private theorem even_class_coloring_word (l : Nat) (b : Bool) (n : Nat)
    (hn : n = 2 * (3 + evenWordLength l)) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (p : EvenTail .positive (evenWordLength l) (bitState b))
    (he : ∀ e ∈ formsEdges n 2
      (evenPathForms (evenBitPath b p)), monochrome color e) :
    ∃! w : Fin l → Bool, p = evenWordTail l b w := by
  have hstart : monochrome color (formPair n 2
      (startValue (h := .positive) (if b then 1 else 0)).label) := by
    cases b <;> exact he _ (by simp [evenBitPath, evenPathForms, formsEdges])
  have hmark := start_color_mark n color hp hm b hstart
  have htail : EvenColorTail n color p 3 := by
    apply (even_color_edges n color p 3 hn).mpr
    intro e hmem
    cases b <;> exact he e (List.mem_cons_of_mem _ hmem)
  apply (even_separated_word_unique l b p).mp
  apply even_colored_separated n color hp hm (bitMark b)
    ((bit_mark_state b).symm ▸ p) 3 (by omega) hn
  · simpa using hmark
  · exact (even_color_transport color (bit_mark_state b).symm p).mpr htail

/-- The odd singleton cap has the same forced absolute word, at its own length. -/
private theorem odd_class_coloring_word (l : Nat) (b : Bool) (n : Nat)
    (hn : n + 1 = 2 * (3 + oddWordLength l)) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (p : OddTail .positive (oddWordLength l) (bitState b))
    (he : ∀ e ∈ formsEdges n 2
      (oddPathForms (oddBitPath b p)), monochrome color e) :
    ∃! w : Fin l → Bool, p = oddWordTail l b w := by
  have hstart : monochrome color (formPair n 2
      (startValue (h := .positive) (if b then 1 else 0)).label) := by
    cases b <;> exact he _ (by simp [oddBitPath, oddPathForms, formsEdges])
  have hmark := start_color_mark n color hp hm b hstart
  have htail : OddColorTail n color p 3 := by
    apply (odd_color_edges n color p 3 hn).mpr
    intro e hmem
    cases b <;> exact he e (List.mem_cons_of_mem _ hmem)
  apply (odd_separated_word_unique l b p).mp
  apply odd_colored_separated n color hp hm (bitMark b)
    ((bit_mark_state b).symm ▸ p) 3 (by omega) hn
  · simpa using hmark
  · exact (odd_color_transport color (bit_mark_state b).symm p).mpr htail

private theorem even_path_coloring_word (l n : Nat)
    (hn : n = 2 * (3 + evenWordLength l)) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (p : EvenPath .positive (evenWordLength l))
    (he : ∀ e ∈ formsEdges n 2 (evenPathForms p), monochrome color e) :
    ∃ (b : Bool) (w : Fin l → Bool), p = evenWordPath l b w := by
  rcases p with ⟨i, p⟩
  fin_cases i
  · obtain ⟨w, hw, _⟩ := even_class_coloring_word l false n hn color hp hm p he
    exact ⟨false, w, by cases hw; rfl⟩
  · obtain ⟨w, hw, _⟩ := even_class_coloring_word l true n hn color hp hm p he
    exact ⟨true, w, by cases hw; rfl⟩

private theorem odd_path_coloring_word (l n : Nat)
    (hn : n + 1 = 2 * (3 + oddWordLength l)) (color : ZMod n → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (p : OddPath .positive (oddWordLength l))
    (he : ∀ e ∈ formsEdges n 2 (oddPathForms p), monochrome color e) :
    ∃ (b : Bool) (w : Fin l → Bool), p = oddWordPath l b w := by
  rcases p with ⟨i, p⟩
  fin_cases i
  · obtain ⟨w, hw, _⟩ := odd_class_coloring_word l false n hn color hp hm p he
    exact ⟨false, w, by cases hw; rfl⟩
  · obtain ⟨w, hw, _⟩ := odd_class_coloring_word l true n hn color hp hm p he
    exact ⟨true, w, by cases hw; rfl⟩

private theorem even_forms_transport {m k : Nat} (h : m = k)
    (p : EvenPath .positive m) : evenPathForms (h ▸ p) = evenPathForms p := by
  cases h
  rfl

private theorem odd_forms_transport {m k : Nat} (h : m = k)
    (p : OddPath .positive m) : oddPathForms (h ▸ p) = oddPathForms p := by
  cases h
  rfl

private theorem even_zero_transport {m k : Nat} (h : m = k)
    (p : {p : EvenPath .positive m // evenPathCharge p = 0}) :
    (h ▸ p).1 = h ▸ p.1 := by
  cases h
  rfl

private theorem odd_zero_transport {m k : Nat} (h : m = k)
    (p : {p : OddPath .positive m // oddPathCharge p = 0}) :
    (h ▸ p).1 = h ▸ p.1 := by
  cases h
  rfl

/-- The inverse reads every original native class label, with no closure constraint. -/
theorem even_native_separation_code (r : Nat) (hr : 1 ≤ r)
    (p : EvenPath .positive (3*r-3)) (color : ZMod (3*(2*r)) → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (he : ∀ i, color (chosenPair (evenPathChoices r hr p) i).1 =
      color (chosenPair (evenPathChoices r hr p) i).2) :
    ∃ (b : Bool) (w : Fin (r-1) → Bool), p = (evenCodedPath r hr b w).1 := by
  have hl : evenWordLength (r-1) = 3*r-3 := by rw [even_word_length]; omega
  let q : EvenPath .positive (evenWordLength (r-1)) := hl.symm ▸ p
  have hforms : evenPathForms q = evenPathForms p := even_forms_transport hl.symm p
  have hedges : ∀ e ∈ formsEdges (3*(2*r)) 2
      (choiceForms (evenPathChoices r hr p)), monochrome color e := by
    intro e hmem
    obtain ⟨i, rfl⟩ := (choice_edges_mem _ e).mp hmem
    exact he i
  rw [even_decode_forms] at hedges
  obtain ⟨b, w, hcode⟩ := even_path_coloring_word (r-1) (3*(2*r))
    (by omega) color hp hm q (by simpa only [hforms] using hedges)
  refine ⟨b, w, ?_⟩
  have hc : (evenCodedPath r hr b w).1 = hl ▸ evenWordPath (r-1) b w :=
    even_zero_transport hl _
  rw [hc, ← hcode]
  exact (transport_cancel (fun k => EvenPath .positive k) hl p).symm

/-- The native odd inverse includes its singleton cap and all original labels. -/
theorem odd_native_separation_code (r : Nat) (hr : 1 ≤ r)
    (p : OddPath .positive (3*r-1)) (color : ZMod (3*(2*r+1)) → Bool)
    (hp : color 1 = true) (hm : color (-1) = false)
    (he : ∀ i, color (chosenPair (oddPathChoices r hr p) i).1 =
      color (chosenPair (oddPathChoices r hr p) i).2) :
    ∃ (b : Bool) (w : Fin (r-1) → Bool), p = (oddCodedPath r hr b w).1 := by
  have hl : oddWordLength (r-1) = 3*r-1 := by rw [odd_word_length]; omega
  let q : OddPath .positive (oddWordLength (r-1)) := hl.symm ▸ p
  have hforms : oddPathForms q = oddPathForms p := odd_forms_transport hl.symm p
  have hedges : ∀ e ∈ formsEdges (3*(2*r+1)) 2
      (choiceForms (oddPathChoices r hr p)), monochrome color e := by
    intro e hmem
    obtain ⟨i, rfl⟩ := (choice_edges_mem _ e).mp hmem
    exact he i
  rw [odd_decode_forms] at hedges
  obtain ⟨b, w, hcode⟩ := odd_path_coloring_word (r-1) (3*(2*r+1))
    (by omega) color hp hm q (by simpa only [hforms] using hedges)
  refine ⟨b, w, ?_⟩
  have hc : (oddCodedPath r hr b w).1 = hl ▸ oddWordPath (r-1) b w :=
    odd_zero_transport hl _
  rw [hc, ← hcode]
  exact (transport_cancel (fun k => OddPath .positive k) hl p).symm

end D5.S3.Combinatorics.Zigzag
