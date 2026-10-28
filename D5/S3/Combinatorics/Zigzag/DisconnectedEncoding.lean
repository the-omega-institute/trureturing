/- GID: D5/S3/Combinatorics/Zigzag/DisconnectedEncoding
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/DisconnectedEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Labelled native paths and their absolute successor-state words. -/

import D5.S3.Combinatorics.Zigzag.ActiveSupport
import D5.S3.Combinatorics.Zigzag.OddPaths
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Zigzag
abbrev bitState (b : Bool) : State := if b then State.D else State.A
private def bitCharge (b : Bool) : Int := if b then 1 else 0
def prependEvenBlock {m : Nat} : (b b' : Bool) →
    EvenTail .positive m (bitState b') → EvenTail .positive (m+3) (bitState b)
  | false, false, p => ⟨(2 : Fin 4), ⟨(1 : Fin 2), ⟨(0 : Fin 4), p⟩⟩⟩
  | false, true, p => ⟨(2 : Fin 4), ⟨(1 : Fin 2), ⟨(1 : Fin 4), p⟩⟩⟩
  | true, false, p => ⟨(2 : Fin 4), ⟨(0 : Fin 2), ⟨(0 : Fin 4), p⟩⟩⟩
  | true, true, p => ⟨(2 : Fin 4), ⟨(0 : Fin 2), ⟨(1 : Fin 4), p⟩⟩⟩
def prependOddBlock {m : Nat} : (b b' : Bool) →
    OddTail .positive m (bitState b') → OddTail .positive (m+3) (bitState b)
  | false, false, p => ⟨(2 : Fin 4), ⟨(1 : Fin 2), ⟨(0 : Fin 4), p⟩⟩⟩
  | false, true, p => ⟨(2 : Fin 4), ⟨(1 : Fin 2), ⟨(1 : Fin 4), p⟩⟩⟩
  | true, false, p => ⟨(2 : Fin 4), ⟨(0 : Fin 2), ⟨(0 : Fin 4), p⟩⟩⟩
  | true, true, p => ⟨(2 : Fin 4), ⟨(0 : Fin 2), ⟨(1 : Fin 4), p⟩⟩⟩
private theorem even_block_charge {m : Nat} (b b' : Bool)
    (p : EvenTail .positive m (bitState b')) :
    evenTailCharge (h := .positive) (prependEvenBlock b b' p) =
      bitCharge b' - bitCharge b + evenTailCharge (h := .positive) p := by
  cases b <;> cases b' <;>
    simp [prependEvenBlock, bitState, bitCharge, evenTailCharge, stepValue,
      positiveStepLabel, stepTarget, stepTargets, State.A, State.D, State.E] <;> omega
private theorem odd_block_charge {m : Nat} (b b' : Bool)
    (p : OddTail .positive m (bitState b')) :
    oddTailCharge (h := .positive) (prependOddBlock b b' p) =
      bitCharge b' - bitCharge b + oddTailCharge (h := .positive) p := by
  cases b <;> cases b' <;>
    simp [prependOddBlock, bitState, bitCharge, oddTailCharge, stepValue,
      positiveStepLabel, stepTarget, stepTargets, State.A, State.D, State.E] <;> omega
def evenFinal : (b : Bool) → EvenTail .positive 0 (bitState b)
  | false => (0 : Fin 1)
  | true => (0 : Fin 1)
def oddFinal : (b : Bool) → OddTail .positive 2 (bitState b)
  | false => ⟨(2 : Fin 4), ⟨(1 : Fin 2), (0 : Fin 1)⟩⟩
  | true => ⟨(2 : Fin 4), ⟨(0 : Fin 2), (0 : Fin 1)⟩⟩
private theorem even_final_charge (b : Bool) : evenTailCharge (h := .positive) (evenFinal b) = -bitCharge b := by
  cases b <;> rfl
private theorem odd_final_charge (b : Bool) : oddTailCharge (h := .positive) (oddFinal b) = -bitCharge b := by
  cases b <;>
    simp [oddFinal, bitState, bitCharge, oddTailCharge, stepValue,
      positiveStepLabel, stepTarget, stepTargets, oddTerminalValue, State.A, State.D, State.E]
def evenWordLength : Nat → Nat
  | 0 => 0
  | l+1 => evenWordLength l + 3
def oddWordLength : Nat → Nat
  | 0 => 2
  | l+1 => oddWordLength l + 3
theorem even_word_length (l : Nat) : evenWordLength l = 3*l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [evenWordLength, ih]; omega
theorem odd_word_length (l : Nat) : oddWordLength l = 3*l+2 := by
  induction l with
  | zero => rfl
  | succ l ih => simp [oddWordLength, ih]; omega
def evenWordTail : (l : Nat) → (b : Bool) → (Fin l → Bool) →
    EvenTail .positive (evenWordLength l) (bitState b)
  | 0, b, _ => evenFinal b
  | l+1, b, w => prependEvenBlock b (w 0)
      (evenWordTail l (w 0) (fun i => w i.succ))
def oddWordTail : (l : Nat) → (b : Bool) → (Fin l → Bool) →
    OddTail .positive (oddWordLength l) (bitState b)
  | 0, b, _ => oddFinal b
  | l+1, b, w => prependOddBlock b (w 0)
      (oddWordTail l (w 0) (fun i => w i.succ))
private theorem even_word_tail_charge (l : Nat) (b : Bool) (w : Fin l → Bool) :
    evenTailCharge (h := .positive) (evenWordTail l b w) = -bitCharge b := by
  induction l generalizing b with
  | zero => exact even_final_charge b
  | succ l ih =>
      change evenTailCharge (h := .positive) (prependEvenBlock b (w 0)
        (evenWordTail l (w 0) (fun i => w i.succ))) = -bitCharge b
      rw [even_block_charge, ih]
      ring
private theorem odd_word_tail_charge (l : Nat) (b : Bool) (w : Fin l → Bool) :
    oddTailCharge (h := .positive) (oddWordTail l b w) = -bitCharge b := by
  induction l generalizing b with
  | zero => exact odd_final_charge b
  | succ l ih =>
      change oddTailCharge (h := .positive) (prependOddBlock b (w 0)
        (oddWordTail l (w 0) (fun i => w i.succ))) = -bitCharge b
      rw [odd_block_charge, ih]
      ring
def evenWordPath (l : Nat) : (b : Bool) → (Fin l → Bool) →
    EvenPath .positive (evenWordLength l)
  | false, w => ⟨0, evenWordTail l false w⟩
  | true, w => ⟨1, evenWordTail l true w⟩
def oddWordPath (l : Nat) : (b : Bool) → (Fin l → Bool) →
    OddPath .positive (oddWordLength l)
  | false, w => ⟨0, oddWordTail l false w⟩
  | true, w => ⟨1, oddWordTail l true w⟩
private theorem even_word_path_charge (l : Nat) (b : Bool) (w : Fin l → Bool) :
    evenPathCharge (h := .positive) (evenWordPath l b w) = 0 := by
  cases b
  · change 0 + evenTailCharge (h := .positive) (evenWordTail l false w) = 0
    rw [even_word_tail_charge]
    rfl
  · change 1 + evenTailCharge (h := .positive) (evenWordTail l true w) = 0
    rw [even_word_tail_charge]
    rfl

private theorem odd_word_path_charge (l : Nat) (b : Bool) (w : Fin l → Bool) :
    oddPathCharge (h := .positive) (oddWordPath l b w) = 0 := by
  cases b
  · change 0 + oddTailCharge (h := .positive) (oddWordTail l false w) = 0
    rw [odd_word_tail_charge]
    rfl
  · change 1 + oddTailCharge (h := .positive) (oddWordTail l true w) = 0
    rw [odd_word_tail_charge]
    rfl

theorem even_word_tail_injective (l : Nat) (b : Bool) :
    Function.Injective (evenWordTail l b) := by
  induction l generalizing b with
  | zero => intro w w' _; exact Subsingleton.elim _ _
  | succ l ih =>
      intro w w' he
      have head : w 0 = w' 0 := by
        cases b <;> cases hw : w 0 <;> cases hw' : w' 0
        all_goals simp only [evenWordTail] at he
        all_goals rw [hw, hw'] at he
        all_goals dsimp only [prependEvenBlock] at he
        all_goals first | rfl | skip
        all_goals
          have h1 := eq_of_heq (PSigma.mk.inj he).2
          have h2 := eq_of_heq (PSigma.mk.inj h1).2
          have h3 := (PSigma.mk.inj h2).1
          have hv := congrArg Fin.val h3
          norm_num at hv
      have tail : (fun i : Fin l => w i.succ) = (fun i : Fin l => w' i.succ) := by
        apply ih (w 0)
        simp only [evenWordTail] at he
        rw [← head] at he
        cases b <;> cases hw : w 0
        all_goals rw [hw] at he
        all_goals dsimp only [prependEvenBlock] at he
        all_goals
          have h1 := eq_of_heq (PSigma.mk.inj he).2
          have h2 := eq_of_heq (PSigma.mk.inj h1).2
          exact eq_of_heq (PSigma.mk.inj h2).2
      funext i
      refine Fin.cases head (fun i => congrFun tail i) i
theorem odd_word_tail_injective (l : Nat) (b : Bool) :
    Function.Injective (oddWordTail l b) := by
  induction l generalizing b with
  | zero => intro w w' _; exact Subsingleton.elim _ _
  | succ l ih =>
      intro w w' he
      have head : w 0 = w' 0 := by
        cases b <;> cases hw : w 0 <;> cases hw' : w' 0
        all_goals simp only [oddWordTail] at he
        all_goals rw [hw, hw'] at he
        all_goals dsimp only [prependOddBlock] at he
        all_goals first | rfl | skip
        all_goals
          have h1 := eq_of_heq (PSigma.mk.inj he).2
          have h2 := eq_of_heq (PSigma.mk.inj h1).2
          have h3 := (PSigma.mk.inj h2).1
          have hv := congrArg Fin.val h3
          norm_num at hv
      have tail : (fun i : Fin l => w i.succ) = (fun i : Fin l => w' i.succ) := by
        apply ih (w 0)
        simp only [oddWordTail] at he
        rw [← head] at he
        cases b <;> cases hw : w 0
        all_goals rw [hw] at he
        all_goals dsimp only [prependOddBlock] at he
        all_goals
          have h1 := eq_of_heq (PSigma.mk.inj he).2
          have h2 := eq_of_heq (PSigma.mk.inj h1).2
          exact eq_of_heq (PSigma.mk.inj h2).2
      funext i
      refine Fin.cases head (fun i => congrFun tail i) i

def evenCodedPath (r : Nat) (hr : 1 ≤ r) (b : Bool) (w : Fin (r-1) → Bool) :
    {p : EvenPath .positive (3*r-3) // evenPathCharge (h := .positive) p = 0} := by
  have hlen : evenWordLength (r-1) = 3*r-3 := by rw [even_word_length]; omega
  exact hlen ▸ ⟨evenWordPath (r-1) b w, even_word_path_charge (r-1) b w⟩
def oddCodedPath (r : Nat) (hr : 1 ≤ r) (b : Bool) (w : Fin (r-1) → Bool) :
    {p : OddPath .positive (3*r-1) // oddPathCharge (h := .positive) p = 0} := by
  have hlen : oddWordLength (r-1) = 3*r-1 := by rw [odd_word_length]; omega
  exact hlen ▸ ⟨oddWordPath (r-1) b w, odd_word_path_charge (r-1) b w⟩
/-- Outputs are literal native labelled choices, not an independently counted automaton. -/
def evenCodedChoice (r : Nat) (hr : 1 ≤ r) (b : Bool) (w : Fin (r-1) → Bool) :
    {c : Choices (2*r) // Balanced c} :=
  evenZeroPathChoices r hr (Sum.inl (evenCodedPath r hr b w))
def oddCodedChoice (r : Nat) (hr : 1 ≤ r) (b : Bool) (w : Fin (r-1) → Bool) :
    {c : Choices (2*r+1) // Balanced c} :=
  oddZeroPathChoices r hr (Sum.inl (oddCodedPath r hr b w))

private theorem even_word_path_injective (l : Nat) :
    Function.Injective (fun x : Bool × (Fin l → Bool) => evenWordPath l x.1 x.2) := by
  rintro ⟨b, w⟩ ⟨b', w'⟩ he
  cases b <;> cases b'
  · have ht := eq_of_heq (PSigma.mk.inj he).2
    exact Prod.ext rfl (even_word_tail_injective l false ht)
  · have hh := (PSigma.mk.inj he).1
    have hv := congrArg Fin.val hh
    norm_num at hv
  · have hh := (PSigma.mk.inj he).1
    have hv := congrArg Fin.val hh
    norm_num at hv
  · have ht := eq_of_heq (PSigma.mk.inj he).2
    exact Prod.ext rfl (even_word_tail_injective l true ht)

private theorem odd_word_path_injective (l : Nat) :
    Function.Injective (fun x : Bool × (Fin l → Bool) => oddWordPath l x.1 x.2) := by
  rintro ⟨b, w⟩ ⟨b', w'⟩ he
  cases b <;> cases b'
  · have ht := eq_of_heq (PSigma.mk.inj he).2
    exact Prod.ext rfl (odd_word_tail_injective l false ht)
  · have hh := (PSigma.mk.inj he).1
    have hv := congrArg Fin.val hh
    norm_num at hv
  · have hh := (PSigma.mk.inj he).1
    have hv := congrArg Fin.val hh
    norm_num at hv
  · have ht := eq_of_heq (PSigma.mk.inj he).2
    exact Prod.ext rfl (odd_word_tail_injective l true ht)

private theorem eq_of_transport_eq {α : Type} {F : α → Type} {a b : α}
    (h : a = b) {p q : F a} (he : h ▸ p = h ▸ q) : p = q := by
  cases h
  exact he

/-- No two absolute words or initial bits produce the same native labelled choice. -/
theorem evenCodedChoice_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (fun x : Bool × (Fin (r-1) → Bool) => evenCodedChoice r hr x.1 x.2) := by
  rintro ⟨b, w⟩ ⟨b', w'⟩ he
  have hc : evenCodedPath r hr b w = evenCodedPath r hr b' w' :=
    Sum.inl.inj ((evenBalancedChoicesEquiv r hr).symm.injective he)
  have hl : evenWordLength (r-1) = 3*r-3 := by rw [even_word_length]; omega
  have hw : (⟨evenWordPath (r-1) b w, even_word_path_charge (r-1) b w⟩ :
      {p : EvenPath .positive (evenWordLength (r-1)) // evenPathCharge p = 0}) =
      ⟨evenWordPath (r-1) b' w', even_word_path_charge (r-1) b' w'⟩ :=
    eq_of_transport_eq (F := fun k =>
      {p : EvenPath .positive k // evenPathCharge p = 0}) hl hc
  exact even_word_path_injective (r-1) (congrArg Subtype.val hw)

/-- The odd singleton boundary also preserves every initial bit and absolute word. -/
theorem oddCodedChoice_injective (r : Nat) (hr : 1 ≤ r) :
    Function.Injective (fun x : Bool × (Fin (r-1) → Bool) => oddCodedChoice r hr x.1 x.2) := by
  rintro ⟨b, w⟩ ⟨b', w'⟩ he
  have hc : oddCodedPath r hr b w = oddCodedPath r hr b' w' :=
    Sum.inl.inj ((oddBalancedChoicesEquiv r hr).symm.injective he)
  have hl : oddWordLength (r-1) = 3*r-1 := by rw [odd_word_length]; omega
  have hw : (⟨oddWordPath (r-1) b w, odd_word_path_charge (r-1) b w⟩ :
      {p : OddPath .positive (oddWordLength (r-1)) // oddPathCharge p = 0}) =
      ⟨oddWordPath (r-1) b' w', odd_word_path_charge (r-1) b' w'⟩ :=
    eq_of_transport_eq (F := fun k =>
      {p : OddPath .positive k // oddPathCharge p = 0}) hl hc
  exact odd_word_path_injective (r-1) (congrArg Subtype.val hw)

end D5.S3.Combinatorics.Zigzag
