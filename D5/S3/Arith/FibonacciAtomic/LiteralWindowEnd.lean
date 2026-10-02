/- GID: D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LiteralWindowEnd
   mirror-E: none(waiver:exact-executable-window-language)
   anchors: []
   utility: none
   digest: Successful End queries are exactly the terminally trimmed legal three-bit words. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S3.Arith.ZeckendorfFutureKernel
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd

open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Arith.ZeckendorfFutureKernel (legal value)

/-- Window bits are written from low to high. -/
inductive Window
  | zero | low | middle | ends | high
  deriving DecidableEq

instance : Fintype Window where
  elems := {.zero, .low, .middle, .ends, .high}
  complete b := by cases b <;> simp

def bits : Window -> List Bool
  | .zero => [false, false, false]
  | .low => [true, false, false]
  | .middle => [false, true, false]
  | .ends => [true, false, true]
  | .high => [false, false, true]

def first : Window -> Bool
  | .low | .ends => true
  | _ => false

def last : Window -> Bool
  | .ends | .high => true
  | _ => false

def nonzero (b : Window) : Bool := b != .zero

def flatten (w : List Window) : List Bool := w.flatMap bits

/-- `none` is the absorbing illegal-seam state. The second live field is
replaced by the current window flag, including on an all-zero window. -/
def step : Option (Bool × Bool) -> Window -> Option (Bool × Bool)
  | none, _ => none
  | some (s, _), b => if s && first b then none else some (last b, nonzero b)

def run : Option (Bool × Bool) -> List Window -> Option (Bool × Bool)
  | q, [] => q
  | q, b :: w => run (step q b) w

def endable (q : Option (Bool × Bool)) : Bool := q.any Prod.snd

/-- End is queried once, after the entire literal word. The single error is
`none`; numeric evaluation reuses the low-to-high Fibonacci evaluator. -/
def observe {Y : Type*} (out : Nat -> Y) (s E : Bool) (r u v : Nat)
    (w : List Window) : Option Y :=
  if endable (run (some (s, E)) w) then some (out (r + value u v (flatten w)))
  else none

def initialized (epsilon : Bool) (w : List Window) : Option Nat :=
  observe id epsilon epsilon (if epsilon then 1 else 0) 2 3 w

def initialIndex (H : Nat) (epsilon : Bool) (w : List Window) : Option Nat :=
  observe (fun N => H / Nat.gcd N H) epsilon epsilon
    (if epsilon then 1 else 0) 2 3 w

def query (r u v : Nat) (w : List Window) : Option Nat :=
  observe id true true r u v w

def gcdQuery (H r u v : Nat) (w : List Window) : Option Nat :=
  observe (fun N => Nat.gcd N H) true true r u v w

/-- Remove only terminal whole zero windows, retaining internal and leading
zero windows and every nonzero terminal window. -/
def trim : List Window -> List Window
  | [] => []
  | b :: w =>
      let tail := trim w
      if b = .zero /\ tail = [] then [] else b :: tail

def pad (t : Nat) (w : List Window) : List Window :=
  w ++ List.replicate (t - w.length) .zero

/-- Group a legal low-to-high bit stream into its five possible windows.
Illegal triples map to zero here; they never occur in the proved inverse. -/
def triple : Bool -> Bool -> Bool -> Window
  | false, false, false => .zero
  | true, false, false => .low
  | false, true, false => .middle
  | true, false, true => .ends
  | false, false, true => .high
  | _, _, _ => .zero

def pack : List Bool -> List Window
  | a :: b :: c :: tail => triple a b c :: pack tail
  | _ => []

def PaddedWord (t : Nat) :=
  {w : List Window // w.length = t ∧ legal true (flatten w)}

def Success (w : List Window) : Prop := endable (run (some (true, true)) w) = true

def SuccessfulWord (t : Nat) := {w : List Window // w.length <= t /\ Success w}

def LiteralWord (t : Nat) := {w : List Window // w.length <= t}

def IndependentWord : Nat -> Type
  | 0 => PUnit
  | t + 1 => {f : Fin (3 * (t + 1) - 1) -> Bool // Adm (3 * (t + 1) - 1) f}

def independentBits : (t : Nat) -> IndependentWord t -> List Bool
  | 0, _ => []
  | _ + 1, x => false :: List.ofFn x.val

def encode (t : Nat) (x : IndependentWord t) : List Window :=
  trim (pack (independentBits t x))

def BitWord (t : Nat) := {bs : List Bool // bs.length = 3 * t ∧ legal true bs}

instance (t : Nat) : Finite (SuccessfulWord t) :=
  (List.finite_length_le Window t).subset
    (show {w : List Window | w.length <= t /\ Success w} ⊆
      {w : List Window | w.length <= t} from by intro w hw; exact hw.1)

noncomputable instance (t : Nat) : Fintype (SuccessfulWord t) := Fintype.ofFinite _

instance (t : Nat) : Finite (LiteralWord t) := List.finite_length_le Window t

noncomputable instance (t : Nat) : Fintype (LiteralWord t) := Fintype.ofFinite _

def RejectedWord (t : Nat) := {w : LiteralWord t // ¬ Success w.val}

noncomputable instance (t : Nat) : Fintype (RejectedWord t) := by
  classical
  unfold RejectedWord
  infer_instance

noncomputable instance (t : Nat) : Fintype (IndependentWord t) := by
  cases t <;> unfold IndependentWord <;> infer_instance

open scoped BigOperators

def independentOffset : (t : Nat) -> Nat -> Nat -> IndependentWord t -> Nat
  | 0, _, _, _ => 0
  | _ + 1, u, v, x =>
      ∑ i, if x.val i then Nat.fib i.val * u + Nat.fib (i.val + 1) * v else 0

noncomputable def centerImage (t H : Nat) (u v : ZMod H) : Finset (ZMod H) := by
  classical
  exact Finset.univ.image (fun w : SuccessfulWord t => -value u v (flatten w.val))

/-- Both structure fields are computed by the actual transition sequence;
the seam guard recognizes exactly the flattened bit language. -/
theorem execution (s E : Bool) (w : List Window) :
    (run (some (s, E)) w =
        some (w.foldl (fun _ b => last b) s, w.foldl (fun _ b => nonzero b) E) ↔
      legal s (flatten w)) ∧
    (run (some (s, E)) w = none ↔ ¬ legal s (flatten w)) := by
  have dead : ∀ w : List Window, run none w = none := by
    intro w
    induction w with
    | nil => rfl
    | cons b w ih => exact ih
  have window_legal (s : Bool) (b : Window) (tail : List Bool) :
      legal s (bits b ++ tail) ↔
        ¬ (s = true ∧ first b = true) ∧ legal (last b) tail := by
    cases s <;> cases b <;> simp [bits, first, last, legal]
  induction w generalizing s E with
  | nil => simp [run, flatten, legal]
  | cons b w ih =>
    simp only [run, flatten, List.flatMap_cons, List.foldl_cons, window_legal]
    by_cases h : s = true ∧ first b = true
    · simp [step, h.1, h.2, dead]
    · have hguard : (s && first b) = false := by
        cases s <;> cases hb : first b <;> simp_all
      simp only [step, hguard, Bool.false_eq_true, ↓reduceIte]
      simpa only [h, not_false_eq_true, true_and, flatten] using ih (last b) (nonzero b)

#print axioms execution

/-- The complete successful literal query family, with its executable numeric
readout, canonical inverse, Fibonacci count and common error complement. -/
theorem result (t : Nat) :
    (∃ e : SuccessfulWord t ≃ IndependentWord t,
      (∀ x, (e.symm x).val = encode t x) ∧
      (∀ w, independentBits t (e w) = flatten (pad t w.val)) ∧
      (∀ w r u v, query r u v w.val = some (r + independentOffset t u v (e w))) ∧
      (∀ H (u v : Nat) (w : SuccessfulWord t),
        value (u : ZMod H) (v : ZMod H) (flatten w.val) =
          (independentOffset t u v (e w) : ZMod H))) ∧
    Fintype.card (SuccessfulWord t) = Nat.fib (3 * t + 1) ∧
    (∀ w r u v, query r u v w = none ↔ ¬ Success w) ∧
    (∀ w r u v, Success w → 0 < r → ∃ N, 0 < N ∧ query r u v w = some N) ∧
    Fintype.card (LiteralWord t) = (∑ n : Fin (t + 1), 5 ^ n.val) ∧
    Fintype.card (RejectedWord t) = (∑ n : Fin (t + 1), 5 ^ n.val) - Nat.fib (3 * t + 1) ∧
    (∀ H (u v : ZMod H), (centerImage t H u v).card ≤ Nat.fib (3 * t + 1)) ∧
    (∀ epsilon w N, initialized epsilon w = some N → 0 < N) := by
  classical
  have length_flatten (w : List Window) : (flatten w).length = 3 * w.length := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      cases b <;> simp [flatten, bits] at * <;> omega
  have legal_zeros (w : List Window) (k : Nat) (s : Bool) :
      legal s (flatten (w ++ List.replicate k .zero)) ↔ legal s (flatten w) := by
    induction w generalizing s with
    | nil =>
      simp only [List.nil_append, flatten, List.flatMap_nil, legal, iff_true]
      induction k generalizing s with
      | zero => trivial
      | succ k ih => simpa [List.replicate_succ, flatten, bits, legal] using ih false
    | cons b w ih =>
      simp only [flatten, List.flatMap_append] at ih
      cases s <;> cases b <;> simp [flatten, bits, legal, ih]
  have trim_decomp (w : List Window) :
      ∃ k : Nat, w = trim w ++ List.replicate k .zero := by
    induction w with
    | nil => exact ⟨0, rfl⟩
    | cons b w ih =>
      obtain ⟨k, hk⟩ := ih
      by_cases h : b = .zero ∧ trim w = []
      · refine ⟨k + 1, ?_⟩
        change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
        rw [if_pos h, List.nil_append, List.replicate_succ, h.1]
        congr 1
        simpa only [h.2, List.nil_append] using hk
      · refine ⟨k, ?_⟩
        change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
        rw [if_neg h, List.cons_append, ← hk]
  have trim_terminal (w : List Window) (E : Bool) :
      (trim w).foldl (fun _ b => nonzero b) E =
        if trim w = [] then E else true := by
    induction w generalizing E with
    | nil => rfl
    | cons b w ih =>
      by_cases h : b = .zero ∧ trim w = []
      · simp [trim, h]
      · simp only [trim, if_neg h, List.foldl_cons, List.cons_ne_nil, ↓reduceIte]
        rw [ih]
        by_cases ht : trim w = []
        · have hb : b ≠ .zero := by intro hb; exact h ⟨hb, ht⟩
          simp [ht, nonzero, hb]
        · simp [ht]
  have normal_trim (w : List Window) (E : Bool)
      (hw : w.foldl (fun _ b => nonzero b) E = true) : trim w = w := by
    induction w generalizing E with
    | nil => rfl
    | cons b w ih =>
      have ht := ih (nonzero b) hw
      by_cases h : b = .zero ∧ trim w = []
      · have he := ht.symm.trans h.2
        subst w
        simp [nonzero, h.1] at hw
      · change (if b = .zero ∧ trim w = [] then [] else b :: trim w) = b :: w
        rw [if_neg h, ht]
  have success_iff (w : List Window) :
      Success w ↔ legal true (flatten w) ∧
        w.foldl (fun _ b => nonzero b) true = true := by
    by_cases h : legal true (flatten w)
    · rw [Success, (execution true true w).1.2 h]
      simp [endable, h]
    · rw [Success, (execution true true w).2.2 h]
      simp [endable, h]
  have trim_success (w : List Window) (hw : legal true (flatten w)) :
      Success (trim w) := by
    apply (success_iff _).2
    obtain ⟨k, hk⟩ := trim_decomp w
    refine ⟨?_, ?_⟩
    · rw [hk] at hw
      exact (legal_zeros (trim w) k true).1 hw
    · simpa using trim_terminal w true
  have trim_zeros (w : List Window) (k : Nat) :
      trim (w ++ List.replicate k .zero) = trim w := by
    induction w with
    | nil =>
      simp only [List.nil_append, trim]
      induction k with
      | zero => rfl
      | succ k ih => simp [List.replicate_succ, trim, ih]
    | cons b w ih => simp [List.cons_append, trim, ih]
  have trim_length (w : List Window) : (trim w).length <= w.length := by
    obtain ⟨k, hk⟩ := trim_decomp w
    have hl := congrArg List.length hk
    simp only [List.length_append, List.length_replicate] at hl
    omega
  let paddedEquiv (t : Nat) : SuccessfulWord t ≃ PaddedWord t := {
    toFun w := ⟨pad t w.val, by
      constructor
      · simp only [pad, List.length_append, List.length_replicate]
        have hw := w.property.1
        omega
      · exact (legal_zeros w.val (t - w.val.length) true).2
          ((success_iff _).1 w.property.2).1⟩
    invFun w := ⟨trim w.val,
      (trim_length _).trans w.property.1.le, trim_success _ w.property.2⟩
    left_inv w := by
      apply Subtype.ext
      change trim (w.val ++ List.replicate (t - w.val.length) .zero) = w.val
      rw [trim_zeros]
      exact normal_trim w.val true ((success_iff _).1 w.property.2).2
    right_inv w := by
      apply Subtype.ext
      obtain ⟨k, hk⟩ := trim_decomp w.val
      have hl := congrArg List.length hk
      simp only [List.length_append, List.length_replicate] at hl
      have hw := w.property.1
      have hn : t - (trim w.val).length = k := by omega
      change trim w.val ++ List.replicate (t - (trim w.val).length) .zero = w.val
      rw [hn]
      exact hk.symm
  }
  have pack_flatten (w : List Window) : pack (flatten w) = w := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      have hc := congrArg (fun tail => b :: tail) ih
      cases b <;> simpa [flatten, bits, pack, triple] using hc
  have pack_legal (t : Nat) (bs : List Bool) (hl : bs.length = 3 * t)
      (s : Bool) (hs : legal s bs) :
      (pack bs).length = t ∧ flatten (pack bs) = bs := by
    induction t generalizing bs s with
    | zero =>
      have hnil : bs = [] := List.length_eq_zero_iff.1 (by omega)
      subst bs
      exact ⟨rfl, rfl⟩
    | succ t ih =>
      rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
      · simp at hl
      · simp at hl; omega
      · simp at hl; omega
      · have htail : tail.length = 3 * t := by simp only [List.length_cons] at hl; omega
        have hlegal : legal c tail := hs.2.2.2
        obtain ⟨hlen, hflat⟩ := ih tail htail c hlegal
        cases a <;> cases b <;> cases c <;>
          simp_all [legal, pack, triple, flatten, bits]
  let flatEquiv (t : Nat) : PaddedWord t ≃ BitWord t := {
    toFun w := ⟨flatten w.val, by rw [length_flatten, w.property.1], w.property.2⟩
    invFun bs := ⟨pack bs.val, (pack_legal t bs.val bs.property.1 true bs.property.2).1,
      by rw [(pack_legal t bs.val bs.property.1 true bs.property.2).2]; exact bs.property.2⟩
    left_inv w := Subtype.ext (pack_flatten w.val)
    right_inv bs := Subtype.ext (pack_legal t bs.val bs.property.1 true bs.property.2).2
  }
  have adm_legal (n : Nat) (f : Fin n -> Bool) (previous : Bool) :
      legal previous (List.ofFn f) ↔
        (previous = true -> (List.ofFn f).head? ≠ some true) ∧ Adm n f := by
    induction n generalizing previous with
    | zero => simp [legal, Adm]
    | succ n ih =>
      cases n with
      | zero =>
        cases previous <;> cases h : f 0 <;> simp [List.ofFn_succ, legal, Adm, h]
      | succ n =>
        have ht := ih (Fin.tail f) false
        simp only [Bool.false_eq_true, false_implies, true_and] at ht
        rw [adm_two_iff, ← ht]
        simp only [List.ofFn_succ, List.head?_cons, legal]
        have h1 : (Fin.tail f) 0 = f 1 := by simp [Fin.tail, Fin.succ_zero_eq_one]
        rw [h1]
        cases previous <;> cases h0 : f 0 <;> cases h1 : f 1 <;> simp_all [Fin.tail]
  let positiveBitEquiv (t : Nat) (ht : t ≠ 0) :
      {f : Fin (3 * t - 1) -> Bool // Adm (3 * t - 1) f} ≃ BitWord t :=
    Equiv.ofBijective (fun f => ⟨false :: List.ofFn f.val, by
      constructor
      · simp only [List.length_cons, List.length_ofFn]
        omega
      · exact ⟨by simp, (adm_legal _ f.val false).2 ⟨by simp, f.property⟩⟩⟩)
    ⟨by
      intro f g he
      apply Subtype.ext
      apply List.ofFn_injective
      exact (List.cons.inj (congrArg Subtype.val he)).2,
    by
      rintro ⟨bs, hlen, hlegal⟩
      rcases bs with _ | ⟨a, tail⟩
      · simp at hlen; omega
      · have ha : a = false := by
          cases a
          · rfl
          · exact False.elim (hlegal.1 ⟨rfl, rfl⟩)
        subst a
        have htail : tail.length = 3 * t - 1 := by
          simp only [List.length_cons] at hlen
          omega
        let f : Fin (3 * t - 1) -> Bool := fun i => tail.get (Fin.cast htail.symm i)
        have hf : List.ofFn f = tail := by
          rw [List.ofFn_congr htail.symm]
          exact List.ofFn_get tail
        refine ⟨⟨f, ?_⟩, ?_⟩
        · apply ((adm_legal _ f false).1 ?_).2
          rw [hf]
          exact hlegal.2
        · apply Subtype.ext
          change false :: List.ofFn f = false :: tail
          rw [hf]⟩
  have value_zeros (w : List Window) (k u v : Nat) :
      value u v (flatten (w ++ List.replicate k .zero)) = value u v (flatten w) := by
    induction w generalizing u v with
    | nil =>
      simp only [List.nil_append, flatten, List.flatMap_nil, value]
      induction k generalizing u v with
      | zero => rfl
      | succ k ih =>
        simpa [List.replicate_succ, flatten, bits, value] using
          (ih (v + (u + v)) ((u + v) + (v + (u + v))))
    | cons b w ih =>
      simp only [flatten, List.flatMap_append] at ih
      cases b <;> simp [flatten, bits, value, ih]
  have fib_value (n k u v : Nat) (f : Fin n -> Bool) :
      value (Nat.fib k * u + Nat.fib (k + 1) * v)
          (Nat.fib (k + 1) * u + Nat.fib (k + 2) * v) (List.ofFn f) =
        ∑ i, if f i then Nat.fib (k + i.val) * u + Nat.fib (k + i.val + 1) * v
          else 0 := by
    induction n generalizing k with
    | zero => simp [value]
    | succ n ih =>
      rw [List.ofFn_succ, value, Fin.sum_univ_succ]
      have hnext :
          (Nat.fib k * u + Nat.fib (k + 1) * v) +
              (Nat.fib (k + 1) * u + Nat.fib (k + 2) * v) =
            Nat.fib (k + 2) * u + Nat.fib (k + 3) * v := by
        have hF := Nat.fib_add_two (n := k)
        have hG : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
          simpa only [Nat.add_assoc] using Nat.fib_add_two (n := k + 1)
        simp only [hG, hF]
        ring
      have hi :
          value (Nat.fib (k + 1) * u + Nat.fib (k + 2) * v)
              (Nat.fib (k + 2) * u + Nat.fib (k + 3) * v)
              (List.ofFn (fun i : Fin n => f i.succ)) =
            ∑ i : Fin n, if f i.succ then
              Nat.fib (k + 1 + i.val) * u + Nat.fib (k + 1 + i.val + 1) * v else 0 := by
        simpa only [Nat.add_assoc, Nat.reduceAdd, Fin.tail_def] using
          ih (k + 1) (Fin.tail f)
      rw [hnext, hi]
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [Nat.add_comm, Nat.add_left_comm]
  have cast_value (H : Nat) (w : List Bool) (u v : Nat) :
      value (u : ZMod H) (v : ZMod H) w = ((value u v w : Nat) : ZMod H) := by
    induction w generalizing u v with
    | nil => simp [value]
    | cons b w ih =>
      cases b with
      | false => simpa [value, Nat.cast_add] using ih v (u + v)
      | true =>
          simpa [value, Nat.cast_add] using
            congrArg (fun x : ZMod H => (u : ZMod H) + x) (ih v (u + v))
  have literal_card (t : Nat) :
      Fintype.card (LiteralWord t) = ∑ n : Fin (t + 1), 5 ^ n.val := by
    let e : LiteralWord t ≃ (Σ n : Fin (t + 1), List.Vector Window n.val) := {
      toFun w := ⟨⟨w.val.length, by have hw := w.property; omega⟩, ⟨w.val, rfl⟩⟩
      invFun w := ⟨w.2.val, by have hw := w.2.property; have hn := w.1.isLt; omega⟩
      left_inv w := rfl
      right_inv := by
        rintro ⟨⟨n, hn⟩, ⟨w, hw⟩⟩
        dsimp at hw
        subst n
        rfl
    }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [card_vector]
    have hwindow : Fintype.card Window = 5 := by decide
    rw [hwindow]
  have equiv_exists (t : Nat) :
      ∃ e : SuccessfulWord t ≃ IndependentWord t,
        (∀ x, (e.symm x).val = encode t x) ∧
        (∀ w, independentBits t (e w) = flatten (pad t w.val)) := by
    cases t with
    | zero =>
      let e : SuccessfulWord 0 ≃ IndependentWord 0 := {
        toFun _ := PUnit.unit
        invFun _ := ⟨[], by simp [Success, run, endable]⟩
        left_inv w := Subtype.ext (by
          have hw := w.property.1
          exact (List.length_eq_zero_iff.1 (by omega)).symm)
        right_inv x := by cases x; rfl
      }
      refine ⟨e, by intro x; rfl, ?_⟩
      intro w
      have hw : w.val = [] := List.length_eq_zero_iff.1 (by have hw := w.property.1; omega)
      simp [independentBits, pad, hw, flatten]
    | succ t =>
      let p := (paddedEquiv (t + 1)).trans (flatEquiv (t + 1))
      let f := positiveBitEquiv (t + 1) (by omega)
      let e : SuccessfulWord (t + 1) ≃ IndependentWord (t + 1) := p.trans f.symm
      refine ⟨e, ?_, ?_⟩
      · intro x
        rfl
      · intro w
        have h := congrArg Subtype.val (f.apply_symm_apply (p w))
        exact h
  have success_count (t : Nat) :
      Fintype.card (SuccessfulWord t) = Nat.fib (3 * t + 1) := by
    obtain ⟨e, _⟩ := equiv_exists t
    rw [Fintype.card_congr e]
    cases t with
    | zero => simp [IndependentWord]
    | succ t =>
      change Fintype.card {f : Fin (3 * (t + 1) - 1) -> Bool // Adm _ f} = _
      rw [admissibleWord_card_eq_fib]
      congr 1
  have rejected_count (t : Nat) :
      Fintype.card (RejectedWord t) =
        (∑ n : Fin (t + 1), 5 ^ n.val) - Nat.fib (3 * t + 1) := by
    let e : {w : LiteralWord t // Success w.val} ≃ SuccessfulWord t := {
      toFun w := ⟨w.val.val, w.val.property, w.property⟩
      invFun w := ⟨⟨w.val, w.property.1⟩, w.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
    }
    change Fintype.card {w : LiteralWord t // ¬ Success w.val} = _
    rw [Fintype.card_subtype_compl, Fintype.card_congr e, success_count, literal_card]
  have query_error (w : List Window) (r u v : Nat) :
      query r u v w = none ↔ ¬ Success w := by
    simp [query, observe, Success]
  have positive_value (w : List Window) (r u v : Nat) (E : Bool)
      (hu : 0 < u) (hv : 0 < v) (he : E = true → 0 < r)
      (hw : w.foldl (fun _ b => nonzero b) E = true) :
      0 < r + value u v (flatten w) := by
    induction w generalizing r u v E with
    | nil => simpa [flatten, value] using he hw
    | cons b w ih =>
      have hwindow :
          value u v (flatten (b :: w)) = value u v (bits b) +
            value (v + (u + v)) ((u + v) + (v + (u + v))) (flatten w) := by
        cases b <;> simp [flatten, bits, value, Nat.add_assoc]
      have hstart : nonzero b = true → 0 < r + value u v (bits b) := by
        cases b <;> simp [nonzero, bits, value] <;> omega
      have hpos := ih (r + value u v (bits b))
        (v + (u + v)) ((u + v) + (v + (u + v))) (nonzero b)
        (by omega) (by omega) hstart hw
      rw [hwindow]
      omega
  obtain ⟨e, hinv, hbits⟩ := equiv_exists t
  have offset_eq (w : SuccessfulWord t) (u v : Nat) :
      value u v (flatten w.val) = independentOffset t u v (e w) := by
    have hp := value_zeros w.val (t - w.val.length) u v
    change value u v (flatten (pad t w.val)) = value u v (flatten w.val) at hp
    rw [← hp, ← hbits w]
    cases t with
    | zero => simp [independentBits, independentOffset, value]
    | succ t =>
      simpa [independentBits, independentOffset, value] using
        fib_value (3 * (t + 1) - 1) 0 u v (e w).val
  refine ⟨⟨e, hinv, hbits, ?_, ?_⟩, success_count t, query_error, ?_,
    literal_card t, rejected_count t, ?_, ?_⟩
  · intro w r u v
    have hs := w.property.2
    simp only [query, observe, Success] at hs ⊢
    rw [if_pos hs, offset_eq]
    rfl
  · intro H u v w
    rw [cast_value, offset_eq]
  · intro w r u v hs hr
    refine ⟨r + value u v (flatten w), by omega, ?_⟩
    change endable (run (some (true, true)) w) = true at hs
    simp only [query, observe, hs, ↓reduceIte, id_eq]
  · intro H u v
    exact (Finset.card_image_le).trans (by rw [Finset.card_univ, success_count])
  · intro epsilon w N hN
    unfold initialized observe at hN
    split at hN
    · rename_i hflag
      have hl : legal epsilon (flatten w) := by
        by_contra hl
        rw [(execution epsilon epsilon w).2.2 hl] at hflag
        simp [endable] at hflag
      rw [(execution epsilon epsilon w).1.2 hl] at hflag
      have he : w.foldl (fun _ b => nonzero b) epsilon = true := by
        simpa only [endable, Option.any_some] using hflag
      have hp := positive_value w (if epsilon then 1 else 0) 2 3 epsilon
        (by decide) (by decide) (by cases epsilon <;> simp) he
      exact (Option.some.inj hN) ▸ hp
    · simp at hN

#print axioms result

end D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
