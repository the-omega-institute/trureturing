/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Native full-support laws keep proper joint reports but separate actual null replies. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber
import D5.S1.Words.Palindromes.FridPrefix.NumeralSemantics
import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
import D5.S3.Entropy.Forgetting.CapacityMonotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw

open scoped BigOperators
open LiteralWindowEnd (Window bits first last)
open GraftAffineClosure (step quantity residue)
open ImmediateWindowStateCapacity (clock rawMachine rawOutput rawTransition task displacement)
open NullReplyFiber (highBits bitComposition NativeHistory native_execution null_reply_zero_iff)
open D5.S3.Arith.ZeckendorfFutureKernel (legal value)
open D5.S1.Digit.GoldenBase4IntervalMachine (fibPair fibPair_append_digit)
open D5.S1.Words.FridPrefix (canonical_lex_value)
open D5.S0.Automata.BinaryZeckendorfLanguage (NoAdjacentOnes)
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)

/-- The original natural composition, in chronological window order. -/
def composition (w : List Window) : ℕ × ℕ :=
  w.foldl (fun c b => step (step (step c)) + bitComposition b) (0, 0)

/-- The complete high-to-low bit history in the existing binary digit carrier. -/
def digits (w : List Window) : List (Fin 2) :=
  (highBits w).map (fun b => if b then 1 else 0)

private theorem history_fold {s t : Bool} {c d : ℕ × ℕ} {w : List Window}
    (h : NativeHistory s c w t d) :
    d = w.foldl (fun c b => step (step (step c)) + bitComposition b) c := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem history_seam {s t : Bool} {c d : ℕ × ℕ} {w : List Window}
    (h : NativeHistory s c w t d) : t = (w.getLast?.map first).getD s := by
  induction h with
  | nil => rfl
  | @cons s t c d b w _ _ ih =>
    cases w with
    | nil => exact ih
    | cons a w =>
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp
        (show (a :: w).getLast? ≠ none by simp)
      simpa [List.getLast?_cons_cons, hz] using ih

/-- The existing reader's actual seam and natural composition on every legal word. -/
theorem actual_state (w : List Window) (hw : legal false (highBits w)) :
    (rawMachine 0).toDFA.eval w =
      some ((w.getLast?.map first).getD false, residue 0 (composition w)) := by
  have hn := (native_execution false (0, 0) w).1
  cases hr : (rawMachine 0).toDFA.eval w with
  | none => exact ((hn.mp hr) hw).elim
  | some z =>
    rcases z with ⟨s, x⟩
    obtain ⟨d, hd, hx⟩ := (native_execution false (0, 0) w).2 s x |>.mp hr
    have hdc : d = composition w := history_fold hd
    simp [hx, hdc, history_seam hd]

/-- Every legal word's actual integer task has its original natural composition. -/
theorem actual_quantity (w : List Window) (hw : legal false (highBits w)) :
    task 0 w = some ((quantity (composition w) : ℕ) : ZMod 0) := by
  change rawOutput ((rawMachine 0).toDFA.eval w) = _
  rw [actual_state w hw]
  simp [rawOutput, quantity, residue]

private theorem composition_append (w : List Window) (b : Window) :
    composition (w ++ [b]) = step (step (step (composition w))) + bitComposition b := by
  simp [composition, List.foldl_append]

private theorem digits_append (w : List Window) (b : Window) :
    digits (w ++ [b]) = digits w ++ ((bits b).reverse.map (fun a => if a then 1 else 0)) := by
  simp [digits, highBits, List.flatMap_append]

/-- The same natural source has exactly the existing padded Fibonacci coordinates. -/
theorem composition_coordinates (w : List Window) :
    fibPair (digits w) = step (step (step (composition w))) := by
  induction w using List.reverseRecOn with
  | nil => simp [digits, highBits, fibPair, composition, step]
  | append_singleton w b ih =>
    rw [digits_append, composition_append]
    cases b <;> simp only [bits, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.map_cons, List.map_nil,
      List.cons_append, Bool.false_eq_true, ↓reduceIte]
    all_goals
      rw [show ∀ (a b c : Fin 2), digits w ++ [a, b, c] =
        ((digits w ++ [a]) ++ [b]) ++ [c] from fun _ _ _ => by simp]
      simp only [fibPair_append_digit, ih, bitComposition, bits, value, step,
        Prod.mk_add_mk, Fin.val_zero, Fin.val_one]
      ext <;> simp <;> ring

private theorem digits_legal (w : List Window) (hw : legal false (highBits w)) :
    NoAdjacentOnes (digits w) := by
  have aux : ∀ (v : List Bool) (s : Bool), legal s v →
      ((if s then 1 else 0 : Fin 2) :: v.map (fun b => if b then 1 else 0)).IsChain
        (fun a b => a = 0 ∨ b = 0) := by
    intro v
    induction v with
    | nil => simp
    | cons b v ih =>
      intro s h
      cases s <;> cases b <;> simp_all [legal, List.isChain_cons_cons]
  exact (aux _ false hw).tail

/-- The source is the entire legal fixed-length five-mode domain, with free final seam. -/
abbrev Source (n : ℕ) := {w : Fin n → Window // legal false (highBits (List.ofFn w))}

noncomputable instance (n : ℕ) : Fintype (Source n) := by
  unfold Source
  exact Fintype.ofFinite _

/-- The actual natural reply after one appended null window. -/
def reply {n : ℕ} (w : Source n) : ℕ :=
  quantity (step (step (step (composition (List.ofFn w.val)))))

/-- Every source performs the specified null continuation in the existing reader. -/
theorem actual_null_reply {n : ℕ} (w : Source n) :
    task 0 (List.ofFn w.val ++ [.zero]) = some ((reply w : ℕ) : ZMod 0) := by
  have hlegal : legal false (highBits (List.ofFn w.val ++ [.zero])) := by
    rw [highBits, List.flatMap_append]
    exact (D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ false).2
      ⟨w.property, by simp [bits, legal]⟩
  rw [actual_quantity _ hlegal]
  simp [reply, composition_append, bitComposition, bits, value, Prod.mk_zero_zero]

/-- At each fixed length the actual natural null reply separates legal sources. -/
theorem native_reply_injective (n : ℕ) : Function.Injective (@reply n) := by
  intro u v he
  let du := digits (List.ofFn u.val ++ [.zero]) ++ [0]
  let dv := digits (List.ofFn v.val ++ [.zero]) ++ [0]
  have coord (w : Source n) :
      (fibPair (digits (List.ofFn w.val ++ [.zero]) ++ [0])).1 = reply w := by
    rw [fibPair_append_digit, composition_coordinates]
    simp [reply, composition_append, bitComposition, bits, value, step, quantity]
    ring
  have hu : NoAdjacentOnes du := by
    apply List.IsChain.append
    · apply digits_legal
      rw [highBits, List.flatMap_append]
      exact (D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ false).2
        ⟨u.property, by simp [bits, legal]⟩
    · simp
    · simp
  have hv : NoAdjacentOnes dv := by
    apply List.IsChain.append
    · apply digits_legal
      rw [highBits, List.flatMap_append]
      exact (D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ false).2
        ⟨v.property, by simp [bits, legal]⟩
    · simp
    · simp
  have hc : (fibPair du).1 = (fibPair dv).1 := (coord u).trans (he.trans (coord v).symm)
  have length_digits (w : List Window) : (digits w).length = 3 * w.length := by
    induction w with
    | nil => simp [digits, highBits]
    | cons b w ih => cases b <;> simp [digits, highBits, bits] at * <;> omega
  have dl : du.length = dv.length := by simp [du, dv, length_digits]
  have de : du = dv := by
    rcases lt_trichotomy du dv with h | h | h
    · have hlt := (canonical_lex_value du dv hu hv dl).2 h
      omega
    · exact h
    · have hlt := (canonical_lex_value dv du hv hu dl.symm).2 h
      omega
  have encode_inj : Function.Injective (fun w : List Window => digits w) := by
    intro w z
    induction w generalizing z with
    | nil =>
      intro h
      cases z with
      | nil => rfl
      | cons a z => cases a <;> simp [digits, highBits, bits] at h
    | cons b w ih =>
      intro h
      cases z with
      | nil => cases b <;> simp [digits, highBits, bits] at h
      | cons a z =>
        cases b <;> cases a <;> simp [digits, highBits, bits] at h ⊢
        all_goals exact ih h
  apply Subtype.ext
  apply List.ofFn_injective
  exact List.append_cancel_right (encode_inj (List.append_cancel_right de))

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The null/middle cube in the same five-mode alphabet. -/
def bitWindow (b : Fin 2) : Window := if b = 0 then .zero else .middle

private theorem bitWindow_injective : Function.Injective bitWindow := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [bitWindow]

private theorem cube_legal (b : List (Fin 2)) (s : Bool) :
    legal s (highBits (b.map bitWindow)) := by
  induction b generalizing s with
  | nil => simp [highBits, legal]
  | cons a b ih => fin_cases a <;> simpa [bitWindow, highBits, bits, legal] using ih false

/-- The actual cube embedding, keeping all n positions and its zero seam history. -/
def embed (n : ℕ) (b : Fin n → Fin 2) : Source n :=
  ⟨fun i => bitWindow (b i), by
    rw [List.ofFn_comp']
    exact cube_legal _ false⟩

private theorem embed_injective (n : ℕ) : Function.Injective (embed n) := by
  intro a b h
  funext i
  exact bitWindow_injective (congrFun (congrArg Subtype.val h) i)

private theorem push_injective {X Y : Type*} [Fintype X]
    (f : X → Y) (hf : Function.Injective f) (p : X → ℝ) (x : X) :
    pushforward f p (f x) = p x := by
  classical
  simp only [pushforward, hf.eq_iff]
  simp

private theorem push_outside {X Y : Type*} [Fintype X]
    (f : X → Y) (p : X → ℝ) (y : Y) (hy : y ∉ Set.range f) : pushforward f p y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  simp only [if_neg (fun h => hy ⟨x, h⟩)]

private theorem push_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : X → ℝ) : (∑ y, pushforward f p y) = ∑ x, p x := by
  classical
  simp only [pushforward]
  rw [Finset.sum_comm]
  simp

private theorem push_test {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : X → ℝ) (H : Y → ℝ) :
    (∑ y, pushforward f p y * H y) = ∑ x, p x * H (f x) := by
  classical
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- The real-valued existing fair parity law; zero has sign minus one. -/
def cubeLaw (n : ℕ) (ε : ℤ) (b : Fin n → Fin 2) : ℝ := parityLaw n ε b

private theorem cube_nonneg (n : ℕ) (ε : ℤ) (b : Fin n → Fin 2) :
    0 ≤ cubeLaw n ε b := by
  unfold cubeLaw parityLaw
  split <;> positivity

private theorem cube_sum (n : ℕ) (hn : 0 < n) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    (∑ b, cubeLaw n ε b) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := (parity_conditioned_probability_form k).1
  unfold cubeLaw
  rcases hε with rfl | rfl
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- Both laws use the uniform background on the entire legal source domain. -/
def law (n : ℕ) (mix : ℝ) (ε : ℤ) (w : Source n) : ℝ :=
  (1 - mix) / Fintype.card (Source n) + mix * pushforward (embed n) (cubeLaw n ε) w

private theorem source_nonempty (n : ℕ) : Nonempty (Source n) := ⟨embed n (fun _ => 0)⟩

private theorem law_probability (n : ℕ) (hn : 0 < n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    (∀ w, 0 < law n mix ε w) ∧ (∑ w, law n mix ε w) = 1 := by
  classical
  let := source_nonempty n
  have hc : (0 : ℝ) < Fintype.card (Source n) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro w
    have hm : 0 ≤ pushforward (embed n) (cubeLaw n ε) w :=
      Finset.sum_nonneg (fun b _ => by split <;> simp [cube_nonneg])
    exact add_pos_of_pos_of_nonneg (div_pos (by linarith) hc) (mul_nonneg hl.le hm)
  · simp only [law, Finset.sum_add_distrib, ← Finset.mul_sum,
      push_sum, cube_sum n hn ε hε, mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    field_simp
    ring

/-- The complete actual seam vector includes the initial zero seam. -/
def seams {n : ℕ} (w : Source n) : List Bool :=
  false :: (List.ofFn w.val).map first

/-- The mass of a finite-source event. -/
def mass {X : Type*} [Fintype X] (p : X → ℝ) (E : X → Prop) : ℝ :=
  ∑ w, if E w then p w else 0

private theorem mass_push {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (p : X → ℝ) (E : Y → Prop) :
    mass (pushforward f p) E = mass p (fun x => E (f x)) := by
  have h := push_test f p (fun y => if E y then 1 else 0)
  simpa only [mass, mul_ite, mul_one, mul_zero] using h

private theorem mass_mix {X : Type*} [Fintype X]
    (b p : X → ℝ) (t : ℝ) (E : X → Prop) :
    mass (fun x => b x + t * p x) E = mass b E + t * mass p E := by
  unfold mass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp only [h, ↓reduceIte, mul_zero, add_zero]

/-- One complete-seam/proper-coordinate joint table, with its original position labels. -/
def jointMass {n : ℕ} (p : Source n → ℝ) (A : Finset (Fin n))
    (s : List Bool) (y : Fin n → Window) : ℝ :=
  mass p (fun w => seams w = s ∧ ∀ i ∈ A, w.val i = y i)

/-- The mass of an arbitrary event in the complete seam vector. -/
def seamEventMass {n : ℕ} (p : Source n → ℝ) (E : List Bool → Prop) : ℝ :=
  mass p (fun w => E (seams w))

/-- Conditional coordinate tables at a seam event of positive mass. -/
def conditionalMass {n : ℕ} (p : Source n → ℝ) (E : List Bool → Prop)
    (A : Finset (Fin n)) (y : Fin n → Window) : ℝ :=
  mass p (fun w => E (seams w) ∧ ∀ i ∈ A, w.val i = y i) / seamEventMass p E

private theorem cube_seams (n : ℕ) (b : Fin n → Fin 2) :
    seams (embed n b) = List.replicate (n + 1) false := by
  have letter : ∀ b : Fin 2, first (bitWindow b) = false := by
    intro b; fin_cases b <;> rfl
  simp [seams, embed, List.map_ofFn, Function.comp_def, letter,
    List.ofFn_const, List.replicate_succ]

private theorem proper_test (n : ℕ) (hn : 0 < n) (A : Finset (Fin n))
    (hA : A ≠ Finset.univ) (y : Fin n → Window) :
    (∑ b, if ∀ i ∈ A, bitWindow (b i) = y i then cubeLaw n (-1) b else 0) =
      ∑ b, if ∀ i ∈ A, bitWindow (b i) = y i then cubeLaw n 1 b else 0 := by
  classical
  by_cases hy : ∀ i ∈ A, ∃ a, bitWindow a = y i
  · let z : Fin n → Fin 2 := fun i => if h : ∃ a, bitWindow a = y i then h.choose else 0
    have agree (b : Fin n → Fin 2) :
        (∀ i ∈ A, bitWindow (b i) = y i) ↔ ∀ i ∈ A, b i = z i := by
      refine forall₂_congr fun i hi => ?_
      have he : bitWindow (z i) = y i := by
        dsimp only [z]
        rw [dif_pos (hy i hi)]
        exact (hy i hi).choose_spec
      rw [← he, bitWindow_injective.eq_iff]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h := (parity_conditioned_probability_form k).2.2.2.2 A hA z
    unfold parityMarginalMass at h
    have cast :
        (∑ b, if ∀ i ∈ A, b i = z i then cubeLaw (k + 1) (-1) b else 0) =
          ∑ b, if ∀ i ∈ A, b i = z i then cubeLaw (k + 1) 1 b else 0 := by
      unfold cubeLaw
      simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using
        congrArg (fun q : ℚ => (q : ℝ)) h
    simpa only [agree] using cast
  · have no (b : Fin n → Fin 2) : ¬∀ i ∈ A, bitWindow (b i) = y i := by
      intro h; exact hy (fun i hi => ⟨b i, h i hi⟩)
    simp [no]


private theorem proper_event (n : ℕ) (hn : 0 < n) (mix : ℝ)
    (E : List Bool → Prop) (A : Finset (Fin n)) (hA : A ≠ Finset.univ)
    (y : Fin n → Window) :
    mass (law n mix (-1)) (fun w => E (seams w) ∧ ∀ i ∈ A, w.val i = y i) =
      mass (law n mix 1) (fun w => E (seams w) ∧ ∀ i ∈ A, w.val i = y i) := by
  let test : Source n → Prop := fun w => E (seams w) ∧ ∀ i ∈ A, w.val i = y i
  have expand (ε : ℤ) : mass (law n mix ε) test =
      mass (fun _ : Source n => (1 - mix) / Fintype.card (Source n)) test +
      mix * mass (cubeLaw n ε) (fun b => E (List.replicate (n + 1) false) ∧
        ∀ i ∈ A, bitWindow (b i) = y i) := by
    change mass (fun w => (1 - mix) / Fintype.card (Source n) +
      mix * pushforward (embed n) (cubeLaw n ε) w) test = _
    rw [mass_mix, mass_push]
    have predicate : (fun b => test (embed n b)) =
        (fun b => E (List.replicate (n + 1) false) ∧ ∀ i ∈ A, bitWindow (b i) = y i) := by
      funext b
      dsimp only [test]
      rw [cube_seams]
      rfl
    rw [predicate]
  change mass (law n mix (-1)) test = mass (law n mix 1) test
  rw [expand, expand]
  congr 1
  congr 1
  unfold mass
  by_cases h : E (List.replicate (n + 1) false)
  · simpa only [h, true_and] using proper_test n hn A hA y
  · simp only [h, false_and, ↓reduceIte, Finset.sum_const_zero]

private theorem seam_events_equal (n : ℕ) (hn : 0 < n) (mix : ℝ)
    (E : List Bool → Prop) :
    seamEventMass (law n mix (-1)) E = seamEventMass (law n mix 1) E := by
  have empty : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at hc
    omega
  simpa [seamEventMass] using proper_event n hn mix E ∅ empty (fun _ => .zero)

private theorem singleton_proper (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    ({i} : Finset (Fin n)) ≠ Finset.univ := by
  intro h
  have hc := congrArg Finset.card h
  simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem coordinate_expectation (n : ℕ) (hn : 2 ≤ n) (mix : ℝ)
    (i : Fin n) (H : Window → ℝ) :
    (∑ w, law n mix (-1) w * H (w.val i)) =
      ∑ w, law n mix 1 w * H (w.val i) := by
  classical
  have table (a : Window) :
      (∑ w, if w.val i = a then law n mix (-1) w else 0) =
        ∑ w, if w.val i = a then law n mix 1 w else 0 := by
    simpa [mass] using proper_event n (by omega) mix (fun _ => True) {i}
      (singleton_proper n hn i) (fun _ => a)
  have expand (ε : ℤ) : (∑ w, law n mix ε w * H (w.val i)) =
      ∑ a : Window, (∑ w, if w.val i = a then law n mix ε w else 0) * H a := by
    rw [show (∑ a : Window, (∑ w, if w.val i = a then law n mix ε w else 0) * H a) =
      ∑ w : Source n, ∑ a : Window, (if w.val i = a then law n mix ε w else 0) * H a
      by simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro w _
    simp [ite_mul]
  rw [expand, expand]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun z => z * H a) (table a))

/-- Every prefix composition is tested in its own natural history, with fixed real coefficients. -/
def linearReadout {n : ℕ} (j : ℕ) (a b : ℝ) (w : Source n) : ℝ :=
  a * (composition ((List.ofFn w.val).take j)).1 +
    b * (composition ((List.ofFn w.val).take j)).2

private theorem linear_expectations (n : ℕ) (hn : 2 ≤ n) (mix : ℝ)
    (j : ℕ) (hj : j ≤ n) (a b : ℝ) :
    (∑ w, law n mix (-1) w * linearReadout j a b w) =
      ∑ w, law n mix 1 w * linearReadout j a b w := by
  induction j generalizing a b with
  | zero => simp [linearReadout, composition]
  | succ j ih =>
    let i : Fin n := ⟨j, by omega⟩
    have advance (w : Source n) : linearReadout (j + 1) a b w =
        linearReadout j (a + 2 * b) (2 * a + 3 * b) w +
          (a * (bitComposition (w.val i)).1 + b * (bitComposition (w.val i)).2) := by
      have take : (List.ofFn w.val).take (j + 1) =
          (List.ofFn w.val).take j ++ [w.val i] := by
        rw [List.take_add_one]
        simp [i, show j < n by omega]
      rw [linearReadout, take, composition_append]
      simp only [linearReadout, step, Prod.fst_add, Prod.snd_add, Nat.cast_add]
      ring
    simp_rw [advance, mul_add, Finset.sum_add_distrib]
    rw [ih (by omega)]
    rw [coordinate_expectation n hn mix i (fun z => a * (bitComposition z).1),
      coordinate_expectation n hn mix i (fun z => b * (bitComposition z).2)]

private theorem reply_expectations (n : ℕ) (hn : 2 ≤ n) (mix : ℝ) :
    (∑ w, law n mix (-1) w * (reply w : ℝ)) =
      ∑ w, law n mix 1 w * (reply w : ℝ) := by
  have equation (w : Source n) : (reply w : ℝ) = linearReadout n 8 13 w := by
    have ht : (List.ofFn w.val).take n = List.ofFn w.val := by
      exact List.take_of_length_le (by simp)
    simp [reply, linearReadout, ht, step, quantity]
    ring
  simp_rw [equation]
  exact linear_expectations n hn mix n le_rfl 8 13

private theorem zero_reply_source (n : ℕ) (w : Source n) :
    reply w = 0 ↔ w = embed n (fun _ => 0) := by
  have taskzero : task 0 (List.ofFn w.val ++ [.zero]) = some 0 ↔ reply w = 0 := by
    rw [actual_null_reply]
    simp only [Option.some.injEq]
    exact_mod_cast (Iff.rfl : (reply w : ℤ) = 0 ↔ (reply w : ℤ) = 0)
  rw [← taskzero, null_reply_zero_iff]
  constructor
  · intro h
    apply Subtype.ext
    funext i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rintro rfl
    simp [embed, bitWindow]

private theorem zero_reply_mass (n : ℕ) (mix : ℝ) (ε : ℤ) :
    pushforward (@reply n) (law n mix ε) 0 = law n mix ε (embed n (fun _ => 0)) := by
  classical
  unfold pushforward
  simp_rw [zero_reply_source]
  simp

private theorem zero_difference (n : ℕ) (mix : ℝ) :
    pushforward (@reply n) (law n mix 1) 0 - pushforward (@reply n) (law n mix (-1)) 0 =
      (-1 : ℝ) ^ n * mix / 2 ^ (n - 1) := by
  rw [zero_reply_mass, zero_reply_mass]
  simp only [law, push_injective (embed n) (embed_injective n)]
  have hp : (∏ i : Fin n, paritySign (0 : Fin 2)) = (-1 : ℤ) ^ n := by simp [paritySign]
  rcases neg_one_pow_eq_or ℤ n with h | h
  · have hr : (-1 : ℝ) ^ n = 1 := by exact_mod_cast h
    simp [cubeLaw, parityLaw, parityFiber, hp, h, hr]
    ring
  · have hr : (-1 : ℝ) ^ n = -1 := by exact_mod_cast h
    simp [cubeLaw, parityLaw, parityFiber, hp, h, hr]
    ring

/-- Total variation of the two finite source tables. -/
def sourceTV {n : ℕ} (p q : Source n → ℝ) : ℝ := (1 / 2) * ∑ w, |p w - q w|

/-- Total variation of complete natural reply laws, over their actual finite image. -/
def replyTV {n : ℕ} (p q : Source n → ℝ) : ℝ :=
  (1 / 2) * ∑ r ∈ Finset.univ.image (@reply n), |pushforward reply p r - pushforward reply q r|

private theorem cube_abs (n : ℕ) (b : Fin n → Fin 2) :
    |cubeLaw n 1 b - cubeLaw n (-1) b| = cubeLaw n 1 b + cubeLaw n (-1) b := by
  have disjoint : b ∈ parityFiber n 1 → b ∉ parityFiber n (-1) := by
    simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  by_cases hp : b ∈ parityFiber n 1
  · have hm := disjoint hp
    simp [cubeLaw, parityLaw, hp, hm]
  · have hz : cubeLaw n 1 b = 0 := by simp [cubeLaw, parityLaw, hp]
    rw [hz, zero_sub, zero_add, abs_neg, abs_of_nonneg (cube_nonneg n (-1) b)]

private theorem source_tv (n : ℕ) (hn : 0 < n) (mix : ℝ) (hm : 0 ≤ mix) :
    sourceTV (law n mix 1) (law n mix (-1)) = mix := by
  classical
  have reduce :
      (∑ w, |pushforward (embed n) (cubeLaw n 1) w - pushforward (embed n) (cubeLaw n (-1)) w|) =
        ∑ b, |cubeLaw n 1 b - cubeLaw n (-1) b| := by
    symm
    apply Fintype.sum_of_injective (embed n) (embed_injective n)
    · intro w hw
      simp [push_outside _ _ w hw]
    · intro b
      rw [push_injective _ (embed_injective n), push_injective _ (embed_injective n)]
  have diff (w : Source n) : law n mix 1 w - law n mix (-1) w =
      mix * (pushforward (embed n) (cubeLaw n 1) w - pushforward (embed n) (cubeLaw n (-1)) w) := by
    unfold law; ring
  simp only [sourceTV, diff, abs_mul, abs_of_nonneg hm, ← Finset.mul_sum, reduce,
    cube_abs, Finset.sum_add_distrib, cube_sum n hn 1 (Or.inr rfl),
    cube_sum n hn (-1) (Or.inl rfl)]
  ring

private theorem reply_tv (n : ℕ) (p q : Source n → ℝ) : replyTV p q = sourceTV p q := by
  classical
  unfold replyTV sourceTV
  rw [Finset.sum_image]
  · simp only [push_injective reply (native_reply_injective n)]
  · exact fun a _ b _ h => native_reply_injective n h

/-- For all n at least three and every real mixing parameter strictly between zero and one,
the same two full-support native laws agree on every proper complete-seam joint table and
positive-event conditional table, have equal fixed linear prefix expectations, and separate
actual null replies by the signed zero event and by total variation equal to the parameter. -/
theorem native_probability_separation (n : ℕ) (hn : 3 ≤ n) (mix : ℝ)
    (hl : 0 < mix) (hu : mix < 1) :
    (∀ ε ∈ ({-1, 1} : Finset ℤ),
      (∀ w : Source n, 0 < law n mix ε w) ∧ (∑ w, law n mix ε w) = 1) ∧
    (∀ A : Finset (Fin n), A ≠ Finset.univ → ∀ s y,
      jointMass (law n mix 1) A s y = jointMass (law n mix (-1)) A s y) ∧
    (∀ E : List Bool → Prop,
      seamEventMass (law n mix 1) E = seamEventMass (law n mix (-1)) E ∧
      (0 < seamEventMass (law n mix 1) E →
        ∀ A : Finset (Fin n), A ≠ Finset.univ → ∀ y,
          conditionalMass (law n mix 1) E A y = conditionalMass (law n mix (-1)) E A y)) ∧
    (∀ w : Source n,
      task 0 (List.ofFn w.val ++ [.zero]) = some ((reply w : ℕ) : ZMod 0)) ∧
    (pushforward (@reply n) (law n mix 1) 0 - pushforward (@reply n) (law n mix (-1)) 0 =
      (-1 : ℝ) ^ n * mix / 2 ^ (n - 1) ∧ (-1 : ℝ) ^ n * mix / 2 ^ (n - 1) ≠ 0) ∧
    (∀ j : ℕ, j ≤ n → ∀ a b : ℝ,
      (∑ w, law n mix 1 w * linearReadout j a b w) =
        ∑ w, law n mix (-1) w * linearReadout j a b w) ∧
    ((∑ w, law n mix 1 w * (reply w : ℝ)) =
      ∑ w, law n mix (-1) w * (reply w : ℝ)) ∧
    sourceTV (law n mix 1) (law n mix (-1)) = mix ∧
    replyTV (law n mix 1) (law n mix (-1)) = mix := by
  have pos : 0 < n := by omega
  refine ⟨?_, ?_, ?_, actual_null_reply, ?_, ?_, ?_, source_tv n pos mix hl.le, ?_⟩
  · intro ε hε
    have signs : ε = -1 ∨ ε = 1 := by simpa using hε
    exact law_probability n pos mix hl hu ε signs
  · intro A hA s y
    unfold jointMass
    exact (proper_event n pos mix (fun t => t = s) A hA y).symm
  · intro E
    refine ⟨(seam_events_equal n pos mix E).symm, ?_⟩
    intro _ A hA y
    unfold conditionalMass
    rw [proper_event n pos mix E A hA y, seam_events_equal n pos mix E]
  · refine ⟨zero_difference n mix, ?_⟩
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hl.ne')
      (pow_ne_zero _ (by norm_num))
  · intro j hj a b
    exact (linear_expectations n (by omega) mix j hj a b).symm
  · exact (reply_expectations n (by omega) mix).symm
  · rw [reply_tv, source_tv n pos mix hl.le]

#print axioms actual_state
#print axioms actual_quantity
#print axioms composition_coordinates
#print axioms actual_null_reply
#print axioms native_reply_injective
#print axioms native_probability_separation

end

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.JointLaw
