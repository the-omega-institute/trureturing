/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/CommonDirectionScheduler
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs]
   utility: none
   digest: Effective digit and CRT control retains complete replies in two common directions. -/

import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Sort

/-! # Full-reply digit scheduling in common compiler directions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler

open TerminalGcdAcquisitionCost (quantity replace runWord terminalGcd costBound residueSource)
open PositiveProbeCompiler (direction compile graftBound effective_short_compiler)

/-- A base-p prefix and the next digit being tested. All fields are local data. -/
structure Axis where
  level : ℕ
  residue : ℕ
  trial : ℕ
  deriving DecidableEq, Repr

def initialAxis : Axis := ⟨0, 0, 0⟩

def center (p : ℕ) (a : Axis) : ℕ := a.residue + p ^ a.level * a.trial

/-- A full gcd answer is retained by the caller. This update asks only its
next-digit divisibility question, without replacing the answer by a bit. -/
def advance (p e : ℕ) (a : Axis) (g : ℕ) : Axis :=
  if e ≤ a.level then a else
  if p ^ (a.level + 1) ∣ g then ⟨a.level + 1, center p a, 0⟩ else
  if a.trial + 1 < p - 1 then ⟨a.level, a.residue, a.trial + 1⟩ else
    ⟨a.level + 1, a.residue + p ^ a.level * (p - 1), 0⟩

private def Valid (p e n : ℕ) (a : Axis) : Prop :=
  a.level ≤ e ∧ a.residue = n % p ^ a.level ∧
    a.trial < p - 1 ∧ a.trial ≤ n / p ^ a.level % p

def remaining (p e : ℕ) (a : Axis) : ℕ := (e - a.level) * (p - 1) - a.trial

private theorem initial_valid (p e n : ℕ) (hp : 2 ≤ p) :
    Valid p e n initialAxis := by
  simp [Valid, initialAxis]
  omega

private theorem advance_valid (p e n g : ℕ) (hp : 2 ≤ p) (a : Axis)
    (ha : Valid p e n a)
    (reply : a.level < e → (p ^ (a.level + 1) ∣ g ↔
      n % p ^ (a.level + 1) = center p a)) :
    Valid p e n (advance p e a g) ∧
      (a.level < e → remaining p e (advance p e a g) < remaining p e a) := by
  obtain ⟨hs, hr, ht, hd⟩ := ha
  have hpow : 0 < p ^ a.level := pow_pos (by omega) _
  have digit : n / p ^ a.level % p < p := Nat.mod_lt _ (by omega)
  have expand := Nat.mod_pow_succ (x := n) (b := p) (k := a.level)
  by_cases he : e ≤ a.level
  · simp only [advance, he, ↓reduceIte]
    exact ⟨⟨hs, hr, ht, hd⟩, by omega⟩
  have hse : a.level < e := by omega
  have hprod : a.trial < (e - a.level) * (p - 1) := by
    have hm := Nat.mul_le_mul_right (p - 1) (by omega : 1 ≤ e - a.level)
    omega
  have ranks : (e - a.level) * (p - 1) =
      (e - (a.level + 1)) * (p - 1) + (p - 1) := by
    calc
      _ = (e - (a.level + 1) + 1) * (p - 1) := by congr 1; omega
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]
  by_cases hit : p ^ (a.level + 1) ∣ g
  · have matched := (reply hse).mp hit
    have hdigit : a.trial = n / p ^ a.level % p := by
      rw [expand, center, hr] at matched
      exact Nat.eq_of_mul_eq_mul_left hpow (Nat.add_left_cancel matched.symm)
    simp only [advance, he, hit, ↓reduceIte, Valid]
    constructor
    · exact ⟨by omega, matched.symm, by omega, Nat.zero_le _⟩
    · intro _
      simp only [remaining, Nat.sub_zero]
      omega
  have missed : a.trial ≠ n / p ^ a.level % p := by
    intro h
    apply hit
    apply (reply hse).mpr
    simpa only [center, hr, h] using expand
  have strict : a.trial < n / p ^ a.level % p := by omega
  by_cases more : a.trial + 1 < p - 1
  · simp only [advance, he, hit, more, ↓reduceIte, Valid]
    refine ⟨⟨hs, hr, by trivial, by omega⟩, ?_⟩
    intro _
    simp only [remaining]
    omega
  · have last : n / p ^ a.level % p = p - 1 := by omega
    simp only [advance, he, hit, more, ↓reduceIte, Valid]
    constructor
    · refine ⟨by omega, ?_, by omega, Nat.zero_le _⟩
      simpa only [hr, last] using expand.symm
    · intro _
      simp only [remaining, Nat.sub_zero]
      omega

/-- There is one finite local record per prime divisor of the public modulus. -/
abbrev Joint (H : ℕ) := H.primeFactors → Axis

def desired (p e : ℕ) (a : Axis) : ℕ :=
  if e ≤ a.level then a.residue else center p a

def Compatible (H : ℕ) (a : Joint H) (c : ℕ) : Prop :=
  ∀ p : H.primeFactors,
    p.val ^ H.factorization p.val ∣ desired p.val (H.factorization p.val) (a p) + c

instance compatibleDecidable (H : ℕ) (a : Joint H) (c : ℕ) :
    Decidable (Compatible H a c) := inferInstanceAs (Decidable (∀ p : H.primeFactors, _))

/-- Bounded public CRT search. This implementation makes no polynomial local-work claim. -/
def shift (H : ℕ) (a : Joint H) : ℕ :=
  ((List.range H).find? (fun c => decide (Compatible H a c))).getD 0

private theorem shift_spec (H : ℕ) (hH : 0 < H) (a : Joint H) :
    shift H a < H ∧ Compatible H a (shift H a) := by
  letI : NeZero H := ⟨by omega⟩
  let crt := ZMod.equivPi H (by omega)
  let z : ZMod H := crt.symm (fun p => -(desired p.val (H.factorization p.val) (a p) :
    ZMod (p.val ^ H.factorization p.val)))
  have exists_shift : ∃ c ∈ List.range H, Compatible H a c := by
    refine ⟨z.val, List.mem_range.mpr z.val_lt, ?_⟩
    intro p
    let π := TerminalGcdAcquisitionCost.localProjection H p
    have proj : crt z p = π z := by
      exact RingHom.congr_fun
        (Subsingleton.elim ((Pi.evalRingHom _ p).comp crt.toRingHom) π) z
    have hz : π z = -(desired p.val (H.factorization p.val) (a p) :
        ZMod (p.val ^ H.factorization p.val)) := by
      rw [← proj]
      exact congrFun (crt.apply_symm_apply _) p
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_add]
    have hv : (z.val : ZMod (p.val ^ H.factorization p.val)) = π z := by
      exact (ZMod.cast_eq_val z).symm
    rw [hv, hz, add_neg_cancel]
  obtain ⟨c, hc, hs⟩ := exists_shift
  have some : ∃ d, (List.range H).find? (fun c => decide (Compatible H a c)) = some d := by
    apply Option.ne_none_iff_exists'.mp
    intro hn
    have hf := List.find?_eq_none.mp hn c hc
    have ht : decide (Compatible H a c) = true := by simp [hs]
    exact hf ht
  obtain ⟨d, hd⟩ := some
  have hm := List.mem_of_find?_eq_some hd
  have ht := List.find?_some hd
  simpa only [shift, hd, Option.getD_some] using
    And.intro (List.mem_range.mp hm) (of_decide_eq_true ht)

def advanceAll (H : ℕ) (a : Joint H) (g : ℕ) : Joint H :=
  fun p => advance p.val (H.factorization p.val) (a p) g

/-- The oracle argument is an operational reply interface. Its full answers,
including all intermediate depths, are kept in chronological order. -/
def rounds (H : ℕ) (answer : ℕ → ℕ) : ℕ → Joint H → Joint H × List (ℕ × ℕ)
  | 0, a => (a, [])
  | j + 1, a =>
    let c := shift H a
    let g := answer c
    let t := rounds H answer j (advanceAll H a g)
    (t.1, (c, g) :: t.2)

private theorem reply_test (H n c : ℕ) (a : Joint H) (hc : Compatible H a c)
    (p : H.primeFactors) (ha : Valid p.val (H.factorization p.val) n (a p))
    (active : (a p).level < H.factorization p.val) :
    p.val ^ ((a p).level + 1) ∣ Nat.gcd (n + c) H ↔
      n % p.val ^ ((a p).level + 1) = center p.val (a p) := by
  let m := p.val ^ ((a p).level + 1)
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hm : m ∣ H := (pow_dvd_pow p.val (by omega)).trans (Nat.ordProj_dvd H p.val)
  have hh : m ∣ center p.val (a p) + c := by
    have hs := hc p
    simp only [desired, if_neg (by omega : ¬ H.factorization p.val ≤ (a p).level)] at hs
    exact (pow_dvd_pow p.val (by omega)).trans hs
  have hlt : center p.val (a p) < m := by
    have hr : (a p).residue < p.val ^ (a p).level := by
      rw [ha.2.1]
      exact Nat.mod_lt _ (pow_pos hp.pos _)
    have ht := ha.2.2.1
    have ht' : (a p).trial + 1 ≤ p.val := by omega
    have hmul := Nat.mul_le_mul_left (p.val ^ (a p).level) ht'
    dsimp [center, m]
    rw [pow_succ]
    nlinarith
  rw [Nat.dvd_gcd_iff, and_iff_left hm]
  have cancel : m ∣ n + c ↔ Nat.ModEq m n (center p.val (a p)) := by
    have hh' : Nat.ModEq m (center p.val (a p) + c) 0 :=
      Nat.modEq_zero_iff_dvd.mpr hh
    exact ⟨fun h => Nat.ModEq.add_right_cancel' c
        ((Nat.modEq_zero_iff_dvd.mpr h).trans hh'.symm),
      fun h => Nat.modEq_zero_iff_dvd.mp ((h.add_right c).trans hh')⟩
  rw [cancel]
  change n % m = center p.val (a p) % m ↔ _
  rw [Nat.mod_eq_of_lt hlt]

private theorem rounds_correct (H n : ℕ) (hH : 0 < H) (answer : ℕ → ℕ)
    (answers : ∀ c, answer c = Nat.gcd (n + c) H) (j : ℕ) (a : Joint H)
    (valid : ∀ p, Valid p.val (H.factorization p.val) n (a p))
    (bound : ∀ p, remaining p.val (H.factorization p.val) (a p) ≤ j) :
    (∀ p, ((rounds H answer j a).1 p).level = H.factorization p.val ∧
      ((rounds H answer j a).1 p).residue = n % p.val ^ H.factorization p.val) ∧
    (rounds H answer j a).2.length = j := by
  induction j generalizing a with
  | zero =>
    refine ⟨?_, rfl⟩
    intro p
    change (a p).level = H.factorization p.val ∧
      (a p).residue = n % p.val ^ H.factorization p.val
    have hp := Nat.prime_of_mem_primeFactors p.property
    have hp2 := hp.two_le
    have hv := valid p
    have hb := bound p
    have done : (a p).level = H.factorization p.val := by
      have ht := hv.2.2.1
      have hs := hv.1
      by_contra hn
      have hmul := Nat.mul_le_mul_right (p.val - 1)
        (by omega : 1 ≤ H.factorization p.val - (a p).level)
      simp only [remaining] at hb
      omega
    exact ⟨done, by simpa only [done] using hv.2.1⟩
  | succ j ih =>
    let c := shift H a
    let g := answer c
    have hs := (shift_spec H hH a).2
    have step_spec (p : H.primeFactors) := advance_valid p.val
      (H.factorization p.val) n g (Nat.prime_of_mem_primeFactors p.property).two_le
      (a p) (valid p) (by
        intro h
        change p.val ^ ((a p).level + 1) ∣ answer c ↔ _
        rw [answers c]
        exact reply_test H n c a hs p (valid p) h)
    have next_valid : ∀ p, Valid p.val (H.factorization p.val) n (advanceAll H a g p) :=
      fun p => (step_spec p).1
    have next_bound : ∀ p, remaining p.val (H.factorization p.val)
        (advanceAll H a g p) ≤ j := by
      intro p
      by_cases ha : (a p).level < H.factorization p.val
      · change remaining p.val (H.factorization p.val)
          (advance p.val (H.factorization p.val) (a p) g) ≤ j
        have := (step_spec p).2 ha
        have := bound p
        omega
      · simp only [advanceAll, advance, if_pos (by omega : H.factorization p.val ≤ (a p).level),
          remaining, Nat.sub_eq_zero_of_le (by omega : H.factorization p.val ≤ (a p).level),
          Nat.zero_mul, Nat.zero_sub, Nat.zero_le]
    obtain ⟨correct, length⟩ := ih (advanceAll H a g) next_valid next_bound
    exact ⟨correct, by simpa only [rounds, List.length_cons] using congrArg Nat.succ length⟩

/-- Reconstruct the scalar from the completed local records. -/
def recover (H : ℕ) (a : Joint H) : ZMod H := -(shift H a : ZMod H)

def stage (H : ℕ) (answer : ℕ → ℕ) : ZMod H × List (ℕ × ℕ) :=
  if H = 1 then (0, []) else
  let t := rounds H answer (costBound H) (fun _ => initialAxis)
  (recover H t.1, t.2)

private theorem recover_correct (H n : ℕ) (hH : 0 < H) (a : Joint H)
    (done : ∀ p, (a p).level = H.factorization p.val ∧
      (a p).residue = n % p.val ^ H.factorization p.val) :
    recover H a = (n : ZMod H) := by
  letI : NeZero H := ⟨by omega⟩
  apply (ZMod.equivPi H (by omega)).injective
  funext p
  let π := TerminalGcdAcquisitionCost.localProjection H p
  have proj (z : ZMod H) : (ZMod.equivPi H (by omega)) z p = π z := by
    exact RingHom.congr_fun
      (Subsingleton.elim ((Pi.evalRingHom _ p).comp
        (ZMod.equivPi H (by omega)).toRingHom) π) z
  rw [proj, proj]
  have hc := (shift_spec H hH a).2 p
  simp only [desired, (done p).1, le_refl, ↓reduceIte, (done p).2] at hc
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hc
  have hm : ((n % p.val ^ H.factorization p.val : ℕ) :
      ZMod (p.val ^ H.factorization p.val)) = (n : ZMod _) := by simp
  rw [Nat.cast_add, hm] at hz
  change π (-(shift H a : ZMod H)) = π (n : ZMod H)
  simp only [map_neg, map_natCast]
  exact (eq_neg_of_add_eq_zero_left hz).symm

private theorem stage_correct (H n : ℕ) (hH : 1 ≤ H) (answer : ℕ → ℕ)
    (answers : ∀ c, answer c = Nat.gcd (n + c) H) :
    (stage H answer).1 = (n : ZMod H) ∧
    (stage H answer).2.length = if H = 1 then 0 else costBound H := by
  by_cases h1 : H = 1
  · subst H
    exact ⟨Subsingleton.elim _ _, by simp [stage]⟩
  have result := rounds_correct H n (by omega) answer answers (costBound H)
    (fun _ => initialAxis)
    (fun p => initial_valid p.val _ n (Nat.prime_of_mem_primeFactors p.property).two_le)
    (by
      intro p
      simpa only [remaining, initialAxis, Nat.sub_zero, costBound] using
        (Finset.le_sup (f := fun p => H.factorization p * (p - 1)) p.property))
  exact ⟨by simpa only [stage, h1, ↓reduceIte] using
    recover_correct H n (by omega) _ result.1,
    by simpa only [stage, h1, ↓reduceIte] using result.2⟩

private theorem rounds_tape (H : ℕ) (hH : 0 < H) (answer : ℕ → ℕ)
    (j : ℕ) (a : Joint H) :
    ∀ t ∈ (rounds H answer j a).2, t.1 < H ∧ t.2 = answer t.1 := by
  induction j generalizing a with
  | zero => simp [rounds]
  | succ j ih =>
    intro t ht
    simp only [rounds, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨(shift_spec H hH a).1, rfl⟩
    · exact ih _ t ht

/-- Both stages use the same source-blind local policy; only the public direction differs. -/
def schedule (H : ℕ) (answer : ℕ → ℕ → ℕ) :
    (ZMod H × ZMod H) × List (ℕ × ℕ × ℕ) :=
  let s := stage H (answer (direction H))
  let t := stage H (answer (direction H + 1))
  ((s.1, t.1), s.2.map (fun x => (direction H, x)) ++
    t.2.map (fun x => (direction H + 1, x)))

/-- This interpreter specifies the reply obtained by an actual compiled experiment
at the required residue cut. It is not a primitive of the local controller. -/
def compiledReply (H : ℕ) (v : ℕ × ℕ) (k c : ℕ) : ℕ :=
  terminalGcd H (compile H k c) v

/-- Exact public interface for positive closing: each experiment begins at a
source having the entry residue, emits the compiler word chronologically, pays
for its full terminal reply, then returns to that residue before the next cut. -/
def ClosingCut (H k c : ℕ) (entry current : ℕ × ℕ) : Prop :=
  residueSource H current = residueSource H entry ∧
  terminalGcd H (compile H k c) current = terminalGcd H (compile H k c) entry

/-- The scheduler earns the two consecutive scalar coordinates, with full replies
and exactly the scalar minimax budget in each direction. -/
private theorem effective_common_direction (H : ℕ) (hH : 1 ≤ H) (v : ℕ × ℕ) :
    (schedule H (compiledReply H v)).1 =
      ((quantity (replace^[direction H] v) : ZMod H),
       (quantity (replace^[direction H + 1] v) : ZMod H)) ∧
    (schedule H (compiledReply H v)).2.length =
      (if H = 1 then 0 else 2 * costBound H) ∧
    ∀ t ∈ (schedule H (compiledReply H v)).2,
      (t.1 = direction H ∨ t.1 = direction H + 1) ∧ t.2.1 < H ∧
      (compile H t.1 t.2.1).count true = t.1 ∧
      (compile H t.1 t.2.1).count false ≤ graftBound H ∧
      t.2.2 = Nat.gcd (quantity (replace^[t.1] v) + t.2.1) H ∧
      t.2.2 = terminalGcd H (compile H t.1 t.2.1) v := by
  by_cases h1 : H = 1
  · subst H
    refine ⟨Subsingleton.elim _ _, by simp [schedule, stage], ?_⟩
    simp [schedule, stage]
  have hh : 1 < H := by omega
  have supply (k c : ℕ) (hk : k = direction H ∨ k = direction H + 1) :=
    (effective_short_compiler H hh).2.2.2 k c hk
  have correctness (k : ℕ) (hk : k = direction H ∨ k = direction H + 1) :=
    stage_correct H (quantity (replace^[k] v)) hH (compiledReply H v k)
      (fun c => ((supply k c hk).2.2.2.2.2.2 v).2)
  refine ⟨Prod.ext (correctness _ (Or.inl rfl)).1 (correctness _ (Or.inr rfl)).1, ?_, ?_⟩
  · simp only [schedule, List.length_append, List.length_map]
    rw [(correctness _ (Or.inl rfl)).2, (correctness _ (Or.inr rfl)).2]
    simp only [h1, ↓reduceIte]
    omega
  · intro t ht
    simp only [schedule, List.mem_append, List.mem_map] at ht
    have run_tape (k : ℕ) (x : ℕ × ℕ)
        (hx : x ∈ (stage H (compiledReply H v k)).2) :
        x.1 < H ∧ x.2 = compiledReply H v k x.1 := by
      simp only [stage, h1, ↓reduceIte] at hx
      exact rounds_tape H (by omega) _ _ _ x hx
    rcases ht with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · have ht := run_tape _ x hx
      have hs := supply (direction H) x.1 (Or.inl rfl)
      exact ⟨Or.inl rfl, ht.1, hs.2.2.2.1, hs.2.2.2.2.2.1,
        ht.2.trans (hs.2.2.2.2.2.2 v).2, ht.2⟩
    · have ht := run_tape _ x hx
      have hs := supply (direction H + 1) x.1 (Or.inr rfl)
      exact ⟨Or.inr rfl, ht.1, hs.2.2.2.1, hs.2.2.2.2.2.1,
        ht.2.trans (hs.2.2.2.2.2.2 v).2, ht.2⟩

/-- Invert the two scalar rows and then the public common Fibonacci direction. -/
def decode (H : ℕ) (y : ZMod H × ZMod H) : ZMod H × ZMod H :=
  (TerminalGcdAcquisitionCost.residueReplace H ^ direction H).symm
    (5 * y.1 - 3 * y.2, -3 * y.1 + 2 * y.2)

private theorem cast_iterate (H k : ℕ) (v : ℕ × ℕ) :
    residueSource H (replace^[k] v) =
      (TerminalGcdAcquisitionCost.residueReplace H ^ k) (residueSource H v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, pow_succ, Equiv.Perm.mul_apply]
    congr 1
    ext <;> simp [residueSource, replace, TerminalGcdAcquisitionCost.residueReplace]

private theorem decode_scalars (H : ℕ) (v : ℕ × ℕ) :
    decode H ((quantity (replace^[direction H] v) : ZMod H),
      (quantity (replace^[direction H + 1] v) : ZMod H)) = residueSource H v := by
  have rows :
      (5 * (quantity (replace^[direction H] v) : ZMod H) -
         3 * (quantity (replace^[direction H + 1] v) : ZMod H),
       -3 * (quantity (replace^[direction H] v) : ZMod H) +
         2 * (quantity (replace^[direction H + 1] v) : ZMod H)) =
        residueSource H (replace^[direction H] v) := by
    rw [Function.iterate_succ_apply']
    ext <;> simp [quantity, replace, residueSource] <;> ring
  unfold decode
  rw [rows, cast_iterate]
  exact Equiv.symm_apply_apply _ _

private theorem closing_cut (H : ℕ) (hH : 1 < H) (k c : ℕ)
    (hk : k = direction H ∨ k = direction H + 1) (entry current : ℕ × ℕ)
    (hres : residueSource H current = residueSource H entry) :
    ClosingCut H k c entry current := by
  refine ⟨hres, ?_⟩
  have supply := (effective_short_compiler H hH).2.2.2 k c hk
  rw [(supply.2.2.2.2.2.2 current).2, (supply.2.2.2.2.2.2 entry).2]
  have hr : residueSource H (replace^[k] current) = residueSource H (replace^[k] entry) := by
    rw [cast_iterate, cast_iterate, hres]
  have hq := congrArg (fun z : ZMod H × ZMod H => 2 * z.1 + 3 * z.2) hr
  have hm : Nat.ModEq H (quantity (replace^[k] current)) (quantity (replace^[k] entry)) :=
    (ZMod.natCast_eq_natCast_iff _ _ H).mp (by simpa [quantity, residueSource] using hq)
  exact (hm.add_right c).gcd_eq

/-- All natural entries, including zero, are identified by an executable two-stage
full-reply policy. The separate closing implementation must realize its cuts. -/
theorem effective_scheduler (H : ℕ) (hH : 1 ≤ H) (v : ℕ × ℕ) :
    decode H (schedule H (compiledReply H v)).1 = residueSource H v ∧
    (schedule H (compiledReply H v)).1 =
      ((quantity (replace^[direction H] v) : ZMod H),
       (quantity (replace^[direction H + 1] v) : ZMod H)) ∧
    (schedule H (compiledReply H v)).2.length =
      (if H = 1 then 0 else 2 * costBound H) ∧
    ∀ t ∈ (schedule H (compiledReply H v)).2,
      (t.1 = direction H ∨ t.1 = direction H + 1) ∧ t.2.1 < H ∧
      (compile H t.1 t.2.1).count true = t.1 ∧
      (compile H t.1 t.2.1).count false ≤ graftBound H ∧
      t.2.2 = Nat.gcd (quantity (replace^[t.1] v) + t.2.1) H ∧
      t.2.2 = terminalGcd H (compile H t.1 t.2.1) v ∧
      ∀ current : ℕ × ℕ, residueSource H current = residueSource H v →
        ClosingCut H t.1 t.2.1 v current := by
  have h := effective_common_direction H hH v
  refine ⟨by rw [h.1]; exact decode_scalars H v, h.1, h.2.1, ?_⟩
  intro t ht
  obtain ⟨hk, hc, hr, hg, hs, htape⟩ := h.2.2 t ht
  refine ⟨hk, hc, hr, hg, hs, htape, ?_⟩
  intro current hcurrent
  have hne : H ≠ 1 := by
    intro he
    subst H
    simpa [schedule, stage] using ht
  exact closing_cut H (by omega) t.1 t.2.1 hk v current hcurrent

/-- Binary naturals use little-endian digits. Their lists are finite, including
an empty representation of zero. -/
abbrev Binary := List ℕ
abbrev BinaryAxis := Binary × Binary × Binary
abbrev BinaryJoint (H : ℕ) := List (H.primeFactors × BinaryAxis)

def encodeAxis (a : Axis) : BinaryAxis :=
  (Nat.digits 2 a.level, Nat.digits 2 a.residue, Nat.digits 2 a.trial)

def decodeAxis (a : BinaryAxis) : Axis :=
  ⟨Nat.ofDigits 2 a.1, Nat.ofDigits 2 a.2.1, Nat.ofDigits 2 a.2.2⟩

/-- The prime keys enumerate a fixed public finite table, not source data. -/
def encodeJoint (H : ℕ) (a : Joint H) : BinaryJoint H :=
  (H.primeFactors.attach.sort (· ≤ ·)).map (fun p => (p, encodeAxis (a p)))

def decodeJoint (H : ℕ) (b : BinaryJoint H) : Joint H :=
  fun p => decodeAxis ((b.lookup p).getD ([], [], []))

private theorem decode_encode (H : ℕ) (a : Joint H) :
    decodeJoint H (encodeJoint H a) = a := by
  funext p
  have h := List.lookup_graph (fun p => encodeAxis (a p))
    ((Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_attach _ p))
  unfold decodeJoint encodeJoint
  rw [h]
  simp only [Option.getD_some, decodeAxis, encodeAxis, Nat.ofDigits_digits]

/-- The binary transition decodes only local finite data and the actual complete
binary reply, then commits the next local table. -/
def binaryAdvance (H : ℕ) (b : BinaryJoint H) (reply : Binary) : BinaryJoint H :=
  encodeJoint H (advanceAll H (decodeJoint H b) (Nat.ofDigits 2 reply))

def binaryShift (H : ℕ) (b : BinaryJoint H) : Binary :=
  Nat.digits 2 (shift H (decodeJoint H b))

/-- Finite binary refinement commutes with every full-reply transition, including
zero, invalid histories and arbitrary public moduli. No source coordinate is an input. -/
private theorem binary_refinement (H : ℕ) (a : Joint H) (g : ℕ) :
    decodeJoint H (encodeJoint H a) = a ∧
    Nat.ofDigits 2 (binaryShift H (encodeJoint H a)) = shift H a ∧
    decodeJoint H (binaryAdvance H (encodeJoint H a) (Nat.digits 2 g)) =
      advanceAll H a g ∧
    (encodeJoint H a).length = H.primeFactors.card ∧
    (∀ n d, d ∈ Nat.digits 2 n → d < 2) := by
  refine ⟨decode_encode H a, ?_, ?_, ?_, ?_⟩
  · simp only [binaryShift, decode_encode, Nat.ofDigits_digits]
  · simp only [binaryAdvance, decode_encode, Nat.ofDigits_digits]
  · simp [encodeJoint]
  · intro n d hd
    exact Nat.digits_lt_base (by decide) hd

/-- A binary reply port transports the entire natural reply, not its nonzero bit. -/
def binaryRounds (H : ℕ) (answer : Binary → Binary) :
    ℕ → BinaryJoint H → BinaryJoint H × List (Binary × Binary)
  | 0, b => (b, [])
  | j + 1, b =>
    let c := binaryShift H b
    let g := answer c
    let t := binaryRounds H answer j (binaryAdvance H b g)
    (t.1, (c, g) :: t.2)

private theorem binary_rounds (H : ℕ) (answer : ℕ → ℕ) (j : ℕ) (a : Joint H) :
    binaryRounds H (fun c => Nat.digits 2 (answer (Nat.ofDigits 2 c))) j
      (encodeJoint H a) =
    (encodeJoint H (rounds H answer j a).1,
      (rounds H answer j a).2.map (fun t => (Nat.digits 2 t.1, Nat.digits 2 t.2))) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    simp only [binaryRounds, binaryShift, decode_encode, Nat.ofDigits_digits,
      binaryAdvance, rounds, List.map_cons]
    rw [ih]

/-- For every finite horizon the binary controller and numeric controller have
identical decisions, states and complete chronological replies. The prime table
is finite; every stored digit and every encoded reply is binary. -/
theorem finite_binary_execution (H : ℕ) (answer : ℕ → ℕ) (j : ℕ) (a : Joint H) :
    binaryRounds H (fun c => Nat.digits 2 (answer (Nat.ofDigits 2 c))) j
      (encodeJoint H a) =
    (encodeJoint H (rounds H answer j a).1,
      (rounds H answer j a).2.map (fun t => (Nat.digits 2 t.1, Nat.digits 2 t.2))) ∧
    decodeJoint H (encodeJoint H a) = a ∧
    (encodeJoint H a).length = H.primeFactors.card ∧
    (∀ n d, d ∈ Nat.digits 2 n → d < 2) := by
  have h := binary_refinement H a 0
  exact ⟨binary_rounds H answer j a, h.1, h.2.2.2.1, h.2.2.2.2⟩

#print axioms schedule
#print axioms binaryRounds
#print axioms effective_scheduler
#print axioms finite_binary_execution

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.CommonDirectionScheduler
