/- GID: D5/S3/Arith/ZeckendorfFutureKernel
   generality: G
   mirror-B: none(waiver:all-moduli-constructive-legal-continuations)
   mirror-E: none(waiver:exact-two-sided-future-classification)
   anchors: []
   digest: Legal Zeckendorf continuations identify exactly a unit-scaling quotient of residue states. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ZeckendorfFutureKernel

/-- The two consecutive weights after a given number of input positions. -/
def advance {R : Type*} [Add R] : ℕ → R × R → R × R
  | 0, z => z
  | n + 1, z => advance n (z.2, z.1 + z.2)

/-- Actual least-significant-first evaluation with arbitrary consecutive weights. -/
def value {R : Type*} [AddMonoid R] : R → R → List Bool → R
  | _, _, [] => 0
  | u, v, b :: w => (if b then u else 0) + value v (u + v) w

/-- Admissibility includes the incoming previous bit; high zero padding is allowed. -/
def legal : Bool → List Bool → Prop
  | _, [] => True
  | previous, b :: w => ¬(previous = true ∧ b = true) ∧ legal b w

/-- Equality of every legal continuation's terminal divisibility answer. -/
def sameFuture {M : ℕ} (previous : Bool)
    (r u v r' u' v' : ZMod M) : Prop :=
  ∀ w : List Bool,
    (legal previous w ∧ r + value u v w = 0) ↔
      (legal previous w ∧ r' + value u' v' w = 0)

private def zeros (n : ℕ) : List Bool := List.replicate n false

private def flag : Bool → List Bool → Bool
  | previous, [] => previous
  | _, b :: w => flag b w

private lemma advance_add {R : Type*} [Add R] (n k : ℕ) (z : R × R) :
    advance (n + k) z = advance k (advance n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simpa only [Nat.succ_add, advance] using ih (z.2, z.1 + z.2)

private lemma value_append {R : Type*} [AddMonoid R]
    (w w' : List Bool) (u v : R) :
    value u v (w ++ w') = value u v w +
      value (advance w.length (u,v)).1 (advance w.length (u,v)).2 w' := by
  induction w generalizing u v with
  | nil => simp [value, advance]
  | cons b w ih =>
    simp only [List.cons_append, value, List.length_cons, advance]
    rw [ih]
    exact (add_assoc _ _ _).symm

private lemma legal_append (w w' : List Bool) (b : Bool) :
    legal b (w ++ w') ↔ legal b w ∧ legal (flag b w) w' := by
  induction w generalizing b with
  | nil => simp [legal, flag]
  | cons c w ih => simp only [List.cons_append, legal, flag, ih, and_assoc]

private lemma flag_append (w w' : List Bool) (b : Bool) :
    flag b (w ++ w') = flag (flag b w) w' := by
  induction w generalizing b with
  | nil => rfl
  | cons c w ih => exact ih c

private lemma zero_facts {R : Type*} [AddMonoid R] (n : ℕ) :
    (∀ u v : R, value u v (zeros n) = 0) ∧
      (∀ b, legal b (zeros n)) ∧
      (∀ b, flag b (zeros (n+1)) = false) := by
  induction n with
  | zero => simp [zeros, value, legal, flag]
  | succ n ih =>
    constructor
    · intro u v
      simpa only [zeros, List.replicate_succ, value, Bool.false_eq_true,
        ↓reduceIte, zero_add] using ih.1 v (u+v)
    constructor
    · intro b
      simpa [zeros, List.replicate_succ, legal] using ih.2.1 false
    · intro b
      simpa only [zeros, List.replicate_succ, flag] using ih.2.2 false

/-- The only general-purpose queries in the proof are explicitly constructed
legal words. The period premise is the literal Fibonacci return pair in the
actual coefficient ring, and both rows have displayed Bezout certificates.
This is a theorem about every finite input word, including arbitrarily long
continuations, not a bounded automaton search. -/
theorem result (M T : ℕ) (hM : 2 ≤ M) (hT : 3 ≤ T)
    (hF : (Nat.fib T : ZMod M) = 0)
    (hG : (Nat.fib (T+1) : ZMod M) = 1)
    (previous : Bool) (r u v r' u' v' e f e' f' : ZMod M)
    (huv : e*u + f*v = 1) (huv' : e'*u' + f'*v' = 1) :
    (∀ A B : ZMod M, ∃ w : List Bool,
      (∀ b : Bool, legal b w) ∧
      (∀ x y : ZMod M, value x y w = A*x+B*y)) ∧
    (sameFuture previous r u v r' u' v' ↔
      ∃ a aInv : ZMod M, a*aInv = 1 ∧
        r' = a*r ∧ u' = a*u ∧ v' = a*v) := by
  letI : NeZero M := ⟨by omega⟩
  have pair_formula : ∀ n : ℕ, ∀ x y : ZMod M,
      advance (n+1) (x,y) =
        ((Nat.fib n : ZMod M)*x + (Nat.fib (n+1) : ZMod M)*y,
         (Nat.fib (n+1) : ZMod M)*x + (Nat.fib (n+2) : ZMod M)*y) := by
    intro n
    induction n with
    | zero => intro x y; simp [advance]
    | succ n ih =>
      intro x y
      change advance (n+1) (y,x+y) = _
      rw [ih]
      have hf : (Nat.fib (n+2) : ZMod M) =
          (Nat.fib n : ZMod M) + (Nat.fib (n+1) : ZMod M) := by
        simp only [Nat.fib_add_two, Nat.cast_add]
      have hg : (Nat.fib (n+3) : ZMod M) =
          (Nat.fib (n+1) : ZMod M) + (Nat.fib (n+2) : ZMod M) := by
        simpa [Nat.add_assoc] using congrArg (fun a : ℕ => (a : ZMod M))
          (Nat.fib_add_two (n := n+1))
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd, hf, hg] <;> ring
  have hprev : (Nat.fib (T-1) : ZMod M) = 1 := by
    have hg : (Nat.fib (T+1) : ZMod M) =
        (Nat.fib (T-1) : ZMod M) + (Nat.fib T : ZMod M) := by
      simpa only [show T-1+1=T by omega, show T-1+2=T+1 by omega,
        Nat.cast_add] using congrArg (fun a : ℕ => (a : ZMod M))
          (Nat.fib_add_two (n := T-1))
    rw [hG,hF,add_zero] at hg
    exact hg.symm
  have period : ∀ z : ZMod M × ZMod M, advance T z = z := by
    rintro ⟨x,y⟩
    have hh := pair_formula (T-1) x y
    simpa only [show T-1+1=T by omega, show T-1+2=T+1 by omega,
      hprev,hF,hG,zero_mul,one_mul,zero_add,add_zero] using hh
  have period2 : ∀ z : ZMod M × ZMod M, advance (2*T) z = z := by
    intro z
    rw [show 2*T=T+T by omega, advance_add, period, period]
  let pulse0 := zeros T ++ true :: zeros (T-1)
  let pulse1 := zeros (T+1) ++ true :: zeros (T-2)
  have pulseFacts : ∀ i : Bool,
      let w := if i then pulse1 else pulse0
      w.length = 2*T ∧ (∀ b, legal b w) ∧ (∀ b, flag b w = false) ∧
        (∀ x y : ZMod M, value x y w = if i then y else x) := by
    intro i
    have hzeros (n : ℕ) (b : Bool) (hn : 0 < n) : flag b (zeros n) = false := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact (zero_facts (R := ZMod M) j).2.2 b
    have hvzero (n : ℕ) (x y : ZMod M) := (zero_facts n).1 x y
    cases i
    · change pulse0.length = _ ∧ _
      refine ⟨by simp [pulse0,zeros]; omega, ?_, ?_, ?_⟩
      · intro b
        rw [legal_append]
        exact ⟨(zero_facts (R := ZMod M) T).2.1 b,
          by simpa [hzeros T b (by omega), legal] using
            (zero_facts (R := ZMod M) (T-1)).2.1 true⟩
      · intro b
        rw [flag_append]
        exact hzeros (T-1) true (by omega)
      · intro x y
        change value x y (zeros T ++ true :: zeros (T-1)) = x
        rw [value_append]
        have hlen : (zeros T).length = T := by simp [zeros]
        rw [hlen,period]
        change value x y (zeros T) + (x + value y (x+y) (zeros (T-1))) = x
        rw [hvzero,hvzero]
        simp
    · change pulse1.length = _ ∧ _
      refine ⟨by simp [pulse1,zeros]; omega, ?_, ?_, ?_⟩
      · intro b
        rw [legal_append]
        exact ⟨(zero_facts (R := ZMod M) (T+1)).2.1 b,
          by simpa [hzeros (T+1) b (by omega), legal] using
            (zero_facts (R := ZMod M) (T-2)).2.1 true⟩
      · intro b
        rw [flag_append]
        exact hzeros (T-2) true (by omega)
      · intro x y
        change value x y (zeros (T+1) ++ true :: zeros (T-2)) = y
        rw [value_append]
        have hlen : (zeros (T+1)).length = T+1 := by simp [zeros]
        have hshift : advance (T+1) (x,y) = (y,x+y) := by
          rw [advance_add,period]; rfl
        rw [hlen,hshift]
        change value x y (zeros (T+1)) +
          (y + value (x+y) (y+(x+y)) (zeros (T-2))) = y
        rw [hvzero,hvzero]
        simp
  let copies : ℕ → List Bool → List Bool := fun n w => (List.replicate n w).flatten
  have repeats : ∀ n : ℕ, ∀ i : Bool,
      let w := copies n (if i then pulse1 else pulse0)
      w.length = n*(2*T) ∧ (∀ b, legal b w) ∧
        (∀ x y : ZMod M, advance w.length (x,y) = (x,y)) ∧
        (∀ x y : ZMod M, value x y w = (n : ZMod M)*(if i then y else x)) := by
    intro n
    induction n with
    | zero => intro i; simp [copies,legal,value,advance]
    | succ n ih =>
      intro i
      have hp := pulseFacts i
      have hi := ih i
      simp only [copies,List.replicate_succ,List.flatten_cons] at *
      refine ⟨by rw [List.length_append,hp.1,hi.1]; omega, ?_, ?_, ?_⟩
      · intro b
        exact (legal_append _ _ b).mpr ⟨hp.2.1 b, hi.2.1 _⟩
      · intro x y
        rw [List.length_append,advance_add,hp.1,period2]
        exact hi.2.2.1 x y
      · intro x y
        rw [value_append,hp.1,period2,hp.2.2.2,hi.2.2.2]
        push_cast
        ring
  have program : ∀ A B : ZMod M, ∃ w : List Bool,
      (∀ b, legal b w) ∧ (∀ x y : ZMod M, value x y w = A*x+B*y) := by
    intro A B
    let w0 := copies A.val pulse0
    let w1 := copies B.val pulse1
    have h0 := repeats A.val false
    have h1 := repeats B.val true
    refine ⟨w0++w1, ?_, ?_⟩
    · intro b
      exact (legal_append _ _ b).mpr ⟨h0.2.1 b, h1.2.1 _⟩
    · intro x y
      rw [value_append,h0.2.2.1]
      simpa only [Bool.false_eq_true,↓reduceIte,ZMod.natCast_zmod_val] using
        congrArg₂ (fun a b : ZMod M => a+b) (h0.2.2.2 x y) (h1.2.2.2 x y)
  refine ⟨program, ?_⟩
  constructor
  · intro heq
    have hfibers : ∀ A B : ZMod M,
        r+A*u+B*v=0 ↔ r'+A*u'+B*v'=0 := by
      intro A B
      obtain ⟨w,hw,hval⟩ := program A B
      have hh := heq w
      simpa only [hw previous,hval,and_true,true_and,add_assoc] using hh
    let a := e*u'+f*v'
    have hr : r'=a*r := by
      have hzero : r+(-r*e)*u+(-r*f)*v=0 := by
        linear_combination -r*huv
      have hz := (hfibers (-r*e) (-r*f)).mp hzero
      dsimp [a]
      linear_combination hz
    have hcross : v*u'-u*v'=0 := by
      have hzero : r+(-r*e+v)*u+(-r*f-u)*v=0 := by
        linear_combination -r*huv
      have hz := (hfibers (-r*e+v) (-r*f-u)).mp hzero
      dsimp [a] at hr
      linear_combination hz-hr
    have hu : u'=a*u := by
      dsimp [a]
      linear_combination -u'*huv+f*hcross
    have hv : v'=a*v := by
      dsimp [a]
      linear_combination -v'*huv-e*hcross
    refine ⟨a,e'*u+f'*v,?_,hr,hu,hv⟩
    calc
      a*(e'*u+f'*v)=e'*u'+f'*v' := by rw [hu,hv]; ring
      _=1 := huv'
  · rintro ⟨a,aInv,ha,hr,hu,hv⟩
    have hscale : ∀ w : List Bool, ∀ x y : ZMod M,
        value (a*x) (a*y) w = a*value x y w := by
      intro w
      induction w with
      | nil => simp [value]
      | cons b w ih =>
        intro x y
        simp only [value,← mul_add]
        rw [ih]
        cases b <;> simp [mul_add]
    intro w
    have hz : r'+value u' v' w=a*(r+value u v w) := by
      rw [hr,hu,hv,hscale,mul_add]
    rw [hz]
    constructor
    · rintro ⟨hl,he⟩
      exact ⟨hl,by rw [he,mul_zero]⟩
    · rintro ⟨hl,he⟩
      refine ⟨hl,?_⟩
      have hh := congrArg (fun z : ZMod M => aInv*z) he
      simpa only [← mul_assoc,mul_comm aInv a,ha,one_mul,mul_zero] using hh

end D5.S3.Arith.ZeckendorfFutureKernel
