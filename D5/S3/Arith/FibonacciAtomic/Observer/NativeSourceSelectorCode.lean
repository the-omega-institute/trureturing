/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Closed selector with universal raw instructions and exact original-state realization. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveSourceProducer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode

open Nat.Partrec (Code)
open NativeSerialEffective

private def add : Code :=
  .prec Code.id (.comp .succ (.comp .right .right))

private def pred : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero Code.id)

/-- Pairing and unpairing turn any natural input into a Boolean-sized counter. -/
private def positive : Code :=
  .comp .left (.comp .succ (.pair .zero Code.id))

private def isZero : Code :=
  .comp (.prec (Code.const 1) .zero) (.pair .zero positive)

/-- The branch counter is zero or one. The zero branch is evaluated before
the positive branch, as required by the primitive-recursion constructor. -/
private def branch (test zeroCase positiveCase : Code) : Code :=
  .comp (.prec zeroCase (.comp positiveCase .left))
    (.pair Code.id (.comp positive test))

private def double (c : Code) : Code := .comp add (.pair c c)
private def inl (c : Code) : Code := double c
private def inr (c : Code) : Code := .comp .succ (double c)
private def cons (h t : Code) : Code := .comp .succ (.pair h t)

/-- Quotient and parity are kept together throughout recursion. -/
private def halfParity : Code :=
  let result : Code := .comp .right .right
  let quotient : Code := .comp .left result
  let parity : Code := .comp .right result
  .comp (.prec (.pair .zero .zero)
    (branch parity (.pair quotient (Code.const 1))
      (.pair (.comp .succ quotient) .zero))) (.pair .zero Code.id)

private def half (c : Code) : Code := .comp .left (.comp halfParity c)
private def parity (c : Code) : Code := .comp .right (.comp halfParity c)

/-- Iterate a numeric step and minimize the first zero of the supplied test.
The returned value is the numeric state at that index. -/
private def firstZero (initial step test : Code) : Code :=
  let iter : Code := .prec initial (.comp step (.comp .right .right))
  let index : Code := .comp (.rfind' (.comp test iter)) (.pair Code.id .zero)
  .comp iter (.pair Code.id index)

private def listHead (c : Code) : Code := .comp .left (.comp pred c)
private def listTail (c : Code) : Code := .comp .right (.comp pred c)

/-- The scan rejects a list whenever a head fails the numeric element test. -/
private def validList (element : Code) : Code :=
  let flag : Code := .right
  let cursor : Code := .left
  let nextFlag : Code := branch flag .zero (.comp element (listHead cursor))
  let next : Code := .pair (listTail cursor) nextFlag
  .comp .right (firstZero (.pair Code.id (Code.const 1))
    (branch cursor Code.id next) cursor)

private def addressValid : Code := validList (.comp isZero pred)

private def frameValid : Code :=
  branch (parity Code.id) (.comp addressValid (half Code.id)) (Code.const 1)

private def framesValid : Code := validList frameValid

private def controlValid : Code :=
  let payload : Code := half Code.id
  let frames : Code := .comp framesValid (.comp .right payload)
  let address : Code := .comp addressValid (.comp .left payload)
  let first : Code := branch (parity Code.id) address (Code.const 1)
  branch first .zero frames

private def reverseOnto (seed : Nat) : Code :=
  let cursor : Code := .left
  let next : Code := .pair (listTail cursor) (cons (listHead cursor) .right)
  .comp .right (firstZero (.pair Code.id (Code.const seed))
    (branch cursor Code.id next) cursor)

private def appendBit (b : Bool) (address : Code) : Code :=
  .comp (reverseOnto (match b with | false => 1 | true => 3))
    (.comp (reverseOnto 0) address)

private def visit : Code :=
  let payload : Code := half Code.id
  let address : Code := .comp .left payload
  let stack : Code := .comp .right payload
  let alpha : Code := inr (.pair .zero stack)
  let beta : Code := inr (.pair (Code.const 1) stack)
  let fork : Code := inl (.pair (appendBit false address)
    (cons (inl (appendBit true address)) stack))
  let continuations : Code := .pair alpha (.pair beta (.pair fork alpha))
  inl (inl (.pair address continuations))

private def deliver : Code :=
  let payload : Code := half Code.id
  let name : Code := .comp .left payload
  let stack : Code := .comp .right payload
  let frame : Code := listHead stack
  let tail : Code := listTail stack
  let value : Code := half frame
  let stop : Code := inl (inr (inr name))
  let pendingAddress : Code := inr (inl (.pair value (cons (inr name) tail)))
  let combined : Code := .comp .succ (.comp .succ (.pair value name))
  let pendingName : Code := inr (inr (.pair combined tail))
  branch stack stop (branch (parity frame) pendingAddress pendingName)

/-- Encoded instruction on every raw numeric workspace. The
validity checks include both addresses and every address-valued stack frame.
Failure selects numericInitial, whose encoding is zero. -/
def tickCode : Code :=
  let normalized : Code := branch controlValid .zero Code.id
  .comp (branch (.comp isZero (parity Code.id)) deliver visit) normalized

/-- First-return program data. Values are encoded OriginalAction Nat, with
all four read continuations retained in their nested product encoding. -/
def workspaceCode : Code :=
  let test : Code := parity tickCode
  let step : Code := branch test Code.id (half tickCode)
  .comp (half tickCode) (firstZero Code.id step test)

/-- Closed executable program data for the numeric workspace projection of
an OriginalState. Its all-state realization equation is selector_code_correct. -/
def selectorCode : Code :=
  .comp workspaceCode (.comp .left .right)

/-- Execution uses the existing bounded evaluator. No realization record
is asserted by this computational interface. -/
def evaluate (stage : Nat) (s : OriginalState) : Option (OriginalAction Nat) :=
  evalOriginalActionFromCode selectorCode stage (Encodable.encode s)

/-- The existing controller receives the same closed program data. -/
def controller (control : Nat) : NativeSerialMachine.Op Nat Nat :=
  originalNativeControlFromCode selectorCode control



set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open Nat.Partrec.Code
open NativeEffectiveSourceProducer

attribute [local simp] Code.eval.eq_2 Code.eval.eq_6

@[simp] private theorem eval_pair (c d : Code) (n : Nat) :
    Code.eval (.pair c d) n = (Code.eval c n).bind (fun x =>
      (Code.eval d n).map (Nat.pair x)) := by
  simp only [Code.eval, Seq.seq, Part.map_eq_map, Part.bind_eq_bind, Part.bind_map]
@[simp] private theorem eval_zero (n : Nat) : Code.eval .zero n = Part.some 0 := rfl
@[simp] private theorem eval_left (n : Nat) : Code.eval .left n = Part.some n.unpair.1 := rfl
@[simp] private theorem eval_right (n : Nat) : Code.eval .right n = Part.some n.unpair.2 := rfl

private theorem positive_eval (n : Nat) :
    Code.eval positive n = Part.some (if n = 0 then 0 else 1) := by
  have h : (Nat.unpair (Nat.pair 0 n + 1)).1 = (if n=0 then 0 else 1) := by
    cases n with
    | zero => norm_num [Nat.pair, Nat.unpair]
    | succ n =>
      cases n with
      | zero => norm_num [Nat.pair, Nat.unpair]
      | succ n =>
        have hp : Nat.pair 0 (n+2) + 1 = Nat.pair 1 (n+2) := by
          simp only [Nat.pair]
          split_ifs <;> omega
        rw [hp, Nat.unpair_pair]
        simp
  simpa only [positive,Code.eval.eq_6,eval_pair,Code.eval_id,eval_zero,Code.eval.eq_2,eval_left,
    Part.bind_eq_bind,PFun.coe_val,Part.bind_some,Part.map_some] using congrArg Part.some h

private theorem branch_eval (test zeroCase positiveCase : Code) (t z p n : Nat)
    (ht : Code.eval test n = Part.some t)
    (hz : Code.eval zeroCase n = Part.some z)
    (hp : Code.eval positiveCase n = Part.some p) :
    Code.eval (branch test zeroCase positiveCase) n =
      Part.some (if t = 0 then z else p) := by
  simp only [branch, Code.eval.eq_6, eval_pair, Code.eval_id, positive_eval, ht,
    Part.bind_some, Part.map_some, Part.bind_eq_bind]
  split_ifs with h
  · simpa using hz
  · simpa [Code.eval_prec_succ, Code.eval_prec_zero, hz, eval_pair, eval_zero, eval_left, eval_right, Part.bind_eq_bind] using hp

private theorem iterate_eval (initial step : Code) (i f : Nat → Nat)
    (hi : ∀ n, Code.eval initial n = Part.some (i n))
    (hf : ∀ n, Code.eval step n = Part.some (f n)) (n k : Nat) :
    Code.eval (.prec initial (.comp step (.comp .right .right))) (Nat.pair n k) =
      Part.some ((f^[k]) (i n)) := by
  induction k with
  | zero => simp [hi]
  | succ k ih =>
      rw [Code.eval_prec_succ, ih]
      simp [eval_pair, eval_zero, eval_left, eval_right, Part.bind_eq_bind, hf,
        Function.iterate_succ_apply']

private theorem halfParity_eval (n : Nat) :
    Code.eval halfParity n = Part.some (Nat.pair (n/2) (n%2)) := by
  let body : Code :=
    branch (.comp .right (.comp .right .right))
      (.pair (.comp .left (.comp .right .right)) (Code.const 1))
      (.pair (.comp .succ (.comp .left (.comp .right .right))) .zero)
  have h (k : Nat) : Code.eval (.prec (.pair .zero .zero) body) (Nat.pair 0 k) =
      Part.some (Nat.pair (k/2) (k%2)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Code.eval_prec_succ, ih]
      simp only [Part.bind_some, Part.bind_eq_bind]
      have hb := branch_eval (.comp .right (.comp .right .right))
        (.pair (.comp .left (.comp .right .right)) (Code.const 1))
        (.pair (.comp .succ (.comp .left (.comp .right .right))) .zero)
        (k%2) (Nat.pair (k/2) 1) (Nat.pair (k/2+1) 0)
        (Nat.pair 0 (Nat.pair k (Nat.pair (k/2) (k%2))))
        (by simp [eval_pair, eval_zero, eval_left, eval_right, Part.bind_eq_bind])
        (by simp [eval_pair, eval_zero, eval_left, eval_right, Part.bind_eq_bind])
        (by simp [eval_pair, eval_zero, eval_left, eval_right, Part.bind_eq_bind])
      change Code.eval (branch _ _ _) _ = _
      rw [hb]
      split_ifs with hk
      · congr 2 <;> omega
      · congr 2 <;> omega
  simpa [halfParity, body] using h n

private theorem half_eval (c : Code) (n m : Nat)
    (hc : Code.eval c n = Part.some m) :
    Code.eval (half c) n = Part.some (m/2) := by
  simp [half, hc, halfParity_eval, Part.bind_eq_bind]

private theorem parity_eval (c : Code) (n m : Nat)
    (hc : Code.eval c n = Part.some m) :
    Code.eval (parity c) n = Part.some (m%2) := by
  simp [parity, hc, halfParity_eval, Part.bind_eq_bind]

private theorem eval_rfind_zero (c : Code) (a : Nat) :
    Code.eval (.rfind' c) (Nat.pair a 0) =
      Nat.rfind (fun k => (Code.eval c (Nat.pair a k)).map (fun m => decide (m=0))) := by
  simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Nat.add_zero, Part.map_id']
  rfl

private theorem firstZero_mem (initial step test : Code) (i f t : Nat → Nat)
    (hi : ∀ n, Code.eval initial n = Part.some (i n))
    (hf : ∀ n, Code.eval step n = Part.some (f n))
    (ht : ∀ n, Code.eval test n = Part.some (t n)) (n x : Nat) :
    x ∈ Code.eval (firstZero initial step test) n ↔
      ∃ k : Nat, ((t ((f^[k]) (i n)) = 0 ∧
        ∀ j < k, t ((f^[j]) (i n)) ≠ 0) ∧ (f^[k]) (i n) = x) := by
  let iter : Code := .prec initial (.comp step (.comp .right .right))
  have he (k : Nat) : Code.eval iter (Nat.pair n k) = Part.some ((f^[k]) (i n)) :=
    iterate_eval initial step i f hi hf n k
  have hs : Code.eval (.rfind' (.comp test iter)) (Nat.pair n 0) =
      Nat.rfind (fun k => Part.some (decide (t ((f^[k]) (i n)) = 0))) := by
    simp [eval_rfind_zero, he, ht]
  have hresult : Code.eval (firstZero initial step test) n =
      (Nat.rfind (fun k => Part.some (decide (t ((f^[k]) (i n)) = 0)))).bind
        (fun k => Part.some ((f^[k]) (i n))) := by
    unfold firstZero
    change Code.eval (.comp iter (.pair Code.id
      (.comp (.rfind' (.comp test iter)) (.pair Code.id .zero)))) n = _
    simp [hs, he, Part.bind_map]
  rw [hresult]
  simp only [Part.mem_bind_iff, Nat.mem_rfind, Part.mem_some_iff, decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨k,⟨hk,hm⟩,hx⟩
    exact ⟨k,⟨of_decide_eq_true hk.symm,
      fun j hj => of_decide_eq_false (hm hj).symm⟩,hx.symm⟩
  · rintro ⟨k,⟨hk,hm⟩,hx⟩
    exact ⟨k,⟨(decide_eq_true_eq.mpr hk).symm,
      fun {j} hj => (decide_eq_false_iff_not.mpr (hm j hj)).symm⟩,hx.symm⟩

@[simp] private theorem add_eval (n : Nat) :
    Code.eval add n = Part.some (n.unpair.1 + n.unpair.2) := by
  obtain ⟨a,b,h⟩ : ∃ a b, Nat.pair a b = n :=
    ⟨n.unpair.1,n.unpair.2,Nat.pair_unpair n⟩
  subst n
  induction b with
  | zero => simp [add]
  | succ b ih =>
    change Code.eval (.prec Code.id (.comp .succ (.comp .right .right)))
      (Nat.pair a (b+1)) = _
    simp only [add,Nat.unpair_pair] at ih
    rw [Code.eval_prec_succ, ih]
    simp [Part.bind_eq_bind, Nat.add_assoc]

@[simp] private theorem pred_eval (n : Nat) :
    Code.eval pred n = Part.some (n-1) := by
  have h (k : Nat) : Code.eval (.prec .zero (.comp .left .right))
      (Nat.pair 0 k) = Part.some (k-1) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Code.eval_prec_succ, ih]; simp [Part.bind_eq_bind]
  simpa [pred, Part.bind_eq_bind] using h n

@[simp] private theorem isZero_eval (n : Nat) :
    Code.eval isZero n = Part.some (if n=0 then 1 else 0) := by
  simp only [isZero, Code.eval.eq_6, eval_pair, eval_zero, positive_eval,
    Part.bind_some, Part.map_some]
  split_ifs with h
  · simp
  · simp [Code.eval_prec_succ, Part.bind_eq_bind]

private theorem scan_trace (f : Nat → Nat) (u : Nat → Nat → Nat)
    (hf : ∀ (h a : Nat) (l : List Nat),
      f (Nat.pair (Encodable.encode (h::l)) a) =
        Nat.pair (Encodable.encode l) (u h a))
    (l : List Nat) (a : Nat) :
    (f^[l.length]) (Nat.pair (Encodable.encode l) a) =
      Nat.pair 0 (l.foldl (fun a h => u h a) a) ∧
    ∀ j < l.length, ((f^[j]) (Nat.pair (Encodable.encode l) a)).unpair.1 ≠ 0 := by
  induction l generalizing a with
  | nil => simp
  | cons h l ih =>
    obtain ⟨he,hb⟩ := ih (u h a)
    constructor
    · simpa only [List.length_cons, Function.iterate_succ_apply, hf, List.foldl_cons]
        using he
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        simpa only [Function.iterate_succ_apply, hf] using hb j (by simpa using hj)

/-- The finite scan visits the complete raw list, including its last cell. -/
private theorem scan_eval (update : Code) (u : Nat → Nat → Nat)
    (hu : ∀ n, Code.eval update n =
      Part.some (u ((n.unpair.1-1).unpair.1) n.unpair.2))
    (l : List Nat) (a : Nat) :
    Code.eval (firstZero (.pair Code.id (Code.const a))
      (branch .left Code.id (.pair (listTail .left) update)) .left)
      (Encodable.encode l) =
      Part.some (Nat.pair 0 (l.foldl (fun a h => u h a) a)) := by
  let f : Nat → Nat := fun n => if n.unpair.1=0 then n else
    Nat.pair (n.unpair.1-1).unpair.2 (u ((n.unpair.1-1).unpair.1) n.unpair.2)
  have hs (n : Nat) : Code.eval
      (branch .left Code.id (.pair (listTail .left) update)) n = Part.some (f n) := by
    apply branch_eval .left Code.id (.pair (listTail .left) update)
      n.unpair.1 n _ n (eval_left n) (Code.eval_id n)
    simp [listTail, hu, Part.bind_eq_bind]
  have hf (h a : Nat) (l : List Nat) :
      f (Nat.pair (Encodable.encode (h::l)) a) = Nat.pair (Encodable.encode l) (u h a) := by
    simp [f]
  obtain ⟨he,hb⟩ := scan_trace f u hf l a
  apply Part.eq_some_iff.mpr
  apply (firstZero_mem (.pair Code.id (Code.const a))
    (branch .left Code.id (.pair (listTail .left) update)) .left
    (fun n => Nat.pair n a) f (fun n => n.unpair.1)
    (by intro n; simp) hs eval_left _ _).mpr
  exact ⟨l.length,⟨by rw [he]; simp, hb⟩,he⟩

private theorem validList_eval (element : Code) (e : Nat → Nat)
    (he : ∀ n, Code.eval element n = Part.some (e n)) (l : List Nat) :
    Code.eval (validList element) (Encodable.encode l) =
      Part.some (l.foldl (fun a h => if a=0 then 0 else e h) 1) := by
  let update : Code := branch .right .zero (.comp element (listHead .left))
  have hu (n : Nat) : Code.eval update n =
      Part.some (if n.unpair.2=0 then 0 else e ((n.unpair.1-1).unpair.1)) := by
    apply branch_eval .right .zero (.comp element (listHead .left))
      n.unpair.2 0 _ n (eval_right n) (eval_zero n)
    simp [listHead, he, Part.bind_eq_bind]
  have h := scan_eval update (fun h a => if a=0 then 0 else e h) hu l 1
  simpa [validList,update,Part.bind_eq_bind,h] using congrArg
    (fun p => p.bind (fun n => Part.some n.unpair.2)) h

private theorem reverseOnto_eval (seed : Nat) (l : List Nat) :
    Code.eval (reverseOnto seed) (Encodable.encode l) =
      Part.some (l.foldl (fun a h => Nat.pair h a + 1) seed) := by
  let update : Code := cons (listHead .left) .right
  have hu (n : Nat) : Code.eval update n =
      Part.some (Nat.pair ((n.unpair.1-1).unpair.1) n.unpair.2 + 1) := by
    simp [update,cons,listHead,Part.bind_eq_bind]
  have h := scan_eval update (fun h a => Nat.pair h a+1) hu l seed
  simpa [reverseOnto,update,Part.bind_eq_bind,h] using congrArg
    (fun p => p.bind (fun n => Part.some n.unpair.2)) h

private theorem reverseOnto_encoded {α : Type} [Encodable α]
    (l t : List α) :
    Code.eval (reverseOnto (Encodable.encode t)) (Encodable.encode l) =
      Part.some (Encodable.encode (l.reverse ++ t)) := by
  have hm (v : List α) : Encodable.encode (v.map Encodable.encode) = Encodable.encode v := by
    induction v with
    | nil => rfl
    | cons h v ih => simp [ih]
  have hf (v t : List α) : (v.map Encodable.encode).foldl
      (fun a h => Nat.pair h a + 1) (Encodable.encode t) =
      Encodable.encode (v.reverse ++ t) := by
    induction v generalizing t with
    | nil => simp
    | cons h v ih =>
      simpa [List.reverse_cons, List.append_assoc] using ih (h::t)
  have h := reverseOnto_eval (Encodable.encode t) (l.map Encodable.encode)
  simpa only [hm, hf] using h

private theorem appendBit_eval (b : Bool) (address : Code) (n : Nat)
    (l : ActualTreeReadoutAcquisition.Address)
    (h : Code.eval address n = Part.some (Encodable.encode l)) :
    Code.eval (appendBit b address) n = Part.some (Encodable.encode (l ++ [b])) := by
  have hs : (match b with | false => 1 | true => 3) = Encodable.encode [b] := by
    cases b <;> rfl
  simp only [appendBit, Code.eval.eq_6, Part.bind_eq_bind, h, Part.bind_some, hs]
  rw [show 0 = Encodable.encode ([] : List Bool) from rfl,
    reverseOnto_encoded, Part.bind_some, List.append_nil, reverseOnto_encoded,
    List.reverse_reverse]

private def optionFlag {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

private theorem fold_flags (e : Nat → Bool) (l : List Nat) :
    l.foldl (fun a h => if a=0 then 0 else if e h then 1 else 0) 1 =
      if l.all e then 1 else 0 := by
  have hz (v : List Nat) :
      v.foldl (fun a h => if a=0 then 0 else if e h then 1 else 0) 0 = 0 := by
    induction v with
    | nil => rfl
    | cons h v ih => simpa using ih
  induction l with
  | nil => simp
  | cons h l ih =>
    cases he : e h <;> simp [List.foldl_cons, he, hz, ih]

private theorem decode_list_flags {α : Type} [Encodable α] (l : List Nat) :
    (Encodable.decode (α := List α) (Encodable.encode l)).isSome =
      l.all (fun n => (Encodable.decode (α := α) n).isSome) := by
  induction l with
  | nil => simp
  | cons h l ih =>
    simp only [Encodable.encode_list_cons,Encodable.encode_nat,
      Encodable.decode_list_succ,Nat.unpair_pair,List.all_cons]
    cases hd : Encodable.decode (α := α) h <;>
      cases ht : Encodable.decode (α := List α) (Encodable.encode l) <;>
      simp_all [Seq.seq,instMonadOption]

private theorem validList_decode {α : Type} [Encodable α] (element : Code)
    (he : ∀ n, Code.eval element n = Part.some (optionFlag (Encodable.decode (α := α) n)))
    (n : Nat) : Code.eval (validList element) n =
      Part.some (optionFlag (Encodable.decode (α := List α) n)) := by
  obtain ⟨l,_,hl⟩ := Denumerable.denumerable_list_aux (α := Nat) n
  change Encodable.encode l = n at hl
  subst n
  have h := validList_eval element (fun n => optionFlag (Encodable.decode (α := α) n)) he l
  simpa only [optionFlag,fold_flags,decode_list_flags] using h

private theorem addressValid_eval (n : Nat) :
    Code.eval addressValid n =
      Part.some (optionFlag (Encodable.decode (α := List Bool) n)) := by
  apply validList_decode (α := Bool) (.comp isZero pred)
  intro m
  simp only [Code.eval.eq_6,Part.bind_eq_bind,pred_eval,Part.bind_some,isZero_eval]
  by_cases h : m-1=0
  · have hm : m=0 ∨ m=1 := by omega
    rcases hm with rfl | rfl <;> rfl
  · have hm : 2 ≤ m := by omega
    rw [Encodable.decode_ge_two m hm]
    simp [optionFlag,h]

private theorem frameValid_eval (n : Nat) :
    Code.eval frameValid n =
      Part.some (optionFlag (Encodable.decode (α := NumericFrame) n)) := by
  have h := branch_eval (parity Code.id) (.comp addressValid (half Code.id))
    (Code.const 1) (n%2)
    (optionFlag (Encodable.decode (α := List Bool) (n/2))) 1 n
    (parity_eval Code.id n n (Code.eval_id n))
    (by simp [half_eval Code.id n n (Code.eval_id n),addressValid_eval,Part.bind_eq_bind])
    (by simp)
  change Code.eval (branch _ _ _) n = _
  rw [h]
  have hm := Nat.mod_two_of_bodd n
  cases hb : n.bodd <;>
    simp [Encodable.decodeSum,Nat.div2_val,optionFlag,hb,hm,Encodable.decode_nat]

private theorem framesValid_eval (n : Nat) :
    Code.eval framesValid n =
      Part.some (optionFlag (Encodable.decode (α := List NumericFrame) n)) :=
  validList_decode frameValid frameValid_eval n

private theorem controlValid_eval (n : Nat) :
    Code.eval controlValid n =
      Part.some (optionFlag (Encodable.decode (α := NumericControl) n)) := by
  let a := optionFlag (Encodable.decode (α := List Bool) (n/2).unpair.1)
  let k := optionFlag (Encodable.decode (α := List NumericFrame) (n/2).unpair.2)
  have hp := half_eval Code.id n n (Code.eval_id n)
  have ha : Code.eval (.comp addressValid (.comp .left (half Code.id))) n = Part.some a := by
    simp [hp,addressValid_eval,a,Part.bind_eq_bind]
  have hk : Code.eval (.comp framesValid (.comp .right (half Code.id))) n = Part.some k := by
    simp [hp,framesValid_eval,k,Part.bind_eq_bind]
  have hf := branch_eval (parity Code.id)
    (.comp addressValid (.comp .left (half Code.id))) (Code.const 1)
    (n%2) a 1 n (parity_eval Code.id n n (Code.eval_id n)) ha (by simp)
  have h := branch_eval
    (branch (parity Code.id) (.comp addressValid (.comp .left (half Code.id))) (Code.const 1))
    .zero (.comp framesValid (.comp .right (half Code.id)))
    (if n%2=0 then a else 1) 0 k n hf (eval_zero n) hk
  change Code.eval (branch _ _ _) n = _
  rw [h]
  have hm := Nat.mod_two_of_bodd n
  cases hb : n.bodd <;>
    cases hd : Encodable.decode (α := List Bool) (n/2).unpair.1 <;>
    cases ht : Encodable.decode (α := List NumericFrame) (n/2).unpair.2 <;>
    simp [Encodable.decodeSum,Encodable.decode_prod_val,Nat.div2_val,
      optionFlag,hb,hm,a,k,hd,ht]

private theorem decode_list_exact {α : Type} [Encodable α]
    (ha : ∀ (n : Nat) (a : α), Encodable.decode n = some a → Encodable.encode a = n)
    (n : Nat) (l : List α) (hl : Encodable.decode n = some l) :
    Encodable.encode l = n := by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    cases n with
    | zero => have he : l=[] := by simpa using hl.symm
              subst l; rfl
    | succ n =>
      rw [Encodable.decode_list_succ] at hl
      cases hd : Encodable.decode (α := α) n.unpair.1 with
      | none => simp [hd,Seq.seq,instMonadOption] at hl
      | some a =>
        cases ht : Encodable.decode (α := List α) n.unpair.2 with
        | none => simp [hd,ht,Seq.seq,instMonadOption] at hl
        | some t =>
          have he : a::t=l := by simpa [hd,ht,Seq.seq,instMonadOption] using hl
          subst l
          have htail := ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n)) t ht
          simp [ha _ _ hd,htail,Nat.pair_unpair]

private theorem decode_prod_exact {α β : Type} [Encodable α] [Encodable β]
    (ha : ∀ (n : Nat) (a : α), Encodable.decode n = some a → Encodable.encode a = n)
    (hb : ∀ (n : Nat) (b : β), Encodable.decode n = some b → Encodable.encode b = n)
    (n : Nat) (p : α × β) (hp : Encodable.decode n = some p) :
    Encodable.encode p = n := by
  rw [Encodable.decode_prod_val] at hp
  cases hd : Encodable.decode (α := α) n.unpair.1 with
  | none => simp [hd] at hp
  | some a =>
    cases ht : Encodable.decode (α := β) n.unpair.2 with
    | none => simp [hd,ht] at hp
    | some b =>
      have he : (a,b)=p := by simpa [hd,ht] using hp
      subst p
      simp [ha _ _ hd,hb _ _ ht,Nat.pair_unpair]

private theorem decode_sum_exact {α β : Type} [Encodable α] [Encodable β]
    (ha : ∀ (n : Nat) (a : α), Encodable.decode n = some a → Encodable.encode a = n)
    (hb : ∀ (n : Nat) (b : β), Encodable.decode n = some b → Encodable.encode b = n)
    (n : Nat) (p : α ⊕ β) (hp : Encodable.decode n = some p) :
    Encodable.encode p = n := by
  have hm := Nat.mod_two_of_bodd n
  change Encodable.decodeSum n = some p at hp
  cases hd : n.bodd with
  | false =>
    cases ht : Encodable.decode (α := α) (n/2) with
    | none => simp [Encodable.decodeSum,hd,Nat.div2_val,ht] at hp
    | some a =>
      have he : Sum.inl a=p := by simpa [Encodable.decodeSum,hd,Nat.div2_val,ht] using hp
      subst p
      rw [Encodable.encode_inl,ha _ _ ht]
      simp [hd] at hm
      omega
  | true =>
    cases ht : Encodable.decode (α := β) (n/2) with
    | none => simp [Encodable.decodeSum,hd,Nat.div2_val,ht] at hp
    | some b =>
      have he : Sum.inr b=p := by simpa [Encodable.decodeSum,hd,Nat.div2_val,ht] using hp
      subst p
      rw [Encodable.encode_inr,hb _ _ ht]
      simp [hd] at hm
      omega

private theorem numericControl_decode_exact (n : Nat) (c : NumericControl)
    (hc : Encodable.decode n = some c) : Encodable.encode c = n := by
  have hn : ∀ n a : Nat, Encodable.decode n = some a → Encodable.encode a = n := by
    intro n a h; simpa using h.symm
  have hb : ∀ n b, Encodable.decode (α := Bool) n = some b → Encodable.encode b = n := by
    intro n b h
    by_cases h2 : 2 ≤ n
    · simp [Encodable.decode_ge_two n h2] at h
    · have : n=0 ∨ n=1 := by omega
      rcases this with rfl | rfl <;> cases b <;> simpa using h
  have ha := decode_list_exact hb
  have hf := decode_sum_exact ha hn
  have hk := decode_list_exact hf
  exact decode_sum_exact (decode_prod_exact ha hk) (decode_prod_exact hn hk) n c hc

private theorem visit_eval (a : ActualTreeReadoutAcquisition.Address)
    (k : List NumericFrame) :
    Code.eval visit (Encodable.encode (Sum.inl (a,k) : NumericControl)) =
      Part.some (Encodable.encode (Sum.inl (visitAction (a,k)) : OriginalAction Nat ⊕ Nat)) := by
  let n := Encodable.encode (Sum.inl (a,k) : NumericControl)
  have hp : Code.eval (half Code.id) n = Part.some (Nat.pair (Encodable.encode a) (Encodable.encode k)) := by
    simpa [n,Encodable.encodeSum] using half_eval Code.id n n (Code.eval_id n)
  have ha : Code.eval (.comp .left (half Code.id)) n = Part.some (Encodable.encode a) := by
    simp [hp,Part.bind_eq_bind]
  have hk : Code.eval (.comp .right (half Code.id)) n = Part.some (Encodable.encode k) := by
    simp [hp,Part.bind_eq_bind]
  have hfalse := appendBit_eval false (.comp .left (half Code.id)) n a ha
  have htrue := appendBit_eval true (.comp .left (half Code.id)) n a ha
  change Code.eval visit n = _
  simp [visit,inl,inr,double,cons,ha,hk,hfalse,htrue,Part.bind_eq_bind,
    visitAction,visitContinuations,originalRead,Encodable.encodeSum,Encodable.encode_prod_val,
    Encodable.encode_nat,Nat.mul_comm,Nat.mul_assoc,←two_mul] <;> ring

private theorem deliver_eval (v : Nat) (k : List NumericFrame) (tag : Bool) :
    Code.eval deliver (2 * Nat.pair v (Encodable.encode k) + tag.toNat) =
      Part.some (Encodable.encode ((deliverTick (v,k)).map id Encodable.encode :
        OriginalAction Nat ⊕ Nat)) := by
  let n := 2 * Nat.pair v (Encodable.encode k) + tag.toNat
  have hp : Code.eval (half Code.id) n = Part.some (Nat.pair v (Encodable.encode k)) := by
    have h := half_eval Code.id n n (Code.eval_id n)
    cases tag <;> simpa [n,Nat.add_div] using h
  have hv : Code.eval (.comp .left (half Code.id)) n = Part.some v := by
    simp [hp,Part.bind_eq_bind]
  have hk : Code.eval (.comp .right (half Code.id)) n = Part.some (Encodable.encode k) := by
    simp [hp,Part.bind_eq_bind]
  cases k with
  | nil =>
    have ht : Code.eval (.comp .right (half Code.id)) n = Part.some 0 := hk
    have hzero : Code.eval (inl (inr (inr (.comp .left (half Code.id))))) n =
        Part.some (8*v+6) := by
      simp [inl,inr,double,hv,Part.bind_eq_bind,←two_mul,Nat.add_assoc] <;> ring
    -- Both branches are total, even when the stack is empty.
    have hb : ∃ z, Code.eval (branch (parity (listHead (.comp .right (half Code.id))))
        (inr (inl (.pair (half (listHead (.comp .right (half Code.id))))
          (cons (inr (.comp .left (half Code.id))) (listTail (.comp .right (half Code.id)))))))
        (inr (inr (.pair (.comp .succ (.comp .succ (.pair
          (half (listHead (.comp .right (half Code.id)))) (.comp .left (half Code.id)))))
          (listTail (.comp .right (half Code.id))))))) n = Part.some z := by
      have hhead : Code.eval (listHead (.comp .right (half Code.id))) n = Part.some 0 := by
        simp [listHead,hk,Part.bind_eq_bind]
      have htail : Code.eval (listTail (.comp .right (half Code.id))) n = Part.some 0 := by
        simp [listTail,hk,Part.bind_eq_bind]
      have hhalf := half_eval _ n 0 hhead
      have hpar := parity_eval _ n 0 hhead
      refine ⟨4 * Nat.pair 0 (Nat.pair (2*v+1) 0+1)+1,
        branch_eval _ _ _ 0 (4 * Nat.pair 0 (Nat.pair (2*v+1) 0+1)+1)
          (4 * Nat.pair (Nat.pair 0 v+2) 0+3) n hpar ?_ ?_⟩ <;>
        simp [inl,inr,double,cons,hv,hhalf,htail,Part.bind_eq_bind,←two_mul,Nat.add_assoc] <;> ring
    obtain ⟨z,hz⟩ := hb
    change Code.eval (branch _ _ _) n = _
    rw [branch_eval _ _ _ 0 (8*v+6) z n ht hzero hz]
    simp [deliverTick,originalStop,Encodable.encodeSum]
    ring
  | cons f k =>
    have hhead : Code.eval (listHead (.comp .right (half Code.id))) n =
        Part.some (Encodable.encode f) := by
      simp [listHead,hk,Part.bind_eq_bind]
    have htail : Code.eval (listTail (.comp .right (half Code.id))) n =
        Part.some (Encodable.encode k) := by
      simp [listTail,hk,Part.bind_eq_bind]
    have hhalf := half_eval _ n _ hhead
    have hpar := parity_eval _ n _ hhead
    have hs : Code.eval (inl (inr (inr (.comp .left (half Code.id))))) n =
        Part.some (8*v+6) := by
      simp [inl,inr,double,hv,Part.bind_eq_bind,←two_mul,Nat.add_assoc] <;> ring
    have haddr : Code.eval (inr (inl (.pair (half (listHead (.comp .right (half Code.id))))
        (cons (inr (.comp .left (half Code.id))) (listTail (.comp .right (half Code.id))))))) n =
        Part.some (4 * Nat.pair (Encodable.encode f / 2)
          (Nat.pair (2*v+1) (Encodable.encode k)+1)+1) := by
      simp [inl,inr,double,cons,hv,hhalf,htail,Part.bind_eq_bind,←two_mul] <;> ring
    have hname : Code.eval (inr (inr (.pair
        (.comp .succ (.comp .succ (.pair (half (listHead (.comp .right (half Code.id))))
          (.comp .left (half Code.id))))) (listTail (.comp .right (half Code.id)))))) n =
        Part.some (4 * Nat.pair (Nat.pair (Encodable.encode f/2) v+2)
          (Encodable.encode k)+3) := by
      simp [inl,inr,double,cons,hv,hhalf,htail,Part.bind_eq_bind,←two_mul,Nat.add_assoc] <;> ring
    have hb := branch_eval _ _ _ _ _ _ n hpar haddr hname
    change Code.eval (branch _ _ _) n = _
    rw [branch_eval _ _ _ (Encodable.encode (f::k)) (8*v+6) _ n hk hs hb]
    simp only [Encodable.encode_list_cons, Nat.succ_ne_zero, if_false]
    cases f with
    | inl a =>
      simp [deliverTick,Encodable.encodeSum,Encodable.encode_prod_val,Nat.mul_comm] <;> ring
    | inr w =>
      simp [deliverTick,Encodable.encodeSum,Encodable.encode_prod_val,Nat.add_div,Nat.mul_comm]
      ring

private theorem branch_eval_zero (test zeroCase positiveCase : Code) (z n : Nat)
    (ht : Code.eval test n = Part.some 0)
    (hz : Code.eval zeroCase n = Part.some z) :
    Code.eval (branch test zeroCase positiveCase) n = Part.some z := by
  simp [branch,ht,positive_eval,hz,Part.bind_eq_bind]

private theorem instruction_eval (c : NumericControl) :
    Code.eval (branch (.comp isZero (parity Code.id)) deliver visit) (Encodable.encode c) =
      Part.some (Encodable.encode (numericTick (Encodable.encode c))) := by
  simp only [numericTick,Encodable.encodek,Option.getD_some]
  cases c with
  | inl p =>
    rcases p with ⟨a,k⟩
    let n := Encodable.encode (Sum.inl (a,k) : NumericControl)
    have ht : Code.eval (.comp isZero (parity Code.id)) n = Part.some 1 := by
      have h := parity_eval Code.id n n (Code.eval_id n)
      have hm : n%2=0 := by simp [n,Encodable.encodeSum]
      simp [h,hm,Part.bind_eq_bind]
    have hd := deliver_eval (Encodable.encode a) k false
    have hd' : Code.eval deliver n = Part.some
        (Encodable.encode ((deliverTick (Encodable.encode a,k)).map id Encodable.encode :
          OriginalAction Nat ⊕ Nat)) := by
      simpa [n,Encodable.encodeSum] using hd
    have hv := visit_eval a k
    have h := branch_eval _ _ _ 1 _ _ n ht hd' hv
    simpa [n] using h
  | inr p =>
    rcases p with ⟨v,k⟩
    let n := Encodable.encode (Sum.inr (v,k) : NumericControl)
    have ht : Code.eval (.comp isZero (parity Code.id)) n = Part.some 0 := by
      have h := parity_eval Code.id n n (Code.eval_id n)
      have hm : n%2=1 := by simp [n,Encodable.encodeSum]
      simp [h,hm,Part.bind_eq_bind]
    have hd := deliver_eval v k true
    have hd' : Code.eval deliver n = Part.some
        (Encodable.encode ((deliverTick (v,k)).map id Encodable.encode :
          OriginalAction Nat ⊕ Nat)) := by
      simpa [n,Encodable.encodeSum] using hd
    exact branch_eval_zero _ _ _ _ n ht hd'

/-- Every raw workspace uses the complete decoder, including unused suffixes.
Invalid encodings execute the source-independent initial control. -/
theorem tick_code_correct (n : Nat) :
    Code.eval tickCode n = Part.some (Encodable.encode (numericTick n)) := by
  have hn := branch_eval controlValid .zero Code.id
    (optionFlag (Encodable.decode (α := NumericControl) n)) 0 n n
    (controlValid_eval n) (eval_zero n) (Code.eval_id n)
  cases hd : Encodable.decode (α := NumericControl) n with
  | none =>
    have hnorm : Code.eval (branch controlValid .zero Code.id) n = Part.some 0 := by
      simpa [hd,optionFlag] using hn
    change (Code.eval (branch controlValid .zero Code.id) n).bind _ = _
    rw [hnorm,Part.bind_some]
    have hi : Encodable.encode numericInitial = 0 := rfl
    have hz := instruction_eval numericInitial
    rw [hi] at hz
    have hz0 : Encodable.decode (α := NumericControl) 0 = some numericInitial := by
      simpa only [hi] using Encodable.encodek numericInitial
    have ht : numericTick n = numericTick 0 := by
      simp only [numericTick,hd,hz0,Option.getD_none,Option.getD_some]
    simpa only [ht] using hz
  | some c =>
    have hnorm : Code.eval (branch controlValid .zero Code.id) n = Part.some n := by
      simpa [hd,optionFlag] using hn
    change (Code.eval (branch controlValid .zero Code.id) n).bind _ = _
    rw [hnorm,Part.bind_some,← numericControl_decode_exact n c hd]
    simpa [numericTick,Encodable.encodek] using instruction_eval c

private def localNext (n : Nat) : Nat :=
  (numericTick n).elim (fun _ => n) id

private theorem local_first_return_mem (n : Nat) (a : OriginalAction Nat) :
    a ∈ selectWorkspace n ↔
      ∃ k : Nat, numericTick ((localNext^[k]) n) = .inl a ∧
        ∀ j < k, ∃ w : Nat, numericTick ((localNext^[j]) n) = .inr w := by
  let F : Nat → Nat → Part (OriginalAction Nat ⊕ Nat) := fun v k =>
    k.rec (Part.some (.inr v)) (fun _ p =>
      p.bind (fun z => z.elim (fun _ => Part.some z) (fun w => Part.some (numericTick w))))
  have hF (v k : Nat) : F v (k+1) = Part.some (numericTick ((localNext^[k]) v)) := by
    induction k with
    | zero => simp [F]
    | succ k ih =>
      change (F v (k+1)).bind _ = _
      rw [ih, Part.bind_some, Function.iterate_succ_apply']
      cases hz : numericTick ((localNext^[k]) v) <;> simp [localNext, hz]
  have bridge := Partrec.fix_aux (fun v => Part.some (numericTick v)) n a
  change (∃ k : Nat, ((∃ b, Sum.inl b ∈ F n k) ∧
    ∀ {j : Nat}, j < k → ∃ w, Sum.inr w ∈ F n j) ∧ Sum.inl a ∈ F n k) ↔
    a ∈ selectWorkspace n at bridge
  rw [← bridge]
  constructor
  · rintro ⟨k,⟨_,before⟩,ha⟩
    cases k with
    | zero => simp [F] at ha
    | succ k =>
      refine ⟨k,?_,?_⟩
      · simpa only [hF, Part.mem_some_iff, eq_comm] using ha
      · intro j hj
        obtain ⟨w,hw⟩ := before (Nat.succ_lt_succ hj)
        exact ⟨w,by simpa only [hF, Part.mem_some_iff, eq_comm] using hw⟩
  · rintro ⟨k,hk,before⟩
    have ha : Sum.inl a ∈ F n (k+1) := by simpa only [hF,Part.mem_some_iff,eq_comm] using hk
    refine ⟨k+1,⟨⟨a,ha⟩,?_⟩,ha⟩
    intro j hj
    cases j with
    | zero => exact ⟨n,Part.mem_some _⟩
    | succ j =>
      obtain ⟨w,hw⟩ := before j (Nat.lt_of_succ_lt_succ hj)
      exact ⟨w,by simpa only [hF,Part.mem_some_iff,eq_comm] using hw⟩

/-- Exact first-return equality on all natural workspaces, conditional only on the
raw instruction realization law. Equality preserves values and definedness. -/
theorem workspace_code_correct_of_tick
    (hTick : ∀ n : Nat, Code.eval tickCode n = Part.some (Encodable.encode (numericTick n)))
    (n : Nat) :
    Code.eval workspaceCode n = (selectWorkspace n).map Encodable.encode := by
  let test : Code := parity tickCode
  let step : Code := branch test Code.id (half tickCode)
  let tag : Nat → Nat := fun v => (numericTick v).elim (fun _ => 0) (fun _ => 1)
  let out : Nat → Nat := fun v => (numericTick v).elim Encodable.encode id
  have ht (v : Nat) : Code.eval test v = Part.some (tag v) := by
    have h := parity_eval tickCode v _ (hTick v)
    cases hz : numericTick v <;> simpa [test,tag,hz,Encodable.encode,Encodable.encodeSum] using h
  have ho (v : Nat) : Code.eval (half tickCode) v = Part.some (out v) := by
    have h := half_eval tickCode v _ (hTick v)
    cases hz : numericTick v <;> simpa [out,hz,Encodable.encode,Encodable.encodeSum,Nat.add_div] using h
  have hs (v : Nat) : Code.eval step v = Part.some (localNext v) := by
    have h := branch_eval test Code.id (half tickCode) (tag v) v (out v) v
      (ht v) (Code.eval_id v) (ho v)
    cases hz : numericTick v <;> simpa [step,localNext,tag,out,hz] using h
  have hw : Code.eval workspaceCode n =
      (Code.eval (firstZero Code.id step test) n).bind (fun v => Part.some (out v)) := by
    change Code.eval (.comp (half tickCode) (firstZero Code.id step test)) n = _
    simp only [Code.eval.eq_6,Part.bind_eq_bind]
    congr 1
    funext v
    exact ho v
  rw [hw]
  apply Part.ext
  intro x
  simp only [Part.mem_bind_iff,Part.mem_some_iff,Part.mem_map_iff]
  constructor
  · rintro ⟨v,hv,hx⟩
    obtain ⟨k,⟨hk,hbefore⟩,rfl⟩ :=
      (firstZero_mem Code.id step test id localNext tag
        Code.eval_id hs ht n v).mp hv
    cases hz : numericTick ((localNext^[k]) n) with
    | inr w => simp [tag,hz] at hk
    | inl a =>
      refine ⟨a,(local_first_return_mem n a).mpr ⟨k,hz,?_⟩,?_⟩
      · intro j hj
        cases he : numericTick ((localNext^[j]) n) with
        | inr w => exact ⟨w,rfl⟩
        | inl b => exact (hbefore j hj (by simp [tag,he])).elim
      · simpa [out,hz] using hx.symm
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨k,hk,hbefore⟩ := (local_first_return_mem n a).mp ha
    refine ⟨(localNext^[k]) n,?_,by simp [out,hk]⟩
    apply (firstZero_mem Code.id step test id localNext tag
      Code.eval_id hs ht n ((localNext^[k]) n)).mpr
    refine ⟨k,⟨by simp [tag,hk],?_⟩,rfl⟩
    intro j hj
    obtain ⟨w,hw⟩ := hbefore j hj
    simp [tag,hw]

/-- The existing realization interface assembled from the raw instruction law.
The universal tick_code_correct theorem supplies its premise. -/
def realizationOfTick
    (hTick : ∀ n : Nat, Code.eval tickCode n = Part.some (Encodable.encode (numericTick n))) :
    OriginalCodeRealization sourceService where
  code := selectorCode
  realizes s := by
    rcases s with ⟨i,w,e,H⟩
    change Code.eval selectorCode (Nat.pair i (Nat.pair w (Nat.pair e (Encodable.encode H)))) =
      (selectWorkspace w).map Encodable.encode
    simpa only [selectorCode,Code.eval.eq_6,Part.bind_eq_bind,eval_left,eval_right,
      Nat.unpair_pair,Part.bind_some]
      using workspace_code_correct_of_tick hTick w

/-- Exact values and definedness on the full original-state domain. -/
theorem selector_code_correct (s : OriginalState) :
    Code.eval selectorCode (Encodable.encode s) =
      (sourceService.select s).map Encodable.encode :=
  (realizationOfTick tick_code_correct).realizes s

/-- The original evaluator and simulation consume this closed executable program. -/
def realization : OriginalCodeRealization sourceService where
  code := selectorCode
  realizes := selector_code_correct

end D5.S3.Arith.FibonacciAtomic.Observer.NativeSourceSelectorCode
