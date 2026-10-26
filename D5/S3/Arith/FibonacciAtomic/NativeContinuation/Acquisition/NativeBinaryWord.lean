/- GID: D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Physical initial-seam selection and original successful-word output. -/

import D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryTable

/-! A finite controller scans acquired binary rows and prints original windows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord

open LiteralWindowEnd (Window bits first last)
open NativeSuffixAcquisition (Row entry counts table pick reconstruct Allowed modes)
open NativeBinaryRow (Column serialize value)
open Complexity StackProgram StackWords
open StackMachine (Registers set branch)

private def join (p q : Column) : Column := (p.1 || q.1, p.2 || q.2)
private def signals (xs : List Column) : Column := xs.foldr join (false, false)
private def payload (xs : List Column) : List Bool :=
  xs.flatMap (fun p => [true, p.2, true, p.1])

private theorem join_assoc (p q r : Column) : join (join p q) r = join p (join q r) := by
  simp [join, Bool.or_assoc]

private theorem signals_append (xs ys : List Column) :
    signals (xs ++ ys) = join (signals xs) (signals ys) := by
  induction xs with
  | nil => simp [signals, join]
  | cons p xs ih =>
      change join p (signals (xs ++ ys)) = join (join p (signals xs)) (signals ys)
      rw [ih, join_assoc]

private theorem signals_reverse (xs : List Column) : signals xs.reverse = signals xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      rw [List.reverse_cons, signals_append, ih]
      simp [signals, join, Bool.or_comm]

private theorem signals_value (xs : List Column) :
    signals xs = (decide (0 < (value xs).1), decide (0 < (value xs).2)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      obtain ⟨x,y⟩ := p
      simp only [signals, List.foldr_cons]
      change join (x,y) (signals xs) = _
      rw [ih]
      cases x <;> cases y <;>
        simp [join, value, Lax51Proofs.RamToTM.bitsValue, Nat.bit_val] <;> first | rfl | exact ⟨rfl,rfl⟩

private theorem pack_payload (xs : List Column) :
    NativeBinaryTable.pack (serialize xs) = false :: payload xs.reverse := by
  have h (ys : List Column) :
      (serialize ys).reverse.flatMap (fun b => [true,b]) = payload ys.reverse := by
    induction ys with
    | nil => rfl
    | cons p ys ih =>
        change (([p.1,p.2] ++ serialize ys).reverse.flatMap (fun b => [true,b])) = _
        rw [List.reverse_append, List.flatMap_append, ih]
        simp [payload, List.reverse_cons, List.flatMap_append]
  exact congrArg (List.cons false) (h xs)

private def registers (fixed : Registers 8) (src masks word : List Bool) : Registers 8 :=
  fun j => if j = 1 then src else if j = 6 then masks else if j = 8 then word else fixed j

private theorem set1 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 1 bs = registers fixed bs masks word := by
  funext j; fin_cases j <;> simp [StackMachine.set, registers]
private theorem set6 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 6 bs = registers fixed src bs word := by
  funext j; fin_cases j <;> simp [StackMachine.set, registers]
private theorem set8 (fixed : Registers 8) (src masks word bs : List Bool) :
    set (registers fixed src masks word) 8 bs = registers fixed src masks bs := by
  funext j; fin_cases j <;> simp [StackMachine.set, registers]

/-- Every component of the reconstruction controller is finite. -/
inductive Control where
  | start
  | header (s : Bool)
  | scan (initial s : Bool) (p : Column)
  | trueBit (initial s : Bool) (p : Column)
  | falseMark (initial s : Bool) (p : Column)
  | falseBit (initial s : Bool) (p : Column)
  | done (initial s : Bool) (p : Column) (next : Bool)
  | load (s : Bool) (p : Column) (next : Bool) (n : Fin 6) (a : Finset Window)
  | emit (b : Window) (p : Column) (next : Bool) (n : Fin 4)
  | fail
  deriving DecidableEq

/-- The table scan only tests zero; integer counts remain physically stored. -/
def walk : Program 8 Control where
  start := .start
  code q := match q with
    | .start => .pop 8 .fail (.header false) (.header true)
    | .header s => .pop 1 .fail (.scan true s (false,false)) .fail
    | .scan i s p => .pop 1 (.done i s p false) (.done i s p true) (.trueBit i s p)
    | .trueBit i s p => .pop 1 .fail (.falseMark i s p)
        (.falseMark i s (p.1,true))
    | .falseMark i s p => .pop 1 .fail .fail (.falseBit i s p)
    | .falseBit i s p => .pop 1 .fail (.scan i s p) (.scan i s (true,p.2))
    | .done i s p next => if i then
        if (if s then p.2 else p.1) then
          if next then .goto (.scan false s (false,false)) else .halt true
        else .halt false
      else .goto (.load s p next 0 ∅)
    | .load s p next n a => if h : n.val < 5 then
        let b := modes[4 - n.val]'(by simp [modes]; omega)
        let n' : Fin 6 := ⟨n.val+1,by omega⟩
        .pop 6 .fail (.load s p next n' a) (.load s p next n' (insert b a))
      else match pick a (p.1.toNat,p.2.toNat) s with
        | none => .halt false
        | some b => .goto (.emit b p next 0)
    | .emit b p next n => if h : n.val < 3 then
        .push 8 ((bits b)[n.val]'(by cases b <;> simpa [bits] using h))
          (.emit b p next ⟨n.val+1,by omega⟩)
      else .goto (.done true (first b) p next)
    | .fail => .halt false

private abbrev Raw := Fin 10 × Bool × Bool × Bool × Column × NativeBinaryRow.Control
private def windowCode : Window → Fin 5
  | .zero => 0 | .low => 1 | .middle => 2 | .high => 3 | .ends => 4
private def raw (q : Control) : Raw := match q with
  | .start => (0,false,false,false,(false,false),.fail)
  | .header s => (1,s,false,false,(false,false),.fail)
  | .scan i s p => (2,s,i,false,p,.fail)
  | .trueBit i s p => (3,s,i,false,p,.fail)
  | .falseMark i s p => (4,s,i,false,p,.fail)
  | .falseBit i s p => (5,s,i,false,p,.fail)
  | .done i s p next => (6,s,i,next,p,.fail)
  | .load s p next n a => (7,s,false,next,p,.load n a)
  | .emit b p next n => (8,false,false,next,p,
      .scan ∅ (windowCode b,⟨n.val,by have := n.isLt; omega⟩))
  | .fail => (9,false,false,false,(false,false),.fail)
private def unraw (q : Raw) : Control := match q with
  | (tag,s,i,next,p,c) =>
      if tag = 0 then .start else if tag = 1 then .header s
      else if tag = 2 then .scan i s p else if tag = 3 then .trueBit i s p
      else if tag = 4 then .falseMark i s p else if tag = 5 then .falseBit i s p
      else if tag = 6 then .done i s p next
      else if tag = 7 then match c with | .load n a => .load s p next n a | _ => .fail
      else if tag = 8 then match c with
        | .scan _ (b,n) => .emit (modes[b.val]'(by simp [modes]))
            p next ⟨n.val % 4,Nat.mod_lt _ (by decide)⟩
        | _ => .fail
      else .fail
private theorem unraw_raw (q : Control) : unraw (raw q) = q := by
  cases q <;> simp [raw,unraw]
  case emit b p next n =>
    have hn := n.isLt
    cases b <;> simp [windowCode,modes,Nat.mod_eq_of_lt hn]
private def rawEncoding : Encoding Raw :=
  (Encoding.fin 9).prod (Encoding.bool.prod (Encoding.bool.prod
    (Encoding.bool.prod ((Encoding.bool.prod Encoding.bool).prod NativeBinaryRow.controlEncoding))))

/-- The source row-controller encoding supplies the finite mask and carry fields. -/
def walkEncoding : Encoding Control where
  states := rawEncoding.states
  encode q := rawEncoding.encode (raw q)
  decode q := unraw (rawEncoding.decode q)
  decode_encode q := by rw [rawEncoding.decode_encode,unraw_raw]

private theorem exec_scan (i s : Bool) (p : Column) (xs : List Column)
    (next : Bool) (rest masks word : List Bool) (fixed : Registers 8)
    (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.done i s (join p (signals xs)) next)
      (registers fixed (if next then rest else []) masks word) t out) :
    Exec walk (.scan i s p)
      (registers fixed (payload xs ++ if next then false :: rest else []) masks word)
      (4 * xs.length + 1 + t) out := by
  induction xs generalizing p with
  | nil =>
      have he : join p (signals []) = p := by simp [join, signals]
      rw [he] at h
      have hh : StackProgram.step walk (.scan i s p)
          (registers fixed (if next then false :: rest else []) masks word) =
          .inr (.done i s p next, registers fixed (if next then rest else []) masks word) := by
        cases next <;> simp [StackProgram.step,walk,registers,branch,set1]
      simpa [payload, Nat.add_comm] using Exec.next hh h
  | cons c xs ih =>
      obtain ⟨x,y⟩ := c
      have ht := ih (join p (x,y)) (by
        simpa only [signals, List.foldr_cons, join_assoc] using h)
      have hh := Exec.next (p := walk)
        (q := .scan i s p) (q' := .trueBit i s p)
        (r := registers fixed (payload ((x,y)::xs) ++ if next then false::rest else []) masks word)
        (r' := registers fixed (y :: true :: x :: (payload xs ++ if next then false::rest else [])) masks word)
        (by simp [StackProgram.step,walk,payload,registers,branch,set1])
        (Exec.next (q' := .falseMark i s (p.1,p.2 || y))
          (r' := registers fixed (true :: x :: (payload xs ++ if next then false::rest else [])) masks word)
          (by cases y <;> simp [StackProgram.step,walk,registers,branch,set1])
          (Exec.next (q' := .falseBit i s (p.1,p.2 || y))
            (r' := registers fixed (x :: (payload xs ++ if next then false::rest else [])) masks word)
            (by simp [StackProgram.step,walk,registers,branch,set1])
            (Exec.next (by cases x <;> simp [StackProgram.step,walk,registers,branch,set1,join]) ht)))
      convert hh using 1 <;> simp only [List.length_cons] <;> omega

private def more (as : List (Finset Window)) : Bool := !as.isEmpty
private def tailPayload (B : Finset Bool) : List (Finset Window) → List Bool
  | [] => []
  | _ :: as => (NativeBinaryTable.records B as).tail
private def permissions (as : List (Finset Window)) : List Bool :=
  as.flatMap (fun a => (NativeBinaryTable.mask a).reverse)

/-- Original low, middle, high printed bits, with all window positions retained. -/
def printed (w : List Window) : List Bool := w.flatMap bits

private theorem child_stream (B : Finset Bool) (as : List (Finset Window)) :
    (NativeBinaryTable.records B as).tail =
      payload (NativeBinaryTable.row B as).reverse ++
        if more as then false :: tailPayload B as else [] := by
  cases as with
  | nil => simp [NativeBinaryTable.records,NativeBinaryTable.rows,pack_payload,more,tailPayload]
  | cons a as =>
      change (NativeBinaryTable.pack (serialize (NativeBinaryTable.row B (a::as))) ++
        NativeBinaryTable.records B as).tail = _
      rw [pack_payload]
      simp only [List.cons_append,List.tail_cons,more,List.isEmpty_cons,Bool.not_false,
        ↓reduceIte,tailPayload]
      congr 1
      cases as <;> simp [NativeBinaryTable.records,NativeBinaryTable.rows,pack_payload]

private theorem pick_signals (a : Finset Window) (xs : List Column) (s : Bool) :
    pick a ((signals xs).1.toNat,(signals xs).2.toNat) s = pick a (value xs) s := by
  unfold pick
  congr 1
  funext b
  congr 1
  congr 1
  rw [signals_value]
  cases h : first b <;> simp [entry,h,Bool.toNat] <;> split_ifs <;> simp_all


private theorem exec_load_next (s : Bool) (p : Column) (next : Bool)
    (n : ℕ) (hn : n < 5) (a : Finset Window) (v : Bool)
    (src masks word : List Bool) (fixed : Registers 8) (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.load s p next ⟨n+1,by omega⟩
        (NativeBinaryRow.insertBit a (modes[4-n]'(by simp [modes];omega)) v))
      (registers fixed src masks word) t out) :
    Exec walk (.load s p next ⟨n,by omega⟩ a)
      (registers fixed src (v::masks) word) (t+1) out := by
  apply Exec.next (rest := h)
  cases v <;> simp [StackProgram.step,walk,hn,NativeBinaryRow.insertBit,registers,branch,set6]

private theorem exec_load (s : Bool) (p : Column) (next : Bool) (a : Finset Window)
    (src masks word : List Bool) (fixed : Registers 8) (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.load s p next 5 a) (registers fixed src masks word) t out) :
    Exec walk (.load s p next 0 ∅)
      (registers fixed src ((NativeBinaryTable.mask a).reverse ++ masks) word) (t+5) out := by
  let v0 := decide (Window.ends ∈ a)
  let v1 := decide (Window.high ∈ a)
  let v2 := decide (Window.middle ∈ a)
  let v3 := decide (Window.low ∈ a)
  let v4 := decide (Window.zero ∈ a)
  let a1 := NativeBinaryRow.insertBit ∅ Window.ends v0
  let a2 := NativeBinaryRow.insertBit a1 Window.high v1
  let a3 := NativeBinaryRow.insertBit a2 Window.middle v2
  let a4 := NativeBinaryRow.insertBit a3 Window.low v3
  let a5 := NativeBinaryRow.insertBit a4 Window.zero v4
  have ha : a5 = a := by
    ext b; cases b <;>
      simp [a5,a4,a3,a2,a1,v0,v1,v2,v3,v4,NativeBinaryRow.insertBit] <;>
      split_ifs <;> simp_all
  have h5 : Exec walk (.load s p next 5 a5) (registers fixed src masks word) t out := ha ▸ h
  have h4 := exec_load_next s p next 4 (by decide) a4 v4 _ _ _ _ _ _ h5
  have h3 := exec_load_next s p next 3 (by decide) a3 v3 _ _ _ _ _ _ h4
  have h2 := exec_load_next s p next 2 (by decide) a2 v2 _ _ _ _ _ _ h3
  have h1 := exec_load_next s p next 1 (by decide) a1 v1 _ _ _ _ _ _ h2
  have h0 := exec_load_next s p next 0 (by decide) ∅ v0 _ _ _ _ _ _ h1
  simpa [NativeBinaryTable.mask,modes,v0,v1,v2,v3,v4] using h0

private theorem exec_emit (b : Window) (p : Column) (next : Bool)
    (src masks word : List Bool) (fixed : Registers 8) (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.done true (first b) p next)
      (registers fixed src masks ((bits b).reverse ++ word)) t out) :
    Exec walk (.emit b p next 0) (registers fixed src masks word) (t+4) out := by
  have hlen : (bits b).length = 3 := by cases b <;> rfl
  let lo := (bits b)[0]'(by omega)
  let mi := (bits b)[1]'(by omega)
  let hi := (bits b)[2]'(by omega)
  have hw : hi::mi::lo::word = (bits b).reverse ++ word := by cases b <;> rfl
  apply Exec.next (q' := .emit b p next 1)
    (r' := registers fixed src masks (lo::word))
  · simp [StackProgram.step,walk,registers,set8,lo]
  apply Exec.next (q' := .emit b p next 2)
    (r' := registers fixed src masks (mi::lo::word))
  · simp [StackProgram.step,walk,registers,set8,mi]
  apply Exec.next (q' := .emit b p next 3)
    (r' := registers fixed src masks (hi::mi::lo::word))
  · simp [StackProgram.step,walk,registers,set8,hi]
  rw [hw]
  exact Exec.next (by simp [StackProgram.step,walk]) h

private theorem reconstruct_cons (B : Finset Bool) (a : Finset Window)
    (as : List (Finset Window)) (s : Bool) :
    reconstruct B (a::as) (table B (a::as)) s = (do
      let b ← pick a (counts B as) s
      let w ← reconstruct B as (table B as) (first b)
      pure (b::w)) := by cases as <;> rfl

private theorem reconstruction_signal (B : Finset Bool) (as : List (Finset Window))
    (s : Bool) (w : List Window) (hw : reconstruct B as (table B as) s = some w) :
    (if s then (signals (NativeBinaryTable.row B as)).2
      else (signals (NativeBinaryTable.row B as)).1) = true := by
  have hz := ((NativeSuffixAcquisition.native_suffix_acquisition as.length as.get B).2.2 s).1
  simp only [List.ofFn_get,NativeSuffixAcquisition.acquire] at hz
  have hp : 0 < entry (counts B as) s := by
    apply Nat.pos_of_ne_zero
    intro he
    have hn := hz.mpr he
    rw [hw] at hn
    contradiction
  rw [signals_value,NativeBinaryTable.row_value]
  cases s <;> simpa [entry] using hp

private theorem exec_reconstruct (B : Finset Bool) (as : List (Finset Window))
    (s : Bool) (w : List Window) (hw : reconstruct B as (table B as) s = some w)
    (masks word : List Bool) (fixed : Registers 8) :
    ∃ t, t + (NativeBinaryTable.pack (serialize (NativeBinaryTable.row B as))).length ≤
        (NativeBinaryTable.records B as).length + 12 * as.length + 1 ∧
      Exec walk (.done true s (signals (NativeBinaryTable.row B as)) (more as))
        (registers fixed (tailPayload B as) (permissions as ++ masks) word) t
        (true,registers fixed [] masks ((printed w).reverse ++ word)) := by
  induction as generalizing s w word with
  | nil =>
      have hp := reconstruction_signal B [] s w hw
      have hw0 : w = [] := by
        simp only [reconstruct] at hw
        split_ifs at hw <;> simp_all
      subst w
      refine ⟨1,?_,?_⟩
      · simp [NativeBinaryTable.records,NativeBinaryTable.rows,Nat.add_comm]
      · apply Exec.halt
        cases s <;> simp at hp <;>
          simp [StackProgram.step,walk,more,hp,tailPayload,permissions,printed]
  | cons a as ih =>
      have hp := reconstruction_signal B (a::as) s w hw
      rw [reconstruct_cons] at hw
      cases hb : pick a (counts B as) s with
      | none => simp [hb] at hw
      | some b =>
          cases ht : reconstruct B as (table B as) (first b) with
          | none => simp [hb,ht] at hw
          | some v =>
              have hw0 : b::v = w := by simpa [hb,ht] using hw
              subst w
              obtain ⟨t,hbound,he⟩ := ih (first b) v ht ((bits b).reverse ++ word)
              have hrest : (if more as then tailPayload B as else []) = tailPayload B as := by
                cases as <;> rfl
              have hsignal : join (false,false) (signals (NativeBinaryTable.row B as).reverse) =
                  signals (NativeBinaryTable.row B as) := by rw [signals_reverse]; simp [join]
              have hchoose : pick a
                  ((signals (NativeBinaryTable.row B as)).1.toNat,
                   (signals (NativeBinaryTable.row B as)).2.toNat) s = some b := by
                rw [pick_signals,NativeBinaryTable.row_value]
                exact hb
              have hemit := exec_emit b (signals (NativeBinaryTable.row B as)) (more as)
                (tailPayload B as) (permissions as ++ masks) word fixed t _ he
              have hselect : Exec walk (.load s (signals (NativeBinaryTable.row B as)) (more as) 5 a)
                  (registers fixed (tailPayload B as) (permissions as ++ masks) word) (t+5)
                  (true,registers fixed [] masks ((printed v).reverse ++ ((bits b).reverse ++ word))) :=
                .next (by simp [StackProgram.step,walk,hchoose]) hemit
              have hload := exec_load s (signals (NativeBinaryTable.row B as)) (more as) a
                (tailPayload B as) (permissions as ++ masks) word fixed (t+5) _ hselect
              have hdone : Exec walk (.done false s (signals (NativeBinaryTable.row B as)) (more as))
                  (registers fixed (tailPayload B as) (permissions (a::as) ++ masks) word) (t+11)
                  (true,registers fixed [] masks ((printed v).reverse ++ ((bits b).reverse ++ word))) := by
                apply Exec.next (q' := .load s (signals (NativeBinaryTable.row B as)) (more as) 0 ∅)
                  (r' := registers fixed (tailPayload B as) (permissions (a::as) ++ masks) word)
                · simp [StackProgram.step,walk]
                · simpa [permissions,List.append_assoc] using hload
              have hscan := exec_scan false s (false,false) (NativeBinaryTable.row B as).reverse
                (more as) (tailPayload B as) (permissions (a::as) ++ masks) word fixed (t+11) _
                (by simpa only [hsignal,hrest] using hdone)
              have hscan' : Exec walk (.scan false s (false,false))
                  (registers fixed (tailPayload B (a::as)) (permissions (a::as) ++ masks) word)
                  (4 * (NativeBinaryTable.row B as).length + 1 + (t+11))
                  (true,registers fixed [] masks ((printed v).reverse ++ ((bits b).reverse ++ word))) := by
                have hh : tailPayload B (a::as) = payload (NativeBinaryTable.row B as).reverse ++
                    if more as then false :: tailPayload B as else [] := child_stream B as
                rw [hh]
                simpa only [List.length_reverse] using hscan
              have hstart : Exec walk (.done true s (signals (NativeBinaryTable.row B (a::as))) (more (a::as)))
                  (registers fixed (tailPayload B (a::as)) (permissions (a::as) ++ masks) word)
                  (t + 4 * (NativeBinaryTable.row B as).length + 13)
                  (true,registers fixed [] masks ((printed (b::v)).reverse ++ word)) := by
                have hh := Exec.next (p := walk)
                  (q := .done true s (signals (NativeBinaryTable.row B (a::as))) (more (a::as)))
                  (r := registers fixed (tailPayload B (a::as)) (permissions (a::as) ++ masks) word)
                  (by cases s <;> simp at hp <;> simp [StackProgram.step,walk,more,hp]) hscan'
                convert hh using 1
                · omega
                · simp [printed,List.reverse_append,List.append_assoc]
              refine ⟨_,?_,hstart⟩
              have hpack : (NativeBinaryTable.pack (serialize (NativeBinaryTable.row B as))).length =
                  1 + 4 * (NativeBinaryTable.row B as).length := by
                rw [NativeBinaryTable.pack_length,NativeBinaryRow.serialize_length]; ring
              have hrecords : (NativeBinaryTable.records B (a::as)).length =
                  (NativeBinaryTable.pack (serialize (NativeBinaryTable.row B (a::as)))).length +
                  (NativeBinaryTable.records B as).length := by
                change (NativeBinaryTable.pack _ ++ NativeBinaryTable.records B as).length = _
                exact List.length_append
              rw [hrecords,List.length_cons]
              omega

/-- A real seam bit precedes the terminal and permission input. -/
def input (B : Finset Bool) (as : List (Finset Window)) (s : Bool) : List Bool :=
  s :: NativeBinaryTable.input B as

def readSeam : Program 8 (Fin 4 × Bool) where
  start := (0,false)
  code q := if q.1 = 0 then .pop 0 (3,false) (1,false) (1,true)
    else if q.1 = 1 then .push 8 q.2 (2,q.2)
    else .halt (q.1 == 2)

def prepare := seq (clear (k := 8) 5)
  (seq (clear 6) (seq (copy 0 1 5) (transfer 7 6)))
private def prepareEncoding := Encoding.bool.sum
  (Encoding.bool.sum (copyMapEncoding.sum (Encoding.fin 3)))

/-- Output both the retained table and the selected status and word. -/
def finish (b : Bool) := seq (transfer (k := 8) 0 5)
  (seq (transfer 8 0) (seq (push 0 b) (seq (transfer 5 0) (stop 8 b))))
private def finishEncoding := (Encoding.fin 3).sum
  ((Encoding.fin 3).sum (Encoding.bool.sum ((Encoding.fin 3).sum Encoding.unit)))

/-- One fixed controller performs every input, count, branch and output operation. -/
def program := seq readSeam (seq (copy (k := 8) 0 7 5)
  (seq (StackFrame.lift StackFrame.includeRegister NativeBinaryTable.program)
    (seq prepare (StackControl.choose walk (finish true) (finish false)))))

def encoding := ((Encoding.fin 3).prod Encoding.bool).sum
  (copyMapEncoding.sum (NativeBinaryTable.encoding.sum
    (prepareEncoding.sum (StackControl.chooseEncoding walkEncoding finishEncoding))))
def stackMachine := StackProgram.compile program encoding
def binaryMachine := StackCompile.compile stackMachine

/-- Table bits followed by a status bit and the original low-to-high window codes. -/
def output (B : Finset Bool) (as : List (Finset Window)) (s : Bool) : List Bool :=
  let answer := reconstruct B as (table B as) s
  NativeBinaryTable.records B as ++ answer.isSome :: (answer.toList.flatMap printed)

private theorem exec_finish (b : Bool) (r : Registers 8) (h5 : r 5 = []) :
    ∃ out, Exec (finish b) (finish b).start r
      (4 * (r 0).length + 2 * (r 8).length + 9) (b,out) ∧
      out 0 = r 0 ++ b :: (r 8).reverse := by
  let r1 := set (set r 0 []) 5 ((r 0).reverse ++ r 5)
  let r2 := set (set r1 8 []) 0 ((r1 8).reverse ++ r1 0)
  let r3 := set r2 0 (b :: r2 0)
  let r4 := set (set r3 5 []) 0 ((r3 5).reverse ++ r3 0)
  have h0 := exec_transfer (k := 8) 0 5 (by decide) r
  have h1 := exec_transfer (k := 8) 8 0 (by decide) r1
  have h2 := exec_push (k := 8) 0 b r2
  have h3 := exec_transfer (k := 8) 5 0 (by decide) r3
  have h4 := exec_stop 8 b r4
  have hh := exec_seq _ _ h0 (exec_seq _ _ h1 (exec_seq _ _ h2 (exec_seq _ _ h3 h4)))
  have hc : (2 * (r 0).length + 2) + ((2 * (r1 8).length + 2) +
      (2 + ((2 * (r3 5).length + 2) + 1))) =
      4 * (r 0).length + 2 * (r 8).length + 9 := by
    simp [r1,r2,r3,StackMachine.set,h5]
    omega
  rw [hc] at hh
  refine ⟨r4,hh,?_⟩
  simp [r4,r3,r2,r1,StackMachine.set,h5]

private theorem exec_prepare (r : Registers 8) (bound : ℕ)
    (hb : ∀ j, (r j).length ≤ bound) :
    ∃ t out, t ≤ 3 * bound + 5 * (r 0).length + 2 * (r 7).length + 12 ∧
      Exec prepare prepare.start r t (true,out) ∧
      out 0 = r 0 ∧ out 1 = r 0 ∧ out 5 = [] ∧ out 6 = (r 7).reverse ∧
      out 7 = [] ∧ out 8 = r 8 := by
  let r1 := set r 5 []
  let r2 := set r1 6 []
  let r3 := set r2 1 (r2 0)
  let r4 := set (set r3 7 []) 6 ((r3 7).reverse ++ r3 6)
  have h0 := exec_clear (k := 8) 5 r
  have h1 := exec_clear (k := 8) 6 r1
  have h2 := exec_copy (k := 8) 0 1 5 (by decide) (by decide) (by decide) r2
    (by simp [r2,r1,StackMachine.set])
  have h3 := exec_transfer (k := 8) 7 6 (by decide) r3
  have hh := exec_seq _ _ h0 (exec_seq _ _ h1 (exec_seq _ _ h2 h3))
  refine ⟨_,r4,?_,hh,?_,?_,?_,?_,?_,?_⟩
  · have h5 := hb 5
    have h6 := hb 6
    have h1 := hb 1
    change ((r 5).length+2) + (((r1 6).length+2) +
      ((r2 1).length + 5*(r2 0).length+6 + (2*(r3 7).length+2))) ≤ _
    simp [r3,r2,r1,StackMachine.set]
    omega
  all_goals simp [r4,r3,r2,r1,StackMachine.set]

private theorem exec_initial_scan (B : Finset Bool) (as : List (Finset Window)) (s : Bool)
    (masks : List Bool) (fixed : Registers 8) (t : ℕ) (out : Bool × Registers 8)
    (h : Exec walk (.done true s (signals (NativeBinaryTable.row B as)) (more as))
      (registers fixed (tailPayload B as) masks []) t out) :
    Exec walk walk.start (registers fixed (NativeBinaryTable.records B as) masks [s])
      (4 * (NativeBinaryTable.row B as).length + 3 + t) out := by
  have hrest : (if more as then tailPayload B as else []) = tailPayload B as := by
    cases as <;> rfl
  have hsignal : join (false,false) (signals (NativeBinaryTable.row B as).reverse) =
      signals (NativeBinaryTable.row B as) := by rw [signals_reverse]; simp [join]
  have hs := exec_scan true s (false,false) (NativeBinaryTable.row B as).reverse
    (more as) (tailPayload B as) masks [] fixed t out (by simpa only [hrest,hsignal] using h)
  have hs' : Exec walk (.scan true s (false,false))
      (registers fixed (NativeBinaryTable.records B as).tail masks [])
      (4 * (NativeBinaryTable.row B as).length + 1 + t) out := by
    simpa only [child_stream,List.length_reverse] using hs
  have hheader : NativeBinaryTable.records B as = false :: (NativeBinaryTable.records B as).tail := by
    cases as <;> simp [NativeBinaryTable.records,NativeBinaryTable.rows,pack_payload]
  have hh : Exec walk (.header s) (registers fixed (NativeBinaryTable.records B as) masks [])
      (4 * (NativeBinaryTable.row B as).length + 2 + t) out := by
    apply Exec.next (q' := .scan true s (false,false))
      (r' := registers fixed (NativeBinaryTable.records B as).tail masks [])
    · rw [hheader]
      simp [StackProgram.step,walk,registers,branch,set1]
    · convert hs' using 1 <;> omega
  apply Exec.next (q' := .header s)
    (r' := registers fixed (NativeBinaryTable.records B as) masks [])
  · cases s <;> simp [StackProgram.step,walk,registers,branch,set8]
  · convert hh using 1 <;> omega

private theorem exec_answer (B : Finset Bool) (as : List (Finset Window)) (s : Bool)
    (masks : List Bool) (fixed : Registers 8) :
    let answer := reconstruct B as (table B as) s
    ∃ t out, t ≤ (NativeBinaryTable.records B as).length + 12 * as.length + 4 ∧
      Exec walk walk.start
        (registers fixed (NativeBinaryTable.records B as) (permissions as ++ masks) [s]) t
        (answer.isSome,out) ∧ out 0 = fixed 0 ∧ out 5 = fixed 5 ∧
        out 8 = (answer.toList.flatMap printed).reverse := by
  dsimp only
  have hpack : (NativeBinaryTable.pack (serialize (NativeBinaryTable.row B as))).length =
      1 + 4 * (NativeBinaryTable.row B as).length := by
    rw [NativeBinaryTable.pack_length,NativeBinaryRow.serialize_length]; ring
  cases hw : reconstruct B as (table B as) s with
  | none =>
      have hz := ((NativeSuffixAcquisition.native_suffix_acquisition as.length as.get B).2.2 s).1
      simp only [List.ofFn_get,NativeSuffixAcquisition.acquire] at hz
      have hc := hz.mp hw
      have hp : (if s then (signals (NativeBinaryTable.row B as)).2
          else (signals (NativeBinaryTable.row B as)).1) = false := by
        rw [signals_value,NativeBinaryTable.row_value]
        cases s <;> simp [entry] at hc <;> simp [hc]
      have he : Exec walk (.done true s (signals (NativeBinaryTable.row B as)) (more as))
          (registers fixed (tailPayload B as) (permissions as ++ masks) []) 1
          (false,registers fixed (tailPayload B as) (permissions as ++ masks) []) := by
        apply Exec.halt
        cases s <;> simp at hp <;> simp [StackProgram.step,walk,hp]
      have hh := exec_initial_scan B as s (permissions as ++ masks) fixed 1 _ he
      refine ⟨_,_,?_,hh,by simp [registers],by simp [registers],by simp [registers]⟩
      have ht : ∃ tail, NativeBinaryTable.records B as =
          NativeBinaryTable.pack (serialize (NativeBinaryTable.row B as)) ++ tail := by
        cases as with
        | nil => exact ⟨[],rfl⟩
        | cons a as => exact ⟨NativeBinaryTable.records B as,rfl⟩
      obtain ⟨tail,ht⟩ := ht
      rw [ht,List.length_append,hpack]
      omega
  | some w =>
      obtain ⟨t,hb,he⟩ := exec_reconstruct B as s w hw masks [] fixed
      have hh := exec_initial_scan B as s (permissions as ++ masks) fixed t _ he
      refine ⟨_,_,?_,hh,by simp [registers],by simp [registers],by simp [registers]⟩
      omega

end D5.S3.Arith.FibonacciAtomic.NativeContinuation.Acquisition.NativeBinaryWord
