/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact bounded control fields and their paid native word realization. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderRows
import D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord
import Mathlib.Data.Nat.Log

/-! The finite table is selected only by its installed constants and bank bits.
Sources and traversal prefixes occur only in its correctness relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl

open NativeBoundedPreorderRows
open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord (Bank Table Flag Opcode RawReply
  replyFlag rawReply actualObservation sourceProgram Execution ready)
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution (Instruction Run)

/-- The seven mode codes use the installation order. Code seven is unused. -/
def modeCode : Mode → Nat
  | .value => 0 | .guard => 1 | .poll => 2 | .update => 3
  | .halt0 => 4 | .halt1 => 5 | .error => 6

/-- Binary fields all use least-significant-bit-first order. -/
def fieldBits (w n : Nat) : List Bool :=
  List.ofFn (fun i : Fin w => (BitVec.ofNat w n).getLsbD i.val)

/-- The exact ordinary-bit width before physical zero interleaving. -/
def bankWidth (h e : Nat) : Nat := h + 3 + Nat.clog 2 h + 2 * Nat.clog 2 (h + 1) + e

/-- Candidate indices use the installed range, including zero-width direct indices. -/
def indexWidth (h T : Nat) (active : Bool) : Nat :=
  if active && decide (0 < T) then Nat.clog 2 (2 * h) else Nat.clog 2 (T + 1)

/-- The path, length, branch count, leaf count, candidate, parity and mode fields. -/
def controlBits (h e : Nat) (z : Control) : List Bool :=
  z.p.rightpad (h - 1) false ++ fieldBits (Nat.clog 2 h) z.s ++
    fieldBits (Nat.clog 2 (h + 1)) z.b ++ fieldBits (Nat.clog 2 (h + 1)) z.l ++
    fieldBits e z.j ++ [z.a] ++ fieldBits 3 (modeCode z.mu)

/-- Every bank position is one ordinary bit of the displayed field list. -/
def encode (h e : Nat) (z : Control) : Bank (bankWidth h e) :=
  Finset.univ.filter (fun i => ((controlBits h e z)[i.val]?).getD false = true)

private theorem bounded_fields (P : Parameters) (positive : 0 < P.h) (z : Control)
    (valid : Valid P z) :
    z.s = z.p.length ∧ z.p.length < P.h ∧ z.b < P.h ∧ z.l ≤ P.h ∧ z.j ≤ P.last := by
  have normal (hm : z.mu = .value ∨ z.mu = .guard) :
      z.s = z.p.length ∧ z.p.length < P.h ∧ z.b < P.h ∧ z.l ≤ P.h ∧ z.j ≤ P.last := by
    rcases hm with hm | hm
    all_goals
      simp only [Valid, hm] at valid
      obtain ⟨hs, depth, hb, hl, hj, _⟩ := valid
      exact ⟨hs, by omega, hb, hl, hj⟩
  cases hm : z.mu with
  | value => exact normal (Or.inl hm)
  | guard => exact normal (Or.inr hm)
  | poll | update =>
    have eq : z = canonical z.mu := by
      simp only [Valid, hm] at valid
      simpa only [hm] using valid.2
    rw [eq]
    simp [canonical, positive]
  | halt0 | halt1 | error =>
    have eq : z = canonical z.mu := by simpa only [Valid, hm] using valid
    rw [eq]
    simp [canonical, positive]

private theorem bits_length (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (z : Control) (valid : Valid P z) :
    (controlBits P.h e z).length = bankWidth P.h e := by
  have bounds := bounded_fields P positive z valid
  have path : z.p.length ≤ P.h - 1 := by omega
  simp only [controlBits, List.length_append, List.length_rightpad, Nat.max_eq_left path,
    fieldBits, List.length_ofFn, List.length_singleton, bankWidth]
  omega

private theorem field_injective (w x y : Nat) (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (eq : fieldBits w x = fieldBits w y) : x = y := by
  have pointwise := List.ofFn_injective eq
  have vec : BitVec.ofNat w x = BitVec.ofNat w y :=
    BitVec.eq_of_getLsbD_eq (fun i hi => congrFun pointwise ⟨i, hi⟩)
  have number := congrArg BitVec.toNat vec
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using number

private theorem encoding_injective (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (x y : Control) (vx : Valid P x) (vy : Valid P y)
    (eq : encode P.h e x = encode P.h e y) : x = y := by
  obtain ⟨sx, px, bx, lx, jx⟩ := bounded_fields P positive x vx
  obtain ⟨sy, py, by', ly, jy⟩ := bounded_fields P positive y vy
  have lenx := bits_length P e positive x vx
  have leny := bits_length P e positive y vy
  have bits : controlBits P.h e x = controlBits P.h e y := by
    apply List.ext_getElem (lenx.trans leny.symm)
    intro i hi hj
    have ik : i < bankWidth P.h e := by omega
    apply Bool.eq_iff_iff.mpr
    have member := (Finset.ext_iff.mp eq) ⟨i, ik⟩
    simpa [encode, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using member
  unfold controlBits at bits
  simp only [List.append_assoc] at bits
  obtain ⟨path, bits⟩ := List.append_inj bits (by
    rw [List.length_rightpad, List.length_rightpad,
      Nat.max_eq_left (by omega), Nat.max_eq_left (by omega)])
  obtain ⟨sbits, bits⟩ := List.append_inj bits (by simp [fieldBits])
  obtain ⟨bbits, bits⟩ := List.append_inj bits (by simp [fieldBits])
  obtain ⟨lbits, bits⟩ := List.append_inj bits (by simp [fieldBits])
  obtain ⟨jbits, bits⟩ := List.append_inj bits (by simp [fieldBits])
  obtain ⟨abits, mbits⟩ := List.append_inj bits (by simp)
  have sizeCap := Nat.le_pow_clog (by decide : 1 < 2) P.h
  have countCap := Nat.le_pow_clog (by decide : 1 < 2) (P.h + 1)
  have se : x.s = y.s := field_injective _ _ _ (by omega) (by omega) sbits
  have be : x.b = y.b := field_injective _ _ _ (by omega) (by omega) bbits
  have le : x.l = y.l := field_injective _ _ _ (by omega) (by omega) lbits
  have je : x.j = y.j := field_injective _ _ _ (by omega) (by omega) jbits
  have codes : modeCode x.mu = modeCode y.mu := field_injective 3 _ _
    (by cases x.mu <;> decide) (by cases y.mu <;> decide) mbits
  have me : x.mu = y.mu := by
    have modeInjective : Function.Injective modeCode := by
      intro m n eq
      cases m <;> cases n <;> simp [modeCode] at eq ⊢
    exact modeInjective codes
  have pe : x.p = y.p := by
    have sameLength : x.p.length = y.p.length := by omega
    have recover (p : Address) : (p.rightpad (P.h - 1) false).take p.length = p := by
      simp [List.rightpad]
    have taken := congrArg (List.take x.p.length) path
    rw [recover, sameLength, recover] at taken
    exact taken
  have ae : x.a = y.a := by simpa using abits
  cases x
  cases y
  simp_all

/-- Invert precisely the valid field codes; every remaining word denotes ERROR. -/
noncomputable def decode (P : Parameters) (e : Nat) (w : Bank (bankWidth P.h e)) : Control := by
  classical
  exact if h : ∃ z, Valid P z ∧ encode P.h e z = w then Classical.choose h
    else canonical .error

private theorem decode_encode (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (z : Control) (valid : Valid P z) :
    decode P e (encode P.h e z) = z := by
  classical
  have existsCode : ∃ x, Valid P x ∧ encode P.h e x = encode P.h e z := ⟨z, valid, rfl⟩
  simp only [decode, dite_eq_left existsCode]
  exact encoding_injective P e positive fits _ z (Classical.choose_spec existsCode).1 valid
    (Classical.choose_spec existsCode).2

/-- Read replies use flag columns zero through three; other columns decode absent. -/
def flagReply (r : Flag) : Reply :=
  match r.val with
  | 0 => .alpha | 1 => .beta | 2 => .branch | _ => .absent

/-- Forget the successor fields while retaining the fixed Halt output. -/
def opcode (P : Parameters) (z : Control) : Opcode :=
  match controlProgram P z with
  | .read p _ => .read p
  | .update _ => .update
  | .halt => .halt (z.mu == .halt1)

/-- The full finite source table. Unsupported columns send the control to ERROR. -/
noncomputable def rowTable (P : Parameters) (e : Nat) : Table (bankWidth P.h e) where
  instruction w := opcode P (decode P e w)
  delta w r := match controlProgram P (decode P e w) with
    | .read _ next => if r.val < 4 then encode P.h e (next (flagReply r))
        else encode P.h e (canonical .error)
    | .update next => if r = 4 then encode P.h e next else encode P.h e (canonical .error)
    | .halt => encode P.h e (canonical .error)

private theorem encoded_read (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (z : Control) (valid : Valid P z) (p : Address)
    (next : Reply → Control) (row : controlProgram P z = .read p next) :
    sourceProgram (rowTable P e) (encode P.h e z) =
      .read p (fun r => encode P.h e (next (flagReply (replyFlag r)))) := by
  simp only [sourceProgram, rowTable, opcode, decode_encode P e positive fits z valid, row]
  congr 1
  funext r
  simp [replyFlag, r.isLt]

private theorem encoded_update (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (z : Control) (valid : Valid P z) (next : Control)
    (row : controlProgram P z = .update next) :
    sourceProgram (rowTable P e) (encode P.h e z) = .update (encode P.h e next) := by
  simp [sourceProgram, rowTable, opcode, decode_encode P e positive fits z valid, row]

private theorem encoded_halt (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (z : Control) (valid : Valid P z)
    (row : controlProgram P z = .halt) :
    (rowTable P e).instruction (encode P.h e z) = .halt (z.mu == .halt1) := by
  simp [rowTable, opcode, decode_encode P e positive fits z valid, row]

private theorem terminating_valid (P : Parameters) (obs : Nat → Address → Reply)
    {x y : Control} {a b : Nat} (path : Run (controlProgram P) obs x a y b)
    (halt : controlProgram P y = .halt) : Valid P x ∧ x.mu ≠ .error := by
  classical
  induction path with
  | refl x a =>
    by_cases valid : Valid P x
    · refine ⟨valid, ?_⟩
      intro mode
      simp [controlProgram, valid, mode] at halt
    · simp [controlProgram, valid] at halt
  | @read x p next a y b row tail ih =>
    have good := ih halt
    by_cases valid : Valid P x
    · refine ⟨valid, ?_⟩
      intro mode
      simp only [controlProgram, ite_eq_left valid, mode] at row
      cases row
      exact good.2 rfl
    · simp only [controlProgram, ite_eq_right valid] at row
      cases row
      exact (good.2 rfl).elim
  | @update x next a y b row tail ih =>
    by_cases valid : Valid P x
    · refine ⟨valid, ?_⟩
      intro mode
      simp only [controlProgram, ite_eq_left valid, mode] at row
      cases row
    · simp only [controlProgram, ite_eq_right valid] at row
      cases row

private theorem actual_reply (y : Source) (a : Nat) (p : Address) :
    flagReply (replyFlag (actualObservation y a p)) =
      NativePollingAlignment.observations y a p := by
  unfold actualObservation NativePollingAlignment.observations
  cases readout p (substitution^[a] y) <;> rfl

private theorem encoded_execution (P : Parameters) (e : Nat) (positive : 0 < P.h)
    (fits : P.last < 2 ^ e) (y : Source)
    {x final : Control} {a b : Nat}
    (path : Run (controlProgram P) (NativePollingAlignment.observations y) x a final b)
    (halt : controlProgram P final = .halt) :
    Run (sourceProgram (rowTable P e)) (actualObservation y)
      (encode P.h e x) a (encode P.h e final) b ∧
    (∀ w c, Run (sourceProgram (rowTable P e)) (actualObservation y)
      (encode P.h e x) a w c →
      ∃ z, w = encode P.h e z ∧
        Run (controlProgram P) (NativePollingAlignment.observations y) x a z c ∧
        Valid P z ∧ z.mu ≠ .error) := by
  induction path with
  | refl x a =>
    have good := terminating_valid P (NativePollingAlignment.observations y) (.refl x a) halt
    have valid := good.1
    have row := encoded_halt P e positive fits x valid halt
    have stopped : sourceProgram (rowTable P e) (encode P.h e x) = .halt := by
      simp [sourceProgram, row]
    refine ⟨.refl _ _, ?_⟩
    intro w c other
    cases other with
    | refl => exact ⟨x, rfl, .refl _ _, good⟩
    | read h _ => cases stopped.symm.trans h
    | update h _ => cases stopped.symm.trans h
  | @read x p next a final b row tail ih =>
    have good := terminating_valid P _ (.read row tail) halt
    have valid := good.1
    have hop := encoded_read P e positive fits x valid p next row
    obtain ⟨compiled, reverse⟩ := ih halt
    have compiledNext := compiled
    rw [← actual_reply y a p] at compiledNext
    refine ⟨.read hop compiledNext, ?_⟩
    intro w c other
    cases other with
    | refl => exact ⟨x, rfl, .refl _ _, good⟩
    | read h rest =>
      cases hop.symm.trans h
      dsimp only at rest
      rw [actual_reply y a p] at rest
      obtain ⟨z, eq, orig, valid, safe⟩ := reverse w c rest
      exact ⟨z, eq, .read row orig, valid, safe⟩
    | update h _ => cases hop.symm.trans h
  | @update x next a final b row tail ih =>
    have good := terminating_valid P _ (.update row tail) halt
    have valid := good.1
    have hop := encoded_update P e positive fits x valid next row
    obtain ⟨compiled, reverse⟩ := ih halt
    refine ⟨.update hop compiled, ?_⟩
    intro w c other
    cases other with
    | refl => exact ⟨x, rfl, .refl _ _, good⟩
    | read h _ => cases hop.symm.trans h
    | update h rest =>
      cases hop.symm.trans h
      obtain ⟨z, eq, orig, valid, safe⟩ := reverse w c rest
      exact ⟨z, eq, .update row orig, valid, safe⟩

/-- Actual intermediate executions with the number of POLL Reads exposed.
The count is a mathematical label, never a selector argument. -/
inductive PollingRun (P : Parameters) (obs : Nat → Address → Reply) :
    Control → Nat → Control → Nat → Nat → Prop where
  | refl (z : Control) (a : Nat) : PollingRun P obs z a z a 0
  | read {z : Control} {p : Address} {next : Reply → Control} {a : Nat}
      {final : Control} {b n : Nat} :
      controlProgram P z = .read p next →
      PollingRun P obs (next (obs a p)) a final b n →
      PollingRun P obs z a final b (n + if z.mu == .poll then 1 else 0)
  | update {z next final : Control} {a b n : Nat} :
      controlProgram P z = .update next → PollingRun P obs next (a + 1) final b n →
      PollingRun P obs z a final b n

private def pollLevel (z : Control) : Nat := if z.mu == .poll then 0 else 1

private theorem query_not_poll (N : Nat) (p : Address) : queryMode N p ≠ .poll := by
  unfold queryMode
  split <;> decide

private theorem virtual_not_poll (P : Parameters) (z : Control) (r : Reply) :
    (virtualDelta P z r).mu ≠ .poll := by
  cases r with
  | absent => simp [virtualDelta, canonical]
  | branch =>
    simp only [virtualDelta]
    split
    · split <;> simp [fresh, canonical]
    · split
      · exact query_not_poll _ _
      · decide
  | alpha | beta =>
    simp only [virtualDelta]
    split
    · decide
    · split
      · exact query_not_poll _ _
      · split
        · simp only [canonical]
          split <;> decide
        · decide

private theorem polling_count (P : Parameters) (obs : Nat → Address → Reply)
    {z final : Control} {a b : Nat}
    (path : Run (controlProgram P) obs z a final b) (halt : controlProgram P final = .halt) :
    ∃ n, PollingRun P obs z a final b n ∧ a + pollLevel z + n = b + pollLevel final := by
  induction path with
  | refl z a => exact ⟨0, .refl z a, by omega⟩
  | @read z p next a final b row tail ih =>
    obtain ⟨n, counted, balance⟩ := ih halt
    have valid := (terminating_valid P obs (.read row tail) halt).1
    have modeBalance : pollLevel z + (if z.mu == .poll then 1 else 0) =
        pollLevel (next (obs a p)) := by
      cases mode : z.mu with
      | value =>
        simp only [controlProgram, ite_eq_left valid, mode] at row
        cases row
        simp [pollLevel, mode, virtual_not_poll]
      | guard =>
        simp only [controlProgram, ite_eq_left valid, mode] at row
        cases row
        by_cases accept : DelayedOriginalReadout.guardAccept (P.start + z.j)
            (obs a (z.p.dropLast ++ DelayedOriginalReadout.rights
              ((P.start + z.j) / 2 + 1))) = true
        all_goals simp [pollLevel, mode, canonical, accept]
      | poll =>
        simp only [controlProgram, ite_eq_left valid, mode] at row
        cases row
        cases obs a (DelayedOriginalReadout.rights P.pollDepth) <;>
          simp [pollLevel, mode, canonical, fresh]
      | update | halt0 | halt1 =>
        simp [controlProgram, valid, mode] at row
      | error =>
        simp only [controlProgram, ite_eq_left valid, mode] at row
        cases row
        simp [pollLevel, mode, canonical]
    exact ⟨_, .read row counted, by omega⟩
  | @update z next a final b row tail ih =>
    obtain ⟨n, counted, balance⟩ := ih halt
    have valid := (terminating_valid P obs (.update row tail) halt).1
    have modeBalance : pollLevel z = pollLevel next + 1 := by
      cases mode : z.mu <;> simp only [controlProgram, ite_eq_left valid, mode] at row
      all_goals try cases row
      simp [pollLevel, mode, canonical]
    exact ⟨n, .update row counted, by omega⟩

/-- The finite bit table recognizes exactly the valid padded controls. -/
def TableContract (P : Parameters) (e : Nat) : Prop :=
  (∀ z, Valid P z → (controlBits P.h e z).length = bankWidth P.h e ∧
    decode P e (encode P.h e z) = z) ∧
  (∀ w, (¬ ∃ z, Valid P z ∧ encode P.h e z = w) →
    (rowTable P e).instruction w = .read [] ∧
      ∀ r, (rowTable P e).delta w r = encode P.h e (canonical .error))

/-- Actual paid implementation, including all installed rows and remaining rank. -/
def PhysicalRealization (P : Parameters) (e : Nat) (y : Source)
    (initial final : Control) (U : Nat) (bit : Bool) : Prop :=
  let k := bankWidth P.h e
  let T := rowTable P e
  let obs := actualObservation y
  let z := encode P.h e initial
  let t := encode P.h e final
  (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installedWords k).card =
      2 ^ (2 * k + 8) ∧
  2 * (k + (k + (5 + 3))) - 1 = 4 * k + 15 ∧
  (∀ s : Bool, ∀ u : Bank k, ∀ r : Flag,
    u.card + (T.delta u r).card + (if s then 7 else 5) ≤ 2 * k + 7) ∧
  (∀ w : D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Word k, ∀ r : Flag,
    (∀ i j, i.val + 1 = j.val →
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physical w i = false ∨
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physical w j = false) ∧
    ((D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed T w).next r = w ∨
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.OneBit
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physical w)
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physical
          ((D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed T w).next r)))) ∧
  (∀ right : Bool, ∀ w : Bank k, ∀ a : Nat,
    (∀ p, T.instruction w = .read p →
      Execution T obs (ready right w) a
        (ready (!right) (T.delta w (replyFlag (obs a p)))) a
        (.read p (obs a p) :: List.replicate
          (w.card + (T.delta w (replyFlag (obs a p))).card + if right then 6 else 4)
          (.read [] (obs a [])))) ∧
    (T.instruction w = .update →
      Execution T obs (ready right w) a (ready (!right) (T.delta w 4)) (a + 1)
        (.update :: List.replicate
          (w.card + (T.delta w 4).card + if right then 6 else 4)
          (.read [] (obs (a + 1) []))))) ∧
  ∃ last events,
    D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Execution T obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z) 0
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t) U events ∧
    (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed T
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t)).instruction = .halt bit ∧
    (∀ w c, Run (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.wordProgram T) obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z) 0 w c →
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.wordProgram T w = .halt →
      w = D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t ∧ c = U) ∧
    D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalInstruction T
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalEquiv
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t)) = .halt bit ∧
    Run (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalProgram T) obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalEquiv
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z)) 0
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalEquiv
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t)) U ∧
    (∀ w c, Run (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalProgram T) obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalEquiv
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z)) 0 w c →
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalProgram T w = .halt →
      w = D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.physicalEquiv
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t) ∧ c = U) ∧
    D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.remaining T obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z) 0 = events.length ∧
    D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.remaining T obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t) U = 0 ∧
    (∀ w c, Run (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.wordProgram T) obs
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready false z) 0 w c →
      ∃ suffix, D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Execution T obs w c
        (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.ready last t) U suffix ∧
        D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.remaining T obs w c = suffix.length) ∧
    (∀ w v u : D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Word k,
      ∀ a b c : Nat, ∀ event es bit',
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Execution T obs w a v b [event] →
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.Execution T obs v b u c es →
      (D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed T u).instruction =
        .halt bit' →
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.remaining T obs w a =
        D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.remaining T obs v b + 1) ∧
    D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.SourceRankInvariant T

/-- The uniform field, concrete execution, all-prefix and physical conclusions. -/
def Specification (h T t : Nat) (u : Source) (active bit : Bool) : Prop :=
  let P := rowParameters h T active
  let e := indexWidth h T active
  let U := rowUpdates h T t u active
  let initial := rowInitial T active
  let final := canonical (if bit then .halt1 else .halt0)
  P.h = h ∧ TableContract P e ∧
  P.start ≤ t + U ∧ t + U ≤ P.start + P.last ∧
  (U = 0 ∨ (0 < U ∧
    t + U = alignmentBudget h T - DelayedOriginalReadout.rightClock u)) ∧
  Run (sourceProgram (rowTable P e)) (actualObservation (substitution^[t] u))
    (encode P.h e initial) 0 (encode P.h e final) U ∧
  (rowTable P e).instruction (encode P.h e final) = .halt bit ∧
  (∀ w a, Run (sourceProgram (rowTable P e)) (actualObservation (substitution^[t] u))
    (encode P.h e initial) 0 w a →
    ∃ z, w = encode P.h e z ∧ Valid P z ∧ z.mu ≠ .error ∧
      RowPoint P (t + U) u U z a) ∧
  PhysicalRealization P e (substitution^[t] u) initial final U bit ∧
  (∃ n, PollingRun P (NativePollingAlignment.observations (substitution^[t] u))
    initial 0 final U n ∧ n = if active && decide (0 < T) then U + 1 else 0) ∧
  (∀ N, N ≤ t + U → BoundedPreorderTrial.TrialSpec h (t + U) N u
    (substitution^[t + U] u))

/-- A single installed table for each bound and regime computes every promised
source's original parity, with compressed fields at every actual finite prefix. -/
theorem native_bounded_preorder_control (h T t : Nat) (u : Source)
    (hu : u.length = h) (ht : t ≤ T) (regime : T = 0 ∨ h % 2 = 0) (active : Bool) :
    Specification h T t u active (decide ((composition u).2 % 2 = 1)) := by
  classical
  let P := rowParameters h T active
  let e := indexWidth h T active
  let U := rowUpdates h T t u active
  let y := substitution^[t] u
  let bit := decide ((composition u).2 % 2 = 1)
  let final := canonical (if bit then .halt1 else .halt0)
  have size : P.h = h := by unfold P rowParameters; split <;> rfl
  have positive : 0 < P.h := by rw [size, ← hu]; exact u.length_pos
  have fits : P.last < 2 ^ e := by
    have cap := Nat.le_pow_clog (by decide : 1 < 2)
    by_cases flag : (active && decide (0 < T)) = true
    · simp only [P, e, rowParameters, indexWidth, flag, ite_true, activeParameters]
      have bound := cap (2 * h)
      have hp : 0 < h := by omega
      omega
    · simp only [P, e, rowParameters, indexWidth, flag, Bool.false_eq_true, ite_false]
      have bound := cap (T + 1)
      omega
  obtain ⟨lower, upper, clock, run, halt, _, prefixes⟩ :=
    native_bounded_rows_execution h T t u hu ht regime active
  have compiled := encoded_execution P e positive fits y run halt
  have finalValid :=
    (terminating_valid P (NativePollingAlignment.observations y) (.refl final U) halt).1
  have fixed : (rowTable P e).instruction (encode P.h e final) = .halt bit := by
    have hi := encoded_halt P e positive fits final finalValid halt
    have mode : (final.mu == .halt1) = bit := by dsimp [final]; cases bit <;> rfl
    exact hi.trans (congrArg Opcode.halt mode)
  have table : TableContract P e := by
    constructor
    · intro z valid
      exact ⟨bits_length P e positive z valid, decode_encode P e positive fits z valid⟩
    · intro w invalid
      have error : decode P e w = canonical .error := by simp [decode, invalid]
      constructor
      · simp [rowTable, error, opcode, controlProgram, Valid, canonical]
      · intro r
        simp [rowTable, error, controlProgram, Valid, canonical]
  refine ⟨size, table, lower, upper, clock, compiled.1, fixed, ?_, ?_, ?_, ?_⟩
  · intro w a pref
    obtain ⟨z, eq, orig, valid, safe⟩ := compiled.2 w a pref
    exact ⟨z, eq, valid, safe, prefixes z a orig⟩
  · obtain ⟨count, width, routing, legal, implementation⟩ :=
      D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.installed_halt
        compiled.1 fixed false
    refine ⟨count, width, routing, legal, ?_, implementation⟩
    intro right w a
    exact D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord.native_transfer
      (rowTable P e) (actualObservation y) right w a
  · obtain ⟨n, counted, balance⟩ := polling_count P _ run halt
    refine ⟨n, counted, ?_⟩
    have phaseFinal : pollLevel final = 1 := by dsimp [final, pollLevel]; cases bit <;> rfl
    rw [phaseFinal] at balance
    by_cases flag : (active && decide (0 < T)) = true
    · have phaseInitial : pollLevel (rowInitial T active) = 0 := by
        simp [rowInitial, flag, pollLevel, canonical]
      rw [phaseInitial] at balance
      simp only [flag, ite_true]
      omega
    · have zero : rowUpdates h T t u active = 0 := by simp [rowUpdates, flag]
      have phaseInitial : pollLevel (rowInitial T active) = 1 := by
        simp [rowInitial, flag, pollLevel, fresh]
      rw [phaseInitial, zero] at balance
      simp only [flag, Bool.false_eq_true, ite_false]
      omega
  · exact (BoundedPreorderTrial.bounded_preorder_trial h (t + U) P.start u
      (substitution^[t + U] u) hu rfl lower).1

#print axioms native_bounded_preorder_control

end D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
