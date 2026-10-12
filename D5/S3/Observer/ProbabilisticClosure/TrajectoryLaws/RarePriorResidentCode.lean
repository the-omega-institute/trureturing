/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit finite codecs serialize native runtime and fair-bit workspaces into resident tables. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFairBitService

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
open FourthSegmentStoppedLaw NativeAcquiredPrefixState RarePriorFiniteMonitor RarePriorFairBitService

def pairFin {α β : Type} {m n : ℕ} (a : α ≃ Fin m) (b : β ≃ Fin n) :
    α × β ≃ Fin (m*n) := (Equiv.prodCongr a b).trans finProdFinEquiv

def sumFin {α β : Type} {m n : ℕ} (a : α ≃ Fin m) (b : β ≃ Fin n) :
    α ⊕ β ≃ Fin (m+n) := (Equiv.sumCongr a b).trans finSumFinEquiv

def phaseCodec : ActivePhase ≃ Fin 2 where
  toFun | .p => 0 | .beta => 1
  invFun k := if k = 0 then .p else .beta
  left_inv s := by cases s <;> rfl
  right_inv k := by fin_cases k <;> rfl

def unitCodec : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := by fin_cases k; rfl

def fourthCodec : FourthControl ≃ Fin 5 :=
  ({ toFun := fun c => match c with
      | .active s => .inl s
      | .pending b => .inr (.inl b)
      | .delivered => .inr (.inr ())
     invFun := fun c => match c with
      | .inl s => .active s
      | .inr (.inl b) => .pending b
      | .inr (.inr _) => .delivered
     left_inv := by intro c; cases c <;> rfl
     right_inv := by intro c; rcases c with s | b | u; rfl; rfl; cases u; rfl } :
      FourthControl ≃ (ActivePhase ⊕ Letter ⊕ Unit)).trans
    (sumFin phaseCodec (sumFin (Equiv.refl _) unitCodec))

def optionLetterCodec : Option Letter ≃ Fin 3 := (finSuccEquiv 2).symm

def controlCodec : NativeControl ≃ Fin 14 :=
  ({ toFun := fun c => match c with
      | .seed s => .inl s
      | .early t p => .inr (.inl (t,p))
      | .fourth c => .inr (.inr c)
     invFun := fun c => match c with
      | .inl s => .seed s
      | .inr (.inl (t,p)) => .early t p
      | .inr (.inr c) => .fourth c
     left_inv := by intro c; cases c <;> rfl
     right_inv := by intro c; rcases c with s | ⟨t,p⟩ | c <;> rfl } :
      NativeControl ≃ (Option Letter ⊕ (Fin 3 × ActivePhase) ⊕ FourthControl)).trans
    (sumFin optionLetterCodec (sumFin (pairFin (Equiv.refl _) phaseCodec) fourthCodec))

def qoneCodec : QOne ≃ Fin 6 where
  toFun | .empty => 0 | .a => 1 | .ac => 2 | .d => 3 | .ad => 4 | .da => 5
  invFun k := match k.val with | 0 => .empty | 1 => .a | 2 => .ac | 3 => .d | 4 => .ad | _ => .da
  left_inv q := by cases q <;> rfl
  right_inv k := by fin_cases k <;> rfl

def qtwoCodec : QTwo ≃ Fin 5 where
  toFun | .empty => 0 | .b => 1 | .c => 2 | .bc => 3 | .cb => 4
  invFun k := match k.val with | 0 => .empty | 1 => .b | 2 => .c | 3 => .bc | _ => .cb
  left_inv q := by cases q <;> rfl
  right_inv k := by fin_cases k <;> rfl

def snapshotCodec : ThirdSnapshot ≃ Fin 20 :=
  ({ toFun := fun s => (s.seed,s.weight,s.syndrome)
     invFun := fun s => ⟨s.1,s.2.1,s.2.2⟩
     left_inv := by intro s; rfl
     right_inv := by intro s; rfl } : ThirdSnapshot ≃ (Letter × Fin 5 × Letter)).trans
    (pairFin (Equiv.refl _) (pairFin (Equiv.refl _) (Equiv.refl _)))

def registersCodec : Registers ≃ Fin 56700 :=
  ({ toFun := fun r => (r.seed,r.weight,r.syndrome,r.qone,r.qtwo,r.z,r.snapshot)
     invFun := fun r => ⟨r.1,r.2.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2.1,r.2.2.2.2.2.1,r.2.2.2.2.2.2⟩
     left_inv := by intro r; rfl
     right_inv := by intro r; rfl } :
      Registers ≃ (Option Letter × Fin 5 × Option Letter × QOne × QTwo × Letter × Option ThirdSnapshot)).trans
    (pairFin optionLetterCodec (pairFin (Equiv.refl _) (pairFin optionLetterCodec
      (pairFin qoneCodec (pairFin qtwoCodec (pairFin (Equiv.refl _)
        ((Equiv.optionCongr snapshotCodec).trans (finSuccEquiv 20).symm)))))))

def fieldsCodec : FiniteFields ≃ Fin 793800 :=
  ({ toFun := fun f => (f.control,f.registers)
     invFun := fun f => ⟨f.1,f.2⟩
     left_inv := by intro f; rfl
     right_inv := by intro f; rfl } : FiniteFields ≃ (NativeControl × Registers)).trans
    (pairFin controlCodec registersCodec)

def monitorCodec : Monitor ≃ Fin 6023 :=
  ({ toFun := fun m => match m with
      | .block c p => .inl (c,p)
      | .suffix p => .inr (.inl p)
      | .accepted => .inr (.inr (0 : Fin 2))
      | .sink => .inr (.inr (1 : Fin 2))
     invFun := fun m => match m with
      | .inl (c,p) => .block c p
      | .inr (.inl p) => .suffix p
      | .inr (.inr k) => if k = 0 then .accepted else .sink
     left_inv := by intro m; cases m <;> rfl
     right_inv := by intro m; rcases m with ⟨c,p⟩ | p | k; rfl; rfl; fin_cases k <;> rfl } :
      Monitor ≃ ((Fin 376 × Fin 16) ⊕ Fin 5 ⊕ Fin 2)).trans
    (sumFin (pairFin (Equiv.refl _) (Equiv.refl _))
      (sumFin (Equiv.refl _) (Equiv.refl _)))

def modeCodec : Mode ≃ Fin 4 where
  toFun | .watching => 0 | .ordinary => 1 | .g => 2 | .gBeta => 3
  invFun k := match k.val with | 0 => .watching | 1 => .ordinary | 2 => .g | _ => .gBeta
  left_inv m := by cases m <;> rfl
  right_inv k := by fin_cases k <;> rfl

def runtimeSize : ℕ := 793800*(6023*4)

def runtimeCodec : Runtime ≃ Fin runtimeSize :=
  ({ toFun := fun z => (z.fields,z.monitor,z.mode)
     invFun := fun z => ⟨z.1,z.2.1,z.2.2⟩
     left_inv := by intro z; rfl
     right_inv := by intro z; rfl } : Runtime ≃ (FiniteFields × Monitor × Mode)).trans
    (pairFin fieldsCodec (pairFin monitorCodec modeCodec))

def thresholdCodec : Threshold ≃ Fin 3 where
  toFun | .ordinary => 0 | .high => 1 | .low => 2
  invFun k := match k.val with | 0 => .ordinary | 1 => .high | _ => .low
  left_inv t := by cases t <;> rfl
  right_inv k := by fin_cases k <;> rfl

def pcCodec : PC ≃ Fin 4 where
  toFun | .reset => 0 | .bit => 1 | .compare => 2 | .returned => 3
  invFun k := match k.val with | 0 => .reset | 1 => .bit | 2 => .compare | _ => .returned
  left_inv p := by cases p <;> rfl
  right_inv k := by fin_cases k <;> rfl

def serviceCodec : Service ≃ Fin 21504 :=
  ({ toFun := fun s => (s.thresholdTag,s.pc,s.bitPosition,s.candidate,s.output)
     invFun := fun s => ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩
     left_inv := by intro s; rfl
     right_inv := by intro s; rfl } : Service ≃ (Threshold × PC × Fin 7 × Fin 128 × Letter)).trans
    (pairFin thresholdCodec (pairFin pcCodec (pairFin (Equiv.refl _)
      (pairFin (Equiv.refl _) (Equiv.refl _)))))

def operationCodec : Operation ≃ Fin 4 :=
  ({ toFun := fun op => match op with | .read x => .inl x | .stop b => .inr b
     invFun := fun op => match op with | .inl x => .read x | .inr b => .stop b
     left_inv := by intro op; cases op <;> rfl
     right_inv := by intro op; cases op <;> rfl } : Operation ≃ (Letter ⊕ Letter)).trans
    (sumFin (Equiv.refl _) (Equiv.refl _))


/-- A literal unary bit block, with a fixed length even at value zero. -/
def bitCode {n : ℕ} (x : Fin n) : List Bool :=
  List.replicate x.val true ++ List.replicate (n-x.val) false

theorem bit_code_length {n : ℕ} (x : Fin n) : (bitCode x).length = n := by
  simp [bitCode]

theorem bit_code_injective {n : ℕ} : Function.Injective (@bitCode n) := by
  intro x y h
  have hc := congrArg (List.count true) h
  simp [bitCode, List.count_replicate] at hc
  exact Fin.ext hc

def nativeKeyCodec : Runtime × Operation ≃ Fin (runtimeSize*4) := pairFin runtimeCodec operationCodec

def optionalRuntimeCodec : Option Runtime ≃ Fin (runtimeSize+1) :=
  (Equiv.optionCongr runtimeCodec).trans (finSuccEquiv runtimeSize).symm

@[irreducible] def nativeRowValue (k : Fin (runtimeSize*4)) : Fin (runtimeSize+1) :=
  let z := nativeKeyCodec.symm k
  optionalRuntimeCodec (runtimeStep z.1 z.2)


/-- A bounded resident-row read. The immutable vector is code, not a runtime archive. -/
@[irreducible] def readRow {α : Type} {n : ℕ} (table : Vector α n) (i : Fin n) : α := table[i.val]

private theorem read_row_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    readRow (Vector.ofFn f) i = f i := by
  simp only [readRow, Vector.getElem_ofFn, Fin.eta]

private theorem dictionary_code_length {k n : ℕ} (table : Vector (Fin k × Fin n) k) :
    (table.toList.map (fun row => bitCode row.1 ++ bitCode row.2)).flatten.length = k*(k+n) := by
  simp only [List.length_flatten, List.map_map, Function.comp_def,
    List.length_append, bit_code_length]
  simp

/-- Resident rows carry their exact addressed finite data relation. -/
structure InstalledTable {k n : ℕ} (f : Fin k → Fin n) where
  rows : Vector (Fin k × Fin n) k
  binding : ∀ a, readRow rows a = (a,f a)
  code : List Bool
  serialization : code = (rows.toList.map (fun row => bitCode row.1 ++ bitCode row.2)).flatten
  codeLength : code.length = k*(k+n)

private def installTable {k n : ℕ} (f : Fin k → Fin n) : InstalledTable f where
  rows := Vector.ofFn (fun a => (a,f a))
  binding a := read_row_ofFn _ a
  code := ((Vector.ofFn (fun a => (a,f a))).toList.map
    (fun row => bitCode row.1 ++ bitCode row.2)).flatten
  serialization := rfl
  codeLength := dictionary_code_length _

/-- A fixed native table with a kernel-verified row relation. -/
opaque installedNative : InstalledTable nativeRowValue := installTable nativeRowValue

/-- Each table row stores its entire input address and the original partial successor. -/
def nativeDictionary : Vector (Fin (runtimeSize*4) × Fin (runtimeSize+1)) (runtimeSize*4) :=
  installedNative.rows

def bitKeyCodec : Service × Letter ≃ Fin 43008 := pairFin serviceCodec (Equiv.refl _)

@[irreducible] def serviceRowValue (k : Fin 43008) : Fin 21504 :=
  let s := bitKeyCodec.symm k
  serviceCodec (microStep s.1 s.2)

/-- A fixed service table with a kernel-verified row relation. -/
opaque installedService : InstalledTable serviceRowValue := installTable serviceRowValue

def bitDictionary : Vector (Fin 43008 × Fin 21504) 43008 := installedService.rows

@[irreducible] def nativeTable (k : Fin (runtimeSize*4)) : Fin (runtimeSize+1) :=
  (readRow nativeDictionary k).2

@[irreducible] def serviceTable (k : Fin 43008) : Fin 21504 :=
  (readRow bitDictionary k).2

/-- The query controller selects its service tag by another fixed resident row. -/
@[irreducible] def initializationRowValue (k : Fin runtimeSize) : Fin 21504 :=
  serviceCodec (entry (selectedThreshold (runtimeCodec.symm k)))

opaque installedInitialization : InstalledTable initializationRowValue := installTable initializationRowValue

def initializationDictionary : Vector (Fin runtimeSize × Fin 21504) runtimeSize :=
  installedInitialization.rows

@[irreducible] def initializationTable (k : Fin runtimeSize) : Fin 21504 :=
  (readRow initializationDictionary k).2

private theorem initialization_resident_row (a : Fin runtimeSize) :
    readRow initializationDictionary a = (a,initializationRowValue a) :=
  installedInitialization.binding a

private theorem native_resident_row (a : Fin (runtimeSize*4)) :
    readRow nativeDictionary a = (a,nativeRowValue a) := by
  exact installedNative.binding a

private theorem service_resident_row (a : Fin 43008) :
    readRow bitDictionary a = (a,serviceRowValue a) := by
  exact installedService.binding a


/-- Addressed instruction records contain opcode and both branch destinations. -/
def instructionGraph : Vector (Fin 4 × Fin 4 × Fin 4) 4 :=
  #v[(0,1,0),(1,2,3),(2,2,2),(3,3,3)]

def instructionCode : List Bool :=
  (instructionGraph.toList.map (fun r => bitCode r.1 ++ bitCode r.2.1 ++ bitCode r.2.2)).flatten

def constantsCode : List Bool :=
  bitCode (375 : Fin 376) ++ bitCode (40 : Fin 101) ++ bitCode (90 : Fin 101) ++
    bitCode (1 : Fin 101) ++ bitCode (100 : Fin 129) ++ bitCode (7 : Fin 8)

@[irreducible] def residentCode : List Bool := instructionCode ++ constantsCode ++
  installedNative.code ++ installedService.code ++ installedInitialization.code

def residentWidth : ℕ := 48 + 816 + (runtimeSize*4)*(runtimeSize*5+1) +
  43008*(43008+21504) + runtimeSize*(runtimeSize+21504)

private theorem instruction_code_length : instructionCode.length = 48 := by
  simp only [instructionCode, instructionGraph, Vector.toList_mk, List.toList_toArray,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.length_append,
    bit_code_length, List.length_nil]

private theorem constants_code_length : constantsCode.length = 816 := by
  unfold constantsCode
  simp only [List.length_append, bit_code_length]

private theorem resident_code_length : residentCode.length = residentWidth := by
  rw [residentCode, List.length_append, List.length_append, List.length_append,
    List.length_append, instruction_code_length, constants_code_length,
    installedNative.codeLength, installedService.codeLength, installedInitialization.codeLength]
  unfold residentWidth
  rw [show runtimeSize*4 + (runtimeSize+1) = runtimeSize*5+1 by omega]


/-- The output store is a bounded scratch block; original record rendering is a separate consumer. -/
@[ext] structure MicroSnapshot where
  ready : Runtime
  syntheticCopy : Runtime
  service : Service
  operation : Operation
  output : Fin 32 → Fin 16
  outputCursor : Fin 33
  pc : Fin 8
  tableAddress : Fin (runtimeSize*4+1)
  sourceAddress : Fin (runtimeSize*5+2)
  destinationAddress : Fin (runtimeSize*5+2)
  bitPosition : Fin (runtimeSize*5+2)
  matchFlag : Bool
  workspace : Bool


/-- All resident and transient fields, including three table addresses, are serialized. -/
@[irreducible] def snapshotCode (s : MicroSnapshot) : List Bool :=
  bitCode (runtimeCodec s.ready) ++ bitCode (runtimeCodec s.syntheticCopy) ++
  bitCode (serviceCodec s.service) ++ bitCode (operationCodec s.operation) ++
  (List.ofFn (fun i : Fin 32 => bitCode (s.output i))).flatten ++
  bitCode s.outputCursor ++ bitCode s.pc ++ bitCode s.tableAddress ++
  bitCode s.sourceAddress ++ bitCode s.destinationAddress ++ bitCode s.bitPosition ++
  [s.matchFlag,s.workspace]

def snapshotWidth : ℕ :=
  2*runtimeSize + 21504 + 4 + 32*16 + 33 + 8 + (runtimeSize*4+1) +
    3*(runtimeSize*5+2) + 2

def B0 : ℕ := residentWidth + snapshotWidth + 1

private theorem block_split {n : ℕ} (x y : Fin n) (u v : List Bool)
    (h : bitCode x ++ u = bitCode y ++ v) : x = y ∧ u = v := by
  obtain ⟨ha,hb⟩ := List.append_inj h (by rw [bit_code_length, bit_code_length])
  exact ⟨bit_code_injective ha,hb⟩

private theorem output_code_length {n m : ℕ} (f : Fin n → Fin m) :
    (List.ofFn (fun i => bitCode (f i))).flatten.length = n*m := by
  rw [List.length_flatten, List.map_ofFn]
  have h : (List.length ∘ fun i => bitCode (f i)) = fun _ : Fin n => m := by
    funext i
    exact bit_code_length (f i)
  rw [h]
  simp only [List.ofFn_const, List.sum_replicate, smul_eq_mul]

set_option maxRecDepth 10000

/-- This fixed charged bound includes every table bit and every complete microstate bit. -/
theorem charged_snapshot_bound (s : MicroSnapshot) :
    (snapshotCode s).length = snapshotWidth ∧
    residentCode.length + (snapshotCode s).length < B0 ∧ 1 ≤ B0 := by
  have hs : (snapshotCode s).length = snapshotWidth := by
    simp only [snapshotCode, List.length_append, bit_code_length, output_code_length,
      List.length_cons, List.length_nil]
    change _ = 2*runtimeSize + 21504 + 4 + 32*16 + 33 + 8 + (runtimeSize*4+1) +
      3*(runtimeSize*5+2) + 2
    omega
  refine ⟨hs, ?_, ?_⟩
  · rw [hs, resident_code_length]
    exact Nat.lt_succ_self _
  · exact Nat.succ_le_succ (Nat.zero_le _)

private theorem output_code_injective {n m : ℕ} :
    Function.Injective (fun f : Fin n → Fin m => (List.ofFn (fun i => bitCode (f i))).flatten) := by
  intro f g h
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨h0,ht⟩ := block_split (f 0) (g 0) _ _ h
    have he := ih ht
    funext i
    refine Fin.cases h0 (fun j => congrFun he j) i


/-- Every original field, monitor register and transient address can be recovered from the tape. -/
theorem complete_snapshot_encoding : Function.Injective snapshotCode := by
  intro x y h
  simp only [snapshotCode, List.append_assoc] at h
  obtain ⟨hready,h⟩ := block_split _ _ _ _ h
  obtain ⟨hcopy,h⟩ := block_split _ _ _ _ h
  obtain ⟨hservice,h⟩ := block_split _ _ _ _ h
  obtain ⟨hop,h⟩ := block_split _ _ _ _ h
  obtain ⟨hout,h⟩ := List.append_inj h (by rw [output_code_length,output_code_length])
  have ho := output_code_injective hout
  obtain ⟨hcursor,h⟩ := block_split _ _ _ _ h
  obtain ⟨hpc,h⟩ := block_split _ _ _ _ h
  obtain ⟨htable,h⟩ := block_split _ _ _ _ h
  obtain ⟨hsrc,h⟩ := block_split _ _ _ _ h
  obtain ⟨hdst,h⟩ := block_split _ _ _ _ h
  obtain ⟨hbit,h⟩ := block_split _ _ _ _ h
  have hflags := List.cons.inj h
  have hflag := hflags.1
  have hwork := (List.cons.inj hflags.2).1
  apply MicroSnapshot.ext
  · exact runtimeCodec.injective hready
  · exact runtimeCodec.injective hcopy
  · exact serviceCodec.injective hservice
  · exact operationCodec.injective hop
  · exact ho
  · exact hcursor
  · exact hpc
  · exact htable
  · exact hsrc
  · exact hdst
  · exact hbit
  · exact hflag
  · exact hwork


/-- A bounded register machine for a single sequential unary table scan. -/
@[ext] structure Scanner (k n : ℕ) where
  query : Fin k
  row : Fin (k+1)
  cursor : Fin (k+n+1)
  accumulator : Fin (n+1)
  pc : Fin 4
  equalFlag : Bool
  deriving DecidableEq, Fintype

def tapeBit {n : ℕ} (v : Fin n) (i : ℕ) : Bool := (bitCode v)[i]?.getD false

private theorem tape_bit_correct {n : ℕ} (v : Fin n) (i : ℕ) :
    tapeBit v i = decide (i < v.val) := by
  by_cases h : i < v.val
  · unfold tapeBit bitCode
    rw [List.getElem?_append_left (by simpa only [List.length_replicate] using h)]
    simp [h]
  · rw [tapeBit, bitCode, List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp only [List.getElem?_replicate, decide_eq_false h]
    split <;> rfl



/-- PC zero compares one key bit, PC one copies one payload bit, PC two returns,
    and PC three denotes an exhausted or malformed scan. -/
def scannerStep {k n : ℕ} (table : Fin k → Fin n) (s : Scanner k n) : Scanner k n :=
  if hr : s.row.val < k then
    let r : Fin k := ⟨s.row.val,hr⟩
    if s.pc = 0 then
      if hi : s.cursor.val < k then
        { s with
          cursor := ⟨s.cursor.val+1,by omega⟩
          equalFlag := s.equalFlag && (tapeBit s.query s.cursor.val == tapeBit r s.cursor.val) }
      else if s.equalFlag then
        { s with pc := (instructionGraph[0]).2.1, cursor := 0, accumulator := 0 }
      else { s with row := ⟨s.row.val+1,by omega⟩, pc := (instructionGraph[0]).2.2, cursor := 0, equalFlag := true }
    else if s.pc = 1 then
      if hi : s.cursor.val < n then
        { s with
          cursor := ⟨s.cursor.val+1,by omega⟩
          accumulator := ⟨min n (s.accumulator.val + if tapeBit (table r) s.cursor.val then 1 else 0),
            Nat.lt_succ_of_le (min_le_left _ _)⟩ }
      else { s with pc := if s.accumulator.val < n then (instructionGraph[1]).2.1 else (instructionGraph[1]).2.2 }
    else s
  else { s with pc := (instructionGraph[3]).1 }

def scannerEntry {k n : ℕ} (a : Fin k) : Scanner k n := ⟨a,0,0,0,0,true⟩

def scannerTicks {k n : ℕ} (table : Fin k → Fin n) (m : ℕ) (s : Scanner k n) :
    Scanner k n := (scannerStep table)^[m] s

private theorem ticks_succ {k n : ℕ} (table : Fin k → Fin n) (m : ℕ) (s : Scanner k n) :
    scannerTicks table (m+1) s = scannerStep table (scannerTicks table m s) := by
  exact Function.iterate_succ_apply' _ _ _

private theorem ticks_add {k n : ℕ} (table : Fin k → Fin n) (m p : ℕ) (s : Scanner k n) :
    scannerTicks table (m+p) s = scannerTicks table p (scannerTicks table m s) := by
  simp only [scannerTicks]
  rw [Nat.add_comm m p, Function.iterate_add_apply]

def scannerResult {k n : ℕ} (s : Scanner k n) : Option (Fin n) :=
  if s.pc = 2 then if h : s.accumulator.val < n then some ⟨s.accumulator.val,h⟩ else none
  else none

private def prefixFlag {k : ℕ} (a r : Fin k) (j : ℕ) : Bool :=
  decide (min j a.val = min j r.val)

private theorem prefix_next {k : ℕ} (a r : Fin k) (j : ℕ) :
    prefixFlag a r (j+1) = (prefixFlag a r j && (tapeBit a j == tapeBit r j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [prefixFlag, tape_bit_correct, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [decide_eq_decide]
  omega

private def compareState {k n : ℕ} (a r : Fin k) (j : ℕ) (h : j ≤ k) : Scanner k n :=
  ⟨a,⟨r.val,by omega⟩,⟨j,by omega⟩,0,0,prefixFlag a r j⟩

private theorem compare_run {k n : ℕ} (table : Fin k → Fin n) (a r : Fin k)
    (j : ℕ) (hj : j ≤ k) :
    scannerTicks table j (compareState a r 0 (Nat.zero_le _)) = compareState a r j hj := by
  induction j with
  | zero => simp [scannerTicks, compareState, prefixFlag]
  | succ j ih =>
    rw [ticks_succ, ih (by omega)]
    have hr := r.isLt
    have hjk : j < k := by omega
    simp only [scannerStep, instructionGraph, compareState, hr, ↓reduceDIte, Fin.mk.injEq,
      Fin.val_zero, Fin.zero_eta, hjk, ↓reduceIte, Fin.val_mk]
    congr 1
    exact (prefix_next a r j).symm

private def copyState {k n : ℕ} (table : Fin k → Fin n) (a r : Fin k)
    (j : ℕ) (h : j ≤ n) : Scanner k n :=
  ⟨a,⟨r.val,by omega⟩,⟨j,by omega⟩,
    ⟨min j (table r).val,by have := (table r).isLt; omega⟩,1,true⟩

private theorem copy_run {k n : ℕ} (table : Fin k → Fin n) (a r : Fin k)
    (j : ℕ) (hj : j ≤ n) :
    scannerTicks table j (copyState table a r 0 (Nat.zero_le _)) = copyState table a r j hj := by
  induction j with
  | zero => simp [scannerTicks]
  | succ j ih =>
    rw [ticks_succ, ih (by omega)]
    have hr := r.isLt
    have hjn : j < n := by omega
    simp only [scannerStep, instructionGraph, copyState, hr, ↓reduceDIte, Fin.mk.injEq,
      Fin.val_zero, Fin.val_one, hjn, ↓reduceIte, Fin.val_mk, Fin.isValue, one_ne_zero]
    apply Scanner.ext <;> try rfl
    apply Fin.ext
    simp only [tape_bit_correct, Fin.eta, decide_eq_true_eq]
    split <;> omega

private theorem matched_copy {k n : ℕ} (table : Fin k → Fin n) (a : Fin k) :
    scannerStep table (compareState a a k le_rfl) =
      copyState table a a 0 (Nat.zero_le _) := by
  have ha := a.isLt
  simp [scannerStep, instructionGraph, compareState, copyState, prefixFlag, ha]

private theorem copy_returns {k n : ℕ} (table : Fin k → Fin n) (a : Fin k) :
    scannerResult (scannerStep table (copyState table a a n le_rfl)) = some (table a) := by
  have ha := a.isLt
  have ht := (table a).isLt
  simp [scannerStep, instructionGraph, copyState, scannerResult, ha, ht, Nat.min_eq_right (by omega : (table a).val ≤ n)]

private theorem skipped_row {k n : ℕ} (table : Fin k → Fin n) (a r : Fin k)
    (h : r.val < a.val) :
    scannerStep table (compareState a r k le_rfl) =
      compareState a ⟨r.val+1,by have := a.isLt; omega⟩ 0 (Nat.zero_le _) := by
  have hr := r.isLt
  have ha := a.isLt
  have hn : min k a.val ≠ min k r.val := by omega
  simp [scannerStep, instructionGraph, compareState, prefixFlag, hr, hn, ne_of_gt h]

private theorem reaches_row {k n : ℕ} (table : Fin k → Fin n) (a : Fin k)
    (r : ℕ) (hr : r ≤ a.val) :
    scannerTicks table (r*(k+1)) (scannerEntry a) =
      compareState a ⟨r,by have := a.isLt; omega⟩ 0 (Nat.zero_le _) := by
  induction r with
  | zero => simp [scannerTicks, scannerEntry, compareState, prefixFlag]
  | succ r ih =>
    have hl : r < a.val := by omega
    have he : (r+1)*(k+1) = r*(k+1) + k + 1 := by ring
    rw [he, ticks_succ, ticks_add, ih (by omega),
      compare_run table a _ k le_rfl, skipped_row table a _ hl]


/-- The actual bounded-register graph scans the installed keys and copies every payload bit. -/
theorem bounded_scanner_correct {k n : ℕ} (table : Fin k → Fin n) (a : Fin k) :
    scannerResult (scannerTicks table (a.val*(k+1)+k+1+n+1) (scannerEntry a)) =
      some (table a) := by
  rw [ticks_succ, ticks_add]
  have hm : scannerTicks table (a.val*(k+1)+k+1) (scannerEntry a) =
      copyState table a a 0 (Nat.zero_le _) := by
    rw [ticks_succ, ticks_add, reaches_row table a a.val le_rfl,
      compare_run table a a k le_rfl, matched_copy]
  rw [hm, copy_run table a a n le_rfl, copy_returns]

def installedGraphStep {k n : ℕ} (table : Fin k → Fin n) (s : Scanner k n) : Scanner k n :=
  scannerStep table { s with pc := (instructionGraph[s.pc.val]).1 }

private theorem graph_opcode (p : Fin 4) : (instructionGraph[p.val]).1 = p := by
  fin_cases p <;> rfl

private theorem graph_step_correct {k n : ℕ} (table : Fin k → Fin n) (s : Scanner k n) :
    installedGraphStep table s = scannerStep table s := by
  rw [installedGraphStep, graph_opcode]

@[irreducible] def tableProgram {k n : ℕ} (t : Fin k → Fin n) (a : Fin k) : Option (Fin n) :=
  scannerResult ((installedGraphStep t)^[a.val*(k+1)+k+1+n+1] (scannerEntry a))

private theorem table_program_correct {k n : ℕ} (t : Fin k → Fin n) (a : Fin k) :
    tableProgram t a = some (t a) := by
  have hg : installedGraphStep t = scannerStep t := funext (graph_step_correct t)
  rw [tableProgram, hg]
  exact bounded_scanner_correct t a

@[irreducible] def nativeProgram (z : Runtime) (op : Operation) : Option Runtime :=
  (tableProgram nativeTable (nativeKeyCodec (z,op))).bind optionalRuntimeCodec.symm

@[irreducible] def serviceProgram (s : Service) (b : Letter) : Option Service :=
  (tableProgram serviceTable (bitKeyCodec (s,b))).map serviceCodec.symm

@[irreducible] def initializationProgram (z : Runtime) : Option Service :=
  (tableProgram initializationTable (runtimeCodec z)).map serviceCodec.symm

private theorem decoded_table_correct {β : Type} {k n : ℕ} (e : β ≃ Fin n)
    (t : Fin k → Fin n) (a : Fin k) (v : β) (h : t a = e v) :
    (tableProgram t a).map e.symm = some v := by
  rw [table_program_correct, Option.map_some, h, e.symm_apply_apply]

private theorem decoded_partial_table_correct {β : Type} {k n : ℕ} (e : Option β ≃ Fin n)
    (t : Fin k → Fin n) (a : Fin k) (v : Option β) (h : t a = e v) :
    (tableProgram t a).bind e.symm = v := by
  rw [table_program_correct, Option.bind_some, h, e.symm_apply_apply]


/-- Every scanner register occupies an address already charged by the complete snapshot. -/
def scannerSnapshot {k n : ℕ} (base : MicroSnapshot) (s : Scanner k n)
    (hk : k ≤ runtimeSize*4) (hn : n ≤ runtimeSize+1) : MicroSnapshot :=
  { base with
    pc := ⟨s.pc.val,by have := s.pc.isLt; omega⟩
    tableAddress := ⟨s.row.val,by have := s.row.isLt; omega⟩
    sourceAddress := ⟨s.query.val,by have := s.query.isLt; omega⟩
    destinationAddress := ⟨s.accumulator.val,by have := s.accumulator.isLt; omega⟩
    bitPosition := ⟨s.cursor.val,by have := s.cursor.isLt; omega⟩
    matchFlag := s.equalFlag
    workspace := false }

private theorem scanner_snapshot_injective {k n : ℕ} (base : MicroSnapshot)
    (hk : k ≤ runtimeSize*4) (hn : n ≤ runtimeSize+1) :
    Function.Injective (fun s : Scanner k n => scannerSnapshot base s hk hn) := by
  intro s q h
  apply Scanner.ext
  · exact Fin.ext (congrArg (fun x => x.sourceAddress.val) h)
  · exact Fin.ext (congrArg (fun x => x.tableAddress.val) h)
  · exact Fin.ext (congrArg (fun x => x.bitPosition.val) h)
  · exact Fin.ext (congrArg (fun x => x.destinationAddress.val) h)
  · exact Fin.ext (congrArg (fun x => x.pc.val) h)
  · exact congrArg MicroSnapshot.matchFlag h

set_option Elab.async false

private theorem scanner_code_injective {k n : ℕ} (base : MicroSnapshot)
    (hk : k ≤ runtimeSize*4) (hn : n ≤ runtimeSize+1) :
    Function.Injective (fun q : Scanner k n => snapshotCode (scannerSnapshot base q hk hn)) := by
  intro x y h
  exact (scanner_snapshot_injective base hk hn) (complete_snapshot_encoding h)

/-- The installed instruction graph and addressed bit tapes execute both original updates;
    all intermediate scanner states have the same recoverable fixed charged bound. -/
theorem installed_bounded_program (z : Runtime) (op : Operation) (s : Service) (b : Letter)
    (base : MicroSnapshot) :
    nativeProgram z op = runtimeStep z op ∧ serviceProgram s b = some (microStep s b) ∧
    initializationProgram z = some (entry (selectedThreshold z)) ∧
    (∀ (k n : ℕ) (hk : k ≤ runtimeSize*4) (hn : n ≤ runtimeSize+1) (q : Scanner k n),
      residentCode.length + (snapshotCode (scannerSnapshot base q hk hn)).length < B0) ∧
    (∀ (k n : ℕ) (hk : k ≤ runtimeSize*4) (hn : n ≤ runtimeSize+1),
      Function.Injective (fun q : Scanner k n => snapshotCode (scannerSnapshot base q hk hn))) ∧
    (∀ (r : Registers) (mon : Monitor) (m : Mode) (a b x : Letter),
      runtimeStep ⟨⟨.fourth (.pending a),r⟩,mon,m⟩ (.read x) = none ∧
      (runtimeStep ⟨⟨.fourth (.pending a),r⟩,mon,m⟩ (.stop b)).map Runtime.fields =
        (if b=a then some ⟨.fourth .delivered,r⟩ else none) ∧
      runtimeStep ⟨⟨.fourth .delivered,r⟩,mon,m⟩ (.read x) = none ∧
      runtimeStep ⟨⟨.fourth .delivered,r⟩,mon,m⟩ (.stop b) = none) := by
  have hnd : nativeTable (nativeKeyCodec (z,op)) = optionalRuntimeCodec (runtimeStep z op) := by
    rw [nativeTable, native_resident_row]
    simp only [nativeRowValue, Equiv.symm_apply_apply]
  have hbd : serviceTable (bitKeyCodec (s,b)) = serviceCodec (microStep s b) := by
    rw [serviceTable, service_resident_row]
    simp only [serviceRowValue, Equiv.symm_apply_apply]
  have hn : nativeProgram z op = runtimeStep z op := by
    simpa only [nativeProgram] using decoded_partial_table_correct
      optionalRuntimeCodec nativeTable (nativeKeyCodec (z,op)) (runtimeStep z op) hnd
  have hb : serviceProgram s b = some (microStep s b) := by
    simpa only [serviceProgram] using decoded_table_correct
      serviceCodec serviceTable (bitKeyCodec (s,b)) (microStep s b) hbd
  have hi : initializationProgram z = some (entry (selectedThreshold z)) := by
    have he : initializationTable (runtimeCodec z) = serviceCodec (entry (selectedThreshold z)) := by
      rw [initializationTable, initialization_resident_row]
      simp only [initializationRowValue, runtimeCodec.symm_apply_apply]
    simpa only [initializationProgram] using decoded_table_correct
      serviceCodec initializationTable (runtimeCodec z) (entry (selectedThreshold z)) he
  refine ⟨hn,hb,hi,?_,?_,terminal_permissions⟩
  ·
    intro k n hk hn q
    exact (charged_snapshot_bound (scannerSnapshot base q hk hn)).2.1
  ·
    intro k n hk hn
    exact scanner_code_injective base hk hn

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorResidentCode
