/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformInput
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed common-input decoding and uniform exact native cell materialization. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address Reply)
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (History)
open NativeSerialDepth (RowWord rowWord)
open NativeSerialEffective (originalReplyCode)
open NativeUniformPatterns

/-- The four codes are the existing chronological-event codes 0,1,2,3. -/
def replyEquiv : Reply ≃ Fin 4 where
  toFun r := ⟨originalReplyCode r, by cases r <;> decide⟩
  invFun i := if i.val = 0 then .alpha else if i.val = 1 then .beta
    else if i.val = 2 then .branch else .absent
  left_inv r := by cases r <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance replyPrimcodable : Primcodable Reply :=
  Primcodable.ofEquiv (Fin 4) replyEquiv

abbrev HistoryWord := List (Nat × Address × Nat)
abbrev CommonCode := RowWord × List Address × HistoryWord × Nat
abbrev CommonData := LiteralRow × List Address × History × Nat

/-- Neither semantic consistency nor source reachability is required to encode
an arbitrary finite mixed-epoch computation input. -/
def codeHistory (H : History) : HistoryWord :=
  H.map (fun e => (e.1,e.2.1,originalReplyCode e.2.2))

def parseHistory (w : HistoryWord) : Option History :=
  w.foldr (fun e rest =>
    (Encodable.decode (α := Reply) e.2.2).bind fun r =>
      rest.map fun H => (e.1,e.2.1,r) :: H) (some [])

/-- Q is presented by its native lexicographically sorted finite address list. -/
def codeCommon (C : LiteralRow) (Q : CutSet) (H : History) (N : Nat) : CommonCode :=
  (rowWord C,Q.sort (· ≤ ·),codeHistory H,N)

def parseCommon (w : CommonCode) : Option CommonData := do
  let C ← parse w.1
  let H ← parseHistory w.2.2.1
  some (C,w.2.1,H,w.2.2.2)

private theorem row_word_eq (C : LiteralRow) : rowWord C = word C := by
  induction C using FreeMagma.recOn with
  | of a => rfl
  | mul l r ihl ihr => simp only [rowWord, word, ihl, ihr]

private theorem reply_code_encode (r : Reply) : originalReplyCode r = Encodable.encode r := rfl

private theorem parse_history_primrec : Primrec parseHistory := by
  have hs : Primrec (fun p : (Nat × Address × Nat) × Option History =>
      (Encodable.decode (α := Reply) p.1.2.2).bind fun r =>
        p.2.map fun H => (p.1.1,p.1.2.1,r) :: H) := by
    refine Primrec.option_bind
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) ?_
    change Primrec (fun p : ((Nat × Address × Nat) × Option History) × Reply =>
      p.1.2.map fun H => (p.1.1.1,p.1.1.2.1,p.2) :: H)
    refine Primrec.option_map (Primrec.snd.comp Primrec.fst) ?_
    change Primrec (fun p : (((Nat × Address × Nat) × Option History) × Reply) × History =>
      (p.1.1.1.1,p.1.1.1.2.1,p.1.2) :: p.2)
    exact Primrec.list_cons.comp
      ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))).pair (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const (some []))
    (Primrec.comp hs Primrec.snd).to₂

private theorem parse_history_exact (H : History) : parseHistory (codeHistory H) = some H := by
  induction H with
  | nil => rfl
  | cons e H ih =>
      simp only [codeHistory, List.map_cons, parseHistory, List.foldr_cons]
      simp only [parseHistory, codeHistory] at ih
      rw [reply_code_encode, Encodable.encodek, ih]
      rfl

private theorem parse_row_primrec : Primrec (parse : RowWord → Option LiteralRow) := by
  have h : Primrec (fun w : RowWord => Encodable.decode (α := LiteralRow) (Encodable.encode w)) :=
    Primrec.decode.comp Primrec.encode
  exact h.of_eq (fun w => by
    change (Encodable.decode (α := RowWord) (Encodable.encode w)).bind parse = parse w
    rw [Encodable.encodek]
    rfl)

private theorem parse_common_primrec : Primrec parseCommon := by
  unfold parseCommon
  refine Primrec.option_bind (parse_row_primrec.comp Primrec.fst) ?_
  refine Primrec.option_bind
    (parse_history_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))) ?_
  exact Primrec.option_some.comp
    ((Primrec.snd.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst)))))))

/-- There is one primitive recursive decoder before all input quantifiers.
Every concrete old row, finite Q, mixed history and unbounded N round-trips. -/
theorem uniform_common_codec :
    Primrec parseCommon ∧ ∀ C Q H N,
      parseCommon (codeCommon C Q H N) = some (C,Q.sort (· ≤ ·),H,N) := by
  refine ⟨parse_common_primrec, ?_⟩
  intro C Q H N
  simp only [parseCommon, codeCommon, row_word_eq, (preorder_codec (word C) C).mpr rfl,
    parse_history_exact]
  rfl

/-- The class occurrence stream includes repeated labels; sorting its dedup
retains original numeric names rather than replacing them by dense ranks. -/
def rowNames : LiteralRow → List Nat :=
  @FreeMagma.lift (Bool ⊕ Nat) (List Nat) ⟨List.append⟩
    (fun a => Sum.casesOn a (fun _ => []) (fun n => [n]))

def orderedNames (C : LiteralRow) : List Nat := (rowNames C).dedup.insertionSort (· ≤ ·)

private theorem row_names_primrec : Primrec rowNames := by
  have hl : Primrec (fun a : Bool ⊕ Nat =>
      (Sum.casesOn a (fun _ => []) (fun n => [n]) : List Nat)) :=
    Primrec.sumCasesOn (Primrec.id : Primrec (id : Bool ⊕ Nat → Bool ⊕ Nat))
      (Primrec.const ([] : List Nat)).to₂
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂
  exact (uniform_tree_fold (fun (_ : Nat) (a : Bool ⊕ Nat) =>
      (Sum.casesOn a (fun _ => []) (fun n => [n]) : List Nat))
    (fun (_ : Nat) p => p.1 ++ p.2) (hl.comp Primrec.snd).to₂
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).comp
      (Primrec.const 0) Primrec.id

private theorem ordered_names_primrec : Primrec orderedNames :=
  (primitive_list_algorithms ((· ≤ ·) : Nat → Nat → Prop) Primrec.nat_le).2.comp
    ((primitive_list_algorithms ((· ≤ ·) : Nat → Nat → Prop) Primrec.nat_le).1.comp row_names_primrec)

private theorem row_names_set (C : LiteralRow) : (rowNames C).toFinset = NativeCutFibers.labels C := by
  induction C using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r ihl ihr =>
      change (rowNames l ++ rowNames r).toFinset = _
      rw [List.toFinset_append, ihl, ihr]
      rfl

private theorem ordered_names_exact (C : LiteralRow) :
    orderedNames C = (NativeWholeRowService.classList C).map Subtype.val := by
  have nd : (orderedNames C).Nodup := by
    exact (List.perm_insertionSort (· ≤ ·) (rowNames C).dedup).nodup_iff.mpr (List.nodup_dedup _)
  have set : (orderedNames C).toFinset = NativeCutFibers.labels C := by
    have hp := List.perm_insertionSort (· ≤ ·) (rowNames C).dedup
    have he : (orderedNames C).toFinset = (rowNames C).dedup.toFinset := by
      ext n
      simp only [List.mem_toFinset]
      exact hp.mem_iff
    rw [he]
    have hd : (rowNames C).dedup.toFinset = (rowNames C).toFinset := by
      ext n
      simp only [List.mem_toFinset, List.mem_dedup]
    rw [hd, row_names_set]
  have sorted : (orderedNames C).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have eq := (List.toFinset_sort (r := (· ≤ ·)) nd).mpr sorted
  rw [set] at eq
  unfold NativeWholeRowService.classList
  simp only [List.map_map, Function.comp_def, List.attach_map_subtype_val]
  exact eq.symm

/-- Maxima are taken from finite syntax, without a bound on epoch numbers. -/
def addressDepth (qs : List Address) : Nat := (qs.map List.length).foldr max 0

def inputDepth (Q : List Address) (H : History) : Nat :=
  1 + max (addressDepth Q) (addressDepth (H.map (fun e => e.2.1)))

private theorem address_depth_primrec : Primrec addressDepth :=
  Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.list_length.comp Primrec.snd).to₂)
    (Primrec.const 0) (Primrec.comp Primrec.nat_max Primrec.snd).to₂

private theorem input_depth_primrec : Primrec₂ inputDepth :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_max.comp (address_depth_primrec.comp Primrec.fst)
      (address_depth_primrec.comp (Primrec.list_map Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))

private theorem address_depth_exact (qs : List Address) :
    addressDepth qs = qs.toFinset.sup List.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      change max q.length (addressDepth qs) = _
      rw [ih]
      simp only [List.toFinset_cons, Finset.sup_insert]

private theorem input_depth_exact (Q : CutSet) (H : History) :
    inputDepth (Q.sort (· ≤ ·)) H = NativeHistoryCells.requiredDepth Q H := by
  simp only [inputDepth, address_depth_exact, Finset.sort_toFinset,
    NativeHistoryCells.requiredDepth, ActualCutPartitionRecovery.cutDepth]

abbrev CellCode := Nat × List Nat × List (List PatternWord)

def materializeCells (w : CommonCode) : Option CellCode :=
  (parseCommon w).map fun s =>
    let d := inputDepth s.2.1 s.2.2.1
    let names := orderedNames s.1
    (d,names,vectors (patternWords d) names.length)

/-- The infinite common-input family has a single primitive recursive cell
factory. Its output is the exact current allPatterns list, with unchanged class
order and original required depth; no feasible source witness is an input. -/
theorem uniform_cell_materializer :
    Primrec materializeCells ∧ ∀ C Q H N,
      materializeCells (codeCommon C Q H N) =
        some (NativeHistoryCells.requiredDepth Q H,
          (NativeWholeRowService.classList C).map Subtype.val,
          (NativeWholeRowService.allPatterns C (NativeHistoryCells.requiredDepth Q H)).map familyWord) := by
  constructor
  · unfold materializeCells
    apply Primrec.option_map parse_common_primrec
    have hd : Primrec (fun s : CommonData => inputDepth s.2.1 s.2.2.1) :=
      input_depth_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have hn : Primrec (fun s : CommonData => orderedNames s.1) := ordered_names_primrec.comp Primrec.fst
    exact (hd.pair (hn.pair ((uniform_pattern_families.1).comp
      (Primrec.list_length.comp hn) hd))).comp Primrec.snd
  · intro C Q H N
    rw [materializeCells, uniform_common_codec.2 C Q H N, Option.map_some]
    simp only [input_depth_exact, ordered_names_exact, List.length_map]
    rw [uniform_pattern_families.2]

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
