/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformVariables
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform structural variable tables and exact native presentation ordinals. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables

open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (LiteralRow)
open NativeDepthPatterns (Pattern Frontier frontierAddress)
open NativeHistoryCells (Patterns Variables)
open NativeWholeRowService (classList frontierList variableList presentation)
open NativeUniformPatterns
open NativeUniformInput
open NativeTermUnification (finName)
open D5.S0.Computability.PreorderTreeEvaluation (primitive_list_algorithms)

abbrev VariableKey := Nat × Address

def variableKey {C : LiteralRow} {d : Nat} {η : Patterns C d}
    (x : Variables η) : VariableKey := (x.1.val,frontierAddress (η x.1) x.2)

theorem frontier_injective {d : Nat} (p : Pattern d) :
    Function.Injective (frontierAddress p) := by
  intro x y h
  by_contra ne
  let f : Frontier p → FreeMagma Bool :=
    fun z => if z = x then .of false else .of true
  have hx := (NativeDepthPatterns.frontier_geometry d p).2.1 f x
  have hy := (NativeDepthPatterns.frontier_geometry d p).2.1 f y
  rw [h, hy] at hx
  have yne : y ≠ x := Ne.symm ne
  simp [f, yne] at hx
  cases hx

private theorem variable_key_injective {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    Function.Injective (variableKey (η := η)) := by
  intro x y h
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  have bc : b = c := Subtype.ext (congrArg Prod.fst h)
  subst c
  have xy : x = y := frontier_injective (η b) (congrArg Prod.snd h)
  subst y
  rfl

/-- A class name and the actual reached relative address form the variable key. -/
def namedFrontier (n : Nat) (w : PatternWord) : Option (List VariableKey) :=
  (frontierWords w).map (List.map (fun a => (n,a)))

private theorem named_frontier_primrec : Primrec₂ namedFrontier := by
  unfold namedFrontier
  refine Primrec.option_map (uniform_frontier_words.1.comp Primrec.snd) ?_
  change Primrec (fun p : (Nat × PatternWord) × List Address =>
    p.2.map (fun a => (p.1.1,a)))
  exact Primrec.list_map Primrec.snd
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)

/-- An explicit finite cursor consumes the class-ordered pattern vector. -/
def keyStep (s : List PatternWord × Option (List VariableKey)) (n : Nat) :
    List PatternWord × Option (List VariableKey) :=
  (s.1.tail, s.1.head?.bind fun w =>
    (namedFrontier n w).bind fun ks => s.2.map (fun acc => acc ++ ks))

def variableKeys (names : List Nat) (ws : List PatternWord) : Option (List VariableKey) :=
  ((names.foldl keyStep (ws,some [])).2).map List.dedup

private theorem key_step_primrec : Primrec₂ keyStep := by
  unfold keyStep
  refine (Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst)).pair ?_
  refine Primrec.option_bind
    (Primrec.list_head?.comp (Primrec.fst.comp Primrec.fst)) ?_
  change Primrec (fun p : ((List PatternWord × Option (List VariableKey)) × Nat) × PatternWord =>
    (namedFrontier p.1.2 p.2).bind fun ks => p.1.1.2.map (fun acc => acc ++ ks))
  refine Primrec.option_bind
    (named_frontier_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) ?_
  change Primrec (fun p :
      (((List PatternWord × Option (List VariableKey)) × Nat) × PatternWord) × List VariableKey =>
    p.1.1.1.2.map (fun acc => acc ++ p.2))
  refine Primrec.option_map (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) ?_
  change Primrec (fun p :
      ((((List PatternWord × Option (List VariableKey)) × Nat) × PatternWord) × List VariableKey) × List VariableKey =>
    p.2 ++ p.1.2)
  exact Primrec.list_append.comp Primrec.snd (Primrec.snd.comp Primrec.fst)

private theorem variable_keys_primrec : Primrec₂ variableKeys := by
  unfold variableKeys
  refine Primrec.option_map
    (Primrec.snd.comp (Primrec.list_foldl Primrec.fst
      (Primrec.snd.pair (Primrec.const (some [])))
      (Primrec.comp key_step_primrec Primrec.snd).to₂)) ?_
  exact ((primitive_list_algorithms ((· = ·) : VariableKey → VariableKey → Prop)
    Primrec.eq).1.comp Primrec.snd).to₂

private theorem keys_fold_exact {C : LiteralRow} {d : Nat} (η : Patterns C d)
    (bs : List (NativeCutFibers.Classes C)) (acc : List VariableKey) :
    (bs.map Subtype.val).foldl keyStep (bs.map (fun b => patternWord (η b)),some acc) =
      ([],some (acc ++ bs.flatMap (fun b =>
        (frontierList (η b)).map (fun x => (b.val,frontierAddress (η b) x))))) := by
  induction bs generalizing acc with
  | nil => simp only [List.map_nil, List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons b bs ih =>
      simp only [List.map_cons, List.foldl_cons, keyStep, List.tail_cons, List.head?_cons,
        Option.bind_some, namedFrontier, uniform_frontier_words.2, Option.map_some]
      rw [ih]
      simp only [List.flatMap_cons, List.map_map, Function.comp_def, List.append_assoc]

private theorem variable_keys_exact {C : LiteralRow} {d : Nat} (η : Patterns C d) :
    variableKeys ((classList C).map Subtype.val) (familyWord η) =
      some ((variableList η).map variableKey) := by
  unfold variableKeys familyWord
  rw [keys_fold_exact]
  simp only [List.nil_append, Option.map_some]
  unfold variableList
  rw [← List.dedup_map_of_injective (variable_key_injective η)]
  simp only [List.map_flatMap, List.map_map, Function.comp_def, variableKey]

/-- Fixed keys give the exact variable list, including every otherwise unused
old class. The primitive recursive assertion is uniform in both finite lists. -/
theorem uniform_variable_table :
    Primrec₂ variableKeys ∧ ∀ C d (η : Patterns C d),
      variableKeys ((classList C).map Subtype.val) (familyWord η) =
        some ((variableList η).map variableKey) :=
  ⟨variable_keys_primrec, fun _ _ η => variable_keys_exact η⟩

abbrev VariableCellCode := Nat × List Nat × List (List PatternWord × List VariableKey)

/-- The native cell materializer now supplies every concrete first-order
variable table, without selecting a source or encoding a dependent closure. -/
def materializeVariableCells (w : CommonCode) : Option VariableCellCode :=
  (materializeCells w).bind fun s =>
    (s.2.2.foldr (fun ws rest => do
      let keys ← variableKeys s.2.1 ws
      let cells ← rest
      some ((ws,keys) :: cells)) (some [])).map fun cells => (s.1,s.2.1,cells)

set_option maxHeartbeats 2000000 in
private theorem variable_cells_primrec : Primrec materializeVariableCells := by
  unfold materializeVariableCells
  refine Primrec.option_bind uniform_cell_materializer.1 ?_
  change Primrec (fun p : CommonCode × CellCode =>
    (p.2.2.2.foldr (fun ws rest => do
      let keys ← variableKeys p.2.2.1 ws
      let cells ← rest
      some ((ws,keys) :: cells)) (some [])).map fun cells => (p.2.1,p.2.2.1,cells))
  refine Primrec.option_map
    (Primrec.list_foldr
      (h := fun (p : CommonCode × CellCode)
        (q : List PatternWord × Option (List (List PatternWord × List VariableKey))) => do
        let keys ← variableKeys p.2.2.1 q.1
        let cells ← q.2
        some ((q.1,keys) :: cells))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const (some [])) ?_) ?_
  · change Primrec (fun p : (CommonCode × CellCode) ×
        (List PatternWord × Option (List (List PatternWord × List VariableKey))) => do
      let keys ← variableKeys p.1.2.2.1 p.2.1
      let cells ← p.2.2
      some ((p.2.1,keys) :: cells))
    refine Primrec.option_bind
      (uniform_variable_table.1.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd)) ?_
    change Primrec (fun p : ((CommonCode × CellCode) ×
        (List PatternWord × Option (List (List PatternWord × List VariableKey)))) ×
        List VariableKey => do
      let cells ← p.1.2.2
      some ((p.1.2.1,p.2) :: cells))
    refine Primrec.option_bind (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) ?_
    change Primrec (fun p : (((CommonCode × CellCode) ×
        (List PatternWord × Option (List (List PatternWord × List VariableKey)))) ×
        List VariableKey) × List (List PatternWord × List VariableKey) =>
      some ((p.1.1.2.1,p.1.2) :: p.2))
    exact Primrec.option_some.comp (Primrec.list_cons.comp
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  · change Primrec (fun p : (CommonCode × CellCode) ×
        List (List PatternWord × List VariableKey) => (p.1.2.1,p.1.2.2.1,p.2))
    exact (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)

private theorem map_variable_cells {C : LiteralRow} {d : Nat}
    (es : List (Patterns C d)) :
    ((es.map familyWord).foldr (fun ws rest => do
      let keys ← variableKeys ((classList C).map Subtype.val) ws
      let cells ← rest
      some ((ws,keys) :: cells)) (some [])) =
      some (es.map (fun η => (familyWord η,(variableList η).map variableKey))) := by
  induction es with
  | nil => rfl
  | cons η es ih =>
      simp only [List.map_cons, List.foldr_cons, uniform_variable_table.2, ih]
      rfl

private theorem variable_ordinal_exact {C : LiteralRow} {d : Nat}
    (η : Patterns C d) (x : Variables η) :
    (presentation η).code x = finName
      (((variableList η).map variableKey).idxOf (variableKey x)) := by
  have he : (((variableList η).map variableKey).idxOf (variableKey x)) =
      (variableList η).idxOf x := by
    unfold List.idxOf
    rw [List.findIdx_map]
    congr 1
    funext y
    simp only [Function.comp_def, beq_iff_eq]
    exact Bool.eq_iff_iff.mpr (by
      simp only [beq_iff_eq]
      exact (variable_key_injective η).eq_iff)
  rw [he]
  rfl

/-- One first-order algorithm reconstructs all actual cell variable tables for
all common inputs, retaining the native enumeration and structural keys. -/
theorem uniform_variable_materializer :
    Primrec materializeVariableCells ∧ ∀ C Q H N,
      materializeVariableCells (codeCommon C Q H N) =
        some (NativeHistoryCells.requiredDepth Q H,
          (classList C).map Subtype.val,
          (NativeWholeRowService.allPatterns C (NativeHistoryCells.requiredDepth Q H)).map
            (fun η => (familyWord η,(variableList η).map variableKey))) ∧
      ∀ (η : Patterns C (NativeHistoryCells.requiredDepth Q H)) (x : Variables η),
        (presentation η).code x = finName
          (((variableList η).map variableKey).idxOf (variableKey x)) := by
  constructor
  · exact variable_cells_primrec
  · intro C Q H N
    constructor
    · rw [materializeVariableCells, uniform_cell_materializer.2 C Q H N]
      simp only [Option.bind_some]
      rw [map_variable_cells]
      rfl
    · exact variable_ordinal_exact

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
