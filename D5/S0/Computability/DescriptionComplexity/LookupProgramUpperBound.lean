/- GID: D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/LookupProgramUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A lookup compiler bounds the least cost of a total program consistent with a record. -/

import Mathlib.Data.Nat.Find

namespace D5.S0.Computability.DescriptionComplexity.LookupProgramUpperBound

/-- A fixed-overhead compiler from records to consistent total programs. -/
structure LookupCompiler (Record TotalProgram : Type*)
    (consistent : TotalProgram -> Record -> Prop)
    (programCost : TotalProgram -> Nat)
    (recordComplexity : Record -> Nat) (overhead : Nat) where
  compile : Record -> TotalProgram
  compile_consistent : forall record, consistent (compile record) record
  compile_cost_le : forall record,
    programCost (compile record) <= recordComplexity record + overhead

private theorem consistentCostExists {Record TotalProgram : Type*}
    {consistent : TotalProgram -> Record -> Prop}
    {programCost : TotalProgram -> Nat}
    {recordComplexity : Record -> Nat} {overhead : Nat}
    (compiler : LookupCompiler Record TotalProgram consistent programCost
      recordComplexity overhead)
    (record : Record) :
    exists cost, exists program, consistent program record /\ programCost program = cost :=
  ⟨programCost (compiler.compile record), compiler.compile record,
    compiler.compile_consistent record, rfl⟩

/-- The least cost of a total program consistent with a record. The compiler
supplies the lookup program that makes this minimum well-defined. -/
noncomputable def spectrumBottom {Record TotalProgram : Type*}
    {consistent : TotalProgram -> Record -> Prop}
    {programCost : TotalProgram -> Nat}
    {recordComplexity : Record -> Nat} {overhead : Nat}
    (compiler : LookupCompiler Record TotalProgram consistent programCost
      recordComplexity overhead)
    (record : Record) : Nat := by
  classical
  exact Nat.find (consistentCostExists compiler record)

/-- The table-lookup program witnesses that the least consistent total-program
cost is at most the record-description cost plus fixed compiler overhead. -/
theorem lookup_program_upper_bound {Record TotalProgram : Type*}
    {consistent : TotalProgram -> Record -> Prop}
    {programCost : TotalProgram -> Nat}
    {recordComplexity : Record -> Nat} {overhead : Nat}
    (compiler : LookupCompiler Record TotalProgram consistent programCost
      recordComplexity overhead)
    (record : Record) :
    spectrumBottom compiler record <= recordComplexity record + overhead := by
  classical
  unfold spectrumBottom
  exact le_trans
    (Nat.find_min' (consistentCostExists compiler record)
      ⟨compiler.compile record, compiler.compile_consistent record, rfl⟩)
    (compiler.compile_cost_le record)

/-- A concrete one-record lookup compiler witnesses that all hypotheses are
satisfiable and that the bound can be attained at positive cost. -/
example :
    let consistent : Unit -> Unit -> Prop := fun _ _ => True
    let programCost : Unit -> Nat := fun _ => 3
    let recordComplexity : Unit -> Nat := fun _ => 2
    let compiler : LookupCompiler Unit Unit consistent programCost recordComplexity 1 :=
      { compile := fun _ => ()
        compile_consistent := fun _ => trivial
        compile_cost_le := fun _ => by decide }
    programCost (compiler.compile ()) = 3 /\
      spectrumBottom compiler () <= recordComplexity () + 1 := by
  dsimp
  constructor
  · rfl
  · exact lookup_program_upper_bound _ _

end D5.S0.Computability.DescriptionComplexity.LookupProgramUpperBound
