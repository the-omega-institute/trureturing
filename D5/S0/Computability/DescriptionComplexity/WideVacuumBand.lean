/- GID: D5/S0/Computability/DescriptionComplexity/WideVacuumBand
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/WideVacuumBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite low-cost cover leaves records with an unbounded spectrum gap. -/

import Mathlib
import D5.S0.Computability.DescriptionComplexity.LookupProgramUpperBound

open scoped BigOperators

namespace D5.S0.Computability.DescriptionComplexity.WideVacuumBand

open LookupProgramUpperBound

/-- If every low-cost total program belongs to a finite family whose consistency
fibers do not cover the admissible records, then binary records have arbitrarily
large gaps between entry cost and least consistent-program cost. -/
theorem arbitrarily_wide_vacuum_band
    {Record TotalProgram : Type*}
    {consistent : TotalProgram -> Record -> Prop}
    {programCost : TotalProgram -> Nat}
    {recordComplexity : Record -> Nat}
    {compilerOverhead : Nat}
    (compiler : LookupCompiler Record TotalProgram consistent programCost
      recordComplexity compilerOverhead)
    (records : Nat -> Finset Record)
    (simplePrograms : Nat -> Finset TotalProgram)
    (consistentRecords : Nat -> TotalProgram -> Finset Record)
    (recordSize entryCost : Record -> Nat)
    (binaryCoordinates : Record -> Prop)
    (entryBound spectrumDefect : Nat)
    (records_structured : forall n, 2 <= n -> forall record, record ∈ records n ->
      recordSize record = n /\ binaryCoordinates record /\ entryCost record <= entryBound)
    (lowCost_listed : forall n program,
      programCost program < n - spectrumDefect -> program ∈ simplePrograms n)
    (consistentRecords_spec : forall n program record,
      record ∈ consistentRecords n program <->
        record ∈ records n /\ consistent program record)
    (consistency_sum_small : forall n, 2 <= n ->
      (∑ program ∈ simplePrograms n, (consistentRecords n program).card) <
        (records n).card) :
    exists c0 c1,
      (forall n, 2 <= n -> exists record, record ∈ records n /\
        recordSize record = n /\ binaryCoordinates record /\ entryCost record <= c0 /\
        n - c1 <= spectrumBottom compiler record /\
        n - c0 - c1 <= spectrumBottom compiler record - entryCost record) /\
      forall width, exists n, 2 <= n /\ exists record, record ∈ records n /\
        recordSize record = n /\ binaryCoordinates record /\ entryCost record <= c0 /\
        n - c1 <= spectrumBottom compiler record /\
        width <= spectrumBottom compiler record - entryCost record := by
  classical
  have hrecord : forall n, 2 <= n -> exists record, record ∈ records n /\
      recordSize record = n /\ binaryCoordinates record /\
      entryCost record <= entryBound /\
      n - spectrumDefect <= spectrumBottom compiler record /\
      n - entryBound - spectrumDefect <=
        spectrumBottom compiler record - entryCost record := by
    intro n hn
    have hcovered_card :
        ((simplePrograms n).biUnion (consistentRecords n)).card <=
          ∑ program ∈ simplePrograms n, (consistentRecords n program).card :=
      Finset.card_biUnion_le
    have huncovered : exists record, record ∈ records n /\
        record ∉ (simplePrograms n).biUnion (consistentRecords n) := by
      by_contra hall
      have hsubset : records n ⊆
          (simplePrograms n).biUnion (consistentRecords n) := by
        intro record hrecord_mem
        by_contra huncovered
        exact hall ⟨record, hrecord_mem, huncovered⟩
      have hle : (records n).card <=
          ∑ program ∈ simplePrograms n, (consistentRecords n program).card :=
        (Finset.card_le_card hsubset).trans hcovered_card
      exact (Nat.not_lt_of_ge hle) (consistency_sum_small n hn)
    obtain ⟨record, hrecord_mem, huncovered⟩ := huncovered
    have hprogram_floor : forall program, consistent program record ->
        n - spectrumDefect <= programCost program := by
      intro program hconsistent
      by_contra hfloor
      have hcost : programCost program < n - spectrumDefect :=
        Nat.lt_of_not_ge hfloor
      have hlisted := lowCost_listed n program hcost
      apply huncovered
      exact Finset.mem_biUnion.mpr
        ⟨program, hlisted, (consistentRecords_spec n program record).mpr
          ⟨hrecord_mem, hconsistent⟩⟩
    let costExists : exists cost : Nat, exists program : TotalProgram,
        consistent program record /\ programCost program = cost :=
      ⟨programCost (compiler.compile record), compiler.compile record,
        compiler.compile_consistent record, rfl⟩
    have hbottom_eq : spectrumBottom compiler record = Nat.find costExists := by
      unfold spectrumBottom
      rfl
    obtain ⟨program, hconsistent, hcost⟩ := Nat.find_spec costExists
    have hbottom : n - spectrumDefect <= spectrumBottom compiler record := by
      rw [hbottom_eq, <- hcost]
      exact hprogram_floor program hconsistent
    obtain ⟨hsize, hbinary, hentry⟩ :=
      records_structured n hn record hrecord_mem
    have hband : n - entryBound - spectrumDefect <=
        spectrumBottom compiler record - entryCost record := by
      omega
    exact ⟨record, hrecord_mem, hsize, hbinary, hentry, hbottom, hband⟩
  refine ⟨entryBound, spectrumDefect, hrecord, ?_⟩
  intro width
  let n := width + entryBound + spectrumDefect + 2
  have hn : 2 <= n := by
    simp [n]
  obtain ⟨record, hrecord_mem, hsize, hbinary, hentry, hbottom, hband⟩ :=
    hrecord n hn
  refine ⟨n, hn, record, hrecord_mem, hsize, hbinary, hentry, hbottom, ?_⟩
  have hwidth : width <= n - entryBound - spectrumDefect := by
    dsimp [n]
    omega
  exact hwidth.trans hband

/-- A singleton record family with threshold consistency witnesses that all
hypotheses are jointly satisfiable and realizes positive, unbounded gaps. -/
example :
    let consistent : Nat -> Nat -> Prop := fun program record => record <= program
    let programCost : Nat -> Nat := id
    let recordComplexity : Nat -> Nat := id
    let compiler : LookupCompiler Nat Nat consistent programCost recordComplexity 0 :=
      { compile := id
        compile_consistent := fun record => Nat.le_refl record
        compile_cost_le := fun record => Nat.le_refl record }
    let records : Nat -> Finset Nat := fun n => {n}
    let recordSize : Nat -> Nat := id
    let entryCost : Nat -> Nat := fun _ => 0
    exists c0 c1,
      (forall n, 2 <= n -> exists record, record ∈ records n /\
        recordSize record = n /\ True /\ entryCost record <= c0 /\
        n - c1 <= spectrumBottom compiler record /\
        n - c0 - c1 <= spectrumBottom compiler record - entryCost record) /\
      forall width, exists n, 2 <= n /\ exists record, record ∈ records n /\
        recordSize record = n /\ True /\ entryCost record <= c0 /\
        n - c1 <= spectrumBottom compiler record /\
        width <= spectrumBottom compiler record - entryCost record := by
  dsimp
  apply arbitrarily_wide_vacuum_band
    (simplePrograms := fun n => Finset.range n)
    (consistentRecords := fun n program =>
      ({n} : Finset Nat).filter (fun record => record <= program))
    (entryBound := 0) (spectrumDefect := 0)
  · intro n hn record hrecord
    simp at hrecord
    subst record
    simp
  · intro n program hcost
    simpa using hcost
  · intro n program record
    simp
  · intro n hn
    calc
      (∑ program ∈ Finset.range n,
          (({n} : Finset Nat).filter (fun record => record <= program)).card) = 0 := by
        apply Finset.sum_eq_zero
        intro program hprogram
        have hlt : program < n := Finset.mem_range.mp hprogram
        simp [hlt]
      _ < ({n} : Finset Nat).card := by simp

end D5.S0.Computability.DescriptionComplexity.WideVacuumBand
