/- GID: D5/S0/Computability/DenseClauseConversion
   generality: G
   mirror-B: D5/B/S0/Computability/DenseClauseConversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S0/Computability/DenseClauseConversion.dense_word_run; instance=D5/S0/Computability/ConventionalClauseWords.comparisonSource
   digest: Paid finite dense-name conversion preserves the independent appearing-variable count. -/


import D5.S0.Computability.DenseClauseExecution
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.BinaryNames
open Turing StateTransition

def denseFormula (F : Conventional.Formula) : UnaryFormula (Conventional.dictionary F).length :=
  F.attach.map fun c => c.val.attach.map fun literal =>
    (⟨(Conventional.dictionary F).idxOf literal.val.1, by
      apply List.idxOf_lt_length_iff.mpr
      apply List.mem_dedup.mpr
      exact List.mem_flatMap.mpr ⟨c.val, c.property,
        List.mem_map.mpr ⟨literal.val, literal.property, rfl⟩⟩⟩, literal.val.2)

def densePrepared (w : List Bool) : Σ n, UnaryFormula n :=
  match Conventional.readWord w with
  | none => ⟨0,[[]]⟩
  | some F => ⟨(Conventional.dictionary F).length,denseFormula F⟩

def denseOutput (w : List Bool) : List Bool := sourceWord (densePrepared w).2

def unaryStandard {n : Nat} (F : UnaryFormula n) : Std.Sat.CNF (Fin n) := ⟨F.toArray⟩
def unaryCount {n : Nat} (F : UnaryFormula n) : Nat :=
  (Finset.univ.filter (fun a : Fin n → Bool => (unaryStandard F).eval a = true)).card

/-- Every raw conventional word is parsed, densely renamed and returned by
one fixed finite machine. The returned explicit-universe source is decodable,
preserves the independently defined appearing-name assignment count, and has
quadratic output growth and a directly charged quadratic execution bound. -/
theorem dense_word_run (w : List Bool) :
    Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
      (some (haltList denseMachine (denseOutput w))) (80*(w.length+1)^2)) ∧
    (denseOutput w).length ≤ w.length^2+8*w.length+7 ∧
    ClauseCodec.readWord false (denseOutput w) = some (densePrepared w) ∧
    (∀ c ∈ (densePrepared w).2, c.length ≤ 3) ∧
    unaryCount (densePrepared w).2 = Conventional.rawCount w := by
  have operational : ∀ w : List Bool,
      Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
        (some (haltList denseMachine (denseConverted w))) (denseRunClock w)) :=
    fun w => (denseExecution w).1
  have shape : ∀ (w : List Bool) (F : Conventional.Formula),
      Conventional.readWord w = some F →
      w = Conventional.formulaWord F ∧ ∀ c ∈ F, c.length ≤ 3 :=
    fun w => (denseExecution w).2
  have counted : ∀ F : Conventional.Formula,
      unaryCount (denseFormula F) = Conventional.satisfyingCount F := by
    intro F
    classical
    let dictionary := Conventional.dictionary F
    let names : Fin dictionary.length ≃ Conventional.Appearing F :=
      (List.Nodup.getEquiv dictionary (List.nodup_dedup _)).trans
        (Equiv.subtypeEquivRight (fun _ => List.mem_dedup))
    let assignments : (Fin dictionary.length → Bool) ≃ (Conventional.Appearing F → Bool) :=
      Equiv.arrowCongr names (Equiv.refl Bool)
    let source : List (Std.Sat.CNF.Clause (Conventional.Appearing F)) :=
      F.attach.map fun c => c.val.attach.map fun literal =>
        (⟨literal.val.1, List.mem_flatMap.mpr ⟨c.val,c.property,
          List.mem_map.mpr ⟨literal.val,literal.property,rfl⟩⟩⟩,literal.val.2)
    let standard : Std.Sat.CNF (Conventional.Appearing F) := ⟨source.toArray⟩
    have relabelled : Std.Sat.CNF.relabel names.symm standard =
        unaryStandard (denseFormula F) := by
      have lists : source.map (Std.Sat.CNF.Clause.relabel names.symm) = denseFormula F := by
        simp [source,denseFormula,Std.Sat.CNF.Clause.relabel,List.map_map,
          names,dictionary,Conventional.dictionary,Equiv.trans,Equiv.subtypeEquivRight,
          Equiv.subtypeEquiv,List.Nodup.getEquiv]
        all_goals
          intro c _ name
          constructor <;> intro
          all_goals
            dsimp only [List.idxOf]
            congr 1
            funext x
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq]
      have arrays := congrArg (fun clauses : List (Std.Sat.CNF.Clause (Fin dictionary.length)) =>
        (⟨clauses.toArray⟩ : Std.Sat.CNF (Fin dictionary.length))) lists
      simpa only [Std.Sat.CNF.relabel,standard,unaryStandard,List.map_toArray] using arrays
    have listArray : ∀ a, standard.eval a = Conventional.evaluate F a := by
      intro a
      have clauseEval : ∀ c : {c // c ∈ F},
          Std.Sat.CNF.Clause.eval a (c.val.attach.map fun literal =>
            (⟨literal.val.1, List.mem_flatMap.mpr ⟨c.val,c.property,
              List.mem_map.mpr ⟨literal.val,literal.property,rfl⟩⟩⟩,
              literal.val.2)) =
            c.val.eval (Conventional.extendAssignment F a) := by
        intro c
        rw [Bool.eq_iff_iff]
        simp only [Std.Sat.CNF.Clause.eval,List.any_map,List.any_eq_true]
        constructor
        · rintro ⟨literal,_,sat⟩
          refine ⟨literal.val,literal.property,?_⟩
          have appearing : literal.val.1 ∈ Conventional.occurrences F :=
            List.mem_flatMap.mpr ⟨c.val,c.property,
              List.mem_map.mpr ⟨literal.val,literal.property,rfl⟩⟩
          simpa [Conventional.extendAssignment,appearing] using sat
        · rintro ⟨literal,member,sat⟩
          refine ⟨⟨literal,member⟩,by simp,?_⟩
          have appearing : literal.1 ∈ Conventional.occurrences F :=
            List.mem_flatMap.mpr ⟨c.val,c.property,List.mem_map.mpr ⟨literal,member,rfl⟩⟩
          simpa [Conventional.extendAssignment,appearing] using sat
      rw [Bool.eq_iff_iff]
      simp only [standard,Std.Sat.CNF.eval,List.all_toArray,source,List.all_map,
        List.all_eq_true,Conventional.evaluate]
      constructor
      · intro sat c member
        have hc := sat ⟨c,member⟩ (by simp)
        exact (clauseEval ⟨c,member⟩).symm.trans (by simpa only [Function.comp_apply] using hc)
      · intro sat c _
        simpa only [Function.comp_apply] using (clauseEval c).trans (sat c.val c.property)
    have evaluation : ∀ a : Fin dictionary.length → Bool,
        (unaryStandard (denseFormula F)).eval a =
          Conventional.evaluate F (assignments a) := by
      intro a
      rw [← relabelled,Std.Sat.CNF.eval_relabel]
      exact listArray (assignments a)
    let satisfying := Equiv.subtypeEquiv
      (p := fun a : Fin dictionary.length → Bool => (unaryStandard (denseFormula F)).eval a = true)
      (q := fun a : Conventional.Appearing F → Bool => Conventional.evaluate F a = true)
      assignments (fun a => by
      change (unaryStandard (denseFormula F)).eval a = true ↔
        Conventional.evaluate F (assignments a) = true
      rw [evaluation a])
    have transported := Fintype.card_congr satisfying
    have leftCard : Fintype.card {a : Fin dictionary.length → Bool //
        (unaryStandard (denseFormula F)).eval a = true} =
        unaryCount (denseFormula F) := by
      apply Fintype.card_of_subtype (Finset.univ.filter fun a =>
        (unaryStandard (denseFormula F)).eval a = true)
      intro a
      simp
    have rightCard : Fintype.card {a : Conventional.Appearing F → Bool //
        Conventional.evaluate F a = true} = Conventional.satisfyingCount F := by
      apply Fintype.card_of_subtype (Finset.univ.filter fun a => Conventional.evaluate F a = true)
      intro a
      simp
    exact leftCard.symm.trans (transported.trans rightCard)
  have estimates : ∀ (F : Conventional.Formula),
    let d := Conventional.dictionary F
    let L := (Conventional.formulaWord F).length
    let S := (dictionaryStream (Conventional.occurrences F)).length
    4*L+5+1+20*(S+1)^2+(d.length+1)+
      ((F.map (denseClauseClock d)).sum+2)+((dictionaryStream d).length+1)+
      ((denseRawWord d F).length+1) ≤ 80*(L+1)^2 ∧
    (denseRawWord d F).length ≤ L^2+8*L+3 := by
    intro F
    dsimp only
    let mass (names : List Conventional.Name) := (names.map List.length).sum
    let indices (names : List Conventional.Name) :=
      (names.map (fun name => (Conventional.dictionary F).idxOf name)).sum
    let names := Conventional.occurrences F
    let d := Conventional.dictionary F
    let L := (Conventional.formulaWord F).length
    have streamSize : ∀ ns : List Conventional.Name,
        (dictionaryStream ns).length = 2*mass ns+ns.length := by
      intro ns
      induction ns with
      | nil => simp [dictionaryStream,mass]
      | cons name ns ih =>
        simp only [dictionaryStream,List.flatMap_cons,List.length_append,
          Conventional.nameWord,List.length_cons,List.length_nil,List.length_flatMap,
          List.map_cons,List.sum_cons] at *
        have pairs : ∀ bits : List Bool,
            (bits.reverse.flatMap (fun b => [true,b])).length = 2*bits.length := by
          intro bits
          simp [List.length_flatMap,List.length_reverse,List.map_const,List.sum_replicate,Nat.mul_comm]
        dsimp [mass] at *
        simp [dictionaryStream, List.length_flatMap, List.map_const, List.sum_replicate,
          List.length_reverse, mass] at ih ⊢
        omega
    have literalSize : ∀ c : Std.Sat.CNF.Clause Conventional.Name,
        (c.flatMap Conventional.literalWord).length =
          2*mass (c.map Prod.fst)+4*c.length := by
      intro c
      induction c with
      | nil => simp [mass]
      | cons literal c ih =>
        simp [Conventional.literalWord,Conventional.nameWord,List.length_flatMap,
          List.map_const,List.sum_replicate,mass,ih]
        omega
    have size : ∀ f : Conventional.Formula,
        (Conventional.formulaWord f).length =
          2*mass (Conventional.occurrences f)+4*(Conventional.occurrences f).length+
            4*f.length+2 := by
      intro f
      induction f with
      | nil => simp [Conventional.formulaWord,Conventional.occurrences,mass]
      | cons c f ih =>
        have h := literalSize c
        simp [Conventional.formulaWord,Conventional.clauseWord,Conventional.occurrences,
          mass,List.map_append,List.sum_append] at ih h ⊢
        omega
    have indexLe : ∀ ns : List Conventional.Name, indices ns ≤ ns.length*d.length := by
      intro ns
      induction ns with
      | nil => simp [indices]
      | cons name ns ih =>
        have one := List.idxOf_le_length (l := d) (a := name)
        simp only [indices,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
        dsimp [d] at one
        nlinarith
    have denseLiterals : ∀ c : Std.Sat.CNF.Clause Conventional.Name,
        (c.flatMap (denseLiteralWord d)).length = indices (c.map Prod.fst)+4*c.length := by
      intro c
      induction c with
      | nil => simp [indices]
      | cons literal c ih =>
        simp [denseLiteralWord,indices,d,ih]
        omega
    have denseSize : ∀ f : Conventional.Formula,
        (denseRawWord d f).length = d.length+indices (Conventional.occurrences f)+
          4*(Conventional.occurrences f).length+4*f.length+3 := by
      intro f
      have bodySize : ∀ f : Conventional.Formula,
          (denseBodyWord d f).length = indices (Conventional.occurrences f)+
            4*(Conventional.occurrences f).length+4*f.length+2 := by
        intro f
        induction f with
        | nil => simp [denseBodyWord,Conventional.occurrences,indices]
        | cons c f ih =>
          have hc := denseLiterals c
          simp [denseBodyWord,denseClauseWord,Conventional.occurrences,indices,
            List.map_append,List.sum_append] at ih hc ⊢
          omega
      simp [denseRawWord,bodySize f,Nat.add_assoc]
    have literalClock : ∀ c : Std.Sat.CNF.Clause Conventional.Name,
        (c.map (denseLiteralClock d)).sum =
          (2*mass (c.map Prod.fst)+12*c.length)*d.length+
            4*c.length*(dictionaryStream d).length+4*mass (c.map Prod.fst)+
            indices (c.map Prod.fst)+11*c.length := by
      intro c
      induction c with
      | nil => simp [mass,indices]
      | cons literal c ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,mass,indices] at ih ⊢
        rw [ih]
        dsimp [denseLiteralClock,d,indices,mass]
        ring
    have bodyClock : ∀ f : Conventional.Formula,
        (f.map (denseClauseClock d)).sum+2 =
          (2*mass (Conventional.occurrences f)+12*(Conventional.occurrences f).length)*d.length+
            4*(Conventional.occurrences f).length*(dictionaryStream d).length+
            4*mass (Conventional.occurrences f)+indices (Conventional.occurrences f)+
            11*(Conventional.occurrences f).length+4*f.length+2 := by
      intro f
      induction f with
      | nil => simp [Conventional.occurrences,mass,indices]
      | cons c f ih =>
        have hc := literalClock c
        simp only [List.map_cons,List.sum_cons,denseClauseClock,
          Conventional.occurrences,List.flatMap_cons,List.length_append,
          List.length_map,List.length_cons,mass,List.map_append,List.sum_append,
          indices] at ih hc ⊢
        nlinarith
    have hL := size F
    have hs := streamSize names
    have hd : List.Sublist d names := List.dedup_sublist _
    have hn : d.length ≤ names.length := hd.length_le
    have hm : mass d ≤ mass names :=
      (hd.map List.length).sum_le_sum (fun _ _ => Nat.zero_le _)
    have hw := streamSize d
    have hi := indexLe names
    have hU := denseSize F
    have hC := bodyClock F
    have haL : mass names ≤ L := by dsimp [names,L] at *; omega
    have htL : names.length ≤ L := by dsimp [names,L] at *; omega
    have hnL : d.length ≤ L := hn.trans htL
    have hmL : F.length ≤ L := by dsimp [names,L] at *; omega
    have hsL : (dictionaryStream names).length ≤ L := by dsimp [names,L] at *; omega
    have hwL : (dictionaryStream d).length ≤ L := by omega
    have hiL : indices names ≤ L^2 := by
      have product := Nat.mul_le_mul htL hnL
      nlinarith
    have uBound : (denseRawWord d F).length ≤ L^2+8*L+3 := by
      dsimp only [names] at hiL hnL htL
      nlinarith
    have cBound : (F.map (denseClauseClock d)).sum+2 ≤ 19*L^2+19*L+2 := by
      have an := Nat.mul_le_mul haL hnL
      have tn := Nat.mul_le_mul htL hnL
      have tw := Nat.mul_le_mul htL hwL
      dsimp [names] at hiL haL htL hnL
      nlinarith
    have builderBound : 20*((dictionaryStream names).length+1)^2 ≤ 20*(L+1)^2 := by
      nlinarith [Nat.mul_le_mul (Nat.add_le_add_right hsL 1) (Nat.add_le_add_right hsL 1)]
    constructor
    · change 4*L+5+1+20*((dictionaryStream names).length+1)^2+(d.length+1)+
        ((F.map (denseClauseClock d)).sum+2)+((dictionaryStream d).length+1)+
        ((denseRawWord d F).length+1) ≤ 80*(L+1)^2
      nlinarith
    · exact uBound
  have spelling : ∀ F : Conventional.Formula,
      denseRawWord (Conventional.dictionary F) F = sourceWord (denseFormula F) := by
    intro F
    simp [sourceWord,denseRawWord,denseBodyWord,denseClauseWord,denseLiteralWord,
      denseFormula,unaryClause,unaryLiteral,List.flatMap_map,List.attach_map_val,
      List.flatMap_append,List.append_assoc,List.map_map,Function.comp_def]
    apply List.flatMap_congr
    intro c _
    simp [denseClauseWord,denseLiteralWord]
    change c.flatMap (denseLiteralWord (Conventional.dictionary F)) =
      c.attach.flatMap (fun a => denseLiteralWord (Conventional.dictionary F) a.val)
    symm
    simpa only [List.unattach_attach] using
      (List.flatMap_subtype (l := c.attach)
        (f := fun a => denseLiteralWord (Conventional.dictionary F) a.val)
        (g := denseLiteralWord (Conventional.dictionary F)) (fun _ _ => rfl))
  cases read : Conventional.readWord w with
  | none =>
    have preparedEq : densePrepared w = ⟨0,([[]] : UnaryFormula 0)⟩ := by
      unfold densePrepared
      rw [read]
    have outputEq : denseOutput w = dummySource := by
      unfold denseOutput
      rw [preparedEq]
      rfl
    rw [outputEq,preparedEq]
    have fallbackCheck : ClauseCodec.readWord false dummySource =
        some ⟨0,([[]] : UnaryFormula 0)⟩ := rfl
    have fallbackSound := (ClauseCodec.codec_exact false dummySource 0
      ([[]] : UnaryFormula 0)).mp fallbackCheck
    have run := Classical.choice (operational w)
    have bounded : Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
        (some (haltList denseMachine dummySource)) (80*(w.length+1)^2)) := by
      refine ⟨{steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_}⟩
      · simpa [denseConverted,denseOutput,preparedEq,read,dummySource,sourceWord,
          unaryClause,unaryLiteral] using run.evals_in_steps
      · have bound := run.steps_le_m
        simp only [denseRunClock,read] at bound
        nlinarith
    refine ⟨bounded,?_,?_,?_,?_⟩
    · simp only [dummySource,sourceWord,unaryClause,List.replicate_zero,
        List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.length_cons,List.length_nil,List.length_append]
      omega
    · simpa [denseOutput,preparedEq,read,dummySource] using fallbackCheck
    · simpa [preparedEq,read] using fallbackSound.2
    · have zero : unaryCount ([[]] : UnaryFormula 0) = 0 := by
        simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
      simpa [preparedEq,read,Conventional.rawCount] using zero
  | some F =>
    have preparedEq : densePrepared w = ⟨(Conventional.dictionary F).length,denseFormula F⟩ := by
      unfold densePrepared
      rw [read]
    have outputEq : denseOutput w = sourceWord (denseFormula F) := by
      unfold denseOutput
      rw [preparedEq]
    rw [outputEq,preparedEq]
    obtain ⟨encoded,width⟩ := shape w F read
    have widthDense : ∀ c ∈ denseFormula F, c.length ≤ 3 := by
      intro c member
      obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
      simpa using width source.val source.property
    have sourceEq : ClauseCodec.encodeWord false (denseFormula F) =
        sourceWord (denseFormula F) := by
      have general : ∀ (n : Nat) (G : UnaryFormula n),
          ClauseCodec.encodeWord false G = sourceWord G := by
        intro n G
        induction G with
        | nil => simp [ClauseCodec.encodeWord,ClauseCodec.bodyWord,sourceWord,List.append_assoc]
        | cons c G ih =>
          simpa [ClauseCodec.encodeWord,ClauseCodec.bodyWord,ClauseCodec.termWord,
            sourceWord,unaryClause,List.append_assoc] using ih
      exact general _ _
    have decoded := (ClauseCodec.codec_exact false (sourceWord (denseFormula F))
      (Conventional.dictionary F).length (denseFormula F)).mpr ⟨sourceEq.symm,widthDense⟩
    have amount := estimates F
    have run := Classical.choice (operational w)
    have bounded : Nonempty (EvalsToInTime denseMachine.step (initList denseMachine w)
        (some (haltList denseMachine (sourceWord (denseFormula F)))) (80*(w.length+1)^2)) := by
      refine ⟨{steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_}⟩
      · simpa [denseConverted,denseOutput,preparedEq,read,spelling F]
          using run.evals_in_steps
      · have bound := run.steps_le_m
        have maximum := amount.1
        simp only [denseRunClock,read] at bound
        rw [← encoded] at maximum
        exact bound.trans maximum
    refine ⟨bounded,?_,?_,?_,?_⟩
    · have bound := amount.2
      rw [← encoded,spelling F] at bound
      simpa [denseOutput,preparedEq,read] using
        bound.trans (by omega : w.length^2+8*w.length+3 ≤ w.length^2+8*w.length+7)
    · simpa [denseOutput,preparedEq,read] using decoded
    · simpa [preparedEq,read] using widthDense
    · simpa [preparedEq,read,Conventional.rawCount] using counted F
end PredictiveThermodynamic.BinaryNames
