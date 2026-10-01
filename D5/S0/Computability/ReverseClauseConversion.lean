/- GID: D5/S0/Computability/ReverseClauseConversion
   generality: G
   mirror-B: D5/B/S0/Computability/ReverseClauseConversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Computability/DenseClauseConversion, D5/S0/Computability/ReverseClauseMachine]
   utility: kind=checker; basis=consumer=D5/S0/Computability/ReverseClauseConversion.reverse_word_run; instance=D5/S0/Computability/ClauseQueryPreprocessor.dummySource
   digest: Paid finite reverse conversion preserves the complete explicitly declared universe. -/

import D5.S0.Computability.ReverseClauseMachine
import D5.S0.Computability.DenseClauseConversion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PredictiveThermodynamic.ConventionalReverse
open Turing StateTransition
open PredictiveThermodynamic.BinaryNames (unaryCount unaryStandard)

def explicitRawCount (w : List Bool) : Nat :=
  match ClauseCodec.readWord false w with
  | none => 0
  | some value => unaryCount value.2

/-- The fixed reverse word machine converts every explicit unary universe to
canonical appearing binary names, adding tautologies for precisely the declared
variables. Output decoding and assignment count agree on malformed inputs too. -/
theorem reverse_word_run (w : List Bool) :
    Nonempty (EvalsToInTime reverseMachine.step (initList reverseMachine w)
      (some (haltList reverseMachine (convertedWord w))) (10*w.length^2+41*w.length+33)) ∧
    (convertedWord w).length ≤ 4*w.length^2+14*w.length+6 ∧
    Conventional.readWord (convertedWord w) = some (saturatedFormula (preparedFormula w).2) ∧
    Conventional.rawCount (convertedWord w) = explicitRawCount w := by
  have counted : ∀ (n : Nat) (F : UnaryFormula n),
      Conventional.satisfyingCount (saturatedFormula F) = unaryCount F := by
    intro n F
    classical
    let S := saturatedFormula F
    have present : ∀ i : Fin n, variableName i.val ∈ Conventional.occurrences S := by
      intro i
      apply List.mem_flatMap.mpr
      refine ⟨[(variableName i.val,true),(variableName i.val,false)],?_,by simp⟩
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨i,by simp,rfl⟩
    let naming : Fin n → Conventional.Appearing S := fun i => ⟨variableName i.val,present i⟩
    have injective : Function.Injective naming := by
      intro i j equal
      have spelling := congrArg (fun v : Conventional.Appearing S => v.val.length) equal
      simp only [naming,variableName,List.length_cons,List.length_replicate] at spelling
      exact Fin.ext (by omega)
    have surjective : Function.Surjective naming := by
      intro name
      obtain ⟨clause,member,occurs⟩ := List.mem_flatMap.mp name.property
      rcases List.mem_append.mp member with member | member
      · obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp member
        obtain ⟨literal,literalMember,equal⟩ := List.mem_map.mp occurs
        obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp literalMember
        refine ⟨original.1,?_⟩
        apply Subtype.ext
        exact equal
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
        simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at occurs
        refine ⟨i,?_⟩
        apply Subtype.ext
        rcases occurs with equal | equal <;> exact equal.symm
    let names : Fin n ≃ Conventional.Appearing S := Equiv.ofBijective naming ⟨injective,surjective⟩
    let assignments : (Fin n → Bool) ≃ (Conventional.Appearing S → Bool) :=
      Equiv.arrowCongr names (Equiv.refl Bool)
    have values : ∀ (a : Fin n → Bool) (i : Fin n),
        Conventional.extendAssignment S (assignments a) (variableName i.val) = a i := by
      intro a i
      simp only [Conventional.extendAssignment,present i,↓reduceDIte]
      change (assignments a) (names i) = a i
      change a (names.symm (names i)) = a i
      rw [names.symm_apply_apply]
    have split : ∀ r : Conventional.Name → Bool,
        S.all (fun c => Std.Sat.CNF.Clause.eval r c) =
          (F.all (fun c => Std.Sat.CNF.Clause.eval r (c.map renamedLiteral)) &&
            (List.finRange n).all (fun i => Std.Sat.CNF.Clause.eval r
              [(variableName i.val,true),(variableName i.val,false)])) := by
      intro r
      dsimp only [S,saturatedFormula,renamedLiteral]
      simp only [List.all_append,List.all_map,Function.comp_def]
      rfl
    have evaluation : ∀ a : Fin n → Bool,
        Conventional.evaluate S (assignments a) = (unaryStandard F).eval a := by
      intro a
      have clause : ∀ c : Std.Sat.CNF.Clause (Fin n),
          Std.Sat.CNF.Clause.eval (Conventional.extendAssignment S (assignments a)) (c.map renamedLiteral) = c.eval a := by
        intro c
        simp only [Std.Sat.CNF.Clause.eval,List.any_map]
        apply List.any_congr rfl
        intro literal
        simp [renamedLiteral,values a literal.1]
      have taut : ∀ i : Fin n,
          Std.Sat.CNF.Clause.eval (Conventional.extendAssignment S (assignments a))
            [(variableName i.val,true),(variableName i.val,false)] = true := by
        intro i
        simp [Std.Sat.CNF.Clause.eval,values a i]
      change S.all (fun c => Std.Sat.CNF.Clause.eval
        (Conventional.extendAssignment S (assignments a)) c) = (unaryStandard F).eval a
      rw [split]
      have main : F.all (fun c => Std.Sat.CNF.Clause.eval
          (Conventional.extendAssignment S (assignments a)) (c.map renamedLiteral)) =
          (unaryStandard F).eval a := by
        simp only [unaryStandard,Std.Sat.CNF.eval,List.all_toArray]
        exact List.all_congr rfl clause
      rw [main]
      have allTaut : (List.finRange n).all (fun i =>
          Std.Sat.CNF.Clause.eval (Conventional.extendAssignment S (assignments a))
            [(variableName i.val,true),(variableName i.val,false)]) = true := by
        apply List.all_eq_true.mpr
        intro i _
        exact taut i
      rw [allTaut]
      simp
    let satisfying := Equiv.subtypeEquiv
      (p := fun a : Fin n → Bool => (unaryStandard F).eval a = true)
      (q := fun a : Conventional.Appearing S → Bool => Conventional.evaluate S a = true)
      assignments (fun a => by
      change (unaryStandard F).eval a = true ↔
        Conventional.evaluate S (assignments a) = true
      rw [evaluation a])
    have transported := Fintype.card_congr satisfying
    have leftCard : Fintype.card {a : Fin n → Bool //
        (unaryStandard F).eval a = true} = unaryCount F := by
      apply Fintype.card_of_subtype (Finset.univ.filter fun a =>
        (unaryStandard F).eval a = true)
      intro a
      simp
    have rightCard : Fintype.card {a : Conventional.Appearing S → Bool //
        Conventional.evaluate S a = true} = Conventional.satisfyingCount S := by
      apply Fintype.card_of_subtype (Finset.univ.filter fun a => Conventional.evaluate S a = true)
      intro a
      simp
    exact rightCard.symm.trans (transported.symm.trans leftCard)
  have estimates : ∀ (n : Nat) (F : UnaryFormula n),
      let U := (sourceWord F).length
      let R := (Conventional.formulaWord (saturatedFormula F)).length
      R ≤ 4*U^2+14*U+2 ∧
      (F.map queryClauseClock).sum+2+n*(n+3)+2*n+6+R ≤ 6*U^2+21*U+10 := by
    intro n F
    dsimp only
    let body := (F.flatMap unaryClause).length
    let U := (sourceWord F).length
    have literal : ∀ l : Fin n × Bool,
        (Conventional.literalWord (variableName l.1.val,l.2)).length ≤ 2*(unaryLiteral l).length := by
      intro l
      simp [Conventional.literalWord,Conventional.nameWord,variableName,unaryLiteral,
        List.length_flatMap,List.map_const,List.sum_replicate]
      omega
    have clause : ∀ c : Std.Sat.CNF.Clause (Fin n),
        (Conventional.clauseWord (c.map (fun l => (variableName l.1.val,l.2)))).length ≤
          2*(unaryClause c).length := by
      intro c
      have terms : (c.flatMap (fun l => Conventional.literalWord (variableName l.1.val,l.2))).length ≤
          2*(c.flatMap unaryLiteral).length := by
        induction c with
        | nil => simp
        | cons l c ih =>
          have h := literal l
          simp only [List.flatMap_cons,List.length_append] at *
          omega
      simp only [Conventional.clauseWord,unaryClause,List.flatMap_map,List.length_append,
        List.length_cons,List.length_nil]
      omega
    have main : (F.flatMap (fun c => Conventional.clauseWord
        (c.map (fun l => (variableName l.1.val,l.2))))).length ≤ 2*body := by
      dsimp [body]
      induction F with
      | nil => simp
      | cons c F ih =>
        have h := clause c
        simp only [List.flatMap_cons,List.length_append] at *
        omega
    have saturation : ∀ indices : List (Fin n),
        (indices.flatMap (fun i => Conventional.clauseWord
          [(variableName i.val,true),(variableName i.val,false)])).length ≤
            indices.length*(4*n+12) := by
      intro indices
      induction indices with
      | nil => simp
      | cons i indices ih =>
        have less := i.isLt
        have head : (Conventional.clauseWord
            [(variableName i.val,true),(variableName i.val,false)]).length = 4*i.val+16 := by
          simp [Conventional.clauseWord,Conventional.literalWord,Conventional.nameWord,
            variableName,List.length_flatMap,List.map_const,List.sum_replicate]
          omega
        simp only [List.flatMap_cons,List.length_append,List.length_cons,head]
        nlinarith
    have taut := saturation (List.finRange n)
    simp only [List.length_finRange] at taut
    have source : U = n+body+3 := by
      simp [U,sourceWord,body]
      omega
    have output : (Conventional.formulaWord (saturatedFormula F)).length ≤
        2*body+n*(4*n+12)+2 := by
      simp only [Conventional.formulaWord,saturatedFormula,List.flatMap_append,
        List.flatMap_map,List.length_append,List.length_cons,List.length_nil]
      omega
    have clockClause : ∀ c : Std.Sat.CNF.Clause (Fin n),
        queryClauseClock c ≤ n+2*(unaryClause c).length := by
      intro c
      have terms : (c.map (fun l => l.1.val+4)).sum = (c.flatMap unaryLiteral).length := by
        induction c with
        | nil => simp
        | cons l c ih =>
          simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,
            unaryLiteral,List.length_cons,List.length_nil,List.length_replicate,ih]
          omega
      simp only [queryClauseClock,terms,unaryClause,List.length_append,List.length_cons,List.length_nil]
      omega
    have clocksAll : ∀ G : UnaryFormula n,
        (G.map queryClauseClock).sum ≤ n*G.length+2*(G.flatMap unaryClause).length := by
      intro G
      induction G with
      | nil => simp
      | cons c F ih =>
        have h := clockClause c
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,List.length_cons]
        nlinarith
    have clocks := clocksAll F
    change (F.map queryClauseClock).sum ≤ n*F.length+2*body at clocks
    have numberAll : ∀ G : UnaryFormula n, G.length ≤ (G.flatMap unaryClause).length := by
      intro G
      induction G with
      | nil => simp
      | cons c F ih =>
        simp only [List.length_cons,List.flatMap_cons,List.length_append,unaryClause,
          List.length_cons,List.length_nil]
        omega
    have number := numberAll F
    change F.length ≤ body at number
    have nBound : n ≤ U := by omega
    have bodyBound : body ≤ U := by omega
    have clauseBound : F.length ≤ U := by omega
    have nn := Nat.mul_self_le_mul_self nBound
    have nm := Nat.mul_le_mul nBound clauseBound
    have outBound : (Conventional.formulaWord (saturatedFormula F)).length ≤ 4*U^2+14*U+2 := by
      nlinarith
    refine ⟨outBound,?_⟩
    nlinarith
  have decoding : ∀ (n : Nat) (F : UnaryFormula n), (∀ c ∈ F, c.length ≤ 3) →
      Conventional.readWord (Conventional.formulaWord (saturatedFormula F)) = some (saturatedFormula F) := by
    intro n F width
    have bits : ∀ (name tail : List Bool),
        Conventional.readBits (Conventional.nameWord name ++ tail) = some (name,tail) := by
      intro name
      induction name with
      | nil => intro tail; rfl
      | cons b name ih =>
        intro tail
        simpa [Conventional.nameWord,List.append_assoc,Conventional.readBits] using
          congrArg (fun result => result.map (fun r => (b::r.1,r.2))) (ih tail)
    have name : ∀ (v tail : List Bool), v.head? = some true →
        Conventional.readName (Conventional.nameWord v ++ tail) = some (v,tail) := by
      intro v tail canonical
      simp [Conventional.readName,bits,canonical]
    have clause : ∀ (c : Std.Sat.CNF.Clause Conventional.Name) (budget : Nat) (tail : List Bool),
        c.length ≤ budget → (∀ l ∈ c, l.1.head? = some true) →
        Conventional.readClause budget (c.flatMap Conventional.literalWord ++ [true,false] ++ tail) =
          some (c,tail) := by
      intro c
      induction c with
      | nil =>
        intro budget tail _ _
        cases budget <;> rfl
      | cons l c ih =>
        intro budget tail bounded canonical
        cases budget with
        | zero => simp at bounded
        | succ budget =>
          have first := canonical l (by simp)
          have rest : ∀ l ∈ c, l.1.head? = some true := by
            intro l member
            exact canonical l (by simp [member])
          have bound : c.length ≤ budget := by simpa using bounded
          have nr := name l.1 (c.flatMap Conventional.literalWord ++ [true,false] ++ tail) first
          have cr := ih budget tail bound rest
          simp only [List.append_assoc,List.cons_append,List.nil_append] at nr cr
          simp only [List.flatMap_cons,Conventional.literalWord,List.append_assoc,
            List.cons_append,List.nil_append,Conventional.readClause,nr]
          change (Conventional.readClause budget
            (c.flatMap Conventional.literalWord ++ true::false::tail)).bind
              (fun result => some (l::result.1,result.2)) = some (l::c,tail)
          rw [cr]
          rfl
    have body : ∀ (G : Conventional.Formula) (fuel : Nat),
        G.length < fuel → (∀ c ∈ G, c.length ≤ 3) →
        (∀ c ∈ G, ∀ l ∈ c, l.1.head? = some true) →
        Conventional.readBody fuel (Conventional.formulaWord G) = some G := by
      intro G
      induction G with
      | nil =>
        intro fuel bound _ _
        cases fuel with
        | zero => omega
        | succ fuel => rfl
      | cons c G ih =>
        intro fuel bound width canonical
        cases fuel with
        | zero => omega
        | succ fuel =>
          have bound : G.length < fuel := by simpa using bound
          have cr := clause c 3 (Conventional.formulaWord G) (width c (by simp))
            (canonical c (by simp))
          have gr := ih fuel bound (fun c h => width c (by simp [h]))
            (fun c h => canonical c (by simp [h]))
          simp only [Conventional.formulaWord,List.append_assoc,List.cons_append,List.nil_append] at cr gr
          simp only [Conventional.formulaWord,Conventional.clauseWord,List.flatMap_cons,
            List.append_assoc,List.cons_append,List.nil_append,Conventional.readBody,cr]
          change (Conventional.readBody fuel
            (G.flatMap Conventional.clauseWord ++ [false,false])).bind
              (fun result => some (c::result)) = some (c::G)
          rw [gr]
          rfl
    have widths : ∀ c ∈ saturatedFormula F, c.length ≤ 3 := by
      intro c member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨original,h,rfl⟩ := List.mem_map.mp member
        simpa using width original h
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
        simp
    have canonical : ∀ c ∈ saturatedFormula F, ∀ l ∈ c, l.1.head? = some true := by
      intro c member l occurs
      rcases List.mem_append.mp member with member | member
      · obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
        obtain ⟨literal,_,rfl⟩ := List.mem_map.mp occurs
        rfl
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at occurs
        rcases occurs with rfl | rfl <;> rfl
    have size : (saturatedFormula F).length ≤
        (Conventional.formulaWord (saturatedFormula F)).length := by
      have general : ∀ G : Conventional.Formula,
          G.length ≤ (Conventional.formulaWord G).length := by
        intro G
        induction G with
        | nil => simp [Conventional.formulaWord]
        | cons c G ih =>
          simp only [Conventional.formulaWord,List.flatMap_cons,List.length_append,
            List.length_cons,List.length_nil,Conventional.clauseWord] at *
          omega
      exact general _
    exact body _ _ (by omega) widths canonical
  have widths := (pre_word_run w).2.2.2.1
  have decoded : Conventional.readWord (convertedWord w) =
      some (saturatedFormula (preparedFormula w).2) := decoding _ _ widths
  have transport : Conventional.rawCount (convertedWord w) = explicitRawCount w := by
    rw [Conventional.rawCount,decoded]
    dsimp only
    rw [counted]
    unfold explicitRawCount preparedFormula
    cases read : ClauseCodec.readWord false w with
    | none => simp [unaryCount,unaryStandard,Std.Sat.CNF.eval,Std.Sat.CNF.Clause.eval]
    | some value => rfl
  have run := Classical.choice (reverseExecution w)
  have bounded : reverseClock w ≤ 10*w.length^2+41*w.length+33 ∧
      (convertedWord w).length ≤ 4*w.length^2+14*w.length+6 := by
    cases read : ClauseCodec.readWord false w with
    | none =>
      have prepared : preparedFormula w = ⟨0,([[]] : UnaryFormula 0)⟩ := by
        unfold preparedFormula
        rw [read]
        rfl
      have output : convertedWord w = [false,true,true,false,false,false] := by
        unfold convertedWord
        rw [prepared]
        rfl
      unfold reverseClock
      rw [prepared,output]
      norm_num [queryClauseClock]
      nlinarith
    | some value =>
      rcases value with ⟨n,F⟩
      have prepared : preparedFormula w = ⟨n,F⟩ := by
        unfold preparedFormula
        rw [read]
        rfl
      have spelling := (ClauseCodec.codec_exact false w n F).mp read
      have sourceEq : ClauseCodec.encodeWord false F = sourceWord F := by
        have general : ∀ (n : Nat) (G : UnaryFormula n),
            ClauseCodec.encodeWord false G = sourceWord G := by
          intro n G
          induction G with
          | nil => simp [ClauseCodec.encodeWord,ClauseCodec.bodyWord,sourceWord,List.append_assoc]
          | cons c G ih =>
            simpa [ClauseCodec.encodeWord,ClauseCodec.bodyWord,ClauseCodec.termWord,
              sourceWord,unaryClause,List.append_assoc] using ih
        exact general n F
      have source : (sourceWord F).length = w.length := by
        rw [← sourceEq,← spelling.1]
      have output : convertedWord w = Conventional.formulaWord (saturatedFormula F) := by
        unfold convertedWord
        rw [prepared]
      have amount := estimates n F
      dsimp only at amount
      rw [source] at amount
      unfold reverseClock
      rw [prepared,output]
      constructor
      · nlinarith [amount.2]
      · exact amount.1.trans (by omega)
  exact ⟨⟨{ steps := run.steps
            evals_in_steps := run.evals_in_steps
            steps_le_m := run.steps_le_m.trans bounded.1 }⟩, bounded.2, decoded, transport⟩
end PredictiveThermodynamic.ConventionalReverse
