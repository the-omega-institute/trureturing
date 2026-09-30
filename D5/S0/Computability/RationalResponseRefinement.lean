/- GID: D5/S0/Computability/RationalResponseRefinement
   generality: G
   mirror-B: D5/B/S0/Computability/RationalResponseRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every raw rational-response word reaches its exact clean postprocessor output. -/

import D5.S0.Computability.RationalMalformedCleanup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic
open Turing StateTransition Lax51Proofs.RamToTM

/-- The whole suffix consists of zero digits; the returned number is its length. -/
def responseZeroSuffix : List ResponseSymbol → Option Nat
  | [] => some 0
  | .zero :: rest => Nat.succ <$> responseZeroSuffix rest
  | _ => none

/-- Denominator syntax and the reducedness test against a positive power of two. -/
def postDenominatorOutput (st : PostControl) (q : List Bool)
    (w : List ResponseSymbol) : List Bool :=
  match w with
  | .one :: rest =>
    match responseZeroSuffix rest with
    | none => [false]
    | some e =>
      if e = 0 then canonicalBinary (false :: q).reverse
      else if st.last then canonicalBinary (q.drop (e-1)).reverse else [false]
  | _ => [false]

/-- Total numerator scan, with the actual finite remainder and quotient bits. -/
def postNumeratorOutput (st : PostControl) (q : List Bool) :
    List ResponseSymbol → List Bool
  | [] => [false]
  | .slash :: rest =>
    if st.remainder = 0 then postDenominatorOutput st q rest else [false]
  | .zero :: rest => postNumeratorOutput (advance st false)
      (quotientBit st.remainder false :: q) rest
  | .one :: rest => postNumeratorOutput (advance st true)
      (quotientBit st.remainder true :: q) rest

/-- Ordinary raw response processing; faults produce the one-symbol zero. -/
def totalPostOutput : List ResponseSymbol → List Bool
  | .one :: rest => postNumeratorOutput ⟨1,none,true⟩ [false] rest
  | _ => [false]

/-- Arithmetic suitability of the complete ordinary response, independent of any Hamiltonian. -/
def suitableResponse (w : List ResponseSymbol) : Prop :=
  ∃ (xs : List Bool) (e : Nat), w = responseWord xs e ∧
    3 ∣ msbValue (true::xs) ∧ (0 < e → Odd (msbValue (true::xs)))

/-- Every raw word executes to the stated clean output. On suitable ordinary
responses its numeric value agrees with the established dyadic recovery law. -/
theorem post_word_run (w : List ResponseSymbol) :
    Nonempty (TM2OutputsInTime postMachine w (some (binaryWord (totalPostOutput w)))
      (3*w.length+10)) ∧
    (∀ (xs : List Bool) (e : Nat), w = responseWord xs e →
      3 ∣ msbValue (true :: xs) →
      (0 < e → Odd (msbValue (true :: xs))) →
      msbValue (totalPostOutput w) =
        if e = 0 then 2*(msbValue (true :: xs)/3)
        else (msbValue (true :: xs)/3)/2^(e-1)) ∧
    (¬ suitableResponse w → totalPostOutput w = [false]) ∧
    (totalPostOutput w = [false] ∨ ∃ xs : List Bool, totalPostOutput w = true::xs) := by
  let single : ∀ (a b : postMachine.Cfg), postMachine.step a = some b →
      EvalsToInTime postMachine.step a (some b) 1 :=
    fun a b h => { steps := 1, evals_in_steps := h, steps_le_m := by decide }
  have zeroRun : ∀ (input : List ResponseSymbol) (q : List Bool) (t : Nat) st,
      EvalsToInTime postMachine.step
        (postCfg .badInput st input (binaryWord q) (List.replicate t .zero) [])
        (some (haltList postMachine (binaryWord [false])))
        (input.length+q.length+t+3) := by
    intro input q t st
    let run := Classical.choice (post_error_cleanup st input (binaryWord q)
      (List.replicate t .zero))
    simpa [binaryWord,bitSymbol] using run
  have zeros : ∀ input q t st, EvalsToInTime postMachine.step
      (postCfg .denominatorZeros st input (binaryWord q) (List.replicate t .zero) [])
      (some (haltList postMachine (binaryWord
        (match responseZeroSuffix input with
         | none => [false]
         | some e => canonicalBinary (q.drop (t+e)).reverse))))
      (3*input.length+2*q.length+t+8) := by
    intro input
    induction input with
    | nil =>
      intro q t st
      have run := denominatorZerosRun st q 0 t
      simp only [Nat.zero_add,List.replicate_zero] at run
      refine { run with steps_le_m := ?_ }
      have hb := run.steps_le_m
      simp [responseZeroSuffix]
      omega
    | cons a input ih =>
      intro q t st
      cases a with
      | zero =>
        have hs : postMachine.step
            (postCfg .denominatorZeros st (.zero::input) (binaryWord q)
              (List.replicate t .zero) []) =
            some (postCfg .denominatorZeros (clearSymbol st) input (binaryWord q)
              (List.replicate (t+1) .zero) []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
            readSymbol,clearSymbol]
          simp only [List.replicate_succ]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (3*input.length+2*q.length+(t+1)+8)
          _ _ _ (single _ _ hs) (ih q (t+1) (clearSymbol st))
        cases parsed : responseZeroSuffix input with
        | none =>
          simp only [responseZeroSuffix,parsed,Option.map_none] at ⊢
          simp only [parsed] at run
          exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
        | some e =>
          simp only [responseZeroSuffix,parsed,Option.map_some] at ⊢
          simp only [parsed] at run
          have eq : t+Nat.succ e = (t+1)+e := by omega
          change EvalsToInTime postMachine.step _
            (some (haltList postMachine
              (binaryWord (canonicalBinary (q.drop (t+Nat.succ e)).reverse)))) _
          rw [eq]
          exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | one =>
        have hs : postMachine.step
            (postCfg .denominatorZeros st (.one::input) (binaryWord q)
              (List.replicate t .zero) []) =
            some (postCfg .badInput (readSymbol st (some .one)) input (binaryWord q)
              (List.replicate t .zero) []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+q.length+t+3)
          _ _ _ (single _ _ hs) (zeroRun input q t _)
        refine { run with steps_le_m := ?_ }
        have hb := run.steps_le_m
        simp only [List.length_cons]
        omega
      | slash =>
        have hs : postMachine.step
            (postCfg .denominatorZeros st (.slash::input) (binaryWord q)
              (List.replicate t .zero) []) =
            some (postCfg .badInput (readSymbol st (some .slash)) input (binaryWord q)
              (List.replicate t .zero) []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+q.length+t+3)
          _ _ _ (single _ _ hs) (zeroRun input q t _)
        refine { run with steps_le_m := ?_ }
        have hb := run.steps_le_m
        simp only [List.length_cons]
        omega
  have denominator : ∀ input q st, EvalsToInTime postMachine.step
      (postCfg .denominatorFirst st input (binaryWord q) [] [])
      (some (haltList postMachine (binaryWord (postDenominatorOutput st q input))))
      (3*input.length+2*q.length+8) := by
    intro input q st
    cases input with
    | nil =>
      have hs : postMachine.step (postCfg .denominatorFirst st [] (binaryWord q) [] []) =
          some (postCfg .badInput (readSymbol st none) [] (binaryWord q) [] []) := by
        apply congrArg some
        dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
        congr 1
        funext k
        cases k <;> rfl
      have run := EvalsToInTime.trans _ 1 (q.length+3) _ _ _
        (single _ _ hs) (by simpa using zeroRun [] q 0 _)
      exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
    | cons a input =>
      cases a with
      | zero =>
        have hs : postMachine.step
            (postCfg .denominatorFirst st (.zero::input) (binaryWord q) [] []) =
            some (postCfg .badInput (readSymbol st (some .zero)) input (binaryWord q) [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+q.length+3) _ _ _
          (single _ _ hs) (zeroRun input q 0 _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | slash =>
        have hs : postMachine.step
            (postCfg .denominatorFirst st (.slash::input) (binaryWord q) [] []) =
            some (postCfg .badInput (readSymbol st (some .slash)) input (binaryWord q) [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+q.length+3) _ _ _
          (single _ _ hs) (zeroRun input q 0 _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | one =>
        cases input with
        | nil =>
          have run := denominatorRun st q 0 (by simp)
          simpa [postDenominatorOutput,responseZeroSuffix] using
            ({ run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega } :
              EvalsToInTime postMachine.step _ _ (3*([ResponseSymbol.one]).length+2*q.length+8))
        | cons a input =>
          have first : postMachine.step
              (postCfg .denominatorFirst st (.one::a::input) (binaryWord q) [] []) =
              some (postCfg .denominatorTail (clearSymbol st) (a::input)
                (binaryWord q) [] []) := by
            apply congrArg some
            dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
              readSymbol,clearSymbol]
            congr 1
            funext k
            cases k <;> rfl
          cases a with
          | one =>
            have second : postMachine.step
                (postCfg .denominatorTail (clearSymbol st) (.one::input) (binaryWord q) [] []) =
                some (postCfg .badInput (readSymbol (clearSymbol st) (some .one))
                  input (binaryWord q) [] []) := by
              apply congrArg some
              dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
              simp only [Bool.false_and]
              dsimp only [cond]
              congr 1
              funext k
              cases k <;> rfl
            have tail := EvalsToInTime.trans _ 1 (input.length+q.length+3)
              _ _ _ (single _ _ second) (zeroRun input q 0 _)
            have run := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) tail
            exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
          | slash =>
            have second : postMachine.step
                (postCfg .denominatorTail (clearSymbol st) (.slash::input) (binaryWord q) [] []) =
                some (postCfg .badInput (readSymbol (clearSymbol st) (some .slash))
                  input (binaryWord q) [] []) := by
              apply congrArg some
              dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
              simp only [Bool.false_and]
              dsimp only [cond]
              congr 1
              funext k
              cases k <;> rfl
            have tail := EvalsToInTime.trans _ 1 (input.length+q.length+3)
              _ _ _ (single _ _ second) (zeroRun input q 0 _)
            have run := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) tail
            exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
          | zero =>
            cases last : st.last with
            | false =>
              have second : postMachine.step
                  (postCfg .denominatorTail (clearSymbol st) (.zero::input)
                    (binaryWord q) [] []) =
                  some (postCfg .badInput (readSymbol (clearSymbol st) (some .zero))
                    input (binaryWord q) [] []) := by
                apply congrArg some
                dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
                  readSymbol,clearSymbol]
                simp only [last,Bool.and_false]
                dsimp only [cond]
                congr 1
                funext k
                cases k <;> rfl
              have tail := EvalsToInTime.trans _ 1 (input.length+q.length+3)
                _ _ _ (single _ _ second) (zeroRun input q 0 _)
              have run := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) tail
              cases parsed : responseZeroSuffix input <;>
                simp [postDenominatorOutput,responseZeroSuffix,parsed,last]
              all_goals exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
            | true =>
              have second : postMachine.step
                  (postCfg .denominatorTail (clearSymbol st) (.zero::input)
                    (binaryWord q) [] []) =
                  some (postCfg .denominatorZeros (clearSymbol (clearSymbol st)) input
                    (binaryWord q) [] []) := by
                apply congrArg some
                dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
                  readSymbol,clearSymbol]
                simp only [last,Bool.and_true]
                dsimp only [cond]
                congr 1
                funext k
                cases k <;> rfl
              have tail := EvalsToInTime.trans _ 1 (3*input.length+2*q.length+8)
                _ _ _ (single _ _ second) (zeros input q 0 (clearSymbol (clearSymbol st)))
              have run := EvalsToInTime.trans _ 1 _ _ _ _ (single _ _ first) tail
              cases parsed : responseZeroSuffix input <;>
                simp [postDenominatorOutput,responseZeroSuffix,parsed,last]
              all_goals
                simp only [parsed,Nat.zero_add] at run
                exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
  have numerator : ∀ input q st, EvalsToInTime postMachine.step
      (postCfg .numerator st input (binaryWord q) [] [])
      (some (haltList postMachine (binaryWord (postNumeratorOutput st q input))))
      (3*input.length+2*q.length+10) := by
    intro input
    induction input with
    | nil =>
      intro q st
      have hs : postMachine.step (postCfg .numerator st [] (binaryWord q) [] []) =
          some (postCfg .badInput (readSymbol st none) [] (binaryWord q) [] []) := by
        apply congrArg some
        dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
        congr 1
        funext k
        cases k <;> rfl
      have run := EvalsToInTime.trans _ 1 (q.length+3) _ _ _
        (single _ _ hs) (by simpa using zeroRun [] q 0 _)
      exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
    | cons a input ih =>
      intro q st
      cases a with
      | slash =>
        by_cases rem : st.remainder = 0
        · have hs : postMachine.step
              (postCfg .numerator st (.slash::input) (binaryWord q) [] []) =
              some (postCfg .denominatorFirst (clearSymbol st) input (binaryWord q) [] []) := by
            apply congrArg some
            dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
              readSymbol,clearSymbol]
            simp only [rem,Fin.val_zero,decide_true]
            dsimp only [cond]
            congr 1
            funext k
            cases k <;> rfl
          have run := EvalsToInTime.trans _ 1 (3*input.length+2*q.length+8)
            _ _ _ (single _ _ hs) (denominator input q (clearSymbol st))
          simpa [postNumeratorOutput,rem,postDenominatorOutput,clearSymbol] using
            ({ run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega } :
              EvalsToInTime postMachine.step _ _ (3*(.slash::input).length+2*q.length+10))
        · have hs : postMachine.step
              (postCfg .numerator st (.slash::input) (binaryWord q) [] []) =
              some (postCfg .badInput (readSymbol st (some .slash)) input
                (binaryWord q) [] []) := by
            have val : st.remainder.val ≠ 0 := by
              intro eq; apply rem; exact Fin.ext eq
            apply congrArg some
            dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
            simp only [val,decide_false]
            dsimp only [cond]
            congr 1
            funext k
            cases k <;> rfl
          have run := EvalsToInTime.trans _ 1 (input.length+q.length+3)
            _ _ _ (single _ _ hs) (zeroRun input q 0 _)
          simp only [postNumeratorOutput,rem,ite_false]
          exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | zero =>
        have hs : postMachine.step
            (postCfg .numerator st (.zero::input) (binaryWord q) [] []) =
            some (postCfg .numerator (advance st false) input
              (binaryWord (quotientBit st.remainder false::q)) [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
            readSymbol,advance]
          simp only [binaryWord,List.map_cons,bitSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1
          (3*input.length+2*(quotientBit st.remainder false::q).length+10) _ _ _ (single _ _ hs) (ih _ _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | one =>
        have hs : postMachine.step
            (postCfg .numerator st (.one::input) (binaryWord q) [] []) =
            some (postCfg .numerator (advance st true) input
              (binaryWord (quotientBit st.remainder true::q)) [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,postCfg,postStacks,isSymbol,symbolEq,
            readSymbol,advance]
          simp only [binaryWord,List.map_cons,bitSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1
          (3*input.length+2*(quotientBit st.remainder true::q).length+10) _ _ _ (single _ _ hs) (ih _ _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
  have actual : EvalsToInTime postMachine.step (initList postMachine w)
      (some (haltList postMachine (binaryWord (totalPostOutput w)))) (3*w.length+10) := by
    cases w with
    | nil =>
      have hs : postMachine.step (initList postMachine []) =
          some (postCfg .badInput (readSymbol default none) [] [] [] []) := by
        apply congrArg some
        dsimp [postMachine,TM2.stepAux,initList,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
        congr 1
        funext k
        cases k <;> rfl
      have run := EvalsToInTime.trans _ 1 3 _ _ _ (single _ _ hs) (zeroRun [] [] 0 _)
      exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
    | cons a input =>
      cases a with
      | zero =>
        have hs : postMachine.step (initList postMachine (.zero::input)) =
            some (postCfg .badInput (readSymbol default (some .zero)) input [] [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,initList,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+3) _ _ _
          (single _ _ hs) (zeroRun input [] 0 _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | slash =>
        have hs : postMachine.step (initList postMachine (.slash::input)) =
            some (postCfg .badInput (readSymbol default (some .slash)) input [] [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,initList,postCfg,postStacks,isSymbol,symbolEq,readSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (input.length+3) _ _ _
          (single _ _ hs) (zeroRun input [] 0 _)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
      | one =>
        have hs : postMachine.step (initList postMachine (.one::input)) =
            some (postCfg .numerator ⟨1,none,true⟩ input (binaryWord [false]) [] []) := by
          apply congrArg some
          dsimp [postMachine,TM2.stepAux,initList,postCfg,postStacks,isSymbol,symbolEq,
            readSymbol,binaryWord,bitSymbol]
          congr 1
          funext k
          cases k <;> rfl
        have run := EvalsToInTime.trans _ 1 (3*input.length+2*([false]).length+10)
          _ _ _ (single _ _ hs) (numerator input [false] ⟨1,none,true⟩)
        exact { run with steps_le_m := by have hb := run.steps_le_m; first | (simp_all only [List.length_cons,List.length_nil] <;> omega) | omega }
  refine ⟨⟨actual⟩,?_,?_,?_⟩
  · intro xs e encoded divisible odd
    obtain ⟨⟨valid⟩,value⟩ := dyadic_response_run xs e divisible odd
    rw [← encoded] at valid
    have traceReaches : ∀ (f : postMachine.Cfg → Option postMachine.Cfg) k a b,
        (flip bind f)^[k] (some a) = some b → Reaches f a b := by
      intro f
      have noneStable : ∀ k, (flip bind f)^[k] none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => simpa [Function.iterate_succ_apply,flip] using ih
      intro k
      induction k with
      | zero =>
        intro a b trace
        have eq : a = b := Option.some.inj trace
        subst b
        exact Relation.ReflTransGen.refl
      | succ k ih =>
        intro a b trace
        simp only [Function.iterate_succ_apply,flip,Option.bind_some] at trace
        change (flip bind f)^[k] (f a) = some b at trace
        cases step : f a with
        | none => rw [step,noneStable] at trace; cases trace
        | some a' => rw [step] at trace; exact Relation.ReflTransGen.head step (ih a' b trace)
    have terminal : haltList postMachine (binaryWord (totalPostOutput w)) =
        haltList postMachine (binaryWord (responseOutput xs e)) := by
      apply Part.mem_unique
      · exact mem_eval.mpr ⟨traceReaches _ actual.steps _ _ actual.evals_in_steps,rfl⟩
      · exact mem_eval.mpr ⟨traceReaches _ valid.steps _ _ valid.evals_in_steps,rfl⟩
    have output := congrArg (fun c : postMachine.Cfg => c.stk .output) terminal
    have mapInjective : Function.Injective binaryWord := by
      intro a b eq
      apply (List.map_injective_iff.mpr (show Function.Injective bitSymbol from ?_)) eq
      intro a b eq
      cases a <;> cases b <;> cases eq <;> rfl
    have words := mapInjective output
    rw [words]
    exact value

  · classical
    have zeroSyntax : ∀ (input : List ResponseSymbol) (e : Nat),
        responseZeroSuffix input = some e → input = List.replicate e .zero := by
      intro input
      induction input with
      | nil =>
        intro e eq
        have value : e = 0 := (Option.some.inj eq).symm
        subst e
        rfl
      | cons a input ih =>
        intro e eq
        cases a with
        | one | slash => simp [responseZeroSuffix] at eq
        | zero =>
          cases parsed : responseZeroSuffix input with
          | none => simp [responseZeroSuffix,parsed] at eq
          | some k =>
            have value : e = k+1 := by
              simpa [responseZeroSuffix,parsed] using eq.symm
            subst e
            rw [ih k parsed]
            rfl
    have denSound : ∀ st q input, postDenominatorOutput st q input ≠ [false] →
        ∃ e, input = .one :: List.replicate e .zero ∧
          (0 < e → st.last = true) := by
      intro st q input nonzero
      cases input with
      | nil => exact (nonzero rfl).elim
      | cons a input =>
        cases a with
        | zero | slash => exact (nonzero rfl).elim
        | one =>
          cases parsed : responseZeroSuffix input with
          | none => exact (nonzero (by simp [postDenominatorOutput,parsed])).elim
          | some e =>
            refine ⟨e,congrArg (List.cons .one) (zeroSyntax input e parsed),?_⟩
            intro positive
            cases last : st.last with
            | true => rfl
            | false =>
              have notZero : e ≠ 0 := by omega
              exact (nonzero (by simp [postDenominatorOutput,parsed,notZero,last])).elim
    have numSound : ∀ input st q, postNumeratorOutput st q input ≠ [false] →
        ∃ (xs : List Bool) (e : Nat),
          input = binaryWord xs ++ .slash :: .one :: List.replicate e .zero ∧
          (scan st q xs).1.remainder = 0 ∧
          (0 < e → (scan st q xs).1.last = true) := by
      intro input
      induction input with
      | nil => intro st q nonzero; exact (nonzero rfl).elim
      | cons a input ih =>
        intro st q nonzero
        cases a with
        | slash =>
          by_cases rem : st.remainder = 0
          · have good : postDenominatorOutput st q input ≠ [false] := by
              simpa only [postNumeratorOutput,rem,ite_true] using nonzero
            obtain ⟨e,word,parity⟩ := denSound st q input good
            exact ⟨[],e,by simpa [binaryWord] using congrArg (List.cons .slash) word,
              rem,parity⟩
          · exact (nonzero (by simp [postNumeratorOutput,rem])).elim
        | zero =>
          obtain ⟨xs,e,word,rem,parity⟩ := ih (advance st false)
            (quotientBit st.remainder false :: q) nonzero
          refine ⟨false::xs,e,?_,rem,parity⟩
          simpa [binaryWord,bitSymbol,List.cons_append] using congrArg (List.cons .zero) word
        | one =>
          obtain ⟨xs,e,word,rem,parity⟩ := ih (advance st true)
            (quotientBit st.remainder true :: q) nonzero
          refine ⟨true::xs,e,?_,rem,parity⟩
          simpa [binaryWord,bitSymbol,List.cons_append] using congrArg (List.cons .one) word
    have scanBridge : ∀ (st : PostControl) (q bs : List Bool),
        (scan st q bs).2 = (divisionScan 3 ⟨q,st.remainder.val⟩ bs).quotient ∧
        (scan st q bs).1.remainder.val =
          (divisionScan 3 ⟨q,st.remainder.val⟩ bs).remainder := by
      intro st q bs
      induction bs generalizing st q with
      | nil => exact ⟨rfl,rfl⟩
      | cons b bs ih =>
        have step : divisionScanStep 3 ⟨q,st.remainder.val⟩ b =
            ⟨quotientBit st.remainder b::q,(nextRemainder st.remainder b).val⟩ := by
          rcases st with ⟨r,held,last⟩
          fin_cases r <;> cases b <;> rfl
        simpa only [scan,divisionScan,step,advance] using
          ih (advance st b) (quotientBit st.remainder b::q)
    have scanParity : ∀ (bs : List Bool) (st : PostControl) (q : List Bool) (a : Nat),
        (st.last = true ↔ Odd a) →
        ((scan st q bs).1.last = true ↔ Odd (msbValueFrom a bs)) := by
      intro bs
      induction bs with
      | nil => intro st q a parity; exact parity
      | cons b bs ih =>
        intro st q a _
        apply ih (advance st b) (quotientBit st.remainder b::q) (2*a+b.toNat)
        cases b with
        | false =>
          change (false = true) ↔ Odd (2*a)
          constructor
          · intro eq; cases eq
          · rintro ⟨k,hk⟩; omega
        | true =>
          change (true = true) ↔ Odd (2*a+1)
          constructor
          · intro _; exact ⟨a,by omega⟩
          · intro _; rfl
    have nonzeroSuitable : totalPostOutput w ≠ [false] → suitableResponse w := by
      intro nonzero
      cases w with
      | nil => exact (nonzero rfl).elim
      | cons a input =>
        cases a with
        | zero | slash => exact (nonzero rfl).elim
        | one =>
          obtain ⟨xs,e,word,rem,last⟩ := numSound input ⟨1,none,true⟩ [false] nonzero
          refine ⟨xs,e,?_,?_,?_⟩
          · simpa [responseWord,binaryWord,bitSymbol,List.cons_append] using
              congrArg (List.cons .one) word
          · obtain ⟨qBridge,rBridge⟩ := scanBridge ⟨1,none,true⟩ [false] xs
            change (scan ⟨1,none,true⟩ [false] xs).2 =
              (divisionScan 3 ⟨[false],1⟩ xs).quotient at qBridge
            change (scan ⟨1,none,true⟩ [false] xs).1.remainder.val =
              (divisionScan 3 ⟨[false],1⟩ xs).remainder at rBridge
            have inv := (divisionScan_invariant (d:=3) (by decide) xs ⟨[false],1⟩
              (by decide)).1
            change bitsValue (divisionScan 3 ⟨[false],1⟩ xs).quotient*3+
              (divisionScan 3 ⟨[false],1⟩ xs).remainder = msbValueFrom 1 xs at inv
            rw [←qBridge,←rBridge] at inv
            rw [rem] at inv
            change bitsValue (scan ⟨1,none,true⟩ [false] xs).2*3+0 =
              msbValue (true::xs) at inv
            exact ⟨bitsValue (scan ⟨1,none,true⟩ [false] xs).2,by omega⟩
          · intro positive
            have parity := scanParity xs ⟨1,none,true⟩ [false] 1 (by
              constructor
              · intro _; exact ⟨0,by decide⟩
              · intro _; rfl)
            exact parity.mp (last positive)
    intro unsuitable
    by_contra nonzero
    exact unsuitable (nonzeroSuitable nonzero)

  · have canon : ∀ xs : List Bool,
        canonicalBinary xs = [false] ∨ ∃ bs : List Bool, canonicalBinary xs = true::bs := by
      intro xs
      induction xs with
      | nil => exact Or.inl rfl
      | cons b xs ih =>
        cases b with
        | false => exact ih
        | true => exact Or.inr ⟨xs,rfl⟩
    have denCanonical : ∀ st q input,
        postDenominatorOutput st q input = [false] ∨
          ∃ bs : List Bool, postDenominatorOutput st q input = true::bs := by
      intro st q input
      cases input with
      | nil => exact Or.inl rfl
      | cons a input =>
        cases a with
        | zero | slash => exact Or.inl rfl
        | one =>
          cases parsed : responseZeroSuffix input with
          | none => exact Or.inl (by simp [postDenominatorOutput,parsed])
          | some e =>
            by_cases he : e=0
            · simpa [postDenominatorOutput,parsed,he] using canon (false::q).reverse
            · cases last : st.last with
              | false => exact Or.inl (by simp [postDenominatorOutput,parsed,he,last])
              | true =>
                  simpa [postDenominatorOutput,parsed,he,last] using
                    (canon (q.drop (e-1)).reverse)
    have numCanonical : ∀ input st q,
        postNumeratorOutput st q input = [false] ∨
          ∃ bs : List Bool, postNumeratorOutput st q input = true::bs := by
      intro input
      induction input with
      | nil => intro st q; exact Or.inl rfl
      | cons a input ih =>
        intro st q
        cases a with
        | slash =>
          by_cases rem : st.remainder=0
          · simpa only [postNumeratorOutput,rem,ite_true] using denCanonical st q input
          · exact Or.inl (by simp [postNumeratorOutput,rem])
        | zero => exact ih (advance st false) (quotientBit st.remainder false::q)
        | one => exact ih (advance st true) (quotientBit st.remainder true::q)
    cases w with
    | nil => exact Or.inl rfl
    | cons a input =>
      cases a with
      | zero | slash => exact Or.inl rfl
      | one => exact numCanonical input ⟨1,none,true⟩ [false]

end PredictiveThermodynamic
