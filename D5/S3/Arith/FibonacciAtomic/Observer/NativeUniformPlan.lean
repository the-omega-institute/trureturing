/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform finite pair-plan coding with exact normalized native action transport. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformVariables
import D5.S0.Rewriting.UniformNativeUnification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (Pattern Frontier frontierAddress History)
open NativeHistoryCells (Patterns Variables oldTerm wholeTerm patternTerm)
open NativeUniformPatterns NativeUniformInput NativeUniformVariables
open NativeWholeRowService (PairKind PairPlan planPair presentation variableList)
open NativeGroundSolutionSpace
open NativeTermUnification (Term Presentation finPresentation encode nativeDecode)
open Lambda Strata.Util
open Lambda.UniformNativeUnification (TermN F liftTerm liftEquations project)

abbrev TemplateWord := Word Bool
abbrev PairCode := Address × Address × Nat × List (Nat × TemplateWord)
abbrev PlanInput := Nat × Equations Nat × Address × Address × TermN × TermN

/-- Constructor words preserve every Boolean label and the order of children. -/
def templateWord (t : TermN) : TemplateWord :=
  word (NativeTermUnification.evaluate (fun _ => .of true) t)

def kindCode : PairKind → Nat
  | .nativeFailure => 0
  | .oldCollapse => 1
  | .groundBindings => 2
  | .feasibleNonground => 3

def codePlan {n : Nat} (p : PairPlan (Fin n)) : PairCode :=
  (p.first,p.second,kindCode p.kind,p.bindings.map (fun b => (b.1.val,word b.2)))

/-- The solver receives one equality. Delta remains the complete old
inequality list and is tested under the returned, fully composed action. -/
def codedPlan (a : PlanInput) : Option PairCode := do
  let out ← F (a.1,[(a.2.2.2.2.1,a.2.2.2.2.2)])
  match out with
  | none => some (a.2.2.1,a.2.2.2.1,0,[])
  | some S =>
      if a.2.1.any (fun e => UniformNativeUnification.Code.apply S e.1 ==
          UniformNativeUnification.Code.apply S e.2) then
        some (a.2.2.1,a.2.2.2.1,1,[])
      else if S.all (fun b => (UniformNativeUnification.Code.vars b.2).isEmpty) then
        some (a.2.2.1,a.2.2.2.1,2,S.map (fun b => (b.1,templateWord b.2)))
      else some (a.2.2.1,a.2.2.2.1,3,[])

private theorem template_word_prim : Primrec templateWord := by
  have hl : Primrec₂ (fun (_ : Nat) (a : Bool ⊕ Nat) =>
      Sum.elim (fun b => ([some b] : TemplateWord)) (fun _ => [some true]) a) := by
    refine Primrec.sumCasesOn Primrec.snd ?_ (Primrec.const [some true]).to₂
    exact (Primrec.list_cons.comp (Primrec.option_some.comp Primrec.snd) (Primrec.const [])).to₂
  have hn : Primrec₂ (fun (_ : Nat) (p : TemplateWord × TemplateWord) =>
      none :: (p.1 ++ p.2)) :=
    Primrec.list_cons.comp (Primrec.const none)
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact ((uniform_tree_fold
    (fun (_ : Nat) (a : Bool ⊕ Nat) => Sum.elim (fun b => [some b]) (fun _ => [some true]) a)
    (fun (_ : Nat) (p : TemplateWord × TemplateWord) => none :: (p.1 ++ p.2)) hl hn).comp
      (Primrec.const 0) Primrec.id).of_eq (fun t => by
        induction t using FreeMagma.recOn with
        | of a => cases a <;> rfl
        | mul l r hl hr =>
            change none :: (_ ++ _) = none :: (_ ++ _)
            exact congrArg (none :: ·) (congrArg₂ List.append hl hr))

private theorem lift_injective (n : Nat) : Function.Injective (@liftTerm n) := by
  intro t u h
  apply NativeTermUnification.encode_injective (finPresentation n)
  rw [← UniformNativeUnification.Code.native_lift,← UniformNativeUnification.Code.native_lift,h]

private theorem project_actions (n : Nat) (E : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S) :
    project n S.subst =
      ((List.finRange n).filter (fun i => (finPresentation n).code i ∈ S.subst.keys)).map
        (fun i => (i.val,liftTerm (action (finPresentation n) S i))) := rfl

private theorem lookup_filtered_graph (xs : List Nat) (f : Nat → TermN) (p : Nat → Bool)
    (a : Nat) (ha : a ∈ xs) :
    ((xs.filter p).map (fun x => (x,f x))).lookup a =
      if p a then some (f a) else none := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases he : a = x
      · subst x
        cases hp : p a
        · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
          by_cases hm : a ∈ xs
          · simpa only [hp,Bool.false_eq_true,↓reduceIte] using ih hm
          · have hn : ∀ ys : List Nat, a ∉ ys →
                ((ys.filter p).map (fun x => (x,f x))).lookup a = none := by
              intro ys
              induction ys with
              | nil => simp [List.lookup]
              | cons y ys ihy =>
                  intro hy
                  have ne : a ≠ y := fun e => hy (by simp [e])
                  have nm : a ∉ ys := fun h => hy (List.mem_cons_of_mem _ h)
                  cases hpy : p y <;> simp [List.filter_cons,hpy,List.lookup,(beq_eq_false_iff_ne.mpr ne),ihy nm]
            exact hn xs hm
        · simp [List.filter_cons,hp,List.lookup]
      · have hm : a ∈ xs := (List.mem_cons.mp ha).resolve_left he
        cases hpx : p x <;> simp [List.filter_cons,hpx,List.lookup,(beq_eq_false_iff_ne.mpr he),ih hm]

private theorem project_lookup (n : Nat) (E : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S)
    (i : Fin n) :
    (project n S.subst).lookup i.val =
      if (finPresentation n).code i ∈ S.subst.keys then
        some (liftTerm (action (finPresentation n) S i)) else none := by
  let value (x : Nat) : TermN := if hx : x < n then
    liftTerm (action (finPresentation n) S ⟨x,hx⟩) else .of (.inr x)
  let pred (x : Nat) : Bool := decide (NativeTermUnification.finName x ∈ S.subst.keys)
  have he : project n S.subst = ((List.range n).filter pred).map (fun x => (x,value x)) := by
    rw [project_actions n E S hs]
    have hr : (List.finRange n).map Fin.val = List.range n := by simp
    rw [← hr,List.filter_map,List.map_map]
    apply List.map_congr_left
    intro j hj
    simp [value,pred,j.isLt,finPresentation]
  rw [he,lookup_filtered_graph _ _ _ _ (by simp [i.isLt])]
  simp [pred,value,i.isLt,finPresentation]

private theorem apply_project (n : Nat) (E : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S)
    (t : Term (Fin n)) :
    UniformNativeUnification.Code.apply (project n S.subst) (liftTerm t) =
      liftTerm (substitute (action (finPresentation n) S) t) := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr i =>
        change ((project n S.subst).lookup i.val).getD (.of (.inr i.val)) =
          liftTerm (action (finPresentation n) S i)
        rw [project_lookup n E S hs]
        by_cases hi : (finPresentation n).code i ∈ S.subst.keys
        · simp [hi]
        · rw [if_neg hi,Option.getD_none,action_identity (finPresentation n) S i hi]
          rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem vars_lift (n : Nat) (t : Term (Fin n)) :
    UniformNativeUnification.Code.vars (liftTerm t) = (termVars t).map Fin.val := by
  induction t using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r hl hr =>
      change UniformNativeUnification.Code.vars (liftTerm l) ++ UniformNativeUnification.Code.vars (liftTerm r) = (termVars l ++ termVars r).map Fin.val
      rw [List.map_append,hl,hr]

private theorem collapse_project (n : Nat) (E Δ : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S) :
    (liftEquations Δ).any (fun e => UniformNativeUnification.Code.apply (project n S.subst) e.1 ==
      UniformNativeUnification.Code.apply (project n S.subst) e.2) =
      NativeWholeRowService.collapse (finPresentation n) S Δ := by
  simp only [liftEquations,List.any_map,Function.comp_def,apply_project n E S hs,
    NativeWholeRowService.collapse]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact (lift_injective n).eq_iff

private theorem ground_project (n : Nat) (E : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S) :
    (project n S.subst).all (fun b => (UniformNativeUnification.Code.vars b.2).isEmpty) =
      NativeWholeRowService.allGround (finPresentation n) S := by
  rw [project_actions n E S hs]
  simp only [List.all_map,Function.comp_def,vars_lift, List.isEmpty_map,
    NativeWholeRowService.allGround,NativeWholeRowService.boundList,finPresentation]

private theorem ground_evaluate_encode {X : Type} (p : Presentation X) (t : Term X)
    (hg : termVars t = []) :
    NativeTermUnification.encodeGround (NativeTermUnification.evaluate (fun _ => .of true) t) =
      encode p t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x => simp [termVars] at hg
  | mul l r hl hr =>
      have h : termVars l = [] ∧ termVars r = [] := by
        simpa only [termVars,List.append_eq_nil_iff] using hg
      exact congrArg₂ NativeTermUnification.pair (hl h.1) (hr h.2)

private theorem evaluate_lift (n : Nat) (t : Term (Fin n)) :
    NativeTermUnification.evaluate (fun _ => .of true) (liftTerm t) =
      NativeTermUnification.evaluate (fun _ => .of true) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem bindings_project (n : Nat) (E : Equations (Fin n)) (S : SubstInfo)
    (hs : (encodeEquations (finPresentation n) E).unify SubstInfo.empty = .ok S)
    (hg : NativeWholeRowService.allGround (finPresentation n) S = true) :
    (project n S.subst).map (fun b => (b.1,templateWord b.2)) =
      (NativeWholeRowService.groundBindings (finPresentation n) S).map
        (fun b => (b.1.val,word b.2)) := by
  rw [project_actions n E S hs]
  simp only [List.map_map,Function.comp_def,NativeWholeRowService.groundBindings,
    NativeWholeRowService.boundList,finPresentation]
  apply List.map_congr_left
  intro i hi
  have ht : termVars (action (finPresentation n) S i) = [] := by
    have h := List.all_eq_true.mp hg i hi
    exact List.isEmpty_iff.mp h
  have hd := (groundDecoder_exact _ _).mpr
    ((ground_evaluate_encode (finPresentation n) _ ht).trans (action_encode _ E S hs i))
  dsimp only [finPresentation] at hd
  rw [hd,Option.getD_some]
  simp only [templateWord,evaluate_lift]


private def oldCollapseCode (S : UniformNativeUnification.Code.Store) (Δ : Equations Nat) : Bool :=
  Δ.any (fun e => UniformNativeUnification.Code.apply S e.1 ==
    UniformNativeUnification.Code.apply S e.2)

private def allGroundCode (S : UniformNativeUnification.Code.Store) : Bool :=
  S.all (fun b => (UniformNativeUnification.Code.vars b.2).isEmpty)

private def payload (Δ : Equations Nat) (S : UniformNativeUnification.Code.Store) :
    Nat × List (Nat × TemplateWord) :=
  bif oldCollapseCode S Δ then (1,[]) else
    bif allGroundCode S then (2,S.map (fun b => (b.1,templateWord b.2))) else (3,[])

private theorem collapse_code_prim : Primrec₂ oldCollapseCode := by
  have h := Primrec.list_foldr Primrec.snd (Primrec.const false)
    ((Primrec.or.comp
      (Primrec.beq.comp
        (UniformNativeUnification.Code.apply_prim.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (UniformNativeUnification.Code.apply_prim.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun p => by
    simp only [oldCollapseCode]
    induction p.2 <;> simp_all)

private theorem all_ground_code_prim : Primrec allGroundCode := by
  have hempty : Primrec (fun xs : List Nat => xs.isEmpty) :=
    (Primrec.eq.comp Primrec.list_length (Primrec.const 0)).decide.of_eq
      (fun xs => by cases xs <;> rfl)
  have h : Primrec (fun S : UniformNativeUnification.Code.Store => S.foldr
      (fun b acc => (UniformNativeUnification.Code.vars b.2).isEmpty && acc) true) :=
    Primrec.list_foldr Primrec.id (Primrec.const true)
    ((Primrec.and.comp
      (hempty.comp (UniformNativeUnification.Code.vars_prim.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun S => by
    simp only [allGroundCode]
    induction S <;> simp_all)

private theorem payload_prim : Primrec₂ payload := by
  unfold payload
  refine Primrec.cond (collapse_code_prim.comp Primrec.snd Primrec.fst) (Primrec.const (1,[])) ?_
  refine Primrec.cond (all_ground_code_prim.comp Primrec.snd) ?_ (Primrec.const (3,[]))
  exact (Primrec.const 2).pair
    (Primrec.list_map Primrec.snd
      ((Primrec.fst.comp Primrec.snd).pair
        (template_word_prim.comp (Primrec.snd.comp Primrec.snd))).to₂)

theorem coded_plan_computable : Computable codedPlan := by
  have solver : Computable (fun a : PlanInput =>
      F (a.1,[(a.2.2.2.2.1,a.2.2.2.2.2)])) := by
    refine UniformNativeUnification.computable_F.comp (Computable.fst.pair ?_)
    exact Computable.list_cons.comp
      ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp (Computable.snd))))).pair
       (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp (Computable.snd)))))) (Computable.const [])
  have branch : Computable (fun p : PlanInput × Option UniformNativeUnification.Code.Store =>
      (Option.casesOn p.2
        (some (p.1.2.2.1,p.1.2.2.2.1,(0 : Nat),([] : List (Nat × TemplateWord))))
        (fun S => some (p.1.2.2.1,p.1.2.2.2.1,payload p.1.2.1 S)) : Option PairCode)) := by
    refine Computable.option_casesOn Computable.snd ?_ ?_
    · exact Computable.option_some.comp
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.fst)))).pair (Computable.const ((0 : Nat),([] : List (Nat × TemplateWord))))))
    · exact (Computable.option_some.comp
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst)))).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp (Computable.fst.comp Computable.fst))))).pair
            (payload_prim.to_comp.comp
              (Computable.fst.comp (Computable.snd.comp
                (Computable.fst.comp Computable.fst))) Computable.snd)))).to₂
  exact (Computable.option_bind solver (branch.comp Computable.id).to₂).of_eq (fun a => by
    unfold codedPlan
    cases F (a.1,[(a.2.2.2.2.1,a.2.2.2.2.2)]) with
    | none => rfl
    | some out => cases out with
      | none => rfl
      | some S =>
          simp [id_eq, Option.bind_some, Option.casesOn, payload,
            oldCollapseCode, allGroundCode]
          cases h : a.2.1.any (fun e =>
              UniformNativeUnification.Code.apply S e.1 == UniformNativeUnification.Code.apply S e.2) <;>
            cases hg : S.all (fun b => (UniformNativeUnification.Code.vars b.2).isEmpty) <;>
            simp [h, hg, cond])

theorem coded_plan_exact (n : Nat) (Δ : Equations (Fin n)) (q r : Address)
    (s t : Term (Fin n)) :
    codedPlan (n,liftEquations Δ,q,r,liftTerm s,liftTerm t) =
      some (codePlan (planPair (finPresentation n) Δ q r s t)) := by
  have hf := UniformNativeUnification.exact_native n [(s,t)]
  change F (n,[(liftTerm s,liftTerm t)]) = _ at hf
  simp only [liftEquations,List.map_cons,List.map_nil] at hf
  unfold codedPlan
  dsimp only
  rw [hf]
  cases hs : (encodeEquations (finPresentation n) [(s,t)]).unify SubstInfo.empty with
  | error e =>
      simp only [encodeEquations,List.map_cons,List.map_nil] at hs
      simp only [hs,bind,Option.bind,planPair,encodeEquations,List.map_cons,List.map_nil,codePlan,kindCode,Option.some.injEq]
  | ok S =>
      have hc := collapse_project n [(s,t)] Δ S hs
      have hg := ground_project n [(s,t)] S hs
      simp only [encodeEquations,List.map_cons,List.map_nil] at hs
      simp only [hs,bind,Option.bind]
      rw [hc,hg]
      simp only [planPair,encodeEquations,List.map_cons,List.map_nil,hs]
      cases hcol : NativeWholeRowService.collapse (finPresentation n) S Δ with
      | true =>
          simp only [hcol, ↓reduceIte, codePlan, kindCode, List.map_nil]
      | false =>
          cases hgrd : NativeWholeRowService.allGround (finPresentation n) S with
          | true =>
              have hb := bindings_project n [(s,t)] S
                (by simpa only [encodeEquations,List.map_cons,List.map_nil] using hs) hgrd
              simpa [hcol, hgrd, codePlan, kindCode] using hb
          | false =>
              simp [hcol, hgrd, codePlan, kindCode]


def renameTerm {X Y : Type} (f : X → Y) : Term X → Term Y :=
  FreeMagma.map (Sum.map id f)

private theorem rename_encode {X Y : Type} (p : Presentation Y) (e : X ≃ Y)
    (t : Term X) : encode p (renameTerm e t) = encode (p.transport e) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r hl hr => exact congrArg₂ NativeTermUnification.pair hl hr

private theorem equations_transport {X Y : Type} (p : Presentation Y) (e : X ≃ Y)
    (E : Equations X) :
    encodeEquations p (E.map (fun z => (renameTerm e z.1,renameTerm e z.2))) =
      encodeEquations (p.transport e) E := by
  simp only [encodeEquations,List.map_map,Function.comp_def,rename_encode]

private theorem collapse_transport {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (p : Presentation Y) (e : X ≃ Y) (E Δ : Equations X) (S : SubstInfo)
    (hs : (encodeEquations (p.transport e) E).unify SubstInfo.empty = .ok S) :
    NativeWholeRowService.collapse p S
      (Δ.map (fun z => (renameTerm e z.1,renameTerm e z.2))) =
      NativeWholeRowService.collapse (p.transport e) S Δ := by
  have hs' : (encodeEquations p
      (E.map (fun z => (renameTerm e z.1,renameTerm e z.2)))).unify
      SubstInfo.empty = .ok S := by rw [equations_transport]; exact hs
  simp only [NativeWholeRowService.collapse,List.any_map,Function.comp_def]
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [← (NativeTermUnification.encode_injective p).eq_iff,
    ← (NativeTermUnification.encode_injective (p.transport e)).eq_iff,
    action_substitute_encode p _ S hs',action_substitute_encode p _ S hs',
    action_substitute_encode (p.transport e) E S hs,
    action_substitute_encode (p.transport e) E S hs,rename_encode,rename_encode]

private theorem ground_action_native {X : Type} (p : Presentation X)
    (E : Equations X) (S : SubstInfo)
    (hs : (encodeEquations p E).unify SubstInfo.empty = .ok S) (x : X) :
    (termVars (action p S x)).isEmpty =
      (LMonoTy.subst S.subst (.ftvar (p.code x))).freeVars.isEmpty := by
  rw [← action_encode p E S hs x,encode_variables,List.isEmpty_map]

private theorem ground_transport {X Y : Type} (p : Presentation Y) (e : X ≃ Y)
    (E : Equations X) (S : SubstInfo)
    (hs : (encodeEquations (p.transport e) E).unify SubstInfo.empty = .ok S) :
    NativeWholeRowService.allGround p S =
      NativeWholeRowService.allGround (p.transport e) S := by
  have hs' : (encodeEquations p
      (E.map (fun z => (renameTerm e z.1,renameTerm e z.2)))).unify
      SubstInfo.empty = .ok S := by rw [equations_transport]; exact hs
  simp only [NativeWholeRowService.allGround,NativeWholeRowService.boundList,
    NativeTermUnification.Presentation.transport,List.filter_map,List.all_map,
    Function.comp_def,Equiv.apply_symm_apply]
  congr 1
  funext y
  change (termVars (action p S y)).isEmpty =
    (termVars (action (p.transport e) S (e.symm y))).isEmpty
  rw [ground_action_native p _ S hs',ground_action_native (p.transport e) E S hs]
  simp only [NativeTermUnification.Presentation.transport,Equiv.apply_symm_apply]

def ordinalPlan {X : Type} (j : X → Nat) (p : PairPlan X) : PairCode :=
  (p.first,p.second,kindCode p.kind,p.bindings.map (fun b => (j b.1,word b.2)))

theorem plan_transport {X : Type} [DecidableEq X] (n : Nat)
    (e : X ≃ Fin n) (Δ : Equations X) (q r : Address) (s t : Term X) :
    codePlan (planPair (finPresentation n)
      (Δ.map (fun z => (renameTerm e z.1,renameTerm e z.2))) q r
      (renameTerm e s) (renameTerm e t)) =
    ordinalPlan (fun x => (e x).val)
      (planPair ((finPresentation n).transport e) Δ q r s t) := by
  have he := equations_transport (finPresentation n) e [(s,t)]
  simp only [List.map_cons,List.map_nil] at he
  unfold planPair
  rw [he]
  cases hs : (encodeEquations ((finPresentation n).transport e) [(s,t)]).unify
      SubstInfo.empty with
  | error err => rfl
  | ok S =>
      dsimp only
      rw [collapse_transport (finPresentation n) e [(s,t)] Δ S hs,
        ground_transport (finPresentation n) e [(s,t)] S hs]
      split
      · rfl
      · split
        · simp only [codePlan,ordinalPlan,NativeWholeRowService.groundBindings,
            NativeWholeRowService.boundList,NativeTermUnification.Presentation.transport,
            List.filter_map,List.map_map,Function.comp_def,Equiv.apply_symm_apply]
        · rfl


end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
