/- GID: D5/S0/Rewriting/UniformNativeUnification
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform original-domain projection of exact native unification. -/

import D5.S0.Rewriting.UnificationFuel
import D5.S0.Computability.PreorderTreeEvaluation
import Mathlib.Computability.PartrecCode
import D5.S0.Rewriting.UniformNativeUnificationDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Lambda.UniformNativeUnification
open Strata.Util NativeTermUnification
open D5.S0.Computability.PreorderTreeEvaluation

namespace Code
private theorem name_injective : Function.Injective finName := by
  intro x y h
  have := congrArg (fun s : String => s.toList.length) h
  simpa [finName] using this

theorem native_lift (n : Nat) (t : Term (Fin n)) :
    nativeTerm (liftTerm t) = encode (finPresentation n) t := by
  induction t using FreeMagma.recOn with
  | of a => cases a <;> rfl
  | mul l r hl hr =>
      change pair (nativeTerm (liftTerm l)) (nativeTerm (liftTerm r)) = _
      rw [hl, hr]
      rfl

private theorem native_injective : Function.Injective nativeTerm := by
  intro t
  induction t using FreeMagma.recOn with
  | of a =>
      intro u h
      cases a with
      | inl b => cases u with
        | of c => cases c with
          | inl c => cases b <;> cases c <;> simp_all [nativeTerm, leaf]
          | inr x => cases b <;> simp_all [nativeTerm, leaf]
        | mul l r => cases b <;> simp_all [nativeTerm, leaf, pair]
      | inr x => cases u with
        | of c => cases c with
          | inl b => cases b <;> simp_all [nativeTerm, leaf]
          | inr y =>
              simp only [nativeTerm, LMonoTy.ftvar.injEq] at h
              exact congrArg (fun z => FreeMagma.of (Sum.inr z)) (name_injective h)
        | mul l r => simp [nativeTerm, pair] at h
  | mul l r hl hr =>
      intro u h
      cases u with
      | of c => cases c with
        | inl b => cases b <;> simp [nativeTerm, pair, leaf] at h
        | inr x => simp [nativeTerm, pair] at h
      | mul a b =>
          simp only [nativeTerm, pair, LMonoTy.tcons.injEq, List.cons.injEq] at h
          exact congrArg₂ FreeMagma.mul (hl h.2.1) (hr h.2.2.1)

/-- Substitution is one fully composed native action, not recursive expansion
of a rational tree or an arbitrary satisfying assignment. -/
def apply (S : Store) : TermN → TermN
  | .of (.inl b) => .of (.inl b)
  | .of (.inr x) => (S.lookup x).getD (.of (.inr x))
  | .mul l r => .mul (apply S l) (apply S r)

def vars : TermN → List Nat
  | .of (.inl _) => []
  | .of (.inr x) => [x]
  | .mul l r => vars l ++ vars r

/-- Lookup correspondence is sufficient for all native variable branches;
internal hash bucket order is not used as an output-key order. -/
def Represents (S : Store) (native : Subst) : Prop :=
  ∀ x, native.find? (finName x) = (S.lookup x).map nativeTerm

private theorem native_vars (t : TermN) :
    (nativeTerm t).freeVars = (vars t).map finName := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => cases b <;> rfl
    | inr x => rfl
  | mul l r hl hr => simp [nativeTerm, pair, vars, LMonoTy.freeVars,
      LMonoTys.freeVars, hl, hr]

private theorem apply_represents (S : Store) (native : Subst)
    (h : Represents S native) (t : TermN) :
    LMonoTy.subst native (nativeTerm t) = nativeTerm (apply S t) := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => cases b <;> simp [nativeTerm, leaf, apply,
        LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    | inr x =>
        rw [nativeTerm, LMonoTy.subst_unfold]
        dsimp only
        rw [h x]
        cases hs : S.lookup x <;> simp [apply, nativeTerm, hs]
  | mul l r hl hr =>
      simpa [nativeTerm, pair, apply, LMonoTy.subst_tcons,
        LMonoTys.subst_eq_map] using congrArg₂ pair hl hr

private theorem empty_represents : Represents [] [] := by
  intro x
  rfl

/-- The fresh binding composes into every old value before insertion. The
first lookup convention is retained even when a raw representation repeats keys. -/
def insert (S : Store) (x : Nat) (t : TermN) : Store :=
  (x,t) :: S.map (fun e => (e.1, apply [(x,t)] e.2))

private theorem lookup_map_values (S : Store) (f : TermN → TermN) (x : Nat) :
    (S.map (fun e => (e.1, f e.2))).lookup x = (S.lookup x).map f := by
  induction S with
  | nil => rfl
  | cons e S ih =>
      cases hb : x == e.1 <;> simp only [List.map_cons, List.lookup_cons, hb, ih, Option.map_none, Option.map_some] <;> rw [List.lookup_cons] <;> simp only [hb, Option.map_none, Option.map_some]

private theorem insert_represents (S : Store) (native : Subst)
    (h : Represents S native) (x : Nat) (t : TermN) :
    Represents (insert S x t)
      ((Subst.apply (HMap.single (finName x) (nativeTerm t)) native).insert (finName x) (nativeTerm t)) := by
  intro y
  by_cases he : y = x
  · subst y
    simp [insert, HMaps.find?_insert_self, List.lookup_cons]
  · rw [HMaps.find?_insert_ne _ _ _ _ (by
      exact fun hxy => he (name_injective hxy))]
    rw [Subst.find?_apply, h y]
    have hs : Represents [(x,t)] [HMap.single (finName x) (nativeTerm t)] := by
      intro z
      by_cases hz : z = x
      · subst z; simp [HMaps.find?, HMap.find?_single_self, List.lookup_cons]
      · simp [HMaps.find?, HMap.find?_single_ne, List.lookup_cons, beq_eq_false_iff_ne.mpr hz,
          show finName z ≠ finName x from fun hzx => hz (name_injective hzx)]
    rw [insert, List.lookup_cons]
    simp only [beq_eq_false_iff_ne.mpr he, lookup_map_values, Option.map_map]
    apply congrArg (fun f => (S.lookup y).map f)
    funext u
    exact apply_represents [(x,t)] _ hs u


abbrev Output := Option (Option Store)

mutual
/-- Coding of the existing bounded one-equation evaluator on its native fragment. -/
def one : Nat → (TermN × TermN) → Store → Output
  | 0, _, _ => none
  | fuel+1, (t1,t2), S =>
      if t1 = t2 then some (some S) else
      match t1,t2 with
      | .of (.inr x), orig | orig, .of (.inr x) =>
          let t := apply S orig
          if .of (.inr x) = t then some (some S)
          else if x ∈ vars t then some none
          else match S.lookup x with
            | some old => one fuel (old,t) S
            | none => some (some (insert S x t))
      | .mul l r, .mul l' r' => core fuel [(l,l'),(r,r')] S
      | _,_ => some none
/-- Coding of the native equation-list evaluator, with identical equation order. -/
def core : Nat → Equations Nat → Store → Output
  | 0, _, _ => none
  | fuel+1, [], S => some (some S)
  | fuel+1, e :: E, S =>
      match one fuel e S with
      | none => none
      | some none => some none
      | some (some S') => core fuel E S'
end

/-- Only the outer API discards error payloads. Success retains the complete
lookup action of the actual native finite substitution. -/
inductive Matches : Output → Option UnificationFuel.Result → Prop
  | exhausted : Matches none none
  | failure (e : UnifyError) : Matches (some none) (some (.error e))
  | success {S : Store} {native : Subst} (h : Represents S native) :
      Matches (some (some S)) (some (.ok native))

private theorem native_eq (a b : TermN) :
    (nativeTerm a == nativeTerm b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, native_injective.eq_iff]

private theorem occurs_eq (x : Nat) (t : TermN) :
    finName x ∈ (nativeTerm t).freeVars ↔ x ∈ vars t := by
  rw [native_vars]
  simp only [List.mem_map, native_injective.eq_iff]
  constructor
  · rintro ⟨y,hy,he⟩; exact name_injective he ▸ hy
  · intro h; exact ⟨x,h,rfl⟩

private theorem variable_step (fuel : Nat) (x : Nat) (orig : TermN)
    (S : Store) (native : Subst) (hrep : Represents S native) (c : Constraint)
    (ih : ∀ a b S native, Represents S native →
      Matches (one fuel (a,b) S)
        (UnificationFuel.one fuel (nativeTerm a,nativeTerm b) native)) :
    Matches
      (if FreeMagma.of (Sum.inr x) = apply S orig then some (some S)
       else if x ∈ vars (apply S orig) then some none
       else match S.lookup x with
         | some old => one fuel (old,apply S orig) S
         | none => some (some (insert S x (apply S orig))))
      (if LMonoTy.ftvar (finName x) == LMonoTy.subst native (nativeTerm orig) then
         some (.ok native)
       else if finName x ∈ (LMonoTy.subst native (nativeTerm orig)).freeVars then
         some (.error (.FailedOccursCheck (finName x)
           (LMonoTy.subst native (nativeTerm orig))
           c))
       else match native.find? (finName x) with
         | some old => UnificationFuel.one fuel
             (old,LMonoTy.subst native (nativeTerm orig)) native
         | none => some (.ok ((Subst.apply
             (HMap.single (finName x) (LMonoTy.subst native (nativeTerm orig))) native).insert (finName x) (LMonoTy.subst native (nativeTerm orig))))) := by
  rw [apply_represents S native hrep orig]
  change Matches _ (if nativeTerm (.of (.inr x)) == nativeTerm (apply S orig) then _ else _)
  rw [native_eq]
  simp only [decide_eq_true_eq]
  split
  · exact Matches.success hrep
  · by_cases ho : x ∈ vars (apply S orig)
    · simp only [if_pos ho, if_pos ((occurs_eq x _).mpr ho)]
      exact Matches.failure _
    · simp only [if_neg ho, if_neg (fun h => ho ((occurs_eq x _).mp h))]
      rw [hrep x]
      cases hl : S.lookup x with
      | none => exact Matches.success (insert_represents S native hrep x (apply S orig))
      | some old => exact ih old (apply S orig) S native hrep

private theorem bounded_matches (fuel : Nat) :
    (∀ a b S native, Represents S native →
      Matches (one fuel (a,b) S)
        (UnificationFuel.one fuel (nativeTerm a,nativeTerm b) native)) ∧
    (∀ E S native, Represents S native →
      Matches (core fuel E S)
        (UnificationFuel.core fuel
          (E.map (fun e => (nativeTerm e.1,nativeTerm e.2))) native)) := by
  induction fuel with
  | zero => constructor <;> intros <;> exact Matches.exhausted
  | succ fuel ih =>
      constructor
      · intro a b S native hrep
        simp only [one, UnificationFuel.one, native_eq, decide_eq_true_eq]
        split
        · exact Matches.success hrep
        · rename_i hne
          cases a with
          | of a => cases a with
            | inr x =>
                have h := variable_step fuel x b S native hrep (nativeTerm (.of (.inr x)),nativeTerm b) ih.1
                convert h using 1 <;> simp only [nativeTerm, leaf, pair]
                cases b with
                | of z => cases z <;> rfl
                | mul l r => rfl
            | inl x => cases b with
              | of b => cases b with
                | inr y =>
                    have h := variable_step fuel y (.of (.inl x)) S native hrep (nativeTerm (.of (.inl x)),nativeTerm (.of (.inr y))) ih.1
                    cases x <;> convert h using 1 <;> simp only [nativeTerm, leaf, pair] <;> rfl
                | inl y => cases x <;> cases y <;> simp_all [nativeTerm, leaf] <;> exact Matches.failure _
              | mul l r => cases x <;> simp [nativeTerm, leaf, pair] <;> exact Matches.failure _
          | mul l r => cases b with
            | of b => cases b with
              | inr y =>
                  have h := variable_step fuel y (.mul l r) S native hrep (nativeTerm (.mul l r),nativeTerm (.of (.inr y))) ih.1
                  convert h using 1 <;> simp only [nativeTerm, leaf, pair] <;> rfl
              | inl y => cases y <;> simp [nativeTerm, leaf, pair] <;> exact Matches.failure _
            | mul l' r' =>
                simpa [nativeTerm, pair] using ih.2 [(l,l'),(r,r')] S native hrep
      · intro E S native hrep
        cases E with
        | nil => exact Matches.success hrep
        | cons e E =>
            simp only [core, List.map_cons, UnificationFuel.core]
            have h := ih.1 e.1 e.2 S native hrep
            generalize hc : one fuel (e.1,e.2) S = out at h ⊢
            generalize hn : UnificationFuel.one fuel (nativeTerm e.1,nativeTerm e.2) native = nativeOut at h ⊢
            cases h with
            | exhausted => exact Matches.exhausted
            | failure err => exact Matches.failure (err.addOriginalConstraint _)
            | @success S' native' hs => exact ih.2 E S' native' hs



private theorem tree_of_prim : Primrec (FreeMagma.of : Bool ⊕ Nat → TermN) := by
  apply Primrec.encode_iff.mp
  change Primrec (fun a : Bool ⊕ Nat => Encodable.encode ([some a] : Word (Bool ⊕ Nat)))
  exact Primrec.encode.comp (Primrec.list_cons.comp
    (Primrec.option_some.comp Primrec.id) (Primrec.const []))

private theorem tree_mul_prim : Primrec₂ (FreeMagma.mul : TermN → TermN → TermN) := by
  have hw : Primrec (word : TermN → Word (Bool ⊕ Nat)) :=
    Primrec.encode_iff.mp (show Primrec (fun t : TermN => Encodable.encode (word t)) from Primrec.encode)
  apply Primrec₂.uncurry.mp
  apply Primrec.encode_iff.mp
  change Primrec (fun p : TermN × TermN => Encodable.encode
    (none :: (word p.1 ++ word p.2)))
  exact Primrec.encode.comp (Primrec.list_cons.comp (Primrec.const none)
    (Primrec.list_append.comp (hw.comp Primrec.fst) (hw.comp Primrec.snd)))

private theorem fold_mul {A B : Type} (leaf : A → B) (node : B → B → B)
    (l r : FreeMagma A) :
    (@FreeMagma.lift A B ⟨node⟩ leaf) (.mul l r) =
      node ((@FreeMagma.lift A B ⟨node⟩ leaf) l)
        ((@FreeMagma.lift A B ⟨node⟩ leaf) r) := rfl

theorem apply_prim : Primrec₂ apply := by
  have leaf : Primrec₂ (fun (S : Store) (a : Bool ⊕ Nat) =>
      Sum.elim (fun b => FreeMagma.of (Sum.inl b))
        (fun x => (S.lookup x).getD (.of (.inr x))) a) := by
    refine Primrec.sumCasesOn Primrec.snd ?_ ?_
    · exact (tree_of_prim.comp (Primrec.sumInl.comp Primrec.snd)).to₂
    · exact Primrec.option_getD.comp
        (Primrec.listLookup.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
        (tree_of_prim.comp (Primrec.sumInr.comp Primrec.snd))
  have hf := uniform_tree_fold
    (fun (S : Store) (a : Bool ⊕ Nat) =>
      Sum.elim (fun b => FreeMagma.of (Sum.inl b))
        (fun x => (S.lookup x).getD (.of (.inr x))) a)
    (fun (_ : Store) p => FreeMagma.mul p.1 p.2) leaf
    (tree_mul_prim.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact hf.of_eq (fun S t => by
    induction t using FreeMagma.recOn with
    | of a => cases a <;> rfl
    | mul l r hl hr =>
        try dsimp only [id] at hl hr ⊢
        rw [fold_mul, hl, hr]
        rfl)

theorem vars_prim : Primrec vars := by
  have leaf : Primrec₂ (fun (_ : Nat) (a : Bool ⊕ Nat) =>
      Sum.elim (fun _ => ([] : List Nat)) (fun x => [x]) a) :=
    Primrec.sumCasesOn Primrec.snd (Primrec.const []).to₂
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have h := uniform_tree_fold
    (fun (_ : Nat) (a : Bool ⊕ Nat) => Sum.elim (fun _ => []) (fun x => [x]) a)
    (fun (_ : Nat) (p : List Nat × List Nat) => p.1 ++ p.2) leaf
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (h.comp (Primrec.const 0) Primrec.id).of_eq (fun t => by
    induction t using FreeMagma.recOn with
    | of a => cases a <;> rfl
    | mul l r hl hr =>
        try dsimp only [id] at hl hr ⊢
        rw [fold_mul, hl, hr]
        rfl)

private theorem insert_prim : Primrec (fun p : Store × Nat × TermN => insert p.1 p.2.1 p.2.2) := by
  unfold insert
  refine Primrec.list_cons.comp
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)) ?_
  refine Primrec.list_map Primrec.fst ?_
  exact (Primrec.fst.comp Primrec.snd).pair
    (apply_prim.comp
      (Primrec.list_cons.comp
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const []))
      (Primrec.snd.comp Primrec.snd))

abbrev View := (Bool ⊕ Nat) ⊕ (TermN × TermN)

def view : TermN → View
  | .of a => .inl a
  | .mul l r => .inr (l,r)

private theorem view_prim : Primrec view := by
  have leaf : Primrec₂ (fun (_ : Nat) (a : Bool ⊕ Nat) =>
      (FreeMagma.of a, (Sum.inl a : View))) :=
    (tree_of_prim.comp Primrec.snd).pair (Primrec.sumInl.comp Primrec.snd)
  have node : Primrec₂ (fun (_ : Nat) (p : (TermN × View) × (TermN × View)) =>
      (FreeMagma.mul p.1.1 p.2.1, (Sum.inr (p.1.1,p.2.1) : View))) :=
    (tree_mul_prim.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
    (Primrec.sumInr.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have h := uniform_tree_fold
    (fun (_ : Nat) (a : Bool ⊕ Nat) => (FreeMagma.of a,(Sum.inl a : View)))
    (fun (_ : Nat) (p : (TermN × View) × (TermN × View)) =>
      (FreeMagma.mul p.1.1 p.2.1, (Sum.inr (p.1.1,p.2.1) : View))) leaf node
  have he : ∀ t : TermN, (@FreeMagma.lift (Bool ⊕ Nat) (TermN × View)
      ⟨fun p q => (FreeMagma.mul p.1 q.1,Sum.inr (p.1,q.1))⟩
      (fun a => (FreeMagma.of a,Sum.inl a))) t = (t,view t) := by
    intro t
    induction t using FreeMagma.recOn with
    | of a => rfl
    | mul l r hl hr =>
        try dsimp only [id] at hl hr ⊢
        rw [fold_mul, hl, hr]
        rfl
  exact (Primrec.snd.comp (h.comp (Primrec.const 0) Primrec.id)).of_eq
    (fun t => congrArg Prod.snd (he t))



abbrev Job := (TermN × TermN) ⊕ Equations Nat
abbrev Request := Job × Store
abbrev Action := Output ⊕ Request
abbrev Input := Nat × Request

private def getVar (t : TermN) : Option Nat :=
  Sum.casesOn (view t) (Sum.elim (fun _ => none) some) (fun _ => none)

private theorem getVar_prim : Primrec getVar := by
  unfold getVar
  refine Primrec.sumCasesOn view_prim ?_ (Primrec.const none).to₂
  exact Primrec.sumCasesOn Primrec.snd (Primrec.const none).to₂
    (Primrec.option_some.comp Primrec.snd).to₂

private def children (t : TermN) : Option (TermN × TermN) :=
  Sum.casesOn (view t) (fun _ => none) some

private theorem children_prim : Primrec children :=
  Primrec.sumCasesOn view_prim (Primrec.const none).to₂
    (Primrec.option_some.comp Primrec.snd).to₂

private def varsPair (e : TermN × TermN) : Option (Nat × TermN) :=
  Option.casesOn (getVar e.1) ((getVar e.2).map (fun x => (x,e.1)))
    (fun x => some (x,e.2))

private theorem varsPair_prim : Primrec varsPair := by
  unfold varsPair
  exact Primrec.option_casesOn (getVar_prim.comp Primrec.fst)
    (Primrec.option_map (getVar_prim.comp Primrec.snd)
      (Primrec.snd.pair (Primrec.fst.comp Primrec.fst)).to₂)
    (Primrec.option_some.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂

private def pairs (e : TermN × TermN) : Option (Equations Nat) := do
  let a ← children e.1
  let b ← children e.2
  some [(a.1,b.1),(a.2,b.2)]

private theorem pairs_prim : Primrec pairs := by
  unfold pairs
  refine Primrec.option_bind (children_prim.comp Primrec.fst) ?_
  change Primrec (fun p : (TermN × TermN) × (TermN × TermN) =>
    (children p.1.2).bind fun b => some [(p.2.1,b.1),(p.2.2,b.2)])
  refine Primrec.option_bind (children_prim.comp (Primrec.snd.comp Primrec.fst)) ?_
  change Primrec (fun p : ((TermN × TermN) × (TermN × TermN)) × (TermN × TermN) =>
    some [(p.1.2.1,p.2.1),(p.1.2.2,p.2.2)])
  exact Primrec.option_some.comp (Primrec.list_cons.comp
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.snd)) (Primrec.const [])))

private def varAction (p : Store × Nat × TermN) : Action :=
  if FreeMagma.of (Sum.inr p.2.1) = p.2.2 then .inl (some (some p.1))
  else if p.2.1 ∈ vars p.2.2 then .inl (some none)
  else Option.casesOn (p.1.lookup p.2.1)
    (.inl (some (some (insert p.1 p.2.1 p.2.2))))
    (fun old => .inr (.inl (old,p.2.2),p.1))

private theorem varAction_prim : Primrec varAction := by
  unfold varAction
  refine Primrec.ite
    (Primrec.eq.comp
      (tree_of_prim.comp (Primrec.sumInr.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.sumInl.comp (Primrec.option_some.comp
      (Primrec.option_some.comp Primrec.fst))) ?_
  have mem : PrimrecRel (fun (xs : List Nat) (x : Nat) => x ∈ xs) :=
    (PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel ((· = ·) : Nat → Nat → Prop))).of_eq
      (fun xs x => by simp)
  refine Primrec.ite
    (mem.comp (vars_prim.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)) (Primrec.const (Sum.inl (some none) : Action)) ?_
  refine Primrec.option_casesOn
    (Primrec.listLookup.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
    (Primrec.sumInl.comp (Primrec.option_some.comp (Primrec.option_some.comp insert_prim))) ?_
  exact (Primrec.sumInr.comp
    ((Primrec.sumInl.comp (Primrec.snd.pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
      (Primrec.fst.comp Primrec.fst))).to₂

private def action (p : (TermN × TermN) × Store) : Action :=
  if p.1.1 = p.1.2 then .inl (some (some p.2)) else
  Option.casesOn (varsPair p.1)
    (Option.casesOn (pairs p.1) (.inl (some none))
      (fun E => .inr (.inr E,p.2)))
    (fun v => varAction (p.2,v.1,apply p.2 v.2))

private theorem action_prim : Primrec action := by
  unfold action
  refine Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (Primrec.sumInl.comp (Primrec.option_some.comp
      (Primrec.option_some.comp Primrec.snd))) ?_
  refine Primrec.option_casesOn (varsPair_prim.comp Primrec.fst) ?_ ?_
  · exact Primrec.option_casesOn (pairs_prim.comp Primrec.fst)
      (Primrec.const (Sum.inl (some none) : Action))
      (Primrec.sumInr.comp
        ((Primrec.sumInr.comp Primrec.snd).pair (Primrec.snd.comp Primrec.fst))).to₂
  · exact (varAction_prim.comp
      ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair
          (apply_prim.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))))).to₂

private def bounded (input : Input) : Output :=
  Sum.casesOn input.2.1 (fun e => one input.1 e input.2.2)
    (fun E => core input.1 E input.2.2)

private def resume (fuel : Nat) (a : Action) : Output :=
  Sum.casesOn a id (fun p => bounded (fuel,p))

private theorem action_exact (fuel : Nat) (e : TermN × TermN) (S : Store) :
    resume fuel (action (e,S)) = one (fuel+1) e S := by
  rcases e with ⟨a,b⟩
  by_cases he : a = b
  · simp [action, one, he, resume]
  · simp only [action, one, he, if_false]
    cases a with
    | of a => cases a with
      | inr x =>
          dsimp only [varsPair, getVar, view, varAction, Option.map, Option.casesOn, Sum.casesOn, Sum.elim]
          by_cases h1 : FreeMagma.of (Sum.inr x) = apply S b
          · simp only [h1,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
          · by_cases h2 : x ∈ vars (apply S b)
            · simp only [h1,h2,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
            · cases hl : S.lookup x <;> simp only [h1,h2,hl,if_pos,if_neg,resume,bounded,Sum.casesOn,Option.casesOn,if_true,if_false,id]
      | inl x => cases b with
        | of b => cases b with
          | inl y => rfl
          | inr y =>
              dsimp only [varsPair, getVar, view, varAction, Option.map, Option.casesOn, Sum.casesOn, Sum.elim]
              by_cases h1 : FreeMagma.of (Sum.inr y) = apply S (.of (.inl x))
              · simp only [h1,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
              · by_cases h2 : y ∈ vars (apply S (.of (.inl x)))
                · simp only [h1,h2,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
                · cases hl : S.lookup y <;> simp only [h1,h2,hl,if_pos,if_neg,resume,bounded,Sum.casesOn,Option.casesOn,if_true,if_false,id]
        | mul l r => rfl
    | mul l r => cases b with
      | of b => cases b with
        | inl y => rfl
        | inr y =>
            dsimp only [varsPair, getVar, view, varAction, Option.map, Option.casesOn, Sum.casesOn, Sum.elim]
            by_cases h1 : FreeMagma.of (Sum.inr y) = apply S (.mul l r)
            · simp only [h1,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
            · by_cases h2 : y ∈ vars (apply S (.mul l r))
              · simp only [h1,h2,if_pos,if_neg,resume,Sum.casesOn,if_true,if_false,id]
              · cases hl : S.lookup y <;> simp only [h1,h2,hl,if_pos,if_neg,resume,bounded,Sum.casesOn,Option.casesOn,if_true,if_false,id]
      | mul l' r' => rfl

private def functional (call : Input → Part Output) (input : Input) : Part Output :=
  Nat.casesOn input.1 (Part.some none) (fun fuel =>
    Sum.casesOn input.2.1
      (fun e => Sum.casesOn (action (e,input.2.2)) Part.some (fun p => call (fuel,p)))
      (fun E => List.casesOn E (Part.some (some (some input.2.2))) (fun e rest => do
        let out ← call (fuel,.inl e,input.2.2)
        Option.casesOn out (Part.some none) (fun out =>
          Option.casesOn out (Part.some (some none)) (fun S => call (fuel,.inr rest,S))))))

private def evalCode (c : Nat.Partrec.Code) (input : Input) : Part Output :=
  (c.eval (Encodable.encode input)).bind
    (fun n => Part.ofOption (Encodable.decode (α := Output) n))

private theorem evalCode_partrec : Partrec₂ evalCode := by
  unfold evalCode
  refine Partrec.bind
    (Nat.Partrec.Code.eval_part.comp Computable.fst
      (Computable.encode.comp Computable.snd)) ?_
  exact (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂

private theorem partrec_sumCases {A B C R : Type}
    [Primcodable A] [Primcodable B] [Primcodable C] [Primcodable R]
    {f : A → B ⊕ C} {g : A → B → Part R} {h : A → C → Part R}
    (hf : Computable f) (hg : Partrec₂ g) (hh : Partrec₂ h) :
    Partrec (fun a => Sum.casesOn (f a) (g a) (h a)) := by
  have first : Partrec (fun a => Sum.casesOn (f a)
      (fun b => (g a b).map (Sum.inl : R → R ⊕ C))
      (fun c => Part.some (Sum.inr c : R ⊕ C))) :=
    Partrec.sumCasesOn_left hf
      (Partrec.map hg (Computable.sumInl.comp Computable.snd).to₂).to₂
      (Computable.sumInr.comp Computable.snd).to₂
  have second : Partrec₂ (fun a (s : R ⊕ C) =>
      Sum.casesOn s Part.some (h a)) :=
    (Partrec.sumCasesOn_right Computable.snd Computable.snd.to₂
      (hh.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).to₂
  exact (first.bind second).of_eq (fun a => by
    cases f a <;> simp [Part.bind_assoc, Part.bind_some_eq_map])

abbrev Context := Nat.Partrec.Code × Nat × Store

private def continuePart (p : (Context × Equations Nat) × Output) : Part Output :=
  Option.casesOn p.2 (Part.some none) (fun out =>
    Option.casesOn out (Part.some (some none))
      (fun S => evalCode p.1.1.1 (p.1.1.2.1,.inr p.1.2,S)))

private theorem continuePart_partrec : Partrec continuePart := by
  unfold continuePart
  refine Partrec.optionCasesOn_right Computable.snd (Computable.const none) ?_
  refine Partrec.optionCasesOn_right Computable.snd (Computable.const (some none)) ?_
  exact (evalCode_partrec.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
    ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))).pair ((Computable.sumInr.comp (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))).pair Computable.snd))).to₂

private def onePart (p : Context × (TermN × TermN)) : Part Output :=
  Sum.casesOn (action (p.2,p.1.2.2)) Part.some
    (fun req => evalCode p.1.1 (p.1.2.1,req))

private theorem onePart_partrec : Partrec onePart := by
  unfold onePart
  refine Partrec.sumCasesOn_right
    (action_prim.to_comp.comp (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))) Computable.snd.to₂ ?_
  exact (evalCode_partrec.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair Computable.snd)).to₂

private def corePart (p : Context × Equations Nat) : Part Output :=
  Option.casesOn (p.2.head?.map (fun e => (e,p.2.tail)))
    (Part.some (some (some p.1.2.2))) (fun q => do
      let out ← evalCode p.1.1 (p.1.2.1,.inl q.1,p.1.2.2)
      continuePart ((p.1,q.2),out))

private theorem corePart_partrec : Partrec corePart := by
  unfold corePart
  have hd : Computable (fun E : Equations Nat =>
      E.head?.map (fun e => (e,E.tail))) :=
    Computable.option_map Primrec.list_head?.to_comp
      (Computable.snd.pair (Primrec.list_tail.to_comp.comp Computable.fst)).to₂
  refine Partrec.optionCasesOn_right (hd.comp Computable.snd)
    (Computable.option_some.comp (Computable.option_some.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))) ?_
  refine Partrec.bind
    (evalCode_partrec.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      ((Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair ((Computable.sumInl.comp (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))))) ?_
  exact (continuePart_partrec.comp
    (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd)).to₂

private theorem functional_partrec :
    Partrec (fun p : Nat.Partrec.Code × Input => functional (evalCode p.1) p.2) := by
  have h : Partrec (fun p : Nat.Partrec.Code × Input =>
      Nat.casesOn p.2.1 (Part.some none) (fun fuel =>
        Sum.casesOn p.2.2.1
          (fun e => onePart ((p.1,fuel,p.2.2.2),e))
          (fun E => corePart ((p.1,fuel,p.2.2.2),E)))) := by
    refine Partrec.nat_casesOn_right (Computable.fst.comp Computable.snd)
      (Computable.const none) ?_
    refine partrec_sumCases (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) ?_ ?_
    · exact (onePart_partrec.comp
        (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))))).pair Computable.snd)).to₂
    · exact (corePart_partrec.comp
        (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair ((Computable.snd.comp Computable.fst).pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))))).pair Computable.snd)).to₂
  exact h.of_eq (fun p => by
    rcases p with ⟨c,fuel,job,S⟩
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases job with
      | inl e => rfl
      | inr E => cases E <;> rfl)

private theorem bounded_computable : Computable bounded := by
  let numeric (c : Nat.Partrec.Code) (n : Nat) : Part Nat :=
    Option.casesOn (Encodable.decode (α := Input) n) (Part.some 0)
      (fun input => (functional (evalCode c) input).map Encodable.encode)
  have hn : Partrec₂ numeric := by
    refine Partrec.optionCasesOn_right (Computable.decode.comp Computable.snd)
      (Computable.const 0) ?_
    exact (Partrec.map
      (functional_partrec.comp
        ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (Computable.encode.comp Computable.snd).to₂).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hn
  have hc' : ∀ input : Input, evalCode c input = functional (evalCode c) input := by
    intro input
    change ((c.eval (Encodable.encode input)).bind
      (fun n => Part.ofOption (Encodable.decode (α := Output) n))) = _
    rw [hc]
    simp only [numeric, Encodable.encodek, Option.casesOn]
    simp [Part.bind_assoc, Part.bind_some_eq_map, Part.map_bind, Encodable.encodek]
  have he : ∀ fuel req, evalCode c (fuel,req) = Part.some (bounded (fuel,req)) := by
    intro fuel
    induction fuel with
    | zero =>
        rintro ⟨job,S⟩
        rw [hc']
        cases job <;> rfl
    | succ fuel ih =>
      intro req
      rw [hc']
      rcases req with ⟨job,S⟩
      cases job with
      | inl e =>
          change Sum.casesOn (action (e,S)) Part.some
            (fun p => evalCode c (fuel,p)) = Part.some (one (fuel+1) e S)
          rw [← action_exact]
          cases ha : action (e,S) with
          | inl out => rfl
          | inr req => exact ih req
      | inr E =>
          cases E with
          | nil => rfl
          | cons e E =>
              change ((evalCode c (fuel,.inl e,S)).bind fun out =>
                Option.casesOn out (Part.some none) (fun out =>
                  Option.casesOn out (Part.some (some none))
                    (fun S => evalCode c (fuel,.inr E,S)))) = _
              rw [ih]
              simp only [Part.bind_some, bounded, Sum.casesOn, core]
              cases ho : one fuel e S with
              | none => rfl
              | some out => cases out with
                | none => rfl
                | some S' => exact ih (.inr E,S')
  exact (evalCode_partrec.comp (Computable.const c) Computable.id).of_eq_tot
    (fun input => by
       change bounded input ∈ evalCode c input
       rcases input with ⟨fuel,req⟩
       rw [he]; exact Part.mem_some_iff.mpr rfl)

private theorem finite_run (E : Equations Nat) : ∃ fuel, (core fuel E []).isSome := by
  let cs := E.map (fun e => (nativeTerm e.1,nativeTerm e.2))
  obtain ⟨b,hb⟩ := (UnificationFuel.exact_fuel_simulation cs SubstInfo.empty).1
  have hm := (bounded_matches b).2 E [] [] empty_represents
  have hbe := hb b (Nat.le_refl b)
  change UnificationFuel.core b cs [] = _ at hbe
  rw [hbe] at hm
  cases out : core b E [] with
  | none => rw [out] at hm; cases hm
  | some s => exact ⟨b,by rw [out]; rfl⟩

private def run (E : Equations Nat) : Option Store :=
  (core (Nat.find (finite_run E)) E []).getD none

private theorem run_computable : Computable run := by
  have hb : Computable₂ (fun (E : Equations Nat) (fuel : Nat) => core fuel E []) :=
    (bounded_computable.comp
      (Computable.snd.pair ((Computable.sumInr.comp Computable.fst).pair
        (Computable.const [])))).to₂
  have hp := Partrec.rfindOpt hb
  apply hp.of_eq_tot
  intro E
  -- Every finished execution represents the same native action. Its finite
  -- first-fuel search is total independently of the magnitude of the bound.
  have hr : run E ∈ Nat.rfindOpt (fun fuel => core fuel E []) := by
    unfold run
    let h := finite_run E
    have hn := Nat.find_spec h
    have hfirst : Nat.find h ∈ Nat.rfind
        (fun fuel => Part.some (core fuel E []).isSome) := by
      apply Nat.mem_rfind.mpr
      refine ⟨?_, ?_⟩
      · simpa using hn
      · intro m hm
        have := Nat.find_min h hm
        cases ho : core m E [] <;> simp_all
    apply Part.mem_bind_iff.mpr
    refine ⟨Nat.find h,hfirst,?_⟩
    cases ho : core (Nat.find h) E [] with
    | none => simp [ho] at hn
    | some out => simp [ho]
  exact hr


private theorem lift_lower (n : Nat) (t : TermN) (u : Term (Fin n))
    (h : lowerTerm n t = some u) : liftTerm u = t := by
  induction t using FreeMagma.recOn generalizing u with
  | of a => cases a with
    | inl b => cases h; rfl
    | inr x =>
        simp only [lowerTerm] at h
        split at h
        · cases h; rfl
        · simp at h
  | mul l r hl hr =>
      simp only [lowerTerm] at h
      cases hL : lowerTerm n l <;> cases hR : lowerTerm n r <;> simp_all
      cases h
      exact congrArg₂ FreeMagma.mul hl hr

private theorem decode_native (n : Nat) (t : TermN) :
    nativeDecode (finPresentation n) (nativeTerm t) = lowerTerm n t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => cases b <;> simp [nativeTerm,leaf,nativeDecode,lowerTerm]
    | inr x =>
        simp [nativeTerm, nativeDecode, finPresentation, finName, lowerTerm]
  | mul l r hl hr => simp [nativeTerm, pair, nativeDecode, lowerTerm, hl, hr]

private def clip (n : Nat) (t : TermN) : Option TermN :=
  if inRange n t then some t else none

private theorem clip_lower (n : Nat) (t : TermN) :
    (lowerTerm n t).map liftTerm = clip n t := by
  have hi := lower_range n t
  cases h : lowerTerm n t with
  | none => simp only [h,Option.isSome_none] at hi; simp [clip,← hi,h]
  | some u =>
      simp only [h,Option.isSome_some] at hi
      simp [clip,← hi,h,lift_lower n t u h]

private def projection (n : Nat) (S : Store) : List (Nat × TermN) :=
  ((List.range n).filter (fun x => (S.lookup x).isSome)).map
    (fun x => (x, (clip n (apply S (.of (.inr x)))).getD (.of (.inr x))))

private theorem projection_exact (n : Nat) (S : Store) (native : Subst)
    (h : Represents S native) : projection n S = project n native := by
  have key : ∀ x, decide (finName x ∈ native.keys) = (S.lookup x).isSome := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Option.isSome_iff_exists]
    constructor
    · intro hx
      obtain ⟨v,hv⟩ := HMaps.find?_of_mem_keys native (finName x) hx
      rw [h x] at hv
      cases hl : S.lookup x <;> simp_all
    · rintro ⟨v,hv⟩
      apply HMaps.find?_mem_keys native
      rw [h x,hv]
      rfl
  have val : ∀ i : Fin n,
      (clip n (apply S (.of (.inr i.val)))).getD (.of (.inr i.val)) =
      liftTerm ((nativeDecode (finPresentation n)
        (LMonoTy.subst native (.ftvar ((finPresentation n).code i)))).getD (.of (.inr i))) := by
    intro i
    rw [← clip_lower]
    have ha := apply_represents S native h (.of (.inr i.val))
    change LMonoTy.subst native (.ftvar (finName i.val)) = _ at ha
    change _ = liftTerm ((nativeDecode (finPresentation n)
      (LMonoTy.subst native (.ftvar (finName i.val)))).getD (.of (.inr i)))
    rw [ha,decode_native]
    cases hl : lowerTerm n (apply S (.of (.inr i.val))) <;> rfl
  unfold projection project
  have hr : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hr, List.filter_map, List.map_map]
  have hk : (fun i : Fin n => (S.lookup i.val).isSome) =
      (fun i : Fin n => decide ((finPresentation n).code i ∈ native.keys)) := by
    funext i; exact (key i.val).symm
  dsimp only [Function.comp_def]
  rw [hk]
  apply List.map_congr_left
  intro i hi
  exact congrArg (fun t => (i.val,t)) (val i)


private theorem inRange_prim : Primrec₂ inRange := by
  have leaf : Primrec₂ (fun (n : Nat) (a : Bool ⊕ Nat) =>
      Sum.elim (fun _ => true) (fun x => decide (x < n)) a) := by
    refine Primrec.sumCasesOn Primrec.snd (Primrec.const true).to₂ ?_
    exact (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).decide.to₂
  have h := uniform_tree_fold
    (fun (n : Nat) (a : Bool ⊕ Nat) => Sum.elim (fun _ => true) (fun x => decide (x < n)) a)
    (fun (_ : Nat) (p : Bool × Bool) => p.1 && p.2) leaf
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq (fun n t => by
    induction t using FreeMagma.recOn with
    | of a => cases a <;> rfl
    | mul l r hl hr =>
        try dsimp only [id] at hl hr ⊢
        rw [fold_mul,hl,hr]; rfl)

private theorem clip_prim : Primrec₂ clip := by
  have h : Primrec (fun p : Nat × TermN => bif inRange p.1 p.2 then some p.2 else none) :=
    Primrec.cond inRange_prim (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  change Primrec (fun p : Nat × TermN => clip p.1 p.2)
  exact h.of_eq (fun p => by
    unfold clip
    cases hi : inRange p.1 p.2 <;> simp [hi])

private theorem projection_prim : Primrec₂ projection := by
  have filtered : Primrec (fun p : Nat × Store =>
      (List.range p.1).filter (fun x => (p.2.lookup x).isSome)) := by
    have h : Primrec (fun p : Nat × Store => (List.range p.1).filterMap
        (fun x => bif (p.2.lookup x).isSome then some x else none)) :=
      Primrec.listFilterMap (Primrec.list_range.comp Primrec.fst)
      ((Primrec.cond
        (Primrec.option_isSome.comp (Primrec.listLookup.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
        (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂)
    exact h.of_eq (fun p => by
      simpa only [Option.guard, Bool.cond_eq_ite] using
        congrFun (List.filterMap_eq_filter
          (p := fun x => (p.2.lookup x).isSome)) (List.range p.1))
  change Primrec (fun p : Nat × Store => projection p.1 p.2)
  unfold projection
  refine Primrec.list_map filtered ?_
  exact Primrec.snd.pair (Primrec.option_getD.comp
    (clip_prim.comp (Primrec.fst.comp Primrec.fst)
      (apply_prim.comp (Primrec.snd.comp Primrec.fst)
        (tree_of_prim.comp (Primrec.sumInr.comp Primrec.snd))))
    (tree_of_prim.comp (Primrec.sumInr.comp Primrec.snd)))

private def valid (input : SolverInput) : Bool :=
  input.2.all (fun e => inRange input.1 e.1 && inRange input.1 e.2)

private theorem valid_prim : Primrec valid := by
  have h := Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : SolverInput → Equations Nat))
    (Primrec.const true)
    ((Primrec.and.comp
      (Primrec.and.comp
        (inRange_prim.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (inRange_prim.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun input => by
    unfold valid
    induction input.2 <;> simp_all)

private theorem run_matches (E : Equations Nat) :
    Matches (some (run E)) (some ((Constraints.unify
      (E.map (fun e => (nativeTerm e.1,nativeTerm e.2))) SubstInfo.empty).map SubstInfo.subst)) := by
  let k := Nat.find (finite_run E)
  have hk : (core k E []).isSome := Nat.find_spec (finite_run E)
  have hm := (bounded_matches k).2 E [] [] empty_represents
  cases ho : core k E [] with
  | none => simp [ho] at hk
  | some out =>
      rw [ho] at hm
      cases hn : UnificationFuel.core k
          (E.map (fun e => (nativeTerm e.1,nativeTerm e.2))) [] with
      | none => rw [hn] at hm; cases hm
      | some r =>
          have he := (UnificationFuel.exact_fuel_simulation
            (E.map (fun e => (nativeTerm e.1,nativeTerm e.2))) SubstInfo.empty).2.1 k r hn
          rw [hn,he] at hm
          change Matches (some ((core k E []).getD none)) _
          rw [ho]
          exact hm

private theorem lift_lower_equations (n : Nat) (E : Equations Nat)
    (es : Equations (Fin n)) (h : lowerEquations n E = some es) : liftEquations es = E := by
  induction E generalizing es with
  | nil => cases h; rfl
  | cons e E ih =>
      change ((lowerTerm n e.1).bind fun l => (lowerTerm n e.2).bind fun r =>
        (lowerEquations n E).bind fun tail => some ((l,r)::tail)) = some es at h
      cases hL : lowerTerm n e.1 <;> cases hR : lowerTerm n e.2 <;>
        cases hE : lowerEquations n E <;> simp only [hL,hR,hE,Option.bind_none,Option.bind_some,reduceCtorEq,Option.some.injEq] at h
      subst es
      simp only [liftEquations,List.map_cons]
      rw [lift_lower n _ _ hL,lift_lower n _ _ hR]
      exact congrArg (List.cons e) (ih _ hE)

private def encodedF (input : SolverInput) : SolverOutput :=
  if valid input then some ((run input.2).map (projection input.1)) else none

private theorem encodedF_computable : Computable encodedF := by
  unfold encodedF
  have h : Computable (fun input : SolverInput => bif valid input then
      some ((run input.2).map (projection input.1)) else none) := by
    refine Computable.cond valid_prim.to_comp ?_ (Computable.const (none : SolverOutput))
    exact Computable.option_some.comp (Computable.option_map
      (run_computable.comp Computable.snd)
      (projection_prim.to_comp.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)
  exact h.of_eq (fun input => by cases valid input <;> rfl)

private theorem encodedF_exact (input : SolverInput) : encodedF input = F input := by
  rcases input with ⟨n,E⟩
  cases hl : lowerEquations n E with
  | none =>
      have hr := lower_equations_range n E
      rw [hl] at hr
      have hf : F (n,E) = none := rejection_exact n E |>.mpr (by simpa using hr.symm)
      rw [hf]
      simp [encodedF,valid,← hr]
  | some es =>
      have hE := lift_lower_equations n E es hl
      subst E
      have hr := lower_equations_range n (liftEquations es)
      rw [hl] at hr
      simp only [encodedF,valid,← hr,Option.isSome_some,if_true]
      rw [exact_native]
      have hm := run_matches (liftEquations es)
      have hn : (liftEquations es).map (fun e => (nativeTerm e.1,nativeTerm e.2)) =
          es.map (fun e => (encode (finPresentation n) e.1,encode (finPresentation n) e.2)) := by
        simp only [liftEquations,List.map_map,Function.comp_def,native_lift]
      rw [hn] at hm
      generalize hx : run (liftEquations es) = out at *
      cases hu : Constraints.unify
          (es.map (fun e => (encode (finPresentation n) e.1,encode (finPresentation n) e.2))) SubstInfo.empty with
      | error err =>
          simp only [hu,Except.map_error] at hm
          cases hm
          rfl
      | ok S =>
          simp only [hu,Except.map_ok] at hm
          cases hm with
          | success h =>
              simp only [Option.map_some]
              exact congrArg (fun t => some (some t)) (projection_exact n _ S.subst h)

end Code

/-- The unbounded terminating native solver is computable uniformly in the
finite domain and the complete ordered finite equation input. -/
theorem computable_F : Computable F :=
  Code.encodedF_computable.of_eq Code.encodedF_exact

end Lambda.UniformNativeUnification
