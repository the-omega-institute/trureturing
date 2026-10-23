/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteBudgetClassification
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Lawful deep perturbations preserve all old inequalities and complete literal history. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowService

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery ActualCutPartitionDecoder
open NativeDepthPatterns (Pattern Frontier fill frontierAddress depthEquiv History)
open NativeCutFibers (Classes)
open NativeHistoryCells NativeSymbolicRecutting
open NativeGroundSeparation (Term code code_mass code_injective bounded_eval_injective)
open NativeGroundSolutionSpace hiding Source fill
open NativeTermUnification (Presentation finPresentation evaluate)
open NativeWholeRowService
open Lambda Strata.Util

/-- Ground every other coordinate, retaining exactly one unary unknown. -/
def unarySpecialize {X : Type} [DecidableEq X] (v : X → Source) (x : X) :
    Term X →ₙ* Term (Fin 1) :=
  FreeMagma.lift (Sum.elim (fun b => .of (.inl b))
    (fun y => if y = x then .of (.inr 0) else FreeMagma.map Sum.inl (v y)))

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem ground_embed_any {X : Type} (v : X → Source) (g : Source) :
    evaluate v (FreeMagma.map Sum.inl g) = g := by
  induction g with
  | of b => rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem unary_evaluate {X : Type} [DecidableEq X] (v : X → Source)
    (x : X) (w : Source) (t : Term X) :
    evaluate (fun _ : Fin 1 => w) (unarySpecialize v x t) =
      evaluate (Function.update v x w) t := by
  induction t with
  | of b => cases b with
    | inl b => rfl
    | inr y =>
        change evaluate (fun _ : Fin 1 => w)
          (if y = x then .of (.inr 0) else FreeMagma.map Sum.inl (v y)) =
          Function.update v x w y
        by_cases he : y = x
        · subst y
          rw [if_pos rfl]
          simp only [evaluate, FreeMagma.lift_of, Sum.elim_inr, Function.update_self]
        · rw [if_neg he, Function.update_of_ne he, ground_embed_any]
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- A distinguishing unary base point prevents an empty-domain unifier;
any successful unary equation therefore has at most one finite ground root. -/
private theorem unary_roots_unique (A B : Term (Fin 1)) (w₀ w wprime : Source)
    (base : evaluate (fun _ => w₀) A ≠ evaluate (fun _ => w₀) B)
    (root : evaluate (fun _ => w) A = evaluate (fun _ => w) B)
    (rootprime : evaluate (fun _ => wprime) A = evaluate (fun _ => wprime) B) : w = wprime := by
  let p := finPresentation 1
  let E : Equations (Fin 1) := [(A,B)]
  have sol (z : Source) (hz : evaluate (fun _ => z) A = evaluate (fun _ => z) B) :
      Sol E (fun _ => z) := by simpa [Sol, E] using hz
  obtain ⟨S,hok⟩ := native_complete p E (fun _ => w) (sol w root)
  have bound : (0 : Fin 1) ∈ D p S := by
    by_contra hn
    have ident (i : Fin 1) : action p S i = .of (.inr i) := by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact action_identity p S 0 hn
    have ext : Ext p E S hok (restriction p S (fun _ => w₀)) = (fun _ => w₀) := by
      funext i
      unfold NativeGroundSolutionSpace.Ext sigma
      rw [evaluate_restrictTerm, ident]
      rfl
    have hs := Ext_sol p E S hok (restriction p S (fun _ => w₀))
    rw [ext] at hs
    exact base (hs (A,B) (by simp [E]))
  have restrict : restriction p S (fun _ => w) = restriction p S (fun _ => wprime) := by
    funext y
    have hy : y.val = (0 : Fin 1) := Subsingleton.elim _ _
    exact False.elim (y.property (hy.symm ▸ bound))
  have eq : (fun _ : Fin 1 => w) = (fun _ : Fin 1 => wprime) := by
    rw [← Ext_restriction p E S hok _ (sol w root),
      ← Ext_restriction p E S hok _ (sol wprime rootprime), restrict]
  exact congrFun eq 0

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem one_old_equation_finite {X : Type} [DecidableEq X] (v : X → Source)
    (x : X) (A B : Term X) (base : evaluate v A ≠ evaluate v B) :
    Set.Finite {w : Source | evaluate (Function.update v x w) A =
      evaluate (Function.update v x w) B} := by
  apply Set.Subsingleton.finite
  intro w hw wprime hwprime
  apply unary_roots_unique (unarySpecialize v x A) (unarySpecialize v x B) (v x) w wprime
  · simpa only [unary_evaluate, Function.update_eq_self] using base
  · change evaluate (Function.update v x w) A = evaluate (Function.update v x w) B at hw
    simpa only [unary_evaluate] using hw
  · change evaluate (Function.update v x wprime) A = evaluate (Function.update v x wprime) B at hwprime
    simpa only [unary_evaluate] using hwprime

def forbidden {X : Type} [DecidableEq X] (Δ : Equations X) (v : X → Source) (x : X) :
    Set Source := {w | ¬ Diseq Δ (Function.update v x w)}

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- The complete finite old disequality family excludes only finitely many replacements. -/
private theorem forbidden_finite {X : Type} [DecidableEq X] (Δ : Equations X)
    (v : X → Source) (x : X) (base : Diseq Δ v) : (forbidden Δ v x).Finite := by
  classical
  induction Δ with
  | nil => simp [forbidden, Diseq]
  | cons e es ih =>
      have first : evaluate v e.1 ≠ evaluate v e.2 := base e (by simp)
      have rest : Diseq es v := fun e he => base e (by simp [he])
      have eq : forbidden (e :: es) v x =
          {w | evaluate (Function.update v x w) e.1 = evaluate (Function.update v x w) e.2} ∪
          forbidden es v x := by
        ext w
        simp only [forbidden, Set.mem_setOf_eq, Set.mem_union, Diseq, List.forall_mem_cons, not_and_or, not_ne_iff]
      rw [eq]
      exact (one_old_equation_finite v x e.1 e.2 first).union (ih rest)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem fill_prefix_constant (d : Nat) (p : Pattern d)
    (f g : Frontier p → Source) (a : Address) (ha : a.length < d) :
    readout a (fill p f) = readout a (fill p g) := by
  have hd := pattern_deep (X := Frontier p) d d p id [] (by simp)
  have hh := original_fill_reply d [] a (patternTerm p id) hd (by simpa using ha) f g
  simpa only [pattern_evaluate, Function.comp_id] using hh

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem closed_pattern_mass (d : Nat) (p : Pattern d) (f : Frontier p → Source)
    (empty : ∀ x : Frontier p, False) : (fill p f).length ≤ 2^d := by
  induction d with
  | zero => exact (empty ()).elim
  | succ d ih => cases p with
    | inl b => simpa [fill, FreeMagma.length] using (Nat.one_le_two_pow : 1 ≤ 2^(d+1))
    | inr p =>
        have hl := ih p.1 (fun x => f (.inl x)) (fun x => empty (.inl x))
        have hr := ih p.2 (fun x => f (.inr x)) (fun x => empty (.inr x))
        change (fill p.1 _).length + (fill p.2 _).length ≤ _
        rw [Nat.pow_succ]
        omega

private def sourceSequence (n : Nat) : Source := code (n+1) ⟨0,by omega⟩

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem sourceSequence_injective : Function.Injective sourceSequence := by
  intro n m he
  have h := congrArg FreeMagma.length he
  simp only [sourceSequence, code_mass] at h
  omega

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- A reached frontier below the inclusive observation depth gives an infinite
cylinder of finite sources, with absent and early-leaf replies unchanged. -/
private theorem infinite_prefix_cylinder (h : Nat) (t : Source)
    (mass : 2^(h+1) < t.length) :
    Set.Infinite {w : Source | ∀ a : Address, a.length ≤ h → readout a w = readout a t} := by
  classical
  let p := (depthEquiv (h+1) t).1
  let f := (depthEquiv (h+1) t).2
  have tf : fill p f = t := (depthEquiv (h+1)).left_inv t
  have existsFront : Nonempty (Frontier p) := by
    by_contra hn
    have empty : ∀ x : Frontier p, False := fun x => hn ⟨x⟩
    have hm := closed_pattern_mass (h+1) p f empty
    rw [tf] at hm
    omega
  obtain ⟨x⟩ := existsFront
  let vary (n : Nat) : Source := fill p (Function.update f x (sourceSequence n))
  have inj : Function.Injective vary := by
    intro n m he
    have hf := congrArg (ActualLeafHistoryRigidity.subtree (frontierAddress p x)) he
    simp only [vary, (NativeDepthPatterns.frontier_geometry (h+1) p).2.1,
      Function.update_self, Option.some.injEq] at hf
    exact sourceSequence_injective hf
  have member : Set.range vary ⊆ {w : Source | ∀ a : Address,
      a.length ≤ h → readout a w = readout a t} := by
    rintro w ⟨n,rfl⟩ a ha
    rw [← tf]
    exact fill_prefix_constant (h+1) p _ f a (by omega)
  exact (Set.infinite_range_of_injective inj).mono member

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Structural evaluation preserves every occurrence of a same-prefix replacement. -/
private theorem evaluate_prefix_congr {X : Type} (v w : X → Source) (h : Nat)
    (same : ∀ x a, a.length ≤ h → readout a (v x) = readout a (w x))
    (t : Term X) : ∀ a : Address, a.length ≤ h →
      readout a (evaluate v t) = readout a (evaluate w t) := by
  induction t with
  | of b => cases b with
    | inl b => intro a ha; rfl
    | inr x => exact same x
  | mul l r hl hr =>
      intro a ha
      cases a with
      | nil => rfl
      | cons b a =>
          have haone : a.length ≤ h := by simp only [List.length_cons] at ha; omega
          cases b
          · simpa [evaluate, readout] using hl a haone
          · simpa [evaluate, readout] using hr a haone

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem large_separation {X : Type} [Fintype X]
    (pairs : Equations X) (distinct : ∀ e ∈ pairs, e.1 ≠ e.2) (threshold : Nat) :
    ∃ (M : Nat) (v : X → Source), threshold < M ∧
      (∀ x, (v x).length = M) ∧ Diseq pairs v := by
  classical
  let L := (pairs.map (fun p => max p.1.length p.2.length)).foldr max 0
  let n := max (Fintype.card X) (max L (threshold+1))
  let e := Fintype.equivFin X
  let cast : Fin (Fintype.card X) → Fin n := fun i =>
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_max_left _ _)⟩
  let v : X → Source := fun x => code n (cast (e x))
  have mass : ∀ x, (v x).length = n+1 := fun x => code_mass n _
  have inj : Function.Injective v := by
    intro x y he
    have q := code_injective n he
    exact e.injective (Fin.ext (congrArg (fun z : Fin n => z.val) q))
  have member_bound (p : Term X × Term X) (hp : p ∈ pairs) :
      max p.1.length p.2.length ≤ L := by
    have hm : max p.1.length p.2.length ∈ pairs.map (fun p => max p.1.length p.2.length) :=
      List.mem_map.mpr ⟨p,hp,rfl⟩
    change _ ≤ (pairs.map (fun p => max p.1.length p.2.length)).foldr max 0
    generalize pairs.map (fun p => max p.1.length p.2.length) = xs at hm ⊢
    induction xs with
    | nil => simp at hm
    | cons a xs ih =>
        rcases List.mem_cons.mp hm with he | he
        · subst a; exact Nat.le_max_left _ _
        · exact (ih he).trans (Nat.le_max_right _ _)
  have hn : L ≤ n := (Nat.le_max_left L _).trans (Nat.le_max_right _ _)
  have ht : threshold+1 ≤ n := (Nat.le_max_right L _).trans (Nat.le_max_right _ _)
  refine ⟨n+1,v,by omega,mass,?_⟩
  intro p hp he
  have hb := member_bound p hp
  apply distinct p hp
  exact bounded_eval_injective v (n+1) (by omega) mass inj p.1 p.2
    (by have := Nat.le_max_left p.1.length p.2.length; omega)
    (by have := Nat.le_max_right p.1.length p.2.length; omega) he

/-- The normalized substitution is applied into the same unbound carrier. -/
def sigmaTerm {X : Type} (p : Presentation X) (E : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S) :
    Term X →ₙ* Term (Y p S) :=
  FreeMagma.lift (Sum.elim (fun b => .of (.inl b)) (sigma p E S hok))

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem restrict_embed {X : Type} (p : Presentation X) (S : SubstInfo)
    (t : Term X) (support : ∀ x ∈ termVars t, x ∉ D p S) :
    FreeMagma.map (Sum.map id Subtype.val) (restrictTerm p S t support) = t := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul (hl _) (hr _)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem sigmaTerm_embed {X : Type} (p : Presentation X) (E : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S)
    (t : Term X) :
    FreeMagma.map (Sum.map id Subtype.val) (sigmaTerm p E S hok t) =
      substitute (action p S) t := by
  induction t with
  | of b => cases b with
    | inl b => rfl
    | inr x => exact restrict_embed p S (action p S x) _
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem sigmaTerm_evaluate {X : Type} (p : Presentation X) (E : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p E).unify SubstInfo.empty = .ok S)
    (w : Y p S → Source) (t : Term X) :
    evaluate w (sigmaTerm p E S hok t) = evaluate (Ext p E S hok w) t := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem restrict_vars {X : Type} (p : Presentation X) (S : SubstInfo)
    (t : Term X) (support : ∀ x ∈ termVars t, x ∉ D p S) :
    (termVars (restrictTerm p S t support)).map Subtype.val = termVars t := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r hl hr => simpa [restrictTerm, termVars, List.map_append] using congrArg₂ List.append (hl _) (hr _)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem variable_mass_lower {X : Type} (v : X → Source) (M : Nat)
    (mass : ∀ x, (v x).length = M) (t : Term X) (hasVar : termVars t ≠ []) :
    M ≤ (evaluate v t).length := by
  induction t with
  | of b => cases b with
    | inl b => exact (hasVar rfl).elim
    | inr x => exact (mass x).ge
  | mul l r hl hr =>
      have which : termVars l ≠ [] ∨ termVars r ≠ [] := by
        by_cases hl : termVars l = []
        · right
          intro hr
          exact hasVar (by simp only [termVars,hl,hr,List.nil_append])
        · exact Or.inl hl
      change M ≤ (evaluate v l).length + (evaluate v r).length
      rcases which with hh | hh
      · exact (hl hh).trans (Nat.le_add_right _ _)
      · exact (hr hh).trans (Nat.le_add_left _ _)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Perturb one genuine nonground binding, preserving the complete old
constraint family and every original reply through an arbitrary inclusive h. -/
theorem lawful_nonground_perturbation {X : Type} [Fintype X] [DecidableEq X]
    (p : Presentation X) (A B : Term X) (Δ : Equations X) (S : SubstInfo)
    (hok : (encodeEquations p [(A,B)]).unify SubstInfo.empty = .ok S)
    (noCollapse : collapse p S Δ = false)
    (x : X) (bound : x ∈ D p S) (nonground : termVars (action p S x) ≠ [])
    (h : Nat) :
    ∃ v w : X → Source, Diseq Δ v ∧ Diseq Δ w ∧
      evaluate v A = evaluate v B ∧ evaluate w A ≠ evaluate w B ∧
      (∀ y a, a.length ≤ h → readout a (v y) = readout a (w y)) := by
  classical
  let E : Equations X := [(A,B)]
  let pulled : Equations (Y p S) := Δ.map
    (fun e => (sigmaTerm p E S hok e.1, sigmaTerm p E S hok e.2))
  have distinct : ∀ e ∈ pulled, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp he
    intro eq
    have eq' := congrArg (FreeMagma.map (Sum.map id Subtype.val)) eq
    rw [sigmaTerm_embed, sigmaTerm_embed] at eq'
    have hc := List.any_eq_false.mp noCollapse t ht
    have : substitute (action p S) t.1 == substitute (action p S) t.2 := by simp [eq']
    simp only [collapse] at noCollapse
    exact hc this
  obtain ⟨M,z,large,mass,legal⟩ := large_separation pulled distinct (2^(h+1))
  let v := Ext p E S hok z
  have vv : Diseq Δ v := by
    intro e he
    have hh := legal _ (List.mem_map.mpr ⟨e,he,rfl⟩)
    simpa only [sigmaTerm_evaluate] using hh
  have root : evaluate v A = evaluate v B := (Ext_sol p E S hok z) (A,B) (by simp [E])
  have sx : termVars (sigma p E S hok x) ≠ [] := by
    intro emp
    have hh := restrict_vars p S (action p S x) (fun y hy => action_support p E S hok x y hy)
    change (termVars (sigma p E S hok x)).map Subtype.val = termVars (action p S x) at hh
    rw [emp,List.map_nil] at hh
    exact nonground hh.symm
  have size : 2^(h+1) < (v x).length :=
    large.trans_le (variable_mass_lower z M mass (sigma p E S hok x) sx)
  have infinite := infinite_prefix_cylinder h (v x) size
  have excluded := (forbidden_finite Δ v x vv).union (Set.finite_singleton (v x))
  obtain ⟨replacement,agree,avoid⟩ := (infinite.diff excluded).nonempty
  have avoidOld : replacement ∉ forbidden Δ v x := fun hh => avoid (Set.mem_union_left _ hh)
  have different : replacement ≠ v x := fun eq => avoid (Set.mem_union_right _ (by simp [eq]))
  let w := Function.update v x replacement
  have ww : Diseq Δ w := by simpa [forbidden, w] using avoidOld
  have restrictions : restriction p S w = restriction p S v := by
    funext y
    have ne : y.val ≠ x := fun eq => y.property (eq.symm ▸ bound)
    exact Function.update_of_ne ne _ _
  have notroot : evaluate w A ≠ evaluate w B := by
    intro eq
    have solw : Sol E w := by simpa [Sol,E] using eq
    have rw' := Ext_restriction p E S hok w solw
    have rv := Ext_restriction p E S hok v (Ext_sol p E S hok z)
    rw [restrictions,rv] at rw'
    have same := congrFun rw' x
    exact different (by simpa [w] using same.symm)
  refine ⟨v,w,vv,ww,root,notroot,?_⟩
  intro y a ha
  by_cases eq : y = x
  · subst y
    simpa [w] using (agree a ha).symm
  · simp only [w, Function.update_of_ne eq]

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem lawful_cell_source (P : CutSet) (hP : CutPrefixFree P) (base : Source)
    (Q : CutSet) (H : History) (η : Patterns (canonicalRow P base) (requiredDepth Q H))
    (pass : feasible η H = true) (v : Variables η → Source) (legal : Diseq (delta η) v) :
    canonicalRow P (evaluate v (wholeTerm η)) = canonicalRow P base ∧
      NativeDepthPatterns.Consistent H (evaluate v (wholeTerm η)) := by
  constructor
  · change canonicalRow P (NativeGroundSeparation.evaluate v (wholeTerm η)) = _
    rw [whole_evaluate]
    exact NativeCutFibers.legal_values_row P hP base ⟨_,(delta_legal η v).mp legal⟩
  · exact feasible_history η H (required_bounds Q H).2 pass v

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem reached_info {X : Type} (Q : CutSet) (t : Term X) (q : Address)
    (hq : q ∈ symbolicOrdered Q t) : q ∈ Q ∧ (termAt q t).isSome := by
  exact Finset.mem_filter.mp ((Finset.mem_sort _).mp hq)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- A feasible nonground binding yields two actual original sources in the
same complete old-row/history fiber at every inclusive original depth. -/
theorem nonground_full_fiber_obstruction (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (base : Source) (H : History)
    (η : Patterns (canonicalRow P base) (requiredDepth Q H))
    (pass : feasible η H = true) (q r : Address)
    (hq : q ∈ symbolicOrdered Q (wholeTerm η))
    (hr : r ∈ symbolicOrdered Q (wholeTerm η))
    (A B : Term (Variables η))
    (atq : termAt q (wholeTerm η) = some A) (atr : termAt r (wholeTerm η) = some B)
    (S : SubstInfo)
    (hok : (encodeEquations (presentation η) [(A,B)]).unify SubstInfo.empty = .ok S)
    (noCollapse : collapse (presentation η) S (delta η) = false)
    (x : Variables η) (bound : x ∈ D (presentation η) S)
    (nonground : termVars (action (presentation η) S x) ≠ []) :
    ∀ h : Nat, ∃ u v : Source,
      (canonicalRow P u = canonicalRow P base ∧ NativeDepthPatterns.Consistent H u) ∧
      (canonicalRow P v = canonicalRow P base ∧ NativeDepthPatterns.Consistent H v) ∧
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) ∧
      canonicalRow Q u ≠ canonicalRow Q v := by
  intro h
  obtain ⟨v,w,vlegal,wlegal,eq,ne,same⟩ := lawful_nonground_perturbation
    (presentation η) A B (delta η) S hok noCollapse x bound nonground h
  let u := evaluate v (wholeTerm η)
  let z := evaluate w (wholeTerm η)
  have us := lawful_cell_source P hP base Q H η pass v vlegal
  have zs := lawful_cell_source P hP base Q H η pass w wlegal
  refine ⟨u,z,us,zs,evaluate_prefix_congr v w h same (wholeTerm η),?_⟩
  intro roweq
  have records := (canonicalRow_record_iff Q hQ u z).mp roweq
  have qe := (reached_info Q (wholeTerm η) q hq).1
  have re := (reached_info Q (wholeTerm η) r hr).1
  have uq := (recutCell Q H hQ η v).subtrees q qe
  have ur := (recutCell Q H hQ η v).subtrees r re
  have zq := (recutCell Q H hQ η w).subtrees q qe
  have zr := (recutCell Q H hQ η w).subtrees r re
  change ActualLeafHistoryRigidity.subtree q u = (termAt q (wholeTerm η)).map (evaluate v) at uq
  change ActualLeafHistoryRigidity.subtree r u = (termAt r (wholeTerm η)).map (evaluate v) at ur
  change ActualLeafHistoryRigidity.subtree q z = (termAt q (wholeTerm η)).map (evaluate w) at zq
  change ActualLeafHistoryRigidity.subtree r z = (termAt r (wholeTerm η)).map (evaluate w) at zr
  rw [atq] at uq zq
  rw [atr] at ur zr
  have uqmem : q ∈ orderedHoles Q u := by
    change q ∈ orderedHoles Q (NativeGroundSeparation.evaluate v (wholeTerm η))
    rw [(recutCell Q H hQ η v).ordering]; exact hq
  have urmem : r ∈ orderedHoles Q u := by
    change r ∈ orderedHoles Q (NativeGroundSeparation.evaluate v (wholeTerm η))
    rw [(recutCell Q H hQ η v).ordering]; exact hr
  have inpart : (q,r) ∈ (literalRecord Q u).2 := by
    simp only [literalRecord, actualPartition, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      List.mem_toFinset]
    exact ⟨⟨uqmem,urmem⟩,uq.trans ((congrArg some eq).trans ur.symm)⟩
  have transferred : (q,r) ∈ (literalRecord Q z).2 := by rw [← records]; exact inpart
  have equal := (Finset.mem_filter.mp transferred).2
  change ActualLeafHistoryRigidity.subtree q z = ActualLeafHistoryRigidity.subtree r z at equal
  rw [zq,zr,Option.map_some,Option.map_some,Option.some.injEq] at equal
  exact ne equal

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem source_embed_injective : Function.Injective
    (FreeMagma.map Sum.inl : Source →ₙ* HoleExterior) := by
  let undo : HoleExterior →ₙ* Source := FreeMagma.lift
    (Sum.elim FreeMagma.of (fun _ => .of true))
  have comp : undo.comp (FreeMagma.map Sum.inl) = MulHom.id Source := by
    apply FreeMagma.hom_ext
    funext b
    rfl
  intro u v he
  have hh := congrArg undo he
  have left (t : Source) : undo (FreeMagma.map Sum.inl t) = t :=
    congrArg (fun f : Source →ₙ* Source => f t) comp
  exact (left u).symm.trans (hh.trans (left v))

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem exterior_update_injective {X : Type} [DecidableEq X]
    (e : SymbolicExterior X) (v : X → Source) (x : X) (hx : x ∈ exteriorVariables e) :
    Function.Injective (fun w => exteriorFill (Function.update v x w) e) := by
  induction e with
  | of b => cases b with
    | inr p => simp [exteriorVariables] at hx
    | inl b => cases b with
      | inl b => simp [exteriorVariables] at hx
      | inr y =>
          have eq : x = y := by simpa [exteriorVariables] using hx
          subst y
          simpa only [exteriorFill,FreeMagma.lift_of,Function.update_self] using source_embed_injective
  | mul l r hl hr =>
      rcases List.mem_append.mp hx with hx | hx
      · intro a b he
        change FreeMagma.mul _ _ = FreeMagma.mul _ _ at he
        injection he with le re
        exact hl hx le
      · intro a b he
        change FreeMagma.mul _ _ = FreeMagma.mul _ _ at he
        injection he with le re
        exact hr hx re

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Any surviving exterior variable has an infinite image of complete actual
new rows on the entire legal old-row/history fiber. -/
theorem exterior_full_fiber_infinite (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (base : Source) (H : History)
    (η : Patterns (canonicalRow P base) (requiredDepth Q H))
    (pass : feasible η H = true) (x : Variables η)
    (outside : x ∈ exteriorVariables (symbolicExterior Q [] (wholeTerm η))) :
    Set.Infinite ((canonicalRow Q) '' {u : Source |
      canonicalRow P u = canonicalRow P base ∧ NativeDepthPatterns.Consistent H u}) := by
  classical
  obtain ⟨v,legal,hist⟩ := (cell_feasibility_exact η H (required_bounds Q H).2).mp pass
  have oldlegal := (delta_legal η v).mpr legal
  have infinite : (Set.range sourceSequence).Infinite := Set.infinite_range_of_injective sourceSequence_injective
  have allowed := infinite.diff (forbidden_finite (delta η) v x oldlegal)
  let row (w : Source) := canonicalRow Q (evaluate (Function.update v x w) (wholeTerm η))
  have inj : Function.Injective row := by
    intro a b he
    have records := (canonicalRow_record_iff Q hQ _ _).mp he
    have exteq := congrArg Prod.fst records
    have ea := (recutCell Q H hQ η (Function.update v x a)).actual
    have eb := (recutCell Q H hQ η (Function.update v x b)).actual
    change (literalRecord Q (NativeGroundSeparation.evaluate (Function.update v x a) (wholeTerm η))).1 =
      (literalRecord Q (NativeGroundSeparation.evaluate (Function.update v x b) (wholeTerm η))).1 at exteq
    rw [← ea, ← eb] at exteq
    exact exterior_update_injective _ v x outside exteq
  have inside : row '' ((Set.range sourceSequence) \ forbidden (delta η) v x) ⊆
      (canonicalRow Q) '' {u : Source | canonicalRow P u = canonicalRow P base ∧
        NativeDepthPatterns.Consistent H u} := by
    rintro r ⟨w,hw,rfl⟩
    have law : Diseq (delta η) (Function.update v x w) := by
      exact not_not.mp hw.2
    exact ⟨_,lawful_cell_source P hP base Q H η pass _ law,rfl⟩
  exact (allowed.image inj.injOn).mono inside

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem equal_pattern_prefix (h : Nat) (u v : Source)
    (eq : (depthEquiv (h+1) u).1 = (depthEquiv (h+1) v).1) :
    ∀ a : Address, a.length ≤ h → readout a u = readout a v := by
  have hu := (depthEquiv (h+1)).left_inv u
  have hv := (depthEquiv (h+1)).left_inv v
  cases eu : depthEquiv (h+1) u with
  | mk p f =>
    cases ev : depthEquiv (h+1) v with
    | mk q g =>
      simp only [eu,ev] at eq hu hv
      subst q
      change (depthEquiv (h+1)).invFun ((depthEquiv (h+1)) u) = u at hu
      change (depthEquiv (h+1)).invFun ((depthEquiv (h+1)) v) = v at hv
      rw [eu] at hu
      rw [ev] at hv
      change fill p f = u at hu
      change fill p g = v at hv
      intro a ha
      rw [← hu,← hv]
      exact fill_prefix_constant (h+1) p f g a (by omega)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem finite_row_image_of_depth (Q : CutSet) (U : Set Source) (h : Nat)
    (determines : ∀ u ∈ U, ∀ v ∈ U,
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) → canonicalRow Q u = canonicalRow Q v) :
    (canonicalRow Q '' U).Finite := by
  classical
  let row (p : Pattern (h+1)) : LiteralRow :=
    if he : ∃ u ∈ U, (depthEquiv (h+1) u).1 = p then
      canonicalRow Q he.choose else .of (.inl true)
  have subset : canonicalRow Q '' U ⊆ Set.range row := by
    rintro r ⟨u,hu,rfl⟩
    refine ⟨(depthEquiv (h+1) u).1,?_⟩
    have he : ∃ v ∈ U, (depthEquiv (h+1) v).1 = (depthEquiv (h+1) u).1 := ⟨u,hu,rfl⟩
    dsimp only [row]
    rw [dif_pos he]
    exact determines he.choose he.choose_spec.1 u hu
      (equal_pattern_prefix h _ _ he.choose_spec.2)
  exact (Set.finite_range row).subset subset

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Exterior freedom refutes every finite determining original depth on the
complete source fiber, without an operational-service premise. -/
theorem exterior_no_finite_depth (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (base : Source) (H : History)
    (η : Patterns (canonicalRow P base) (requiredDepth Q H))
    (pass : feasible η H = true) (x : Variables η)
    (outside : x ∈ exteriorVariables (symbolicExterior Q [] (wholeTerm η))) :
    ∀ h : Nat, ∃ u v : Source,
      (canonicalRow P u = canonicalRow P base ∧ NativeDepthPatterns.Consistent H u) ∧
      (canonicalRow P v = canonicalRow P base ∧ NativeDepthPatterns.Consistent H v) ∧
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) ∧ canonicalRow Q u ≠ canonicalRow Q v := by
  classical
  intro h
  by_contra no
  push_neg at no
  let U : Set Source := {u | canonicalRow P u = canonicalRow P base ∧ NativeDepthPatterns.Consistent H u}
  have determines : ∀ u ∈ U, ∀ v ∈ U,
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) → canonicalRow Q u = canonicalRow Q v := by
    intro u hu v hv same
    exact no u v hu hv same
  exact exterior_full_fiber_infinite P Q hP hQ base H η pass x outside
    (finite_row_image_of_depth Q U h determines)

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
private theorem nonground_plan_witness {X : Type} [DecidableEq X]
    (p : Presentation X) (Δ : Equations X) (q r : Address) (A B : Term X)
    (bad : (planPair p Δ q r A B).kind = .feasibleNonground) :
    ∃ (S : SubstInfo) (x : X),
      (encodeEquations p [(A,B)]).unify SubstInfo.empty = .ok S ∧
      collapse p S Δ = false ∧ x ∈ D p S ∧ termVars (action p S x) ≠ [] := by
  cases hs : (encodeEquations p [(A,B)]).unify SubstInfo.empty with
  | error e => simp [planPair,hs] at bad
  | ok S =>
      by_cases collapseYes : collapse p S Δ = true
      · simp [planPair,hs,collapseYes] at bad
      · have collapseNo : collapse p S Δ = false := Bool.eq_false_of_not_eq_true collapseYes
        by_cases groundYes : allGround p S = true
        · simp [planPair,hs,collapseNo,groundYes] at bad
        · have groundNo : allGround p S = false := Bool.eq_false_of_not_eq_true groundYes
          obtain ⟨x,hx,hn⟩ := List.all_eq_false.mp groundNo
          have hd : x ∈ D p S := by
            change p.code x ∈ S.subst.keys
            exact of_decide_eq_true (List.mem_filter.mp hx).2
          have ng : termVars (action p S x) ≠ [] := by
            intro eq
            simp [eq] at hn
          exact ⟨S,x,rfl,collapseNo,hd,ng⟩

set_option maxHeartbeats 2000000 in
-- The finite dependent carrier and transcript proofs require extended elaboration fuel.
/-- Failure of the executable entire criterion supplies lawful actual
whole-row counterexamples at every inclusive depth. -/
theorem criterion_failure_arbitrary_depth (P Q : CutSet) (hP : CutPrefixFree P)
    (hQ : CutPrefixFree Q) (base : Source) (H : History)
    (bad : (analyze (canonicalRow P base) Q H).passes = false) :
    ∀ h : Nat, ∃ u v : Source,
      (canonicalRow P u = canonicalRow P base ∧ NativeDepthPatterns.Consistent H u) ∧
      (canonicalRow P v = canonicalRow P base ∧ NativeDepthPatterns.Consistent H v) ∧
      (∀ a : Address, a.length ≤ h → readout a u = readout a v) ∧ canonicalRow Q u ≠ canonicalRow Q v := by
  classical
  obtain ⟨η,hη,badCell⟩ := List.all_eq_false.mp bad
  have pass : feasible η H = true := (List.mem_filter.mp hη).2
  by_cases outside : (exteriorVariables (symbolicExterior Q [] (wholeTerm η))).isEmpty = true
  · have pairBad : (pairPlans Q η).all (fun p => p.kind != .feasibleNonground) = false := by
      apply Bool.eq_false_of_not_eq_true
      intro good
      exact badCell (by simp [cellPass, outside, good])
    obtain ⟨plan,hplan,badPlan⟩ := List.all_eq_false.mp pairBad
    have kind : plan.kind = .feasibleNonground := by simpa using badPlan
    obtain ⟨q,hq,hplan⟩ := List.mem_flatMap.mp hplan
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hplan
    have rmem := (List.mem_filter.mp hr).1
    obtain ⟨A,atq⟩ := Option.isSome_iff_exists.mp (reached_info Q (wholeTerm η) q hq).2
    obtain ⟨B,atr⟩ := Option.isSome_iff_exists.mp (reached_info Q (wholeTerm η) r rmem).2
    simp only [atq,atr,Option.getD_some] at kind
    obtain ⟨S,x,hok,nocollapse,hd,ng⟩ := nonground_plan_witness (presentation η) (delta η) q r A B kind
    exact nonground_full_fiber_obstruction P Q hP hQ base H η pass q r hq rmem A B atq atr
      S hok nocollapse x hd ng
  · have ne : exteriorVariables (symbolicExterior Q [] (wholeTerm η)) ≠ [] := by
      intro eq
      simp [eq] at outside
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ ne
    exact exterior_no_finite_depth P Q hP hQ base H η pass x hx

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteBudgetClassification
