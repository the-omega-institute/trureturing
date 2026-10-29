/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sort-sensitive inversion of symbolic row exteriors into consumed bindings. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeWholeRowPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Exact sort-sensitive inversion of symbolic row exteriors into consumed bindings. -/

namespace D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination

open GenealogicalFiberTransport (Source)
open NativeGroundSeparation (Term evaluate)
open NativeSymbolicRecutting (SymbolicExterior exteriorFill)
open ActualCutPartitionDecoder (HoleExterior)

def sourceTerm {X : Type} (u : Source) : Term X :=
  FreeMagma.lift (fun b : Bool => .of (.inl b)) u

def decodeHoleFree : HoleExterior → Option Source
  | .of (.inl b) => some (.of b)
  | .of (.inr _) => none
  | .mul l r =>
      match decodeHoleFree l, decodeHoleFree r with
      | some u, some v => some (.mul u v)
      | _, _ => none

def bindingHolds {X : Type} (v : X → Source) : List (X × Term X) → Prop
  | [] => True
  | (x, t) :: rest => v x = evaluate v t ∧ bindingHolds v rest

def matchExterior {X : Type} : SymbolicExterior X → HoleExterior →
    Option (List (X × Term X))
  | .of (.inl (.inl b)), .of (.inl c) =>
      if b = c then some [] else none
  | .of (.inl (.inl _)), _ => none
  | .of (.inl (.inr x)), u =>
      (decodeHoleFree u).map (fun s => [(x, sourceTerm s)])
  | .of (.inr q), .of (.inr r) =>
      if q = r then some [] else none
  | .of (.inr _), _ => none
  | .mul p q, .mul u v =>
      match matchExterior p u, matchExterior q v with
      | some bp, some bq => some (bp ++ bq)
      | _, _ => none
  | .mul _ _, _ => none

private theorem evaluate_sourceTerm {X : Type} (v : X → Source) (u : Source) :
    evaluate v (sourceTerm u) = u :=
  NativeWholeRowService.evaluate_embedded v u

private theorem decodeHoleFree_sound (u : HoleExterior) (s : Source)
    (h : decodeHoleFree u = some s) : FreeMagma.map Sum.inl s = u := by
  induction u generalizing s with
  | of a =>
      cases a with
      | inl b =>
          simp only [decodeHoleFree] at h
          cases h
          rfl
      | inr q => simp [decodeHoleFree] at h
  | mul l r ihl ihr =>
      cases hs : decodeHoleFree l with
      | none => simp [decodeHoleFree, hs] at h
      | some sl =>
          cases hr : decodeHoleFree r with
          | none => simp [decodeHoleFree, hs, hr] at h
          | some sr =>
              cases s with
              | of b => simp [decodeHoleFree, hs, hr] at h
              | mul s₁ s₂ =>
                  simp only [decodeHoleFree, hs, hr, Option.some.injEq] at h
                  cases h
                  exact congrArg₂ FreeMagma.mul (ihl sl hs) (ihr sr hr)

private theorem decodeHoleFree_map (s : Source) :
    decodeHoleFree (FreeMagma.map Sum.inl s) = some s := by
  induction s with
  | of b => rfl
  | mul l r ihl ihr =>
      change decodeHoleFree
        (FreeMagma.mul (FreeMagma.map Sum.inl l) (FreeMagma.map Sum.inl r)) = _
      simp [decodeHoleFree, ihl, ihr]

private theorem bindingHolds_append {X : Type} (v : X → Source)
    (a b : List (X × Term X)) :
    bindingHolds v (a ++ b) ↔ bindingHolds v a ∧ bindingHolds v b := by
  induction a with
  | nil => simp [bindingHolds]
  | cons h a ih =>
      cases h with
      | mk x t => simp only [List.cons_append, bindingHolds, ih, and_assoc]

private theorem matchExterior_sound {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) (bs : List (X × Term X))
    (hm : matchExterior p u = some bs) (hb : bindingHolds v bs) :
    exteriorFill v p = u := by
  induction p generalizing u bs with
  | of a =>
      cases a with
      | inl a =>
          cases a with
          | inl b =>
              cases u with
              | of c =>
                  cases c with
                  | inl c =>
                      simp only [matchExterior] at hm
                      split at hm <;> simp_all [exteriorFill]
                  | inr q => simp [matchExterior] at hm
              | mul l r => simp [matchExterior] at hm
          | inr x =>
              obtain ⟨s, hs, hbs⟩ := Option.map_eq_some_iff.mp hm
              subst bs
              have hxs : v x = s := by
                simpa [bindingHolds, evaluate_sourceTerm] using hb
              have hmap := decodeHoleFree_sound u s hs
              simpa [exteriorFill, hxs] using hmap
      | inr q =>
          cases u with
          | of c =>
              cases c with
              | inl b => simp [matchExterior] at hm
              | inr r =>
                  simp only [matchExterior] at hm
                  split at hm <;> simp_all [exteriorFill]
          | mul l r => simp [matchExterior] at hm
  | mul p q ihp ihq =>
      cases u with
      | of a => simp [matchExterior] at hm
      | mul u w =>
          cases hpm : matchExterior p u with
          | none => simp [matchExterior, hpm] at hm
          | some bp =>
              cases hqm : matchExterior q w with
              | none => simp [matchExterior, hpm, hqm] at hm
              | some bq =>
                  have hbs : bp ++ bq = bs := by
                    simpa [matchExterior, hpm, hqm] using hm
                  rw [← hbs] at hb
                  have hsplit := (bindingHolds_append v bp bq).mp hb
                  change exteriorFill v p * exteriorFill v q = u * w
                  rw [ihp u bp hpm hsplit.1, ihq w bq hqm hsplit.2]

private theorem matchExterior_complete {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) (he : exteriorFill v p = u) :
    ∃ bs, matchExterior p u = some bs ∧ bindingHolds v bs := by
  induction p generalizing u with
  | of a =>
      cases a with
      | inl a =>
          cases a with
          | inl b =>
              cases u with
              | of c =>
                  cases c with
                  | inl c =>
                      simp only [exteriorFill] at he
                      have : b = c := by cases he; rfl
                      subst c
                      exact ⟨[], by simp [matchExterior], trivial⟩
                  | inr q => cases he
              | mul l r => cases he
          | inr x =>
              have hd : decodeHoleFree u = some (v x) := by
                rw [← he]
                simp [exteriorFill, decodeHoleFree_map]
              exact ⟨[(x, sourceTerm (v x))], by
                simp [matchExterior, hd, evaluate_sourceTerm, bindingHolds]⟩
      | inr q =>
          cases u with
          | of c =>
              cases c with
              | inl b => cases he
              | inr r =>
                  have : q = r := by cases he; rfl
                  subst r
                  exact ⟨[], by simp [matchExterior], trivial⟩
          | mul l r => cases he
  | mul p q ihp ihq =>
      cases u with
      | of a => simp [exteriorFill] at he
      | mul u w =>
          have hp : exteriorFill v p = u := by injection he with hp _
          have hq : exteriorFill v q = w := by injection he with _ hq
          obtain ⟨bp, hbp, hbpp⟩ := ihp u hp
          obtain ⟨bq, hbq, hbqq⟩ := ihq w hq
          exact ⟨bp ++ bq, by simp [matchExterior, hbp, hbq],
            (bindingHolds_append v bp bq).mpr ⟨hbpp, hbqq⟩⟩

theorem exterior_match_exact {X : Type} (p : SymbolicExterior X)
    (u : HoleExterior) (v : X → Source) :
    exteriorFill v p = u ↔
      ∃ bs, matchExterior p u = some bs ∧ bindingHolds v bs := by
  constructor
  · exact matchExterior_complete p u v
  · rintro ⟨bs, hm, hb⟩
    exact matchExterior_sound p u v bs hm hb



open ActualTreeReadoutAcquisition (Address)
open ActualCutPartitionRecovery (CutSet CutPrefixFree)
open ActualCutPartitionDecoder (literalRecord)
open NativeSymbolicRecutting
  (termAt symbolicOrdered symbolicPartition symbolicRecord symbolicExterior DeepAt symbolic_recut_exact)
open NativeTermUnification (Presentation)
open NativeGroundSolutionSpace (Equations Sol Diseq)

abbrev RawRow := CutSet × HoleExterior × Finset (Address × Address)
abbrev SignedConstraints (X : Type) := Equations X × Equations X

/-- Every ordered reached pair is retained, including diagonals and both orders. -/
def reachedPairs {X : Type} (Q : CutSet) (t : Term X) : Finset (Address × Address) :=
  (symbolicOrdered Q t).toFinset.product (symbolicOrdered Q t).toFinset

def pairTerms {X : Type} (t : Term X) (pq : Address × Address) : Term X × Term X :=
  ((termAt pq.1 t).getD (.of (.inl false)),
   (termAt pq.2 t).getD (.of (.inl false)))

def rowPairList {X : Type} (Q : CutSet) (t : Term X) : List (Address × Address) :=
  (symbolicOrdered Q t).product (symbolicOrdered Q t)

private theorem row_pair_list_mem {X : Type} (Q : CutSet) (t : Term X)
    (pq : Address × Address) : pq ∈ rowPairList Q t ↔ pq ∈ reachedPairs Q t := by
  simp [rowPairList, reachedPairs]

def positivePairs {X : Type} (Q : CutSet) (t : Term X)
    (K : Finset (Address × Address)) : Equations X :=
  ((rowPairList Q t).filter (fun pq => decide (pq ∈ K))).map (pairTerms t)

def negativePairs {X : Type} (Q : CutSet) (t : Term X)
    (K : Finset (Address × Address)) : Equations X :=
  ((rowPairList Q t).filter (fun pq => decide (pq ∉ K))).map (pairTerms t)

def bindingEquations {X : Type} (bs : List (X × Term X)) : Equations X :=
  bs.map (fun b => (.of (.inr b.1), b.2))

def constraintsHold {X : Type} (c : SignedConstraints X) (v : X → Source) : Prop :=
  Sol c.1 v ∧ Diseq c.2 v

def mergeConstraints {X : Type} (a b : SignedConstraints X) : SignedConstraints X :=
  (a.1 ++ b.1, a.2 ++ b.2)

/-- Raw labels are checked against the actual symbolic reached set. No
partition validity or attained-label certificate is supplied. -/
def compileRow {X : Type} (t : Term X) (r : RawRow) : Option (SignedConstraints X) :=
  if r.2.2 ⊆ reachedPairs r.1 t then
    (matchExterior (symbolicExterior r.1 [] t) r.2.1).map
      (fun bs => (bindingEquations bs ++ positivePairs r.1 t r.2.2,
        negativePairs r.1 t r.2.2))
  else none

def compileRows {X : Type} (t : Term X) : List RawRow → Option (SignedConstraints X)
  | [] => some ([], [])
  | r :: rs => do
      let a ← compileRow t r
      let b ← compileRows t rs
      pure (mergeConstraints a b)

private theorem binding_equations_exact {X : Type} (v : X → Source)
    (bs : List (X × Term X)) : Sol (bindingEquations bs) v ↔ bindingHolds v bs := by
  induction bs with
  | nil => simp [Sol, bindingEquations, bindingHolds]
  | cons b bs ih =>
      simp only [bindingEquations, List.map_cons, Sol, List.mem_cons, forall_eq_or_imp]
      change (v b.1 = evaluate v b.2 ∧ Sol (bindingEquations bs) v) ↔ _
      rw [ih]
      rfl

private theorem constraints_merge_exact {X : Type} (a b : SignedConstraints X)
    (v : X → Source) :
    constraintsHold (mergeConstraints a b) v ↔ constraintsHold a v ∧ constraintsHold b v := by
  simp only [constraintsHold, mergeConstraints, Sol, Diseq, List.mem_append,
    or_imp, forall_and]
  tauto

private theorem pair_terms_exact {X : Type} (Q : CutSet) (t : Term X)
    (v : X → Source) (pq : Address × Address) (hp : pq ∈ reachedPairs Q t) :
    (termAt pq.1 t).map (evaluate v) = (termAt pq.2 t).map (evaluate v) ↔
      evaluate v (pairTerms t pq).1 = evaluate v (pairTerms t pq).2 := by
  have hp' := Finset.mem_product.mp hp
  have h₁ : (termAt pq.1 t).isSome := by
    have h := (Finset.mem_filter.mp ((Finset.mem_sort _).mp
      (List.mem_toFinset.mp hp'.1))).2
    exact h
  have h₂ : (termAt pq.2 t).isSome := by
    have h := (Finset.mem_filter.mp ((Finset.mem_sort _).mp
      (List.mem_toFinset.mp hp'.2))).2
    exact h
  cases ha : termAt pq.1 t <;> cases hb : termAt pq.2 t <;>
    simp_all [pairTerms]

private theorem partition_constraints_exact {X : Type} (Q : CutSet) (t : Term X)
    (K : Finset (Address × Address)) (v : X → Source) :
    symbolicPartition Q t v = K ↔ K ⊆ reachedPairs Q t ∧
      Sol (positivePairs Q t K) v ∧ Diseq (negativePairs Q t K) v := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro pq hp
      rw [← h] at hp
      exact (Finset.mem_filter.mp hp).1
    · intro c hc
      obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hp, hk⟩ : pq ∈ reachedPairs Q t ∧ pq ∈ K := by
        simpa only [List.mem_filter, decide_eq_true_eq, row_pair_list_mem] using hpq
      have hs : pq ∈ symbolicPartition Q t v := h.symm ▸ hk
      exact (pair_terms_exact Q t v pq hp).mp (Finset.mem_filter.mp hs).2
    · intro c hc he
      obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hp, hk⟩ : pq ∈ reachedPairs Q t ∧ pq ∉ K := by
        simpa only [List.mem_filter, decide_eq_true_eq, row_pair_list_mem] using hpq
      apply hk
      rw [← h]
      exact Finset.mem_filter.mpr ⟨hp, (pair_terms_exact Q t v pq hp).mpr he⟩
  · rintro ⟨sub, pos, neg⟩
    ext pq
    constructor
    · intro hpq
      obtain ⟨hp, he⟩ := Finset.mem_filter.mp hpq
      by_contra hk
      apply neg (pairTerms t pq) (List.mem_map.mpr ⟨pq,
        (by simpa only [List.mem_filter, decide_eq_true_eq, row_pair_list_mem]
          using (show pq ∈ reachedPairs Q t ∧ pq ∉ K from ⟨hp, hk⟩)), rfl⟩)
      exact (pair_terms_exact Q t v pq hp).mp he
    · intro hk
      have hp := sub hk
      apply Finset.mem_filter.mpr
      refine ⟨hp, (pair_terms_exact Q t v pq hp).mpr ?_⟩
      exact pos (pairTerms t pq) (List.mem_map.mpr ⟨pq,
        (by simpa only [List.mem_filter, decide_eq_true_eq, row_pair_list_mem]
          using (show pq ∈ reachedPairs Q t ∧ pq ∈ K from ⟨hp, hk⟩)), rfl⟩)

private theorem compile_row_exact {X : Type} (t : Term X) (r : RawRow)
    (v : X → Source) :
    symbolicRecord r.1 t v = r.2 ↔
      ∃ c, compileRow t r = some c ∧ constraintsHold c v := by
  rcases r with ⟨Q, u, K⟩
  change (exteriorFill v (symbolicExterior Q [] t), symbolicPartition Q t v) = (u, K) ↔ _
  rw [Prod.mk.injEq, partition_constraints_exact]
  by_cases sub : K ⊆ reachedPairs Q t
  · cases hm : matchExterior (symbolicExterior Q [] t) u with
    | none =>
        have no : exteriorFill v (symbolicExterior Q [] t) ≠ u := by
          intro he
          obtain ⟨bs, hb, _⟩ := (exterior_match_exact _ _ v).mp he
          rw [hm] at hb
          cases hb
        simp [compileRow, sub, hm, no]
    | some bs =>
        have ext : exteriorFill v (symbolicExterior Q [] t) = u ↔ bindingHolds v bs := by
          constructor
          · intro he
            obtain ⟨cs, hc, hh⟩ := (exterior_match_exact _ _ v).mp he
            rw [hm] at hc
            cases hc
            exact hh
          · exact fun hb => (exterior_match_exact _ _ v).mpr ⟨bs, hm, hb⟩
        rw [ext]
        simp only [compileRow, sub, ↓reduceIte, hm, Option.map_some, Option.some.injEq,
          exists_eq_left', constraintsHold, Sol, List.mem_append, or_imp, forall_and]
        rw [show (∀ c ∈ bindingEquations bs, evaluate v c.1 = evaluate v c.2) ↔
          bindingHolds v bs from binding_equations_exact v bs]
        simp only [sub, true_and]
        tauto
  · simp [compileRow, sub]

private theorem compile_rows_exact {X : Type} (t : Term X) (rs : List RawRow)
    (v : X → Source) :
    (∀ r ∈ rs, symbolicRecord r.1 t v = r.2) ↔
      ∃ c, compileRows t rs = some c ∧ constraintsHold c v := by
  induction rs with
  | nil => simp [compileRows, constraintsHold, Sol, Diseq]
  | cons r rs ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [compile_row_exact, ih]
      constructor
      · rintro ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩
        exact ⟨mergeConstraints a b, by simp [compileRows, ha, hb],
          (constraints_merge_exact a b v).mpr ⟨hsa, hsb⟩⟩
      · rintro ⟨c, hc, hs⟩
        cases ha : compileRow t r with
        | none => simp [compileRows, ha] at hc
        | some a =>
            cases hb : compileRows t rs with
            | none => simp [compileRows, ha, hb] at hc
            | some b =>
                have he : mergeConstraints a b = c := by simpa [compileRows, ha, hb] using hc
                subst c
                obtain ⟨hsa, hsb⟩ := (constraints_merge_exact a b v).mp hs
                exact ⟨⟨a, rfl, hsa⟩, ⟨b, rfl, hsb⟩⟩

/-- A simultaneous substitution may change the finite variable carrier. -/
def rebind {X Y : Type} (theta : X → Term Y) : Term X →ₙ* Term Y :=
  FreeMagma.lift (Sum.elim (fun b => .of (.inl b)) theta)

private theorem rebind_evaluate {X Y : Type} (theta : X → Term Y)
    (z : Y → Source) (t : Term X) :
    NativeTermUnification.evaluate z (rebind theta t) =
      NativeTermUnification.evaluate (fun x => evaluate z (theta x)) t := by
  have h : (evaluate z).comp (rebind theta) =
      evaluate (fun x => evaluate z (theta x)) := by
    apply FreeMagma.hom_ext
    funext a
    cases a <;> rfl
  exact congrArg (fun f : Term X →ₙ* Source => f t) h

/-- Enumerate precisely the unbound original variables, without dropping
unused coordinates from the supplied finite presentation. -/
def unboundVariables {X : Type} (p : Presentation X) (S : Lambda.SubstInfo) :
    List (NativeGroundSolutionSpace.Y p S) :=
  p.enumeration.attach.filterMap (fun x =>
    if h : x.val ∉ NativeGroundSolutionSpace.D p S then some ⟨x.val, h⟩ else none)

private theorem unbound_complete {X : Type} (p : Presentation X) (S : Lambda.SubstInfo)
    (x : NativeGroundSolutionSpace.Y p S) : x ∈ unboundVariables p S := by
  apply List.mem_filterMap.mpr
  refine ⟨⟨x.val, p.complete x.val⟩, by simp, ?_⟩
  dsimp only
  rw [dif_pos x.property]

/-- The free carrier is a subset of the original finite presentation.
There are no positive equations or shape restrictions on its valuations. -/
structure RowOutput (X : Type) where
  free : Set X
  enumeration : List free
  complete : ∀ x, x ∈ enumeration
  theta : X → Term free
  delta : Equations free

def outputHolds {X : Type} (o : RowOutput X) (v : X → Source) : Prop :=
  ∃ z : o.free → Source, (∀ x, evaluate z (o.theta x) = v x) ∧ Diseq o.delta z

def eliminateRows {X : Type} (p : Presentation X) (t : Term X)
    (rs : List RawRow) : Option (RowOutput X) :=
  match compileRows t rs with
  | none => none
  | some c =>
      match h : (NativeGroundSolutionSpace.encodeEquations p c.1).unify Lambda.SubstInfo.empty with
      | .error _ => none
      | .ok S => some {
          free := fun x => x ∉ NativeGroundSolutionSpace.D p S
          enumeration := unboundVariables p S
          complete := unbound_complete p S
          theta := NativeGroundSolutionSpace.sigma p c.1 S h
          delta := c.2.map (fun d =>
            (rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.1,
             rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.2)) }

private theorem mgu_output_exact {X : Type} (p : Presentation X)
    (c : SignedConstraints X) (S : Lambda.SubstInfo)
    (h : (NativeGroundSolutionSpace.encodeEquations p c.1).unify Lambda.SubstInfo.empty = .ok S)
    (v : X → Source) :
    constraintsHold c v ↔ outputHolds {
      free := fun x => x ∉ NativeGroundSolutionSpace.D p S
      enumeration := unboundVariables p S
      complete := unbound_complete p S
      theta := NativeGroundSolutionSpace.sigma p c.1 S h
      delta := c.2.map (fun d =>
        (rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.1,
         rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.2)) } v := by
  have transport (z : NativeGroundSolutionSpace.Y p S → Source) :
      Diseq (c.2.map (fun d =>
        (rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.1,
         rebind (NativeGroundSolutionSpace.sigma p c.1 S h) d.2))) z ↔
      Diseq c.2 (NativeGroundSolutionSpace.Ext p c.1 S h z) := by
    simp only [Diseq, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      rebind_evaluate, NativeGroundSolutionSpace.Ext]
  constructor
  · rintro ⟨sol, neg⟩
    refine ⟨NativeGroundSolutionSpace.restriction p S v, ?_, ?_⟩
    · exact congrFun (NativeGroundSolutionSpace.Ext_restriction p c.1 S h v sol)
    · apply (transport _).mpr
      rw [NativeGroundSolutionSpace.Ext_restriction p c.1 S h v sol]
      exact neg
  · rintro ⟨z, hz, neg⟩
    have same : NativeGroundSolutionSpace.Ext p c.1 S h z = v := funext hz
    refine ⟨?_, ?_⟩
    · rw [← same]
      exact NativeGroundSolutionSpace.Ext_sol p c.1 S h z
    · rw [← same]
      exact (transport z).mp neg

/-- All raw rows are eliminated on one total original variable family.
A successful output may have an empty disequality domain. -/
private theorem symbolic_rows_elimination {X : Type} (p : Presentation X) (t : Term X)
    (rs : List RawRow) (v : X → Source) :
    (∀ r ∈ rs, symbolicRecord r.1 t v = r.2) ↔
      ∃ o, eliminateRows p t rs = some o ∧ outputHolds o v := by
  rw [compile_rows_exact]
  unfold eliminateRows
  cases hc : compileRows t rs with
  | none => simp
  | some c =>
      simp only [Option.some.injEq, exists_eq_left']
      split
      · rename_i e hu
        have no : ¬ constraintsHold c v := by
          intro h
          obtain ⟨S, hs⟩ := NativeGroundSolutionSpace.native_complete p c.1 v h.1
          rw [hu] at hs
          cases hs
        simp [no]
      · rename_i S hu
        simpa only [Option.some.injEq, exists_eq_left'] using mgu_output_exact p c S hu v


/-- The same executable output describes arbitrary symbolic rows and the
actual rows of every sufficiently deep original prefix pattern. -/
theorem complete_row_elimination {X : Type} (p : Presentation X) (t : Term X)
    (rs : List RawRow) (v : X → Source) :
    ((∀ r ∈ rs, symbolicRecord r.1 t v = r.2) ↔
      ∃ o, eliminateRows p t rs = some o ∧ outputHolds o v) ∧
    ∀ (d : Nat) (pat : NativeDepthPatterns.Pattern d)
      (name : NativeDepthPatterns.Frontier pat → X),
      t = NativeHistoryCells.patternTerm pat name →
      (∀ r ∈ rs, CutPrefixFree r.1) →
      (∀ r ∈ rs, ∀ q ∈ r.1, q.length < d) →
      ((∀ r ∈ rs, literalRecord r.1 (NativeDepthPatterns.fill pat (v ∘ name)) = r.2) ↔
        ∃ o, eliminateRows p t rs = some o ∧ outputHolds o v) := by
  have hs := symbolic_rows_elimination p t rs v
  refine ⟨hs, ?_⟩
  intro d pat name ht prefix bound
  have deep : DeepAt d [] t := by
    rw [ht]
    exact NativeHistoryCells.pattern_deep d d pat name [] (by simp)
  have filled : evaluate v t = NativeDepthPatterns.fill pat (v ∘ name) := by
    rw [ht]
    exact NativeHistoryCells.pattern_evaluate d pat name v
  have rows :
      (∀ r ∈ rs, literalRecord r.1 (NativeDepthPatterns.fill pat (v ∘ name)) = r.2) ↔
      (∀ r ∈ rs, symbolicRecord r.1 t v = r.2) := by
    constructor <;> intro h r hr
    · have he := (symbolic_recut_exact d r.1 (prefix r hr) (bound r hr) t deep v).2.2.2
      rw [filled] at he
      exact he.symm.trans (h r hr)
    · have he := (symbolic_recut_exact d r.1 (prefix r hr) (bound r hr) t deep v).2.2.2
      rw [filled] at he
      exact he.trans (h r hr)
  exact rows.trans hs

end D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeSymbolicRowElimination
