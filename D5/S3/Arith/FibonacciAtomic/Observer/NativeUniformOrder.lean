/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformOrder
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive lexicographic address order and exact native cut enumeration. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformTree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis

open D5.S0.Computability.PreorderTreeEvaluation
open ActualTreeReadoutAcquisition (Address)
open Lambda.UniformNativeUnification (TermN)

private def lexChildren (p : Address × Address) : List (Address × Address) :=
  if p.1 = [] ∨ p.2 = [] then [] else [(p.1.tail,p.2.tail)]

private def lexStep (p : Address × Address) (out : List Bool) : Option Bool :=
  if p.1 = [] then some (decide (p.2 ≠ [])) else
  if p.2 = [] then some false else
  if p.1.headI = p.2.headI then out.head? else some (!p.1.headI && p.2.headI)

private theorem lex_children_prim : Primrec lexChildren := by
  unfold lexChildren
  exact Primrec.ite
    ((Primrec.eq.comp Primrec.fst (Primrec.const [])).or
      (Primrec.eq.comp Primrec.snd (Primrec.const []))) (Primrec.const [])
    (Primrec.list_cons.comp
      ((Primrec.list_tail.comp Primrec.fst).pair (Primrec.list_tail.comp Primrec.snd))
      (Primrec.const []))

private theorem lex_step_prim : Primrec₂ lexStep := by
  unfold lexStep
  refine Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const []))
    (Primrec.option_some.comp
      (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const [])).not.decide) ?_
  refine Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))
    (Primrec.const (some false)) ?_
  refine Primrec.ite
    (Primrec.eq.comp (Primrec.list_headI.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_headI.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.list_head?.comp Primrec.snd) ?_
  exact Primrec.option_some.comp
    (Primrec.and.comp (Primrec.not.comp (Primrec.list_headI.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_headI.comp (Primrec.snd.comp Primrec.fst)))

/-- The native list lexicographic order is decided uniformly on arbitrary addresses. -/
theorem address_lt_prim : PrimrecRel ((· < ·) : Address → Address → Prop) := by
  have h : Primrec (fun p : Address × Address => decide (p.1 < p.2)) := by
    apply Primrec.nat_omega_rec' _
      (m := fun p => p.1.length + p.2.length) (l := lexChildren) (g := lexStep)
    · exact Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)
    · exact lex_children_prim
    · exact lex_step_prim
    · rintro ⟨a,b⟩ z hz
      cases a with
      | nil => simp [lexChildren] at hz
      | cons x a => cases b with
        | nil => simp [lexChildren] at hz
        | cons y b =>
            simp [lexChildren] at hz
            subst z
            simp only [List.length_cons,List.tail_cons]
            omega
    · rintro ⟨a,b⟩
      cases a with
      | nil =>
          cases b with
          | nil => simp [lexStep]
          | cons y b =>
              have h : ([] : Address) < y :: b := List.Lex.nil
              simp [lexStep,h]
      | cons x a => cases b with
        | nil =>
            have h : ¬ x :: a < ([] : Address) := fun h => by cases h
            simp [lexStep,h]
        | cons y b =>
            cases x <;> cases y
            · have h : (false :: a < false :: b) ↔ a < b := List.lex_cons_iff
              simp [lexStep,lexChildren,h]
            · have h : false :: a < true :: b := List.Lex.rel (by decide)
              simp [lexStep,lexChildren,h]
            · have h : ¬ true :: a < false :: b := by
                intro h
                cases h with
                | rel h => exact (by decide : ¬ (true < false)) h
              simp [lexStep,lexChildren,h]
            · have h : (true :: a < true :: b) ↔ a < b := List.lex_cons_iff
              simp [lexStep,lexChildren,h]
  exact h.primrecPred

theorem address_le_prim : PrimrecRel ((· ≤ ·) : Address → Address → Prop) :=
  (address_lt_prim.or Primrec.eq).of_eq (fun _ => le_iff_lt_or_eq.symm)

private theorem sort_addresses_prim : Primrec (fun qs : List Address =>
    qs.toFinset.sort (· ≤ ·)) := by
  have hsort := (primitive_list_algorithms ((· ≤ ·) : Address → Address → Prop)
    address_le_prim).2
  have hdedup := (primitive_list_algorithms ((· ≤ ·) : Address → Address → Prop)
    address_le_prim).1
  refine (hsort.comp hdedup).of_eq ?_
  intro qs
  change List.insertionSort (· ≤ ·) qs.dedup = _
  have hnodup := (List.perm_insertionSort (· ≤ ·) qs.dedup).nodup_iff.mpr (List.nodup_dedup qs)
  have hpair := List.pairwise_insertionSort (r := ((· ≤ ·) : Address → Address → Prop)) qs.dedup
  have hfin : (List.insertionSort (· ≤ ·) qs.dedup).toFinset = qs.toFinset := by
    ext a
    simp only [List.mem_toFinset]
    exact (List.perm_insertionSort (· ≤ ·) qs.dedup).mem_iff.trans (List.mem_dedup)
  rw [← hfin]
  exact ((List.toFinset_sort (· ≤ ·) hnodup).mpr hpair).symm

/-- Sorting and filtering use the original native address order, including arbitrary inputs. -/
theorem symbolic_ordered_prim : Primrec₂ (fun (qs : List Address) (t : TermN) =>
    NativeSymbolicRecutting.symbolicOrdered qs.toFinset t) := by
  have hr : PrimrecRel (fun (q : Address) (t : TermN) =>
      (NativeSymbolicRecutting.termAt q t).isSome = true) :=
    Primrec.eq.comp (Primrec.option_isSome.comp (term_at_prim.comp Primrec.fst Primrec.snd))
      (Primrec.const true)
  have hfilter : Primrec₂ (fun (qs : List Address) (t : TermN) =>
      qs.filter (fun q => (NativeSymbolicRecutting.termAt q t).isSome)) :=
    (PrimrecRel.listFilter hr).of_eq (fun qs t => by simp)
  exact (sort_addresses_prim.comp hfilter).of_eq (fun p => by
    simp [NativeSymbolicRecutting.symbolicOrdered,List.toFinset_filter])

end D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformAnalysis
