/- GID: D5/S3/Combinatorics/Graph/LinearForests/DirectedForestPathOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/DirectedForestPathOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Finite]
   utility: none
   digest: Every finite acyclic partial permutation component has one unique directed path order. -/

import Mathlib.Data.Fintype.Sort
import Mathlib.Order.RelClasses
import Mathlib.Order.Preorder.Finite
import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion

/-! The reachability order of an actual component is a finite directed path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder

open D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open Relation

universe u
variable {V : Type u}

abbrev ComponentFiber (E : V → V → Prop) (A : Component E) :=
  {x : V // Quotient.mk (EqvGen.setoid E) x = A}

private theorem no_intermediate [Finite V]
    (E : V → V → Prop) (hout : Relator.RightUnique E)
    (ha : ∀ x, ¬ TransGen E x x) {x y z : V}
    (hxy : E x y) (hxz : TransGen E x z) (hzy : TransGen E z y) : False := by
  rcases TransGen.head'_iff.mp hxz with ⟨w, hxw, hwz⟩
  have hwy : w = y := (hout hxy hxw).symm
  have hyz : ReflTransGen E y z := by
    simpa [hwy] using hwz
  exact ha y (TransGen.trans_right hyz hzy)

private theorem fiber_comparable [Finite V]
    (E : V → V → Prop) (hout : Relator.RightUnique E)
    (hin : Relator.LeftUnique E) (ha : ∀ x, ¬ TransGen E x x)
    {A : Component E} (x y : ComponentFiber E A) :
    x = y ∨ TransGen E x.1 y.1 ∨ TransGen E y.1 x.1 := by
  classical
  obtain ⟨q, h, Φ, hq, hh, hΦ⟩ := full_cycle_completion_equiv E hout hin ha
  let tx : Tail E := q A
  have hcx : EqvGen E x.1 tx.1 := Quotient.exact (x.2.trans (hq A).symm)
  have hcy : EqvGen E y.1 tx.1 := Quotient.exact (y.2.trans (hq A).symm)
  have hx : ReflTransGen E x.1 tx.1 := path_to_tail E hout ha tx hcx
  have hy : ReflTransGen E y.1 tx.1 := path_to_tail E hout ha tx hcy
  have hx' : ReflTransGen (Function.swap E) tx.1 x.1 :=
    reflTransGen_swap.mpr hx
  have hy' : ReflTransGen (Function.swap E) tx.1 y.1 :=
    reflTransGen_swap.mpr hy
  have htot := ReflTransGen.total_of_right_unique (r := Function.swap E)
    (a := tx.1) (b := x.1) (c := y.1) (fun _ _ _ h₁ h₂ => hin h₁ h₂) hx' hy'
  rcases htot with hxy | hyx
  · rcases reflTransGen_iff_eq_or_transGen.mp hxy with heq | hpath
    · exact Or.inl (Subtype.ext heq.symm)
    · exact Or.inr (Or.inr (transGen_swap.mp hpath))
  · rcases reflTransGen_iff_eq_or_transGen.mp hyx with heq | hpath
    · exact Or.inl (Subtype.ext heq)
    · exact Or.inr (Or.inl (transGen_swap.mp hpath))

private theorem component_path_exists [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (A : Component E) :
    ∃ e : Fin (Nat.card (ComponentFiber E A)) ≃ ComponentFiber E A,
      ∀ i j, E (e i).1 (e j).1 ↔ i.1 + 1 = j.1 := by
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite (ComponentFiber E A)
  let r : ComponentFiber E A → ComponentFiber E A → Prop :=
    fun x y => TransGen E x.1 y.1
  letI : IsStrictTotalOrder (ComponentFiber E A) r := {
    irrefl := fun x h => ha x.1 h
    trans := fun x y z hxy hyz => TransGen.trans hxy hyz
    trichotomous := by
      intro x y hxy hyx
      rcases fiber_comparable E hout hin ha x y with h | h | h
      · exact h
      · exact (hxy h).elim
      · exact (hyx h).elim }
  letI : DecidableRel r := Classical.decRel r
  letI : LinearOrder (ComponentFiber E A) := linearOrderOfSTO r
  have hcard : Fintype.card (ComponentFiber E A) = Nat.card (ComponentFiber E A) :=
    Nat.card_eq_fintype_card.symm
  let e : Fin (Nat.card (ComponentFiber E A)) ≃o ComponentFiber E A :=
    monoEquivOfFin (ComponentFiber E A) hcard
  refine ⟨e, ?_⟩
  intro i j
  constructor
  · intro hxy
    have hlt : e i < e j := by
      change TransGen E (e i).1 (e j).1
      exact TransGen.single hxy
    have hij : i < j := e.lt_iff_lt.mp hlt
    by_contra hstep
    have hgap : i.1 + 1 < j.1 := by omega
    let k : Fin (Nat.card (ComponentFiber E A)) := ⟨i.1 + 1, by omega⟩
    have hik : i < k := by
      apply Fin.lt_def.mpr
      simp [k]
    have hkj : k < j := by simp [k]; omega
    have hzik : TransGen E (e i).1 (e k).1 := by
      exact e.lt_iff_lt.mpr hik
    have hzkj : TransGen E (e k).1 (e j).1 := by
      exact e.lt_iff_lt.mpr hkj
    exact no_intermediate E hout ha hxy hzik hzkj
  · intro hstep
    have hij : i < j := by omega
    have hpath : TransGen E (e i).1 (e j).1 := e.lt_iff_lt.mpr hij
    rcases TransGen.head'_iff.mp hpath with ⟨z, hzi, hzj⟩
    rcases reflTransGen_iff_eq_or_transGen.mp hzj with hzeq | hzy
    · exact hzeq.symm ▸ hzi
    · have hzA : Quotient.mk (EqvGen.setoid E) z = A := by
        calc
          Quotient.mk (EqvGen.setoid E) z = Quotient.mk (EqvGen.setoid E) (e i).1 :=
            (Quotient.sound (EqvGen.rel _ _ hzi)).symm
          _ = A := (e i).2
      let z' : ComponentFiber E A := ⟨z, hzA⟩
      have hiz : e i < z' := by
        change TransGen E (e i).1 z
        exact TransGen.single hzi
      have hzj' : z' < e j := by
        change TransGen E z (e j).1
        exact hzy
      have hik : i < (e.symm z') := by simpa using e.symm.strictMono hiz
      have hkj : (e.symm z') < j := by simpa using e.symm.strictMono hzj'
      have hik' : i.1 < (e.symm z').1 := hik
      have hkj' : (e.symm z').1 < j.1 := hkj
      omega

private theorem path_index_unique {W : Type u} {n : ℕ} (E : W → W → Prop)
    (e f : Fin n ≃ W)
    (he : ∀ i j, E (e i) (e j) ↔ i.1 + 1 = j.1)
    (hf : ∀ i j, E (f i) (f j) ↔ i.1 + 1 = j.1) : f = e := by
  let g : Fin n → Fin n := fun i => e.symm (f i)
  have hg : StrictMono g := by
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have h : E (f i.castSucc) (f i.succ) :=
        (hf _ _).mpr (by simp)
      have h' : (g i.castSucc).1 + 1 = (g i.succ).1 := by
        apply (he _ _).mp
        simpa [g] using h
      exact Fin.lt_def.mpr (by omega)
  have hgid : g = id := hg.eq_id
  apply Equiv.ext
  intro i
  have hi : e.symm (f i) = i := congrFun hgid i
  exact e.symm.injective (by simpa using hi)

/-- Each actual component has a unique exhaustive enumeration whose consecutive
indices are exactly the original directed edges, including isolated singletons. -/
theorem component_path_order [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (ha : ∀ x, ¬ TransGen E x x) (A : Component E) :
    ∃! e : Fin (Nat.card (ComponentFiber E A)) ≃ ComponentFiber E A,
      ∀ i j, E (e i).1 (e j).1 ↔ i.1 + 1 = j.1 := by
  obtain ⟨e, he⟩ := component_path_exists E hout hin ha A
  refine ⟨e, he, ?_⟩
  intro f hf
  exact path_index_unique (fun x y : ComponentFiber E A => E x.1 y.1) e f he hf

end D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder
