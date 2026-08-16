/- GID: D5/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal trace-rank spectra need not determine an eight-state functional graph. -/

import Mathlib

/- Library-search audit trail (2026-08-16):
   * Repository searches for `rank spectrum`, `trace spectrum`, `functional graph`,
     iterate-image cardinalities, and equivalent `Semiconj`/`Equiv.Perm` shapes found no equal
     or stronger D5 declaration. The nearby `StableImagePeriodicCore` proves only general
     antitonicity and eventual stabilization of finite iterate ranges.
   * Pinned Mathlib supplies `Function.Semiconj`, `Function.iterate_add_apply`,
     `Finset.image_const`, and `Fintype.card_congr`; they are reused below. Text searches found
     no functional-graph spectrum collision theorem or graph-isomorphism carrier.
   * GitHub Lean-code searches for the spectrum/function-graph statement returned no exact hit;
     the only `Function.Semiconj`/`Equiv.Perm` hits were Mathlib and mirrors. The atom CAS search
     hit only its own digestion residual, and the open-PR search found no colliding lane. -/

namespace D5.S3.ObserverMemory.InverseLimits.FunctionGraphSpectrumCollision

/-- The first explicit self-map, on `0,a,b,c,d,e,f,g` encoded as `Fin 8`. -/
def tauA : Fin 8 -> Fin 8 := ![0, 0, 0, 0, 1, 1, 1, 2]

/-- The second explicit self-map, on `0,a,b,c,d,e,f,g` encoded as `Fin 8`. -/
def tauB : Fin 8 -> Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 2]

/-- The cardinality of the image of the `k`-th iterate, i.e. the rank-spectrum value. -/
def rankSpectrumValue (f : Fin 8 -> Fin 8) (k : Nat) : Nat :=
  (Finset.univ.image (f^[k])).card

/-- The number of fixed points of the `k`-th iterate, i.e. the trace-spectrum value. -/
def traceSpectrumValue (f : Fin 8 -> Fin 8) (k : Nat) : Nat :=
  (Finset.univ.filter (fun x => (f^[k]) x = x)).card

/-- The number of leaf predecessors attached to a specified node. -/
def leafCount (f : Fin 8 -> Fin 8) (parent : Fin 8) : Nat :=
  (Finset.univ.filter fun child =>
    f child = parent /\ (Finset.univ.filter fun x => f x = child).card = 0).card

/-- The multiset of leaf counts at the non-root children of the root `0`. -/
def depthOneLeafMultiset (f : Fin 8 -> Fin 8) : Multiset Nat :=
  (Finset.univ.filter (fun x => x ≠ 0 /\ f x = 0)).val.map (leafCount f)

private theorem tauA_sq (x : Fin 8) : tauA (tauA x) = 0 := by
  fin_cases x <;> rfl

private theorem tauB_sq (x : Fin 8) : tauB (tauB x) = 0 := by
  fin_cases x <;> rfl

private theorem tauA_iterate_ge_two (k : Nat) (hk : 2 <= k) (x : Fin 8) :
    (tauA^[k]) x = 0 := by
  rw [show k = 2 + (k - 2) by omega, Function.iterate_add_apply]
  change tauA (tauA ((tauA^[k - 2]) x)) = 0
  exact tauA_sq _

private theorem tauB_iterate_ge_two (k : Nat) (hk : 2 <= k) (x : Fin 8) :
    (tauB^[k]) x = 0 := by
  rw [show k = 2 + (k - 2) by omega, Function.iterate_add_apply]
  change tauB (tauB ((tauB^[k - 2]) x)) = 0
  exact tauB_sq _

private theorem tauA_rank_ge_two (k : Nat) (hk : 2 <= k) :
    rankSpectrumValue tauA k = 1 := by
  unfold rankSpectrumValue
  have hconstant : tauA^[k] = fun _ => 0 := by
    funext x
    exact tauA_iterate_ge_two k hk x
  rw [hconstant, Finset.image_const Finset.univ_nonempty]
  rfl

private theorem tauB_rank_ge_two (k : Nat) (hk : 2 <= k) :
    rankSpectrumValue tauB k = 1 := by
  unfold rankSpectrumValue
  have hconstant : tauB^[k] = fun _ => 0 := by
    funext x
    exact tauB_iterate_ge_two k hk x
  rw [hconstant, Finset.image_const Finset.univ_nonempty]
  rfl

private theorem tauA_iterate_fixed_iff_zero
    (k : Nat) (hk : 1 <= k) (x : Fin 8) : (tauA^[k]) x = x <-> x = 0 := by
  by_cases htwo : 2 <= k
  · rw [tauA_iterate_ge_two k htwo x]
    exact eq_comm
  · have hk_one : k = 1 := by omega
    subst k
    simp only [Function.iterate_one]
    fin_cases x <;> decide

private theorem tauB_iterate_fixed_iff_zero
    (k : Nat) (hk : 1 <= k) (x : Fin 8) : (tauB^[k]) x = x <-> x = 0 := by
  by_cases htwo : 2 <= k
  · rw [tauB_iterate_ge_two k htwo x]
    exact eq_comm
  · have hk_one : k = 1 := by omega
    subst k
    simp only [Function.iterate_one]
    fin_cases x <;> decide

private theorem trace_spectra_equal (k : Nat) :
    traceSpectrumValue tauA k = traceSpectrumValue tauB k := by
  by_cases hzero : k = 0
  · subst k
    simp [traceSpectrumValue]
  · have hpos : 1 <= k := by omega
    unfold traceSpectrumValue
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (tauA_iterate_fixed_iff_zero k hpos x).trans
      (tauB_iterate_fixed_iff_zero k hpos x).symm

private theorem rank_spectra_equal (k : Nat) :
    rankSpectrumValue tauA k = rankSpectrumValue tauB k := by
  by_cases hzero : k = 0
  · subst k
    simp [rankSpectrumValue]
  by_cases hone : k = 1
  · subst k
    decide
  · have htwo : 2 <= k := by omega
    rw [tauA_rank_ge_two k htwo, tauB_rank_ge_two k htwo]

private theorem fiber_card_eq_of_semiconj
    (e : Equiv.Perm (Fin 8)) (h : Function.Semiconj e tauA tauB) (y : Fin 8) :
    Fintype.card {x : Fin 8 // tauA x = y} =
      Fintype.card {x : Fin 8 // tauB x = e y} := by
  let fiberEquiv : {x : Fin 8 // tauA x = y} ≃ {x : Fin 8 // tauB x = e y} :=
    { toFun := fun x => ⟨e x.1, by rw [<- h x.1, x.2]⟩
      invFun := fun x => ⟨e.symm x.1, by
        apply e.injective
        rw [h (e.symm x.1), e.apply_symm_apply, x.2]⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact e.symm_apply_apply x.1
      right_inv := fun x => by
        apply Subtype.ext
        exact e.apply_symm_apply x.1 }
  exact Fintype.card_congr fiberEquiv

private theorem tauB_fiber_card_ne_three (y : Fin 8) :
    Fintype.card {x : Fin 8 // tauB x = y} ≠ 3 := by
  fin_cases y <;> decide

private theorem not_semiconjugate_by_equiv :
    ¬ (Exists fun e : Equiv.Perm (Fin 8) => Function.Semiconj e tauA tauB) := by
  rintro ⟨e, h⟩
  have hcard := fiber_card_eq_of_semiconj e h 1
  have hleft : Fintype.card {x : Fin 8 // tauA x = 1} = 3 := by decide
  have hright : Fintype.card {x : Fin 8 // tauB x = e 1} = 3 := hcard.symm.trans hleft
  exact tauB_fiber_card_ne_three (e 1) hright

/-- Two explicit eight-state maps have the same complete trace and rank spectra, but their
depth-one leaf multisets differ and no relabeling conjugates their functional graphs. -/
theorem same_trace_rank_spectra_not_function_graph_conjugate :
    tauA 0 = 0 /\ tauA 1 = 0 /\ tauA 2 = 0 /\ tauA 3 = 0 /\
    tauA 4 = 1 /\ tauA 5 = 1 /\ tauA 6 = 1 /\ tauA 7 = 2 /\
    tauB 0 = 0 /\ tauB 1 = 0 /\ tauB 2 = 0 /\ tauB 3 = 0 /\
    tauB 4 = 1 /\ tauB 5 = 1 /\ tauB 6 = 2 /\ tauB 7 = 2 /\
    (forall x, tauA x = x <-> x = 0) /\
    (forall x, tauB x = x <-> x = 0) /\
    Fintype.card (Fin 8) = 8 /\
    rankSpectrumValue tauA 1 = 3 /\ rankSpectrumValue tauB 1 = 3 /\
    (forall k, 2 <= k -> rankSpectrumValue tauA k = 1) /\
    (forall k, 2 <= k -> rankSpectrumValue tauB k = 1) /\
    (forall k, traceSpectrumValue tauA k = traceSpectrumValue tauB k) /\
    (forall k, rankSpectrumValue tauA k = rankSpectrumValue tauB k) /\
    depthOneLeafMultiset tauA = ({3, 1, 0} : Multiset Nat) /\
    depthOneLeafMultiset tauB = ({2, 2, 0} : Multiset Nat) /\
    depthOneLeafMultiset tauA ≠ depthOneLeafMultiset tauB /\
    ¬ (Exists fun e : Equiv.Perm (Fin 8) => Function.Semiconj e tauA tauB) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, by decide,
    by decide, by decide, tauA_rank_ge_two, tauB_rank_ge_two,
    trace_spectra_equal, rank_spectra_equal, by decide, by decide,
    by decide, not_semiconjugate_by_equiv⟩
  · intro x
    fin_cases x <;> decide
  · intro x
    fin_cases x <;> decide

example : Unit := ()

example : Nonempty (Fin 8) := ⟨0⟩

#print axioms same_trace_rank_spectra_not_function_graph_conjugate

end D5.S3.ObserverMemory.InverseLimits.FunctionGraphSpectrumCollision
