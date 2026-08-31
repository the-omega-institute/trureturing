/- GID: D5/S3/Observer/Separation/CongruenceClosureDuality
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/CongruenceClosureDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Forward congruences have dual repairs, common fixed points, and an adjoint triple. -/

import D5.S3.Observer.Separation.CongruenceKernel
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Closure

/- Library-search audit trail (2026-09-01):
   * Five-route repository searches found no receipt for the source atom and no
     theorem giving both repairs. The exact D5 hit `congruence_kernel_laws`
     supplies the maximal stable subrelation and is reused for the interior.
     Nearby source-closure, commuting-closure, and consequence fixed-point
     modules have different carriers or only one closure direction.
   * Pinned Mathlib's `ClosureOperator.ofCompletePred`, `isClosed_iff`,
     `closure_min`, and `ClosureOperator.gi` provide the closure side. The
     complete lattice on `Setoid` and `Setoid.sInf_iff` show that forward
     congruences are closed under arbitrary infima.
   * No `InteriorOperator` declaration was found in pinned Mathlib. The
     interior is therefore packaged as a `ClosureOperator` on the order dual.
     Searches of the other installed Lean packages found no matching API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Separation.CongruenceClosureDuality

open D5.S3.Observer.Separation.CongruenceKernel

universe u

/-- The pair-set underlying a setoid. This connects Mathlib's lattice of
setoids to the relation carrier used by `congruenceKernel`. -/
def setoidRelation {Y : Type u} (R : Setoid Y) : StateRelation Y :=
  {pair | R pair.1 pair.2}

/-- An equivalence relation is an `F`-congruence when it is preserved by the
forward update. -/
def IsForwardCongruence {Y : Type u} (update : Y -> Y) (R : Setoid Y) : Prop :=
  forall {y y'}, R y y' -> R (update y) (update y')

/-- The greatest forward congruence contained in an equivalence relation. -/
def congruenceInterior {Y : Type u} (update : Y -> Y) (R : Setoid Y) : Setoid Y where
  r y y' := (y, y') ∈ congruenceKernel update (setoidRelation R)
  iseqv := (congruence_kernel_laws update (setoidRelation R) R.iseqv).1

private theorem congruenceInterior_isForward {Y : Type u} (update : Y -> Y)
    (R : Setoid Y) : IsForwardCongruence update (congruenceInterior update R) := by
  intro y y' hyy'
  exact (congruence_kernel_laws update (setoidRelation R) R.iseqv).2.1 hyy'

private theorem congruenceInterior_le {Y : Type u} (update : Y -> Y)
    (R : Setoid Y) : congruenceInterior update R <= R := by
  intro y y' hyy'
  exact (congruence_kernel_laws update (setoidRelation R) R.iseqv).2.2.1 hyy'

private theorem congruenceInterior_mono {Y : Type u} (update : Y -> Y) :
    Monotone (congruenceInterior update) := by
  intro R S hRS
  have hrelations : setoidRelation R ⊆ setoidRelation S := by
    intro pair hpair
    exact hRS hpair
  intro y y' hyy'
  exact
    (congruence_kernel_laws update (setoidRelation S) S.iseqv).2.2.2.1
      (setoidRelation R) hrelations hyy'

private theorem le_congruenceInterior {Y : Type u} (update : Y -> Y)
    {S R : Setoid Y} (hS : IsForwardCongruence update S) (hSR : S <= R) :
    S <= congruenceInterior update R := by
  have hstable : TauCongruence update (setoidRelation S) := by
    intro y y' hyy'
    exact hS hyy'
  have hrelations : setoidRelation S ⊆ setoidRelation R := by
    intro pair hpair
    exact hSR hpair
  intro y y' hyy'
  exact
    (congruence_kernel_laws update (setoidRelation R) R.iseqv).2.2.2.2.2.1
      (setoidRelation S) hstable hrelations hyy'

private theorem congruenceInterior_idempotent {Y : Type u} (update : Y -> Y)
    (R : Setoid Y) :
    congruenceInterior update (congruenceInterior update R) =
      congruenceInterior update R := by
  apply le_antisymm
  · exact congruenceInterior_le update (congruenceInterior update R)
  · exact le_congruenceInterior update (congruenceInterior_isForward update R) le_rfl

/-- The predictive interior, represented by the standard closure-operator API
on the order-dual lattice of equivalence relations. -/
def congruenceInteriorOperator {Y : Type u} (update : Y -> Y) :
    ClosureOperator (OrderDual (Setoid Y)) :=
  ClosureOperator.mk'
    (fun R : OrderDual (Setoid Y) =>
      (congruenceInterior update (show Setoid Y from R) : OrderDual (Setoid Y)))
    (fun _ _ h => congruenceInterior_mono update h)
    (congruenceInterior_le update)
    (by
      intro R
      change congruenceInterior update R <=
        congruenceInterior update (congruenceInterior update R)
      exact le_of_eq (congruenceInterior_idempotent update R).symm)

private theorem isForwardCongruence_sInf {Y : Type u} (update : Y -> Y)
    (relations : Set (Setoid Y))
    (hrelations : ∀ R ∈ relations, IsForwardCongruence update R) :
    IsForwardCongruence update (sInf relations) := by
  intro y y' hyy'
  rw [Setoid.sInf_iff] at hyy' |- 
  intro R hR
  exact hrelations R hR (hyy' R hR)

/-- The least forward congruence containing an equivalence relation. -/
def congruenceClosure {Y : Type u} (update : Y -> Y) : ClosureOperator (Setoid Y) :=
  ClosureOperator.ofCompletePred (IsForwardCongruence update)
    (isForwardCongruence_sInf update)

private theorem congruenceInterior_fixed_iff {Y : Type u} (update : Y -> Y)
    (R : Setoid Y) :
    congruenceInterior update R = R <-> IsForwardCongruence update R := by
  constructor
  · intro hfixed
    rw [<- hfixed]
    exact congruenceInterior_isForward update R
  · intro hstable
    exact le_antisymm (congruenceInterior_le update R)
      (le_congruenceInterior update hstable le_rfl)

private theorem congruenceClosure_fixed_iff {Y : Type u} (update : Y -> Y)
    (R : Setoid Y) :
    congruenceClosure update R = R <-> IsForwardCongruence update R := by
  change congruenceClosure update R = R <->
    (congruenceClosure update).IsClosed R
  exact (congruenceClosure update).isClosed_iff.symm

/-- The ordered type of forward congruences for a fixed update. -/
abbrev ForwardCongruences {Y : Type u} (update : Y -> Y) :=
  {R : Setoid Y // IsForwardCongruence update R}

/-- Inclusion of forward congruences into all equivalence relations. -/
def congruenceInclusion {Y : Type u} (update : Y -> Y) :
    ForwardCongruences update -> Setoid Y :=
  fun R => R.1

/-- Closure repair, regarded as a forward congruence. -/
def closureRepair {Y : Type u} (update : Y -> Y) (R : Setoid Y) :
    ForwardCongruences update :=
  ⟨congruenceClosure update R,
    (congruenceClosure_fixed_iff update (congruenceClosure update R)).1
      ((congruenceClosure update).idempotent R)⟩

/-- Interior repair, regarded as a forward congruence. -/
def interiorRepair {Y : Type u} (update : Y -> Y) (R : Setoid Y) :
    ForwardCongruences update :=
  ⟨congruenceInterior update R, congruenceInterior_isForward update R⟩

private theorem closureRepair_galois {Y : Type u} (update : Y -> Y) :
    GaloisConnection (closureRepair update) (congruenceInclusion update) := by
  intro R S
  constructor
  · intro h
    exact ((congruenceClosure update).le_closure R).trans h
  · intro h
    apply (congruenceClosure update).closure_min h
    exact (congruenceClosure update).isClosed_iff.2
      ((congruenceClosure_fixed_iff update S.1).2 S.2)

private theorem interiorRepair_galois {Y : Type u} (update : Y -> Y) :
    GaloisConnection (congruenceInclusion update) (interiorRepair update) := by
  intro S R
  constructor
  · intro h
    exact le_congruenceInterior update S.2 h
  · intro h
    change S.1 <= congruenceInterior update R at h
    exact h.trans (congruenceInterior_le update R)

/-- Predictive interior and forgetting closure obey their three operator laws,
have exactly the forward congruences as their common fixed points, form the
adjoint triple `C_F ⊣ inclusion ⊣ I_F`, and sandwich every equivalence
relation between its two canonical repairs. -/
theorem dual_congruence_repair_laws {Y : Type u} (update : Y -> Y) :
    (forall R : Setoid Y, congruenceInterior update R <= R) /\
    Monotone (congruenceInterior update) /\
    (forall R : Setoid Y,
      congruenceInterior update (congruenceInterior update R) =
        congruenceInterior update R) /\
    (forall R : Setoid Y, R <= congruenceClosure update R) /\
    Monotone (congruenceClosure update) /\
    (forall R : Setoid Y,
      congruenceClosure update (congruenceClosure update R) =
        congruenceClosure update R) /\
    (forall R : Setoid Y,
      congruenceInterior update R = R <-> IsForwardCongruence update R) /\
    (forall R : Setoid Y,
      IsForwardCongruence update R <-> congruenceClosure update R = R) /\
    GaloisConnection (closureRepair update) (congruenceInclusion update) /\
    GaloisConnection (congruenceInclusion update) (interiorRepair update) /\
    (forall R : Setoid Y,
      congruenceInterior update R <= R /\ R <= congruenceClosure update R) := by
  exact
    ⟨congruenceInterior_le update,
      congruenceInterior_mono update,
      congruenceInterior_idempotent update,
      (congruenceClosure update).le_closure,
      (congruenceClosure update).monotone,
      (congruenceClosure update).idempotent,
      congruenceInterior_fixed_iff update,
      fun R => (congruenceClosure_fixed_iff update R).symm,
      closureRepair_galois update,
      interiorRepair_galois update,
      fun R =>
        ⟨congruenceInterior_le update R, (congruenceClosure update).le_closure R⟩⟩

#print axioms dual_congruence_repair_laws

end D5.S3.Observer.Separation.CongruenceClosureDuality
