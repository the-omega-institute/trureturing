/- GID: D5/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/QueryFamilyIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dependent query kernels characterize identification, including empty cases. -/
/- Library-search audit trail (2026-08-25):
   * `rg -n 'query.*identification|identification.*kernel' D5` found no exact theorem.
   * The repository hit `universal_sufficiency_factorization` is the single-interface
     theorem. It is reused below with the dependent joint interface `M -> ((i : I) -> A i)`.
   * `GlobalProfileQuotientUniversality` already treats a dependent readout family, but
     proves recovery of its components rather than identification of a target or unique
     target descent through the quotient.
   * Pinned Mathlib exact hits `Function.FactorsThrough`, `Quotient.lift`,
     `Quotient.sound`, and `Quotient.mk_surjective` are all reused below. The local proof
     only assembles the dependent joint kernel and audits its empty cases. -/

import Mathlib.Data.Setoid.Basic
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.QueryFamilyIdentification

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

universe u v w x

/-- The joint interface records the answer to every query in a dependent family. -/
def jointQuery {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) : M -> ((i : I) -> A i) :=
  fun m i => Q i m

/-- Two models are query-equivalent when every query gives the same answer. -/
def queryKernel {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) : M -> M -> Prop :=
  fun m n => forall i, Q i m = Q i n

/-- The equivalence relation induced by simultaneous agreement of the query family. -/
def querySetoid {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) : Setoid M where
  r := queryKernel Q
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h i => (h i).symm
    trans := fun hmn hnp i => (hmn i).trans (hnp i)
  }

/-- The model space modulo simultaneous agreement of all queries. -/
abbrev QueryQuotient {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) :=
  Quotient (querySetoid Q)

/-- The canonical projection to the query quotient. -/
def queryQuotientProjection {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) : M -> QueryQuotient Q :=
  Quotient.mk (querySetoid Q)

/-- A query family identifies a target when the target is constant on joint-query fibers. -/
def IdentifiedBy {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> M -> A i) (T : M -> Z) : Prop :=
  Function.FactorsThrough T (jointQuery Q)

/-- Identification is exactly inclusion of the simultaneous query kernel in the target
kernel. No nonemptiness assumption is needed. -/
theorem identification_iff_kernel_inclusion
    {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> M -> A i) (T : M -> Z) :
    IdentifiedBy Q T <->
      forall m n, queryKernel Q m n -> T m = T n := by
  constructor
  · intro identified m n sameQueries
    apply identified
    funext i
    exact sameQueries i
  · intro kernelInclusion m n sameJointAnswer
    apply kernelInclusion m n
    intro i
    exact congrFun sameJointAnswer i

#print axioms identification_iff_kernel_inclusion

/-- On a nonempty model space, the dependent joint interface connects the family theorem
directly to the existing single-interface refinement theorem. -/
theorem identification_iff_joint_refinement
    {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x} [Nonempty M]
    (Q : (i : I) -> M -> A i) (T : M -> Z) :
    IdentifiedBy Q T <->
      Refines (canonicalTargetReadout T) (jointQuery Q) := by
  have universal := universal_sufficiency_factorization (jointQuery Q) T
  simpa [IdentifiedBy, Function.FactorsThrough] using
    (universal.1.trans universal.2).symm

#print axioms identification_iff_joint_refinement

/-- Empty models show that nonemptiness is necessary only for refinement through the
entire joint-answer type: kernel identification itself remains true. -/
theorem nonempty_is_necessary_for_joint_refinement :
    let Q : (i : Empty) -> Empty -> Unit := fun i => i.elim
    let T : Empty -> Empty := fun m => m.elim
    IdentifiedBy Q T /\
      Not (Refines (canonicalTargetReadout T) (jointQuery Q)) := by
  dsimp
  constructor
  · intro m
    exact m.elim
  · rintro ⟨factor, _⟩
    exact (factor (fun i => i.elim)).1.elim

#print axioms nonempty_is_necessary_for_joint_refinement

/-- Two target readouts through the query quotient are equal because the quotient
projection is surjective. No identification hypothesis is needed once both factors exist. -/
theorem quotient_factorization_unique
    {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> M -> A i) (T : M -> Z)
    {first second : QueryQuotient Q -> Z}
    (firstFactors : T = first ∘ queryQuotientProjection Q)
    (secondFactors : T = second ∘ queryQuotientProjection Q) :
    first = second := by
  funext quotient
  obtain ⟨m, rfl⟩ := Quotient.mk_surjective quotient
  simpa [queryQuotientProjection] using
    (congrFun firstFactors m).symm.trans (congrFun secondFactors m)

#print axioms quotient_factorization_unique

/-- A target is identified by the family exactly when it factors uniquely through the
quotient by the simultaneous query kernel. -/
theorem identification_iff_unique_quotient_factorization
    {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> M -> A i) (T : M -> Z) :
    IdentifiedBy Q T <->
      ExistsUnique fun factor : QueryQuotient Q -> Z =>
        T = factor ∘ queryQuotientProjection Q := by
  constructor
  · intro identified
    have kernelInclusion := (identification_iff_kernel_inclusion Q T).1 identified
    let factor : QueryQuotient Q -> Z :=
      Quotient.lift T (fun m n sameQueries => kernelInclusion m n sameQueries)
    refine ⟨factor, ?_, ?_⟩
    · funext m
      rfl
    · intro candidate candidateFactors
      apply quotient_factorization_unique Q T candidateFactors
      funext m
      rfl
  · rintro ⟨factor, factors, _⟩
    apply (identification_iff_kernel_inclusion Q T).2
    intro m n sameQueries
    calc
      T m = factor (queryQuotientProjection Q m) := congrFun factors m
      _ = factor (queryQuotientProjection Q n) :=
        congrArg factor (Quotient.sound sameQueries)
      _ = T n := (congrFun factors n).symm

#print axioms identification_iff_unique_quotient_factorization

example {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> Empty -> A i) (T : Empty -> Z) : IdentifiedBy Q T := by
  intro m
  exact m.elim

example {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> Unit -> A i) (T : Unit -> Z) : IdentifiedBy Q T := by
  apply (identification_iff_kernel_inclusion Q T).2
  intro m n _
  cases m
  cases n
  rfl

example {M : Type u} {I : Type v} {A : I -> Type w} {Z : Type x}
    (Q : (i : I) -> M -> A i) (z : Z) : IdentifiedBy Q (fun _ => z) := by
  apply (identification_iff_kernel_inclusion Q (fun _ => z)).2
  intro _ _ _
  rfl

example {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) : IdentifiedBy Q (fun _ => (0 : Nat)) := by
  apply (identification_iff_kernel_inclusion Q (fun _ => (0 : Nat))).2
  intro _ _ _
  rfl

example {M : Type u} {I : Type v} {A : I -> Type w}
    (Q : (i : I) -> M -> A i) :
    IdentifiedBy Q id <-> forall m n, queryKernel Q m n -> m = n := by
  simpa using identification_iff_kernel_inclusion Q (id : M -> M)

example {M : Type u} {Z : Type x} (T : M -> Z) :
    IdentifiedBy (fun i : Fin 0 => (i.elim0 : M -> Unit)) T <->
      forall m n, T m = T n := by
  rw [identification_iff_kernel_inclusion]
  simp [queryKernel]

end D5.S3.ConceptDynamics.Sufficiency.QueryFamilyIdentification
