/- GID: D5/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/QuotientCutNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every decidable primitive kernel is recovered by its canonical quotient CUT. -/

import D5.S3.ConceptDynamics.CIRPT.PrimitiveKernel
import Mathlib.Data.Quot

/- Library-search audit trail (2026-09-04):
   * Repository searches for quotient CUT normal forms found quotient maps for
     task identities and sufficient statistics, but no declaration over the
     new `DecidableKernel` carrier.
   * Pinned Mathlib exact hits `Quotient.eq` and `Quotient.eq_iff_equiv` state
     equality of quotient constructors iff the underlying setoid relation;
     `Quotient.eq` is applied directly below rather than reproved.
   * Pinned Mathlib's `Multiset.decidableEq` supplies the reusable
     `Quotient.recOnSubsingleton₂` plus `decidable_of_iff'` construction pattern.
     No generic quotient `DecidableEq` instance was found because decidability
     belongs to the particular underlying setoid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT

universe u

namespace DecidableKernel

/-- The setoid carried by a decidable kernel. -/
def toSetoid {X : Type u} (K : DecidableKernel X) : Setoid X where
  r := K.relation
  iseqv := K.equivalence

/-- The canonical CUT from a state space to the quotient by a kernel. -/
def quotientCut {X : Type u} (K : DecidableKernel X) : X -> Quotient K.toSetoid :=
  Quotient.mk K.toSetoid

/-- A decidable kernel induces decidable equality on its canonical quotient. -/
instance instDecidableEqQuotient {X : Type u} (K : DecidableKernel X) :
    DecidableEq (Quotient K.toSetoid) :=
  fun left right =>
    Quotient.recOnSubsingleton₂ left right fun x y =>
      decidable_of_iff' (K.relation x y) Quotient.eq

end DecidableKernel

/-- CIRPT-IE-002: quotient projection equality is exactly the original kernel. -/
theorem quotient_cut_kernel_normal_form {X : Type u} (K : DecidableKernel X)
    (x y : X) :
    K.relation x y <-> K.quotientCut x = K.quotientCut y :=
  by
    exact
      (show K.relation x y <-> K.toSetoid x y from Iff.rfl).trans
        (@Quotient.eq X K.toSetoid x y).symm

/-- The CUT built from the quotient projection recovers the original relation. -/
theorem cutKernel_quotientCut_relation_iff {X : Type u} (K : DecidableKernel X)
    (x y : X) :
    (cutKernel K.quotientCut).relation x y <-> K.relation x y :=
  (quotient_cut_kernel_normal_form K x y).symm

end D5.S3.ConceptDynamics.CIRPT
