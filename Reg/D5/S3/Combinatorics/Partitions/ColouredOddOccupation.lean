import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.ColouredOddOccupation
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Partitions.ColouredOddOccupation
open LeanInformationAudit
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section
universe u v
namespace Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation
abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def natActual : Realization natSignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
theorem natDependence : ObservationalDependence natSignature natActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h
abbrev seriesSignature : Signature where
  Params := Type u
  State R := PowerSeries R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := PowerSeries R → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def seriesActual : Realization seriesSignature.{u} :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def seriesRejected : Realization seriesSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
theorem seriesDependence : ObservationalDependence seriesSignature.{u} seriesActual := by
  intro i
  refine ⟨ULift.{u} ℕ, 0, 1, ?_⟩
  intro he
  have h : (1 : PowerSeries (ULift.{u} ℕ)) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h
structure ProductParams where
  K : Type u
  field : Field K
  topology : TopologicalSpace K
  t2 : @T2Space K topology
  topRing : letI : Field K := field; letI : TopologicalSpace K := topology; IsTopologicalRing K
abbrev productSignature : Signature where
  Params := ProductParams.{u}
  State p := ℕ → PowerSeries p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PowerSeries p.K → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def productActual : Realization productSignature.{u} :=
  realize _ (fun _ p f => by
    letI := p.field
    letI := p.topology
    letI := p.t2
    letI := p.topRing
    exact fun s => HasProd f s) (fun e => nomatch e)
def productRejected : Realization productSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
theorem productDependence : ObservationalDependence productSignature.{u} productActual := by
  intro i
  let K := ULift.{u} ℂ
  let p : ProductParams.{u} := ⟨K, inferInstance, inferInstance, inferInstance, inferInstance⟩
  let f : ℕ → PowerSeries K := fun n => if n = 0 then 0 else 1
  refine ⟨p, (fun _ => 1), f, ?_⟩
  intro he
  have hp : HasProd (fun _ : ℕ => (1 : PowerSeries K)) 1 := hasProd_one
  have hq : HasProd f 1 := Eq.mp (congrFun he 1) hp
  have hz : HasProd f 0 := hasProd_ite_eq (0 : ℕ) (0 : PowerSeries K)
  exact zero_ne_one (hz.unique hq)


namespace Energy
abbrev signature := natSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (ι : Type u) [Fintype ι] (d : (ι × ℕ) →₀ ℕ),
    r.readout () () (colouredEnergy ι d) (∑ i, singleEnergy (colourEquiv ι d i))
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredEnergy_eq_sum.{u})) ↔ arena.{u}.Law natActual := Iff.rfl
private theorem actualLaw : arena.{u}.Law natActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredEnergy_eq_sum.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law natRejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance 0
def family : Registration arena.{u} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredEnergy_eq_sum.{u})) where
  actual := natActual
  bridge := sourceBridge
  variation := ⟨actualLaw, natRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredEnergy_eq_sum.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Energy.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Energy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Energy

namespace Cardinality
abbrev signature := natSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (N : ℕ),
    r.readout () () (Nat.card (ColouredOddFiber ι N))
      (∑ e ∈ (Finset.univ : Finset ι).finsuppAntidiag N,
        ∏ i : ι, (Nat.Partition.odds (e i)).card)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.card_colouredOddFiber.{u})) ↔ arena.{u}.Law natActual := Iff.rfl
private theorem actualLaw : arena.{u}.Law natActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.card_colouredOddFiber.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law natRejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance 0
def family : Registration arena.{u} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.card_colouredOddFiber.{u})) where
  actual := natActual
  bridge := sourceBridge
  variation := ⟨actualLaw, natRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.card_colouredOddFiber.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Cardinality.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cardinality

namespace Convolution
abbrev signature := seriesSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : Type u) [CommSemiring R] (ι : Type v) [Fintype ι],
    r.readout () R (colouredFiberSeries R ι) (∏ _ : ι, oddPartitionSeries R)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_prod.{u,v})) ↔ arena.{u,v}.Law seriesActual := Iff.rfl
private theorem actualLaw : arena.{u,v}.Law seriesActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_prod.{u,v})
private theorem rejectedLaw : ¬ arena.{u,v}.Law seriesRejected := by
  intro h
  exact @h (ULift.{u} ℕ) inferInstance PUnit.{v+1} inferInstance
def family : Registration arena.{u,v} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_prod.{u,v})) where
  actual := seriesActual
  bridge := sourceBridge
  variation := ⟨actualLaw, seriesRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_prod.{u,v}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Convolution.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.Convolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Convolution

namespace FinitePower
abbrev signature := seriesSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (R : Type u) [CommSemiring R] (ι : Type v) [Fintype ι],
    r.readout () R (colouredFiberSeries R ι) (oddPartitionSeries R ^ Fintype.card ι)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_pow.{u,v})) ↔ arena.{u,v}.Law seriesActual := Iff.rfl
private theorem actualLaw : arena.{u,v}.Law seriesActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_pow.{u,v})
private theorem rejectedLaw : ¬ arena.{u,v}.Law seriesRejected := by
  intro h
  exact @h (ULift.{u} ℕ) inferInstance PUnit.{v+1} inferInstance
def family : Registration arena.{u,v} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_pow.{u,v})) where
  actual := seriesActual
  bridge := sourceBridge
  variation := ⟨actualLaw, seriesRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.colouredFiberSeries_eq_pow.{u,v}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.FinitePower.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.FinitePower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FinitePower

namespace GeometricInverse
abbrev signature := seriesSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (K : Type u) [Field K] [TopologicalSpace K] [T2Space K] [IsTopologicalRing K] (n : ℕ),
    r.readout () K (∑' j : ℕ, (PowerSeries.X : PowerSeries K) ^ (oddWeight n * j))
      (((1 : PowerSeries K) - PowerSeries.X ^ oddWeight n)⁻¹)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.odd_geometric_eq_inverse.{u})) ↔ arena.{u}.Law seriesActual := Iff.rfl
private theorem actualLaw : arena.{u}.Law seriesActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.odd_geometric_eq_inverse.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law seriesRejected := by
  intro h
  exact @h (ULift.{u} ℂ) inferInstance inferInstance inferInstance inferInstance 0
def family : Registration arena.{u} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.odd_geometric_eq_inverse.{u})) where
  actual := seriesActual
  bridge := sourceBridge
  variation := ⟨actualLaw, seriesRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.odd_geometric_eq_inverse.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.GeometricInverse.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.GeometricInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GeometricInverse

namespace OddProduct
abbrev signature := productSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (K : Type u) [iF : Field K] [iT : TopologicalSpace K] [iS : T2Space K] [iR : IsTopologicalRing K],
    r.readout () ⟨K, iF, iT, iS, iR⟩
      (fun n : ℕ => ((1 : PowerSeries K) - PowerSeries.X ^ oddWeight n)⁻¹)
      (oddPartitionSeries K)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_oddPartitionSeries.{u})) ↔ arena.{u}.Law productActual := Iff.rfl
private theorem actualLaw : arena.{u}.Law productActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_oddPartitionSeries.{u})
private theorem rejectedLaw : ¬ arena.{u}.Law productRejected := by
  intro h
  exact @h (ULift.{u} ℂ) inferInstance inferInstance inferInstance inferInstance
def family : Registration arena.{u} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_oddPartitionSeries.{u})) where
  actual := productActual
  bridge := sourceBridge
  variation := ⟨actualLaw, productRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨productRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := productDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_oddPartitionSeries.{u}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.OddProduct.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.OddProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} productActual.readout productActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end OddProduct

namespace ColouredProduct
abbrev signature := productSignature.{u}
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (K : Type u) [iF : Field K] [iT : TopologicalSpace K] [iS : T2Space K] [iR : IsTopologicalRing K]
    (ι : Type v) [Fintype ι],
    r.readout () ⟨K, iF, iT, iS, iR⟩
      (fun n : ℕ => (((1 : PowerSeries K) - PowerSeries.X ^ (2*n+1))⁻¹) ^ Fintype.card ι)
      (colouredFiberSeries K ι)
theorem sourceBridge : (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_colouredFiberSeries.{u,v})) ↔ arena.{u,v}.Law productActual := Iff.rfl
private theorem actualLaw : arena.{u,v}.Law productActual := (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_colouredFiberSeries.{u,v})
private theorem rejectedLaw : ¬ arena.{u,v}.Law productRejected := by
  intro h
  exact @h (ULift.{u} ℂ) inferInstance inferInstance inferInstance inferInstance PUnit.{v+1} inferInstance
def family : Registration arena.{u,v} (type_of% (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_colouredFiberSeries.{u,v})) where
  actual := productActual
  bridge := sourceBridge
  variation := ⟨actualLaw, productRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨productRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := productDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Combinatorics.Partitions.ColouredOddOccupation.hasProd_colouredFiberSeries.{u,v}) (Realization signature.{u}) (Type u → Type u) Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.ColouredProduct.unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation.ColouredProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} productActual.readout productActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.ColouredOddOccupation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ColouredProduct

end Reg.D5.S3.Combinatorics.Partitions.ColouredOddOccupation
