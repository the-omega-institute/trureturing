/- GID: D5/S3/Resource/PriceFace
   generality: G
   mirror-B: D5/B/S3/Resource/PriceFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The price of an equality is the minimal face of its valid-witness tax receipts. -/

import Mathlib.Order.Minimal
import Mathlib.Order.Filter.AtTopBot.Defs

namespace D5.S3.Resource.PriceFace

/-- A scale-dependent cost, compared below by eventual domination. -/
structure CostProfile (Cost : Type*) where
  atScale : Nat -> Cost

instance {Cost : Type*} : CoeFun (CostProfile Cost) (fun _ => Nat -> Cost) where
  coe profile := profile.atScale

/-- Cost profiles are ordered by domination at all sufficiently large input scales. -/
instance {Cost : Type*} [LE Cost] : LE (CostProfile Cost) where
  le left right := Filter.EventuallyLE Filter.atTop left right

/-- The time and space costs of both directions of a witness. -/
structure PhysicalCosts (Cost : Type*) where
  forwardTime : CostProfile Cost
  forwardSpace : CostProfile Cost
  reverseTime : CostProfile Cost
  reverseSpace : CostProfile Cost

/-- Physical costs use the componentwise order, with each function field compared eventually. -/
instance {Cost : Type*} [LE Cost] : LE (PhysicalCosts Cost) where
  le left right :=
    left.forwardTime <= right.forwardTime ∧
      left.forwardSpace <= right.forwardSpace ∧
      left.reverseTime <= right.reverseTime ∧
      left.reverseSpace <= right.reverseSpace

/-- The receipt attached to a witness pair. The rate field may use an option type when it is
derived only for a restricted class of witnesses. -/
structure TaxReceipt
    (AlgorithmCost RateCost PhysicalCost HeatCost : Type*) where
  forwardAlgorithm : AlgorithmCost
  reverseAlgorithm : AlgorithmCost
  rate : RateCost
  physical : PhysicalCosts PhysicalCost
  heat : HeatCost

/-- Tax receipts are ordered componentwise. -/
instance
    {AlgorithmCost RateCost PhysicalCost HeatCost : Type*}
    [LE AlgorithmCost] [LE RateCost] [LE PhysicalCost] [LE HeatCost] :
    LE (TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost) where
  le left right :=
    left.forwardAlgorithm <= right.forwardAlgorithm ∧
      left.reverseAlgorithm <= right.reverseAlgorithm ∧
      left.rate <= right.rate ∧
      left.physical <= right.physical ∧
      left.heat <= right.heat

/-- The price face of an equality is the set of minimal receipts produced by its valid
witnesses. This definition does not assert that the face has more than one independent cost
direction. -/
def priceFace
    {Object Witness AlgorithmCost RateCost PhysicalCost HeatCost : Type*}
    [LE AlgorithmCost] [LE RateCost] [LE PhysicalCost] [LE HeatCost]
    (validWitness : Witness -> Object -> Object -> Prop)
    (receipt : Witness -> TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost)
    (left right : Object) :
    Set (TaxReceipt AlgorithmCost RateCost PhysicalCost HeatCost) :=
  { candidate |
    Minimal
      (fun proposed =>
        exists witness, validWitness witness left right ∧ receipt witness = proposed)
      candidate }

#print axioms priceFace

end D5.S3.Resource.PriceFace
