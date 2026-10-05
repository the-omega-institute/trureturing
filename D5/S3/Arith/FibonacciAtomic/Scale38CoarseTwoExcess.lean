/- GID: D5/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual coarse nested-compensation scanning and exact two-excess bills. -/

import D5.S3.Arith.FibonacciAtomic.Scale38NestedCompensation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale38CoarseTwoExcess

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
open ActualCoarseReadoutHistory (kappa kappa_hist CoarseObservable)
open ActualCoarseReadoutCompletion (compileRaw encodeHistory cachedExecute completion_contract)
open ActualJointResponseCostCore (controllerPolicy)
open ActualImageSevenLeafSeparation (leafLabel leafAddresses seven_leaf_separation A C)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)
open Scale38NestedCompensation (family query stop route compatible)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
local notation "CH" => Hist (fun _ : Address => Option Bool)
local notation "RH" => Hist (fun _ : Address => Reply)

/-- Zero-based t: the secondary literal address g_(t+1)=p_(t+1)LLLR. -/
def discriminator (t : Nat) : Address :=
  false :: (List.replicate t true ++ [false,false,false,false,true])

/-- A finite coarse scan; an interior first none triggers exactly one secondary query. -/
def scan (k : Nat) : List Nat → PassiveProtocol Address (fun _ => Option Bool)
  | [] => .stop
  | t :: ts => .query (query t) (fun y =>
      if y = some true then scan k ts
      else if y = none ∧ 0 < t ∧ t < k then
        .query (discriminator t) (fun _ => .stop)
      else .stop)

/-- Decode the first merged exception, using its secondary report only at interior slots. -/
def decode (k : Nat) : List Nat → CH → Option (Index k)
  | [], _ => some (.inl ())
  | t :: ts, a :: h =>
      if a.2 = some true then decode k ts h
      else if a.2 = none then
        if ht : t < k then
          if t = 0 then some (.inr (.inl ⟨t,ht⟩))
          else match h with
            | b :: _ =>
                if b.2 = some true then some (.inr (.inl ⟨t,ht⟩))
                else if b.2 = none then some (.inr (.inr ⟨t-1,by omega⟩))
                else none
            | [] => none
        else if ht : t = k ∧ 0 < k then
          some (.inr (.inr ⟨k-1,by omega⟩))
        else none
      else none
  | _ :: _, [] => none

/-- Secondary queries appended to the existing actually reached primary prefix. -/
def secondary (k : Nat) : Index k → List Address
  | .inl _ => []
  | .inr (.inl j) => if 0 < j.val then [discriminator j.val] else []
  | .inr (.inr i) => if i.val + 1 < k then [discriminator (i.val+1)] else []

end D5.S3.Arith.FibonacciAtomic.Scale38CoarseTwoExcess
