/- GID: D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal Scale36 family and actual conditional routing addresses. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
import D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutCompletion
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition
open ActualImageSevenLeafSeparation (thirdImage leafAddresses leafLabel Nonconflict)
open FourExitRawEndpointSpectrum (comb comb_slot_readout comb_tail_readout)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
  (PassiveProtocol runPassiveProtocol)

local notation "Index" => fun k : Nat => Unit ⊕ (Fin k × Fin 2)
local notation "E" => ActualImageSevenLeafSeparation.E
local notation "A" => ActualImageSevenLeafSeparation.A
local notation "C" => ActualImageSevenLeafSeparation.C
local notation "B" => FourExitRawEndpointSpectrum.B
local notation "Kₜ" => FourExitRawEndpointSpectrum.H
local notation "T" => thirdImage FourExitRawEndpointSpectrum.t
local notation "W₁" => Source.mul B C

/-- Original activity blocks, ordered U then V. -/
def active (r : Fin 2) : Source := if r.val = 0 then T else W₁

/-- The coupled compensation blocks, ordered B then A. -/
def compensation (r : Fin 2) : Source := if r.val = 0 then B else A

/-- Complete original Scale36 prototypes. The left summand is P0. -/
def family (k : Nat) : Index k → Source
  | .inl _ => comb k (fun _ => C) Kₜ
  | .inr (j,r) => comb k (fun i => if i = j then active r else C) (compensation r)

/-- Bracket-preserving original preimages of the prototypes. -/
def preFamily (k : Nat) : Index k → Source
  | .inl _ => comb k (fun _ => .of false) FourExitRawEndpointSpectrum.h
  | .inr (j,r) => comb k (fun i => if i = j then
      (if r.val = 0 then FourExitRawEndpointSpectrum.t else .mul E (.of false))
      else .of false) (if r.val = 0 then E else .of true)

/-- Literal a, b, q, r addresses in an activity slot. -/
def addresses (k : Nat) (j : Fin k) (s : Fin 4) : Address :=
  List.replicate j.val true ++ false ::
    (match s.val with
      | 0 => [false,false,true]
      | 1 => [true,true]
      | 2 => [true,false,false,true]
      | _ => [false,false,false,false,true])

/-- The one additional paid address prescribed by each target/input pair. -/
def extra (k : Nat) (target row : Index k) : Option Address :=
  if target = row then none else
    match row with
    | .inl _ => match target with
      | .inl _ => none
      | .inr (j,_) => some (addresses k j 2)
    | .inr (j,r) =>
      if r.val = 1 then some (addresses k j 0) else
        match target with
        | .inl _ => some (addresses k j 1)
        | .inr (l,s) =>
          if l = j ∧ s.val = 1 then some (addresses k j 3)
          else some (addresses k j 1)

end D5.S3.Arith.FibonacciAtomic.Scale36ActualEndpointAcquisition
