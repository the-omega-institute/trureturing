/- GID: D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The four-exit right-comb family and its raw endpoint menu interface. -/

import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

open GenealogicalFiberTransport (Source substitution)
open scoped BigOperators
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore

abbrev Row := Fin 4
abbrev Index (k : Nat) := Unit ⊕ (Fin k × Row)

open ActualImageSevenLeafSeparation (thirdImage)

def b : Source := .mul (.of false) (.of true)
def t : Source := .mul (.of true) (.of false)
def w : Source := .mul b (.of false)
def h : Source := .mul t (.of true)
def y : Source := .mul w (.of true)
def z : Source := .mul (.of false) b
def r₀ : Source := .mul t b
def rₐ : Source := .mul t z

def E : Source := .mul (.of false) (.of true)
def A : Source := thirdImage (.of true)
def C : Source := thirdImage (.of false)
def B : Source := thirdImage b
def T : Source := thirdImage t
def W₁ : Source := thirdImage w
def H : Source := thirdImage h
def Y : Source := thirdImage y
def Z : Source := thirdImage z
def R₀ : Source := thirdImage r₀
def Rₐ : Source := thirdImage rₐ

def comb : (n : Nat) → (Fin n → Source) → Source → Source
  | 0, _, q => q
  | n + 1, f, q => .mul (f 0)
      (comb n (fun i => f i.succ) q)

def preActive (_k : Nat) (_j : Fin _k) (r : Row) : Source :=
  match r.1 with
  | 0 => .of true
  | 1 => y
  | 2 => h
  | _ => z

def preComp (r : Row) : Source :=
  match r.1 with
  | 0 => rₐ
  | 1 => b
  | 2 => z
  | _ => h

def active (r : Row) : Source :=
  match r.1 with
  | 0 => A
  | 1 => Y
  | 2 => H
  | _ => Z

def comp (r : Row) : Source :=
  match r.1 with
  | 0 => Rₐ
  | 1 => B
  | 2 => Z
  | _ => H

def baselinePre (k : Nat) : Source := comb k (fun _ => b) r₀

def preFamily (k : Nat) : Index k → Source
  | Sum.inl _ => baselinePre k
  | Sum.inr ⟨j, r⟩ => comb k (fun i => if i = j then preActive k j r else b) (preComp r)

def family (k : Nat) : Index k → Source
  | Sum.inl _ => comb k (fun _ => B) R₀
  | Sum.inr ⟨j, r⟩ => comb k (fun i => if i = j then active r else B) (comp r)

def endpoint (k : Nat) (i : Index k) : Index k → Nat := fun j =>
  if j = i then 0 else 1

def endpointWith (k : Nat) (j : Fin k) (b : Row) : Index k → Nat := fun i =>
  if i = Sum.inr ⟨j, 0⟩ then 0
  else if i = Sum.inr ⟨j, b⟩ then 2
  else 1

def menu (k : Nat) : Set (Index k → Nat) :=
  Set.range (fun u : Unit => endpoint k (Sum.inl u)) ∪
    Set.range (fun p : Fin k × Fin 3 => endpoint k (Sum.inr ⟨p.1, Fin.succ p.2⟩)) ∪
    Set.range (fun p : Fin k × Fin 3 => endpointWith k p.1 (Fin.succ p.2))


end D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
