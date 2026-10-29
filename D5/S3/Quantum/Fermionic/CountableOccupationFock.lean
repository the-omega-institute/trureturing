/- GID: D5/S3/Quantum/Fermionic/CountableOccupationFock
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/CountableOccupationFock
   mirror-E: none(waiver:algebraic-countable-fock)
   anchors: []
   utility: none
   digest: Signed finite occupations intertwine the finite Jordan-Wigner action. -/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
import Mathlib.LinearAlgebra.Finsupp.LSum

open scoped BigOperators Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
open PredictiveThermodynamic.Physical (Assignment)

noncomputable section
namespace D5.S3.Quantum.Fermionic.CountableOccupationFock

abbrev Fock := (Finset ℕ) →₀ ℂ

def ket (S : Finset ℕ) : Fock := Finsupp.single S 1

def vacuum : Fock := ket ∅

def prefix (j : ℕ) (S : Finset ℕ) : ℕ := (S.filter (· < j)).card

def phase (j : ℕ) (S : Finset ℕ) : ℂ := (-1 : ℂ) ^ prefix j S

def annihilate (j : ℕ) : Module.End ℂ Fock :=
  Finsupp.lift Fock ℂ (Finset ℕ) fun S =>
    if j ∈ S then phase j S • ket (S.erase j) else 0

def create (j : ℕ) : Module.End ℂ Fock :=
  Finsupp.lift Fock ℂ (Finset ℕ) fun S =>
    if j ∈ S then 0 else phase j S • ket (insert j S)

def parity : Module.End ℂ Fock :=
  Finsupp.lift Fock ℂ (Finset ℕ) fun S => (-1 : ℂ) ^ S.card • ket S

def prefixEmbed (N : ℕ) : (Assignment N → ℂ) →ₗ[ℂ] Fock :=
  ∑ t : Assignment N, (LinearMap.proj t).smulRight (ket (occupationSet t))

end D5.S3.Quantum.Fermionic.CountableOccupationFock
