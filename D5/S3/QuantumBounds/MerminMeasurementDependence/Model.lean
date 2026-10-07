/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/Model
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/Model
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite GHZ--Mermin settings, deterministic tables, densities and faithfulness. -/
/-
Direct frozen dependencies: none.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section


def boolSign (b : Bool) : ℝ := if b then -1 else 1


abbrev Setting (n : ℕ) := {x : Fin n → Bool // (fun x => hammingDist x (fun _ => false)) x % 2 = 0}

abbrev Strategy (n : ℕ) := Fin n → Bool × Bool

def target {n : ℕ} (x : Setting n) : ℝ :=
  boolSign (decide (((fun x => hammingDist x (fun _ => false)) x.1 / 2) % 2 = 1))

def responseBit {n : ℕ} (lambda : Strategy n) (x : Setting n) (i : Fin n) : Bool :=
  if x.1 i then (lambda i).2 else (lambda i).1

def response {n : ℕ} (lambda : Strategy n) (x : Setting n) (I : Finset (Fin n)) : ℝ :=
  ∏ i ∈ I, boolSign (responseBit lambda x i)

def IsDensity {n : ℕ} (rho : Setting n → Strategy n → ℝ) : Prop :=
  (∀ x lambda, 0 ≤ rho x lambda) ∧ (∀ x, ∑ lambda, rho x lambda = 1)

def correlator {n : ℕ} (rho : Setting n → Strategy n → ℝ)
    (x : Setting n) (I : Finset (Fin n)) : ℝ :=
  ∑ lambda, rho x lambda * response lambda x I

def Faithful {n : ℕ} (rho : Setting n → Strategy n → ℝ) : Prop :=
  IsDensity rho ∧
  (∀ x, correlator rho x Finset.univ = target x) ∧
  (∀ x I, I.Nonempty → I ≠ Finset.univ → correlator rho x I = 0)

def M {n : ℕ} (rho : Setting n → Strategy n → ℝ) : ℝ :=
  sSup (Set.range fun xy : Setting n × Setting n =>
    ∑ lambda, |rho xy.1 lambda - rho xy.2 lambda|)

def F {n : ℕ} (rho : Setting n → Strategy n → ℝ) : ℝ := M rho / 2

def ratio (n : ℕ) : ℕ := 2 ^ ((n - 1) / 2)

def floorValue (n : ℕ) : ℝ := (ratio n : ℝ) / (2 * ((ratio n : ℝ) + 1))
end
end D5.S3.QuantumBounds.MerminMeasurementDependence
