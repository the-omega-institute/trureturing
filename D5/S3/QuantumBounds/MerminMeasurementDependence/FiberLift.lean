/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/FiberLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform parity fibers lift class weights to local deterministic tables. -/
/-
Model definitions consumed by the odd-party and even-party faithful constructions.
Direct frozen dependencies:
  D5/S3/Divergence/ClassicalDPI.channelOutput; statement_id: sha256:bb11b45a5bb58d49bd779aa75b68940ca4390a1dc69947eb5336eed0279521e5
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import D5.S3.Divergence.ClassicalDPI

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section

abbrev AlphaFiber (n : ℕ) (P : ZMod 2) := {alpha : Fin n → ZMod 2 // ∑ i, alpha i = P}

def tableOfAlphaGamma {n : ℕ} (alpha gamma : Fin n → ZMod 2) : Strategy n :=
  fun i => (decide (alpha i = 1), decide (alpha i + gamma i = 1))

def fiberEquiv (d : ℕ) (P : ZMod 2) : AlphaFiber (d+1) P ≃ (Fin d → ZMod 2) where
  toFun alpha := fun i => alpha.1 i.castSucc
  invFun x := ⟨Fin.snoc x (P + ∑ i, x i),by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    calc
      (∑ i, x i) + (P + ∑ i, x i) = P + ((∑ i, x i) + (∑ i, x i)) := by abel
      _ = P := by rw [CharTwo.add_self_eq_zero,add_zero]⟩
  left_inv alpha := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      have hp := alpha.2
      rw [Fin.sum_univ_castSucc] at hp
      calc
        P + ∑ j : Fin d, alpha.1 j.castSucc =
                ((∑ j : Fin d, alpha.1 j.castSucc) + alpha.1 (Fin.last d)) +
              ∑ j : Fin d, alpha.1 j.castSucc := by rw [hp]
        _ = alpha.1 (Fin.last d) := by
          calc
            ((∑ j : Fin d, alpha.1 j.castSucc) + alpha.1 (Fin.last d)) +
              ∑ j : Fin d, alpha.1 j.castSucc =
              alpha.1 (Fin.last d) + ((∑ j : Fin d, alpha.1 j.castSucc) +
            ∑ j : Fin d, alpha.1 j.castSucc) := by abel
            _ = alpha.1 (Fin.last d) := by rw [CharTwo.add_self_eq_zero,add_zero]
    · simp
  right_inv x := by funext i;simp

def fiberMixture {d : ℕ} {C : Type*} [Fintype C]
    (P : C → ZMod 2) (p : C → ℝ) (z : (c : C) × AlphaFiber (d+1) (P c)) : ℝ :=
  p z.1 / (2 : ℝ)^d

def liftClassTable {d : ℕ} {C : Type*} (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2)
    (z : (c : C) × AlphaFiber (d+1) (P c)) : Strategy (d+1) :=
  tableOfAlphaGamma z.2.1 (gamma z.1)

def liftedDensity {d : ℕ} {C : Type*} [Fintype C]
    (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2) (p : C → ℝ) : Strategy (d+1) → ℝ :=
  (fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) (liftClassTable P gamma) (fiberMixture P p)

def classResponse {d : ℕ} {C : Type*}
    (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2)
    (x : Setting (d+1)) (c : C) : ℝ :=
  bitSign (P c) * bitSign (∑ i, gamma c i * (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i))


end
end D5.S3.QuantumBounds.MerminMeasurementDependence
