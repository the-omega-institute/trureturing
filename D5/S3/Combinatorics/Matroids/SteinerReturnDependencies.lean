/- GID: D5/S3/Combinatorics/Matroids/SteinerReturnDependencies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerReturnDependencies
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Binary circuit relations characterize simultaneous Steiner returns. -/

import D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Recover a labelling from consistent binary relations among return rows. -/

namespace D5.S3.Combinatorics.Matroids.SteinerReturnDependencies

open LinearMap
open scoped BigOperators

private theorem factorsThrough {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] (incidence : V →ₗ[K] W) (request : V →ₗ[K] U) :
    (∃ label : W →ₗ[K] U, label.comp incidence = request) ↔
      ker incidence ≤ ker request := by
  constructor
  · rintro ⟨label, rfl⟩ y hy
    simp only [mem_ker, comp_apply, (mem_ker.mp hy), map_zero]
  · intro compatible
    let descended : range incidence →ₗ[K] U :=
      ((ker incidence).liftQ request compatible).comp incidence.quotKerEquivRange.symm.toLinearMap
    obtain ⟨label, extension⟩ := descended.exists_extend
    refine ⟨label, ?_⟩
    ext x
    have supported : incidence x ∈ range incidence := ⟨x, rfl⟩
    have atRow := LinearMap.congr_fun extension ⟨incidence x, supported⟩
    change label (incidence x) = descended ⟨incidence x, supported⟩ at atRow
    exact atRow.trans (by
      simp only [descended, comp_apply, LinearEquiv.coe_coe,
        quotKerEquivRange_symm_apply_image]
      rfl)

private theorem binaryRows {I J A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] (rows : I → (J →₀ ZMod 2)) (target : I → A) :
    (∃ label : J → A, ∀ i, Finsupp.linearCombination (ZMod 2) label (rows i) = target i) ↔
      ∀ c : I →₀ ZMod 2, Finsupp.linearCombination (ZMod 2) rows c = 0 →
        Finsupp.linearCombination (ZMod 2) target c = 0 := by
  classical
  let m : (I →₀ ZMod 2) →ₗ[ZMod 2] (J →₀ ZMod 2) :=
    Finsupp.linearCombination (ZMod 2) rows
  let b : (I →₀ ZMod 2) →ₗ[ZMod 2] A :=
    Finsupp.linearCombination (ZMod 2) target
  have hcomp : (∃ evaluation : (J →₀ ZMod 2) →ₗ[ZMod 2] A,
      evaluation.comp m = b) ↔ ker m ≤ ker b := factorsThrough (K := ZMod 2) m b
  change _ ↔ ∀ c, m c = 0 → b c = 0
  constructor
  · rintro ⟨label, hv⟩
    have hc : ker m ≤ ker b := hcomp.mp ⟨Finsupp.linearCombination (ZMod 2) label, by
      apply Finsupp.lhom_ext
      intro i c
      simp only [m, b, comp_apply, Finsupp.linearCombination_single, map_smul, hv]⟩
    intro c hz
    exact hc hz
  · intro consistent
    have hc : ker m ≤ ker b := fun c hz => consistent c hz
    obtain ⟨evaluation, he⟩ := hcomp.mpr hc
    let label : J → A := fun j => evaluation (Finsupp.single j 1)
    have table : Finsupp.linearCombination (ZMod 2) label = evaluation := by
      apply Finsupp.lhom_ext
      intro j c
      rw [Finsupp.linearCombination_single]
      have hs : Finsupp.single j c = c • Finsupp.single j (1 : ZMod 2) := by
        simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]
    refine ⟨label, fun i => ?_⟩
    rw [table]
    have h := LinearMap.congr_fun he (Finsupp.single i 1)
    simpa only [m, b, comp_apply, Finsupp.linearCombination_single, one_smul] using h

open Function Set
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
  (factor pairedLiftIterate pairedLift_eq_mul extensionMul
    extensionSteinerAndCentre returnAlongComponent)

/-- Triples along the alternating circuit contribute one in their coordinate over ZMod 2. -/
noncomputable def returnRow {L : Type*} [Mul L] (e p q x : L) :
    Set L →₀ ZMod 2 := by
  classical
  let step : L → L := fun y => p * (q * y)
  let basis : Set L → (Set L →₀ ZMod 2) := fun t => Finsupp.single t 1
  exact ∑ i ∈ Finset.range (minimalPeriod step x),
    (factor e basis q (step^[i] x) + factor e basis p (q * step^[i] x))

private theorem evaluateFactor {L A : Type*} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (labels : Set L → A) (p x : L) :
    Finsupp.linearCombination (ZMod 2) labels
      (factor e (fun t => Finsupp.single t (1 : ZMod 2)) p x) = factor e labels p x := by
  classical
  by_cases degenerate : p = e ∨ x = e ∨ p = x
  · simp only [factor, ite_eq_left degenerate, map_zero]
  · simp only [factor, ite_eq_right degenerate, Finsupp.linearCombination_single, one_smul]

private theorem firstReturn {L A : Type*} [Mul L] [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (labels : Set L → A) (p q x : L) (a : A) :
    letI := extensionMul e labels
    let step : L → L := fun y => p * (q * y)
    (fun y : L × A => (p, 0) * ((q, 0) * y))^[minimalPeriod step x] (x, a) =
      (x, a + Finsupp.linearCombination (ZMod 2) labels (returnRow e p q x)) := by
  classical
  dsimp only
  rw [← pairedLift_eq_mul e labels p q, pairedLiftIterate]
  apply Prod.ext
  · exact isPeriodicPt_minimalPeriod (fun y => p * (q * y)) x
  · simp only [returnRow, map_sum, map_add, evaluateFactor]

/-- A common labelling exists exactly when the required returns respect all binary relations. -/
theorem realizesExactlyCompatibleReturns {I L A : Type*} [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A]
    (e : L) (p q rep : I → L) (G : I → SimpleGraph L)
    (unit : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (edges : ∀ i u v, (G i).Adj u v ↔ p i * u = v ∨ q i * u = v)
    (target : I → A) :
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      (∀ x : L × A, (e, 0) * x = x) ∧
      (∀ x y : L × A, x * y = y * x) ∧
      (∀ x y : L × A, x * (x * y) = y) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      ∀ i x, (G i).Reachable (rep i) x → ∀ a : A,
        (fun y : L × A => (p i, 0) * ((q i, 0) * y))^[
          minimalPeriod (fun y => p i * (q i * y)) x] (x, a) = (x, a + target i)) ↔
      ∀ c : I →₀ ZMod 2,
        Finsupp.linearCombination (ZMod 2) (fun i => returnRow e (p i) (q i) (rep i)) c = 0 →
        Finsupp.linearCombination (ZMod 2) target c = 0 := by
  classical
  have compatible := binaryRows (fun i => returnRow e (p i) (q i) (rep i)) target
  constructor
  · rintro ⟨labels, _, _, _, _, returns⟩
    apply compatible.mp
    refine ⟨labels, fun i => ?_⟩
    have h := (firstReturn e labels (p i) (q i) (rep i) 0).symm.trans
      (returns i (rep i) SimpleGraph.Reachable.rfl 0)
    simpa only [zero_add] using congrArg Prod.snd h
  · intro consistent
    obtain ⟨labels, atRep⟩ := compatible.mpr consistent
    have twice (a : A) : a + a = 0 := by
      have two : (2 : ZMod 2) = 0 := by decide
      simpa only [two_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • a) two
    obtain ⟨idExt, commExt, involExt, centreExt⟩ :=
      extensionSteinerAndCentre e labels unit comm invol twice centreless
    refine ⟨labels, idExt, commExt, involExt, centreExt, fun i x reachable => ?_⟩
    apply returnAlongComponent (G i) e (p i) (q i) labels invol twice
      (edges i) involExt reachable (target i)
    intro a
    simpa only [atRep i] using firstReturn e labels (p i) (q i) (rep i) a

end D5.S3.Combinatorics.Matroids.SteinerReturnDependencies
