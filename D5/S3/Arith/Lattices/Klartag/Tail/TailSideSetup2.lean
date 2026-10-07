/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup
import D5.S3.Arith.Lattices.Klartag.Walk.WalkMeasurable

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

noncomputable section

section ActiveVec

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
variable {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`ChainWiring.measurable_of_active`, vector-valued.**  A statistic of the active set alone is
measurable; the proof is the same finite partition over `W.powerset`. -/
theorem measurable_of_active_vec (hξ : ∀ k, Measurable (ξ k)) (k : ℕ)
    (f : Finset ι → EuclideanSpace ℝ (UT n)) :
    Measurable fun ω => f (Chain.chain q W A₀ ξ k ω).2 := by
  classical
  have hrep : (fun ω => f (Chain.chain q W A₀ ξ k ω).2)
      = fun ω => ∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then f c else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2 (fun c => f c),
      if_pos (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
  rw [hrep]
  exact Finset.measurable_sum _ fun c _ =>
    Measurable.ite (ChainWiring.measurableSet_active_eq hξ k c) measurable_const measurable_const

end ActiveVec

section Direction

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- A truncated past, read back as a full path at scale `c`. -/
def extendc (c : ℝ) {i : ℕ} (z : Fin i → EuclideanSpace ℝ (UT n)) :
    ℕ → EuclideanSpace ℝ (UT n) := fun j => if h : j < i then c • z ⟨j, h⟩ else 0

theorem measurable_extendc (c : ℝ) {i : ℕ} (j : ℕ) :
    Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) => extendc c z j := by
  by_cases h : j < i
  · show Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) =>
      if h' : j < i then c • z ⟨j, h'⟩ else 0
    simp only [dif_pos h]
    exact (measurable_pi_apply _).const_smul c
  · show Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) =>
      if h' : j < i then c • z ⟨j, h'⟩ else 0
    simp only [dif_neg h]
    exact measurable_const

theorem extendc_restr {c : ℝ} {i : ℕ} {j : ℕ} (hj : j < i)
    (ω : ℕ → EuclideanSpace ℝ (UT n)) :
    extendc c (restr i ω) j = step c j ω := by
  show (if h : j < i then c • (restr i ω) ⟨j, h⟩ else 0) = c • coord j ω
  rw [dif_pos hj]; rfl

/-- **The chain's projected direction at `q y`, normalised.** -/
def dirOf (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (c : ℝ) (y : ι) (i : ℕ) (z : Fin i → EuclideanSpace ℝ (UT n)) :
    EuclideanSpace ℝ (UT n) :=
  ‖q y‖⁻¹ • (Chain.freeSub q (Chain.chain q W A₀
    (fun j (z' : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z' j) i z).2).starProjection (q y)

theorem measurable_dirOf (c : ℝ) (y : ι) (i : ℕ) : Measurable (dirOf q W A₀ c y i) :=
  measurable_of_active_vec (ξ := fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j)
    (fun j => measurable_extendc c j) i
    (fun a => ‖q y‖⁻¹ • (Chain.freeSub q a).starProjection (q y))

theorem norm_dirOf_le {y : ι} (hqy : q y ≠ 0) (c : ℝ) (i : ℕ)
    (z : Fin i → EuclideanSpace ℝ (UT n)) : ‖dirOf q W A₀ c y i z‖ ≤ 1 := by
  have hqn : (0 : ℝ) < ‖q y‖ := norm_pos_iff.2 hqy
  have hproj := Submodule.norm_starProjection_apply_le
    (Chain.freeSub q (Chain.chain q W A₀
      (fun j (z' : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z' j) i z).2) (q y)
  rw [dirOf, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖q y‖⁻¹),
    inv_mul_le_iff₀ hqn, mul_one]
  exact hproj

theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Submodule ℝ E} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K = L) (x : E) : K.starProjection x = L.starProjection x := by subst hKL; rfl

theorem dirOf_restr (c : ℝ) (y : ι) (i : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT n)) :
    dirOf q W A₀ c y i (restr i ω)
      = ‖q y‖⁻¹ • (Chain.freeSub q
          (Chain.chain q W A₀ (step c) i ω).2).starProjection (q y) := by
  have hchain : Chain.chain q W A₀
      (fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) i (restr i ω)
      = Chain.chain q W A₀ (step c) i ω :=
    chain_eq_of_eq (q := q) (W := W) (A₀ := A₀)
      (ξ := fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) (step c)
      (restr i ω) ω i (fun j hj => extendc_restr hj ω)
  show ‖q y‖⁻¹ • (Chain.freeSub q (Chain.chain q W A₀
      (fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) i (restr i ω)).2
      ).starProjection (q y) = _
  exact congrArg (fun v => ‖q y‖⁻¹ • v) (starProjection_congr (by rw [hchain]) (q y))

end Direction

section Instantiate

/-- The two identities `RawData` does not carry: Klartag's eq. (61) at time zero.  Both are
immediate for the chain's own `q y = ChainWiring.qUT (α • toE n y)` and `A₀ = a0C n • Id`. -/
structure NormData (n : ℕ) (α : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop where
  hnorm : ∀ y ∈ W, ‖q y‖ = (α * ‖toE n y‖) ^ 2
  hinner : ∀ y ∈ W, ⟪A₀, q y⟫ = a0C n * (α * ‖toE n y‖) ^ 2

theorem stepSizeAdopted2_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ParamsAdopted2.stepSizeAdopted2 n := by
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [ParamsAdopted2.stepSizeAdopted2, ChainDrift.stepSize, ChainDrift.horizon]
  exact div_pos (by positivity) (ChainDrift.numSteps_pos hn)

end Instantiate

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
