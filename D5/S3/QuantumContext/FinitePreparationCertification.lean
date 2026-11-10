/- GID: D5/S3/QuantumContext/FinitePreparationCertification
   generality: I
   mirror-B: D5/B/S3/QuantumContext/FinitePreparationCertification
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite preparations strictly separate every nonclassical finite-outcome measurement. -/

/-
proof_shape: result: bind-only; escape_witness: none
admission_basis: open-problem-resolution (#23171; Proved)
Direct frozen dependencies: the following rows expand all same-module helpers.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25274.
The public predicates and claim retain the source's full preparation and effect identities.
The auxiliary response subspace is an intersection of linear-map kernels; the table map uses
mulRightLinearMap. Density inhabitance uses CartesianVariance.density_nonempty.
The response-identity and table-map expressions are used without duplicate definitions.
Every helper is bind-only and has a consumer. Declaration identities follow statement-v1.
responsePolytope | proof_shape: bind-only | escape_witness: none
  consumers: NoncontextualTable, compress_table, finite_obstruction, fixed_table_model, response_finite_hull, separate_finite_table, vertex_coordinates
  Direct frozen dependencies: none
NoncontextualTable | proof_shape: bind-only | escape_witness: none
  consumers: Classical, claim, compress_table, finite_obstruction, fixed_table_model, result, separate_finite_table
  Direct frozen dependencies: none
Classical | proof_shape: bind-only | escape_witness: none
  consumers: claim, finite_obstruction, result
  Direct frozen dependencies:
    D5/S3/Quantum/FiniteDimensional.bornProbability sha256:70d0693159ac58607261fa66304a04ba6078de3492431f14485817d5497d9d6d
    D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
claim | proof_shape: bind-only | escape_witness: none
  consumers: result
  Direct frozen dependencies:
    D5/S3/Quantum/FiniteDimensional.bornProbability sha256:70d0693159ac58607261fa66304a04ba6078de3492431f14485817d5497d9d6d
    D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
    D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
response_finite_hull | proof_shape: bind-only | escape_witness: none
  consumers: finite_obstruction, separate_finite_table
  Direct frozen dependencies:
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.IsPolytope sha256:1cec797eb5470787778683b0fde74dec9bf09711656592a7bbd6ee171bc1fda6
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber sha256:4440d0ec64b1b5409dc44779ae9ba3612cc520abd549812d351ec595b6ae6ff9
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber_isPolytope sha256:b0cbf76e0c6bd5443e395dee4ebfaf77a356b7d427c2884ad2bb9541354289c0
vertex_coordinates | proof_shape: bind-only | escape_witness: none
  consumers: compress_table
  Direct frozen dependencies: none
FixedTable | proof_shape: bind-only | escape_witness: none
  consumers: compress_table, finite_obstruction, fixed_global_of_finite, fixed_table_iff_image, fixed_table_model, fixed_table_reindex, separate_finite_table
  Direct frozen dependencies: none
compress_table | proof_shape: bind-only | escape_witness: none
  consumers: finite_obstruction, separate_finite_table
  Direct frozen dependencies: none
fixed_table_model | proof_shape: bind-only | escape_witness: none
  consumers: finite_obstruction, separate_finite_table
  Direct frozen dependencies: none
localConstraints | proof_shape: bind-only | escape_witness: none
  consumers: fixed_global_of_finite, localConstraints_closed, preparationWeights_compact
  Direct frozen dependencies: none
localConstraints_closed | proof_shape: bind-only | escape_witness: none
  consumers: fixed_global_of_finite, preparationWeights_compact
  Direct frozen dependencies: none
fixed_global_of_finite | proof_shape: bind-only | escape_witness: none
  consumers: finite_obstruction
  Direct frozen dependencies: none
preparationWeights | proof_shape: bind-only | escape_witness: none
  consumers: fixed_table_iff_image, preparationWeights_compact, preparationWeights_convex, separate_finite_table
  Direct frozen dependencies: none
preparationWeights_compact | proof_shape: bind-only | escape_witness: none
  consumers: separate_finite_table
  Direct frozen dependencies: none
preparationWeights_convex | proof_shape: bind-only | escape_witness: none
  consumers: separate_finite_table
  Direct frozen dependencies: none
fixed_table_iff_image | proof_shape: bind-only | escape_witness: none
  consumers: separate_finite_table
  Direct frozen dependencies: none
dual_table_coordinates | proof_shape: bind-only | escape_witness: none
  consumers: separate_finite_table
  Direct frozen dependencies:
    D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.continuous_linear_expansion sha256:1fa41d9614547f8ad7cc9f56010786362e0c5dd2fa04a8c473f9e75d92106007
separate_finite_table | proof_shape: bind-only | escape_witness: none
  consumers: result
  Direct frozen dependencies:
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.IsPolytope sha256:1cec797eb5470787778683b0fde74dec9bf09711656592a7bbd6ee171bc1fda6
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber sha256:4440d0ec64b1b5409dc44779ae9ba3612cc520abd549812d351ec595b6ae6ff9
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber_isPolytope sha256:b0cbf76e0c6bd5443e395dee4ebfaf77a356b7d427c2884ad2bb9541354289c0
    D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.continuous_linear_expansion sha256:1fa41d9614547f8ad7cc9f56010786362e0c5dd2fa04a8c473f9e75d92106007
fixed_table_reindex | proof_shape: bind-only | escape_witness: none
  consumers: finite_obstruction
  Direct frozen dependencies: none
finite_obstruction | proof_shape: bind-only | escape_witness: none
  consumers: result
  Direct frozen dependencies:
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.IsPolytope sha256:1cec797eb5470787778683b0fde74dec9bf09711656592a7bbd6ee171bc1fda6
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber sha256:4440d0ec64b1b5409dc44779ae9ba3612cc520abd549812d351ec595b6ae6ff9
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber_isPolytope sha256:b0cbf76e0c6bd5443e395dee4ebfaf77a356b7d427c2884ad2bb9541354289c0
    D5/S3/Quantum/FiniteDimensional.bornProbability sha256:70d0693159ac58607261fa66304a04ba6078de3492431f14485817d5497d9d6d
    D5/S3/Quantum/Matrix/CartesianVariance.density_nonempty sha256:18b5b208f62ae872abfb0b7d5989bb6985e01575eb116c91f9cb1104621a29af
    D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
result | proof_shape: bind-only | escape_witness: none
  consumers: external problem settlement
  Direct frozen dependencies:
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.IsPolytope sha256:1cec797eb5470787778683b0fde74dec9bf09711656592a7bbd6ee171bc1fda6
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber sha256:4440d0ec64b1b5409dc44779ae9ba3612cc520abd549812d351ec595b6ae6ff9
    D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope.simplexFiber_isPolytope sha256:b0cbf76e0c6bd5443e395dee4ebfaf77a356b7d427c2884ad2bb9541354289c0
    D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion.continuous_linear_expansion sha256:1fa41d9614547f8ad7cc9f56010786362e0c5dd2fa04a8c473f9e75d92106007
    D5/S3/Quantum/FiniteDimensional.bornProbability sha256:70d0693159ac58607261fa66304a04ba6078de3492431f14485817d5497d9d6d
    D5/S3/Quantum/Matrix/CartesianVariance.density_nonempty sha256:18b5b208f62ae872abfb0b7d5989bb6985e01575eb116c91f9cb1104621a29af
    D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
    D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity sha256:4ba4e6b5fd69f7af3d48c8ecc93d1d3efe0fbd32799aa8b021b502f76ad76988
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
import D5.S3.Estimation.DecisionRisk.FiniteBayesRiskDominanceCriterion
import Mathlib.Analysis.Normed.Group.Quotient
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.FiniteDimensional (bornProbability)

namespace D5.S3.QuantumContext.FinitePreparationCertification

/-- Definition 3, with the measurement-setting index trivial: all effect identities. -/
def responsePolytope {d m : ℕ}
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ) : Set (Fin m → ℝ) :=
  {r | (∀ b, 0 ≤ r b) ∧ (∑ b, r b) = 1 ∧
    ∀ β : Fin m → ℝ,
      (∑ b, (β b : ℂ) • M b) = 0 → (∑ b, β b * r b) = 0}

/-- Definition 1 for normalized preparations and one measurement.
The finite sums express every preparation identity, including on an infinite index set.
HasSum expresses the source's discrete ontic sum, without a finite-alphabet assumption.
Unlike the existing matrix-factorized Subtheory predicate, the assignments here are unrestricted.
-/
def NoncontextualTable {d m : ℕ} {ι : Type}
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ) (p : ι → Fin m → ℝ) : Prop :=
  ∃ (Λ : Type) (μ : ι → Λ → ℝ) (ξ : Λ → Fin m → ℝ),
    (∀ a : ι, ∀ l : Λ, 0 ≤ μ a l) ∧
    (∀ a : ι, HasSum (μ a) 1) ∧
    (∀ l : Λ, ξ l ∈ responsePolytope M) ∧
    (∀ l : Λ, ∀ s : Finset ι, ∀ α : ι → ℝ,
      (∑ a ∈ s, (α a : ℂ) • ρ a) = 0 → (∑ a ∈ s, α a * μ a l) = 0) ∧
    ∀ a : ι, ∀ b : Fin m,
      HasSum (fun l : Λ => ξ l b * μ a l) (p a b)

/-- Definition 2: a single common model for the set of all normalized quantum states. -/
def Classical {d m : ℕ} (M : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  NoncontextualTable
    (fun ρ : {ρ : Matrix (Fin d) (Fin d) ℂ // IsDensity ρ} => ρ.val) M
    (fun ρ b => (bornProbability ρ.val (M b)).re)

/-- Conjecture 1: an actual violated linear inequality, not merely an SDP witness. -/
def claim : Prop :=
  ∀ d : ℕ, 0 < d → ∀ m : ℕ, 0 < m →
    ∀ M : Fin m → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM M → ¬ Classical M →
      ∃ (n : ℕ) (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ)
        (w : Fin n → Fin m → ℝ) (c : ℝ),
        (∀ a : Fin n, IsDensity (ρ a)) ∧
        (∀ p : Fin n → Fin m → ℝ, NoncontextualTable ρ M p →
          (∑ a, ∑ b, w a b * p a b) ≤ c) ∧
        c < ∑ a, ∑ b, w a b * (bornProbability (ρ a) (M b)).re

open D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope

private theorem response_finite_hull {d m : ℕ}
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    ∃ V : Finset (Fin m → ℝ), convexHull ℝ (V : Set (Fin m → ℝ)) = responsePolytope M := by
  classical
  let K : Submodule ℝ (Fin m → ℝ) :=
    ⨅ β : {β : Fin m → ℝ // (∑ b, (β b : ℂ) • M b) = 0},
      LinearMap.ker (dotProductBilin ℝ ℝ β.val)
  letI : IsClosed (K : Set (Fin m → ℝ)) := K.closed_of_finiteDimensional
  obtain ⟨V, hV⟩ := simplexFiber_isPolytope K.mkQ 0
  refine ⟨V, hV.trans ?_⟩
  ext r
  simp only [simplexFiber, Set.mem_ofPred_eq, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  change ((∀ b, 0 ≤ r b) ∧ (∑ b, r b) = 1) ∧
    (∀ β : Fin m → ℝ, (∑ b, (β b : ℂ) • M b) = 0 → (∑ b, β b * r b) = 0) ↔ _
  exact and_assoc

private theorem vertex_coordinates {d m : ℕ}
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (V : Finset (Fin m → ℝ))
    (hV : convexHull ℝ (V : Set (Fin m → ℝ)) = responsePolytope M)
    (r : Fin m → ℝ) (hr : r ∈ responsePolytope M) :
    ∃ t : V → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧
      ∀ b, (∑ i : V, t i * i.val b) = r b := by
  classical
  obtain ⟨w, hw, hs, he⟩ := Finset.mem_convexHull'.mp (hV.symm ▸ hr)
  refine ⟨fun i => w i.val, fun i => hw i.val i.property, ?_, ?_⟩
  · simpa only [Finset.sum_coe_sort] using hs
  · intro b
    have hb := congrFun he b
    rw [Finset.sum_coe_sort (s := V) (f := fun y => w y * y b)]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hb

private def FixedTable {d m : ℕ} {ι κ : Type} [Fintype κ]
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : ι → Fin m → ℝ) : Prop :=
  ∃ μ : ι → κ → ℝ,
    (∀ a i, 0 ≤ μ a i) ∧ (∀ a, (∑ i, μ a i) = 1) ∧
    (∀ i, ∀ s : Finset ι, ∀ α : ι → ℝ,
      (∑ a ∈ s, (α a : ℂ) • ρ a) = 0 → (∑ a ∈ s, α a * μ a i) = 0) ∧
    ∀ a b, (∑ i, v i b * μ a i) = p a b

private theorem compress_table {d m : ℕ} {ι : Type}
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ) (p : ι → Fin m → ℝ)
    (V : Finset (Fin m → ℝ))
    (hV : convexHull ℝ (V : Set (Fin m → ℝ)) = responsePolytope M)
    (h : NoncontextualTable ρ M p) : FixedTable ρ (fun i : V => i.val) p := by
  classical
  obtain ⟨Λ, μ, ξ, hn, hs, hξ, hi, hp⟩ := h
  choose t htn hts hte using fun l => vertex_coordinates M V hV (ξ l) (hξ l)
  have htl (l : Λ) (i : V) : t l i ≤ 1 := by
    exact (mem_Icc_of_mem_stdSimplex
      (show t l ∈ stdSimplex ℝ V from ⟨htn l, hts l⟩) i).2
  have hsum (a : ι) (i : V) : Summable (fun l => t l i * μ a l) := by
    exact (hs a).summable.of_nonneg_of_le
      (fun l => mul_nonneg (htn l i) (hn a l))
      (fun l => by simpa only [one_mul] using mul_le_mul_of_nonneg_right (htl l i) (hn a l))
  let ν : ι → V → ℝ := fun a i => ∑' l, t l i * μ a l
  refine ⟨ν, ?_, ?_, ?_, ?_⟩
  · intro a i
    exact tsum_nonneg (fun l => mul_nonneg (htn l i) (hn a l))
  · intro a
    change (∑ i : V, ∑' l, t l i * μ a l) = 1
    rw [← Summable.tsum_finsetSum (fun i _ => hsum a i)]
    simp_rw [← Finset.sum_mul, hts, one_mul]
    exact (hs a).tsum_eq
  · intro i s α hα
    change (∑ a ∈ s, α a * ∑' l, t l i * μ a l) = 0
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun a _ => (hsum a i).mul_left (α a))]
    have he (l : Λ) : (∑ a ∈ s, α a * (t l i * μ a l)) = 0 := by
      calc
        _ = t l i * ∑ a ∈ s, α a * μ a l := by rw [Finset.mul_sum]; congr 1; ext a; ring
        _ = 0 := by rw [hi l s α hα, mul_zero]
    simp_rw [he]
    exact tsum_zero
  · intro a b
    change (∑ i : V, i.val b * ∑' l, t l i * μ a l) = p a b
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum a i).mul_left (i.val b))]
    have he (l : Λ) : (∑ i : V, i.val b * (t l i * μ a l)) = ξ l b * μ a l := by
      calc
        _ = (∑ i : V, t l i * i.val b) * μ a l := by rw [Finset.sum_mul]; congr 1; ext i; ring
        _ = _ := by rw [hte l b]
    simp_rw [he]
    exact (hp a b).tsum_eq

private theorem fixed_table_model {d m : ℕ} {ι κ : Type} [Fintype κ]
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (v : κ → Fin m → ℝ) (p : ι → Fin m → ℝ)
    (hv : ∀ i, v i ∈ responsePolytope M) (h : FixedTable ρ v p) :
    NoncontextualTable ρ M p := by
  obtain ⟨μ, hn, hs, hi, hp⟩ := h
  refine ⟨κ, μ, v, hn, ?_, hv, hi, ?_⟩
  · intro a
    simpa only [hs a] using hasSum_fintype (μ a)
  · intro a b
    simpa only [hp a b] using hasSum_fintype (fun i => v i b * μ a i)

private def localConstraints {d m : ℕ} {ι κ : Type} [Fintype κ]
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : ι → Fin m → ℝ) (S : Finset ι) : Set (ι → κ → ℝ) :=
  {μ | (∀ a ∈ S, ∀ b, (∑ i, v i b * μ a i) = p a b) ∧
    ∀ i, ∀ s : Finset ι, s ⊆ S → ∀ α : ι → ℝ,
      (∑ a ∈ s, (α a : ℂ) • ρ a) = 0 → (∑ a ∈ s, α a * μ a i) = 0}

private theorem localConstraints_closed {d m : ℕ} {ι κ : Type} [Fintype κ]
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : ι → Fin m → ℝ) (S : Finset ι) : IsClosed (localConstraints ρ v p S) := by
  simp only [localConstraints, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · refine isClosed_iInter fun a => isClosed_iInter fun _ =>
      isClosed_iInter fun b => ?_
    exact isClosed_eq (by fun_prop) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun s =>
      isClosed_iInter fun _ => isClosed_iInter fun α =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq (by fun_prop) continuous_const

private theorem fixed_global_of_finite {d m : ℕ} {ι κ : Type} [Fintype κ] [Nonempty κ]
    (ρ : ι → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : ι → Fin m → ℝ)
    (h : ∀ S : Finset ι, FixedTable (fun a : S => ρ a.val) v (fun a => p a.val)) :
    FixedTable ρ v p := by
  classical
  let B : Set (ι → κ → ℝ) := {μ | ∀ a, μ a ∈ stdSimplex ℝ κ}
  have hB : IsCompact B := isCompact_pi_infinite (fun _ : ι => isCompact_stdSimplex ℝ κ)
  have hne (S : Finset ι) : (B ∩ localConstraints ρ v p S).Nonempty := by
    obtain ⟨μ, hn, hs, hi, hp⟩ := h S
    let i₀ : κ := Classical.choice (inferInstance : Nonempty κ)
    let μ₀ : κ → ℝ := fun i => if i = i₀ then 1 else 0
    have hμ₀ : μ₀ ∈ stdSimplex ℝ κ := by
      simpa only [μ₀, eq_comm] using ite_eq_mem_stdSimplex ℝ i₀
    let ν : ι → κ → ℝ := fun a => if ha : a ∈ S then μ ⟨a, ha⟩ else μ₀
    refine ⟨ν, ?_, ?_, ?_⟩
    · intro a
      dsimp [ν]
      split_ifs with ha
      · exact ⟨hn ⟨a, ha⟩, hs ⟨a, ha⟩⟩
      · exact hμ₀
    · intro a ha b
      simpa only [ν, dif_pos ha] using hp ⟨a, ha⟩ b
    · intro i s hsS α hα
      let t : Finset S := s.attach.image (fun a => (⟨a.val, hsS a.property⟩ : S))
      have ht : ∀ a : S, a ∈ t ↔ a.val ∈ s := by
        intro a
        simp only [t, Finset.mem_image, Finset.mem_attach, true_and]
        constructor
        · rintro ⟨b, rfl⟩; exact b.property
        · intro ha; exact ⟨⟨a.val, ha⟩, Subtype.ext rfl⟩
      have hsum {F : Type} [AddCommMonoid F] (f : ι → F) :
          (∑ a ∈ t, f a.val) = ∑ a ∈ s, f a := by
        apply Finset.sum_bij (fun a _ => a.val)
        · intro a ha; exact (ht a).mp ha
        · intro a ha b hb hab; exact Subtype.ext hab
        · intro a ha; exact ⟨⟨a, hsS ha⟩, (ht _).mpr ha, rfl⟩
        · intros; rfl
      have hi' := hi i t (fun a => α a.val) ((hsum (fun a => (α a : ℂ) • ρ a)).trans hα)
      have he : (∑ a ∈ s, α a * ν a i) = ∑ a ∈ t, α a.val * μ a i := by
        rw [← hsum (fun a => α a * ν a i)]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [ν, dif_pos a.property]
      exact he.trans hi'
  obtain ⟨μ, hμB, hμ⟩ := hB.inter_iInter_nonempty
    (localConstraints ρ v p) (localConstraints_closed ρ v p) (by
      intro T
      let S := T.biUnion id
      obtain ⟨μ, hμB, hμ⟩ := hne S
      refine ⟨μ, hμB, Set.mem_iInter₂.mpr ?_⟩
      intro R hR
      have hRS : R ⊆ S := by
        exact Finset.subset_biUnion_of_mem id hR
      exact ⟨fun a ha b => hμ.1 a (hRS ha) b,
        fun i s hs α hα => hμ.2 i s (hs.trans hRS) α hα⟩)
  have hμS (S : Finset ι) := Set.mem_iInter.mp hμ S
  refine ⟨μ, fun a => (hμB a).1,
    fun a => (hμB a).2, ?_, ?_⟩
  · intro i s α hα
    exact (hμS s).2 i s (Finset.Subset.refl s) α hα
  · intro a b
    exact (hμS {a}).1 a (Finset.mem_singleton_self a) b

private def preparationWeights {d n : ℕ} {κ : Type} [Fintype κ]
    (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ) : Set (Fin n → κ → ℝ) :=
  {μ | (∀ a, μ a ∈ stdSimplex ℝ κ) ∧
    ∀ i, ∀ s : Finset (Fin n), ∀ α : Fin n → ℝ,
      (∑ a ∈ s, (α a : ℂ) • ρ a) = 0 → (∑ a ∈ s, α a * μ a i) = 0}

private theorem preparationWeights_compact {d n : ℕ} {κ : Type} [Fintype κ]
    (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ) : IsCompact (preparationWeights (κ := κ) ρ) := by
  have hc : IsClosed {μ : Fin n → κ → ℝ |
      ∀ i, ∀ s : Finset (Fin n), ∀ α : Fin n → ℝ,
        (∑ a ∈ s, (α a : ℂ) • ρ a) = 0 → (∑ a ∈ s, α a * μ a i) = 0} := by
    simpa [localConstraints] using
      (localConstraints_closed (m := 0) ρ
        (fun (_ : κ) (b : Fin 0) => Fin.elim0 b)
        (fun (_ : Fin n) (b : Fin 0) => Fin.elim0 b) Finset.univ)
  exact (isCompact_pi_infinite (fun _ : Fin n => isCompact_stdSimplex ℝ κ)).inter_right hc

private theorem preparationWeights_convex {d n : ℕ} {κ : Type} [Fintype κ]
    (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ) : Convex ℝ (preparationWeights (κ := κ) ρ) := by
  intro μ hμ ν hν a b ha hb hab
  refine ⟨fun x => convex_stdSimplex ℝ κ (hμ.1 x) (hν.1 x) ha hb hab, ?_⟩
  intro i s α hα
  change (∑ x ∈ s, α x * (a * μ x i + b * ν x i)) = 0
  calc
    _ = a * (∑ x ∈ s, α x * μ x i) + b * (∑ x ∈ s, α x * ν x i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hμ.2 i s α hα, hν.2 i s α hα]; ring

private theorem fixed_table_iff_image {d n m : ℕ} {κ : Type} [Fintype κ]
    (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) :
    FixedTable ρ v p ↔ p ∈ (show (Fin n → _ → ℝ) →ₗ[ℝ] (Fin n → Fin m → ℝ) from mulRightLinearMap (Fin n) ℝ v) '' preparationWeights ρ := by
  constructor
  · rintro ⟨μ, hn, hs, hi, hp⟩
    refine ⟨μ, ⟨fun a => ⟨hn a, hs a⟩, hi⟩, ?_⟩
    ext a b
    change (∑ i, μ a i * v i b) = p a b
    simpa only [mul_comm] using hp a b
  · rintro ⟨μ, hμ, hp⟩
    refine ⟨μ, fun a => (hμ.1 a).1, fun a => (hμ.1 a).2, hμ.2, ?_⟩
    intro a b
    have he := congrFun (congrFun hp a) b
    change (∑ i, μ a i * v i b) = p a b at he
    simpa only [mul_comm] using he

private theorem dual_table_coordinates {n m : ℕ}
    (f : (Fin n → Fin m → ℝ) →ₗ[ℝ] ℝ) (p : Fin n → Fin m → ℝ) :
    f p = ∑ a, ∑ b, f (Pi.single a (Pi.single b 1)) * p a b := by
  exact D5.S3.Estimation.DecisionRisk.FiniteBayesRiskDominanceCriterion.continuous_linear_expansion
    (LinearMap.toContinuousLinearMap f) p

private theorem separate_finite_table {d n m : ℕ}
    (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (p : Fin n → Fin m → ℝ)
    (h : ¬ NoncontextualTable ρ M p) :
    ∃ (w : Fin n → Fin m → ℝ) (c : ℝ),
      (∀ q, NoncontextualTable ρ M q → (∑ a, ∑ b, w a b * q a b) ≤ c) ∧
      c < ∑ a, ∑ b, w a b * p a b := by
  classical
  obtain ⟨V, hV⟩ := response_finite_hull M
  let v : V → Fin m → ℝ := fun i => i.val
  have hv (i : V) : v i ∈ responsePolytope M := by
    rw [← hV]
    exact subset_convexHull ℝ (V : Set (Fin m → ℝ)) i.property
  let C := (show (Fin n → _ → ℝ) →ₗ[ℝ] (Fin n → Fin m → ℝ) from mulRightLinearMap (Fin n) ℝ v) '' preparationWeights ρ
  have he (q : Fin n → Fin m → ℝ) : NoncontextualTable ρ M q ↔ q ∈ C := by
    constructor
    · intro hq
      exact (fixed_table_iff_image ρ v q).mp (compress_table ρ M q V hV hq)
    · intro hq
      exact fixed_table_model ρ M v q hv ((fixed_table_iff_image ρ v q).mpr hq)
  have hcc : IsCompact C := (preparationWeights_compact ρ).image
    ((show (Fin n → _ → ℝ) →ₗ[ℝ] (Fin n → Fin m → ℝ) from mulRightLinearMap (Fin n) ℝ v)).continuous_of_finiteDimensional
  have hcv : Convex ℝ C := (preparationWeights_convex ρ).linear_image ((show (Fin n → _ → ℝ) →ₗ[ℝ] (Fin n → Fin m → ℝ) from mulRightLinearMap (Fin n) ℝ v))
  have hout : p ∉ C := fun hp => h ((he p).mpr hp)
  obtain ⟨f, c, hfc, hfp⟩ := geometric_hahn_banach_closed_point hcv hcc.isClosed hout
  refine ⟨fun a b => f (Pi.single a (Pi.single b 1)), c, ?_, ?_⟩
  · intro q hq
    exact (dual_table_coordinates f.toLinearMap q).symm.le.trans (hfc q ((he q).mp hq)).le
  · exact hfp.trans_eq (dual_table_coordinates f.toLinearMap p)

private theorem fixed_table_reindex {d m : ℕ} {ι η κ : Type} [Fintype κ]
    (e : ι ≃ η) (ρ : η → Matrix (Fin d) (Fin d) ℂ) (v : κ → Fin m → ℝ)
    (p : η → Fin m → ℝ) (h : FixedTable ρ v p) :
    FixedTable (fun a => ρ (e a)) v (fun a => p (e a)) := by
  classical
  obtain ⟨μ, hn, hs, hi, hp⟩ := h
  refine ⟨fun a => μ (e a), fun a => hn (e a), fun a => hs (e a), ?_, fun a => hp (e a)⟩
  intro i s α hα
  let β : η → ℝ := fun a => α (e.symm a)
  have hsum {F : Type} [AddCommMonoid F] (f : ι → F) :
      (∑ a ∈ s.image e, f (e.symm a)) = ∑ a ∈ s, f a := by
    rw [Finset.sum_image]
    · simp only [Equiv.symm_apply_apply]
    · intro a ha b hb hab
      exact e.injective hab
  have hrel : (∑ a ∈ s.image e, (β a : ℂ) • ρ a) = 0 := by
    simpa only [β, Equiv.apply_symm_apply] using
      (hsum (fun a => (α a : ℂ) • ρ (e a))).trans hα
  have hμ := hi i (s.image e) β hrel
  have he : (∑ a ∈ s.image e, β a * μ a i) = ∑ a ∈ s, α a * μ (e a) i := by
    simpa only [β, Equiv.apply_symm_apply] using hsum (fun a => α a * μ (e a) i)
  exact he.symm.trans hμ

open scoped ComplexOrder

private theorem finite_obstruction {d m : ℕ} (hd : 0 < d)
    (M : Fin m → Matrix (Fin d) (Fin d) ℂ) (hnc : ¬ Classical M) :
    ∃ (n : ℕ) (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ),
      (∀ a, IsDensity (ρ a)) ∧
      ¬ NoncontextualTable ρ M (fun a b => (bornProbability (ρ a) (M b)).re) := by
  classical
  by_contra hgoal
  have hfinite (n : ℕ) (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ)
      (hρ : ∀ a, IsDensity (ρ a)) :
      NoncontextualTable ρ M (fun a b => (bornProbability (ρ a) (M b)).re) := by
    by_contra hn
    exact hgoal ⟨n, ρ, hρ, hn⟩
  obtain ⟨V, hV⟩ := response_finite_hull M
  obtain ⟨ρ₀, hρ₀⟩ := D5.S3.Quantum.Matrix.CartesianVariance.density_nonempty hd
  have hsingle := compress_table (fun _ : Fin 1 => ρ₀) M
    (fun _ b => (bornProbability ρ₀ (M b)).re) V hV
    (hfinite 1 (fun _ => ρ₀) (fun _ => hρ₀))
  have hVne : Nonempty V := by
    obtain ⟨μ, hn, hs, hi, hp⟩ := hsingle
    by_contra hnV
    haveI : IsEmpty V := not_nonempty_iff.mp hnV
    have hf := hs 0
    simp at hf
  letI : Nonempty V := hVne
  let Ω := {ρ : Matrix (Fin d) (Fin d) ℂ // IsDensity ρ}
  let R : Ω → Matrix (Fin d) (Fin d) ℂ := fun a => a.val
  let p : Ω → Fin m → ℝ := fun a b => (bornProbability a.val (M b)).re
  let v : V → Fin m → ℝ := fun i => i.val
  have hlocal (S : Finset Ω) : FixedTable (fun a : S => R a.val) v (fun a => p a.val) := by
    let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
    let ρ : Fin (Fintype.card S) → Matrix (Fin d) (Fin d) ℂ := fun a => R (e a).val
    have hρ (a) : IsDensity (ρ a) := (e a).val.property
    have hc := compress_table ρ M
      (fun a b => (bornProbability (ρ a) (M b)).re) V hV (hfinite _ ρ hρ)
    simpa only [ρ, R, p, Equiv.apply_symm_apply] using
      fixed_table_reindex e.symm ρ v (fun a b => (bornProbability (ρ a) (M b)).re) hc
  have hg := fixed_global_of_finite R v p hlocal
  apply hnc
  exact fixed_table_model R M v p (fun i => by
    rw [← hV]
    exact subset_convexHull ℝ (V : Set (Fin m → ℝ)) i.property) hg


theorem result : D5.S3.QuantumContext.FinitePreparationCertification.claim := by
  intro d hd m hm M hM hnc
  obtain ⟨n, ρ, hρ, hn⟩ := finite_obstruction hd M hnc
  obtain ⟨w, c, hw, hc⟩ := separate_finite_table ρ M _ hn
  exact ⟨n, ρ, w, c, hρ, hw, hc⟩


end D5.S3.QuantumContext.FinitePreparationCertification
