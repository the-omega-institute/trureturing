/- GID: D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A finite set has a common entangled state for all partitions in every frame. -/

import D5.S3.Quantum.PureState.PureStateHandshake

open Matrix BigOperators

namespace D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions

open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

/-- Ordered factorizations into at least two factors, each of dimension at least two. -/
def Partition (d : ℕ) :=
  {p : (Σ k : ℕ, Fin k → ℕ) //
    2 ≤ p.1 ∧ (∀ i, 2 ≤ p.2 i) ∧ ∏ i, p.2 i = d}

/-- The fixed mixed-radix identification for an ordered factorization. -/
def partitionEquiv {d : ℕ} (p : Partition d) :
    ((i : Fin p.val.1) → Fin (p.val.2 i)) ≃ Fin d :=
  finPiFinEquiv.trans (finCongr p.property.2.2)

/-- Tensor products of local matrices in the fixed coordinate identification. -/
def productState {d : ℕ} (p : Partition d)
    (ρ : (i : Fin p.val.1) → Matrix (Fin (p.val.2 i)) (Fin (p.val.2 i)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun x y => ∏ i, ρ i (partitionEquiv p |>.symm x i) (partitionEquiv p |>.symm y i)

/-- Separable states are the real convex hull of products of local density matrices. -/
def Separable {d : ℕ} (p : Partition d) (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ ∈ convexHull ℝ {σ | ∃ τ, (∀ i, (τ i).PosSemidef ∧ (τ i).trace = 1) ∧
    σ = productState p τ}

/-- In every frame one member of a fixed finite set is entangled for all factorizations. -/
def claim : Prop :=
  ∀ d a b : ℕ, 2 ≤ a → 2 ≤ b → d = a * b →
    ∃ s : Finset (Matrix (Fin d) (Fin d) ℂ),
      (∀ ρ ∈ s, ρ.PosSemidef ∧ ρ.trace = 1) ∧
      ∀ u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ,
        ∃ ρ ∈ s, ∀ p : Partition d, ¬ Separable p (u * ρ * star u)

private def corner {d : ℕ} (p : Partition d) (x : Fin 2 × Fin 2) : Fin d :=
  partitionEquiv p fun i =>
    ⟨if i.val = 0 then x.1.val else if i.val = 1 then x.2.val else 0, by
      have hi := p.property.2.1 i
      split_ifs <;> omega⟩

private def minor {d : ℕ} (c : Fin 2 × Fin 2 → Fin d) (v : Fin d → ℂ) : ℂ :=
  v (c (0, 0)) * v (c (1, 1)) - v (c (0, 1)) * v (c (1, 0))

private lemma corner_injective {d : ℕ} (p : Partition d) :
    Function.Injective (corner p) := by
  sorry

private def minorPolynomial {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) : MvPolynomial (Fin d) ℂ :=
  let l := fun i => ∑ j, MvPolynomial.C (u i j) * MvPolynomial.X j
  l (c (0, 0)) * l (c (1, 1)) - l (c (0, 1)) * l (c (1, 0))

private lemma minorPolynomial_eval {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) (v : Fin d → ℂ) :
    MvPolynomial.eval v (minorPolynomial u c) = minor c (u *ᵥ v) := by
  sorry

private lemma minorPolynomial_nonzero {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ) (c : Fin 2 × Fin 2 ↪ Fin d) :
    minorPolynomial u c ≠ 0 := by
  sorry

private lemma minorPolynomial_degree {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin 2 × Fin 2 ↪ Fin d) : (minorPolynomial u c).totalDegree ≤ 2 := by
  sorry

private def gridBound (d : ℕ) : ℕ :=
  2 * Fintype.card ((Fin 2 × Fin 2) ↪ Fin d)

private noncomputable def grid (d : ℕ) : Finset (Fin d → ℂ) := by
  classical
  exact (Fintype.piFinset fun _ =>
    (Finset.range (gridBound d + 1)).image (fun n => (n : ℂ))).filter (· ≠ 0)

private lemma common_grid {d : ℕ} (hd : 4 ≤ d) (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u ∈ Matrix.specialUnitaryGroup (Fin d) ℂ) :
    ∃ v ∈ grid d, ∀ c : Fin 2 × Fin 2 ↪ Fin d, minor c (u *ᵥ v) ≠ 0 := by
  sorry

private def mass {d : ℕ} (v : Fin d → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

private noncomputable def pure {d : ℕ} (v : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (mass v)⁻¹ • rankOneDensity v

private lemma mass_pos {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) : 0 < mass v := by
  sorry

private lemma pure_density {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    (pure v).PosSemidef ∧ (pure v).trace = 1 := by
  sorry

private lemma pure_transform {d : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    u * pure v * star u = (mass v)⁻¹ • rankOneDensity (u *ᵥ v) := by
  sorry

private lemma separable_pure_minor {d : ℕ} (p : Partition d) (v : Fin d → ℂ)
    (t : ℝ) (ht : 0 < t) (hs : Separable p (t • rankOneDensity v)) :
    minor (corner p) v = 0 := by
  sorry

theorem result : claim := by
  classical
  intro d a b ha hb hd
  have hd4 : 4 ≤ d := by nlinarith
  refine ⟨(grid d).image pure, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hρ
    exact pure_density v (Finset.mem_filter.mp hv).2
  · intro u hu
    obtain ⟨v, hv, hminor⟩ := common_grid hd4 u hu
    refine ⟨pure v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    intro p hs
    rw [pure_transform] at hs
    exact hminor ⟨corner p, corner_injective p⟩
      (separable_pure_minor p (u *ᵥ v) (mass v)⁻¹
        (inv_pos.mpr (mass_pos v (Finset.mem_filter.mp hv).2)) hs)

end D5.S3.Quantum.Entanglement.Witness.AbsolutelyEntangledAllPartitions
