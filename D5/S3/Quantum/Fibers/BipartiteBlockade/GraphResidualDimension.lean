/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/GraphResidualDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/GraphResidualDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual nonlinear neighborhood coordinates of a bipartite graph have a codimension-one balanced diagonal residual. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
import D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
import D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension

open JointDiagonalCoordinates DiagonalResidual
open private signed_conservation small_vertex_recovery colorSign from
  D5.S3.Quantum.Fibers.BipartiteBlockade.SmallSettingRecovery
open private residual_eq_ker from
  D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
open private neighborhood_independent same_color_of_common_neighbor from
  D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
open private coherent_lift_of_balanced_diagonal small_centered_density_perturbations from
  D5.S3.Quantum.Fibers.BipartiteBlockade.PhysicalSingleSettingLower

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The full-rank maximally mixed state on the legal independent configurations. -/
def maximallyMixed (G : SimpleGraph V) : Matrix (Configuration G) (Configuration G) ℂ :=
  ((Fintype.card (Configuration G) : ℝ)⁻¹) • 1

/-- The actual vertex sum multiplying one distinct nonlinear neighborhood. -/
def classWeight (G : SimpleGraph V) (color : V → Bool) (Ω : V → ℝ)
    (N : nonlinearNeighborhoods G) : ℝ :=
  ∑ v, if G.neighborFinset v = N.val then (if color v then 1 else -1) * Ω v ^ 2 else 0

private theorem nonlinear_mem (G : SimpleGraph V) (v : V)
    (hv : 2 ≤ (G.neighborFinset v).card) :
    G.neighborFinset v ∈ nonlinearNeighborhoods G := by
  exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩

private theorem family_independent (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) :
    ∀ N ∈ nonlinearNeighborhoods G, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v := by
  intro N hN
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hN
  exact neighborhood_independent G color proper v

private theorem family_large (G : SimpleGraph V) :
    ∀ N ∈ nonlinearNeighborhoods G, 2 ≤ N.card := by
  intro N hN
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hN
  exact (Finset.mem_filter.mp hv).2

private theorem classWeight_nonzero (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (nonzero : ∀ v, Ω v ≠ 0) (N : nonlinearNeighborhoods G) :
    classWeight G color Ω N ≠ 0 := by
  obtain ⟨base, hbase, hN⟩ := Finset.mem_image.mp N.property
  have large : 2 ≤ (G.neighborFinset base).card := (Finset.mem_filter.mp hbase).2
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset base).card)
  have hcolor : ∀ v, G.neighborFinset v = N.val → color v = color base := by
    intro v hv
    apply same_color_of_common_neighbor G color proper
    · have hmem : w ∈ G.neighborFinset v := by rw [hv, ← hN]; exact hw
      simpa using hmem
    · simpa using hw
  have hfactor : classWeight G color Ω N =
      (if color base then 1 else -1) *
        ∑ v, if G.neighborFinset v = N.val then Ω v ^ 2 else 0 := by
    unfold classWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : G.neighborFinset v = N.val
    · simp [hv, hcolor v hv]
    · simp [hv]
  rw [hfactor]
  apply mul_ne_zero
  · cases h : color base <;> norm_num [h]
  · apply ne_of_gt
    apply Finset.sum_pos'
    · intro v _; split_ifs <;> positivity
    · exact ⟨base, Finset.mem_univ _, by
        simpa [hN] using sq_pos_of_ne_zero (nonzero base)⟩

private theorem clear_disjoint (G : SimpleGraph V) (v : V) (S : Configuration G) :
    clear G v S ↔ Disjoint (G.neighborFinset v) S.val := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro u hu hS
    exact h u hS (by simpa using hu)
  · intro h u hu huv
    exact Finset.disjoint_left.mp h (by simpa using huv) hu

private theorem block_eq (G : SimpleGraph V) (δ : Configuration G → ℝ) (v : V) :
    blockMoment G δ v = blockingMoment G (G.neighborFinset v) δ := by
  unfold blockMoment blockingMoment
  simp_rw [clear_disjoint]

private theorem small_block_zero (G : SimpleGraph V) (δ : Configuration G → ℝ)
    (zeroTrace : (∑ S, δ S) = 0)
    (zeroMean : ∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0)
    (v : V) (small : (G.neighborFinset v).card ≤ 1) :
    blockMoment G δ v = 0 := by
  rw [block_eq]
  by_cases he : G.neighborFinset v = ∅
  · simpa [blockingMoment, he] using zeroTrace
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hs : G.neighborFinset v = {u} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hu, fun w hw => Finset.card_le_one.mp small w hw u hu⟩
    have hsplit : blockingMoment G (G.neighborFinset v) δ =
        (∑ S, δ S) - ∑ S, δ S * (if u ∈ S.val then 1 else 0) := by
      unfold blockingMoment
      rw [hs, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S _
      by_cases huS : u ∈ S.val <;> simp [huS]
    rw [hsplit, zeroTrace, zeroMean u, sub_zero]

private theorem class_decomposition (G : SimpleGraph V) (color : V → Bool) (Ω : V → ℝ)
    (δ : Configuration G → ℝ) (zeroTrace : (∑ S, δ S) = 0)
    (zeroMean : ∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) :
    (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) =
      compatibility (nonlinearNeighborhoods G) (classWeight G color Ω)
        (fun N => blockingMoment G N.val δ) := by
  change _ = ∑ N : nonlinearNeighborhoods G,
    (∑ v, if G.neighborFinset v = N.val then
      (if color v then 1 else -1) * Ω v ^ 2 else 0) * blockingMoment G N.val δ
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 2 ≤ (G.neighborFinset v).card
  · let N : nonlinearNeighborhoods G := ⟨G.neighborFinset v, nonlinear_mem G v hv⟩
    rw [Finset.sum_eq_single N]
    · simp only [N, ite_true, block_eq]
    · intro M _ hM
      have hn : G.neighborFinset v ≠ M.val := by
        intro heq
        exact hM (Subtype.ext heq.symm)
      simp only [hn, ite_false, zero_mul]
    · simp
  · have hs : (G.neighborFinset v).card ≤ 1 := by omega
    rw [small_block_zero G δ zeroTrace zeroMean v hs, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro N _
    have hn : G.neighborFinset v ≠ N.val := by
      intro heq
      exact hv (heq ▸ family_large G N.val N.property)
    simp only [hn, ite_false, zero_mul]

/-- For the distinct nonlinear open neighborhoods of any finite bipartite graph,
the actual zero-mass, fixed-mean diagonal blocking directions satisfying the
bipartite acceleration compatibility equation form a space of dimension d−1.
Every vector in that compatibility kernel is realized by one actual signed
diagonal on the legal independent configurations. -/
theorem graph_residual_dimension_and_realization
    (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty) :
    Module.finrank ℝ
      (attainableResidual G (nonlinearNeighborhoods G) (classWeight G color Ω)) =
        (nonlinearNeighborhoods G).card - 1 ∧
    ∀ x : nonlinearNeighborhoods G → ℝ,
      compatibility (nonlinearNeighborhoods G) (classWeight G color Ω) x = 0 →
      ∃ δ : Configuration G → ℝ,
        (∑ S, δ S) = 0 ∧
        (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
        (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 ∧
        (∀ N : nonlinearNeighborhoods G, blockingMoment G N.val δ = x N) ∧
        (G.Connected → ∃ R : Matrix (Configuration G) (Configuration G) ℂ,
          R.IsHermitian ∧ Matrix.trace R = 0 ∧
          (∀ v, Matrix.trace (R * number G v) = 0) ∧
          (∀ v, Matrix.trace (R *
            ⁅hamiltonian G (fun u => (Ω u : ℂ)),
              ⁅hamiltonian G (fun u => (Ω u : ℂ)), number G v⁆⁆) = 0) ∧
          (∀ v, Matrix.trace (R * blockade G v) = (blockMoment G δ v : ℂ)) ∧
          ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
            (maximallyMixed G + t • R).PosDef ∧
            Matrix.trace (maximallyMixed G + t • R) = 1 ∧
            (∀ v, occupationMean G (maximallyMixed G + t • R) v =
              occupationMean G (maximallyMixed G) v) ∧
            (∀ v, acceleration G Ω (maximallyMixed G + t • R) v =
              acceleration G Ω (maximallyMixed G) v) ∧
            ∀ v, blockadeMean G (maximallyMixed G + t • R) v =
              blockadeMean G (maximallyMixed G) v + t * blockMoment G δ v) := by
  have hi := family_independent G color proper
  have hl := family_large G
  constructor
  · obtain ⟨N, hN⟩ := nonempty
    exact residual_dimension_exact G (nonlinearNeighborhoods G) hi hl
      (classWeight G color Ω) ⟨⟨N,hN⟩, classWeight_nonzero G color proper Ω nonzero ⟨N,hN⟩⟩
  · intro x hx
    obtain ⟨δ, ht, hm, hb⟩ :=
      arbitrary_diagonal_blocking_coordinates G (nonlinearNeighborhoods G) hi hl x
    have hbalanced :
        (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 := by
      rw [class_decomposition G color Ω δ ht hm]
      rw [show (fun N : nonlinearNeighborhoods G => blockingMoment G N.val δ) = x
        from funext hb]
      exact hx
    refine ⟨δ, ht, hm, hbalanced, hb, ?_⟩
    intro connected
    obtain ⟨R, hRH, hRt, hRn, hRa, hRb⟩ :=
      coherent_lift_of_balanced_diagonal G connected color proper Ω nonzero δ ht hm hbalanced
    refine ⟨R, hRH, hRt, hRn, hRa, hRb, ?_⟩
    letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨η, hη, hsmall⟩ := small_centered_density_perturbations R hRH hRt
    refine ⟨η, hη, fun t ht => ?_⟩
    obtain ⟨hpos, htr⟩ := hsmall t ht
    have heval (O : Matrix (Configuration G) (Configuration G) ℂ) :
        Matrix.trace ((maximallyMixed G + t • R) * O) =
          Matrix.trace (maximallyMixed G * O) + t • Matrix.trace (R * O) := by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
    refine ⟨hpos, htr, ?_, ?_, ?_⟩
    · intro v
      unfold occupationMean
      rw [heval, hRn, smul_zero, add_zero]
    · intro v
      unfold acceleration
      rw [heval, hRa, smul_zero, add_zero]
    · intro v
      unfold blockadeMean
      rw [heval, hRb]
      simp only [Complex.add_re, Complex.real_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The Born blocking readout for one independent neighborhood coordinate. -/
def blockingReadout (G : SimpleGraph V) (N : Finset V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) : ℝ :=
  (Matrix.trace (ρ * Matrix.diagonal fun S : Configuration G =>
    if Disjoint N S.val then (1 : ℂ) else 0)).re

/-- Actual density-coordinate displacements at fixed occupation and
single-drive acceleration data, inside an operator-norm ball about the same
maximally mixed state. -/
def physicalBlockingResiduals (G : SimpleGraph V) (Ω : V → ℝ) (radius : ℝ) :
    Set (nonlinearNeighborhoods G → ℝ) :=
  {x | ∃ ρ : Matrix (Configuration G) (Configuration G) ℂ,
    ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
    ‖CStarMatrix.ofMatrix (ρ - maximallyMixed G)‖ < radius ∧
    (∀ v, occupationMean G ρ v = occupationMean G (maximallyMixed G) v) ∧
    (∀ v, acceleration G Ω ρ v = acceleration G Ω (maximallyMixed G) v) ∧
    ∀ N : nonlinearNeighborhoods G,
      blockingReadout G N.val ρ - blockingReadout G N.val (maximallyMixed G) = x N}

private theorem blockade_readout (G : SimpleGraph V) (ρ : Matrix (Configuration G)
    (Configuration G) ℂ) (v : V) :
    blockadeMean G ρ v = blockingReadout G (G.neighborFinset v) ρ := by
  unfold blockadeMean blockingReadout
  congr 2
  ext S T
  simp only [blockade, clear_disjoint]

private theorem value_class_decomposition (G : SimpleGraph V) (color : V → Bool)
    (Ω : V → ℝ) (y : V → ℝ) (x : nonlinearNeighborhoods G → ℝ)
    (small : ∀ v, (G.neighborFinset v).card ≤ 1 → y v = 0)
    (large : ∀ v (hv : 2 ≤ (G.neighborFinset v).card),
      y v = x ⟨G.neighborFinset v, nonlinear_mem G v hv⟩) :
    (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * y v) =
      compatibility (nonlinearNeighborhoods G) (classWeight G color Ω) x := by
  change _ = ∑ N : nonlinearNeighborhoods G,
    (∑ v, if G.neighborFinset v = N.val then
      (if color v then 1 else -1) * Ω v ^ 2 else 0) * x N
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : 2 ≤ (G.neighborFinset v).card
  · let N : nonlinearNeighborhoods G := ⟨G.neighborFinset v, nonlinear_mem G v hv⟩
    rw [Finset.sum_eq_single N]
    · simp only [N, ite_true, large v hv]
    · intro M _ hM
      have hn : G.neighborFinset v ≠ M.val := by
        intro heq
        exact hM (Subtype.ext heq.symm)
      simp only [hn, ite_false, zero_mul]
    · simp
  · rw [small v (by omega), mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro N _
    have hn : G.neighborFinset v ≠ N.val := by
      intro heq
      exact hv (by simpa only [heq] using family_large G N.val N.property)
    simp only [hn, ite_false, zero_mul]

private theorem maximallyMixed_trace (G : SimpleGraph V) :
    Matrix.trace (maximallyMixed G) = 1 := by
  letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
  simp only [maximallyMixed, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  apply inv_mul_cancel₀
  exact_mod_cast Fintype.card_ne_zero (α := Configuration G)

private theorem physicalResidual_balanced (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (radius : ℝ) (x : nonlinearNeighborhoods G → ℝ)
    (hx : x ∈ physicalBlockingResiduals G Ω radius) :
    compatibility (nonlinearNeighborhoods G) (classWeight G color Ω) x = 0 := by
  obtain ⟨ρ, _, htr, _, hm, ha, hb⟩ := hx
  let y : V → ℝ := fun v => blockadeMean G ρ v - blockadeMean G (maximallyMixed G) v
  have hsmall : ∀ v, (G.neighborFinset v).card ≤ 1 → y v = 0 := by
    intro v hv
    apply sub_eq_zero.mpr
    exact small_vertex_recovery G ρ (maximallyMixed G)
      (by rw [htr, maximallyMixed_trace]) hm v hv
  have hlarge : ∀ v (hv : 2 ≤ (G.neighborFinset v).card),
      y v = x ⟨G.neighborFinset v, nonlinear_mem G v hv⟩ := by
    intro v hv
    rw [show y v = blockadeMean G ρ v - blockadeMean G (maximallyMixed G) v from rfl,
      blockade_readout, blockade_readout]
    exact hb ⟨G.neighborFinset v, nonlinear_mem G v hv⟩
  have hρ := signed_conservation G color proper Ω ρ
  have hcenter := signed_conservation G color proper Ω (maximallyMixed G)
  simp only [colorSign] at hρ hcenter
  have hleft : (∑ v, (if color v then (1 : ℝ) else -1) *
      (acceleration G Ω ρ v + 4 * Ω v ^ 2 * occupationMean G ρ v)) =
      ∑ v, (if color v then (1 : ℝ) else -1) *
        (acceleration G Ω (maximallyMixed G) v +
          4 * Ω v ^ 2 * occupationMean G (maximallyMixed G) v) := by
    simp_rw [hm, ha]
  have hbalance : (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * y v) = 0 := by
    dsimp [y]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith
  rw [value_class_decomposition G color Ω y x hsmall hlarge] at hbalance
  exact hbalance

/-- In every positive operator-norm neighborhood of the maximally mixed state,
the actual positive-density blocking fiber at fixed means and one drive has
exactly d−1 affine directions. The span is stated as an equality with the
explicit compatibility hyperplane, not merely as a count of unknowns. -/
theorem local_density_residual_dimension (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty) (radius : ℝ) (positive : 0 < radius) :
    Submodule.span ℝ (physicalBlockingResiduals G Ω radius) =
      LinearMap.ker (compatibility (nonlinearNeighborhoods G) (classWeight G color Ω)) ∧
    Module.finrank ℝ (Submodule.span ℝ (physicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 ∧
    Module.finrank ℝ (affineSpan ℝ (physicalBlockingResiduals G Ω radius)).direction =
      (nonlinearNeighborhoods G).card - 1 := by
  have hgraph := graph_residual_dimension_and_realization G color proper Ω nonzero nonempty
  have heq : Submodule.span ℝ (physicalBlockingResiduals G Ω radius) =
      LinearMap.ker (compatibility (nonlinearNeighborhoods G) (classWeight G color Ω)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro x hx
      exact physicalResidual_balanced G color proper Ω radius x hx
    · intro x hx
      obtain ⟨δ, _, _, _, hb, hphysical⟩ := hgraph.2 x hx
      obtain ⟨R, _, _, _, _, hRb, η, hη, hpath⟩ := hphysical connected
      let B := CStarMatrix.ofMatrix R
      let t : ℝ := min (η / 2) (radius / (2 * (‖B‖ + 1)))
      have ht : 0 < t := lt_min (by linarith) (div_pos positive (by positivity))
      have htη : |t| < η := by
        rw [abs_of_pos ht]
        have := min_le_left (η / 2) (radius / (2 * (‖B‖ + 1)))
        linarith
      have htnorm : |t| * ‖B‖ < radius := by
        rw [abs_of_pos ht]
        have htbound := min_le_right (η / 2) (radius / (2 * (‖B‖ + 1)))
        have hden : 0 < 2 * (‖B‖ + 1) := by positivity
        have hmul := (le_div_iff₀ hden).mp htbound
        have hnorm := norm_nonneg B
        nlinarith
      obtain ⟨hpos, htr, hm, ha, hbp⟩ := hpath t htη
      have hmember : t • x ∈ physicalBlockingResiduals G Ω radius := by
        refine ⟨maximallyMixed G + t • R, hpos.posSemidef, htr, ?_, hm, ha, ?_⟩
        · have hd : maximallyMixed G + t • R - maximallyMixed G = t • R := by abel
          rw [hd]
          change ‖(t : ℂ) • B‖ < radius
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact htnorm
        · intro N
          obtain ⟨v, hv, hN⟩ := Finset.mem_image.mp N.property
          have hvlarge : 2 ≤ (G.neighborFinset v).card := (Finset.mem_filter.mp hv).2
          have hNb : blockingReadout G N.val (maximallyMixed G + t • R) -
              blockingReadout G N.val (maximallyMixed G) = t * blockMoment G δ v := by
            rw [← hN, ← blockade_readout, ← blockade_readout, hbp]
            ring
          rw [hNb, block_eq, hN, hb]
          rfl
      have hspan : t • x ∈ Submodule.span ℝ (physicalBlockingResiduals G Ω radius) :=
        Submodule.subset_span hmember
      have hscaled := (Submodule.span ℝ (physicalBlockingResiduals G Ω radius)).smul_mem t⁻¹ hspan
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul] using hscaled
  have hdim : Module.finrank ℝ (Submodule.span ℝ (physicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 := by
    rw [heq]
    rw [residual_eq_ker G (nonlinearNeighborhoods G)
      (family_independent G color proper) (family_large G)] at hgraph
    exact hgraph.1
  have hzero : (0 : nonlinearNeighborhoods G → ℝ) ∈ physicalBlockingResiduals G Ω radius := by
    letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨η, hη, hsmall⟩ := small_centered_density_perturbations
      (0 : Matrix (Configuration G) (Configuration G) ℂ) (by simp [Matrix.IsHermitian]) (by simp)
    have hp := (hsmall 0 (by simpa using hη)).1
    refine ⟨maximallyMixed G, ?_, maximallyMixed_trace G, ?_, ?_, ?_, ?_⟩
    · have hpd : (maximallyMixed G).PosDef := by simpa [maximallyMixed] using hp
      exact hpd.posSemidef
    · simpa using positive
    · intro v; rfl
    · intro v; rfl
    · intro N; simp
  have haff : (affineSpan ℝ (physicalBlockingResiduals G Ω radius)).direction =
      Submodule.span ℝ (physicalBlockingResiduals G Ω radius) := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hzero]
    simp only [vsub_eq_sub, sub_zero, Set.image_id']
  exact ⟨heq, hdim, by rw [haff]; exact hdim⟩

/-- Expand distinct nonlinear-neighborhood coordinates to the complete vertex
blocking vector. The remaining entries vanish at fixed trace and means. -/
def classExpansion (G : SimpleGraph V) : (nonlinearNeighborhoods G → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun x v := if hv : 2 ≤ (G.neighborFinset v).card then
    x ⟨G.neighborFinset v, nonlinear_mem G v hv⟩ else 0
  map_add' := by
    intro a b
    ext v
    by_cases hv : 2 ≤ (G.neighborFinset v).card
    · simp only [dif_pos hv, Pi.add_apply]
    · simp only [dif_neg hv, Pi.add_apply, add_zero]
  map_smul' := by
    intro r x
    ext v
    by_cases hv : 2 ≤ (G.neighborFinset v).card
    · simp only [dif_pos hv, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg hv, Pi.smul_apply, RingHom.id_apply, smul_zero]

private theorem classExpansion_injective (G : SimpleGraph V) :
    Function.Injective (classExpansion G) := by
  intro x y hxy
  ext N
  obtain ⟨v, hv, hN⟩ := Finset.mem_image.mp N.property
  have hvlarge : 2 ≤ (G.neighborFinset v).card := (Finset.mem_filter.mp hv).2
  have hindex : (⟨G.neighborFinset v, nonlinear_mem G v hvlarge⟩ : nonlinearNeighborhoods G) = N :=
    Subtype.ext hN
  have hvxy := congrFun hxy v
  change (if h : 2 ≤ (G.neighborFinset v).card then
    x ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0) =
    if h : 2 ≤ (G.neighborFinset v).card then
      y ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0 at hvxy
  simpa only [dif_pos hvlarge, hindex] using hvxy

/-- The complete vertex-indexed Born blocking residual of actual density states. -/
def fullPhysicalBlockingResiduals (G : SimpleGraph V) (Ω : V → ℝ) (radius : ℝ) : Set (V → ℝ) :=
  {y | ∃ ρ : Matrix (Configuration G) (Configuration G) ℂ,
    ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
    ‖CStarMatrix.ofMatrix (ρ - maximallyMixed G)‖ < radius ∧
    (∀ v, occupationMean G ρ v = occupationMean G (maximallyMixed G) v) ∧
    (∀ v, acceleration G Ω ρ v = acceleration G Ω (maximallyMixed G) v) ∧
    ∀ v, blockadeMean G ρ v - blockadeMean G (maximallyMixed G) v = y v}

/-- The full vertex b-vector has exactly the same physical residual as the
injective expansion of the distinct nonlinear-neighborhood coordinates. Its
local affine dimension is therefore exactly d−1 in every positive-radius ball. -/
theorem full_blocking_residual_dimension (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty) (radius : ℝ) (positive : 0 < radius) :
    fullPhysicalBlockingResiduals G Ω radius =
      classExpansion G '' physicalBlockingResiduals G Ω radius ∧
    Function.Injective (classExpansion G) ∧
    Module.finrank ℝ (Submodule.span ℝ (fullPhysicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 ∧
    Module.finrank ℝ (affineSpan ℝ (fullPhysicalBlockingResiduals G Ω radius)).direction =
      (nonlinearNeighborhoods G).card - 1 := by
  have himage : fullPhysicalBlockingResiduals G Ω radius =
      classExpansion G '' physicalBlockingResiduals G Ω radius := by
    ext y
    constructor
    · rintro ⟨ρ, hp, ht, hr, hm, ha, hb⟩
      let x : nonlinearNeighborhoods G → ℝ := fun N =>
        blockingReadout G N.val ρ - blockingReadout G N.val (maximallyMixed G)
      refine ⟨x, ⟨ρ, hp, ht, hr, hm, ha, fun N => rfl⟩, ?_⟩
      ext v
      by_cases hv : 2 ≤ (G.neighborFinset v).card
      · change (if h : 2 ≤ (G.neighborFinset v).card then
          x ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0) = y v
        rw [dif_pos hv]
        change blockingReadout G (G.neighborFinset v) ρ -
          blockingReadout G (G.neighborFinset v) (maximallyMixed G) = y v
        rw [← blockade_readout, ← blockade_readout]
        exact hb v
      · have hz : blockadeMean G ρ v = blockadeMean G (maximallyMixed G) v :=
          small_vertex_recovery G ρ (maximallyMixed G)
            (by rw [ht, maximallyMixed_trace]) hm v (by omega)
        have hy : y v = 0 := by rw [← hb v, hz, sub_self]
        change (if h : 2 ≤ (G.neighborFinset v).card then
          x ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0) = y v
        rw [dif_neg hv, hy]
    · rintro ⟨x, ⟨ρ, hp, ht, hr, hm, ha, hb⟩, rfl⟩
      refine ⟨ρ, hp, ht, hr, hm, ha, ?_⟩
      intro v
      by_cases hv : 2 ≤ (G.neighborFinset v).card
      · change blockadeMean G ρ v - blockadeMean G (maximallyMixed G) v =
          if h : 2 ≤ (G.neighborFinset v).card then
            x ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0
        rw [dif_pos hv, blockade_readout, blockade_readout]
        exact hb ⟨G.neighborFinset v, nonlinear_mem G v hv⟩
      · have hz : blockadeMean G ρ v = blockadeMean G (maximallyMixed G) v :=
          small_vertex_recovery G ρ (maximallyMixed G)
            (by rw [ht, maximallyMixed_trace]) hm v (by omega)
        change blockadeMean G ρ v - blockadeMean G (maximallyMixed G) v =
          if h : 2 ≤ (G.neighborFinset v).card then
            x ⟨G.neighborFinset v, nonlinear_mem G v h⟩ else 0
        rw [dif_neg hv, hz, sub_self]
  have hinj := classExpansion_injective G
  have hdim := (local_density_residual_dimension G connected color proper Ω nonzero
    nonempty radius positive).2.1
  have hfull : Module.finrank ℝ
      (Submodule.span ℝ (fullPhysicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 := by
    rw [himage, Submodule.span_image]
    rw [← hdim]
    exact (Submodule.equivMapOfInjective (classExpansion G) hinj _).finrank_eq.symm
  have hzero : (0 : V → ℝ) ∈ fullPhysicalBlockingResiduals G Ω radius := by
    letI : Nonempty (Configuration G) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨η, hη, hsmall⟩ := small_centered_density_perturbations
      (0 : Matrix (Configuration G) (Configuration G) ℂ) (by simp [Matrix.IsHermitian]) (by simp)
    have hp := (hsmall 0 (by simpa using hη)).1
    refine ⟨maximallyMixed G, ?_, maximallyMixed_trace G, ?_, ?_, ?_, ?_⟩
    · have hpd : (maximallyMixed G).PosDef := by simpa [maximallyMixed] using hp
      exact hpd.posSemidef
    · simpa using positive
    · intro v; rfl
    · intro v; rfl
    · intro v; simp
  have haff : (affineSpan ℝ (fullPhysicalBlockingResiduals G Ω radius)).direction =
      Submodule.span ℝ (fullPhysicalBlockingResiduals G Ω radius) := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hzero]
    simp only [vsub_eq_sub, sub_zero, Set.image_id']
  exact ⟨himage, hinj, hfull, by rw [haff]; exact hfull⟩

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension.graph_residual_dimension_and_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_residual_dimension_and_realization

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension.local_density_residual_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms local_density_residual_dimension

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension.full_blocking_residual_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms full_blocking_residual_dimension

end D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension
