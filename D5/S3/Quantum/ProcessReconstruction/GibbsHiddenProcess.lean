/- GID: D5/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/GibbsHiddenProcess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive Gibbs semigroups hide their difference from every proper output. -/

import D5.S3.Quantum.ProcessReconstruction.HiddenProcessSemigroup
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! Two explicit finite-register semigroups with a common faithful Gibbs state.
Their every-time proper output channels agree on the full input algebra, although
their global diamond distance is positive at each positive finite time. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra NNReal
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance (act traceNorm)
open UnitaryReconstruction.RankTwoHiddenProcess
open UnitaryReconstruction.ParityFamily (Bits split)
open Filter Topology

namespace UnitaryReconstruction.GibbsHiddenProcess

universe u

variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem coefficient_cross (u v : a) (huv : u ≠ v) (flip : Bool) :
    coefficient u v flip u v = (if flip then -1 else 1) ∧
    coefficient u v flip v u = (if flip then -1 else 1) := by
  unfold coefficient act
  let X : Matrix a a ℂ := of fun _ _ => 1
  change (hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) u v = _ ∧
    (hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) v u = _
  rw [hiddenChannel_entry, hiddenChannel_entry]
  cases flip <;> simp [inBlock, phase, huv, X]

/-- The scalar multiplying the checked static channel difference. -/
def differenceScale (γ t : ℝ) : ℝ := decay γ t * (1 - Real.exp (-2 * t)) / 2

private theorem differenceScale_nonneg (γ t : ℝ≥0) : 0 ≤ differenceScale γ t := by
  have he : Real.exp (-2 * (t : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) t.2)
  unfold differenceScale
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr he)) (by norm_num)

theorem flow_difference (τ : DensityState a) (γ : ℝ≥0) (u v : a) (huv : u ≠ v)
    (t : ℝ≥0) (X : Matrix a a ℂ) :
    act (flow τ γ u v false t) X - act (flow τ γ u v true t) X =
      (differenceScale γ t : ℂ) •
        (act (hiddenChannel u v false) X - act (hiddenChannel u v true) X) := by
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [flow_entry, flow_entry, hidden_entry, hidden_entry]
  by_cases hxy : x = u ∧ y = v
  · rcases hxy with ⟨hx, hy⟩
    subst x y
    rw [(coefficient_cross u v huv false).1, (coefficient_cross u v huv true).1]
    simp [rate, (coefficient_cross u v huv false).1, (coefficient_cross u v huv true).1,
      differenceScale, mul_comm (t : ℝ)]
    ring
  · by_cases hyx : x = v ∧ y = u
    · rcases hyx with ⟨hx, hy⟩
      subst x y
      rw [(coefficient_cross u v huv false).2, (coefficient_cross u v huv true).2]
      simp [rate, (coefficient_cross u v huv false).2, (coefficient_cross u v huv true).2,
        differenceScale, mul_comm (t : ℝ)]
      ring
    · have hc : coefficient u v false x y = coefficient u v true x y :=
        hiddenChannel_entry_eq u v _ x y hxy hyx
      simp [rate, hc]

open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)

private theorem flow_referenceError {r : Type*} [Fintype r] [DecidableEq r]
    (τ : DensityState a) (γ : ℝ≥0) (u v : a) (huv : u ≠ v) (t : ℝ≥0)
    (ρ : DensityState (r × a)) :
    referenceError (flow τ γ u v false t) (flow τ γ u v true t) ρ =
      differenceScale γ t *
        referenceError (hiddenChannel u v false) (hiddenChannel u v true) ρ := by
  let X := CStarMatrix.ofMatrix.symm ρ.1
  change traceNorm (referenceMatrix (flow τ γ u v false t) X -
      referenceMatrix (flow τ γ u v true t) X) =
    differenceScale γ t * traceNorm (referenceMatrix (hiddenChannel u v false) X -
      referenceMatrix (hiddenChannel u v true) X)
  have h :
      referenceMatrix (flow τ γ u v false t) X - referenceMatrix (flow τ γ u v true t) X =
      (differenceScale γ t : ℂ) •
        (referenceMatrix (hiddenChannel u v false) X -
          referenceMatrix (hiddenChannel u v true) X) := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, referenceMatrix_apply]
    exact congrArg (fun M : Matrix a a ℂ => M x y)
      (flow_difference τ γ u v huv t (of fun x y => X (i, x) (j, y)))
  rw [h, traceNorm_smul_nonneg _ _ (differenceScale_nonneg γ t)]

/-- Exact unhalved diamond distance with arbitrary finite reference systems. -/
theorem flow_diamond (τ : DensityState a) (γ : ℝ≥0) (u v : a) (huv : u ≠ v) (t : ℝ≥0) :
    diamondDistance (flow τ γ u v false t) (flow τ γ u v true t) =
      Real.exp (-(γ : ℝ) * t) * (1 - Real.exp (-2 * t)) := by
  let C := flow τ γ u v false t
  let D := flow τ γ u v true t
  let c := differenceScale γ t
  have hc : 0 ≤ c := differenceScale_nonneg γ t
  have htwo : c * 2 = Real.exp (-(γ : ℝ) * t) * (1 - Real.exp (-2 * t)) := by
    dsimp [c, differenceScale, decay]
    ring
  rw [← htwo]
  change diamondDistance C D = c * 2
  apply le_antisymm
  · refine diamondDistance_le C D (by positivity) fun n ρ => ?_
    rw [flow_referenceError τ γ u v huv t ρ]
    exact mul_le_mul_of_nonneg_left (referenceError_le_two _ _ ρ) hc
  · rcases hc.eq_or_lt with he | hp
    · simpa [← he] using diamondDistance_nonneg' C D
    · have hbound : 2 ≤ diamondDistance C D / c := by
        rw [← hiddenChannel_maximal_diamond u v huv]
        refine diamondDistance_le _ _ (div_nonneg (diamondDistance_nonneg' C D) hc) fun n ρ => ?_
        apply (le_div_iff₀ hp).mpr
        rw [mul_comm, ← flow_referenceError τ γ u v huv t ρ]
        exact referenceError_le_diamond C D ρ
      simpa [mul_comm] using (le_div_iff₀ hp).mp hbound

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The two flows on the bit register, with the same density and reset rate. -/
def registerFlow (τ : DensityState (Bits ι)) (γ : ℝ≥0) (flip : Bool) (t : ℝ≥0) :
    QuantumChannel (Bits ι) (Bits ι) :=
  flow τ γ zeroWord oneWord flip t

omit [Fintype ι] [DecidableEq ι] in
private theorem extreme_words_ne [Nontrivial ι] : (zeroWord : Bits ι) ≠ oneWord := by
  intro h
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact Bool.false_ne_true (congrFun h i)

theorem register_diamond [Nontrivial ι] (τ : DensityState (Bits ι)) (γ t : ℝ≥0) :
    diamondDistance (registerFlow τ γ false t) (registerFlow τ γ true t) =
      Real.exp (-(γ : ℝ) * t) * (1 - Real.exp (-2 * t)) :=
  flow_diamond τ γ zeroWord oneWord extreme_words_ne t

/-- Every proper output agrees as a channel on the entire input algebra. -/
theorem register_proper_output_eq [Nontrivial ι] (τ : DensityState (Bits ι)) (γ t : ℝ≥0)
    (s : Finset ι) (hs : s ≠ Finset.univ) :
    (discard (split s)).comp (registerFlow τ γ false t) =
      (discard (split s)).comp (registerFlow τ γ true t) := by
  apply channel_ext
  intro X
  simp only [QuantumChannel.comp_apply]
  let L := (discard (split s)).toCompletelyPositiveMap.toLinearMap
  apply sub_eq_zero.mp
  change L ((registerFlow τ γ false t).toCompletelyPositiveMap X) -
    L ((registerFlow τ γ true t).toCompletelyPositiveMap X) = 0
  rw [← map_sub]
  have h := congrArg CStarMatrix.ofMatrix
    (flow_difference τ γ zeroWord oneWord extreme_words_ne t (CStarMatrix.ofMatrix.symm X))
  have h' :
      (registerFlow τ γ false t).toCompletelyPositiveMap X -
        (registerFlow τ γ true t).toCompletelyPositiveMap X =
      (differenceScale γ t : ℂ) •
        ((channel false).toCompletelyPositiveMap X - (channel true).toCompletelyPositiveMap X) := h
  rw [h', map_smul, map_sub]
  have hstatic : L ((channel false).toCompletelyPositiveMap X) =
      L ((channel true).toCompletelyPositiveMap X) :=
    congrArg (fun C : QuantumChannel (Bits ι) (ParityFamily.Kept s) =>
      C.toCompletelyPositiveMap X) (proper_output_eq s hs)
  simp [hstatic]

section Gibbs

open D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open scoped Matrix.Norms.L2Operator

variable [Nonempty a]

/-- Any real diagonal energy function, including degeneracies, is allowed. -/
def logBoltzmann (β : ℝ) (E : a → ℝ) : CStarMatrix a a ℂ :=
  CStarMatrix.ofMatrix (diagonal fun x => ((-β * E x : ℝ) : ℂ))

omit [Fintype a] [Nonempty a] in
theorem logBoltzmann_selfAdjoint (β : ℝ) (E : a → ℝ) :
    IsSelfAdjoint (logBoltzmann β E) := by
  change star (logBoltzmann β E) = logBoltzmann β E
  apply CStarMatrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [logBoltzmann, CStarMatrix.star_apply, Complex.conj_ofReal]
  · simp [logBoltzmann, CStarMatrix.star_apply, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (Ne.symm h)]

/-- The repository Gibbs density for the Hamiltonian diag(E) at inverse temperature β. -/
def gibbs (β : ℝ) (E : a → ℝ) : DensityState a :=
  gibbsState (logBoltzmann β E) (logBoltzmann_selfAdjoint β E)

omit [Nonempty a] in
private theorem boltzmann_exp (β : ℝ) (E : a → ℝ) :
    CStarMatrix.ofMatrix.symm (NormedSpace.exp (logBoltzmann β E)) =
      diagonal (fun i => (Real.exp (-β * E i) : ℂ)) := by
  let f := CStarMatrix.ofMatrixStarAlgEquiv (n := a) (A := ℂ)
  let : NormedAlgebra ℚ (Matrix a a ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have h := NormedSpace.map_exp f
    f.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
    (diagonal fun i => ((-β * E i : ℝ) : ℂ))
  rw [Matrix.exp_diagonal] at h
  apply f.injective
  change NormedSpace.exp (f (diagonal fun i => ((-β * E i : ℝ) : ℂ))) =
    f (diagonal fun i => (Real.exp (-β * E i) : ℂ))
  rw [← h]
  apply congrArg (fun w : a → ℂ => f (diagonal w))
  funext i
  rw [Pi.coe_exp]
  change NormedSpace.exp (((-β * E i : ℝ) : ℂ)) = _
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

/-- The normalized finite Boltzmann weights, in the computational basis. -/
theorem gibbs_matrix (β : ℝ) (E : a → ℝ) :
    CStarMatrix.ofMatrix.symm (gibbs β E).1 =
      diagonal fun i => ((Real.exp (-β * E i) / ∑ j, Real.exp (-β * E j) : ℝ) : ℂ) := by
  have hpart : partitionFunction (logBoltzmann β E) = ∑ j, Real.exp (-β * E j) := by
    unfold partitionFunction
    rw [boltzmann_exp, trace_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re]
  change (partitionFunction (logBoltzmann β E))⁻¹ •
    CStarMatrix.ofMatrix.symm (NormedSpace.exp (logBoltzmann β E)) = _
  rw [hpart, boltzmann_exp]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, Complex.real_smul, div_eq_mul_inv, mul_comm]
  · simp [Matrix.smul_apply, diagonal_apply_ne _ hij]

theorem gibbs_diagonal (β : ℝ) (E : a → ℝ) : IsDiagonal (gibbs β E) := by
  intro x y hxy
  change CStarMatrix.ofMatrix.symm (gibbs β E).1 x y = 0
  rw [gibbs_matrix, diagonal_apply_ne _ hxy]

theorem gibbs_faithful (β : ℝ) (E : a → ℝ) : (CStarMatrix.ofMatrix.symm (gibbs β E).1).PosDef :=
  gibbs_state_posDef _ _

end Gibbs

/-- Every proper output trajectory agrees at all times. The global diamond distance
has an exact formula and is strictly positive at each positive time. -/
theorem gibbs_hidden_process [Nontrivial ι] (β : ℝ) (_hβ : 0 < β) (E : Bits ι → ℝ)
    (γ : ℝ≥0) (_hγ : 0 < γ) (t : ℝ≥0) :
    let τ := gibbs β E
    let C := registerFlow τ γ false t
    let D := registerFlow τ γ true t
    (∀ s : Finset ι, s ≠ Finset.univ →
      (discard (split s)).comp C = (discard (split s)).comp D) ∧
      diamondDistance C D = Real.exp (-(γ : ℝ) * t) * (1 - Real.exp (-2 * t)) ∧
      (0 < t → 0 < diamondDistance C D) := by
  dsimp only
  refine ⟨fun s hs => register_proper_output_eq _ γ t s hs, register_diamond _ γ t, ?_⟩
  intro ht
  rw [register_diamond]
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by norm_num) ht)))

/-- The two finite register dynamics share the faithful diagonal Gibbs equilibrium. -/
theorem gibbs_register_dynamics (β : ℝ) (_hβ : 0 < β) (E : Bits ι → ℝ)
    (γ : ℝ≥0) (hγ : 0 < γ) :
    let τ := gibbs β E
    let S := registerFlow τ γ
    IsDiagonal τ ∧ (CStarMatrix.ofMatrix.symm τ.1).PosDef ∧
    ∀ flip,
      S flip 0 = identity ∧
      (∀ s t, S flip (s + t) = (S flip s).comp (S flip t)) ∧
      (∀ t, (S flip t).mapState τ = τ) ∧
      (∀ σ, (∀ t, (S flip t).mapState σ = σ) → σ = τ) ∧
      (∀ t, 0 < t → ∀ X : Matrix (Bits ι) (Bits ι) ℂ,
        X.PosSemidef → X ≠ 0 → (act (S flip t) X).PosDef) ∧
      (∀ X : Matrix (Bits ι) (Bits ι) ℂ,
        Tendsto (fun t => act (S flip t) X) atTop
          (𝓝 (trace X • CStarMatrix.ofMatrix.symm τ.1))) ∧
      (∀ t A B, gns τ A (heisenberg τ γ zeroWord oneWord flip t B) =
        gns τ (heisenberg τ γ zeroWord oneWord flip t A) B) := by
  dsimp only
  refine ⟨gibbs_diagonal β E, gibbs_faithful β E, ?_⟩
  intro flip
  exact ⟨flow_zero _ γ zeroWord oneWord flip,
    flow_add _ (gibbs_diagonal β E) γ zeroWord oneWord flip,
    flow_stationary _ (gibbs_diagonal β E) γ zeroWord oneWord flip,
    fun σ hσ => flow_unique_stationary _ γ hγ zeroWord oneWord flip σ hσ,
    fun t ht => flow_positivity_improving _ (gibbs_faithful β E) γ hγ
      zeroWord oneWord flip t ht,
    flow_tendsto_reset _ γ hγ zeroWord oneWord flip,
    fun t => heisenberg_gns_symmetric _ (gibbs_diagonal β E) γ zeroWord oneWord flip t⟩

end UnitaryReconstruction.GibbsHiddenProcess
