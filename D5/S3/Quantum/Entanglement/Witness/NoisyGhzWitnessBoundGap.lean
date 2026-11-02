/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim; result=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result; claim=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim
   digest: The optimized GHZ witness bound is strictly below the convex roof. -/

import D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
import D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness
import D5.S3.Zeros.CriticalPoints.RankOneTraceBound
import D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality
import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel

/-! The geometric GME measure and optimized witness bound of Xu et al.,
arXiv:2211.05563v1, Section "Estimating entanglement measures" and Appendix
"Multipartite states admitting Schmidt decomposition". -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

/-- The normalized equal superposition of the constant computational words. -/
def ghz (n d : ℕ) : Word (Fin d) n → ℂ := by
  classical
  exact fun x => if ∃ j : Fin d, ∀ i, x i = j then (Real.sqrt d : ℂ)⁻¹ else 0

/-- Unit pure states that factor across some nonempty proper bipartition. -/
def IsBiseparable {n d : ℕ} (φ : Word (Fin d) n → ℂ) : Prop :=
  IsUnitState φ ∧ ∃ a : Finset (Fin n), a.Nonempty ∧ aᶜ.Nonempty ∧
    ∃ u : (a → Fin d) → ℂ, ∃ v : (↥aᶜ → Fin d) → ℂ,
      ∀ x, φ x = u (fun i => x i) * v (fun i => x i)

/-- The source's sum over the orthogonal set `S` of distinct arrangements:
precisely the diagonal projector onto words with at most two distinct symbols. -/
def supportProjector (n d : ℕ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ := by
  classical
  exact diagonal fun x => if (Finset.univ.image x).card ≤ 2 then 1 else 0

/-- The optimized source witness `P/d − |GHZ⟩⟨GHZ|`. -/
def witnessOp (n d : ℕ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (1 / (d : ℝ)) • supportProjector n d - rankOneDensity (ghz n d)

/-- White noise mixed with the `n`-party `d`-dimensional GHZ state. -/
def noisyGhz (n d : ℕ) (p : ℝ) : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ :=
  (p / (d : ℝ) ^ n) • 1 + (1 - p) • rankOneDensity (ghz n d)

/-- Witness readout on the noisy GHZ state. -/
def witnessValue (n d : ℕ) (p : ℝ) : ℝ :=
  (trace (noisyGhz n d p * witnessOp n d)).re

/-- Pure-state geometric GME measure, optimized over all biseparable unit vectors. -/
def geometricMeasurePure {n d : ℕ} (ψ : Word (Fin d) n → ℂ) : ℝ :=
  1 - sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)}

/-- The convex roof over arbitrary finite normalized pure-state ensembles. -/
def geometricMeasure {n d : ℕ} (ρ : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) : ℝ :=
  sInf {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word (Fin d) n → ℂ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnitState (ψ i)) ∧
    ρ = ∑ i, p i • rankOneDensity (ψ i) ∧ t = ∑ i, p i * geometricMeasurePure (ψ i)}

/-- The source's two pure-state optimizations defining the convex conjugate. -/
def hatE (n d : ℕ) (r : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
    t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1}

/-- The optimized witness lower bound on geometric GME. -/
def epsilonO (n d : ℕ) (p : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ r : ℝ, t = r * witnessValue n d p - hatE n d r}

/-- The open equality question, for all party counts, dimensions, and noise probabilities. -/
def claim : Prop :=
  ∀ n d : ℕ, 3 ≤ n → 3 ≤ d → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    epsilonO n d p = geometricMeasure (noisyGhz n d p)

private def q : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ := 1 - supportProjector 3 3
private def b : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ :=
  -(2 / 3 : ℝ) • witnessOp 3 3 + (1 / 9 : ℝ) • q
private def dmat : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ :=
  (2 / 3 : ℝ) • rankOneDensity (ghz 3 3) +
    (4 / 3 : ℝ) • (supportProjector 3 3 - rankOneDensity (ghz 3 3)) + q
private def dinv : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ :=
  (3 / 2 : ℝ) • rankOneDensity (ghz 3 3) +
    (3 / 4 : ℝ) • (supportProjector 3 3 - rankOneDensity (ghz 3 3)) + q
private def testPsi : Word (Fin 3) 3 → ℂ := by
  classical
  exact fun x => (if x = (fun _ => 0) then 4 else
    if x = (fun _ => 1) ∨ x = (fun _ => 2) then 1 else 0) / (Real.sqrt 18 : ℂ)

private lemma sum_words {α : Type*} [AddCommMonoid α] (f : Word (Fin 3) 3 → α) :
    ∑ x, f x = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f ![i, j, k] := by
  simp only [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons,
    Fintype.sum_unique, Matrix.empty_eq, Matrix.Fin.cons_vecEmpty, Matrix.Fin.cons_vecCons]

private lemma cs {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by
  classical
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq u v

private lemma expectation_rank_one (φ ψ : Word (Fin 3) 3 → ℂ) :
    readout (rankOneDensity φ) ψ = Complex.normSq (star φ ⬝ᵥ ψ) := by
  have h := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.quadratic_projector ψ φ
  rw [star_dotProduct ψ φ, Complex.star_def, Complex.normSq_conj] at h
  exact congrArg Complex.re h

private lemma expectation_add (a c : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)
    (ψ : Word (Fin 3) 3 → ℂ) : readout (a + c) ψ = readout a ψ + readout c ψ := by
  exact RHLinalg.hermForm_add a c ψ

private lemma expectation_smul (r : ℝ) (a : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)
    (ψ : Word (Fin 3) 3 → ℂ) : readout (r • a) ψ = r * readout a ψ := by
  change (star ψ ⬝ᵥ ((r • a) *ᵥ ψ)).re = r * (star ψ ⬝ᵥ (a *ᵥ ψ)).re
  rw [← Complex.coe_smul r a]
  exact D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.quadratic_smul ψ r a

private lemma expectation_one (ψ : Word (Fin 3) 3 → ℂ) :
    readout 1 ψ = ∑ x, Complex.normSq (ψ x) := by
  simpa only [RHLinalg.hermForm, readout, RCLike.re_to_complex,
    Complex.normSq_eq_norm_sq] using
    RHLinalg.hermForm_one ψ

private lemma expectation_sub (a c : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ)
    (ψ : Word (Fin 3) 3 → ℂ) : readout (a - c) ψ = readout a ψ - readout c ψ := by
  exact RHLinalg.hermForm_sub a c ψ

private lemma support_expectation (ψ : Word (Fin 3) 3 → ℂ) :
    readout (supportProjector 3 3) ψ =
      ∑ x ∈ Finset.univ.filter (fun x : Word (Fin 3) 3 => (Finset.univ.image x).card ≤ 2),
        Complex.normSq (ψ x) := by
  classical
  rw [readout, supportProjector]
  have hdiag :
      (fun x : Word (Fin 3) 3 =>
        if (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) =
        (fun x : Word (Fin 3) 3 =>
          ((if (Finset.univ.image x).card ≤ 2 then (1 : ℝ) else 0) : ℂ)) := by
    funext x
    split_ifs <;> rfl
  rw [hdiag]
  have hquad :=
    D5.S3.Quantum.Divergence.CanonicalChannelDPI.diagonal_quadratic_form
      (d := fun x : Word (Fin 3) 3 =>
        if (Finset.univ.image x).card ≤ 2 then (1 : ℝ) else 0) ψ
  convert hquad using 1
  · congr 2
    funext x
    simp only [mulVec_diagonal]
    split_ifs <;> rfl
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [Complex.normSq_eq_norm_sq]

private lemma support_bounds (ψ : Word (Fin 3) 3 → ℂ) :
    0 ≤ readout (supportProjector 3 3) ψ ∧
      readout (supportProjector 3 3) ψ ≤ ∑ x, Complex.normSq (ψ x) := by
  classical
  rw [support_expectation]
  exact ⟨Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _),
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Complex.normSq_nonneg _)⟩

private lemma ghz_expectation (ψ : Word (Fin 3) 3 → ℂ) :
    3 * readout (rankOneDensity (ghz 3 3)) ψ =
      Complex.normSq (∑ i : Fin 3, ψ (fun _ => i)) := by
  classical
  let e : (Fin 3 × Fin 3 × Fin 3) ≃ Word (Fin 3) 3 :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun x => (x 0, x 1, x 2)
      left_inv := by rintro ⟨i, j, k⟩; rfl
      right_inv := by intro x; funext i; fin_cases i <;> rfl }
  have hghz : ghz 3 3 ∘ e = D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.ghz 3 := by
    funext p
    rcases p with ⟨i, j, k⟩
    rw [Function.comp_apply, ghz.eq_1]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.ghz,
        e, Function.comp_def, Fin.sum_univ_succ, Pi.single_apply, Fin.forall_fin_succ]
  have hoverlap : star (ghz 3 3) ⬝ᵥ ψ =
      star (D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.ghz 3) ⬝ᵥ (ψ ∘ e) := by
    rw [← hghz]
    exact (comp_equiv_dotProduct_comp_equiv (star (ghz 3 3)) ψ e).symm
  have hc (i : Fin 3) : e (i, i, i) = fun _ => i := by
    dsimp [e]
    simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const]
  rw [expectation_rank_one, hoverlap,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.ghz_overlap_normSq]
  simp only [Function.comp_apply, hc]
  norm_num [← mul_assoc]

private lemma join_support (a : Finset (Fin 3)) (i j : Fin 3) :
    (Finset.univ.image ((a.piecewise (fun _ => i) (fun _ => j)))).card ≤ 2 := by
  classical
  have h : Finset.univ.image ((a.piecewise (fun _ => i) (fun _ => j))) ⊆ {i, j} := by
    apply Finset.coe_subset.mp
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Finset.coe_insert, Finset.coe_singleton]
    change Set.range (fun k : Fin 3 => if k ∈ a then i else j) ⊆ ({i, j} : Set (Fin 3))
    simpa only [Set.range_const, Set.union_singleton, Set.pair_comm] using
      (Set.range_ite_subset (p := fun k : Fin 3 => k ∈ a)
        (f := fun _ => i) (g := fun _ => j))
  exact (Finset.card_le_card h).trans Finset.card_le_two

private lemma join_injective (a : Finset (Fin 3)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    Function.Injective (fun ij : Fin 3 × Fin 3 => (a.piecewise (fun _ => ij.1) (fun _ => ij.2))) := by
  classical
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hc
  intro x y h
  apply Prod.ext
  · simpa [hk] using congrFun h k
  · simpa [Finset.mem_compl.mp hl] using congrFun h l

private lemma trace_rank_one (ψ : Word (Fin 3) 3 → ℂ) :
    trace (rankOneDensity ψ) = ((∑ x, Complex.normSq (ψ x) : ℝ) : ℂ) := by
  simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm, Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.dot_star_self ψ

private lemma ghz_supported (x : Word (Fin 3) 3) :
    (if (Finset.univ.image x).card ≤ 2 then (1 : ℂ) else 0) * ghz 3 3 x = ghz 3 3 x := by
  classical
  by_cases h : ∃ j : Fin 3, ∀ i, x i = j
  · obtain ⟨j, hj⟩ := h
    have he : x = fun _ => j := funext hj
    subst x
    simp [Finset.image_const]
  · delta ghz
    simp [h]

private lemma finite_ranks : trace (supportProjector 3 3) = 21 ∧ trace q = 6 := by
  classical
  have hc : (Finset.univ.filter fun x : Word (Fin 3) 3 =>
      (Finset.univ.image x).card ≤ 2).card = 21 := by decide
  have hp : trace (supportProjector 3 3) = 21 := by
    simpa [supportProjector, trace_diagonal, Finset.sum_boole] using
      congrArg (fun k : ℕ => (k : ℂ)) hc
  refine ⟨hp, ?_⟩
  rw [q]
  norm_num [ trace_sub, hp, trace_one, Word]
private lemma ghz_unit : IsUnitState (ghz 3 3) := by
  classical
  delta ghz
  simp only [Fin.exists_fin_succ]
  norm_num [IsUnitState, sum_words, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Complex.normSq_inv, Complex.normSq_ofReal, Real.sq_sqrt,
    Real.mul_self_sqrt]
private lemma projector_data :
    supportProjector 3 3 * supportProjector 3 3 = supportProjector 3 3 ∧
    supportProjector 3 3 * rankOneDensity (ghz 3 3) = rankOneDensity (ghz 3 3) ∧
    rankOneDensity (ghz 3 3) * supportProjector 3 3 = rankOneDensity (ghz 3 3) ∧
    rankOneDensity (ghz 3 3) * rankOneDensity (ghz 3 3) = rankOneDensity (ghz 3 3) := by
  classical
  have hn : star (ghz 3 3) ⬝ᵥ ghz 3 3 = 1 := by
    exact (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff _).mpr ghz_unit
  refine ⟨?_, ?_, ?_,
    (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake (ghz 3 3) hn 1).1⟩
  · simp only [supportProjector, diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> norm_num
  · ext x y
    simp only [supportProjector, diagonal_mul, rankOneDensity, vecMulVec_apply, Pi.star_apply]
    rw [← mul_assoc, ghz_supported]
  · ext x y
    simp only [supportProjector, mul_diagonal, rankOneDensity, vecMulVec_apply, Pi.star_apply]
    by_cases h : (Finset.univ.image y).card ≤ 2
    · simp [h]
    · have hz : ghz 3 3 y = 0 := by simpa [h] using (ghz_supported y).symm
      simp [h, hz]

private lemma orthogonal_positive :
    (supportProjector 3 3 - rankOneDensity (ghz 3 3)).PosSemidef ∧ q.PosSemidef := by
  classical
  obtain ⟨hpp, hpg, hgp, hgg⟩ := projector_data
  have hp : (supportProjector 3 3).IsHermitian := by
    apply isHermitian_diagonal_of_self_adjoint
    funext x
    simp only [Pi.star_apply]
    split_ifs <;> simp
  have hg : (rankOneDensity (ghz 3 3)).IsHermitian :=
    (posSemidef_vecMulVec_self_star (ghz 3 3)).isHermitian
  have hP : IsStarProjection (supportProjector 3 3) := ⟨hpp, hp.isSelfAdjoint⟩
  have hG : IsStarProjection (rankOneDensity (ghz 3 3)) := ⟨hgg, hg.isSelfAdjoint⟩
  exact ⟨(hG.sub_of_mul_eq_left hP hgp).nonneg.posSemidef,
    hP.one_sub_nonneg.posSemidef⟩

private lemma witness_value : witnessValue 3 3 (3 / 8) = -(1 / 3) := by
  classical
  obtain ⟨_, _, hgp, hgg⟩ := projector_data
  have ht : trace (rankOneDensity (ghz 3 3)) = 1 := by rw [trace_rank_one, ghz_unit]; rfl
  rw [witnessValue, noisyGhz]
  norm_num [witnessOp, add_mul, mul_sub, sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_add, trace_sub, trace_smul,
    hgp, hgg, ht, finite_ranks.1, Complex.real_smul]
private lemma basis_unit (x : Word (Fin 3) 3) : IsUnitState (Pi.single x 1) := by
  classical
  rw [IsUnitState]
  simp [Pi.single_apply]
private lemma zero_biseparable : IsBiseparable (Pi.single (fun _ : Fin 3 => (0 : Fin 3)) (1 : ℂ)) := by
  classical
  refine ⟨basis_unit _, {0}, by simp, by decide,
    fun u => if ∀ i, u i = 0 then 1 else 0,
    fun v => if ∀ i, v i = 0 then 1 else 0, ?_⟩
  intro x
  have he : x = (fun _ => 0) ↔
      (∀ i : ↥({0} : Finset (Fin 3)), x i = 0) ∧
      (∀ i : ↥({0} : Finset (Fin 3))ᶜ, x i = 0) := by
    rw [← Set.eqOn_univ x (fun _ => 0),
      ← Set.union_compl_self (↑({0} : Finset (Fin 3)) : Set (Fin 3)), Set.eqOn_union]
    simp only [Set.EqOn, Finset.mem_coe, Subtype.forall,
      Finset.mem_compl, Set.mem_compl_iff]
  simp only [Pi.single_apply]
  by_cases h : ∀ i : ↥({0} : Finset (Fin 3)), x i = 0 <;>
    by_cases g : ∀ i : ↥({0} : Finset (Fin 3))ᶜ, x i = 0 <;>
      simp_all
private lemma test_unit : IsUnitState testPsi := by
  classical
  delta testPsi
  norm_num [IsUnitState, sum_words, Fin.sum_univ_succ, funext_iff,
    Fin.forall_fin_succ, Complex.normSq_div, Complex.normSq_ofReal, Real.sq_sqrt,
    Real.mul_self_sqrt]
private lemma test_expectation : readout (witnessOp 3 3) testPsi = -(1 / 3) := by
  classical
  have hp : readout (supportProjector 3 3) testPsi = 1 := by
    have he (i : Fin 3) : (![i, i, i] : Word (Fin 3) 3) = (fun _ => i) := by
      simp only [Matrix.vec_single_eq_const, Matrix.vecCons_const]
    delta testPsi
    norm_num [support_expectation, Finset.sum_filter, sum_words,
      Fin.sum_univ_succ, he, Finset.image_const, funext_iff, Fin.forall_fin_succ,
      Complex.normSq_div, Complex.normSq_ofReal, Real.sq_sqrt, Real.mul_self_sqrt]
  have hs : (∑ i : Fin 3, testPsi (fun _ => i)) = 6 / (Real.sqrt 18 : ℂ) := by
    delta testPsi
    norm_num [Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]
    ring
  have hg := ghz_expectation testPsi
  rw [hs] at hg
  norm_num [Complex.normSq_div, Complex.normSq_ofReal, Real.sq_sqrt, Real.mul_self_sqrt] at hg
  rw [witnessOp, expectation_sub, expectation_smul, hp]
  linarith
private lemma test_overlap : Complex.normSq (star (Pi.single (fun _ => 0) 1) ⬝ᵥ testPsi) = 8 / 9 := by
  classical
  delta testPsi
  norm_num [dotProduct, Pi.single_apply, Complex.normSq_div,
    Complex.normSq_ofReal, Real.sq_sqrt, Real.mul_self_sqrt]

private lemma witness_bounds (ψ : Word (Fin 3) 3 → ℂ) (hψ : IsUnitState ψ) :
    -1 ≤ readout (witnessOp 3 3) ψ ∧ readout (witnessOp 3 3) ψ ≤ 1 / 3 := by
  classical
  have hp := support_bounds ψ
  have hg := cs (ghz 3 3) ψ
  rw [ghz_unit, hψ, one_mul] at hg
  have hq := Complex.normSq_nonneg (star (ghz 3 3) ⬝ᵥ ψ)
  rw [witnessOp, expectation_sub, expectation_smul, expectation_rank_one]
  change (∑ x, Complex.normSq (ψ x)) = 1 at hψ
  constructor <;> linarith

private lemma hat_bdd (r : ℝ) : BddAbove {t : ℝ | ∃ ψ φ : Word (Fin 3) 3 → ℂ,
    IsUnitState ψ ∧ IsBiseparable φ ∧
      t = readout (r • witnessOp 3 3 + rankOneDensity φ) ψ - 1} := by
  classical
  refine ⟨|r|, ?_⟩
  rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
  rw [expectation_add, expectation_smul, expectation_rank_one]
  have hp := cs φ ψ
  rw [hφ.1, hψ, one_mul] at hp
  have hw := witness_bounds ψ hψ
  have hr : r * readout (witnessOp 3 3) ψ ≤ |r| := by
    by_cases h : 0 ≤ r
    · rw [abs_of_nonneg h]
      have ht := mul_le_mul_of_nonneg_left hw.2 h
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      have ht := mul_le_mul_of_nonpos_left hw.1 (le_of_lt (lt_of_not_ge h))
      linarith
  linarith

private lemma hat_lower (r : ℝ) : -r / 3 - 1 / 9 ≤ hatE 3 3 r := by
  classical
  have hm : -r / 3 - 1 / 9 ∈ {t : ℝ | ∃ ψ φ : Word (Fin 3) 3 → ℂ,
      IsUnitState ψ ∧ IsBiseparable φ ∧
        t = readout (r • witnessOp 3 3 + rankOneDensity φ) ψ - 1} := by
    refine ⟨testPsi, Pi.single (fun _ => 0) 1, test_unit, zero_biseparable, ?_⟩
    rw [expectation_add, expectation_smul, expectation_rank_one, test_expectation, test_overlap]
    ring
  exact le_csSup (hat_bdd r) hm
private lemma epsilon_upper : epsilonO 3 3 (3 / 8) ≤ 1 / 9 := by
  classical
  apply csSup_le
  · exact ⟨-hatE 3 3 0, 0, by simp⟩
  · rintro t ⟨r, rfl⟩
    rw [witness_value]
    linarith [hat_lower r]

/-- The nine words constant on each side of a cut all lie in the support of `P`.
Cauchy–Schwarz for the two factors bounds the three constant-word amplitudes. -/
private lemma biseparable_overlap (φ : Word (Fin 3) 3 → ℂ) (hφ : IsBiseparable φ) :
    3 * readout (rankOneDensity (ghz 3 3)) φ ≤ readout (supportProjector 3 3) φ := by
  classical
  obtain ⟨_, a, ha, hc, u, v, h⟩ := hφ
  have hj (i j : Fin 3) : φ ((a.piecewise (fun _ => i) (fun _ => j))) = u (fun _ => i) * v (fun _ => j) := by
    rw [h]
    congr 1
    · congr 1; funext k; simp [k.property]
    · congr 1; funext k; simp [Finset.mem_compl.mp k.property]
  have hd (i : Fin 3) : φ (fun _ => i) = u (fun _ => i) * v (fun _ => i) := h _
  rw [ghz_expectation, support_expectation]
  calc
    Complex.normSq (∑ i : Fin 3, φ (fun _ => i)) ≤
        (∑ i : Fin 3, Complex.normSq (u (fun _ => i))) *
          ∑ j : Fin 3, Complex.normSq (v (fun _ => j)) := by
      simpa [dotProduct, Complex.star_def, hd] using
        cs (star (fun i : Fin 3 => u (fun _ => i))) (fun j : Fin 3 => v (fun _ => j))
    _ = ∑ ij : Fin 3 × Fin 3, Complex.normSq (φ ((a.piecewise (fun _ => ij.1) (fun _ => ij.2)))) := by
      simp only [Fintype.sum_prod_type, hj, Complex.normSq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      classical
      have hs : (∑ ij : Fin 3 × Fin 3, Complex.normSq (φ ((a.piecewise (fun _ => ij.1) (fun _ => ij.2))))) =
          ∑ x ∈ Finset.univ.image (fun ij : Fin 3 × Fin 3 => (a.piecewise (fun _ => ij.1) (fun _ => ij.2))),
            Complex.normSq (φ x) :=
        (Finset.sum_image (f := fun x : Word (Fin 3) 3 => Complex.normSq (φ x))
          (s := Finset.univ) (g := fun ij : Fin 3 × Fin 3 => (a.piecewise (fun _ => ij.1) (fun _ => ij.2)))
          (fun x _ y _ hxy => join_injective a ha hc hxy)).symm
      rw [hs]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, join_support a ij.1 ij.2⟩
      · intro x _ _; exact Complex.normSq_nonneg _

private lemma inverse_bound (φ : Word (Fin 3) 3 → ℂ) (hφ : IsBiseparable φ) :
    readout dinv φ ≤ 1 := by
  classical
  have h := biseparable_overlap φ hφ
  have hu : readout 1 φ = 1 := by rw [expectation_one]; exact hφ.1
  simp only [dinv, q, expectation_add, expectation_sub, expectation_smul] at *
  linarith
private lemma d_positive : dmat.PosDef := by
  classical
  have he : dmat = (2 / 3 : ℝ) • (1 : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ) +
      (2 / 3 : ℝ) • (supportProjector 3 3 - rankOneDensity (ghz 3 3)) +
      (1 / 3 : ℝ) • q := by
    dsimp [dmat, q]
    module
  rw [he]
  exact ((Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 2 / 3)).add_posSemidef
    (orthogonal_positive.1.smul (by norm_num : (0 : ℝ) ≤ 2 / 3))).add_posSemidef
      (orthogonal_positive.2.smul (by norm_num : (0 : ℝ) ≤ 1 / 3))
private lemma d_inverse : dmat * dinv = 1 := by
  classical
  obtain ⟨hpp, hpg, hgp, hgg⟩ := projector_data
  rw [dmat, dinv, q]
  simp only [add_mul, mul_add, sub_mul, mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one, hpp, hpg, hgp, hgg]
  module

/-- Apply the positive-definite Cauchy–Schwarz inequality to `ψ` and `D⁻¹ φ`. -/
private lemma weighted_cs (φ ψ : Word (Fin 3) 3 → ℂ) :
    Complex.normSq (star φ ⬝ᵥ ψ) ≤ readout dinv φ * readout dmat ψ := by
  classical
  have hi : dinv.PosSemidef := by
    dsimp only [dinv]
    exact (((posSemidef_vecMulVec_self_star (ghz 3 3)).smul
      (by norm_num : (0 : ℝ) ≤ 3 / 2)).add
      (orthogonal_positive.1.smul (by norm_num : (0 : ℝ) ≤ 3 / 4))).add orthogonal_positive.2
  have hm : dmat *ᵥ (dinv *ᵥ φ) = φ := by
    rw [mulVec_mulVec, d_inverse, one_mulVec]
  have hr : star (dinv *ᵥ φ) ⬝ᵥ φ = star φ ⬝ᵥ dinv *ᵥ φ := by
    rw [star_mulVec, hi.isHermitian.eq, ← dotProduct_mulVec]
  have hc := D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.psd_cauchy_schwarz
    dmat d_positive.posSemidef ψ (dinv *ᵥ φ)
  rw [hm, hr] at hc
  rw [← Complex.normSq_eq_norm_sq,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.normSq_overlap_comm ψ φ] at hc
  simpa only [readout, mul_comm] using hc

private lemma pure_lower (ψ : Word (Fin 3) 3 → ℂ) (hψ : IsUnitState ψ) :
    readout b ψ - 1 / 9 ≤ geometricMeasurePure ψ := by
  classical
  have hd : 0 ≤ readout dmat ψ :=
    RHLinalg.hermForm_nonneg_of_posSemidef d_positive.posSemidef ψ
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ readout dmat ψ := by
    apply csSup_le
    · exact ⟨_, Pi.single (fun _ => 0) 1, zero_biseparable, rfl⟩
    · rintro t ⟨φ, hφ, rfl⟩
      exact (weighted_cs φ ψ).trans (mul_le_of_le_one_left hd (inverse_bound φ hφ))
  have hu : readout 1 ψ = 1 := by rw [expectation_one]; exact hψ
  have he : readout dmat ψ + readout b ψ = 10 / 9 := by
    simp only [dmat, b, q, witnessOp, expectation_add, expectation_sub, expectation_smul] at *
    linarith
  dsimp only [geometricMeasurePure]
  linarith

private lemma trace_b : (trace (noisyGhz 3 3 (3 / 8) * b)).re - 1 / 9 = 13 / 108 := by
  classical
  obtain ⟨_, _, hgp, _⟩ := projector_data
  have hq : rankOneDensity (ghz 3 3) * q = 0 := by simp [q, mul_sub, hgp]
  have ht : (trace (noisyGhz 3 3 (3 / 8) * q)).re = 1 / 12 := by
    norm_num [noisyGhz, add_mul, Matrix.smul_mul, hq, trace_smul, finite_ranks.2,
      Complex.real_smul]
  rw [b]
  simp only [mul_add, Matrix.mul_smul, trace_add, trace_smul,
    Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
  change -(2 / 3) * witnessValue 3 3 (3 / 8) +
    (1 / 9) * (trace (noisyGhz 3 3 (3 / 8) * q)).re - 1 / 9 = 13 / 108
  rw [witness_value, ht]
  norm_num

private lemma ensemble_nonempty :
    {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word (Fin 3) 3 → ℂ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnitState (ψ i)) ∧
      noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOneDensity (ψ i) ∧
      t = ∑ i, p i * geometricMeasurePure (ψ i)}.Nonempty := by
  classical
  let ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin 3) 3) :=
    ⟨CStarMatrix.ofMatrix (noisyGhz 3 3 (3 / 8)), by
      apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      dsimp only [noisyGhz]
      exact ((Matrix.PosSemidef.one.smul
        (by norm_num : (0 : ℝ) ≤ (3 / 8) / (3 : ℝ) ^ 3)).add
        ((posSemidef_vecMulVec_self_star (ghz 3 3)).smul
          (by norm_num : (0 : ℝ) ≤ 1 - 3 / 8))).nonneg, by
      change trace (noisyGhz 3 3 (3 / 8)) = 1
      rw [noisyGhz, trace_add, trace_smul, trace_smul, trace_one, trace_rank_one, ghz_unit]
      norm_num [Word, Complex.real_smul]⟩
  obtain ⟨k, p, ψ, hp, hs, hu, he⟩ :=
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.density_ensemble ρ
  refine ⟨_, k, p, ψ, hp, hs, ?_, ?_, rfl⟩
  · intro i
    exact (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff _).mp (hu i)
  · change noisyGhz 3 3 (3 / 8) = ∑ i, (algebraMap ℝ ℂ) (p i) • rankOneDensity (ψ i) at he
    simpa only [algebraMap_smul] using he

private lemma average_lower (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word (Fin 3) 3 → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i))
    (he : noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOneDensity (ψ i)) :
    13 / 108 ≤ ∑ i, p i * geometricMeasurePure (ψ i) := by
  classical
  have htrace : (trace (noisyGhz 3 3 (3 / 8) * b)).re =
      ∑ i, p i * readout b (ψ i) := by
    rw [trace_mul_comm, he]
    have ht := congrArg Complex.re
      (D5.S3.Zeros.CriticalPoints.RankOneTraceBound.trace_rank_one_sum
        (fun i => WithLp.toLp 2 (ψ i)) p (fun _ => 1) b)
    simpa only [mul_one, rankOneDensity, Complex.coe_smul,
      EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, Complex.re_sum, Complex.re_ofReal_mul, readout,
      dotProduct_comm] using ht
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pure_lower (ψ i) (hu i)) (hp i))
  have ht := trace_b
  rw [htrace] at ht
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs] at h
  linarith

private lemma roof_lower : 13 / 108 ≤ geometricMeasure (noisyGhz 3 3 (3 / 8)) := by
  classical
  apply le_csInf ensemble_nonempty
  rintro t ⟨k, p, ψ, hp, hs, hu, he, rfl⟩
  exact average_lower k p ψ hp hs hu he

/-- At three parties and three levels, noise `3/8` gives a strict gap. -/
theorem result : ¬ claim := by
  classical
  intro h
  have he := h 3 3 (by norm_num) (by norm_num) (3 / 8) (by norm_num) (by norm_num)
  have hu := epsilon_upper
  have hl := roof_lower
  rw [he] at hu
  linarith


end D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap
