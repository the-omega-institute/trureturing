/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim; result=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result; claim=D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.claim
   digest: The optimized GHZ witness bound is strictly below the convex roof. -/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

/-! The geometric GME measure and optimized witness bound of Xu et al.,
arXiv:2211.05563v1, Section "Estimating entanglement measures" and Appendix
"Multipartite states admitting Schmidt decomposition". -/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

/-- Computational words for `n` parties of local dimension `d`. -/
abbrev Word (n d : ℕ) := Fin n → Fin d

/-- Normalization of a pure-state amplitude vector. -/
def IsUnit {n d : ℕ} (ψ : Word n d → ℂ) : Prop := ∑ x, Complex.normSq (ψ x) = 1

/-- The normalized equal superposition of the constant computational words. -/
def ghz (n d : ℕ) : Word n d → ℂ := by
  classical
  exact fun x => if ∃ j : Fin d, ∀ i, x i = j then (Real.sqrt d : ℂ)⁻¹ else 0

/-- Unit pure states that factor across some nonempty proper bipartition. -/
def IsBiseparable {n d : ℕ} (φ : Word n d → ℂ) : Prop :=
  IsUnit φ ∧ ∃ a : Finset (Fin n), a.Nonempty ∧ aᶜ.Nonempty ∧
    ∃ u : (a → Fin d) → ℂ, ∃ v : (↥aᶜ → Fin d) → ℂ,
      ∀ x, φ x = u (fun i => x i) * v (fun i => x i)

/-- The source's sum over the orthogonal set `S` of distinct arrangements:
precisely the diagonal projector onto words with at most two distinct symbols. -/
def supportProjector (n d : ℕ) : Matrix (Word n d) (Word n d) ℂ := by
  classical
  exact diagonal fun x => if (Finset.univ.image x).card ≤ 2 then 1 else 0

/-- The optimized source witness `P/d − |GHZ⟩⟨GHZ|`. -/
def witnessOp (n d : ℕ) : Matrix (Word n d) (Word n d) ℂ :=
  (1 / (d : ℝ)) • supportProjector n d - rankOneDensity (ghz n d)

/-- White noise mixed with the `n`-party `d`-dimensional GHZ state. -/
def noisyGhz (n d : ℕ) (p : ℝ) : Matrix (Word n d) (Word n d) ℂ :=
  (p / (d : ℝ) ^ n) • 1 + (1 - p) • rankOneDensity (ghz n d)

/-- Real quadratic expectation of an operator. -/
def expectation {n d : ℕ} (a : Matrix (Word n d) (Word n d) ℂ)
    (ψ : Word n d → ℂ) : ℝ := (star ψ ⬝ᵥ a *ᵥ ψ).re

/-- Witness readout on the noisy GHZ state. -/
def witnessValue (n d : ℕ) (p : ℝ) : ℝ :=
  (trace (noisyGhz n d p * witnessOp n d)).re

/-- Pure-state geometric GME measure, optimized over all biseparable unit vectors. -/
def geometricMeasurePure {n d : ℕ} (ψ : Word n d → ℂ) : ℝ :=
  1 - sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)}

/-- The convex roof over arbitrary finite normalized pure-state ensembles. -/
def geometricMeasure {n d : ℕ} (ρ : Matrix (Word n d) (Word n d) ℂ) : ℝ :=
  sInf {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word n d → ℂ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnit (ψ i)) ∧
    ρ = ∑ i, p i • rankOneDensity (ψ i) ∧ t = ∑ i, p i * geometricMeasurePure (ψ i)}

/-- The source's two pure-state optimizations defining the convex conjugate. -/
def hatE (n d : ℕ) (r : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ ψ φ, IsUnit ψ ∧ IsBiseparable φ ∧
    t = expectation (r • witnessOp n d + rankOneDensity φ) ψ - 1}

/-- The optimized witness lower bound on geometric GME. -/
def epsilonO (n d : ℕ) (p : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ r : ℝ, t = r * witnessValue n d p - hatE n d r}

/-- The open equality question, for all party counts, dimensions, and noise probabilities. -/
def claim : Prop :=
  ∀ n d : ℕ, 3 ≤ n → 3 ≤ d → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    epsilonO n d p = geometricMeasure (noisyGhz n d p)

private def q : Matrix (Word 3 3) (Word 3 3) ℂ := 1 - supportProjector 3 3
private def b : Matrix (Word 3 3) (Word 3 3) ℂ :=
  -(2 / 3 : ℝ) • witnessOp 3 3 + (1 / 9 : ℝ) • q
private def dmat : Matrix (Word 3 3) (Word 3 3) ℂ :=
  (2 / 3 : ℝ) • rankOneDensity (ghz 3 3) +
    (4 / 3 : ℝ) • (supportProjector 3 3 - rankOneDensity (ghz 3 3)) + q
private def dinv : Matrix (Word 3 3) (Word 3 3) ℂ :=
  (3 / 2 : ℝ) • rankOneDensity (ghz 3 3) +
    (3 / 4 : ℝ) • (supportProjector 3 3 - rankOneDensity (ghz 3 3)) + q
private def testPsi : Word 3 3 → ℂ := by
  classical
  exact fun x => (if x = (fun _ => 0) then 4 else
    if x = (fun _ => 1) ∨ x = (fun _ => 2) then 1 else 0) / (Real.sqrt 18 : ℂ)
private def basis (x : Word 3 3) : Word 3 3 → ℂ := Pi.single x 1

private def wordEquiv : Word 3 3 ≃ Fin 3 × Fin 3 × Fin 3 where
  toFun x := (x 0, x 1, x 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by rcases x with ⟨i, j, k⟩; rfl

private lemma sum_words {α : Type*} [AddCommMonoid α] (f : Word 3 3 → α) :
    ∑ x, f x = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f ![i, j, k] := by
  classical
  have h := (wordEquiv.symm.sum_comp f).symm
  rw [wordEquiv] at h
  simpa [Fintype.sum_prod_type] using h

private lemma cs {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (∑ i, Complex.normSq (u i)) * ∑ i, Complex.normSq (v i) := by
  classical
  simpa only [Complex.normSq_eq_norm_sq] using
    D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.cs_sq u v

private lemma expectation_rank_one (φ ψ : Word 3 3 → ℂ) :
    expectation (rankOneDensity φ) ψ = Complex.normSq (star φ ⬝ᵥ ψ) := by
  classical
  rw [expectation]
  simp only [rankOneDensity, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, smul_eq_mul]
  rw [star_dotProduct ψ φ]
  simp [Complex.mul_conj]

private lemma expectation_add (a c : Matrix (Word 3 3) (Word 3 3) ℂ)
    (ψ : Word 3 3 → ℂ) : expectation (a + c) ψ = expectation a ψ + expectation c ψ := by
  classical
  simp [expectation, add_mulVec, dotProduct_add]

private lemma expectation_smul (r : ℝ) (a : Matrix (Word 3 3) (Word 3 3) ℂ)
    (ψ : Word 3 3 → ℂ) : expectation (r • a) ψ = r * expectation a ψ := by
  classical
  simp [expectation, smul_mulVec, dotProduct_smul, Complex.real_smul]

private lemma expectation_one (ψ : Word 3 3 → ℂ) :
    expectation 1 ψ = ∑ x, Complex.normSq (ψ x) := by
  classical
  simp [expectation, dotProduct, Pi.star_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum]

private lemma expectation_sub (a c : Matrix (Word 3 3) (Word 3 3) ℂ)
    (ψ : Word 3 3 → ℂ) : expectation (a - c) ψ = expectation a ψ - expectation c ψ := by
  classical
  simp [expectation, sub_mulVec, dotProduct_sub]

private lemma support_expectation (ψ : Word 3 3 → ℂ) :
    expectation (supportProjector 3 3) ψ =
      ∑ x ∈ Finset.univ.filter (fun x : Word 3 3 => (Finset.univ.image x).card ≤ 2),
        Complex.normSq (ψ x) := by
  classical
  rw [expectation, supportProjector]
  simp only [mulVec_diagonal, dotProduct,
    Pi.star_apply, Finset.sum_filter]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp [← Complex.normSq_eq_conj_mul_self]

private lemma support_bounds (ψ : Word 3 3 → ℂ) :
    0 ≤ expectation (supportProjector 3 3) ψ ∧
      expectation (supportProjector 3 3) ψ ≤ ∑ x, Complex.normSq (ψ x) := by
  classical
  rw [support_expectation]
  exact ⟨Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _),
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Complex.normSq_nonneg _)⟩

private lemma ghz_dot (ψ : Word 3 3 → ℂ) :
    star (ghz 3 3) ⬝ᵥ ψ =
      (Real.sqrt 3 : ℂ)⁻¹ * ∑ i : Fin 3, ψ (fun _ => i) := by
  classical
  delta ghz
  have hc (i : Fin 3) : (![i, i, i] : Word 3 3) = (fun _ => i) := by
    funext k; fin_cases k <;> rfl
  norm_num [dotProduct, sum_words, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Pi.star_apply, hc]
  ring

private lemma ghz_expectation (ψ : Word 3 3 → ℂ) :
    3 * expectation (rankOneDensity (ghz 3 3)) ψ =
      Complex.normSq (∑ i : Fin 3, ψ (fun _ => i)) := by
  classical
  rw [expectation_rank_one, ghz_dot, Complex.normSq_mul]
  norm_num [Complex.normSq_inv, Complex.normSq_ofReal, Real.sq_sqrt, Real.mul_self_sqrt]
  ring

private def join (a : Finset (Fin 3)) (i j : Fin 3) : Word 3 3 :=
  fun k => if k ∈ a then i else j

private lemma join_support (a : Finset (Fin 3)) (i j : Fin 3) :
    (Finset.univ.image (join a i j)).card ≤ 2 := by
  classical
  have h : Finset.univ.image (join a i j) ⊆ {i, j} := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    rw [join]
    split_ifs <;> simp
  exact (Finset.card_le_card h).trans (by by_cases h : i = j <;> simp [h])

private lemma join_injective (a : Finset (Fin 3)) (ha : a.Nonempty) (hc : aᶜ.Nonempty) :
    Function.Injective (fun ij : Fin 3 × Fin 3 => join a ij.1 ij.2) := by
  classical
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hc
  intro x y h
  apply Prod.ext
  · simpa [join, hk] using congrFun h k
  · simpa [join, Finset.mem_compl.mp hl] using congrFun h l

private lemma trace_rank_one (ψ : Word 3 3 → ℂ) :
    trace (rankOneDensity ψ) = ((∑ x, Complex.normSq (ψ x) : ℝ) : ℂ) := by
  classical
  simp [rankOneDensity, trace_vecMulVec, dotProduct, Complex.mul_conj]

private lemma ghz_supported (x : Word 3 3) :
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
  have hc : (Finset.univ.filter fun x : Word 3 3 =>
      (Finset.univ.image x).card ≤ 2).card = 21 := by decide
  have hp : trace (supportProjector 3 3) = 21 := by
    simpa [supportProjector, trace_diagonal, Finset.sum_boole] using
      congrArg (fun k : ℕ => (k : ℂ)) hc
  refine ⟨hp, ?_⟩
  rw [q]
  norm_num [ trace_sub, hp, trace_one, Word]
private lemma ghz_unit : IsUnit (ghz 3 3) := by
  classical
  delta ghz
  simp only [Fin.exists_fin_succ]
  norm_num [IsUnit, sum_words, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Complex.normSq_inv, Complex.normSq_ofReal, Real.sq_sqrt,
    Real.mul_self_sqrt]
private lemma projector_data :
    supportProjector 3 3 * supportProjector 3 3 = supportProjector 3 3 ∧
    supportProjector 3 3 * rankOneDensity (ghz 3 3) = rankOneDensity (ghz 3 3) ∧
    rankOneDensity (ghz 3 3) * supportProjector 3 3 = rankOneDensity (ghz 3 3) ∧
    rankOneDensity (ghz 3 3) * rankOneDensity (ghz 3 3) = rankOneDensity (ghz 3 3) := by
  classical
  have hn : star (ghz 3 3) ⬝ᵥ ghz 3 3 = 1 := by
    rw [D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.dot_star_self]
    simpa only [← Complex.normSq_eq_norm_sq, Complex.ofReal_one] using
      congrArg (fun x : ℝ => (x : ℂ)) ghz_unit
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
  constructor
  · have h := posSemidef_conjTranspose_mul_self
      (supportProjector 3 3 - rankOneDensity (ghz 3 3))
    simpa only [conjTranspose_sub, hp.eq, hg.eq, sub_mul, mul_sub, hpp, hpg, hgp, hgg,
      sub_self, sub_zero] using h
  · have h := posSemidef_conjTranspose_mul_self q
    simpa only [q, conjTranspose_sub, conjTranspose_one, hp.eq, sub_mul, mul_sub,
      one_mul, mul_one, hpp, sub_self, sub_zero] using h

private lemma witness_value : witnessValue 3 3 (3 / 8) = -(1 / 3) := by
  classical
  obtain ⟨_, _, hgp, hgg⟩ := projector_data
  have ht : trace (rankOneDensity (ghz 3 3)) = 1 := by rw [trace_rank_one, ghz_unit]; rfl
  rw [witnessValue, noisyGhz]
  norm_num [witnessOp, add_mul, mul_sub, sub_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_add, trace_sub, trace_smul,
    hgp, hgg, ht, finite_ranks.1, Complex.real_smul]
private lemma basis_unit (x : Word 3 3) : IsUnit (basis x) := by
  classical
  rw [IsUnit, basis]
  simp [Pi.single_apply]
private lemma zero_biseparable : IsBiseparable (basis (fun _ => 0)) := by
  classical
  refine ⟨basis_unit _, {0}, by simp, by decide,
    fun u => if ∀ i, u i = 0 then 1 else 0,
    fun v => if ∀ i, v i = 0 then 1 else 0, ?_⟩
  intro x
  have he : x = (fun _ => 0) ↔
      (∀ i : ↥({0} : Finset (Fin 3)), x i = 0) ∧
      (∀ i : ↥({0} : Finset (Fin 3))ᶜ, x i = 0) := by
    constructor
    · intro h; subst x; simp
    · rintro ⟨h, g⟩
      funext i
      by_cases hi : i ∈ ({0} : Finset (Fin 3))
      · exact h ⟨i, hi⟩
      · exact g ⟨i, Finset.mem_compl.mpr hi⟩
  simp only [basis, Pi.single_apply]
  by_cases h : ∀ i : ↥({0} : Finset (Fin 3)), x i = 0 <;>
    by_cases g : ∀ i : ↥({0} : Finset (Fin 3))ᶜ, x i = 0 <;>
      simp_all
private lemma test_unit : IsUnit testPsi := by
  classical
  delta testPsi
  norm_num [IsUnit, sum_words, Fin.sum_univ_succ, funext_iff,
    Fin.forall_fin_succ, Complex.normSq_div, Complex.normSq_ofReal, Real.sq_sqrt,
    Real.mul_self_sqrt]
private lemma test_expectation : expectation (witnessOp 3 3) testPsi = -(1 / 3) := by
  classical
  have hp : expectation (supportProjector 3 3) testPsi = 1 := by
    have he (i : Fin 3) : (![i, i, i] : Word 3 3) = (fun _ => i) := by
      funext k; fin_cases k <;> rfl
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
private lemma test_overlap : Complex.normSq (star (basis (fun _ => 0)) ⬝ᵥ testPsi) = 8 / 9 := by
  classical
  delta testPsi
  norm_num [basis, dotProduct, Pi.single_apply, Complex.normSq_div,
    Complex.normSq_ofReal, Real.sq_sqrt, Real.mul_self_sqrt]

private lemma witness_bounds (ψ : Word 3 3 → ℂ) (hψ : IsUnit ψ) :
    -1 ≤ expectation (witnessOp 3 3) ψ ∧ expectation (witnessOp 3 3) ψ ≤ 1 / 3 := by
  classical
  have hp := support_bounds ψ
  have hg := cs (ghz 3 3) ψ
  rw [ghz_unit, hψ, one_mul] at hg
  have hq := Complex.normSq_nonneg (star (ghz 3 3) ⬝ᵥ ψ)
  rw [witnessOp, expectation_sub, expectation_smul, expectation_rank_one]
  change (∑ x, Complex.normSq (ψ x)) = 1 at hψ
  constructor <;> linarith

private lemma hat_bdd (r : ℝ) : BddAbove {t : ℝ | ∃ ψ φ : Word 3 3 → ℂ,
    IsUnit ψ ∧ IsBiseparable φ ∧
      t = expectation (r • witnessOp 3 3 + rankOneDensity φ) ψ - 1} := by
  classical
  refine ⟨|r|, ?_⟩
  rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
  rw [expectation_add, expectation_smul, expectation_rank_one]
  have hp := cs φ ψ
  rw [hφ.1, hψ, one_mul] at hp
  have hw := witness_bounds ψ hψ
  have hr : r * expectation (witnessOp 3 3) ψ ≤ |r| := by
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
  have hm : -r / 3 - 1 / 9 ∈ {t : ℝ | ∃ ψ φ : Word 3 3 → ℂ,
      IsUnit ψ ∧ IsBiseparable φ ∧
        t = expectation (r • witnessOp 3 3 + rankOneDensity φ) ψ - 1} := by
    refine ⟨testPsi, basis (fun _ => 0), test_unit, zero_biseparable, ?_⟩
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
private lemma biseparable_overlap (φ : Word 3 3 → ℂ) (hφ : IsBiseparable φ) :
    3 * expectation (rankOneDensity (ghz 3 3)) φ ≤ expectation (supportProjector 3 3) φ := by
  classical
  obtain ⟨_, a, ha, hc, u, v, h⟩ := hφ
  have hj (i j : Fin 3) : φ (join a i j) = u (fun _ => i) * v (fun _ => j) := by
    rw [h]
    congr 1
    · congr 1; funext k; simp [join, k.property]
    · congr 1; funext k; simp [join, Finset.mem_compl.mp k.property]
  have hd (i : Fin 3) : φ (fun _ => i) = u (fun _ => i) * v (fun _ => i) := h _
  rw [ghz_expectation, support_expectation]
  calc
    Complex.normSq (∑ i : Fin 3, φ (fun _ => i)) ≤
        (∑ i : Fin 3, Complex.normSq (u (fun _ => i))) *
          ∑ j : Fin 3, Complex.normSq (v (fun _ => j)) := by
      simpa [dotProduct, Complex.star_def, hd] using
        cs (star (fun i : Fin 3 => u (fun _ => i))) (fun j : Fin 3 => v (fun _ => j))
    _ = ∑ ij : Fin 3 × Fin 3, Complex.normSq (φ (join a ij.1 ij.2)) := by
      simp only [Fintype.sum_prod_type, hj, Complex.normSq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      classical
      have hs : (∑ ij : Fin 3 × Fin 3, Complex.normSq (φ (join a ij.1 ij.2))) =
          ∑ x ∈ Finset.univ.image (fun ij : Fin 3 × Fin 3 => join a ij.1 ij.2),
            Complex.normSq (φ x) :=
        (Finset.sum_image (f := fun x : Word 3 3 => Complex.normSq (φ x))
          (s := Finset.univ) (g := fun ij : Fin 3 × Fin 3 => join a ij.1 ij.2)
          (fun x _ y _ hxy => join_injective a ha hc hxy)).symm
      rw [hs]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, join_support a ij.1 ij.2⟩
      · intro x _ _; exact Complex.normSq_nonneg _

private lemma inverse_bound (φ : Word 3 3 → ℂ) (hφ : IsBiseparable φ) :
    expectation dinv φ ≤ 1 := by
  classical
  have h := biseparable_overlap φ hφ
  have hu : expectation 1 φ = 1 := by rw [expectation_one]; exact hφ.1
  simp only [dinv, q, expectation_add, expectation_sub, expectation_smul] at *
  linarith
private lemma d_positive : dmat.PosDef := by
  classical
  have he : dmat = (2 / 3 : ℝ) • (1 : Matrix (Word 3 3) (Word 3 3) ℂ) +
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
private lemma weighted_cs (φ ψ : Word 3 3 → ℂ) :
    Complex.normSq (star φ ⬝ᵥ ψ) ≤ expectation dinv φ * expectation dmat ψ := by
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
  have hc := d_positive.star_dotProduct_mulVec_mul_le ψ (dinv *ᵥ φ)
  rw [hm, hr] at hc
  have he := (Complex.le_def.mp hc).1
  have hz := (Complex.nonneg_iff.mp (d_positive.posSemidef.dotProduct_mulVec_nonneg ψ)).2
  have hn : Complex.normSq (star ψ ⬝ᵥ φ) = Complex.normSq (star φ ⬝ᵥ ψ) := by
    rw [star_dotProduct ψ φ]
    exact Complex.normSq_conj _
  change ((star (star ψ ⬝ᵥ φ)) * (star ψ ⬝ᵥ φ)).re ≤
    ((star ψ ⬝ᵥ dmat *ᵥ ψ) * (star φ ⬝ᵥ dinv *ᵥ φ)).re at he
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, hn,
    Complex.mul_re, ← hz, zero_mul, sub_zero] at he
  simpa only [expectation, mul_comm] using he

private lemma pure_lower (ψ : Word 3 3 → ℂ) (hψ : IsUnit ψ) :
    expectation b ψ - 1 / 9 ≤ geometricMeasurePure ψ := by
  classical
  have hd : 0 ≤ expectation dmat ψ :=
    Complex.nonneg_iff.mp (d_positive.posSemidef.dotProduct_mulVec_nonneg ψ) |>.1
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ expectation dmat ψ := by
    apply csSup_le
    · exact ⟨_, basis (fun _ => 0), zero_biseparable, rfl⟩
    · rintro t ⟨φ, hφ, rfl⟩
      exact (weighted_cs φ ψ).trans (mul_le_of_le_one_left hd (inverse_bound φ hφ))
  have hu : expectation 1 ψ = 1 := by rw [expectation_one]; exact hψ
  have he : expectation dmat ψ + expectation b ψ = 10 / 9 := by
    simp only [dmat, b, q, witnessOp, expectation_add, expectation_sub, expectation_smul] at *
    linarith
  dsimp only [geometricMeasurePure]
  linarith

private lemma trace_expectation (a : Matrix (Word 3 3) (Word 3 3) ℂ)
    (ψ : Word 3 3 → ℂ) : (trace (rankOneDensity ψ * a)).re = expectation a ψ := by
  classical
  rw [trace_mul_comm]
  simp [rankOneDensity, mul_vecMulVec, trace_vecMulVec, expectation, dotProduct_comm]

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

private lemma basis_resolution : (∑ x : Word 3 3, rankOneDensity (basis x)) = 1 := by
  classical
  simpa only [basis, rankOneDensity, Pi.star_single, star_one,
    ← Matrix.single_eq_single_vecMulVec_single] using
      (Matrix.sum_single_one : (∑ i : Word 3 3, Matrix.single i i (1 : ℂ)) = 1)

private lemma ensemble_nonempty :
    {t : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word 3 3 → ℂ),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsUnit (ψ i)) ∧
      noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOneDensity (ψ i) ∧
      t = ∑ i, p i * geometricMeasurePure (ψ i)}.Nonempty := by
  classical
  let e := (Fintype.equivFin (Option (Word 3 3))).symm
  let w : Option (Word 3 3) → ℝ := fun i => if i = none then 5 / 8 else 1 / 72
  let v : Option (Word 3 3) → Word 3 3 → ℂ := fun i => i.elim (ghz 3 3) basis
  refine ⟨_, Fintype.card (Option (Word 3 3)), (fun i => w (e i)),
    (fun i => v (e i)), ?_, ?_, ?_, ?_, rfl⟩
  · intro i
    dsimp [w]
    split_ifs <;> norm_num
  · rw [e.sum_comp]
    norm_num [w, Fintype.sum_option, Word, Fintype.card_fun]
  · intro i
    cases h : e i with
    | none => simpa [v, h] using ghz_unit
    | some x => simpa [v, h] using basis_unit x
  · change noisyGhz 3 3 (3 / 8) =
      ∑ i, (fun j : Option (Word 3 3) => w j • rankOneDensity (v j)) (e i)
    conv_rhs =>
      rw [show (∑ i, (fun j : Option (Word 3 3) => w j • rankOneDensity (v j)) (e i)) =
          ∑ j : Option (Word 3 3), w j • rankOneDensity (v j) from
        e.sum_comp (fun j : Option (Word 3 3) => w j • rankOneDensity (v j))]
    norm_num [w, v, Fintype.sum_option, ← Finset.smul_sum, basis_resolution, noisyGhz]
    module

private lemma average_lower (k : ℕ) (p : Fin k → ℝ) (ψ : Fin k → Word 3 3 → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnit (ψ i))
    (he : noisyGhz 3 3 (3 / 8) = ∑ i, p i • rankOneDensity (ψ i)) :
    13 / 108 ≤ ∑ i, p i * geometricMeasurePure (ψ i) := by
  classical
  have htrace : (trace (noisyGhz 3 3 (3 / 8) * b)).re =
      ∑ i, p i * expectation b (ψ i) := by
    rw [he]
    simp [Finset.sum_mul, trace_sum, trace_smul,
      Complex.real_smul, trace_expectation]
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
