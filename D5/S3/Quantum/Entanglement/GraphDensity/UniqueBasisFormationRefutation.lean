/- GID: D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.claim; result=D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.result; claim=D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.claim
   digest: A nonorthogonal ensemble refutes constant formation on the source subspace. -/
/-
proof_shape: result: bind-only; consumers: none (settling result)
proof_shape: G: bind-only; consumers: Psi; escape_witness: none
proof_shape: Psi: bind-only; consumers: spanPsi, claim, psi_unit, psi_cross, psi0_marginal, psi2_marginal, phi_marginal; escape_witness: none
proof_shape: spanPsi: bind-only; consumers: claim, rho0_range; escape_witness: none
proof_shape: claim: bind-only; consumers: result; escape_witness: none
proof_shape: singletonEnsemble: bind-only; consumers: pure_formation_eq; escape_witness: none
proof_shape: rho0Ensemble: bind-only; consumers: rho0_cost, result; escape_witness: none
proof_shape: d0: bind-only; consumers: entropy_gap_identity, entropy_strict, psi0_marginal, psi0_entropy, psi2_entropy, psi0_formation, rho0_cost; escape_witness: none
proof_shape: d2: bind-only; consumers: psi2_marginal, psi2_entropy; escape_witness: none
proof_shape: ds: bind-only; consumers: entropy_gap_identity, entropy_strict, R_charpoly, phi_entropy, rho0_cost; escape_witness: none
proof_shape: R: bind-only; consumers: phi_marginal, R_charpoly; escape_witness: none
escape_witness: none
admission_basis: open-problem-resolution (#16853; Refuted)
proof_shape: density_entropy_nonneg: bind-only; consumers: pure_entropy_nonneg; escape_witness: none
proof_shape: pure_entropy_nonneg: bind-only; consumers: formation_le_cost_general; escape_witness: none
proof_shape: formation_le_cost_general: bind-only; consumers: result; escape_witness: none
proof_shape: positive_minor_zero: bind-only; consumers: positive_phase; escape_witness: none
proof_shape: positive_phase: bind-only; consumers: pure_cost_eq; escape_witness: none
proof_shape: pure_cost_eq: bind-only; consumers: pure_formation_eq; escape_witness: none
proof_shape: pure_formation_eq: bind-only; consumers: psi0_formation; escape_witness: none
proof_shape: psi_unit: bind-only; consumers: phi_unit, rho0_trace, rho0Ensemble, psi0_formation; escape_witness: none
proof_shape: psi_cross: bind-only; consumers: phi_unit; escape_witness: none
proof_shape: phi_unit: bind-only; consumers: rho0Ensemble; escape_witness: none
proof_shape: rho0_psd: bind-only; consumers: result; escape_witness: none
proof_shape: rho0_trace: bind-only; consumers: result; escape_witness: none
proof_shape: rho0_range: bind-only; consumers: result; escape_witness: none
proof_shape: phi_projectors: bind-only; consumers: rho0Ensemble; escape_witness: none
proof_shape: integer_certificate: bind-only; consumers: entropy_strict; escape_witness: none
proof_shape: entropy_gap_identity: bind-only; consumers: entropy_strict; escape_witness: none
proof_shape: entropy_strict: bind-only; consumers: result; escape_witness: none
proof_shape: psi0_marginal: bind-only; consumers: psi0_entropy; escape_witness: none
proof_shape: psi2_marginal: bind-only; consumers: psi2_entropy; escape_witness: none
proof_shape: phi_marginal: bind-only; consumers: phi_entropy; escape_witness: none
proof_shape: R_charpoly: bind-only; consumers: phi_entropy; escape_witness: none
proof_shape: entropy_of_charpoly: bind-only; consumers: psi0_entropy, psi2_entropy, phi_entropy; escape_witness: none
proof_shape: psi0_entropy: bind-only; consumers: psi0_formation, rho0_cost; escape_witness: none
proof_shape: psi2_entropy: bind-only; consumers: rho0_cost; escape_witness: none
proof_shape: phi_entropy: bind-only; consumers: rho0_cost; escape_witness: none
proof_shape: psi0_formation: bind-only; consumers: result; escape_witness: none
proof_shape: rho0_cost: bind-only; consumers: result; escape_witness: none
Direct frozen dependencies: FormationBounds.E_F, FormationBounds.Ensemble, FormationBounds.S,
FormationBounds.ensembleCost, FormationBounds.trace_outer, FormationBounds.marginal_trace;
PureStateHandshake.rankOneDensity; PartialTraceMutualInformation.partialTraceRight,
PartialTraceMutualInformation.partialTraceRight_posSemidef,
PartialTraceMutualInformation.spectral_sum_eq_of_charpoly_prod;
SeparableStateLocalUnitaryStabilizerObstruction.ensemble_kernel;
EntropyNonneg.shannon_entropy_nonneg; CartesianVariance.density_eigenvalues_sum;
DomiRankEntropyRefutation.entropyBits;
EmpiricalReflexiveSeparation.complex_sqrt_two_sq; CStarSmaleHigherOrder.sqrt3_sq.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source uses columns of G and zero-based indices; S is measured in bits.
The positive-weight phase argument leaves zero-weight ensemble slots unconstrained.
The superpositions use midpoint and the mixed density uses Finset.centerMass.
The projector scaling step applies Mathlib's public vecMulVec scaling laws.
Entropy nonnegativity applies EntropyNonneg.shannon_entropy_nonneg to the spectrum.
Literature completeness and the journal paragraph are ASSUMED-UNVERIFIED.
Escape audit unfinished for CartesianVariance.density_eigenvalues_sum: https://github.com/the-omega-institute/trureturing/issues/17533.
-/
import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import D5.S3.Entropy.EntropyNonneg
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation
import D5.S3.Quantum.Algebra.CStarSmaleHigherOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Polynomial
open D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation (entropyBits)
open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation

open D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds (E_F)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

/-- Eq. (2), 0-based indices: the nonzero entries of `G`. -/
noncomputable def G : Matrix (Fin 9) (Fin 9) ℂ := fun i j =>
  if i = 0 ∧ j = 0 then 2 / 3
  else if i = 1 ∧ j = 1 then 1 / Real.sqrt 3
  else if i = 1 ∧ j = 5 then Complex.I / (3 * Real.sqrt 3)
  else if i = 1 ∧ j = 6 then 2 / (3 * Real.sqrt 3)
  else if i = 2 ∧ j = 2 then Real.sqrt 2 / 3
  else if i = 3 ∧ j = 3 then 1 / Real.sqrt 3
  else if i = 4 ∧ j = 4 then Real.sqrt 2 / 3
  else if i = 5 ∧ j = 5 then Real.sqrt 11 / (3 * Real.sqrt 3)
  else if i = 5 ∧ j = 6 then (3 + 2 * Complex.I) / (3 * Real.sqrt 33)
  else if i = 6 ∧ j = 6 then 1 / Real.sqrt 33
  else if i = 7 ∧ j = 7 then 2 / 3
  else if i = 8 ∧ j = 8 then 1 / Real.sqrt 3
  else 0

/-- Eq. (3): `|Ψ_k⟩ = Σ_a |a⟩ ⊗ |r_{3a+k}⟩`, with `r_i` the `i`-th column of `G`. -/
noncomputable def Psi (k : Fin 3) : Fin 3 × Fin 9 → ℂ :=
  fun ab => G ab.2 ⟨3 * ab.1.val + k.val, by omega⟩

/-- The span `S` of `Ψ₁, Ψ₂, Ψ₃`. -/
noncomputable def spanPsi : Submodule ℂ (Fin 3 × Fin 9 → ℂ) := Submodule.span ℂ (Set.range Psi)

/-- The source's open equality: every density operator with range in `S` has the EOF of `|Ψ₁⟩`. -/
def claim : Prop :=
  ∀ ρ : Matrix (Fin 3 × Fin 9) (Fin 3 × Fin 9) ℂ, ρ.PosSemidef → ρ.trace = 1 →
    LinearMap.range (Matrix.toLin' ρ) ≤ spanPsi → E_F ρ = E_F (rankOneDensity (Psi 0))


private theorem density_entropy_nonneg {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ)
    (hp : A.PosSemidef) (ht : A.trace = 1) : 0 ≤ S A := by
  have hs : ∑ i, hp.1.eigenvalues i = 1 :=
    D5.S3.Quantum.Matrix.CartesianVariance.density_eigenvalues_sum A ⟨hp, ht⟩
  simp only [S, dif_pos hp.1, spectralEntropy]
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  exact D5.S3.Entropy.EntropyNonneg.shannon_entropy_nonneg
    hp.1.eigenvalues ⟨hp.eigenvalues_nonneg, hs⟩


private theorem pure_entropy_nonneg {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (hv : ∑ x, ‖v x‖^2 = 1) : 0 ≤ S (partialTraceRight (rankOneDensity v)) := by
  apply density_entropy_nonneg
  · exact partialTraceRight_posSemidef (posSemidef_vecMulVec_self_star v)
  · rw [marginal_trace, hv]; norm_num

private theorem formation_le_cost_general {p q : ℕ} {ρ : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ}
    (e : Ensemble ρ) : E_F ρ ≤ ensembleCost e := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro s ⟨f, rfl⟩
    exact Finset.sum_nonneg fun i _ => mul_nonneg (f.nonneg i) (pure_entropy_nonneg _ (f.unit i))
  · exact ⟨e, rfl⟩

private theorem positive_minor_zero {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (e : Ensemble (rankOneDensity v)) (i : Fin e.N) (hi : 0 < e.weight i)
    (a b : Fin p × Fin q) : v a * e.psi i b - v b * e.psi i a = 0 := by
  classical
  let z : Fin p × Fin q → ℂ :=
    star (v a) • Pi.single b 1 - star (v b) • Pi.single a 1
  have hd (f : Fin p × Fin q → ℂ) : star z ⬝ᵥ f = v a * f b - v b * f a := by
    simp [z, star_sub, star_smul, smul_dotProduct, single_dotProduct]
  have hz : star z ⬝ᵥ v = 0 := by rw [hd]; ring
  have hav : ∑ j, e.weight j • rankOneDensity (e.psi j) = rankOneDensity v := by
    exact e.average
  have hzero : star z ⬝ᵥ ((∑ j, e.weight j • rankOneDensity (e.psi j)) *ᵥ z) = 0 := by
    rw [hav]
    simp only [rankOneDensity, vecMulVec_mulVec, dotProduct_smul, smul_eq_mul, hz, mul_zero, smul_zero]
  have hk := D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.ensemble_kernel
    e.psi e.weight e.nonneg z hzero i hi
  simpa only [hd] using hk

theorem positive_phase {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (hv : ∑ x, ‖v x‖^2 = 1) (e : Ensemble (rankOneDensity v))
    (i : Fin e.N) (hi : 0 < e.weight i) : ∃ z : ℂ, ‖z‖ = 1 ∧ e.psi i = z • v := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hv
  have hm (b) : v a * e.psi i b - v b * e.psi i a = 0 :=
    positive_minor_zero v e i hi a b
  let z := e.psi i a / v a
  have heq : e.psi i = z • v := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [z]
    have h := sub_eq_zero.mp (hm b)
    field_simp
    linear_combination h
  refine ⟨z, ?_, heq⟩
  have hu := e.unit i
  rw [heq] at hu
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, hv, mul_one] at hu
  nlinarith [norm_nonneg z]


private theorem pure_cost_eq {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (hv : ∑ x, ‖v x‖^2 = 1) (e : Ensemble (rankOneDensity v)) :
    ensembleCost e = S (partialTraceRight (rankOneDensity v)) := by
  unfold ensembleCost
  calc
    _ = ∑ i, e.weight i * S (partialTraceRight (rankOneDensity v)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : e.weight i = 0
      · simp [h]
      · obtain ⟨z, hz, heq⟩ := positive_phase v hv e i (lt_of_le_of_ne (e.nonneg i) (Ne.symm h))
        rw [heq]
        have hzz : z * star z = 1 := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
          norm_num
        congr 2
        simp only [rankOneDensity, star_smul, Matrix.smul_vecMulVec,
          Matrix.vecMulVec_smul, smul_smul, mul_comm (star z) z, hzz, one_smul]
    _ = _ := by rw [← Finset.sum_mul, e.total, one_mul]

private noncomputable def singletonEnsemble {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (hv : ∑ x, ‖v x‖^2 = 1) : Ensemble (rankOneDensity v) where
  N := 1
  weight := fun _ => 1
  nonneg := by intro i; norm_num
  le_one := by intro i; norm_num
  total := by simp
  psi := fun _ => v
  unit := fun _ => hv
  average := by simp

private theorem pure_formation_eq {p q : ℕ} (v : Fin p × Fin q → ℂ)
    (hv : ∑ x, ‖v x‖^2 = 1) :
    E_F (rankOneDensity v) = S (partialTraceRight (rankOneDensity v)) := by
  have hset : {t | ∃ e : Ensemble (rankOneDensity v), t = ensembleCost e} =
      {S (partialTraceRight (rankOneDensity v))} := by
    ext t
    constructor
    · rintro ⟨e, rfl⟩
      exact pure_cost_eq v hv e
    · intro h
      refine ⟨singletonEnsemble v hv, ?_⟩
      rw [pure_cost_eq v hv]
      exact h
  unfold E_F
  rw [hset, csInf_singleton]


private theorem psi_unit (k : Fin 3) : ∑ x, ‖Psi k x‖^2 = 1 := by
  fin_cases k <;> simp_rw [← Complex.normSq_eq_norm_sq]
  all_goals simp +decide only [Psi, G, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Complex.normSq_zero, add_zero, zero_add]
  all_goals norm_num [Complex.normSq_div, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 11),
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 33)]
  norm_num [Complex.normSq_apply]

local notation "phi" => fun s : ℝ => midpoint ℂ (Psi 0) ((s * Real.sqrt 3 : ℝ) • Psi 1)

private theorem psi_cross (x : Fin 3 × Fin 9) : Psi 0 x * star (Psi 1 x) = 0 := by
  rcases x with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp +decide [Psi,G]

private theorem phi_unit (s : ℝ) (hs : s^2 = 1) : ∑ x, ‖phi s x‖^2 = 1 := by
  have hr : Real.sqrt 3 ^ 2 = 3 := by
    exact_mod_cast D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
  simp only [midpoint_eq_smul_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Complex.real_smul, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
  have hcross (x) : (Psi 0 x * star ((s * Real.sqrt 3 : ℝ) * Psi 1 x)).re = 0 := by
    calc
      _ = ((Psi 0 x * star (Psi 1 x)) * star ((s * Real.sqrt 3 : ℝ) : ℂ)).re := by
        simp only [star_mul]
        congr 1
        ring
      _ = 0 := by rw [psi_cross]; simp
  simp only [Complex.star_def] at hcross
  simp only [hcross, mul_zero, add_zero]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Complex.normSq_eq_norm_sq, psi_unit]
  norm_num [mul_pow, hs, hr, Complex.normSq_apply]
  have hx : (s * Real.sqrt 3)^2 = 3 := by rw [mul_pow,hs,hr]; norm_num
  nlinarith [hx]

local notation "rho0" => Finset.univ.centerMass (fun _ : Fin 3 => (1 : ℂ))
  (fun k => rankOneDensity (Psi k))

private theorem rho0_psd : (rho0).PosSemidef := by
  norm_num only [Finset.centerMass, Fin.sum_univ_succ, Fin.sum_univ_zero, one_smul, add_zero, ← add_assoc]
  exact ((posSemidef_vecMulVec_self_star (Psi 0)).add
    (posSemidef_vecMulVec_self_star (Psi 1)) |>.add
    (posSemidef_vecMulVec_self_star (Psi 2))).smul (by norm_num [Complex.le_def])

private theorem rho0_trace : (rho0).trace = 1 := by
  norm_num [Finset.centerMass, Fin.sum_univ_succ, Fin.sum_univ_zero, one_smul, add_zero, trace_smul, trace_add, trace_outer, psi_unit]

private theorem rho0_range : LinearMap.range (Matrix.toLin' rho0) ≤ spanPsi := by
  rintro y ⟨x, rfl⟩
  have hp (k : Fin 3) : Psi k ∈ spanPsi := Submodule.subset_span ⟨k,rfl⟩
  change rho0 *ᵥ x ∈ spanPsi
  simp only [Finset.centerMass, Fin.sum_univ_succ, Fin.sum_univ_zero, one_smul, add_zero, ← add_assoc, add_mulVec, smul_mulVec, rankOneDensity, vecMulVec_mulVec, op_smul_eq_smul]
  exact (spanPsi.smul_mem _ (spanPsi.add_mem
    (spanPsi.add_mem (spanPsi.smul_mem _ (hp 0)) (spanPsi.smul_mem _ (hp 1)))
    (spanPsi.smul_mem _ (hp 2))))

private theorem phi_projectors : rankOneDensity (phi 1) + rankOneDensity (phi (-1)) =
    (1/2 : ℂ) • rankOneDensity (Psi 0) + (3/2 : ℂ) • rankOneDensity (Psi 1) := by
  have hr : (Real.sqrt 3 : ℂ)^2 = 3 :=
    D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
  ext a b
  simp only [midpoint_eq_smul_add, rankOneDensity, vecMulVec_apply, Pi.smul_apply, Pi.add_apply,
    Pi.star_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply, star_mul, star_add]
  norm_num [Complex.star_def]
  linear_combination (Psi 1 a * (starRingEnd ℂ) (Psi 1 b) / 2) * hr

private noncomputable def rho0Ensemble : Ensemble rho0 where
  N := 4
  weight := ![2/9,2/9,2/9,1/3]
  nonneg := by intro i; fin_cases i <;> norm_num
  le_one := by intro i; fin_cases i <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]
  psi := ![phi 1,phi (-1),Psi 0,Psi 2]
  unit := by intro i; fin_cases i
             exact phi_unit 1 (by norm_num)
             exact phi_unit (-1) (by norm_num)
             exact psi_unit 0
             exact psi_unit 2
  average := by
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue, Fin.sum_univ_zero, add_zero]
    rw [← add_assoc, ← add_assoc, ← smul_add, phi_projectors]
    norm_num [Finset.centerMass, Fin.sum_univ_succ, smul_add, smul_smul]
    module


private noncomputable def d0 : Fin 3 → ℝ := ![4/9,1/3,2/9]
private noncomputable def d2 : Fin 3 → ℝ := ![2/9,4/9,1/3]
private noncomputable def ds : Fin 3 → ℝ := ![17/36,10/36,9/36]

private theorem integer_certificate : (2:ℕ)^102 < 17^17 * 5^10 * 3^6 := by
  exact Nat.lt_of_sub_eq_succ rfl

private theorem entropy_gap_identity :
     36 * Real.log 2 * ((entropyBits d0) - (entropyBits ds)) =
       17 * Real.log 17 + 10 * Real.log 5 + 6 * Real.log 3 - 102 * Real.log 2 := by
   have hl2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
   have h4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
   have h9 : Real.log 9 = 2 * Real.log 3 := by
     rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; norm_num
   have h36 : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
     rw [show (36:ℝ) = 4*9 by norm_num, Real.log_mul (by norm_num) (by norm_num),h4,h9]
   have h10 : Real.log 10 = Real.log 2 + Real.log 5 := Real.log_ten_eq
   simp only [entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy, d0, ds, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,Real.negMulLog,Real.log_div (by norm_num : (4:ℝ)≠0) (by norm_num : (9:ℝ)≠0),
      Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (3:ℝ)≠0),
      Real.log_div (by norm_num : (2:ℝ)≠0) (by norm_num : (9:ℝ)≠0),
      Real.log_div (by norm_num : (17:ℝ)≠0) (by norm_num : (36:ℝ)≠0),
      Real.log_div (by norm_num : (10:ℝ)≠0) (by norm_num : (36:ℝ)≠0),
      Real.log_div (by norm_num : (9:ℝ)≠0) (by norm_num : (36:ℝ)≠0),
      Real.log_one,h4,h9,h10,h36]
   field_simp
   ring

private theorem entropy_strict : (entropyBits ds) < (entropyBits d0) := by
   have hint : (2:ℝ)^102 < 17^17 * 5^10 * 3^6 := by exact_mod_cast integer_certificate
   have hpos : 0 < (2:ℝ)^102 := pow_pos (by norm_num) 102
   have hlog := Real.strictMonoOn_log hpos (by positivity : 0 < (17:ℝ)^17 * 5^10 * 3^6) hint
   rw [Real.log_mul (by positivity) (by positivity),
       Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow,Real.log_pow] at hlog
   norm_num only [Nat.cast_ofNat] at hlog
   have hg := entropy_gap_identity
   have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
   nlinarith


private theorem psi0_marginal : partialTraceRight (rankOneDensity (Psi 0)) =
     Matrix.diagonal (fun i => (d0 i : ℂ)) := by
   have h2 : (Real.sqrt 2:ℂ)^2 = 2 := D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq
   have h3 : (Real.sqrt 3:ℂ)^2 = 3 := D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
   have h11 : (Real.sqrt 11:ℂ)^2 = 11 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤11)
   have h33 : (Real.sqrt 33:ℂ)^2 = 33 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤33)
   have hn3 : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num : (3:ℝ) ≠ 0)
   have hn33 : (Real.sqrt 33:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 33)).mpr (by norm_num : (33:ℝ) ≠ 0)
   ext a c
   fin_cases a <;> fin_cases c
   all_goals simp +decide only [partialTraceRight,rankOneDensity,Psi,G,Matrix.vecMulVec_apply,
      Pi.star_apply, Fin.sum_univ_succ, Matrix.diagonal, d0, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue, mul_zero, zero_mul, star_zero, add_zero, zero_add]
   all_goals norm_num [Complex.star_def, Complex.mul_conj, Complex.normSq_div,
      Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0:ℝ)≤3), Real.mul_self_sqrt (by norm_num : (0:ℝ)≤33)]

   all_goals try field_simp [hn3,hn33]
   all_goals ring_nf
   all_goals simp only [h2,h3,h11,h33,Complex.I_sq]
   all_goals ring

private theorem psi2_marginal : partialTraceRight (rankOneDensity (Psi 2)) =
     Matrix.diagonal (fun i => (d2 i : ℂ)) := by
   have h2 : (Real.sqrt 2:ℂ)^2 = 2 := D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq
   have h3 : (Real.sqrt 3:ℂ)^2 = 3 := D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
   have h11 : (Real.sqrt 11:ℂ)^2 = 11 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤11)
   have h33 : (Real.sqrt 33:ℂ)^2 = 33 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤33)
   have hn3 : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num : (3:ℝ) ≠ 0)
   have hn33 : (Real.sqrt 33:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 33)).mpr (by norm_num : (33:ℝ) ≠ 0)
   ext a c
   fin_cases a <;> fin_cases c
   all_goals simp +decide only [partialTraceRight,rankOneDensity,Psi,G,Matrix.vecMulVec_apply,
      Pi.star_apply, Fin.sum_univ_succ, Matrix.diagonal, d2, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.isValue, mul_zero, zero_mul, star_zero, add_zero, zero_add]
   all_goals norm_num [Complex.star_def, Complex.mul_conj, Complex.normSq_div,
      Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2), Real.mul_self_sqrt (by norm_num : (0:ℝ)≤3),
      Real.mul_self_sqrt (by norm_num : (0:ℝ)≤11)]

   all_goals try field_simp [hn3,hn33]
   all_goals ring_nf
   all_goals simp only [h2,h3,h11,h33,Complex.I_sq]
   all_goals ring

private noncomputable def R (s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
     (1/36:ℂ) • !![13,0,((2*s*Real.sqrt 3:ℝ):ℂ); 0,9,0; ((2*s*Real.sqrt 3:ℝ):ℂ),0,14]

private theorem phi_marginal (s : ℝ) (hs : s^2 = 1) :
     partialTraceRight (rankOneDensity (phi s)) = R s := by
   have h2 : (Real.sqrt 2:ℂ)^2 = 2 := D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq
   have h3 : (Real.sqrt 3:ℂ)^2 = 3 := D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
   have h33 : (Real.sqrt 33:ℂ)^2 = 33 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤33)
   have hn3 : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num : (3:ℝ) ≠ 0)
   have hn33 : (Real.sqrt 33:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero (by norm_num : (0:ℝ) ≤ 33)).mpr (by norm_num : (33:ℝ) ≠ 0)
   have hsC : (s:ℂ)^2 = 1 := by exact_mod_cast hs
   have h34 : (Real.sqrt 3:ℂ)^4 = 9 := by
     calc
       _ = ((Real.sqrt 3:ℂ)^2)^2 := by ring
       _ = 9 := by rw [h3]; norm_num
   ext a c
   fin_cases a <;> fin_cases c
   all_goals simp +decide only [partialTraceRight,rankOneDensity,midpoint_eq_smul_add,Psi,G,Matrix.vecMulVec_apply,
      Pi.star_apply,Pi.smul_apply, Complex.real_smul, Pi.add_apply, smul_eq_mul, Fin.sum_univ_succ,R,
      Matrix.smul_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,
      mul_zero,zero_mul,star_zero,add_zero,zero_add]
   all_goals norm_num [Complex.star_def]
   all_goals try field_simp [hn3, hn33]
   all_goals ring_nf
   all_goals simp only [h2,h3,h34,h33,hsC, Complex.I_sq]
   all_goals ring

private theorem R_charpoly (s : ℝ) (hs : s^2 = 1) :
     (R s).charpoly = ∏ i, (X - C (ds i : ℂ)) := by
   have h3 : (Real.sqrt 3:ℂ)^2 = 3 := D5.S3.Quantum.Algebra.CStarSmaleHigherOrder.sqrt3_sq
   have hsC : (s:ℂ)^2 = 1 := by exact_mod_cast hs
   simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three, R,ds,Fin.prod_univ_succ,
     Matrix.smul_apply,Matrix.cons_val_zero,Matrix.cons_val_succ]
   ring_nf
   simp [← map_pow,h3,hsC]
   apply Polynomial.funext
   intro t
   simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
     Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X]
   norm_num
   ring

private theorem entropy_of_charpoly (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian)
     (d : Fin 3 → ℝ) (hc : A.charpoly = ∏ i, (X - C (d i : ℂ))) :
     S A = (∑ i, Real.negMulLog (d i)) / Real.log 2 := by
   simp only [S, dif_pos hA,spectralEntropy]
   rw [spectral_sum_eq_of_charpoly_prod hA d Real.negMulLog hc]

private theorem psi0_entropy : S (partialTraceRight (rankOneDensity (Psi 0))) = (entropyBits d0) := by
   apply (entropy_of_charpoly _
     (partialTraceRight_posSemidef (posSemidef_vecMulVec_self_star _)).1 d0 ?_).trans
   · simp [d0,entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy,Fin.sum_univ_succ,add_assoc]
   · change (partialTraceRight (rankOneDensity (Psi 0))).charpoly = _
     rw [psi0_marginal, charpoly_diagonal]

private theorem psi2_entropy : S (partialTraceRight (rankOneDensity (Psi 2))) = (entropyBits d0) := by
   apply (entropy_of_charpoly _
     (partialTraceRight_posSemidef (posSemidef_vecMulVec_self_star _)).1 d2 ?_).trans
   · simp [d0,d2,entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy,Fin.sum_univ_succ]
     ring
   · change (partialTraceRight (rankOneDensity (Psi 2))).charpoly = _
     rw [psi2_marginal, charpoly_diagonal]

private theorem phi_entropy (s : ℝ) (hs : s^2=1) :
     S (partialTraceRight (rankOneDensity (phi s))) = (entropyBits ds) := by
   apply (entropy_of_charpoly _
     (partialTraceRight_posSemidef (posSemidef_vecMulVec_self_star _)).1 ds ?_).trans
   · simp [ds,entropyBits, D5.S3.Entropy.MaxEntropy.shannonEntropy,Fin.sum_univ_succ,add_assoc]
   · change (partialTraceRight (rankOneDensity (phi s))).charpoly = _
     rw [phi_marginal s hs]; exact R_charpoly s hs


private theorem psi0_formation : E_F (rankOneDensity (Psi 0)) = (entropyBits d0) := by
   rw [pure_formation_eq (Psi 0) (psi_unit 0), psi0_entropy]

private theorem rho0_cost : ensembleCost rho0Ensemble = (4/9) * (entropyBits ds) + (5/9) * (entropyBits d0) := by
   change (∑ i : Fin 4, (![2/9,2/9,2/9,1/3] : Fin 4 → ℝ) i *
     S (partialTraceRight (rankOneDensity ((![phi 1,phi (-1),Psi 0,Psi 2] :
       Fin 4 → Fin 3 × Fin 9 → ℂ) i)))) = _
   simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,
     Matrix.cons_val_succ,Fin.isValue,Fin.sum_univ_zero,add_zero]
   rw [phi_entropy 1 (by norm_num),phi_entropy (-1) (by norm_num),psi0_entropy,psi2_entropy]
   ring

theorem result : ¬ claim := by
   intro hc
   have hsame := hc rho0 rho0_psd rho0_trace rho0_range
   have hbound := formation_le_cost_general rho0Ensemble
   rw [hsame, psi0_formation, rho0_cost] at hbound
   have hl := entropy_strict
   linarith

end D5.S3.Quantum.Entanglement.GraphDensity.UniqueBasisFormationRefutation
