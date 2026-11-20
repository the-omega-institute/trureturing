/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Continuous physical collisions of one-site periodic marginal observations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A collective rotation can preserve one-site data while changing adjacent correlations. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSOneSiteAmbiguity

open Matrix NormedSpace Filter Set
open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator Topology
open PeriodicMPSParentIntersection (Bond Word twoFlattening wordMatrix wordMatrix_cons)
open PeriodicMPSTwoSiteAmbiguity (rawTwo parityPair parity_cross rawTwo_star_swap flattening_entry)
open PeriodicMPSAmbiguityDensity (changePhysical pairBasis changePhysical_unitary_raw)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (trace_local_right)
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

private abbrev Bits := Fin 2 × Fin 2
private abbrev TwoDensity := Matrix Bits Bits ℂ

/-- The single-site reduced matrix, retaining the mass of the full amplitude. -/
def rawOne (A : Fin 2 → Bond) (r : ℕ) : Bond :=
  partialTraceRight (rawTwo A r)

/-- The commutator of the observed pair with the sum of its two one-site generators. -/
def defect (G : TwoDensity) : TwoDensity :=
  let H := partialTraceRight G
  let K := H ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ H
  K * G - G * K

private lemma rawOne_hermitian (A : Fin 2 → Bond) (r : ℕ) : IsSelfAdjoint (rawOne A r) := by
  change (rawOne A r)ᴴ = rawOne A r
  ext i j
  simp only [rawOne, partialTraceRight, conjTranspose_apply, star_sum, rawTwo_star_swap]

private def rotation (H : Bond) (t : ℝ) : Bond := exp (t • (Complex.I • H))

private lemma rotation_unitary (H : Bond) (hH : IsSelfAdjoint H) (t : ℝ) :
    rotation H t ∈ unitaryGroup (Fin 2) ℂ := by
  let : NormedAlgebra ℚ Bond := NormedAlgebra.restrictScalars ℚ ℂ _
  apply exp_mem_unitary_of_mem_skewAdjoint
  have hs : ((t : ℂ) * Complex.I) • H ∈ skewAdjoint Bond :=
    hH.smul_mem_skewAdjoint (by
      change star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I)
      simp)
  simpa [rotation, mul_smul, Complex.real_smul] using hs

private lemma rawOne_rotate (A : Fin 2 → Bond) (r : ℕ) (t : ℝ) :
    rawOne (changePhysical (rotation (rawOne A r) t) A) r = rawOne A r := by
  let H := rawOne A r
  let U : unitaryGroup (Fin 2) ℂ := ⟨rotation H t, rotation_unitary H (rawOne_hermitian A r) t⟩
  have hU := mem_unitaryGroup_iff'.mp U.property
  have hc : Commute H (rotation H t) := by
    let : NormedAlgebra ℚ Bond := NormedAlgebra.restrictScalars ℚ ℂ _
    exact (((Commute.refl H).smul_right Complex.I).smul_right t).exp_right
  change partialTraceRight (rawTwo (changePhysical U.val A) r) = H
  rw [changePhysical_unitary_raw U A r]
  change partialTraceRight ((U.val ⊗ₖ U.val) * rawTwo A r * (U.val ⊗ₖ U.val)ᴴ) = H
  rw [trace_local_right _ _ _ hU]
  change rotation H t * H * (rotation H t)ᴴ = H
  rw [hc.eq.symm, mul_assoc, show (rotation H t) * (rotation H t)ᴴ = 1 from
    mem_unitaryGroup_iff.mp U.property, mul_one]

private def entry {n : Type*} [Fintype n] [DecidableEq n] (i j : n) :
    Matrix n n ℂ →L[ℝ] ℂ :=
  ({ toFun := fun M => M i j
     map_add' := fun M N => Matrix.add_apply M N i j
     map_smul' := fun c M => Matrix.smul_apply c M i j } :
        Matrix n n ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

private lemma rotation_entry_deriv (H : Bond) (i j : Fin 2) :
    HasDerivAt (fun t => rotation H t i j) (Complex.I * H i j) 0 := by
  let : NormedAlgebra ℚ Bond := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAddCommGroup Bond := Matrix.instL2OpNormedAddCommGroup
  let : NormedSpace ℝ Bond := NormedAlgebra.toNormedSpace Bond
  have h := hasDerivAt_exp_smul_const (Complex.I • H) (0 : ℝ)
  rw [zero_smul, exp_zero, one_mul] at h
  have hg := (entry i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact hg

private lemma rawTwo_rotate_entry_deriv (A : Fin 2 → Bond) (r : ℕ) (p q : Bits) :
    HasDerivAt
      (fun t => rawTwo (changePhysical (rotation (rawOne A r) t) A) r p q)
      (Complex.I * defect (rawTwo A r) p q) 0 := by
  let G := rawTwo A r
  let H := rawOne A r
  let U (t : ℝ) : unitaryGroup (Fin 2) ℂ :=
    ⟨rotation H t, rotation_unitary H (rawOne_hermitian A r) t⟩
  let L := (Complex.I • H) ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ (Complex.I • H)
  have hp (i j : Bits) :
      HasDerivAt (fun t => pairBasis (rotation H t) i j) (L i j) 0 := by
    have h := (rotation_entry_deriv H i.1 j.1).fun_mul (rotation_entry_deriv H i.2 j.2)
    simpa [pairBasis, L, rotation, Matrix.add_apply, Matrix.smul_apply, add_comm] using h
  have hq (i j : Bits) :
      HasDerivAt (fun t => (pairBasis (rotation H t))ᴴ i j) (Lᴴ i j) 0 :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (hp j i)
  have hstar : Lᴴ = -L := by
    have hH : Hᴴ = H := rawOne_hermitian A r
    simp only [L, conjTranspose_add, conjTranspose_kronecker, conjTranspose_smul, hH,
      Complex.star_def, Complex.conj_I, neg_smul, conjTranspose_one]
    ext i j
    simp [add_comm]
  have hone : pairBasis (rotation H 0) = 1 := by
    change rotation H 0 ⊗ₖ rotation H 0 = 1
    simp [rotation]
  have hprod (k : Bits) :
      HasDerivAt (fun t => (pairBasis (rotation H t) * G) p k) ((L * G) p k) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun l _ => (hp p l).mul_const (G l k)
  have hder := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hprod k).fun_mul (hq k q)
  have hresult :
      HasDerivAt (fun t => (pairBasis (rotation H t) * G * (pairBasis (rotation H t))ᴴ) p q)
        ((L * G - G * L) p q) 0 := by
    rw [show (L * G - G * L) p q = (L * G * (pairBasis (rotation H 0))ᴴ +
      (pairBasis (rotation H 0) * G) * Lᴴ) p q by simp [hone, hstar, sub_eq_add_neg]]
    simpa only [Matrix.add_apply, Matrix.mul_apply (M := _ * _), ← Finset.sum_add_distrib]
      using hder
  have hL : L * G - G * L = Complex.I • defect G := by
    simp [L, defect, H, G, rawOne, smul_kronecker, kronecker_smul,
      ← smul_add, smul_sub]
  rw [hL] at hresult
  convert hresult using 1
  funext t
  exact congrArg (fun M : TwoDensity => M p q) (changePhysical_unitary_raw (U t) A r)

/-- A nonzero commutator certifies actual arbitrarily small perturbations that are
invisible to the single-site observation and visible on an adjacent pair. -/
theorem arbitrarily_close_one_site_collisions (A : Fin 2 → Bond) (r : ℕ)
    (h : defect (rawTwo A r) ≠ 0) :
    ∃ B : ℝ → Fin 2 → Bond, Continuous B ∧ B 0 = A ∧
      (∀ t, rawOne (B t) r = rawOne A r) ∧
      ¬ (fun t => rawTwo (B t) r) =ᶠ[nhds 0] (fun _ => rawTwo A r) := by
  let B (t : ℝ) := changePhysical (rotation (rawOne A r) t) A
  refine ⟨B, ?_, ?_, rawOne_rotate A r, ?_⟩
  · apply continuous_pi
    intro i
    change Continuous (fun t => ∑ j, rotation (rawOne A r) t i j • A j)
    let : NormedAlgebra ℚ Bond := NormedAlgebra.restrictScalars ℚ ℂ _
    have hu : Continuous (rotation (rawOne A r)) :=
      exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_finsetSum _ fun j _ =>
      ((entry i j).continuous.comp hu).smul continuous_const
  · funext i
    simp [B, changePhysical, rotation, Matrix.one_apply]
  intro he
  apply h
  ext p q
  have he' : (fun _ : ℝ => rawTwo A r p q) =ᶠ[𝓝 0] (fun t => rawTwo (B t) r p q) :=
    he.symm.mono fun _ ht => congrArg (fun M : TwoDensity => M p q) ht
  have h0 := (rawTwo_rotate_entry_deriv A r p q).congr_of_eventuallyEq he'
  exact (mul_eq_zero.mp (h0.unique (hasDerivAt_const 0 _))).resolve_left Complex.I_ne_zero

private def sample : Fin 2 → Bond := parityPair 1 1 2

private lemma sample_zero : sample 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sample, parityPair]

private lemma sample_square : sample 1 * sample 1 = (4 : ℂ) • (1 : Bond) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sample, parityPair, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private lemma sample_defect (r : ℕ) : defect (rawTwo sample r) (0, 0) (1, 1) ≠ 0 := by
  let G := rawTwo sample r
  let H := partialTraceRight G
  let m := G (0, 0) (0, 0)
  have hc (i j : Fin 2) : G (i, i) (j, 1 - j) = 0 := by
    fin_cases j <;> exact (parity_cross 1 1 2 r i _ _).resolve_right (by decide)
  have hc' (i j : Fin 2) : G (j, 1 - j) (i, i) = 0 := by
    have e : star (G (i, i) (j, 1 - j)) = G (j, 1 - j) (i, i) :=
      rawTwo_star_swap sample r (i, i) (j, 1 - j)
    simpa only [hc, star_zero] using e.symm
  have hr (w : Word (r + 2)) :
      twoFlattening sample r (1, 1) w = 4 * twoFlattening sample r (0, 0) w := by
    rw [flattening_entry, flattening_entry, sample_square, sample_zero,
      Matrix.smul_mul, Matrix.trace_smul, one_mul, one_mul, one_mul, smul_eq_mul]
  have hmixed (w : Word (r + 2)) :
      twoFlattening sample r (0, 1) w = twoFlattening sample r (1, 0) w := by
    rw [flattening_entry, flattening_entry, sample_zero, one_mul, mul_one]
  have h03 : G (0, 0) (1, 1) = 4 * m := by
    simp only [G, m, rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, hr,
      star_mul, star_ofNat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h33 : G (1, 1) (1, 1) = 16 * m := by
    simp only [G, m, rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, hr, star_mul,
      Complex.star_def, map_ofNat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h12 : G (0, 1) (0, 1) = G (1, 0) (1, 0) := by
    simp [G, rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, hmixed]
  have hdiag : H = Matrix.diagonal (fun i => H i i) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    fin_cases i <;> fin_cases j <;> try contradiction
    · have e₁ : G (0, 0) (1, 0) = 0 := hc 0 1
      have e₂ : G (0, 1) (1, 1) = 0 := hc' 1 0
      simp [H, partialTraceRight, Fin.sum_univ_two, e₁, e₂]
    · have e₁ : G (1, 0) (0, 0) = 0 := hc' 0 1
      have e₂ : G (1, 1) (0, 1) = 0 := hc 1 0
      simp [H, partialTraceRight, Fin.sum_univ_two, e₁, e₂]
  have hdiff : H 0 0 - H 1 1 = -15 * m := by
    simp only [H, partialTraceRight, Fin.sum_univ_two, h12, h33, ← show m = G (0, 0) (0, 0) by rfl]
    ring
  have hm : m ≠ 0 := by
    have hword : twoFlattening sample r (0, 0) (fun _ => 0) = 2 := by
      rw [flattening_entry, sample_zero, one_mul, one_mul]
      simp [wordMatrix, sample_zero, List.ofFn_const, List.prod_replicate, Matrix.trace_one]
    have hnorm : m = (↑(∑ w, Complex.normSq (twoFlattening sample r (0, 0) w)) : ℂ) := by
      simp [G, m, rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.mul_conj, Complex.ofReal_sum]
    rw [hnorm]
    apply Complex.ofReal_ne_zero.mpr
    intro hz
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (w : Word (r + 2)) _ => Complex.normSq_nonneg (twoFlattening sample r (0, 0) w))).mp
      hz (fun _ => 0) (Finset.mem_univ _)
    rw [hword] at hz'
    norm_num [Complex.normSq_apply] at hz'
  have hk : H ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ H =
      Matrix.diagonal (fun i : Bits => H i.1 i.1 + H i.2 i.2) := by
    conv_lhs => rw [hdiag, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
      Matrix.diagonal_kronecker_diagonal]
    simp only [mul_one, one_mul]
    exact Matrix.diagonal_add (fun i : Bits => H i.1 i.1) (fun i : Bits => H i.2 i.2)
  change ((H ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ H) * G -
    G * (H ⊗ₖ (1 : Bond) + (1 : Bond) ⊗ₖ H)) (0, 0) (1, 1) ≠ 0
  simp only [hk, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change (H 0 0 + H 0 0) * G (0, 0) (1, 1) -
    G (0, 0) (1, 1) * (H 1 1 + H 1 1) ≠ 0
  rw [show (H 0 0 + H 0 0) * G (0, 0) (1, 1) -
    G (0, 0) (1, 1) * (H 1 1 + H 1 1) =
    2 * (H 0 0 - H 1 1) * G (0, 0) (1, 1) by ring, hdiff, h03]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hm))
    (mul_ne_zero (by norm_num) hm)

private lemma analytic_wordMatrix {n : ℕ} (w : Word n) (i j : Fin 2) (A : Fin 2 → Bond) :
    AnalyticAt ℝ (fun B : Fin 2 → Bond => wordMatrix B w i j) A := by
  induction n generalizing i j with
  | zero => simpa [wordMatrix, List.ofFn_zero] using
      (analyticAt_const (𝕜 := ℝ) (v := (1 : Bond) i j) (x := A))
  | succ n ih =>
    rw [← Fin.cons_self_tail w]
    simp only [wordMatrix_cons, Matrix.mul_apply]
    apply Finset.analyticAt_fun_sum
    intro k _
    exact ((entry i k).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Bond)
      (w 0))).analyticAt A |>.mul (ih (Fin.tail w) k j)

private lemma analytic_flattening (r : ℕ) (p : Bits) (w : Word (r + 2))
    (A : Fin 2 → Bond) : AnalyticAt ℝ (fun B : Fin 2 → Bond => twoFlattening B r p w) A := by
  change AnalyticAt ℝ (fun B => ∑ i : Fin 2, wordMatrix B (Fin.append ![p.1, p.2] w) i i) A
  exact Finset.analyticAt_fun_sum _ fun i _ => analytic_wordMatrix (Fin.append ![p.1, p.2] w) i i A

private lemma analytic_pair (r : ℕ) (p q : Bits) (A : Fin 2 → Bond) :
    AnalyticAt ℝ (fun B => rawTwo B r p q) A := by
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.analyticAt_fun_sum
  intro w _
  exact (analytic_flattening r p w A).mul
    ((Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (analytic_flattening r q w A))

private lemma analytic_defect (r : ℕ) (p q : Bits) (A : Fin 2 → Bond) :
    AnalyticAt ℝ (fun B => defect (rawTwo B r) p q) A := by
  have h (i j : Fin 2) : AnalyticAt ℝ (fun B => partialTraceRight (rawTwo B r) i j) A :=
    Finset.analyticAt_fun_sum _ fun k _ => analytic_pair r (i, k) (j, k) A
  have hk (i j : Bits) : AnalyticAt ℝ (fun B =>
      (partialTraceRight (rawTwo B r) ⊗ₖ (1 : Bond) +
        (1 : Bond) ⊗ₖ partialTraceRight (rawTwo B r)) i j) A := by
    simp only [Matrix.add_apply]
    exact ((h _ _).mul analyticAt_const).add (analyticAt_const.mul (h _ _))
  simp only [defect, Matrix.sub_apply, Matrix.mul_apply]
  exact (Finset.analyticAt_fun_sum _ fun k _ => (hk p k).mul (analytic_pair r k q A)).sub
    (Finset.analyticAt_fun_sum _ fun k _ => (analytic_pair r p k A).mul (hk k q))

private lemma dense_parameters (r : ℕ) : Dense {A : Fin 2 → Bond | defect (rawTwo A r) ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro V hV hne
  by_contra hmiss
  obtain ⟨A, hA⟩ := hne
  let f (B : Fin 2 → Bond) := defect (rawTwo B r) (0, 0) (1, 1)
  have hf : AnalyticOnNhd ℝ f univ := fun B _ => analytic_defect r _ _ B
  have hz : f =ᶠ[𝓝 A] 0 := by
    filter_upwards [hV.mem_nhds hA] with B hB
    have he : defect (rawTwo B r) = 0 := by
      by_contra hn
      exact hmiss ⟨B, hB, hn⟩
    simp [f, he]
  exact sample_defect r (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ A) hz (mem_univ sample))

/-- A density computed directly from the amplitudes, independent of their presentation. -/
def amplitudeTwo (r : ℕ) (ψ : Word (2 + (r + 2)) → ℂ) : TwoDensity :=
  let F : Matrix Bits (Word (r + 2)) ℂ := fun p w => ψ (Fin.append ![p.1, p.2] w)
  F * Fᴴ

private lemma continuous_amplitudeTwo (r : ℕ) : Continuous (amplitudeTwo r) := by
  let F (ψ : Word (2 + (r + 2)) → ℂ) : Matrix Bits (Word (r + 2)) ℂ :=
    fun p w => ψ (Fin.append ![p.1, p.2] w)
  have hF : Continuous F := continuous_matrix fun p w => continuous_apply (Fin.append ![p.1, p.2] w)
  exact hF.matrix_mul hF.matrix_conjTranspose

/-- The actual states with a nonzero commutator form a relatively open dense locus. -/
theorem actual_locus_open_dense (r : ℕ) :
    let X := Set.range (traceWord 2 2 (2 + (r + 2)))
    let G := {ψ : X | defect (amplitudeTwo r ψ.val) ≠ 0}
    G.Nonempty ∧ IsOpen G ∧ Dense G := by
  let F := traceWord 2 2 (2 + (r + 2))
  let X := Set.range F
  let f (A : Fin 2 → Bond) : X := ⟨F A, A, rfl⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    change Continuous (fun A : Fin 2 → Bond => ∑ i : Fin 2, wordMatrix A w i i)
    exact continuous_finsetSum _ fun i _ =>
      continuous_iff_continuousAt.mpr fun A => (analytic_wordMatrix w i i A).continuousAt
  have hg : Continuous (fun ψ : X => defect (amplitudeTwo r ψ.val)) := by
    have hG := (continuous_amplitudeTwo r).comp
      (continuous_subtype_val : Continuous (Subtype.val : X → _))
    have hH : Continuous (fun ψ : X => partialTraceRight (amplitudeTwo r ψ.val)) :=
      continuous_matrix fun i j => continuous_finsetSum _ fun k _ => hG.matrix_elem (i, k) (j, k)
    have hK : Continuous (fun ψ : X => partialTraceRight (amplitudeTwo r ψ.val) ⊗ₖ (1 : Bond) +
        (1 : Bond) ⊗ₖ partialTraceRight (amplitudeTwo r ψ.val)) :=
      continuous_matrix fun i j =>
        ((hH.matrix_elem i.1 j.1).mul continuous_const).add
          (continuous_const.mul (hH.matrix_elem i.2 j.2))
    exact (hK.matrix_mul hG).sub (hG.matrix_mul hK)
  have hs : defect (amplitudeTwo r (f sample).val) ≠ 0 := by
    intro he
    exact sample_defect r (congrArg (fun M : TwoDensity => M (0, 0) (1, 1)) he)
  refine ⟨⟨f sample, hs⟩, isOpen_ne_fun hg continuous_const, ?_⟩
  apply dense_iff_inter_open.mpr
  intro V hv hne
  obtain ⟨⟨_, A, rfl⟩, hA⟩ := hne
  obtain ⟨B, hB, hne⟩ := (dense_parameters r).inter_open_nonempty _ (hv.preimage hf) ⟨A, hA⟩
  exact ⟨f B, hB, hne⟩

private lemma amplitudeTwo_unitPhase (r : ℕ) (ψ : Word (2 + (r + 2)) → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) : amplitudeTwo r (c • ψ) = amplitudeTwo r ψ := by
  let F : Matrix Bits (Word (r + 2)) ℂ := fun p w => ψ (Fin.append ![p.1, p.2] w)
  have hz : c * star c = 1 := by
    change c * (starRingEnd ℂ) c = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  change (c • F) * (c • F)ᴴ = F * Fᴴ
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, one_smul]

/-- On a nonempty relatively open dense part of the actual periodic state image,
each state has arbitrarily nearby distinct unit-phase classes with the same one-site data.
The competitors lie on a continuous curve of shared-tensor periodic amplitudes. -/
theorem generic_one_site_ambiguity (r : ℕ) :
    let F := traceWord 2 2 (2 + (r + 2))
    let X := Set.range F
    ∃ G : Set X, G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      ∀ A, (⟨F A, A, rfl⟩ : X) ∈ G →
        ∃ B : ℝ → Fin 2 → Bond, Continuous B ∧ B 0 = A ∧
          (∀ t, rawOne (B t) r = rawOne A r) ∧
          ∃ᶠ t in 𝓝 (0 : ℝ), ∀ c : ℂ, ‖c‖ = 1 → F (B t) ≠ c • F A := by
  let F := traceWord 2 2 (2 + (r + 2))
  let X := Set.range F
  let G : Set X := {ψ | defect (amplitudeTwo r ψ.val) ≠ 0}
  obtain ⟨hne, hopen, hdense⟩ := actual_locus_open_dense r
  refine ⟨G, hne, hopen, hdense, ?_⟩
  intro A hA
  obtain ⟨B, hB, h0, hsame, hchange⟩ := arbitrarily_close_one_site_collisions A r hA
  refine ⟨B, hB, h0, hsame, ?_⟩
  have hf : ∃ᶠ t in 𝓝 (0 : ℝ), rawTwo (B t) r ≠ rawTwo A r := by
    simpa only [Filter.Frequently, Filter.EventuallyEq, not_not] using hchange
  refine hf.mono fun t ht c hc he => ht ?_
  change amplitudeTwo r (F (B t)) = amplitudeTwo r (F A)
  change F (B t) = c • F A at he
  rw [he, amplitudeTwo_unitPhase r _ c hc]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSOneSiteAmbiguity
