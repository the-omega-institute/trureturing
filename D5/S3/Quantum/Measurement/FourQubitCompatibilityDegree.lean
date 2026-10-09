/- GID: D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FourQubitCompatibilityDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The minimum four-qubit compatibility degree is exactly two over root thirteen. -/



/-
  compatDegree_nonneg: proof_shape: bind-only; escape_witness: none;
    consumer: optimalTuple_degree.
  le_compatDegree_of_feasible: proof_shape: bind-only; escape_witness: none;
    consumer: feasible_eq_Icc, optimalTuple_degree, minimum_attained.
  compatDegree_attained: proof_shape: bind-only; escape_witness: none;
    consumer: feasible_eq_Icc.
  feasible_eq_Icc: proof_shape: bind-only; escape_witness: none;
    consumer: optimalTuple_degree.
  optimalInactive is a private Prop predicate; proof_shape: bind-only;
    consumer: optimalParent, optimal_active_squared, optimalParent_posSemidef,
    optimalParent_sum, optimalParent_marginal.
  result: proof_shape: content; escape_witness: four_vector_inequality,
    all_povms_compatible on its live path. At the Stage A boundary, same-delivery
    declarations are inlined down to pinned Mathlib and baseline-frozen prerequisites.
    The terminal csInf application alone is bind-only.
  admission_basis: open-problem-resolution (#14687; Proved).
  Direct frozen dependencies:
    D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
      statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
    D5/S3/Combinatorics/IsingUniquenessSets.sgn
      statement_id: sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481
    D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
      statement_id: sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
  Same-delivery prerequisites: FourQubitParentConstruction and FourVectorSignSumBound.
  Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14767.
  Utility is none: the main content is the exact global compatibility minimum;
  finite parent and dual identities certify the attaining tuple inside that proof.
-/

import D5.S3.Quantum.Measurement.FourQubitParentConstruction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
open Matrix
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Geometry.FourVectorSignSumBound
open D5.S3.Quantum.Measurement.FourQubitParentConstruction

namespace D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree

def feasible (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : Set ℝ :=
  {s | s ∈ Set.Icc 0 1 ∧ Compatible4 (noisy s E)}
def compatDegree (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : ℝ := sSup (feasible E)
def povmTuples : Set (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ) := {E | ∀ i, IsPOVM (E i)}
def minCompatDegree : ℝ := sInf (compatDegree '' povmTuples)
private def uniformParent : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) := fun _ => (1 / 16 : ℝ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))
private def uniformTuple : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ) := fun _ _ => (1 / 2 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))
private theorem uniformParent_povm : IsPOVM uniformParent := by
  constructor
  · intro ε
    exact Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 16)
  · ext j k
    simp [uniformParent, Finset.sum_const, Matrix.smul_apply, Complex.real_smul, Matrix.one_apply]
private theorem uniformTuple_povm (i : Fin 4) : IsPOVM (uniformTuple i) := by
  constructor
  · intro b
    have hc : (0 : ℂ) ≤ 1 / 2 := by norm_num [Complex.le_def]
    exact Matrix.PosSemidef.one.smul hc
  · ext j k
    simp [uniformTuple, Matrix.smul_apply]
private theorem uniform_marginal (i : Fin 4) (b : Bool) :
    uniformTuple i b = ∑ ε with ε i = b, uniformParent ε := by
  have hc : (Finset.univ.filter (fun ε : (Fin 4 → Bool) => ε i = b)).card = 8 := by
    fin_cases i <;> cases b <;> decide
  ext j k
  simp [uniformParent, uniformTuple, Finset.sum_const, hc, Matrix.smul_apply,
    Complex.real_smul]
  ring
private theorem uniform_compatible : Compatible4 uniformTuple :=
  ⟨uniformTuple_povm, uniformParent, uniformParent_povm, uniform_marginal⟩
@[simp] private theorem noisy_zero (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : noisy 0 E = uniformTuple := by
  funext i b
  simp [noisy, uniformTuple]
private theorem zero_feasible (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : (0 : ℝ) ∈ feasible E := by
  exact ⟨by norm_num, by simpa using uniform_compatible⟩
private theorem feasible_nonempty (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : (feasible E).Nonempty := ⟨0, zero_feasible E⟩
private theorem feasible_bddAbove (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : BddAbove (feasible E) :=
  ⟨1, fun _ h => h.1.2⟩
private theorem compatDegree_nonneg (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : 0 ≤ compatDegree E :=
  le_csSup (feasible_bddAbove E) (zero_feasible E)
private theorem le_compatDegree_of_feasible {E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)} {s : ℝ} (h : s ∈ feasible E) :
    s ≤ compatDegree E :=
  le_csSup (feasible_bddAbove E) h
private theorem povm_isClosed {Ω : Type} [Fintype Ω] :
    IsClosed {A : Ω → (Matrix (Fin 2) (Fin 2) ℂ) | IsPOVM A} := by
  classical
  have hp : IsClosed {A : Ω → (Matrix (Fin 2) (Fin 2) ℂ) | ∀ a, 0 ≤ A a} := by
    convert isClosed_iInter (fun a : Ω =>
      isClosed_le (show Continuous (fun _ : Ω → (Matrix (Fin 2) (Fin 2) ℂ) => (0 : (Matrix (Fin 2) (Fin 2) ℂ))) from continuous_const) (continuous_apply a)) using 1
    ext A
    simp
  have hs : IsClosed {A : Ω → (Matrix (Fin 2) (Fin 2) ℂ) | ∑ a, A a = 1} :=
    isClosed_eq (continuous_finsetSum Finset.univ fun a _ => continuous_apply a) continuous_const
  convert hp.inter hs using 1
  ext A
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, IsPOVM,
    D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM,
    Matrix.nonneg_iff_posSemidef]
private theorem matrix_unit_interval_isCompact : IsCompact (Set.Icc (0 : (Matrix (Fin 2) (Fin 2) ℂ)) 1) := by
  apply (isCompact_closedBall (0 : (Matrix (Fin 2) (Fin 2) ℂ)) 1).of_isClosed_subset isClosed_Icc
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg A hA.1).2 hA.2
private theorem povm_effect_le_one {Ω : Type} [Fintype Ω] (J : Ω → (Matrix (Fin 2) (Fin 2) ℂ)) (hJ : IsPOVM J)
    (a : Ω) : J a ≤ 1 := by
  classical
  calc
    J a ≤ ∑ b, J b := Finset.single_le_sum (fun b _ => (hJ.1 b).nonneg) (Finset.mem_univ a)
    _ = 1 := hJ.2
private theorem parent_set_isCompact : IsCompact {J : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) | IsPOVM J} := by
  apply (isCompact_pi_infinite (fun _ : (Fin 4 → Bool) => matrix_unit_interval_isCompact)).of_isClosed_subset
    povm_isClosed
  intro J hJ ε
  exact ⟨(hJ.1 ε).nonneg, povm_effect_le_one J hJ ε⟩
private def parentFeasible (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : Set (ℝ × ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)) :=
  {p | p.1 ∈ Set.Icc 0 1 ∧ IsPOVM p.2 ∧
    ∀ i b, noisy p.1 E i b = ∑ ε with ε i = b, p.2 ε}
private theorem parentFeasible_isClosed (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : IsClosed (parentFeasible E) := by
  have hs : IsClosed {p : ℝ × ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) | p.1 ∈ Set.Icc 0 1} :=
    isClosed_Icc.preimage continuous_fst
  have hp : IsClosed {p : ℝ × ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) | IsPOVM p.2} :=
    povm_isClosed.preimage continuous_snd
  have hm : IsClosed {p : ℝ × ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) | ∀ i b,
      noisy p.1 E i b = ∑ ε with ε i = b, p.2 ε} := by
    convert isClosed_iInter (fun i : Fin 4 => isClosed_iInter (fun b : Bool =>
      isClosed_eq (show Continuous (fun p : ℝ × ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) => noisy p.1 E i b) by
        unfold noisy
        fun_prop)
      (continuous_finsetSum (Finset.univ.filter (fun ε : (Fin 4 → Bool) => ε i = b))
        (fun ε _ => (continuous_apply ε).comp continuous_snd)))) using 1
    ext p
    simp
  exact hs.inter (hp.inter hm)
private theorem parentFeasible_isCompact (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : IsCompact (parentFeasible E) := by
  apply (isCompact_Icc.prod parent_set_isCompact).of_isClosed_subset (parentFeasible_isClosed E)
  intro p hp
  exact ⟨hp.1, hp.2.1⟩
private theorem feasible_eq_image_parent (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) :
    feasible E = Prod.fst '' parentFeasible E := by
  ext s
  constructor
  · rintro ⟨hs, hE, J, hJ, hm⟩
    exact ⟨(s, J), ⟨hs, hJ, hm⟩, rfl⟩
  · rintro ⟨⟨t, J⟩, hp, rfl⟩
    exact ⟨hp.1, compatible_of_parent J hp.2.1 hp.2.2⟩
private theorem feasible_isCompact (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : IsCompact (feasible E) := by
  rw [feasible_eq_image_parent]
  exact (parentFeasible_isCompact E).image continuous_fst
private theorem compatDegree_attained (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) :
    compatDegree E ∈ Set.Icc (0 : ℝ) 1 ∧ Compatible4 (noisy (compatDegree E) E) :=
  (feasible_isCompact E).sSup_mem (feasible_nonempty E)
private theorem povm_mix {Ω : Type} [Fintype Ω] (A B : Ω → (Matrix (Fin 2) (Fin 2) ℂ))
    (hA : IsPOVM A) (hB : IsPOVM B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsPOVM (fun a => t • A a + (1 - t) • B a) := by
  constructor
  · intro a
    exact (hA.1 a).smul ht.1 |>.add ((hB.1 a).smul (sub_nonneg.mpr ht.2))
  · rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hA.2, hB.2,
      ← add_smul]
    simp
private theorem compatible_mix (E F : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (hE : Compatible4 E) (hF : Compatible4 F)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Compatible4 (fun i b => t • E i b + (1 - t) • F i b) := by
  obtain ⟨J, hJ, hmJ⟩ := hE.2
  obtain ⟨K, hK, hmK⟩ := hF.2
  apply compatible_of_parent (fun ε => t • J ε + (1 - t) • K ε)
    (povm_mix J K hJ hK t ht)
  intro i b
  rw [hmJ, hmK, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
private theorem noisy_mix_uniform (s t : ℝ) (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) :
    (fun i b => t • noisy s E i b + (1 - t) • uniformTuple i b) = noisy (t * s) E := by
  funext i b
  ext j k
  simp only [noisy, uniformTuple, Matrix.smul_apply, Matrix.add_apply, Complex.real_smul,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  ring
private theorem compatible_noisy_mul {s : ℝ} {E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)} (hs : Compatible4 (noisy s E))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Compatible4 (noisy (t * s) E) := by
  rw [← noisy_mix_uniform]
  exact compatible_mix (noisy s E) uniformTuple hs uniform_compatible t ht
private theorem feasible_downward {s t : ℝ} {E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)} (hs : s ∈ feasible E)
    (ht : 0 ≤ t) (hts : t ≤ s) : t ∈ feasible E := by
  by_cases hz : s = 0
  · have ht0 : t = 0 := le_antisymm (hz ▸ hts) ht
    simpa [ht0] using zero_feasible E
  · have hspos : 0 < s := lt_of_le_of_ne hs.1.1 (Ne.symm hz)
    have hratio : t / s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht hspos.le, (div_le_one hspos).2 hts⟩
    constructor
    · exact ⟨ht, hts.trans hs.1.2⟩
    · have h := compatible_noisy_mul hs.2 (t / s) hratio
      simpa [div_mul_cancel₀ t hz] using h
private theorem feasible_eq_Icc (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) : feasible E = Set.Icc 0 (compatDegree E) := by
  ext s
  constructor
  · intro h
    exact ⟨h.1.1, le_compatDegree_of_feasible h⟩
  · intro h
    exact feasible_downward (compatDegree_attained E) h.1 h.2


private def optimum : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[3,0,0], !₂[-3/2,3*Real.sqrt 3/2,0], !₂[-3/2,-3*Real.sqrt 3/2,0], !₂[0,0,4]]

private theorem optimum_norms (i : Fin 4) : ‖optimum i‖ = ![3,3,3,4] i := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := norm_nonneg (optimum i)
  fin_cases i
  · have hsq : ‖optimum 0‖^2 = 9 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [optimum, Fin.sum_univ_succ]
      <;> nlinarith [hs]
    have hsq2 : ‖optimum 0‖^2 = (3:ℝ)^2 := by nlinarith only [hsq]
    exact (sq_eq_sq₀ (norm_nonneg (optimum 0)) (by norm_num : (0:ℝ) ≤ 3)).mp hsq2
  · have hsq : ‖optimum 1‖^2 = 9 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [optimum, Fin.sum_univ_succ]
      <;> nlinarith [hs]
    have hsq2 : ‖optimum 1‖^2 = (3:ℝ)^2 := by nlinarith only [hsq]
    exact (sq_eq_sq₀ (norm_nonneg (optimum 1)) (by norm_num : (0:ℝ) ≤ 3)).mp hsq2
  · have hsq : ‖optimum 2‖^2 = 9 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [optimum, Fin.sum_univ_succ]
      <;> nlinarith [hs]
    have hsq2 : ‖optimum 2‖^2 = (3:ℝ)^2 := by nlinarith only [hsq]
    exact (sq_eq_sq₀ (norm_nonneg (optimum 2)) (by norm_num : (0:ℝ) ≤ 3)).mp hsq2
  · have hsq : ‖optimum 3‖^2 = 16 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [optimum, Fin.sum_univ_succ]
      <;> nlinarith [hs]
    have hsq2 : ‖optimum 3‖^2 = (4:ℝ)^2 := by nlinarith only [hsq]
    exact (sq_eq_sq₀ (norm_nonneg (optimum 3)) (by norm_num : (0:ℝ) ≤ 4)).mp hsq2

private theorem optimum_sum : (∑ i, ‖optimum i‖) = 13 := by
  norm_num [optimum_norms, Fin.sum_univ_succ]

private theorem optimum_signed_squared_bound (ε : Fin 4 → Bool) : ‖signedSum optimum ε‖^2 ≤ 52 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3 <;>
    rw [EuclideanSpace.real_norm_sq_eq] <;>
    simp [signedSum, optimum, Fin.sum_univ_succ, sgn, h0, h1, h2, h3] <;>
    nlinarith [hs]

private theorem optimum_signed_attained : ‖signedSum optimum ![true,true,false,true]‖^2 = 52 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [signedSum, optimum, Fin.sum_univ_succ, sgn]
  nlinarith [hs]

private theorem optimum_max : maxNorm optimum = Real.sqrt 52 := by
  have hs : (Real.sqrt 52)^2 = 52 := Real.sq_sqrt (by norm_num)
  have hp := Real.sqrt_nonneg 52
  apply le_antisymm
  · apply Finset.sup'_le
    intro ε _
    have h := optimum_signed_squared_bound ε
    have hn := norm_nonneg (signedSum optimum ε)
    nlinarith
  · have h := signedSum_le_max optimum ![true,true,false,true]
    have he := optimum_signed_attained
    have hn := norm_nonneg (signedSum optimum ![true,true,false,true])
    nlinarith

def claim : Prop := minCompatDegree = 2 / Real.sqrt 13

private theorem signed_marginal (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (J : (Fin 4 → Bool) → (Matrix (Fin 2) (Fin 2) ℂ))
    (hm : ∀ i b, E i b = ∑ ε with ε i = b, J ε) (i : Fin 4) :
    (∑ ε, sgn (ε i) • J ε) = E i true - E i false := by
  classical
  rw [hm i true, hm i false]
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ε _
  cases h : ε i <;> simp [sgn, h]

private theorem compatible_trace_bound (E : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ)) (F : Fin 4 → (Matrix (Fin 2) (Fin 2) ℂ)) (Y : (Matrix (Fin 2) (Fin 2) ℂ))
    (hcert : ∀ ε : Fin 4 → Bool, (Y - ∑ i, sgn (ε i) • F i).PosSemidef)
    (hc : Compatible4 E) :
    (∑ i, (F i * (E i true - E i false)).trace.re) ≤ Y.trace.re := by
  classical
  rcases hc.2 with ⟨J,hJ,hm⟩
  have hp : 0 ≤ ∑ ε, ((Y - ∑ i, sgn (ε i) • F i) * J ε).trace.re := by
    apply Finset.sum_nonneg
    intro ε _
    exact RHLinalg.trace_mul_nonneg_of_posSemidef (hcert ε) (hJ.1 ε)
  have hpair : (∑ ε, ((Y - ∑ i, sgn (ε i) • F i) * J ε).trace.re) =
      Y.trace.re - ∑ i, (F i * (E i true - E i false)).trace.re := by
    simp only [Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_sub, Matrix.trace_sum,
      Complex.sub_re, Complex.re_sum, Finset.sum_sub_distrib]
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hJ.2, Matrix.mul_one]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Complex.re_sum, ← Matrix.trace_sum]
    congr 1
    rw [← signed_marginal E J hm i, Matrix.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [hpair] at hp
  linarith

private def optimalTuple : (Fin 4 → Bool → Matrix (Fin 2) (Fin 2) ℂ) := fun i b =>
  (1 / 2 : ℂ) • scalarB 1 (sgn b • (NormedSpace.normalize (optimum i)))

private def dualY : (Matrix (Fin 2) (Fin 2) ℂ) := (Real.sqrt 52 : ℂ) • (1 : (Matrix (Fin 2) (Fin 2) ℂ))

private theorem optimum_norm_pos (i : Fin 4) : 0 < ‖optimum i‖ := by
  rw [optimum_norms]
  fin_cases i <;> norm_num

private theorem optimalDirection_norm (i : Fin 4) : ‖(NormedSpace.normalize (optimum i))‖ = 1 :=
  NormedSpace.norm_normalize (norm_ne_zero_iff.mp (optimum_norm_pos i).ne')

private theorem optimalTuple_povm (i : Fin 4) : IsPOVM (optimalTuple i) := by
  constructor
  · intro b
    apply (half_scalarB_posSemidef_iff _ _).mpr
    cases b <;> simp [sgn, optimalDirection_norm]
  · ext j k
    fin_cases j <;> fin_cases k <;>
      simp [optimalTuple, scalarB, sgn, B_neg, B_formula,
      Matrix.smul_apply, Complex.real_smul]
      <;> ring

private theorem noisy_optimal_difference (s : ℝ) (i : Fin 4) :
    noisy s optimalTuple i true - noisy s optimalTuple i false = s • B ((NormedSpace.normalize (optimum i))) := by
  ext j k
  simp [noisy, optimalTuple, scalarB, sgn, B_neg,
    Matrix.smul_apply, Complex.real_smul]
  ring

private theorem dual_certificate (ε : (Fin 4 → Bool)) :
    (dualY - ∑ i, sgn (ε i) • B (optimum i)).PosSemidef := by
  have he : dualY - ∑ i, sgn (ε i) • B (optimum i) =
      scalarB (Real.sqrt 52) (-signedSum optimum ε) := by
    simp only [dualY,scalarB,B_neg,signedSum,B_sum,B_real_smul]
    rfl
  rw [he,scalarB_posSemidef_iff,norm_neg]
  rw [← optimum_max]
  exact signedSum_le_max _ _

private theorem optimum_direction_inner (i : Fin 4) :
    inner ℝ (optimum i) ((NormedSpace.normalize (optimum i))) = ‖optimum i‖ := by
  rw [NormedSpace.normalize,inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp [(optimum_norm_pos i).ne']

private theorem dual_value (s : ℝ) :
    (∑ i, (B (optimum i) * (noisy s optimalTuple i true - noisy s optimalTuple i false)).trace.re) = 26 * s := by
  have ht (i : Fin 4) :
      (B (optimum i) * (noisy s optimalTuple i true - noisy s optimalTuple i false)).trace.re =
        2 * s * ‖optimum i‖ := by
    rw [noisy_optimal_difference, Matrix.mul_smul, Matrix.trace_smul, trace_B_mul]
    simp [Complex.real_smul, optimum_direction_inner]
    ring
  simp_rw [ht]
  rw [← Finset.mul_sum, optimum_sum]
  ring

private theorem sqrt52_eq : Real.sqrt 52 = 2 * Real.sqrt 13 := by
  have h13 := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have h52 := Real.sq_sqrt (show (0 : ℝ) ≤ 52 by norm_num)
  nlinarith [Real.sqrt_nonneg 13, Real.sqrt_nonneg 52]

private theorem dualY_trace : dualY.trace.re = 4 * Real.sqrt 13 := by
  have hs := sqrt52_eq
  simp [dualY, Matrix.trace_smul, Matrix.trace_one,hs]
  ring

private theorem compatible_optimal_upper (s : ℝ) (hc : Compatible4 (noisy s optimalTuple)) :
    s ≤ endpoint := by
  have h := compatible_trace_bound (noisy s optimalTuple) (fun i => B (optimum i)) dualY dual_certificate hc
  rw [dual_value,dualY_trace] at h
  have hs : 0 < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 13)^2 = 13 := Real.sq_sqrt (by norm_num)
  apply (le_div_iff₀ hs).mpr
  have hm := mul_le_mul_of_nonneg_right h hs.le
  nlinarith [hs2]

private abbrev optimalInactive (ε : (Fin 4 → Bool)) : Prop := ε 0 = ε 1 ∧ ε 1 = ε 2

private def optimalParent : ((Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) := fun ε =>
  if optimalInactive ε then 0 else
    (1 / 12 : ℂ) • scalarB 1 ((Real.sqrt 52)⁻¹ • signedSum optimum ε)


private theorem sum_cons {A : Type*} [AddCommMonoid A] {n : ℕ}
    (f : (Fin (n + 1) → Bool) → A) :
    ∑ ε, f ε = ∑ b : Bool, ∑ ε : Fin n → Bool, f (Matrix.vecCons b ε) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)),
    Fintype.sum_prod_type]
  rfl

private theorem optimal_active_squared (ε : (Fin 4 → Bool)) (hε : ¬ optimalInactive ε) :
    ‖signedSum optimum ε‖ ^ 2 = 52 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3 <;>
    simp [optimalInactive, h0, h1, h2] at hε <;>
    rw [norm_sq_coords] <;>
    simp [signedSum, optimum, Fin.sum_univ_succ,
      sgn, h0, h1, h2, h3] <;> nlinarith [hs]

private theorem optimal_active_norm (ε : (Fin 4 → Bool)) (hε : ¬ optimalInactive ε) :
    ‖signedSum optimum ε‖ = Real.sqrt 52 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [optimal_active_squared ε hε, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 52)]

private theorem optimalParent_posSemidef (ε : (Fin 4 → Bool)) : (optimalParent ε).PosSemidef := by
  by_cases hi : optimalInactive ε
  · rw [optimalParent, if_pos hi]
    exact Matrix.PosSemidef.zero
  · rw [optimalParent, if_neg hi]
    apply ((scalarB_posSemidef_iff _ _).mpr ?_).smul
      (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 12)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg 52)),
      optimal_active_norm ε hi]
    exact le_of_eq (inv_mul_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne')

private theorem optimalParent_sum : ∑ ε, optimalParent ε = 1 := by

  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [sum_cons, Fintype.sum_bool, Fintype.sum_unique, optimalParent, optimalInactive, scalarB, B_formula,
      signedSum, optimum, sgn, Fin.sum_univ_succ,
      Matrix.smul_apply, Matrix.add_apply, Complex.real_smul] <;> ring

private theorem optimalParent_povm : IsPOVM optimalParent :=
  ⟨optimalParent_posSemidef, optimalParent_sum⟩

private theorem optimalParent_marginal (i : Fin 4) (b : Bool) :
    noisy endpoint optimalTuple i b = ∑ ε with ε i = b, optimalParent ε := by

  have hn : Real.sqrt 13 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 13)).ne'
  simp only [noisy, optimalTuple, NormedSpace.normalize, optimum_norms]
  rw [Finset.sum_filter]
  ext j k
  fin_cases i <;> cases b <;> fin_cases j <;> fin_cases k <;>
    simp [sum_cons, Fintype.sum_bool, Fintype.sum_unique, optimalParent, optimalInactive, endpoint, scalarB, B_formula,
      signedSum, optimum, sgn, Fin.sum_univ_succ,
      Matrix.smul_apply, Matrix.add_apply, Complex.real_smul, sqrt52_eq] <;>
    field_simp [hn] <;> ring

private theorem optimal_endpoint_compatible : Compatible4 (noisy endpoint optimalTuple) :=
  compatible_of_parent optimalParent optimalParent_povm optimalParent_marginal

private theorem optimalTuple_degree : compatDegree optimalTuple = endpoint := by
  exact le_antisymm
    (compatible_optimal_upper _ (show Compatible4 (noisy (compatDegree optimalTuple) optimalTuple) from
      (show compatDegree optimalTuple ∈ feasible optimalTuple from
        (feasible_eq_Icc optimalTuple).symm ▸
          ⟨compatDegree_nonneg optimalTuple, le_rfl⟩).2))
    (le_compatDegree_of_feasible ⟨endpoint_mem_Icc, optimal_endpoint_compatible⟩)

private theorem minimum_attained : IsLeast (compatDegree '' povmTuples) endpoint := by
  refine ⟨⟨optimalTuple, optimalTuple_povm, optimalTuple_degree⟩, ?_⟩
  rintro d ⟨E, hE, rfl⟩
  exact le_compatDegree_of_feasible ⟨endpoint_mem_Icc, all_povms_compatible E hE⟩

theorem result : claim := minimum_attained.csInf_eq

end D5.S3.Quantum.Measurement.FourQubitCompatibilityDegree
