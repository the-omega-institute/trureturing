/- GID: D5/S3/Quantum/Decoherence/ExactQubitBathErasure
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/ExactQubitBathErasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact reset feasibility and minimal heat for retained qubit records with a Gibbs qubit bath. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.PureState.PureStateHandshake

/-!
# Exact retained-record erasure with a qubit bath

The record coordinates are ordered by the eigenvalues of the retained state.
The bath coordinates are ordered by energy, ground first. Partial traces use the
convention of `PartialTraceMutualInformation`.
-/

namespace ExactQubitBathErasure

open Matrix Complex Unitary
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

abbrev Qubit := Fin 2
abbrev TwoQubits := Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ

/-- A Hermitian idempotent of trace two. -/
abbrev IsRankTwoProjection (P : TwoQubits) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.trace = 2

private lemma projection_diagonal_bounds {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P * P = P) (i : n) :
    0 ≤ (P i i).re ∧ (P i i).re ≤ 1 := by
  have hpos : P.PosSemidef := by
    simpa only [hP.eq, hPP] using posSemidef_conjTranspose_mul_self P
  have hneg : (1 - P).PosSemidef := by
    have hinv : (1 - P)ᴴ = 1 - P := by simp [hP.eq]
    have hsq : (1 - P) * (1 - P) = 1 - P := by
      simp [sub_mul, mul_sub, hPP]
    have h := posSemidef_conjTranspose_mul_self (1 - P : Matrix n n ℂ)
    rwa [hinv, hsq] at h
  exact ⟨(Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1,
    by
      have h := (Complex.nonneg_iff.mp (hneg.diag_nonneg (i := i))).1
      simpa only [Matrix.sub_apply, one_apply_eq, sub_re, one_re, sub_nonneg] using h⟩

/-- The projector onto the first coordinate of a qubit. -/
def first : Matrix Qubit Qubit ℂ := diagonal ![1, 0]

/-- The sum of the two lifted first-coordinate projections. -/
def firstSum : TwoQubits := first ⊗ₖ 1 + 1 ⊗ₖ first

lemma trace_firstSum (P : TwoQubits) :
    (P * firstSum).trace = partialTraceRight P 0 0 + partialTraceLeft P 0 0 := by
  simp [firstSum, first, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, partialTraceRight, partialTraceLeft]
  ring

/-- For any projection of trace two, the sum of the two selected marginal
populations is at most three. The bath coordinate can be the ground state or any
chosen unit vector by using a basis containing that vector. -/
theorem trace_mul_firstSum_le_three {P : TwoQubits} (hP : IsRankTwoProjection P) :
    ((P * firstSum).trace).re ≤ 3 := by
  rw [trace_firstSum, add_re]
  have htr := congrArg Complex.re hP.2.2
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    add_re] at htr
  norm_num at htr
  have h00 := (projection_diagonal_bounds hP.1 hP.2.1 (0, 0)).2
  have h11 := (projection_diagonal_bounds hP.1 hP.2.1 (1, 1)).1
  simp only [partialTraceRight, partialTraceLeft, Fin.sum_univ_two, add_re]
  linarith

/-- The spanning vector orthogonal to `|00⟩` in the optimal projection. -/
noncomputable def boundaryVector (a : ℝ) (ij : Qubit × Qubit) : ℂ :=
  (![![0, (Real.sqrt a : ℂ)], ![(Real.sqrt (1 - a) : ℂ), 0]] :
    Qubit → Qubit → ℂ) ij.1 ij.2

/-- Orthogonal projection onto `span {|00⟩, √a |01⟩ + √(1-a) |10⟩}` for `0 ≤ a ≤ 1`. -/
noncomputable def boundaryProjection (a : ℝ) : TwoQubits :=
  rankOneDensity (Pi.single (0, 0) 1) + rankOneDensity (boundaryVector a)

theorem boundaryProjection_spec {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    IsRankTwoProjection (boundaryProjection a) ∧
      partialTraceRight (boundaryProjection a) = diagonal ![(1 + a : ℂ), 1 - a] ∧
      partialTraceLeft (boundaryProjection a) = diagonal ![(2 - a : ℂ), a] := by
  have hs : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = a := by
    exact_mod_cast (Real.mul_self_sqrt ha)
  have ht : (Real.sqrt (1 - a) : ℂ) * (Real.sqrt (1 - a) : ℂ) = 1 - a := by
    exact_mod_cast (Real.mul_self_sqrt (sub_nonneg.mpr ha'))
  have hm : partialTraceRight (boundaryProjection a) = diagonal ![(1 + a : ℂ), 1 - a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partialTraceRight, boundaryProjection, boundaryVector, rankOneDensity,
        Fin.sum_univ_two, hs, ht, Pi.single_apply, vecMulVec_apply, Pi.star_apply,
        Complex.conj_ofReal]
  refine ⟨⟨?_, ?_, ?_⟩, hm, ?_⟩
  · change (boundaryProjection a)ᴴ = boundaryProjection a
    simp [boundaryProjection, rankOneDensity, conjTranspose_vecMulVec]
  · have hdot : star (boundaryVector a) ⬝ᵥ boundaryVector a = 1 := by
      simp [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, boundaryVector, hs, ht]
    simp [boundaryProjection, rankOneDensity, add_mul, mul_add, vecMulVec_mul_vecMulVec,
      dotProduct_single, single_dotProduct, boundaryVector, hdot]
  · rw [← trace_partialTraceRight, hm, trace_diagonal, Fin.sum_univ_two]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partialTraceLeft, boundaryProjection, boundaryVector, rankOneDensity,
        Fin.sum_univ_two, hs, ht, Pi.single_apply, vecMulVec_apply, Pi.star_apply,
        Complex.conj_ofReal]
    ring

/-- A diagonal qubit state, with population imbalance `u` in favor of coordinate zero. -/
noncomputable def biasedQubit (u : ℝ) : Matrix Qubit Qubit ℂ :=
  diagonal ![(1 + (u : ℂ)) / 2, (1 - (u : ℂ)) / 2]

/-- An EB state with the doubled thermal spectrum when `P` is a rank-two projection. -/
noncomputable def thermalSpectrumState (r : ℝ) (P : TwoQubits) : TwoQubits :=
  ((1 - (r : ℂ)) / 4) • 1 + ((r : ℂ) / 2) • P

private lemma marginal_record (r : ℝ) (P : TwoQubits) :
    partialTraceRight (thermalSpectrumState r P) =
      ((1 - (r : ℂ)) / 2) • 1 + ((r : ℂ) / 2) • partialTraceRight P := by
  ext i j
  simp [partialTraceRight, thermalSpectrumState, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, one_apply, smul_eq_mul]
  split <;> simp_all <;> ring

private lemma marginal_bath (r : ℝ) (P : TwoQubits) :
    partialTraceLeft (thermalSpectrumState r P) =
      ((1 - (r : ℂ)) / 2) • 1 + ((r : ℂ) / 2) • partialTraceLeft P := by
  ext i j
  simp [partialTraceLeft, thermalSpectrumState, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.smul_apply, one_apply, smul_eq_mul]
  split <;> simp_all <;> ring

private lemma trace_thermalSpectrumState {P : TwoQubits} (hP : IsRankTwoProjection P) (r : ℝ) :
    (thermalSpectrumState r P).trace = 1 := by
  simp [thermalSpectrumState, trace_add, trace_smul, trace_one, hP.2.2,
    Fintype.card_prod]

/-- Bath Hamiltonian expectation increase, with energy zero at coordinate zero. -/
noncomputable def bathHeat (Δ r : ℝ) (ρ : TwoQubits) : ℝ :=
  Δ * ((partialTraceLeft ρ 1 1).re - (1 - r) / 2)

theorem projection_feasibility_and_heat_bound {r s Δ : ℝ} (hr : 0 ≤ r) (hΔ : 0 ≤ Δ)
    {P : TwoQubits} (hP : IsRankTwoProjection P)
    (hret : partialTraceRight (thermalSpectrumState r P) = biasedQubit s) :
    s ≤ r ∧ Δ * s / 2 ≤ bathHeat Δ r (thermalSpectrumState r P) := by
  have he : (1 - r) / 2 + r / 2 * (partialTraceRight P 0 0).re = (1 + s) / 2 := by
    have hv := congrArg (fun A : Matrix Qubit Qubit ℂ => (A 0 0).re) hret
    rw [marginal_record] at hv
    simpa [Matrix.add_apply, Matrix.smul_apply, biasedQubit, Complex.div_re,
      Complex.mul_re] using hv
  have hE : (partialTraceRight P 0 0).re ≤ 2 := by
    simp only [partialTraceRight, Fin.sum_univ_two, add_re]
    linarith [(projection_diagonal_bounds hP.1 hP.2.1 (0, 0)).2,
      (projection_diagonal_bounds hP.1 hP.2.1 (0, 1)).2]
  have hpop : (partialTraceRight P 0 0).re + (partialTraceLeft P 0 0).re ≤ 3 := by
    simpa [trace_firstSum, add_re] using trace_mul_firstSum_le_three hP
  have hb : (partialTraceLeft (thermalSpectrumState r P) 0 0).re =
      (1 - r) / 2 + r / 2 * (partialTraceLeft P 0 0).re := by
    simp [marginal_bath, Matrix.add_apply, Matrix.smul_apply, Complex.mul_re]
  have htotal : (partialTraceLeft (thermalSpectrumState r P) 0 0).re +
      (partialTraceLeft (thermalSpectrumState r P) 1 1).re = 1 := by
    have ht := congrArg Complex.re (trace_thermalSpectrumState hP r)
    rwa [← trace_partialTraceLeft, trace, Fin.sum_univ_two, diag_apply, diag_apply,
      add_re, one_re] at ht
  have hg := mul_le_mul_of_nonneg_left hpop (show 0 ≤ r / 2 by positivity)
  have hp := mul_le_mul_of_nonneg_left hE (show 0 ≤ r / 2 by positivity)
  refine ⟨by linarith, ?_⟩
  have hex : s / 2 ≤ (partialTraceLeft (thermalSpectrumState r P) 1 1).re - (1 - r) / 2 :=
    by linarith
  simpa only [bathHeat, mul_div_assoc] using mul_le_mul_of_nonneg_left hex hΔ

theorem boundaryState_marginals {a r : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    partialTraceRight (thermalSpectrumState r (boundaryProjection a)) = biasedQubit (r * a) ∧
    partialTraceLeft (thermalSpectrumState r (boundaryProjection a)) = biasedQubit (r - r * a) := by
  obtain ⟨_, hE, hB⟩ := boundaryProjection_spec ha ha'
  constructor
  · rw [marginal_record, hE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [biasedQubit, Matrix.add_apply, Matrix.smul_apply] <;> ring
  · rw [marginal_bath, hB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [biasedQubit, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem projection_heat_attained {r s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (Δ : ℝ) :
    ∃ P : TwoQubits, IsRankTwoProjection P ∧
      partialTraceRight (thermalSpectrumState r P) = biasedQubit s ∧
      partialTraceLeft (thermalSpectrumState r P) = biasedQubit (r - s) ∧
      bathHeat Δ r (thermalSpectrumState r P) = Δ * s / 2 := by
  have hr := hs.trans hsr
  have ha : 0 ≤ s / r := div_nonneg hs hr
  have ha' : s / r ≤ 1 := div_le_one_of_le₀ hsr hr
  have hrs : r * (s / r) = s := by
    by_cases h : r = 0
    · have : s = 0 := le_antisymm (h ▸ hsr) hs
      simp [h, this]
    · field_simp
  obtain ⟨hE, hB⟩ := boundaryState_marginals (r := r) ha ha'
  rw [hrs] at hE hB
  refine ⟨boundaryProjection (s / r), (boundaryProjection_spec ha ha').1, hE, hB, ?_⟩
  rw [bathHeat, hB]
  simp [biasedQubit]
  ring

section UnitaryOrbit

private lemma exists_unitary_of_charpoly_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) :
    ∃ U : unitary (Matrix n n ℂ), conjStarAlgAut ℂ _ U A = B := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h
  refine ⟨hB.eigenvectorUnitary * star hA.eigenvectorUnitary, ?_⟩
  rw [conjStarAlgAut_mul_apply, hA.conjStarAlgAut_star_eigenvectorUnitary, he, ← hB.spectral_theorem]

private lemma projection_eigenvalues {P : TwoQubits} (hP : IsRankTwoProjection P) :
    hP.1.eigenvalues₀ = (![1, 1, 0, 0] : Fin 4 → ℝ) := by
  let e : Fin 4 ≃ Qubit × Qubit := Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (i : Fin 4) : hP.1.eigenvalues (e i) = hP.1.eigenvalues₀ i := by
    change hP.1.eigenvalues₀ (e.symm (e i)) = _
    rw [Equiv.symm_apply_apply]
  have h01 (i : Fin 4) : hP.1.eigenvalues₀ i = 0 ∨ hP.1.eigenvalues₀ i = 1 := by
    let φ := conjStarAlgAut ℂ TwoQubits (star hP.1.eigenvectorUnitary)
    have hp := congrArg φ hP.2.1
    change φ (P * P) = φ P at hp
    rw [map_mul, show φ P = diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) from
      hP.1.conjStarAlgAut_star_eigenvectorUnitary, diagonal_mul_diagonal] at hp
    have hi := congrArg (fun A : TwoQubits => A (e i) (e i)) hp
    simp only [diagonal_apply_eq, Function.comp_apply, he] at hi
    exact eq_zero_or_one_of_sq_eq_self
      (by simpa [pow_two] using congrArg Complex.re hi)
  have ht : ∑ i : Fin 4, hP.1.eigenvalues₀ i = 2 := by
    have hs := e.sum_comp (fun i => (hP.1.eigenvalues i : ℂ))
    simp only [he] at hs
    have hsum := hs.trans hP.1.trace_eq_sum_eigenvalues.symm |>.trans hP.2.2
    simpa using congrArg Complex.re hsum
  let x (i : Fin 4) := hP.1.eigenvalues₀ i
  change x = _
  have hsum : x 0 + x 1 + x 2 + x 3 = 2 := by
    change (∑ i : Fin 4, x i) = 2 at ht
    simpa only [Fin.sum_univ_four, add_assoc] using ht
  have h10 : x 1 ≤ x 0 := hP.1.eigenvalues₀_antitone (by decide)
  have h21 : x 2 ≤ x 1 := hP.1.eigenvalues₀_antitone (by decide)
  have h32 : x 3 ≤ x 2 := hP.1.eigenvalues₀_antitone (by decide)
  have bounds (i : Fin 4) : 0 ≤ x i ∧ x i ≤ 1 := by
    rcases h01 i with h | h
    all_goals change x i = _ at h; simp [h]
  have h1 : x 1 = 1 := by
    rcases h01 1 with h | h
    · change x 1 = 0 at h
      linarith [(bounds 0).2]
    · exact h
  have h2 : x 2 = 0 := by
    rcases h01 2 with h | h
    · exact h
    · change x 2 = 1 at h
      linarith [(bounds 3).1]
  have h0 : x 0 = 1 := by linarith [(bounds 0).2]
  have h3 : x 3 = 0 := by linarith [(bounds 3).1]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private lemma same_projection_orbit {P T : TwoQubits}
    (hP : IsRankTwoProjection P) (hT : IsRankTwoProjection T) :
    ∃ U : unitary TwoQubits, conjStarAlgAut ℂ _ U T = P := by
  apply exists_unitary_of_charpoly_eq hT.1 hP.1
  apply (hT.1.eigenvalues_eq_eigenvalues_iff hP.1).mp
  funext i
  exact congrFun ((projection_eigenvalues hT).trans (projection_eigenvalues hP).symm)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- The high-population bath sector. The other factor indexes the two input branches. -/
def highSector : TwoQubits := 1 ⊗ₖ first

private lemma highSector_spec : IsRankTwoProjection highSector := by
  have hfirst : first.IsHermitian := by
    change firstᴴ = first
    ext i j
    fin_cases i <;> fin_cases j <;> simp [first, conjTranspose_apply]
  have hsq : first * first = first := by
    rw [first, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  refine ⟨?_, ?_, ?_⟩
  · change highSectorᴴ = highSector
    simp [highSector, conjTranspose_kronecker, hfirst.eq]
  · simp [highSector, ← mul_kronecker_mul, hsq]
  · norm_num [highSector, trace_kronecker, first, Fin.sum_univ_two, trace_one]

private lemma conjugate_projection {P : TwoQubits} (hP : IsRankTwoProjection P)
    (U : unitary TwoQubits) : IsRankTwoProjection (conjStarAlgAut ℂ _ U P) := by
  let φ := conjStarAlgAut ℂ TwoQubits U
  refine ⟨?_, by rw [← map_mul, hP.2.1], ?_⟩
  · change star (φ P) = φ P
    rw [← map_star]
    exact congrArg φ hP.1.eq
  · rw [conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, hP.2.2]

/-- The branch-by-bath spectrum, with input probabilities `1/2` on the two branches. -/
noncomputable def supportedInput (r : ℝ) : TwoQubits := thermalSpectrumState r highSector

theorem supportedInput_eq (r : ℝ) :
    supportedInput r = (1 / 2 : ℂ) • ((1 : Matrix Qubit Qubit ℂ) ⊗ₖ biasedQubit r) := by
  ext ⟨i, b⟩ ⟨j, c⟩
  fin_cases b <;> fin_cases c <;>
    by_cases h : i = j <;>
    simp [supportedInput, thermalSpectrumState, highSector, first, biasedQubit,
      Matrix.smul_apply, Matrix.add_apply, h] <;> ring

private lemma conjugate_thermalSpectrumState (r : ℝ) (P : TwoQubits) (U : unitary TwoQubits) :
    conjStarAlgAut ℂ _ U (thermalSpectrumState r P) =
      thermalSpectrumState r (conjStarAlgAut ℂ _ U P) := by
  simp only [thermalSpectrumState, map_add, map_smul, map_one]

/-- Exactly the supported EB states reachable from the doubled bath spectrum by a unitary. -/
theorem supported_unitary_orbit_iff (r : ℝ) (ρ : TwoQubits) :
    (∃ U : unitary TwoQubits, conjStarAlgAut ℂ _ U (supportedInput r) = ρ) ↔
    ∃ P : TwoQubits, IsRankTwoProjection P ∧ thermalSpectrumState r P = ρ := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨_, conjugate_projection highSector_spec U, ?_⟩
    rw [← conjugate_thermalSpectrumState, ← supportedInput, hU]
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨U, hU⟩ := same_projection_orbit hP highSector_spec
    exact ⟨U, by rw [supportedInput, conjugate_thermalSpectrumState, hU]⟩

/-- For the doubled thermal spectrum the exact record constraint is feasible iff `s ≤ r`.
Whenever feasible, `Δ * s / 2` is the attained minimum bath heat. -/
theorem supported_erasure_threshold_and_minimum {r s Δ : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) :
    ((∃ U : unitary TwoQubits,
      partialTraceRight (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit s) ↔ s ≤ r) ∧
    (∀ U : unitary TwoQubits,
      partialTraceRight (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit s →
        Δ * s / 2 ≤ bathHeat Δ r (conjStarAlgAut ℂ _ U (supportedInput r))) ∧
    (s ≤ r → ∃ U : unitary TwoQubits,
      partialTraceRight (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit s ∧
      partialTraceLeft (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit (r - s) ∧
      bathHeat Δ r (conjStarAlgAut ℂ _ U (supportedInput r)) = Δ * s / 2) := by
  have hlower (U : unitary TwoQubits) (hU :
      partialTraceRight (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit s) :=
    projection_feasibility_and_heat_bound hr hΔ
      (conjugate_projection highSector_spec U) (by
        simpa only [supportedInput, conjugate_thermalSpectrumState] using hU)
  have hattain (hle : s ≤ r) : ∃ U : unitary TwoQubits,
      partialTraceRight (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit s ∧
      partialTraceLeft (conjStarAlgAut ℂ _ U (supportedInput r)) = biasedQubit (r - s) ∧
      bathHeat Δ r (conjStarAlgAut ℂ _ U (supportedInput r)) = Δ * s / 2 := by
    obtain ⟨P, hP, hE, hB, hQ⟩ := projection_heat_attained hs hle Δ
    obtain ⟨U, hU⟩ := (supported_unitary_orbit_iff r _).mpr ⟨P, hP, rfl⟩
    exact ⟨U, hU.symm ▸ hE, hU.symm ▸ hB, hU.symm ▸ hQ⟩
  refine ⟨⟨?_, ?_⟩, ?_, hattain⟩
  · rintro ⟨U, hU⟩
    exact (hlower U hU).1
  · intro hle
    obtain ⟨U, hU, _, _⟩ := hattain hle
    exact ⟨U, hU⟩
  · intro U hU
    simpa only [supportedInput, conjugate_thermalSpectrumState] using (hlower U hU).2

end UnitaryOrbit

section LocalBasis

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private def tensorUnitary (U : unitary (Matrix A A ℂ)) (V : unitary (Matrix B B ℂ)) :
    unitary (Matrix (A × B) (A × B) ℂ) :=
  ⟨U.val ⊗ₖ V.val, Matrix.kronecker_mem_unitary U.property V.property⟩

private lemma conjugate_kronecker (U : unitary (Matrix A A ℂ)) (V : unitary (Matrix B B ℂ))
    (X : Matrix A A ℂ) (Y : Matrix B B ℂ) :
    conjStarAlgAut ℂ (Matrix (A × B) (A × B) ℂ) (tensorUnitary U V) (X ⊗ₖ Y) =
      conjStarAlgAut ℂ (Matrix A A ℂ) U X ⊗ₖ conjStarAlgAut ℂ (Matrix B B ℂ) V Y := by
  simp only [conjStarAlgAut_apply, tensorUnitary, star_eq_conjTranspose,
    conjTranspose_kronecker, ← mul_kronecker_mul]

private lemma trace_adjoint {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (X Y : Matrix n n ℂ) :
    (conjStarAlgAut ℂ _ U X * Y).trace =
      (X * conjStarAlgAut ℂ _ (star U) Y).trace := by
  simp only [conjStarAlgAut_apply, coe_star, star_star, Matrix.mul_assoc]
  rw [trace_mul_comm (U : Matrix n n ℂ)]
  simp only [Matrix.mul_assoc]

/-- The same bound for any two local first-coordinate projections in independent
orthonormal bases. The two unitaries can send coordinate zero to any unit vector. -/
theorem trace_mul_local_projections_le_three {P : TwoQubits} (hP : IsRankTwoProjection P)
    (U V : unitary (Matrix Qubit Qubit ℂ)) :
    ((P * (conjStarAlgAut ℂ _ U first ⊗ₖ 1 +
      1 ⊗ₖ conjStarAlgAut ℂ _ V first)).trace).re ≤ 3 := by
  let W := tensorUnitary U V
  have h : (conjStarAlgAut ℂ _ W firstSum) =
      conjStarAlgAut ℂ _ U first ⊗ₖ 1 + 1 ⊗ₖ conjStarAlgAut ℂ _ V first := by
    simp only [firstSum, map_add, W, conjugate_kronecker, map_one]
  have hadj := trace_adjoint (star W) P firstSum
  rw [star_star] at hadj
  rw [← h, ← hadj]
  exact trace_mul_firstSum_le_three (conjugate_projection hP (star W))

omit [DecidableEq A] in
private lemma record_trace_embed_mul (C : Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight ((C ⊗ₖ (1 : Matrix B B ℂ)) * ρ) = C * partialTraceRight ρ := by
  ext i j
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

omit [DecidableEq A] in
private lemma record_trace_mul_embed (C : Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (ρ * (C ⊗ₖ (1 : Matrix B B ℂ))) = partialTraceRight ρ * C := by
  ext i j
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

omit [DecidableEq A] in
private lemma bath_trace_embed_comm (C : Matrix A A ℂ) (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft ((C ⊗ₖ (1 : Matrix B B ℂ)) * ρ) =
      partialTraceLeft (ρ * (C ⊗ₖ (1 : Matrix B B ℂ))) := by
  ext i j
  simp only [partialTraceLeft, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [mul_comm]

private lemma local_record (C : unitary (Matrix A A ℂ)) (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (conjStarAlgAut ℂ (Matrix (A × B) (A × B) ℂ) (tensorUnitary C (1 : unitary (Matrix B B ℂ))) ρ) =
      conjStarAlgAut ℂ (Matrix A A ℂ) C (partialTraceRight ρ) := by
  simp only [conjStarAlgAut_apply, tensorUnitary, Submonoid.coe_one, star_eq_conjTranspose,
    conjTranspose_kronecker, conjTranspose_one, record_trace_mul_embed, record_trace_embed_mul]

private lemma local_bath (C : unitary (Matrix A A ℂ)) (ρ : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (conjStarAlgAut ℂ (Matrix (A × B) (A × B) ℂ) (tensorUnitary C (1 : unitary (Matrix B B ℂ))) ρ) =
      partialTraceLeft ρ := by
  simp only [conjStarAlgAut_apply, tensorUnitary, Submonoid.coe_one, star_eq_conjTranspose,
    conjTranspose_kronecker, conjTranspose_one]
  rw [Matrix.mul_assoc, bath_trace_embed_comm, Matrix.mul_assoc,
    ← mul_kronecker_mul, Matrix.one_mul, ← star_eq_conjTranspose, coe_star_mul_self,
    one_kronecker_one, Matrix.mul_one]

end LocalBasis

section FullUnitary

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev Total (E : Type*) := Matrix (Qubit × (E × Qubit)) (Qubit × (E × Qubit)) ℂ

/-- The two classical branches, each embedded with its own pure record. -/
def recordEmbedding (v : Qubit → E → ℂ) : Matrix (Qubit × (E × Qubit)) (Qubit × Qubit) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.2 = j.2 then v j.1 i.2.1 else 0

omit [DecidableEq E] in
private lemma recordEmbedding_isometry (v : Qubit → E → ℂ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    (recordEmbedding v)ᴴ * recordEmbedding v = 1 := by
  ext ⟨x, b⟩ ⟨y, c⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, recordEmbedding, Fintype.sum_prod_type]
  by_cases h : (x, b) = (y, c)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    fin_cases x <;> fin_cases b <;>
      simpa [Fin.sum_univ_two, dotProduct, Pi.star_apply] using hv _
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro z _
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro d _
    split_ifs with h₁ h₂ h₂
    · exact (h (Prod.ext (h₁.1.symm.trans h₂.1) (h₁.2.symm.trans h₂.2))).elim
    all_goals simp

/-- The physical input on XEB, written as the weighted sum of the four
orthogonal branch-and-bath projectors. -/
noncomputable def initialRecords (v : Qubit → E → ℂ) (r : ℝ) : Total E :=
  recordEmbedding v * supportedInput r * (recordEmbedding v)ᴴ

/-- The fair mixture of the two record vectors. -/
noncomputable def recordMixture (v : Qubit → E → ℂ) : Matrix E E ℂ :=
  (1 / 2 : ℂ) • (rankOneDensity (v 0) + rankOneDensity (v 1))

private lemma supportedInput_diagonal (r : ℝ) :
    supportedInput r = diagonal (fun p : Qubit × Qubit => biasedQubit r p.2 p.2 / 2) := by
  rw [supportedInput_eq]
  ext ⟨x, b⟩ ⟨y, c⟩
  by_cases hxy : x = y <;> by_cases hbc : b = c
  all_goals simp [biasedQubit, Matrix.diagonal, hxy, hbc,
    Matrix.smul_apply, Prod.ext_iff]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The input is classical in X and has the independent Gibbs bath diagonal. -/
theorem initialRecords_apply (v : Qubit → E → ℂ) (r : ℝ)
    (x y b c : Qubit) (i j : E) :
    initialRecords v r (x, i, b) (y, j, c) =
      if x = y ∧ b = c then (biasedQubit r b b / 2) * rankOneDensity (v x) i j else 0 := by
  rw [initialRecords, supportedInput_diagonal, Matrix.mul_apply]
  simp_rw [mul_diagonal, recordEmbedding, conjTranspose_apply]
  by_cases hxy : x = y
  · subst y
    by_cases hbc : b = c
    · subst c
      fin_cases x <;> fin_cases b <;>
        simp [Fin.sum_univ_two, Fintype.sum_prod_type, rankOneDensity, vecMulVec_apply,
          Pi.star_apply, recordEmbedding] <;> ring
    · rw [ite_eq_right (fun h => hbc h.2)]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : x = p.1 ∧ b = p.2
      · have hne : c ≠ p.2 := fun h => hbc (hp.2.trans h.symm)
        simp [hp, recordEmbedding, hne]
      · simp [hp]
  · rw [ite_eq_right (fun h => hxy h.1)]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : x = p.1 ∧ b = p.2
    · have hne : y ≠ p.1 := fun h => hxy (hp.1.trans h.symm)
      simp [hp, recordEmbedding, hne]
    · simp [hp]

private lemma biasedQubit_hermitian (r : ℝ) : (biasedQubit r).IsHermitian := by
  change (biasedQubit r)ᴴ = biasedQubit r
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [biasedQubit, conjTranspose_apply, Complex.conj_ofReal]

private lemma biasedQubit_psd {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (biasedQubit r).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i
  · change 0 ≤ (1 + (r : ℂ)) / 2
    exact_mod_cast (show 0 ≤ (1 + r) / 2 by linarith)
  · change 0 ≤ (1 - (r : ℂ)) / 2
    exact_mod_cast (show 0 ≤ (1 - r) / 2 by linarith)

private lemma supportedInput_psd {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (supportedInput r).PosSemidef := by
  rw [supportedInput_eq]
  apply (Matrix.PosSemidef.one.kronecker (biasedQubit_psd hr hr')).smul
  exact Complex.nonneg_iff.mpr (by norm_num [Complex.div_re, Complex.div_im])

private lemma conjugate_psd {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (conjStarAlgAut ℂ _ U A).PosSemidef := by
  rw [conjStarAlgAut_apply, star_eq_conjTranspose]
  simpa only [conjTranspose_conjTranspose] using
    hA.conjTranspose_mul_mul_same (U : Matrix n n ℂ)ᴴ

private lemma padding_charpoly {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (J : Matrix n m ℂ) (hJ : Jᴴ * J = 1)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hB : J * A * Jᴴ = B) :
    Polynomial.X ^ Fintype.card m * B.charpoly =
      Polynomial.X ^ Fintype.card n * A.charpoly := by
  subst B
  simpa [← Matrix.mul_assoc, hJ] using charpoly_mul_comm' (J * A) Jᴴ

private lemma padding_hermitian {n m : Type*} [Fintype n] [Fintype m]
    (J : Matrix n m ℂ) {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    (J * A * Jᴴ).IsHermitian := by
  change (J * A * Jᴴ)ᴴ = J * A * Jᴴ
  simp [conjTranspose_mul, hA.eq, Matrix.mul_assoc]

private def resetEmbedding : Matrix (Qubit × (Qubit × Qubit)) (Qubit × Qubit) ℂ :=
  fun i j => if i.1 = 0 ∧ i.2 = j then 1 else 0

private lemma resetEmbedding_isometry : resetEmbeddingᴴ * resetEmbedding = 1 := by
  ext ⟨i, b⟩ ⟨j, c⟩
  fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
    simp [resetEmbedding, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]

private lemma resetEmbedding_eq (ρ : TwoQubits) :
    resetEmbedding * ρ * resetEmbeddingᴴ = first ⊗ₖ ρ := by
  ext ⟨x, i⟩ ⟨y, j⟩
  fin_cases x <;> fin_cases y <;>
    simp [resetEmbedding, Matrix.mul_apply, conjTranspose_apply, first, Matrix.diagonal,
      Matrix.kroneckerMap_apply]
/-- Equality of the full XEB and supported EB orbit conditions for a reset state.
Both isometric embeddings use the same four-dimensional spectrum and add the same zeros. -/
theorem reset_unitary_orbit_iff (v : Qubit → Qubit → ℂ) (r : ℝ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) {ρ : TwoQubits} (hρ : ρ.IsHermitian) :
    (∃ U : unitary (Total Qubit), conjStarAlgAut ℂ _ U (initialRecords v r) = first ⊗ₖ ρ) ↔
    (∃ U : unitary TwoQubits, conjStarAlgAut ℂ _ U (supportedInput r) = ρ) := by
  have hS : (supportedInput r).IsHermitian := by
    rw [supportedInput_eq]
    apply Matrix.IsHermitian.smul
    · exact isHermitian_kronecker isHermitian_one (biasedQubit_hermitian r)
    · change star (1 / 2 : ℂ) = 1 / 2
      simp
  have hI : (initialRecords v r).IsHermitian := padding_hermitian _ hS
  have hR : (first ⊗ₖ ρ).IsHermitian := by
    rw [← resetEmbedding_eq]
    exact padding_hermitian _ hρ
  have hin := padding_charpoly (recordEmbedding v) (recordEmbedding_isometry v hv)
    (supportedInput r) (initialRecords v r) rfl
  have hout := padding_charpoly resetEmbedding resetEmbedding_isometry ρ
    (first ⊗ₖ ρ) (resetEmbedding_eq ρ)
  constructor
  · rintro ⟨U, hU⟩
    have h := charpoly_conj_unitary (ρ := initialRecords v r) (coe_star_mul_self U)
    change (conjStarAlgAut ℂ (Total Qubit) U (initialRecords v r)).charpoly = _ at h
    rw [hU] at h
    rw [← h, hout] at hin
    have heq := hin
    exact exists_unitary_of_charpoly_eq hS hρ
      (mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) heq.symm)
  · rintro ⟨U, hU⟩
    have h := charpoly_conj_unitary (ρ := supportedInput r) (coe_star_mul_self U)
    change (conjStarAlgAut ℂ TwoQubits U (supportedInput r)).charpoly = _ at h
    rw [hU] at h
    rw [← h, ← hout] at hin
    exact exists_unitary_of_charpoly_eq hI hR
      (mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) hin)

private lemma first_trace : first.trace = 1 := by
  simp [first, Fin.sum_univ_two]

/-- A positive joint state whose first qubit has the prescribed pure marginal
is the tensor product of that pure state with its remaining marginal. -/
theorem pure_reset_factors {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix (Qubit × n) (Qubit × n) ℂ} (hA : A.PosSemidef)
    (hreset : partialTraceRight A = first) :
    A = first ⊗ₖ partialTraceLeft A := by
  have hdiag : ∑ i : n, A (1, i) (1, i) = 0 := by
    simpa [partialTraceRight, first] using congrArg (fun M : Matrix Qubit Qubit ℂ => M 1 1) hreset
  have hzero (i : n) : A (1, i) (1, i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hA.diag_nonneg (i := (1, j)))).mp
      hdiag i (Finset.mem_univ i)
  have hcol (i : n) (j : Qubit × n) : A j (1, i) = 0 := by
    have hx : star (Pi.single (1, i) 1) ⬝ᵥ (A *ᵥ Pi.single (1, i) 1) = 0 := by
      simpa using hzero i
    have hv := hA.dotProduct_mulVec_zero_iff.mp hx
    simpa using congrFun hv j
  have hrow (i : n) (j : Qubit × n) : A (1, i) j = 0 := by
    have h := congrArg (fun M : Matrix (Qubit × n) (Qubit × n) ℂ => M (1, i) j) hA.isHermitian.eq
    simpa [conjTranspose_apply, hcol] using h.symm
  ext ⟨x, i⟩ ⟨y, j⟩
  fin_cases x <;> fin_cases y <;>
    simp [first, partialTraceLeft, Fin.sum_univ_two, hcol, hrow]

omit [DecidableEq E] in
private lemma initialRecords_psd {v : Qubit → E → ℂ} {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) :
    (initialRecords v r).PosSemidef := by
  simpa only [initialRecords, conjTranspose_conjTranspose] using
    (supportedInput_psd hr hr').conjTranspose_mul_mul_same (recordEmbedding v)ᴴ

/-- The retained record after tracing out the bath. -/
noncomputable def retainedRecord (A : Total Qubit) : Matrix Qubit Qubit ℂ :=
  partialTraceRight (partialTraceLeft A)

theorem retainedRecord_initial (v : Qubit → Qubit → ℂ) (r : ℝ) :
    retainedRecord (initialRecords v r) = recordMixture v := by
  ext i j
  simp only [retainedRecord, partialTraceRight, partialTraceLeft, initialRecords_apply,
    Fin.sum_univ_two, ↓reduceIte, and_self, biasedQubit, diagonal_apply_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, recordMixture, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_apply]
  ring

/-- Exact erasure of X to a prescribed state, with the record marginal retained. -/
def ErasesTo (v : Qubit → Qubit → ℂ) (target : Matrix Qubit Qubit ℂ) (A : Total Qubit) : Prop :=
  partialTraceRight A = target ∧ retainedRecord A = recordMixture v

abbrev Erases (v : Qubit → Qubit → ℂ) (A : Total Qubit) : Prop := ErasesTo v first A

/-- Full one-unitary threshold and attained minimum with the fair record mixture
given by its unitary diagonalization. -/
theorem erasure_of_record_diagonalization {r s Δ : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hs : 0 ≤ s)
    (hΔ : 0 ≤ Δ) (v : Qubit → Qubit → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (C : unitary (Matrix Qubit Qubit ℂ))
    (hrecord : conjStarAlgAut ℂ _ C (biasedQubit s) = recordMixture v) :
    let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
    ((∃ U, Erases v (final U)) ↔ s ≤ r) ∧
      (∀ U, Erases v (final U) → Δ * s / 2 ≤ bathHeat Δ r (partialTraceLeft (final U))) ∧
      (s ≤ r → ∃ U, Erases v (final U) ∧
        partialTraceLeft (partialTraceLeft (final U)) = biasedQubit (r - s) ∧
        bathHeat Δ r (partialTraceLeft (final U)) = Δ * s / 2) := by
  dsimp only
  let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
  obtain ⟨hfeas, hlower, hattain⟩ := supported_erasure_threshold_and_minimum hr hs hΔ
  let rotate (D : unitary (Matrix Qubit Qubit ℂ)) :=
    tensorUnitary D (1 : unitary (Matrix Qubit Qubit ℂ))
  have hinv : conjStarAlgAut ℂ _ (star C) (recordMixture v) = biasedQubit s := by
    rw [← conjStarAlgAut_symm, hrecord.symm, StarAlgEquiv.symm_apply_apply]
  have hforward (U : unitary (Total Qubit)) (hU : Erases v (final U)) :
      ∃ W : unitary TwoQubits,
        partialTraceRight (conjStarAlgAut ℂ _ W (supportedInput r)) = biasedQubit s ∧
        partialTraceLeft (conjStarAlgAut ℂ _ W (supportedInput r)) =
          partialTraceLeft (partialTraceLeft (final U)) := by
    have hpos := conjugate_psd U (initialRecords_psd (v := v) hr hr')
    have hρ := (partialTraceLeft_posSemidef hpos).isHermitian
    obtain ⟨W, hW⟩ := (reset_unitary_orbit_iff v r hv hρ).mp ⟨U, pure_reset_factors hpos hU.1⟩
    refine ⟨rotate (star C) * W, ?_, ?_⟩
    · rw [conjStarAlgAut_mul_apply, hW, local_record, ← retainedRecord, hU.2, hinv]
    · rw [conjStarAlgAut_mul_apply, hW, local_bath]
  have hwitness (hle : s ≤ r) : ∃ U : unitary (Total Qubit), Erases v (final U) ∧
      partialTraceLeft (partialTraceLeft (final U)) = biasedQubit (r - s) ∧
      bathHeat Δ r (partialTraceLeft (final U)) = Δ * s / 2 := by
    obtain ⟨W, hE, hB, hQ⟩ := hattain hle
    let V := rotate C * W
    let ρ := conjStarAlgAut ℂ TwoQubits V (supportedInput r)
    have hρE : partialTraceRight ρ = recordMixture v := by
      dsimp only [ρ, V, rotate]
      rw [conjStarAlgAut_mul_apply, local_record, hE, hrecord]
    have hρB : partialTraceLeft ρ = biasedQubit (r - s) := by
      dsimp only [ρ, V, rotate]
      rw [conjStarAlgAut_mul_apply, local_bath, hB]
    have hρ := (conjugate_psd V (supportedInput_psd hr hr')).isHermitian
    obtain ⟨U, hU⟩ := (reset_unitary_orbit_iff v r hv hρ).mpr ⟨V, rfl⟩
    change final U = first ⊗ₖ ρ at hU
    have hρtr : ρ.trace = 1 := by
      obtain ⟨P, hP, hPρ⟩ := (supported_unitary_orbit_iff r ρ).mp ⟨V, rfl⟩
      rw [← hPρ, trace_thermalSpectrumState hP]
    have hreset : partialTraceRight (final U) = first := by
      rw [hU]
      change partialTraceRight (Matrix.kronecker first ρ) = first
      rw [partialTraceRight_kronecker, hρtr, one_smul]
    have hrest : partialTraceLeft (final U) = ρ := by
      rw [hU]
      change partialTraceLeft (Matrix.kronecker first ρ) = ρ
      rw [partialTraceLeft_kronecker, first_trace, one_smul]
    refine ⟨U, ⟨hreset, ?_⟩, ?_, ?_⟩
    · simpa only [retainedRecord, hrest] using hρE
    · rw [hrest, hρB]
    · rw [hrest, bathHeat, hρB]
      rwa [bathHeat, hB] at hQ
  refine ⟨⟨?_, ?_⟩, ?_, hwitness⟩
  · rintro ⟨U, hU⟩
    obtain ⟨W, hW, _⟩ := hforward U hU
    exact hfeas.mp ⟨W, hW⟩
  · intro hle
    obtain ⟨U, hU, _, _⟩ := hwitness hle
    exact ⟨U, hU⟩
  · intro U hU
    obtain ⟨W, hW, hB⟩ := hforward U hU
    simpa only [bathHeat, hB] using hlower W hW

/-- Absolute inner product of the two pure-record amplitudes. -/
noncomputable def recordOverlap (v : Qubit → E → ℂ) : ℝ :=
  ‖star (v 0) ⬝ᵥ v 1‖

private def recordColumns (v : Qubit → E → ℂ) : Matrix E Qubit ℂ :=
  fun i x => v x i

omit [Fintype E] [DecidableEq E] in
private lemma recordMixture_eq (v : Qubit → E → ℂ) :
    recordMixture v = ((1 / 2 : ℂ) • recordColumns v) * (recordColumns v)ᴴ := by
  ext i j
  simp [recordMixture, recordColumns, rankOneDensity, Matrix.mul_apply, Matrix.smul_apply,
    conjTranspose_apply, Fin.sum_univ_two, vecMulVec_apply, Pi.star_apply]
  ring

omit [DecidableEq E] in
private lemma gram_charpoly (v : Qubit → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    ((recordColumns v)ᴴ * ((1 / 2 : ℂ) • recordColumns v)).charpoly =
      (biasedQubit (recordOverlap v)).charpoly := by
  let z := star (v 0) ⬝ᵥ v 1
  have hz : star (v 1) ⬝ᵥ v 0 = star z := by
    exact star_dotProduct (v 1) (v 0)
  have hentry (x y : Qubit) :
      ((recordColumns v)ᴴ * ((1 / 2 : ℂ) • recordColumns v)) x y =
        (star (v x) ⬝ᵥ v y) / 2 := by
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      recordColumns, dotProduct, Pi.star_apply, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  have ht : ((recordColumns v)ᴴ * ((1 / 2 : ℂ) • recordColumns v)).trace =
      (biasedQubit (recordOverlap v)).trace := by
    rw [Matrix.trace, Fin.sum_univ_two, diag_apply, diag_apply, hentry, hentry, hv, hv]
    simp [Matrix.trace, Fin.sum_univ_two, biasedQubit]
    ring
  have hd : ((recordColumns v)ᴴ * ((1 / 2 : ℂ) • recordColumns v)).det =
      (biasedQubit (recordOverlap v)).det := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hentry, hentry, hentry, hentry, hv, hv, hz]
    change (1 / 2 : ℂ) * (1 / 2) - z / 2 * ((starRingEnd ℂ) z / 2) = _
    have hs : z * (starRingEnd ℂ) z = ((recordOverlap v : ℝ) : ℂ) ^ 2 := by
      change z * (starRingEnd ℂ) z = (↑‖z‖ : ℂ) ^ 2
      exact Complex.mul_conj' z
    simp [biasedQubit]
    calc
      _ = (1 - z * (starRingEnd ℂ) z) / 4 := by ring
      _ = _ := by rw [hs]; ring
  rw [ht, hd]

/-- For the fair pure-record mixture on a qubit, the two eigenvalues are
`(1 ± |⟨v₀,v₁⟩|)/2`, expressed as a unitary diagonalization. -/
theorem recordMixture_diagonalization (v : Qubit → Qubit → ℂ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    ∃ C : unitary (Matrix Qubit Qubit ℂ),
      conjStarAlgAut ℂ _ C (biasedQubit (recordOverlap v)) = recordMixture v := by
  have hM : (recordMixture v).IsHermitian := by
    rw [recordMixture_eq]
    change (((1 / 2 : ℂ) • recordColumns v) * (recordColumns v)ᴴ)ᴴ = _
    simp [conjTranspose_mul, conjTranspose_smul]
  apply exists_unitary_of_charpoly_eq (biasedQubit_hermitian _) hM
  rw [recordMixture_eq, Matrix.charpoly_mul_comm, gram_charpoly v hv]

/-- For arbitrary normalized pure qubit records, a single unitary on XEB
erases X while retaining E iff the overlap is at most the thermal bias.
Every feasible erasure has bath heat at least `Δ * s / 2`, and a single
unitary attains it with a diagonal bath of bias `r - s`. -/
theorem erasure_threshold_and_minimum {r Δ : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (hΔ : 0 < Δ)
    (v : Qubit → Qubit → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    let s := recordOverlap v
    let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
    ((∃ U, Erases v (final U)) ↔ s ≤ r) ∧
      (∀ U, Erases v (final U) → Δ * s / 2 ≤ bathHeat Δ r (partialTraceLeft (final U))) ∧
      (s ≤ r → ∃ U, Erases v (final U) ∧
        partialTraceLeft (partialTraceLeft (final U)) = biasedQubit (r - s) ∧
        bathHeat Δ r (partialTraceLeft (final U)) = Δ * s / 2) := by
  obtain ⟨C, hC⟩ := recordMixture_diagonalization v hv
  exact erasure_of_record_diagonalization hr hr'.le (norm_nonneg _) hΔ.le v hv C hC

private lemma pureReset_diagonalization (χ : Qubit → ℂ) (hχ : star χ ⬝ᵥ χ = 1) :
    ∃ D : unitary (Matrix Qubit Qubit ℂ), conjStarAlgAut ℂ _ D first = rankOneDensity χ := by
  have hfirst : first.IsHermitian := by
    change firstᴴ = first
    ext i j
    fin_cases i <;> fin_cases j <;> simp [first, conjTranspose_apply]
  have hp : (rankOneDensity χ).IsHermitian := by
    change (rankOneDensity χ)ᴴ = rankOneDensity χ
    simp [rankOneDensity, conjTranspose_vecMulVec]
  apply exists_unitary_of_charpoly_eq hfirst hp
  rw [rankOneDensity, charpoly_vecMulVec, dotProduct_comm χ _, hχ]
  simp [first, charpoly_diagonal, Fin.prod_univ_two]
  ring

set_option maxHeartbeats 500000 in
/-- Exact erasure to any prescribed pure state of X. -/
theorem erasure_to_pure_state {r Δ : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (hΔ : 0 < Δ)
    (v : Qubit → Qubit → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (χ : Qubit → ℂ) (hχ : star χ ⬝ᵥ χ = 1) :
    let s := recordOverlap v
    let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
    let erases := ErasesTo v (rankOneDensity χ)
    ((∃ U, erases (final U)) ↔ s ≤ r) ∧
      (∀ U, erases (final U) → Δ * s / 2 ≤ bathHeat Δ r (partialTraceLeft (final U))) ∧
      (s ≤ r → ∃ U, erases (final U) ∧
        partialTraceLeft (partialTraceLeft (final U)) = biasedQubit (r - s) ∧
        bathHeat Δ r (partialTraceLeft (final U)) = Δ * s / 2) := by
  obtain ⟨D, hD⟩ := pureReset_diagonalization χ hχ
  obtain ⟨hfeas, hlower, hattain⟩ := erasure_threshold_and_minimum hr hr' hΔ v hv
  let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
  let rotate (C : unitary (Matrix Qubit Qubit ℂ)) :=
    tensorUnitary C (1 : unitary TwoQubits)
  have hleft (C : unitary (Matrix Qubit Qubit ℂ)) (U : unitary (Total Qubit)) :
      partialTraceLeft (final (rotate C * U)) = partialTraceLeft (final U) := by
    dsimp only [final, rotate]
    rw [conjStarAlgAut_mul_apply, local_bath]
  have hright (C : unitary (Matrix Qubit Qubit ℂ)) (U : unitary (Total Qubit)) :
      partialTraceRight (final (rotate C * U)) =
        conjStarAlgAut ℂ _ C (partialTraceRight (final U)) := by
    dsimp only [final, rotate]
    rw [conjStarAlgAut_mul_apply, local_record]
  have hundo (U : unitary (Total Qubit)) (hU : ErasesTo v (rankOneDensity χ) (final U)) :
      Erases v (final (rotate (star D) * U)) := by
    constructor
    · rw [hright, hU.1, ← hD, ← conjStarAlgAut_symm, StarAlgEquiv.symm_apply_apply]
    · simpa only [retainedRecord, hleft] using hU.2
  have hdo (U : unitary (Total Qubit)) (hU : Erases v (final U)) :
      ErasesTo v (rankOneDensity χ) (final (rotate D * U)) := by
    constructor
    · rw [hright, hU.1, hD]
    · simpa only [retainedRecord, hleft] using hU.2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨U, hU⟩
    exact hfeas.mp ⟨rotate (star D) * U, hundo U hU⟩
  · intro hs
    obtain ⟨U, hU, _, _⟩ := hattain hs
    have herase := hdo U hU
    exact ⟨rotate D * U, herase⟩
  · intro U hU
    have h := hlower (rotate (star D) * U) (hundo U hU)
    change Δ * recordOverlap v / 2 ≤ bathHeat Δ r (partialTraceLeft (final (rotate (star D) * U))) at h
    rwa [hleft] at h
  · intro hs
    obtain ⟨U, hU, hB, hQ⟩ := hattain hs
    have herase := hdo U hU
    have hbath : partialTraceLeft (partialTraceLeft (final (rotate D * U))) =
        biasedQubit (r - recordOverlap v) := by rw [hleft]; exact hB
    have hheat : bathHeat Δ r (partialTraceLeft (final (rotate D * U))) =
        Δ * recordOverlap v / 2 := by rw [hleft]; exact hQ
    exact ⟨rotate D * U, herase, hbath, hheat⟩

end FullUnitary

/-- The normalized Gibbs state of a qubit with energies zero and `Δ`, in its energy basis. -/
noncomputable def qubitGibbs (β Δ : ℝ) : Matrix Qubit Qubit ℂ :=
  let z := Real.exp (-(β * Δ))
  diagonal ![((1 / (1 + z) : ℝ) : ℂ), ((z / (1 + z) : ℝ) : ℂ)]

theorem qubitGibbs_eq (β Δ : ℝ) :
    qubitGibbs β Δ = biasedQubit (Real.tanh (β * Δ / 2)) := by
  let x := β * Δ / 2
  let z := Real.exp (-(β * Δ))
  have hp : 0 < Real.exp x := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  have hm : Real.exp (-x) = Real.exp x * z := by
    rw [show Real.exp x * z = Real.exp (x + -(β * Δ)) by rw [Real.exp_add]]
    congr 1
    dsimp [x]
    ring
  have ht : Real.tanh x = (1 - z) / (1 + z) := by
    rw [Real.tanh_eq, hm, ← mul_one_sub, ← mul_one_add, mul_div_mul_left _ _ hp.ne']
  change diagonal (![((1 / (1 + z) : ℝ) : ℂ), ((z / (1 + z) : ℝ) : ℂ)] : Qubit → ℂ) =
    diagonal ![(1 + (Real.tanh x : ℂ)) / 2, (1 - (Real.tanh x : ℂ)) / 2]
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i
  · change ((1 / (1 + z) : ℝ) : ℂ) = (1 + (Real.tanh x : ℂ)) / 2
    rw [ht]
    push_cast
    have hdenom : (1 + (z : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + z ≠ 0 by positivity)
    field_simp
    ring
  · change ((z / (1 + z) : ℝ) : ℂ) = (1 - (Real.tanh x : ℂ)) / 2
    rw [ht]
    push_cast
    have hdenom : (1 + (z : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + z ≠ 0 by positivity)
    field_simp
    ring

/-- Heat is the change of the expectation of the bath Hamiltonian. -/
theorem bathHeat_eq_energy_change (Δ r : ℝ) (ρ : TwoQubits) :
    bathHeat Δ r ρ =
      let H : Matrix Qubit Qubit ℂ := diagonal ![0, (Δ : ℂ)]
      (H * partialTraceLeft ρ).trace.re - (H * biasedQubit r).trace.re := by
  simp [bathHeat, Matrix.trace, Fin.sum_univ_two, diagonal_mul, biasedQubit, mul_re]
  ring

/-- The Gibbs-qubit erasure threshold and sharp heat at finite nonnegative
inverse temperature, for a qubit record and an arbitrary pure reset state. -/
theorem gibbs_erasure_threshold_and_minimum {β Δ : ℝ} (hβ : 0 ≤ β) (hΔ : 0 < Δ)
    (v : Qubit → Qubit → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (χ : Qubit → ℂ) (hχ : star χ ⬝ᵥ χ = 1) :
    let r := Real.tanh (β * Δ / 2)
    let s := recordOverlap v
    let final (U : unitary (Total Qubit)) := conjStarAlgAut ℂ _ U (initialRecords v r)
    let erases := ErasesTo v (rankOneDensity χ)
    ((∃ U, erases (final U)) ↔ s ≤ r) ∧
      (∀ U, erases (final U) → Δ * s / 2 ≤ bathHeat Δ r (partialTraceLeft (final U))) ∧
      (s ≤ r → ∃ U, erases (final U) ∧
        partialTraceLeft (partialTraceLeft (final U)) = biasedQubit (r - s) ∧
        bathHeat Δ r (partialTraceLeft (final U)) = Δ * s / 2) := by
  have hx : 0 ≤ β * Δ / 2 := by positivity
  have hr : 0 ≤ Real.tanh (β * Δ / 2) := by
    rw [Real.tanh_eq]
    apply div_nonneg _ (by positivity)
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  exact erasure_to_pure_state hr (Real.tanh_lt_one _) hΔ v hv χ hχ

end ExactQubitBathErasure
