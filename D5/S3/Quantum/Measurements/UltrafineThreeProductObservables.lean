/- GID: D5/S3/Quantum/Measurements/UltrafineThreeProductObservables
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/UltrafineThreeProductObservables
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three product observables have useless pairs and a useful triple. -/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.PureState.PureStateHandshake

/-! A three-observable separation between pairwise and joint entanglement detection. -/

open Matrix Finset
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (IsDensity)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

namespace D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
noncomputable section
set_option autoImplicit false

/-- The convex hull of unit pure product projectors. -/
def IsSeparable {m n : ℕ}
    (σ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : Prop :=
  σ ∈ convexHull ℝ {τ | ∃ (a : Fin m → ℂ) (b : Fin n → ℂ),
    star a ⬝ᵥ a = 1 ∧ star b ⬝ᵥ b = 1 ∧
      τ = rankOneDensity (fun p : Fin m × Fin n => a p.1 * b p.2)}

/-- Every joint expectation in the family is realised by a separable density matrix. -/
def IsUseless {d : ℕ} {ι : Type*}
    (obs : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (s : Finset ι) : Prop :=
  ∀ ρ, IsDensity ρ → ∃ σ, IsDensity σ ∧ IsSeparable σ ∧
    ∀ i ∈ s, trace (σ * obs i) = trace (ρ * obs i)

/-- The three-observable existence question of Gachechiladze--Wyderka--Gühne. -/
def claim : Prop :=
  ∃ a b : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
    (∀ i, (a i).IsHermitian ∧ (b i).IsHermitian) ∧
    (∀ i j, i ≠ j → IsUseless (fun k => a k ⊗ₖ b k) {i, j}) ∧
    ¬ IsUseless (fun k => a k ⊗ₖ b k) univ

private def alice : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![1,0,0; 0,1,0; 0,0,1/100],
    !![0,1,0; 1,0,0; 0,0,1/100],
    !![1,0,0; 0,-1,0; 0,0,1/100]]

private def bob : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![2,1,0; 1,2,1; 0,1,2],
    !![1,0,0; 0,2,0; 0,0,3],
    !![1,0,0; 0,4,0; 0,0,9]]

private def obs (i : Fin 3) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  alice i ⊗ₖ bob i

private def hamiltonian : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  obs 0 + obs 1 + obs 2

private lemma factors_hermitian (i : Fin 3) :
    (alice i).IsHermitian ∧ (bob i).IsHermitian := by
  fin_cases i <;> constructor <;> apply IsHermitian.ext <;>
    intro j k <;> fin_cases j <;> fin_cases k <;> norm_num [alice, bob]

private lemma diagonal_family_useless {d : ℕ} {ι : Type*}
    (a b : ι → Matrix (Fin d) (Fin d) ℂ) (s : Finset ι)
    (u : Matrix.unitaryGroup (Fin d) ℂ)
    (hdiag : (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * a i * u).IsDiag) ∨
      (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * b i * u).IsDiag)) :
    IsUseless (fun i => a i ⊗ₖ b i) s := by
  sorry

private lemma pairs_useless (i j : Fin 3) (hij : i ≠ j) : IsUseless obs {i, j} := by
  sorry

private lemma hamiltonian_hermitian : hamiltonian.IsHermitian := by
  have ho (i : Fin 3) : (obs i).IsHermitian := by
    change (alice i ⊗ₖ bob i).conjTranspose = alice i ⊗ₖ bob i
    rw [conjTranspose_kronecker, (factors_hermitian i).1.eq,
      (factors_hermitian i).2.eq]
  exact ((ho 0).add (ho 1)).add (ho 2)

private lemma ground_state :
    ∃ (μ : ℝ) (g : Fin 3 × Fin 3 → ℂ),
      μ < 0 ∧ star g ⬝ᵥ g = 1 ∧
      hamiltonian *ᵥ g = (μ : ℂ) • g ∧
      (hamiltonian - (μ : ℂ) • 1).PosSemidef := by
  let hh := hamiltonian_hermitian
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image (univ : Finset (Fin 3 × Fin 3))
    hh.eigenvalues univ_nonempty
  let μ := hh.eigenvalues k
  have hmin (i : Fin 3 × Fin 3) : μ ≤ hh.eigenvalues i := hk i (mem_univ i)
  have hdiag : (diagonal (fun i => ((hh.eigenvalues i - μ : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    exact Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hmin i), by simp⟩
  have hshift : hamiltonian - (μ : ℂ) • 1 =
      hh.eigenvectorUnitary * diagonal (fun i => ((hh.eigenvalues i - μ : ℝ) : ℂ)) *
        (hh.eigenvectorUnitary : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ).conjTranspose := by
    have hd : diagonal (fun i => ((hh.eigenvalues i - μ : ℝ) : ℂ)) =
        diagonal (fun i => (hh.eigenvalues i : ℂ)) - (μ : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hd, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, ← star_eq_conjTranspose, ← Unitary.coe_star, Unitary.coe_mul_star_self]
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      congrArg (fun x => x - (μ : ℂ) • 1) hh.spectral_theorem
  have hpos : (hamiltonian - (μ : ℂ) • 1).PosSemidef := by
    rw [hshift]
    exact hdiag.mul_mul_conjTranspose_same _
  have hneg : μ < 0 := by
    have hr := (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := (1, 2)))).1
    norm_num [hamiltonian, obs, alice, bob, kroneckerMap_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.sub_re, Complex.mul_re] at hr
    linarith
  refine ⟨μ, ⇑(hh.eigenvectorBasis k), hneg, ?_, hh.mulVec_eigenvectorBasis k, hpos⟩
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    hh.eigenvectorBasis.inner_eq_one k

private lemma outside_psd : (bob 0 + bob 1 + bob 2).PosSemidef := by
  have hd : (diagonal (![3, 6, 13] : Fin 3 → ℂ)).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  convert (hd.add (posSemidef_vecMulVec_self_star (![1, 1, 0] : Fin 3 → ℂ))).add
    (posSemidef_vecMulVec_self_star (![0, 1, 1] : Fin 3 → ℂ)) using 1
  ext i j
  simp only [Matrix.add_apply, vecMulVec_apply, Pi.star_apply]
  fin_cases i <;> fin_cases j <;> norm_num [bob, diagonal_apply]

private lemma no_product_ground (μ : ℝ) (hμ : μ < 0)
    (a b : Fin 3 → ℂ) (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    hamiltonian *ᵥ (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) ≠
      (μ : ℂ) • (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) := by
  intro heig
  have hout (j : Fin 3) :
      a 2 * ((bob 0 + bob 1 + bob 2) *ᵥ b) j =
        (100 * (μ : ℂ)) * (a 2 * b j) := by
    have h := congrFun heig (2, j)
    fin_cases j <;>
      norm_num [hamiltonian, obs, alice, bob, mulVec, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_succ, kroneckerMap_apply] at h ⊢ <;>
      linear_combination 100 * h
  have ha2 : a 2 = 0 := by
    by_contra hn
    have he : (bob 0 + bob 1 + bob 2) *ᵥ b = (100 * (μ : ℂ)) • b := by
      funext j
      apply mul_left_cancel₀ hn
      change a 2 * _ = a 2 * ((100 * (μ : ℂ)) * b j)
      linear_combination hout j
    have hp := outside_psd.re_dotProduct_nonneg b
    rw [he, dotProduct_smul, hb, smul_eq_mul, mul_one] at hp
    norm_num [Complex.mul_re] at hp
    linarith
  have hactive : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    norm_num [dotProduct, Fin.sum_univ_succ, hn.1, hn.2, ha2] at ha
  have h00 := congrFun heig (0, 0)
  have h01 := congrFun heig (0, 1)
  have h02 := congrFun heig (0, 2)
  have h10 := congrFun heig (1, 0)
  have h11 := congrFun heig (1, 1)
  have h12 := congrFun heig (1, 2)
  norm_num [hamiltonian, obs, alice, bob, mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_succ, kroneckerMap_apply, ha2] at h00 h01 h02 h10 h11 h12
  let c := a 1 ^ 2 - a 0 ^ 2
  let e := 2 * a 0 * a 1
  let w : Fin 3 → ℂ := ![1, 2, 3]
  have hp (i : Fin 3) : (c * w i + e * (w i) ^ 2) * b i = 0 := by
    fin_cases i
    · dsimp [c, e, w]
      linear_combination a 1 * h00 - a 0 * h10
    · dsimp [c, e, w]
      linear_combination a 1 * h01 - a 0 * h11
    · dsimp [c, e, w]
      linear_combination a 1 * h02 - a 0 * h12
  have hs (i j : Fin 3) (hi : b i ≠ 0) (hj : b j ≠ 0) : i = j := by
    by_contra hij
    have hpi := (mul_eq_zero.mp (hp i)).resolve_right hi
    have hpj := (mul_eq_zero.mp (hp j)).resolve_right hj
    have hdet : w i * (w j) ^ 2 - w j * (w i) ^ 2 ≠ 0 := by
      fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim) <;> norm_num [w]
    have hc : c = 0 := by
      have hz : c * (w i * (w j) ^ 2 - w j * (w i) ^ 2) = 0 := by
        linear_combination (w j) ^ 2 * hpi - (w i) ^ 2 * hpj
      exact (mul_eq_zero.mp hz).resolve_right hdet
    have he : e = 0 := by
      have hwi : (w i) ^ 2 ≠ 0 := by fin_cases i <;> norm_num [w]
      rw [hc, zero_mul, zero_add] at hpi
      exact (mul_eq_zero.mp hpi).resolve_right hwi
    have hxy : a 0 * a 1 = 0 := by
      dsimp [e] at he
      linear_combination (1 / 2 : ℂ) * he
    have hz : a 0 = 0 ∧ a 1 = 0 := by
      rcases mul_eq_zero.mp hxy with hx | hy
      · refine ⟨hx, ?_⟩
        apply eq_zero_of_pow_eq_zero (n := 2)
        simpa only [c, hx, zero_pow (by decide : 2 ≠ 0), sub_zero] using hc
      · refine ⟨?_, hy⟩
        apply eq_zero_of_pow_eq_zero (n := 2)
        have : -(a 0 ^ 2) = 0 := by
          simpa only [c, hy, zero_pow (by decide : 2 ≠ 0), zero_sub] using hc
        exact neg_eq_zero.mp this
    exact hactive.elim (fun hx => hx hz.1) (fun hy => hy hz.2)
  have hbne : b ≠ 0 := by
    intro hz
    simp only [hz, star_zero, dotProduct_zero] at hb
    exact zero_ne_one hb
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hbne
  have hz (j : Fin 3) (hj : j ≠ k) : b j = 0 := by
    by_contra hn
    exact hj (hs j k hn hk)
  have hzero : a 0 = 0 ∧ a 1 = 0 := by
    fin_cases k
    · have hb1 := hz 1 (by decide)
      have hb2 := hz 2 (by decide)
      simp only [hb1, hb2, mul_zero, neg_zero, add_zero, zero_add] at h01 h11
      exact ⟨(mul_eq_zero.mp h01).resolve_right hk, (mul_eq_zero.mp h11).resolve_right hk⟩
    · have hb0 := hz 0 (by decide)
      have hb2 := hz 2 (by decide)
      simp only [hb0, mul_zero, neg_zero, add_zero, zero_add] at h00 h10
      exact ⟨(mul_eq_zero.mp h00).resolve_right hk, (mul_eq_zero.mp h10).resolve_right hk⟩
    · have hb0 := hz 0 (by decide)
      have hb1 := hz 1 (by decide)
      simp only [hb0, hb1, mul_zero, neg_zero, add_zero, zero_add] at h01 h11
      exact ⟨(mul_eq_zero.mp h01).resolve_right hk, (mul_eq_zero.mp h11).resolve_right hk⟩
  exact hactive.elim (fun hx => hx hzero.1) (fun hy => hy hzero.2)

private lemma separable_ground_exclusion
    (μ : ℝ) (hpos : (hamiltonian - (μ : ℂ) • 1).PosSemidef)
    (hnoprod : ∀ (a b : Fin 3 → ℂ), star a ⬝ᵥ a = 1 → star b ⬝ᵥ b = 1 →
      hamiltonian *ᵥ (fun p : Fin 3 × Fin 3 => a p.1 * b p.2) ≠
        (μ : ℂ) • (fun p : Fin 3 × Fin 3 => a p.1 * b p.2))
    (σ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hσ : IsSeparable σ) :
    μ < (trace (σ * hamiltonian)).re := by
  have hlin : IsLinearMap ℝ
      (fun τ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ =>
        (trace (τ * hamiltonian)).re) := by
    constructor
    · intro x y
      simp only [add_mul, trace_add, Complex.add_re]
    · intro r x
      simp only [smul_mul_assoc, trace_smul, Complex.real_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply convexHull_min (t := {τ | μ < (trace (τ * hamiltonian)).re})
    ?_ (convex_halfSpace_gt hlin μ) hσ
  rintro τ ⟨a, b, ha, hb, rfl⟩
  let v : Fin 3 × Fin 3 → ℂ := fun p => a p.1 * b p.2
  have hv : star v ⬝ᵥ v = 1 := by
    change (∑ p : Fin 3 × Fin 3, star (a p.1 * b p.2) * (a p.1 * b p.2)) = 1
    rw [Fintype.sum_prod_type]
    calc
      _ = (star a ⬝ᵥ a) * (star b ⬝ᵥ b) := by
        simp only [dotProduct, Pi.star_apply, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [star_mul]
        ring
      _ = 1 := by rw [ha, hb, one_mul]
  have hne : (hamiltonian - (μ : ℂ) • 1) *ᵥ v ≠ 0 := by
    intro heq
    apply hnoprod a b ha hb
    exact sub_eq_zero.mp (by
      simpa only [sub_mulVec, smul_mulVec, one_mulVec] using heq)
  have hq := hpos.dotProduct_mulVec_nonneg v
  have hqn : star v ⬝ᵥ ((hamiltonian - (μ : ℂ) • 1) *ᵥ v) ≠ 0 :=
    hpos.dotProduct_mulVec_zero_iff.not.mpr hne
  have hqr : 0 < (star v ⬝ᵥ ((hamiltonian - (μ : ℂ) • 1) *ᵥ v)).re := by
    refine lt_of_le_of_ne (Complex.nonneg_iff.mp hq).1 ?_
    intro heq
    apply hqn
    exact Complex.ext heq.symm (Complex.nonneg_iff.mp hq).2.symm
  change μ < (trace (rankOneDensity v * hamiltonian)).re
  rw [trace_mul_comm, rankOneDensity, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    hv, smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re] at hqr
  linarith

private lemma triple_useful : ¬ IsUseless obs univ := by
  obtain ⟨μ, g, hμ, hg, heig, hpos⟩ := ground_state
  have hρ : IsDensity (rankOneDensity g) := by
    refine ⟨posSemidef_vecMulVec_self_star g, ?_⟩
    simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm] using hg
  intro huseless
  obtain ⟨σ, _, hσ, hmatch⟩ := huseless (rankOneDensity g) hρ
  have henergy : trace (σ * hamiltonian) = (μ : ℂ) := by
    have h0 := hmatch 0 (mem_univ 0)
    have h1 := hmatch 1 (mem_univ 1)
    have h2 := hmatch 2 (mem_univ 2)
    change trace (σ * (obs 0 + obs 1 + obs 2)) = _
    rw [mul_add, mul_add, trace_add, trace_add, h0, h1, h2,
      ← trace_add, ← trace_add, ← mul_add, ← mul_add]
    change trace (rankOneDensity g * hamiltonian) = _
    rw [trace_mul_comm, rankOneDensity, mul_vecMulVec, trace_vecMulVec,
      heig, smul_dotProduct, dotProduct_comm, hg, smul_eq_mul, mul_one]
  have hstrict := separable_ground_exclusion μ hpos (no_product_ground μ hμ) σ hσ
  rw [henergy] at hstrict
  exact (lt_irrefl μ) hstrict

/-- Every pair is useless, whereas the full triple detects entanglement. -/
theorem result : claim := by
  exact ⟨alice, bob, factors_hermitian, pairs_useless, triple_useful⟩

end
end D5.S3.Quantum.Measurements.UltrafineThreeProductObservables
