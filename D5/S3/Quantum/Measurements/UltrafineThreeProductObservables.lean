/- GID: D5/S3/Quantum/Measurements/UltrafineThreeProductObservables
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/UltrafineThreeProductObservables
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three product observables have useless pairs and a useful triple. -/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Resource.CompositeConeDuality

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
  rw [alice.eq_1, bob.eq_1]
  fin_cases i <;> constructor <;> apply IsHermitian.ext <;>
    intro j k <;> fin_cases j <;> fin_cases k <;> norm_num

private lemma spectral_rankOne {d : ℕ} (c : Matrix (Fin d) (Fin d) ℂ)
    (hc : c.IsHermitian) :
    c = ∑ j, (hc.eigenvalues j : ℂ) • rankOneDensity (⇑(hc.eigenvectorBasis j)) := by
  conv_lhs => rw [hc.spectral_theorem]
  ext i j
  simp only [Unitary.conjStarAlgAut_apply, mul_apply, diagonal_apply, Function.comp_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, star_apply,
    IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply, Matrix.smul_apply,
    rankOneDensity, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    RCLike.ofReal_eq_complex_ofReal]
  exact Finset.sum_congr rfl fun k _ => by ring

private lemma separable_blocks {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    (c : Fin d → Matrix (Fin d) (Fin d) ℂ) (hc : ∀ k, (c k).PosSemidef)
    (ht : trace (∑ k, rankOneDensity (fun i => u.val i k) ⊗ₖ c k) = 1) :
    IsSeparable (∑ k, rankOneDensity (fun i => u.val i k) ⊗ₖ c k) := by
  have hu (k : Fin d) : star (fun i => u.val i k) ⬝ᵥ (fun i => u.val i k) = 1 := by
    have h := congrArg (fun m : Matrix (Fin d) (Fin d) ℂ => m k k)
      (Unitary.coe_star_mul_self u)
    simpa only [Unitary.coe_star, star_eq_conjTranspose, mul_apply, conjTranspose_apply,
      one_apply_eq, dotProduct, Pi.star_apply] using h
  have hq (k : Fin d) : trace (rankOneDensity (fun i => u.val i k)) = 1 := by
    simpa only [rankOneDensity, trace_vecMulVec, dotProduct_comm] using hu k
  let w : Fin d × Fin d → ℝ := fun p => (hc p.1).1.eigenvalues p.2
  let z : Fin d × Fin d → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun p =>
    rankOneDensity (fun r => u.val r.1 p.1 * ((hc p.1).1.eigenvectorBasis p.2) r.2)
  apply mem_convexHull_of_exists_fintype w z
  · intro p
    exact (hc p.1).eigenvalues_nonneg p.2
  · calc
      ∑ p, w p = ∑ k, (trace (c k)).re := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        rw [(hc k).1.trace_eq_sum_eigenvalues]
        simp only [w, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
      _ = (trace (∑ k, rankOneDensity (fun i => u.val i k) ⊗ₖ c k)).re := by
        simp only [trace_sum, trace_kronecker, hq, one_mul, Complex.re_sum]
      _ = 1 := by rw [ht]; rfl
  · intro p
    refine ⟨fun i => u.val i p.1, ⇑((hc p.1).1.eigenvectorBasis p.2), hu p.1, ?_, rfl⟩
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      (hc p.1).1.eigenvectorBasis.inner_eq_one p.2
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    change (∑ j, (w (k, j)) • z (k, j)) = _
    have hz (j : Fin d) : z (k, j) =
        rankOneDensity (fun i => u.val i k) ⊗ₖ
          rankOneDensity (⇑((hc k).1.eigenvectorBasis j)) := by
      simpa only [z, rankOneDensity] using
        (D5.S3.Resource.CompositeConeDuality.kronecker_rank_one
          (fun i => u.val i k) (⇑((hc k).1.eigenvectorBasis j))).symm
    simp only [hz]
    conv_rhs => rw [spectral_rankOne (c k) (hc k).1]
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply,
      Finset.mul_sum, w, Complex.real_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => by ring

private lemma left_diagonal_useless {d : ℕ} {ι : Type*}
    (a b : ι → Matrix (Fin d) (Fin d) ℂ) (s : Finset ι)
    (u : Matrix.unitaryGroup (Fin d) ℂ)
    (hd : ∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * a i *
      (u : Matrix (Fin d) (Fin d) ℂ)).IsDiag) :
    IsUseless (fun i => a i ⊗ₖ b i) s := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u
  let e (k : Fin d) : Matrix (Fin d) (Fin d) ℂ := diagonal (Pi.single k 1)
  let q (k : Fin d) := φ (e k)
  have hq (k : Fin d) : q k = rankOneDensity (fun i => u.val i k) := by
    ext i j
    simp [q, φ, e, Unitary.conjStarAlgAut_apply, mul_apply, diagonal_apply,
      Pi.single_apply, rankOneDensity, vecMulVec_apply, conjTranspose_apply,
      star_eq_conjTranspose, mul_assoc]
  have he (k : Fin d) : e k * e k = e k := by
    simp only [e, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = k <;> simp [hi]
  have hqid (k : Fin d) : q k * q k = q k := by
    change φ (e k) * φ (e k) = φ (e k)
    rw [← map_mul, he]
  have hqsum : ∑ k, q k = 1 := by
    have hesum : ∑ k, e k = 1 := by
      ext i j
      simp only [Matrix.sum_apply, e, diagonal_apply]
      by_cases hij : i = j
      · subst j; simp
      · simp [hij]
    change (∑ k, φ (e k)) = 1
    rw [← map_sum, hesum, map_one]
  have hqcomm (i : ι) (hi : i ∈ s) (k : Fin d) : q k * a i = a i * q k := by
    let c := diag (star (u : Matrix (Fin d) (Fin d) ℂ) * a i *
      (u : Matrix (Fin d) (Fin d) ℂ))
    have ha : a i = φ (diagonal c) := by
      change a i = φ (diagonal (diag (star (u : Matrix (Fin d) (Fin d) ℂ) * a i *
        (u : Matrix (Fin d) (Fin d) ℂ))))
      rw [(hd i hi).diagonal_diag]
      exact (φ.apply_symm_apply (a i)).symm
    calc
      q k * a i = φ (e k) * φ (diagonal c) := congrArg (fun x => q k * x) ha
      _ = φ (e k * diagonal c) := (map_mul φ _ _).symm
      _ = φ (diagonal c * e k) := congrArg φ (commute_diagonal _ _).eq
      _ = a i * q k := by rw [map_mul]; exact congrArg (fun x => x * q k) ha.symm
  let p (k : Fin d) := q k ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
  have hpid (k : Fin d) : p k * p k = p k := by
    dsimp only [p]
    rw [← mul_kronecker_mul, hqid, one_mul]
  have hph (k : Fin d) : (p k).IsHermitian := by
    change (q k ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).conjTranspose = _
    rw [conjTranspose_kronecker, conjTranspose_one]
    congr 1
    rw [hq]
    exact (posSemidef_vecMulVec_self_star _).isHermitian.eq
  have hpsum : ∑ k, p k = 1 := by
    calc
      ∑ k, p k = (∑ k, q k) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) := by
        ext i j
        simp only [p, Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]
      _ = 1 := by rw [hqsum, one_kronecker_one]
  have hpcomm (i : ι) (hi : i ∈ s) (k : Fin d) :
      p k * (a i ⊗ₖ b i) = (a i ⊗ₖ b i) * p k := by
    dsimp only [p]
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, hqcomm i hi k]
  let v (k : Fin d) : Matrix (Fin d × Fin d) (Fin d) ℂ :=
    fun r j => u.val r.1 k * if r.2 = j then 1 else 0
  have hv (k : Fin d) (c : Matrix (Fin d) (Fin d) ℂ) :
      v k * c * (v k).conjTranspose = q k ⊗ₖ c := by
    rw [hq]
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [v, kroneckerMap_apply, rankOneDensity, vecMulVec_apply, mul_assoc]
    simp only [apply_ite, map_zero, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hvp (k : Fin d) : v k * (v k).conjTranspose = p k := by
    simpa only [Matrix.mul_one] using hv k 1
  intro ρ hρ
  let c (k : Fin d) := (v k).conjTranspose * ρ * v k
  have hc (k : Fin d) : (c k).PosSemidef := hρ.1.conjTranspose_mul_mul_same _
  let σ := ∑ k, q k ⊗ₖ c k
  have hσ (k : Fin d) : q k ⊗ₖ c k = p k * ρ * p k := by
    rw [← hv k (c k), ← hvp k]
    dsimp only [c]
    simp only [Matrix.mul_assoc]
  have hσsum : σ = ∑ k, p k * ρ * p k := by
    exact Finset.sum_congr rfl fun k _ => hσ k
  have ht : trace σ = 1 := by
    rw [hσsum, trace_sum]
    calc
      ∑ k, trace (p k * ρ * p k) = ∑ k, trace (ρ * p k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [trace_mul_cycle, hpid, trace_mul_comm]
      _ = trace (ρ * ∑ k, p k) := by rw [Finset.mul_sum, trace_sum]
      _ = 1 := by rw [hpsum, mul_one, hρ.2]
  refine ⟨σ, ⟨?_, ht⟩, ?_, ?_⟩
  · rw [hσsum]
    apply posSemidef_sum
    intro k _
    simpa only [(hph k).eq] using hρ.1.mul_mul_conjTranspose_same (p k)
  · have ht0 : trace (∑ k, rankOneDensity (fun i => u.val i k) ⊗ₖ c k) = 1 := by
      simpa only [← hq] using ht
    simpa only [← hq] using separable_blocks u c hc ht0
  · intro i hi
    rw [hσsum, Finset.sum_mul, trace_sum]
    calc
      ∑ k, trace (p k * ρ * p k * (a i ⊗ₖ b i)) =
          ∑ k, trace (ρ * ((a i ⊗ₖ b i) * p k)) := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          trace (p k * ρ * p k * (a i ⊗ₖ b i)) =
              trace (p k * (ρ * p k * (a i ⊗ₖ b i))) := by simp only [mul_assoc]
          _ = trace ((ρ * p k * (a i ⊗ₖ b i)) * p k) := trace_mul_comm _ _
          _ = trace (ρ * (p k * (a i ⊗ₖ b i) * p k)) := by simp only [mul_assoc]
          _ = trace (ρ * ((a i ⊗ₖ b i) * p k)) := by
            rw [hpcomm i hi k, mul_assoc (a i ⊗ₖ b i), hpid]
      _ = trace (ρ * ((a i ⊗ₖ b i) * ∑ k, p k)) := by
        rw [Finset.mul_sum, Finset.mul_sum, trace_sum]
      _ = trace (ρ * (a i ⊗ₖ b i)) := by rw [hpsum, mul_one]

private lemma diagonal_family_useless {d : ℕ} {ι : Type*}
    (a b : ι → Matrix (Fin d) (Fin d) ℂ) (s : Finset ι)
    (u : Matrix.unitaryGroup (Fin d) ℂ)
    (hdiag : (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * a i *
      (u : Matrix (Fin d) (Fin d) ℂ)).IsDiag) ∨
      (∀ i ∈ s, (star (u : Matrix (Fin d) (Fin d) ℂ) * b i * u).IsDiag)) :
    IsUseless (fun i => a i ⊗ₖ b i) s := by
  classical
  rcases hdiag with hd | hd
  · exact left_diagonal_useless a b s u hd
  · have hleft := left_diagonal_useless b a s u hd
    let f : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℝ]
        Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
      { toFun := fun x => x.submatrix Prod.swap Prod.swap
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hft (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : trace (f x) = trace x := by
      simp only [f, trace, diag_apply, Fintype.sum_prod_type]
      exact Finset.sum_comm
    have hfm (x y : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
        f (x * y) = f x * f y := by
      exact (submatrix_mul_equiv x y Prod.swap (Equiv.prodComm _ _) Prod.swap).symm
    have hfk (x y : Matrix (Fin d) (Fin d) ℂ) : f (x ⊗ₖ y) = y ⊗ₖ x := by
      ext i j
      exact mul_comm _ _
    have hfs (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
        (hx : IsSeparable x) : IsSeparable (f x) := by
      apply convexHull_min (t := {y | IsSeparable (f y)}) ?_ ?_ hx
      · rintro τ ⟨v, w, hv, hw, rfl⟩
        apply subset_convexHull ℝ _
        refine ⟨w, v, hw, hv, ?_⟩
        ext i j
        change v i.2 * w i.1 * star (v j.2 * w j.1) =
          w i.1 * v i.2 * star (w j.1 * v j.2)
        rw [mul_comm (v i.2) (w i.1), mul_comm (v j.2) (w j.1)]
      · exact (convex_convexHull ℝ _).is_linear_preimage f.isLinear
    intro ρ hρ
    have hρf : IsDensity (f ρ) := ⟨hρ.1.submatrix Prod.swap, (hft ρ).trans hρ.2⟩
    obtain ⟨σ, hσ, hsep, hmatch⟩ := hleft (f ρ) hρf
    refine ⟨f σ, ⟨hσ.1.submatrix Prod.swap, (hft σ).trans hσ.2⟩, hfs σ hsep, ?_⟩
    intro i hi
    calc
      trace (f σ * (a i ⊗ₖ b i)) = trace (f (σ * (b i ⊗ₖ a i))) := by rw [hfm, hfk]
      _ = trace (σ * (b i ⊗ₖ a i)) := hft _
      _ = trace (f ρ * (b i ⊗ₖ a i)) := hmatch i hi
      _ = trace (f (ρ * (a i ⊗ₖ b i))) := by rw [hfm, hfk]
      _ = trace (ρ * (a i ⊗ₖ b i)) := hft _


private lemma pairs_useless (i j : Fin 3) (hij : i ≠ j) : IsUseless obs {i, j} := by
  let r : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hr : r * r = (1 / 2 : ℂ) := by
    dsimp [r]
    rw [← _root_.mul_inv_rev, ← pow_two, hsqrt]
    norm_num
  have hstar : (starRingEnd ℂ) r = r := by simp [r]
  let u0 : Matrix (Fin 3) (Fin 3) ℂ := !![r,r,0; r,-r,0; 0,0,1]
  have hu0 : u0 ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext k l
    fin_cases k <;> fin_cases l <;>
      norm_num [u0, Matrix.mul_apply, Fin.sum_univ_succ, star_eq_conjTranspose,
        Matrix.conjTranspose_apply, hstar, hr]
  let u : Matrix.unitaryGroup (Fin 3) ℂ := ⟨u0, hu0⟩
  have h01 : IsUseless obs {0, 1} := by
    apply diagonal_family_useless alice bob {0, 1} u
    left
    intro k hk
    have hk2 : k = 0 ∨ k = 1 := by simpa only [mem_insert, mem_singleton] using hk
    rcases hk2 with rfl | rfl <;>
      intro l m hlm <;> fin_cases l <;> fin_cases m <;>
      (try exact (hlm rfl).elim) <;>
      norm_num [u, u0, alice, Matrix.mul_apply, Fin.sum_univ_succ,
        star_eq_conjTranspose, Matrix.conjTranspose_apply, hstar, hr]
  have h02 : IsUseless obs {0, 2} := by
    apply diagonal_family_useless alice bob {0, 2} 1
    left
    intro k hk
    have hk2 : k = 0 ∨ k = 2 := by simpa only [mem_insert, mem_singleton] using hk
    rcases hk2 with rfl | rfl <;>
      simp only [OneMemClass.coe_one, star_one, one_mul, mul_one] <;>
      intro l m hlm <;> fin_cases l <;> fin_cases m <;>
      (try exact (hlm rfl).elim) <;> norm_num [alice]
  have h12 : IsUseless obs {1, 2} := by
    apply diagonal_family_useless alice bob {1, 2} 1
    right
    intro k hk
    have hk2 : k = 1 ∨ k = 2 := by simpa only [mem_insert, mem_singleton] using hk
    rcases hk2 with rfl | rfl <;>
      simp only [OneMemClass.coe_one, star_one, one_mul, mul_one] <;>
      intro l m hlm <;> fin_cases l <;> fin_cases m <;>
      (try exact (hlm rfl).elim) <;> norm_num [bob]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · rw [Finset.pair_comm]; exact h01
  · exact (hij rfl).elim
  · exact h12
  · rw [Finset.pair_comm]; exact h02
  · rw [Finset.pair_comm]; exact h12
  · exact (hij rfl).elim

private lemma hamiltonian_hermitian : hamiltonian.IsHermitian := by
  have ho (i : Fin 3) : (obs i).IsHermitian := by
    rw [obs.eq_1]
    change (alice i ⊗ₖ bob i).conjTranspose = alice i ⊗ₖ bob i
    rw [conjTranspose_kronecker, (factors_hermitian i).1.eq,
      (factors_hermitian i).2.eq]
  rw [hamiltonian.eq_1]
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
      simp only [hb0, mul_zero, add_zero, zero_add] at h00 h10
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
