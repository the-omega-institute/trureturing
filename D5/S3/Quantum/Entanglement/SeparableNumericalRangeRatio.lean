/- GID: D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SeparableNumericalRangeRatio
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The minimal separable numerical range ratio of one two-qubit observable is 1/2. -/

/-
proof_shape: result: content (separable decompositions of the rank-two operators
  `zz† + C rr†` in magic coordinates, one separable noise operator shared by two pure states,
  the resulting width inequality for all states, and the volume comparison)
escape_witness: result (form (2) of §3.2: the public conclusion is produced by the separable
  decompositions and the width inequality; no step instantiates an existing statement of the
  bound)
admission_basis: open-problem-resolution (issue #12146; Proved)
Direct frozen dependencies:
  D5/S3/Resource/CompositeCones.separableCone
    sha256:c652793a23fc76192f4a1526d019bf7da39990b83067ec9d3207e1e287a3a64f
  D5/S3/Resource/CompositeCones.separable_isPosSemidef
    sha256:b496967807946e56f47ebcd79e7eef83aa10b388907e1d7d18b07325d1a1cc98
  D5/S3/Resource/EntanglementWitness.separableCone_add
    sha256:338bdd18c4d0a6bd87fb1089a5f5c07b2ffc9ed10ec8176379b119e67ca97642
  D5/S3/Resource/EntanglementWitness.separableCone_smul
    sha256:8cdce7cfcaf6233b78e1d05f29cd8aae4b73eea4a3b9691abd155d811a22069c
  D5/S3/Resource/CompositeConeDuality.kronecker_rank_one
-/

import D5.S3.Resource.EntanglementWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio

open Matrix MeasureTheory Complex Set
open D5.S3.Resource
open D5.S3.Resource.CompositeCones D5.S3.Resource.EntanglementWitness
open scoped Kronecker ComplexOrder ENNReal

/-- Two-qubit density matrices: positive semidefinite with trace `1`. -/
def states : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  {ρ | ρ.PosSemidef ∧ ρ.trace = 1}

/-- Separable two-qubit states: finite sums of Kronecker products of positive semidefinite
`2 × 2` factors, with trace `1`. -/
def separableStates : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  {ρ | separableCone ρ ∧ ρ.trace = 1}

/-- The restricted numerical range `L_X(A) = {Tr ρA | ρ ∈ X}` of one observable. -/
noncomputable def numericalRange (X : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
    (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Set ℝ :=
  (fun ρ => (ρ * A).trace.re) '' X

/-- Conjecture 8 of Simnacher, Czartowski, Szymański and Życzkowski (arXiv:2107.04365):
`1/2` is the least value of `vol L_Sep(A) / vol L(A)` over two-qubit observables `A` with
`vol L(A) ≠ 0`. -/
def claim : Prop :=
  IsLeast {r : ℝ≥0∞ | ∃ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, A.IsHermitian ∧
    volume (numericalRange states A) ≠ 0 ∧
      r = volume (numericalRange separableStates A) / volume (numericalRange states A)} (1 / 2)

/-- The projector `vv†`. -/
private noncomputable def P (v : Fin 2 × Fin 2 → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  vecMulVec v (star v)

/-- The vector with magic coordinates `z`. -/
private noncomputable def mg (z : Fin 4 → ℂ) : Fin 2 × Fin 2 → ℂ := fun ij =>
  (!![z 0 + I * z 1, I * z 2 + z 3; I * z 2 - z 3, z 0 - I * z 1] ij.1 ij.2) / (Real.sqrt 2 : ℂ)

/-- Two pure states differ by a positive multiple, at most `2`, of a difference of two separable
states: both receive the same separable noise. -/
private theorem pure_pair (u v : Fin 2 × Fin 2 → ℂ) (hu : ∑ i, normSq (u i) = 1)
    (hv : ∑ i, normSq (v i) = 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∃ σ ∈ separableStates, ∃ τ ∈ separableStates,
      P u - P v = ((1 + c : ℝ) : ℂ) • (σ - τ) := by
  have rsmul : ∀ (t : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), t • M = (t : ℂ) • M := by
    intro t M; ext i j; simp [Complex.real_smul]
  have cone_smul : ∀ (t : ℝ) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), 0 ≤ t →
      separableCone X →
      separableCone ((t : ℂ) • X) := by
    intro t X ht hX; rw [← rsmul]; exact separableCone_smul ht hX
  have cone_prod : ∀ u : Fin 2 × Fin 2 → ℂ, u (0, 0) * u (1, 1) = u (0, 1) * u (1, 0) →
      separableCone (P u) := by
    intro u hu
    have hab : ∃ a b : Fin 2 → ℂ, ∀ i j, u (i, j) = a i * b j := by
      by_cases h00 : u (0, 0) = 0
      · by_cases h01 : u (0, 1) = 0
        · refine ⟨![0, 1], ![u (1, 0), u (1, 1)], fun i j => ?_⟩
          fin_cases i <;> fin_cases j <;> simp [h00, h01]
        · refine ⟨![1, u (1, 1) / u (0, 1)], ![u (0, 0), u (0, 1)], fun i j => ?_⟩
          have h10 : u (1, 0) = 0 := by
            rw [h00, zero_mul] at hu
            exact (mul_eq_zero.mp hu.symm).resolve_left h01
          fin_cases i <;> fin_cases j <;> simp [h00, h10]
          field_simp
      · refine ⟨![1, u (1, 0) / u (0, 0)], ![u (0, 0), u (0, 1)], fun i j => ?_⟩
        fin_cases i <;> fin_cases j <;> simp
        · field_simp
        · field_simp
          linear_combination hu
    obtain ⟨a, b, hab⟩ := hab
    have hu' : u = fun ij : Fin 2 × Fin 2 => a ij.1 * b ij.2 := funext fun ij => hab ij.1 ij.2
    refine ⟨1, fun _ => vecMulVec a (star a), fun _ => vecMulVec b (star b),
      fun _ => ⟨posSemidef_vecMulVec_self_star a, posSemidef_vecMulVec_self_star b⟩, ?_⟩
    rw [Fin.sum_univ_one, CompositeConeDuality.kronecker_rank_one, hu']
    rfl
  have mg_det : ∀ z : Fin 4 → ℂ,
      mg z (0, 0) * mg z (1, 1) - mg z (0, 1) * mg z (1, 0) =
        (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) / 2 := by
    intro z
    have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
    have h2' : (Real.sqrt 2 : ℂ) ≠ 0 := by
      intro h; rw [h] at h2; norm_num at h2
    simp only [mg, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    field_simp
    linear_combination (z 1 ^ 2 + z 2 ^ 2) * (-2) * I_sq -
      (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) * h2
  have mg_add : ∀ a b : Fin 4 → ℂ, mg (a + b) = mg a + mg b := by
    intro a b; funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [mg] <;> ring
  have mg_smul : ∀ (c : ℂ) (a : Fin 4 → ℂ), mg (c • a) = c • mg a := by
    intro c a; funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [mg] <;> ring
  have cone_sq : ∀ w : Fin 4 → ℂ, ∑ i, w i ^ 2 = 0 → separableCone (P (mg w)) := by
    intro w hw
    apply cone_prod
    rw [← sub_eq_zero, mg_det]
    rw [Fin.sum_univ_four] at hw
    rw [hw]; simp
  have correction : ∀ (z : Fin 4 → ℂ) (C : ℝ), ∑ i, z i ^ 2 = (C : ℂ) → 0 ≤ C →
      ∀ r : Fin 4 → ℝ, ∑ i, r i ^ 2 = 1 → ∑ i, r i * (z i).re = 0 →
        separableCone (P (mg z) + (C : ℂ) • P (mg (fun i => (r i : ℂ)))) := by
    intro z C hC hC0 r hr hrz
    rcases hC0.eq_or_lt with hC0 | hCpos
    · subst hC0
      simpa using cone_sq z (by simpa using hC)
    set η : ℝ := ∑ i, r i * (z i).im with hη
    set δ : ℝ := Real.sqrt (η ^ 2 + C) with hδ
    have hδsq : δ ^ 2 = η ^ 2 + C := Real.sq_sqrt (by positivity)
    have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
    have hδη : |η| ≤ δ := by
      rw [hδ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    have hzr : ∑ i, z i * (r i : ℂ) = I * η := by
      apply Complex.ext
      · simp only [re_sum, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        simpa [mul_comm] using hrz
      · simp only [im_sum, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]
        simp [hη, mul_comm]
    set rc : Fin 4 → ℂ := fun i => (r i : ℂ) with hrc
    have hsq : ∀ t : ℝ, t ^ 2 + 2 * η * t - C = 0 →
        ∑ i, (z + (I * t) • rc) i ^ 2 = 0 := by
      intro t ht
      have hrr : ∑ i, rc i ^ 2 = 1 := by
        simp only [hrc, ← ofReal_pow, ← ofReal_sum, hr, ofReal_one]
      have : ∑ i, (z + (I * t) • rc) i ^ 2 =
          ∑ i, z i ^ 2 + 2 * (I * t) * ∑ i, z i * rc i + (I * t) ^ 2 * ∑ i, rc i ^ 2 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [this, hC, hzr, hrr]
      have ht' : ((t : ℂ)) ^ 2 + 2 * η * t - C = 0 := by exact_mod_cast ht
      linear_combination (-1 : ℂ) * ht' + (2 * (t : ℂ) * η + (t : ℂ) ^ 2) * I_sq
    set tp : ℝ := δ - η
    set tm : ℝ := -δ - η
    set pp : ℝ := (δ + η) / (2 * δ)
    set pm : ℝ := (δ - η) / (2 * δ)
    have htp : tp ^ 2 + 2 * η * tp - C = 0 := by simp only [tp]; nlinarith [hδsq]
    have htm : tm ^ 2 + 2 * η * tm - C = 0 := by simp only [tm]; nlinarith [hδsq]
    have hpp : 0 ≤ pp := div_nonneg (by linarith [neg_abs_le η]) (by positivity)
    have hpm : 0 ≤ pm := div_nonneg (by linarith [le_abs_self η]) (by positivity)
    have e1 : pp + pm = 1 := by simp only [pp, pm]; field_simp; ring
    have e2 : pp * tp + pm * tm = 0 := by simp only [pp, pm, tp, tm]; field_simp; ring
    have e3 : pp * tp ^ 2 + pm * tm ^ 2 = C := by
      simp only [pp, pm, tp, tm]; field_simp; nlinarith [hδsq]
    have key : (pp : ℂ) • P (mg (z + (I * tp) • rc)) + (pm : ℂ) • P (mg (z + (I * tm) • rc)) =
        P (mg z) + (C : ℂ) • P (mg rc) := by
      have e1' : (pp : ℂ) + pm = 1 := by exact_mod_cast e1
      have e2' : (pp : ℂ) * tp + pm * tm = 0 := by exact_mod_cast e2
      have e3' : (pp : ℂ) * tp ^ 2 + pm * tm ^ 2 = C := by exact_mod_cast e3
      ext i j
      simp only [P, mg_add, mg_smul, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul, smul_eq_mul,
        RCLike.star_def, map_mul, conj_I, conj_ofReal]
      linear_combination (mg z i * (starRingEnd ℂ) (mg z j)) * e1' +
        (I * mg rc i * (starRingEnd ℂ) (mg z j) - I * mg z i * (starRingEnd ℂ) (mg rc j)) * e2' +
        (mg rc i * (starRingEnd ℂ) (mg rc j)) * e3' -
        ((pp : ℂ) * tp ^ 2 + pm * tm ^ 2) * (mg rc i * (starRingEnd ℂ) (mg rc j)) * I_sq
    rw [← key]
    exact separableCone_add (cone_smul _ _ hpp (cone_sq _ (hsq _ htp)))
      (cone_smul _ _ hpm (cone_sq _ (hsq _ htm)))
  have orth : ∀ x y : Fin 4 → ℝ, ∃ r s : Fin 4 → ℝ, ∑ i, r i ^ 2 = 1 ∧ ∑ i, s i ^ 2 = 1 ∧
      ∑ i, r i * s i = 0 ∧ ∑ i, r i * x i = 0 ∧ ∑ i, s i * x i = 0 ∧
      ∑ i, r i * y i = 0 ∧ ∑ i, s i * y i = 0 := by
    intro x y
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
      Submodule.span ℝ {WithLp.toLp 2 x, WithLp.toLp 2 y}
    have hK : Module.finrank ℝ K ≤ 2 := by
      have := finrank_span_finset_le_card (R := ℝ)
        ({WithLp.toLp 2 x, WithLp.toLp 2 y} : Finset (EuclideanSpace ℝ (Fin 4)))
      simp only [Finset.coe_insert, Finset.coe_singleton] at this
      exact this.trans (Finset.card_le_two)
    have hKo : 2 ≤ Module.finrank ℝ Kᗮ := by
      have := K.finrank_add_finrank_orthogonal
      rw [finrank_euclideanSpace_fin] at this
      omega
    let b := stdOrthonormalBasis ℝ Kᗮ
    let e0 : Fin (Module.finrank ℝ Kᗮ) := ⟨0, by omega⟩
    let e1 : Fin (Module.finrank ℝ Kᗮ) := ⟨1, by omega⟩
    have h01 : e0 ≠ e1 := by simp [e0, e1, Fin.ext_iff]
    have hxK : WithLp.toLp 2 x ∈ K := Submodule.subset_span (by simp)
    have hyK : WithLp.toLp 2 y ∈ K := Submodule.subset_span (by simp)
    have inner_eq : ∀ u v : EuclideanSpace ℝ (Fin 4), inner ℝ u v = ∑ i, u i * v i := by
      intro u v; simp [PiLp.inner_apply, mul_comm]
    refine ⟨fun i => ((b e0 : Kᗮ) : EuclideanSpace ℝ (Fin 4)) i,
      fun i => ((b e1 : Kᗮ) : EuclideanSpace ℝ (Fin 4)) i, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := b.inner_eq_one e0
      rw [Submodule.coe_inner, inner_eq] at this
      simpa [sq] using this
    · have := b.inner_eq_one e1
      rw [Submodule.coe_inner, inner_eq] at this
      simpa [sq] using this
    · have := b.inner_eq_zero h01
      rw [Submodule.coe_inner, inner_eq] at this
      exact this
    · have := Submodule.inner_right_of_mem_orthogonal hxK (b e0).2
      rw [inner_eq] at this
      simpa [mul_comm] using this
    · have := Submodule.inner_right_of_mem_orthogonal hxK (b e1).2
      rw [inner_eq] at this
      simpa [mul_comm] using this
    · have := Submodule.inner_right_of_mem_orthogonal hyK (b e0).2
      rw [inner_eq] at this
      simpa [mul_comm] using this
    · have := Submodule.inner_right_of_mem_orthogonal hyK (b e1).2
      rw [inner_eq] at this
      simpa [mul_comm] using this
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at h2; norm_num at h2
  have hs2 : normSq ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  -- the magic coordinates are an isometry
  have mg_normSq : ∀ z : Fin 4 → ℂ, ∑ ij, normSq (mg z ij) = ∑ k, normSq (z k) := by
    intro z
    simp only [mg, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, normSq_div, hs2,
      normSq_add, normSq_sub, normSq_mul, normSq_I]
    simp only [mul_re, I_re, I_im, map_mul, conj_I, mul_im]
    ring
  have mg_inv : ∀ u : Fin 2 × Fin 2 → ℂ, ∃ z : Fin 4 → ℂ, mg z = u := by
    intro u
    refine ⟨![(u (0, 0) + u (1, 1)) / (Real.sqrt 2 : ℂ),
      -I * (u (0, 0) - u (1, 1)) / (Real.sqrt 2 : ℂ),
      -I * (u (0, 1) + u (1, 0)) / (Real.sqrt 2 : ℂ),
      (u (0, 1) - u (1, 0)) / (Real.sqrt 2 : ℂ)], ?_⟩
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [mg] <;> field_simp <;> ring_nf <;>
      simp only [I_sq, h2] <;> ring_nf
  have P_smul : ∀ (ω : ℂ) (w : Fin 2 × Fin 2 → ℂ), normSq ω = 1 → P (ω • w) = P w := by
    intro ω w hω
    have hωc : ω * (starRingEnd ℂ) ω = 1 := by rw [mul_conj, hω]; simp
    ext i j
    simp only [P, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul, smul_eq_mul,
      RCLike.star_def]
    linear_combination (w i * (starRingEnd ℂ) (w j)) * hωc
  have phase : ∀ u : Fin 2 × Fin 2 → ℂ, ∑ i, normSq (u i) = 1 → ∃ (z : Fin 4 → ℂ) (C : ℝ),
      P (mg z) = P u ∧ ∑ i, z i ^ 2 = (C : ℂ) ∧ 0 ≤ C ∧ C ≤ 1 ∧ ∑ i, normSq (z i) = 1 := by
    intro u hu
    obtain ⟨z0, hz0⟩ := mg_inv u
    set w := ∑ i, z0 i ^ 2 with hw
    set ω : ℂ := exp (((-(arg w / 2) : ℝ) : ℂ) * I) with hω
    have hω1 : normSq ω = 1 := by
      rw [hω, normSq_eq_norm_sq, norm_exp_ofReal_mul_I]; norm_num
    have hωw : ω ^ 2 * w = (‖w‖ : ℂ) := by
      have hw' : w = (‖w‖ : ℂ) * exp ((arg w : ℂ) * I) := (norm_mul_exp_arg_mul_I w).symm
      have h1 : ω ^ 2 * exp ((arg w : ℂ) * I) = 1 := by
        rw [hω, ← exp_nat_mul, ← exp_add]; push_cast; ring_nf; simp
      calc ω ^ 2 * w = (‖w‖ : ℂ) * (ω ^ 2 * exp ((arg w : ℂ) * I)) := by
            conv_lhs => rw [hw']
            ring
        _ = (‖w‖ : ℂ) := by rw [h1, mul_one]
    have hn0 : ∑ i, normSq (z0 i) = 1 := by rw [← mg_normSq, hz0, hu]
    refine ⟨ω • z0, ‖w‖, ?_, ?_, norm_nonneg _, ?_, ?_⟩
    · rw [mg_smul, hz0, P_smul _ _ hω1]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      exact hωw
    · calc ‖w‖ ≤ ∑ i, ‖z0 i ^ 2‖ := norm_sum_le _ _
        _ = ∑ i, normSq (z0 i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_pow, ← normSq_eq_norm_sq]
        _ = 1 := hn0
    · simp only [Pi.smul_apply, smul_eq_mul, normSq_mul, hω1, one_mul]
      exact hn0
  obtain ⟨zu, Cu, hPu, hzu, hCu0, hCu1, hnu⟩ := phase u hu
  obtain ⟨zv, Cv, hPv, hzv, hCv0, hCv1, hnv⟩ := phase v hv
  obtain ⟨r, s, hr, hs, hrs, hru, hsu, hrv, hsv⟩ :=
    orth (fun i => (zu i).re) (fun i => (zv i).re)
  set rc : Fin 4 → ℂ := fun i => (r i : ℂ) with hrc
  set sc : Fin 4 → ℂ := fun i => (s i : ℂ) with hsc
  set N := P (mg rc) + P (mg sc) with hN
  have hrr : ∑ i, rc i ^ 2 = 1 := by
    simp only [hrc, ← ofReal_pow, ← ofReal_sum, hr, ofReal_one]
  have hss : ∑ i, sc i ^ 2 = 1 := by
    simp only [hsc, ← ofReal_pow, ← ofReal_sum, hs, ofReal_one]
  have hrsc : ∑ i, rc i * sc i = 0 := by
    simp only [hrc, hsc, ← ofReal_mul, ← ofReal_sum, hrs, ofReal_zero]
  have hNcone : separableCone N := by
    have hw : ∀ ε : ℂ, ε ^ 2 = 1 → ∑ i, (rc + (ε * I) • sc) i ^ 2 = 0 := by
      intro ε hε
      have e : ∑ i, (rc + (ε * I) • sc) i ^ 2 = ∑ i, rc i ^ 2 +
          2 * (ε * I) * ∑ i, rc i * sc i + (ε * I) ^ 2 * ∑ i, sc i ^ 2 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, hrr, hss, hrsc]
      linear_combination (I ^ 2) * hε + I_sq
    have hsum : P (mg (rc + (1 * I) • sc)) + P (mg (rc + ((-1) * I) • sc)) =
        (2 : ℂ) • N := by
      ext i j
      simp only [hN, P, mg_add, mg_smul, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
        Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul, smul_eq_mul,
        RCLike.star_def, map_mul, conj_I, map_neg, map_one]
      linear_combination (-2 * mg sc i * (starRingEnd ℂ) (mg sc j)) * I_sq
    have : N = ((1 / 2 : ℝ) : ℂ) • (P (mg (rc + (1 * I) • sc)) +
        P (mg (rc + ((-1) * I) • sc))) := by
      rw [hsum, smul_smul]; norm_num
    rw [this]
    exact cone_smul _ _ (by norm_num)
      (separableCone_add (cone_sq _ (hw 1 (by norm_num))) (cone_sq _ (hw (-1) (by norm_num))))
  have trace_P : ∀ w : Fin 2 × Fin 2 → ℂ, (P w).trace = ((∑ i, normSq (w i) : ℝ) : ℂ) := by
    intro w
    simp only [P, trace, diag, vecMulVec_apply, Pi.star_apply, RCLike.star_def, mul_conj,
      ofReal_sum]
  have hnr : ∑ k, normSq (rc k) = 1 := by
    simp only [hrc, normSq_ofReal, ← sq]; exact hr
  have hns : ∑ k, normSq (sc k) = 1 := by
    simp only [hsc, normSq_ofReal, ← sq]; exact hs
  have hNtr : N.trace = 2 := by
    rw [hN, trace_add, trace_P, trace_P, mg_normSq, mg_normSq, hnr, hns]; norm_num
  set c := max Cu Cv with hc
  have hc0 : 0 ≤ c := le_max_of_le_left hCu0
  have hc1 : c ≤ 1 := max_le hCu1 hCv1
  set σ : (Fin 4 → ℂ) → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun z =>
    (((1 + c)⁻¹ : ℝ) : ℂ) • (P (mg z) + ((c / 2 : ℝ) : ℂ) • N) with hσ
  have hmem : ∀ (z : Fin 4 → ℂ) (C : ℝ), ∑ i, z i ^ 2 = (C : ℂ) → 0 ≤ C → C ≤ c →
      ∑ i, r i * (z i).re = 0 → ∑ i, s i * (z i).re = 0 → ∑ i, normSq (z i) = 1 →
      σ z ∈ separableStates := by
    intro z C hz hC0 hCc hzr hzs hzn
    have split : P (mg z) + ((c / 2 : ℝ) : ℂ) • N =
        ((1 / 2 : ℝ) : ℂ) • (P (mg z) + (C : ℂ) • P (mg rc)) +
          ((1 / 2 : ℝ) : ℂ) • (P (mg z) + (C : ℂ) • P (mg sc)) +
            (((c - C) / 2 : ℝ) : ℂ) • N := by
      rw [hN]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · refine cone_smul _ _ (inv_nonneg.mpr (by linarith)) ?_
      rw [split]
      exact separableCone_add
        (separableCone_add (cone_smul _ _ (by norm_num) (correction z C hz hC0 r hr hzr))
        (cone_smul _ _ (by norm_num) (correction z C hz hC0 s hs hzs)))
        (cone_smul _ _ (by linarith) hNcone)
    · rw [hσ]
      simp only [trace_smul, trace_add, trace_P, mg_normSq, hzn, hNtr, smul_eq_mul]
      push_cast
      field_simp
  refine ⟨c, hc0, hc1, σ zu, hmem zu Cu hzu hCu0 (le_max_left _ _) hru hsu hnu,
    σ zv, hmem zv Cv hzv hCv0 (le_max_right _ _) hrv hsv hnv, ?_⟩
  rw [← hPu, ← hPv, hσ]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  have : (1 + c : ℂ) ≠ 0 := by exact_mod_cast (show (1 + c : ℝ) ≠ 0 by linarith)
  push_cast
  field_simp
  ring

/-- The bound `vol L(A) ≤ 2 vol L_Sep(A)` and its attainment by the Bell projector. -/
theorem result : claim := by
  have trace_P : ∀ w : Fin 2 × Fin 2 → ℂ, (P w).trace = ((∑ i, normSq (w i) : ℝ) : ℂ) := by
    intro w
    simp only [P, trace, diag, vecMulVec_apply, Pi.star_apply, RCLike.star_def, mul_conj,
      ofReal_sum]
  have rsmul : ∀ (t : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), t • M = (t : ℂ) • M := by
    intro t M; ext i j; simp [Complex.real_smul]
  -- expectation values
  set f : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ → ℝ :=
    fun A ρ => (ρ * A).trace.re with hf
  have f_add : ∀ A ρ ρ', f A (ρ + ρ') = f A ρ + f A ρ' := by
    intro A ρ ρ'; simp [hf, add_mul, trace_add]
  have f_smul : ∀ A (t : ℝ) ρ, f A ((t : ℂ) • ρ) = t * f A ρ := by
    intro A t ρ; simp [hf, trace_smul]
  have f_sub : ∀ A ρ ρ', f A (ρ - ρ') = f A ρ - f A ρ' := by
    intro A ρ ρ'; simp [hf, sub_mul, trace_sub]
  have f_sum : ∀ A {ι : Type} [Fintype ι] (g : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      f A (∑ k, g k) = ∑ k, f A (g k) := by
    intro A ι _ g; simp [hf, Finset.sum_mul, trace_sum, re_sum]
  -- every state is a convex combination of pure states
  have decomp : ∀ ρ ∈ states, ∃ (l : Fin 2 × Fin 2 → ℝ) (w : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ),
      (∀ k, 0 ≤ l k) ∧
      ∑ k, l k = 1 ∧ (∀ k, ∑ i, normSq (w k i) = 1) ∧ ρ = ∑ k, (l k : ℂ) • P (w k) := by
    rintro ρ ⟨hρ, htr⟩
    have hH := hρ.isHermitian
    refine ⟨hH.eigenvalues, fun k => ⇑(hH.eigenvectorBasis k), fun k => hρ.eigenvalues_nonneg k,
      ?_, ?_, ?_⟩
    · have := congrArg Complex.re hH.trace_eq_sum_eigenvalues
      simpa [htr] using this.symm
    · intro k
      have h := hH.eigenvectorBasis.inner_eq_one k
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h
      have h' : ((∑ i, normSq ((hH.eigenvectorBasis k) i) : ℝ) : ℂ) = 1 := by
        rw [← h]
        simp [dotProduct, mul_conj]
      exact_mod_cast h'
    · conv_lhs => rw [hH.spectral_theorem]
      ext i j
      simp only [Unitary.conjStarAlgAut_apply, mul_apply, diagonal_apply, Function.comp_apply,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_apply,
        IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply, Matrix.smul_apply, P,
        vecMulVec_apply,
        Pi.star_apply, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
      refine Finset.sum_congr rfl fun k _ => by ring
  have unit_P : ∀ w : Fin 2 × Fin 2 → ℂ, ∑ i, normSq (w i) = 1 → P w ∈ states := by
    intro w hw
    refine ⟨posSemidef_vecMulVec_self_star w, ?_⟩
    rw [trace_P, hw]; simp
  have f_state : ∀ A, ∀ ρ ∈ states, ∃ (l : Fin 2 × Fin 2 → ℝ)
      (w : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ), (∀ k, 0 ≤ l k) ∧
      ∑ k, l k = 1 ∧ (∀ k, ∑ i, normSq (w k i) = 1) ∧ f A ρ = ∑ k, l k * f A (P (w k)) := by
    intro A ρ hρ
    obtain ⟨l, w, hl, hl1, hw, hρw⟩ := decomp ρ hρ
    refine ⟨l, w, hl, hl1, hw, ?_⟩
    rw [hρw, f_sum]
    exact Finset.sum_congr rfl fun k _ => f_smul _ _ _
  -- boundedness
  have bound : ∀ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ∀ ρ ∈ states,
      |f A ρ| ≤ ∑ i, ∑ j, ‖A j i‖ := by
    intro A ρ hρ
    have hpure : ∀ w : Fin 2 × Fin 2 → ℂ, ∑ i, normSq (w i) = 1 →
        |f A (P w)| ≤ ∑ i, ∑ j, ‖A j i‖ := by
      intro w hw
      have hwi : ∀ i, ‖w i‖ ≤ 1 := by
        intro i
        have : normSq (w i) ≤ 1 := hw ▸ Finset.single_le_sum
          (fun j _ => normSq_nonneg (w j)) (Finset.mem_univ i)
        rw [normSq_eq_norm_sq] at this
        nlinarith [norm_nonneg (w i)]
      calc |f A (P w)| ≤ ‖(P w * A).trace‖ := abs_re_le_norm _
        _ = ‖∑ i, ∑ j, P w i j * A j i‖ := by simp only [Matrix.trace, Matrix.diag, mul_apply]
        _ ≤ ∑ i, ∑ j, ‖P w i j * A j i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
        _ ≤ ∑ i, ∑ j, ‖A j i‖ := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          have : ‖P w i j‖ ≤ 1 := by
            simp only [P, vecMulVec_apply, Pi.star_apply, norm_mul, norm_star]
            exact mul_le_one₀ (hwi i) (norm_nonneg _) (hwi j)
          nlinarith [norm_nonneg (A j i), norm_nonneg (P w i j)]
    obtain ⟨l, w, hl, hl1, hw, hfρ⟩ := f_state A ρ hρ
    rw [hfρ]
    calc |∑ k, l k * f A (P (w k))| ≤ ∑ k, |l k * f A (P (w k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, l k * ∑ i, ∑ j, ‖A j i‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (hl k)]
          exact mul_le_mul_of_nonneg_left (hpure _ (hw k)) (hl k)
      _ = ∑ i, ∑ j, ‖A j i‖ := by rw [← Finset.sum_mul, hl1, one_mul]
  have sep_sub : separableStates ⊆ states := fun ρ hρ => ⟨separable_isPosSemidef hρ.1, hρ.2⟩
  have conv_image : ∀ (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (X : Set (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)),
      Convex ℝ X →
      Convex ℝ (numericalRange X A) := by
    rintro A X hX _ ⟨ρ, hρ, rfl⟩ _ ⟨ρ', hρ', rfl⟩ a b ha hb hab
    refine ⟨a • ρ + b • ρ', hX hρ hρ' ha hb hab, ?_⟩
    change f A (a • ρ + b • ρ') = a • f A ρ + b • f A ρ'
    rw [f_add, rsmul a, rsmul b, f_smul, f_smul, smul_eq_mul, smul_eq_mul]
  have conv_sep : Convex ℝ separableStates := by
    rintro ρ ⟨hρ, htr⟩ ρ' ⟨hρ', htr'⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · exact separableCone_add (separableCone_smul ha hρ) (separableCone_smul hb hρ')
    · rw [trace_add, trace_smul, trace_smul, htr, htr']
      simp [Complex.real_smul, ← ofReal_add, hab]
  have conv_states : Convex ℝ states := by
    rintro ρ ⟨hρ, htr⟩ ρ' ⟨hρ', htr'⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · rw [rsmul, rsmul]
      exact (hρ.smul (by exact_mod_cast ha)).add (hρ'.smul (by exact_mod_cast hb))
    · rw [trace_add, trace_smul, trace_smul, htr, htr']
      simp [Complex.real_smul, ← ofReal_add, hab]
  -- a separable state
  set e : Fin 2 × Fin 2 → ℂ := Pi.single (0, 0) 1 with he
  have he1 : ∑ i, normSq (e i) = 1 := by
    simp [he, Pi.single_apply]
  obtain ⟨-, -, -, σ₀, hσ₀, -⟩ := pure_pair e e he1 he1
  -- the lower bound
  have lower : ∀ A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, A.IsHermitian →
      volume (numericalRange states A) ≠ 0 →
      1 / 2 ≤ volume (numericalRange separableStates A) / volume (numericalRange states A) := by
    intro A _ h0
    set K := ∑ i, ∑ j, ‖A j i‖
    set L := numericalRange states A with hL
    set S := numericalRange separableStates A with hS
    have hLb : L ⊆ Icc (-K) K := by
      rintro _ ⟨ρ, hρ, rfl⟩; exact abs_le.mp (bound A ρ hρ)
    have hSL : S ⊆ L := image_mono sep_sub
    have hSb : S ⊆ Icc (-K) K := hSL.trans hLb
    have hSne : S.Nonempty := ⟨_, ⟨σ₀, hσ₀, rfl⟩⟩
    have hSa : BddAbove S := ⟨K, fun x hx => (hSb hx).2⟩
    have hSbl : BddBelow S := ⟨-K, fun x hx => (hSb hx).1⟩
    set D := sSup S - sInf S with hD
    have hD0 : 0 ≤ D := by
      obtain ⟨x, hx⟩ := hSne
      have h1 := csInf_le hSbl hx
      have h2 := le_csSup hSa hx
      linarith
    have hpure : ∀ u v : Fin 2 × Fin 2 → ℂ, ∑ i, normSq (u i) = 1 → ∑ i, normSq (v i) = 1 →
        f A (P u) - f A (P v) ≤ 2 * D := by
      intro u v hu hv
      obtain ⟨c, hc0, hc1, σ, hσ, τ, hτ, hP⟩ := pure_pair u v hu hv
      have hfe : f A (P u) - f A (P v) = (1 + c) * (f A σ - f A τ) := by
        rw [← f_sub, hP, f_smul, f_sub]
      have h1 : f A σ ≤ sSup S := le_csSup hSa ⟨σ, hσ, rfl⟩
      have h2 : sInf S ≤ f A τ := csInf_le hSbl ⟨τ, hτ, rfl⟩
      rw [hfe]
      nlinarith
    have hmixed : ∀ ρ ∈ states, ∀ ρ' ∈ states, f A ρ - f A ρ' ≤ 2 * D := by
      intro ρ hρ ρ' hρ'
      obtain ⟨l, w, hl, hl1, hw, hfρ⟩ := f_state A ρ hρ
      obtain ⟨m, w', hm, hm1, hw', hfρ'⟩ := f_state A ρ' hρ'
      have e1 : f A ρ = ∑ k, ∑ k', l k * m k' * f A (P (w k)) := by
        rw [hfρ]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, hm1, mul_one]
      have e2 : f A ρ' = ∑ k, ∑ k', l k * m k' * f A (P (w' k')) := by
        rw [hfρ', Finset.sum_comm]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, hl1, one_mul]
      have e3 : ∑ k, ∑ k', l k * m k' * (2 * D) = 2 * D := by
        calc ∑ k, ∑ k', l k * m k' * (2 * D) = ∑ k, l k * (2 * D) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Finset.sum_mul, ← Finset.mul_sum, hm1, mul_one]
          _ = 2 * D := by rw [← Finset.sum_mul, hl1, one_mul]
      rw [e1, e2, ← e3, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun k' _ => ?_
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left (hpure _ _ (hw k) (hw' k')) (mul_nonneg (hl k) (hm k'))
    have hdiam : Metric.ediam L ≤ ENNReal.ofReal (2 * D) := by
      refine Metric.ediam_le_of_forall_dist_le ?_
      rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨ρ', hρ', rfl⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hmixed ρ hρ ρ' hρ', hmixed ρ' hρ' ρ hρ]
    have hvolL : volume L ≤ ENNReal.ofReal (2 * D) := (Real.volume_le_diam L).trans hdiam
    have hvolS : ENNReal.ofReal D ≤ volume S := by
      have hc : IsConnected S := ⟨hSne, (conv_image A _ conv_sep).isPreconnected⟩
      calc ENNReal.ofReal D = volume (Ioo (sInf S) (sSup S)) := by rw [Real.volume_Ioo]
        _ ≤ volume S := measure_mono (hc.Ioo_csInf_csSup_subset hSbl hSa)
    have hLtop : volume L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolL
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hLtop)]
    calc 1 / 2 * volume L ≤ 1 / 2 * ENNReal.ofReal (2 * D) := by gcongr
      _ = ENNReal.ofReal D := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← mul_assoc,
            one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ volume S := hvolS
  -- the Bell projector attains the bound
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  set φ : Fin 2 × Fin 2 → ℂ := fun ij => if ij.1 = ij.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0
    with hφ
  have hφ1 : ∑ i, normSq (φ i) = 1 := by
    simp only [hφ, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [normSq_ofReal, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  set A := P φ with hA
  have hAH : A.IsHermitian := (posSemidef_vecMulVec_self_star φ).isHermitian
  have fA_pure : ∀ w : Fin 2 × Fin 2 → ℂ, f A (P w) = normSq (star w ⬝ᵥ φ) := by
    intro w
    simp only [hf, hA, P, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul,
      smul_eq_mul]
    have : w ⬝ᵥ star φ = (starRingEnd ℂ) (star w ⬝ᵥ φ) := by
      simp [dotProduct, map_sum, mul_comm]
    rw [this, mul_conj, ofReal_re]
  have hφS : f A (P φ) = 1 := by
    rw [fA_pure]
    have : star φ ⬝ᵥ φ = ((∑ i, normSq (φ i) : ℝ) : ℂ) := by
      simp [dotProduct, normSq_eq_conj_mul_self]
    rw [this, hφ1]; simp
  set e01 : Fin 2 × Fin 2 → ℂ := Pi.single (0, 1) 1 with he01
  have he01n : ∑ i, normSq (e01 i) = 1 := by
    simp [he01, Pi.single_apply]
  have he01f : f A (P e01) = 0 := by
    rw [fA_pure]
    simp [dotProduct, he01, hφ, Pi.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hL1 : Icc 0 1 ⊆ numericalRange states A := by
    have h1 : (1 : ℝ) ∈ numericalRange states A := ⟨P φ, unit_P φ hφ1, hφS⟩
    have h0 : (0 : ℝ) ∈ numericalRange states A := ⟨P e01, unit_P _ he01n, he01f⟩
    rw [← segment_eq_Icc zero_le_one]
    exact (conv_image A _ conv_states).segment_subset h0 h1
  have hvolL : 1 ≤ volume (numericalRange states A) := by
    calc (1 : ℝ≥0∞) = volume (Icc (0 : ℝ) 1) := by simp [Real.volume_Icc]
      _ ≤ _ := measure_mono hL1
  have hL0 : volume (numericalRange states A) ≠ 0 := (zero_lt_one.trans_le hvolL).ne'
  have hss : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← sq, hs2]; norm_num
  have hprod : ∀ B C : Matrix (Fin 2) (Fin 2) ℂ, B.PosSemidef → C.PosSemidef →
      f A (B ⊗ₖ C) ≤ 1 / 2 * ((B.trace).re * (C.trace).re) := by
    intro B C hB hC
    have hval : (B ⊗ₖ C * A).trace =
        (B 0 0 * C 0 0 + B 0 1 * C 0 1 + B 1 0 * C 1 0 + B 1 1 * C 1 1) / 2 := by
      simp only [hA, P, trace, diag, mul_apply, vecMulVec_apply, Pi.star_apply, hφ,
        Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply]
      simp [conj_ofReal]
      linear_combination (B 0 0 * C 0 0 + B 0 1 * C 0 1 + B 1 0 * C 1 0 + B 1 1 * C 1 1) * hss
    have hdiag : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.PosSemidef → ∀ i,
        0 ≤ (M i i).re ∧ (M i i).im = 0 := by
      intro M hM i
      have := hM.diag_nonneg (i := i)
      rw [Complex.le_def] at this
      exact ⟨by simpa using this.1, by simpa using this.2.symm⟩
    have hoff : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), M.PosSemidef →
        M 1 0 = (starRingEnd ℂ) (M 0 1) ∧ normSq (M 0 1) ≤ (M 0 0).re * (M 1 1).re := by
      intro M hM
      have h10 : M 1 0 = (starRingEnd ℂ) (M 0 1) := (hM.isHermitian.apply 1 0).symm
      refine ⟨h10, ?_⟩
      have hdet := hM.det_nonneg
      rw [det_fin_two, h10, mul_conj, Complex.le_def] at hdet
      obtain ⟨h00, h00'⟩ := hdiag M hM 0
      obtain ⟨h11, h11'⟩ := hdiag M hM 1
      have := hdet.1
      simp only [sub_re, mul_re, ofReal_re, h00', h11', mul_zero, sub_zero, zero_re] at this
      linarith
    obtain ⟨hb0, hb0'⟩ := hdiag B hB 0
    obtain ⟨hb1, hb1'⟩ := hdiag B hB 1
    obtain ⟨hc0, hc0'⟩ := hdiag C hC 0
    obtain ⟨hc1, hc1'⟩ := hdiag C hC 1
    obtain ⟨hB10, hBd⟩ := hoff B hB
    obtain ⟨hC10, hCd⟩ := hoff C hC
    have hf' : f A (B ⊗ₖ C) = ((B 0 0).re * (C 0 0).re + (B 1 1).re * (C 1 1).re +
        2 * ((B 0 1).re * (C 0 1).re - (B 0 1).im * (C 0 1).im)) / 2 := by
      simp only [hf]
      rw [hval, hB10, hC10]
      simp [mul_re, hb0', hb1', hc0', hc1', conj_re, conj_im, add_re]
      ring
    have htrB : (B.trace).re = (B 0 0).re + (B 1 1).re := by simp [trace, Fin.sum_univ_two]
    have htrC : (C.trace).re = (C 0 0).re + (C 1 1).re := by simp [trace, Fin.sum_univ_two]
    rw [hf', htrB, htrC]
    rw [normSq_apply] at hBd hCd
    set x1 := (B 0 1).re
    set x2 := (B 0 1).im
    set y1 := (C 0 1).re
    set y2 := (C 0 1).im
    set a := (B 0 0).re
    set d := (B 1 1).re
    set e := (C 0 0).re
    set g := (C 1 1).re
    have hXY : (x1 * y1 - x2 * y2) ^ 2 ≤ (a * g) * (d * e) := by
      have h1 : (x1 * y1 - x2 * y2) ^ 2 ≤ (x1 * x1 + x2 * x2) * (y1 * y1 + y2 * y2) := by
        nlinarith [sq_nonneg (x1 * y2 + x2 * y1)]
      have h2 : (x1 * x1 + x2 * x2) * (y1 * y1 + y2 * y2) ≤ (a * d) * (e * g) :=
        mul_le_mul hBd hCd (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
          (mul_nonneg hb0 hb1)
      nlinarith
    have hag : 0 ≤ a * g := mul_nonneg hb0 hc1
    have hde : 0 ≤ d * e := mul_nonneg hb1 hc0
    nlinarith [sq_nonneg (a * g - d * e), sq_nonneg (2 * (x1 * y1 - x2 * y2) - (a * g + d * e))]
  have hS : numericalRange separableStates A ⊆ Icc 0 (1 / 2) := by
    rintro _ ⟨ρ, ⟨hρ, htr⟩, rfl⟩
    have hpsd := separable_isPosSemidef hρ
    constructor
    · change 0 ≤ f A ρ
      have : f A ρ = RCLike.re (star φ ⬝ᵥ (ρ *ᵥ φ)) := by
        simp only [hf, hA, P]
        rw [trace_mul_comm, vecMulVec_mul, trace_vecMulVec, dotProduct_comm,
          ← dotProduct_mulVec]
        rfl
      rw [this]; exact hpsd.re_dotProduct_nonneg φ
    · change f A ρ ≤ 1 / 2
      obtain ⟨k, B, C, hBC, rfl⟩ := hρ
      have htr' : ∑ i, (B i).trace.re * (C i).trace.re = 1 := by
        have h := congrArg Complex.re htr
        rw [trace_sum, re_sum] at h
        simp only [trace_kronecker, mul_re, one_re] at h
        have him : ∀ i, (B i).trace.im = 0 := fun i => by
          have := (hBC i).1.trace_nonneg; rw [Complex.le_def] at this; simpa using this.2.symm
        simpa [him] using h
      calc f A (∑ i, B i ⊗ₖ C i) = ∑ i, f A (B i ⊗ₖ C i) := f_sum A _
        _ ≤ ∑ i, 1 / 2 * ((B i).trace.re * (C i).trace.re) :=
            Finset.sum_le_sum fun i _ => hprod _ _ (hBC i).1 (hBC i).2
        _ = 1 / 2 := by rw [← Finset.mul_sum, htr', mul_one]
  have hvolS : volume (numericalRange separableStates A) ≤ 1 / 2 := by
    refine (measure_mono hS).trans ?_
    rw [Real.volume_Icc, sub_zero, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat, one_div]
  have hupper : volume (numericalRange separableStates A) / volume (numericalRange states A) ≤
      1 / 2 := by
    calc _ ≤ (1 / 2) / 1 := ENNReal.div_le_div hvolS hvolL
      _ = 1 / 2 := by simp
  refine ⟨⟨A, hAH, hL0, (le_antisymm hupper (lower A hAH hL0)).symm⟩, ?_⟩
  rintro r ⟨B, hB, h0, rfl⟩
  exact lower B hB h0

end D5.S3.Quantum.Entanglement.SeparableNumericalRangeRatio
