/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: The identity plus twice any normalized bipartite rank-one matrix is separable. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays

open scoped BigOperators Kronecker ComplexOrder ComplexConjugate
open Matrix Metric Set
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRaysAverages

private theorem norm_le_of_unit_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (q : E) (a : ℝ) (ha : 0 ≤ a)
    (hmax : ∀ w : E, ‖w‖ = 1 → (inner ℂ w q).re ≤ a) : ‖q‖ ≤ a := by
  by_cases hq : q = 0
  · simpa [hq] using ha
  · have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
    have h := hmax ((‖q‖⁻¹ : ℂ) • q) (norm_smul_inv_norm hq)
    have hid : (inner ℂ ((‖q‖⁻¹ : ℂ) • q) q).re = ‖q‖ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        Complex.re_ofReal_mul]
      have hself : (inner ℂ q q).re = ‖q‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) q).symm
      rw [hself]
      simp [pow_two, hqn]
    simpa only [hid] using h

private theorem support_max_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (q u : E) (hu : ‖u‖ = 1)
    (hmax : ∀ w : E, ‖w‖ = 1 → (inner ℂ w q).re ≤ (inner ℂ u q).re) :
    0 ≤ (inner ℂ u q).re ∧ q = ((inner ℂ u q).re : ℂ) • u := by
  by_cases hq : q = 0
  · subst q
    simp
  · let a := (inner ℂ u q).re
    have hbound : ‖q‖ ≤ a :=
      norm_le_of_unit_support q a
        (by
          have h := hmax (-u) (by simpa using hu)
          simp only [inner_neg_left, Complex.neg_re] at h
          dsimp [a]
          linarith)
        hmax
    have ha : 0 ≤ a := le_trans (norm_nonneg q) hbound
    refine ⟨ha, ?_⟩
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ) (x := q) (y := (a : ℂ) • u)
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, hu, mul_one]
      exact hbound
    · change (inner ℂ q ((a : ℂ) • u)).re = ‖(a : ℂ) • u‖ ^ 2
      have hsym : (inner ℂ q u).re = (inner ℂ u q).re := inner_re_symm (𝕜 := ℂ) q u
      rw [inner_smul_right, Complex.re_ofReal_mul, hsym, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, hu, mul_one]
      change a * a = a ^ 2
      simp [pow_two]

private theorem exists_maximizing_pair
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [Nontrivial E] [Nontrivial F]
    (qA : F → E) (qB : E → F) (hcont : Continuous qA)
    (hswap : ∀ u v, inner ℂ u (qA v) = inner ℂ v (qB u))
    (hscale : ∀ (r : ℝ) b, qA ((r : ℂ) • b) = (r : ℂ) • qA b) :
    ∃ (u : E) (v : F) (a : ℝ), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ 0 ≤ a ∧
      qA v = (a : ℂ) • u ∧ qB u = (a : ℂ) • v ∧
      (∀ b, ‖qA b‖ ≤ a * ‖b‖) := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  let : ProperSpace F := FiniteDimensional.proper ℂ F
  let s : Set (E × F) := sphere 0 1 ×ˢ sphere 0 1
  let f : E × F → ℝ := fun z => (inner ℂ z.1 (qA z.2)).re
  have hs : IsCompact s := (isCompact_sphere (0 : E) 1).prod (isCompact_sphere (0 : F) 1)
  have hne : s.Nonempty := by
    obtain ⟨⟨u, hu⟩⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := E) zero_le_one
    obtain ⟨⟨v, hv⟩⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := F) zero_le_one
    exact ⟨(u, v), hu, hv⟩
  have hc : Continuous f := Complex.continuous_re.comp
    (continuous_fst.inner (hcont.comp continuous_snd))
  obtain ⟨⟨u, v⟩, huv, hmax⟩ := hs.exists_isMaxOn hne hc.continuousOn
  have hmax' : ∀ z ∈ s, f z ≤ f (u, v) := Filter.eventually_principal.mp hmax
  have hu : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp huv.1
  have hv : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp huv.2
  let a := (inner ℂ u (qA v)).re
  have hA := support_max_eq (qA v) u hu (fun w hw =>
    hmax' (w, v) ⟨mem_sphere_zero_iff_norm.mpr hw, huv.2⟩)
  have hB := support_max_eq (qB u) v hv (by
    intro w hw
    simpa only [f, hswap] using hmax' (u, w) ⟨huv.1, mem_sphere_zero_iff_norm.mpr hw⟩)
  refine ⟨u, v, a, hu, hv, hA.1, hA.2, ?_, ?_⟩
  · simpa only [a, hswap] using hB.2
  · intro b
    by_cases hb : b = 0
    · subst b
      have hzero : qA 0 = 0 := by simpa using hscale 0 (0 : F)
      simp [hzero]
    · let w : F := (‖b‖⁻¹ : ℂ) • b
      have hw : ‖w‖ = 1 := norm_smul_inv_norm hb
      have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
      have hbnd : ‖qA w‖ ≤ a := norm_le_of_unit_support (qA w) a hA.1 (by
        intro z hz
        exact hmax' (z, w) ⟨mem_sphere_zero_iff_norm.mpr hz, mem_sphere_zero_iff_norm.mpr hw⟩)
      dsimp [w] at hbnd
      rw [← Complex.ofReal_inv, hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_norm] at hbnd
      calc
        ‖qA b‖ = (‖b‖⁻¹ * ‖qA b‖) * ‖b‖ := by
          rw [mul_comm ‖b‖⁻¹, mul_assoc, inv_mul_cancel₀ hbpos.ne', mul_one]
        _ ≤ a * ‖b‖ := mul_le_mul_of_nonneg_right hbnd hbpos.le

private theorem exists_product_max {m n : ℕ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (ψ : Fin m × Fin n → ℂ) :
    ∃ (u : Fin m → ℂ) (v : Fin n → ℂ) (a : ℝ),
      (∑ i, ‖u i‖ ^ 2) = 1 ∧ (∑ j, ‖v j‖ ^ 2) = 1 ∧ 0 ≤ a ∧
      (∀ i, ∑ j, ψ (i, j) * conj (v j) = (a : ℂ) * u i) ∧
      (∀ j, ∑ i, ψ (i, j) * conj (u i) = (a : ℂ) * v j) ∧
      (∀ b : Fin n → ℂ,
        (∑ i, ‖∑ j, ψ (i, j) * conj (b j)‖ ^ 2) ≤ a ^ 2 * ∑ j, ‖b j‖ ^ 2) := by
  let qA : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m) :=
    fun b => WithLp.toLp 2 (fun i => ∑ j, ψ (i, j) * conj (b j))
  let qB : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin n) :=
    fun a => WithLp.toLp 2 (fun j => ∑ i, ψ (i, j) * conj (a i))
  have hcont : Continuous qA := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℂ)).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).star)
  have hswap : ∀ u v, inner ℂ u (qA v) = inner ℂ v (qB u) := by
    intro u v
    simp only [PiLp.inner_apply, RCLike.inner_apply', qA, qB,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hscale : ∀ (r : ℝ) b, qA ((r : ℂ) • b) = (r : ℂ) • qA b := by
    intro r b
    ext i
    simp only [qA, PiLp.smul_apply, smul_eq_mul, map_mul,
      Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  obtain ⟨u, v, a, hu, hv, ha, hA, hB, hbnd⟩ :=
    exists_maximizing_pair qA qB hcont hswap hscale
  refine ⟨u, v, a, ?_, ?_, ha, ?_, ?_, ?_⟩
  · simpa [hu] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin m => ℂ) u).symm
  · simpa [hv] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℂ) v).symm
  · intro i
    exact congrArg (fun z : EuclideanSpace ℂ (Fin m) => z i) hA
  · intro j
    exact congrArg (fun z : EuclideanSpace ℂ (Fin n) => z j) hB
  · intro b
    have h := hbnd (WithLp.toLp 2 b)
    have hsq : ‖qA (WithLp.toLp 2 b)‖ ^ 2 ≤ (a * ‖WithLp.toLp 2 b‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mpr h
    simpa only [mul_pow, PiLp.norm_sq_eq_of_L2, qA, PiLp.toLp_apply] using hsq

private theorem exists_product_max_of_normalized {m n : ℕ}
    (ψ : Fin m × Fin n → ℂ) (hψ : (∑ x, ‖ψ x‖ ^ 2) = 1) :
    ∃ (u : Fin m → ℂ) (v : Fin n → ℂ) (a : ℝ),
      (∑ i, ‖u i‖ ^ 2) = 1 ∧ (∑ j, ‖v j‖ ^ 2) = 1 ∧ 0 ≤ a ∧
      (∀ i, ∑ j, ψ (i, j) * conj (v j) = (a : ℂ) * u i) ∧
      (∀ j, ∑ i, ψ (i, j) * conj (u i) = (a : ℂ) * v j) ∧
      (∀ b : Fin n → ℂ,
        (∑ i, ‖∑ j, ψ (i, j) * conj (b j)‖ ^ 2) ≤ a ^ 2 * ∑ j, ‖b j‖ ^ 2) := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    simp at hψ
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp at hψ
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact exists_product_max ψ

private theorem rankOne_residual_properties {m n : ℕ}
    (ψ : Fin m × Fin n → ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ) (a : ℝ)
    (hψ : (∑ x, ‖ψ x‖ ^ 2) = 1) (hu : (∑ i, ‖u i‖ ^ 2) = 1)
    (hv : (∑ j, ‖v j‖ ^ 2) = 1)
    (hA : ∀ i, ∑ j, ψ (i, j) * conj (v j) = (a : ℂ) * u i)
    (hB : ∀ j, ∑ i, ψ (i, j) * conj (u i) = (a : ℂ) * v j) :
    let χ : Fin m × Fin n → ℂ := fun x => ψ x - (a : ℂ) * u x.1 * v x.2
    (∀ i, ∑ j, χ (i, j) * conj (v j) = 0) ∧
    (∀ j, ∑ i, χ (i, j) * conj (u i) = 0) ∧
    (∑ x, ‖χ x‖ ^ 2) = 1 - a ^ 2 := by
  classical
  let χ : Fin m × Fin n → ℂ := fun x => ψ x - (a : ℂ) * u x.1 * v x.2
  have hsumU : (∑ i, u i * conj (u i)) = (1 : ℂ) := by
    calc
      _ = ∑ i, ((‖u i‖ ^ 2 : ℝ) : ℂ) := Finset.sum_congr rfl fun i _ => by
        simpa only [Complex.ofReal_pow] using Complex.mul_conj' (u i)
      _ = 1 := by rw [← Complex.ofReal_sum, hu]; rfl
  have hsumV : (∑ j, v j * conj (v j)) = (1 : ℂ) := by
    calc
      _ = ∑ j, ((‖v j‖ ^ 2 : ℝ) : ℂ) := Finset.sum_congr rfl fun j _ => by
        simpa only [Complex.ofReal_pow] using Complex.mul_conj' (v j)
      _ = 1 := by rw [← Complex.ofReal_sum, hv]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (∑ j, (ψ (i, j) - (a : ℂ) * u i * v j) * conj (v j)) = 0
    calc
      _ = (∑ j, ψ (i, j) * conj (v j)) -
          ((a : ℂ) * u i) * ∑ j, v j * conj (v j) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [hA, hsumV]; simp
  · intro j
    change (∑ i, (ψ (i, j) - (a : ℂ) * u i * v j) * conj (u i)) = 0
    calc
      _ = (∑ i, ψ (i, j) * conj (u i)) -
          ((a : ℂ) * v j) * ∑ i, u i * conj (u i) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hB, hsumU]; simp
  · let p : EuclideanSpace ℂ (Fin m × Fin n) := WithLp.toLp 2 ψ
    let r : EuclideanSpace ℂ (Fin m × Fin n) :=
      WithLp.toLp 2 (fun x => u x.1 * v x.2)
    have hp : ‖p‖ ^ 2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      exact hψ
    have hr : ‖r‖ ^ 2 = 1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [r, norm_mul, mul_pow, Fintype.sum_prod_type,
        ← Finset.mul_sum, hv, mul_one, hu]
    have hip : inner ℂ r p = (a : ℂ) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply', r, p,
        Fintype.sum_prod_type, map_mul]
      calc
        _ = ∑ i, conj (u i) * ∑ j, ψ (i, j) * conj (v j) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (a : ℂ) * ∑ i, u i * conj (u i) := by
          simp only [hA, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (a : ℂ) := by rw [hsumU, mul_one]
    have hinner : (inner ℂ p ((a : ℂ) • r)).re = a ^ 2 := by
      have hsym : (inner ℂ p r).re = (inner ℂ r p).re := inner_re_symm (𝕜 := ℂ) p r
      rw [inner_smul_right, Complex.re_ofReal_mul, hsym, hip, Complex.ofReal_re]
      simp [pow_two]
    have hnorm : ‖(a : ℂ) • r‖ ^ 2 = a ^ 2 := by
      rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hr, mul_one]
    have h := norm_sub_sq (𝕜 := ℂ) p ((a : ℂ) • r)
    rw [hp, hnorm] at h
    change ‖p - (a : ℂ) • r‖ ^ 2 = 1 - 2 * (inner ℂ p ((a : ℂ) • r)).re + a ^ 2 at h
    rw [hinner] at h
    have hsame : WithLp.toLp 2 χ = p - (a : ℂ) • r := by
      ext x
      simp [χ, p, r, mul_assoc]
    rw [← hsame, PiLp.norm_sq_eq_of_L2] at h
    change (∑ x, ‖χ x‖ ^ 2) = _ at h
    nlinarith


private lemma dot_star_self {J : Type*} [Fintype J] (x : J → ℂ) :
    star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

private lemma cs_sq {J : Type*} [Fintype J] (d x : J → ℂ) :
    ‖star d ⬝ᵥ x‖ ^ 2 ≤ (∑ j, ‖d j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 d) (WithLp.toLp 2 x)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply] using hsq

private lemma rank_one_upper {J : Type*} [Fintype J] [DecidableEq J] (d : J → ℂ) :
    (((∑ j, ‖d j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix J J ℂ) -
      vecMulVec d (star d)).PosSemidef := by
  let t : ℝ := ∑ j, ‖d j‖ ^ 2
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((PosSemidef.one.smul (Complex.zero_le_real.mpr ht)).1.sub
      (posSemidef_vecMulVec_self_star d).1) ?_
  intro x
  have hstar : star x ⬝ᵥ d = star (star d ⬝ᵥ x) := by
    exact star_dotProduct x d
  have heq : star x ⬝ᵥ (((t : ℂ) • (1 : Matrix J J ℂ) -
      vecMulVec d (star d)) *ᵥ x) =
      ((t * (∑ j, ‖x j‖ ^ 2) - ‖star d ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, hstar]
    rw [dot_star_self, Complex.star_def, Complex.conj_mul']
    simp
  rw [heq]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (cs_sq d x))

private lemma gram_upper {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (d : I → J → ℂ) :
    (((∑ i, ∑ j, ‖d i j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix J J ℂ) -
      ∑ i, vecMulVec (d i) (star (d i))).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ (fun i _ => rank_one_upper (d i))
  convert h using 1
  simp [Finset.sum_sub_distrib, ← Finset.sum_smul]

private lemma rank_one_idem {J : Type*} [Fintype J] (v : J → ℂ)
    (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    vecMulVec v (star v) * vecMulVec v (star v) = vecMulVec v (star v) := by
  rw [vecMulVec_mul_vecMulVec, dot_star_self, hv]
  simp

private lemma complement_idem {J : Type*} [Fintype J] [DecidableEq J] (v : J → ℂ)
    (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    (1 - vecMulVec v (star v)) * (1 - vecMulVec v (star v)) =
      (1 - vecMulVec v (star v)) :=
  (show IsIdempotentElem (vecMulVec v (star v)) from rank_one_idem v hv).one_sub

private lemma complement_psd {J : Type*} [Fintype J] [DecidableEq J] (v : J → ℂ)
    (hv : ∑ j, ‖v j‖ ^ 2 = 1) :
    (1 - vecMulVec v (star v)).PosSemidef := by
  simpa [hv] using rank_one_upper v

private lemma supported_bound {I J : Type*} [Fintype I] [Fintype J]
    (d : I → J → ℂ) (Q : Matrix J J ℂ) (hQ : Q.IsHermitian)
    (hQQ : Q * Q = Q) (hd : ∀ i, Q *ᵥ d i = d i) :
    (((∑ i, ∑ j, ‖d i j‖ ^ 2 : ℝ) : ℂ) • Q -
      ∑ i, vecMulVec (d i) (star (d i))).PosSemidef := by
  classical
  have hs : ∀ i, star (d i) ᵥ* Q = star (d i) := by
    intro i
    rw [← hQ.eq, ← star_mulVec, hd i]
  have hr : ∀ i, Q * vecMulVec (d i) (star (d i)) * Q =
      vecMulVec (d i) (star (d i)) := by
    intro i
    rw [mul_vecMulVec, hd i, vecMulVec_mul, hs i]
  have h := (gram_upper d).conjTranspose_mul_mul_same Q
  rw [hQ.eq] at h
  convert h using 1
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    Matrix.mul_sum, Matrix.sum_mul, hr, hQQ]

private lemma residual_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (d : I → J → ℂ) (v : J → ℂ) (hv : ∑ j, ‖v j‖ ^ 2 = 1)
    (hd : ∀ i, star v ⬝ᵥ d i = 0) :
    (((∑ i, ∑ j, ‖d i j‖ ^ 2 : ℝ) : ℂ) • (1 - vecMulVec v (star v)) -
      ∑ i, vecMulVec (d i) (star (d i))).PosSemidef := by
  apply supported_bound d (1 - vecMulVec v (star v))
    (complement_psd v hv).1 (complement_idem v hv)
  intro i
  rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, hd i]
  simp

private lemma gram_upper_of_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (d : I → J → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ x : J → ℂ, (∑ i, ‖star (d i) ⬝ᵥ x‖ ^ 2) ≤
      t * (∑ j, ‖x j‖ ^ 2)) :
    ((t : ℂ) • (1 : Matrix J J ℂ) -
      ∑ i, vecMulVec (d i) (star (d i))).PosSemidef := by
  have hr := Matrix.posSemidef_sum Finset.univ
    (fun i _ => posSemidef_vecMulVec_self_star (d i))
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((PosSemidef.one.smul (Complex.zero_le_real.mpr ht)).1.sub hr.1) ?_
  intro x
  have hi : ∀ i, star x ⬝ᵥ (vecMulVec (d i) (star (d i)) *ᵥ x) =
      ((‖star (d i) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      star_dotProduct x (d i), Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  have heq : star x ⬝ᵥ (((t : ℂ) • (1 : Matrix J J ℂ) -
      ∑ i, vecMulVec (d i) (star (d i))) *ᵥ x) =
      ((t * (∑ j, ‖x j‖ ^ 2) - ∑ i, ‖star (d i) ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, sum_mulVec, dotProduct_sum, smul_eq_mul, hi, dot_star_self]
    simp
  rw [heq]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hb x))

private lemma correction_psd {J : Type*}
    (V Q rho : Matrix J J ℂ) (l : ℝ)
    (hV : V.PosSemidef) (hQ : Q.PosSemidef) (hl : 1 / 2 ≤ l)
    (hK : (((1 - l : ℝ) : ℂ) • Q - rho).PosSemidef) :
    (Q - (2 : ℂ) • rho).PosSemidef ∧
    (V + Q - ((4 * l : ℝ) : ℂ) • rho).PosSemidef := by
  classical
  have h1 : 0 ≤ 2 * l - 1 := by linarith
  have h4 : 0 ≤ 4 * l := by linarith
  have heq1 : Q - (2 : ℂ) • rho = ((2 * l - 1 : ℝ) : ℂ) • Q +
      (2 : ℂ) • (((1 - l : ℝ) : ℂ) • Q - rho) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have heq2 : V + Q - ((4 * l : ℝ) : ℂ) • rho =
      V + (((2 * l - 1) ^ 2 : ℝ) : ℂ) • Q +
        ((4 * l : ℝ) : ℂ) • (((1 - l : ℝ) : ℂ) • Q - rho) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [heq1, heq2]
  exact ⟨(hQ.smul (Complex.zero_le_real.mpr h1)).add
      (hK.smul (show (0 : ℂ) ≤ 2 by norm_num)),
    (hV.add (hQ.smul (Complex.zero_le_real.mpr (sq_nonneg (2 * l - 1))))).add
      (hK.smul (Complex.zero_le_real.mpr h4))⟩

private lemma small_correction_psd {J : Type*} [DecidableEq J]
    (rho : Matrix J J ℂ) (l : ℝ) (hl : l ≤ 1 / 2)
    (hR : ((l : ℂ) • (1 : Matrix J J ℂ) - rho).PosSemidef) :
    (1 - (2 : ℂ) • rho).PosSemidef := by
  classical
  have h1 : 0 ≤ 1 - 2 * l := by linarith
  have heq : (1 : Matrix J J ℂ) - (2 : ℂ) • rho =
      (2 : ℂ) • ((l : ℂ) • (1 : Matrix J J ℂ) - rho) +
        ((1 - 2 * l : ℝ) : ℂ) • (1 : Matrix J J ℂ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [heq]
  exact (hR.smul (show (0 : ℂ) ≤ 2 by norm_num)).add
    (PosSemidef.one.smul (Complex.zero_le_real.mpr h1))

private lemma gram_upper_of_coordinate_bound {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (d : I → J → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ b : J → ℂ, (∑ i, ‖∑ j, d i j * star (b j)‖ ^ 2) ≤
      t * (∑ j, ‖b j‖ ^ 2)) :
    ((t : ℂ) • (1 : Matrix J J ℂ) -
      ∑ i, vecMulVec (d i) (star (d i))).PosSemidef := by
  apply gram_upper_of_bound d t ht
  intro b
  convert hb b using 1
  congr 1
  funext i
  rw [star_dotProduct (d i) b, norm_star]
  simp [dotProduct, mul_comm]


/-- Adding twice any normalized rank-one projector to the identity gives a separable matrix. -/
theorem separableCone_one_add_two_rankOne {m n : ℕ} (ψ : Fin m × Fin n → ℂ)
    (hψ : ∑ ij, ‖ψ ij‖ ^ 2 = 1) :
    separableCone (1 + (2 : ℂ) • vecMulVec ψ (star ψ)) := by
  classical
  obtain ⟨u,v,a,hu,hv,ha,hA,hB,hbound⟩ := exists_product_max_of_normalized ψ hψ
  let rho := reduced ψ
  have hrho : rho = ∑ i, vecMulVec (fun j => ψ (i,j)) (star (fun j => ψ (i,j))) := by
    ext j l
    dsimp [rho, reduced,
      D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
      Matrix.vecMulVec, star]
    rw [Matrix.sum_apply]
    rfl
  by_cases hl : a ^ 2 ≤ 1 / 2
  · have hR : (((a ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - rho).PosSemidef := by
      rw [hrho]
      exact gram_upper_of_coordinate_bound (fun i j => ψ (i,j)) (a ^ 2) (sq_nonneg a)
        (by simpa only [Complex.star_def] using hbound)
    have hc := small_correction_psd rho (a ^ 2) hl hR
    have hsep := separableCone_add
      (separableCone_smul (by norm_num : (0 : ℝ) ≤ 2) (separable_rankOne_add_reduced ψ))
      (separable_kronecker PosSemidef.one hc)
    convert hsep using 1
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, smul_eq_mul, Complex.real_smul]
    have hid : (if (i,j) = (k,l) then (1 : ℂ) else 0) =
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
      by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi,hj]
    rw [hid]
    change _ = 2 * (vecMulVec ψ (star ψ) (i,j) (k,l) +
      (if i = k then 1 else 0) * rho j l) +
      (if i = k then 1 else 0) * ((if j = l then 1 else 0) - 2 * rho j l)
    ring
  · have hl' : 1 / 2 ≤ a ^ 2 := le_of_lt (lt_of_not_ge hl)
    let χ : Fin m × Fin n → ℂ := fun ij => ψ ij - (a : ℂ) * u ij.1 * v ij.2
    obtain ⟨hχv,hχu,hχnorm⟩ := rankOne_residual_properties ψ u v a hψ hu hv hA hB
    let U := vecMulVec u (star u)
    let V := vecMulVec v (star v)
    let P : Matrix (Fin m) (Fin m) ℂ := 1 - U
    let Q : Matrix (Fin n) (Fin n) ℂ := 1 - V
    let ρ := reduced χ
    have hU : U.PosSemidef := posSemidef_vecMulVec_self_star u
    have hV : V.PosSemidef := posSemidef_vecMulVec_self_star v
    have hP : P.PosSemidef := complement_psd u hu
    have hQ : Q.PosSemidef := complement_psd v hv
    have hχrows : ∀ i, star v ⬝ᵥ (fun j => χ (i,j)) = 0 := by
      intro i
      simpa [χ, dotProduct, mul_comm] using hχv i
    have hK : ((((1 - a ^ 2 : ℝ) : ℂ) • Q) - ρ).PosSemidef := by
      have h := residual_bound (fun i j => χ (i,j)) v hv hχrows
      have hn : (∑ i, ∑ j, ‖χ (i,j)‖ ^ 2) = 1 - a ^ 2 := by
        simpa only [Fintype.sum_prod_type] using hχnorm
      have hsum : (∑ i, vecMulVec (fun j => χ (i,j)) (star (fun j => χ (i,j)))) =
          reduced χ := by
        ext j l
        dsimp [reduced,
          D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft,
          Matrix.vecMulVec, star]
        rw [Matrix.sum_apply]
        rfl
      change ((((1 - a ^ 2 : ℝ) : ℂ) •
        (1 - vecMulVec v (star v)) - reduced χ).PosSemidef)
      rw [← hsum, ← hn]
      exact h
    obtain ⟨hcQ,hcU⟩ := correction_psd V Q ρ (a ^ 2) hV hQ hl' hK
    have hPsupport : ∀ j, P *ᵥ (fun i => χ (i,j)) = fun i => χ (i,j) := by
      intro j
      have hd : star u ⬝ᵥ (fun i => χ (i,j)) = 0 := by
        simpa [χ, dotProduct, mul_comm] using hχu j
      change (1 - vecMulVec u (star u)) *ᵥ (fun i => χ (i,j)) = _
      rw [sub_mulVec, one_mulVec, vecMulVec_mulVec, hd]
      simp
    have hs := separable_projected_rankOne χ u v a P hP.1 (complement_idem u hu) hPsupport
    have hψeq : (fun ij : Fin m × Fin n => (a : ℂ) * u ij.1 * v ij.2 + χ ij) = ψ := by
      ext ij; dsimp [χ]; ring
    rw [hψeq] at hs
    have hsep := separableCone_add (separableCone_add
      (separableCone_smul (by norm_num : (0 : ℝ) ≤ 2) hs)
      (separable_kronecker hU hcU)) (separable_kronecker hP hcQ)
    convert hsep using 1
    ext ⟨i,j⟩ ⟨k,l⟩
    have hid : (if (i,j) = (k,l) then (1 : ℂ) else 0) =
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
      by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi,hj]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul, Complex.real_smul]
    change (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (i,j) (k,l) +
      2 * vecMulVec ψ (star ψ) (i,j) (k,l) =
      2 * (vecMulVec ψ (star ψ) (i,j) (k,l) +
        (P i k + ((2 * a ^ 2 : ℝ) : ℂ) * U i k) * ρ j l +
        (1 / 2 : ℂ) * (P i k * V j l)) +
      U i k * (V j l + Q j l - ((4 * a ^ 2 : ℝ) : ℂ) * ρ j l) +
      P i k * (Q j l - 2 * ρ j l)
    simp only [P, Q, Matrix.sub_apply, Matrix.one_apply, hid]
    push_cast
    ring

#print axioms separableCone_one_add_two_rankOne

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
