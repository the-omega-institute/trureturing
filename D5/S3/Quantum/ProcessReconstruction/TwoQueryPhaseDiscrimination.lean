/- GID: D5/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/TwoQueryPhaseDiscrimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove the attainable two-query phase discrimination bound. -/

import D5.S3.Quantum.ProcessReconstruction.PureDistance
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-! The two-slot phase simulation acts on matrices of the physical sensing
qubit and any finite memory, with an arbitrary isometric intermediate control. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped InnerProductSpace ComplexOrder Matrix MatrixOrder BigOperators
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)

namespace D5.S3.Quantum.ProcessReconstruction.TwoQueryPhaseDiscrimination

private def mix {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (p : ℝ) (plus minus : V →ₗ[ℝ] W) (state : V) : W :=
  p • plus state + (1 - p) • minus state

/-- Complementary binary channel mixtures have the same mixed-label terms
after two queries, even with a common linear control between the queries. -/
private theorem two_queries_sub {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (p : ℝ) (firstPlus firstMinus : V →ₗ[ℝ] V)
    (secondPlus secondMinus : W →ₗ[ℝ] W) (control : V →ₗ[ℝ] W) (state : V) :
    mix p secondPlus secondMinus (control (mix p firstPlus firstMinus state)) -
        mix (1 - p) secondPlus secondMinus (control (mix (1 - p) firstPlus firstMinus state)) =
      (2 * p - 1) • (secondPlus (control (firstPlus state)) -
        secondMinus (control (firstMinus state))) := by
  simp only [mix, map_add, map_smul, smul_add, smul_smul]
  module

/-- An intermediate unit vector with equal real overlap bounds the
angle between the two extremal paths of the experiment. -/
private theorem two_query_overlap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v w z : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    {x : ℝ} (hx : 0 ≤ x) (hvw : (⟪w, v⟫_ℂ).re = x) (hwz : (⟪w, z⟫_ℂ).re = x) :
    max 0 (2 * x ^ 2 - 1) ≤ ‖⟪z, v⟫_ℂ‖ := by
  have hsum : (⟪w, v + z⟫_ℂ).re = 2 * x := by
    rw [inner_add_right, Complex.add_re, hvw, hwz]
    ring
  have hnorm : 2 * x ≤ ‖v + z‖ := by
    calc
      2 * x = (⟪w, v + z⟫_ℂ).re := hsum.symm
      _ ≤ ‖⟪w, v + z⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖v + z‖ := by simpa only [hw, one_mul] using norm_inner_le_norm (𝕜 := ℂ) w (v + z)
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * x) (norm_nonneg (v + z))).2 hnorm
  have hadd := norm_add_sq (𝕜 := ℂ) v z
  change ‖v + z‖ ^ 2 = ‖v‖ ^ 2 + 2 * (⟪v, z⟫_ℂ).re + ‖z‖ ^ 2 at hadd
  rw [hv, hz] at hadd
  have hre : 2 * x ^ 2 - 1 ≤ (⟪v, z⟫_ℂ).re := by nlinarith only [hadd, hsq]
  have hcore : (⟪v, z⟫_ℂ).re ≤ ‖⟪z, v⟫_ℂ‖ := by
    rw [← norm_inner_symm (𝕜 := ℂ) v z]
    exact Complex.re_le_norm _
  exact max_le (norm_nonneg _) (hre.trans hcore)

/-- Trace-distance bound for the two pure paths of a two-query unitary
comparison with a common intermediate control. -/
private theorem pure_paths_traceNorm_le {n : Type*} [Fintype n]
    (v w z : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    {x : ℝ} (hx : 0 ≤ x) (hvw : (⟪w, v⟫_ℂ).re = x) (hwz : (⟪w, z⟫_ℂ).re = x) :
    traceNorm (vecMulVec (⇑v) (star (⇑v)) - vecMulVec (⇑z) (star (⇑z))) ≤
      2 * Real.sqrt (1 - (max 0 (2 * x ^ 2 - 1)) ^ 2) := by
  classical
  have h := two_query_overlap v w z hv hw hz hx hvw hwz
  have hsq := (sq_le_sq₀ (le_max_left _ _) (norm_nonneg _)).2 h
  exact (UnitaryReconstruction.traceNorm_pure_sub_le v z hv hz).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_left hsq 1)) (by norm_num))

section PureStates

open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation (qubit qubit_norm)

variable {n : Type*} [Fintype n]

private def columns (z w : EuclideanSpace ℂ n) : Matrix n (Fin 2) ℂ :=
  Matrix.of fun i j => if j = 0 then z i else w i

private lemma columns_isometry (z w : EuclideanSpace ℂ n)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hzw : ⟪z, w⟫_ℂ = 0) :
    (columns z w)ᴴ * columns z w = 1 := by
  have hwz : ⟪w, z⟫_ℂ = 0 := by rw [← inner_conj_symm, hzw, map_zero]
  have hzz : ⟪z, z⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hz]
  have hww : ⟪w, w⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hw]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm] using
      (show (∑ i, z i * star (z i)) = 1 from by
        rw [← show ⟪z, z⟫_ℂ = ∑ i, z i * star (z i) from rfl, hzz])
  · simpa [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hzw
  · simpa [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm] using hwz
  · simpa [columns, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm] using
      (show (∑ i, w i * star (w i)) = 1 from by
        rw [← show ⟪w, w⟫_ℂ = ∑ i, w i * star (w i) from rfl, hww])

private def pureOuter (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

omit [Fintype n] in
private lemma transport_pureOuter {m : Type*} [Fintype m] (W : Matrix n m ℂ) (u : m → ℂ) :
    W * pureOuter u * Wᴴ = pureOuter (W *ᵥ u) := by
  unfold pureOuter
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- The exact trace norm of the difference of two normalized rank-one states. -/
private theorem traceNorm_pure_sub (v z : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    traceNorm (pureOuter (⇑v) - pureOuter (⇑z)) = 2 * Real.sqrt (1 - ‖⟪z, v⟫_ℂ‖ ^ 2) := by
  classical
  let c := ⟪z, v⟫_ℂ
  let r := Real.sqrt (1 - ‖c‖ ^ 2)
  have hc : ‖c‖ ≤ 1 := by
    simpa only [c, hv, hz, one_mul] using (norm_inner_le_norm (𝕜 := ℂ) z v)
  have hcsq := (sq_le_sq₀ (norm_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)).2 hc
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 1 - ‖c‖ ^ 2 := Real.sq_sqrt (by linarith)
  by_cases hr0 : r = 0
  · change traceNorm (pureOuter (⇑v) - pureOuter (⇑z)) = 2 * r
    rw [hr0, mul_zero]
    apply le_antisymm _ (traceNorm_nonneg _)
    have h := UnitaryReconstruction.traceNorm_pure_sub_le v z hv hz
    change traceNorm (pureOuter (⇑v) - pureOuter (⇑z)) ≤ 2 * r at h
    simpa only [hr0, mul_zero] using h
  let w := ((r⁻¹ : ℝ) : ℂ) • (v - c • z)
  have hnorm : ‖v - c • z‖ = r := by
    apply (sq_eq_sq₀ (norm_nonneg _) hr).1
    rw [hrsq, UnitaryReconstruction.orthogonal_residual_norm v z hz, hv]
    norm_num [c]
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hr), hnorm, inv_mul_cancel₀ hr0]
  have hzz : ⟪z, z⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hz]
  have hzw : ⟪z, w⟫_ℂ = 0 := by
    simp only [w, inner_smul_right, inner_sub_right, hzz, mul_one, c, sub_self, mul_zero]
  let W := columns z w
  have hW : Wᴴ * W = 1 := columns_isometry z w hz hw hzw
  let u : Fin 2 → ℂ := ![c, (r : ℂ)]
  let e : Fin 2 → ℂ := ![1, 0]
  have hvr : (r : ℂ) • w = v - c • z := by
    dsimp only [w]
    rw [smul_smul, show (r : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 from by
      exact_mod_cast mul_inv_cancel₀ hr0, one_smul]
  have hWu : W *ᵥ u = ⇑v := by
    ext i
    have he := congrArg (fun x : EuclideanSpace ℂ n => x i) hvr
    change (r : ℂ) * w i = v i - c * z i at he
    simp [W, columns, u, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination he
  have hWe : W *ᵥ e = ⇑z := by
    ext i
    simp [W, columns, e, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcoord : pureOuter u - pureOuter e = qubit (-(r ^ 2)) (c * (r : ℂ)) := by
    have hc' : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
    ext i j
    change u i * star (u j) - e i * star (e j) = qubit (-(r ^ 2)) (c * (r : ℂ)) i j
    fin_cases i <;> fin_cases j <;>
      simp [qubit, u, e, Complex.mul_conj, ← hc', hrsq, mul_comm]
    have hreal : r * r = 1 - Complex.normSq c := by rw [← pow_two, hrsq, hc']
    exact_mod_cast hreal
  calc
    traceNorm (pureOuter (⇑v) - pureOuter (⇑z)) = traceNorm (W * (pureOuter u - pureOuter e) * Wᴴ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, transport_pureOuter, transport_pureOuter, hWu, hWe]
    _ = traceNorm (pureOuter u - pureOuter e) := traceNorm_isometry W hW _
    _ = 2 * r := by
      rw [hcoord, qubit_norm, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
      have hrad : (-(r ^ 2)) ^ 2 + ‖c‖ ^ 2 * r ^ 2 = r ^ 2 := by
        calc
          _ = r ^ 2 * (r ^ 2 + ‖c‖ ^ 2) := by ring
          _ = r ^ 2 := by rw [hrsq]; ring
      rw [← pow_two r, hrad, Real.sqrt_sq hr]

end PureStates

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private def outer (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

private def sandwich (V : Matrix m n ℂ) : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [smul_mul]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
private lemma sandwich_outer (V : Matrix m n ℂ) (v : n → ℂ) :
    sandwich V (outer v) = outer (V *ᵥ v) := by
  change V * vecMulVec v (star v) * Vᴴ = vecMulVec (V *ᵥ v) (star (V *ᵥ v))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

private def phase (bit : n → Bool) (a : ℂ) : Matrix n n ℂ :=
  diagonal (fun i => if bit i then star a else a)

omit [Fintype n] [DecidableEq n] in
private lemma norm_square_phase (a : ℂ) (ha : Complex.normSq a = 1)
    (bit : n → Bool) (i : n) :
    star (if bit i then star a else a) * (if bit i then star a else a) = 1 := by
  have hunit : a * star a = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ha, Complex.ofReal_one]
  cases h : bit i
  · simpa only [h, Bool.false_eq_true, ite_false] using (mul_comm (star a) a).trans hunit
  · simpa only [h, ite_true, star_star] using hunit

private lemma phase_isometry (bit : n → Bool) (a : ℂ) (ha : Complex.normSq a = 1) :
    (phase bit a)ᴴ * phase bit a = 1 := by
  simp only [phase, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact norm_square_phase a ha bit i

private def lift (v : n → ℂ) : EuclideanSpace ℂ n := WithLp.toLp 2 v

omit [DecidableEq n] [DecidableEq m] in
private lemma inner_apply (V : Matrix m n ℂ) (u v : n → ℂ) :
    ⟪lift (V *ᵥ u), lift (V *ᵥ v)⟫_ℂ = ⟪lift u, lift ((Vᴴ * V) *ᵥ v)⟫_ℂ := by
  simp only [lift, EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm (V *ᵥ v), Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec]
  exact dotProduct_comm _ _

omit [DecidableEq m] in
private lemma isometry_inner (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (u v : n → ℂ) :
    ⟪lift (V *ᵥ u), lift (V *ᵥ v)⟫_ℂ = ⟪lift u, lift v⟫_ℂ := by
  rw [inner_apply, hV, one_mulVec]

omit [DecidableEq m] in
private lemma isometry_norm (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (v : n → ℂ) :
    ‖lift (V *ᵥ v)‖ = ‖lift v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), isometry_inner V hV]

private lemma phase_cross (bit : n → Bool) (a : ℂ) (v : n → ℂ) :
    (⟪lift (phase bit (star a) *ᵥ v), lift (phase bit a *ᵥ v)⟫_ℂ).re =
      (a ^ 2).re * ‖lift v‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [lift, EuclideanSpace.inner_toLp_toLp, dotProduct, RCLike.re_eq_complex_re]
  simp_rw [phase, Matrix.mulVec_diagonal]
  simp only [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : bit i <;>
    simp [h, Matrix.mulVec_diagonal, Complex.star_def, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- Apply the two independent convex queries and the common isometric
control to a pure input. The real upper and lower phase amplitudes use
the same complex number of modulus one and complementary mixtures. -/
def experiment (firstBit : n → Bool) (secondBit : m → Bool)
    (a : ℂ) (p : ℝ) (V : Matrix m n ℂ) (v : n → ℂ) : Matrix m m ℂ :=
  let firstPlus := sandwich (phase firstBit a)
  let firstMinus := sandwich (phase firstBit (star a))
  let secondPlus := sandwich (phase secondBit a)
  let secondMinus := sandwich (phase secondBit (star a))
  let out := sandwich V (p • firstPlus (outer v) + (1 - p) • firstMinus (outer v))
  p • secondPlus out + (1 - p) • secondMinus out

/-- The identical two-dwell upper bound permits arbitrary finite quantum memory
and arbitrary intermediate isometries, including coherent control of feedback. -/
theorem experiment_traceNorm_le (firstBit : n → Bool) (secondBit : m → Bool)
    (a : ℂ) (ha : Complex.normSq a = 1) (hx : 0 ≤ (a ^ 2).re)
    (p : ℝ) (hp : 1 / 2 ≤ p)
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (v : n → ℂ) (hv : ‖lift v‖ = 1) :
    traceNorm (experiment firstBit secondBit a p V v -
      experiment firstBit secondBit a (1 - p) V v) ≤
        (2 * p - 1) * (2 * Real.sqrt (1 - (max 0 (2 * (a ^ 2).re ^ 2 - 1)) ^ 2)) := by
  have hg : 0 ≤ 2 * p - 1 := by linarith
  have ha' : Complex.normSq (star a) = 1 := by simpa [Complex.star_def] using ha
  rw [show experiment firstBit secondBit a p V v -
      experiment firstBit secondBit a (1 - p) V v =
      (2 * p - 1) •
        (sandwich (phase secondBit a) (sandwich V (sandwich (phase firstBit a) (outer v))) -
          sandwich (phase secondBit (star a))
            (sandwich V (sandwich (phase firstBit (star a)) (outer v)))) from
    two_queries_sub p (sandwich (phase firstBit a)) (sandwich (phase firstBit (star a)))
      (sandwich (phase secondBit a)) (sandwich (phase secondBit (star a))) (sandwich V) (outer v)]
  change traceNorm (((2 * p - 1 : ℝ) : ℂ) • _) ≤ _
  rw [traceNorm_smul_nonneg _ _ hg]
  apply mul_le_mul_of_nonneg_left _ hg
  simp only [sandwich_outer]
  let u := V *ᵥ (phase firstBit a *ᵥ v)
  let u' := V *ᵥ (phase firstBit (star a) *ᵥ v)
  have hu : ‖lift u‖ = 1 := by
    rw [show u = _ from rfl, isometry_norm _ hV, isometry_norm _ (phase_isometry _ _ ha), hv]
  have hu' : ‖lift u'‖ = 1 := by
    rw [show u' = _ from rfl, isometry_norm _ hV, isometry_norm _ (phase_isometry _ _ ha'), hv]
  let left := lift (phase secondBit a *ᵥ u)
  let mid := lift (phase secondBit (star a) *ᵥ u)
  let right := lift (phase secondBit (star a) *ᵥ u')
  have hl : ‖left‖ = 1 := (isometry_norm _ (phase_isometry _ _ ha) _).trans hu
  have hm : ‖mid‖ = 1 := (isometry_norm _ (phase_isometry _ _ ha') _).trans hu
  have hr : ‖right‖ = 1 := (isometry_norm _ (phase_isometry _ _ ha') _).trans hu'
  have hlm : (⟪mid, left⟫_ℂ).re = (a ^ 2).re := by
    dsimp only [mid, left]
    rw [phase_cross, hu]
    ring
  have hmr : (⟪mid, right⟫_ℂ).re = (a ^ 2).re := by
    dsimp only [mid, right, u, u']
    rw [isometry_inner _ (phase_isometry _ _ ha'), isometry_inner _ hV]
    rw [show (⟪lift (phase firstBit a *ᵥ v), lift (phase firstBit (star a) *ᵥ v)⟫_ℂ).re =
      (⟪lift (phase firstBit (star a) *ᵥ v), lift (phase firstBit a *ᵥ v)⟫_ℂ).re from
        inner_re_symm (𝕜 := ℂ) _ _, phase_cross, hv]
    ring
  exact pure_paths_traceNorm_le left mid right hl hm hr hx hlm hmr

private abbrev Basis := Bool × Bool

private def probe (u : ℝ) (i : Basis) : ℂ :=
  (Real.sqrt (if i.1 = i.2 then u / 2 else (1 - u) / 2) : ℂ)

private lemma probe_norm_two (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖lift (probe u)‖ = 1 := by
  have he : 0 ≤ u / 2 := by positivity
  have hn : 0 ≤ (1 - u) / 2 := by linarith
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).1
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [lift, EuclideanSpace.inner_toLp_toLp, dotProduct, RCLike.re_eq_complex_re,
    Fintype.sum_prod_type, Fintype.sum_bool, probe, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [← pow_two, Real.sq_sqrt he, ← pow_two, Real.sq_sqrt hn]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

private lemma extremal_phase_overlap (a : ℂ) (ha : Complex.normSq a = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    let v := probe u
    ⟪lift (phase Prod.snd (star a) *ᵥ (phase Prod.fst (star a) *ᵥ v)),
      lift (phase Prod.snd a *ᵥ (phase Prod.fst a *ᵥ v))⟫_ℂ =
        ((1 - 2 * u * (1 - (a ^ 2).re ^ 2) : ℝ) : ℂ) := by
  dsimp only
  have he : 0 ≤ u / 2 := by positivity
  have hn : 0 ≤ (1 - u) / 2 := by linarith
  have ha2 : Complex.normSq (a ^ 2) = 1 := by simp [pow_two, Complex.normSq_mul, ha]
  have ha4 : (a ^ 4).re = 2 * (a ^ 2).re ^ 2 - 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (a ^ 2), Complex.mul_re]
    have hnorm := Complex.normSq_apply (a ^ 2)
    nlinarith only [hnorm, ha2]
  have hunit : a * star a = 1 := by
    rw [Complex.star_def, Complex.mul_conj, ha, Complex.ofReal_one]
  simp only [lift, EuclideanSpace.inner_toLp_toLp, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_bool, phase, Matrix.mulVec_diagonal, probe, Prod.fst, Prod.snd,
    Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, Pi.star_apply, star_mul,
    star_star, Complex.star_def, Complex.conj_ofReal]
  let re := Real.sqrt (u / 2)
  let rn := Real.sqrt ((1 - u) / 2)
  have hre : (re : ℂ) * (re : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    norm_cast
    rw [← pow_two, Real.sq_sqrt he]
  have hrn : (rn : ℂ) * (rn : ℂ) = (((1 - u) / 2 : ℝ) : ℂ) := by
    norm_cast
    rw [← pow_two, Real.sq_sqrt hn]
  have hs : (a ^ 4) + star (a ^ 4) = ((2 * (a ^ 4).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im, add_neg_cancel]
  calc
    _ = (a ^ 4 + star (a ^ 4)) * ((re : ℂ) * re) +
        2 * (a * star a) ^ 2 * ((rn : ℂ) * rn) := by
      dsimp only [re, rn]
      simp only [starRingEnd_apply, star_star, star_pow]
      ring
    _ = _ := by rw [hs, hunit, hre, hrn, ha4]; push_cast; ring

private lemma attaining_weight (x : ℝ) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1, 1 - 2 * u * (1 - x ^ 2) = max 0 (2 * x ^ 2 - 1) := by
  by_cases h : 2 * x ^ 2 - 1 ≤ 0
  · have hd : 1 ≤ 2 * (1 - x ^ 2) := by linarith
    have hd0 : 0 < 2 * (1 - x ^ 2) := by linarith
    refine ⟨(2 * (1 - x ^ 2))⁻¹, ⟨inv_nonneg.mpr hd0.le, inv_le_one_of_one_le₀ hd⟩, ?_⟩
    rw [max_eq_left h, show 2 * (2 * (1 - x ^ 2))⁻¹ * (1 - x ^ 2) =
      (2 * (1 - x ^ 2))⁻¹ * (2 * (1 - x ^ 2)) from by ring, inv_mul_cancel₀ hd0.ne']
    ring
  · exact ⟨1, ⟨by norm_num, le_rfl⟩, by rw [max_eq_right (le_of_not_ge h)]; ring⟩


/-- For two identical independent dwells, a parallel pure two-qubit probe
attains the upper bound for any finite isometric-control strategy. -/
theorem parallel_attains (a : ℂ) (ha : Complex.normSq a = 1)
    (p : ℝ) (hp : 1 / 2 ≤ p) :
    ∃ v : Basis → ℂ, ‖lift v‖ = 1 ∧
      traceNorm (experiment Prod.fst Prod.snd a p (1 : Matrix Basis Basis ℂ) v -
        experiment Prod.fst Prod.snd a (1 - p) (1 : Matrix Basis Basis ℂ) v) =
      (2 * p - 1) * (2 * Real.sqrt (1 - (max 0 (2 * (a ^ 2).re ^ 2 - 1)) ^ 2)) := by
  obtain ⟨u, hu, hweight⟩ := attaining_weight (a ^ 2).re
  let v := probe u
  refine ⟨v, probe_norm_two u hu.1 hu.2, ?_⟩
  have hg : 0 ≤ 2 * p - 1 := by linarith
  rw [show experiment Prod.fst Prod.snd a p (1 : Matrix Basis Basis ℂ) v -
      experiment Prod.fst Prod.snd a (1 - p) (1 : Matrix Basis Basis ℂ) v =
      (2 * p - 1) •
        (sandwich (phase Prod.snd a) (sandwich (1 : Matrix Basis Basis ℂ) (sandwich (phase Prod.fst a) (outer v))) -
          sandwich (phase Prod.snd (star a))
            (sandwich (1 : Matrix Basis Basis ℂ) (sandwich (phase Prod.fst (star a)) (outer v)))) from
    two_queries_sub p (sandwich (phase Prod.fst a)) (sandwich (phase Prod.fst (star a)))
      (sandwich (phase Prod.snd a)) (sandwich (phase Prod.snd (star a))) (sandwich (1 : Matrix Basis Basis ℂ)) (outer v)]
  change traceNorm (((2 * p - 1 : ℝ) : ℂ) • _) = _
  rw [traceNorm_smul_nonneg _ _ hg]
  simp only [sandwich_outer, Matrix.one_mulVec]
  congr 1
  let vPlus := lift (phase Prod.snd a *ᵥ (phase Prod.fst a *ᵥ v))
  let vMinus := lift (phase Prod.snd (star a) *ᵥ (phase Prod.fst (star a) *ᵥ v))
  have hv := probe_norm_two u hu.1 hu.2
  have hvPlus : ‖vPlus‖ = 1 := by
    dsimp only [vPlus]
    rw [isometry_norm _ (phase_isometry _ _ ha), isometry_norm _ (phase_isometry _ _ ha), hv]
  have ha' : Complex.normSq (star a) = 1 := by simpa [Complex.star_def] using ha
  have hvMinus : ‖vMinus‖ = 1 := by
    dsimp only [vMinus]
    rw [isometry_norm _ (phase_isometry _ _ ha'), isometry_norm _ (phase_isometry _ _ ha'), hv]
  have he : ⟪vMinus, vPlus⟫_ℂ = ((max 0 (2 * (a ^ 2).re ^ 2 - 1) : ℝ) : ℂ) := by
    exact (extremal_phase_overlap a ha u hu.1 hu.2).trans
      (congrArg Complex.ofReal hweight)
  have hnorm := traceNorm_pure_sub vPlus vMinus hvPlus hvMinus
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)] at hnorm
  exact hnorm

end D5.S3.Quantum.ProcessReconstruction.TwoQueryPhaseDiscrimination
