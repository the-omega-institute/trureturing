/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Raw prefix density recovery through a shared coherent chart and injective transfer. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
import D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection

/-! A conditional all-competitor bridge toward Critch--Morton Conjecture 9.
The observation is a Hermitian partial trace on the unnormalized state cone.
The transfer inverse is algebraic; no positive or physical inverse is asserted. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery

open scoped BigOperators Matrix
open Matrix
open OpenBoundaryMPSMarginalBirationality
open PeriodicMPSParentIntersection (Bond Word wordMatrix)

noncomputable section

/-- Amplitude columns obtained by separating a prefix from its actual complement. -/
def amplitudeColumns (k m : ℕ) (ψ : Word (k + m) → ℂ) :
    Matrix (Word k) (Word m) ℂ := fun u b => ψ (Fin.append u b)

/-- Raw prefix partial trace: sum of amplitudes times conjugate amplitudes. -/
def rawPrefix (k m : ℕ) (ψ : Word (k + m) → ℂ) :
    Matrix (Word k) (Word k) ℂ :=
  amplitudeColumns k m ψ * (amplitudeColumns k m ψ)ᴴ

/-- Prefix rows acting on the two-dimensional virtual boundary. -/
def prefixMap (A : Fin 2 → Bond) (l : Fin 2 → ℂ) (k : ℕ) :
    Matrix (Word k) (Fin 2) ℂ := fun w => l ᵥ* wordMatrix A w

/-- Complement columns retain the actual free right boundary. -/
def tailMap (A : Fin 2 → Bond) (r : Fin 2 → ℂ) (m : ℕ) :
    Matrix (Fin 2) (Word m) ℂ := fun i w => (wordMatrix A w *ᵥ r) i

/-- The linear completely positive transfer, without a trace-preservation premise. -/
def transfer (A : Fin 2 → Bond) (X : Bond) : Bond :=
  ∑ i : Fin 2, A i * X * (A i)ᴴ

/-- The canonical core supplied by the coherent three-site reconstruction. -/
def canonicalCore (t : Word 3 → ℂ) : Fin 2 → Bond := reconstructedMatrix t

private lemma state_formula (n : ℕ) (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (w : Word n) :
    mpsState n (A 0) (A 1) l r w = dotProduct l (wordMatrix A w *ᵥ r) := by
  have hA : (![A 0, A 1] : Fin 2 → Bond) = A := FinVec.etaExpand_eq A
  simp only [mpsState, wordMatrix, hA]

private lemma columns_factor (k m : ℕ) (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) :
    amplitudeColumns k m (mpsState (k + m) (A 0) (A 1) l r) =
      prefixMap A l k * tailMap A r m := by
  ext u b
  rw [amplitudeColumns, state_formula]
  have hw : wordMatrix A (Fin.append u b) = wordMatrix A u * wordMatrix A b := by
    simp [wordMatrix, List.ofFn_comp', List.ofFn_fin_append, List.prod_append]
  rw [hw, ← mulVec_mulVec, dotProduct_mulVec]
  rfl

private lemma observed_coherent (m : ℕ) (A : Fin 2 → Bond) (l r : Fin 2 → ℂ)
    (v : Word 3 → ℂ) :
    ∃ q : Fin 2 → ℂ,
      rawPrefix 3 m (mpsState (3 + m) (A 0) (A 1) l r) *ᵥ v =
        mpsState 3 (A 0) (A 1) l q := by
  let C := amplitudeColumns 3 m (mpsState (3 + m) (A 0) (A 1) l r)
  refine ⟨tailMap A r m *ᵥ (Cᴴ *ᵥ v), ?_⟩
  change (C * Cᴴ) *ᵥ v = _
  rw [← mulVec_mulVec, show C = prefixMap A l 3 * tailMap A r m from
    columns_factor 3 m A l r, ← mulVec_mulVec]
  funext w
  rw [state_formula, dotProduct_mulVec]
  rfl

private lemma gauge_lift (t : Word 3 → ℂ) (A : Fin 2 → Bond)
    (l g : Fin 2 → ℂ) (ht : mpsState 3 (A 0) (A 1) l g = t)
    (hg : MvPolynomial.eval t chartPoly ≠ 0) (n : ℕ) (r : Fin 2 → ℂ) :
    ∃ q : Fin 2 → ℂ, mpsState n (A 0) (A 1) l r =
      mpsState n (canonicalCore t 0) (canonicalCore t 1) (reconstructedLeft t) q := by
  obtain ⟨s, hs, u, hu, hl, hm, _⟩ := triple_gauge (A 0) (A 1) l g
    (by simpa only [ht] using hg)
  rw [ht] at hl hm
  let φ : Bond →* Bond :=
    { toFun := fun x => u * x * u⁻¹
      map_one' := by simp only [mul_one, mul_nonsing_inv _ hu]
      map_mul' := by intro x y; simp only [mul_assoc,
        nonsing_inv_mul_cancel_left _ _ hu] }
  refine ⟨(s * s⁻¹ ^ n) • (u *ᵥ r), ?_⟩
  have hword (w : Word n) : wordMatrix (canonicalCore t) w =
      s ^ n • (u * wordMatrix A w * u⁻¹) := by
    have hA : (![A 0, A 1] : Fin 2 → Bond) = A := FinVec.etaExpand_eq A
    simp only [hA] at hm
    rw [wordMatrix, show (fun i => canonicalCore t (w i)) =
      (fun i => s • φ (A (w i))) from funext (fun i => hm (w i))]
    rw [show (List.ofFn fun i => s • φ (A (w i))) =
      (List.ofFn fun i => φ (A (w i))).map (s • ·) from List.map_ofFn.symm,
      ← List.smul_prod, List.length_ofFn]
    congr 1
    exact (show φ (wordMatrix A w) = _ from by
      rw [wordMatrix, map_list_prod, List.map_ofFn]; rfl).symm
  funext w
  rw [state_formula, state_formula, hword, hl]
  simp only [smul_mulVec, mulVec_smul, smul_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_mulVec, smul_vecMul,
    vecMul_vecMul, mul_assoc, nonsing_inv_mul_cancel_left _ _ hu,
    nonsing_inv_mul _ hu]
  simp only [Matrix.mul_one]
  rw [inv_pow]
  field_simp

private lemma chart_prefix_injective (A : Fin 2 → Bond) (l g : Fin 2 → ℂ)
    (hg : MvPolynomial.eval (mpsState 3 (A 0) (A 1) l g) chartPoly ≠ 0) :
    Function.Injective (prefixMap A l 3).mulVec := by
  let U : Bond := Matrix.of fun i j => (l ᵥ* A i) j
  let V : Bond := Matrix.of fun i j => (A j *ᵥ g) i
  let t := mpsState 3 (A 0) (A 1) l g
  have ht (j : Fin 2) : Matrix.of (fun i k => t ![i, j, k]) = U * A j * V := by
    ext i k
    simp [t, state_formula, wordMatrix, List.ofFn_succ, Matrix.mul_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, U, V, Matrix.of_apply]
    ring
  simp only [chartPoly, map_mul, mul_ne_zero_iff] at hg
  have hd := hg.1.2
  simp only [map_sub, map_mul] at hd
  change MvPolynomial.eval t (MvPolynomial.X ![0, 0, 0]) *
      MvPolynomial.eval t (MvPolynomial.X ![1, 0, 1]) -
      MvPolynomial.eval t (MvPolynomial.X ![0, 0, 1]) *
      MvPolynomial.eval t (MvPolynomial.X ![1, 0, 0]) ≠ 0 at hd
  simp only [MvPolynomial.eval_X] at hd
  have hdet : (U * A 0 * V).det ≠ 0 := by
    rw [← ht 0, det_fin_two]
    exact hd
  simp only [det_mul, mul_ne_zero_iff] at hdet
  have hD : (U * A 0 ^ 2).det ≠ 0 := by
    simpa only [det_mul, det_pow] using
      (mul_ne_zero hdet.1.1 (pow_ne_zero 2 hdet.1.2))
  intro x y hxy
  apply mulVec_injective_of_det_ne_zero hD
  funext i
  have hw (z : Fin 2 → ℂ) :
      (prefixMap A l 3 *ᵥ z) ![i, 0, 0] = ((U * A 0 ^ 2) *ᵥ z) i := by
    change dotProduct (l ᵥ* wordMatrix A ![i, 0, 0]) z = _
    simp [wordMatrix, List.ofFn_succ, Matrix.mulVec, Matrix.vecMul, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_two, pow_two, U, Matrix.of_apply]
    ring
  simpa only [hw] using congrFun hxy ![i, 0, 0]

private lemma tail_gram (A : Fin 2 → Bond) (r : Fin 2 → ℂ) (m : ℕ) :
    tailMap A r m * (tailMap A r m)ᴴ =
      (transfer A)^[m] (vecMulVec r (star r)) := by
  have hs (k : ℕ) : tailMap A r k * (tailMap A r k)ᴴ =
      ∑ w : Word k, vecMulVec (wordMatrix A w *ᵥ r) (star (wordMatrix A w *ᵥ r)) := by
    ext i j
    simp only [mul_apply, conjTranspose_apply, tailMap, Matrix.sum_apply,
      vecMulVec_apply, Pi.star_apply]
  rw [hs]
  induction m with
  | zero =>
    simp [wordMatrix, Function.iterate_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, wordMatrix, List.ofFn_succ, List.prod_cons,
      Fin.cons_zero, Fin.cons_succ]
    simp only [transfer, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro w _
    rw [← mulVec_mulVec]
    simp only [mul_vecMulVec, vecMulVec_mul, star_mulVec]

private lemma density_factor (k m : ℕ) (A : Fin 2 → Bond) (l r : Fin 2 → ℂ) :
    rawPrefix k m (mpsState (k + m) (A 0) (A 1) l r) =
      prefixMap A l k * (transfer A)^[m] (vecMulVec r (star r)) *
        (prefixMap A l k)ᴴ := by
  rw [rawPrefix, columns_factor, conjTranspose_mul]
  simp only [← tail_gram, Matrix.mul_assoc]

private lemma sandwich_injective {ι : Type} [Fintype ι]
    (F : Matrix ι (Fin 2) ℂ) (hF : Function.Injective F.mulVec) :
    Function.Injective (fun X : Bond => F * X * Fᴴ) := by
  have hleft {κ : Type} (X Y : Matrix (Fin 2) κ ℂ) (h : F * X = F * Y) : X = Y := by
    ext i j
    exact congrFun (hF (show F *ᵥ X.col j = F *ᵥ Y.col j from congrArg (fun M => M.col j) h)) i
  intro X Y h
  have he : X * Fᴴ = Y * Fᴴ := hleft _ _ (by simpa only [Matrix.mul_assoc] using h)
  have hc : F * Xᴴ = F * Yᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using congrArg conjTranspose he
  exact conjTranspose_injective (hleft _ _ hc)

private lemma boundary_phase (x y : Fin 2 → ℂ)
    (h : vecMulVec x (star x) = vecMulVec y (star y)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ y = z • x := by
  classical
  by_cases hx : x = 0
  · have hy : y = 0 := by
      funext i
      have hd := congrFun (congrFun h i) i
      simp only [hx, vecMulVec_apply, Pi.star_apply, Pi.zero_apply, zero_mul] at hd
      rcases mul_eq_zero.mp hd.symm with hi | hi
      · exact hi
      · exact star_eq_zero.mp hi
    exact ⟨1, norm_one, by simp [hx, hy]⟩
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    have hd : x i * star (x i) = y i * star (y i) := congrFun (congrFun h i) i
    have hy : y i ≠ 0 := by
      intro hy
      rw [hy, zero_mul] at hd
      exact (mul_ne_zero hi (star_ne_zero.mpr hi)) hd
    have hn : ‖x i‖ = ‖y i‖ := by
      have he := congrArg norm hd
      simp only [norm_mul, norm_star] at he
      nlinarith [norm_nonneg (x i), norm_nonneg (y i)]
    refine ⟨star (x i) / star (y i), ?_, ?_⟩
    · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.mpr hy)]
    · funext j
      have hj : x j * star (x i) = y j * star (y i) := congrFun (congrFun h j) i
      change y j = star (x i) / star (y i) * x j
      rw [div_mul_eq_mul_div]
      exact (eq_div_iff (star_ne_zero.mpr hy)).mpr (by simpa only [mul_comm] using hj.symm)

/-- Intrinsic observable hypothesis: one vector in the raw density range belongs
to the coherent chart and its reconstructed core has injective linear transfer. -/
def ObservableChart (m : ℕ) (ψ : Word (3 + m) → ℂ) : Prop :=
  ∃ v : Word 3 → ℂ,
    let t := rawPrefix 3 m ψ *ᵥ v
    MvPolynomial.eval t chartPoly ≠ 0 ∧ Function.Injective (transfer (canonicalCore t))

/-- On the observable chart, the raw first-three-site density determines every
actual free-boundary competitor up to phase. No regularity premise is imposed
on that competitor. This conditional theorem does not assert genericity or
two-site minimality. -/
theorem observable_chart_phase_recovery (m : ℕ) (ψ φ : Word (3 + m) → ℂ)
    (hψ : ψ ∈ openBoundaryMPS (3 + m)) (hφ : φ ∈ openBoundaryMPS (3 + m))
    (hc : ObservableChart m ψ) :
    rawPrefix 3 m φ = rawPrefix 3 m ψ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ := by
  constructor
  · intro hraw
    obtain ⟨v, hg, hE⟩ := hc
    let t := rawPrefix 3 m ψ *ᵥ v
    change MvPolynomial.eval t chartPoly ≠ 0 at hg
    change Function.Injective (transfer (canonicalCore t)) at hE
    obtain ⟨a₀, a₁, l, r, hψ⟩ := hψ
    obtain ⟨b₀, b₁, l', r', hφ⟩ := hφ
    let A : Fin 2 → Bond := ![a₀, a₁]
    let B : Fin 2 → Bond := ![b₀, b₁]
    obtain ⟨g, hgA⟩ := observed_coherent m A l r v
    have htA : mpsState 3 (A 0) (A 1) l g = t := by
      rw [← hgA]
      exact congrArg (fun f => rawPrefix 3 m f *ᵥ v) hψ.symm
    obtain ⟨g', hgB⟩ := observed_coherent m B l' r' v
    have htB : mpsState 3 (B 0) (B 1) l' g' = t := by
      rw [← hgB]
      change rawPrefix 3 m (mpsState (3 + m) b₀ b₁ l' r') *ᵥ v = t
      rw [← hφ, hraw]
    obtain ⟨q, hq⟩ := gauge_lift t A l g htA hg (3 + m) r
    obtain ⟨q', hq'⟩ := gauge_lift t B l' g' htB hg (3 + m) r'
    have hψc : ψ = mpsState (3 + m) (canonicalCore t 0) (canonicalCore t 1)
        (reconstructedLeft t) q := hψ.trans hq
    have hφc : φ = mpsState (3 + m) (canonicalCore t 0) (canonicalCore t 1)
        (reconstructedLeft t) q' := hφ.trans hq'
    obtain ⟨g'', hgt⟩ := gauge_lift t A l g htA hg 3 g
    have hF : Function.Injective (prefixMap (canonicalCore t) (reconstructedLeft t) 3).mulVec :=
      chart_prefix_injective (canonicalCore t) (reconstructedLeft t) g''
        (by rw [← hgt, htA]; exact hg)
    rw [hψc, hφc, density_factor, density_factor] at hraw
    have hGr := (Function.Injective.iterate hE m)
      (sandwich_injective _ hF hraw)
    obtain ⟨z, hz, hphase⟩ := boundary_phase q q' hGr.symm
    refine ⟨z, hz, ?_⟩
    rw [hψc, hφc, hphase]
    funext w
    simp only [state_formula, mulVec_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
  · rintro ⟨z, hz, rfl⟩
    have hC : amplitudeColumns 3 m (z • ψ) = z • amplitudeColumns 3 m ψ := rfl
    rw [rawPrefix, hC, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hunit : z * star z = 1 := by
      change z * (starRingEnd ℂ) z = 1
      rw [Complex.mul_conj', hz]
      norm_num
    rw [hunit, one_smul]
    rfl

#print axioms observable_chart_phase_recovery

end
end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
