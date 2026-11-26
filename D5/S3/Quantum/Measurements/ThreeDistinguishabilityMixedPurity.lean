/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.inRegion_iff_cubic; instance=D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity.infeasible_not_inRegion
   digest: The closed-simplex mixed distinguishability region is given by the guarded cubic. -/

import D5.S3.Quantum.Measurements.ThreeDistinguishabilitySupportCount
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityRealCompression
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
import D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation

/-!
Korzekwa, Czachórski, Puchała and Życzkowski (arXiv:1812.09083v3),
Lemma 5 treats the pure-state criterion and Lemma 6 gives a boundary
pure-state reduction. Here the rank and real compression arguments apply
to the full four-coordinate mixed region.
-/

set_option autoImplicit false

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity

open Matrix
open D5.S3.Quantum.Measurements.ThreeDistinguishabilitySupportCount
  (exists_perm_rank_one_pair exists_rankOneDensity_of_rank_one)
open D5.S3.Quantum.Measurements.ThreeDistinguishabilityRealCompression
  (pure_replacement_for_conjugate_pair)
open D5.S3.Quantum.Measurements.ThreeDistinguishabilityProductRefutation (InRegion)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

private def gram (x y : Fin 4 → ℂ) : ℂ := star x ⬝ᵥ y

private theorem gram_swap (x y : Fin 4 → ℂ) : gram y x = star (gram x y) :=
  Matrix.star_dotProduct y x

private theorem gram_self (x : Fin 4 → ℂ) :
    gram x x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  change (∑ i, star (x i) * x i) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

private theorem trace_rankOneDensity (x : Fin 4 → ℂ) :
    (rankOneDensity x).trace = gram x x := by
  rw [rankOneDensity, Matrix.trace_vecMulVec, gram, dotProduct_comm]

private theorem diagonal_rankOneDensity (x : Fin 4 → ℂ) (i : Fin 4) :
    ((rankOneDensity x) i i).re = Complex.normSq (x i) := by
  change (x i * star (x i)).re = _
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem exists_entry_ne_zero (x : Fin 4 → ℂ) (hx : gram x x = 1) :
    ∃ j, x j ≠ 0 := by
  classical
  by_contra h
  have h0 : x = 0 := by
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  simpa [gram, h0] using hx

private theorem annihilates_of_mul_rankOneDensity_eq_zero
    (ρ : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℂ) (hx : gram x x = 1)
    (h : ρ * rankOneDensity x = 0) : ρ *ᵥ x = 0 := by
  obtain ⟨j, hj⟩ := exists_entry_ne_zero x hx
  rw [rankOneDensity, Matrix.mul_vecMulVec] at h
  funext i
  have hentry : (ρ *ᵥ x) i * star (x j) = 0 :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) h
  exact (mul_eq_zero.mp hentry).resolve_right (star_ne_zero.mpr hj)

private theorem gram_eq_zero_of_mul_rankOneDensity_eq_zero
    (x y : Fin 4 → ℂ) (hx : gram x x = 1) (hy : gram y y = 1)
    (h : rankOneDensity x * rankOneDensity y = 0) : gram x y = 0 := by
  obtain ⟨i, hi⟩ := exists_entry_ne_zero x hx
  obtain ⟨j, hj⟩ := exists_entry_ne_zero y hy
  simp only [rankOneDensity, Matrix.vecMulVec_mul_vecMulVec] at h
  have hentry : x i * (gram x y * star (y j)) = 0 :=
    congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hentry).resolve_left hi)).resolve_right
    (star_ne_zero.mpr hj)

private def phase (g x : Fin 4 → ℂ) : Fin 4 → ℂ := fun i => g i * x i

private theorem gram_phase (g : Fin 4 → ℂ) (hg : ∀ i, star (g i) * g i = 1)
    (x y : Fin 4 → ℂ) : gram (phase g x) (phase g y) = gram x y := by
  change (∑ i, star (g i * x i) * (g i * y i)) = ∑ i, star (x i) * y i
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  calc
    _ = (star (g i) * g i) * (star (x i) * y i) := by ring
    _ = _ := by rw [hg, one_mul]

/-- Replace a density annihilating the two pure columns by a unit column with
the same diagonal. The density and the two fixed columns are gauged together. -/
theorem pure_replacement_for_equal_moduli
    (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (x y : Fin 4 → ℂ) (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    (hxy : star x ⬝ᵥ y = 0)
    (hmx : ∀ i, Complex.normSq (x i) = p i) (hmy : ∀ i, Complex.normSq (y i) = p i)
    (ρ : Matrix (Fin 4) (Fin 4) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hρx : ρ *ᵥ x = 0) (hρy : ρ *ᵥ y = 0) :
    ∃ w : Fin 4 → ℂ, star x ⬝ᵥ w = 0 ∧ star y ⬝ᵥ w = 0 ∧
      (∀ i, Complex.normSq (w i) = (ρ i i).re) ∧ star w ⬝ᵥ w = 1 := by
  classical
  choose g hg hpair using fun i =>
    ThreeDistinguishabilityCubic.conjugate_pair_gauge_nonneg (x i) (y i) (p i) (hp i) (hmx i) (hmy i)
  have hstar (i : Fin 4) : star (g i) * g i = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, hg i, Complex.ofReal_one]
  let D := Matrix.diagonal g
  have hD : Dᴴ * D = 1 := by
    change (Matrix.diagonal g)ᴴ * Matrix.diagonal g = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    exact funext hstar
  have hphase (v : Fin 4 → ℂ) : D *ᵥ v = phase g v := by
    ext i
    exact Matrix.mulVec_diagonal g v i
  let z := phase g y
  have hcz : phase g x = star z := funext hpair
  have hzz : gram z z = 1 := (gram_phase g hstar y y).trans hy
  have horth : gram (star z) z = 0 := by
    rw [← hcz, show z = phase g y from rfl, gram_phase g hstar]
    exact hxy
  let B := D * ρ * Dᴴ
  have hB : B.PosSemidef := hρ.mul_mul_conjTranspose_same D
  have htB : B.trace = 1 := by
    change (D * ρ * Dᴴ).trace = 1
    rw [Matrix.trace_mul_comm (D * ρ) Dᴴ, ← Matrix.mul_assoc, hD, Matrix.one_mul, ht]
  have hdB (i : Fin 4) : (B i i).re = (ρ i i).re := by
    change ((Matrix.diagonal g * ρ * (Matrix.diagonal g)ᴴ) i i).re = _
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change (g i * ρ i i * star (g i)).re = _
    rw [show g i * ρ i i * star (g i) = (star (g i) * g i) * ρ i i by ring,
      hstar, one_mul]
  have hBphase (v : Fin 4 → ℂ) (hv : ρ *ᵥ v = 0) : B *ᵥ phase g v = 0 := by
    rw [← hphase]
    calc
      B *ᵥ (D *ᵥ v) = D *ᵥ (ρ *ᵥ ((Dᴴ * D) *ᵥ v)) := by
        simp only [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [hD, Matrix.one_mulVec, hv, Matrix.mulVec_zero]
  obtain ⟨w', hyw', hxw', hmw', hww'⟩ :=
    pure_replacement_for_conjugate_pair z hzz horth B hB htB
      (hBphase y hρy) (hcz ▸ hBphase x hρx)
  let w := phase (star g) w'
  have hw' : phase g w = w' := by
    funext i
    change g i * (star (g i) * w' i) = w' i
    rw [← mul_assoc, mul_comm (g i) (star (g i)), hstar, one_mul]
  have hwx : gram x w = 0 := by
    rw [← gram_phase g hstar x w, hcz, hw']
    exact hxw'
  have hwy : gram y w = 0 := by
    rw [← gram_phase g hstar y w, hw']
    exact hyw'
  have hwunit : gram w w = 1 := by
    rw [← gram_phase g hstar w w, hw']
    exact hww'
  refine ⟨w, hwx, hwy, ?_, hwunit⟩
  intro i
  change Complex.normSq (star (g i) * w' i) = _
  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, hg, one_mul, hmw', hdB]

/-- A witness for the mixed region is obtained from the three column projectors. -/
theorem inRegion_of_weighted_isometry (p : Fin 4 → ℝ)
    (W : Matrix (Fin 4) (Fin 3) ℂ) (hW : Wᴴ * W = 1)
    (hm : ∀ i j, ‖W i j‖ ^ 2 = p i) : InRegion p := by
  let v (j : Fin 3) : Fin 4 → ℂ := fun i => W i j
  have hmod (i : Fin 4) (j : Fin 3) : Complex.normSq (v j i) = p i :=
    (Complex.normSq_eq_norm_sq (W i j)).trans (hm i j)
  have hGram (j k : Fin 3) : gram (v j) (v k) = if j = k then 1 else 0 := by
    rw [← Matrix.one_apply]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j k) hW
  have hnorm (j : Fin 3) : gram (v j) (v j) = 1 := by simpa using hGram j j
  have hp1 : ∑ i, p i = 1 := by
    have h := hnorm 0
    rw [gram_self, show (∑ i, Complex.normSq (v 0 i)) = ∑ i, p i by simp [hmod],
      ← Complex.ofReal_one] at h
    exact Complex.ofReal_injective h
  refine ⟨⟨fun i => (Complex.normSq_nonneg (v 0 i)).trans_eq (hmod i 0), hp1⟩,
      fun j => rankOneDensity (v j), ?_, ?_, ?_⟩
  · intro j
    exact ⟨Matrix.posSemidef_vecMulVec_self_star _, (trace_rankOneDensity _).trans (hnorm j)⟩
  · intro j k hjk
    have hzero : gram (v j) (v k) = 0 := by simpa [hjk] using hGram j k
    change Matrix.vecMulVec (v j) (star (v j)) * Matrix.vecMulVec (v k) (star (v k)) = 0
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change Matrix.vecMulVec (v j) (gram (v j) (v k) • star (v k)) = 0
    rw [hzero, zero_smul, Matrix.vecMulVec_zero]
  · intro j i
    exact (diagonal_rankOneDensity _ i).trans (hmod i j)

/-- Every law in the mixed region has three pure, orthonormal witnesses. -/
theorem weighted_isometry_of_inRegion (p : Fin 4 → ℝ) (hp : InRegion p) :
    ∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧ ∀ i j, ‖W i j‖ ^ 2 = p i := by
  rcases hp with ⟨⟨hnn, _⟩, ρ, hρ, hOrth, hdiag⟩
  obtain ⟨σ, h0, h1⟩ := exists_perm_rank_one_pair ρ hρ hOrth
  obtain ⟨x, hx⟩ := exists_rankOneDensity_of_rank_one (hρ (σ 0)).1 (hρ (σ 0)).2 h0
  obtain ⟨y, hy⟩ := exists_rankOneDensity_of_rank_one (hρ (σ 1)).1 (hρ (σ 1)).2 h1
  have hUnitX : gram x x = 1 := by rw [← trace_rankOneDensity, ← hx, (hρ (σ 0)).2]
  have hUnitY : gram y y = 1 := by rw [← trace_rankOneDensity, ← hy, (hρ (σ 1)).2]
  have hPair : gram x y = 0 := by
    apply gram_eq_zero_of_mul_rankOneDensity_eq_zero x y hUnitX hUnitY
    rw [← hx, ← hy]
    exact hOrth _ _ (σ.injective.ne (by decide))
  have hModX (i : Fin 4) : Complex.normSq (x i) = p i := by
    rw [← diagonal_rankOneDensity, ← hx]
    exact hdiag (σ 0) i
  have hModY (i : Fin 4) : Complex.normSq (y i) = p i := by
    rw [← diagonal_rankOneDensity, ← hy]
    exact hdiag (σ 1) i
  have hKerX : ρ (σ 2) *ᵥ x = 0 := by
    apply annihilates_of_mul_rankOneDensity_eq_zero _ x hUnitX
    rw [← hx]
    exact hOrth _ _ (σ.injective.ne (by decide))
  have hKerY : ρ (σ 2) *ᵥ y = 0 := by
    apply annihilates_of_mul_rankOneDensity_eq_zero _ y hUnitY
    rw [← hy]
    exact hOrth _ _ (σ.injective.ne (by decide))
  obtain ⟨w, hxw, hyw, hmw, hww⟩ :=
    pure_replacement_for_equal_moduli p hnn x y hUnitX hUnitY hPair hModX hModY
      (ρ (σ 2)) (hρ (σ 2)).1 (hρ (σ 2)).2 hKerX hKerY
  have hUnitW : gram w w = 1 := hww
  have hXW : gram x w = 0 := hxw
  have hYW : gram y w = 0 := hyw
  have hYX : gram y x = 0 := by rw [gram_swap x y, hPair, star_zero]
  have hWX : gram w x = 0 := by rw [gram_swap x w, hXW, star_zero]
  have hWY : gram w y = 0 := by rw [gram_swap y w, hYW, star_zero]
  have hModW (i : Fin 4) : Complex.normSq (w i) = p i := (hmw i).trans (hdiag (σ 2) i)
  let v : Fin 3 → Fin 4 → ℂ := ![x, y, w]
  let W : Matrix (Fin 4) (Fin 3) ℂ := Matrix.of fun i j => v j i
  refine ⟨W, ?_, ?_⟩
  · ext j k
    change gram (v j) (v k) = (1 : Matrix (Fin 3) (Fin 3) ℂ) j k
    fin_cases j <;> fin_cases k <;> norm_num [v, Matrix.one_apply,
      hUnitX, hUnitY, hUnitW, hPair, hYX, hXW, hWX, hYW, hWY]
  · intro i j
    change ‖v j i‖ ^ 2 = p i
    rw [← Complex.normSq_eq_norm_sq]
    fin_cases j <;> simp [v, hModX, hModY, hModW]

/-- The four-level mixed region is exactly the region of three weighted
orthonormal columns. The isometry also forces the simplex conditions. -/
theorem inRegion_iff_weighted_isometry (p : Fin 4 → ℝ) :
    InRegion p ↔
      ∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧ ∀ i j, ‖W i j‖ ^ 2 = p i := by
  constructor
  · exact weighted_isometry_of_inRegion p
  · rintro ⟨W, hW, hm⟩
    exact inRegion_of_weighted_isometry p W hW hm

/-- The guarded cubic describes the mixed region on the closed simplex. -/
theorem inRegion_iff_cubic (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    InRegion p ↔ (∀ i, p i ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (∀ i, ThreeDistinguishabilityCubic.q p i ^ 2 * t ≥ ThreeDistinguishabilityCubic.d p i ^ 2) ∧
        ThreeDistinguishabilityCubic.phaseCubic p t = 0 :=
  (inRegion_iff_weighted_isometry p).trans
    (ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic_nonneg p hp hp1)

private def oneZeroWeights : Fin 4 → ℝ := ![0, 1 / 3, 1 / 3, 1 / 3]

/-- The vertex with first weight zero lies in the mixed region. -/
theorem one_zero_feasible : InRegion (![0, 1 / 3, 1 / 3, 1 / 3] : Fin 4 → ℝ) := by
  change InRegion oneZeroWeights
  have hn (i : Fin 4) : 0 ≤ oneZeroWeights i := by
    fin_cases i <;> norm_num [oneZeroWeights]
  have hs : ∑ i, oneZeroWeights i = 1 := by
    norm_num [oneZeroWeights, Fin.sum_univ_four]
  apply (inRegion_iff_cubic oneZeroWeights hn hs).2
  refine ⟨?_, 1, by norm_num, le_rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [oneZeroWeights]
  · intro i
    fin_cases i <;>
      norm_num [oneZeroWeights, ThreeDistinguishabilityCubic.q, ThreeDistinguishabilityCubic.d]
  · norm_num [oneZeroWeights, ThreeDistinguishabilityCubic.phaseCubic,
      ThreeDistinguishabilityCubic.cubicAfterConstant,
      ThreeDistinguishabilityCubic.q, ThreeDistinguishabilityCubic.d]

/-- An interior simplex law strictly below every cap is outside the mixed region. -/
theorem infeasible_not_inRegion : ¬ InRegion ThreeDistinguishabilityCubic.infeasibleWeights := by
  intro h
  exact ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns.2
    ((inRegion_iff_weighted_isometry _).1 h)

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityMixedPurity
