/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality
   mirror-E: none(waiver:source-owner-registration-pending)
   anchors: []
   utility: none
   digest: The real thirteen-parameter canonical MPS chart and its twelve-coordinate raw prefix record. -/

import D5.S3.Geometry.C1LocalFiber
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial

/-! Canonical parameters and their real observation map for the prefix reading
of Critch--Morton Conjecture 9. The canonical inverse argument belongs to
Ma--Zhang's note.tex (the Conjecture 8 supplier); this module does not claim it
as a new discovery. Raw densities retain the affine norm scale. -/

noncomputable section
open Matrix Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality

open OpenBoundaryMPSMarginalBirationality
open OpenBoundaryMPSDensityRecovery
open PeriodicMPSParentIntersection (Bond Word)

/-- Five complex core coordinates, a real phase-fixing coordinate and one complex boundary. -/
abbrev Parameter := (Fin 5 → ℂ) × ℝ × ℂ

/-- Two real diagonal entries, a complex off-diagonal entry, and a complex two by two block. -/
abbrev Record := (ℝ × ℝ) × ℂ × Bond

def left (θ : Parameter) : Fin 2 → ℂ := ![θ.1 0, 1]

def core (θ : Parameter) : Fin 2 → Bond :=
  ![!![θ.1 1, θ.1 2; 1 - θ.1 0 * θ.1 1, -θ.1 0 * θ.1 2],
    !![θ.1 3, θ.1 4; -θ.1 0 * θ.1 3, 1 - θ.1 0 * θ.1 4]]

def right (θ : Parameter) : Fin 2 → ℂ := ![(θ.2.1 : ℂ), θ.2.2]

def state (n : ℕ) (θ : Parameter) : Word n → ℂ :=
  mpsState n (core θ 0) (core θ 1) (left θ) (right θ)

def density (m : ℕ) (θ : Parameter) : Matrix (Word 2) (Word 2) ℂ :=
  rawPrefix 2 m (state (2 + m) θ)

def densityRecord (Q : Matrix (Word 2) (Word 2) ℂ) : Record :=
  (((Q ![0, 0] ![0, 0]).re, (Q ![0, 1] ![0, 1]).re),
    Q ![0, 0] ![0, 1], fun i j => Q ![0, i] ![1, j])

def record (m : ℕ) (θ : Parameter) : Record := densityRecord (density m θ)

private lemma smooth_core (i j k : Fin 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => core θ i j k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> dsimp [core, Matrix.of_apply] <;> fun_prop

private lemma smooth_left (i : Fin 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => left θ i) := by
  fin_cases i <;> dsimp [left] <;> fun_prop

private lemma smooth_right (i : Fin 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => right θ i) := by
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_snd.fst)
  · dsimp [right]; fun_prop

private lemma smooth_product (s : List (Fin 2)) (i j : Fin 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => (s.map (core θ)).prod i j) := by
  induction s generalizing i j with
  | nil => simp only [List.map_nil, List.prod_nil]; exact contDiff_const
  | cons a s ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    apply ContDiff.sum
    intro k _
    exact (smooth_core a i k).mul (ih k j)

private lemma smooth_state (n : ℕ) (w : Word n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => state n θ w) := by
  have hcore (θ : Parameter) : ![core θ 0, core θ 1] = core θ := FinVec.etaExpand_eq _
  simp only [state, mpsState, hcore, List.ofFn_comp', dotProduct, mulVec]
  apply ContDiff.sum
  intro i _
  apply (smooth_left i).mul
  apply ContDiff.sum
  intro j _
  exact (smooth_product (List.ofFn w) i j).mul (smooth_right j)

private lemma smooth_density (m : ℕ) (u v : Word 2) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun θ : Parameter => density m θ u v) := by
  simp only [density, rawPrefix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    amplitudeColumns]
  apply ContDiff.sum
  intro b _
  exact (smooth_state (2 + m) (Fin.append u b)).mul
    (Complex.conjCLE.contDiff.comp (smooth_state (2 + m) (Fin.append v b)))

private lemma smooth_record (m : ℕ) : ContDiff ℝ (⊤ : WithTop ℕ∞) (record m) := by
  unfold record densityRecord
  apply ContDiff.prodMk
  · exact (Complex.reCLM.contDiff.comp (smooth_density m ![0, 0] ![0, 0])).prodMk
      (Complex.reCLM.contDiff.comp (smooth_density m ![0, 1] ![0, 1]))
  · apply ContDiff.prodMk
    · exact smooth_density m _ _
    · apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      exact smooth_density m _ _

private lemma normalized_rows (θ : Parameter) (i : Fin 2) :
    left θ ᵥ* core θ i = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [left, core, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private lemma gauge_row (θ : Parameter) (s : ℂ) (hs : s ≠ 0)
    (U : Bond) (hU : IsUnit U.det) (i : Fin 2) :
    (s⁻¹ • (left θ ᵥ* U⁻¹)) ᵥ* (s • (U * core θ i * U⁻¹)) =
      (U⁻¹).row i := by
  rw [smul_vecMul, vecMul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul,
    vecMul_vecMul, Matrix.mul_assoc U (core θ i) U⁻¹,
    Matrix.nonsing_inv_mul_cancel_left _ _ hU, ← vecMul_vecMul,
    normalized_rows, single_one_vecMul]

/-- The common three-site reconstruction identifies the five canonical core
coordinates. Right boundaries are unrestricted in this intermediate statement. -/
private lemma canonical_core_rigidity (θ η : Parameter) (g h : Fin 2 → ℂ)
    (heq : mpsState 3 (core θ 0) (core θ 1) (left θ) g =
      mpsState 3 (core η 0) (core η 1) (left η) h)
    (hg : MvPolynomial.eval (mpsState 3 (core θ 0) (core θ 1) (left θ) g)
      chartPoly ≠ 0) : θ.1 = η.1 := by
  obtain ⟨s, hs, U, hU, hl, hm, _⟩ :=
    triple_gauge (core θ 0) (core θ 1) (left θ) g hg
  obtain ⟨t, ht, V, hV, hl', hm', _⟩ :=
    triple_gauge (core η 0) (core η 1) (left η) h (by simpa only [heq] using hg)
  rw [← heq] at hl' hm'
  have hrows (i : Fin 2) : (U⁻¹).row i = (V⁻¹).row i := by
    have hA (ξ : Parameter) : ![core ξ 0, core ξ 1] = core ξ := FinVec.etaExpand_eq _
    calc
      (U⁻¹).row i = _ := (gauge_row θ s hs U hU i).symm
      _ = reconstructedLeft _ ᵥ* reconstructedMatrix _ i := by rw [hl, hm, hA]
      _ = _ := by rw [hl', hm', hA]
      _ = (V⁻¹).row i := gauge_row η t ht V hV i
  have hinv : U⁻¹ = V⁻¹ := by ext i j; exact congrFun (hrows i) j
  have hUV : U = V := by
    have hh := congrArg (fun M : Bond => M⁻¹) hinv
    simpa only [Matrix.nonsing_inv_nonsing_inv U hU,
      Matrix.nonsing_inv_nonsing_inv V hV] using hh
  subst V
  have hscaled : s⁻¹ • left θ = t⁻¹ • left η := by
    have hh := congrArg (fun v : Fin 2 → ℂ => v ᵥ* U) (hl.symm.trans hl')
    simpa only [smul_vecMul, vecMul_vecMul, Matrix.nonsing_inv_mul U hU,
      vecMul_one] using hh
  have hst : s = t := by
    have hh := congrFun hscaled 1
    have hi : s⁻¹ = t⁻¹ := by simpa [left] using hh
    exact inv_injective hi
  subst t
  have hleft : left θ = left η := by
    have hh := congrArg (fun v : Fin 2 → ℂ => s • v) hscaled
    simpa only [smul_smul, mul_inv_cancel₀ hs, one_smul] using hh
  have hcore (i : Fin 2) : core θ i = core η i := by
    have hh := congrArg (fun M : Bond => U⁻¹ * (s⁻¹ • M) * U)
      ((hm i).symm.trans (hm' i))
    have hA (ξ : Parameter) : ![core ξ 0, core ξ 1] = core ξ := FinVec.etaExpand_eq _
    simpa only [hA, smul_smul, inv_mul_cancel₀ hs, one_smul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left U _ hU,
      Matrix.nonsing_inv_mul U hU, Matrix.mul_one] using hh
  ext i
  fin_cases i
  · exact congrFun hleft 0
  · exact congrFun (congrFun (hcore 0) 0) 0
  · exact congrFun (congrFun (hcore 0) 0) 1
  · exact congrFun (congrFun (hcore 1) 0) 0
  · exact congrFun (congrFun (hcore 1) 0) 1

private lemma triple_formula (θ : Parameter) (g : Fin 2 → ℂ) (i j k : Fin 2) :
    mpsState 3 (core θ 0) (core θ 1) (left θ) g ![i, j, k] =
      ((core θ j * core θ k) *ᵥ g) i := by
  have hA : ![core θ 0, core θ 1] = core θ := FinVec.etaExpand_eq _
  simp only [mpsState, hA, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.empty_val', mul_one]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    normalized_rows, single_one_dotProduct, Matrix.mulVec_mulVec]
  rfl

private lemma boundary_contraction (θ : Parameter) (g : Fin 2 → ℂ) (k : Fin 2) :
    (∑ i : Fin 2, ∑ j : Fin 2, left θ i * left θ j *
      mpsState 3 (core θ 0) (core θ 1) (left θ) g ![i, j, k]) = g k := by
  simp only [triple_formula]
  calc
    (∑ i : Fin 2, ∑ j : Fin 2, left θ i * left θ j *
      ((core θ j * core θ k) *ᵥ g) i) =
        ∑ j : Fin 2, left θ j * dotProduct (left θ) ((core θ j * core θ k) *ᵥ g) := by
          simp only [Fin.sum_univ_two, dotProduct]
          ring
    _ = ∑ j : Fin 2, left θ j * (core θ k *ᵥ g) j := by
      congr 1
      ext j
      rw [← mulVec_mulVec, dotProduct_mulVec, normalized_rows, single_one_dotProduct]
    _ = g k := by
      change dotProduct (left θ) (core θ k *ᵥ g) = g k
      rw [dotProduct_mulVec, normalized_rows, single_one_dotProduct]

/-- On the positive-real right-boundary slice, phase equality of canonical
three-site tensors in the coherent chart forces equality of all parameters.
This is a consumed chart inverse, not the C9 two-site minimality conclusion. -/
theorem three_site_phase_rigidity (θ η : Parameter)
    (hθ : 0 < θ.2.1) (hη : 0 < η.2.1) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (heq : state 3 η = ζ • state 3 θ)
    (hg : MvPolynomial.eval (state 3 η) chartPoly ≠ 0) : θ = η := by
  have hscale : mpsState 3 (core θ 0) (core θ 1) (left θ) (ζ • right θ) =
      ζ • state 3 θ := by
    ext w
    simp only [mpsState, state, mulVec_smul, dotProduct_smul, Pi.smul_apply]
  have htensor : mpsState 3 (core θ 0) (core θ 1) (left θ) (ζ • right θ) =
      mpsState 3 (core η 0) (core η 1) (left η) (right η) := hscale.trans heq.symm
  have hc : θ.1 = η.1 := canonical_core_rigidity θ η _ _ htensor
    (by simpa only [htensor, state] using hg)
  have hl : left θ = left η := by simp only [left, hc]
  have hr : ζ • right θ = right η := by
    ext k
    rw [← boundary_contraction θ (ζ • right θ) k,
      ← boundary_contraction η (right η) k]
    rw [htensor, hl]
  have hr0 : ζ * (θ.2.1 : ℂ) = (η.2.1 : ℂ) := by
    simpa [right] using congrFun hr 0
  have hre : ζ.re * θ.2.1 = η.2.1 := by
    simpa using congrArg Complex.re hr0
  have him : ζ.im * θ.2.1 = 0 := by
    simpa using congrArg Complex.im hr0
  have hζim : ζ.im = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt hθ)
  have hζre : 0 < ζ.re := (mul_pos_iff_of_pos_right hθ).mp (hre ▸ hη)
  have hζone : ζ = 1 := by
    have hn : ζ.re ^ 2 = 1 := by
      have hh := Complex.sq_norm ζ
      rw [hζ] at hh
      simp only [one_pow, Complex.normSq_apply, hζim, mul_zero, add_zero] at hh
      nlinarith
    have hre1 : ζ.re = 1 := by nlinarith
    exact Complex.ext hre1 (by simpa using hζim)
  rw [hζone, one_smul] at hr
  apply Prod.ext hc
  apply Prod.ext
  · exact Complex.ofReal_injective (by simpa [right] using congrFun hr 0)
  · simpa [right] using congrFun hr 1

set_option maxHeartbeats 800000 in
private lemma schur_of_rank_le_two (H B C D : Bond) (hH : IsUnit H.det)
    (hr : (Matrix.fromBlocks H B C D).rank ≤ 2) : D = C * H⁻¹ * B := by
  let V := Fin 2 → ℂ
  let Q := Matrix.fromBlocks H B C D
  let M : V × V →ₗ[ℂ] (Fin 2 ⊕ Fin 2 → ℂ) :=
    { toFun := fun w => Sum.elim (H⁻¹ *ᵥ (w.1 - B *ᵥ w.2)) w.2
      map_add' := by
        intro x y
        ext i
        cases i with
        | inl i =>
          change (H⁻¹ *ᵥ ((x.1 + y.1) - B *ᵥ (x.2 + y.2))) i =
            (H⁻¹ *ᵥ (x.1 - B *ᵥ x.2)) i + (H⁻¹ *ᵥ (y.1 - B *ᵥ y.2)) i
          rw [mulVec_add, ← sub_add_sub_comm, mulVec_add]
          rfl
        | inr i => rfl
      map_smul' := by
        intro c x
        ext i
        cases i with
        | inl i =>
          change (H⁻¹ *ᵥ (c • x.1 - B *ᵥ (c • x.2))) i =
            (c • (H⁻¹ *ᵥ (x.1 - B *ᵥ x.2))) i
          rw [mulVec_smul, ← smul_sub, mulVec_smul]
        | inr i => rfl }
  let p : (Fin 2 ⊕ Fin 2 → ℂ) →ₗ[ℂ] V :=
    { toFun := fun v i => v (Sum.inl i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T := Q.mulVecLin.comp M
  have htop : p.comp T = LinearMap.fst ℂ V V := by
    apply LinearMap.ext
    intro w
    funext i
    change (Q *ᵥ (Sum.elim (H⁻¹ *ᵥ (w.1 - B *ᵥ w.2)) w.2)) (Sum.inl i) = w.1 i
    simp only [Q, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv H hH, one_mulVec]
    exact congrFun (sub_add_cancel w.1 (B *ᵥ w.2)) i
  have hrT : Module.finrank ℂ (LinearMap.range T) ≤ Module.finrank ℂ V := by
    rw [show Module.finrank ℂ V = 2 from Module.finrank_fin_fun ℂ]
    have hrQ : Module.finrank ℂ (LinearMap.range Q.mulVecLin) ≤ 2 := hr
    have hsub : LinearMap.range T ≤ LinearMap.range Q.mulVecLin := by
      rintro y ⟨x, rfl⟩
      exact ⟨M x, rfl⟩
    have hle : Module.finrank ℂ (LinearMap.range T) ≤
        Module.finrank ℂ (LinearMap.range Q.mulVecLin) := Submodule.finrank_mono hsub
    exact hle.trans hrQ
  have hz (z : V) := D5.S3.Geometry.C1LocalFiber.linear_vertical_eq_zero T p htop hrT z
  ext i j
  have hh := congrFun (hz (Pi.single j 1)) (Sum.inr i)
  change (Q *ᵥ Sum.elim (H⁻¹ *ᵥ ((0 : V) - B *ᵥ Pi.single j 1))
    (Pi.single j 1)) (Sum.inr i) = 0 at hh
  simp only [Q, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr] at hh
  change (C *ᵥ (H⁻¹ *ᵥ ((0 : V) - B *ᵥ Pi.single j 1))) i +
    (D *ᵥ Pi.single j 1) i = 0 at hh
  simp only [zero_sub, mulVec_neg, mulVec_mulVec, mulVec_single_one,
    Pi.neg_apply, Matrix.mul_assoc] at hh
  rw [Matrix.mulVec_neg] at hh
  change -(C * H⁻¹ * B) i j + D i j = 0 at hh
  exact (neg_add_eq_zero.mp hh).symm

def leading (Q : Matrix (Word 2) (Word 2) ℂ) : Bond :=
  fun i j => Q ![0, i] ![0, j]

private def cross (Q : Matrix (Word 2) (Word 2) ℂ) : Bond :=
  fun i j => Q ![0, i] ![1, j]

private def trailing (Q : Matrix (Word 2) (Word 2) ℂ) : Bond :=
  fun i j => Q ![1, i] ![1, j]

private lemma hermitian_diagonal_im {ι : Type*} {Q : Matrix ι ι ℂ}
    (hQ : Q.IsHermitian) (i : ι) : (Q i i).im = 0 := by
  have hh := congrArg Complex.im (hQ.apply i i)
  simp only [Complex.star_def, Complex.conj_im] at hh
  linarith

private lemma schur_completion {Q : Matrix (Word 2) (Word 2) ℂ}
    (hQ : Q.IsHermitian) (hr : Q.rank ≤ 2) (hH : IsUnit (leading Q).det) :
    trailing Q = (cross Q)ᴴ * (leading Q)⁻¹ * cross Q := by
  let e : Fin 2 ⊕ Fin 2 → Word 2 := Sum.elim (fun i => ![0, i]) (fun i => ![1, i])
  have hblock : Q.submatrix e e =
      Matrix.fromBlocks (leading Q) (cross Q) (cross Q)ᴴ (trailing Q) := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j => exact (hQ.apply _ _).symm
      | inr j => rfl
  apply schur_of_rank_le_two _ _ _ _ hH
  rw [← hblock]
  exact (Matrix.rank_submatrix_le Q e e).trans hr

/-- On Hermitian matrices of rank at most two with invertible fixed leading
principal block, the twelve real record coordinates determine the entire matrix. -/
theorem densityRecord_injective {Q Q' : Matrix (Word 2) (Word 2) ℂ}
    (hQ : Q.IsHermitian) (hQ' : Q'.IsHermitian) (hr : Q.rank ≤ 2) (hr' : Q'.rank ≤ 2)
    (hH : IsUnit (leading Q).det) (heq : densityRecord Q = densityRecord Q') : Q = Q' := by
  have h00 : Q ![0, 0] ![0, 0] = Q' ![0, 0] ![0, 0] := by
    apply Complex.ext (congrArg (fun r : Record => r.1.1) heq)
    rw [hermitian_diagonal_im hQ, hermitian_diagonal_im hQ']
  have h11 : Q ![0, 1] ![0, 1] = Q' ![0, 1] ![0, 1] := by
    apply Complex.ext (congrArg (fun r : Record => r.1.2) heq)
    rw [hermitian_diagonal_im hQ, hermitian_diagonal_im hQ']
  have h01 : Q ![0, 0] ![0, 1] = Q' ![0, 0] ![0, 1] :=
    congrArg (fun r : Record => r.2.1) heq
  have hB : cross Q = cross Q' := congrArg (fun r : Record => r.2.2) heq
  have hlead : leading Q = leading Q' := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · change Q ![0, 1] ![0, 0] = Q' ![0, 1] ![0, 0]
      rw [← hQ.apply ![0, 1] ![0, 0], h01, hQ'.apply]
    · exact h11
  have htail : trailing Q = trailing Q' := by
    rw [schur_completion hQ hr hH,
      schur_completion hQ' hr' (by simpa only [← hlead] using hH), hlead, hB]
  ext u v
  have hu : u = ![u 0, u 1] := (FinVec.etaExpand_eq u).symm
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hu, hv]
  generalize u 0 = i, u 1 = j, v 0 = k, v 1 = l
  fin_cases i <;> fin_cases k
  · exact congrFun (congrFun hlead j) l
  · exact congrFun (congrFun hB j) l
  · rw [← hQ.apply, ← hQ'.apply]
    exact congrArg star (congrFun (congrFun hB l) j)
  · exact congrFun (congrFun htail j) l

/-- The actual coherent first-three-site contraction at source length `3 + m`. -/
def coherent (m : ℕ) (θ : Parameter) : Word 3 → ℂ :=
  improperMarginal (3 + m) 0 (by omega) (state (3 + m) θ)

/-- The intended phase-fixed open chart; nonemptiness is not included as a premise
or silently inferred from its openness. -/
def canonicalChart (m : ℕ) : Set Parameter :=
  {θ | 0 < θ.2.1 ∧ MvPolynomial.eval (coherent m θ) chartPoly ≠ 0 ∧
    (core θ 0 + core θ 1).det ≠ 0 ∧ (leading (density (1 + m) θ)).det ≠ 0}

private lemma smooth_coherent (m : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (coherent m) := by
  apply contDiff_pi.mpr
  intro t
  simp only [coherent, improperMarginal]
  apply ContDiff.sum
  intro w _
  split_ifs
  · exact smooth_state (3 + m) w
  · exact contDiff_const

/-- The full phase-fixed canonical parameter conditions are open in the
thirteen-dimensional real source, including the fixed Q2 leading-block test. -/
theorem isOpen_canonicalChart (m : ℕ) : IsOpen (canonicalChart m) := by
  have hρ : Continuous (fun θ : Parameter => θ.2.1) := continuous_snd.fst
  have ht : Continuous (fun θ : Parameter => MvPolynomial.eval (coherent m θ) chartPoly) :=
    (MvPolynomial.continuous_eval chartPoly).comp (smooth_coherent m).continuous
  have hA : Continuous (fun θ : Parameter => core θ 0 + core θ 1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (smooth_core 0 i j).continuous.add (smooth_core 1 i j).continuous
  have hH : Continuous (fun θ : Parameter => leading (density (1 + m) θ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (smooth_density (1 + m) _ _).continuous
  exact (isOpen_lt continuous_const hρ).inter
    ((isOpen_ne_fun ht continuous_const).inter
      ((isOpen_ne_fun hA.matrix_det continuous_const).inter
        (isOpen_ne_fun hH.matrix_det continuous_const)))

/-- Every nonempty open subset of the actual canonical real parameter space
has two distinct parameters with the same twelve raw Q2 coordinates.
This statement alone does not assert equality of Q2 or inequivalence of states. -/
theorem record_collision (m : ℕ) {U : Set Parameter} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ θ ∈ U, ∃ η ∈ U, θ ≠ η ∧ record m θ = record m η := by
  classical
  have hdim : Module.finrank ℝ Record < Module.finrank ℝ Parameter := by
    change Module.finrank ℝ ((ℝ × ℝ) × ℂ × (Fin 2 → Fin 2 → ℂ)) <
      Module.finrank ℝ ((Fin 5 → ℂ) × ℝ × ℂ)
    norm_num [Module.finrank_prod, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
  have hn := D5.S3.Geometry.C1LocalFiber.not_injOn hU hne
    ((smooth_record m).of_le (by norm_num)).contDiffOn hdim
  by_contra hc
  apply hn
  intro θ hθ η hη heq
  by_contra hne
  exact hc ⟨θ, hθ, η, hη, hne, heq⟩

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
