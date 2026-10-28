/- GID: D5/S3/Quantum/Matrix/RpowPencilTaylor
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/RpowPencilTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff]
   utility: none
   digest: Smooth CFC cube roots and ordered jets of positive definite matrix pencils. -/

/-
admission_basis: escape-witness
The noncommutative cubic linearization is inverted in a fixed spectral basis.
The local polynomial inverse is identified with the actual CFC root by continuity.
These are classical inverse-function and spectral calculus arguments; no novelty
or full HSF compatibility conclusion is asserted.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

/-! Actual CFC roots via the classical inverse function theorem on full real matrix space. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ContDiff

namespace D5.S3.Quantum.Matrix.RpowPencilTaylor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Linearization of the noncommutative cubic map on the full real matrix space. -/
def cubicLinear (P : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun E => P * P * E + P * E * P + E * P * P
      map_add' := by intros; simp only [mul_add, add_mul]; abel
      map_smul' := by
        intros
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply] }

/-- Coordinates in a single fixed eigenbasis, with no derivatives of eigenvectors. -/
def spectralCoordinates {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ _ hP.eigenvectorUnitary).symm

private theorem coordinates_self {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    spectralCoordinates hP P = Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) := by
  have hs := hP.conjStarAlgAut_star_eigenvectorUnitary
  rw [spectralCoordinates, Unitary.conjStarAlgAut_symm]
  convert hs using 1
  ext i j
  simp [Function.comp_def, RCLike.ofReal]

/-- The cubic derivative is an entrywise positive divisor, including repeated eigenvalues. -/
theorem cubicLinear_entry {P : Matrix n n ℂ} (hP : P.IsHermitian)
    (E : Matrix n n ℂ) (i j : n) :
    spectralCoordinates hP (cubicLinear P E) i j =
      ((hP.eigenvalues i ^ 2 + hP.eigenvalues i * hP.eigenvalues j +
        hP.eigenvalues j ^ 2 : ℝ) : ℂ) * spectralCoordinates hP E i j := by
  change spectralCoordinates hP (P * P * E + P * E * P + E * P * P) i j = _
  simp only [map_add, map_mul, coordinates_self, Matrix.add_apply,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.mul_apply, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

private theorem cubicLinear_injective {P : Matrix n n ℂ} (hP : P.PosDef) :
    Function.Injective (cubicLinear P) := by
  intro E F hEF
  have hE : cubicLinear P (E-F) = 0 := by rw [map_sub, hEF, sub_self]
  have hz : spectralCoordinates hP.isHermitian (E-F) = 0 := by
    ext i j
    have hpos : 0 < hP.isHermitian.eigenvalues i ^ 2 +
        hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues j +
        hP.isHermitian.eigenvalues j ^ 2 := by
      have hi := hP.eigenvalues_pos i
      have hj := hP.eigenvalues_pos j
      positivity
    have he := cubicLinear_entry hP.isHermitian (E-F) i j
    rw [hE, map_zero, Matrix.zero_apply] at he
    exact (mul_eq_zero.mp he.symm).resolve_left
      (show ((hP.isHermitian.eigenvalues i ^ 2 +
        hP.isHermitian.eigenvalues i * hP.isHermitian.eigenvalues j +
        hP.isHermitian.eigenvalues j ^ 2 : ℝ) : ℂ) ≠ 0 by exact_mod_cast hpos.ne')
  have hz' : spectralCoordinates hP.isHermitian (E-F) = spectralCoordinates hP.isHermitian 0 :=
    hz.trans (map_zero _).symm
  exact sub_eq_zero.mp ((spectralCoordinates hP.isHermitian).injective hz')

set_option backward.privateInPublic true in
/-- The cubic derivative as a continuous linear equivalence over all complex entries. -/
private def cubicEquiv {P : Matrix n n ℂ} (hP : P.PosDef) :
    Matrix n n ℂ ≃L[ℝ] Matrix n n ℂ :=
  (LinearEquiv.ofInjectiveEndo (cubicLinear P).toLinearMap
    (cubicLinear_injective hP)).toContinuousLinearEquiv

private theorem cubic_hasFDerivAt (P : Matrix n n ℂ) :
    HasFDerivAt (fun Q : Matrix n n ℂ => Q * Q * Q) (cubicLinear P) P := by
  have hh := ((hasFDerivAt_id (𝕜 := ℝ) P).mul' (hasFDerivAt_id (𝕜 := ℝ) P)).mul'
    (hasFDerivAt_id (𝕜 := ℝ) P)
  apply hh.congr_fderiv
  ext E : 1
  change P * P * E + (P * E + E * P) * P = P * P * E + P * E * P + E * P * P
  noncomm_ring

private theorem pencil_posDef_near {Y K : Matrix n n ℂ} (hY : Y.PosDef)
    (hK : K.IsHermitian) : ∀ᶠ t : ℝ in 𝓝 0, (Y + t • K).PosDef := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    letI := hn
    exact Filter.Eventually.of_forall fun _ => by
      simpa [Subsingleton.elim (Y + _ • K) 1] using (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef)
  | inr hn =>
    letI := hn
    obtain ⟨r, hr, hrY⟩ := (CFC.exists_pos_algebraMap_le_iff Y hY.isHermitian).mpr
      (fun x hx => hY.isStrictlyPositive.spectrum_pos hx)
    have hcont : ContinuousAt (fun t : ℝ => ‖t • K‖) 0 := by fun_prop
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t • K‖ < r / 2 :=
      hcont.eventually (eventually_lt_nhds (by simpa using half_pos hr))
    filter_upwards [hsmall] with t ht
    have hmap : algebraMap ℝ (Matrix n n ℂ) ‖t • K‖ ≤ algebraMap ℝ _ (r/2) := by
      rw [Matrix.le_iff, ← map_sub, Algebra.algebraMap_eq_smul_one]
      exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr ht.le)
    have hlow : algebraMap ℝ (Matrix n n ℂ) (r/2) ≤ Y + t • K := by
      calc
        algebraMap ℝ _ (r/2) = algebraMap ℝ _ r + -(algebraMap ℝ _ (r/2)) := by
          rw [← map_neg, ← map_add]
          congr 1
          ring
        _ ≤ Y + t • K := add_le_add hrY <| (neg_le_neg hmap).trans <|
          IsSelfAdjoint.neg_algebraMap_norm_le_self (t • K) (hK.smul (IsSelfAdjoint.all t))
    exact (IsStrictlyPositive.of_le (isStrictlyPositive_algebraMap (A := Matrix n n ℂ) (half_pos hr)) hlow).posDef

/-- The positive definite CFC cube root cubes back to the original matrix. -/
private theorem cube_root_cube {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.rpow A (1/3 : ℝ) * CFC.rpow A (1/3 : ℝ) * CFC.rpow A (1/3 : ℝ) = A := by
  have he : CFC.rpow A (1/3 : ℝ) * CFC.rpow A (1/3 : ℝ) * CFC.rpow A (1/3 : ℝ) =
      (CFC.rpow A (1/3 : ℝ)) ^ 3 := by noncomm_ring
  rw [he]
  simp only [CFC.rpow_eq_pow]
  rw [← CFC.rpow_natCast _ 3 CFC.rpow_nonneg,
    CFC.rpow_rpow _ _ _ (by norm_num) hA.isStrictlyPositive]
  norm_num [CFC.rpow_one _ hA.posSemidef.nonneg]

/-- Actual CFC cube roots of arbitrary Hermitian pencils are smooth near zero.
There is no commutativity assumption, spectral floor parameter, or derivative premise. -/
theorem contDiffAt_cubeRoot {Y K : Matrix n n ℂ} (hY : Y.PosDef) (hK : K.IsHermitian) :
    ContDiffAt ℝ ∞ (fun t : ℝ => CFC.rpow (Y + t • K) (1/3 : ℝ)) 0 := by
  let P := CFC.rpow Y (1/3 : ℝ)
  have hP : P.PosDef := (IsStrictlyPositive.rpow Y (1/3 : ℝ) hY.isStrictlyPositive).posDef
  let f := fun Q : Matrix n n ℂ => Q * Q * Q
  have hf : ContDiffAt ℝ ∞ f P := by dsimp [f]; fun_prop
  have hd : HasFDerivAt f (cubicEquiv hP : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) P :=
    cubic_hasFDerivAt P
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let g := hf.localInverse hd hn
  have hcube : f P = Y := cube_root_cube hY
  have hg : ContDiffAt ℝ ∞ g Y := hcube ▸ hf.to_localInverse hd hn
  have hpencil : ContDiffAt ℝ ∞ (fun t : ℝ => Y + t • K) 0 := by fun_prop
  have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => g (Y + t • K)) 0 := by
    have hg' : ContDiffAt ℝ ∞ g (Y + (0 : ℝ) • K) := by simpa only [zero_smul, add_zero] using hg
    exact hg'.comp 0 hpencil
  have hpos := pencil_posDef_near hY hK
  have hq : ContinuousAt (fun t : ℝ => CFC.rpow (Y + t • K) (1/3 : ℝ)) 0 := by
    have hc := (CFC.continuousOn_rpow (A := Matrix n n ℂ) (1/3 : ℝ)).continuousWithinAt
      hY.isStrictlyPositive
    have hp : Tendsto (fun t : ℝ => Y + t • K) (𝓝 0) (𝓝 Y) := by
      simpa only [zero_smul, add_zero] using hpencil.continuousAt.tendsto
    have hct := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hp, hpos.mono fun _ h => h.isStrictlyPositive⟩)
    simpa only [CFC.rpow_eq_pow, ContinuousAt, Function.comp_def, zero_smul, add_zero] using hct
  have hleft := (hf.hasStrictFDerivAt' hd hn).eventually_left_inverse
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      g (f (CFC.rpow (Y + t • K) (1/3 : ℝ))) = CFC.rpow (Y + t • K) (1/3 : ℝ) := by
    have hleft' : ∀ᶠ Q in 𝓝 P, g (f Q) = Q := hleft
    have hq' : Tendsto (fun t : ℝ => CFC.rpow (Y + t • K) (1/3 : ℝ)) (𝓝 0) (𝓝 P) := by
      simpa only [zero_smul, add_zero] using hq.tendsto
    exact hq'.eventually hleft' 
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear, hpos] with t ht hpt
  simpa only [show f (CFC.rpow (Y + t • K) (1/3 : ℝ)) = Y + t • K from cube_root_cube hpt] using ht.symm

end D5.S3.Quantum.Matrix.RpowPencilTaylor
