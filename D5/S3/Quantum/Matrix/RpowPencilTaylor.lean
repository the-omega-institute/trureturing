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

/-! Actual CFC roots via the classical inverse function theorem on full real matrix space.
The six typed registration attempts have unfinished source-selection bindings;
see https://github.com/the-omega-institute/trureturing/issues/23103. -/

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


/-- The factorial-normalized actual derivative at zero, rather than a formal coefficient. -/
def jetCoeff (f : ℝ → Matrix n n ℂ) (j : ℕ) : Matrix n n ℂ :=
  ((j.factorial : ℝ)⁻¹) • iteratedDeriv j f 0

private theorem jetCoeff_mul (f g : ℝ → Matrix n n ℂ)
    (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0)
    (j : ℕ) (hj : j ≤ 3) :
    jetCoeff (fun t => f t * g t) j =
      ∑ a ∈ Finset.range (j+1), jetCoeff f a * jetCoeff g (j-a) := by
  have hf' : ContDiffAt ℝ j f 0 := hf.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffAt ℝ j g 0 := hg.of_le (by exact_mod_cast le_top)
  rw [jetCoeff, iteratedDeriv_fun_mul hf' hg']
  interval_cases j <;>
    norm_num [Finset.sum_range_succ, jetCoeff, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_smul, mul_add, add_mul, two_mul, show (3 : Matrix n n ℂ) = 1+1+1 by norm_num]
  all_goals
    try simp only [show (3 : Matrix n n ℂ) = 1+1+1 by norm_num,
      add_mul, one_mul, smul_add]
    module


private theorem jetCoeff_pencil (Y K : Matrix n n ℂ) :
    jetCoeff (fun t : ℝ => Y+t • K) 1 = K ∧
    jetCoeff (fun t : ℝ => Y+t • K) 2 = 0 ∧
    jetCoeff (fun t : ℝ => Y+t • K) 3 = 0 := by
  have hd : deriv (fun t : ℝ => Y+t • K) = fun _ => K := by
    funext t
    simpa using ((hasDerivAt_const t Y).add ((hasDerivAt_id t).smul_const K)).deriv
  simp [jetCoeff, iteratedDeriv_succ', hd, iteratedDeriv_const]

/-- Cubic recurrences for the first three factorial-normalized actual CFC derivatives. -/
theorem cubeRoot_jet_recurrences {Y K : Matrix n n ℂ} (hY : Y.PosDef)
    (hK : K.IsHermitian) :
    let P := CFC.rpow Y (1/3 : ℝ)
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    C 0 = P ∧ cubicLinear P (C 1) = K ∧
      cubicLinear P (C 2) = -(P * C 1 * C 1 + C 1 * P * C 1 + C 1 * C 1 * P) ∧
      cubicLinear P (C 3) = -(P * C 1 * C 2 + P * C 2 * C 1 +
        C 1 * P * C 2 + C 2 * P * C 1 + C 1 * C 2 * P + C 2 * C 1 * P +
        C 1 * C 1 * C 1) := by
  let P := CFC.rpow Y (1/3 : ℝ)
  let q := fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ)
  let C := jetCoeff q
  have hq : ContDiffAt ℝ ∞ q 0 := contDiffAt_cubeRoot hY hK
  have hc : (fun t => q t * q t * q t) =ᶠ[𝓝 0] fun t => Y+t • K :=
    (pencil_posDef_near hY hK).mono fun _ ht => cube_root_cube ht
  have heq (j : ℕ) : jetCoeff (fun t => q t*q t*q t) j =
      jetCoeff (fun t : ℝ => Y+t • K) j :=
    congrArg (fun M : Matrix n n ℂ => ((j.factorial : ℝ)⁻¹) • M)
      (hc.iteratedDeriv_eq j)
  have h0 : C 0 = P := by simp [C, q, P, jetCoeff]
  have h0' : jetCoeff q 0 = P := h0
  have hs (j : ℕ) (hj : j ≤ 3) := jetCoeff_mul q q hq hq j hj
  have hs0 := hs 0 (by omega)
  have hs1 := hs 1 (by omega)
  have hs2 := hs 2 (by omega)
  have hs3 := hs 3 (by omega)
  change jetCoeff (fun t => q t*q t) 0 = _ at hs0
  norm_num [Finset.sum_range_succ, h0'] at hs0 hs1 hs2 hs3
  have ht (j : ℕ) (hj : j ≤ 3) :=
    jetCoeff_mul (fun t => q t*q t) q (hq.mul hq) hq j hj
  have ht1 := ht 1 (by omega)
  have ht2 := ht 2 (by omega)
  have ht3 := ht 3 (by omega)
  have hp := jetCoeff_pencil Y K
  norm_num [Finset.sum_range_succ, hs0, hs1, hs2, hs3, h0',
    heq, hp.1, hp.2.1, hp.2.2] at ht1 ht2 ht3
  change C 0 = P ∧ _
  refine ⟨h0, ?_, ?_, ?_⟩
  · change P*P*C 1 + P*C 1*P + C 1*P*P = K
    calc _ = P*P*C 1 + (P*C 1 + C 1*P)*P := by noncomm_ring
         _ = K := ht1.symm
  · change P*P*C 2 + P*C 2*P + C 2*P*P = _
    apply eq_neg_iff_add_eq_zero.mpr
    calc _ = P*P*C 2 + (P*C 1 + C 1*P)*C 1 +
        (P*C 2 + C 1*C 1 + C 2*P)*P := by noncomm_ring
         _ = 0 := ht2.symm
  · change P*P*C 3 + P*C 3*P + C 3*P*P = _
    apply eq_neg_iff_add_eq_zero.mpr
    calc _ = P*P*C 3 + (P*C 1 + C 1*P)*C 2 +
        (P*C 2 + C 1*C 1 + C 2*P)*C 1 +
        (P*C 3 + C 1*C 2 + C 2*C 1 + C 3*P)*P := by noncomm_ring
         _ = 0 := ht3.symm


private theorem twoThirds_eq_square {A : Matrix n n ℂ} (hA : A.PosDef) :
    CFC.rpow A (2/3 : ℝ) = CFC.rpow A (1/3 : ℝ) * CFC.rpow A (1/3 : ℝ) := by
  simp only [CFC.rpow_eq_pow]
  rw [show (2/3 : ℝ) = 1/3+1/3 by ring, CFC.rpow_add hA.isUnit]

/-- Smoothness of the actual two-thirds power at an arbitrary positive definite center. -/
theorem contDiffAt_twoThirds {Y K : Matrix n n ℂ} (hY : Y.PosDef) (hK : K.IsHermitian) :
    ContDiffAt ℝ ∞ (fun t : ℝ => CFC.rpow (Y+t • K) (2/3 : ℝ)) 0 := by
  have hq := contDiffAt_cubeRoot hY hK
  apply (hq.mul hq).congr_of_eventuallyEq
  exact (pencil_posDef_near hY hK).mono fun _ ht => twoThirds_eq_square ht

/-- Actual jets of the normalized two-thirds CFC pencil, with multiplication order retained. -/
theorem normalized_twoThirds_jet {Y K : Matrix n n ℂ} (hY : Y.PosDef)
    (hK : K.IsHermitian) (j : ℕ) (hj : j ≤ 3) :
    let P := CFC.rpow Y (1/3 : ℝ)
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹) j =
      P⁻¹ * (∑ a ∈ Finset.range (j+1), C a * C (j-a)) * P⁻¹ := by
  let P := CFC.rpow Y (1/3 : ℝ)
  let q := fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ)
  let f := fun t : ℝ => CFC.rpow (Y+t • K) (2/3 : ℝ)
  have hq : ContDiffAt ℝ ∞ q 0 := contDiffAt_cubeRoot hY hK
  have hf : ContDiffAt ℝ j f 0 := (contDiffAt_twoThirds hY hK).of_le (by simp)
  have he : f =ᶠ[𝓝 0] fun t => q t*q t :=
    (pencil_posDef_near hY hK).mono fun _ ht => twoThirds_eq_square ht
  have hsand : ContDiffAt ℝ j (fun t => P⁻¹ * f t) 0 := by fun_prop
  have hr : iteratedDeriv j (fun t => P⁻¹ * f t * P⁻¹) 0 =
      iteratedDeriv j (fun t => P⁻¹ * f t) 0 * P⁻¹ := by
    simpa only [iteratedDerivWithin_univ] using
      iteratedDerivWithin_mul_const (Set.mem_univ (0 : ℝ)) uniqueDiffOn_univ
        hsand.contDiffWithinAt P⁻¹
  change jetCoeff (fun t => P⁻¹ * f t * P⁻¹) j = _
  rw [jetCoeff, hr, iteratedDeriv_const_mul P⁻¹ hf, he.iteratedDeriv_eq j]
  calc
    _ = P⁻¹ * jetCoeff (fun t => q t*q t) j * P⁻¹ := by
      simp only [jetCoeff, Matrix.smul_mul, Matrix.mul_smul]
    _ = _ := congrArg (fun A : Matrix n n ℂ => P⁻¹ * A * P⁻¹)
      (jetCoeff_mul q q hq hq j hj)


private theorem coordinates_cubeRoot {Y : Matrix n n ℂ} (hY : Y.PosDef) :
    spectralCoordinates hY.isHermitian (CFC.rpow Y (1/3 : ℝ)) =
      Matrix.diagonal (fun i => ((hY.isHermitian.eigenvalues i ^ (1/3 : ℝ) : ℝ) : ℂ)) := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hY.posSemidef.nonneg, hY.isHermitian.cfc_eq]
  simp only [spectralCoordinates, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_symm_apply, Unitary.conjStarAlgAut_apply]
  simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  ext i j
  simp [Function.comp_def, RCLike.ofReal]

private theorem cubicLinear_coordinates_entry (e : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ)
    (P E : Matrix n n ℂ) (p : n → ℝ) (hp : e P = Matrix.diagonal (fun i => (p i : ℂ)))
    (i j : n) :
    e (cubicLinear P E) i j = ((p i ^ 2 + p i*p j + p j ^ 2 : ℝ) : ℂ) * e E i j := by
  change e (P*P*E + P*E*P + E*P*P) i j = _
  simp only [map_add, map_mul, hp, Matrix.add_apply, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

/-- Spectral recurrences of the actual root jets in the fixed eigenbasis of Y.
The diagonal entries p are cube roots of Y's eigenvalues, not a moving eigenbasis. -/
theorem cubeRoot_jet_spectral {Y K : Matrix n n ℂ} (hY : Y.PosDef) (hK : K.IsHermitian) :
    let p := fun i => hY.isHermitian.eigenvalues i ^ (1/3 : ℝ)
    let T := Matrix.diagonal (fun i => (p i : ℂ))
    let e := spectralCoordinates hY.isHermitian
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    let D := fun a => e (C a)
    D 0 = T ∧ ∀ i j,
      0 < p i ^ 2 + p i*p j + p j ^ 2 ∧
      ((p i ^ 2 + p i*p j + p j ^ 2 : ℝ) : ℂ) * D 1 i j = e K i j ∧
      ((p i ^ 2 + p i*p j + p j ^ 2 : ℝ) : ℂ) * D 2 i j =
        -(T*D 1*D 1 + D 1*T*D 1 + D 1*D 1*T) i j ∧
      ((p i ^ 2 + p i*p j + p j ^ 2 : ℝ) : ℂ) * D 3 i j =
        -(T*D 1*D 2 + T*D 2*D 1 + D 1*T*D 2 + D 2*T*D 1 +
          D 1*D 2*T + D 2*D 1*T + D 1*D 1*D 1) i j := by
  let P := CFC.rpow Y (1/3 : ℝ)
  let p := fun i => hY.isHermitian.eigenvalues i ^ (1/3 : ℝ)
  let T := Matrix.diagonal (fun i => (p i : ℂ))
  let e := spectralCoordinates hY.isHermitian
  let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
  let D := fun a => e (C a)
  have hp : e P = T := coordinates_cubeRoot hY
  have hp' : e (CFC.rpow Y (1/3 : ℝ)) = T := hp
  have hc := cubeRoot_jet_recurrences hY hK
  change C 0 = P ∧ _ at hc
  change D 0 = T ∧ _
  refine ⟨(congrArg e hc.1).trans hp, fun i j => ?_⟩
  have hi : 0 < p i := Real.rpow_pos_of_pos (hY.eigenvalues_pos i) _
  have hj : 0 < p j := Real.rpow_pos_of_pos (hY.eigenvalues_pos j) _
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · calc
      _ = e (cubicLinear P (C 1)) i j :=
        (cubicLinear_coordinates_entry e P (C 1) p hp i j).symm
      _ = e K i j := congrArg (fun A => e A i j) hc.2.1
  · have hh := congrArg (fun A => e A i j) hc.2.2.1
    rw [cubicLinear_coordinates_entry e P (C 2) p hp i j] at hh
    simpa only [map_neg, map_add, map_mul, hp', Matrix.neg_apply] using hh
  · have hh := congrArg (fun A => e A i j) hc.2.2.2
    rw [cubicLinear_coordinates_entry e P (C 3) p hp i j] at hh
    simpa only [map_neg, map_add, map_mul, hp', Matrix.neg_apply] using hh

end D5.S3.Quantum.Matrix.RpowPencilTaylor
