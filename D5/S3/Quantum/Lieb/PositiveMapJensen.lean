/- GID: D5/S3/Quantum/Lieb/PositiveMapJensen
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/PositiveMapJensen
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Finite positive unital matrix-map Jensen via spectral effects and rectangular isometric dilation. -/

import D5.S3.Quantum.Lieb.JensenOperatorInequalityIImpIV
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Source candidate; current elaboration, kernel and axiom checks are pending.

The analytic supplier is the existing attributed Physlib transplant by
Kei Tsukamoto, Kento Mori and Hayata Yamasaki, revision
b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. Its license is retained
at docs/reports/inoutbalance/physlib-LICENSE.txt. The finite spectral-effect
Jensen and support-corner arguments are classical; no novelty is claimed.
The rectangular CFC coefficient argument is extracted from the local
rectangularCFCAmbient proof in CanonicalChannelDPI. The public diagonal-CFC
supplier is used directly. Internal contraction and spectral-effect helpers
are consumed on the positive-unital Jensen proof path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open LownerHeinzTheorem JensenOperatorInequality

namespace D5.S3.Quantum.Lieb.PositiveMapJensen

variable {n : Type u} {m : Type v}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Rectangular congruence preserves the finite Loewner order. -/
theorem congruence_mono {A B : Matrix n n ℂ} (hAB : A ≤ B)
    (V : Matrix n m ℂ) : Vᴴ * A * V ≤ Vᴴ * B * V := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same V

/-- Intertwining of Hermitian matrices is preserved by every real spectral
function. Finiteness makes every such function continuous on these spectra. -/
theorem cfc_intertwining (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix n m ℂ)
    (hAV : A * V = V * B) (f : ℝ → ℝ) :
    cfc f A * V = V * cfc f B := by
  classical
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let T : Matrix m m ℂ := hB.eigenvectorUnitary
  let E : Matrix n m ℂ := Uᴴ * V * T
  have hU : Uᴴ * U = 1 := hA.eigenvectorUnitary.2.1
  have hu : U * Uᴴ = 1 := hA.eigenvectorUnitary.2.2
  have hT : Tᴴ * T = 1 := hB.eigenvectorUnitary.2.1
  have ht : T * Tᴴ = 1 := hB.eigenvectorUnitary.2.2
  have hsA : A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using hA.spectral_theorem
  have hsB : B = T * diagonal (fun i => (hB.eigenvalues i : ℂ)) * Tᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, T, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using hB.spectral_theorem
  have coeff : diagonal (fun i => (hA.eigenvalues i : ℂ)) * E =
      E * diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
    calc
      _ = Uᴴ * (A * V) * T := by
        conv_rhs => rw [hsA]
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU,
          Matrix.one_mul]
      _ = Uᴴ * (V * B) * T := by rw [hAV]
      _ = _ := by
        conv_lhs => rw [hsB]
        simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, hT,
          Matrix.one_mul, Matrix.mul_one]
  have fcoeff : diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * E =
      E * diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have eq := congrArg (fun M : Matrix n m ℂ => M i j) coeff
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at eq
    by_cases he : hA.eigenvalues i = hB.eigenvalues j
    · rw [he, mul_comm]
    · have hz : E i j = 0 := by
        have hn : (hA.eigenvalues i : ℂ) ≠ (hB.eigenvalues j : ℂ) := by
          exact_mod_cast he
        have heq : ((hA.eigenvalues i : ℂ) - (hB.eigenvalues j : ℂ)) * E i j = 0 := by
          linear_combination eq
        exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hn)
      simp only [hz, mul_zero, zero_mul]
  have reconstruct : U * E * Tᴴ = V := by
    simp only [E, Matrix.mul_assoc, ← Matrix.mul_assoc U Uᴴ, hu,
      Matrix.one_mul, ← Matrix.mul_assoc T Tᴴ, ht, Matrix.mul_one]
  rw [hA.cfc_eq, hB.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  change (U * diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ) * V =
    V * (T * diagonal (fun j => (f (hB.eigenvalues j) : ℂ)) * Tᴴ)
  conv_lhs => rw [← reconstruct]
  conv_rhs => rw [← reconstruct]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul,
    ← Matrix.mul_assoc Tᴴ T, hT, Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc _ E, fcoeff]
  simp only [Matrix.mul_assoc]

private lemma transport_cfc [Nonempty n] (f : ℝ → ℝ)
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (cfc f A) =
      cfc f ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) A) := by
  exact StarAlgHomClass.map_cfc (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) f A
    (A.finite_real_spectrum.continuousOn f)
    (StarAlgEquiv.isometry (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))).continuous
    hA (hA.isSelfAdjoint.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)))

end D5.S3.Quantum.Lieb.PositiveMapJensen

namespace D5.S3.Quantum.Lieb.PositiveMapJensen

-- Both matrix carriers below live in Type u. The supplier is uniform over all
-- Hilbert spaces in that same universe, including the sum and product carriers.
variable {n m k : Type u}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype k] [DecidableEq k]

/-- Matrix endomorphism contraction Jensen, transported from the existing
all-Hilbert supplier. This is the only call to its analytic proof. -/
private theorem contraction_jensen [Nonempty n] {f : ℝ → ℝ}
    (hf : CondIciAll.{u} f) (A X : Matrix n n ℂ) (hA : A.PosSemidef)
    (hX : Xᴴ * X ≤ 1) :
    cfc f (Xᴴ * A * X) ≤ Xᴴ * cfc f A * X := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have heStar (Z : Matrix n n ℂ) : e Zᴴ = star (e Z) := map_star e Z
  have hAe : 0 ≤ e A := map_nonneg e hA.nonneg
  have hXe : star (e X) * e X ≤ 1 := by
    have h := map_nonneg e (sub_nonneg.mpr hX)
    apply sub_nonneg.mp
    simpa only [map_sub, map_one, map_mul, heStar] using h
  have hnormSq : ‖star (e X) * e X‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg (e X))).2 hXe
  have hnorm : ‖e X‖ ≤ 1 := by
    have hsq : ‖e X‖ * ‖e X‖ ≤ 1 := by
      simpa only [CStarRing.norm_star_mul_self] using hnormSq
    nlinarith [norm_nonneg (e X)]
  have hspec : spectrum ℝ (e A) ⊆ Set.Ici (0 : ℝ) :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (e A)
      (ha := IsSelfAdjoint.of_nonneg hAe)).1 hAe
  have h := theorem_2_5_2_i_ici_all_imp_iv (ℋ := EuclideanSpace ℂ n) hf
    (IsSelfAdjoint.of_nonneg hAe) hspec hnorm
  have hAX : (Xᴴ * A * X).IsHermitian :=
    (hA.conjTranspose_mul_mul_same X).isHermitian
  have hcA := transport_cfc f A hA.isHermitian
  have hcAX := transport_cfc f (Xᴴ * A * X) hAX
  have h' : e (cfc f (Xᴴ * A * X)) ≤ e (Xᴴ * cfc f A * X) := by
    calc
      _ = cfcR f (star (e X) * e A * e X) := by
        change e (cfc f (Xᴴ * A * X)) = cfc f (e (Xᴴ * A * X)) at hcAX
        simpa only [map_mul, heStar] using hcAX
      _ ≤ star (e X) * cfcR f (e A) * e X := h
      _ = e (Xᴴ * cfc f A * X) := by
        rw [map_mul, map_mul, heStar]
        change star (e X) * cfc f (e A) * e X = star (e X) * e (cfc f A) * e X
        rw [hcA]
  have hback := map_nonneg e.symm (sub_nonneg.mpr h')
  simpa only [map_sub, StarAlgEquiv.symm_apply_apply, sub_nonneg] using hback

/-- Rectangular isometric Jensen, obtained from the endomorphism contraction
theorem by an explicit square dilation on n ⊕ m. -/
private theorem isometry_jensen [Nonempty m] {f : ℝ → ℝ}
    (hf : CondIciAll.{u} f) (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    cfc f (Vᴴ * A * V) ≤ Vᴴ * cfc f A * V := by
  classical
  let L : Matrix (n ⊕ m) n ℂ := Matrix.fromRows (1 : Matrix n n ℂ) 0
  let J : Matrix (n ⊕ m) m ℂ := Matrix.fromRows 0 (1 : Matrix m m ℂ)
  let T : Matrix (n ⊕ m) (n ⊕ m) ℂ := Matrix.fromBlocks A 0 0 0
  let W : Matrix (n ⊕ m) (n ⊕ m) ℂ := Matrix.fromBlocks 0 V 0 0
  let C : Matrix m m ℂ := Vᴴ * A * V
  let D : Matrix (n ⊕ m) (n ⊕ m) ℂ := Wᴴ * T * W
  have hLL : Lᴴ * L = 1 := by
    simp only [L, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_zero, add_zero]
  have hJJ : Jᴴ * J = 1 := by
    simp only [J, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.fromCols_mul_fromRows, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have hLAL : L * A * Lᴴ = T := by
    change Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix m n ℂ) * A *
      (Matrix.fromRows (1 : Matrix n n ℂ) (0 : Matrix m n ℂ))ᴴ = T
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    simp only [T, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero]
  have hT : T.PosSemidef := hLAL ▸ hA.mul_mul_conjTranspose_same L
  have hWW : Wᴴ * W = Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 1 := by
    simp only [W, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, hV]
  have hDiff : 1 - Wᴴ * W = L * Lᴴ := by
    rw [hWW]
    simp only [L, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.fromRows_mul_fromCols, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hW : Wᴴ * W ≤ 1 := by
    apply sub_nonneg.mp
    rw [hDiff]
    exact (Matrix.posSemidef_self_mul_conjTranspose L).nonneg
  have hD : D.PosSemidef := hT.conjTranspose_mul_mul_same W
  have hC : C.PosSemidef := hA.conjTranspose_mul_mul_same V
  have hDblock : D = Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 C := by
    simp only [D, W, T, C, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  have hTL : T * L = L * A := by
    simp only [T, L, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add]
  have hDJ : D * J = J * C := by
    rw [hDblock]
    simp only [J, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add]
  have hWJ : W * J = L * V := by
    simp only [W, J, L, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add]
  have hJW : Jᴴ * Wᴴ = Vᴴ * Lᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hWJ
  have hTf : Lᴴ * cfc f T * L = cfc f A := by
    have h := cfc_intertwining T A hT.isHermitian hA.isHermitian L hTL f
    have h' := congrArg (fun M : Matrix (n ⊕ m) n ℂ => Lᴴ * M) h
    simpa only [← Matrix.mul_assoc, hLL, Matrix.one_mul] using h'
  have hDf : Jᴴ * cfc f D * J = cfc f C := by
    have h := cfc_intertwining D C hD.isHermitian hC.isHermitian J hDJ f
    have h' := congrArg (fun M : Matrix (n ⊕ m) m ℂ => Jᴴ * M) h
    simpa only [← Matrix.mul_assoc, hJJ, Matrix.one_mul] using h'
  have hRight : Jᴴ * (Wᴴ * cfc f T * W) * J = Vᴴ * cfc f A * V := by
    calc
      _ = (Jᴴ * Wᴴ) * cfc f T * (W * J) := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * Lᴴ) * cfc f T * (L * V) := by rw [hJW, hWJ]
      _ = Vᴴ * (Lᴴ * cfc f T * L) * V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTf]
  have hj := congruence_mono (contraction_jensen hf T W hT hW) J
  change Jᴴ * cfc f D * J ≤ Jᴴ * (Wᴴ * cfc f T * W) * J at hj
  rw [hDf, hRight] at hj
  exact hj

private def stack (S : k → Matrix m m ℂ) : Matrix (k × m) m ℂ :=
  fun i j => S i.1 i.2 j

private lemma stack_weighted_gram (S : k → Matrix m m ℂ) (a : k → ℂ) :
    (stack S)ᴴ * diagonal (fun i : k × m => a i.1) * stack S =
      ∑ i, a i • ((S i)ᴴ * S i) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply,
    stack, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Finite positive effects summing to the identity satisfy operator Jensen.
The proof constructs the dilation; no complete positivity is supplied. -/
private theorem finite_effects_jensen [Nonempty m] {f : ℝ → ℝ}
    (hf : CondIciAll.{u} f) (weights : k → ℝ) (hweights : ∀ i, 0 ≤ weights i)
    (F : k → Matrix m m ℂ) (hF : ∀ i, (F i).PosSemidef)
    (hFsum : ∑ i, F i = 1) :
    cfc f (∑ i, (weights i : ℂ) • F i) ≤ ∑ i, (f (weights i) : ℂ) • F i := by
  let S : k → Matrix m m ℂ := fun i => CFC.sqrt (F i)
  let V := stack S
  let T : Matrix (k × m) (k × m) ℂ := diagonal (fun i => (weights i.1 : ℂ))
  have hSS (i : k) : (S i)ᴴ * S i = F i := by
    have hs : (S i)ᴴ = S i := (CFC.sqrt_nonneg (F i)).posSemidef.isHermitian.eq
    rw [hs]
    exact CFC.sqrt_mul_sqrt_self (F i) (hF i).nonneg
  have hV : Vᴴ * V = 1 := by
    have h := stack_weighted_gram S (fun _ => (1 : ℂ))
    simpa only [V, diagonal_one, Matrix.mul_one, one_smul, hSS, hFsum] using h
  have hT : T.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (weights i.1 : ℂ)
    exact_mod_cast hweights i.1
  have hInput : Vᴴ * T * V = ∑ i, (weights i : ℂ) • F i := by
    simpa only [V, T, hSS] using stack_weighted_gram S (fun i => (weights i : ℂ))
  have hOutput : Vᴴ * cfc f T * V = ∑ i, (f (weights i) : ℂ) • F i := by
    rw [show cfc f T = diagonal (fun i : k × m => (f (weights i.1) : ℂ)) from
      D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
        f (fun i : k × m => weights i.1)]
    simpa only [V, hSS] using stack_weighted_gram S (fun i => (f (weights i) : ℂ))
  simpa only [hInput, hOutput] using isometry_jensen hf T hT V hV

private def spectralEffect {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * single i i 1 *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

private lemma spectralEffect_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    (spectralEffect hA i).PosSemidef := by
  have hsingle : (single i i (1 : ℂ)).PosSemidef := by
    rw [← Matrix.diagonal_single]
    apply Matrix.PosSemidef.diagonal
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  exact hsingle.mul_mul_conjTranspose_same _

private lemma spectralEffect_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ i, spectralEffect hA i = 1 := by
  simp only [spectralEffect, ← Matrix.mul_sum, ← Matrix.sum_mul,
    Matrix.sum_single_one, Matrix.mul_one]
  exact hA.eigenvectorUnitary.2.2

private lemma spectralEffect_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f A = ∑ i, (f (hA.eigenvalues i) : ℂ) • spectralEffect hA i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  change (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = _
  symm
  calc
    _ = ∑ i, ((hA.eigenvectorUnitary : Matrix n n ℂ) *
        ((f (hA.eigenvalues i) : ℂ) • single i i (1 : ℂ))) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [spectralEffect, Matrix.smul_mul, Matrix.mul_smul]
    _ = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        (∑ i, (f (hA.eigenvalues i) : ℂ) • single i i (1 : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = _ := by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one,
        Matrix.sum_single_eq_diagonal]

private theorem positive_unital_jensen_nonpos_zero [Nonempty n] [Nonempty m]
    {f : ℝ → ℝ} (hf : CondIciAll.{u} f)
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    cfc f (Φ A) ≤ Φ (cfc f A) := by
  let E := spectralEffect hA.isHermitian
  let F : n → Matrix m m ℂ := fun i => Φ (E i)
  have hF (i : n) : (F i).PosSemidef :=
    (map_nonneg Φ (spectralEffect_nonneg hA.isHermitian i).nonneg).posSemidef
  have hFsum : ∑ i, F i = 1 := by
    simp only [F, ← map_sum, E, spectralEffect_sum, hΦ]
  have hAres : A = ∑ i, (hA.isHermitian.eigenvalues i : ℂ) • E i := by
    simpa only [cfc_id' ℝ A hA.isHermitian.isSelfAdjoint] using
      spectralEffect_cfc hA.isHermitian (fun x => x)
  have hInput : Φ A = ∑ i, (hA.isHermitian.eigenvalues i : ℂ) • F i := by
    conv_lhs => rw [hAres]
    simp only [map_sum, map_smul, F]
  have hOutput : Φ (cfc f A) = ∑ i, (f (hA.isHermitian.eigenvalues i) : ℂ) • F i := by
    rw [spectralEffect_cfc hA.isHermitian f]
    simp only [map_sum, map_smul, F, E]
  rw [hInput, hOutput]
  exact finite_effects_jensen hf hA.isHermitian.eigenvalues hA.eigenvalues_nonneg F hF hFsum

private lemma shifted_cond {f : ℝ → ℝ}
    (hconv : OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) :
    CondIciAll.{u} (fun x => f x - f 0) := by
  refine ⟨?_, hcont.sub continuousOn_const, by simp⟩
  intro K _ _ _ _
  intro A B t hA hB ht0 ht1 hAs hBs
  have hA0 : (0 : L K) ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 hAs
  have hB0 : (0 : L K) ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 hBs
  have hM0 : (0 : L K) ≤ (1 - t) • A + t • B :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hA0) (smul_nonneg ht0 hB0)
  have hc (T : L K) (hT : 0 ≤ T) :
      cfc (fun x => f x - f 0) T = cfc f T - f 0 • (1 : L K) := by
    have hspec : spectrum ℝ T ⊆ Set.Ici (0 : ℝ) :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) T
        (ha := IsSelfAdjoint.of_nonneg hT)).1 hT
    rw [cfc_sub f (fun _ => f 0) T (hcont.mono hspec) continuousOn_const,
      cfc_const (f 0) T (IsSelfAdjoint.of_nonneg hT), Algebra.algebraMap_eq_smul_one]
  have h := hconv (K := K) hA hB ht0 ht1 hAs hBs
  change cfc (fun x => f x - f 0) ((1 - t) • A + t • B) ≤
    (1 - t) • cfc (fun x => f x - f 0) A +
      t • cfc (fun x => f x - f 0) B
  rw [hc _ hM0, hc _ hA0, hc _ hB0]
  have hsc : (1 - t) • (f 0 • (1 : L K)) + t • (f 0 • (1 : L K)) =
      f 0 • (1 : L K) := by
    rw [← add_smul]
    simp
  have hright : (1 - t) • (cfc f A - f 0 • (1 : L K)) +
      t • (cfc f B - f 0 • (1 : L K)) =
      ((1 - t) • cfc f A + t • cfc f B) - f 0 • (1 : L K) := by
    simp only [smul_sub]
    calc
      _ = ((1 - t) • cfc f A + t • cfc f B) -
          ((1 - t) • (f 0 • (1 : L K)) + t • (f 0 • (1 : L K))) := by abel
      _ = _ := by rw [hsc]
  rw [hright]
  exact sub_le_sub_right h _

/-- Jensen for arbitrary complex-linear positive unital maps between finite
matrix algebras. Neither complete positivity nor a sign condition on f(0) is
assumed. Empty carriers are included. -/
theorem positive_unital_jensen {f : ℝ → ℝ}
    (hconv : OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    cfc f (Φ A) ≤ Φ (cfc f A) := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hm =>
    letI := hm
    exact le_of_eq (Subsingleton.elim _ _)
  | inr hm =>
    letI := hm
    cases isEmpty_or_nonempty n with
    | inl hn =>
      letI := hn
      have hone : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
      have hbad : (1 : Matrix m m ℂ) = 0 := by
        rw [← hΦ, hone, map_zero]
      exact (one_ne_zero hbad).elim
    | inr hn =>
      letI := hn
      have hΦA : (Φ A).PosSemidef := (map_nonneg Φ hA.nonneg).posSemidef
      have h := positive_unital_jensen_nonpos_zero (shifted_cond (f := f) (@hconv) hcont) Φ hΦ A hA
      have hc (T : Matrix n n ℂ) (hT : T.PosSemidef) :
          cfc (fun x => f x - f 0) T = cfc f T - f 0 • (1 : Matrix n n ℂ) := by
        rw [cfc_sub f (fun _ => f 0) T (T.finite_real_spectrum.continuousOn f)
          continuousOn_const, cfc_const (f 0) T hT.isHermitian.isSelfAdjoint,
          Algebra.algebraMap_eq_smul_one]
      have hcOut : cfc (fun x => f x - f 0) (Φ A) =
          cfc f (Φ A) - f 0 • (1 : Matrix m m ℂ) := by
        rw [cfc_sub f (fun _ => f 0) (Φ A) ((Φ A).finite_real_spectrum.continuousOn f)
          continuousOn_const, cfc_const (f 0) (Φ A) hΦA.isHermitian.isSelfAdjoint,
          Algebra.algebraMap_eq_smul_one]
      rw [hcOut, hc A hA, map_sub, PositiveLinearMap.map_smul_of_tower, hΦ] at h
      exact (sub_le_sub_iff_right (f 0 • (1 : Matrix m m ℂ))).mp h

end D5.S3.Quantum.Lieb.PositiveMapJensen
