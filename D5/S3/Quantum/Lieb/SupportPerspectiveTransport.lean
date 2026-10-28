/- GID: D5/S3/Quantum/Lieb/SupportPerspectiveTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/SupportPerspectiveTransport
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Signed support transport and fixed-ambient positive unitalization for the supported spectral perspective. -/



import D5.S3.Quantum.Lieb.PositiveMapJensen
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery

/-!
Source candidate; current elaboration, kernel and axiom checks are pending.

The analytic supplier is the existing attributed Physlib transplant by
Kei Tsukamoto, Kento Mori and Hayata Yamasaki, revision
b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. Its license is retained
at docs/reports/inoutbalance/physlib-LICENSE.txt. The finite spectral-effect
Jensen and support-corner arguments are classical; no novelty is claimed.
The existing spectralSupport and spectralInverseSqrt are used unchanged.
Singleton square-root Kraus normalization supplies the support identities.
Signed support and CFC localization feed SupportPerspectiveTransformer;
coordinate compensation unitalizes the map on the full output carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Lieb.PositiveMapJensen
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

namespace D5.S3.Quantum.Lieb.SupportPerspectiveTransport

variable {n : Type u} {m : Type v}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Specialize the existing Kraus support/normalization suppliers to the single
Kraus matrix sqrt Q. No second support or pseudoinverse definition is made. -/
theorem spectral_sqrt_normalization (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    let R := CFC.sqrt Q
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    Rᴴ = R ∧ Wᴴ = W ∧ Pᴴ = P ∧ P * P = P ∧
      P * R = R ∧ R * P = R ∧ P * Q = Q ∧ W * Q * W = P := by
  classical
  dsimp only
  let R := CFC.sqrt Q
  let W := spectralInverseSqrt Q
  let P := spectralSupport Q
  have hR : Rᴴ = R := (CFC.sqrt_nonneg Q).posSemidef.isHermitian.eq
  have hRR : R * R = Q := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  let E : Unit → Matrix n n ℂ := fun _ => R
  have hGram : (∑ a : Unit, E a * (E a)ᴴ) = Q := by
    simpa only [E, Fintype.sum_unique, hR] using hRR
  have hPR : P * R = R := by
    have h := spectral_support_on_kraus E ()
    simpa only [hGram, E, P] using h
  obtain ⟨hW, hP, hPP, hK⟩ := spectral_decoder_normalization E
  rw [hGram] at hW hP hPP hK
  change Wᴴ = W at hW
  change Pᴴ = P at hP
  change P * P = P at hPP
  have hRP : R * P = R := by
    simpa only [Matrix.conjTranspose_mul, hP, hR] using
      congrArg Matrix.conjTranspose hPR
  have hPQ : P * Q = Q := by
    rw [← hRR, ← Matrix.mul_assoc, hPR]
  have hWQW : W * Q * W = P := by
    have hK' : ((Rᴴ * W)ᴴ * (Rᴴ * W)) = P := by
      simpa only [E, Fintype.sum_unique] using hK
    simpa only [Matrix.conjTranspose_mul, hR, hW, Matrix.mul_assoc,
      ← Matrix.mul_assoc R R, hRR] using hK'
  exact ⟨hR, hW, hP, hPP, hPR, hRP, hPQ, hWQW⟩

/-- The orthogonal complement of a Hermitian projection is nonnegative. -/
private theorem projection_complement_nonneg (P : Matrix n n ℂ)
    (hP : Pᴴ = P) (hPP : P * P = P) : 0 ≤ 1 - P := by
  have hGram : (1 - P)ᴴ * (1 - P) = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  rw [← hGram]
  exact (Matrix.posSemidef_conjTranspose_mul_self (1 - P)).nonneg

/-- Positivity and domination force support, without assuming complete
positivity of any map. The scalar need not be strictly positive. -/
private theorem support_of_nonneg_le_smul (C D P : Matrix n n ℂ)
    (hP : Pᴴ = P) (hPC : P * C = C) (hD : D.PosSemidef)
    (r : ℝ) (hDC : D ≤ r • C) : P * D = D ∧ D * P = D := by
  let H : Matrix n n ℂ := 1 - P
  let S := CFC.sqrt D
  have hH : Hᴴ = H := by
    simp only [H, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]
  have hHC : H * C = 0 := by
    simp only [H, Matrix.sub_mul, Matrix.one_mul, hPC, sub_self]
  have hHDH : H * D * H = 0 := by
    have hLo : 0 ≤ H * D * H := by
      simpa only [hH] using (hD.conjTranspose_mul_mul_same H).nonneg
    have hHi := congruence_mono hDC H
    have hHi' : H * D * H ≤ 0 := by
      simpa only [hH, Matrix.mul_smul, Matrix.smul_mul, hHC,
        Matrix.zero_mul, smul_zero] using hHi
    exact le_antisymm hHi' hLo
  have hS : Sᴴ = S := (CFC.sqrt_nonneg D).posSemidef.isHermitian.eq
  have hSS : S * S = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  have hSH : S * H = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    calc
      (S * H)ᴴ * (S * H) = H * (S * S) * H := by
        simp only [Matrix.conjTranspose_mul, hH, hS, Matrix.mul_assoc]
      _ = 0 := by rw [hSS, hHDH]
  have hDH : D * H = 0 := by
    rw [← hSS, Matrix.mul_assoc, hSH, Matrix.mul_zero]
  have hDP : D * P = D := by
    have hz : D - D * P = 0 := by
      simpa only [H, Matrix.mul_sub, Matrix.mul_one] using hDH
    exact (sub_eq_zero.mp hz).symm
  have hPD : P * D = D := by
    simpa only [Matrix.conjTranspose_mul, hP, hD.isHermitian.eq] using
      congrArg Matrix.conjTranspose hDP
  exact ⟨hPD, hDP⟩

/-- Two-sided Loewner bounds force support even when the middle matrix is
signed. In particular this covers f(X) when f has negative values. -/
private theorem support_of_two_sided_bounds (C H P : Matrix n n ℂ)
    (hC : C.PosSemidef) (hP : Pᴴ = P) (hPC : P * C = C)
    (r : ℝ) (hLo : -(r • C) ≤ H) (hHi : H ≤ r • C) :
    P * H = H ∧ H * P = H := by
  have hD : (r • C + H).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    simpa only [sub_neg_eq_add, add_comm] using sub_nonneg.mpr hLo
  have hDC : r • C + H ≤ (2 * r) • C := by
    have hs : r • C + r • C = (2 * r) • C := by
      rw [← add_smul]
      congr 1
      ring
    calc
      _ ≤ r • C + r • C := add_le_add le_rfl hHi
      _ = _ := hs
  obtain ⟨hPD, hDP⟩ := support_of_nonneg_le_smul C (r • C + H) P hP hPC hD
    (2 * r) hDC
  have hCP : C * P = C := by
    simpa only [Matrix.conjTranspose_mul, hP, hC.isHermitian.eq] using
      congrArg Matrix.conjTranspose hPC
  constructor
  · have h : r • C + P * H = r • C + H := by
      simpa only [Matrix.mul_add, Matrix.mul_smul, hPC] using hPD
    exact add_left_cancel h
  · have h : r • C + H * P = r • C + H := by
      simpa only [Matrix.add_mul, Matrix.smul_mul, hCP] using hDP
    exact add_left_cancel h

/-- A positive map sends every signed Hermitian B-sandwich into the support of
its image of B. This is the support step that a CP/Kraus argument would obscure. -/
theorem positive_map_sandwich_support
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (Z : Matrix n n ℂ) (hZ : Z.IsHermitian) :
    let S := Φ (CFC.sqrt B * Z * CFC.sqrt B)
    let P := spectralSupport (Φ B)
    P * S = S ∧ S * P = S := by
  let R := CFC.sqrt B
  let C := Φ B
  let S := Φ (R * Z * R)
  let P := spectralSupport C
  have hC : C.PosSemidef := (map_nonneg Φ hB.nonneg).posSemidef
  obtain ⟨hR, -, -, -, -, -, -, -⟩ := spectral_sqrt_normalization B hB
  change Rᴴ = R at hR
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  obtain ⟨-, -, hP, -, -, -, hPC, -⟩ := spectral_sqrt_normalization C hC
  change Pᴴ = P at hP
  change P * C = C at hPC
  have hZHi : Z ≤ ‖Z‖ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hZ.isSelfAdjoint.le_algebraMap_norm_self
  have hZLo : -(‖Z‖ • (1 : Matrix n n ℂ)) ≤ Z := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hZ.isSelfAdjoint.neg_algebraMap_norm_le_self
  have hHi : S ≤ ‖Z‖ • C := by
    have h := Φ.monotone (congruence_mono hZHi R)
    change Φ (Rᴴ * Z * R) ≤ Φ (Rᴴ * (‖Z‖ • (1 : Matrix n n ℂ)) * R) at h
    simpa only [hR, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hRR, PositiveLinearMap.map_smul_of_tower, S, C] using h
  have hLo : -(‖Z‖ • C) ≤ S := by
    have h := Φ.monotone (congruence_mono hZLo R)
    change Φ (Rᴴ * -(‖Z‖ • (1 : Matrix n n ℂ)) * R) ≤ Φ (Rᴴ * Z * R) at h
    simpa only [hR, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hRR, map_neg,
      PositiveLinearMap.map_smul_of_tower, S, C] using h
  exact support_of_two_sided_bounds C S P hC hP hPC ‖Z‖ hLo hHi

/-- CFC is unchanged on a supported sandwich after adding a scalar block on
the orthogonal complement. It follows from the rectangular CFC interface,
not from an assumed block-CFC identity. -/
theorem cfc_supported_localization (P Y R : Matrix n n ℂ)
    (hP : Pᴴ = P) (hPP : P * P = P) (hY : Y.IsHermitian)
    (hPY : P * Y = Y) (hPR : P * R = R) (hRP : R * P = R)
    (t : ℝ) (f : ℝ → ℝ) :
    R * cfc f (Y + t • (1 - P)) * R = R * cfc f Y * R := by
  have hYP : Y * P = Y := by
    simpa only [Matrix.conjTranspose_mul, hP, hY.eq] using
      congrArg Matrix.conjTranspose hPY
  have hZ : (Y + t • (1 - P)).IsHermitian := by
    change star (Y + t • (1 - P)) = Y + t • (1 - P)
    simp only [star_add, star_smul, star_sub, star_one, star_trivial,
      hY.isSelfAdjoint.star_eq, Matrix.star_eq_conjTranspose, hP]
  have hZP : (Y + t • (1 - P)) * P = P * Y := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul,
      Matrix.one_mul, hPP, sub_self, smul_zero, add_zero, hYP, hPY]
  have hcf := cfc_intertwining (Y + t • (1 - P)) Y hZ hY P hZP f
  calc
    _ = R * (cfc f (Y + t • (1 - P)) * P) * R := by
      simp only [Matrix.mul_assoc, hPR]
    _ = R * (P * cfc f Y) * R := by rw [hcf]
    _ = _ := by rw [← Matrix.mul_assoc R P, hRP]

/-- The supported perspective uses the existing spectral inverse square root,
which is zero on the kernel, rather than the ambient algebraic inverse. -/
def supportedPerspective (f : ℝ → ℝ) (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt B * cfc f (spectralInverseSqrt B * A * spectralInverseSqrt B) * CFC.sqrt B

/-- Positive normalization of an arbitrary positive map, on the fixed ambient
carriers. Its unit is the output support projection. -/
def normalizedPositiveMap
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun Z => spectralInverseSqrt (Φ B) *
        Φ (CFC.sqrt B * Z * CFC.sqrt B) * spectralInverseSqrt (Φ B)
      map_add' := by
        intro X Y
        simp only [Matrix.mul_add, Matrix.add_mul, map_add]
      map_smul' := by
        intro c Z
        simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply] }
    (by
      intro Z hZ
      change 0 ≤ spectralInverseSqrt (Φ B) *
        Φ (CFC.sqrt B * Z * CFC.sqrt B) * spectralInverseSqrt (Φ B)
      have hR : (CFC.sqrt B)ᴴ = CFC.sqrt B :=
        (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
      have hW : (spectralInverseSqrt (Φ B))ᴴ = spectralInverseSqrt (Φ B) := by
        exact (cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) (Φ B) :
          IsSelfAdjoint (spectralInverseSqrt (Φ B))).star_eq
      have hMid : 0 ≤ Φ (CFC.sqrt B * Z * CFC.sqrt B) := by
        apply map_nonneg Φ
        simpa only [hR] using
          (hZ.posSemidef.conjTranspose_mul_mul_same (CFC.sqrt B)).nonneg
      simpa only [hW] using
        (hMid.posSemidef.conjTranspose_mul_mul_same (spectralInverseSqrt (Φ B))).nonneg)

private theorem normalizedPositiveMap_one
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    normalizedPositiveMap Φ B 1 = spectralSupport (Φ B) := by
  have hC : (Φ B).PosSemidef := (map_nonneg Φ hB.nonneg).posSemidef
  obtain ⟨-, -, -, -, -, -, -, hW⟩ := spectral_sqrt_normalization (Φ B) hC
  change spectralInverseSqrt (Φ B) *
    Φ (CFC.sqrt B * 1 * CFC.sqrt B) * spectralInverseSqrt (Φ B) = _
  rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  exact hW

/-- A concrete positive unital map on the full output algebra. The positive
coordinate state fills only the complement of the output support. It remains
valid when Φ B = 0. -/
def ambientUnitalization
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) (i : n) :
    Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun Z => normalizedPositiveMap Φ B Z +
        Z i i • (1 - spectralSupport (Φ B))
      map_add' := by
        intro X Y
        simp only [map_add, Matrix.add_apply, add_smul]
        abel
      map_smul' := by
        intro c Z
        simp only [map_smul, Matrix.smul_apply, smul_eq_mul, smul_add, smul_smul,
          RingHom.id_apply] }
    (by
      intro Z hZ
      have hC : (Φ B).PosSemidef := (map_nonneg Φ hB.nonneg).posSemidef
      obtain ⟨-, -, hP, hPP, -, -, -, -⟩ := spectral_sqrt_normalization (Φ B) hC
      have hComp := projection_complement_nonneg (spectralSupport (Φ B)) hP hPP
      exact add_nonneg (map_nonneg (normalizedPositiveMap Φ B) hZ)
        ((hComp.posSemidef.smul hZ.posSemidef.diag_nonneg).nonneg))

private theorem ambientUnitalization_one
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) (i : n) :
    ambientUnitalization Φ B hB i 1 = 1 := by
  change normalizedPositiveMap Φ B 1 +
    (1 : Matrix n n ℂ) i i • (1 - spectralSupport (Φ B)) = 1
  rw [normalizedPositiveMap_one Φ B hB]
  simp only [Matrix.one_apply_eq, one_smul]
  abel

section Uniform

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Actual Jensen applied to the constructed full-ambient unitalization.
The compensation block is explicit, and no unitality of Φ is required. -/
theorem ambient_unitalized_jensen {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix a a ℂ →ₚ[ℂ] Matrix b b ℂ)
    (B : Matrix a a ℂ) (hB : B.PosSemidef) (i : a)
    (X : Matrix a a ℂ) (hX : X.PosSemidef) :
    cfc f (normalizedPositiveMap Φ B X +
        X i i • (1 - spectralSupport (Φ B))) ≤
      normalizedPositiveMap Φ B (cfc f X) +
        (cfc f X) i i • (1 - spectralSupport (Φ B)) := by
  exact positive_unital_jensen (@hconv) hcont (ambientUnitalization Φ B hB i)
    (ambientUnitalization_one Φ B hB i) X hX

end Uniform

end D5.S3.Quantum.Lieb.SupportPerspectiveTransport
