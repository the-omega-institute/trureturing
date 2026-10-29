/- GID: D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Integral translation matrices for every positive modulus and actual cusp-space twists. -/

/- The translation construction is classical (Atkin–Li, Proposition 3.1).
This module constructs integral intertwiners and the actual Gamma1 cusp-space operator.
The Gamma0 character-square law and q-expansion coefficient law remain outstanding. -/

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped BigOperators MatrixGroups ModularForm Pointwise

namespace D5.S3.Arith.ModularForms

noncomputable section

/- The two divisibility hypotheses here are discharged in the universal theorem below.
   In particular, the public contact does not assume an integral intertwiner. -/
private theorem integral_translation_matrix
    (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (U V : ℤ)
    (hC : (N : ℤ) ^ 2 ∣ γ 1 0)
    (hUV : (N : ℤ) ∣ γ 1 1 * U - γ 0 0 * V) :
    ∃ M : SL(2, ℤ),
      GeneralLinearGroup.upperRightHom ((U : ℝ) / (N : ℝ)) * mapGL ℝ γ =
        mapGL ℝ M * GeneralLinearGroup.upperRightHom ((V : ℝ) / (N : ℝ)) := by
  obtain ⟨h, hc⟩ := hC
  obtain ⟨t, ht⟩ := hUV
  let A : Matrix (Fin 2) (Fin 2) ℤ :=
    !![γ 0 0 + (N : ℤ) * h * U, γ 0 1 + t - h * U * V;
       (N : ℤ) ^ 2 * h, γ 1 1 - (N : ℤ) * h * V]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hA : A.det = 1 := by
    rw [Matrix.det_fin_two]
    change (γ 0 0 + (N : ℤ) * h * U) * (γ 1 1 - (N : ℤ) * h * V) -
      (γ 0 1 + t - h * U * V) * ((N : ℤ) ^ 2 * h) = 1
    calc
      _ = γ 0 0 * γ 1 1 - γ 0 1 * ((N : ℤ) ^ 2 * h) +
          (N : ℤ) * h * (γ 1 1 * U - γ 0 0 * V - (N : ℤ) * t) := by ring
      _ = 1 := by
        rw [ht, sub_self, mul_zero, add_zero, ← hc]
        exact hdet
  let M : SL(2, ℤ) := ⟨A, hA⟩
  have hcR : (γ 1 0 : ℝ) = (N : ℝ) ^ 2 * (h : ℝ) := by
    exact_mod_cast hc
  have htR : (γ 1 1 : ℝ) * (U : ℝ) - (γ 0 0 : ℝ) * (V : ℝ) =
      (N : ℝ) * (t : ℝ) := by
    exact_mod_cast ht
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  refine ⟨M, ?_⟩
  apply Units.ext
  change
    !![(1 : ℝ), (U : ℝ) / (N : ℝ); 0, 1] *
        (γ.1.map (algebraMap ℤ ℝ)) =
      (A.map (algebraMap ℤ ℝ)) *
        !![(1 : ℝ), (V : ℝ) / (N : ℝ); 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, A, hcR] <;>
    push_cast <;> field_simp [hNR] <;> nlinarith only [htR]

/-- For every positive (possibly composite, possibly one) modulus, the determinant relation
makes the lower-right residue a unit and makes the translated integral matrix exist.
The second lift is the canonical lift of `d²u`, including when `u` is a nonunit. -/
theorem gamma0_translation_intertwining
    (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N ^ 2)) (u : ZMod N) :
    IsUnit (γ 1 1 : ZMod N) ∧
      ((N : ℤ) ∣ γ 1 1 * (u.val : ℤ) -
        γ 0 0 * (((γ 1 1 : ZMod N) ^ 2 * u).val : ℤ)) ∧
      ∃ M : SL(2, ℤ),
        GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)) * mapGL ℝ γ =
          mapGL ℝ M * GeneralLinearGroup.upperRightHom
            ((((γ 1 1 : ZMod N) ^ 2 * u).val : ℝ) / (N : ℝ)) := by
  let v : ZMod N := (γ 1 1 : ZMod N) ^ 2 * u
  have hC : (N : ℤ) ^ 2 ∣ γ 1 0 := by
    simpa only [Nat.cast_pow] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (N ^ 2)).mp
        (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hcN : (γ 1 0 : ZMod N) = 0 := by
    obtain ⟨h, hc⟩ := hC
    rw [hc]
    simp
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hdetN : (γ 0 0 : ZMod N) * (γ 1 1 : ZMod N) -
      (γ 0 1 : ZMod N) * (γ 1 0 : ZMod N) = 1 := by
    have hcast := congrArg (fun x : ℤ => (x : ZMod N)) hdet
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using hcast
  have had : (γ 0 0 : ZMod N) * (γ 1 1 : ZMod N) = 1 := by
    simpa only [hcN, mul_zero, sub_zero] using hdetN
  have hdUnit : IsUnit (γ 1 1 : ZMod N) := by
    refine ⟨⟨(γ 1 1 : ZMod N), (γ 0 0 : ZMod N), ?_, had⟩, rfl⟩
    calc
      (γ 1 1 : ZMod N) * (γ 0 0 : ZMod N) =
          (γ 0 0 : ZMod N) * (γ 1 1 : ZMod N) := mul_comm _ _
      _ = 1 := had
  have hUVzero :
      ((γ 1 1 * (u.val : ℤ) - γ 0 0 * (v.val : ℤ) : ℤ) : ZMod N) = 0 := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    change (γ 1 1 : ZMod N) * u -
      (γ 0 0 : ZMod N) * ((γ 1 1 : ZMod N) ^ 2 * u) = 0
    calc
      _ = (γ 1 1 : ZMod N) * u *
          (1 - (γ 0 0 : ZMod N) * (γ 1 1 : ZMod N)) := by ring
      _ = 0 := by rw [had]; ring
  have hUV : (N : ℤ) ∣ γ 1 1 * (u.val : ℤ) - γ 0 0 * (v.val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hUVzero
  refine ⟨hdUnit, hUV, ?_⟩
  simpa only [Int.cast_natCast] using
    integral_translation_matrix N γ (u.val : ℤ) (v.val : ℤ) hC hUV

/-- The actual real image of `Gamma1 (N²)` lies in the subgroup on which translation
of a level-one form by `upperRightHom (u.val / N)` is invariant. -/
theorem gamma1_le_translation_conjugate
    (N : ℕ) [NeZero N] (u : ZMod N) :
    (CongruenceSubgroup.Gamma1 (N ^ 2) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct
        (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))⁻¹ •
          (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  intro g hg
  change g ∈ (CongruenceSubgroup.Gamma1 (N ^ 2)).map (mapGL ℝ) at hg
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  have hdSq : (γ 1 1 : ZMod (N ^ 2)) = 1 :=
    ((CongruenceSubgroup.Gamma1_mem (N ^ 2) γ).mp hγ).2.1
  have hdSqZero : ((γ 1 1 - 1 : ℤ) : ZMod (N ^ 2)) = 0 := by
    simpa only [Int.cast_sub, Int.cast_one, hdSq, sub_self]
  have hNdiv : (N : ℤ) ∣ ((N ^ 2 : ℕ) : ℤ) := by
    refine ⟨(N : ℤ), ?_⟩
    push_cast
    ring
  have hdDiv : (N : ℤ) ∣ γ 1 1 - 1 :=
    dvd_trans hNdiv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ (N ^ 2)).mp hdSqZero)
  have hdZero : ((γ 1 1 - 1 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hdDiv
  have hdN : (γ 1 1 : ZMod N) = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_one] using hdZero
  obtain ⟨M, hM⟩ :=
    (gamma0_translation_intertwining N γ
      (CongruenceSubgroup.Gamma1_in_Gamma0 (N ^ 2) hγ) u).2.2
  have hMu :
      GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)) * mapGL ℝ γ =
        mapGL ℝ M * GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)) := by
    simpa only [hdN, one_pow, one_mul] using hM
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  refine ⟨M, ?_⟩
  calc
    mapGL ℝ M =
        (mapGL ℝ M * GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) *
          (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))⁻¹ := by
            simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by rw [← hMu]

/- This value computation is consumed by the linearity proof. It also ensures that the
   implemented summands are the requested actual horizontal translations. -/
private theorem upperRight_slash_apply (f : ℍ → ℂ) (k : ℤ) (x : ℝ) (z : ℍ) :
    (f ∣[k] GeneralLinearGroup.upperRightHom x) z = f (x +ᵥ z) := by
  have hT : GeneralLinearGroup.upperRightHom x • z = x +ᵥ z := by
    ext
    simp [UpperHalfPlane.σ, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  rw [ModularForm.slash_apply, hT]
  simp [UpperHalfPlane.σ, UpperHalfPlane.denom, GeneralLinearGroup.val_det_apply]

/- Restrict the existing arbitrary-real-GL translate by the proved inclusion.
   The all-cusp field is transported by IsCusp.mono; no cusp hypothesis is assumed.
   CuspForm.coe_translate is deliberately not used for this nonintegral matrix. -/
private def restrictedTranslation (N : ℕ) [NeZero N] (k : ℤ) (u : ZMod N) :
    CuspForm 𝒮ℒ k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma1 (N ^ 2) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun f :=
    { toFun := CuspForm.translate f
        (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))
      slash_action_eq' γ hγ :=
        (CuspForm.translate f
          (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))).slash_action_eq'
            γ (gamma1_le_translation_conjugate N u hγ)
      holo' := (CuspForm.translate f
        (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))).holo'
      zero_at_cusps' hc := (CuspForm.translate f
        (GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ)))).zero_at_cusps'
          (hc.mono (gamma1_le_translation_conjugate N u)) }
  map_add' f g := by
    ext z
    change ((⇑(f + g)) ∣[k]
        GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) z =
      ((⇑f ∣[k] GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) z) +
      ((⇑g ∣[k] GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) z)
    simp only [upperRight_slash_apply]
    rfl
  map_smul' c f := by
    ext z
    change ((⇑(c • f)) ∣[k]
        GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) z =
      c * ((⇑f ∣[k] GeneralLinearGroup.upperRightHom ((u.val : ℝ) / (N : ℝ))) z)
    simp only [upperRight_slash_apply]
    rfl

/-- The actual Gauss-normalized finite translation sum into `CuspForm (Gamma1 (N²)) k`.
Its definition is meaningful for every Dirichlet character; primitivity and Gauss-sum
nonvanishing are needed for the future coefficient theorem, not for this cusp-space
construction. Pointwise it is
`(gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * ∑ u, χ⁻¹ u * f (u.val / N +ᵥ z)`.
No nebentypus or q-expansion theorem is asserted here. -/
def dirichletTranslationTwist (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℤ) :
    CuspForm 𝒮ℒ k →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma1 (N ^ 2) : Subgroup (GL (Fin 2) ℝ)) k :=
  (gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)))⁻¹ •
    ∑ u : ZMod N, (χ⁻¹ u) • restrictedTranslation N k u

/- The conductor-one case is the normalization anchor for the missing coefficient
   theorem: the unique primitive character and the unique translation both reduce
   to the identity.  Keeping this pointwise statement separate avoids assuming any
   nonvanishing or nebentypus law before the general twist proof. -/
theorem restrictedTranslation_one_zero_apply
    (k : ℤ) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (restrictedTranslation 1 k (0 : ZMod 1) f) z = f z := by
  change (f ∣[k]
      GeneralLinearGroup.upperRightHom ((0 : ℝ) / (1 : ℝ))) z = f z
  rw [upperRight_slash_apply]
  simp

theorem dirichletTranslationTwist_one_apply
    (k : ℤ) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (dirichletTranslationTwist 1 (1 : DirichletCharacter ℂ 1) k f) z = f z := by
  have hstd : (ZMod.stdAddChar (N := 1) : AddChar (ZMod 1) ℂ) = 1 := by
    apply AddMonoidHom.ext
    intro u
    exact Subsingleton.elim _ _
  have htrans (u : ZMod 1) : (restrictedTranslation 1 k u f) z = f z := by
    rw [show u = 0 by exact Subsingleton.elim _ _]
    exact restrictedTranslation_one_zero_apply k f z
  change ((gaussSum ((1 : DirichletCharacter ℂ 1)⁻¹)
      (ZMod.stdAddChar (N := 1)))⁻¹ : ℂ) *
      (∑ u : ZMod 1, ((1 : DirichletCharacter ℂ 1)⁻¹ u) *
        (restrictedTranslation 1 k u f) z) = f z
  rw [inv_one, hstd, gaussSum_one_one]
  simp [htrans]

end

end D5.S3.Arith.ModularForms
