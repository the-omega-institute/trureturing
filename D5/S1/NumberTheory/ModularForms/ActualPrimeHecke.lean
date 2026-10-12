/- GID: D5/S1/NumberTheory/ModularForms/ActualPrimeHecke
   generality: G
   mirror-B: D5/B/S1/NumberTheory/ModularForms/ActualPrimeHecke
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Actual trace-and-translate prime Hecke endomorphism on level-one cusp forms. -/

import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open scoped BigOperators ModularForm MatrixGroups CongruenceSubgroup Pointwise

namespace D5.S1.NumberTheory.ModularForms

noncomputable section

/-- The rational diagonal matrix whose real image is the `p`-isogeny matrix. -/
def primeDiagRat (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(p : ℚ), 0; 0, 1]) (by
      rw [Matrix.det_fin_two]
      norm_num
      exact_mod_cast (Nat.Prime.ne_zero Fact.out))

/-- We use the inverse rational diagonal in order that translation by its real image
has target subgroup `g⁻¹ • 𝒮ℒ`, exactly the subgroup recognized by the arithmetic API. -/
def primeHeckeRat (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  primeDiagRat p

def primeHeckeReal (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (primeHeckeRat p)

abbrev primeHeckeSubgroup (p : ℕ) [Fact p.Prime] :
    Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct (primeHeckeReal p)⁻¹ • (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))

private lemma primeHeckeSubgroup_arithmetic (p : ℕ) [Fact p.Prime] :
    (primeHeckeSubgroup p).IsArithmetic := by
  simpa [primeHeckeSubgroup, primeHeckeReal, primeHeckeRat] using
    (CongruenceSubgroup.isArithmetic_conj_SL2Z (primeDiagRat p)⁻¹)

private lemma primeHeckeReal_det_pos (p : ℕ) [Fact p.Prime] :
    0 < (primeHeckeReal p).det.val := by
  have hp : 0 < p := (show Nat.Prime p from Fact.out).pos
  norm_num [primeHeckeReal, primeHeckeRat, primeDiagRat,
    Matrix.det_fin_two, hp]

private instance primeHeckeSubgroup_isArithmetic (p : ℕ) [Fact p.Prime] :
    (primeHeckeSubgroup p).IsArithmetic := primeHeckeSubgroup_arithmetic p

private instance primeHeckeSubgroup_isFiniteRelIndex (p : ℕ) [Fact p.Prime] :
    (primeHeckeSubgroup p).IsFiniteRelIndex
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.IsArithmetic.isFiniteRelIndexSL (primeHeckeSubgroup p)

private lemma quotientFunc_add
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] (f h : CuspForm 𝒢 k)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    SlashInvariantForm.quotientFunc (f + h) q =
      SlashInvariantForm.quotientFunc f q + SlashInvariantForm.quotientFunc h q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp [SlashInvariantForm.quotientFunc]

private lemma translate_add
    {k : ℤ} (f h : CuspForm 𝒮ℒ k) (g : GL (Fin 2) ℝ) :
    CuspForm.translate (f + h) g =
      CuspForm.translate f g + CuspForm.translate h g := by
  ext z
  change (((⇑f) + (⇑h)) ∣[k] g) z = _
  rw [SlashAction.add_slash]
  rfl

private lemma translate_smul
    {k : ℤ} (c : ℂ) (f : CuspForm 𝒮ℒ k) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) :
    CuspForm.translate (c • f) g =
      c • CuspForm.translate f g := by
  ext z
  change ((c • ⇑f) ∣[k] g) z = c * ((⇑f ∣[k] g) z)
  rw [ModularForm.smul_slash]
  have hg' : 0 < g.1.det := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hg
  simp [σ, hg']

private lemma quotientFunc_smul
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [𝒢.HasDetOne] [ℋ.HasDetOne] (c : ℂ) (f : CuspForm 𝒢 k)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    SlashInvariantForm.quotientFunc (c • f) q =
      c • SlashInvariantForm.quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    change ((c • ⇑f) ∣[k] ((↑r : GL (Fin 2) ℝ)⁻¹)) = _
    rw [ModularForm.smul_slash]
    have hdet := Subgroup.HasDetOne.det_eq (Γ := ℋ) r.property
    simp [σ, hdet]

/-- The actual prime Hecke action is translate by `diag(p,1)` followed by
Mathlib's cusp-preserving finite-index trace.  No coefficient law is assumed. -/
noncomputable def primeHecke (p : ℕ) [Fact p.Prime] (k : ℤ) :
    CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k := by
  letI : (primeHeckeSubgroup p).IsArithmetic := primeHeckeSubgroup_arithmetic p
  letI : (primeHeckeSubgroup p).IsFiniteRelIndex
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.IsArithmetic.isFiniteRelIndexSL (primeHeckeSubgroup p)
  letI : Fintype ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸
      (primeHeckeSubgroup p).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let g := primeHeckeReal p
  let op : CuspForm 𝒮ℒ k → CuspForm 𝒮ℒ k := fun f =>
    CuspForm.trace 𝒮ℒ (CuspForm.translate f g)
  exact
    { toFun := op
      map_add' := by
        intro f h
        ext z
        change
          (∑ q : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ,
            SlashInvariantForm.quotientFunc (CuspForm.translate (f + h) g) q) z =
          (∑ q : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ,
            SlashInvariantForm.quotientFunc (CuspForm.translate f g) q) z +
          (∑ q : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ,
            SlashInvariantForm.quotientFunc (CuspForm.translate h g) q) z
        simp only [Finset.sum_apply]
        rw [translate_add]
        simp_rw [quotientFunc_add]
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext z
        change
          (∑ q : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ,
            SlashInvariantForm.quotientFunc (CuspForm.translate (c • f) g) q) z =
          c • (∑ q : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ,
            SlashInvariantForm.quotientFunc (CuspForm.translate f g) q) z
        simp only [Finset.sum_apply]
        rw [translate_smul _ _ _ (by simpa [g] using primeHeckeReal_det_pos p)]
        simp_rw [quotientFunc_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum] }

/-- Pointwise, the operator is the trace of the actual translated cusp form.
The finite quotient is the one used by `CuspForm.trace`, so holomorphy and
vanishing at every cusp are inherited from the library construction. -/
theorem primeHecke_apply (p : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    primeHecke p k f z =
      (CuspForm.trace 𝒮ℒ (CuspForm.translate f (primeHeckeReal p))) z := by
  rfl

end

end D5.S1.NumberTheory.ModularForms

#print axioms D5.S1.NumberTheory.ModularForms.primeHecke
#print axioms D5.S1.NumberTheory.ModularForms.primeHecke_apply
