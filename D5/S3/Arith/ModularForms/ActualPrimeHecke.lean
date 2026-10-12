/- GID: D5/S3/Arith/ModularForms/ActualPrimeHecke
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/ActualPrimeHecke
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: Actual prime Hecke trace, complete finite representatives and analytic coefficients. -/

import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open scoped BigOperators ModularForm MatrixGroups CongruenceSubgroup Pointwise

namespace D5.S3.Arith.ModularForms

noncomputable section

/-- The rational diagonal matrix whose real image is the `p`-isogeny matrix. -/
def primeDiagRat (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(p : ℚ), 0; 0, 1]) (by
      rw [Matrix.det_fin_two]
      norm_num
      exact_mod_cast (Nat.Prime.ne_zero Fact.out))

/-- The same rational diagonal used in the classical prime Hecke correspondence; its
real image translates level-one forms and has target subgroup `g⁻¹ • 𝒮ℒ`. -/
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

private lemma primeHeckeReal_coe (p : ℕ) [Fact p.Prime] :
    (primeHeckeReal p : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeHeckeReal, primeHeckeRat, primeDiagRat,
      Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private lemma primeHeckeReal_10 (p : ℕ) [Fact p.Prime] :
    primeHeckeReal p 1 0 = (0 : ℝ) := by
  simpa using congrFun₂ (primeHeckeReal_coe p) 1 0

private lemma primeHeckeReal_11 (p : ℕ) [Fact p.Prime] :
    primeHeckeReal p 1 1 = (1 : ℝ) := by
  simpa using congrFun₂ (primeHeckeReal_coe p) 1 1

private lemma primeHecke_diag_apply (p : ℕ) [Fact p.Prime] (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    ((f : ℍ → ℂ) ∣[k] primeHeckeReal p) z =
      (p : ℂ) ^ (k - 1) * f (primeHeckeReal p • z) := by
  rw [ModularForm.slash_apply]
  simp [UpperHalfPlane.denom, primeHeckeReal_10, primeHeckeReal_11]
  have hdet : (primeHeckeReal p : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
    rw [primeHeckeReal_coe]
    simp [Matrix.det_fin_two]
  have hdet' : (primeHeckeReal p).det.val = (p : ℝ) := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hdet
  rw [hdet]
  simp only [σ]
  rw [hdet']
  simp [show (0 : ℝ) < p by exact_mod_cast (show 0 < p from (Fact.out : Nat.Prime p).pos)]
  ring

/-- The upper-triangular representative of the non-infinite cosets. -/
def primeHeckeUpper (p : ℕ) [Fact p.Prime] (a : ℤ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(1 : ℝ), (a : ℝ); 0, (p : ℝ)]) (by
      rw [Matrix.det_fin_two]
      norm_num
      exact_mod_cast (Nat.Prime.ne_zero Fact.out))

private lemma primeHecke_upper_matrix (p : ℕ) [Fact p.Prime] (a : ℤ) :
    Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * primeHeckeUpper p a =
      primeHeckeReal p *
        Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ a) := by
  apply Units.ext
  change
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S : Matrix (Fin 2) (Fin 2) ℝ) *
        (primeHeckeUpper p a : Matrix (Fin 2) (Fin 2) ℝ) =
      (primeHeckeReal p : Matrix (Fin 2) (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ a) :
          Matrix (Fin 2) (Fin 2) ℝ)
  rw [primeHeckeReal_coe]
  have hST :
      (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ a) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 1, (a : ℝ)] := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    change
      ((((ModularGroup.S * ModularGroup.T ^ a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom ℝ))) = _
    rw [show ((ModularGroup.S * ModularGroup.T ^ a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) *
        ((ModularGroup.T ^ a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) by rfl]
    rw [ModularGroup.coe_T_zpow]
    simp only [Matrix.map_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hST]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeHeckeUpper, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual upper-half-plane point `(z+a)/p`, with its positivity proof retained. -/
def primeHeckeUpperPoint (p : ℕ) [Fact p.Prime] (a : ℤ) (z : ℍ) : ℍ :=
  ⟨((z : ℂ) + (a : ℂ)) / (p : ℂ), by
    have hp : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p from (Fact.out : Nat.Prime p).pos)
    simp [Complex.div_im, hp, z.im_pos]
  ⟩

private lemma primeHeckeUpper_coe (p : ℕ) [Fact p.Prime] (a : ℤ) :
    (primeHeckeUpper p a : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (a : ℝ); 0, (p : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeHeckeUpper]

private lemma primeHecke_upper_apply (p : ℕ) [Fact p.Prime] (a : ℤ)
    (k : ℤ) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    ((f : ℍ → ℂ) ∣[k] primeHeckeUpper p a) z =
      (p : ℂ)⁻¹ * f (primeHeckeUpperPoint p a z) := by
  rw [ModularForm.slash_apply]
  have hdet : (primeHeckeUpper p a : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
    rw [primeHeckeUpper_coe]
    simp [Matrix.det_fin_two]
  have hdet' : (primeHeckeUpper p a).det.val = (p : ℝ) := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using hdet
  have hp : (0 : ℝ) < p := by
    exact_mod_cast (show 0 < p from (Fact.out : Nat.Prime p).pos)
  have hpoint : primeHeckeUpper p a • z = primeHeckeUpperPoint p a z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa [hdet'] using hp)]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, primeHeckeUpper_coe,
      primeHeckeUpperPoint, div_eq_mul_inv]
  rw [hpoint]
  simp only [σ]
  rw [hdet']
  simp only [if_pos hp]
  have hdenom : UpperHalfPlane.denom (primeHeckeUpper p a) (z : ℂ) = (p : ℂ) := by
    simp [UpperHalfPlane.denom, primeHeckeUpper_coe]
  rw [hdenom]
  simp only [abs_of_pos hp, Complex.ofReal_natCast, ContinuousAlgEquiv.refl_apply]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  calc
    f (primeHeckeUpperPoint p a z) * (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-k) =
        f (primeHeckeUpperPoint p a z) *
          ((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-k)) := by ring
    _ = f (primeHeckeUpperPoint p a z) * (p : ℂ) ^ ((-1 : ℤ)) := by
      rw [← zpow_add₀ hpC]
      congr 2
      omega
    _ = (p : ℂ)⁻¹ * f (primeHeckeUpperPoint p a z) := by
      rw [zpow_neg_one]
      ring

/-- Representatives are inverted because `CuspForm.trace` uses their inverses. -/
def primeCosetRep (p : ℕ) : Fin p ⊕ Unit → SL(2, ℤ)
  | .inl a => (ModularGroup.S * ModularGroup.T ^ (a.val : ℤ))⁻¹
  | .inr _ => 1

private lemma primeCosetRep_inl_coe (p : ℕ) (a : Fin p) :
    (primeCosetRep p (.inl a) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(a.val : ℤ), 1; -1, 0] := by
  simp only [primeCosetRep, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T_zpow]
  norm_num [Matrix.mul_fin_two, Matrix.adjugate_fin_two]

private lemma primeCosetRep_inv_inl_coe (p : ℕ) (a : Fin p) :
    (((primeCosetRep p (.inl a))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, (a.val : ℤ)] := by
  simp only [primeCosetRep, inv_inv, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T_zpow]
  norm_num [Matrix.mul_fin_two]

private lemma primeCosetRep_pair_mem (p : ℕ) [Fact p.Prime] (a b : Fin p) :
    (primeCosetRep p (.inl a))⁻¹ * primeCosetRep p (.inl b) ∈
      CongruenceSubgroup.Gamma0 p ↔ a = b := by
  rw [CongruenceSubgroup.Gamma0_mem]
  change ((((((primeCosetRep p (.inl a))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
    (primeCosetRep p (.inl b) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod p) = 0 ↔ _
  rw [primeCosetRep_inv_inl_coe, primeCosetRep_inl_coe]
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [← sub_eq_add_neg, sub_eq_zero]
  constructor
  · intro h
    apply Fin.ext
    have h' := (ZMod.natCast_eq_natCast_iff' b.val a.val p).mp h
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h'.symm
  · rintro rfl
    rfl

private lemma primeCosetRep_cover (p : ℕ) [Fact p.Prime] (s : SL(2, ℤ)) :
    ∃ i : Fin p ⊕ Unit, (primeCosetRep p i)⁻¹ * s ∈ CongruenceSubgroup.Gamma0 p := by
  by_cases hc : (s 1 0 : ZMod p) = 0
  · exact ⟨.inr (), by simpa [primeCosetRep] using hc⟩
  · let x : ZMod p := -(s 0 0 : ZMod p) / (s 1 0 : ZMod p)
    let a : Fin p := ⟨x.val, ZMod.val_lt x⟩
    refine ⟨.inl a, ?_⟩
    rw [CongruenceSubgroup.Gamma0_mem]
    change ((((((primeCosetRep p (.inl a))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (s : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod p) = 0
    rw [primeCosetRep_inv_inl_coe]
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    change (s 0 0 : ZMod p) + (x.val : ZMod p) * (s 1 0 : ZMod p) = 0
    rw [ZMod.natCast_zmod_val]
    dsimp [x]
    simp [div_mul_cancel₀ _ hc]

private def primeCosetClass (p : ℕ) (i : Fin p ⊕ Unit) :
    SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p := ⟦primeCosetRep p i⟧

private lemma primeCosetClass_bijective (p : ℕ) [Fact p.Prime] :
    Function.Bijective (primeCosetClass p) := by
  constructor
  · intro i j hij
    have hm : (primeCosetRep p i)⁻¹ * primeCosetRep p j ∈
        CongruenceSubgroup.Gamma0 p :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact hij)
    cases i with
    | inl a =>
      cases j with
      | inl b => exact congrArg Sum.inl ((primeCosetRep_pair_mem p a b).mp hm)
      | inr u =>
        exfalso
        rw [show primeCosetRep p (.inr u) = 1 by rfl, mul_one] at hm
        rw [CongruenceSubgroup.Gamma0_mem] at hm
        have he := congrFun₂ (primeCosetRep_inv_inl_coe p a) 1 0
        rw [he] at hm
        norm_num at hm
    | inr u =>
      cases j with
      | inl b =>
        exfalso
        rw [CongruenceSubgroup.Gamma0_mem] at hm
        simp only [primeCosetRep, inv_one, one_mul] at hm
        have he := congrFun₂ (primeCosetRep_inl_coe p b) 1 0
        change ((primeCosetRep p (.inl b) 1 0 : ℤ) : ZMod p) = 0 at hm
        rw [he] at hm
        norm_num at hm
      | inr v => congr
  · intro q
    induction q using Quotient.inductionOn with
    | h s =>
      obtain ⟨i, hi⟩ := primeCosetRep_cover p s
      exact ⟨i, Quotient.sound (QuotientGroup.leftRel_apply.mpr hi)⟩

/-- All the prime-index cosets, including `p = 2`, have exactly these representatives. -/
def primeCosetEquiv (p : ℕ) [Fact p.Prime] :
    (Fin p ⊕ Unit) ≃ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 p) :=
  Equiv.ofBijective (primeCosetClass p) (primeCosetClass_bijective p)

private lemma primeHeckeSubgroup_mem_iff (p : ℕ) [Fact p.Prime] (s : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ s ∈ primeHeckeSubgroup p ↔
      ∃ t : SL(2, ℤ), Matrix.SpecialLinearGroup.mapGL ℝ t * primeHeckeReal p =
        primeHeckeReal p * Matrix.SpecialLinearGroup.mapGL ℝ s := by
  change Matrix.SpecialLinearGroup.mapGL ℝ s ∈
    (ConjAct.toConjAct (primeHeckeReal p))⁻¹ •
      (Matrix.SpecialLinearGroup.mapGL ℝ).range ↔ _
  rw [Subgroup.mem_inv_pointwise_smul_iff]
  simp only [ConjAct.toConjAct_smul, MonoidHom.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (eq_mul_inv_iff_mul_eq).mp ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (eq_mul_inv_iff_mul_eq).mpr ht⟩

/-- The actual conjugate intersection is exactly the lower-left congruence subgroup. -/
theorem primeHeckeSubgroup_mem (p : ℕ) [Fact p.Prime] (s : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ s ∈ primeHeckeSubgroup p ↔
      s ∈ CongruenceSubgroup.Gamma0 p := by
  rw [primeHeckeSubgroup_mem_iff, CongruenceSubgroup.Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨t, ht⟩
    have he := congrArg (fun x : GL (Fin 2) ℝ => x 1 0) ht
    have he' : (t 1 0 : ℝ) * (p : ℝ) = (s 1 0 : ℝ) := by
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, primeHeckeReal_coe] using he
    have heZ : t 1 0 * (p : ℤ) = s 1 0 := by exact_mod_cast he'
    exact ⟨t 1 0, by simpa [mul_comm] using heZ.symm⟩
  · rintro ⟨m, hm⟩
    let t : SL(2, ℤ) := ⟨!![s 0 0, (p : ℤ) * s 0 1; m, s 1 1], by
      have hs := s.property
      rw [Matrix.det_fin_two] at hs
      norm_num [Matrix.det_fin_two]
      rw [hm] at hs
      nlinarith⟩
    refine ⟨t, ?_⟩
    apply Units.ext
    change (Matrix.SpecialLinearGroup.mapGL ℝ t : Matrix (Fin 2) (Fin 2) ℝ) *
      (primeHeckeReal p : Matrix (Fin 2) (Fin 2) ℝ) =
        (primeHeckeReal p : Matrix (Fin 2) (Fin 2) ℝ) *
          (Matrix.SpecialLinearGroup.mapGL ℝ s : Matrix (Fin 2) (Fin 2) ℝ)
    rw [primeHeckeReal_coe]
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    change ((t : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) *
      !![(p : ℝ), 0; 0, 1] =
        !![(p : ℝ), 0; 0, 1] *
          ((s : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [t, Matrix.mul_apply, Fin.sum_univ_succ, hm] <;> ring

private instance primeHeckeSubgroup_isArithmetic (p : ℕ) [Fact p.Prime] :
    (primeHeckeSubgroup p).IsArithmetic := primeHeckeSubgroup_arithmetic p

private instance primeHeckeSubgroup_isFiniteRelIndex (p : ℕ) [Fact p.Prime] :
    (primeHeckeSubgroup p).IsFiniteRelIndex
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.IsArithmetic.isFiniteRelIndexSL (primeHeckeSubgroup p)

private def primeTraceRep (p : ℕ) (i : Fin p ⊕ Unit) :
    (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p i),
    ⟨primeCosetRep p i, rfl⟩⟩

private def primeTraceClass (p : ℕ) [Fact p.Prime] (i : Fin p ⊕ Unit) :
    (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ :=
  ⟦primeTraceRep p i⟧

private lemma primeTraceClass_bijective (p : ℕ) [Fact p.Prime] :
    Function.Bijective (primeTraceClass p) := by
  constructor
  · intro i j hij
    have hm := QuotientGroup.leftRel_apply.mp (Quotient.exact hij)
    change (Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p i))⁻¹ *
      Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p j) ∈ primeHeckeSubgroup p at hm
    rw [← map_inv, ← map_mul, primeHeckeSubgroup_mem] at hm
    apply (primeCosetEquiv p).injective
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hm)
  · intro q
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨s, hs⟩ := r.property
      obtain ⟨i, hi⟩ := primeCosetRep_cover p s
      refine ⟨i, Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)⟩
      change (Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p i))⁻¹ *
        r.val ∈ primeHeckeSubgroup p
      rw [← hs, ← map_inv, ← map_mul, primeHeckeSubgroup_mem]
      exact hi

/-- The complete finite representative bijection for the actual quotient used by the trace. -/
def primeTraceEquiv (p : ℕ) [Fact p.Prime] :
    (Fin p ⊕ Unit) ≃
      ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ) :=
  Equiv.ofBijective (primeTraceClass p) (primeTraceClass_bijective p)

private lemma quotientFunc_add
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] (f h : CuspForm 𝒢 k)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    SlashInvariantForm.quotientFunc (f + h) q =
      SlashInvariantForm.quotientFunc f q + SlashInvariantForm.quotientFunc h q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp

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

/-- The point `pz` of the upper half-plane. -/
def primeHeckeDiagPoint (p : ℕ) [Fact p.Prime] (z : ℍ) : ℍ :=
  ⟨(p : ℂ) * (z : ℂ), by
    have hp : (0 : ℝ) < p := by
      exact_mod_cast (show 0 < p from (Fact.out : Nat.Prime p).pos)
    simpa using mul_pos hp z.im_pos⟩

private lemma primeHecke_diag_point (p : ℕ) [Fact p.Prime] (z : ℍ) :
    primeHeckeReal p • z = primeHeckeDiagPoint p z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (primeHeckeReal_det_pos p)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, primeHeckeReal_coe,
    primeHeckeDiagPoint]

private lemma primeTrace_term (p : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (i : Fin p ⊕ Unit) :
    SlashInvariantForm.quotientFunc (CuspForm.translate f (primeHeckeReal p))
      (primeTraceEquiv p i) =
      ((f : ℍ → ℂ) ∣[k]
        (primeHeckeReal p * Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p i)⁻¹)) := by
  change (((f : ℍ → ℂ) ∣[k] primeHeckeReal p) ∣[k]
    (Matrix.SpecialLinearGroup.mapGL ℝ (primeCosetRep p i))⁻¹) = _
  rw [← SlashAction.slash_mul, map_inv]

/-- The literal `p+1` action of the actual cusp-preserving trace operator. -/
theorem primeHecke_action (p : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    primeHecke p k f z = (p : ℂ) ^ (k - 1) * f (primeHeckeDiagPoint p z) +
      (p : ℂ)⁻¹ * ∑ a : Fin p, f (primeHeckeUpperPoint p (a.val : ℤ) z) := by
  rw [primeHecke_apply]
  let := Fintype.ofFinite
    ((𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) ⧸ (primeHeckeSubgroup p).subgroupOf 𝒮ℒ)
  change (∑ q, SlashInvariantForm.quotientFunc
    (CuspForm.translate f (primeHeckeReal p)) q) z = _
  simp only [Finset.sum_apply]
  rw [← (primeTraceEquiv p).sum_comp]
  simp_rw [primeTrace_term]
  rw [Fintype.sum_sum_type]
  simp only [primeCosetRep, inv_inv, inv_one, map_mul, map_one, mul_one,
    Fintype.sum_unique]
  rw [primeHecke_diag_apply, primeHecke_diag_point]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← map_mul, ← primeHecke_upper_matrix, SlashAction.slash_mul]
  have hS : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S ∈
      (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨ModularGroup.S, rfl⟩
  rw [SlashInvariantFormClass.slash_action_eq (Γ := 𝒮ℒ) (k := k) f _ hS]
  exact primeHecke_upper_apply p (a.val : ℤ) k f z

local notation "𝕢" => Function.Periodic.qParam

private lemma prime_root_filter (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∑ a : Fin p, Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (a.val : ℂ) / (p : ℂ))) =
      if p ∣ n then (p : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))
  have hζ : IsPrimitiveRoot ζ p :=
    Complex.isPrimitiveRoot_exp p (Fact.out : Nat.Prime p).ne_zero
  have he (a : Fin p) : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (a.val : ℂ) / (p : ℂ))) =
      (ζ ^ n) ^ a.val := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  by_cases hn : p ∣ n
  · rw [if_pos hn, hζ.pow_eq_one_iff_dvd n |>.mpr hn]
    simp
  · rw [if_neg hn, Fin.sum_univ_eq_sum_range]
    have hz : ζ ^ n ≠ 1 := fun h => hn ((hζ.pow_eq_one_iff_dvd n).mp h)
    have hpow : (ζ ^ n) ^ p = 1 := by
      rw [← pow_mul, mul_comm n p, pow_mul, hζ.pow_eq_one, one_pow]
    have h := geom_sum_mul (ζ ^ n) p
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz)

private lemma prime_q_diag (p : ℕ) [Fact p.Prime] (z : ℍ) :
    𝕢 1 (primeHeckeDiagPoint p z) = (𝕢 1 z) ^ p := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  simp only [primeHeckeDiagPoint]
  ring

private lemma prime_q_step (p : ℕ) [Fact p.Prime] (z : ℍ) :
    (𝕢 (p : ℝ) z) ^ p = 𝕢 1 z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hp : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  field_simp

private lemma prime_q_upper_power (p : ℕ) [Fact p.Prime] (a : ℤ) (z : ℍ) (n : ℕ) :
    𝕢 1 (primeHeckeUpperPoint p a z) ^ n = (𝕢 (p : ℝ) z) ^ n *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (a : ℂ) / (p : ℂ))) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [primeHeckeUpperPoint]
  ring

private lemma prime_q_upper_sum (p : ℕ) [Fact p.Prime] (z : ℍ) (n : ℕ) :
    ∑ a : Fin p, 𝕢 1 (primeHeckeUpperPoint p (a.val : ℤ) z) ^ n =
      if p ∣ n then (p : ℂ) * 𝕢 1 z ^ (n / p) else 0 := by
  simp_rw [prime_q_upper_power, Int.cast_natCast]
  rw [← Finset.mul_sum, prime_root_filter]
  by_cases hn : p ∣ n
  · rw [if_pos hn, if_pos hn]
    have hpow : (𝕢 (p : ℝ) z) ^ n = 𝕢 1 z ^ (n / p) := by
      nth_rw 1 [← Nat.mul_div_cancel' hn]
      rw [pow_mul, prime_q_step]
    rw [hpow, mul_comm]
  · simp [hn]

private lemma prime_hasSum_dilate (p : ℕ) (hp : p ≠ 0)
    (c : ℕ → ℂ) (q v : ℂ) (h : HasSum (fun m => c m * (q ^ p) ^ m) v) :
    HasSum (fun n => (if p ∣ n then c (n / p) else 0) * q ^ n) v := by
  have hi : Function.Injective (fun m : ℕ => p * m) :=
    fun _ _ h => mul_left_cancel₀ hp h
  apply (hi.hasSum_iff ?_).mp
  · apply h.congr_fun
    intro m
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), pow_mul]
  · intro n hn
    have hnd : ¬ p ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [hnd]

private lemma prime_hasSum_upper (p : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    HasSum (fun n => (qExpansion 1 f).coeff (p * n) * 𝕢 1 z ^ n)
      ((p : ℂ)⁻¹ * ∑ a : Fin p, f (primeHeckeUpperPoint p (a.val : ℤ) z)) := by
  have hp : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hi : Function.Injective (fun m : ℕ => p * m) :=
    fun _ _ h => mul_left_cancel₀ hp h
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin p)))
    (fun a _ => ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_SL
      (primeHeckeUpperPoint p (a.val : ℤ) z))
  let d : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m *
    (if p ∣ m then (p : ℂ) * 𝕢 1 z ^ (m / p) else 0)
  have hd : HasSum d (∑ a : Fin p, f (primeHeckeUpperPoint p (a.val : ℤ) z)) :=
    hsum.congr_fun (by
      intro m
      rw [← Finset.mul_sum, prime_q_upper_sum])
  have hz (m : ℕ) (hm : m ∉ Set.range (fun n : ℕ => p * n)) : d m = 0 := by
    have hnd : ¬ p ∣ m := by
      rintro ⟨n, rfl⟩
      exact hm ⟨n, rfl⟩
    simp [d, hnd]
  have hcomp := (hi.hasSum_iff hz).mpr hd
  apply (hcomp.mul_left (p : ℂ)⁻¹).congr_fun
  intro n
  simp only [Function.comp_def, d, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
  field_simp

/-- The coefficient law of the actual analytic Hecke operator, including the constant term. -/
theorem primeHecke_qExpansion_coeff (p : ℕ) [Fact p.Prime] (k : ℤ)
    (f : CuspForm 𝒮ℒ k) (n : ℕ) :
    (qExpansion 1 (primeHecke p k f)).coeff n = (qExpansion 1 f).coeff (p * n) +
      (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
  let c : ℕ → ℂ := fun m => (qExpansion 1 f).coeff (p * m) +
    (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0)
  suffices h : ∀ z : ℍ, HasSum (fun m => c m • 𝕢 1 z ^ m) (primeHecke p k f z) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL h n).symm
  intro z
  have hdiag := ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_SL
    (primeHeckeDiagPoint p z)
  simp_rw [prime_q_diag] at hdiag
  have hd := prime_hasSum_dilate p (Fact.out : Nat.Prime p).ne_zero
    (fun m => (qExpansion 1 f).coeff m) (𝕢 1 z) (f (primeHeckeDiagPoint p z)) hdiag
  have hu := prime_hasSum_upper p k f z
  have h := (hu.add (hd.mul_left ((p : ℂ) ^ (k - 1)))).congr_fun
    (g := fun m => c m • 𝕢 1 z ^ m) (by
      intro m
      simp only [c, smul_eq_mul]
      ring)
  convert h using 1
  rw [primeHecke_action]
  ring

end

end D5.S3.Arith.ModularForms

#print axioms D5.S3.Arith.ModularForms.primeHecke
#print axioms D5.S3.Arith.ModularForms.primeHecke_apply
#print axioms D5.S3.Arith.ModularForms.primeHecke_action
#print axioms D5.S3.Arith.ModularForms.primeHecke_qExpansion_coeff

#print axioms D5.S3.Arith.ModularForms.primeHeckeSubgroup_mem
#print axioms D5.S3.Arith.ModularForms.primeTraceEquiv
