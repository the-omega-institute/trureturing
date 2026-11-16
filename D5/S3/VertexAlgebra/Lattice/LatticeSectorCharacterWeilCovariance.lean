/- GID: D5/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeSectorCharacterWeilCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual dual-coset energy traces and their normalized Weil S covariance. -/

import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetPositiveEnergy
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
import Mathlib.LinearAlgebra.Trace

/-! The finite actual dual-coset energy traces are regrouped analytically
before applying the existing discriminant theta and eta transformation laws. -/

/-
proof_shape: lattice_sector_character_s_transform: content
admission_basis: escape-witness
escape_witness: character_formula identifies the rationally indexed actual
  eigenspace-trace sum with the joint charge/occupation sum, proves absolute
  convergence before regrouping, and evaluates its oscillator factor. The
  character is not introduced by the theta/eta formula or a transformation law.
  The analytic theta and eta suppliers, the actual dual-coset action and its
  coefficient-fiber equivalence are reused without changing their statements.
This is classical lattice-character mathematics, not an originality claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeDualCosetConformal LatticeDiscriminantTheta LatticeDiscriminantWeil
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation
open D5.S3.Fourier.MatrixGaussian
open Complex
open private rat_unit summable_coset_norm from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private eta_S_principal from
  D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

private lemma duality (D : LatticeData) (hD : (gramReal D).PosDef) (r : Charge D) :
    ∀ i, ∑ j, (D.G i j : ℚ) * dualVector D r j = (r i : ℚ) := by
  have h : gramRat D *ᵥ dualVector D r = (fun i => (r i : ℚ)) := by
    rw [dualVector, inverseRat, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (rat_unit D hD), Matrix.one_mulVec]
  exact congrFun h

/-- The literal original-omega zero-mode eigenspace of the actual coset module. -/
abbrev sectorGrade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Discriminant D) (e : ℚ) :=
  (moduleL D (representative D a) H 0).eigenspace (e : ℂ)

/-- Each coefficient is a trace on a finite actual eigenspace, never on the
infinite ambient carrier. Positivity and both inverse identities supply finiteness. -/
def sectorTraceTerm (D : LatticeData) (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (τ : ℂ) (e : ℚ) : ℂ := by
  letI := LatticeDualCosetEnergy.eigenspace_finiteDimensional D (representative D a)
    H hHG hGH (dualVector D (representative D a)) (duality D hD _) hD e
  exact LinearMap.trace ℂ (sectorGrade D H a e) LinearMap.id *
    exp (2 * Real.pi * I * τ * ((e : ℂ) - D.rank / 24))

/-- The central-charge-normalized sum of actual finite-grade identity traces.
All rational energies are retained, including empty grades and rank zero. -/
def sectorCharacter (D : LatticeData) (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (τ : ℂ) : ℂ :=
  ∑' e : ℚ, sectorTraceTerm D hD H hHG hGH a τ e

private lemma trace_eq_card (D : LatticeData) (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (e : ℚ) :
    LinearMap.trace ℂ (sectorGrade D H a e) LinearMap.id =
      (Nat.card {x : Label D //
        LatticeDualCosetEnergy.weight D (dualVector D (representative D a)) x = e} : ℂ) := by
  classical
  let μ := dualVector D (representative D a)
  letI := LatticeDualCosetEnergy.fiber_finite D μ hD e
  letI : Fintype {x : Label D // LatticeDualCosetEnergy.weight D μ x = e} :=
    Fintype.ofFinite _
  have he : sectorGrade D H a e = LatticeDualCosetEnergy.rationalGrade D μ e := by
    ext v
    rw [Module.End.mem_eigenspace_iff]
    exact LatticeDualCosetEnergy.moduleL_eigen_iff D (representative D a)
      H hHG hGH μ (duality D hD _) e v
  let b := Module.Basis.ofRepr ((LinearEquiv.ofEq _ _ he).trans
    (LatticeDualCosetEnergy.gradeCoeffEquiv D μ e))
  letI := Module.Finite.of_basis b
  rw [LinearMap.trace_id, Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card]

private lemma oscillator_norm (D : LatticeData) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : Exponent D => ‖q ^ oscillatorEnergy d‖) := by
  simpa [signedIntegerMonomial, integerEnergy, oscillatorEnergy] using
    summable_norm_signed_integer_occupations (Fin D.rank) hq

private lemma oscillator_monomial (D : LatticeData) (q : ℂ) (d : Exponent D) :
    monomial (fun x : Index D => q ^ (x.2 + 1)) d = q ^ oscillatorEnergy d := by
  classical
  simp only [monomial, Finsupp.prod, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

private lemma oscillator_eta (D : LatticeData) (τ : ℂ) (hτ : 0 < τ.im) :
    exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d) =
      (ModularForm.eta τ ^ D.rank)⁻¹ := by
  let q := exp (2 * Real.pi * I * τ)
  have hq : ‖q‖ < 1 := by
    simpa [q, Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hτ
  have hp := hasProd_inverse_eq_occupation_sum (fun x : Index D => q ^ (x.2 + 1))
    ((oscillator_norm D hq).congr (fun d => congrArg norm (oscillator_monomial D q d).symm))
    (fun x => by simpa only [norm_pow] using
      pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero x.2))
  simp_rw [oscillator_monomial] at hp
  have hs : HasProd (fun n : ℕ => ((1 - q ^ (n + 1))⁻¹) ^ D.rank)
      (∑' d : Exponent D, q ^ oscillatorEnergy d) := by
    have hh := (Equiv.prodComm ℕ (Fin D.rank)).hasProd_iff.mpr hp
    simpa using hh.prod_fiberwise
      (fun n => hasProd_fintype (fun _ : Fin D.rank => (1 - q ^ (n + 1))⁻¹))
  have hn : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 := by
    simpa [ModularForm.eta_q, Function.Periodic.qParam, q] using
      ModularForm.eta_tprod_ne_zero hτ
  have he := ((ModularForm.multipliable_one_sub_pow hq).hasProd.inv₀ hn).pow D.rank
  have heta : ModularForm.eta τ ^ D.rank =
      exp (2 * Real.pi * I * τ * D.rank / 24) *
        (∏' n : ℕ, (1 - q ^ (n + 1))) ^ D.rank := by
    have hparam : Function.Periodic.qParam 1 τ = q := by
      simp [q, Function.Periodic.qParam]
    simp only [ModularForm.eta, ModularForm.eta_q, mul_pow, hparam]
    congr 1
    simp only [Function.Periodic.qParam, ofReal_ofNat, ← exp_nat_mul]
    congr 1
    ring
  have hexp : exp (-2 * Real.pi * I * τ * D.rank / 24) =
      (exp (2 * Real.pi * I * τ * D.rank / 24))⁻¹ := by
    rw [← exp_neg]
    congr 1
    ring
  rw [hs.unique he, heta, _root_.mul_inv_rev, hexp, inv_pow]
  exact mul_comm _ _

private lemma charge_exponential (D : LatticeData) (r n : Charge D) (τ : ℂ) :
    exp (2 * Real.pi * I * τ * (LatticeDualCosetEnergy.chargeWeight D (dualVector D r) n : ℂ)) =
      exp (Real.pi * I * τ *
        (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ)) := by
  have hw : (LatticeDualCosetEnergy.chargeWeight D (dualVector D r) n : ℂ) =
      (quadratic (gramReal D) ((fun i => (n i : ℝ)) + shift D r) : ℂ) / 2 := by
    simp [LatticeDualCosetEnergy.chargeWeight, LatticeDualCosetEnergy.pairing,
      quadratic, dotProduct, Matrix.mulVec, gramReal, shift, Finset.mul_sum, mul_assoc]
  rw [hw]
  congr 1
  ring

private lemma basis_term (D : LatticeData) (r : Charge D) (τ : ℂ) (x : Label D) :
    exp (2 * Real.pi * I * τ *
      ((LatticeDualCosetEnergy.weight D (dualVector D r) x : ℂ) - D.rank / 24)) =
    exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (exp (Real.pi * I * τ *
        (quadratic (gramReal D) ((fun i => (x.1 i : ℝ)) + shift D r) : ℂ)) *
        exp (2 * Real.pi * I * τ) ^ oscillatorEnergy x.2) := by
  rw [← charge_exponential, ← exp_nat_mul, ← exp_add, ← exp_add]
  congr 1
  simp only [LatticeDualCosetEnergy.weight, Rat.cast_add, Rat.cast_natCast]
  ring

private lemma character_formula (D : LatticeData) (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun e : ℚ => ‖sectorTraceTerm D hD H hHG hGH a τ e‖) ∧
      sectorCharacter D hD H hHG hGH a τ = sectorTheta D a τ / ModularForm.eta τ ^ D.rank := by
  classical
  let μ := dualVector D (representative D a)
  let f : Label D → ℂ := fun x =>
    exp (2 * Real.pi * I * τ * ((LatticeDualCosetEnergy.weight D μ x : ℂ) - D.rank / 24))
  have hq : ‖exp (2 * Real.pi * I * τ)‖ < 1 := by
    simpa [Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hτ
  have hc := summable_coset_norm D hD (representative D a) τ hτ
  have ho := oscillator_norm D hq
  have habs : Summable (fun x => ‖f x‖) := by
    have h := (hc.mul_norm ho).mul_left ‖exp (-2 * Real.pi * I * τ * D.rank / 24)‖
    simpa only [f, μ, basis_term, norm_mul] using h
  have hfiber (e : ℚ) :
      (∑' x : {x : Label D // LatticeDualCosetEnergy.weight D μ x = e}, f x) =
        sectorTraceTerm D hD H hHG hGH a τ e := by
    letI := LatticeDualCosetEnergy.fiber_finite D μ hD e
    letI : Fintype {x : Label D // LatticeDualCosetEnergy.weight D μ x = e} := Fintype.ofFinite _
    simp only [tsum_fintype, f]
    simp_rw [show ∀ x : {x : Label D // LatticeDualCosetEnergy.weight D μ x = e},
      LatticeDualCosetEnergy.weight D μ x.val = e from fun x => x.property]
    simp [sectorTraceTerm, trace_eq_card D hD H hHG hGH, μ, Nat.card_eq_fintype_card]
  have hnorm (e : ℚ) :
      ‖sectorTraceTerm D hD H hHG hGH a τ e‖ ≤
        ∑' x : {x : Label D // LatticeDualCosetEnergy.weight D μ x = e}, ‖f x‖ := by
    rw [← hfiber]
    exact norm_tsum_le_tsum_norm (habs.subtype _)
  have hgroup := habs.hasSum.tsum_fiberwise (LatticeDualCosetEnergy.weight D μ)
  have hs := habs.of_norm.hasSum.tsum_fiberwise (LatticeDualCosetEnergy.weight D μ)
  have hs' : HasSum (sectorTraceTerm D hD H hHG hGH a τ) (∑' x, f x) := by
    exact hs.congr_fun (fun e => (hfiber e).symm)
  refine ⟨hgroup.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm, ?_⟩
  rw [sectorCharacter, hs'.tsum_eq]
  simp_rw [f, μ, basis_term]
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hc ho]
  change exp (-2 * Real.pi * I * τ * D.rank / 24) *
    (sectorTheta D a τ * ∑' d : Exponent D,
      exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d) = _
  rw [mul_left_comm, oscillator_eta D τ hτ, div_eq_mul_inv]

/-- The actual rational-grade trace character converges absolutely and
transforms by the existing negative, cardinality-normalized Weil S operator.
The theta/eta expression is proved from actual eigenspace traces. -/
theorem lattice_sector_character_s_transform (D : LatticeData)
    (hD : (gramReal D).PosDef) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im) :
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    Summable (fun e : ℚ => ‖sectorTraceTerm D hD H hHG hGH a τ e‖) ∧
      sectorCharacter D hD H hHG hGH a (-1 / τ) =
        weilS D (fun b => sectorCharacter D hD H hHG hGH b τ) a := by
  letI : Fact (gramReal D).PosDef := ⟨hD⟩
  letI : Fintype (Discriminant D) := Fintype.ofFinite _
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  refine ⟨(character_formula D hD H hHG hGH a τ hτ).1, ?_⟩
  rw [(character_formula D hD H hHG hGH a (-1 / τ) hS).2,
    sector_S D hD a τ hτ, eta_S_principal τ hτ, mul_pow]
  have hpower : sqrt (-I * τ) ^ D.rank = (-I * τ) ^ ((D.rank : ℂ) / 2) := by
    simp only [sqrt, ← cpow_nat_mul, div_eq_mul_inv]
  have hnonzero : (-I * τ) ^ ((D.rank : ℂ) / 2) ≠ 0 := by
    apply cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by intro h; simp [h] at hτ)
  have hr : rho D = (Real.sqrt (gramReal D).det : ℂ) := by
    rw [rho, (dual_lattice_realization D hD).2.2.1]
  change _ = (rho D)⁻¹ * ∑ b : Discriminant D,
    pairingCharacter D hD a (-b) * sectorCharacter D hD H hHG hGH b τ
  simp_rw [(character_formula D hD H hHG hGH _ τ hτ).2]
  rw [hpower, hr]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hn' : (-(I * τ)) ^ ((D.rank : ℂ) / 2) ≠ 0 := by
    simpa only [neg_mul] using hnonzero
  field_simp [hnonzero, hn', pow_ne_zero D.rank (ModularForm.eta_ne_zero hτ),
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD.det_pos).ne']

#print axioms sectorGrade
#print axioms sectorTraceTerm
#print axioms sectorCharacter
#print axioms lattice_sector_character_s_transform

end D5.S3.VertexAlgebra.LatticeSectorCharacterWeilCovariance
