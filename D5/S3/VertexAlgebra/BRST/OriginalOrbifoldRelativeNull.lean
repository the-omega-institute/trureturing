/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull
   mirror-E: none(waiver:algebraic-original-orbifold-relative-null)
   anchors: []
   utility: none
   digest: The relative BRST shell at null momentum of the Golay–Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeGround
import Mathlib.LinearAlgebra.Basis.SMul

/-! The original Golay–Leech weight-one eigenspace vanishes. At null hyperbolic
momentum this leaves only its vacuum tensor the relative ghost and hyperbolic
oscillator states of combined excitation one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRelativeNull

open OriginalOrbifoldCriticalMatter OriginalOrbifoldBRSTZeroEnergy
open OriginalOrbifoldRelativeMassShell
open LatticeGeneratingFieldLocality (Charge Oscillator)
open LatticePositiveEnergy (chargeEnergy oscillatorEnergy oscillatorEnergy_eq_zero_iff
  carrierBasis_apply)
open D5.S3.Quantum.Fermionic
open BcGhostRelativeEnergy (level level_cast levelOccupationSets mem_levelOccupationSets_iff
  relative_level_coeff_iff relative_level_support)
open CountableOccupationFock (Fock ket)
open private fullBasis_apply orbifoldMode_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private weightZeroLabel orbifold_eigenspace_zero from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeGround
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData

/-- Exhaust the sixteen occupations in the level-zero cutoff. -/
theorem levelOccupationSets_zero : levelOccupationSets 0 = {{1}} := by
  decide

/-- Exhaust the sixty-four occupations in the level-one cutoff. -/
theorem levelOccupationSets_one : levelOccupationSets 1 = {∅, {1, 5}} := by
  decide

private theorem mem_levelOccupationSets_of_level (S : Finset ℕ) (hS : 3 ∉ S) :
    S ∈ levelOccupationSets (level S) := by
  have hcoeff (T : Finset ℕ) (hT : ket S T ≠ 0) : S = T := by
    by_contra hn
    exact hT (by simp [ket, hn])
  have hv : BcGhostRelativeEnergy.RelativeLevel (level S) (ket S) :=
    (relative_level_coeff_iff _ _).mpr ⟨fun T hT => by
      by_contra hn
      exact hS (hcoeff T hn ▸ hT), fun T hT => by
      rw [← hcoeff T hT, level_cast]⟩
  exact (mem_levelOccupationSets_iff _ _).mpr
    ⟨relative_level_support _ _ hv S (by simp [ket]), hS, (level_cast S).symm⟩

private theorem weight_one_empty (j : OrbifoldLabel) : j.1 ≠ 1 := by
  rcases j with ⟨n, i⟩
  intro hj
  change n = 1 at hj
  subst n
  have hr : Module.finrank ℂ ((orbifoldMode 0).eigenspace (1 : ℂ)) = 0 :=
    TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_low_spectrum.2.2.2.2.1
  have hk := i.isLt
  change i.val < Module.finrank ℂ ((orbifoldMode 0).eigenspace ((1 : ℕ) : ℂ)) at hk
  rw [Nat.cast_one, hr] at hk
  exact (Nat.not_lt_zero _) hk

private theorem weight_zero_unique (j : OrbifoldLabel) (hj : j.1 = 0) :
    j = weightZeroLabel := by
  rcases j with ⟨n, i⟩
  change n = 0 at hj
  subst n
  have hr : Module.finrank ℂ ((orbifoldMode 0).eigenspace (0 : ℂ)) = 1 :=
    TwistedGround.OriginalOrbifoldLowSpectrum.actual_leech_low_spectrum.2.2.2.1
  have hi := i.isLt
  change i.val < Module.finrank ℂ ((orbifoldMode 0).eigenspace ((0 : ℕ) : ℂ)) at hi
  rw [Nat.cast_zero, hr] at hi
  change (⟨0, i⟩ : OrbifoldLabel) = ⟨0, weightZeroLabel.2⟩
  exact congrArg (Sigma.mk 0) (Fin.ext (by change i.val = 0; omega))

/-- The allowed labels distinguish the hyperbolic oscillator and the two level-one
ghost kets, with a single orbifold label at weight zero. -/
theorem allowedLabels_iff (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0)
    (j : FullLabel) :
    j ∈ allowedLabels a ↔
      j.1 = weightZeroLabel ∧ j.2.1.1 = a ∧
        ((∃ i : Fin 2, j.2.1.2 = Finsupp.single (i, 0) 1 ∧ j.2.2 = {1}) ∨
          (j.2.1.2 = 0 ∧ (j.2.2 = ∅ ∨ j.2.2 = {1, 5}))) := by
  change (j.2.1.1 = a ∧ 3 ∉ j.2.2 ∧
    ((j.1.1 + oscillatorEnergy j.2.1.2 + level j.2.2 : ℕ) : ℤ) =
      1 - chargeEnergy hyperbolicData a) ↔ _
  rw [ha, sub_zero]
  constructor
  · rintro ⟨hm, hb, hcut⟩
    have hw1 := weight_one_empty j.1
    have hw : j.1.1 = 0 := by omega
    refine ⟨weight_zero_unique j.1 hw, hm, ?_⟩
    have hghost := mem_levelOccupationSets_of_level _ hb
    by_cases hl : level j.2.2 = 0
    · rw [hl, levelOccupationSets_zero, Finset.mem_singleton] at hghost
      have ho : oscillatorEnergy j.2.1.2 = 1 := by omega
      obtain ⟨i, hi⟩ := (LatticeZeroMomentumBRST.oscillatorEnergy_one_iff _ _).mp ho
      exact Or.inl ⟨i, hi, hghost⟩
    · have hl1 : level j.2.2 = 1 := by omega
      rw [hl1, levelOccupationSets_one, Finset.mem_insert, Finset.mem_singleton] at hghost
      exact Or.inr ⟨(oscillatorEnergy_eq_zero_iff _ _).mp (by omega), hghost⟩
  · rintro ⟨hw, hm, h⟩
    have hw0 : j.1.1 = 0 := congrArg Sigma.fst hw
    refine ⟨hm, ?_⟩
    rcases h with ⟨i, hi, hS⟩ | ⟨hd, hS | hS⟩
    · have ho :=
        (LatticeZeroMomentumBRST.oscillatorEnergy_one_iff hyperbolicData j.2.1.2).mpr ⟨i, hi⟩
      simp [hS, hw0, ho, level]
    · simp [hS, hw0, hd, oscillatorEnergy, level]
    · norm_num [hS, hw0, hd, oscillatorEnergy, level]

/-- The indices are ordered by native ghost number. -/
abbrev ShellIndex := Unit ⊕ (Fin 2 ⊕ Unit)

private def excitation : ShellIndex → LatticePositiveEnergy.Exponent hyperbolicData
  | .inl _ => 0
  | .inr (.inl i) => Finsupp.single (i, 0) 1
  | .inr (.inr _) => 0

private def occupation : ShellIndex → Finset ℕ
  | .inl _ => ∅
  | .inr (.inl _) => {1}
  | .inr (.inr _) => {1, 5}

private def fullLabel (a : UCharge) (k : ShellIndex) : FullLabel :=
  (weightZeroLabel, (a, excitation k), occupation k)

private theorem fullLabel_injective (a : UCharge) : Function.Injective (fullLabel a) := by
  intro k l h
  have he := congrArg (fun z : FullLabel => z.2.1.2) h
  have hg := congrArg (fun z : FullLabel => z.2.2) h
  rcases k with u | (i | u) <;> rcases l with v | (j | v)
  all_goals try { cases u; cases v; rfl }
  all_goals try {
    have h1 := congrArg (fun S : Finset ℕ => 1 ∈ S) hg
    have h5 := congrArg (fun S : Finset ℕ => 5 ∈ S) hg
    simp [fullLabel, occupation, Finset.mem_insert, Finset.mem_singleton] at h1 h5
    done }
  have hi := congrArg (fun d : LatticePositiveEnergy.Exponent hyperbolicData => d (i, 0)) he
  by_cases hij : i = j
  · rw [hij]
  · simp [fullLabel, excitation, Ne.symm hij] at hi

private theorem fullLabel_range (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Set.range (fullLabel a) = allowedLabels a := by
  ext j
  rw [allowedLabels_iff a ha]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨rfl, rfl, ?_⟩
    rcases k with u | (i | u)
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨i, rfl, rfl⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · rcases j with ⟨j, ⟨q, d⟩, S⟩
    rintro ⟨hj, hq, h⟩
    change j = weightZeroLabel at hj
    change q = a at hq
    subst j q
    rcases h with ⟨i, hi, hS⟩ | ⟨hd, hS | hS⟩
    · exact ⟨.inr (.inl i), by simp only [fullLabel, excitation, occupation, ← hi, ← hS]⟩
    · exact ⟨.inl (), by simp only [fullLabel, excitation, occupation, ← hd, ← hS]⟩
    · exact ⟨.inr (.inr ()), by simp only [fullLabel, excitation, occupation, ← hd, ← hS]⟩

private def chargedMonomial (a : UCharge) (k : ShellIndex) : Hyperbolic :=
  Finsupp.single a (MvPolynomial.monomial (excitation k) 1)

/-- The literal vacuum, charged monomial and occupied-site tensor. -/
def shellVector (a : UCharge) (k : ShellIndex) : State :=
  (orbifoldVertexAlgebra.vacuum ⊗ₜ[ℂ] chargedMonomial a k) ⊗ₜ[ℂ] ket (occupation k)

private theorem exists_vacuum_scale :
    ∃ z : ℂ, orbifoldBasis weightZeroLabel = z • orbifoldVertexAlgebra.vacuum := by
  have h : orbifoldBasis weightZeroLabel ∈ (orbifoldMode 0).eigenspace 0 := by
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [show weightZeroLabel.1 = 0 from rfl, Nat.cast_zero]
      using orbifoldMode_basis weightZeroLabel
  rw [orbifold_eigenspace_zero] at h
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨z, hz.symm⟩

private def vacuumScale : ℂ := Classical.choose exists_vacuum_scale

private theorem fullBasis_fullLabel (a : UCharge) (k : ShellIndex) :
    fullBasis (fullLabel a k) = vacuumScale • shellVector a k := by
  rw [fullBasis_apply, carrierBasis_apply]
  change (orbifoldBasis weightZeroLabel ⊗ₜ[ℂ] chargedMonomial a k)
      ⊗ₜ[ℂ] ket (occupation k) = _
  rw [Classical.choose_spec exists_vacuum_scale, ← TensorProduct.smul_tmul',
    ← TensorProduct.smul_tmul', shellVector, vacuumScale]

private theorem vacuumScale_ne_zero : vacuumScale ≠ 0 := by
  intro h
  exact fullBasis.ne_zero (fullLabel 0 (.inl ()))
    (by rw [fullBasis_fullLabel, h, zero_smul])

private def rawBasis (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Module.Basis ShellIndex ℂ (relativeMassShell a) :=
  let b := Module.Basis.span
    (fullBasis.linearIndependent.comp (fullLabel a) (fullLabel_injective a))
  b.map (LinearEquiv.ofEq _ _ (by
    rw [relativeMassShell_eq_span, ← fullLabel_range a ha, ← Set.range_comp]))

/-- A basis of the actual momentum, b₀, and total L₀ intersection. -/
def shellBasis (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Module.Basis ShellIndex ℂ (relativeMassShell a) :=
  (rawBasis a ha).unitsSMul (fun _ => (Units.mk0 vacuumScale vacuumScale_ne_zero)⁻¹)

theorem shellBasis_coe (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) (k : ShellIndex) :
    (shellBasis a ha k : State) = shellVector a k := by
  rw [shellBasis, Module.Basis.unitsSMul_apply]
  change vacuumScale⁻¹ • (rawBasis a ha k : State) = _
  have hb : (rawBasis a ha k : State) = fullBasis (fullLabel a k) := by
    rw [rawBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Module.Basis.coe_span_apply]
    rfl
  rw [hb, fullBasis_fullLabel, smul_smul, inv_mul_cancel₀ vacuumScale_ne_zero, one_smul]

/-- The null shell consists of four independent states. -/
theorem shell_finrank (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Module.finrank ℂ (relativeMassShell a) = 4 := by
  rw [Module.finrank_eq_card_basis (shellBasis a ha)]
  decide

def ghostNumber : ShellIndex → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- Native ghost number on the literal normalized tensors. -/
theorem ghostNumber_shellVector (a : UCharge) (k : ShellIndex) :
    BcGhostChargeTensor.number (M := Matter) (shellVector a k) =
      (ghostNumber k : ℂ) • shellVector a k := by
  rcases k with u | (i | u)
  all_goals norm_num [BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    shellVector, occupation, ghostNumber, TensorProduct.map_tmul, number_ket,
    BcGhostCharge.charge, Finset.filter_insert, Finset.filter_singleton, TensorProduct.tmul_smul]

#print axioms levelOccupationSets_zero
#print axioms levelOccupationSets_one
#print axioms allowedLabels_iff
#print axioms shellBasis_coe
#print axioms shell_finrank
#print axioms ghostNumber_shellVector

open LatticeGeneratingFieldLocality (bilinear unitCharge)
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeSugawaraCurrents (sugawaraMode_current_commutator)
open CountableOccupationFock (create_ket)
open LatticeSugawaraConformal (chargePolynomial sugawaraMode_ground_minus_one)
open LatticeSugawaraVirasoro (chargeScalar sugawaraMode_ground_positive)
open BcGhostFock (c)
open LatticeZeroMomentumBRST (Qg_down Qg_top c_minus_one_down)
open private c_high_odd from D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST
open private neutralMode_ground_positive from D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
open scoped VertexOperator

private abbrev ground (a : UCharge) : Hyperbolic :=
  Finsupp.single a (1 : Oscillator hyperbolicData)

private abbrev current (a : UCharge) (i : Fin 2) : Hyperbolic :=
  Finsupp.single a (MvPolynomial.X (i, 0) : Oscillator hyperbolicData)

private abbrev withVacuum (u : Hyperbolic) : Matter := orbifoldVertexAlgebra.vacuum ⊗ₜ[ℂ] u

private theorem withVacuum_zero : withVacuum 0 = 0 :=
  TensorProduct.tmul_zero Hyperbolic orbifoldVertexAlgebra.vacuum

abbrev bottom : ShellIndex := .inl ()
abbrev middle (i : Fin 2) : ShellIndex := .inr (.inl i)
abbrev top : ShellIndex := .inr (.inr ())

private theorem shellVector_bottom (a : UCharge) :
    shellVector a bottom = withVacuum (ground a) ⊗ₜ[ℂ] ket ∅ := by
  simp [shellVector, chargedMonomial, excitation, occupation]

private theorem shellVector_middle (a : UCharge) (i : Fin 2) :
    shellVector a (middle i) = withVacuum (current a i) ⊗ₜ[ℂ] ket {1} := by
  rfl

private theorem shellVector_top (a : UCharge) :
    shellVector a top = withVacuum (ground a) ⊗ₜ[ℂ] ket {1, 5} := by
  simp [shellVector, chargedMonomial, excitation, occupation]

private theorem orbifold_vacuum_mode (m : ℤ) (hm : -1 ≤ m) :
    orbifoldMode m orbifoldVertexAlgebra.vacuum = 0 := by
  rcases eq_or_lt_of_le hm with h | h
  · subst m
    rw [orbifoldMode, TwistedGround.OriginalOrbifoldConformal.L_minus_one_eq_translation
      _ _ _ ActualLeechHyperbolic.leech_spec.1]
    exact orbifoldVertexAlgebra.translation_vacuum
  · rw [orbifoldMode_eq_stateField]
    exact orbifoldVertexAlgebra.creativity _ (m + 1) (by omega)

private theorem mode_withVacuum (m : ℤ) (hm : -1 ≤ m) (u : Hyperbolic) :
    mode m (withVacuum u) = withVacuum (hyperbolicMode m u) := by
  simp only [mode, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    orbifold_vacuum_mode m hm, TensorProduct.zero_tmul, zero_add]

private theorem hyperbolic_zero_on_basis (a : UCharge)
    (ha : chargeEnergy hyperbolicData a = 0) (k : ShellIndex) :
    hyperbolicMode 0 (chargedMonomial a k) =
      (oscillatorEnergy (excitation k) : ℂ) • chargedMonomial a k := by
  have h := LatticePositiveEnergy.actualL0_basis hyperbolicData hyperbolicInverse
    hyperbolic_inverse_left hyperbolic_inverse_right (a, excitation k)
  simpa only [hyperbolicMode, chargedMonomial, carrierBasis_apply,
    LatticePositiveEnergy.energy, ha, zero_add, Int.cast_natCast] using h

private theorem hyperbolic_zero_ground (a : UCharge)
    (ha : chargeEnergy hyperbolicData a = 0) : hyperbolicMode 0 (ground a) = 0 := by
  simpa [chargedMonomial, excitation, oscillatorEnergy] using hyperbolic_zero_on_basis a ha bottom

private theorem hyperbolic_zero_current (a : UCharge)
    (ha : chargeEnergy hyperbolicData a = 0) (i : Fin 2) :
    hyperbolicMode 0 (current a i) = current a i := by
  have h := (LatticeZeroMomentumBRST.oscillatorEnergy_one_iff hyperbolicData
    (excitation (middle i))).mpr ⟨i, rfl⟩
  have hs := hyperbolic_zero_on_basis a ha (middle i)
  rw [h, Nat.cast_one, one_smul] at hs
  exact hs

private theorem hyperbolic_positive_ground (a : UCharge) (m : ℤ) (hm : 0 < m) :
    hyperbolicMode m (ground a) = 0 :=
  sugawaraMode_ground_positive hyperbolicData hyperbolicInverse a m hm

private theorem hyperbolic_minus_one_ground (a : UCharge) :
    hyperbolicMode (-1) (ground a) = ∑ i : Fin 2, (a i : ℂ) • current a i := by
  rw [hyperbolicMode, sugawaraMode_ground_minus_one hyperbolicData hyperbolicInverse
    hyperbolic_inverse_left hyperbolic_inverse_right]
  simp only [chargePolynomial, Finsupp.smul_single, Finsupp.single_finsetSum]
  change (∑ i : Fin 2, Finsupp.single a ((a i : ℂ) • MvPolynomial.X (i, 0))) = _
  rfl

private theorem hyperbolic_positive_current (a : UCharge) (i : Fin 2)
    (m : ℤ) (hm : 0 < m) :
    hyperbolicMode m (current a i) = neutralMode hyperbolicData i (m - 1) (ground a) := by
  have hcurrent : neutralMode hyperbolicData i (-1) (ground a) = current a i := by
    simp [LatticeSugawaraCurrents.neutralMode_single,
      LatticeFiniteNegativeGeneration.neutralPolynomialMode]
  have h := LinearMap.congr_fun
    (sugawaraMode_current_commutator hyperbolicData hyperbolicInverse
      hyperbolic_inverse_left hyperbolic_inverse_right i m (-1)) (ground a)
  simpa [LinearMap.sub_apply, Module.End.mul_apply, hcurrent, hyperbolicMode,
    show LatticeSugawaraCurrents.sugawaraMode hyperbolicData hyperbolicInverse m
      (ground a) = 0 from hyperbolic_positive_ground a m hm, sub_eq_add_neg]
    using h

private theorem summand_withVacuum (m : ℤ) (hm : -1 ≤ m) (u : Hyperbolic) (w : Fock) :
    VirasoroBRST.summand matterDatum m (withVacuum u ⊗ₜ[ℂ] w) =
      withVacuum (hyperbolicMode m u) ⊗ₜ[ℂ] c (-m) w := by
  change TensorProduct.map (mode m) (c (-m)) (withVacuum u ⊗ₜ[ℂ] w) = _
  rw [TensorProduct.map_tmul, mode_withVacuum m hm]

private theorem raw_T_term (m : ℤ) (u : Hyperbolic) (w : Fock) :
    VirasoroBRST.summand matterDatum m (withVacuum u ⊗ₜ[ℂ] w) =
      mode m (withVacuum u) ⊗ₜ[ℂ] c (-m) w :=
  TensorProduct.map_tmul _ _ _ _

private theorem Q_withVacuum (u : Hyperbolic) (w : Fock) :
    Q (withVacuum u ⊗ₜ[ℂ] w) =
      VirasoroBRST.T matterDatum (withVacuum u ⊗ₜ[ℂ] w) +
        withVacuum u ⊗ₜ[ℂ] BcGhostBRST.Qg w := by
  change _ + TensorProduct.map LinearMap.id BcGhostBRST.Qg
    (withVacuum u ⊗ₜ[ℂ] w) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]

/-- The native m = -1 term creates the current polarized by the momentum. -/
theorem Q_bottom (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Q (shellVector a bottom) = ∑ i : Fin 2, (a i : ℂ) • shellVector a (middle i) := by
  rw [shellVector_bottom, Q_withVacuum]
  have hg : BcGhostBRST.Qg (ket ∅) = 0 := BcGhostBRST.Qg_vacuum
  rw [hg, TensorProduct.tmul_zero, add_zero]
  change (∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m
    (withVacuum (ground a) ⊗ₜ[ℂ] ket ∅)) = _
  rw [finsum_eq_single _ (-1)]
  · rw [summand_withVacuum (-1) (by omega), hyperbolic_minus_one_ground]
    have hc : c (- -1) (ket ∅) = ket {1} := BcGhostFock.ghost_vacuum.2.2.1
    rw [hc]
    let insertVacua : Hyperbolic →ₗ[ℂ] State :=
      ((TensorProduct.mk ℂ Matter Fock).flip (ket {1})).comp
        (TensorProduct.mk ℂ Orbifold Hyperbolic orbifoldVertexAlgebra.vacuum)
    change insertVacua (∑ i : Fin 2, (a i : ℂ) • current a i) = _
    simp only [map_sum, map_smul]
    rfl
  · intro m hm
    by_cases hlo : m < -1
    · rw [raw_T_term, c_high_odd ∅ (by simp) _ (by omega), TensorProduct.tmul_zero]
    rw [summand_withVacuum m (by omega)]
    rcases eq_or_lt_of_le (show 0 ≤ m by omega) with h | h
    · subst m
      rw [hyperbolic_zero_ground a ha, withVacuum_zero, TensorProduct.zero_tmul]
    · rw [hyperbolic_positive_ground a m h, withVacuum_zero, TensorProduct.zero_tmul]

/-- The m = 0 term cancels the cubic c₀ term. The m = 1 term
has the minus sign of c(-1) on the native occupied-site ket. -/
theorem Q_middle (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) (i : Fin 2) :
    Q (shellVector a (middle i)) = -(chargeScalar hyperbolicData a i) • shellVector a top := by
  rw [shellVector_middle, shellVector_top, Q_withVacuum, Qg_down]
  rw [VirasoroBRST.finite_capture matterDatum _ {0, 1}]
  · rw [Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)), Finset.sum_singleton,
      summand_withVacuum 0 (by omega), summand_withVacuum 1 (by omega),
      hyperbolic_zero_current a ha i, hyperbolic_positive_current a i 1 (by omega)]
    rw [show (1 : ℤ) - 1 = 0 by decide, LatticeSugawaraVirasoro.neutralMode_zero_single]
    norm_num only [neg_zero, c_minus_one_down, TensorProduct.tmul_neg,
      TensorProduct.tmul_smul, neg_smul]
    abel
  · intro m hm
    by_contra h
    apply hm
    change VirasoroBRST.summand matterDatum m (withVacuum (current a i) ⊗ₜ[ℂ] ket {1}) = 0
    have hm0 : m ≠ 0 := fun he => h (by simp [he])
    have hm1 : m ≠ 1 := fun he => h (by simp [he])
    by_cases hlo : m < -1
    · rw [raw_T_term, c_high_odd {1} (by simp) _ (by omega), TensorProduct.tmul_zero]
    by_cases he : m = -1
    · subst m
      rw [raw_T_term]
      norm_num [c, create_ket]
    rw [summand_withVacuum m (by omega), hyperbolic_positive_current a i m (by omega),
      neutralMode_ground_positive _ _ _ _ (by omega),
      withVacuum_zero, TensorProduct.zero_tmul]

/-- The top ket is closed by the actual matter sum and cubic ghost action. -/
theorem Q_top (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    Q (shellVector a top) = 0 := by
  rw [shellVector_top, Q_withVacuum, Qg_top, TensorProduct.tmul_zero, add_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hlo : m < -1
  · rw [raw_T_term, c_high_odd {1, 5} (by simp) _ (by omega), TensorProduct.tmul_zero]
  by_cases he : m = -1
  · subst m
    rw [raw_T_term]
    norm_num [c, create_ket]
  rw [summand_withVacuum m (by omega)]
  rcases eq_or_lt_of_le (show 0 ≤ m by omega) with h | h
  · subst m
    rw [hyperbolic_zero_ground a ha, withVacuum_zero, TensorProduct.zero_tmul]
  · rw [hyperbolic_positive_ground a m h, withVacuum_zero, TensorProduct.zero_tmul]

private theorem chargeScalar_zero (a : UCharge) :
    chargeScalar hyperbolicData a 0 = (a 1 : ℂ) := by
  have h : bilinear hyperbolicData (unitCharge hyperbolicData 0) a = a 1 := by
    change (∑ k : Fin 2, ∑ l : Fin 2,
      unitCharge hyperbolicData 0 k * hyperbolicData.G k l * a l) = _
    rw [hyperbolic_gram]
    simp [unitCharge, Fin.sum_univ_two]
  exact_mod_cast h

private theorem chargeScalar_one (a : UCharge) :
    chargeScalar hyperbolicData a 1 = (a 0 : ℂ) := by
  have h : bilinear hyperbolicData (unitCharge hyperbolicData 1) a = a 0 := by
    change (∑ k : Fin 2, ∑ l : Fin 2,
      unitCharge hyperbolicData 1 k * hyperbolicData.G k l * a l) = _
    rw [hyperbolic_gram]
    simp [unitCharge, Fin.sum_univ_two]
  exact_mod_cast h

/-- The three maps of the restricted native operator in the explicit basis.
The middle row is the negative of the ordered hyperbolic pairing. -/
theorem differential_on_basis (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0) :
    differential a (shellBasis a ha bottom) =
      (a 0 : ℂ) • shellBasis a ha (middle 0) + (a 1 : ℂ) • shellBasis a ha (middle 1) ∧
    differential a (shellBasis a ha (middle 0)) = -(a 1 : ℂ) • shellBasis a ha top ∧
    differential a (shellBasis a ha (middle 1)) = -(a 0 : ℂ) • shellBasis a ha top ∧
    differential a (shellBasis a ha top) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Subtype.ext
  all_goals change Q (↑(shellBasis a ha _) : State) = _
  · simpa only [Submodule.coe_add, Submodule.coe_smul, shellBasis_coe, Fin.sum_univ_two]
      using Q_bottom a ha
  · simpa only [Submodule.coe_smul, shellBasis_coe, chargeScalar_zero] using Q_middle a ha 0
  · simpa only [Submodule.coe_smul, shellBasis_coe, chargeScalar_one] using Q_middle a ha 1
  · simpa only [Submodule.coe_zero, shellBasis_coe] using Q_top a ha

#print axioms Q_bottom
#print axioms Q_middle
#print axioms Q_top
#print axioms differential_on_basis

/-- At nonzero null momentum the restricted differential admits a contracting homotopy. -/
theorem exists_contraction (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0)
    (hne : a ≠ 0) :
    ∃ h : Module.End ℂ (relativeMassShell a),
      differential a * h + h * differential a = 1 := by
  classical
  let B := shellBasis a ha
  let d := differential a
  obtain ⟨hd0, hd10, hd11, hd2⟩ := differential_on_basis a ha
  change d (B bottom) = (a 0 : ℂ) • B (middle 0) + (a 1 : ℂ) • B (middle 1) at hd0
  change d (B (middle 0)) = -(a 1 : ℂ) • B top at hd10
  change d (B (middle 1)) = -(a 0 : ℂ) • B top at hd11
  change d (B top) = 0 at hd2
  change ∃ h : Module.End ℂ (relativeMassShell a), d * h + h * d = 1
  have hnull : a 0 = 0 ∨ a 1 = 0 :=
    mul_eq_zero.mp ((hyperbolic_chargeEnergy a).symm.trans ha)
  have cast_ne {z : ℤ} (hz : z ≠ 0) : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  rcases hnull with hzero | hzero
  · have hnonzero : a 1 ≠ 0 := by
      intro hz
      apply hne
      funext i
      fin_cases i <;> assumption
    let h : Module.End ℂ (relativeMassShell a) := B.constr ℂ (fun k =>
      match k with
      | .inl _ => 0
      | .inr (.inl i) => if i = 1 then (a 1 : ℂ)⁻¹ • B bottom else 0
      | .inr (.inr _) => -((a 1 : ℂ)⁻¹) • B (middle 0))
    have hh (k : ShellIndex) : h (B k) = _ := B.constr_basis ℂ _ k
    refine ⟨h, B.ext ?_⟩
    rintro (⟨⟩ | (i | ⟨⟩))
    · change d (h (B bottom)) + h (d (B bottom)) = B bottom
      simp [hd0, hh, hzero, smul_smul, cast_ne hnonzero]
    · fin_cases i
      · change d (h (B (middle 0))) + h (d (B (middle 0))) = B (middle 0)
        simp [hd10, hh, smul_smul, cast_ne hnonzero]
      · change d (h (B (middle 1))) + h (d (B (middle 1))) = B (middle 1)
        simp [hd0, hd11, hh, hzero, smul_smul, cast_ne hnonzero]
    · change d (h (B top)) + h (d (B top)) = B top
      simp [hd10, hd2, hh, smul_smul, cast_ne hnonzero]
  · have hnonzero : a 0 ≠ 0 := by
      intro hz
      apply hne
      funext i
      fin_cases i <;> assumption
    let h : Module.End ℂ (relativeMassShell a) := B.constr ℂ (fun k =>
      match k with
      | .inl _ => 0
      | .inr (.inl i) => if i = 0 then (a 0 : ℂ)⁻¹ • B bottom else 0
      | .inr (.inr _) => -((a 0 : ℂ)⁻¹) • B (middle 1))
    have hh (k : ShellIndex) : h (B k) = _ := B.constr_basis ℂ _ k
    refine ⟨h, B.ext ?_⟩
    rintro (⟨⟩ | (i | ⟨⟩))
    · change d (h (B bottom)) + h (d (B bottom)) = B bottom
      simp [hd0, hh, hzero, smul_smul, cast_ne hnonzero]
    · fin_cases i
      · change d (h (B (middle 0))) + h (d (B (middle 0))) = B (middle 0)
        simp [hd0, hd10, hh, hzero, smul_smul, cast_ne hnonzero]
      · change d (h (B (middle 1))) + h (d (B (middle 1))) = B (middle 1)
        simp [hd11, hh, smul_smul, cast_ne hnonzero]
    · change d (h (B top)) + h (d (B top)) = B top
      simp [hd11, hd2, hh, smul_smul, cast_ne hnonzero]

/-- Relative BRST cohomology vanishes at each nonzero null hyperbolic momentum. -/
theorem differential_exact (a : UCharge) (ha : chargeEnergy hyperbolicData a = 0)
    (hne : a ≠ 0) :
    LinearMap.range (differential a) = LinearMap.ker (differential a) := by
  let d := differential a
  obtain ⟨h, hh⟩ := exists_contraction a ha hne
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (differential_squared a) y)
  · intro x hx
    have hz : d x = 0 := LinearMap.mem_ker.mp hx
    refine ⟨h x, ?_⟩
    have h' := LinearMap.congr_fun hh x
    change d (h x) + h (d x) = x at h'
    simpa only [hz, map_zero, add_zero] using h'

#print axioms exists_contraction
#print axioms differential_exact

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeNull
