import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
import Reg.Support.SingleDependentReadout

/-! Whole-family interventions for ChiralSymmetrySkyrme4D. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open Filter Matrix
open scoped Matrix Matrix.Norms.Elementwise Topology

namespace Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

local macro "family% " arena:term:max source:term:max actual:term:max witness:term:max
    bad:term:max rejected:term:max : term =>
  `({ actual := $actual
      bridge := Iff.rfl
      variation := ⟨$source, $bad, $rejected⟩
      sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
        ($arena).Law $actual $bad $rejected
      dependence := fun _ => $witness })

local macro "bindSource% " unit:term:max familyName:term:max arena:term:max family:term:max
    actual:term:max coordinates:term:max path:term:max state:term:max function:term:max
    operand:term:max : term =>
  `({ unitName := $unit
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$arena⟩
      objectArena := .source ⟨$arena⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $arena ⟨$family⟩
      correspondence := { stage := .evidence, objectStage := .evidence }
      bundleNonempty := .absent
      readout := some $actual
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
        definition := none
        coordinates := $coordinates
        readouts := #[{
          path := $path
          stateBinder := $state
          functionOperand := $function
          stateOperand := $operand
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

private abbrev Pion := Fin 3 → ℝ

private def axis : Pion := ![1, 0, 0]

private def piDirection : Pion := ![0, 0, Real.pi]

abbrev groupReadout : Signature := signature SU2 (fun _ => SU2) (fun _ => SU2)

abbrev matrixReadout : Signature := signature ℝ (fun _ => Pion) (fun _ => CMat2)

abbrev pauliReadout : Signature := signature Unit (fun _ => Pion) (fun _ => CMat2)

abbrev potentialReadout : Signature :=
  signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => SU2) (fun _ => ℝ)

abbrev lineReadout : Signature := signature (Σ _ : ℝ, Pion) (fun _ => ℝ) (fun _ => CMat2)

abbrev scalarReadout : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ)

abbrev colorReadout : Signature := signature ℝ (fun _ => ℝ) (fun _ => ℝ)

abbrev twoRealReadout : Signature := signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

private def eraseGroup : Realization groupReadout :=
  realize groupReadout (fun _ _ _ => 1) (fun e => nomatch e)

private def eraseMatrix (A : CMat2) : Realization matrixReadout :=
  realize matrixReadout (fun _ _ _ => A) (fun e => nomatch e)

private def erasePauli : Realization pauliReadout :=
  realize pauliReadout (fun _ _ _ => 0) (fun e => nomatch e)

private def erasePotential : Realization potentialReadout :=
  realize potentialReadout (fun _ _ _ => -3) (fun e => nomatch e)

private def eraseLine : Realization lineReadout :=
  realize lineReadout (fun _ _ _ => 1) (fun e => nomatch e)

private def eraseScalar (c : ℝ) : Realization scalarReadout :=
  realize scalarReadout (fun _ _ _ => c) (fun e => nomatch e)

private def eraseColor (c : ℝ) : Realization colorReadout :=
  realize colorReadout (fun _ _ _ => c) (fun e => nomatch e)

private def eraseTwoReal (c : ℝ) : Realization twoRealReadout :=
  realize twoRealReadout (fun _ _ _ => c) (fun e => nomatch e)

private theorem field_pi : chiralField 1 piDirection = -(1 : CMat2) := by
  have hp : pionNorm piDirection = Real.pi := by
    norm_num [pionNorm, piDirection, Real.sqrt_sq_eq_abs, abs_of_pos Real.pi_pos]
  have hs : Real.sinc Real.pi = 0 := by
    rw [Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div]
  simp [chiralField, hp, hs]

private def negativeIdentity : SU2 :=
  ⟨chiralField 1 piDirection, chiralField_mem_su2 one_ne_zero piDirection⟩

private theorem negative_ne_one : negativeIdentity ≠ 1 := by
  intro h
  have hh := congrArg (fun U : SU2 => (U : CMat2) 0 0) h
  change chiralField 1 piDirection 0 0 = 1 at hh
  norm_num [field_pi, Matrix.one_apply] at hh

private theorem group_varies :
    chiralAct 1 1 1 ≠ chiralAct 1 negativeIdentity 1 := by
  simpa [chiralAct, eq_comm] using negative_ne_one

private theorem field_varies : chiralField 1 0 ≠ chiralField 1 piDirection := by
  intro h
  have hh := congrArg (fun A : CMat2 => A 0 0) h
  norm_num [field_pi, chiralField_zero, Matrix.one_apply] at hh

private theorem pauli_varies : pauliPion 0 ≠ pauliPion axis := by
  intro h
  have hh := congrArg (fun A : CMat2 => A 0 1) h
  norm_num [pauliPion, axis] at hh

private theorem potential_identity :
    chiralPotential 1 1 1 1 (1 : CMat2) = -2 := by
  norm_num [chiralPotential, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.mul_one, Matrix.diagonal_apply]

private theorem potential_varies :
    chiralPotential 1 1 1 1 (1 : CMat2) ≠
    chiralPotential 1 1 1 1 (negativeIdentity : CMat2) := by
  change chiralPotential 1 1 1 1 (1 : CMat2) ≠ chiralPotential 1 1 1 1 (chiralField 1 piDirection)
  rw [field_pi, potential_identity]
  norm_num [chiralPotential, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.mul_neg, Matrix.mul_one, Matrix.diagonal_apply]

abbrev stabilizerArena : Arena where
  signature := groupReadout
  Law S := ∀ (L R : SU2),
    S.readout () L R = 1 ↔ L = R

def stabilizerFamily : Registration stabilizerArena (type_of% @chiral_vacuum_stabilizer_iff) :=
  family% stabilizerArena (@chiral_vacuum_stabilizer_iff) (realize groupReadout (fun _ L R => chiralAct L R 1) (fun e => nomatch e))
    (⟨1, 1, negativeIdentity, group_varies⟩)
    (eraseGroup)
    (by
      intro h
      exact negative_ne_one ((h 1 negativeIdentity).1 rfl).symm)

def stabilizerRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiral_vacuum_stabilizer_iff) (Realization groupReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiral_vacuum_stabilizer_iff.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.stabilizerFamily
    stabilizerArena stabilizerFamily (realize groupReadout (fun _ L R => chiralAct L R 1) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "fn", "arg"] 1 false none

abbrev orbitArena : Arena where
  signature := groupReadout
  Law S := ∀ (U : SU2),
    ∃ L R : SU2, S.readout () L R = U

def orbitFamily : Registration orbitArena (type_of% @chiral_orbit_transitive) :=
  family% orbitArena (@chiral_orbit_transitive) (realize groupReadout (fun _ L R => chiralAct L R 1) (fun e => nomatch e))
    (⟨1, 1, negativeIdentity, group_varies⟩)
    (eraseGroup)
    (by
      intro h
      obtain ⟨L, R, hLR⟩ := h negativeIdentity
      exact negative_ne_one hLR.symm)

def orbitRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiral_orbit_transitive) (Realization groupReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiral_orbit_transitive.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.orbitFamily
    orbitArena orbitFamily (realize groupReadout (fun _ L R => chiralAct L R 1) (fun e => nomatch e))
    #[1] #["body", "arg", "body", "arg", "body", "fn", "arg"] 2 false none

abbrev fieldUnitaryArena : Arena where
  signature := matrixReadout
  Law R := ∀ {fπ : ℝ} (_hf : fπ ≠ 0) (π : Fin 3 → ℝ),
    R.readout () fπ π ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ

def fieldUnitaryFamily : Registration fieldUnitaryArena (type_of% @chiralField_mem_su2) :=
  family% fieldUnitaryArena (@chiralField_mem_su2) (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    (⟨1, 0, piDirection, field_varies⟩)
    (eraseMatrix 0)
    (by
      intro h
      have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp (h one_ne_zero 0)).2
      norm_num [eraseMatrix, realize] at hdet)

def fieldUnitaryRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiralField_mem_su2) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiralField_mem_su2.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.fieldUnitaryFamily
    fieldUnitaryArena fieldUnitaryFamily (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    #[0] #["body", "body", "body", "arg"] 2 false none

abbrev fieldOriginArena : Arena where
  signature := matrixReadout
  Law R := ∀ (fπ : ℝ),
    R.readout () fπ 0 = 1

def fieldOriginFamily : Registration fieldOriginArena (type_of% @chiralField_zero) :=
  family% fieldOriginArena (@chiralField_zero) (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    (⟨1, 0, piDirection, field_varies⟩)
    (eraseMatrix 0)
    (by
      intro h
      exact zero_ne_one (h 1))

def fieldOriginRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiralField_zero) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiralField_zero.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.fieldOriginFamily
    fieldOriginArena fieldOriginFamily (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    #[0] #["body", "fn", "arg", "fn"] 0 true none

abbrev kineticArena : Arena where
  signature := pauliReadout
  Law R := ∀ {fπ : ℝ} (_hf : 0 < fπ)
    (v : Fin 3 → ℝ),
    HasDerivAt (fun t : ℝ => chiralField fπ (t • v))
      ((Complex.I / (fπ : ℂ)) • R.readout () () v) 0 ∧
    let U' := deriv (fun t : ℝ => chiralField fπ (t • v)) 0
    (fπ ^ 2 / 4) * (U'ᴴ * U').trace.re = (1 / 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

def kineticFamily : Registration kineticArena (type_of% @chiral_kinetic_quadratic_normalization) :=
  family% kineticArena (@chiral_kinetic_quadratic_normalization) (realize pauliReadout (fun _ _ => pauliPion) (fun e => nomatch e))
    (⟨(), 0, axis, pauli_varies⟩)
    (erasePauli)
    (by
      intro h
      have hbad := (h (show (0 : ℝ) < 1 by norm_num) axis).1
      have htrue := (chiral_kinetic_quadratic_normalization (show (0 : ℝ) < 1 by norm_num) axis).1
      have hh := congrArg (fun A : CMat2 => A 0 1) (hbad.unique htrue)
      simp only [erasePauli, realize, smul_zero, Matrix.zero_apply] at hh
      norm_num [pauliPion, axis, smul_eq_mul] at hh
      exact Complex.I_ne_zero hh.symm)

def kineticRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiral_kinetic_quadratic_normalization) (Realization pauliReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiral_kinetic_quadratic_normalization.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.kineticFamily
    kineticArena kineticFamily (realize pauliReadout (fun _ _ => pauliPion) (fun e => nomatch e))
    #[] #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"] 2 false none

abbrev minimumArena : Arena where
  signature := potentialReadout
  Law R := ∀ {B₀ fπ mᵤ m_d : ℝ}
    (_hB : 0 < B₀) (_hf : 0 < fπ) (_hu : 0 < mᵤ) (_hd : 0 < m_d) (U : SU2),
    chiralPotential B₀ fπ mᵤ m_d 1 ≤ R.readout () ⟨B₀, fπ, mᵤ, m_d⟩ U ∧
      (chiralPotential B₀ fπ mᵤ m_d 1 = chiralPotential B₀ fπ mᵤ m_d U ↔
        (U : CMat2) = 1)

def minimumFamily : Registration minimumArena (type_of% @chiralPotential_global_min_at_one) :=
  family% minimumArena (@chiralPotential_global_min_at_one) (realize potentialReadout (fun _ p U => chiralPotential p.1 p.2.1 p.2.2.1 p.2.2.2 U) (fun e => nomatch e))
    (⟨⟨1, 1, 1, 1⟩, 1, negativeIdentity, potential_varies⟩)
    (erasePotential)
    (by
      intro h
      have hpos : (0 : ℝ) < 1 := by norm_num
      have hh := (h hpos hpos hpos hpos 1).1
      norm_num [erasePotential, realize, potential_identity] at hh)

def minimumRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiralPotential_global_min_at_one) (Realization potentialReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiralPotential_global_min_at_one.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.minimumFamily
    minimumArena minimumFamily (realize potentialReadout (fun _ p U => chiralPotential p.1 p.2.1 p.2.2.1 p.2.2.2 U) (fun e => nomatch e))
    #[0, 1, 2, 3] #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"] 8 false none

abbrev hessianArena : Arena where
  signature := lineReadout
  Law R := ∀ {fπ : ℝ} (_hf : 0 < fπ)
    (B₀ mᵤ m_d : ℝ) (v : Fin 3 → ℝ),
    deriv (deriv (fun t : ℝ =>
      chiralPotential B₀ fπ mᵤ m_d (R.readout () ⟨fπ, v⟩ t))) 0 =
        B₀ * (mᵤ + m_d) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

def hessianFamily : Registration hessianArena (type_of% @gmor_exact_hessian) :=
  family% hessianArena (@gmor_exact_hessian) (realize lineReadout (fun _ p t => chiralField p.1 (t • p.2)) (fun e => nomatch e))
    (by
      refine ⟨⟨1, piDirection⟩, 0, 1, ?_⟩
      simpa [realize] using field_varies)
    (eraseLine)
    (by
      intro h
      have hh := h (show (0 : ℝ) < 1 by norm_num) 1 1 1 axis
      norm_num [eraseLine, realize, axis] at hh)

def hessianRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gmor_exact_hessian) (Realization lineReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.gmor_exact_hessian.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.hessianFamily
    hessianArena hessianFamily (realize lineReadout (fun _ p t => chiralField p.1 (t • p.2)) (fun e => nomatch e))
    #[0, 5] #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body", "arg"] 6 false none

abbrev massArena : Arena where
  signature := colorReadout
  Law R := ∀ {fπ : ℝ} (_hf : 0 < fπ) (B₀ mᵤ m_d : ℝ),
    let mPiSq := B₀ * (mᵤ + m_d)
    let condensate := B₀ * fπ ^ 2
    mPiSq * fπ ^ 2 = (mᵤ + m_d) * condensate ∧
      (∀ i : Fin 3, deriv (deriv (fun t : ℝ =>
        chiralPotential B₀ fπ mᵤ m_d (chiralField fπ (t • Pi.single i 1)))) 0 = mPiSq) ∧
      Tendsto (fun massSum : ℝ => R.readout () B₀ massSum) (𝓝 0) (𝓝 0)

def massFamily : Registration massArena (type_of% @gmor_pion_mass_relation) :=
  family% massArena (@gmor_pion_mass_relation) (realize colorReadout (fun _ B₀ massSum => B₀ * massSum) (fun e => nomatch e))
    (⟨1, 0, 1, by norm_num [realize]⟩)
    (eraseColor 1)
    (by
      intro h
      have hbad := (h (show (0 : ℝ) < 1 by norm_num) 1 1 1).2.2
      have hgood : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
      have hh := tendsto_nhds_unique hbad hgood
      norm_num at hh)

def massRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gmor_pion_mass_relation) (Realization colorReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.gmor_pion_mass_relation.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.massFamily
    massArena massFamily (realize colorReadout (fun _ B₀ massSum => B₀ * massSum) (fun e => nomatch e))
    #[2] #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "arg", "body"] 7 false none

abbrev anomalyArena : Arena where
  signature := colorReadout
  Law R := ∀ {Nc : ℝ} (_hNc : Nc ≠ 0),
    R.readout () Nc ((Nc + 1) / (2 * Nc)) = 1

def anomalyFamily : Registration anomalyArena (type_of% @abj_anomaly_free_general_Nc) :=
  family% anomalyArena (@abj_anomaly_free_general_Nc) (realize colorReadout (fun _ Nc Qu => abjTrace Nc Qu (-(Nc - 1) / (2 * Nc))) (fun e => nomatch e))
    (⟨1, 0, 1, by norm_num [realize, abjTrace]⟩)
    (eraseColor 0)
    (by
      intro h
      have hh := h (Nc := 1) one_ne_zero
      norm_num [eraseColor, realize] at hh)

def anomalyRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abj_anomaly_free_general_Nc) (Realization colorReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.abj_anomaly_free_general_Nc.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.anomalyFamily
    anomalyArena anomalyFamily (realize colorReadout (fun _ Nc Qu => abjTrace Nc Qu (-(Nc - 1) / (2 * Nc))) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg"] 0 false (some #["fn", "arg"])

abbrev fixedChargesArena : Arena where
  signature := scalarReadout
  Law R := ∀ (Nc α mPi fπ : ℝ),
    R.readout () () Nc = Nc / 3 ∧
      abjTrace 3 (2 / 3) (-1 / 3) = 1 ∧
      (0 < fπ → pi0GammaGammaWidth α mPi fπ 3 (2 / 3) (-1 / 3) =
        9 * pi0GammaGammaWidth α mPi fπ 1 (2 / 3) (-1 / 3))

def fixedChargesFamily : Registration fixedChargesArena (type_of% @abj_fixed_charges_color_test) :=
  family% fixedChargesArena (@abj_fixed_charges_color_test) (realize scalarReadout (fun _ _ Nc => abjTrace Nc (2 / 3) (-1 / 3)) (fun e => nomatch e))
    (⟨(), 0, 3, by norm_num [realize, abjTrace]⟩)
    (eraseScalar 0)
    (by
      intro h
      have hh := (h 3 0 0 1).1
      norm_num [eraseScalar, realize] at hh)

def fixedChargesRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abj_fixed_charges_color_test) (Realization scalarReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.abj_fixed_charges_color_test.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.fixedChargesFamily
    fixedChargesArena fixedChargesFamily (realize scalarReadout (fun _ _ Nc => abjTrace Nc (2 / 3) (-1 / 3)) (fun e => nomatch e))
    #[] #["body", "body", "body", "body", "fn", "arg", "fn", "arg"] 0 false none

abbrev boundArena : Arena where
  signature := twoRealReadout
  Law R := ∀ (x y z : ℝ),
    6 * |skyrmeBaryon x y z| ≤ skyrmeE2 x y z + R.readout () ⟨x, y⟩ z

def boundFamily : Registration boundArena (type_of% @faddeev_bogomolny_skyrme_bound) :=
  family% boundArena (@faddeev_bogomolny_skyrme_bound) (realize twoRealReadout (fun _ p z => skyrmeE4 p.1 p.2 z) (fun e => nomatch e))
    (⟨⟨1, 1⟩, 0, 1, by norm_num [realize, skyrmeE4]⟩)
    (eraseTwoReal (-1))
    (by
      intro h
      have hh := h 0 0 0
      norm_num [eraseTwoReal, realize, skyrmeE2, skyrmeBaryon] at hh)

def boundRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@faddeev_bogomolny_skyrme_bound) (Realization twoRealReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.faddeev_bogomolny_skyrme_bound.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.boundFamily
    boundArena boundFamily (realize twoRealReadout (fun _ p z => skyrmeE4 p.1 p.2 z) (fun e => nomatch e))
    #[0, 1] #["body", "body", "body", "arg", "arg"] 2 false none

abbrev saturationArena : Arena where
  signature := twoRealReadout
  Law R := ∀ (x y z : ℝ),
    6 * |skyrmeBaryon x y z| = skyrmeE2 x y z + R.readout () ⟨x, y⟩ z ↔
      (x = 0 ∧ y = 0 ∧ z = 0) ∨ (|x| = 1 ∧ |y| = 1 ∧ |z| = 1)

def saturationFamily : Registration saturationArena (type_of% @faddeev_bogomolny_saturation_iff) :=
  family% saturationArena (@faddeev_bogomolny_saturation_iff) (realize twoRealReadout (fun _ p z => skyrmeE4 p.1 p.2 z) (fun e => nomatch e))
    (⟨⟨1, 1⟩, 0, 1, by norm_num [realize, skyrmeE4]⟩)
    (eraseTwoReal 1)
    (by
      intro h
      have hh := h 0 0 0
      norm_num [eraseTwoReal, realize, skyrmeE2, skyrmeBaryon] at hh)

def saturationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@faddeev_bogomolny_saturation_iff) (Realization twoRealReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.faddeev_bogomolny_saturation_iff.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.saturationFamily
    saturationArena saturationFamily (realize twoRealReadout (fun _ p z => skyrmeE4 p.1 p.2 z) (fun e => nomatch e))
    #[0, 1] #["body", "body", "body", "fn", "arg", "arg", "arg"] 2 false none

abbrev sigmaCollapseArena : Arena where
  signature := colorReadout
  Law R := ∀ {E₂ : ℝ} (_h₂ : 0 < E₂),
    StrictAntiOn (R.readout () E₂) (Set.Ioi 0) ∧
      (∀ μ : ℝ, 0 < μ → ∃ ν : ℝ, 0 < ν ∧
        derrickEnergy E₂ 0 ν < derrickEnergy E₂ 0 μ) ∧
      Tendsto (derrickEnergy E₂ 0) atTop (𝓝 0)

def sigmaCollapseFamily : Registration sigmaCollapseArena (type_of% @derrick_no_pure_sigma_soliton) :=
  family% sigmaCollapseArena (@derrick_no_pure_sigma_soliton) (realize colorReadout (fun _ E₂ => derrickEnergy E₂ 0) (fun e => nomatch e))
    (⟨1, 1, 2, by norm_num [realize, derrickEnergy]⟩)
    (eraseColor 1)
    (by
      intro h
      have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
      have h2 : (2 : ℝ) ∈ Set.Ioi 0 := by norm_num
      have hh := (h (show (0 : ℝ) < 1 by norm_num)).1 h1 h2 (by norm_num : (1 : ℝ) < 2)
      norm_num [eraseColor, realize] at hh)

def sigmaCollapseRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@derrick_no_pure_sigma_soliton) (Realization colorReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.derrick_no_pure_sigma_soliton.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.sigmaCollapseFamily
    sigmaCollapseArena sigmaCollapseFamily (realize colorReadout (fun _ E₂ => derrickEnergy E₂ 0) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg", "fn", "arg"] 0 true none

abbrev virialArena : Arena where
  signature := twoRealReadout
  Law R := ∀ {E₂ E₄ : ℝ} (_h₂ : 0 < E₂) (_h₄ : 0 < E₄),
    let μstar := Real.sqrt (E₂ / E₄)
    0 < μstar ∧ E₂ / μstar = E₄ * μstar ∧
      R.readout () ⟨E₂, E₄⟩ μstar = 2 * Real.sqrt (E₂ * E₄) ∧
      ∀ μ : ℝ, 0 < μ → μ ≠ μstar →
        derrickEnergy E₂ E₄ μstar < derrickEnergy E₂ E₄ μ

def virialFamily : Registration virialArena (type_of% @derrick_skyrme_virial_minimum) :=
  family% virialArena (@derrick_skyrme_virial_minimum) (realize twoRealReadout (fun _ p => derrickEnergy p.1 p.2) (fun e => nomatch e))
    (⟨⟨1, 1⟩, 1, 2, by norm_num [realize, derrickEnergy]⟩)
    (eraseTwoReal 0)
    (by
      intro h
      have hpos : (0 : ℝ) < 1 := by norm_num
      have hh := (h hpos hpos).2.2.1
      norm_num [eraseTwoReal, realize] at hh)

def virialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@derrick_skyrme_virial_minimum) (Realization twoRealReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.derrick_skyrme_virial_minimum.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.virialFamily
    virialArena virialFamily (realize twoRealReadout (fun _ p => derrickEnergy p.1 p.2) (fun e => nomatch e))
    #[0, 1] #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"] 0 true none

abbrev fieldExponentialArena : Arena where
  signature := matrixReadout
  Law R := ∀ (fπ : ℝ) (π : Fin 3 → ℝ),
    R.readout () fπ π = NormedSpace.exp ((Complex.I / (fπ : ℂ)) • pauliPion π)

def fieldExponentialFamily : Registration fieldExponentialArena (type_of% @chiralField_eq_exp) :=
  family% fieldExponentialArena (@chiralField_eq_exp) (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    (⟨1, 0, piDirection, field_varies⟩)
    (eraseMatrix 0)
    (by
      intro h
      have hbad : (0 : CMat2) = _ := h 1 0
      have hbase := chiralField_eq_exp 1 0
      exact zero_ne_one (hbad.trans (hbase.symm.trans (chiralField_zero 1))))

def fieldExponentialRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chiralField_eq_exp) (Realization matrixReadout) Unit Unit :=
  bindSource% `D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.chiralField_eq_exp.__information_unit
    `Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D.fieldExponentialFamily
    fieldExponentialArena fieldExponentialFamily (realize matrixReadout (fun _ => chiralField) (fun e => nomatch e))
    #[0] #["body", "body", "fn", "arg"] 1 false none

end

end Reg.D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
