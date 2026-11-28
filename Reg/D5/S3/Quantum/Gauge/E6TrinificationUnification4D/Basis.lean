import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open OmegaMath
open _root_.D5.S3.Quantum.Gauge
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem spinorYVaries : Y (spinor 0) ≠ Y (spinor 1) := by
  rw [congrFun spinor_sm_bridge.1 0, congrFun spinor_sm_bridge.1 1]
  norm_num [GaugeUnificationRG4D.sm15Y, GaugeUnificationRG4D.sm15State,
    GaugeUnificationRG4D.weylY]

abbrev spinorSMSignature : Signature := signature Unit (fun _ => Fin 16) (fun _ => ℝ)

abbrev spinorSMArena : Arena where
  signature := spinorSMSignature
  Law R := (R.readout () ()) = Fin.cons 0 GaugeUnificationRG4D.sm15Y ∧
    (fun i : Fin 16 => T3 (spinor i)) = Fin.cons 0 GaugeUnificationRG4D.sm15T3

def spinorSMFamily : Registration spinorSMArena (type_of% (@spinor_sm_bridge)) :=
  e6Family% spinorSMArena (@spinor_sm_bridge) (realize spinorSMSignature (fun _ _ i => Y (spinor i)) (fun e => nomatch e))
    (by
      exact ⟨(), 0, 1, spinorYVaries⟩)
    (realize spinorSMSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := congrFun h.1 0
      norm_num [realize, Fin.cons] at hh)

def spinorSMRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spinor_sm_bridge) (Realization spinorSMSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.spinor_sm_bridge.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.spinorSMFamily
    spinorSMArena spinorSMFamily (realize spinorSMSignature (fun _ _ i => Y (spinor i)) (fun e => nomatch e))
    #[] (e6Path% spinor_sm_bridge Y 1 0) 0 false none

abbrev occupationSignature : Signature := signature Unit (fun _ => Fin 16) (fun _ => ℝ)

abbrev occupationArena : Arena where
  signature := occupationSignature
  Law R := ∀ (i : Fin 16),
    R.readout () () i = SpinorWeights5.hypercharge (SpinorWeights5.evenWeight i).1 ∧
    T3 (spinor i) = SpinorWeights5.t3L (SpinorWeights5.evenWeight i).1 ∧
    Q (spinor i) = SpinorWeights5.electricCharge (SpinorWeights5.evenWeight i).1 ∧
    qChi (spinor i) = SpinorWeights5.xCharge (SpinorWeights5.evenWeight i).1 ∧
    bMinusL (spinor i) = SpinorWeights5.bMinusL (SpinorWeights5.evenWeight i).1

def occupationFamily : Registration occupationArena (type_of% (@spinor_occupation_bridge)) :=
  e6Family% occupationArena (@spinor_occupation_bridge) (realize occupationSignature (fun _ _ i => Y (spinor i)) (fun e => nomatch e))
    (by
      exact ⟨(), 0, 1, spinorYVaries⟩)
    (realize occupationSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := (h 0).1
      have hz := (spinor_occupation_bridge 0).1
      have hy := congrFun spinor_sm_bridge.1 0
      change (1 : ℝ) = _ at hh
      norm_num [Fin.cons] at hy
      linarith)

def occupationRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spinor_occupation_bridge) (Realization occupationSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.spinor_occupation_bridge.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.occupationFamily
    occupationArena occupationFamily (realize occupationSignature (fun _ _ i => Y (spinor i)) (fun e => nomatch e))
    #[] (e6Path% spinor_occupation_bridge Y 1 0) 0 false none

abbrev weightsSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev weightsArena : Arena where
  signature := weightsSignature
  Law R := ∀ (s : E6Rep27),
    R.readout () () s = Y s ∧
    entryT3 (e6_27_equiv_trinif s) = T3 s ∧
    entryT3 (e6_27_equiv_trinif s) + entryY (e6_27_equiv_trinif s) = Q s

def weightsFamily : Registration weightsArena (type_of% (@trinification_weights)) :=
  e6Family% weightsArena (@trinification_weights) (realize weightsSignature (fun _ _ s => entryY (e6_27_equiv_trinif s)) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 0, neutral, ?_⟩
      norm_num [realize, e6_27_equiv_trinif, toEntry, entryY, entryPsi, entryChi,
        entryCartan, HL, HR, fundamental, neutral])
    (realize weightsSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (fundamental 0)).1
      norm_num [realize, fundamental, neutral, Y, cartanWeight, fundamental,
        SU5SO10GrandUnification4D.hyperchargeWeights] at hh)

def weightsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinification_weights) (Realization weightsSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinification_weights.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.weightsFamily
    weightsArena weightsFamily (realize weightsSignature (fun _ _ s => entryY (e6_27_equiv_trinif s)) (fun e => nomatch e))
    #[] (e6Path% trinification_weights entryY 1 0) 0 false none

abbrev extraSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev extraArena : Arena where
  signature := extraSignature
  Law R := ∀ (s : E6Rep27),
    R.readout () () s = qPsi s ∧
    entryChi (e6_27_equiv_trinif s) = qChi s ∧
    entryBMinusL (e6_27_equiv_trinif s) = bMinusL s

def extraFamily : Registration extraArena (type_of% (@trinification_extra_charges)) :=
  e6Family% extraArena (@trinification_extra_charges) (realize extraSignature (fun _ _ s => entryPsi (e6_27_equiv_trinif s)) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 0, neutral, ?_⟩
      norm_num [realize, e6_27_equiv_trinif, toEntry, entryY, entryPsi, entryChi,
        entryCartan, HL, HR, fundamental, neutral])
    (realize extraSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := (h neutral).1
      norm_num [realize, neutral, qPsi] at hh)

def extraRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinification_extra_charges) (Realization extraSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinification_extra_charges.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.extraFamily
    extraArena extraFamily (realize extraSignature (fun _ _ s => entryPsi (e6_27_equiv_trinif s)) (fun e => nomatch e))
    #[] (e6Path% trinification_extra_charges entryPsi 1 0) 0 false none

abbrev colorSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ColorSector)

abbrev colorArena : Arena where
  signature := colorSignature
  Law R := ∀ (s : E6Rep27),
    R.readout () () s = colorSector s ∧
    entryColorLabel (e6_27_equiv_trinif s) = colorLabel s

def colorFamily : Registration colorArena (type_of% (@trinification_color)) :=
  e6Family% colorArena (@trinification_color) (realize colorSignature (fun _ _ s => entryColorSector (e6_27_equiv_trinif s)) (fun e => nomatch e))
    (by
      exact ⟨(), fundamental 0, neutral, by change ColorSector.triplet ≠ .singlet; decide⟩)
    (realize colorSignature (fun _ _ _ => .singlet) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (fundamental 0)).1
      change ColorSector.singlet = ColorSector.triplet at hh
      cases hh)

def colorRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinification_color) (Realization colorSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinification_color.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.colorFamily
    colorArena colorFamily (realize colorSignature (fun _ _ s => entryColorSector (e6_27_equiv_trinif s)) (fun e => nomatch e))
    #[] (e6Path% trinification_color entryColorSector 1 0) 0 false none

abbrev contentSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ColorSector)

abbrev contentArena : Arena where
  signature := contentSignature
  Law R := (Finset.univ.filter fun s : E6Rep27 => R.readout () () s = .triplet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .antitriplet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .singlet).card = 9 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .triplet).card / 3 = 3 ∧
    (Finset.univ.filter fun s : E6Rep27 => colorSector s = .antitriplet).card / 3 = 3

def contentFamily : Registration contentArena (type_of% (@color_content)) :=
  e6Family% contentArena (@color_content) (realize contentSignature (fun _ _ => colorSector) (fun e => nomatch e))
    (by
      exact ⟨(), fundamental 0, neutral, by change ColorSector.triplet ≠ .singlet; decide⟩)
    (realize contentSignature (fun _ _ _ => .singlet) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      change (Finset.univ.filter fun _ : E6Rep27 => ColorSector.singlet = .triplet).card = 9 at hh
      norm_num at hh)

def contentRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@color_content) (Realization contentSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.color_content.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.contentFamily
    contentArena contentFamily (realize contentSignature (fun _ _ => colorSector) (fun e => nomatch e))
    #[] (e6Path% color_content colorSector 0 0) 0 true none

abbrev diagonalSignature : Signature := signature Unit (fun _ => Fin 3) (fun _ => ℝ)

abbrev diagonalArena : Arena where
  signature := diagonalSignature
  Law R := Matrix.trace (Matrix.diagonal (R.readout () ())) = 0 ∧
    Matrix.trace (Matrix.diagonal HR) = 0 ∧
    Matrix.trace (Matrix.diagonal T3L) = 0 ∧ HR = HL - T3L

def diagonalFamily : Registration diagonalArena (type_of% (@trinification_diagonal_generators)) :=
  e6Family% diagonalArena (@trinification_diagonal_generators) (realize diagonalSignature (fun _ _ => HL) (fun e => nomatch e))
    (by
      exact ⟨(), 0, 2, by norm_num [realize, HL]⟩)
    (realize diagonalSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      norm_num [realize, Matrix.trace_diagonal, Fin.sum_univ_three] at hh)

def diagonalRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinification_diagonal_generators) (Realization diagonalSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinification_diagonal_generators.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.diagonalFamily
    diagonalArena diagonalFamily (realize diagonalSignature (fun _ _ => HL) (fun e => nomatch e))
    #[] (e6Path% trinification_diagonal_generators HL 0 0) 0 true none

end
abbrev stateCardSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

def stateCardErased : Realization stateCardSignature :=
  realize stateCardSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev stateCardArena : Arena where
  signature := stateCardSignature
  Law R := Fintype.card E6Rep27 = 27 ∧ ∀ s, R.readout () () s ∈ ({1, -2, 4} : Set ℝ)

def stateCardFamily : Registration stateCardArena (type_of% (@state_card)) :=
  e6Family% stateCardArena (@state_card)
    (realize stateCardSignature (fun _ _ s => qPsi s) (fun e => nomatch e))
    (by
      refine ⟨(), spinor 0, neutral, ?_⟩
      norm_num [realize, qPsi, spinor, neutral])
    stateCardErased
    (by
      intro h
      have hn : (0 : ℝ) ∈ ({1, -2, 4} : Set ℝ) := h.2 (spinor 0)
      norm_num at hn)

def stateCardRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@state_card) (Realization stateCardSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.state_card.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.stateCardFamily
    stateCardArena stateCardFamily
    (realize stateCardSignature (fun _ _ s => qPsi s) (fun e => nomatch e))
    #[] (e6Path% state_card qPsi 1 0) 0 false none

abbrev dimensionSignature : Signature := signature Trinif27 (fun _ => E6Rep27) (fun _ => ℂ)

def dimensionErased : Realization dimensionSignature :=
  realize dimensionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev dimensionArena : Arena where
  signature := dimensionSignature
  Law R := Module.finrank ℂ Trinif27 = 27 ∧
    ∀ x y : Trinif27, (∀ s : E6Rep27,
      R.readout () x s = matrixEntry y (e6_27_equiv_trinif s)) ↔ x = y

def dimensionFamily : Registration dimensionArena (type_of% (@trinif_dimension)) :=
  e6Family% dimensionArena (@trinif_dimension)
    (realize dimensionSignature (fun _ x s => matrixEntry x (e6_27_equiv_trinif s))
      (fun e => nomatch e))
    (by
      refine ⟨(1, 0, 0), spinor 2, neutral, ?_⟩
      change (1 : TrinifMatrix) 0 0 ≠ (0 : TrinifMatrix) 2 2
      simp)
    dimensionErased
    (by
      intro h
      have hz (e : Entry) : (0 : ℂ) = matrixEntry (0, 0, 0) e := by
        rcases e with ⟨_, _⟩ | (⟨_, _⟩ | ⟨_, _⟩) <;> rfl
      have he := (h.2 (1, 0, 0) (0, 0, 0)).mp (fun s => hz (e6_27_equiv_trinif s))
      have hn := congrArg (fun x : Trinif27 => x.1 0 0) he
      change (1 : TrinifMatrix) 0 0 = 0 at hn
      simp at hn)

def dimensionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinif_dimension) (Realization dimensionSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinif_dimension.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis.dimensionFamily
    dimensionArena dimensionFamily
    (realize dimensionSignature (fun _ x s => matrixEntry x (e6_27_equiv_trinif s))
      (fun e => nomatch e))
    #[0] (e6Path% trinif_dimension matrixEntry 2 0) 2 false none

end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Basis
