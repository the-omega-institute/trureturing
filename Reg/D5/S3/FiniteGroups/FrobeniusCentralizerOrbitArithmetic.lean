import D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic
import Reg.Support.DependentFamily

/-! Exact source reconstruction for a parameter-only dependent-family audit.
The unit-state encoding has no actual observational dependence, so these
bridges do not constitute a four-slot registration. -/

namespace Reg.D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic
open _root_.D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u v

structure ActionParams where
  G : Type u
  X : Type v
  group : Group G
  action : MulAction G X
  hfixed : ∀ g : G, g ≠ 1 → ∀ x y : X,
    g • x = x → g • y = y → x = y
  d : G
  hd : ∀ x : X, d • x ≠ x

attribute [instance] ActionParams.group ActionParams.action

structure FreeParams extends ActionParams.{u,v} where
  c : Subgroup.centralizer ({d} : Set G)
  hc : c ≠ 1
  x : X

structure CardParams extends ActionParams.{u,v} where
  finiteG : Finite G
  finiteX : Finite X

abbrev freeSignature : Signature where
  Params := FreeParams.{u,v}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.X
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def freeActual : Realization freeSignature.{u,v} :=
  realize freeSignature (fun _ p _ => p.c • p.x) (fun e => nomatch e)

abbrev freeArena : Arena where
  signature := freeSignature.{u,v}
  Law R := ∀ p, R.readout () p () ≠ p.x

theorem free_reconstruction :
    (type_of% (@centralizer_smul_ne_self_of_ne_one.{u,v})) ↔
      freeArena.{u,v}.Law freeActual.{u,v} := by
  constructor
  · intro h p
    exact h p.hfixed p.hd p.c p.hc p.x
  · intro h G X _ _ hfixed d hd c hc x
    exact h ⟨⟨G, X, inferInstance, inferInstance, hfixed, d, hd⟩, c, hc, x⟩

theorem free_positive : freeArena.{u,v}.Law freeActual.{u,v} :=
  free_reconstruction.mp (@centralizer_smul_ne_self_of_ne_one.{u,v})

theorem free_no_unit_state_dependence :
    ¬ ObservationalDependence freeSignature.{u,v} freeActual.{u,v} := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy (by cases x; cases y; rfl)

abbrev cardSignature : Signature where
  Params := CardParams.{u,v}
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def cardActual : Realization cardSignature.{u,v} :=
  realize cardSignature
    (fun _ p _ => Nat.card (Subgroup.centralizer ({p.d} : Set p.G)))
    (fun e => nomatch e)

abbrev cardArena : Arena where
  signature := cardSignature.{u,v}
  Law R := ∀ p, R.readout () p () ∣ Nat.card p.X

theorem card_reconstruction :
    (type_of% (@card_centralizer_dvd_card.{u,v})) ↔
      cardArena.{u,v}.Law cardActual.{u,v} := by
  constructor
  · intro h p
    letI := p.finiteG
    letI := p.finiteX
    exact h p.hfixed p.hd
  · intro h G X _ _ _ _ hfixed d hd
    exact h ⟨⟨G, X, inferInstance, inferInstance, hfixed, d, hd⟩,
      inferInstance, inferInstance⟩

theorem card_positive : cardArena.{u,v}.Law cardActual.{u,v} :=
  card_reconstruction.mp (@card_centralizer_dvd_card.{u,v})

theorem card_no_unit_state_dependence :
    ¬ ObservationalDependence cardSignature.{u,v} cardActual.{u,v} := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy (by cases x; cases y; rfl)

#print axioms free_reconstruction
#print axioms free_positive
#print axioms free_no_unit_state_dependence
#print axioms card_reconstruction
#print axioms card_positive
#print axioms card_no_unit_state_dependence
end Reg.D5.S3.FiniteGroups.FrobeniusCentralizerOrbitArithmetic
