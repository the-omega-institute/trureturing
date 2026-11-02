import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ColoredMatchingSwitch

/-! A dependent-family audit of the actual finite colored matching count law. -/

set_option autoImplicit false
namespace Reg.D5.S3.Topology.ColoredMatchingSwitch
open _root_.D5.S3.Topology.ColoredMatchingSwitch
open _root_.D5.S3.Combinatorics.PerfectMatchings
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv
universe u
noncomputable section

structure Inputs where
  V : Type u
  finite : Finite V

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := Perm P.V × Perm P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ st => Nat.card (Circle st.1 st.2)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs) (s t tPrime : Perm P.V),
    Function.Involutive s → Function.Involutive t → Function.Involutive tPrime →
    (∀ x, s x ≠ x) → (∀ x, t x ≠ x) → (∀ x, tPrime x ≠ x) →
    ∀ (a b c d : P.V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    t a = b → t c = d → tPrime a = c → tPrime b = d →
    (∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → tPrime x = t x) →
    |(R.readout () P (s,tPrime) : ℤ) - (R.readout () P (s,t) : ℤ)| ≤ 1 ∧
    (¬ Reach s t a c →
      (R.readout () P (s,tPrime) : ℤ) = (R.readout () P (s,t) : ℤ) - 1)

abbrev sourceScope := type_of% (@colored_switch_circle_count.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual := by
  constructor
  · intro h P
    exact @h P.V P.finite
  · intro h V hV
    exact h ⟨V,hV⟩

private abbrev J := FiniteBandSwitch.FourEndpoint.J0
private abbrev K := FiniteBandSwitch.FourEndpoint.thirdPairing
private theorem j_involutive : Function.Involutive J := by intro i; fin_cases i <;> rfl
private theorem k_involutive : Function.Involutive K := by intro i; fin_cases i <;> rfl
private theorem j_free : ∀ i, J i ≠ i := by
  intro i; fin_cases i <;>
    simp [J,FiniteBandSwitch.FourEndpoint.J0,Perm.mul_apply,swap_apply_def]
private theorem k_free : ∀ i, K i ≠ i := by
  intro i; fin_cases i <;>
    simp [K,FiniteBandSwitch.FourEndpoint.thirdPairing,Perm.mul_apply,swap_apply_def]
private theorem different : ¬ Reach J J 0 1 := by
  rw [reach_iff_matchingConnected J J j_involutive j_involutive,
    InvolutionOrbitSplit.connected_iff_rotation_orbits J J j_involutive j_involutive,
    FiniteEndpointPairing.square_of_involutive J j_involutive]
  simp [J,FiniteBandSwitch.FourEndpoint.J0,Perm.mul_apply,swap_apply_def]
private theorem outside : ∀ x : Fin 4, x ≠ 0 → x ≠ 2 → x ≠ 1 → x ≠ 3 → K x = J x := by
  intro x; fin_cases x <;> simp

private def witness : Inputs.{u} := ⟨ULift.{u} (Fin 4),inferInstance⟩

/-- Relabeling preserves the full count law, so a failure already occurs at
four darts in every universe. -/
private theorem law_forces_dependence (R : Realization signature.{u})
    (h : arena.Law R) :
    ∃ (P : Inputs) (x y : Perm P.V × Perm P.V), R.readout () P x ≠ R.readout () P y := by
  let e : Fin 4 ≃ ULift.{u} (Fin 4) := Equiv.ulift.symm
  let j := e.permCongr J
  let k := e.permCongr K
  have hj : Function.Involutive j := by
    intro x
    change e (J (e.symm (e (J (e.symm x))))) = x
    rw [e.symm_apply_apply,j_involutive,e.apply_symm_apply]
  have hk : Function.Involutive k := by
    intro x
    change e (K (e.symm (e (K (e.symm x))))) = x
    rw [e.symm_apply_apply,k_involutive,e.apply_symm_apply]
  have jf : ∀ x, j x ≠ x := by
    intro x hx
    apply j_free (e.symm x)
    simpa [j] using congrArg e.symm hx
  have kf : ∀ x, k x ≠ x := by
    intro x hx
    apply k_free (e.symm x)
    simpa [k] using congrArg e.symm hx
  have hd : ¬ Reach j j (e 0) (e 1) := by
    rw [reach_iff_matchingConnected j j hj hj,
      InvolutionOrbitSplit.connected_iff_rotation_orbits j j hj hj,
      FiniteEndpointPairing.square_of_involutive j hj]
    simp [j,e,J,FiniteBandSwitch.FourEndpoint.J0,Perm.mul_apply,swap_apply_def]
  have ho : ∀ x, x ≠ e 0 → x ≠ e 2 → x ≠ e 1 → x ≠ e 3 → k x = j x := by
    intro x h0 h2 h1 h3
    obtain ⟨i,rfl⟩ := e.surjective x
    fin_cases i <;> contradiction
  have hh := (h witness j j k hj hj hk jf jf kf (e 0) (e 2) (e 1) (e 3)
    (e.injective.ne (by decide)) (e.injective.ne (by decide))
    (e.injective.ne (by decide)) (e.injective.ne (by decide))
    (e.injective.ne (by decide)) (e.injective.ne (by decide))
    rfl rfl rfl rfl ho).2 hd
  refine ⟨witness,(j,j),(j,k),?_⟩
  intro he
  rw [he] at hh
  omega

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨P,x,y,hxy⟩ := law_forces_dependence rejected h
  exact hxy rfl

theorem actual_positive : arena.{u}.Law actual := source_bridge.mp colored_switch_circle_count

def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    cases i
    exact law_forces_dependence actual actual_positive

noncomputable def countRegistration :
    LeanInformationAudit.Contract.Registration
      (@colored_switch_circle_count.{u}) (Realization signature.{u}) (Type (u+1)) Unit where
  unitName := `D5.S3.Topology.ColoredMatchingSwitch.colored_switch_circle_count.__information_unit
  realizationName := `Reg.D5.S3.Topology.ColoredMatchingSwitch.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ st => Nat.card (Circle st.1 st.2))
    (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some (Σ P : Inputs.{u}, Perm P.V × Perm P.V)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms countRegistration

end
end Reg.D5.S3.Topology.ColoredMatchingSwitch
