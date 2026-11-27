import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
import D5.S3.Combinatorics.Graph.Chordal.Characterization

/-! Concrete nonflat gains for the unit-quaternion reconstruction bounds. -/

open scoped Quaternion

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds

open SimpleGraph Omega.Geometry.UnitQuaternion Real

noncomputable section

local notation "U" => unitary ℍ[ℝ]

private theorem complete_chordal (n : ℕ) : (⊤ : SimpleGraph (Fin n)).IsChordal := by
  apply IsPEO.isChordal (ord := Fin.val)
  exact ⟨Fin.val_injective, fun _ _ _ _ _ h => h⟩

private theorem complete_clique_bound {n : ℕ} (s : Finset (Fin n))
    (_ : (⊤ : SimpleGraph (Fin n)).IsClique (↑s : Set (Fin n))) : s.card ≤ n := by
  simpa using Finset.card_le_univ s

private def rotation (x : ℝ) : U :=
  ofUnit ⟨cos x, sin x, 0, 0⟩ (by
    have h : ‖(⟨cos x, sin x, 0, 0⟩ : ℍ[ℝ])‖ ^ 2 = 1 := by
      rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
      nlinarith only [sin_sq_add_cos_sq x]
    nlinarith [norm_nonneg (⟨cos x, sin x, 0, 0⟩ : ℍ[ℝ])])

private theorem rotation_distance {x : ℝ} (hx : 0 ≤ x) (hπ : x ≤ π) :
    roundDist (rotation x) 1 = x := by
  unfold roundDist
  change arccos (((↑(rotation x) : ℍ[ℝ]) * star (1 : ℍ[ℝ])).re) = x
  rw [star_one, mul_one]
  exact arccos_cos hx hπ

private def singleEdge {V : Type*} [DecidableEq V] (a b : V) (q : U) (x y : V) : U :=
  if x = a ∧ y = b then q else if x = b ∧ y = a then q⁻¹ else 1

private theorem singleEdge_skew {V : Type*} [DecidableEq V] {a b : V}
    (hab : a ≠ b) (q : U) : (⊤ : SimpleGraph V).SU2Skew (singleEdge a b q) := by
  intro x y hxy
  unfold singleEdge
  split_ifs <;> simp_all

private theorem singleEdge_bound {V : Type*} [DecidableEq V] {a b : V}
    (q : U) {δ : ℝ} (hδ : 0 ≤ δ) (hq : roundDist q 1 ≤ δ) :
    (⊤ : SimpleGraph V).SU2TriangleBound (singleEdge a b q) δ := by
  have hi : roundDist q⁻¹ 1 ≤ δ := by
    simpa only [inv_one] using (round_inv q 1).le.trans hq
  intro x y z hxy hyz hxz
  have hxy' := hxy.ne
  have hyz' := hyz.ne
  have hxz' := hxz.ne
  unfold singleEdge
  split_ifs <;> simp_all [round_comm]

private theorem first_defect {n : ℕ} (hn : 2 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).SU2TriangleBound
      (singleEdge ⟨0, by omega⟩ ⟨1, by omega⟩ (rotation (1 / 10))) (1 / 10) := by
  apply singleEdge_bound _ (by norm_num)
  rw [rotation_distance (by norm_num) (by linarith [pi_gt_three])]

example : (434 / 125 : ℝ) < 7 / 2 ∧ (7 / 2 : ℝ) < 4 ∧ (2 : ℝ) < 434 / 125 := by norm_num

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p ((434 / 125) * (1 / 10)) := by
  apply SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp (complete_chordal _)
    (by
      refine { preconnected := ?_, nonempty := inferInstance }
      intro x y
      rcases eq_or_ne x y with h | h
      · subst y
        exact Reachable.rfl
      · exact (show (⊤ : SimpleGraph (Fin 3)).Adj x y from h).reachable)
    (singleEdge_skew (by decide) _) (by norm_num)
  exact first_defect (by decide)

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (2 * (1 / 10)) :=
  (complete_chordal _).exists_su2_gain_potential_small_defect_two
    (singleEdge_skew (by decide) _) (by norm_num) (by linarith [pi_gt_three]) (first_defect (by decide))

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p ((8 / 5) * (1 / 10)) :=
  (complete_chordal _).exists_su2_gain_potential_small_defect_eight_fifths
    (singleEdge_skew (by decide) _) (by norm_num) le_rfl (first_defect (by decide))

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (min (1 / 10) (π / 2)) :=
  (complete_chordal _).exists_cliqueThree_su2_gain_potential_min
    (singleEdge_skew (by decide) _) (by norm_num) (first_defect (by decide)) complete_clique_bound

example :
    ∃ p : Fin 4 → U, (⊤ : SimpleGraph (Fin 4)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (2 * (1 / 10)) :=
  (complete_chordal _).exists_cliqueFour_su2_gain_potential_two
    (singleEdge_skew (by decide) _) (by norm_num) (first_defect (by decide)) complete_clique_bound

example :
    ∃ p : Fin 5 → U, (⊤ : SimpleGraph (Fin 5)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (π / 2) :=
  (complete_chordal _).exists_cliqueFive_su2_gain_potential_half_pi
    (singleEdge_skew (by decide) _) complete_clique_bound

example : roundDist (singleEdge (0 : Fin 3) 1 (rotation (1 / 10)) 0 1 *
    singleEdge 0 1 (rotation (1 / 10)) 1 2) (singleEdge 0 1 (rotation (1 / 10)) 0 2) = 1 / 10 := by
  simp only [singleEdge]
  norm_num
  exact rotation_distance (by norm_num) (by linarith [pi_gt_three])


open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

private abbrev FitParameters (Radius : Type) :=
  Σ V : Type u, Σ _ : SimpleGraph V, Σ _ : V → V → U, Radius

private abbrev fitSignature (Radius : Type) : Signature where
  Params := FitParameters Radius
  State P := P.1 → U
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def fitReadout {Radius : Type} (radius : Radius → ℝ)
    (P : FitParameters.{u} Radius) (p : P.1 → U) : Bool := by
  classical
  exact decide (P.2.1.SU2Fits P.2.2.1 p (radius P.2.2.2))

private def fitActual {Radius : Type} (radius : Radius → ℝ) : Realization (fitSignature.{u} Radius) :=
  realize _ (fun _ => fitReadout radius) (fun e => nomatch e)

private def fitRejected (Radius : Type) : Realization (fitSignature.{u} Radius) :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

private theorem fit_dependence {Radius : Type} (radius : Radius → ℝ) (t : Radius)
    (h₀ : 0 ≤ radius t) (hπ : radius t < π) :
    ObservationalDependence (fitSignature.{u} Radius) (fitActual radius) := by
  classical
  intro _
  let V := ULift.{u} (Fin 2)
  let x : V := ⟨0⟩
  let y : V := ⟨1⟩
  let P : FitParameters.{u} Radius := ⟨V, ⊤, fun _ _ => 1, t⟩
  let p : V → U := fun a => if a = y then rotation π else 1
  have hxy : x ≠ y := by decide
  refine ⟨P, fun _ => 1, p, ?_⟩
  have good : (⊤ : SimpleGraph V).SU2Fits (fun _ _ => 1) (fun _ => 1) (radius t) := by
    intro a b _
    simpa only [inv_one, mul_one, round_self] using h₀
  have bad : ¬ (⊤ : SimpleGraph V).SU2Fits (fun _ _ => 1) p (radius t) := by
    intro h
    have hres := h x y (show (⊤ : SimpleGraph V).Adj x y from hxy)
    change roundDist 1 ((p x)⁻¹ * p y) ≤ radius t at hres
    simp only [p, ite_eq_right hxy, ite_eq_left rfl, inv_one, one_mul] at hres
    rw [round_comm, rotation_distance pi_pos.le le_rfl] at hres
    exact (not_le_of_gt hπ) hres
  change decide ((⊤ : SimpleGraph V).SU2Fits (fun _ _ => 1) (fun _ => 1) (radius t)) ≠
    decide ((⊤ : SimpleGraph V).SU2Fits (fun _ _ => 1) p (radius t))
  simp [good, bad]


private theorem complete_chordal_lift (n : ℕ) :
    (⊤ : SimpleGraph (ULift.{u} (Fin n))).IsChordal := by
  apply IsPEO.isChordal (ord := fun v => v.down.val)
  exact ⟨Fin.val_injective.comp ULift.down_injective, fun _ _ _ _ _ h => h⟩

private theorem complete_connected_lift : (⊤ : SimpleGraph (ULift.{u} (Fin 3))).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0⟩⟩ }
  intro x y
  rcases eq_or_ne x y with h | h
  · subst y
    exact Reachable.rfl
  · exact (show (⊤ : SimpleGraph (ULift (Fin 3))).Adj x y from h).reachable

private abbrev HemisphereParameters := Σ V : Type u, Σ _ : SimpleGraph V, V → V → U

private abbrev closedHemisphereSignature : Signature where
  Params := HemisphereParameters.{u}
  State P := P.1 → U
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def halfPiReadout (P : HemisphereParameters.{u}) (p : P.1 → U) : Bool := by
  classical
  exact decide (P.2.1.SU2Fits P.2.2 p (π / 2))

private def halfPiActual : Realization closedHemisphereSignature.{u} :=
  realize _ (fun _ => halfPiReadout) (fun e => nomatch e)

private def halfPiRejected : Realization closedHemisphereSignature.{u} :=
  realize _ (fun _ _ _ => false) (fun e => nomatch e)

private theorem halfPi_dependence : ObservationalDependence closedHemisphereSignature.{u} halfPiActual := by
  intro i
  obtain ⟨P, x, y, h⟩ := fit_dependence (fun _ : Unit => π / 2) () (by positivity)
    (by linarith [pi_pos]) i
  exact ⟨⟨P.1, P.2.1, P.2.2.1⟩, x, y, h⟩

private def globalArena : Arena where
  signature := fitSignature.{u} ℝ
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    (_hconn : G.Connected) {g : V → V → U} (_hskew : G.SU2Skew g)
    {δ : ℝ} (_hδ : 0 ≤ δ) (_htri : G.SU2TriangleBound g δ),
    ∃ p : V → U, R.readout () ⟨V, G, g, δ⟩ p = true

private theorem globalRejected : ¬ globalArena.{u}.Law (fitRejected ℝ) := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) complete_connected_lift (fun _ _ => 1) (by simp [SU2Skew])
    0 le_rfl (by simp [SU2TriangleBound, round_self])
  cases hp

def globalFamily : Registration globalArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp.{u})) where
  actual := (fitActual (fun δ => (434 / 125) * δ))
  bridge := by simp only [globalArena, fitActual, fitReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [globalArena, fitActual, fitReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp.{u}),
    (fitRejected ℝ), globalRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨(fitRejected ℝ), fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, globalRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := fit_dependence (fun δ => (434 / 125) * δ) 0 (by norm_num) (by norm_num; linarith [pi_pos])

def globalRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp.{u}) (Realization (fitSignature.{u} ℝ)) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.globalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨globalArena⟩
  objectArena := .source ⟨globalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source globalArena ⟨globalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => fitReadout (fun δ => (434 / 125) * δ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def smallTwoArena : Arena where
  signature := fitSignature.{u} ℝ
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    {g : V → V → U} (_hskew : G.SU2Skew g)
    {δ : ℝ} (_hδ : 0 ≤ δ) (_hsmall : δ ≤ π / 6) (_htri : G.SU2TriangleBound g δ),
    ∃ p : V → U, R.readout () ⟨V, G, g, δ⟩ p = true

private theorem smallTwoRejected : ¬ smallTwoArena.{u}.Law (fitRejected ℝ) := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) (fun _ _ => 1) (by simp [SU2Skew])
    0 le_rfl (by positivity) (by simp [SU2TriangleBound, round_self])
  cases hp

def smallTwoFamily : Registration smallTwoArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_two.{u})) where
  actual := (fitActual (fun δ => 2 * δ))
  bridge := by simp only [smallTwoArena, fitActual, fitReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [smallTwoArena, fitActual, fitReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_two.{u}),
    (fitRejected ℝ), smallTwoRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨(fitRejected ℝ), fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, smallTwoRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := fit_dependence (fun δ => 2 * δ) 0 (by norm_num) (by norm_num; linarith [pi_pos])

def smallTwoRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_two.{u}) (Realization (fitSignature.{u} ℝ)) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_two.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.smallTwoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨smallTwoArena⟩
  objectArena := .source ⟨smallTwoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source smallTwoArena ⟨smallTwoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => fitReadout (fun δ => 2 * δ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def smallEightFifthsArena : Arena where
  signature := fitSignature.{u} ℝ
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    {g : V → V → U} (_hskew : G.SU2Skew g)
    {δ : ℝ} (_hδ : 0 ≤ δ) (_hsmall : δ ≤ 1 / 10) (_htri : G.SU2TriangleBound g δ),
    ∃ p : V → U, R.readout () ⟨V, G, g, δ⟩ p = true

private theorem smallEightFifthsRejected : ¬ smallEightFifthsArena.{u}.Law (fitRejected ℝ) := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) (fun _ _ => 1) (by simp [SU2Skew])
    0 le_rfl (by norm_num) (by simp [SU2TriangleBound, round_self])
  cases hp

def smallEightFifthsFamily : Registration smallEightFifthsArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_eight_fifths.{u})) where
  actual := (fitActual (fun δ => (8 / 5) * δ))
  bridge := by simp only [smallEightFifthsArena, fitActual, fitReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [smallEightFifthsArena, fitActual, fitReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_eight_fifths.{u}),
    (fitRejected ℝ), smallEightFifthsRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨(fitRejected ℝ), fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, smallEightFifthsRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := fit_dependence (fun δ => (8 / 5) * δ) 0 (by norm_num) (by norm_num; linarith [pi_pos])

def smallEightFifthsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_eight_fifths.{u}) (Realization (fitSignature.{u} ℝ)) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_su2_gain_potential_small_defect_eight_fifths.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.smallEightFifthsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨smallEightFifthsArena⟩
  objectArena := .source ⟨smallEightFifthsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source smallEightFifthsArena ⟨smallEightFifthsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => fitReadout (fun δ => (8 / 5) * δ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def cliqueThreeArena : Arena where
  signature := fitSignature.{u} ℝ
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    {g : V → V → U} (_hskew : G.SU2Skew g)
    {δ : ℝ} (_hδ : 0 ≤ δ) (_htri : G.SU2TriangleBound g δ)
    (_hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 3),
    ∃ p : V → U, R.readout () ⟨V, G, g, δ⟩ p = true

private theorem cliqueThreeRejected : ¬ cliqueThreeArena.{u}.Law (fitRejected ℝ) := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) (fun _ _ => 1) (by simp [SU2Skew])
    0 le_rfl (by simp [SU2TriangleBound, round_self])
    (fun s _ => (Finset.card_le_univ s).trans (by simp))
  cases hp

def cliqueThreeFamily : Registration cliqueThreeArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_cliqueThree_su2_gain_potential_min.{u})) where
  actual := (fitActual (fun δ => min δ (π / 2)))
  bridge := by simp only [cliqueThreeArena, fitActual, fitReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [cliqueThreeArena, fitActual, fitReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_cliqueThree_su2_gain_potential_min.{u}),
    (fitRejected ℝ), cliqueThreeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨(fitRejected ℝ), fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, cliqueThreeRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := fit_dependence (fun δ => min δ (π / 2)) 0 (le_min le_rfl (by positivity)) ((min_le_left _ _).trans_lt pi_pos)

def cliqueThreeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_cliqueThree_su2_gain_potential_min.{u}) (Realization (fitSignature.{u} ℝ)) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_cliqueThree_su2_gain_potential_min.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.cliqueThreeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cliqueThreeArena⟩
  objectArena := .source ⟨cliqueThreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cliqueThreeArena ⟨cliqueThreeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => fitReadout (fun δ => min δ (π / 2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def cliqueFourArena : Arena where
  signature := fitSignature.{u} ℝ
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    {g : V → V → U} (_hskew : G.SU2Skew g)
    {δ : ℝ} (_hδ : 0 ≤ δ) (_htri : G.SU2TriangleBound g δ)
    (_hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 4),
    ∃ p : V → U, R.readout () ⟨V, G, g, δ⟩ p = true

private theorem cliqueFourRejected : ¬ cliqueFourArena.{u}.Law (fitRejected ℝ) := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) (fun _ _ => 1) (by simp [SU2Skew])
    0 le_rfl (by simp [SU2TriangleBound, round_self])
    (fun s _ => (Finset.card_le_univ s).trans (by simp))
  cases hp

def cliqueFourFamily : Registration cliqueFourArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_cliqueFour_su2_gain_potential_two.{u})) where
  actual := (fitActual (fun δ => 2 * δ))
  bridge := by simp only [cliqueFourArena, fitActual, fitReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [cliqueFourArena, fitActual, fitReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_cliqueFour_su2_gain_potential_two.{u}),
    (fitRejected ℝ), cliqueFourRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨(fitRejected ℝ), fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, cliqueFourRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := fit_dependence (fun δ => 2 * δ) 0 (by norm_num) (by norm_num; linarith [pi_pos])

def cliqueFourRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_cliqueFour_su2_gain_potential_two.{u}) (Realization (fitSignature.{u} ℝ)) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_cliqueFour_su2_gain_potential_two.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.cliqueFourFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cliqueFourArena⟩
  objectArena := .source ⟨cliqueFourArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cliqueFourArena ⟨cliqueFourFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => fitReadout (fun δ => 2 * δ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private def cliqueFiveArena : Arena where
  signature := closedHemisphereSignature
  Law R := ∀ {V : Type u} {G : SimpleGraph V} [Finite V] (_hG : G.IsChordal)
    {g : V → V → U} (_hskew : G.SU2Skew g)
    (_hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 5),
    ∃ p : V → U, R.readout () ⟨V, G, g⟩ p = true

private theorem cliqueFiveRejected : ¬ cliqueFiveArena.{u}.Law halfPiRejected := by
  intro h
  obtain ⟨p, hp⟩ := @h (ULift.{u} (Fin 3)) ⊤ inferInstance
    (complete_chordal_lift 3) (fun _ _ => 1) (by simp [SU2Skew])
    (fun s _ => (Finset.card_le_univ s).trans (by simp))
  cases hp

def cliqueFiveFamily : Registration cliqueFiveArena.{u} (type_of% (@SimpleGraph.IsChordal.exists_cliqueFive_su2_gain_potential_half_pi.{u})) where
  actual := halfPiActual
  bridge := by simp only [cliqueFiveArena, halfPiActual, halfPiReadout, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [cliqueFiveArena, halfPiActual, halfPiReadout, realize,
    decide_eq_true_eq] using (@SimpleGraph.IsChordal.exists_cliqueFive_su2_gain_potential_half_pi.{u}),
    halfPiRejected, cliqueFiveRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨halfPiRejected, fun j h => (h (@Subsingleton.elim Unit _ j i)).elim, ?_, cliqueFiveRejected⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := halfPi_dependence

def cliqueFiveRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@SimpleGraph.IsChordal.exists_cliqueFive_su2_gain_potential_half_pi.{u}) (Realization closedHemisphereSignature.{u}) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_cliqueFive_su2_gain_potential_half_pi.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds.cliqueFiveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cliqueFiveArena⟩
  objectArena := .source ⟨cliqueFiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cliqueFiveArena ⟨cliqueFiveFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize _ (fun _ => halfPiReadout) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
