import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
open _root_.MatchingCliqueCycle
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open SimpleGraph

noncomputable section

namespace Distance
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Σ m : ℕ, Σ t : ℕ, Vertex m t × Vertex m t
  State p := Matchings p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p M => (graph M).dist p.2.2.1 p.2.2.2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {m t : ℕ} (M : Matchings m t) (x y : Vertex m t),
    (cycleGraph (m + 3)).dist x.1 y.1 ≤ R.readout () ⟨m, t, x, y⟩ M ∧
    R.readout () ⟨m, t, x, y⟩ M ≤ (cycleGraph (m + 3)).dist x.1 y.1 + 1

private def identity : Matchings 0 0 := fun _ => Equiv.refl _
private def swapped : Matchings 0 0 := fun _ => Equiv.swap 0 1

private lemma source_law : arena.Law actual := by
  intro m t M x y
  exact distance_bounds M x y

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h identity (0, 0) (1, 0)).1
  change (cycleGraph 3).dist 0 1 ≤ 0 at hh
  have hadj : (cycleGraph 3).Adj 0 1 := by simp [cycleGraph_adj]
  rw [dist_eq_one_iff_adj.mpr hadj] at hh
  omega

private lemma identity_distance : (graph identity).dist (0, 0) (1, 0) = 1 := by
  apply dist_eq_one_iff_adj.mpr
  right; left
  simp [forward, identity]

private lemma swapped_distance : (graph swapped).dist (0, 0) (1, 0) = 2 := by
  have bounds := distance_bounds swapped (0, 0) (1, 0)
  have hadj : (cycleGraph 3).Adj 0 1 := by simp [cycleGraph_adj]
  rw [dist_eq_one_iff_adj.mpr hadj] at bounds
  have hnot : ¬ (graph swapped).Adj (0, 0) (1, 0) := by
    simp [graph, forward, swapped, Equiv.swap_apply_def]
  have hne : (graph swapped).dist (0, 0) (1, 0) ≠ 1 := by
    intro h
    exact hnot (dist_eq_one_iff_adj.mp h)
  omega

def registration : Registration arena
    (∀ {m t : ℕ} (M : Matchings m t) (x y : Vertex m t),
      (cycleGraph (m + 3)).dist x.1 y.1 ≤ (graph M).dist x y ∧
      (graph M).dist x y ≤ (cycleGraph (m + 3)).dist x.1 y.1 + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨0, 0, (0, 0), (1, 0)⟩, identity, swapped, ?_⟩
    change (graph identity).dist (0, 0) (1, 0) ≠ (graph swapped).dist (0, 0) (1, 0)
    rw [identity_distance, swapped_distance]
    omega

def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.MatchingCliqueCycle.distance_bounds)
    (type_of% (realize signature
      (fun _ p M => (graph M).dist p.2.2.1 p.2.2.2) (fun e => nomatch e)))
    (ℕ → ℕ → Type) Unit := {
  unitName := Lean.Name.str (Lean.Name.str `MatchingCliqueCycle.distance_bounds
    "Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle/Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Distance.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Distance.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p M => (graph M).dist p.2.2.1 p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Matchings
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Distance

private def identity_matching : Matchings 0 0 := fun _ => Equiv.refl _

private lemma singleton_top {V : Type} (v : V) :
    WellCoveredPowerCliqueProduct.IsMaximalIndep (⊤ : SimpleGraph V) {v} := by
  constructor
  · intro x hx y hy hxy
    have hx' := Finset.mem_singleton.mp hx
    have hy' := Finset.mem_singleton.mp hy
    exact (hxy (hx'.trans hy'.symm)).elim
  · intro x hx
    refine ⟨v, Finset.mem_singleton_self _, ?_⟩
    intro h
    exact hx (Finset.mem_singleton.mpr h)

private lemma base_power_one : WellCoveredPowerCliqueProduct.power (cycleGraph 3) 1 = ⊤ := by
  ext x y
  by_cases h : x = y <;>
    simp [WellCoveredPowerCliqueProduct.power, cycleGraph_three_eq_top, dist_top, h]

private lemma matching_power_two :
    WellCoveredPowerCliqueProduct.power (graph identity_matching) 2 = ⊤ := by
  ext x y
  constructor
  · intro h; exact h.1
  · intro h
    refine ⟨h, ?_⟩
    have hu := (distance_bounds identity_matching x y).2
    rw [cycleGraph_three_eq_top, dist_top] at hu
    split_ifs at hu <;> omega

private lemma zero_power_univ :
    WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 0)
      (Finset.univ : Finset (Fin 3)) := by
  constructor
  · intro x _ y _ hxy hadj
    have hdist : (cycleGraph 3).dist x y = 0 := Nat.le_zero.mp hadj.2
    exact hxy ((cycleGraph_connected (n := 2)).dist_eq_zero_iff.mp hdist)
  · intro x hx; exact (hx (Finset.mem_univ _)).elim

private lemma zero_spectrum_three :
    3 ∈ spectrum (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 0) :=
  ⟨Finset.univ, zero_power_univ, by simp⟩

private lemma no_three_in_top_spectrum : 3 ∉ spectrum (⊤ : SimpleGraph (Fin 3)) := by
  rintro ⟨I, hI, hc⟩
  have hsmall : I.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne
    exact hI.1 x hx y hy hne hne
  omega

namespace Projection
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Σ m : ℕ, Σ t : ℕ, Matchings m t × ℕ
  State p := Finset (Vertex p.1 p.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin (p.1 + 3))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ I => I.image Prod.fst) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {m t : ℕ} (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {I : Finset (Vertex m t)}
    (hI : WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (graph M) d) I),
    WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (cycleGraph (m + 3)) (d - 1))
      (R.readout () ⟨m, t, M, d⟩ I) ∧ (R.readout () ⟨m, t, M, d⟩ I).card = I.card

private lemma source_law : arena.Law actual := by
  intro m t M d hd I hI
  exact maximal_projection M hd hI

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hs : WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (graph identity_matching) 2) {(0, 0)} := by
    rw [matching_power_two]
    exact singleton_top _
  have hh := (h identity_matching (d := 2) (by omega) hs).1
  change WellCoveredPowerCliqueProduct.IsMaximalIndep _ (∅ : Finset (Fin 3)) at hh
  obtain ⟨v, hv, _⟩ := hh.2 0 (by simp)
  simpa using hv

def registration : Registration arena (type_of% (@_root_.MatchingCliqueCycle.maximal_projection)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    refine ⟨⟨0, 0, identity_matching, 2⟩, {(0, 0)}, {(1, 0)}, ?_⟩
    change Finset.image Prod.fst ({(0, 0)} : Finset (Vertex 0 0)) ≠
      Finset.image Prod.fst {(1, 0)}
    simp
end Projection

namespace Lift
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Σ m : ℕ, Σ t : ℕ, Matchings m t × ℕ
  State p := Finset (Fin (p.1 + 3))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin (p.1 + 3))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {m t : ℕ} (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d)
    {S : Finset (Fin (m + 3))}
    (hS : WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (cycleGraph (m + 3)) (d - 1)) S),
    ∃ I : Finset (Vertex m t), WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (graph M) d) I ∧
      I.image Prod.fst = R.readout () ⟨m, t, M, d⟩ S ∧ I.card = S.card

private lemma source_law : arena.Law actual := by
  intro m t M d hd S hS
  exact maximal_lift M hd hS

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hs : WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (cycleGraph 3) (2 - 1)) {0} := by
    change WellCoveredPowerCliqueProduct.IsMaximalIndep
      (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 1) {0}
    rw [base_power_one]
    exact singleton_top _
  obtain ⟨I, _, he, hc⟩ := h identity_matching (d := 2) (by omega) hs
  change I.image Prod.fst = ∅ at he
  have hi : I = ∅ := Finset.image_eq_empty.mp he
  simp [hi] at hc

def registration : Registration arena (type_of% (@_root_.MatchingCliqueCycle.maximal_lift)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    refine ⟨⟨0, 0, identity_matching, 2⟩, {0}, {1}, ?_⟩
    change ({0} : Finset (Fin 3)) ≠ {1}
    simp
end Lift

namespace Spectrum
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Σ m : ℕ, Σ t : ℕ, Matchings m t
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p d => spectrum (WellCoveredPowerCliqueProduct.power (graph p.2.2) d))
  (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {m t : ℕ} (M : Matchings m t) {d : ℕ} (hd : 1 ≤ d),
    R.readout () ⟨m, t, M⟩ d =
      spectrum (WellCoveredPowerCliqueProduct.power (cycleGraph (m + 3)) (d - 1))

private lemma source_law : arena.Law actual := by
  intro m t M d hd
  exact spectrum_power M hd

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h identity_matching (d := 1) (by omega)
  change (∅ : Set ℕ) = spectrum (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 0) at hh
  have hc := zero_spectrum_three
  rw [← hh] at hc
  exact hc

def registration : Registration arena (type_of% (@_root_.MatchingCliqueCycle.spectrum_power)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    refine ⟨⟨0, 0, identity_matching⟩, 1, 2, ?_⟩
    change spectrum (WellCoveredPowerCliqueProduct.power (graph identity_matching) 1) ≠
      spectrum (WellCoveredPowerCliqueProduct.power (graph identity_matching) 2)
    rw [spectrum_power identity_matching (d := 1) (by omega),
      spectrum_power identity_matching (d := 2) (by omega)]
    change spectrum (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 0) ≠
      spectrum (WellCoveredPowerCliqueProduct.power (cycleGraph 3) 1)
    rw [base_power_one]
    intro he
    apply no_three_in_top_spectrum
    rw [← he]
    exact zero_spectrum_three
end Spectrum

namespace Diameter
abbrev signature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := Σ m : ℕ, Σ t : ℕ, Matchings m t
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => (graph p.2.2).diam) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena.{0,0,0,0,0} where
  signature := signature
  Law R := ∀ {m t : ℕ} (M : Matchings m t),
    R.readout () () ⟨m, t, M⟩ = (m + 3) / 2 + 1

private lemma source_law : arena.Law actual := by
  intro m t M
  exact diameter M

private lemma rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h identity_matching
  change (0 : ℕ) = 2 at hh
  omega

def registration : Registration arena (type_of% (@_root_.MatchingCliqueCycle.diameter)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    refine ⟨(), ⟨0, 0, identity_matching⟩,
      ⟨1, 0, fun _ => Equiv.refl _⟩, ?_⟩
    change (graph identity_matching).diam ≠
      (graph (fun _ : Fin 4 => Equiv.refl (Fin 3))).diam
    rw [diameter, diameter]
    norm_num
end Diameter

namespace Projection
def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.MatchingCliqueCycle.maximal_projection)
    (type_of% (realize signature (fun _ _ I => I.image Prod.fst) (fun e => nomatch e)))
    (Type → Type) Unit := {
  unitName := Lean.Name.str (Lean.Name.str `MatchingCliqueCycle.maximal_projection
    "Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle/Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Projection.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Projection.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ I => I.image Prod.fst) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Finset
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
#print axioms registration
#print axioms contract
end Projection

namespace Lift
def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.MatchingCliqueCycle.maximal_lift)
    (type_of% (realize signature (fun _ _ S => S) (fun e => nomatch e)))
    (Type → Type) Unit := {
  unitName := Lean.Name.str (Lean.Name.str `MatchingCliqueCycle.maximal_lift
    "Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle/Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Lift.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Lift.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Finset
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
#print axioms registration
#print axioms contract
end Lift

namespace Spectrum
def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.MatchingCliqueCycle.spectrum_power)
    (type_of% (realize signature (fun _ p d => spectrum (WellCoveredPowerCliqueProduct.power (graph p.2.2) d)) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `MatchingCliqueCycle.spectrum_power
    "Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle/Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Spectrum.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Spectrum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => spectrum (WellCoveredPowerCliqueProduct.power (graph p.2.2) d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
#print axioms registration
#print axioms contract
end Spectrum

namespace Diameter
def contract : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.MatchingCliqueCycle.diameter)
    (type_of% (realize signature (fun _ _ p => (graph p.2.2).diam) (fun e => nomatch e)))
    Type Unit := {
  unitName := Lean.Name.str (Lean.Name.str `MatchingCliqueCycle.diameter
    "Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle/Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Diameter.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.Diameter.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => (graph p.2.2).diam) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }
#print axioms registration
#print axioms contract
end Diameter

end
end Reg.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
