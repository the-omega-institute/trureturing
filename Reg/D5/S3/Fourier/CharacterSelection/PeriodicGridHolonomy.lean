import D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
open LeanInformationAudit
open Lean Meta

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N + 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Fintype.card {y : EdgeLabel M N // Flat y} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using flat_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  have hc := flat_label_card 1 1
  change Fintype.card {y : EdgeLabel 1 1 // Flat y} = 0 at hh
  rw [hc] at hh
  exact (by decide : 2 ^ (1 * 1 + 1) ≠ 0) hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (2 ^ (1 * 1 + 1) : ℕ) ≠ 2 ^ (1 * 2 + 1)
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_label_card
  in arena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N + 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

def dimensionActual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => M * N + 1) (fun e => nomatch e)

def dimensionRejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0) (fun e => nomatch e)

def dimensionArena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Module.finrank (ZMod 2) (LinearMap.range (plaquetteLinear M N)) = M * N - 1 ∧
    Module.finrank (ZMod 2) (flatSubspace M N) = R.readout () M N ∧
    0 < (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) ∧
    0 < (Fintype.card (EdgeLabel M N) : ℚ) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) = 1 / 4 ∧
    (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N - 1) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N + 1)

theorem dimension_actual_law : dimensionArena.Law dimensionActual := by
  intro M N _ _
  simpa [dimensionArena, dimensionActual, realize, signature] using
    periodic_grid_linear_statistics M N

theorem dimension_rejected_law : ¬ dimensionArena.Law dimensionRejected := by
  intro h
  have hh := (h 1 1).2.1
  have hc := (periodic_grid_linear_statistics 1 1).2.1
  change Module.finrank (ZMod 2) (flatSubspace 1 1) = 0 at hh
  norm_num at hc
  omega

theorem dimension_sensitivity_proof : Sensitivity dimensionArena dimensionActual := by
  constructor
  · intro i
    refine ⟨dimensionRejected, ?_, rfl, dimension_rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dimension_dependence_proof : ObservationalDependence signature dimensionActual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [dimensionActual, realize, signature]

def dimensionRegistration : Registration dimensionArena (dimensionArena.Law dimensionActual) where
  actual := dimensionActual
  bridge := Iff.rfl
  variation := ⟨dimension_actual_law, dimensionRejected, dimension_rejected_law⟩
  sensitivity := dimension_sensitivity_proof
  dependence := dimension_dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.periodic_grid_linear_statistics
  in dimensionArena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => M * N + 1)
    (fun e => nomatch e))
  realizes dimensionRegistration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

namespace HolonomyConstant

abbrev signature : Signature where
  Params := Σ M : ℕ, Σ N : ℕ, EdgeLabel M N
  State := fun p => Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => rowHolonomy p.2.2 i)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y),
    (∀ i, R.readout () ⟨M, N, y⟩ i = rowHolonomy y 0) ∧
      (∀ j, columnHolonomy y j = columnHolonomy y 0)

theorem actual_law : arena.Law actual := by
  intro M N _ _ y hy
  simpa [actual, realize, signature] using flat_holonomy_constant y hy

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let y : EdgeLabel 1 1 := ⟨fun _ _ => 0, fun _ _ => 0⟩
  have hy : Flat y := by intro i j; simp [plaquette, y]
  have hh := (h y hy).1 0
  norm_num [rejected, realize, rowHolonomy, y] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨2, 1, ⟨(fun i _ => if i = 0 then 0 else 1), fun _ _ => 0⟩⟩,
    0, 1, ?_⟩
  norm_num [actual, realize, rowHolonomy]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.flat_holonomy_constant
  in arena
  readout via (realize signature (fun _ p i => rowHolonomy p.2.2 i)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

end HolonomyConstant

namespace EdgeCardinality

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (2 * M * N))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ M N : ℕ, Fintype.card (EdgeLabel M N) = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N
  simpa [actual, realize, signature] using edge_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  rw [edge_label_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.edge_label_card
  in arena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (2 * M * N))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end EdgeCardinality

namespace AnchoredVertexCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ M N : ℕ, [NeZero M] → [NeZero N] →
    Fintype.card {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using anchored_vertex_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : NeZero 1 := inferInstance
  have hh := h 1 1
  rw [anchored_vertex_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.anchored_vertex_card
  in arena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end AnchoredVertexCard

namespace HolonomySectorCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N] (h v : ZMod 2),
    Fintype.card {y : EdgeLabel M N // Flat y ∧ rowHolonomy y 0 = h ∧
      columnHolonomy y 0 = v} = R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _ h v
  simpa [actual, realize, signature] using holonomy_sector_card M N h v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 0 0
  rw [holonomy_sector_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.holonomy_sector_card
  in arena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end HolonomySectorCard

namespace ExactLabelCard

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ _ : ℕ) => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (M N : ℕ) [NeZero M] [NeZero N],
    Fintype.card {y : EdgeLabel M N // ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} =
      R.readout () M N

theorem actual_law : arena.Law actual := by
  intro M N _ _
  simpa [actual, realize, signature] using exact_label_card M N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  rw [exact_label_card] at hh
  norm_num [rejected, realize, signature] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨2, 0, 1, ?_⟩
  decide

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.exact_label_card
  in arena
  readout via (realize signature (fun (_ : Unit) (M N : ℕ) => 2 ^ (M * N - 1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end ExactLabelCard

namespace SeamHolonomy

abbrev signature : Signature where
  Params := Σ M : ℕ, Σ N : ℕ, ZMod 2
  State := fun _ => ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M N : ℕ} [NeZero M] [NeZero N] (h v : ZMod 2),
    (∀ i, rowHolonomy (seam (M := M) (N := N) h v) i = h) ∧
      (∀ j, columnHolonomy (seam (M := M) (N := N) h v) j =
        R.readout () ⟨M, N, h⟩ v)

theorem actual_law : arena.Law actual := by
  intro M N _ _ h v
  simpa [actual, realize, signature] using seam_holonomy h v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (M := 1) (N := 1) 0 1).2 0
  norm_num [rejected, realize, seam, columnHolonomy] at hh

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 1, 0⟩, 0, 1, ?_⟩
  exact zero_ne_one

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy.seam_holonomy
  in arena
  readout via (realize signature (fun _ _ v => v) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg",
        "body", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

end SeamHolonomy

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof
#print axioms dimension_actual_law
#print axioms dimension_rejected_law
#print axioms dimension_sensitivity_proof
#print axioms dimension_dependence_proof
#print axioms HolonomyConstant.registration
#print axioms EdgeCardinality.registration
#print axioms AnchoredVertexCard.registration
#print axioms HolonomySectorCard.registration
#print axioms ExactLabelCard.registration
#print axioms SeamHolonomy.registration

end Reg.D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
