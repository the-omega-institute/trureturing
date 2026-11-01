import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
import Reg.D5.S3.Geometry.Polygons.PolygonCompressionTrace

/-! Exact source telescopes and dependent readout reconstruction candidates.
These candidates are not Contract.Registration values. SourceSelection binding,
a rejected realization, whole-family intervention sensitivity and actual
observational dependence are not supplied. In particular a law for complete
conditioned counts supplies neither positive fibres nor their variation.
-/

namespace Reg.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace
open _root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
open _root_.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Reg.D5.S3.Geometry.Polygons.PolygonCompressionTrace

abbrev traceState (n : NZ) : Type := by
  letI : NeZero n.1 := ⟨n.2⟩
  exact Σ P : Finset (ZMod n.1), Σ Q : Finset (ZMod n.1),
    Finset (ZMod n.1) × Finset (WholeFiber P Q)

abbrev tracesSignature : Signature where
  Params := NZ
  State := traceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (Finset (ZMod n.1))
  Anchor := Empty
  finiteAnchor := inferInstance

def tracesActual : Realization tracesSignature :=
  realize tracesSignature (fun _ n S => by
    letI : NeZero n.1 := ⟨n.2⟩
    exact familyTraces S.2.2.1 S.2.2.2) (fun e => nomatch e)

abbrev familyTraces_feasible_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.familyTraces_feasible)

theorem familyTraces_feasible_source : familyTraces_feasible_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.familyTraces_feasible

abbrev familyTraces_feasible_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ (hn : 6 ≤ n) (H : Finset (ZMod n))
    {P Q : Finset (ZMod n)} (A : Finset (WholeFiber P Q)),
    familyTraces H A ⊆ feasible H

theorem familyTraces_feasible_bridge : familyTraces_feasible_arena.Law feasibleActual ↔
    familyTraces_feasible_scope := Iff.rfl

theorem familyTraces_feasible_actual_law : familyTraces_feasible_arena.Law feasibleActual :=
  familyTraces_feasible_bridge.mpr familyTraces_feasible_source

abbrev original_card_le_trace_mass_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.original_card_le_trace_mass)

theorem original_card_le_trace_mass_source : original_card_le_trace_mass_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.original_card_le_trace_mass

abbrev original_card_le_trace_mass_arena : Arena where
  signature := weightSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let weight := fun P Q H X : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,X);
    ∀ (P Q H : Finset (ZMod n))
    (A : Finset (WholeFiber P Q)),
    (A.card : ℝ) ≤ mass (weight P Q H) (familyTraces H A)

theorem original_card_le_trace_mass_bridge : original_card_le_trace_mass_arena.Law weightActual ↔
    original_card_le_trace_mass_scope := Iff.rfl

theorem original_card_le_trace_mass_actual_law : original_card_le_trace_mass_arena.Law weightActual :=
  original_card_le_trace_mass_bridge.mpr original_card_le_trace_mass_source

abbrev shared_ear_mem_EK_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.shared_ear_mem_EK)

theorem shared_ear_mem_EK_source : shared_ear_mem_EK_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.shared_ear_mem_EK

abbrev shared_ear_mem_EK_arena : Arena where
  signature := allowedSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let E_K := fun K : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ K;
    ∀ {P Q : Finset (ZMod n)}
    (T : WholeFiber P Q) (U : WholeFiber Q P) {i : ZMod n}
    (hiT : i ∈ EarCenters T.1) (hiU : i ∈ EarCenters U.1),
    i ∈ E_K (P ∪ Q)

theorem shared_ear_mem_EK_bridge : shared_ear_mem_EK_arena.Law allowedActual ↔
    shared_ear_mem_EK_scope := Iff.rfl

theorem shared_ear_mem_EK_actual_law : shared_ear_mem_EK_arena.Law allowedActual :=
  shared_ear_mem_EK_bridge.mpr shared_ear_mem_EK_source

abbrev common_ears_eq_trace_inter_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.common_ears_eq_trace_inter)

theorem common_ears_eq_trace_inter_source : common_ears_eq_trace_inter_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.common_ears_eq_trace_inter

abbrev common_ears_eq_trace_inter_arena : Arena where
  signature := allowedSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let E_K := fun K : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ K;
    ∀ {P Q : Finset (ZMod n)}
    (T : WholeFiber P Q) (U : WholeFiber Q P),
    EarCenters T.1 ∩ EarCenters U.1 =
      (EarCenters T.1 ∩ E_K (P ∪ Q)) ∩ (EarCenters U.1 ∩ E_K (P ∪ Q))

theorem common_ears_eq_trace_inter_bridge : common_ears_eq_trace_inter_arena.Law allowedActual ↔
    common_ears_eq_trace_inter_scope := Iff.rfl

theorem common_ears_eq_trace_inter_actual_law : common_ears_eq_trace_inter_arena.Law allowedActual :=
  common_ears_eq_trace_inter_bridge.mpr common_ears_eq_trace_inter_source

abbrev familyTraces_cross_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.familyTraces_cross)

theorem familyTraces_cross_source : familyTraces_cross_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.familyTraces_cross

abbrev familyTraces_cross_arena : Arena where
  signature := tracesSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    ∀ {P Q : Finset (ZMod n)}
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.1) (EarCenters U.1)),
    CrossIntersecting (O.readout () ⟨n, NeZero.ne n⟩ ⟨P,Q,E_K (P ∪ Q),A⟩) (O.readout () ⟨n, NeZero.ne n⟩ ⟨Q,P,E_K (P ∪ Q),B⟩)

theorem familyTraces_cross_bridge : familyTraces_cross_arena.Law tracesActual ↔
    familyTraces_cross_scope := Iff.rfl

theorem familyTraces_cross_actual_law : familyTraces_cross_arena.Law tracesActual :=
  familyTraces_cross_bridge.mpr familyTraces_cross_source

abbrev exists_original_terminal_compression_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.exists_original_terminal_compression)

theorem exists_original_terminal_compression_source : exists_original_terminal_compression_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression.exists_original_terminal_compression

abbrev exists_original_terminal_compression_arena : Arena where
  signature := weightSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let weight := fun P Q H X : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,X);
    ∀ (hn : 14 ≤ n)
    (P Q : Finset (ZMod n)) (hK : (P ∪ Q).Nonempty)
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.1) (EarCenters U.1)),
    ∃ H : Finset (ZMod n), ∃ C D : Finset (Finset (ZMod n)),
      H ⊆ E_K (P ∪ Q) ∧ Independent H ∧
      (∀ i ∈ H, ∀ j ∈ H, ¬Cross (ear i) (ear j)) ∧
      C ⊆ H.powerset ∧ D ⊆ H.powerset ∧ CrossIntersecting C D ∧
      RelativelyUpper H.powerset C ∧ RelativelyUpper H.powerset D ∧
      (A.card : ℝ) ≤ mass (weight P Q H) C ∧
      (B.card : ℝ) ≤ mass (weight Q P H) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty) ∧
      (A.Nonempty → B.Nonempty → H.Nonempty)

theorem exists_original_terminal_compression_bridge : exists_original_terminal_compression_arena.Law weightActual ↔
    exists_original_terminal_compression_scope := Iff.rfl

theorem exists_original_terminal_compression_actual_law : exists_original_terminal_compression_arena.Law weightActual :=
  exists_original_terminal_compression_bridge.mpr exists_original_terminal_compression_source

end

end Reg.D5.S3.Geometry.Polygons.PolygonSimultaneousCompression
