import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Polygons.PolygonCompressionTrace
import Reg.Support.DependentFamily

/-! Exact source telescopes and dependent readout reconstruction candidates.
These candidates are not Contract.Registration values. SourceSelection binding,
a rejected realization, whole-family intervention sensitivity and actual
observational dependence are not supplied. In particular a law for complete
conditioned counts supplies neither positive fibres nor their variation.
-/

namespace Reg.D5.S3.Geometry.Polygons.PolygonCompressionTrace
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open _root_.D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open _root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace
open _root_.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev independentSignature : Signature where
  Params := ℕ
  State n := Finset (ZMod n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def independentActual : Realization independentSignature :=
  realize independentSignature (fun _ _ H => Independent H) (fun e => nomatch e)

abbrev feasibleSignature : Signature where
  Params := ℕ
  State n := Finset (ZMod n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (Finset (ZMod n))
  Anchor := Empty
  finiteAnchor := inferInstance

def feasibleActual : Realization feasibleSignature :=
  realize feasibleSignature (fun _ _ H => feasible H) (fun e => nomatch e)

abbrev NZ := {n : ℕ // n ≠ 0}

abbrev weightSignature : Signature where
  Params := NZ
  State n := Finset (ZMod n.1) × Finset (ZMod n.1) ×
    Finset (ZMod n.1) × Finset (ZMod n.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ n S => by
    letI : NeZero n.1 := ⟨n.2⟩
    exact weight S.1 S.2.1 S.2.2.1 S.2.2.2) (fun e => nomatch e)

abbrev crossSignature : Signature where
  Params := NZ
  State n := ZMod n.1 × ZMod n.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def crossActual : Realization crossSignature :=
  realize crossSignature (fun _ n S => by
    letI : NeZero n.1 := ⟨n.2⟩
    exact Cross (ear S.1) (ear S.2)) (fun e => nomatch e)

abbrev membershipSignature : Signature where
  Params := ℕ
  State n := Finset (ZMod n) × ZMod n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def membershipActual : Realization membershipSignature :=
  realize membershipSignature (fun _ _ S => S.2 ∈ S.1) (fun e => nomatch e)

abbrev allowedSignature : Signature where
  Params := NZ
  State n := Finset (ZMod n.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (ZMod n.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def allowedActual : Realization allowedSignature :=
  realize allowedSignature (fun _ n K => by
    letI : NeZero n.1 := ⟨n.2⟩
    exact E_K K) (fun e => nomatch e)

abbrev countSignature : Signature where
  Params := NZ
  State n := Finset (ZMod n.1) × Finset (ZMod n.1) ×
    Finset (ZMod n.1) × Finset (ZMod n.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature :=
  realize countSignature (fun _ n S => by
    letI : NeZero n.1 := ⟨n.2⟩
    exact Nat.card (ConditionFiber S.1 S.2.1 S.2.2.1 S.2.2.2)) (fun e => nomatch e)

abbrev mem_feasible_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.mem_feasible)

theorem mem_feasible_source : mem_feasible_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.mem_feasible

abbrev mem_feasible_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ},
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ {H X : Finset (ZMod n)},
    X ∈ feasible H ↔ X ⊆ H ∧ Independent X

theorem mem_feasible_bridge : mem_feasible_arena.Law feasibleActual ↔
    mem_feasible_scope := Iff.rfl

theorem mem_feasible_actual_law : mem_feasible_arena.Law feasibleActual :=
  mem_feasible_bridge.mpr mem_feasible_source

abbrev independent_subset_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.independent_subset)

theorem independent_subset_source : independent_subset_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.independent_subset

abbrev independent_subset_arena : Arena where
  signature := independentSignature
  Law O := ∀ {n : ℕ},
    let Independent := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ {H X : Finset (ZMod n)} (hH : Independent H)
    (hX : X ⊆ H),
    Independent X

theorem independent_subset_bridge : independent_subset_arena.Law independentActual ↔
    independent_subset_scope := Iff.rfl

theorem independent_subset_actual_law : independent_subset_arena.Law independentActual :=
  independent_subset_bridge.mpr independent_subset_source

abbrev cross_ear_iff_adjacent_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.cross_ear_iff_adjacent)

theorem cross_ear_iff_adjacent_source : cross_ear_iff_adjacent_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.cross_ear_iff_adjacent

abbrev cross_ear_iff_adjacent_arena : Arena where
  signature := crossSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    ∀ (hn : 6 ≤ n) (i j : ZMod n),
    O.readout () ⟨n, NeZero.ne n⟩ (i,j) ↔ j = i + 1 ∨ i = j + 1

theorem cross_ear_iff_adjacent_bridge : cross_ear_iff_adjacent_arena.Law crossActual ↔
    cross_ear_iff_adjacent_scope := Iff.rfl

theorem cross_ear_iff_adjacent_actual_law : cross_ear_iff_adjacent_arena.Law crossActual :=
  cross_ear_iff_adjacent_bridge.mpr cross_ear_iff_adjacent_source

abbrev earCenters_independent_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.earCenters_independent)

theorem earCenters_independent_source : earCenters_independent_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.earCenters_independent

abbrev earCenters_independent_arena : Arena where
  signature := independentSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let Independent := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ (hn : 6 ≤ n)
    {T : Finset (Sym2 (ZMod n))} (hT : IsTriangulation T),
    Independent (EarCenters T)

theorem earCenters_independent_bridge : earCenters_independent_arena.Law independentActual ↔
    earCenters_independent_scope := Iff.rfl

theorem earCenters_independent_actual_law : earCenters_independent_arena.Law independentActual :=
  earCenters_independent_bridge.mpr earCenters_independent_source

abbrev block_start_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.block_start)

theorem block_start_source : block_start_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.block_start

abbrev block_start_arena : Arena where
  signature := membershipSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    ∀ (H : Finset (ZMod n)) (hproper : H ≠ Finset.univ),
    (∃ b, O.readout () n (H,b) ∧ O.readout () n (H,b+1)) →
      ∃ a, ¬O.readout () n (H,a) ∧ O.readout () n (H,a+1) ∧ O.readout () n (H,a+2)

theorem block_start_bridge : block_start_arena.Law membershipActual ↔
    block_start_scope := Iff.rfl

theorem block_start_actual_law : block_start_arena.Law membershipActual :=
  block_start_bridge.mpr block_start_source

abbrev trace_mem_feasible_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.trace_mem_feasible)

theorem trace_mem_feasible_source : trace_mem_feasible_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.trace_mem_feasible

abbrev trace_mem_feasible_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (H : Finset (ZMod n)),
    EarCenters T ∩ H ∈ feasible H

theorem trace_mem_feasible_bridge : trace_mem_feasible_arena.Law feasibleActual ↔
    trace_mem_feasible_scope := Iff.rfl

theorem trace_mem_feasible_actual_law : trace_mem_feasible_arena.Law feasibleActual :=
  trace_mem_feasible_bridge.mpr trace_mem_feasible_source

abbrev weight_zero_of_not_feasible_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.weight_zero_of_not_feasible)

theorem weight_zero_of_not_feasible_source : weight_zero_of_not_feasible_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.weight_zero_of_not_feasible

abbrev weight_zero_of_not_feasible_arena : Arena where
  signature := weightSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let weight := fun P Q H X : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,X);
    ∀ (hn : 6 ≤ n)
    (P Q H X : Finset (ZMod n)) (hX : X ∉ feasible H),
    weight P Q H X = 0

theorem weight_zero_of_not_feasible_bridge : weight_zero_of_not_feasible_arena.Law weightActual ↔
    weight_zero_of_not_feasible_scope := Iff.rfl

theorem weight_zero_of_not_feasible_actual_law : weight_zero_of_not_feasible_arena.Law weightActual :=
  weight_zero_of_not_feasible_bridge.mpr weight_zero_of_not_feasible_source

abbrev feasible_projection_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.feasible_projection)

theorem feasible_projection_source : feasible_projection_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.feasible_projection

abbrev feasible_projection_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ},
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ (H : Finset (ZMod n)) (t : ZMod n),
    (feasible H).image (fun X => X.erase t) = feasible (H.erase t)

theorem feasible_projection_bridge : feasible_projection_arena.Law feasibleActual ↔
    feasible_projection_scope := Iff.rfl

theorem feasible_projection_actual_law : feasible_projection_arena.Law feasibleActual :=
  feasible_projection_bridge.mpr feasible_projection_source

abbrev condition_fibre_card_delete_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.condition_fibre_card_delete)

theorem condition_fibre_card_delete_source : condition_fibre_card_delete_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.condition_fibre_card_delete

abbrev condition_fibre_card_delete_arena : Arena where
  signature := countSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    ∀ (P Q H R : Finset (ZMod n)) (t : ZMod n)
    (htH : t ∈ H) (htR : t ∉ R),
    O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H.erase t,R) =
      O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,R) +
      O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,insert t R)

theorem condition_fibre_card_delete_bridge : condition_fibre_card_delete_arena.Law countActual ↔
    condition_fibre_card_delete_scope := Iff.rfl

theorem condition_fibre_card_delete_actual_law : condition_fibre_card_delete_arena.Law countActual :=
  condition_fibre_card_delete_bridge.mpr condition_fibre_card_delete_source

abbrev marginal_weight_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.marginal_weight)

theorem marginal_weight_source : marginal_weight_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.marginal_weight

abbrev marginal_weight_arena : Arena where
  signature := weightSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let weight := fun P Q H X : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,X);
    ∀ (hn : 6 ≤ n) (P Q H R : Finset (ZMod n)) (t : ZMod n)
    (htH : t ∈ H) (hR : R ∈ feasible (H.erase t)),
    marginalWeight (feasible H) (weight P Q H) t R = weight P Q (H.erase t) R

theorem marginal_weight_bridge : marginal_weight_arena.Law weightActual ↔
    marginal_weight_scope := Iff.rfl

theorem marginal_weight_actual_law : marginal_weight_arena.Law weightActual :=
  marginal_weight_bridge.mpr marginal_weight_source

abbrev proper_of_subset_EK_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.proper_of_subset_EK)

theorem proper_of_subset_EK_source : proper_of_subset_EK_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.proper_of_subset_EK

abbrev proper_of_subset_EK_arena : Arena where
  signature := allowedSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let E_K := fun K : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ K;
    ∀ {K H : Finset (ZMod n)} (hK : K.Nonempty)
    (hH : H ⊆ E_K K),
    H ≠ univ

theorem proper_of_subset_EK_bridge : proper_of_subset_EK_arena.Law allowedActual ↔
    proper_of_subset_EK_scope := Iff.rfl

theorem proper_of_subset_EK_actual_law : proper_of_subset_EK_arena.Law allowedActual :=
  proper_of_subset_EK_bridge.mpr proper_of_subset_EK_source

abbrev feasible_of_independent_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.feasible_of_independent)

theorem feasible_of_independent_source : feasible_of_independent_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.feasible_of_independent

abbrev feasible_of_independent_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ},
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ {H : Finset (ZMod n)} (hH : Independent H),
    feasible H = H.powerset

theorem feasible_of_independent_bridge : feasible_of_independent_arena.Law feasibleActual ↔
    feasible_of_independent_scope := Iff.rfl

theorem feasible_of_independent_actual_law : feasible_of_independent_arena.Law feasibleActual :=
  feasible_of_independent_bridge.mpr feasible_of_independent_source

abbrev shift_mem_feasible_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.shift_mem_feasible)

theorem shift_mem_feasible_source : shift_mem_feasible_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.shift_mem_feasible

abbrev shift_mem_feasible_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ},
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ {H X : Finset (ZMod n)} {a : ZMod n}
    (ha0 : a ∉ H) (ha1 : a + 1 ∈ H) (hX : X ∈ feasible H),
    shift (a + 1) (a + 2) X ∈ feasible H

theorem shift_mem_feasible_bridge : shift_mem_feasible_arena.Law feasibleActual ↔
    shift_mem_feasible_scope := Iff.rfl

theorem shift_mem_feasible_actual_law : shift_mem_feasible_arena.Law feasibleActual :=
  shift_mem_feasible_bridge.mpr shift_mem_feasible_source

abbrev local_excludes_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.local_excludes)

theorem local_excludes_source : local_excludes_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.local_excludes

abbrev local_excludes_arena : Arena where
  signature := feasibleSignature
  Law O := ∀ {n : ℕ},
    let feasible := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ {H X : Finset (ZMod n)} {a : ZMod n}
    (hX : X ∈ feasible H) (ht : a + 2 ∈ X),
    a + 1 ∉ X ∧ a + 3 ∉ X

theorem local_excludes_bridge : local_excludes_arena.Law feasibleActual ↔
    local_excludes_scope := Iff.rfl

theorem local_excludes_actual_law : local_excludes_arena.Law feasibleActual :=
  local_excludes_bridge.mpr local_excludes_source

abbrev local_weight_law_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.local_weight_law)

theorem local_weight_law_source : local_weight_law_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.local_weight_law

abbrev local_weight_law_arena : Arena where
  signature := weightSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let weight := fun P Q H X : Finset (ZMod n) => O.readout () ⟨n, NeZero.ne n⟩ (P,Q,H,X);
    ∀ (hn : 14 ≤ n) {P Q H X : Finset (ZMod n)} {a : ZMod n}
    (hH : H ⊆ E_K (P ∪ Q)) (ha0 : a ∉ H)
    (ha1 : a + 1 ∈ H) (ha2 : a + 2 ∈ H)
    (hX : X ∈ feasible H) (ht : a + 2 ∈ X),
    weight P Q H X = weight P Q H (shift (a + 1) (a + 2) X) +
      if insert (a + 3) (shift (a + 1) (a + 2) X) ∈ feasible H then
        weight P Q H (insert (a + 3) (shift (a + 1) (a + 2) X)) else 0

theorem local_weight_law_bridge : local_weight_law_arena.Law weightActual ↔
    local_weight_law_scope := Iff.rfl

theorem local_weight_law_actual_law : local_weight_law_arena.Law weightActual :=
  local_weight_law_bridge.mpr local_weight_law_source

abbrev independent_iff_noncrossing_scope := type_of%
  (@_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.independent_iff_noncrossing)

theorem independent_iff_noncrossing_source : independent_iff_noncrossing_scope :=
  @_root_.D5.S3.Geometry.Polygons.PolygonCompressionTrace.independent_iff_noncrossing

abbrev independent_iff_noncrossing_arena : Arena where
  signature := independentSignature
  Law O := ∀ {n : ℕ} [NeZero n],
    let Independent := fun H : Finset (ZMod n) => O.readout () n H;
    ∀ (hn : 6 ≤ n) (H : Finset (ZMod n)),
    Independent H ↔ ∀ i ∈ H, ∀ j ∈ H, ¬Cross (ear i) (ear j)

theorem independent_iff_noncrossing_bridge : independent_iff_noncrossing_arena.Law independentActual ↔
    independent_iff_noncrossing_scope := Iff.rfl

theorem independent_iff_noncrossing_actual_law : independent_iff_noncrossing_arena.Law independentActual :=
  independent_iff_noncrossing_bridge.mpr independent_iff_noncrossing_source

end

end Reg.D5.S3.Geometry.Polygons.PolygonCompressionTrace
