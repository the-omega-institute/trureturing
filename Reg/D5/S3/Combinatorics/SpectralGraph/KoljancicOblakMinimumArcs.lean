import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
import Reg.Support.DependentFamily

/-! Typed source-family evidence for arc-cardinality and support observations.

The eight `family` values retain exact telescope bridges, variation, sensitivity,
and observational dependence. They are partial audit evidence, not validated
`Contract.Registration` bindings. Contract decoding and current source-selection
binding evidence for all eight targets remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/25108#issuecomment-6555443606.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Fin n × Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => E.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem singleton_exact : ExactSupport
    (Finset.univ : Finset (Fin 1 × Fin 1)) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  simp [Matrix.one_apply, hij]

private theorem singleton_nssp : HasNSSP (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro X hX _
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  change X i j = 0
  have h := hX i j
  simpa only [Matrix.one_apply, if_pos hij, one_mul] using h

private theorem singleton_connected : ConnectedSupport
    (Finset.univ : Finset (Fin 1 × Fin 1)) := by
  intro p _ i j
  exact congrArg p (Subsingleton.elim _ _)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, ∅, Finset.univ, ?_⟩
  change (Finset.card (∅ : Finset (Fin 1 × Fin 1))) ≠ Finset.card (Finset.univ : Finset (Fin 1 × Fin 1))
  simp

namespace Cycle
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ), ExactSupport E A → HasNSSP A →
    n + (incidence E).rank ≤ O.readout () n E

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h Finset.univ 1 singleton_exact singleton_nssp
  change 1 + _ ≤ 0 at hbad
  omega

def family : Registration arena (type_of% @nssp_centralizer_cycle_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nssp_centralizer_cycle_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

end Cycle

namespace Connected
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {n : ℕ}, 1 ≤ n → ∀ (E : Finset (Fin n × Fin n)), ConnectedSupport E →
    ∀ (A : Matrix (Fin n) (Fin n) ℝ), ExactSupport E A → HasNSSP A →
    2*n-1 ≤ O.readout () n E

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (by decide : 1 ≤ 1) Finset.univ singleton_connected 1 singleton_exact singleton_nssp
  change 2*1-1 ≤ 0 at hbad
  omega

def family : Registration arena (type_of% @nssp_arc_bound_of_connected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nssp_arc_bound_of_connected, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

end Connected

namespace SupportObservation
abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Fin n × Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Finset (Fin n × Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => E) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, ∅, Finset.univ, ?_⟩
  change (∅ : Finset (Fin 1 × Fin 1)) ≠ Finset.univ
  exact fun h => by simpa using congrArg Finset.card h

private theorem singleton_requires : Requires
    (Finset.univ : Finset (Fin 1 × Fin 1)) := by
  intro A hA X hX _
  ext i j
  change X i j = 0
  exact (mul_eq_zero.mp (hX i j)).resolve_left ((hA i j).mpr (Finset.mem_univ _))

private theorem empty_not_requires : ¬ Requires (∅ : Finset (Fin 1 × Fin 1)) := by
  intro h
  have hN := h 0 (by intro i j; simp [ExactSupport])
  exact one_ne_zero (hN 1 (by intro i j; simp) (by simp))

namespace Upper
abbrev arena : Arena where
  signature := SupportObservation.signature
  Law O := ∀ (n : ℕ), 1 ≤ n → Requires (O.readout () n (endpointSupport n))
private theorem rejected_law : ¬ arena.Law SupportObservation.rejected := by
  intro h
  have hb := h 1 (by decide)
  exact empty_not_requires hb
def family : Registration arena (type_of% @endpoint_requires) where
  actual := SupportObservation.actual
  bridge := Iff.rfl
  variation := ⟨endpoint_requires, SupportObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨SupportObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := SupportObservation.dependence
end Upper

namespace Attainment
abbrev arena : Arena where
  signature := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.signature
  Law O := ∀ (n : ℕ), 1 ≤ n → ∃ E : Finset (Fin n × Fin n), Requires E ∧ O.readout () n E = 2*n-1
private theorem rejected_law : ¬ arena.Law _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected := by
  intro h
  obtain ⟨E,_,he⟩ := h 1 (by decide)
  change 0 = 2*1-1 at he
  norm_num at he
def family : Registration arena (type_of% @endpoint_attainment) where
  actual := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.actual
  bridge := Iff.rfl
  variation := ⟨endpoint_attainment, _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨_root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.dependence
end Attainment

namespace Level
abbrev arena : Arena where
  signature := SupportObservation.signature
  Law O := ∀ {n : ℕ} (E : Finset (Fin n × Fin n)), Requires E → ∀ (p : Fin n → ℝ), (∀ e : E, p e.val.1 = p e.val.2) → ∀ r : Fin n, ∃ i : Fin n, p i = p r ∧ (i,i) ∈ O.readout () n E
private theorem rejected_law : ¬ arena.Law SupportObservation.rejected := by
  intro h
  obtain ⟨i,_,hi⟩ := h Finset.univ singleton_requires (fun _ => 0) (by intro e; rfl) 0
  exact Finset.notMem_empty _ hi
def family : Registration arena (type_of% @requires_level_has_loop) where
  actual := SupportObservation.actual
  bridge := Iff.rfl
  variation := ⟨requires_level_has_loop, SupportObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨SupportObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := SupportObservation.dependence
end Level

namespace Plant
abbrev arena : Arena where
  signature := SupportObservation.signature
  Law O := ∀ {n : ℕ} (E : Finset (Fin n × Fin n)) (r : Fin n), (r,r) ∈ E → ∃ A : Matrix (Fin n) (Fin n) ℝ, ExactSupport (O.readout () n E) A ∧ (1-A).det = 0
private theorem rejected_law : ¬ arena.Law SupportObservation.rejected := by
  intro h
  obtain ⟨A,hA,hd⟩ := h Finset.univ (0 : Fin 1) (Finset.mem_univ _)
  have hz : A = 0 := by
    ext i j
    change A i j = 0
    by_contra hn
    exact Finset.notMem_empty _ ((hA i j).mp hn)
  simpa [hz] using hd
def family : Registration arena (type_of% @loop_support_eigenvalue_one) where
  actual := SupportObservation.actual
  bridge := Iff.rfl
  variation := ⟨loop_support_eigenvalue_one, SupportObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨SupportObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := SupportObservation.dependence
end Plant

namespace Connectivity
abbrev arena : Arena where
  signature := SupportObservation.signature
  Law O := ∀ {n : ℕ} (E : Finset (Fin n × Fin n)), Requires E → ConnectedSupport (O.readout () n E)
private theorem rejected_law : ¬ arena.Law SupportObservation.rejected := by
  intro h
  have hc := h (endpointSupport 2) (endpoint_requires 2 (by decide))
  have hb := hc (fun i => (i.val : ℝ)) (by intro e; exact (Finset.notMem_empty _ e.property).elim) 0 1
  norm_num at hb
def family : Registration arena (type_of% @requires_connected) where
  actual := SupportObservation.actual
  bridge := Iff.rfl
  variation := ⟨requires_connected, SupportObservation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨SupportObservation.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := SupportObservation.dependence
end Connectivity

namespace Complete
abbrev arena : Arena where
  signature := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.signature
  Law O := ∀ (n : ℕ), 1 ≤ n → (∀ E : Finset (Fin n × Fin n), Requires E → 2*n-1 ≤ O.readout () n E) ∧ ∃ E : Finset (Fin n × Fin n), Requires E ∧ E.card = 2*n-1
private theorem rejected_law : ¬ arena.Law _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected := by
  intro h
  have hb := (h 1 (by decide)).1 (endpointSupport 1) (endpoint_requires 1 (by decide))
  change 2*1-1 ≤ 0 at hb
  norm_num at hb
def family : Registration arena (type_of% @result) where
  actual := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.actual
  bridge := Iff.rfl
  variation := ⟨result, _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨_root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := _root_.Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.dependence
end Complete

end SupportObservation

end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
