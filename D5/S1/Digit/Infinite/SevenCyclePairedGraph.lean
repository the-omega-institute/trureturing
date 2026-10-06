/- GID: D5/S1/Digit/Infinite/SevenCyclePairedGraph
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SevenCyclePairedGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual orbit edges in the original complete paired endpoint graph. -/

import D5.S1.Digit.Infinite.SevenCycleOriginalGraph
import D5.S1.Digit.Infinite.SevenCycleSourceFibres
import D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation
import D5.S1.Digit.Infinite.SevenCycleActualRecords

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SevenCyclePairedGraph

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SevenCycleCoherenceRefutation
open D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
open Quiver
open private source phaseGuard phaseColor firstLabel rivalLabel lowerEntry upperEntry
  firstEntry rivalEntry feedingEntry phase budget_bounds actual_entry
  budget golden_data shifted_source_windows shifted_source_tail source_windows
  from D5.S1.Digit.Infinite.SevenCycleCollisionData
open private actual_phase_mod actual_phase_guard actual_guard phase_state
  from D5.S1.Digit.Infinite.SevenCycleCollisionRecords
open private entry_bounds uniform_colors from D5.S1.Digit.Infinite.SevenCycleCollisionColors
open private feeding_scalar phase_lawful from D5.S1.Digit.Infinite.SevenCycleCollisionFuture
open private denominator orbitVertex orbit_edge orbit_period entry_lattice original_parameters
  from D5.S1.Digit.Infinite.SevenCycleOriginalGraph
open private periodic_targets from D5.S1.Digit.Infinite.SevenCycleActualRecords
open private source_fibre from D5.S1.Digit.Infinite.SevenCycleSourceFibres

private theorem orbit_edge_unique (b : Bool) (j : ℕ) (l : Label)
    (u : Vertex denominator 100) (he : edge (orbitVertex b j) l u) :
    l = window (source b) j ∧ u = orbitVertex b (j + 1) := by
  have hlow : u.val.2.1 ∈ piece u := ⟨le_rfl, u.property.2.2.2.2.1⟩
  have hhigh : u.val.2.2 ∈ piece u := ⟨u.property.2.2.2.2.1, le_rfl⟩
  have hinv (z : ℝ) (hz : z ∈ piece u) :
      z = inverseBranch l (kappa (bitShift (source b) (3 * j))) := by
    obtain ⟨x, hx, rfl⟩ := he.2.2 hz
    have hx' : x = kappa (bitShift (source b) (3 * j)) := by
      simpa only [piece, orbitVertex, Set.Icc_self, Set.mem_singleton_iff] using hx
    rw [hx']
  obtain ⟨y, hy, hky⟩ := (closed_observation_graph_realization.2.1 u.val.1).symm ▸
    u.property.2.2.1
  obtain ⟨x, hx, _⟩ := closed_observation_graph_realization.2.2.2.1
    (orbitVertex b j).val.1 l u.val.1 y he.1 hy
  have hg : g ≠ 0 := by have h := golden_data.2.2.2.1; linarith
  have hscalar : kappa x = kappa (bitShift (source b) (3 * j)) := by
    rw [(closed_observation_graph_realization.2.2.1 x).1, hx.2.1, hx.2.2, hky,
      hinv _ hlow]
    unfold branch inverseBranch
    field_simp [hg]
    <;> ring
  have hxe := source_fibre b j x hscalar
  have hl : l = window (source b) j := by
    rw [hxe, shifted_source_windows, Nat.add_zero] at hx
    exact hx.2.1.symm
  have hnext : inverseBranch l (kappa (bitShift (source b) (3 * j))) =
      kappa (bitShift (source b) (3 * (j + 1))) := by
    have hrec := (closed_observation_graph_realization.2.2.1
      (bitShift (source b) (3 * j))).1
    simp only [shifted_source_windows, Nat.add_zero, shifted_source_tail] at hrec
    rw [hl]
    unfold inverseBranch
    apply (div_eq_iff hg).2
    unfold branch at hrec
    linarith
  refine ⟨hl, Subtype.ext ?_⟩
  have hs := (phase_lawful b j).2
  have hu := he.1.2
  rw [hl] at hu
  have ha := (hinv _ hlow).trans hnext
  have hb := (hinv _ hhigh).trans hnext
  exact Prod.ext (hu.trans hs.symm) (Prod.ext ha hb)

private noncomputable def orbitPair (j : ℕ) :
    Vertex denominator 100 × Vertex denominator 100 := (orbitVertex true j, orbitVertex false j)

local noncomputable instance : Quiver (Vertex denominator 100 × Vertex denominator 100) :=
  pairedGraph budget denominator 100

private theorem orbit_common_color (j : ℕ) :
    permits budget (orbitVertex true j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) ∧
    permits budget (orbitVertex false j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
  obtain ⟨p, hp, epsilon, heps, he⟩ := periodic_targets
  have point_color (b : Bool) :
      kappa (bitShift (source b) (3 * j)) ∈
        observation budget (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
    have hc := hp b ⟨j % 7, Nat.mod_lt _ (by decide)⟩
    have hd := (abs_le.mp (he b ⟨j % 7, Nat.mod_lt _ (by decide)⟩))
    rw [← actual_phase_mod] at hd
    have hs : kappa (bitShift (source b) (3 * j)) ∈ stateInterval false := by
      rw [← closed_observation_graph_realization.2.1 false]
      exact ⟨_, by simp [stateAddress], rfl⟩
    exact ⟨max_le hs.1 (by linarith [hc.1]), le_min hs.2 (by linarith [hc.2])⟩
  have h (b : Bool) :
      permits budget (orbitVertex b j) (phaseColor ⟨j % 7, Nat.mod_lt _ (by decide)⟩) := by
    intro x hx
    have hx' : x = kappa (bitShift (source b) (3 * j)) := by
      simpa only [piece, orbitVertex, Set.Icc_self, Set.mem_singleton_iff] using hx
    rw [hx']
    exact point_color b
  exact ⟨h true, h false⟩

private noncomputable def orbit_arrow (j : ℕ) : orbitPair j ⟶ orbitPair (j + 1) :=
  ⟨(window (source true) j, window (source false) j),
    orbit_edge true j, orbit_edge false j,
    ⟨_, (orbit_common_color j).1, (orbit_common_color j).2⟩⟩

private theorem pair_arrow_unique (j : ℕ) (z : Vertex denominator 100 × Vertex denominator 100)
    (e : orbitPair j ⟶ z) :
    e.val = (window (source true) j, window (source false) j) ∧ z = orbitPair (j + 1) := by
  have h1 := orbit_edge_unique true j e.val.1 z.1 e.property.1
  have h2 := orbit_edge_unique false j e.val.2 z.2 e.property.2.1
  exact ⟨Prod.ext h1.1 h2.1, Prod.ext h1.2 h2.2⟩

private theorem arrow_from_orbit (a z : Vertex denominator 100 × Vertex denominator 100)
    (j : ℕ) (ha : a = orbitPair j) (e : a ⟶ z) :
    e.val = (window (source true) j, window (source false) j) ∧ z = orbitPair (j + 1) := by
  subst a
  exact pair_arrow_unique j z e

private theorem path_forced (j : ℕ) {z : Vertex denominator 100 × Vertex denominator 100}
    (H : Path (orbitPair j) z) :
    z = orbitPair (j + H.length) ∧
    output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val) H = (List.range H.length).map
      (fun i => (window (source true) (j + i), window (source false) (j + i))) := by
  induction H with
  | nil => simp [output]
  | @cons a z H e ih =>
    have he := arrow_from_orbit a z (j + H.length) ih.1 e
    refine ⟨?_, ?_⟩
    · simpa only [Path.length_cons, Nat.add_assoc] using he.2
    · simp only [output, Path.weight_cons, FreeMonoid.toList_mul, FreeMonoid.toList_of]
      change output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val) H ++ [e.val] = _
      rw [ih.2, he.1, Path.length_cons, List.range_succ, List.map_append]
      rfl

private noncomputable def orbit_segment (j : ℕ) :
    (n : ℕ) → Path (orbitPair j) (orbitPair (j + n))
  | 0 => by simpa using (Path.nil : Path (orbitPair j) (orbitPair j))
  | n + 1 => by
      simpa only [Nat.add_assoc] using (orbit_segment j n).cons (orbit_arrow (j + n))

private theorem segment_length (j n : ℕ) : (orbit_segment j n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [orbit_segment] using congrArg Nat.succ ih

private theorem pair_period (j : ℕ) : orbitPair (j + 7) = orbitPair j :=
  Prod.ext (orbit_period true j) (orbit_period false j)

private noncomputable def orbit_return (j : ℕ) : Path (orbitPair j) (orbitPair j) :=
  Eq.rec (motive := fun z _ => Path (orbitPair j) z) (orbit_segment j 7) (pair_period j)

private theorem return_length (j : ℕ) : (orbit_return j).length = 7 := by
  have cast_length (a b c : Vertex denominator 100 × Vertex denominator 100)
      (h : b = c) (H : Path a b) : (Eq.rec (motive := fun z _ => Path a z) H h).length = H.length := by
    subst c
    rfl
  exact (cast_length _ _ _ (pair_period j) (orbit_segment j 7)).trans (segment_length j 7)

private theorem component_orbit (a : Component (StronglyConnectedComponent.mk (orbitPair 1))) :
    ∃ j : ℕ, a.val = orbitPair j := by
  obtain ⟨⟨H⟩, _⟩ := StronglyConnectedComponent.mk_eq_mk.mp a.property.symm
  exact ⟨1 + H.length, (path_forced 1 H).1⟩

private theorem all_component_singletons
    (a : Component (StronglyConnectedComponent.mk (orbitPair 1))) :
    ∃ x y : ℝ, piece a.val.1 = {x} ∧ piece a.val.2 = {y} := by
  obtain ⟨j, hj⟩ := component_orbit a
  rw [hj]
  exact ⟨_, _, Set.Icc_self _, Set.Icc_self _⟩

private theorem inclusion_length
    (S : StronglyConnectedComponent (Vertex denominator 100 × Vertex denominator 100))
    {a z : Component S} (H : Path a z) :
    ((componentInclusion S).mapPath H).length = H.length := by
  induction H <;> simp_all [Prefunctor.mapPath, Path.length]

private theorem original_component_coherent :
    Coherent (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val.1) (StronglyConnectedComponent.mk (orbitPair 1)) ∧
    Coherent (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val.2) (StronglyConnectedComponent.mk (orbitPair 1)) ∧
    Coherent (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val) (StronglyConnectedComponent.mk (orbitPair 1)) := by
  classical
  have hfinite := (closed_observation_graph_realization.2.2.2.2.2.1
    budget denominator 100 original_parameters).2.2.1
  letI : Finite (Vertex denominator 100) := Set.finite_univ_iff.mp hfinite
  have hcy : Cyclic (StronglyConnectedComponent.mk (orbitPair 1)) := by
    let q : Component (StronglyConnectedComponent.mk (orbitPair 1)) := ⟨orbitPair 1, rfl⟩
    obtain ⟨J, hJ⟩ := liftComponentPath _ (orbit_return 1) rfl rfl
    refine ⟨q, J, ?_⟩
    have hl := congrArg Path.length hJ
    rw [inclusion_length, return_length] at hl
    omega
  have hprefix {α : Type} (f : Label × Label → α) :
      PeriodicPrefixes (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) (StronglyConnectedComponent.mk (orbitPair 1)) := by
    intro a
    obtain ⟨j, hj⟩ := component_orbit a
    rcases a with ⟨a, ha⟩
    change a = orbitPair j at hj
    subst a
    refine ⟨(fun i => f (window (source true) (j + i), window (source false) (j + i))),
      7, by decide, ?_, ?_⟩
    · intro n
      simp [source_windows, Nat.add_mod, Nat.add_assoc]
    · intro z H i hi
      let K := (componentInclusion _).mapPath H
      have hK : output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) K =
          output (componentLabel (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) _) H := by
        induction H with
        | nil => rfl
        | cons H e ih =>
          simp only [output, Prefunctor.mapPath_cons, Path.weight_cons,
            FreeMonoid.toList_mul, FreeMonoid.toList_of] at ih ⊢
          exact congrArg (fun l => l ++ [f e.val]) ih
      have hlen : K.length = H.length := inclusion_length _ H
      have hout : output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) K =
          (List.range H.length).map
            (fun n => f (window (source true) (j + n), window (source false) (j + n))) := by
        have hf := (path_forced j K).2
        have hm : output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) K = (output (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => e.val) K).map f := by
          induction K with
          | nil => rfl
          | cons K e ih =>
            simp only [output, Path.weight_cons, FreeMonoid.toList_mul,
              FreeMonoid.toList_of, List.map_append, List.map_cons, List.map_nil] at ih ⊢
            exact congrArg (fun l => l ++ [f e.val]) ih
        rw [hm, hf, hlen, List.map_map]
        rfl
      rw [← hK, hout]
      simp [hi]
  have hcoherent {α : Type} (f : Label × Label → α) :
      Coherent (fun {a z : Vertex denominator 100 × Vertex denominator 100} (e : a ⟶ z) => f e.val) (StronglyConnectedComponent.mk (orbitPair 1)) :=
    (coherent_component_phases _ _ hcy).1.mpr
      ((coherent_component_phases _ _ hcy).2.1.mpr (hprefix f))
  exact ⟨hcoherent Prod.fst, hcoherent Prod.snd, hcoherent id⟩

private noncomputable def feedingVertex : Vertex denominator 100 :=
  ⟨(false, feedingEntry, feedingEntry), entry_lattice.2.2, entry_lattice.2.2,
    entry_lattice.2.2.1, entry_lattice.2.2.1, le_rfl, Or.inl rfl⟩

private noncomputable def feedingPair : Vertex denominator 100 × Vertex denominator 100 :=
  (feedingVertex, orbitVertex false 0)

private noncomputable def feeding_arrow : feedingPair ⟶ orbitPair 1 := by
  have hg : g ≠ 0 := by have h := golden_data.2.2.2.1; linarith
  have hscalar : feedingEntry = branch nullLabel
      (kappa (bitShift (source true) (3 * 1))) := by
    rw [actual_phase_mod]
    simpa only [Nat.mod_eq_of_lt (by decide : 1 < 7), ↓reduceIte] using (show feedingEntry = branch nullLabel (phase firstEntry ⟨1, by decide⟩) from feeding_scalar.symm)
  have hleft : edge feedingVertex nullLabel (orbitVertex true 1) := by
    have hs := phase_state true 1
    rw [← actual_phase_mod] at hs
    have hinv : inverseBranch nullLabel feedingEntry =
        kappa (bitShift (source true) (3 * 1)) := by
      rw [hscalar]
      simp [inverseBranch, branch, hg]
    change lawful false nullLabel false ∧
      Set.Icc feedingEntry feedingEntry ⊆ _ ∧
      Set.Icc (kappa (bitShift (source true) (3 * 1)))
        (kappa (bitShift (source true) (3 * 1))) ⊆ _
    simp only [Set.Icc_self, Set.singleton_subset_iff]
    refine ⟨by simp [lawful, outgoing, nullLabel], ⟨_, ?_, hscalar.symm⟩,
      ⟨feedingEntry, ⟨le_rfl, le_rfl⟩, hinv⟩⟩
    simpa [phaseGuard] using hs
  have hcolor : permits budget feedingVertex 2 ∧ permits budget (orbitVertex false 0) 2 := by
    have hb : 0 < budget := budget_bounds.2.2.1
    have hf := entry_bounds.2.2.2.2.2
    have hr := entry_bounds.2.2.2.2.1
    constructor
    · intro x hx
      have he : x = feedingEntry := by simpa [piece, feedingVertex] using hx
      subst x
      exact ⟨max_le entry_lattice.2.2.1.1 (by linarith [hf.1]),
        le_min entry_lattice.2.2.1.2 (by linarith [hf.2])⟩
    · intro x hx
      have he : x = rivalEntry := by
        have hx' : x = kappa (source false) := by
          simpa [piece, orbitVertex, bitShift] using hx
        exact hx'.trans (actual_entry false)
      subst x
      exact ⟨max_le entry_lattice.2.1.1.1 (by linarith [hr.1]),
        le_min entry_lattice.2.1.1.2 (by linarith [hr.2])⟩
  refine ⟨(nullLabel, nullLabel), hleft, ?_, 2, hcolor.1, hcolor.2⟩
  simpa [source_windows, rivalLabel, feedingPair, orbitPair]
    using orbit_edge false 0

private theorem no_null_window (j : ℕ) : window (source true) j ≠ nullLabel := by
  rw [source_windows]
  simp only [↓reduceIte]
  have hr : j % 7 < 7 := Nat.mod_lt _ (by decide)
  rcases (show j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨
      j % 7 = 4 ∨ j % 7 = 5 ∨ j % 7 = 6 by omega) with h | h | h | h | h | h | h
  all_goals
    simp only [h, firstLabel]
    intro he
  all_goals
    have hc := congrArg (fun l : Label => (l.val 0, l.val 1, l.val 2)) he
    norm_num [threeLabel, twoLabel, fiveLabel, nullLabel] at hc

private theorem no_return_to_head : ¬ Nonempty (Path (orbitPair 1) feedingPair) := by
  rintro ⟨H⟩
  have he := arrow_from_orbit feedingPair (orbitPair 1) (1 + H.length)
    (path_forced 1 H).1 feeding_arrow
  apply no_null_window (1 + H.length)
  simpa only [feeding_arrow] using (congrArg Prod.fst he.1).symm

private theorem actual_coherent_rival :
    actualCoherentRival budget denominator 100 (source false) := by
  classical
  have hfinite := (closed_observation_graph_realization.2.2.2.2.2.1
    budget denominator 100 original_parameters).2.2.1
  letI : Finite (Vertex denominator 100) := Set.finite_univ_iff.mp hfinite
  have hcy : Cyclic (StronglyConnectedComponent.mk (orbitPair 1)) := by
    let q : Component (StronglyConnectedComponent.mk (orbitPair 1)) := ⟨orbitPair 1, rfl⟩
    obtain ⟨J, hJ⟩ := liftComponentPath _ (orbit_return 1) rfl rfl
    refine ⟨q, J, ?_⟩
    have hl := congrArg Path.length hJ
    rw [inclusion_length, return_length] at hl
    omega
  refine ⟨orbitPair 1, ?_, Set.Icc_self _, ?_, hcy,
    original_component_coherent.1, original_component_coherent.2.1,
    original_component_coherent.2.2⟩
  · exact (actual_guard false 1).symm
  · refine ⟨orbitPair 0, orbitPair 0, orbitPair 1, rfl, rfl, Path.nil, ?_,
      orbit_arrow 0, ?_, ⟨Path.nil⟩⟩
    · simp [output]
    · intro he
      have hh := congrArg (fun l : Label => l.val 1) he
      simp [orbit_arrow, source_windows,
        firstLabel,
        rivalLabel, threeLabel, nullLabel] at hh

end D5.S1.Digit.Infinite.SevenCyclePairedGraph
