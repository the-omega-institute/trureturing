/- GID: D5/S1/Dynamics/Shadowing/FiniteObservationShadowing
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteObservationShadowing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite complete observation names construct initial-point control covers. -/

import D5.S1.Dynamics.Shadowing.CompactObservationSubshift
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.LocallyConstant.Basic

/- The new inference constructs the control cover from whole-name fibers.
The disjoint clopen refinement and continuity of observation names are reused;
neither supplies this control cover or its all-time tracing induction.
The finite name image is Hausdorff and hence discrete. Equal whole names at
successive error pairs propagate along the actual dynamics, so the initial
point traces every controlled pseudo-orbit. This construction, rather than a
supplied selector or shadowing hypothesis, is the live escape witness.

The sole theorem has proof_shape content and admission_basis escape-witness.
Its mathematical subject is finite-cover shadowing, adjacent to the existing
observation-language and stable-core suppliers. Utility is none: the theorem
is a universal topological construction, not bounded enumeration, a checker,
a numerical reduction or a certified finite instance. All other utility
fields are not-applicable(kind=none). This repository-derived inference makes
no claim to settle the general zero-dimensional extension problem. -/

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

/-- Finite complete observation names produce an actual control cover.
Every controlled pseudo-orbit is traced by its initial point, at all times
including zero. No onto-dynamics or nonempty-carrier assumption is used. -/
theorem initial_point_tracing_of_finite_observation_names
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    (f : X → X) (hf : Continuous f)
    (hfinite : ∀ (m : ℕ) (q : X → Fin m), Continuous q →
      (Set.range (fun x n => q (f^[n] x))).Finite)
    (C : Finset (Opens X)) (hC : IsOpenCover (fun U : C => U.1)) :
    ∃ D : Finset (Opens X), IsOpenCover (fun U : D => U.1) ∧
      ∀ a : ℕ → X, PseudoOrbit f D a → Shadows f C a (a 0) := by
  classical
  obtain ⟨m, W, hW, hcover, hdis⟩ :=
    hC.exists_finite_nonempty_disjoint_clopen_cover
  have unique_cell (x : X) : ∃! j, x ∈ W j := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover (mem_univ x))
    refine ⟨j, hj, fun i hi => hdis.eq ?_⟩
    simpa [← Clopens.coe_disjoint, not_disjoint_iff] using!
      (show ∃ x : X, x ∈ W i ∧ x ∈ W j from ⟨x, hi, hj⟩)
  choose q hqmem hq_unique using unique_cell
  have hqlc : IsLocallyConstant q := by
    refine (IsLocallyConstant.iff_exists_open q).2 fun x =>
      ⟨W (q x), (W (q x)).isOpen, hqmem x, ?_⟩
    intro y hy
    exact (hq_unique y (q x) hy).symm
  have hq : Continuous q := hqlc.continuous
  let name : X → ℕ → Fin m := fun x n => q (f^[n] x)
  let S : Set (ℕ → Fin m) := Set.range name
  have hS : S.Finite := hfinite m q hq
  letI : Finite S := hS.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  -- The finite Hausdorff subtype S is discrete, by the existing instance.
  let nameS : X → S := fun x => ⟨name x, ⟨x, rfl⟩⟩
  have hname : Continuous name := continuous_observationName f q hf hq
  have hnameS : Continuous nameS := hname.subtype_mk _
  let fiber : S → Opens X := fun w =>
    ⟨nameS ⁻¹' {w}, (isOpen_discrete _).preimage hnameS⟩
  let D : Finset (Opens X) := Finset.univ.image fiber
  have hD : IsOpenCover (fun U : D => U.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    refine Opens.mem_iSup.mpr ⟨⟨fiber (nameS x), ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨nameS x, Finset.mem_univ _, rfl⟩
    · exact rfl
  refine ⟨D, hD, fun a ha => ?_⟩
  have hstep (n : ℕ) : name (f (a n)) = name (a (n + 1)) := by
    obtain ⟨U, hUD, hfa, hanext⟩ := ha n
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hUD
    change nameS (f (a n)) = w at hfa
    change nameS (a (n + 1)) = w at hanext
    exact congrArg Subtype.val (hfa.trans hanext.symm)
  have name_succ (x : X) (k : ℕ) : name (f x) k = name x (k + 1) := by
    dsimp only [name]
    rw [Function.iterate_succ_apply]
  have hwhole (n : ℕ) : name (a n) = name (f^[n] (a 0)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        name (a (n + 1)) = name (f (a n)) := (hstep n).symm
        _ = name (f (f^[n] (a 0))) := by
          funext k
          exact (name_succ (a n) k).trans
            ((congrFun ih (k + 1)).trans (name_succ (f^[n] (a 0)) k).symm)
  intro n
  have hsame : q (a n) = q (f^[n] (a 0)) := by
    simpa only [name, Function.iterate_zero, id_eq] using congrFun (hwhole n) 0
  obtain ⟨U, hWU⟩ := (hW (q (a n))).2
  refine ⟨U.1, U.2, hWU ?_, hWU (hqmem (a n))⟩
  rw [hsame]
  exact hqmem (f^[n] (a 0))

#print axioms initial_point_tracing_of_finite_observation_names

end D5.S1.Dynamics.Shadowing
