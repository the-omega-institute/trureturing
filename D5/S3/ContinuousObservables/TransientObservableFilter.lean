/- GID: D5/S3/ContinuousObservables/TransientObservableFilter
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/TransientObservableFilter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite pullback filtration is a commutative observable algebra with exact image and rank dimensions. -/

import Mathlib
import D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

namespace D5.S3.ContinuousObservables.TransientObservableFilter

open D5.S3.ObserverMemory.InverseLimits.TraceRankCombinatorics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable def pullbackAlgHom {Y : Type*} (tau : Y -> Y) :
    (Y -> ℂ) →ₐ[ℂ] (Y -> ℂ) :=
  Pi.algHom ℂ (fun _ : Y => ℂ) (fun y => Pi.evalAlgHom ℂ (fun _ : Y => ℂ) (tau y))

noncomputable def observableAlgebra {Y : Type*} (tau : Y -> Y) (k : Nat) :
    Subalgebra ℂ (Y -> ℂ) :=
  (pullbackAlgHom tau ^ k).range

private theorem pullbackAlgHom_apply {Y : Type*} (tau : Y -> Y)
    (f : Y -> ℂ) (y : Y) : pullbackAlgHom tau f y = f (tau y) := by
  rfl

private theorem pullbackAlgHom_pow_apply {Y : Type*} (tau : Y -> Y)
    (k : Nat) (f : Y -> ℂ) (y : Y) :
    (pullbackAlgHom tau ^ k) f y = f ((tau^[k]) y) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, AlgHom.mul_apply, ih]
      rw [Function.iterate_succ_apply']
      rfl

theorem transient_observable_filter
    {Y : Type*} [Finite Y]
    (tau : Y -> Y) (k : Nat) :
    (0 ∈ observableAlgebra tau k ∧
      1 ∈ observableAlgebra tau k ∧
      (∀ f g, f ∈ observableAlgebra tau k -> g ∈ observableAlgebra tau k ->
        f + g ∈ observableAlgebra tau k ∧
        f * g ∈ observableAlgebra tau k ∧
        -f ∈ observableAlgebra tau k ∧ f * g = g * f)) ∧
      observableAlgebra tau (k + 1) ≤ observableAlgebra tau k ∧
      (∀ h, h ∈ observableAlgebra tau k ↔
        ∀ y y', (tau^[k]) y = (tau^[k]) y' -> h y = h y') ∧
      (Module.finrank ℂ (observableAlgebra tau k) =
          Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) ∧
        Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) =
          Nat.card (Set.range (tau^[k]))) := by
  classical
  letI := Fintype.ofFinite Y
  have hzero : (0 : Y -> ℂ) ∈ observableAlgebra tau k := by
    exact ⟨0, by simp⟩
  have hone : (1 : Y -> ℂ) ∈ observableAlgebra tau k := by
    exact ⟨1, by simp⟩
  have hadd : ∀ f g, f ∈ observableAlgebra tau k -> g ∈ observableAlgebra tau k ->
      f + g ∈ observableAlgebra tau k := by
    intro f g hf hg
    rcases hf with ⟨f0, hf0⟩
    rcases hg with ⟨g0, hg0⟩
    refine ⟨f0 + g0, ?_⟩
    rw [map_add, hf0, hg0]
  have hmul : ∀ f g, f ∈ observableAlgebra tau k -> g ∈ observableAlgebra tau k ->
      f * g ∈ observableAlgebra tau k := by
    intro f g hf hg
    rcases hf with ⟨f0, hf0⟩
    rcases hg with ⟨g0, hg0⟩
    refine ⟨f0 * g0, ?_⟩
    rw [map_mul, hf0, hg0]
  have hneg : ∀ f, f ∈ observableAlgebra tau k -> -f ∈ observableAlgebra tau k := by
    intro f hf
    rcases hf with ⟨f0, hf0⟩
    refine ⟨-f0, ?_⟩
    rw [map_neg, hf0]
  have hcomm : ∀ f g : Y -> ℂ, f * g = g * f := by
    intro f g
    funext y
    exact mul_comm (f y) (g y)
  have hfilter : observableAlgebra tau (k + 1) ≤ observableAlgebra tau k := by
    intro h hh
    rcases hh with ⟨f, hf⟩
    refine ⟨(pullbackAlgHom tau) f, ?_⟩
    change (pullbackAlgHom tau ^ k) ((pullbackAlgHom tau) f) = h
    change (pullbackAlgHom tau ^ (k + 1)) f = h at hf
    rw [← hf, pow_succ, AlgHom.mul_apply]
  have hfiber : ∀ h, h ∈ observableAlgebra tau k ↔
      ∀ y y', (tau^[k]) y = (tau^[k]) y' -> h y = h y' := by
    intro h
    constructor
    · rintro ⟨f, rfl⟩ y y' hyy'
      change (pullbackAlgHom tau ^ k) f y = (pullbackAlgHom tau ^ k) f y'
      rw [pullbackAlgHom_pow_apply, pullbackAlgHom_pow_apply, hyy']
    · intro hconstant
      let choosePreimage : Y -> Y := fun z =>
        if hz : z ∈ Set.range (tau^[k]) then Classical.choose hz else z
      let witness : Y -> ℂ := fun z =>
        if hz : z ∈ Set.range (tau^[k]) then h (choosePreimage z) else 0
      have hwitness : ∀ y, witness ((tau^[k]) y) = h y := by
        intro y
        have hy : (tau^[k]) y ∈ Set.range (tau^[k]) := ⟨y, rfl⟩
        have hchosen : (tau^[k]) (Classical.choose hy) = (tau^[k]) y :=
          Classical.choose_spec hy
        simp [witness, choosePreimage, hy, hconstant _ _ hchosen]
      refine ⟨witness, ?_⟩
      funext y
      change (pullbackAlgHom tau ^ k) witness y = h y
      rw [pullbackAlgHom_pow_apply, hwitness]
  refine ⟨⟨hzero, hone, ?_⟩, hfilter, hfiber, ?_⟩
  · intro f g hf hg
    exact ⟨hadd f g hf hg, hmul f g hf hg, hneg f hf, hcomm f g⟩
  · constructor
    · let restrict : observableAlgebra tau k →ₗ[ℂ]
          (Set.range (tau^[k]) → ℂ) :=
        { toFun := fun h z => h.1 (Classical.choose z.2)
          map_add' := by
            intro f g
            funext z
            rfl
          map_smul' := by
            intro c f
            funext z
            rfl }
      have restrict_injective : Function.Injective restrict := by
        intro f g hfg
        apply Subtype.ext
        funext y
        have hy : (tau^[k]) y ∈ Set.range (tau^[k]) := ⟨y, rfl⟩
        have hfg' := congrFun hfg ⟨(tau^[k]) y, hy⟩
        have hfiber_f := (hfiber f.1).1 f.2
        have hfiber_g := (hfiber g.1).1 g.2
        have hpre : (tau^[k]) (Classical.choose hy) = (tau^[k]) y :=
          Classical.choose_spec hy
        calc
          f.1 y = f.1 (Classical.choose hy) := hfiber_f y _ hpre.symm
          _ = g.1 (Classical.choose hy) := by simpa [restrict] using hfg'
          _ = g.1 y := hfiber_g _ y hpre
      have restrict_surjective : Function.Surjective restrict := by
        intro g
        let candidate : Y -> ℂ := fun z =>
          g ⟨(tau^[k]) z, ⟨z, rfl⟩⟩
        have hcandidate : candidate ∈ observableAlgebra tau k := by
          apply (hfiber candidate).2
          intro y y' hyy'
          dsimp [candidate]
          congr 1
          exact Subtype.ext hyy'
        refine ⟨⟨candidate, hcandidate⟩, ?_⟩
        funext z
        have hpre : (tau^[k]) (Classical.choose z.2) = z.1 :=
          Classical.choose_spec z.2
        dsimp [restrict, candidate]
        congr 1
        exact Subtype.ext hpre
      let e := LinearEquiv.ofBijective restrict
        ⟨restrict_injective, restrict_surjective⟩
      calc
        Module.finrank ℂ (observableAlgebra tau k) =
            Module.finrank ℂ (Set.range (tau^[k]) → ℂ) := e.finrank_eq
        _ = Fintype.card (Set.range (tau^[k])) := Module.finrank_pi ℂ
        _ = Nat.card (Set.range (tau^[k])) := (Nat.card_eq_fintype_card).symm
        _ = Module.finrank ℂ (LinearMap.range (transferOperator tau ^ k)) :=
          (trace_rank_combinatorial_meaning tau ⟨1, by omega⟩ k).2.symm
    · exact trace_rank_combinatorial_meaning tau ⟨1, by omega⟩ k |>.2

end D5.S3.ContinuousObservables.TransientObservableFilter
