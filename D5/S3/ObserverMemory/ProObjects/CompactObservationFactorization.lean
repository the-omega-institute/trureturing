/- GID: D5/S3/ObserverMemory/ProObjects/CompactObservationFactorization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ProObjects/CompactObservationFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous finite readouts and bounded action windows descend through compact observation fibers. -/

import D5.S0.Rewriting.Quotients.SplitSurjectionFactorization
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finset.Lattice.Fold

namespace D5.S3.ObserverMemory.ProObjects.CompactObservationFactorization

open TopologicalSpace
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)

universe u v w a

/-- Adjacent factor laws propagate equality to every earlier level. -/
private theorem equal_at_earlier_level
    {X : Type u} {Q : ℕ → Type v}
    (q : ∀ n, X → Q n) (p : ∀ n, Q (n + 1) → Q n)
    (compatible : ∀ n x, q n x = p n (q (n + 1) x))
    {n N : ℕ} (h : n ≤ N) {x y : X} (heq : q N x = q N y) :
    q n x = q n y := by
  have descent : ∀ M, n ≤ M → ∀ x y, q M x = q M y → q n x = q n y := by
    intro M hM
    induction hM with
    | refl => exact fun _ _ hxy => hxy
    | @step M hM ih =>
        intro x y hxy
        apply ih x y
        rw [compatible M x, compatible M y, hxy]
  exact descent N h x y heq

/-- Compactness makes the local constant-fiber neighborhoods uniform in level. -/
private theorem common_level
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    {Q : ℕ → Type v} [∀ n, TopologicalSpace (Q n)] [∀ n, DiscreteTopology (Q n)]
    (q : ∀ n, X → Q n) (p : ∀ n, Q (n + 1) → Q n)
    (continuous_q : ∀ n, Continuous (q n))
    (compatible : ∀ n x, q n x = p n (q (n + 1) x))
    (basis : IsTopologicalBasis {U : Set X | ∃ n z, U = q n ⁻¹' {z}})
    {Y : Type w} [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (continuous_f : Continuous f) :
    ∃ N, ∀ x y, q N x = q N y → f x = f y := by
  classical
  have local_fiber : ∀ x : X, ∃ n : ℕ,
      ∀ y, q n y = q n x → f y = f x := by
    intro x
    obtain ⟨U, ⟨n, z, rfl⟩, hx, hU⟩ := basis.exists_subset_of_mem_open
      (show x ∈ f ⁻¹' {f x} from rfl)
      ((isOpen_discrete ({f x} : Set Y)).preimage continuous_f)
    refine ⟨n, fun y hy => ?_⟩
    apply hU
    change q n y = z
    exact hy.trans hx
  choose level hlevel using local_fiber
  let U : X → Set X := fun x => q (level x) ⁻¹' {q (level x) x}
  have open_U : ∀ x, IsOpen (U x) := fun x =>
    (isOpen_discrete ({q (level x) x} : Set (Q (level x)))).preimage
      (continuous_q (level x))
  have covers : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    U open_U covers
  refine ⟨s.sup level, fun x y hxy => ?_⟩
  obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  have earlier : q (level z) x = q (level z) y :=
    equal_at_earlier_level q p compatible (Finset.le_sup hz) hxy
  have hy : q (level z) y = q (level z) z := earlier.symm.trans hx
  exact (hlevel z x hx).trans (hlevel z y hy).symm

/-- Surjectivity supplies both the factor and its uniqueness on the whole stage. -/
private theorem factor_readout
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {Q : ℕ → Type v} [∀ n, Finite (Q n)]
    [∀ n, TopologicalSpace (Q n)] [∀ n, DiscreteTopology (Q n)]
    (q : ∀ n, X → Q n) (p : ∀ n, Q (n + 1) → Q n)
    (continuous_q : ∀ n, Continuous (q n))
    (surjective_q : ∀ n, Function.Surjective (q n))
    (compatible : ∀ n x, q n x = p n (q (n + 1) x))
    (basis : IsTopologicalBasis {U : Set X | ∃ n z, U = q n ⁻¹' {z}})
    {Y : Type w} [Finite Y] [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (continuous_f : Continuous f) :
    ∃ N, ∃! g : Q N → Y, ∀ x, g (q N x) = f x := by
  obtain ⟨N, hN⟩ := common_level q p continuous_q compatible basis f continuous_f
  obtain ⟨g, hg, unique⟩ :=
    D5.S0.Rewriting.Quotients.SplitSurjectionFactorization.split_surjection_factorization
      (q N) f (Function.surjInv (surjective_q N))
      (fun {x y} hxy => hN x y hxy)
      (Function.rightInverse_surjInv (surjective_q N))
  refine ⟨N, g, fun x => (congrFun hg x).symm, ?_⟩
  intro g' hg'
  exact unique g' (funext fun x => (hg' x).symm)

/-- Continuity follows the existing left-to-right word execution. -/
private theorem continuous_runWord
    {X : Type u} [TopologicalSpace X] {Action : Type a}
    (F : Action → X → X) (continuous_F : ∀ a, Continuous (F a)) (word : List Action) :
    Continuous (runWord F word) := by
  induction word with
  | nil => exact continuous_id
  | cons a word ih => exact ih.comp (continuous_F a)

/-- The finite product ranges over every word of length at most the horizon. -/
private theorem factor_window
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {Q : ℕ → Type v} [∀ n, Finite (Q n)]
    [∀ n, TopologicalSpace (Q n)] [∀ n, DiscreteTopology (Q n)]
    (q : ∀ n, X → Q n) (p : ∀ n, Q (n + 1) → Q n)
    (continuous_q : ∀ n, Continuous (q n))
    (surjective_q : ∀ n, Function.Surjective (q n))
    (compatible : ∀ n x, q n x = p n (q (n + 1) x))
    (basis : IsTopologicalBasis {U : Set X | ∃ n z, U = q n ⁻¹' {z}})
    {Y : Type w} [Finite Y] [TopologicalSpace Y] [DiscreteTopology Y]
    {Action : Type a} [Finite Action] (F : Action → X → X)
    (continuous_F : ∀ a, Continuous (F a))
    (o : X → Y) (continuous_o : Continuous o) (H : ℕ) :
    ∃ N, ∀ x y, q N x = q N y →
      ∀ word : List Action, word.length ≤ H →
        o (runWord F word x) = o (runWord F word y) := by
  classical
  let W := {word : List Action // word.length ≤ H}
  letI : Fintype W := (List.finite_length_le Action H).fintype
  let response : X → (W → Y) := fun x word => o (runWord F word.val x)
  have continuous_response : Continuous response :=
    continuous_pi fun word => continuous_o.comp (continuous_runWord F continuous_F word.val)
  obtain ⟨N, g, hg, _⟩ := factor_readout q p continuous_q surjective_q compatible basis
    response continuous_response
  refine ⟨N, fun x y hxy word hw => ?_⟩
  have hresponse : response x = response y :=
    (hg x).symm.trans ((congrArg g hxy).trans (hg y))
  exact congrFun hresponse ⟨word, hw⟩

/-- Every continuous finite readout has a unique factor at some actual observation level.
Every finite action window has one level simultaneously sufficient for all bounded words. -/
theorem compact_observation_factorization
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {Q : ℕ → Type v} [∀ n, Finite (Q n)]
    [∀ n, TopologicalSpace (Q n)] [∀ n, DiscreteTopology (Q n)]
    (q : ∀ n, X → Q n) (p : ∀ n, Q (n + 1) → Q n)
    (continuous_q : ∀ n, Continuous (q n))
    (surjective_q : ∀ n, Function.Surjective (q n))
    (compatible : ∀ n x, q n x = p n (q (n + 1) x))
    (basis : IsTopologicalBasis {U : Set X | ∃ n z, U = q n ⁻¹' {z}})
    {Y : Type w} [Finite Y] [TopologicalSpace Y] [DiscreteTopology Y] :
    (∀ f : X → Y, Continuous f →
      ∃ N, ∃! g : Q N → Y, ∀ x, g (q N x) = f x) ∧
    (∀ {Action : Type a} [Finite Action] (F : Action → X → X),
      (∀ a, Continuous (F a)) → ∀ o : X → Y, Continuous o → ∀ H : ℕ,
      ∃ N, ∀ x y, q N x = q N y →
        ∀ word : List Action, word.length ≤ H →
          o (runWord F word x) = o (runWord F word y)) := by
  exact ⟨factor_readout q p continuous_q surjective_q compatible basis,
    fun F hF o ho H => factor_window q p continuous_q surjective_q compatible basis F hF o ho H⟩

end D5.S3.ObserverMemory.ProObjects.CompactObservationFactorization
