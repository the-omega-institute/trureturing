/- GID: D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory]
   digest: Every finite rational causal law admits a positive latent realization with support controlled by the affine rank of retained linear moments; all LP rows plus one query give an exact witness of size at most the row count plus two. -/

import D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
import D5.S3.ConceptDynamics.CausalMoments.QuaternaryResponseTableCoding
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Option

/- Library and literature-facing audit (2026-09-06):
   * `FiniteResponseLaw`, `LinearFeasible`, and `linearObjective` are reused from
     existing repository owners. No second probability or LP semantics is added.
   * Pinned Mathlib supplies finite-dimensional Caratheodory reduction,
     `AffineIndependent.card_le_finrank_succ`, `Submodule.finrank_mono`,
     `Submodule.finrank_le`, and `Module.finrank_pi`.
   * The selected support depends on the particular law and retained moment
     vector. It is distinct from one generator required to cover every
     unrestricted response table, whose 4^k lower bound is formalized elsewhere.
   * Choe, Kwon, Park, and Lee (UAI 2026) quotient canonical counterfactual states
     that are indistinguishable to all LP rows and the objective. Here the same
     joint feature profile is viewed geometrically: after quotienting duplicate
     profiles, affine rank controls the number of atoms needed to realize each
     feasible moment/query point. No algorithmic runtime or novelty claim is made. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSupportReduction

open scoped BigOperators
open Set
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.QuaternaryResponseTableCoding

/-- Vector of all retained linear moments of a normalized finite law. -/
def lawMomentVector
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    (law : FiniteResponseLaw Atom)
    (feature : Atom → Feature → ℚ) : Feature → ℚ :=
  ∑ atom, law.mass atom • feature atom

/-- Affine dimension of the global atom-profile family for a retained feature
map. This detects duplicate profiles and affine dependencies among coordinates. -/
def profileAffineRank
    {Atom Feature : Type*} [Fintype Feature]
    (feature : Atom → Feature → ℚ) : Nat :=
  Module.finrank ℚ (vectorSpan ℚ (Set.range feature))

/-- The retained moment vector is a convex combination of the atom feature
vectors. This is the exact entry point for Mathlib's Caratheodory theorem. -/
theorem lawMomentVector_mem_convexHull
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    (law : FiniteResponseLaw Atom)
    (feature : Atom → Feature → ℚ) :
    lawMomentVector law feature ∈ convexHull ℚ (Set.range feature) := by
  classical
  have htotal :
      (∑ atom ∈ (Finset.univ : Finset Atom), law.mass atom) = 1 := by
    simpa using law.total
  have hpositive :
      0 < ∑ atom ∈ (Finset.univ : Finset Atom), law.mass atom := by
    rw [htotal]
    norm_num
  have hmem :
      (Finset.univ : Finset Atom).centerMass law.mass feature ∈
        convexHull ℚ (Set.range feature) :=
    Finset.centerMass_mem_convexHull
      (Finset.univ : Finset Atom)
      (fun atom _ => law.nonnegative atom)
      hpositive
      (fun atom _ => Set.mem_range_self atom)
  rw [(Finset.univ : Finset Atom).centerMass_eq_of_sum_1 feature htotal] at hmem
  simpa [lawMomentVector] using hmem

/-- A positive atomic realization of the same retained moment vector. Every
profile comes from an original atom. The selected profiles are affinely
independent, exposing both the exact profile-rank bound and its ambient bound. -/
structure MomentCompression
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    (law : FiniteResponseLaw Atom)
    (feature : Atom → Feature → ℚ) where
  profiles : Finset (Feature → ℚ)
  source : ∀ profile ∈ profiles, profile ∈ Set.range feature
  weight : (Feature → ℚ) → ℚ
  nonnegative : ∀ profile ∈ profiles, 0 ≤ weight profile
  total : ∑ profile ∈ profiles, weight profile = 1
  moment_eq :
    ∑ profile ∈ profiles, weight profile • profile = lawMomentVector law feature
  independent : AffineIndependent ℚ ((↑) : profiles → (Feature → ℚ))
  card_le : profiles.card ≤ Fintype.card Feature + 1

/-- Every normalized finite rational law has a moment-preserving positive atomic
compression with at most one more atom than the retained feature dimension. -/
theorem exists_momentCompression
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    (law : FiniteResponseLaw Atom)
    (feature : Atom → Feature → ℚ) :
    Nonempty (MomentCompression law feature) := by
  classical
  have hx := lawMomentVector_mem_convexHull law feature
  let t : Finset (Feature → ℚ) :=
    Caratheodory.minCardFinsetOfMemConvexHull hx
  have hsubset : (↑t : Set (Feature → ℚ)) ⊆ Set.range feature :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hmem :
      lawMomentVector law feature ∈ convexHull ℚ (t : Set (Feature → ℚ)) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have hind : AffineIndependent ℚ ((↑) : t → (Feature → ℚ)) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  simp only [Finset.convexHull_eq, mem_ofPred_eq] at hmem
  obtain ⟨w, hw_nonnegative, hw_total, hw_center⟩ := hmem
  have hspan :
      Module.finrank ℚ
          (vectorSpan ℚ
            (Set.range ((↑) : t → (Feature → ℚ)))) ≤
        Module.finrank ℚ (Feature → ℚ) :=
    Submodule.finrank_le _
  have hcard : t.card ≤ Fintype.card Feature + 1 := by
    calc
      t.card = Fintype.card t := by simp
      _ ≤ Module.finrank ℚ
            (vectorSpan ℚ
              (Set.range ((↑) : t → (Feature → ℚ)))) + 1 :=
        hind.card_le_finrank_succ
      _ ≤ Module.finrank ℚ (Feature → ℚ) + 1 :=
        Nat.add_le_add_right hspan 1
      _ = Fintype.card Feature + 1 := by
        rw [Module.finrank_pi]
  rw [t.centerMass_eq_of_sum_1 id hw_total] at hw_center
  exact ⟨{
    profiles := t
    source := fun profile hp => hsubset hp
    weight := w
    nonnegative := hw_nonnegative
    total := hw_total
    moment_eq := by simpa only [id_eq] using hw_center
    independent := hind
    card_le := hcard
  }⟩

/-- The selected support is bounded by one plus the affine rank of the complete
feature-profile family. This can be strictly smaller than the raw feature count
when rows are redundant or several atoms share the same joint profile. -/
theorem MomentCompression.card_le_profileAffineRank
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) :
    Fintype.card compression.profiles ≤ profileAffineRank feature + 1 := by
  have hsource :
      Set.range ((↑) : compression.profiles → (Feature → ℚ)) ⊆
        Set.range feature := by
    rintro _ ⟨profile, rfl⟩
    exact compression.source profile.1 profile.2
  have hmono :
      vectorSpan ℚ
          (Set.range ((↑) : compression.profiles → (Feature → ℚ))) ≤
        vectorSpan ℚ (Set.range feature) :=
    vectorSpan_mono ℚ hsource
  calc
    Fintype.card compression.profiles ≤
        Module.finrank ℚ
          (vectorSpan ℚ
            (Set.range ((↑) : compression.profiles → (Feature → ℚ)))) + 1 :=
      compression.independent.card_le_finrank_succ
    _ ≤ Module.finrank ℚ
          (vectorSpan ℚ (Set.range feature)) + 1 :=
      Nat.add_le_add_right (Submodule.finrank_mono hmono) 1
    _ = profileAffineRank feature + 1 := rfl

/-- Choose one original atom realizing each retained profile. -/
noncomputable def MomentCompression.sourceAtom
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature)
    (profile : compression.profiles) : Atom :=
  Classical.choose (compression.source profile.1 profile.2)

/-- The chosen original atom has exactly the profile indexing its latent state. -/
@[simp] theorem MomentCompression.sourceAtom_feature
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature)
    (profile : compression.profiles) :
    feature (compression.sourceAtom profile) = profile.1 :=
  Classical.choose_spec (compression.source profile.1 profile.2)

/-- Distinct retained profiles choose distinct original atoms. -/
theorem MomentCompression.sourceAtom_injective
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) :
    Function.Injective compression.sourceAtom := by
  intro left right equal_source
  apply Subtype.ext
  calc
    left.1 = feature (compression.sourceAtom left) :=
      (compression.sourceAtom_feature left).symm
    _ = feature (compression.sourceAtom right) := by rw [equal_source]
    _ = right.1 := compression.sourceAtom_feature right

/-- The positive Caratheodory weights form a normalized rational law on the
small latent carrier of retained profiles. -/
noncomputable def MomentCompression.latentLaw
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) :
    FiniteResponseLaw compression.profiles where
  mass := fun profile => compression.weight profile.1
  nonnegative := fun profile => compression.nonnegative profile.1 profile.2
  total := by
    simp only [Finset.univ_eq_attach]
    rw [Finset.sum_attach, compression.total]

/-- Evaluating the chosen source atom under the compressed latent law reproduces
the complete retained moment vector exactly. -/
theorem MomentCompression.latent_source_moment_eq
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature) :
    (∑ state : compression.profiles,
        compression.latentLaw.mass state • feature (compression.sourceAtom state)) =
      lawMomentVector law feature := by
  calc
    (∑ state : compression.profiles,
        compression.latentLaw.mass state • feature (compression.sourceAtom state)) =
      ∑ state : compression.profiles,
        compression.weight state.1 • state.1 := by
          apply Finset.sum_congr rfl
          intro state _
          simp [MomentCompression.latentLaw]
    _ = ∑ profile ∈ compression.profiles,
        compression.weight profile • profile := by
          simp only [Finset.univ_eq_attach]
          exact Finset.sum_attach _ (fun profile => compression.weight profile • profile)
    _ = lawMomentVector law feature := compression.moment_eq

/-- Scalar coordinate form of exact moment preservation. -/
theorem MomentCompression.coordinate_eq
    {Atom Feature : Type*} [Fintype Atom] [Fintype Feature]
    {law : FiniteResponseLaw Atom} {feature : Atom → Feature → ℚ}
    (compression : MomentCompression law feature)
    (coordinate : Feature) :
    (∑ state : compression.profiles,
        compression.latentLaw.mass state *
          feature (compression.sourceAtom state) coordinate) =
      ∑ atom, law.mass atom * feature atom coordinate := by
  have h := congrFun compression.latent_source_moment_eq coordinate
  simpa only [lawMomentVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

/-- Put every LP constraint row and one objective into a single finite feature
vector. `none` is the objective coordinate; `some c` is constraint row `c`. -/
def linearRowQueryFeature
    {Constraint Atom : Type*}
    (A : Constraint → Atom → ℚ)
    (objective : Atom → ℚ)
    (atom : Atom) : Option Constraint → ℚ
  | none => objective atom
  | some constraint => A constraint atom

/-- Affine profile rank of all LP rows jointly with the objective. -/
def linearProblemProfileRank
    {Constraint Atom : Type*} [Fintype Constraint]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ) : Nat :=
  profileAffineRank (linearRowQueryFeature A objective)

/-- The LP profile rank is at most the ambient number of coordinates, namely the
row count plus one objective coordinate. -/
theorem linearProblemProfileRank_le
    {Constraint Atom : Type*} [Fintype Constraint]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ) :
    linearProblemProfileRank A objective ≤ Fintype.card Constraint + 1 := by
  unfold linearProblemProfileRank profileAffineRank
  calc
    Module.finrank ℚ
        (vectorSpan ℚ
          (Set.range (linearRowQueryFeature A objective))) ≤
      Module.finrank ℚ (Option Constraint → ℚ) :=
        Submodule.finrank_le _
    _ = Fintype.card (Option Constraint) := by rw [Module.finrank_pi]
    _ = Fintype.card Constraint + 1 := Fintype.card_option

/-- The exact rank-aware Caratheodory bound for an LP row/query profile. -/
theorem MomentCompression.linearRowQuery_profileRank_card_le
    {Constraint Atom : Type*} [Fintype Constraint] [Fintype Atom]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ)
    (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective)) :
    Fintype.card compression.profiles ≤ linearProblemProfileRank A objective + 1 := by
  simpa [linearProblemProfileRank] using compression.card_le_profileAffineRank

/-- The coarser ambient bound is at most the number of LP rows plus two states. -/
theorem MomentCompression.linearRowQuery_card_le
    {Constraint Atom : Type*} [Fintype Constraint] [Fintype Atom]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ)
    (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective)) :
    Fintype.card compression.profiles ≤ Fintype.card Constraint + 2 := by
  calc
    Fintype.card compression.profiles ≤
        linearProblemProfileRank A objective + 1 :=
      compression.linearRowQuery_profileRank_card_le A objective law
    _ ≤ (Fintype.card Constraint + 1) + 1 :=
      Nat.add_le_add_right (linearProblemProfileRank_le A objective) 1
    _ = Fintype.card Constraint + 2 := by omega

/-- If the original law satisfies a finite rational inequality system, the
small latent law satisfies the pulled-back system on its chosen original atoms. -/
theorem MomentCompression.latentLinearFeasible
    {Constraint Atom : Type*} [Fintype Constraint] [Fintype Atom]
    (A : Constraint → Atom → ℚ) (b : Constraint → ℚ)
    (objective : Atom → ℚ) (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective))
    (feasible : LinearFeasible A b law.mass) :
    LinearFeasible
      (fun constraint state => A constraint (compression.sourceAtom state))
      b compression.latentLaw.mass := by
  intro constraint
  have hrow :
      (∑ state : compression.profiles,
          A constraint (compression.sourceAtom state) *
            compression.latentLaw.mass state) =
        ∑ atom, A constraint atom * law.mass atom := by
    simpa [linearRowQueryFeature, mul_comm] using
      compression.coordinate_eq (some constraint)
  rw [hrow]
  exact feasible constraint

/-- The compressed latent witness preserves the exact LP objective value. -/
theorem MomentCompression.latentLinearObjective_eq
    {Constraint Atom : Type*} [Fintype Constraint] [Fintype Atom]
    (A : Constraint → Atom → ℚ) (objective : Atom → ℚ)
    (law : FiniteResponseLaw Atom)
    (compression : MomentCompression law (linearRowQueryFeature A objective)) :
    linearObjective
        (fun state => objective (compression.sourceAtom state))
        compression.latentLaw.mass =
      linearObjective objective law.mass := by
  have hquery := compression.coordinate_eq (none : Option Constraint)
  simpa [linearObjective, linearRowQueryFeature, mul_comm] using hquery

/-- Every feasible value of a finite linear causal problem has an attaining
latent realization with at most the number of LP rows plus two states. -/
theorem finite_linear_problem_small_latent_witness
    {Constraint Atom : Type*} [Fintype Constraint] [Fintype Atom]
    (A : Constraint → Atom → ℚ) (b : Constraint → ℚ)
    (objective : Atom → ℚ) (law : FiniteResponseLaw Atom)
    (feasible : LinearFeasible A b law.mass) :
    ∃ (State : Type*) (_ : Fintype State)
        (latent : FiniteResponseLaw State) (generator : State → Atom),
      Fintype.card State ≤ Fintype.card Constraint + 2 ∧
      LinearFeasible (fun constraint state => A constraint (generator state))
        b latent.mass ∧
      linearObjective (fun state => objective (generator state)) latent.mass =
        linearObjective objective law.mass := by
  classical
  obtain ⟨compression⟩ :=
    exists_momentCompression law (linearRowQueryFeature A objective)
  refine ⟨ULift (Fin (Fintype.card compression.profiles)), inferInstance,
    { mass := fun state =>
        compression.latentLaw.mass ((Fintype.equivFin compression.profiles).symm state.down)
      nonnegative := fun state => compression.latentLaw.nonnegative _
      total := by
        calc
          _ = ∑ profile, compression.latentLaw.mass profile :=
            Fintype.sum_equiv
              (Equiv.ulift.trans (Fintype.equivFin compression.profiles).symm)
              _ _ (fun _ => rfl)
          _ = 1 := compression.latentLaw.total },
    fun state =>
      compression.sourceAtom ((Fintype.equivFin compression.profiles).symm state.down),
    ?_, ?_, ?_⟩
  · simpa using compression.linearRowQuery_card_le A objective law
  · intro constraint
    calc
      _ = ∑ profile, A constraint (compression.sourceAtom profile) *
          compression.latentLaw.mass profile :=
        Fintype.sum_equiv
          (Equiv.ulift.trans (Fintype.equivFin compression.profiles).symm)
          _ _ (fun _ => rfl)
      _ ≤ b constraint :=
        compression.latentLinearFeasible A b objective law feasible constraint
  · calc
      _ = ∑ profile, objective (compression.sourceAtom profile) *
          compression.latentLaw.mass profile :=
        Fintype.sum_equiv
          (Equiv.ulift.trans (Fintype.equivFin compression.profiles).symm)
          _ _ (fun _ => rfl)
      _ = linearObjective objective law.mass :=
        compression.latentLinearObjective_eq A objective law

/-- For k Boolean response-pair strata, retain all four one-stratum cell
indicators plus one scalar query. -/
def responseTableCellQueryFeature
    {k : Nat}
    (query : (Fin k → Bool × Bool) → ℚ)
    (table : Fin k → Bool × Bool) : Option (Fin k × Fin 4) → ℚ
  | none => query table
  | some cell =>
      if responsePairDigitEquiv (table cell.1) = cell.2 then 1 else 0

/-- Although the unrestricted table carrier has `4^k` atoms, all one-stratum
four-cell marginals and one query admit a positive profile witness using at most
`4*k + 2` atoms. This ambient bound is conservative because each four-cell block
has affine redundancy. -/
theorem exists_responseTableCellQueryCompression
    {k : Nat}
    (law : FiniteResponseLaw (Fin k → Bool × Bool))
    (query : (Fin k → Bool × Bool) → ℚ) :
    ∃ compression : MomentCompression law (responseTableCellQueryFeature query),
      compression.profiles.card ≤ 4 * k + 2 := by
  obtain ⟨compression⟩ :=
    exists_momentCompression law (responseTableCellQueryFeature query)
  refine ⟨compression, ?_⟩
  have h := compression.card_le
  simpa [Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm, Nat.add_assoc] using h

/-- Every retained response-cell probability is exactly preserved by the small
latent table witness. -/
theorem MomentCompression.responseTableCellMoment_eq
    {k : Nat}
    (law : FiniteResponseLaw (Fin k → Bool × Bool))
    (query : (Fin k → Bool × Bool) → ℚ)
    (compression : MomentCompression law (responseTableCellQueryFeature query))
    (cell : Fin k × Fin 4) :
    (∑ state : compression.profiles,
        compression.latentLaw.mass state *
          (if responsePairDigitEquiv ((compression.sourceAtom state) cell.1) = cell.2
            then 1 else 0)) =
      ∑ table, law.mass table *
        (if responsePairDigitEquiv (table cell.1) = cell.2 then 1 else 0) := by
  simpa [responseTableCellQueryFeature] using
    compression.coordinate_eq (some cell)

/-- The same small latent table witness exactly preserves the nominated scalar
query together with all response-cell marginals. -/
theorem MomentCompression.responseTableQueryMoment_eq
    {k : Nat}
    (law : FiniteResponseLaw (Fin k → Bool × Bool))
    (query : (Fin k → Bool × Bool) → ℚ)
    (compression : MomentCompression law (responseTableCellQueryFeature query)) :
    (∑ state : compression.profiles,
        compression.latentLaw.mass state * query (compression.sourceAtom state)) =
      ∑ table, law.mass table * query table := by
  simpa [responseTableCellQueryFeature] using
    compression.coordinate_eq (none : Option (Fin k × Fin 4))

#print axioms exists_momentCompression
#print axioms MomentCompression.card_le_profileAffineRank
#print axioms finite_linear_problem_small_latent_witness
#print axioms exists_responseTableCellQueryCompression

end D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSupportReduction
