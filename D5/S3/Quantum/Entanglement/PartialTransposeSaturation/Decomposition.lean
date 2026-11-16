/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/Decomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite recursive singular-block extraction by shortest kernel chains. -/

/- admission_basis: escape-witness -/

import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting

open Submodule LinearMap

namespace FinitePair

/-- A finite-dimensional representation of the two-arrow matrix pencil. -/
structure Pencil (K : Type) [Field K] where
  domain : Type
  codomain : Type
  [domainAdd : AddCommGroup domain]
  [domainModule : Module K domain]
  [codomainAdd : AddCommGroup codomain]
  [codomainModule : Module K codomain]
  [domainFinite : FiniteDimensional K domain]
  [codomainFinite : FiniteDimensional K codomain]
  first : domain →ₗ[K] codomain
  second : domain →ₗ[K] codomain

attribute [instance] Pencil.domainAdd Pencil.domainModule Pencil.codomainAdd
  Pencil.codomainModule Pencil.domainFinite Pencil.codomainFinite

variable {K : Type} [Field K]

/-- Transposing both arrows is duality of the underlying representation. -/
def Pencil.dual (p : Pencil K) : Pencil K where
  domain := Module.Dual K p.codomain
  codomain := Module.Dual K p.domain
  first := p.first.dualMap
  second := p.second.dualMap

/-- There is no nonzero polynomial right-kernel vector. -/
def RightReduced (p : Pencil K) : Prop :=
  ∀ (r : ℕ) (u : Fin (r + 1) → p.domain),
    boundary p.first p.second (r + 1) u = 0 → u (Fin.last r) = 0

/-- A simultaneous subrepresentation cannot acquire a polynomial right kernel. -/
private theorem RightReduced.of_intertwining {p q : Pencil K} (hp : RightReduced p)
    (eU : q.domain →ₗ[K] p.domain) (eV : q.codomain →ₗ[K] p.codomain)
    (hinj : Function.Injective eU)
    (hf : eV.comp q.first = p.first.comp eU)
    (hg : eV.comp q.second = p.second.comp eU) : RightReduced q := by
  intro r u hu
  have he : Fin.snoc (q.first ∘ u) 0 =
      (@Fin.cons _ (fun _ => q.codomain)) 0 (q.second ∘ u) :=
    sub_eq_zero.mp (show Fin.snoc (q.first ∘ u) 0 -
      (@Fin.cons _ (fun _ => q.codomain)) 0 (q.second ∘ u) = 0 from hu)
  have hm := congrArg (fun v : Fin (r + 2) → q.codomain => eV ∘ v) he
  rw [Fin.comp_snoc, Fin.comp_cons] at hm
  simp only [map_zero] at hm
  have hf' : eV ∘ q.first = p.first ∘ eU := by
    ext x
    exact LinearMap.congr_fun hf x
  have hg' : eV ∘ q.second = p.second ∘ eU := by
    ext x
    exact LinearMap.congr_fun hg x
  have hz : boundary p.first p.second (r + 1) (eU ∘ u) = 0 := by
    apply sub_eq_zero.mpr
    simpa only [← Function.comp_assoc, hf', hg'] using hm
  have hlast := hp r (eU ∘ u) hz
  apply hinj
  simpa using hlast

/-- The natural bidual equivalence preserves absence of right kernel chains. -/
private theorem RightReduced.dual_dual {p : Pencil K} (hp : RightReduced p) :
    RightReduced p.dual.dual := by
  refine hp.of_intertwining (Module.evalEquiv K p.domain).symm.toLinearMap
    (Module.evalEquiv K p.codomain).symm.toLinearMap
    (Module.evalEquiv K p.domain).symm.injective ?_ ?_
  · ext x
    change (Module.evalEquiv K p.codomain).symm (p.first.dualMap.dualMap x) = _
    rw [← Module.Dual.eval_comp_comp_evalEquiv_eq]
    exact (Module.evalEquiv K p.codomain).symm_apply_apply _
  · ext x
    change (Module.evalEquiv K p.codomain).symm (p.second.dualMap.dualMap x) = _
    rw [← Module.Dual.eval_comp_comp_evalEquiv_eq]
    exact (Module.evalEquiv K p.codomain).symm_apply_apply _

/-- A pair without a polynomial right kernel has at least as many output as
input dimensions. Truncated coefficient maps give this without a fraction field. -/
private theorem RightReduced.dimension_le {p : Pencil K} (hp : RightReduced p) :
    Module.finrank K p.domain ≤ Module.finrank K p.codomain := by
  let n := Module.finrank K p.codomain + 1
  have hinj := boundary_injective_of_no_chain p.first p.second hp n
  have hbound := LinearMap.finrank_le_finrank_of_injective hinj
  have hnum : n * Module.finrank K p.domain ≤
      (n + 1) * Module.finrank K p.codomain := by
    simpa [Module.finrank_pi_fintype] using hbound
  by_contra hnot
  have hgt : Module.finrank K p.codomain + 1 ≤ Module.finrank K p.domain := by omega
  have hmul := Nat.mul_le_mul_left n hgt
  dsimp [n] at hnum hmul
  nlinarith

/-- An extracted singular block, together with actual complementary projections. -/
structure SplitData (p : Pencil K) (r : ℕ) where
  chain : Fin (r + 1) → p.domain
  boundary_zero : boundary p.first p.second (r + 1) chain = 0
  last_ne_zero : chain (Fin.last r) ≠ 0
  domainProjection : p.domain →ₗ[K] p.domain
  codomainProjection : p.codomain →ₗ[K] p.codomain
  domain_isProj : IsProj (span K (Set.range chain)) domainProjection
  codomain_isProj : IsProj
    (span K (Set.range (fun j : Fin r => p.second (chain j.castSucc)))) codomainProjection
  first_commute : codomainProjection.comp p.first = p.first.comp domainProjection
  second_commute : codomainProjection.comp p.second = p.second.comp domainProjection
  domain_independent : LinearIndependent K chain
  codomain_independent : LinearIndependent K (fun j : Fin r => p.second (chain j.castSucc))

/-- Restrict both arrows to the simultaneous complementary kernels. -/
def SplitData.remainder {p : Pencil K} {r : ℕ} (s : SplitData p r) : Pencil K where
  domain := LinearMap.ker s.domainProjection
  codomain := LinearMap.ker s.codomainProjection
  first := (p.first.comp (LinearMap.ker s.domainProjection).subtype).codRestrict
    (LinearMap.ker s.codomainProjection) (by
      intro x
      change s.codomainProjection (p.first x) = 0
      have h := LinearMap.congr_fun s.first_commute x
      simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp x.property, map_zero] using h)
  second := (p.second.comp (LinearMap.ker s.domainProjection).subtype).codRestrict
    (LinearMap.ker s.codomainProjection) (by
      intro x
      change s.codomainProjection (p.second x) = 0
      have h := LinearMap.congr_fun s.second_commute x
      simpa only [LinearMap.comp_apply, LinearMap.mem_ker.mp x.property, map_zero] using h)

/-- Dualizing an actual simultaneous direct summand preserves absence of right
chains. The dual injection is the transpose of the complementary projection. -/
private theorem RightReduced.dual_remainder {p : Pencil K} {r : ℕ}
    (hp : RightReduced p.dual) (s : SplitData p r) : RightReduced s.remainder.dual := by
  let πP : p.domain →ₗ[K] LinearMap.ker s.domainProjection :=
    (LinearMap.id - s.domainProjection).codRestrict (LinearMap.ker s.domainProjection) (by
      intro x
      change s.domainProjection (x - s.domainProjection x) = 0
      rw [map_sub, s.domain_isProj.map_id _ (s.domain_isProj.map_mem x), sub_self])
  let πQ : p.codomain →ₗ[K] LinearMap.ker s.codomainProjection :=
    (LinearMap.id - s.codomainProjection).codRestrict (LinearMap.ker s.codomainProjection) (by
      intro x
      change s.codomainProjection (x - s.codomainProjection x) = 0
      rw [map_sub, s.codomain_isProj.map_id _ (s.codomain_isProj.map_mem x), sub_self])
  have hsurj : Function.Surjective πQ := by
    intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (x : p.codomain) - s.codomainProjection x = x
    rw [LinearMap.mem_ker.mp x.property, sub_zero]
  have hf : πQ.comp p.first = s.remainder.first.comp πP := by
    ext x
    change p.first x - s.codomainProjection (p.first x) =
      p.first (x - s.domainProjection x)
    rw [map_sub]
    exact congrArg (fun y => p.first x - y) (LinearMap.congr_fun s.first_commute x)
  have hg : πQ.comp p.second = s.remainder.second.comp πP := by
    ext x
    change p.second x - s.codomainProjection (p.second x) =
      p.second (x - s.domainProjection x)
    rw [map_sub]
    exact congrArg (fun y => p.second x - y) (LinearMap.congr_fun s.second_commute x)
  refine hp.of_intertwining πQ.dualMap πP.dualMap
    (LinearMap.dualMap_injective_of_surjective hsurj) ?_ ?_
  · exact (congrArg (fun L : p.domain →ₗ[K] LinearMap.ker s.codomainProjection =>
      L.dualMap) hf).symm
  · exact (congrArg (fun L : p.domain →ₗ[K] LinearMap.ker s.codomainProjection =>
      L.dualMap) hg).symm

/-- Removing a nonzero chain strictly decreases the domain dimension. -/
private theorem SplitData.remainder_dimension_lt {p : Pencil K} {r : ℕ} (s : SplitData p r) :
    Module.finrank K s.remainder.domain < Module.finrank K p.domain := by
  have hrange : 0 < Module.finrank K (LinearMap.range s.domainProjection) := by
    apply Module.finrank_pos_iff.mpr
    have hm : s.chain (Fin.last r) ∈ LinearMap.range s.domainProjection := by
      refine ⟨s.chain (Fin.last r), ?_⟩
      exact s.domain_isProj.map_id _ (subset_span ⟨Fin.last r, rfl⟩)
    exact ⟨⟨⟨s.chain (Fin.last r), hm⟩, 0, fun he =>
      s.last_ne_zero (congrArg Subtype.val he)⟩⟩
  have hdim := s.domainProjection.finrank_range_add_finrank_ker
  change Module.finrank K (LinearMap.ker s.domainProjection) < Module.finrank K p.domain
  omega

/-- If a pair has a right kernel chain, a shortest one admits a genuine split. -/
private theorem exists_split (p : Pencil K) (hp : ¬ RightReduced p) :
    ∃ r : ℕ, Nonempty (SplitData p r) := by
  classical
  have hex : ∃ r : ℕ, ∃ u : Fin (r + 1) → p.domain,
      boundary p.first p.second (r + 1) u = 0 ∧ u (Fin.last r) ≠ 0 := by
    have h := hp
    unfold RightReduced at h
    push_neg at h
    exact h
  have hspec := Nat.find_spec hex
  generalize hr : Nat.find hex = r at hspec
  obtain ⟨u, hu, hlast⟩ := hspec
  cases r with
  | zero =>
      letI : Unique (Fin 1) := { default := 0, uniq := fun i => Fin.eq_zero i }
      have hf : p.first (u 0) = 0 := by
        have h := congrFun hu 0
        simpa [boundary, Fin.snoc_apply_zero, Function.comp_def] using h
      have hg : p.second (u 0) = 0 := by
        have h := congrFun hu (Fin.last 1)
        change 0 - p.second (u 0) = 0 at h
        simpa only [zero_sub, neg_eq_zero] using h
      have hu₀ : u 0 ≠ 0 := by simpa using hlast
      obtain ⟨P, hP, hfP, hgP, hcompl⟩ :=
        split_common_kernel_line p.first p.second (u 0) hu₀ hf hg
      have hspan : span K (Set.range u) = K ∙ u 0 := by
        simp [Set.range_unique]
      refine ⟨0, ⟨{
        chain := u
        boundary_zero := hu
        last_ne_zero := hlast
        domainProjection := P
        codomainProjection := 0
        domain_isProj := hspan.symm ▸ hP
        codomain_isProj := ?_
        first_commute := ?_
        second_commute := ?_
        domain_independent := ?_
        codomain_independent := ?_ }⟩⟩
      · simpa using LinearMap.IsProj.bot K p.codomain
      · simpa using hfP.symm
      · simpa using hgP.symm
      · exact linearIndependent_unique_iff.mpr (by simpa using hlast)
      · exact linearIndependent_empty_type
  | succ n =>
      have hminimal : ∀ z : Fin (n + 1) → p.domain,
          boundary p.first p.second (n + 1) z = 0 → z (Fin.last n) = 0 := by
        intro z hz
        by_contra hne
        have hbound := Nat.find_min' hex ⟨z, hz, hne⟩
        omega
      obtain ⟨P, Q, hP, hQ, hf, hg, hliU, hliV, hcomplU, hcomplV⟩ :=
        split_shortest_chain p.first p.second u hu hlast hminimal
      exact ⟨n + 1, ⟨{
        chain := u
        boundary_zero := hu
        last_ne_zero := hlast
        domainProjection := P
        codomainProjection := Q
        domain_isProj := hP
        codomain_isProj := hQ
        first_commute := hf
        second_commute := hg
        domain_independent := hliU
        codomain_independent := hliV }⟩⟩

/-- A finite decomposition certificate. Each internal node removes an actual
right singular block, and its leaf has no polynomial right kernel. -/
inductive RightReduction : Pencil K → Prop
  | reduced (p : Pencil K) (h : RightReduced p) : RightReduction p
  | split {p : Pencil K} {r : ℕ} (s : SplitData p r)
      (remainder : RightReduction s.remainder) : RightReduction p

/-- Every finite-dimensional pair admits a finite sequence of actual right-block
splittings, ending at a pair without polynomial right kernel. -/
private theorem right_reduction (p : Pencil K) : RightReduction p := by
  generalize hd : Module.finrank K p.domain = d
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
      by_cases hp : RightReduced p
      · exact RightReduction.reduced p hp
      · obtain ⟨r, ⟨s⟩⟩ := exists_split p hp
        exact RightReduction.split s (ih _ (by simpa [hd] using s.remainder_dimension_lt) _ rfl)

/-- With neither right nor left polynomial kernel, the remaining pair is square. -/
private theorem reduced_dimensions_eq {p : Pencil K} (hr : RightReduced p)
    (hl : RightReduced p.dual) : Module.finrank K p.domain = Module.finrank K p.codomain := by
  apply le_antisymm hr.dimension_le
  have h := hl.dimension_le
  change Module.finrank K (Module.Dual K p.codomain) ≤
    Module.finrank K (Module.Dual K p.domain) at h
  rw [Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at h
  exact h

/-- A finite left-block reduction preserves right reduction at every stage and
ends in a square pair with neither right nor left polynomial kernel. -/
inductive LeftReduction : Pencil K → Prop
  | reduced (p : Pencil K) (right : RightReduced p) (left : RightReduced p.dual)
      (square : Module.finrank K p.domain = Module.finrank K p.codomain) : LeftReduction p
  | split {p : Pencil K} {r : ℕ} (right : RightReduced p) (s : SplitData p.dual r)
      (remainder : LeftReduction s.remainder.dual) : LeftReduction p

/-- Left singular blocks can be removed after the right singular blocks without
introducing a right polynomial kernel. -/
private theorem left_reduction (p : Pencil K) (hp : RightReduced p) : LeftReduction p := by
  suffices H : ∀ (d : ℕ) (p : Pencil K), Module.finrank K p.codomain = d →
      RightReduced p → LeftReduction p by
    exact H _ p rfl hp
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro p hd hr
      by_cases hl : RightReduced p.dual
      · exact LeftReduction.reduced p hr hl (reduced_dimensions_eq hr hl)
      · obtain ⟨r, ⟨s⟩⟩ := exists_split p.dual hl
        have hsmall : Module.finrank K s.remainder.dual.codomain < d := by
          have hs := s.remainder_dimension_lt
          change Module.finrank K s.remainder.domain <
            Module.finrank K (Module.Dual K p.codomain) at hs
          change Module.finrank K (Module.Dual K s.remainder.domain) < d
          rw [Subspace.dual_finrank_eq] at hs ⊢
          omega
        have hright : RightReduced s.remainder.dual := hr.dual_dual.dual_remainder s
        exact LeftReduction.split hr s (ih _ hsmall _ rfl hright)

/-- A complete finite two-sided singular-block reduction certificate. Every
split uses actual complementary maps; only its final square pair is unreduced. -/
inductive TwoSidedReduction : Pencil K → Prop
  | left {p : Pencil K} (reduction : LeftReduction p) : TwoSidedReduction p
  | right {p : Pencil K} {r : ℕ} (s : SplitData p r)
      (remainder : TwoSidedReduction s.remainder) : TwoSidedReduction p

/-- Every finite-dimensional pair has an actual finite right-then-left reduction
to square polynomial-regular candidates. -/
theorem two_sided_reduction (p : Pencil K) : TwoSidedReduction p := by
  have h := right_reduction p
  induction h with
  | reduced p hp => exact TwoSidedReduction.left (left_reduction p hp)
  | split s _ ih => exact TwoSidedReduction.right s ih

end FinitePair

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open LinearMap Submodule Module Matrix
open scoped Kronecker TensorProduct

namespace ChainSplitting.FinitePair

/-- Rank of the two-term tensor map belonging to two finite pencils. -/
def Pencil.tensorRank (p q : Pencil ℂ) : ℕ :=
  finrank ℂ (LinearMap.range
    (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second))

/-- Rank of the horizontal pair map. -/
def Pencil.horizontalRank (p : Pencil ℂ) : ℕ :=
  finrank ℂ (LinearMap.range (p.first.coprod p.second))

/-- Rank of the joint pair map. -/
def Pencil.verticalRank (p : Pencil ℂ) : ℕ :=
  finrank ℂ (LinearMap.range (p.first.prod p.second))

/-- Dualizing exchanges horizontal and vertical pair ranks. -/
theorem Pencil.horizontalRank_dual (p : Pencil ℂ) :
    p.dual.horizontalRank = p.verticalRank := by
  let e := Module.dualProdDualEquivDual ℂ p.codomain p.codomain
  have he : (p.first.prod p.second).dualMap.comp e.toLinearMap =
      p.first.dualMap.coprod p.second.dualMap := by
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro x
    rfl
  change finrank ℂ (LinearMap.range (p.first.dualMap.coprod p.second.dualMap)) = _
  rw [← he, LinearMap.range_comp_of_range_eq_top _ e.range]
  exact LinearMap.finrank_range_dualMap_eq_finrank_range _

/-- Vertical pair rank is horizontal rank after dualizing. -/
theorem Pencil.verticalRank_dual (p : Pencil ℂ) :
    p.dual.verticalRank = p.horizontalRank := by
  let e := Module.dualProdDualEquivDual ℂ p.domain p.domain
  have he : e.symm.toLinearMap.comp (p.first.coprod p.second).dualMap =
      p.first.dualMap.prod p.second.dualMap := by
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      change z (p.first x + p.second 0) = z (p.first x)
      rw [map_zero, add_zero]
    · apply LinearMap.ext
      intro x
      change z (p.first 0 + p.second x) = z (p.second x)
      rw [map_zero, zero_add]
  change finrank ℂ (LinearMap.range (p.first.dualMap.prod p.second.dualMap)) = _
  rw [← he, LinearMap.range_comp, LinearEquiv.finrank_map_eq]
  exact LinearMap.finrank_range_dualMap_eq_finrank_range _

section Coordinates

variable {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

/-- Horizontal pair rank agrees with concatenation rank in arbitrary bases. -/
theorem Pencil.horizontalRank_matrix (p : Pencil ℂ)
    (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain) :
    p.horizontalRank = hRank (LinearMap.toMatrix bu bv p.first)
      (LinearMap.toMatrix bu bv p.second) := by
  have he : LinearMap.toMatrix (bu.prod bu) bv (p.first.coprod p.second) =
      Matrix.fromCols (LinearMap.toMatrix bu bv p.first)
        (LinearMap.toMatrix bu bv p.second) := by
    ext i j
    cases j <;> simp [LinearMap.toMatrix_apply, LinearMap.coprod_apply]
  rw [hRank, ← he, Matrix.rank_eq_finrank_range_toLin _ bv (bu.prod bu),
    Matrix.toLin_toMatrix]
  rfl

/-- Vertical pair rank agrees with concatenation rank in arbitrary bases. -/
theorem Pencil.verticalRank_matrix (p : Pencil ℂ)
    (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain) :
    p.verticalRank = vRank (LinearMap.toMatrix bu bv p.first)
      (LinearMap.toMatrix bu bv p.second) := by
  have he : LinearMap.toMatrix bu (bv.prod bv) (p.first.prod p.second) =
      Matrix.fromRows (LinearMap.toMatrix bu bv p.first)
        (LinearMap.toMatrix bu bv p.second) := by
    ext i j
    cases i <;> simp [LinearMap.toMatrix_apply]
  rw [vRank, ← he, Matrix.rank_eq_finrank_range_toLin _ (bv.prod bv) bu,
    Matrix.toLin_toMatrix]
  rfl

/-- Arbitrary bases compute the abstract tensor rank. -/
theorem Pencil.tensorRank_matrix (p q : Pencil ℂ)
    (bu : Basis a ℂ p.domain) (bv : Basis b ℂ p.codomain)
    (bu' : Basis c ℂ q.domain) (bv' : Basis d ℂ q.codomain) :
    p.tensorRank q =
      (tensorSum (LinearMap.toMatrix bu bv p.first) (LinearMap.toMatrix bu bv p.second)
        (LinearMap.toMatrix bu' bv' q.first) (LinearMap.toMatrix bu' bv' q.second)).rank :=
  finrank_tensorSum_toMatrix bu bv bu' bv' p.first p.second q.first q.second

end Coordinates

/-- Dualizing the first factor twice preserves its tensor rank. -/
theorem Pencil.tensorRank_dual_dual_left (p q : Pencil ℂ) :
    p.dual.dual.tensorRank q = p.tensorRank q := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasis ℂ p.codomain
  let bu' := Module.finBasis ℂ q.domain
  let bv' := Module.finBasis ℂ q.codomain
  rw [Pencil.tensorRank_matrix p.dual.dual q bu.dualBasis.dualBasis
      bv.dualBasis.dualBasis bu' bv', Pencil.tensorRank_matrix p q bu bv bu' bv']
  change (tensorSum
    (LinearMap.toMatrix bu.dualBasis.dualBasis bv.dualBasis.dualBasis p.first.dualMap.dualMap)
    (LinearMap.toMatrix bu.dualBasis.dualBasis bv.dualBasis.dualBasis p.second.dualMap.dualMap)
    _ _).rank = _
  simp only [LinearMap.dualMap_def, LinearMap.toMatrix_transpose,
    Matrix.transpose_transpose]

/-- Exchanging both tensor factors only permutes rows and columns. -/
theorem Pencil.tensorRank_comm (p q : Pencil ℂ) : p.tensorRank q = q.tensorRank p := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasis ℂ p.codomain
  let bu' := Module.finBasis ℂ q.domain
  let bv' := Module.finBasis ℂ q.codomain
  rw [Pencil.tensorRank_matrix p q bu bv bu' bv',
    Pencil.tensorRank_matrix q p bu' bv' bu bv]
  have he : tensorSum (LinearMap.toMatrix bu' bv' q.first)
      (LinearMap.toMatrix bu' bv' q.second) (LinearMap.toMatrix bu bv p.first)
      (LinearMap.toMatrix bu bv p.second) =
      (tensorSum (LinearMap.toMatrix bu bv p.first) (LinearMap.toMatrix bu bv p.second)
        (LinearMap.toMatrix bu' bv' q.first) (LinearMap.toMatrix bu' bv' q.second)).reindex
          (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [tensorSum, Matrix.add_apply, Matrix.kronecker_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.kroneckerMap_apply, mul_comm]
  rw [he, Matrix.rank_reindex]

/-- Dualizing both factors transposes the whole tensor matrix. -/
theorem Pencil.tensorRank_dual_dual (p q : Pencil ℂ) :
    p.dual.tensorRank q.dual = p.tensorRank q := by
  classical
  let bu := Module.finBasis ℂ p.domain
  let bv := Module.finBasis ℂ p.codomain
  let bu' := Module.finBasis ℂ q.domain
  let bv' := Module.finBasis ℂ q.codomain
  rw [Pencil.tensorRank_matrix p.dual q.dual bv.dualBasis bu.dualBasis
    bv'.dualBasis bu'.dualBasis, Pencil.tensorRank_matrix p q bu bv bu' bv']
  change (tensorSum
    (LinearMap.toMatrix bv.dualBasis bu.dualBasis p.first.dualMap)
    (LinearMap.toMatrix bv.dualBasis bu.dualBasis p.second.dualMap)
    (LinearMap.toMatrix bv'.dualBasis bu'.dualBasis q.first.dualMap)
    (LinearMap.toMatrix bv'.dualBasis bu'.dualBasis q.second.dualMap)).rank = _
  simp only [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
  let A₁ := LinearMap.toMatrix bu bv p.first
  let A₂ := LinearMap.toMatrix bu bv p.second
  let B₁ := LinearMap.toMatrix bu' bv' q.first
  let B₂ := LinearMap.toMatrix bu' bv' q.second
  have he : tensorSum A₁ᵀ A₂ᵀ B₁ᵀ B₂ᵀ = (tensorSum A₁ A₂ B₁ B₂)ᵀ := by
    simp only [tensorSum, Matrix.kroneckerMap_transpose, Matrix.transpose_add]
  rw [he, Matrix.rank_transpose]

/-- Partial duality can be transferred from one tensor factor to the other. -/
theorem Pencil.tensorRank_dual_left_exchange (p q : Pencil ℂ) :
    p.dual.tensorRank q = p.tensorRank q.dual := by
  calc
    p.dual.tensorRank q = p.dual.dual.tensorRank q.dual :=
      (Pencil.tensorRank_dual_dual p.dual q).symm
    _ = p.tensorRank q.dual := Pencil.tensorRank_dual_dual_left p q.dual


end ChainSplitting.FinitePair

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation
