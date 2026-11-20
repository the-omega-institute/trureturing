/- GID: D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CographDistanceCriterion
   mirror-E: none
   anchors: []
   digest: A native cotree criterion for equality in the cograph distance multiplicity bound. -/


import D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
import D5.S3.QuadraticForms.SymmetricRankOneWidth
import Mathlib.Analysis.Matrix.Spectrum

/-! # Equality in the cograph distance multiplicity bound

Manna, Mandal and Tura, [Open Problem 14.2(ii)](https://arxiv.org/pdf/2611.06981v1#page=22),
ask: “Characterize the connected cographs for which $m_G(\lambda)=\nabla(G)$ for some
$\lambda\ne -1,-2$, and give an explicit infinite family attaining the bound of Theorem 6.4.”
The cotree criterion follows the [analytic result](https://github.com/the-omega-institute/trureturing/issues/32326#issuecomment-7043985785).
-/


set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree

open SimpleGraph NormalizedCographCotree CographVicinalWidth
open D5.S3.QuadraticForms.SymmetricRankOneKernel
open scoped BigOperators

local instance (priority := high) finiteFintype (α : Type) [Finite α] : Fintype α :=
  Fintype.ofFinite α

/-- The eligible shifts in Open Problem 14.2(ii). -/
def Eligible (x : ℝ) : Prop := x ≠ -1 ∧ x ≠ -2

/-- Nullity of the local cotree matrix on the vertex carrier of the induced graph. -/
abbrev kernelCount {V : Type} [Finite V] (G : SimpleGraph V) (q x : ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker (localOperator G q x))

open Classical in
/-- Multiplicity measured by the kernel of the shifted ordinary distance matrix. -/
def distanceMultiplicity {V : Type} [Finite V] (G : SimpleGraph V) (x : ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker
    ((distanceMatrix G - x • (1 : Matrix V V ℝ)).toEuclideanLin))

private theorem distanceMultiplicity_eq {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (x : ℝ) :
    distanceMultiplicity G x = kernelCount G 0 x := by
  unfold distanceMultiplicity kernelCount localOperator
  rw [localMatrix_root hc hP]

private def nonleaves {ι : Type} [Fintype ι] (kind : ι → Option Bool) : Finset ι :=
  open Classical in Finset.univ.filter fun C => kind C ≠ none

private theorem mem_nonleaves {ι : Type} [Fintype ι] (kind : ι → Option Bool) (C : ι) :
    C ∈ nonleaves kind ↔ kind C ≠ none := by
  classical
  simp [nonleaves]

private theorem width_eq_max {V : Type} [Finite V] {G : SimpleGraph V}
    (join : Bool) (kind : (cutGraph G join).ConnectedComponent → Option Bool)
    (child : ∀ C, Cotree (G.induce C.supp) (kind C))
    (arity : Nontrivial (cutGraph G join).ConnectedComponent) :
    width G = max 1 (∑ C ∈ nonleaves kind, width (G.induce C.supp)) := by
  classical
  rw [Cotree.width_node join kind child arity]
  congr 1
  exact (Finset.sum_subtype (nonleaves kind) (fun C => mem_nonleaves kind C)
    (fun C => width (G.induce C.supp))).symm

private theorem label_ne {parent : Bool} {kind : Option Bool}
    (h : kind ≠ some parent) (b : Bool) (hb : kind = some b) :
    label b ≠ label parent := by
  subst kind
  cases parent <;> cases b <;> norm_num [label] at *

private theorem proper_leaf_states {V : Type} [Finite V] {G : SimpleGraph V}
    (tree : Cotree G none) {x : ℝ} (hx : Eligible x) (join : Bool) :
    kernelCount G (label join) x = 0 ∧
      ScalarResponse (localOperator G (label join) x) (oneVector V) (-1 / (x + label join)) := by
  have hp : x + label join ≠ 0 := by
    cases join
    · simpa [label, eq_neg_iff_add_eq_zero] using hx.2
    · simpa [label, eq_neg_iff_add_eq_zero] using hx.1
  simpa only [ite_eq_right hp, kernelCount] using leaf_states tree (label join) x

/-- At every eligible shift and every normalized cotree node with coupling different from
zero, the local nullity is bounded by the vicinal width. Equality gives a kernel vector
of nonzero coordinate sum. -/
theorem cotree_kernelCount_le_and_saturation {V : Type} {G : SimpleGraph V}
    {kind : Option Bool} (tree : Cotree G kind) {x : ℝ} (hx : Eligible x) :
    ∀ [Finite V] (q : ℝ), (∀ b, kind = some b → label b ≠ q) →
    kernelCount G q x ≤ width G ∧
      (kernelCount G q x = width G →
        HasNonzeroPairing (localOperator G q x) (oneVector V)) := by
  classical
  induction tree with
  | @leaf V G v unique =>
    intro finiteV q _
    let leaf : Cotree G none := .leaf v unique
    have hw := leaf.width_leaf
    by_cases hp : x + q = 0
    · have hs := leaf_states leaf q x
      rw [ite_eq_left hp] at hs
      exact ⟨by rw [hw]; exact hs.1.le, fun _ => hs.2⟩
    · have hs := leaf_states leaf q x
      rw [ite_eq_right hp] at hs
      have hk : kernelCount G q x = 0 := hs.1
      rw [hk, hw]
      exact ⟨Nat.zero_le _, fun h => (Nat.zero_ne_one h).elim⟩
  | @node V G join arity kinds alternates child ih =>
    intro finiteV q hq
    let A (C : (cutGraph G join).ConnectedComponent) :=
      localOperator (G.induce C.supp) (label join) x
    let u : PiLp 2
        (fun C : (cutGraph G join).ConnectedComponent => EuclideanSpace ℝ C.supp) :=
      WithLp.toLp 2 (fun C => oneVector C.supp)
    have hl (C) (hC : C ∉ nonleaves kinds) :
        Module.finrank ℝ (LinearMap.ker (A C)) = 0 := by
      have hk : kinds C = none := not_not.mp (fun hn => hC ((mem_nonleaves _ _).mpr hn))
      have leaf : Cotree (G.induce C.supp) none := by rw [← hk]; exact child C
      exact (proper_leaf_states leaf hx join).1
    have hchild (C : (cutGraph G join).ConnectedComponent) := ih C (label join) (label_ne (alternates C))
    have hb := update_block_width (F := fun C => EuclideanSpace ℝ C.supp) A
      (fun C => localOperator_symmetric (G.induce C.supp) (label join) x)
      u (nonleaves kinds) (fun C => width (G.induce C.supp))
      (sub_ne_zero.mpr (hq join rfl)) hl
      (fun C _ => (hchild C).1) (fun C _ => (hchild C).2)
    have hn := localOperator_node_states G join q x
    dsimp only at hb hn
    rw [componentCoordinates_oneVector] at hn
    rw [width_eq_max join kinds child arity]
    have hk : kernelCount G q x = _ := hn.1
    rw [hk]
    exact ⟨hb.1, fun h => hn.2.1.mpr (hb.2.1 h)⟩

private theorem root_kernelCount_le {V : Type} [Finite V] {G : SimpleGraph V}
    (hP : ¬(pathGraph 4).IsIndContained G) (hc : G.Connected) {x : ℝ} (hx : Eligible x) :
    kernelCount G 0 x ≤ width G := by
  let := hc.nonempty
  obtain ⟨tree⟩ := exists_cotree hP
  exact (cotree_kernelCount_le_and_saturation tree hx 0
    (fun join _ => by cases join <;> norm_num [label])).1

/-- An eligible distance eigenvalue has multiplicity at most the vicinal width. -/
theorem distanceMultiplicity_le {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) {x : ℝ} (hx : Eligible x) :
    distanceMultiplicity G x ≤ width G := by
  rw [distanceMultiplicity_eq hc hP]
  exact root_kernelCount_le hP hc hx

/-- The unique internal root child has a deficit of one and a scalar response
that resonates with the leaf responses. The root leaf components contain precisely
the universal vertices. -/
def JoinRootCriterion {V : Type} [Finite V] (G : SimpleGraph V)
    (kind : (cutGraph G true).ConnectedComponent → Option Bool) (x : ℝ) : Prop :=
  open Classical in
  let ℓ := (Finset.univ \ nonleaves kind).card
  ∃ C, nonleaves kind = {C} ∧ 0 < ℓ ∧
    (∀ u : V, (∀ v, u ≠ v → G.Adj u v) ↔ (cutGraph G true).connectedComponentMk u ≠ C) ∧
    kernelCount (G.induce C.supp) 1 x + 1 = width (G.induce C.supp) ∧
    ∃ g, ScalarResponse (localOperator (G.induce C.supp) 1 x) (oneVector C.supp) g ∧
      1 + g - (ℓ : ℝ) / (x + 1) = 0

/-- For any normalized join root of width above one, the root criterion is
equivalent to equality at each eligible real shift. -/
theorem distanceMultiplicity_eq_width_iff_joinRoot {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (hw : 1 < width G)
    (arity : Nontrivial (cutGraph G true).ConnectedComponent)
    (kind : (cutGraph G true).ConnectedComponent → Option Bool)
    (alternates : ∀ C, kind C ≠ some true)
    (child : ∀ C, Cotree (G.induce C.supp) (kind C))
    {x : ℝ} (hx : Eligible x) :
    distanceMultiplicity G x = width G ↔ JoinRootCriterion G kind x := by
  classical
  let I := (cutGraph G true).ConnectedComponent
  let A (C : I) := localOperator (G.induce C.supp) 1 x
  let u : PiLp 2 (fun C : I => EuclideanSpace ℝ C.supp) :=
    WithLp.toLp 2 (fun C => oneVector C.supp)
  have hl (C : I) (hC : C ∉ nonleaves kind) :
      Module.finrank ℝ (LinearMap.ker (A C)) = 0 ∧ ScalarResponse (A C) (u C) (-1 / (x + 1)) := by
    have hk : kind C = none := not_not.mp (fun hn => hC ((mem_nonleaves _ _).mpr hn))
    have leaf : Cotree (G.induce C.supp) none := by rw [← hk]; exact child C
    exact proper_leaf_states leaf hx true
  have hchild (C : I) := cotree_kernelCount_le_and_saturation (child C) hx 1
    (fun b hb => by
      simpa [label] using label_ne (alternates C) b hb)
  have hwidth := width_eq_max true kind child arity
  let : Nontrivial I := arity
  have hwide : 1 < max 1 (∑ C ∈ nonleaves kind, width (G.induce C.supp)) := hwidth ▸ hw
  have hb := update_block_root_iff (F := fun C : I => EuclideanSpace ℝ C.supp)
    A (fun C => localOperator_symmetric (G.induce C.supp) 1 x)
    u (nonleaves kind) (fun C => width (G.induce C.supp)) x Fintype.one_lt_card
    hwide hl (fun C _ => (hchild C).1) (fun C _ => (hchild C).2)
  have hn := (localOperator_node_states G true 0 x).1
  dsimp only at hb hn
  rw [componentCoordinates_oneVector] at hn
  have hk : kernelCount G 0 x =
      Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u 1)) := by
    rw [show label true - (0 : ℝ) = 1 by norm_num [label]] at hn
    exact hn
  rw [distanceMultiplicity_eq hc hP, hk, hwidth, hb]
  constructor
  · rintro ⟨C, hs, hℓ, hd, g, hg, heq⟩
    refine ⟨C, hs, hℓ, ?_, hd, g, hg, heq⟩
    intro v
    rw [Cotree.universal_iff_leaf_child kind child]
    have hm := mem_nonleaves kind ((cutGraph G true).connectedComponentMk v)
    rw [hs, Finset.mem_singleton] at hm
    simpa only [not_not] using not_congr hm.symm
  · rintro ⟨C, hs, hℓ, _, hd, g, hg, heq⟩
    exact ⟨C, hs, hℓ, hd, g, hg, heq⟩

/-- The singleton branch of the paper's multiplicity equality. -/
theorem distanceMultiplicity_eq_width_iff_singleton {V : Type} [Finite V] [Subsingleton V]
    {G : SimpleGraph V} (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (x : ℝ) :
    distanceMultiplicity G x = width G ↔ x = 0 := by
  let := hc.nonempty
  let tree : Cotree G none := .leaf (Classical.choice hc.nonempty) (fun _ => Subsingleton.elim _ _)
  have hs := leaf_states tree 0 x
  rw [distanceMultiplicity_eq hc hP, tree.width_leaf]
  by_cases hx : x = 0
  · rw [add_zero, ite_eq_left hx] at hs
    exact ⟨fun _ => hx, fun _ => hs.1⟩
  · rw [add_zero, ite_eq_right hx] at hs
    exact ⟨fun he => (Nat.zero_ne_one (hs.1.symm.trans he)).elim, fun he => (hx he).elim⟩

open Matrix in
private theorem distanceMultiplicity_pos_iff {V : Type} [Finite V]
    (G : SimpleGraph V) (x : ℝ) :
    0 < distanceMultiplicity G x ↔ ∃ y : V → ℝ, y ≠ 0 ∧ distanceMatrix G *ᵥ y = x • y := by
  classical
  rw [distanceMultiplicity, Module.finrank_pos_iff_exists_ne_zero]
  let L := (distanceMatrix G - x • (1 : Matrix V V ℝ)).toEuclideanLin
  have hker (y : EuclideanSpace ℝ V) :
      y ∈ LinearMap.ker L ↔ distanceMatrix G *ᵥ ⇑y = x • ⇑y := by
    rw [LinearMap.mem_ker]
    have hm : L = (distanceMatrix G).toEuclideanLin -
        x • (LinearMap.id : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V) := by
      simp only [L, map_sub, map_smul, Matrix.toLpLin_one]
    rw [hm, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_smul] using
      ((WithLp.ofLp_injective 2).eq_iff (a := (distanceMatrix G).toEuclideanLin y)
        (b := x • y)).symm
  constructor
  · rintro ⟨⟨y, hy⟩, hne⟩
    exact ⟨⇑y, (WithLp.ofLp_eq_zero 2).ne.mpr (fun hz => hne (Subtype.ext hz)), (hker y).mp hy⟩
  · rintro ⟨y, hne, hy⟩
    let v : EuclideanSpace ℝ V := WithLp.toLp 2 y
    refine ⟨⟨v, (hker v).mpr hy⟩, fun hz => hne ?_⟩
    exact congrArg (fun z : LinearMap.ker L => ⇑(z : EuclideanSpace ℝ V)) hz

open Matrix in
/-- At width one and at an eligible shift, equality is equivalent to a nonzero
eigenvector of the ordinary distance matrix at that shift. -/
theorem distanceMultiplicity_eq_width_iff_width_one {V : Type} [Finite V]
    {G : SimpleGraph V} (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G)
    (hw : width G = 1) {x : ℝ} (hx : Eligible x) :
    distanceMultiplicity G x = width G ↔
      ∃ y : V → ℝ, y ≠ 0 ∧ distanceMatrix G *ᵥ y = x • y := by
  have hle := distanceMultiplicity_le hc hP hx
  rw [← distanceMultiplicity_pos_iff, hw] at *
  omega

open Matrix in
private theorem exists_positive_distance_eigenvector {V : Type} [Finite V] [Nontrivial V]
    {G : SimpleGraph V} (hc : G.Connected) :
    ∃ (x : ℝ) (y : V → ℝ), 0 < x ∧ y ≠ 0 ∧ distanceMatrix G *ᵥ y = x • y := by
  classical
  let D := distanceMatrix G
  have hD : D.IsHermitian := by
    rw [isHermitian_iff_isSymm]
    ext u v
    change (G.dist v u : ℝ) = (G.dist u v : ℝ)
    exact congrArg (fun n : ℕ => (n : ℝ)) SimpleGraph.dist_comm
  have htrace : D.trace = 0 := by simp [D, Matrix.trace, distanceMatrix]
  have hn : D ≠ 0 := by
    let v := Classical.choice hc.nonempty
    obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
    intro he
    have hh := congrArg (fun A : Matrix V V ℝ => A v w) he
    simp [D, distanceMatrix, dist_eq_one_iff_adj.mpr hw] at hh
  have hsum : ∑ i, hD.eigenvalues i = 0 := hD.trace_eq_sum_eigenvalues ▸ htrace
  have hpos : ∃ i, 0 < hD.eigenvalues i := by
    by_contra! hnpos
    apply hn
    apply hD.eigenvalues_eq_zero_iff.mp
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnpos j)).mp hsum i (Finset.mem_univ _)
  obtain ⟨i, hi⟩ := hpos
  exact ⟨_, _, hi, (WithLp.ofLp_eq_zero 2).ne.2 (hD.eigenvectorBasis.orthonormal.ne_zero i),
    hD.mulVec_eigenvectorBasis i⟩

/-- Every connected cograph of width one attains, at zero for a singleton and
at a positive eigenvalue for a nonsingleton. -/
theorem width_one_attains {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) (hw : width G = 1) :
    ∃ x, Eligible x ∧ distanceMultiplicity G x = width G := by
  cases subsingleton_or_nontrivial V with
  | inl hs =>
    exact ⟨0, by norm_num [Eligible], (distanceMultiplicity_eq_width_iff_singleton hc hP 0).mpr rfl⟩
  | inr hn =>
    obtain ⟨x, y, hx, hne, he⟩ := exists_positive_distance_eigenvector hc
    have hel : Eligible x := ⟨by linarith, by linarith⟩
    exact ⟨x, hel, (distanceMultiplicity_eq_width_iff_width_one hc hP hw hel).mpr ⟨y, hne, he⟩⟩

end D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
