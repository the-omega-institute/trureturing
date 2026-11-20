/- GID: D5/S3/Combinatorics/SpectralGraph/CographDistanceCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CographDistanceCriterion
   mirror-E: none
   anchors: []
   digest: A native cotree criterion for equality in the cograph distance multiplicity bound. -/


import D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
import D5.S3.QuadraticForms.SymmetricRankOneWidth
import D5.S3.QuadraticForms.SymmetricRankOneGuards
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
    have hchild (C : (cutGraph G join).ConnectedComponent) :=
      ih C (label join) (label_ne (alternates C))
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


private def combineCotreeStates {ι : Type} [Fintype ι]
    (s : ι → ℕ × Option ℝ) (t : ℝ) : ℕ × Option ℝ :=
  open Classical in
  let K := ∑ i, (s i).1
  if ∃ i, (s i).2 = none then (K - 1, some (1 / t))
  else
    let S := ∑ i, (s i).2.getD 0
    if 1 + t * S = 0 then (K + 1, none)
    else (K, some (S / (1 + t * S)))

/-- At a fixed real shift, compute the nullity together with a scalar response.
The `none` case records a kernel vector of nonzero coordinate sum. -/
def cotreeScalarState {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) (x : ℝ) : ∀ [Finite V], ℝ → ℕ × Option ℝ := by
  classical
  induction tree with
  | leaf _ _ =>
    intro _ q
    exact if x + q = 0 then (1, none) else (0, some (-1 / (x + q)))
  | node join _ _ _ _ ih =>
    intro _ q
    exact combineCotreeStates (fun i => ih i (label join)) (label join - q)

/-- The three scalar transitions recover the native state at every real shift,
including simultaneous guard roots and poles. The coupling is nonzero at each
internal node when its parent label differs from its own. -/
theorem cotreeScalarState_spec {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) (x : ℝ) :
    ∀ [Finite V] (q : ℝ), (∀ b, kind = some b → label b ≠ q) →
      let s := cotreeScalarState tree x q
      s.1 = kernelCount G q x ∧
        match s.2 with
        | none => HasNonzeroPairing (localOperator G q x) (oneVector V)
        | some g => ScalarResponse (localOperator G q x) (oneVector V) g := by
  classical
  induction tree with
  | @leaf V G v unique =>
    intro _ q _
    have hs := leaf_states (Cotree.leaf (G := G) v unique) q x
    by_cases hp : x + q = 0
    · simpa only [cotreeScalarState, ite_eq_left hp] using
        And.intro ((ite_eq_left hp).mp hs).1.symm ((ite_eq_left hp).mp hs).2
    · simpa only [cotreeScalarState, ite_eq_right hp] using
        And.intro ((ite_eq_right hp).mp hs).1.symm ((ite_eq_right hp).mp hs).2
  | @node V G join arity kind alternates child ih =>
    intro _ q hq
    let I := (cutGraph G join).ConnectedComponent
    let A (i : I) := localOperator (G.induce i.supp) (label join) x
    let u : PiLp 2 (fun i : I => EuclideanSpace ℝ i.supp) :=
      WithLp.toLp 2 (fun i => oneVector i.supp)
    let s (i : I) := cotreeScalarState (child i) x (label join)
    let t := label join - q
    let K := ∑ i, (s i).1
    let parent := combineCotreeStates s t
    change parent.1 = kernelCount G q x ∧
      match parent.2 with
      | none => HasNonzeroPairing (localOperator G q x) (oneVector V)
      | some g => ScalarResponse (localOperator G q x) (oneVector V) g
    have hs (i : I) := ih i (label join) (label_ne (alternates i))
    obtain ⟨hsymm, hsum, hflag, hresponse⟩ := blockDiagonal_states
      (F := fun i : I => EuclideanSpace ℝ i.supp)
      A (fun i => localOperator_symmetric (G.induce i.supp) (label join) x) u
    have hK : Module.finrank ℝ (LinearMap.ker (blockDiagonal A)) = K :=
      hsum.trans (Finset.sum_congr rfl (fun i _ => (hs i).1.symm))
    have hn := localOperator_node_states G join q x
    dsimp only at hn
    rw [componentCoordinates_oneVector] at hn
    by_cases h : ∃ i, (s i).2 = none
    · have hr : parent = (K - 1, some (1 / t)) := by
        simp only [parent, combineCotreeStates, ite_eq_left h, K]
      obtain ⟨i, hi⟩ := h
      have hsi := (hs i).2
      change (match (s i).2 with
        | none => HasNonzeroPairing (A i) (u i)
        | some g => ScalarResponse (A i) (u i) g) at hsi
      rw [hi] at hsi
      obtain ⟨hk, hg⟩ := update_of_nonzero_pairing hsymm
        (sub_ne_zero.mpr (hq join rfl)) (hflag.mpr ⟨i, hsi⟩)
      have hcount := hn.1
      rw [hr]
      change K - 1 = kernelCount G q x ∧
        ScalarResponse (localOperator G q x) (oneVector V) (1 / t)
      refine ⟨?_, (hn.2.2 _).mpr hg⟩
      exact (Nat.eq_sub_of_add_eq (hk.trans hK)).symm.trans hcount.symm
    · let g (i : I) := (s i).2.getD 0
      have hg (i : I) : ScalarResponse (A i) (u i) (g i) := by
        have hsi := (hs i).2
        change (match (s i).2 with
          | none => HasNonzeroPairing (A i) (u i)
          | some g => ScalarResponse (A i) (u i) g) at hsi
        cases hi : (s i).2 with
        | none => exact (h ⟨i, hi⟩).elim
        | some v => simpa only [g, hi, Option.getD_some] using hsi
      let S := ∑ i, g i
      by_cases hr : 1 + t * S = 0
      · have hp : parent = (K + 1, none) := by
          simp only [parent, combineCotreeStates, ite_eq_right h, ite_eq_left hr, S, g, K]
        obtain ⟨hk, hf⟩ := update_of_resonance hsymm (hresponse g hg) hr
        rw [hp]
        exact ⟨(hk.trans (congrArg (· + 1) hK)).symm.trans hn.1.symm, hn.2.1.mpr hf⟩
      · have hp : parent = (K, some (S / (1 + t * S))) := by
          simp only [parent, combineCotreeStates, ite_eq_right h, ite_eq_right hr, S, g, K]
        obtain ⟨hk, hsc⟩ := update_of_nonresonance hsymm (hresponse g hg) hr
        rw [hp]
        refine ⟨?_, (hn.2.2 _).mpr hsc⟩
        calc
          K = Module.finrank ℝ (LinearMap.ker (blockDiagonal A)) := hK.symm
          _ = _ := by rw [← hk]; exact hn.1.symm

open Polynomial

private def integralLabel (join : Bool) : ℤ := if join then 1 else 2

private theorem cast_integralLabel (join : Bool) : (integralLabel join : ℝ) = label join := by
  cases join <;> norm_num [integralLabel, label]

/-- The uncancelled response pair at a node and the distinct guard polynomials
from that node and every descendant. -/
structure CotreeGuardData where
  numerator : ℤ[X]
  guard : ℤ[X]
  subtreeGuards : Finset ℤ[X]

/-- Leaf guards are `X+q`. Internal guards use the product of child guards
plus the integer coupling times the response numerator. -/
def cotreeGuardData {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) : ∀ [Finite V], ℤ → CotreeGuardData := by
  classical
  induction tree with
  | leaf _ _ =>
    intro _ q
    exact ⟨-1, X + C q, {X + C q}⟩
  | @node V G join _ _ _ _ ih =>
    intro _ q
    let d (i : (cutGraph G join).ConnectedComponent) := ih i (integralLabel join)
    let P := fun i => (d i).numerator
    let Q := fun i => (d i).guard
    let guard := responseGuard P Q (integralLabel join - q)
    exact ⟨responseNumerator P Q, guard,
      insert guard (Finset.univ.biUnion fun i => (d i).subtreeGuards)⟩

/-- Each guard is monic of degree equal to the size of its subtree. In
particular, all guards that contribute candidate shifts are nonzero. -/
theorem cotreeGuardData_degrees {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) :
    ∀ [Finite V] (q : ℤ),
      let d := cotreeGuardData tree q
      d.numerator.natDegree = Fintype.card V - 1 ∧
      d.numerator.leadingCoeff = -(Fintype.card V : ℤ) ∧
      d.guard.Monic ∧ d.guard.natDegree = Fintype.card V ∧
      d.guard ∈ d.subtreeGuards ∧ (∀ p ∈ d.subtreeGuards, p.Monic) := by
  classical
  induction tree with
  | @leaf V G v unique =>
    intro _ q
    let : Unique V := ⟨⟨v⟩, unique⟩
    change (-1 : ℤ[X]).natDegree = Fintype.card V - 1 ∧
      (-1 : ℤ[X]).leadingCoeff = -(Fintype.card V : ℤ) ∧
      (X + C q).Monic ∧ (X + C q).natDegree = Fintype.card V ∧
      X + C q ∈ ({X + C q} : Finset ℤ[X]) ∧
        (∀ p ∈ ({X + C q} : Finset ℤ[X]), (p : ℤ[X]).Monic)
    rw [Fintype.card_unique]
    refine ⟨by simp, by simp, monic_X_add_C q, natDegree_X_add_C q,
      Finset.mem_singleton_self _, ?_⟩
    intro p hp
    rw [Finset.mem_singleton.mp hp]
    exact monic_X_add_C q
  | @node V G join arity kind alternates child ih =>
    intro _ q
    let I := (cutGraph G join).ConnectedComponent
    let : Nontrivial I := arity
    let d (i : I) := cotreeGuardData (child i) (integralLabel join)
    let P (i : I) := (d i).numerator
    let Q (i : I) := (d i).guard
    let R := responseGuard P Q (integralLabel join - q)
    let n (i : I) := Fintype.card i.supp
    have hcard : ∑ i, n i = Fintype.card V := by
      exact Fintype.card_sigma.symm.trans
        (@Fintype.card_congr _ _ Sigma.instFintype (finiteFintype V) (componentEquiv G join))
    have hpos (i : I) : 0 < n i := by
      let : Nonempty i.supp := i.nonempty_supp.to_subtype
      exact Fintype.card_pos
    have hchild (i : I) := ih i (integralLabel join)
    have hd := responseGuard_degrees P Q (integralLabel join - q) n hpos
      (fun i => ⟨(hchild i).2.2.1, (hchild i).2.2.2.1⟩)
      (fun i => ⟨(hchild i).1, (hchild i).2.1⟩)
    dsimp only at hd
    rw [hcard] at hd
    change (responseNumerator P Q).natDegree = Fintype.card V - 1 ∧
      (responseNumerator P Q).leadingCoeff = -(Fintype.card V : ℤ) ∧
      R.Monic ∧ R.natDegree = Fintype.card V ∧
      R ∈ insert R (Finset.univ.biUnion fun i : I => (d i).subtreeGuards) ∧
        (∀ p ∈ insert R (Finset.univ.biUnion fun i : I => (d i).subtreeGuards), p.Monic)
    refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, Finset.mem_insert_self _ _, ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hd.2.2.1
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      exact (hchild i).2.2.2.2.2 p hi

/-- Away from all descendant guards, the native nullity is zero and the scalar
response is exactly the uncancelled ratio. -/
theorem cotreeGuardData_off_roots {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) (x : ℝ) :
    ∀ [Finite V] (q : ℤ),
      let d := cotreeGuardData tree q
      (∀ p ∈ d.subtreeGuards, p.eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      kernelCount G (q : ℝ) x = 0 ∧
      ScalarResponse (localOperator G (q : ℝ) x) (oneVector V)
        (d.numerator.eval₂ (Int.castRingHom ℝ) x / d.guard.eval₂ (Int.castRingHom ℝ) x) := by
  classical
  induction tree with
  | @leaf V G v unique =>
    intro _ q
    dsimp only
    intro hoff
    have hz : x + (q : ℝ) ≠ 0 := by
      simpa only [eval₂_add, eval₂_X, eval₂_C, Int.coe_castRingHom] using
        hoff (X + C q) (Finset.mem_singleton_self _)
    have hl := leaf_states (Cotree.leaf (G := G) v unique) (q : ℝ) x
    rw [ite_eq_right hz] at hl
    change kernelCount G (q : ℝ) x = 0 ∧
      ScalarResponse (localOperator G (q : ℝ) x) (oneVector V)
        ((-1 : ℤ[X]).eval₂ (Int.castRingHom ℝ) x / (X + C q).eval₂ (Int.castRingHom ℝ) x)
    simpa only [eval₂_neg, eval₂_one, eval₂_add, eval₂_X, eval₂_C, Int.coe_castRingHom] using hl
  | @node V G join arity kind alternates child ih =>
    intro _ q
    dsimp only
    intro hoff
    let I := (cutGraph G join).ConnectedComponent
    let d (i : I) := cotreeGuardData (child i) (integralLabel join)
    let P (i : I) := (d i).numerator
    let Q (i : I) := (d i).guard
    let R := responseGuard P Q (integralLabel join - q)
    change ∀ p ∈ insert R (Finset.univ.biUnion (fun i : I => (d i).subtreeGuards)),
      p.eval₂ (Int.castRingHom ℝ) x ≠ 0 at hoff
    have hchild (i : I) (p : ℤ[X]) (hp : p ∈ (d i).subtreeGuards) :
        p.eval₂ (Int.castRingHom ℝ) x ≠ 0 :=
      hoff p (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩))
    have hqi (i : I) : (Q i).eval₂ (Int.castRingHom ℝ) x ≠ 0 :=
      hchild i _ (cotreeGuardData_degrees (child i) (integralLabel join)).2.2.2.2.1
    have hr : R.eval₂ (Int.castRingHom ℝ) x ≠ 0 :=
      hoff R (Finset.mem_insert_self _ _)
    let A (i : I) := localOperator (G.induce i.supp) (label join) x
    let u : PiLp 2 (fun i : I => EuclideanSpace ℝ i.supp) :=
      WithLp.toLp 2 (fun i => oneVector i.supp)
    have hstates (i : I) :
        Module.finrank ℝ (LinearMap.ker (A i)) = 0 ∧
        ScalarResponse (A i) (u i)
          ((P i).eval₂ (Int.castRingHom ℝ) x / (Q i).eval₂ (Int.castRingHom ℝ) x) := by
      have h := ih i (integralLabel join) (hchild i)
      rw [cast_integralLabel] at h
      exact h
    have hb := update_block_of_guard_ne_zero (F := fun i : I => EuclideanSpace ℝ i.supp)
      A (fun i => localOperator_symmetric (G.induce i.supp) (label join) x)
      u P Q (integralLabel join - q) x hqi hr hstates
    rw [Int.cast_sub, cast_integralLabel] at hb
    have hn := localOperator_node_states G join (q : ℝ) x
    dsimp only at hn
    rw [componentCoordinates_oneVector] at hn
    exact ⟨hn.1.trans hb.1, (hn.2.2 _).mpr hb.2⟩

/-- At each real shift, eligible equality is equivalent to membership in the
finite set of guard roots together with eligible equality of the recursively
computed count. The sum of the guard degrees bounds the number of candidates. -/
theorem distanceMultiplicity_guard_candidates {V : Type} [Finite V]
    {G : SimpleGraph V} {kind : Option Bool} (tree : Cotree G kind)
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) :
    let s := (cotreeGuardData tree 0).subtreeGuards
    let candidates := realGuardCandidates s id
    candidates.card ≤ ∑ p ∈ s, p.natDegree ∧
      ∀ x : ℝ, (Eligible x ∧ distanceMultiplicity G x = width G) ↔
        x ∈ candidates ∧ Eligible x ∧ (cotreeScalarState tree x 0).1 = width G := by
  classical
  let s := (cotreeGuardData tree 0).subtreeGuards
  have hwidth : 0 < width G := by
    cases tree with
    | leaf v unique => rw [(Cotree.leaf (G := G) v unique).width_leaf]; decide
    | node join arity kind _ child => rw [width_eq_max join kind child arity]; omega
  have hnonzero (p) (hp : p ∈ s) : p ≠ 0 :=
    ((cotreeGuardData_degrees tree 0).2.2.2.2.2 p hp).ne_zero
  have hoff (x : ℝ) (h : ∀ p ∈ s, p.eval₂ (Int.castRingHom ℝ) x ≠ 0) :
      distanceMultiplicity G x ≠ width G := by
    have hz := (cotreeGuardData_off_roots tree x 0 h).1
    rw [Int.cast_zero] at hz
    rw [distanceMultiplicity_eq hc hP, hz]
    exact hwidth.ne
  have hsize := (realGuardCandidates_spec s id hnonzero
    (fun x => distanceMultiplicity G x = width G) hoff).1
  refine ⟨hsize, fun x => ?_⟩
  have hstate : (cotreeScalarState tree x 0).1 = distanceMultiplicity G x :=
    (cotreeScalarState_spec tree x 0 (fun join _ => by cases join <;> norm_num [label])).1.trans
      (distanceMultiplicity_eq hc hP x).symm
  rw [hstate]
  constructor
  · rintro ⟨hel, he⟩
    have hfinite := (realGuardCandidates_spec s id hnonzero
      (fun y => y = x ∧ distanceMultiplicity G y = width G)
      (fun y hy hey => hoff y hy hey.2)).2
    obtain ⟨y, hy, rfl, _⟩ := hfinite.mp ⟨x, rfl, he⟩
    exact ⟨hy, hel, he⟩
  · rintro ⟨_, hel, he⟩
    exact ⟨hel, he⟩

/-- A connected cograph attains at an eligible shift exactly when its width is
one, or an eligible candidate shift satisfies the native join-root formula. -/
theorem distanceMultiplicity_attains_iff {V : Type} [Finite V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) :
    (∃ x, Eligible x ∧ distanceMultiplicity G x = width G) ↔
      width G = 1 ∨
      (1 < width G ∧ ∃ (arity : Nontrivial (cutGraph G true).ConnectedComponent)
        (kind : (cutGraph G true).ConnectedComponent → Option Bool)
        (alternates : ∀ C, kind C ≠ some true)
        (child : ∀ C, Cotree (G.induce C.supp) (kind C)),
        let tree := Cotree.node true arity kind alternates child
        ∃ x ∈ realGuardCandidates (cotreeGuardData tree 0).subtreeGuards id,
          Eligible x ∧ JoinRootCriterion G kind x) := by
  classical
  let := hc.nonempty
  rcases eq_or_ne (width G) 1 with hw | hw
  · exact iff_of_true (width_one_attains hc hP hw) (Or.inl hw)
  have hn : Nontrivial V := not_subsingleton_iff_nontrivial.mp (fun hs => hw (width_singleton G))
  let : Nontrivial V := hn
  obtain ⟨tree⟩ := Cotree.exists_join_root hc hP
  cases tree with
  | node _ arity kind alternates child =>
    have hwide : 1 < width G := by rw [width_eq_max true kind child arity] at hw ⊢; omega
    constructor
    · rintro ⟨x, hx, he⟩
      have hfinite :=
        (distanceMultiplicity_guard_candidates (.node true arity kind alternates child) hc hP).2 x
      have hxc := (hfinite.mp ⟨hx, he⟩).1
      have hroot :=
        distanceMultiplicity_eq_width_iff_joinRoot hc hP hwide arity kind alternates child hx
      exact Or.inr ⟨hwide, arity, kind, alternates, child, x, hxc, hx,
        hroot.mp he⟩
    · rintro (h | ⟨hwide, arity', kind', alternates', child', x, _, hx, hr⟩)
      · exact (hw h).elim
      · have hroot := distanceMultiplicity_eq_width_iff_joinRoot
          hc hP hwide arity' kind' alternates' child' hx
        exact ⟨x, hx, hroot.mpr hr⟩

end D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
