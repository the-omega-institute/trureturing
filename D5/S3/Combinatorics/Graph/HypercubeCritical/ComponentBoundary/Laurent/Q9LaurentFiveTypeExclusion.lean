/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: none
   digest: A connected induced cubic nine-cube support with a one-sided Laurent identity has fifty-four vertices or at least seven opposite-parity direction triples. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ProjectedHeightCompatibility
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentStarProducts
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentNormalizedBoxes
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! A connected induced cubic nine-cube support satisfying a one-sided Laurent identity cannot use exactly five opposite-parity direction triples. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9RealizedProjection

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open Q9LaurentGainPartition (Side)
open Q9LaurentCommonTriple (Axes inside outside fiber star UniqueCommonNeighbor)
open Q9ProjectedHeightCompatibility (Point HasBoxHeight occupiedSlices sameBox inBox)
open Q6TwoBlockRigidity (Q3Side q3_side_card)
open private star_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/-- Number the four patterns in the occupied parity half of the common triple. -/
noncomputable def sliceIndex {C : Finset (Q 9)} {b q : Bool} (e : Axes)
    (hp : ∀ x : Side C b, cubeParity (inside e x.val) = q) (x : Side C b) : Fin 4 :=
  Fintype.equivFinOfCardEq (q3_side_card q) ⟨inside e x.val, hp x⟩

private theorem eq_of_slices_and_outside {C : Finset (Q 9)} {b q : Bool} {e : Axes}
    {hp : ∀ x : Side C b, cubeParity (inside e x.val) = q} {x y : Side C b}
    (hSlice : sliceIndex e hp x = sliceIndex e hp y)
    (hOut : outside e x.val = outside e y.val) : x = y := by
  have hIn := congrArg Subtype.val ((Fintype.equivFinOfCardEq (q3_side_card q)).injective hSlice)
  apply Subtype.ext
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  cases j with
  | inl j => exact congrFun hIn j
  | inr j => exact congrFun hOut j

/-- A box realization of the actual connected cube support has only one split.
Its threefold incidence is inherited from the unique common-triple star. -/
theorem no_mixed_of_realization {C : Finset (Q 9)} {b q : Bool} {e : Axes}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcommon : UniqueCommonNeighbor C b e)
    (hp : ∀ x : Side C b, cubeParity (inside e x.val) = q)
    (chart : Q 6 ≃ Point) (slices : Fin 4 → Finset (Bool × Point))
    (height : Point → Fin 6 → ℤ)
    (hcover : ∀ i v, i ∈ occupiedSlices slices v ↔
      ∃ x : Side C b, sliceIndex e hp x = i ∧ chart (outside e x.val) = v)
    (hheight : ∀ i t, t ∈ slices i → HasBoxHeight height t.1 t.2)
    (hdisjoint : ∀ i t u, t ∈ slices i → u ∈ slices i → t ≠ u →
      ∀ v, inBox t.1 t.2 v = true → inBox u.1 u.2 v = false)
    (hstep : ∀ (x y : Side C b) (v : ↥C),
      ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨x.val, x.property.1⟩ v →
      ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨y.val, y.property.1⟩ →
      Relation.ReflTransGen (sameBox (univ.biUnion slices))
        (chart (outside e x.val)) (chart (outside e y.val))) :
    ¬ ((∃ i c, (false, c) ∈ slices i) ∧ (∃ i c, (true, c) ∈ slices i)) := by
  classical
  refine Q9ProjectedHeightCompatibility.no_mixed_splits_of_connected_projection
    slices height hheight hdisjoint ?_ ?_
  · intro u v hu hv
    obtain ⟨i, hi⟩ := hu
    obtain ⟨j, hj⟩ := hv
    obtain ⟨x, _, rfl⟩ := (hcover i u).mp hi
    obtain ⟨y, _, rfl⟩ := (hcover j v).mp hj
    exact Q9ProjectedWalk.projected_of_connected (fun x => chart (outside e x.val)) hc hstep x y
  · intro u hu
    obtain ⟨i, hi⟩ := hu
    obtain ⟨x, _, hxu⟩ := (hcover i u).mp hi
    obtain ⟨c, _, _, hf⟩ := Q9LaurentCommonTriple.exists_star_over_projection hcommon x
    let F := fiber C b e (outside e x.val)
    have hF : F.card = 3 := by rw [show F = _ from hf, star_card]
    let toVertex (v : ↥F) : Side C b :=
      ⟨v.val, (mem_filter.mp v.property).1, (mem_filter.mp v.property).2.1⟩
    have hOut (v : ↥F) : outside e (toVertex v).val = outside e x.val :=
      (mem_filter.mp v.property).2.2
    let index (v : ↥F) : Fin 4 := sliceIndex e hp (toVertex v)
    have hinj : Function.Injective index := by
      intro v w heq
      apply Subtype.ext
      have hEq := eq_of_slices_and_outside heq ((hOut v).trans (hOut w).symm)
      exact congrArg (fun z : Side C b => z.val) hEq
    have himage : F.attach.image index = occupiedSlices slices u := by
      ext j
      constructor
      · intro hj
        obtain ⟨w, _, rfl⟩ := mem_image.mp hj
        exact (hcover _ _).mpr ⟨toVertex w, rfl, (congrArg chart (hOut w)).trans hxu⟩
      · intro hj
        obtain ⟨y, hyi, hyu⟩ := (hcover j u).mp hj
        have hyOut := chart.injective (hyu.trans hxu.symm)
        have hyF : y.val ∈ F := mem_filter.mpr ⟨y.property.1, y.property.2, hyOut⟩
        exact mem_image.mpr ⟨⟨y.val, hyF⟩, mem_attach _ _, hyi⟩
    rw [← himage, card_image_of_injective _ hinj, card_attach, hF]


end Q9RealizedProjection
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9RealizedProjection

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open Q9LaurentGainPartition (Side)
open Q9LaurentCommonTriple (Axes inside outside UniqueCommonNeighbor)
open Q9ProjectedHeightCompatibility (Point HasBoxHeight occupiedSlices sameBox inBox)
open private cubeParity from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open Q9RealizedProjection (eq_of_slices_and_outside)

/-- The actual connected graph uses only one split whenever the selected
vertices decompose into transverse components with affine box height. -/
theorem no_mixed_of_transverse_components {C : Finset (Q 9)} {b q : Bool} {e : Axes}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcommon : UniqueCommonNeighbor C b e)
    (hp : ∀ x : Side C b, cubeParity (inside e x.val) = q)
    (chart : Q 6 ≃ Point) (component : Setoid (Side C b))
    (boxAt : Side C b → Bool × Point) (height : Point → Fin 6 → ℤ)
    (hslice : ∀ x y, component.r x y → sliceIndex e hp x = sliceIndex e hp y)
    (hlabel : ∀ x y, component.r x y → (boxAt x).1 = (boxAt y).1)
    (hrealize : ∀ x v, inBox (boxAt x).1 (boxAt x).2 v = true ↔
      ∃ y : Side C b, component.r x y ∧ chart (outside e y.val) = v)
    (hheight : ∀ x, HasBoxHeight height (boxAt x).1 (boxAt x).2)
    (hstep : ∀ (x y : Side C b) (v : ↥C),
      ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨x.val, x.property.1⟩ v →
      ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨y.val, y.property.1⟩ →
      component.r x y ∨ outside e x.val = outside e y.val) :
    ¬ ((∃ x, (boxAt x).1 = false) ∧ (∃ y, (boxAt y).1 = true)) := by
  classical
  let point (x : Side C b) := chart (outside e x.val)
  let slices (i : Fin 4) := ((univ : Finset (Side C b)).filter fun x => sliceIndex e hp x = i).image boxAt
  have hmem {i : Fin 4} {t : Bool × Point} : t ∈ slices i ↔
      ∃ x : Side C b, sliceIndex e hp x = i ∧ boxAt x = t := by
    simp [slices]
  have hself (x : Side C b) : inBox (boxAt x).1 (boxAt x).2 (point x) = true :=
    (hrealize x _).mpr ⟨x, component.refl x, rfl⟩
  have hcover (i : Fin 4) (v : Point) : i ∈ occupiedSlices slices v ↔
      ∃ x : Side C b, sliceIndex e hp x = i ∧ point x = v := by
    unfold occupiedSlices
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, htv⟩
      obtain ⟨x, hxi, rfl⟩ := hmem.mp ht
      obtain ⟨y, hxy, hyv⟩ := (hrealize x v).mp htv
      exact ⟨y, (hslice x y hxy).symm.trans hxi, hyv⟩
    · rintro ⟨x, hxi, rfl⟩
      exact ⟨boxAt x, hmem.mpr ⟨x, hxi, rfl⟩, hself x⟩
  have hsHeight (i : Fin 4) (t : Bool × Point) (ht : t ∈ slices i) :
      HasBoxHeight height t.1 t.2 := by
    obtain ⟨x, _, rfl⟩ := hmem.mp ht
    exact hheight x
  have hdisjoint (i : Fin 4) (t u : Bool × Point) (ht : t ∈ slices i) (hu : u ∈ slices i)
      (hne : t ≠ u) (v : Point) (htv : inBox t.1 t.2 v = true) : inBox u.1 u.2 v = false := by
    obtain ⟨x, hxi, rfl⟩ := hmem.mp ht
    obtain ⟨y, hyi, rfl⟩ := hmem.mp hu
    apply Bool.eq_false_of_not_eq_true
    intro huv
    obtain ⟨x', hxx', hxv⟩ := (hrealize x v).mp htv
    obtain ⟨y', hyy', hyv⟩ := (hrealize y v).mp huv
    have hxy' : x' = y' := eq_of_slices_and_outside
      (((hslice x x' hxx').symm.trans hxi).trans (hyi.symm.trans (hslice y y' hyy')))
      (chart.injective (hxv.trans hyv.symm))
    have hxy : component.r x y := component.trans hxx' (hxy'.symm ▸ component.symm hyy')
    exact hne (Prod.ext (hlabel x y hxy)
      (Q9ProjectedHeightCompatibility.equal_center_of_overlap (hheight x) (hheight y) htv huv))
  have hsteps (x y : Side C b) (v : ↥C)
      (hx : ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨x.val, x.property.1⟩ v)
      (hy : ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨y.val, y.property.1⟩) :
      Relation.ReflTransGen (sameBox (univ.biUnion slices)) (point x) (point y) := by
    rcases hstep x y v hx hy with hxy | hxy
    · apply Relation.ReflTransGen.single
      refine ⟨boxAt x, mem_biUnion.mpr ⟨sliceIndex e hp x, mem_univ _, hmem.mpr ⟨x, rfl, rfl⟩⟩,
        hself x, (hrealize x _).mpr ⟨y, hxy, rfl⟩⟩
    · rw [show point x = point y from congrArg chart hxy]
  rintro ⟨⟨x, hfalse⟩, ⟨y, htrue⟩⟩
  apply no_mixed_of_realization hc hcommon hp chart slices height hcover hsHeight hdisjoint hsteps
  exact ⟨⟨sliceIndex e hp x, (boxAt x).2, hmem.mpr ⟨x, rfl, Prod.ext hfalse rfl⟩⟩,
    ⟨sliceIndex e hp y, (boxAt y).2, hmem.mpr ⟨y, rfl, Prod.ext htrue rfl⟩⟩⟩


end Q9RealizedProjection
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
local notation "cubeFlip" => BalancedCriticalSpectrum.flip
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open Q9LaurentCommonTriple (Axes commonAxes inside outside)
open Q9ProjectedHeightCompatibility (Point HasBoxHeight inBox)
open Q9RealizedProjection (sliceIndex no_mixed_of_transverse_components)
open private flip_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition
open private mem_transverseSide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers

set_option maxHeartbeats 2000000 in
-- The proof combines dependent parity subtypes, normalized charts, and the box realization.
open scoped Classical in
/-- Five triples would give two complementary splits sharing one block.
The connected projection through the shared block cannot contain both splits. -/
theorem card_directionTypes_ne_five {C : Finset (Q 9)} {b : Bool} {a : Side C b → Exponent}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) : (directionTypes C b).card ≠ 5 := by
  classical
  intro hfive
  obtain ⟨P, R, S, hne, hP, hR, hinter, hfamily⟩ := two_partitions_of_five_directionTypes hC h hfive
  have hS : S ∈ P ∩ R := hinter.symm ▸ mem_singleton.mpr rfl
  obtain ⟨e, hSe, hPe, hRe⟩ := exists_normalized_partitions hP hR (mem_inter.mp hS).1
    (mem_inter.mp hS).2 hne
  let P₀ := normalizedPartition e false
  let P₁ := normalizedPartition e true
  have hp₀ : IsTriplePartition P₀ := by simpa only [P₀, hPe] using hP
  have hp₁ : IsTriplePartition P₁ := by simpa only [P₁, hRe] using hR
  have hne' : P₀ ≠ P₁ := fun he => hne (hPe.symm.trans (he.trans hRe))
  have hInter : P₀ ∩ P₁ = {commonAxes e} := by
    simpa only [P₀, P₁, hPe, hRe, hSe] using hinter
  have hFamily : partitionsOn C b = {P₀, P₁} := by
    simpa only [P₀, P₁, hPe, hRe] using hfamily
  have htypes (x : Side C b) : neighborPartition C x.val = P₀ ∨ neighborPartition C x.val = P₁ := by
    have hx : neighborPartition C x.val ∈ partitionsOn C b := mem_image.mpr ⟨x, mem_univ _, rfl⟩
    rwa [hFamily, mem_insert, mem_singleton] at hx
  have hS₀ : commonAxes e ∈ P₀ := by simp [P₀, normalizedPartition]
  have hS₁ : commonAxes e ∈ P₁ := by simp [P₁, normalizedPartition]
  have hCommon := Q9LaurentCommonTriple.uniqueCommonNeighbor_of_laurent (e := e) hC h (by
    intro x
    have hx : commonAxes e ∈ neighborPartition C x.val := (htypes x).elim
      (fun heq => heq.symm ▸ hS₀) (fun heq => heq.symm ▸ hS₁)
    exact mem_image.mp hx)
  have hdirs (v : Side C (!b)) : directions C v.val = commonAxes e ∨
      Disjoint (directions C v.val) (commonAxes e) := by
    by_cases hv : directions C v.val = commonAxes e
    · exact Or.inl hv
    right
    have hdeg := regular_directions C hC v.property.1
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < (directions C v.val).card)
    let y : Side C b := ⟨cubeFlip v.val i, (mem_directions C _ _).mp hi, by
      rw [flip_parity, v.property.2, Bool.not_not]⟩
    have hback : cubeFlip y.val i = v.val := BalancedCriticalSpectrum.flip_flip _ _
    have hmem : directions C v.val ∈ neighborPartition C y.val :=
      mem_image.mpr ⟨i, (mem_directions C _ _).mpr (hback.symm ▸ v.property.1), by rw [hback]⟩
    rcases htypes y with hY | hY
    · exact hp₀.disjoint_blocks (hY ▸ hmem) hS₀ hv
    · exact hp₁.disjoint_blocks (hY ▸ hmem) hS₁ hv
  have hPmem : P₀ ∈ partitionsOn C b := by simp [hFamily]
  have hRmem : P₁ ∈ partitionsOn C b := by simp [hFamily]
  obtain ⟨x₀, _, hx₀⟩ := mem_image.mp hPmem
  obtain ⟨x₁, _, hx₁⟩ := mem_image.mp hRmem
  have hp (x : Side C b) := Q9LaurentCommonTriple.inside_parity_eq hc hdirs x x₀
  obtain ⟨g, hg⟩ := Q9LaurentCommonTriple.exists_projected_exponent h hCommon
  let height (v : Point) := g (cubeBitVec 6 v)
  have hg' (x : Side C b) (j : Fin 6) :
      height ((cubeBitVec 6).symm (outside e x.val)) j = a x (e (.inr j)) := by
    simp only [height, Equiv.apply_symm_apply, hg]
  let label (x : Side C b) : Bool := decide (neighborPartition C x.val = P₁)
  have hLabel (x : Side C b) : neighborPartition C x.val = normalizedPartition e (label x) := by
    rcases htypes x with hx | hx
    · have hn : neighborPartition C x.val ≠ P₁ := fun he => hne' (hx.symm.trans he)
      simpa [label, hn, P₀] using hx
    · simp [label, hx, P₁]
  have hBox (x : Side C b) := realize_normalized_component hC h e hp₀ hp₁ hInter htypes
    height hg' x (label x) (hLabel x)
  let boxAt (x : Side C b) := (label x, (hBox x).choose)
  let component : Setoid (Side C b) := transverseComponents (commonAxes e)
  have hSlice (x y : Side C b) (hxy : component.r x y) : sliceIndex e hp x = sliceIndex e hp y := by
    have hIn := inside_eq_on_transverseSide (e := e) rfl (mem_transverseSide.mpr hxy)
    unfold sliceIndex
    exact congrArg _ (Subtype.ext hIn.symm)
  have hLabels (x y : Side C b) (hxy : component.r x y) : (boxAt x).1 = (boxAt y).1 := by
    change label x = label y
    unfold label
    rw [neighborPartition_eq_of_transverse_path hInter htypes hxy]
  have hReal (x : Side C b) (v : Point) : inBox (boxAt x).1 (boxAt x).2 v = true ↔
      ∃ y : Side C b, component.r x y ∧ (cubeBitVec 6).symm (outside e y.val) = v := by
    change inBox (label x) (hBox x).choose v = true ↔
      ∃ y : Side C b, Relation.ReflTransGen (transverseMove (commonAxes e)) x y ∧
        (cubeBitVec 6).symm (outside e y.val) = v
    simpa only [mem_transverseSide] using (hBox x).choose_spec.2 v
  apply no_mixed_of_transverse_components hc hCommon hp (cubeBitVec 6).symm component boxAt
    height hSlice hLabels hReal (fun x => (hBox x).choose_spec.1)
    (transverse_or_same_projection hp₀ hp₁ hS₀ hS₁ htypes)
  exact ⟨⟨x₀, by simp [boxAt, label, hx₀, hne']⟩, ⟨x₁, by simp [boxAt, label, hx₁]⟩⟩


end Q9TriplePartitions
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary
namespace Q9LaurentCommonTriple

open Finset
open BalancedCriticalSpectrum (Q)
open Q9IsotropicHuang (parity)
open Q9LaurentGainPartition (Side)
open private star_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentCommonTriple

open scoped Classical in
/-- Every occupied complementary fiber has exactly three vertices, so the
cardinality of the selected parity side is three times the projected cardinality. -/
theorem card_selected_eq_three_mul_card_projection {C : Finset (Q 9)} {b : Bool} {e : Axes}
    (h : UniqueCommonNeighbor C b e) :
    (C.filter fun x => parity x = b).card =
      3 * ((C.filter fun x => parity x = b).image (outside e)).card := by
  classical
  let selected := C.filter fun x => parity x = b
  let projected := selected.image (outside e)
  have hcount (u : Q 6) (hu : u ∈ projected) :
      (selected.filter fun x => outside e x = u).card = 3 := by
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    have hv' := mem_filter.mp hv
    let x : Side C b := ⟨v, hv'.1, hv'.2⟩
    obtain ⟨c, _, _, hfiber⟩ := exists_star_over_projection h x
    change (selected.filter fun v' => outside e v' = outside e v).card = 3
    rw [show (selected.filter fun v' => outside e v' = outside e v) =
      fiber C b e (outside e v) by
        ext w
        simp [selected, fiber, and_assoc]]
    exact (congrArg card hfiber).trans (star_card e c)
  change selected.card = 3 * projected.card
  rw [card_eq_sum_card_image (outside e) selected]
  calc
    (∑ u ∈ projected, (selected.filter fun x => outside e x = u).card) =
        ∑ _u ∈ projected, 3 := Finset.sum_congr rfl hcount
    _ = 3 * projected.card := by simp [Nat.mul_comm]

end Q9LaurentCommonTriple

namespace Q9ProjectedHeightCompatibility

open Finset

/-- The box support is a translate of nine crossing pairs. -/
theorem card_box (p : Bool) (c : Point) :
    (univ.filter fun x : Fin 64 => inBox p c (BitVec.ofFin x)).card = 9 := by
  let box := fun t : Point => univ.filter fun x : Fin 64 => inBox p t (BitVec.ofFin x)
  let translate (x : Fin 64) : Fin 64 := ((BitVec.ofFin x : Point) ^^^ c).toFin
  have hcancel (x : Point) : (x ^^^ c) ^^^ c = x := by
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have hshift (x : Fin 64) : translate (translate x) = x := by
    simp only [translate, BitVec.ofFin_toFin, hcancel, BitVec.toFin_ofFin]
  have hinj : Function.Injective translate := fun x y h => by
    simpa only [hshift] using congrArg translate h
  have himage : (box 0#6).image translate = box c := by
    ext x
    simp only [box, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [inBox, translate, BitVec.ofFin_toFin, hcancel, BitVec.xor_zero] using hy
    · intro hx
      refine ⟨translate x, ?_, hshift x⟩
      simpa only [inBox, translate, BitVec.ofFin_toFin, BitVec.xor_zero] using hx
  change (box c).card = 9
  rw [← himage, card_image_of_injective _ hinj]
  dsimp only [box]
  cases p <;> decide +kernel

open scoped Classical in
/-- A connected union of boxes with a single split and one height has nine
points. Its boxes have one center by the overlap rigidity theorem. -/
theorem card_union_of_connected_uniform_boxes (family : Finset (Bool × Point))
    (hfamily : family.Nonempty) (p : Bool)
    (hsplit : ∀ t ∈ family, t.1 = p) (height : Point → Fin 6 → ℤ)
    (hheight : ∀ t ∈ family, HasBoxHeight height t.1 t.2)
    (hpath : ∀ t ∈ family, ∀ u ∈ family,
      ∀ x y : Point, inBox t.1 t.2 x = true → inBox u.1 u.2 y = true →
        Relation.ReflTransGen (sameBox family) x y) :
    (univ.filter fun x : Fin 64 =>
      ∃ t ∈ family, inBox t.1 t.2 (BitVec.ofFin x) = true).card = 9 := by
  classical
  obtain ⟨t, ht⟩ := hfamily
  have witness (u : Bool × Point) : ∃ x : Point, inBox u.1 u.2 x = true := by
    have hc := card_box u.1 u.2
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 <
      (univ.filter fun x : Fin 64 => inBox u.1 u.2 (BitVec.ofFin x)).card)
    exact ⟨BitVec.ofFin i, (mem_filter.mp hi).2⟩
  have eqBox (u : Bool × Point) (hu : u ∈ family) : u = t := by
    obtain ⟨x, hx⟩ := witness u
    obtain ⟨y, hy⟩ := witness t
    have hc : u.2 = t.2 :=
      equal_center_of_box_path hu ht hheight hx hy (hpath u hu t ht x y hx hy)
    exact Prod.ext ((hsplit u hu).trans (hsplit t ht).symm) hc
  have sole : (univ.filter fun x : Fin 64 =>
      ∃ u ∈ family, inBox u.1 u.2 (BitVec.ofFin x) = true) =
      (univ.filter fun x : Fin 64 => inBox t.1 t.2 (BitVec.ofFin x) = true) := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, hx⟩
      rwa [eqBox u hu] at hx
    · exact fun hx => ⟨t, ht, hx⟩
  rw [sole, card_box]

end Q9ProjectedHeightCompatibility
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions

open Finset
open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9IsotropicHuang (parity)
open Q9LaurentGainPartition (Side Exponent LaurentIdentity)
open Q9LaurentCommonTriple (Axes commonAxes outside exists_projected_exponent)
open Q9ProjectedHeightCompatibility (Point HasBoxHeight inBox sameBox)
open private mem_transverseSide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentTransverseFibers

open scoped Classical in
/-- A constant direction partition, written as the first normalized split,
forces the projection to have nine points. Each has three preimages. -/
theorem card_selected_eq_twentySeven_of_uniform_partition {C : Finset (Q 9)} {b : Bool}
    {a : Side C b → Exponent} (e : Axes)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (base : Side C b)
    (hp : IsTriplePartition (normalizedPartition e false))
    (hq : IsTriplePartition (normalizedPartition e true))
    (hinter : normalizedPartition e false ∩ normalizedPartition e true = {commonAxes e})
    (huniform : ∀ x : Side C b, neighborPartition C x.val = normalizedPartition e false) :
    (C.filter fun x => parity x = b).card = 27 := by
  classical
  have hmem (p : Bool) : commonAxes e ∈ normalizedPartition e p := by
    simp [normalizedPartition]
  have htypes (x : Side C b) : neighborPartition C x.val = normalizedPartition e false ∨
      neighborPartition C x.val = normalizedPartition e true := Or.inl (huniform x)
  have hCommon := Q9LaurentCommonTriple.uniqueCommonNeighbor_of_laurent (e := e) hC h (by
    intro x
    have hx : commonAxes e ∈ neighborPartition C x.val := by
      rw [huniform x]
      exact hmem false
    exact mem_image.mp hx)
  obtain ⟨g, hg⟩ := exists_projected_exponent h hCommon
  let height (v : Point) := g (cubeBitVec 6 v)
  let project (x : Side C b) : Point := (cubeBitVec 6).symm (outside e x.val)
  have hg' (x : Side C b) (j : Fin 6) : height (project x) j = a x (e (.inr j)) := by
    simp only [height, project, Equiv.apply_symm_apply, hg]
  have hBox (x : Side C b) :=
    realize_normalized_component hC h e hp hq hinter htypes height hg' x false (huniform x)
  let box (x : Side C b) : Bool × Point := (false, (hBox x).choose)
  let family : Finset (Bool × Point) := univ.image box
  have hbox_mem (x : Side C b) : box x ∈ family := mem_image.mpr ⟨x, mem_univ _, rfl⟩
  have hbox_height : ∀ t ∈ family, HasBoxHeight height t.1 t.2 := by
    intro t ht
    obtain ⟨x, _, rfl⟩ := mem_image.mp ht
    exact (hBox x).choose_spec.1
  have hbox_cover (x : Side C b) (v : Point) : inBox (box x).1 (box x).2 v = true ↔
      ∃ y ∈ transverseSide (commonAxes e) x, project y = v :=
    (hBox x).choose_spec.2 v
  have hself (x : Side C b) : inBox (box x).1 (box x).2 (project x) = true :=
    (hbox_cover x _).mpr ⟨x, mem_transverseSide.mpr .refl, rfl⟩
  have hstep (x y : Side C b) (v : ↥C)
      (hx : ((hypercube 9).induce (C : Set (Q 9))).Adj ⟨x.val, x.property.1⟩ v)
      (hy : ((hypercube 9).induce (C : Set (Q 9))).Adj v ⟨y.val, y.property.1⟩) :
      Relation.ReflTransGen (sameBox family) (project x) (project y) := by
    rcases transverse_or_same_projection (e := e) hp hq (hmem false) (hmem true)
      htypes x y v hx hy with hxy | hxy
    · exact .single ⟨box x, hbox_mem x, hself x,
        (hbox_cover x _).mpr ⟨y, mem_transverseSide.mpr hxy, rfl⟩⟩
    · have he : project x = project y := congrArg (cubeBitVec 6).symm hxy
      rw [he]
  have hpath (t : Bool × Point) (ht : t ∈ family) (u : Bool × Point) (hu : u ∈ family)
      (v w : Point) (hv : inBox t.1 t.2 v = true) (hw : inBox u.1 u.2 w = true) :
      Relation.ReflTransGen (sameBox family) v w := by
    obtain ⟨x, _, rfl⟩ := mem_image.mp ht
    obtain ⟨y, _, rfl⟩ := mem_image.mp hu
    obtain ⟨x', _, rfl⟩ := (hbox_cover x v).mp hv
    obtain ⟨y', _, rfl⟩ := (hbox_cover y w).mp hw
    exact Q9ProjectedWalk.projected_of_connected project hc hstep x' y'
  have hcard := Q9ProjectedHeightCompatibility.card_union_of_connected_uniform_boxes family
    ⟨box base, hbox_mem base⟩ false
    (by
      intro t ht
      obtain ⟨x, _, rfl⟩ := mem_image.mp ht
      rfl) height hbox_height hpath
  let projected := (C.filter fun x => parity x = b).image (outside e)
  let index (u : Q 6) : Fin 64 := ((cubeBitVec 6).symm u).toFin
  have hinj : Function.Injective index := by
    intro u v he
    apply (cubeBitVec 6).symm.injective
    simpa only [index, BitVec.ofFin_toFin] using congrArg (BitVec.ofFin (w := 6)) he
  have himage : projected.image index = univ.filter fun x : Fin 64 =>
      ∃ t ∈ family, inBox t.1 t.2 (BitVec.ofFin x) = true := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hi
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
      have hx' := mem_filter.mp hx
      let y : Side C b := ⟨x, hx'.1, hx'.2⟩
      exact ⟨box y, hbox_mem y, by simpa only [index, BitVec.ofFin_toFin, project, y] using hself y⟩
    · rintro ⟨t, ht, hi⟩
      obtain ⟨x, _, rfl⟩ := mem_image.mp ht
      obtain ⟨y, _, hproj⟩ := (hbox_cover x _).mp hi
      have hindex : index (outside e y.val) = i := by
        simpa only [index, project, BitVec.toFin_ofFin] using congrArg BitVec.toFin hproj
      exact mem_image.mpr ⟨outside e y.val, mem_image.mpr
        ⟨y.val, mem_filter.mpr ⟨y.property.1, y.property.2⟩, rfl⟩, hindex⟩
  rw [← himage, card_image_of_injective _ hinj] at hcard
  rw [Q9LaurentCommonTriple.card_selected_eq_three_mul_card_projection hCommon]
  change 3 * projected.card = 27
  rw [hcard]

open private exists_third_block from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes

open private exists_other from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentNormalizedBoxes

private theorem exists_companion_partition {P : Partition} {S : Block}
    (hP : IsTriplePartition P) (hS : S ∈ P) :
    ∃ R : Partition, IsTriplePartition R ∧ S ∈ R ∧ P ≠ R := by
  classical
  obtain ⟨A, hA, hAS⟩ := exists_other hP hS
  obtain ⟨B, hB, hBA, hBS⟩ := exists_third_block hP hAS
  have hAB : Disjoint A B := hP.disjoint_blocks hA hB hBA.symm
  have hAS' : Disjoint A S := hP.disjoint_blocks hA hS hAS
  have hBS' : Disjoint B S := hP.disjoint_blocks hB hS hBS
  obtain ⟨i, hi⟩ := card_pos.mp (show 0 < A.card by rw [hP.block_card A hA]; decide)
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < B.card by rw [hP.block_card B hB]; decide)
  have hjA : j ∉ A := fun h => disjoint_left.mp hAB h hj
  have hiS : i ∉ S := disjoint_left.mp hAS' hi
  have hjS : j ∉ S := disjoint_left.mp hBS' hj
  let σ : Equiv.Perm (Fin 9) := Equiv.swap i j
  let move (T : Block) : Block := T.map σ.toEmbedding
  let R := P.image move
  have hinj : Function.Injective move := map_injective _
  have hR : IsTriplePartition R := by
    constructor
    · rw [show R = P.image move by rfl, card_image_of_injective _ hinj, hP.card_eq]
    · intro T ht
      obtain ⟨U, hU, rfl⟩ := mem_image.mp ht
      rw [show move U = _ by rfl, card_map, hP.block_card U hU]
    · intro T ht U hu hne
      obtain ⟨T', ht', rfl⟩ := mem_image.mp ht
      obtain ⟨U', hu', rfl⟩ := mem_image.mp hu
      exact (disjoint_map σ.toEmbedding).mpr
        (hP.disjoint_blocks ht' hu' (fun he => hne (congrArg move he)))
  have hfix : move S = S := by
    ext k
    constructor
    · intro hk
      obtain ⟨l, hl, he⟩ := mem_map.mp hk
      have hli : l ≠ i := fun h => hiS (h ▸ hl)
      have hlj : l ≠ j := fun h => hjS (h ▸ hl)
      change σ l = k at he
      rw [show σ l = l from Equiv.swap_apply_of_ne_of_ne hli hlj] at he
      exact he ▸ hl
    · intro hk
      have hki : k ≠ i := fun h => hiS (h ▸ hk)
      have hkj : k ≠ j := fun h => hjS (h ▸ hk)
      exact mem_map.mpr ⟨k, hk, Equiv.swap_apply_of_ne_of_ne hki hkj⟩
  refine ⟨R, hR, mem_image.mpr ⟨S, hS, hfix⟩, ?_⟩
  intro he
  have hMoveA : move A ∈ P := he.symm ▸ mem_image.mpr ⟨A, hA, rfl⟩
  have hmoved : j ∈ move A := mem_map.mpr ⟨i, hi, Equiv.swap_apply_left i j⟩
  have hne : A ≠ move A := fun h => hjA (h.symm ▸ hmoved)
  obtain ⟨k, hk, hki⟩ := exists_mem_notMem_of_card_lt_card
    (show ({i} : Block).card < A.card by rw [card_singleton, hP.block_card A hA]; decide)
  have hkj : k ≠ j := fun h => hjA (h ▸ hk)
  have hkMove : k ∈ move A := mem_map.mpr
    ⟨k, hk, Equiv.swap_apply_of_ne_of_ne (fun h => hki (mem_singleton.mpr h)) hkj⟩
  exact disjoint_left.mp (hP.disjoint_blocks hA hMoveA hne) hk hkMove

open scoped Classical in
/-- A connected cubic support with at most three direction types has
twenty-seven vertices on either selected parity with Laurent data. -/
theorem card_selected_eq_twentySeven_of_le_three_directionTypes {C : Finset (Q 9)} {b : Bool}
    {a : Side C b → Exponent}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) (x₀ : Side C b) (hsmall : (directionTypes C b).card ≤ 3) :
    (C.filter fun x => parity x = b).card = 27 := by
  classical
  let P := neighborPartition C x₀.val
  have hP : IsTriplePartition P := isTriplePartition_neighborPartition hC h x₀
  have all_eq_types (x : Side C b) : neighborPartition C x.val = directionTypes C b := by
    apply eq_of_subset_of_card_le
    · rw [← blockTypes_partitionsOn hC]
      intro A hA
      exact mem_biUnion.mpr ⟨_, mem_image.mpr ⟨x, mem_univ _, rfl⟩, hA⟩
    · rw [(isTriplePartition_neighborPartition hC h x).card_eq]
      exact hsmall
  have htype (x : Side C b) : neighborPartition C x.val = P :=
    (all_eq_types x).trans (all_eq_types x₀).symm
  obtain ⟨S, hS⟩ := card_pos.mp (show 0 < P.card by rw [hP.card_eq]; decide)
  obtain ⟨R, hR, hSR, hne⟩ := exists_companion_partition hP hS
  obtain ⟨e, hSe, hPe, hRe⟩ := exists_normalized_partitions hP hR hS hSR hne
  have hi : normalizedPartition e false ∩ normalizedPartition e true = {commonAxes e} := by
    rw [hPe, hRe, hSe]
    exact inter_eq_singleton hP hR hne hS hSR
  exact card_selected_eq_twentySeven_of_uniform_partition e hc hC h x₀
    (hPe.symm ▸ hP) (hRe.symm ▸ hR) hi (fun x => (htype x).trans hPe.symm)

open BalancedCriticalSpectrum (flip)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open private cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LaurentGainPartition

open scoped Classical in
private theorem card_eq_twice_selected {C : Finset (Q 9)} (b : Bool)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    C.card = 2 * (C.filter fun x => parity x = b).card := by
  classical
  let G := (hypercube 9).induce (C : Set (Q 9))
  let part (q : Bool) : Finset (↥C) := univ.filter fun x => parity x.val = q
  have hBi : G.IsBipartiteWith (part b : Set (↥C)) (part (!b) : Set (↥C)) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hx' := (mem_filter.mp (show x ∈ part b from hx)).2
      have hy' := (mem_filter.mp (show x ∈ part (!b) from hy)).2
      have he := hx'.symm.trans hy'
      cases b <;> contradiction
    · intro x y hxy
      have hp : parity y.val = !parity x.val :=
        Bool.eq_not_of_ne (Ne.symm (cubeParity_ne_of_adj hxy))
      by_cases hx : parity x.val = b
      · exact Or.inl ⟨mem_filter.mpr ⟨mem_univ _, hx⟩,
          mem_filter.mpr ⟨mem_univ _, hp.trans (congrArg Bool.not hx)⟩⟩
      · have hx' := Bool.eq_not_of_ne hx
        have hy : parity y.val = b := by rw [hp, hx', Bool.not_not]
        exact Or.inr ⟨mem_filter.mpr ⟨mem_univ _, hx'⟩, mem_filter.mpr ⟨mem_univ _, hy⟩⟩
  have hdeg (x : ↥C) : G.degree x = 3 := hC.degree_eq x
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq hBi
  simp only [hdeg, sum_const, smul_eq_mul] at hsum
  have hcard (q : Bool) : (part q).card = (C.filter fun x => parity x = q).card := by
    let toCube : ↥C ↪ Q 9 := ⟨Subtype.val, Subtype.val_injective⟩
    have he : (part q).map toCube = C.filter fun x => parity x = q := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
        exact mem_filter.mpr ⟨u.property, (mem_filter.mp hu).2⟩
      · intro hx
        obtain ⟨hxC, hxq⟩ := mem_filter.mp hx
        exact mem_map.mpr ⟨⟨x, hxC⟩, mem_filter.mpr ⟨mem_univ _, hxq⟩, rfl⟩
    rw [← he, card_map]
  rw [hcard b, hcard (!b)] at hsum
  have hu : C.filter (fun x => parity x = b) ∪ C.filter (fun x => parity x = !b) = C := by
    ext x
    simp only [mem_union, mem_filter]
    cases b <;> cases parity x <;> simp
  have hd : Disjoint (C.filter (fun x => parity x = b)) (C.filter (fun x => parity x = !b)) := by
    apply disjoint_left.mpr
    intro x hx hy
    have he := (mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2
    cases b <;> contradiction
  have htotal := card_union_of_disjoint hd
  rw [hu] at htotal
  omega

open scoped Classical in
/-- A connected induced cubic support in the one-sided Laurent regime has
order fifty-four or at least seven opposite-parity direction types. -/
theorem card_eq_fiftyFour_or_seven_le_directionTypes {C : Finset (Q 9)} {b : Bool}
    {a : Side C b → Exponent}
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : LaurentIdentity a) : C.card = 54 ∨ 7 ≤ (directionTypes C b).card := by
  classical
  rcases card_directionTypes_le_three_or_eq_five_or_ge_seven hc hC h with hsmall | hfive | hlarge
  · left
    obtain ⟨v⟩ := hc.nonempty
    have hx : Nonempty (Side C b) := by
      by_cases hp : parity v.val = b
      · exact ⟨⟨v.val, v.property, hp⟩⟩
      · have hdeg := regular_directions C hC v.property
        obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (directions C v.val).card by omega)
        have hflip : parity (flip v.val i) = b := by
          rw [flip_parity, Bool.eq_not_of_ne hp, Bool.not_not]
        exact ⟨⟨flip v.val i, (mem_directions C _ _).mp hi, hflip⟩⟩
    obtain ⟨x⟩ := hx
    rw [card_eq_twice_selected b hC, card_selected_eq_twentySeven_of_le_three_directionTypes hc hC h x hsmall]
  · exact (card_directionTypes_ne_five hc hC h hfive).elim
  · exact Or.inr hlarge

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TriplePartitions
