/- GID: D5/S3/Geometry/FiniteComponentClosure
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Selected-vertex WPlus wedges and complete finite-component ordinary joins preserve finite sphere-component models. -/
import D5.S3.Geometry.FiniteComponentClosure.JoinModels

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

set_option maxSynthPendingDepth 12

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  joinHomeomorph
  coneBaseSuspensionHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.Transport

open private
  based_normalization
  vertexGluingHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.Models

open private
  nativeConeBaseHomeomorph
  auxiliaryBaseSplit
  disjointJoinConeSplit
  from D5.S3.Geometry.FiniteComponentClosure.ConeSplits

open private
  connectedVertexGluingHomeomorph
  selectedComponentWedgeBased
  selectedComponentWedgeCarrier
  normalWedgeHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.SelectedWedge

open private
  basedTrans
  basedHomeomorphism
  nativeConeRebasedCollapse
  unionConeCollapseBased
  auxiliaryBasedQuotientSplit
  nativeConeSuspensionHomeomorph
  nativeConeSuspension_base
  twoComponentJoinBased
  vertexUnionJoinBased
  nativeBouquetNormalization
  basedBouquetAppend
  from D5.S3.Geometry.FiniteComponentClosure.BasedJoin

open private
  familyJoinBased
  nativeJoinCongr
  spherePairJoinNormalization
  vertexFamilyJoinBased
  bouquetFamilyJoinNormalization
  bouquetPairJoinSpec
  bouquetPairJoinNormalization
  bouquetSuspensionSpec
  bouquetSuspensionNormalization
  normalSuspensionSpec
  bouquetNormalJoinSpec
  constructedJoinSpec
  constructedNormalJoinNormalization
  sameMultiplicityBouquetHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.JoinModels

section CompleteJoinDimensions

private def copies (k : ℕ) (ds : BouquetSpec) : BouquetSpec := (List.replicate k ds).flatten

/-- All sphere-join, suspension, and circle terms, counted with their actual multiplicities. -/
def finiteJoinSpec (m : ℕ) (p : Fin m → BouquetSpec)
    (n : ℕ) (q : Fin n → BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun i => (List.ofFn (fun j => bouquetPairJoinSpec (p i) (q j))).flatten)).flatten ++
  (List.ofFn (fun i => copies (n - 1) (bouquetSuspensionSpec (p i)))).flatten ++
  (List.ofFn (fun j => copies (m - 1) (bouquetSuspensionSpec (q j)))).flatten ++
  List.replicate ((m - 1) * (n - 1)) ⟨1, by omega⟩

private theorem countCopies (k : ℕ) (ds : BouquetSpec) (d : {n : ℕ // 0 < n}) :
    (copies k ds).count d = k * ds.count d := by
  induction k with
  | zero => simp [copies]
  | succ k ih =>
    change ((ds ++ copies k ds).count d) = _
    rw [List.count_append, ih, Nat.succ_mul]
    omega

private theorem countOfFnFlatten {k : ℕ} (f : Fin k → BouquetSpec) (d : {n : ℕ // 0 < n}) :
    ((List.ofFn f).flatten).count d = ∑ i, (f i).count d := by
  rw [List.count_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem copiesSingleton (k : ℕ) (d : {n : ℕ // 0 < n}) :
    copies k [d] = List.replicate k d := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [copies, List.replicate_succ, List.flatten_cons,
      List.singleton_append] using congrArg (List.cons d) ih

private theorem constructedJoinSpec_count (m : ℕ) (p : Fin m → BouquetSpec)
    (n : ℕ) (q : Fin n → BouquetSpec) (d : {n : ℕ // 0 < n}) :
    (constructedJoinSpec m p n q).count d = (finiteJoinSpec m p n q).count d := by
  simp only [constructedJoinSpec, bouquetNormalJoinSpec, normalSuspensionSpec, finiteJoinSpec]
  rw [← copiesSingleton ((m - 1) * (n - 1)) ⟨1, by omega⟩]
  change (((List.ofFn (fun i =>
    (List.ofFn (fun j => bouquetPairJoinSpec (p i) (q j))).flatten ++
      copies (n - 1) (bouquetSuspensionSpec (p i)))).flatten ++
    copies (m - 1) ((List.ofFn (fun j => bouquetSuspensionSpec (q j))).flatten ++
      copies (n - 1) [⟨1, by omega⟩])).count d) = _
  simp only [List.count_append, countOfFnFlatten, countCopies, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

private def completeNormalJoinNormalization (m : ℕ) (hm : 0 < m) (p : Fin m → BouquetSpec)
    (n : ℕ) (hn : 0 < n) (q : Fin n → BouquetSpec) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (normalComplex m p) (normalComplex n q)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (finiteJoinSpec m p n q)) :=
  (constructedNormalJoinNormalization m hm p n hn q).trans
    (sameMultiplicityBouquetHomeomorph _ _ (constructedJoinSpec_count m p n q)).toHomotopyEquiv

end CompleteJoinDimensions

section CompleteJoinClosure

private def singleNormalHomeomorph (ds : BouquetSpec) :
    FiniteSimplicialJoin.Space (normalComplex 1 (fun _ => ds)) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex ds) := by
  let e : (Σ _ : Fin 1, FiniteSimplicialJoin.Space (bouquetComplex ds)) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex ds) := {
    toFun := fun x => x.2
    invFun := fun x => ⟨0, x⟩
    left_inv := by
      rintro ⟨i, x⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_sigma (fun _ => continuous_id)
    continuous_invFun := @continuous_sigmaMk (Fin 1)
      (fun _ => FiniteSimplicialJoin.Space (bouquetComplex ds)) _ 0 }
  exact (normalHomeomorph 1 (fun _ => ds)).trans e

/-- Exact finite-component join closure, including both native and ordinary quotient carriers. -/
structure FiniteComponentJoinClosure {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W) where
  leftCount : ℕ
  leftPositive : 0 < leftCount
  leftSpec : Fin leftCount → BouquetSpec
  rightCount : ℕ
  rightPositive : 0 < rightCount
  rightSpec : Fin rightCount → BouquetSpec
  leftNormalization : FiniteSimplicialJoin.Space K ≃ₕ
    FiniteSimplicialJoin.Space (normalComplex leftCount leftSpec)
  rightNormalization : FiniteSimplicialJoin.Space L ≃ₕ
    FiniteSimplicialJoin.Space (normalComplex rightCount rightSpec)
  equivalence : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin K L) ≃ₕ
    FiniteSimplicialJoin.Space (bouquetComplex (finiteJoinSpec leftCount leftSpec rightCount rightSpec))
  based : ∀ (z : V ⊕ W) (hz : ({z} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin K L),
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin K L) z hz)
      (bouquetPoint (finiteJoinSpec leftCount leftSpec rightCount rightSpec))
  ordinaryEquivalence : FiniteSimplicialJoin.OrdinaryJoin
    (FiniteSimplicialJoin.Space K) (FiniteSimplicialJoin.Space L) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (finiteJoinSpec leftCount leftSpec rightCount rightSpec))
  ordinaryBased : ∀ (z : V ⊕ W)
    (hz : ({z} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin K L),
    SingletonRetractionBasedInverse.BasedEquivalence
      ((FiniteSimplicialJoin.joinHomeomorph K L
        ⟨leftNormalization.invFun (normalPoint leftCount leftSpec ⟨0, leftPositive⟩)⟩
        ⟨rightNormalization.invFun (normalPoint rightCount rightSpec ⟨0, rightPositive⟩)⟩).symm
          (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin K L) z hz))
      (bouquetPoint (finiteJoinSpec leftCount leftSpec rightCount rightSpec))
  wplus : WPlus (FiniteSimplicialJoin.simplicialJoin K L)

/-- Construct the full finite-component join formula without quotient HEP assumptions. -/
def finiteComponentJoinClosure {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L) : FiniteComponentJoinClosure K L := by
  have h : Nonempty (FiniteComponentJoinClosure K L) := by
    obtain ⟨m, hm, p, ⟨EK⟩⟩ := hK
    obtain ⟨n, hn, q, ⟨EL⟩⟩ := hL
    let x := normalPoint m p ⟨0, hm⟩
    let y := normalPoint n q ⟨0, hn⟩
    let hk : Nonempty (FiniteSimplicialJoin.Space K) := ⟨EK.invFun x⟩
    let hl : Nonempty (FiniteSimplicialJoin.Space L) := ⟨EL.invFun y⟩
    let e := (nativeJoinCongr K L (normalComplex m p) (normalComplex n q)
      hk hl ⟨x⟩ ⟨y⟩ EK EL).trans (completeNormalJoinNormalization m hm p n hn q)
    let E := fun (z : V ⊕ W)
        (hz : ({z} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin K L) =>
      nativeBouquetNormalization
      (FiniteSimplicialJoin.simplicialJoin K L) z hz (finiteJoinSpec m p n q) e
    let j := FiniteSimplicialJoin.joinHomeomorph K L hk hl
    refine ⟨{
      leftCount := m
      leftPositive := hm
      leftSpec := p
      rightCount := n
      rightPositive := hn
      rightSpec := q
      leftNormalization := EK
      rightNormalization := EL
      equivalence := e
      based := E
      ordinaryEquivalence := j.toHomotopyEquiv.trans e
      ordinaryBased := fun z hz => basedTrans
        (basedHomeomorphism j (j.symm (FiniteVertexCylinder.vertexPoint _ z hz))
          (FiniteVertexCylinder.vertexPoint _ z hz) (j.apply_symm_apply _)) (E z hz)
      wplus := ⟨1, by omega, (fun _ => finiteJoinSpec m p n q),
        ⟨e.trans (singleNormalHomeomorph (finiteJoinSpec m p n q)).symm.toHomotopyEquiv⟩⟩ }⟩
  exact Classical.choice h

/-- An empty whole left factor gives an empty ordinary join. -/
def ordinaryJoinEmptyLeft {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : IsEmpty X) : FiniteSimplicialJoin.OrdinaryJoin X Y → PEmpty.{1} :=
  Quotient.lift (fun p => False.elim (h.false p.1))
    (fun p _ _ => False.elim (h.false p.1))

/-- An empty whole right factor gives an empty ordinary join. -/
def ordinaryJoinEmptyRight {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : IsEmpty Y) : FiniteSimplicialJoin.OrdinaryJoin X Y → PEmpty.{1} :=
  Quotient.lift (fun p => False.elim (h.false p.2.1))
    (fun p _ _ => False.elim (h.false p.2.1))

end CompleteJoinClosure

#print axioms finiteComponentJoinClosure
#print axioms ordinaryJoinEmptyLeft
#print axioms ordinaryJoinEmptyRight
#print axioms completeNormalJoinNormalization
#print axioms sameMultiplicityBouquetHomeomorph
#print axioms constructedNormalJoinNormalization
#print axioms bouquetPairJoinNormalization
#print axioms bouquetSuspensionNormalization
#print axioms bouquetFamilyJoinNormalization
#print axioms vertexFamilyJoinBased
#print axioms spherePairJoinNormalization
#print axioms familyJoinBased
#print axioms basedBouquetAppend
#print axioms vertexUnionJoinBased
#print axioms twoComponentJoinBased
#print axioms nativeConeSuspensionHomeomorph
#print axioms nativeConeSuspension_base
#print axioms auxiliaryBasedQuotientSplit
#print axioms unionConeCollapseBased
#print axioms nativeConeRebasedCollapse
#print axioms selectedVertexWedgeClosure
#print axioms normalWedgeHomeomorph
#print axioms sphereHomeomorph
#print axioms bouquetQuotientHomeomorph
#print axioms normalHomeomorph
#print axioms based_normalization
#print axioms disjointJoinConeSplit
#print axioms coneBaseSuspensionHomeomorph
#print axioms nativeConeBaseHomeomorph
#print axioms auxiliaryBaseSplit
#print axioms vertexGluingHomeomorph
#print axioms connectedVertexGluingHomeomorph
#print axioms selectedComponentWedgeBased
#print axioms selectedComponentWedgeCarrier

end D5.S3.Geometry.FiniteComponentClosure
