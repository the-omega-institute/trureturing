/- GID: D5/S3/Geometry/CompactSphereNormalForm
   generality: G
   mirror-B: D5/B/S3/Geometry/CompactSphereNormalForm
   mirror-E: none(waiver:compact-sphere-normal-form)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Compact sphere coproduct models transport to finite positive bouquet lists. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.SphereWedgePositiveNormalization
import D5.S3.Geometry.FiniteComponentClosure
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Homotopy.Contractible

/-! Source adapters for the unsuspended hereditary W route of Carnero Bravo
Question 22. Actual source sphere quotient models are identified with native
finite component carriers for consumption by the graph composition proof. -/

noncomputable section
open Set Topology
open scoped ContinuousMap

namespace D5.S3.Geometry.CompactSphereNormalForm

open CompactWedgeFiniteFactor (FamilyWedge base basePoints WedgeSum)
open SphereWedgePositiveNormalization (PositiveIndex ZeroIndex PositiveWedge)
open EuclideanSphereJoin (StdSphere coordinatePoint)
open FiniteConeUnionWedge (subsetSetoid)

universe u v w

/-- Dimensions in the finite output are strictly positive. -/
abbrev PositiveDimension := {d : ℕ // 0 < d}

/-- The genuine quotient bouquet at the coordinate points. The empty list is a point. -/
abbrev Bouquet (l : List PositiveDimension) :=
  FamilyWedge (fun i : Fin l.length => coordinatePoint (l.get i).val)

/-- A finite outer coproduct of the actual positive sphere bouquets. -/
abbrev Model {m : ℕ} (b : Fin m → List PositiveDimension) := Σ k, Bouquet (b k)

/-- Output data, including the actual maps and both inverse homotopies. -/
structure HomotopyModel (X : Type w) [TopologicalSpace X] where
  size : ℕ
  bouquets : Fin size → List PositiveDimension
  equivalence : X ≃ₕ Model bouquets

private instance emptyBouquetUnique : Unique (Bouquet []) where
  default := base _
  uniq x := by
    induction x using Quotient.inductionOn with
    | h x =>
      rcases x with x | ⟨i, x⟩
      · cases x; rfl
      · exact Fin.elim0 i

private def sphereCast {n m : ℕ} (h : n = m) : StdSphere n ≃ₜ StdSphere m := by
  subst m
  exact Homeomorph.refl _

private theorem sphereCast_base {n m : ℕ} (h : n = m) :
    sphereCast h (coordinatePoint n) = coordinatePoint m := by
  subst m
  rfl

/-- Enumerate the dimensions of a finite positive sphere family, retaining multiplicities. -/
def dimensionList {J : Type u} [Fintype J] (n : J → PositiveDimension) :
    List PositiveDimension :=
  List.ofFn (fun i => n ((Fintype.equivFin J).symm i))

private def listIndex {J : Type u} [Fintype J] (n : J → PositiveDimension) :
    J ≃ Fin (dimensionList n).length :=
  (Fintype.equivFin J).trans (finCongr (by simp [dimensionList]))

private theorem list_dimension {J : Type u} [Fintype J]
    (n : J → PositiveDimension) (j : J) :
    ((dimensionList n).get (listIndex n j)).val = (n j).val := by
  have hv : (listIndex n j).val = (Fintype.equivFin J j).val := rfl
  simp only [List.get_eq_getElem, dimensionList, List.getElem_ofFn]
  apply congrArg (fun k : J => (n k).val)
  apply (Fintype.equivFin J).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext hv

private abbrev familyBase {J : Type u} (n : J → PositiveDimension) :=
  fun j => coordinatePoint (n j).val

private abbrev listBase {J : Type u} [Fintype J] (n : J → PositiveDimension) :=
  fun i : Fin (dimensionList n).length => coordinatePoint ((dimensionList n).get i).val

private def listSphere {J : Type u} [Fintype J] (n : J → PositiveDimension) (j : J) :
    StdSphere (n j).val ≃ₜ StdSphere ((dimensionList n).get (listIndex n j)).val :=
  sphereCast (list_dimension n j).symm

private theorem listSphere_base {J : Type u} [Fintype J]
    (n : J → PositiveDimension) (j : J) :
    listSphere n j (familyBase n j) = listBase n (listIndex n j) := sphereCast_base _

private def listSigma {J : Type u} [Fintype J] (n : J → PositiveDimension) :
    (Σ j, StdSphere (n j).val) ≃ₜ
      (Σ i : Fin (dimensionList n).length, StdSphere ((dimensionList n).get i).val) :=
  (Equiv.sigmaCongr (listIndex n) (fun j => (listSphere n j).toEquiv))
    |>.toHomeomorphOfContinuousOpen
      (continuous_sigma_iff.mpr (fun j => by
        change Continuous (fun x => (@Sigma.mk (Fin (dimensionList n).length)
          (fun i => StdSphere ((dimensionList n).get i).val) (listIndex n j))
            (listSphere n j x))
        exact continuous_sigmaMk.comp (listSphere n j).continuous))
      (isOpenMap_sigma.mpr (fun j => by
        change IsOpenMap (fun x => (@Sigma.mk (Fin (dimensionList n).length)
          (fun i => StdSphere ((dimensionList n).get i).val) (listIndex n j))
            (listSphere n j x))
        exact isOpenMap_sigmaMk.comp (listSphere n j).isOpenMap))

private def listRaw {J : Type u} [Fintype J] (n : J → PositiveDimension) :=
  Homeomorph.sumCongr (Homeomorph.refl Unit) (listSigma n)

private theorem listRaw_bases {J : Type u} [Fintype J] (n : J → PositiveDimension)
    (x : Unit ⊕ (Σ j, StdSphere (n j).val)) :
    x ∈ basePoints (familyBase n) ↔ listRaw n x ∈ basePoints (listBase n) := by
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨listIndex n j,
        congrArg Sum.inr (congrArg (Sigma.mk (listIndex n j)) (listSphere_base n j))⟩
  · rintro (hx | ⟨i, hx⟩)
    · left
      exact (listRaw n).injective hx
    · obtain ⟨j, rfl⟩ := (listIndex n).surjective i
      right
      refine ⟨j, (listRaw n).injective ?_⟩
      exact hx.trans (congrArg Sum.inr
        (congrArg (Sigma.mk (listIndex n j)) (listSphere_base n j))).symm

/-- Actual pointed quotient reindexing from a finite positive family to its list.
The dimension casts carry coordinate points to coordinate points. -/
def positiveListHomeomorph {J : Type u} [Fintype J] (n : J → PositiveDimension) :
    {e : FamilyWedge (fun j => coordinatePoint (n j).val) ≃ₜ Bouquet (dimensionList n) //
      e (base _) = base _} := by
  let Q : FamilyWedge (familyBase n) ≃ₜ FamilyWedge (listBase n) :=
    Homeomorph.Quotient.congr (listRaw n) (by
      intro x y
      change (x = y ∨ (x ∈ basePoints (familyBase n) ∧ y ∈ basePoints (familyBase n))) ↔
        (listRaw n x = listRaw n y ∨
          (listRaw n x ∈ basePoints (listBase n) ∧ listRaw n y ∈ basePoints (listBase n)))
      rw [(listRaw n).injective.eq_iff, ← listRaw_bases n x, ← listRaw_bases n y])
  exact ⟨Q, rfl⟩

section FiniteCoproduct

variable {A : Type u} [Fintype A] {I : A → Type v} [∀ a, Fintype (I a)]
    (d : ∀ a, I a → ℕ) (q : ∀ a j, StdSphere (d a j))

private instance zeroIndexFintype (a : A) : Fintype (ZeroIndex (d a)) :=
  inferInstanceAs (Fintype {j : I a // d a j = 0})

private abbrev Component := A ⊕ (Σ a, ZeroIndex (d a))

private def componentList : Component d → List PositiveDimension :=
  Sum.elim (fun a => dimensionList (fun j : PositiveIndex (d a) => ⟨d a j.val, j.property⟩))
    (fun _ => [])

private def positiveListsHomeomorph : (Σ a, PositiveWedge (d a)) ≃ₜ
    (Σ a, Bouquet (componentList d (Sum.inl a))) :=
  (Equiv.sigmaCongrRight (fun a =>
    (positiveListHomeomorph (fun j : PositiveIndex (d a) =>
      ⟨d a j.val, j.property⟩)).val.toEquiv)).toHomeomorphOfContinuousOpen
    (continuous_sigma_iff.mpr (fun a =>
      continuous_sigmaMk.comp
        (positiveListHomeomorph (fun j : PositiveIndex (d a) =>
          ⟨d a j.val, j.property⟩)).val.continuous))
    (isOpenMap_sigma.mpr (fun a =>
      isOpenMap_sigmaMk.comp
        (positiveListHomeomorph (fun j : PositiveIndex (d a) =>
          ⟨d a j.val, j.property⟩)).val.isOpenMap))

private def isolatedListsHomeomorph : (Σ a, ZeroIndex (d a)) ≃ₜ
    (Σ z : (Σ a, ZeroIndex (d a)), Bouquet (componentList d (Sum.inr z))) :=
  (Equiv.sigmaUnique _ (fun _ => Bouquet [])).symm.toHomeomorphOfDiscrete

private def componentDistributeHomeomorph : (Σ c : Component d, Bouquet (componentList d c)) ≃ₜ
    (Σ a, Bouquet (componentList d (Sum.inl a))) ⊕
      (Σ z : (Σ a, ZeroIndex (d a)), Bouquet (componentList d (Sum.inr z))) where
  toEquiv := Equiv.sumSigmaDistrib (fun c : Component d => Bouquet (componentList d c))
  continuous_toFun := continuous_sigma_iff.mpr (by
    rintro (a | z)
    · exact continuous_inl.comp continuous_sigmaMk
    · exact continuous_inr.comp continuous_sigmaMk)
  continuous_invFun := Continuous.sumElim
    (continuous_sigma_iff.mpr (fun a => by
      change Continuous (@Sigma.mk (Component d) (fun c => Bouquet (componentList d c)) (Sum.inl a))
      exact continuous_sigmaMk))
    (continuous_sigma_iff.mpr (fun z => by
      change Continuous (@Sigma.mk (Component d) (fun c => Bouquet (componentList d c)) (Sum.inr z))
      exact continuous_sigmaMk))

private def componentEnumerateHomeomorph :
    (Σ k : Fin (Fintype.card (Component d)),
      Bouquet (componentList d ((Fintype.equivFin (Component d)).symm k))) ≃ₜ
      (Σ c : Component d, Bouquet (componentList d c)) :=
  (Equiv.sigmaCongrLeft (β := fun c : Component d => Bouquet (componentList d c))
    (Fintype.equivFin (Component d)).symm).toHomeomorphOfContinuousOpen
    (continuous_sigma_iff.mpr (fun k => by
      change Continuous (@Sigma.mk (Component d) (fun c => Bouquet (componentList d c))
        ((Fintype.equivFin (Component d)).symm k))
      exact continuous_sigmaMk))
    (isOpenMap_sigma.mpr (fun k => by
      change IsOpenMap (@Sigma.mk (Component d) (fun c => Bouquet (componentList d c))
        ((Fintype.equivFin (Component d)).symm k))
      exact isOpenMap_sigmaMk))

/-- Reassemble the normalized positive bouquets and all isolated S0 poles into
one dependent finite coproduct, then enumerate that coproduct by Fin. -/
def finiteCoproductHomeomorph :
    (Σ a, FamilyWedge (q a)) ≃ₜ
      Model (fun k : Fin (Fintype.card (Component d)) =>
        componentList d ((Fintype.equivFin (Component d)).symm k)) :=
  (SphereWedgePositiveNormalization.coproductNormalizationHomeomorph d q).val.trans
    ((Homeomorph.sumCongr (positiveListsHomeomorph d) (isolatedListsHomeomorph d)).trans
      ((componentDistributeHomeomorph d).symm.trans (componentEnumerateHomeomorph d).symm))

private def finiteCoproductModel : HomotopyModel (Σ a, FamilyWedge (q a)) where
  size := Fintype.card (Component d)
  bouquets := fun k => componentList d ((Fintype.equivFin (Component d)).symm k)
  equivalence := (finiteCoproductHomeomorph d q).toHomotopyEquiv

end FiniteCoproduct

open private SphereWedgePositiveNormalization.spherePointHomeomorph from
  D5.S3.Geometry.SphereWedgePositiveNormalization

section NativeCarrier

private theorem basePoints_factor {J : Type*} {Z : J → Type*} (q : ∀ j, Z j)
    (j : J) (x : Z j) :
    Sum.inr (Sigma.mk j x) ∈ basePoints q ↔ x = q j := by
  constructor
  · rintro (h | ⟨k, h⟩)
    · cases h
    · have hk : j = k := congrArg Sigma.fst (Sum.inr.inj h)
      subst k
      exact sigma_mk_injective (Sum.inr.inj h)
  · rintro rfl
    exact Or.inr ⟨j, rfl⟩

private def nativeSphereRebase (b : List PositiveDimension) (i : Fin b.length) :=
  SphereWedgePositiveNormalization.spherePointHomeomorph (b.get i).val
    (FiniteComponentClosure.standardSphereBase (b.get i).val)

private def nativeSphereFamily (b : List PositiveDimension) :
    (Σ i : Fin b.length, StdSphere (b.get i).val) ≃ₜ
      (Σ i : Fin b.length, StdSphere (b.get i).val) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (nativeSphereRebase b i).val.toEquiv)
  continuous_toFun := continuous_sigma (fun i =>
    continuous_sigmaMk.comp (nativeSphereRebase b i).val.continuous)
  continuous_invFun := continuous_sigma (fun i =>
    continuous_sigmaMk.comp (nativeSphereRebase b i).val.symm.continuous)

private def standardCoordinateBouquetHomeomorph (b : List PositiveDimension) :
    FiniteComponentClosure.StandardBouquet b ≃ₜ Bouquet b := by
  let raw := (Homeomorph.refl Unit).sumCongr (nativeSphereFamily b)
  apply Homeomorph.Quotient.congr raw
  have hb (z : FiniteComponentClosure.StandardBouquetSource b) :
      Sum.elim (fun _ => True)
        (fun x => x.2 = FiniteComponentClosure.standardSphereBase (b.get x.1).val) z ↔
      raw z ∈ basePoints (fun i : Fin b.length => coordinatePoint (b.get i).val) := by
    rcases z with z | ⟨i, x⟩
    · cases z
      exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
    · change x = FiniteComponentClosure.standardSphereBase (b.get i).val ↔
        Sum.inr (Sigma.mk i ((nativeSphereRebase b i).val x)) ∈
          basePoints (fun i : Fin b.length => coordinatePoint (b.get i).val)
      rw [basePoints_factor]
      constructor
      · intro h
        exact (congrArg (nativeSphereRebase b i).val h).trans (nativeSphereRebase b i).property
      · intro h
        exact (nativeSphereRebase b i).val.injective
          (h.trans (nativeSphereRebase b i).property.symm)
  intro z w
  change (z = w ∨ (_ ∧ _)) ↔ (raw z = raw w ∨ (_ ∧ _))
  rw [raw.injective.eq_iff, ← hb z, ← hb w]
  rfl

/-- Actual native finite bouquet to coordinate-based sphere quotient transport.
The native sphere basepoints are moved by the original sphere reflection. -/
def nativeBouquetHomeomorph (b : List PositiveDimension) :
    FiniteSimplicialJoin.Space (FiniteComponentClosure.bouquetComplex b) ≃ₜ Bouquet b :=
  (FiniteComponentClosure.standardBouquetHomeomorph b).trans
    (standardCoordinateBouquetHomeomorph b)

/-- The finite native component carrier is the actual finite outer sphere model. -/
def nativeModelHomeomorph (m : ℕ) (b : Fin m → List PositiveDimension) :
    FiniteSimplicialJoin.Space (FiniteComponentClosure.normalComplex m b) ≃ₜ Model b :=
  (FiniteComponentClosure.normalHomeomorph m b).trans {
    toEquiv := Equiv.sigmaCongrRight (fun i => (nativeBouquetHomeomorph (b i)).toEquiv)
    continuous_toFun := continuous_sigma (fun i =>
      continuous_sigmaMk.comp (nativeBouquetHomeomorph (b i)).continuous)
    continuous_invFun := continuous_sigma (fun i =>
      continuous_sigmaMk.comp (nativeBouquetHomeomorph (b i)).symm.continuous) }

#print axioms nativeBouquetHomeomorph
#print axioms nativeModelHomeomorph

end NativeCarrier

section CompactSource

variable {X : Type w} [TopologicalSpace X]

/-- An empty source has zero outer summands, not a one-point bouquet. -/
def emptyModel [IsEmpty X] : HomotopyModel X where
  size := 0
  bouquets := Fin.elim0
  equivalence := (Homeomorph.empty : X ≃ₜ Model (Fin.elim0 : Fin 0 → _)).toHomotopyEquiv

private theorem model_size_pos [Nonempty X] (M : HomotopyModel X) : 0 < M.size :=
  Nat.zero_lt_of_lt (M.equivalence.toFun (Classical.choice inferInstance)).1.isLt

private def compactSelectedModel [CompactSpace X] [Nonempty X]
    {A : Type u} {I : A → Type v} (d : ∀ a, I a → ℕ)
    (q : ∀ a j, StdSphere (d a j)) (e : X ≃ₕ WedgeSum q) : HomotopyModel X := by
  let R := CompactWedgeFiniteFactor.finiteFactor q e.toFun
  let d' := fun (a : R.outer) (j : R.inner a) => d a.val j.val
  let q' := fun (a : R.outer) (j : R.inner a) => q a.val j.val
  let N := finiteCoproductModel d' q'
  exact {
    size := N.size
    bouquets := N.bouquets
    equivalence := (CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv q e).trans N.equivalence }

/-- Compact nonempty sources with arbitrary sphere-coproduct models have actual
finite positive-list models, with strictly positive outer size. -/
def nonemptyCompactModel [CompactSpace X] [Nonempty X]
    {A : Type u} {I : A → Type v} (d : ∀ a, I a → ℕ)
    (q : ∀ a j, StdSphere (d a j)) (e : X ≃ₕ WedgeSum q) :
    {M : HomotopyModel X // 0 < M.size} :=
  ⟨compactSelectedModel d q e, model_size_pos _⟩

/-- Transport from an arbitrary sphere-coproduct source model. Neither original
index family is assumed finite; compactness produces the finite selections. -/
def compactModel [CompactSpace X] {A : Type u} {I : A → Type v}
    (d : ∀ a, I a → ℕ) (q : ∀ a j, StdSphere (d a j))
    (e : X ≃ₕ WedgeSum q) : HomotopyModel X := by
  classical
  by_cases h : Nonempty X
  · letI := h
    exact (nonemptyCompactModel d q e).val
  · letI : IsEmpty X := ⟨fun x => h ⟨x⟩⟩
    exact emptyModel

/-- The single arbitrary wedge alternative uses an actual one-summand
coproduct homeomorphism before the compact transport. -/
def compactWedgeModel [CompactSpace X] {J : Type v} (d : J → ℕ)
    (q : ∀ j, StdSphere (d j)) (e : X ≃ₕ FamilyWedge q) : HomotopyModel X := by
  let one : (Σ _ : Unit, FamilyWedge q) ≃ₜ FamilyWedge q := {
    toFun := fun x => x.2
    invFun := fun x => ⟨(), x⟩
    left_inv := by rintro ⟨a, x⟩; cases a; rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_sigma_iff.mpr (fun _ => continuous_id)
    continuous_invFun := (continuous_sigmaMk : Continuous
      (@Sigma.mk Unit (fun _ => FamilyWedge q) ())) }
  exact compactModel (fun _ : Unit => d) (fun _ : Unit => q)
    (e.trans one.symm.toHomotopyEquiv)

/-- The contractible alternative has one empty bouquet, with actual maps. -/
def contractibleModel [ContractibleSpace X] : HomotopyModel X := by
  letI : Unique (Model (fun _ : Fin 1 => ([] : List PositiveDimension))) :=
    { default := ⟨0, default⟩
      uniq := by
        rintro ⟨i, x⟩
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact congrArg (Sigma.mk 0) (Subsingleton.elim x default) }
  exact ⟨1, fun _ => [], (ContractibleSpace.hequiv_unit X).some.trans
    (Homeomorph.homeomorphOfUnique Unit _).toHomotopyEquiv⟩

#print axioms positiveListHomeomorph
#print axioms finiteCoproductHomeomorph
#print axioms nonemptyCompactModel
#print axioms compactModel
#print axioms compactWedgeModel
#print axioms contractibleModel

end CompactSource
end D5.S3.Geometry.CompactSphereNormalForm
