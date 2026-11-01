/- GID: D5/S3/Topology/PointedWedgeHomology
   generality: G
   mirror-B: D5/B/S3/Topology/PointedWedgeHomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open saturated subwedges yield actual positive-degree singular homology biproducts. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Topology.OpenCoverHomology
import Mathlib.Topology.CompactOpen

/-! Saturated open subwedges and based quotient contractions give open MV splittings. -/

noncomputable section
open Set Topology CategoryTheory Limits AlgebraicTopology
open scoped ContinuousMap unitInterval

namespace D5.S3.Topology.PointedWedgeHomology
open D5.S3.Geometry.FiniteConeUnionWedge
open private wedgeInverseHomotopy
  wedgeMap
  from
  D5.S3.Geometry.FiniteConeUnionWedge

universe w v u
variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    (a : X) (b : Y)

private def rawMem (A : Set X) (B : Set Y) : X ⊕ Y → Prop :=
  Sum.elim (· ∈ A) (· ∈ B)

private theorem rawMem_base {A : Set X} {B : Set Y} (ha : a ∈ A) (hb : b ∈ B)
    {z : X ⊕ Y} (hz : z ∈ wedgePoints a b) : rawMem A B z := by
  rcases hz with rfl | rfl
  · exact ha
  · exact hb

/-- A saturated subwedge; both original basepoints belong to its pieces. -/
def part (A : Set X) (B : Set Y) (ha : a ∈ A) (hb : b ∈ B) : Set (Wedge a b) :=
  {z | Quotient.lift (rawMem A B) (by
    rintro z w (rfl | ⟨hz, hw⟩)
    · rfl
    · exact propext (iff_of_true (rawMem_base a b ha hb hz)
        (rawMem_base a b ha hb hw))) z}

theorem isOpen_part {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (ha : a ∈ A) (hb : b ∈ B) : IsOpen (part a b A B ha hb) := by
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  exact isOpen_sum_iff.mpr ⟨hA, hB⟩

private def rawPartEquiv (A : Set X) (B : Set Y) :
    A ⊕ B ≃ {z : X ⊕ Y // rawMem A B z} where
  toFun := fun z => ⟨Sum.map Subtype.val Subtype.val z, by
      cases z with
      | inl x => exact x.property
      | inr y => exact y.property⟩
  invFun := fun z => match z with
    | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, hx⟩
    | ⟨Sum.inr y, hy⟩ => Sum.inr ⟨y, hy⟩
  left_inv := by rintro (x | y) <;> rfl
  right_inv := by rintro ⟨x | y, h⟩ <;> rfl

private def rawPartHomeomorph {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) :
    A ⊕ B ≃ₜ {z : X ⊕ Y // rawMem A B z} :=
  (rawPartEquiv A B).toHomeomorphOfContinuousOpen
    ((continuous_subtype_val.sumMap continuous_subtype_val).subtype_mk (fun z => by
      cases z with
      | inl x => exact x.property
      | inr y => exact y.property))
    ((hA.isOpenMap_subtype_val.sumMap hB.isOpenMap_subtype_val).codRestrict (fun z => by
      cases z with
      | inl x => exact x.property
      | inr y => exact y.property))

/-- An actual homeomorphism from the wedge of the two open pieces to the
corresponding open subspace of the original quotient. -/
def partHomeomorph {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (ha : a ∈ A) (hb : b ∈ B) :
    Wedge (⟨a, ha⟩ : A) (⟨b, hb⟩ : B) ≃ₜ part a b A B ha hb := by
  let f : A ⊕ B → part a b A B ha hb := fun z =>
    ⟨Quotient.mk _ (Sum.map Subtype.val Subtype.val z), by
      cases z with
      | inl x => exact x.property
      | inr y => exact y.property⟩
  have hf : IsQuotientMap f := by
    exact (isQuotientMap_quotient_mk'.restrictPreimage_isOpen
      (isOpen_part a b hA hB ha hb)).comp (rawPartHomeomorph hA hB).isQuotientMap
  have hker : ∀ z w : A ⊕ B,
      (subsetSetoid (wedgePoints (⟨a, ha⟩ : A) (⟨b, hb⟩ : B))).r z w ↔
        (Setoid.ker f).r z w := by
    intro z w
    change (z = w ∨ (z ∈ wedgePoints _ _ ∧ w ∈ wedgePoints _ _)) ↔ f z = f w
    rw [Subtype.ext_iff, Quotient.eq]
    change (z = w ∨ (z ∈ wedgePoints (⟨a, ha⟩ : A) (⟨b, hb⟩ : B) ∧
      w ∈ wedgePoints (⟨a, ha⟩ : A) (⟨b, hb⟩ : B))) ↔
      (Sum.map Subtype.val Subtype.val z = Sum.map Subtype.val Subtype.val w ∨
        (Sum.map Subtype.val Subtype.val z ∈ wedgePoints a b ∧
          Sum.map Subtype.val Subtype.val w ∈ wedgePoints a b))
    cases z <;> cases w <;> simp [wedgePoints, Subtype.ext_iff]
  exact (Homeomorph.Quotient.congrRight hker).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨f, hf.continuous⟩) hf)

private def leftProjection : C(Wedge a b, X) := by
  let f : X ⊕ Y → X := Sum.elim id (fun _ => a)
  refine ⟨Quotient.lift f ?_, ?_⟩
  · rintro z w (rfl | ⟨hz, hw⟩)
    · rfl
    · rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;> rfl
  · exact (continuous_id.sumElim continuous_const).quotient_lift _

private def leftInclusion : C(X, Wedge a b) :=
  ⟨fun x => Quotient.mk _ (Sum.inl x), continuous_quotient_mk'.comp continuous_inl⟩

/-- Collapsing the right summand by its actual based contraction is a homotopy
equivalence to the left summand. Cylinder continuity is consumed from the
existing wedgeInverseHomotopy, which uses continuous_lift_prod_right. -/
def leftEquiv (H : (ContinuousMap.id Y).HomotopyRel
    (ContinuousMap.const Y b) {b}) : Wedge a b ≃ₕ X := by
  let c : C(Y, PUnit.{w + 1}) := ContinuousMap.const _ PUnit.unit
  let s : C(PUnit.{w + 1}, Y) := ContinuousMap.const _ b
  let T := wedgeInverseHomotopy (ContinuousMap.id X) c (ContinuousMap.id X) s
    rfl rfl rfl rfl (ContinuousMap.HomotopyRel.refl (ContinuousMap.id X) {a}) H
  have he : (wedgeMap (ContinuousMap.id X) s rfl rfl).comp
      (wedgeMap (ContinuousMap.id X) c rfl rfl) =
        (leftInclusion a b).comp (leftProjection a b) := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
        rcases z with x | y
        · rfl
        · exact Quotient.sound (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
  exact {
    toFun := leftProjection a b
    invFun := leftInclusion a b
    left_inv := ⟨T.symm.cast he rfl⟩
    right_inv := by
      have h : (leftProjection a b).comp (leftInclusion a b) = ContinuousMap.id X := by
        ext x; rfl
      rw [h] }

private def swapHomeomorph : Wedge a b ≃ₜ Wedge b a :=
  Homeomorph.Quotient.congr (Homeomorph.sumComm X Y) (by
    intro z w
    change (z = w ∨ (z ∈ wedgePoints a b ∧ w ∈ wedgePoints a b)) ↔
      (Sum.swap z = Sum.swap w ∨
        (Sum.swap z ∈ wedgePoints b a ∧ Sum.swap w ∈ wedgePoints b a))
    cases z <;> cases w <;> simp [wedgePoints, or_comm])

def rightEquiv (H : (ContinuousMap.id X).HomotopyRel
    (ContinuousMap.const X a) {a}) : Wedge a b ≃ₕ Y :=
  (swapHomeomorph a b).toHomotopyEquiv.trans (leftEquiv b a H)

/-- The actual wedge of two spaces with based contractions is contractible. -/
theorem contractible_wedge
    (H : (ContinuousMap.id X).HomotopyRel (ContinuousMap.const X a) {a})
    (K : (ContinuousMap.id Y).HomotopyRel (ContinuousMap.const Y b) {b}) :
    ContractibleSpace (Wedge a b) := by
  letI : ContractibleSpace X :=
    (contractible_iff_id_nullhomotopic X).mpr ⟨a, ⟨H.toHomotopy⟩⟩
  exact (leftEquiv a b K).contractibleSpace

section Cover
variable {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (ha : a ∈ A) (hb : b ∈ B)
    (H : (ContinuousMap.id A).HomotopyRel
      (ContinuousMap.const A (⟨a, ha⟩ : A)) {⟨a, ha⟩})
    (K : (ContinuousMap.id B).HomotopyRel
      (ContinuousMap.const B (⟨b, hb⟩ : B)) {⟨b, hb⟩})

private abbrev U := part a b univ B (mem_univ a) hb
private abbrev V := part a b A univ ha (mem_univ b)

private theorem cover : U a b hb ∪ V a b ha = univ := by
  ext z
  induction z using Quotient.inductionOn with
  | h z => cases z <;> simp [U, V, part, rawMem]

private theorem inter : U a b hb ∩ V a b ha = part a b A B ha hb := by
  ext z
  induction z using Quotient.inductionOn with
  | h z => cases z <;> simp [U, V, part, rawMem]

private def openLeftEquiv : U a b hb ≃ₕ X :=
  (partHomeomorph a b isOpen_univ hB (mem_univ a) hb).symm.toHomotopyEquiv.trans
    ((leftEquiv (⟨a, mem_univ a⟩ : (univ : Set X)) (⟨b, hb⟩ : B) K).trans
      (Homeomorph.Set.univ X).toHomotopyEquiv)

private def openRightEquiv : V a b ha ≃ₕ Y :=
  (partHomeomorph a b hA isOpen_univ ha (mem_univ b)).symm.toHomotopyEquiv.trans
    ((rightEquiv (⟨a, ha⟩ : A) (⟨b, mem_univ b⟩ : (univ : Set Y)) H).trans
      (Homeomorph.Set.univ Y).toHomotopyEquiv)

set_option maxHeartbeats 1000000 in
/-- Positive singular homology of the actual quotient wedge is the binary
biproduct of the summands. All openness, quotient identifications, both
homotopy equivalences and the intersection contraction are constructed above. -/
def homologyIso {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    (R : C) (q : ℕ) (hq : 0 < q) :
    (((singularHomologyFunctor C q).obj R).obj (TopCat.of X) ⊞
      ((singularHomologyFunctor C q).obj R).obj (TopCat.of Y)) ≅
      ((singularHomologyFunctor C q).obj R).obj (TopCat.of (Wedge a b)) := by
  cases q with
  | zero => exact (Nat.not_lt_zero _ hq).elim
  | succ r =>
      have hU : IsOpen (U a b hb) := isOpen_part a b isOpen_univ hB _ _
      have hV : IsOpen (V a b ha) := isOpen_part a b hA isOpen_univ _ _
      letI : ContractibleSpace (part a b A B ha hb) := by
        letI := contractible_wedge (⟨a, ha⟩ : A) (⟨b, hb⟩ : B) H K
        exact (partHomeomorph a b hA hB ha hb).symm.contractibleSpace
      have hI : ContractibleSpace ↥(U a b hb ∩ V a b ha) :=
        (Homeomorph.setCongr (inter a b ha hb)).contractibleSpace
      let F : TopCat.{w} ⥤ C := (singularHomologyFunctor C (r + 1)).obj R
      let eL : F.obj (TopCat.of X) ≅ F.obj (TopCat.of (U a b hb)) :=
        (openLeftEquiv a b hB hb K).symm.reducedSingularHomologyIso R (r + 1)
      let eR : F.obj (TopCat.of Y) ≅ F.obj (TopCat.of (V a b ha)) :=
        (openRightEquiv a b hA ha H).symm.reducedSingularHomologyIso R (r + 1)
      let eMV : (F.obj (TopCat.of (U a b hb)) ⊞ F.obj (TopCat.of (V a b ha))) ≅
          F.obj (TopCat.of (Wedge a b)) :=
        OpenCoverHomology.inclusionIso R (X := TopCat.of (Wedge a b))
          (U := U a b hb) (V := V a b ha) hU hV (cover a b ha hb)
          (Or.inr hI) (r + 1) (Nat.succ_pos r)
      exact biprod.mapIso eL eR ≪≫ eMV

end Cover
end D5.S3.Topology.PointedWedgeHomology
