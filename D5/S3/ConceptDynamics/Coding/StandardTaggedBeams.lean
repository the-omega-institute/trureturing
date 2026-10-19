/- GID: D5/S3/ConceptDynamics/Coding/StandardTaggedBeams
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardTaggedBeams
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual tagged beams, common-cut matching and integral group completion. -/
import D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Algebra.Group.TypeTags.Hom

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open scoped BigOperators Matrix

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G)

/-- A finite family of actual subsets. Tags distinguish identical copies. -/
structure Object where
  Tag : Type v
  finiteTag : Finite Tag
  beam : Tag → Beam G

instance (A : Object G) : Finite A.Tag := A.finiteTag
instance (A : Object G) : Fintype A.Tag := Fintype.ofFinite _

def singleton (U : Beam G) : Object G := ⟨PUnit, inferInstance, fun _ => U⟩
def family {I : Type v} [Finite I] (U : I → Beam G) : Object G := ⟨I, inferInstance, U⟩
def empty : Object G := ⟨PEmpty, inferInstance, PEmpty.elim⟩
def plus (A B : Object G) : Object G :=
  ⟨A.Tag ⊕ B.Tag, inferInstance, Sum.elim A.beam B.beam⟩

abbrev Normalized (A : Object G) (n : ℤ) : Prop := ∀ i, AtCut G (A.beam i).val n
abbrev Pieces (A : Object G) (n : ℤ) := Σ i : A.Tag, Parts G (A.beam i).val n

def piecesFinite {A : Object G} {n : ℤ} (hn : Normalized G A n) : Finite (Pieces G A n) := by
  letI (i : A.Tag) : Finite (Parts G (A.beam i).val n) := (hn i).1
  exact inferInstanceAs (Finite (Σ i : A.Tag, Parts G (A.beam i).val n))

def pieceEndpoint {A : Object G} {n : ℤ} (P : Pieces G A n) : V := RayAt.endpoint G P.2.val

def row (A : Object G) (n : ℤ) (hn : Normalized G A n) : V → ℤ := by
  letI : Finite (Pieces G A n) := piecesFinite G hn
  letI : Fintype (Pieces G A n) := Fintype.ofFinite _
  exact ∑ P : Pieces G A n, Pi.single (pieceEndpoint G P) 1

/-- DEFINING relation witnesses are actual ray partitions and a bijection of
pieces at the SAME INTEGER cut. Algebraic row equality is not the definition. -/
structure Matching (A B : Object G) (n : ℤ) where
  left : Normalized G A n
  right : Normalized G B n
  pieces : Pieces G A n ≃ Pieces G B n
  endpoints : ∀ P, pieceEndpoint G (pieces P) = pieceEndpoint G P

/-- Every matched piece is implemented by the genuine future-preserving
past splice on its actual subsets. -/
def Matching.pieceSplice {A B : Object G} {n : ℤ} (m : Matching G A B n)
    (P : Pieces G A n) : P.2.val.val ≃ (m.pieces P).2.val.val :=
  (Set.equivOfEq (RayAt.set_eq G P.2.val)).trans
    ((spliceEquiv G (RayAt.representative G P.2.val)
      (RayAt.representative G (m.pieces P).2.val) n (m.endpoints P).symm).trans
      (Set.equivOfEq (RayAt.set_eq G (m.pieces P).2.val)).symm)

/-- Endpoint rows are a CONSEQUENCE of actual geometric matchings. -/
theorem Matching.rows {A B : Object G} {n : ℤ} (m : Matching G A B n) :
    row G A n m.left = row G B n m.right := by
  letI : Finite (Pieces G A n) := piecesFinite G m.left
  letI : Finite (Pieces G B n) := piecesFinite G m.right
  letI : Fintype (Pieces G A n) := Fintype.ofFinite _
  letI : Fintype (Pieces G B n) := Fintype.ofFinite _
  exact Fintype.sum_equiv m.pieces _ _ (fun P => by rw [m.endpoints])

private theorem basis_sum_card {I : Type*} [Fintype I] (f : I → V) (w : V) :
    (∑ i, (Pi.single (f i) (1 : ℤ) : V → ℤ)) w =
      (Fintype.card {i // f i = w} : ℤ) := by
  classical
  simp only [Finset.sum_apply, Pi.single_apply, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = w
  · simp [h]
  · simp [h, Ne.symm h]

/-- The converse selects bijections of finite endpoint fibers, then every
piece is realized by Matching.pieceSplice. This is a proved criterion. -/
def matchingOfRows {A B : Object G} {n : ℤ} (hA : Normalized G A n) (hB : Normalized G B n)
    (hr : row G A n hA = row G B n hB) : Matching G A B n := by
  classical
  letI : Finite (Pieces G A n) := piecesFinite G hA
  letI : Finite (Pieces G B n) := piecesFinite G hB
  letI : Fintype (Pieces G A n) := Fintype.ofFinite _
  letI : Fintype (Pieces G B n) := Fintype.ofFinite _
  have hc (w : V) :
      Fintype.card {P : Pieces G A n // pieceEndpoint G P = w} =
        Fintype.card {P : Pieces G B n // pieceEndpoint G P = w} := by
    have he := congrFun hr w
    change (∑ P : Pieces G A n, (Pi.single (pieceEndpoint G P) (1 : ℤ) : V → ℤ)) w =
      (∑ P : Pieces G B n, (Pi.single (pieceEndpoint G P) (1 : ℤ) : V → ℤ)) w at he
    rw [basis_sum_card, basis_sum_card] at he
    exact_mod_cast he
  let fibers (w : V) := Fintype.equivOfCardEq (hc w)
  let e := (Equiv.sigmaFiberEquiv (pieceEndpoint G (A := A) (n := n))).symm.trans
    ((Equiv.sigmaCongrRight fibers).trans
      (Equiv.sigmaFiberEquiv (pieceEndpoint G (A := B) (n := n))))
  refine ⟨hA, hB, e, ?_⟩
  intro P
  change pieceEndpoint G ((fibers (pieceEndpoint G P) ⟨P, rfl⟩).val) = pieceEndpoint G P
  exact (fibers (pieceEndpoint G P) ⟨P, rfl⟩).property

theorem row_byTag (A : Object G) (n : ℤ) (hn : Normalized G A n) :
    letI (i : A.Tag) : Finite (Parts G (A.beam i).val n) := (hn i).1
    row G A n hn = ∑ i : A.Tag, endpointRow G (A.beam i).val n := by
  letI : Fintype A.Tag := Fintype.ofFinite _
  letI (i : A.Tag) : Finite (Parts G (A.beam i).val n) := (hn i).1
  letI (i : A.Tag) : Fintype (Parts G (A.beam i).val n) := Fintype.ofFinite _
  letI : Finite (Pieces G A n) := piecesFinite G hn
  simp only [row, Pieces, endpointRow, pieceEndpoint]
  rw [show Fintype.ofFinite (Pieces G A n) =
    inferInstanceAs (Fintype (Σ i : A.Tag, Parts G (A.beam i).val n)) from
      Subsingleton.elim _ _]
  exact Fintype.sum_sigma' (fun (i : A.Tag) (P : Parts G (A.beam i).val n) =>
    (Pi.single (RayAt.endpoint G P.val) (1 : ℤ) : V → ℤ))

include hG in
theorem normalized_mono {A : Object G} {n m : ℤ} (hn : Normalized G A n) (h : n ≤ m) :
    Normalized G A m := fun i => atCut_mono G hG (hn i) h

theorem row_refine (A : Object G) (n : ℤ) (hn : Normalized G A n) (r : ℕ) :
    row G A (n + (r : ℤ)) (normalized_mono G hG hn (by omega)) =
      row G A n hn ᵥ* adjacency G ^ r := by
  letI : Fintype A.Tag := Fintype.ofFinite _
  let hn' := normalized_mono G hG hn (show n ≤ n + (r : ℤ) by omega)
  letI (i : A.Tag) : Finite (Parts G (A.beam i).val n) := (hn i).1
  letI (i : A.Tag) : Finite (Parts G (A.beam i).val (n + (r : ℤ))) := (hn' i).1
  calc
    row G A (n + (r : ℤ)) hn' =
        ∑ i : A.Tag, endpointRow G (A.beam i).val (n + (r : ℤ)) :=
      row_byTag G A _ hn'
    _ = ∑ i : A.Tag, endpointRow G (A.beam i).val n ᵥ* adjacency G ^ r := by
      apply Finset.sum_congr rfl
      intro i _
      exact endpointRow_refine G hG (hn i) r
    _ = (∑ i : A.Tag, endpointRow G (A.beam i).val n) ᵥ* adjacency G ^ r :=
      (sum_vecMul _ _).symm
    _ = row G A n hn ᵥ* adjacency G ^ r :=
      congrArg (fun x : V → ℤ => x ᵥ* adjacency G ^ r) (row_byTag G A n hn).symm

private theorem row_cut_congr (A : Object G) {n m : ℤ}
    (hn : Normalized G A n) (hm : Normalized G A m) (h : n = m) :
    row G A n hn = row G A m hm := by
  subst m
  rfl

/-- Common refinement uses the actual numbered partition recurrence. -/
def Matching.refine (hG : Essential G) {A B : Object G} {n m : ℤ}
    (w : Matching G A B n) (hnm : n ≤ m) :
    Matching G A B m := by
  let r := (m - n).toNat
  have he : n + (r : ℤ) = m := by dsimp [r]; omega
  apply matchingOfRows G (normalized_mono G hG w.left hnm) (normalized_mono G hG w.right hnm)
  let hAr := normalized_mono G hG w.left (show n ≤ n + (r : ℤ) by omega)
  let hBr := normalized_mono G hG w.right (show n ≤ n + (r : ℤ) by omega)
  have hA := row_refine G hG A n w.left r
  have hB := row_refine G hG B n w.right r
  calc
    row G A m (normalized_mono G hG w.left hnm) = row G A (n + (r : ℤ)) hAr :=
      row_cut_congr G A (normalized_mono G hG w.left hnm) hAr he.symm
    _ = row G A n w.left ᵥ* adjacency G ^ r := hA
    _ = row G B n w.right ᵥ* adjacency G ^ r :=
      congrArg (fun x : V → ℤ => x ᵥ* adjacency G ^ r) w.rows
    _ = row G B (n + (r : ℤ)) hBr := hB.symm
    _ = row G B m (normalized_mono G hG w.right hnm) :=
      row_cut_congr G B hBr (normalized_mono G hG w.right hnm) he

def Equivalent (A B : Object G) : Prop := ∃ n : ℤ, Nonempty (Matching G A B n)

include hG in
theorem has_cut (A : Object G) : ∃ n : ℤ, Normalized G A n := by
  classical
  letI : Fintype A.Tag := Fintype.ofFinite _
  choose cut hcut using fun i : A.Tag => (A.beam i).property
  let N := Finset.univ.sup (fun i : A.Tag => (cut i).toNat)
  refine ⟨(N : ℤ), ?_⟩
  intro i
  have hi : (cut i).toNat ≤ N := Finset.le_sup (f := fun i => (cut i).toNat) (Finset.mem_univ i)
  exact atCut_mono G hG (hcut i) (by omega)

include hG in
theorem common_cut (A B : Object G) : ∃ n : ℤ, Normalized G A n ∧ Normalized G B n := by
  obtain ⟨n, hn⟩ := has_cut G hG A
  obtain ⟨m, hm⟩ := has_cut G hG B
  exact ⟨max n m, normalized_mono G hG hn (le_max_left _ _),
    normalized_mono G hG hm (le_max_right _ _)⟩

include hG in
theorem equivalent_refl (A : Object G) : Equivalent G A A := by
  obtain ⟨n, hn⟩ := has_cut G hG A
  exact ⟨n, ⟨{ left := hn, right := hn, pieces := Equiv.refl _, endpoints := fun _ => rfl }⟩⟩

theorem equivalent_symm {A B : Object G} (h : Equivalent G A B) : Equivalent G B A := by
  obtain ⟨n, ⟨m⟩⟩ := h
  refine ⟨n, ⟨{ left := m.right, right := m.left, pieces := m.pieces.symm, endpoints := ?_ }⟩⟩
  intro P
  simpa only [Equiv.apply_symm_apply] using (m.endpoints (m.pieces.symm P)).symm

include hG in
theorem equivalent_trans {A B C : Object G} (h : Equivalent G A B) (k : Equivalent G B C) :
    Equivalent G A C := by
  obtain ⟨n, ⟨h⟩⟩ := h
  obtain ⟨m, ⟨k⟩⟩ := k
  let h' := Matching.refine G hG h (le_max_left n m)
  let k' := Matching.refine G hG k (le_max_right n m)
  exact ⟨max n m, ⟨{
    left := h'.left
    right := k'.right
    pieces := h'.pieces.trans k'.pieces
    endpoints := fun P => (k'.endpoints (h'.pieces P)).trans (h'.endpoints P)
  }⟩⟩

/-- Eventual equality at one common INTEGER cut is DERIVED from geometry. -/
theorem equivalent_iff_common_rows (A B : Object G) (n m : ℤ)
    (hn : Normalized G A n) (hm : Normalized G B m) :
    Equivalent G A B ↔ ∃ ell : ℤ, ∃ hnell : n ≤ ell, ∃ hmell : m ≤ ell,
      row G A ell (normalized_mono G hG hn hnell) =
        row G B ell (normalized_mono G hG hm hmell) := by
  constructor
  · rintro ⟨k, ⟨w⟩⟩
    let ell := max k (max n m)
    have hk : k ≤ ell := le_max_left _ _
    have hne : n ≤ ell := (le_max_left n m).trans (le_max_right _ _)
    have hme : m ≤ ell := (le_max_right n m).trans (le_max_right _ _)
    exact ⟨ell, hne, hme, (Matching.refine G hG w hk).rows⟩
  · rintro ⟨ell, hnell, hmell, he⟩
    exact ⟨ell, ⟨matchingOfRows G _ _ he⟩⟩

private theorem normalized_plus {A B : Object G} {n : ℤ}
    (hA : Normalized G A n) (hB : Normalized G B n) : Normalized G (plus G A B) n := by
  intro i
  cases i with
  | inl a => exact hA a
  | inr b => exact hB b

private theorem row_plus {A B : Object G} {n : ℤ}
    (hA : Normalized G A n) (hB : Normalized G B n) :
    row G (plus G A B) n (normalized_plus G hA hB) = row G A n hA + row G B n hB := by
  letI : Fintype A.Tag := Fintype.ofFinite _
  letI : Fintype B.Tag := Fintype.ofFinite _
  letI (i : (plus G A B).Tag) : Finite (Parts G ((plus G A B).beam i).val n) :=
    ((normalized_plus G hA hB) i).1
  rw [row_byTag, row_byTag, row_byTag]
  rw [show instFintypeTag G (plus G A B) =
    inferInstanceAs (Fintype (A.Tag ⊕ B.Tag)) from Subsingleton.elim _ _]
  exact Fintype.sum_sum_type (fun i : (plus G A B).Tag =>
    endpointRow G ((plus G A B).beam i).val n)

include hG in
theorem plus_congr {A B C D : Object G} (h : Equivalent G A B) (k : Equivalent G C D) :
    Equivalent G (plus G A C) (plus G B D) := by
  obtain ⟨n, ⟨h⟩⟩ := h
  obtain ⟨m, ⟨k⟩⟩ := k
  let h' := Matching.refine G hG h (le_max_left n m)
  let k' := Matching.refine G hG k (le_max_right n m)
  refine ⟨max n m, ⟨matchingOfRows G
    (normalized_plus G h'.left k'.left) (normalized_plus G h'.right k'.right) ?_⟩⟩
  rw [row_plus G h'.left k'.left, row_plus G h'.right k'.right, h'.rows, k'.rows]

abbrev beamSetoid : Setoid (Object G) :=
  ⟨Equivalent G, ⟨equivalent_refl G hG, equivalent_symm G, equivalent_trans G hG⟩⟩
abbrev BeamMonoid := Quotient (beamSetoid G hG)

def objectClass (A : Object G) : BeamMonoid G hG := Quotient.mk _ A

include hG in
private theorem plus_comm_rel (A B : Object G) : Equivalent G (plus G A B) (plus G B A) := by
  obtain ⟨n, hn, hm⟩ := common_cut G hG A B
  exact ⟨n, ⟨matchingOfRows G (normalized_plus G hn hm) (normalized_plus G hm hn)
    (by rw [row_plus G hn hm, row_plus G hm hn, add_comm])⟩⟩

include hG in
private theorem plus_assoc_rel (A B C : Object G) :
    Equivalent G (plus G (plus G A B) C) (plus G A (plus G B C)) := by
  obtain ⟨n, hn, hc⟩ := common_cut G hG (plus G A B) C
  have ha : Normalized G A n := fun i => hn (Sum.inl i)
  have hb : Normalized G B n := fun i => hn (Sum.inr i)
  exact ⟨n, ⟨matchingOfRows G (normalized_plus G hn hc)
    (normalized_plus G ha (normalized_plus G hb hc)) (by
      rw [row_plus G hn hc, row_plus G ha hb,
        row_plus G ha (normalized_plus G hb hc), row_plus G hb hc, add_assoc])⟩⟩

include hG in
private theorem empty_plus_rel (A : Object G) : Equivalent G (plus G (empty G) A) A := by
  obtain ⟨n, hn⟩ := has_cut G hG A
  have he : Normalized G (empty G) n := by intro i; exact PEmpty.elim i
  refine ⟨n, ⟨matchingOfRows G (normalized_plus G he hn) hn ?_⟩⟩
  rw [row_plus G he hn]
  have hz : row G (empty G) n he = 0 := by
    unfold row
    apply Finset.sum_eq_zero
    intro P _
    exact PEmpty.elim P.1
  rw [hz, zero_add]

instance : Zero (BeamMonoid G hG) := ⟨objectClass G hG (empty G)⟩
instance : Add (BeamMonoid G hG) :=
  ⟨Quotient.map₂ (plus G) (fun _ _ h _ _ k => plus_congr G hG h k)⟩

instance : AddCommMonoid (BeamMonoid G hG) where
  zero := 0
  add := (· + ·)
  add_assoc a b c := Quotient.inductionOn a (fun A =>
    Quotient.inductionOn b (fun B => Quotient.inductionOn c (fun C =>
      Quotient.sound (plus_assoc_rel G hG A B C))))
  zero_add a := Quotient.inductionOn a (fun A => Quotient.sound (empty_plus_rel G hG A))
  add_zero a := Quotient.inductionOn a (fun A => Quotient.sound
    (equivalent_trans G hG (plus_comm_rel G hG A (empty G)) (empty_plus_rel G hG A)))
  add_comm a b := Quotient.inductionOn a (fun A => Quotient.inductionOn b
    (fun B => Quotient.sound (plus_comm_rel G hG A B)))
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

/-- Library group completion, in Multiplicative form to avoid generated-name
ambiguity. This is the integer group, never a rational or sign-sector quotient. -/
abbrev BeamGroup := Additive (Algebra.GrothendieckGroup (Multiplicative (BeamMonoid G hG)))

def intoGroup : BeamMonoid G hG →+ BeamGroup G hG :=
  (Algebra.GrothendieckGroup.of (M := Multiplicative (BeamMonoid G hG))).toAdditiveRight

def objectGroup (A : Object G) : BeamGroup G hG := intoGroup G hG (objectClass G hG A)

def objectValue (A : Object G) : RowLimit G := by
  letI : Fintype A.Tag := Fintype.ofFinite _
  exact ∑ i : A.Tag, beamCoordinate G (A.beam i)

include hG in
theorem objectValue_at (A : Object G) (n : ℤ) (hn : Normalized G A n) :
    objectValue G A = intStage (rowTransition G) n (row G A n hn) := by
  letI : Fintype A.Tag := Fintype.ofFinite _
  unfold objectValue
  simp_rw [beamCoordinate_at G hG _ n (hn _)]
  unfold coordinateAt
  rw [← map_sum, row_byTag]

include hG in
private theorem objectValue_rel {A B : Object G} (h : Equivalent G A B) :
    objectValue G A = objectValue G B := by
  obtain ⟨n, ⟨w⟩⟩ := h
  rw [objectValue_at G hG A n w.left, objectValue_at G hG B n w.right, w.rows]

def quotientValue : BeamMonoid G hG →+ RowLimit G where
  toFun := Quotient.lift (objectValue G) (fun _ _ h => objectValue_rel G hG h)
  map_zero' := by
    change objectValue G (empty G) = 0
    unfold objectValue
    apply Finset.sum_eq_zero
    intro i _
    exact PEmpty.elim i
  map_add' a b := Quotient.inductionOn a (fun A => Quotient.inductionOn b (fun B => by
    change objectValue G (plus G A B) = objectValue G A + objectValue G B
    obtain ⟨n, hA, hB⟩ := common_cut G hG A B
    rw [objectValue_at G hG (plus G A B) n (normalized_plus G hA hB),
      objectValue_at G hG A n hA, objectValue_at G hG B n hB, row_plus G hA hB,
      map_add]))

/-- F is extended by the actual Mathlib group-completion universal property.
Its invertibility is proved separately in StandardBeamIdentification, not supplied as a field. -/
def F : BeamGroup G hG →+ RowLimit G :=
  (Algebra.GrothendieckGroup.lift (quotientValue G hG).toMultiplicative).toAdditiveLeft

theorem F_objectGroup (A : Object G) : F G hG (objectGroup G hG A) = objectValue G A := by
  have he := (Algebra.GrothendieckGroup.lift
    (M := Multiplicative (BeamMonoid G hG)) (G := Multiplicative (RowLimit G))).left_inv
      (quotientValue G hG).toMultiplicative
  exact DFunLike.congr_fun he (Multiplicative.ofAdd (objectClass G hG A))


/-- Geometric additivity for an actual DISJOINT ray union. -/
theorem disjointUnion_rel {I : Type v} [Fintype I] (beta : I → History G) (n : ℤ)
    (hd : ∀ i j, i ≠ j → Disjoint (ray G (beta i) n) (ray G (beta j) n)) :
    let U : Beam G := ⟨⋃ i, ray G (beta i) n,
      n, atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)⟩
    let W : I → Beam G := fun i => ⟨ray G (beta i) n, n, ray_atCut G hG (beta i) n⟩
    Equivalent G (singleton G U) (family G W) := by
  let U : Beam G := ⟨⋃ i, ray G (beta i) n,
    n, atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)⟩
  let W : I → Beam G := fun i => ⟨ray G (beta i) n, n, ray_atCut G hG (beta i) n⟩
  have hU : Normalized G (singleton G U) n := fun _ =>
    atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)
  have hW : Normalized G (family G W) n := fun i => ray_atCut G hG (beta i) n
  letI : Finite (Parts G (⋃ i, ray G (beta i) n) n) := (hU PUnit.unit).1
  letI (i : I) : Finite (Parts G (ray G (beta i) n) n) := (hW i).1
  letI (i : (family G W).Tag) : Finite (Parts G (W i).val n) := (hW i).1
  refine ⟨n, ⟨matchingOfRows G hU hW ?_⟩⟩
  rw [row_byTag, row_byTag]
  change (∑ _i : (singleton G U).Tag, endpointRow G U.val n) =
    ∑ i : (family G W).Tag, endpointRow G (W i).val n
  letI : Subsingleton (singleton G U).Tag := inferInstanceAs (Subsingleton PUnit)
  rw [Fintype.sum_subsingleton (fun _i : (singleton G U).Tag => endpointRow G U.val n)
    (PUnit.unit : (singleton G U).Tag)]
  rw [show instFintypeTag G (family G W) = ‹Fintype I› from Subsingleton.elim _ _]
  change endpointRow G (⋃ i, ray G (beta i) n) n =
    ∑ i : I, endpointRow G (ray G (beta i) n) n
  rw [endpointRow_disjointUnion G hG beta n hd]
  simp_rw [endpointRow_ray G hG]

/-- The actual group-completion image of a disjoint union is the image of
its tagged copies. It is not defined as overlapping set union. -/
theorem disjointUnion_group {I : Type v} [Fintype I] (beta : I → History G) (n : ℤ)
    (hd : ∀ i j, i ≠ j → Disjoint (ray G (beta i) n) (ray G (beta j) n)) :
    let U : Beam G := ⟨⋃ i, ray G (beta i) n,
      n, atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)⟩
    let W : I → Beam G := fun i => ⟨ray G (beta i) n, n, ray_atCut G hG (beta i) n⟩
    objectGroup G hG (singleton G U) = objectGroup G hG (family G W) := by
  exact congrArg (intoGroup G hG) (Quotient.sound (disjointUnion_rel G hG beta n hd))


include hG in
/-- Equality of forward coordinates is equivalent to an ACTUAL eventual
common-cut matching. Native equality supplies a stage, and matchingOfRows
then constructs the geometric endpoint-fiber bijection and actual splices. -/
theorem equivalent_iff_value_eq (A B : Object G) :
    Equivalent G A B ↔ objectValue G A = objectValue G B := by
  constructor
  · exact objectValue_rel G hG
  · intro he
    obtain ⟨n, hA, hB⟩ := common_cut G hG A B
    let N := n.toNat
    have hnN : n ≤ (N : ℤ) := by dsimp [N]; omega
    have hAN := normalized_mono G hG hA hnN
    have hBN := normalized_mono G hG hB hnN
    rw [objectValue_at G hG A (N : ℤ) hAN,
      objectValue_at G hG B (N : ℤ) hBN, intStage_nat, intStage_nat] at he
    obtain ⟨K, hNK, hK⟩ := Module.DirectLimit.exists_eq_of_of_eq he
    have hm : (N : ℤ) + ((K - N : ℕ) : ℤ) = (K : ℤ) := by omega
    have hr : row G A (K : ℤ) (normalized_mono G hG hAN (by omega)) =
        row G B (K : ℤ) (normalized_mono G hG hBN (by omega)) := by
      let hAK := normalized_mono G hG hAN (show (N : ℤ) ≤ (K : ℤ) by omega)
      let hBK := normalized_mono G hG hBN (show (N : ℤ) ≤ (K : ℤ) by omega)
      let hAr := normalized_mono G hG hAN
        (show (N : ℤ) ≤ (N : ℤ) + ((K - N : ℕ) : ℤ) by omega)
      let hBr := normalized_mono G hG hBN
        (show (N : ℤ) ≤ (N : ℤ) + ((K - N : ℕ) : ℤ) by omega)
      have ha := row_refine G hG A (N : ℤ) hAN (K - N)
      have hb := row_refine G hG B (N : ℤ) hBN (K - N)
      calc
        row G A (K : ℤ) hAK = row G A ((N : ℤ) + ((K - N : ℕ) : ℤ)) hAr :=
          row_cut_congr G A hAK hAr hm.symm
        _ = row G A (N : ℤ) hAN ᵥ* adjacency G ^ (K - N) := ha
        _ = row G B (N : ℤ) hBN ᵥ* adjacency G ^ (K - N) := by
          simpa only [InertGroupBlockConjugacy.stationaryTransition,
            rowTransition_power] using hK
        _ = row G B ((N : ℤ) + ((K - N : ℕ) : ℤ)) hBr := hb.symm
        _ = row G B (K : ℤ) hBK := row_cut_congr G B hBr hBK hm
    exact ⟨(K : ℤ), ⟨matchingOfRows G _ _ hr⟩⟩

end D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
