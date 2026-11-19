/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWordMarks
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWordMarks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite distinct marks and mode bounds for arbitrary four creation words. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
import Mathlib.Data.List.FinRange

/-! An occurrence is labelled by its puncture and its position in that word. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWordMarks

open LatticeGeneratingFieldLocality MvPolynomial
open OriginalFourMActualChart (Chart Puncture loweringParameter)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (exists_lowering_cutoff)
open D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentFiniteLowering (evaluate_lowering_word)
open private wordScale from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCauchyTaylor
open private punctureWords modesBounded creationWord from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection

noncomputable local instance punctureFintype : Fintype Puncture := by
  classical
  exact Fintype.ofList [.P, .Q, .R, .S] (fun p => by cases p <;> simp)

/-- The label distinguishes occurrences even when two modes are equal. -/
abbrev WordMark {D : LatticeData} (words : Puncture → List (Index D)) :=
  Σ p : Puncture, Fin (words p).length

noncomputable instance {D : LatticeData} (words : Puncture → List (Index D)) :
    Fintype (WordMark words) := inferInstanceAs (Fintype (Σ p, Fin (words p).length))

def wordMarkList {D : LatticeData} (words : Puncture → List (Index D)) (p : Puncture) :
    List (WordMark words) :=
  List.ofFn fun i : Fin (words p).length => ⟨p, i⟩

def wordMarkMode {D : LatticeData} (words : Puncture → List (Index D))
    (i : WordMark words) : Index D :=
  (words i.1).get i.2

theorem wordMarkList_maps {D : LatticeData} (words : Puncture → List (Index D)) (p : Puncture) :
    (wordMarkList words p).map (wordMarkMode words) = words p := by
  simp only [wordMarkList, List.map_ofFn, Function.comp_def, wordMarkMode]
  exact List.ofFn_get (words p)

theorem wordMarkList_puncture {D : LatticeData} (words : Puncture → List (Index D))
    (p : Puncture) (i : WordMark words) (hi : i ∈ wordMarkList words p) :
    i.1 = p := by
  unfold wordMarkList at hi
  rcases (List.mem_ofFn' _ _).mp hi with ⟨j, rfl⟩
  rfl

theorem wordMarkList_nodup {D : LatticeData} (words : Puncture → List (Index D)) :
    ((punctureWords (wordMarkList words)).flatMap Prod.snd).Nodup := by
  classical
  change (([.P, .Q, .R, .S] : List Puncture).flatMap (wordMarkList words)).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro p _
    rw [wordMarkList, List.nodup_ofFn]
    intro i j he
    exact Fin.ext (congrArg (fun k : WordMark words => k.2.val) he)
  · have h : ([.P, .Q, .R, .S] : List Puncture).Pairwise (· ≠ ·) := by simp
    refine h.imp ?_
    intro p q hpq
    apply List.disjoint_left.mpr
    intro i hip hiq
    exact hpq ((wordMarkList_puncture words p i hip).symm.trans
      (wordMarkList_puncture words q i hiq))

/-- One finite box contains the marked modes and every supported mode of
the four lowering sequences and their inverse words, uniformly in the chart point. -/
theorem wordMarkMode_finite_box (D : LatticeData) (hu : IsUnit D.G.det)
    (words : Puncture → List (Index D)) :
    ∃ N : ℕ,
      (∀ i : WordMark words, (wordMarkMode words i).2 ≤ N) ∧
      (∀ p j, modesBounded D N ((oscillatorLower D ^ j) (creationWord D (words p)))) ∧
      (∀ c x p, modesBounded D N (inverseLoweredWord D c x p (words p))) := by
  classical
  choose cut hcut using fun p : Puncture => exists_lowering_cutoff D hu (creationWord D (words p))
  let supportModes (P : Oscillator D) : Finset (Index D) := P.support.biUnion Finsupp.support
  let U : Finset (Index D) := Finset.univ.biUnion fun p : Puncture =>
    (words p).toFinset ∪
      (Finset.range (cut p)).biUnion fun j =>
        supportModes ((oscillatorLower D ^ j) (creationWord D (words p)))
  let N := U.sup Prod.snd
  have hboxes (p : Puncture) (j : ℕ) :
      modesBounded D N ((oscillatorLower D ^ j) (creationWord D (words p))) := by
    intro d hd i hi
    by_cases hj : j < cut p
    · exact Finset.le_sup (f := Prod.snd) (s := U) (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_univ p, Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_range.mpr hj, Finset.mem_biUnion.mpr ⟨d, hd, hi⟩⟩)⟩)
    · rw [hcut p j (Nat.le_of_not_gt hj)] at hd
      simp at hd
  refine ⟨N, ?_, hboxes, ?_⟩
  · rintro ⟨p, j⟩
    apply Finset.le_sup (f := Prod.snd) (s := U)
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p,
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.get_mem _ _))⟩
  · intro c x p d hd i hi
    rw [inverseLoweredWord, evaluate_lowering_word D hu (words p)
      (-loweringParameter c p) (cut p) (hcut p)] at hd
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp
      (MvPolynomial.support_sum (MvPolynomial.support_smul hd))
    exact hboxes p j d (MvPolynomial.support_smul hj) i hi

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWordMarks
