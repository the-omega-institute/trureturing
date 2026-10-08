/- GID: D5/S3/FiniteGroups/NikolovSegal/QuantitativeExtraction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/QuantitativeExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.OwnerAdapters
import D5.S3.FiniteGroups.NikolovSegal.Equation47Colours

set_option autoImplicit false
open scoped List

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing Equation47Colours
open Equation47ValueNormalization (colourType)
universe u v
variable {V : Type v} [DecidableEq V] {m : ℕ}

def colours (chi : V → Fin m) (W : Word V) : List (Colour m) :=
  W.map (fun p => (chi p.1,p.2))

/-- Every free cancellation costs a genuine colour pass. This uses the
owner's signed cancellation theorem, including compressed negative boundaries. -/
theorem trivial_length_rank (chi : V → Fin m) {W : Word V}
    (h : FreeGroup.Red W []) : W.length ≤ 2 * signedRank (colours chi W) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.zero_le _
  | @head W R hs hr ih =>
    rcases hs with @⟨A,B,x,s⟩
    have hc : signedRank (colours chi (A++B)) + 1 ≤
        signedRank (colours chi (A++(x,s)::(x,!s)::B)) := by
      simpa [colours,List.map_append,List.append_assoc] using
        signedRank_cancel (colours chi A) (colours chi B) (chi x) s
    have hl : (A++(x,s)::(x,!s)::B).length = (A++B).length + 2 := by simp; omega
    omega

/-- Derive free nonidentity from the true signed colour budget; no
nonidentity, crossing, or extraction oracle is a premise. -/
theorem balanced_rank_nontrivial (chi : V → Fin m) {W : Word V} {n : ℕ}
    (hb : Balanced W) (hc : signedRank (colours chi W) ≤ n)
    (hs : n < (support W).card) : FreeGroup.mk W ≠ 1 := by
  intro he
  have hnil : FreeGroup.reduce W = [] := by
    rw [← FreeGroup.toWord_mk,he,FreeGroup.toWord_one]
  have hred := FreeGroup.reduce.red (L := W)
  rw [hnil] at hred
  have hlen := trivial_length_rank chi hred
  have hbLen := balanced_length hb
  omega

/-- Paper Lemma8.3, on the literal signed word with the exact compressed
colour type. All signs and all empty intermediate segments are allowed. -/
theorem balanced_colour_crossing (chi : V → Fin m) {W : Word V} {n : ℕ}
    (hb : Balanced W) (hc : colourType (colours chi W) <+ colourBound m n)
    (hs : n < (support W).card) :
    ∃ (x y : V) (sx sy : Bool) (A B C D E : Word V), x ≠ y ∧
      W = A ++ [(x,!sx)] ++ B ++ [(y,!sy)] ++ C ++ [(x,sx)] ++ D ++ [(y,sy)] ++ E ∧
      Balanced (A++D++C++B++E) ∧
      colourType (colours chi (A++D++C++B++E)) <+ colourBound m n := by
  have hRank := (signedRank_iff _).mpr hc
  obtain ⟨x,y,sx,sy,A,B,C,D,E,hxy,hW⟩ := balanced_nontrivial_crossing
    hb (balanced_rank_nontrivial chi hb hRank hs)
  refine ⟨x,y,sx,sy,A,B,C,D,E,hxy,hW,
    crossing_balanced hb x y sx sy A B C D E hW,?_⟩
  apply (signedRank_iff _).mp
  have hcut := signedRank_crossing (colours chi A) (colours chi B)
    (colours chi C) (colours chi D) (colours chi E) (chi x) (chi y) sx sy
  have hcut' : signedRank (colours chi (A++D++C++B++E)) ≤ signedRank (colours chi W) := by
    simpa [hW,colours,List.map_append,List.append_assoc] using hcut
  exact hcut'.trans hRank

variable {S : Type u} [Group S]

/-- Quantitative Proposition8.4: construct D ACTUAL fresh crossings on the
original Letter word, with constants and automorphisms retained. -/
theorem extraction_exists (chi : V → Fin m) (n D : ℕ) (W : List (Letter V S))
    (hb : Balanced (signedVariables W))
    (hc : colourType (colours chi (signedVariables W)) <+ colourBound m n)
    (hs : n + 2*D ≤ (support (signedVariables W)).card) :
    ∃ P : Extraction D W,
      Balanced (signedVariables (finalWord P)) ∧
      colourType (colours chi (signedVariables (finalWord P))) <+ colourBound m n ∧
      (support (signedVariables (finalWord P))).card + 2*D =
        (support (signedVariables W)).card := by
  induction D generalizing W with
  | zero => exact ⟨.zero W,hb,hc,by simp [finalWord]⟩
  | succ D ih =>
    have hrank := (signedRank_iff _).mpr hc
    have hgt : n < (support (signedVariables W)).card := by omega
    have hcross := balanced_nontrivial_crossing hb
      (balanced_rank_nontrivial chi hb hrank hgt)
    obtain ⟨x,y,e,f,a,b,sx,sy,A,B,C,E,F,hxy,havoid,hW,hbal,hcard⟩ := literal_crossing hb hcross
    have hrem : colourType (colours chi (signedVariables (remainder a b A B C E F))) <+
        colourBound m n := by
      apply (signedRank_iff _).mp
      have hcut := signedRank_crossing
        (colours chi (signedVariables A)) (colours chi (signedVariables B))
        (colours chi (signedVariables C)) (colours chi (signedVariables E))
        (colours chi (signedVariables F)) (chi x) (chi y) sx sy
      have hcut' : signedRank (colours chi (signedVariables (remainder a b A B C E F))) ≤
          signedRank (colours chi (signedVariables W)) := by
        simpa only [hW,crossing,signedVariables_append,signedVariables_var,
          signedVariables_remainder,colours,List.map_append,List.map_cons,List.map_nil,
          List.append_assoc,Prod.fst,Prod.snd] using hcut
      exact hcut'.trans hrank
    have hbudget : n+2*D ≤ (support (signedVariables (remainder a b A B C E F))).card := by omega
    obtain ⟨P,hPbal,hPcolour,hPcard⟩ := ih (remainder a b A B C E F) hbal hrem hbudget
    let Q := Extraction.step x y hxy e f a b sx sy A B C E F havoid P
    have hresult : ∃ R : Extraction (D+1) (crossing x y e f a b sx sy A B C E F),
        Balanced (signedVariables (finalWord R)) ∧
        colourType (colours chi (signedVariables (finalWord R))) <+ colourBound m n ∧
        (support (signedVariables (finalWord R))).card + 2*(D+1) =
          (support (signedVariables (crossing x y e f a b sx sy A B C E F))).card := by
      refine ⟨Q,hPbal,hPcolour,?_⟩
      change (support (signedVariables (finalWord P))).card + 2*(D+1) = _
      rw [← hW]
      omega
    subst W
    exact hresult

end NikolovSegal.CrossingKernel
