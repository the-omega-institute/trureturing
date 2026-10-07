/- GID: D5/S3/FiniteGroups/NikolovSegal/ExtractionCounting
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/ExtractionCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.ExtractionResidual
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-! Coordinate-retaining realization and quantitative fibres for the actual
WordCoupling.Extraction. The finite-simple twisted-product input remains an
explicit input; no whole-word solver or coordinate-retention oracle is assumed. -/
namespace NikolovSegal.ExtractionCounting
open Equation47WordCoupling CrossingKernel
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

/-- Automorphisms of the actual successive crossings, in extraction order.
The accepted coupling's corresponding lists are private. -/
def alpha {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) : Fin D → MulAut S :=
  match P with
  | .zero _ => Fin.elim0
  | .step _ _ _ _ _ a _ _ _ _ _ _ _ _ _ tail => Fin.cons a (alpha tail)

def beta {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) : Fin D → MulAut S :=
  match P with
  | .zero _ => Fin.elim0
  | .step _ _ _ _ _ _ b _ _ _ _ _ _ _ _ tail => Fin.cons b (beta tail)

/-- Letter evaluation depends only on the signed keys occurring in the
literal word; all original constants and automorphisms stay in evaluation. -/
theorem wordValue_eq_of_signed_agreement (W : List (Letter V S)) (z z' : V → S)
    (h : ∀ p ∈ signedVariables W, z' p.1 = z p.1) : wordValue W z' = wordValue W z := by
  unfold wordValue
  congr 1
  apply List.map_congr_left
  intro l hl
  cases l with
  | constant c => rfl
  | var x g neg =>
    have hp : (x,neg) ∈ signedVariables W := by
      simp only [signedVariables,List.mem_filterMap]
      exact ⟨.var x g neg,hl,rfl⟩
    have hx := h (x,neg) hp
    change (if neg then (g (z' x))⁻¹ else g (z' x)) =
      (if neg then (g (z x))⁻¹ else g (z x))
    rw [hx]

/-- The accepted final-avoidance theorem shows that arbitrary changes of
extracted coordinates leave the actual final residual value unchanged. -/
theorem final_value_of_unextracted_agreement {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (z z' : V → S)
    (h : ∀ v, v ∉ extractedKeys P → z' v = z v) :
    wordValue (finalWord P) z' = wordValue (finalWord P) z := by
  apply wordValue_eq_of_signed_agreement
  intro p hp
  apply h p.1
  intro hkey
  exact signed_of_avoids (finalWord_avoids_extracted P p.1 hkey) p hp rfl

/-- Realize arbitrary extracted twisted factors while retaining EVERY ambient
key outside extractedKeys, including keys absent from W. -/
theorem realize_extraction_retaining {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (z : V → S) (xi eta : Fin D → S) :
    ∃ z' : V → S,
      (∀ v, v ∉ extractedKeys P → z' v = z v) ∧
      wordValue W z' = orderedProduct (fun i =>
        twistedValue (alpha P i) (beta P i) (xi i) (eta i)) * wordValue (finalWord P) z ∧
      wordValue (finalWord P) z' = wordValue (finalWord P) z := by
  induction P with
  | zero W => exact ⟨z,fun _ _ => rfl,by simp [orderedProduct,finalWord],rfl⟩
  | @step n x y hxy e f a b sx sy A B C D E havoid tail ih =>
    obtain ⟨z1,hother1,hz1,_⟩ := ih (Fin.tail xi) (Fin.tail eta)
    obtain ⟨z2,hother2,hz2⟩ := crossing_substitution x y hxy e f a b sx sy
      A B C D E havoid z1 (xi 0) (eta 0)
    have hkeep : ∀ v, v ∉ extractedKeys
        (Extraction.step x y hxy e f a b sx sy A B C D E havoid tail) → z2 v = z v := by
      intro v hv
      have hvx : v ≠ x := by intro he; apply hv; simp [extractedKeys,he]
      have hvy : v ≠ y := by intro he; apply hv; simp [extractedKeys,he]
      have hvt : v ∉ extractedKeys tail := by intro hm; apply hv; simp [extractedKeys,hm]
      rw [hother2 v hvx hvy,hother1 v hvt]
    refine ⟨z2,hkeep,?_,final_value_of_unextracted_agreement _ z z2 hkeep⟩
    rw [hz2,hz1]
    simp only [alpha,beta,finalWord,orderedProduct,List.ofFn_succ,List.prod_cons,
        Fin.cons_zero,Fin.cons_succ,Fin.tail_def,mul_assoc]

/-- Consume the actual twisted PRODUCT input, retaining all unextracted
coordinates of an arbitrary initial assignment. -/
theorem solve_extracted_word_retaining {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (hscalar : PartIITwistedProductInput S D)
    (z : V → S) (target : S) :
    ∃ z' : V → S, wordValue W z' = target ∧
      (∀ v, v ∉ extractedKeys P → z' v = z v) ∧
      wordValue (finalWord P) z' = wordValue (finalWord P) z := by
  obtain ⟨xi,eta,hprod⟩ := hscalar (alpha P) (beta P)
    (target * (wordValue (finalWord P) z)⁻¹)
  obtain ⟨z',hother,hvalue,hfinal⟩ := realize_extraction_retaining P z xi eta
  refine ⟨z',?_,hother,hfinal⟩
  rw [hvalue,hprod]
  simp [mul_assoc]

/-- Unextracted ambient keys, not merely surviving support keys. -/
abbrev Unextracted {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) :=
  {v : V // v ∉ extractedKeys P}

/-- The literal word's genuine solution fibre over a target. -/
abbrev SolutionFiber (W : List (Letter V S)) (target : S) :=
  {z : V → S // wordValue W z = target}

def restrictSolution {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) (target : S) :
    SolutionFiber W target → (Unextracted P → S) := fun z v => z.1 v.1

/-- Every assignment on all unextracted ambient keys extends to a genuine
solution of the original Letter word, with constants, twists and signs intact. -/
theorem solution_restriction_surjective {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (hscalar : PartIITwistedProductInput S D) (target : S) :
    Function.Surjective (restrictSolution P target) := by
  intro rho
  let z : V → S := fun v => if hv : v ∉ extractedKeys P then rho ⟨v,hv⟩ else 1
  obtain ⟨z',hvalue,hother,_⟩ := solve_extracted_word_retaining P hscalar z target
  refine ⟨⟨z',hvalue⟩,?_⟩
  funext v
  change z' v.1 = rho v
  rw [hother v.1 v.2]
  simp [z,v.2]

variable [Fintype V]

/-- The exact 2D key count is derived from the accepted actual Extraction
Nodup and length theorems, with no cardinality premise. -/
theorem extracted_key_card {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) :
    (extractedKeys P).toFinset.card = 2*D := by
  rw [List.toFinset_card_of_nodup (extractedKeys_nodup P),extractedKeys_length P]

theorem unextracted_card {D : ℕ} {W : List (Letter V S)} (P : Extraction D W) :
    Fintype.card (Unextracted P) = Fintype.card V - 2*D := by
  have hchosen : Fintype.card {v : V // v ∈ extractedKeys P} = 2*D := by
    simpa only [List.mem_toFinset] using
      (Fintype.card_coe (extractedKeys P).toFinset).trans (extracted_key_card P)
  exact (Fintype.card_subtype_compl (fun v => v ∈ extractedKeys P)).trans
    (congrArg (fun n => Fintype.card V - n) hchosen)

variable [Fintype S]

/-- A finite fibre instance needs no DecidableEq S assumption in the public
counting theorem. Classical finite enumeration supplies its equality decision. -/
noncomputable instance solutionFiberFintype (W : List (Letter V S)) (target : S) :
    Fintype (SolutionFiber W target) := Fintype.ofFinite _

/-- The required abstract fibre bound, for EVERY target, including D=0 and
empty ambient key types. No whole-word surjectivity/counting input is assumed. -/
theorem solution_fibre_card_lower_bound {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (hscalar : PartIITwistedProductInput S D) (target : S) :
    (Fintype.card S)^(Fintype.card V-2*D) ≤ Fintype.card (SolutionFiber W target) := by
  have hcard := Fintype.card_le_of_surjective (restrictSolution P target)
    (solution_restriction_surjective P hscalar target)
  simpa only [Fintype.card_fun,unextracted_card] using hcard

end NikolovSegal.ExtractionCounting
