/- GID: D5/S3/FiniteGroups/NikolovSegal/LetterCrossing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/LetterCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.BalancedCrossingLift
import D5.S3.FiniteGroups.NikolovSegal.Equation47WordCoupling

set_option autoImplicit false
open scoped List

namespace NikolovSegal.CrossingKernel
open Equation47WordCoupling BalancedCrossing
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

def signedVariable : Letter V S → Option (V × Bool)
  | .var x _ s => some (x,s)
  | .constant _ => none

/-- Exact paper projection: erase constants and automorphisms, retain signs. -/
def signedVariables (W : List (Letter V S)) : Word V := W.filterMap signedVariable

@[simp] theorem signedVariables_append (A B : List (Letter V S)) :
    signedVariables (A++B) = signedVariables A ++ signedVariables B := by
  simp [signedVariables]

@[simp] theorem signedVariables_var (x : V) (g : MulAut S) (s : Bool) :
    signedVariables [.var x g s] = [(x,s)] := rfl

@[simp] theorem signedVariables_twist (g : MulAut S) (W : List (Letter V S)) :
    signedVariables (twist g W) = signedVariables W := by
  induction W with
  | nil => rfl
  | cons l W ih =>
    cases l with
    | var x h s =>
      change (x,s) :: signedVariables (twist g W) = (x,s) :: signedVariables W
      rw [ih]
    | constant c => exact ih

@[simp] theorem signedVariables_remainder (a b : MulAut S)
    (A B C D E : List (Letter V S)) :
    signedVariables (remainder a b A B C D E) =
      signedVariables A ++ signedVariables D ++ signedVariables C ++ signedVariables B ++ signedVariables E := by
  simp [remainder,List.append_assoc]

/-- Split the actual Letter word at a retained signed variable. All skipped
constants remain in the literal prefix; no word is reconstructed from keys. -/
theorem split_signed {W : List (Letter V S)} {A B : Word V} (x : V) (s : Bool)
    (h : signedVariables W = A ++ (x,s)::B) :
    ∃ (P Q : List (Letter V S)) (g : MulAut S),
      W = P ++ [.var x g s] ++ Q ∧ signedVariables P = A ∧ signedVariables Q = B := by
  obtain ⟨U,T,hW,hU,hT⟩ := List.filterMap_eq_append_iff.mp h
  obtain ⟨H,l,Q,hT,hH,hl,hQ⟩ := List.filterMap_eq_cons_iff.mp hT
  have hHnil : signedVariables H = [] := List.filterMap_eq_nil_iff.mpr hH
  change signedVariables U = A at hU
  cases l with
  | constant c => simp [signedVariable] at hl
  | var y g t =>
    have he : (y,t) = (x,s) := Option.some.inj hl
    cases he
    refine ⟨U++H,Q,g,?_,?_,hQ⟩
    · simp [hW,hT,List.append_assoc]
    · simp [signedVariables_append,hHnil,hU]

theorem avoids_of_signed (W : List (Letter V S)) (x : V)
    (h : ∀ p ∈ signedVariables W, p.1 ≠ x) : avoids W x := by
  intro g s hp
  have hm : (x,s) ∈ signedVariables W := by
    simp only [signedVariables,List.mem_filterMap]
    exact ⟨.var x g s,hp,rfl⟩
  exact h (x,s) hm rfl

/-- A fresh actual automorphism-bearing crossing. Its four automorphisms
come from the original Letter word; constants in all five segments survive. -/
theorem literal_crossing {W : List (Letter V S)}
    (hb : Balanced (signedVariables W)) (hc : Crossing (signedVariables W)) :
    ∃ (x y : V) (e f a b : MulAut S) (sx sy : Bool)
      (A B C D E : List (Letter V S)), x ≠ y ∧
      (∀ T ∈ [A,B,C,D,E], avoids T x ∧ avoids T y) ∧
      W = crossing x y e f a b sx sy A B C D E ∧
      Balanced (signedVariables (remainder a b A B C D E)) ∧
      (support (signedVariables (remainder a b A B C D E))).card + 2 =
        (support (signedVariables W)).card := by
  obtain ⟨x,y,sx,sy,A0,B0,C0,D0,E0,hxy,hW⟩ := hc
  have hshape : signedVariables W = A0 ++ (x,!sx)::(B0 ++ (y,!sy)::(C0 ++
      (x,sx)::(D0 ++ (y,sy)::E0))) := by simpa [List.append_assoc] using hW
  obtain ⟨A,W1,e,hWA,hA,h1⟩ := split_signed x (!sx) hshape
  obtain ⟨B,W2,f,hWB,hB,h2⟩ := split_signed y (!sy) h1
  obtain ⟨C,W3,g,hWC,hC,h3⟩ := split_signed x sx h2
  obtain ⟨D,E,k,hWD,hD,hE⟩ := split_signed y sy h3
  let a : MulAut S := g * e⁻¹
  let b : MulAut S := k * f⁻¹
  have hfresh := crossing_fresh hb x y sx sy A0 B0 C0 D0 E0 hW
  have hav : ∀ T ∈ [A,B,C,D,E], avoids T x ∧ avoids T y := by
    intro T hT
    have hs : ∀ p ∈ signedVariables T, p ∈ A0++B0++C0++D0++E0 := by
      intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl <;>
        simp_all only [hA,hB,hC,hD,hE,List.mem_append] <;> tauto
    exact ⟨avoids_of_signed T x (fun p hp => (hfresh p (hs p hp)).1),
      avoids_of_signed T y (fun p hp => (hfresh p (hs p hp)).2)⟩
  refine ⟨x,y,e,f,a,b,sx,sy,A,B,C,D,E,hxy,hav,?_,?_,?_⟩
  · simp [hWA,hWB,hWC,hWD,crossing,a,b,List.append_assoc,mul_assoc]
  · simpa [hA,hB,hC,hD,hE] using crossing_balanced hb x y sx sy A0 B0 C0 D0 E0 hW
  · simpa [hA,hB,hC,hD,hE] using crossing_support_card hb x y sx sy A0 B0 C0 D0 E0 hW

end NikolovSegal.CrossingKernel
