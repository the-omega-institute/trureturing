/- GID: D5/S3/QuadraticForms/PolynomialSignature
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/PolynomialSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial-sign formulas characterize actual symmetric matrix signatures. -/

import D5.S3.QuadraticForms.ActualSignature
import Mathlib.Algebra.MvPolynomial.Eval

/-!
The compiler produces a finite disjunction of finite conjunctions of polynomial
sign conditions in the original variables. Correctness assumes symmetry only
at the assignment under consideration. Dimension zero, singular matrices and
vanishing diagonal pivots are included, with no degree or rank hypotheses.
-/

open scoped BigOperators
open D5.S3.QuadraticForms.ActualSignature
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.QuadraticForms.PolynomialSignature

abbrev Poly (σ : Type*) := MvPolynomial σ ℝ
inductive Sign where | neg | zero | pos
  deriving DecidableEq

def Sign.holds : Sign → ℝ → Prop
  | .neg, x => x < 0
  | .zero, x => x = 0
  | .pos, x => 0 < x

abbrev SignAtom (σ : Type*) := Poly σ × Sign
abbrev Formula (σ : Type*) := List (List (SignAtom σ))
def holds {σ : Type*} (x : σ → ℝ) (F : Formula σ) : Prop :=
  ∃ c ∈ F, ∀ a ∈ c, a.2.holds (MvPolynomial.eval x a.1)
def atom {σ : Type*} (p : Poly σ) (s : Sign) : Formula σ := [[(p,s)]]
def truth {σ : Type*} (p : Prop) [Decidable p] : Formula σ := if p then [[]] else []
def conj {σ : Type*} (F G : Formula σ) : Formula σ :=
  F.flatMap (fun f => G.map (fun g => f ++ g))
def disj {σ : Type*} (F G : Formula σ) : Formula σ := F ++ G

def all {σ ι : Type*} [Fintype ι] (f : ι → SignAtom σ) : Formula σ :=
  [((Finset.univ.toList).map f)]
def any {σ ι : Type*} [Fintype ι] (f : ι → Formula σ) : Formula σ :=
  (Finset.univ.toList).flatMap f

def compile {σ : Type*} : (n : ℕ) → Mat (Poly σ) n → ℤ → Formula σ
  | 0, _, z => truth (z = 0)
  | n+1, A, z =>
    disj (conj (all (fun ij : Fin (n+1) × Fin (n+1) => (A ij.1 ij.2, .zero)))
              (truth (z = 0)))
      (disj (any (fun i => disj
        (conj (atom (A i i) .pos) (compile n (residualOne A i) (z-1)))
        (conj (atom (A i i) .neg) (compile n (residualOne A i) (z+1)))))
      (match n with
       | 0 => []
       | m+1 => conj (all (fun i => (A i i, .zero)))
         (any (fun i => any (fun j => conj
           (disj (atom (A i (i.succAbove j)) .pos) (atom (A i (i.succAbove j)) .neg))
           (compile m (residualTwo A i j) z))))))

/-- At each symmetric specialization, the finite sign formula gives the actual signature. -/
theorem compile_iff_signature {σ : Type*} (n : ℕ) (A : Mat (Poly σ) n)
    (z : ℤ) (x : σ → ℝ)
    (hs : ∀ i j, MvPolynomial.eval x (A i j) = MvPolynomial.eval x (A j i)) :
    holds x (compile n A z) ↔
      signature (Matrix.toQuadraticForm' (fun i j => MvPolynomial.eval x (A i j))) = z := by
  have compile_iff (n : ℕ) (A : Mat (Poly σ) n) (z : ℤ) :
      holds x (compile n A z) ↔
        Realizes n (fun i j => MvPolynomial.eval x (A i j)) z := by
    classical
    have hatom (p : Poly σ) (s : Sign) : holds x (atom p s) ↔ s.holds (MvPolynomial.eval x p) := by
      simp [holds, atom]
    have htruth (p : Prop) [Decidable p] : holds (σ := σ) x (truth p) ↔ p := by
      by_cases h : p <;> simp [truth, h, holds]
    have hconj (F G : Formula σ) : holds x (conj F G) ↔ holds x F ∧ holds x G := by
      simp only [holds, conj, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨c, ⟨f, hf, g, hg, rfl⟩, hc⟩
        exact ⟨⟨f,hf,fun a ha => hc a (List.mem_append_left _ ha)⟩,
          ⟨g,hg,fun a ha => hc a (List.mem_append_right _ ha)⟩⟩
      · rintro ⟨⟨f,hf,hf'⟩,⟨g,hg,hg'⟩⟩
        exact ⟨f++g,⟨f,hf,g,hg,rfl⟩,fun a ha => (List.mem_append.mp ha).elim (hf' a) (hg' a)⟩
    have hdisj (F G : Formula σ) : holds x (disj F G) ↔ holds x F ∨ holds x G := by
      simp only [holds, disj, List.mem_append]
      aesop
    have hall {ι : Type} [Fintype ι] (f : ι → SignAtom σ) :
        holds x (all f) ↔ ∀ i, (f i).2.holds (MvPolynomial.eval x (f i).1) := by
      simp only [holds, all, List.mem_singleton, exists_eq_left, List.mem_map,
        Finset.mem_toList, Finset.mem_univ, true_and]
      constructor
      · intro h i; exact h (f i) ⟨i,rfl⟩
      · intro h a ha; obtain ⟨i,rfl⟩ := ha; exact h i
    have hany {ι : Type} [Fintype ι] (f : ι → Formula σ) :
        holds x (any f) ↔ ∃ i, holds x (f i) := by
      simp only [holds, any, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
      aesop
    have hone {m} (B : Mat (Poly σ) (m+1)) (i) :
        (fun r s => MvPolynomial.eval x (residualOne B i r s)) =
        residualOne (fun r s => MvPolynomial.eval x (B r s)) i := by
      ext r s
      simp [residualOne]
    have htwo {m} (B : Mat (Poly σ) (m+2)) (i j) :
        (fun r s => MvPolynomial.eval x (residualTwo B i j r s)) =
        residualTwo (fun r s => MvPolynomial.eval x (B r s)) i j := by
      ext r s
      simp [residualTwo]
    induction n using Nat.twoStepInduction generalizing z with
    | zero => simp [compile, Realizes, htruth]
    | one =>
      have hnil : holds (σ := σ) x [] ↔ False := by simp [holds]
      simp only [compile, Realizes, hdisj, hconj, hall, hany, hatom, htruth,
        Sign.holds, hnil, or_false, Prod.forall]
    | more n ih ih' =>
      simp only [compile, Realizes, hdisj, hconj, hall, hany, hatom, htruth,
        Sign.holds, ih, ih', hone, htwo, Prod.forall]
      apply or_congr Iff.rfl
      apply or_congr Iff.rfl
      apply and_congr Iff.rfl
      apply exists_congr
      intro i
      apply exists_congr
      intro j
      rw [ne_iff_lt_or_gt]
      tauto
  exact (compile_iff n A z).trans
    (realizes_iff_signature n (fun i j => MvPolynomial.eval x (A i j)) hs z)

end D5.S3.QuadraticForms.PolynomialSignature
