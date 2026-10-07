/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47WordCoupling
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47WordCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeII
import Mathlib.Tactic.Group

set_option autoImplicit false

/-!
The constructive substitution in Part I Proposition 8.2 (pp. 218--219),
consumed recursively as in Proposition 8.4.  Parameters are actual constants;
only the two crossing variables are changed in each step.  Automorphisms are
composed in Lean's left-action convention.  A finite extraction certificate
is syntactic data, not a coverage premise.  Its quantitative existence for
the actual Proposition 9.1 residual words is still to be proved.
-/
namespace NikolovSegal.Equation47WordCoupling
universe u v
variable {S : Type u} [Group S] {V : Type v} [DecidableEq V]

inductive Letter (V : Type v) (S : Type u) [Group S] where
  | var (key : V) (aut : MulAut S) (negative : Bool)
  | constant (value : S)

private def signed (x : S) (neg : Bool) : S := if neg then x⁻¹ else x

private def letterValue (z : V → S) : Letter V S → S
  | .var v g neg => signed (g (z v)) neg
  | .constant s => s

def wordValue (W : List (Letter V S)) (z : V → S) : S :=
  (W.map (letterValue z)).prod

def twist (g : MulAut S) (W : List (Letter V S)) : List (Letter V S) :=
  W.map (fun l => match l with
    | .var v h neg => .var v (g*h) neg
    | .constant s => .constant (g s))

def avoids (W : List (Letter V S)) (x : V) : Prop :=
  ∀ g neg, Letter.var x g neg ∉ W

theorem value_append (A B : List (Letter V S)) (z : V → S) :
    wordValue (A++B) z = wordValue A z * wordValue B z := by
  simp [wordValue]

theorem value_twist (g : MulAut S) (W : List (Letter V S)) (z : V → S) :
    wordValue (twist g W) z = g (wordValue W z) := by
  induction W with
  | nil => simp [wordValue,twist]
  | cons l W ih =>
    change letterValue z (match l with
      | .var v h neg => .var v (g*h) neg
      | .constant s => .constant (g s)) * wordValue (twist g W) z =
        g (letterValue z l * wordValue W z)
    rw [ih,map_mul]
    cases l with
    | constant s => rfl
    | var v h neg => cases neg <;>
        simp [letterValue,signed,MulAut.mul_apply,map_inv]

private theorem value_update (W : List (Letter V S)) (z : V → S) (x : V)
    (s : S) (h : avoids W x) :
    wordValue W (Function.update z x s) = wordValue W z := by
  unfold wordValue
  congr 1
  apply List.map_congr_left
  intro l hl
  cases l with
  | constant s => rfl
  | var v g neg =>
    have hv : v ≠ x := by
      intro he
      subst v
      exact h g neg hl
    simp [letterValue,Function.update_of_ne hv]

def inverseWord (W : List (Letter V S)) : List (Letter V S) :=
  W.reverse.map (fun l => match l with
    | .var v g neg => .var v g (!neg)
    | .constant s => .constant s⁻¹)

theorem value_inverse (W : List (Letter V S)) (z : V → S) :
    wordValue (inverseWord W) z = (wordValue W z)⁻¹ := by
  induction W with
  | nil => simp [inverseWord,wordValue]
  | cons l W ih =>
    simp only [inverseWord,List.reverse_cons,List.map_append]
    rw [value_append]
    change wordValue (inverseWord W) z * _ = (letterValue z l * wordValue W z)⁻¹
    rw [ih,mul_inv_rev]
    congr 1
    cases l with
    | constant s => simp [wordValue,letterValue]
    | var v g neg => cases neg <;> simp [wordValue,letterValue,signed]

theorem value_flatten (L : List (List (Letter V S))) (z : V → S) :
    wordValue L.flatten z = (L.map (fun W => wordValue W z)).prod := by
  induction L with
  | nil => simp [wordValue]
  | cons W L ih => simp [List.flatten_cons,value_append,ih]

@[simp] theorem value_var (z : V → S) (v : V) (g : MulAut S) (neg : Bool) :
    wordValue [Letter.var v g neg] z = if neg then (g (z v))⁻¹ else g (z v) := by
  simp [wordValue,letterValue,signed]

@[simp] theorem value_constant (z : V → S) (s : S) :
    wordValue [Letter.constant s] z = s := by
  simp [wordValue,letterValue]

def crossing (x y : V) (e f a b : MulAut S) (sx sy : Bool)
    (A B C D E : List (Letter V S)) : List (Letter V S) :=
  A ++ [.var x e (!sx)] ++ B ++ [.var y f (!sy)] ++ C ++
    [.var x (a*e) sx] ++ D ++ [.var y (b*f) sy] ++ E

def remainder (a b : MulAut S)
    (A B C D E : List (Letter V S)) : List (Letter V S) :=
  twist b (twist a.symm (twist b.symm (twist a A ++ D) ++ C)) ++ twist b B ++ E

def twistedValue (a b : MulAut S) (x y : S) : S :=
  x⁻¹ * y⁻¹ * a x * b y

/-- Exact automorphism-bearing crossing substitution.  All other variables
and all constants are retained, and both possible signs are allowed. -/
theorem crossing_substitution
    (x y : V) (hxy : x ≠ y) (e f a b : MulAut S) (sx sy : Bool)
    (A B C D E : List (Letter V S))
    (havoid : ∀ W ∈ [A,B,C,D,E], avoids W x ∧ avoids W y)
    (z : V → S) (xi eta : S) :
    ∃ z' : V → S,
      (∀ v, v ≠ x → v ≠ y → z' v = z v) ∧
      wordValue (crossing x y e f a b sx sy A B C D E) z' =
        twistedValue a b xi eta * wordValue (remainder a b A B C D E) z := by
  let U1 := b.symm (a (wordValue A z) * wordValue D z)
  let U2 := a.symm (U1 * wordValue C z)
  let p := signed (e.symm (U2⁻¹ * xi * wordValue A z)) sx
  let r := signed (f.symm (U1⁻¹ * eta * U2 * wordValue B z)) sy
  let z' := Function.update (Function.update z x p) y r
  have hW : ∀ W ∈ [A,B,C,D,E], wordValue W z' = wordValue W z := by
    intro W hW
    obtain ⟨hx,hy⟩ := havoid W hW
    rw [value_update W (Function.update z x p) y r hy,value_update W z x p hx]
  have hx : z' x = p := by simp [z',hxy]
  have hy : z' y = r := by simp [z']
  refine ⟨z',?_,?_⟩
  · intro v hvx hvy
    simp [z',hvx,hvy]
  · have hA := hW A (by simp)
    have hB := hW B (by simp)
    have hC := hW C (by simp)
    have hD := hW D (by simp)
    have hE := hW E (by simp)
    simp only [crossing,remainder,value_append,value_twist]
    simp only [wordValue,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      letterValue,MulAut.mul_apply] at hA hB hC hD hE ⊢
    rw [hA,hB,hC,hD,hE,hx,hy]
    cases sx <;> cases sy <;>
      simp only [p,r,signed,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        ↓reduceIte,inv_inv,map_inv,MulEquiv.apply_symm_apply] <;>
      dsimp [twistedValue,U1,U2] <;>
      simp only [wordValue,map_mul,map_inv,MulEquiv.apply_symm_apply] <;> group

/-- The literal finite pair extraction of Proposition 8.4.  This definition
records displayed word decompositions and fresh crossing variables, rather
than arbitrary surjectivity statements or identifications of residual values.
Its length bound for the actual type-II word is an unfinished obligation. -/
inductive Extraction : ℕ → List (Letter V S) → Type (max u v)
  | zero (W) : Extraction 0 W
  | step {n} (x y : V) (hxy : x ≠ y) (e f a b : MulAut S) (sx sy : Bool)
      (A B C D E : List (Letter V S))
      (havoid : ∀ W ∈ [A,B,C,D,E], avoids W x ∧ avoids W y)
      (tail : Extraction n (remainder a b A B C D E)) :
      Extraction (n+1) (crossing x y e f a b sx sy A B C D E)

private def alphaList {n : ℕ} {W : List (Letter V S)}
    (P : Extraction n W) : List (MulAut S) :=
  match P with
  | .zero _ => []
  | .step _ _ _ _ _ a _ _ _ _ _ _ _ _ _ tail => a :: alphaList tail

private def betaList {n : ℕ} {W : List (Letter V S)}
    (P : Extraction n W) : List (MulAut S) :=
  match P with
  | .zero _ => []
  | .step _ _ _ _ _ _ b _ _ _ _ _ _ _ _ tail => b :: betaList tail

private def residualWord {n : ℕ} {W : List (Letter V S)}
    (P : Extraction n W) : List (Letter V S) :=
  match P with
  | .zero W => W
  | .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => residualWord tail

private theorem extraction_lengths {n : ℕ} {W : List (Letter V S)}
    (P : Extraction n W) : (alphaList P).length = n ∧ (betaList P).length = n := by
  induction P with
  | zero => simp [alphaList,betaList]
  | step x y hxy e f a b sx sy A B C D E havoid tail ih =>
    simp [alphaList,betaList,ih]

private theorem realize_extraction {n : ℕ} {W : List (Letter V S)}
    (P : Extraction n W) (z : V → S) (xi eta : Fin n → S) :
    ∃ z' : V → S, wordValue W z' =
      (List.ofFn (fun i : Fin n => twistedValue
        ((alphaList P)[i.val]'(by rw [(extraction_lengths P).1]; exact i.isLt))
        ((betaList P)[i.val]'(by rw [(extraction_lengths P).2]; exact i.isLt))
        (xi i) (eta i))).prod * wordValue (residualWord P) z := by
  induction P with
  | zero W => exact ⟨z,by simp [residualWord]⟩
  | @step n x y hxy e f a b sx sy A B C D E havoid tail ih =>
    obtain ⟨z1,hz1⟩ := ih (Fin.tail xi) (Fin.tail eta)
    obtain ⟨z2,hother,hz2⟩ := crossing_substitution x y hxy e f a b sx sy
      A B C D E havoid z1 (xi 0) (eta 0)
    refine ⟨z2,?_⟩
    rw [hz2,hz1]
    simp only [alphaList,betaList,residualWord,List.ofFn_succ,List.prod_cons,
      Fin.val_zero,List.getElem_cons_zero,Fin.val_succ,List.getElem_cons_succ,
      Fin.tail_def,mul_assoc]

/-- Exact Part II Theorem 1.1 / Part I Theorem 1.9 input, for this fixed group
and fixed length.  Its uniform finite-simple existence is NOT proved here. -/
def PartIITwistedProductInput (S : Type u) [Group S] (D : ℕ) : Prop :=
  ∀ a b : Fin D → MulAut S, ∀ t : S, ∃ xi eta : Fin D → S,
    orderedProduct (fun i => twistedValue (a i) (b i) (xi i) (eta i)) = t

/-- Consume the real scalar twisted PRODUCT theorem after constructive
finite word extraction.  The residual and its parameters remain fixed while
the independent crossing variables realize the required ordered product. -/
theorem solve_extracted_word {D : ℕ} {W : List (Letter V S)}
    (P : Extraction D W) (hscalar : PartIITwistedProductInput S D)
    (z : V → S) (target : S) : ∃ z' : V → S, wordValue W z' = target := by
  let a : Fin D → MulAut S := fun i => (alphaList P)[i.val]'
    (by rw [(extraction_lengths P).1]; exact i.isLt)
  let b : Fin D → MulAut S := fun i => (betaList P)[i.val]'
    (by rw [(extraction_lengths P).2]; exact i.isLt)
  obtain ⟨xi,eta,h⟩ := hscalar a b (target * (wordValue (residualWord P) z)⁻¹)
  obtain ⟨z',hz'⟩ := realize_extraction P z xi eta
  refine ⟨z',?_⟩
  change orderedProduct _ = _ at h
  change wordValue W z' = orderedProduct
    (fun i => twistedValue (a i) (b i) (xi i) (eta i)) *
      wordValue (residualWord P) z at hz'
  rw [hz',h]
  simp [mul_assoc]

end NikolovSegal.Equation47WordCoupling
