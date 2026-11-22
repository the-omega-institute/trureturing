/- GID: D5/S3/VertexAlgebra/Modules/MixedBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Modules/MixedBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Linear projection and integer-coset reindexing of finite mixed Jacobi. -/

import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

/-! Finite mixed Borcherds identities for three independent module actions. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.IntertwinerZhuTop

open StateFieldResidueReconstruction (integerBinomial epsilon)
open scoped BigOperators

noncomputable section

variable {V U Y X : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup X] [Module ℂ X]

/-- A bilinear mode family indexed by integers. -/
abbrev Modes (V M N : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] :=
  ℤ → V →ₗ[ℂ] M →ₗ[ℂ] N

def iterateTerm (A : Modes V U U) (I : Modes U Y X)
    (a : V) (u : U) (y : Y) (m q r : ℤ) (j : ℕ) : X :=
  integerBinomial m j • I (m + q - j) (A (r + j) a u) y

def firstTerm (B : Modes V X X) (I : Modes U Y X)
    (a : V) (u : U) (y : Y) (m q r : ℤ) (j : ℕ) : X :=
  (((-1 : ℂ) ^ j) * integerBinomial r j) • B (m + r - j) a (I (q + j) u y)

def secondTerm (C : Modes V Y Y) (I : Modes U Y X)
    (a : V) (u : U) (y : Y) (m q r : ℤ) (j : ℕ) : X :=
  (((-1 : ℂ) ^ j) * integerBinomial r j) •
    (epsilon r • I (q + r - j) u (C (m + j) a y))

/-- All three coefficient families are finitely supported and their sums satisfy mixed Jacobi. -/
def Borcherds (A : Modes V U U) (C : Modes V Y Y) (B : Modes V X X)
    (I : Modes U Y X) : Prop :=
  ∀ (a : V) (u : U) (y : Y) (m q r : ℤ),
    Function.HasFiniteSupport (iterateTerm A I a u y m q r) ∧
    Function.HasFiniteSupport (firstTerm B I a u y m q r) ∧
    Function.HasFiniteSupport (secondTerm C I a u y m q r) ∧
    (∑ᶠ j, iterateTerm A I a u y m q r j) =
      (∑ᶠ j, firstTerm B I a u y m q r j) - (∑ᶠ j, secondTerm C I a u y m q r j)

/-- Transport all three finite supports and the coefficient identity through
linear maps intertwining the two input actions and the output action. -/
theorem Borcherds.project
    {V' U' Y' X' : Type*}
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup Y'] [Module ℂ Y'] [AddCommGroup X'] [Module ℂ X']
    {A : Modes V U U} {C : Modes V Y Y} {B : Modes V X X} {I : Modes U Y X}
    {A' : Modes V' U' U'} {C' : Modes V' Y' Y'} {B' : Modes V' X' X'}
    (h : Borcherds A C B I)
    (f : V' →ₗ[ℂ] V) (g : U' →ₗ[ℂ] U) (j : Y' →ₗ[ℂ] Y) (p : X →ₗ[ℂ] X')
    (ha : ∀ n a u, g (A' n a u) = A n (f a) (g u))
    (hc : ∀ n a y, j (C' n a y) = C n (f a) (j y))
    (hb : ∀ n a x, p (B n (f a) x) = B' n a (p x)) :
    Borcherds A' C' B' (fun n => ((I n).compl₁₂ g j).compr₂ p) := by
  intro a u y m q r
  obtain ⟨hl, hf, hs, hsum⟩ := h (f a) (g u) (j y) m q r
  let I' := fun n : ℤ => ((I n).compl₁₂ g j).compr₂ p
  have hleft (k : ℕ) :
      p (iterateTerm A I (f a) (g u) (j y) m q r k) =
        iterateTerm A' I' a u y m q r k := by
    simp only [iterateTerm, I', LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, map_smul, ha]
  have hfirst (k : ℕ) :
      p (firstTerm B I (f a) (g u) (j y) m q r k) =
        firstTerm B' I' a u y m q r k := by
    simp only [firstTerm, I', LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, map_smul, hb]
  have hsecond (k : ℕ) :
      p (secondTerm C I (f a) (g u) (j y) m q r k) =
        secondTerm C' I' a u y m q r k := by
    simp only [secondTerm, I', LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, map_smul, hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hleft] using hl.fun_comp (map_zero p)
  · simpa only [hfirst] using hf.fun_comp (map_zero p)
  · simpa only [hsecond] using hs.fun_comp (map_zero p)
  · have projected := congrArg p hsum
    rw [map_sub, map_finsum p hl, map_finsum p hf, map_finsum p hs] at projected
    simpa only [hleft, hfirst, hsecond] using projected

/-- The integer label `n` represents the physical mode `σ + n`. -/
def shiftedModes (F : ℂ → U →ₗ[ℂ] Y →ₗ[ℂ] X) (σ : ℂ) : Modes U Y X :=
  fun n => F (σ + (n : ℂ))

/-- Changing the origin of the physical coset by an integer relabels mixed Jacobi. -/
theorem Borcherds.reindex_physical
    {A : Modes V U U} {C : Modes V Y Y} {B : Modes V X X}
    {F : ℂ → U →ₗ[ℂ] Y →ₗ[ℂ] X} {σ : ℂ}
    (h : Borcherds A C B (shiftedModes F σ)) (d : ℤ) :
    Borcherds A C B (shiftedModes F (σ + (d : ℂ))) := by
  intro a u y m q r
  have modeIndex (n : ℤ) :
      shiftedModes F σ (d + n) = shiftedModes F (σ + (d : ℂ)) n := by
    simp only [shiftedModes, Int.cast_add, add_assoc]
  have iterateIndex (k : ℕ) : m + (d + q) - (k : ℤ) = d + (m + q - (k : ℤ)) := by
    omega
  have firstIndex (k : ℕ) : d + q + (k : ℤ) = d + (q + (k : ℤ)) := by
    rw [add_assoc]
  have secondIndex (k : ℕ) : d + q + r - (k : ℤ) = d + (q + r - (k : ℤ)) := by
    omega
  have iterate_eq :
      iterateTerm A (shiftedModes F σ) a u y m (d + q) r =
        iterateTerm A (shiftedModes F (σ + (d : ℂ))) a u y m q r := by
    funext k
    simp only [iterateTerm, iterateIndex, modeIndex]
  have first_eq :
      firstTerm B (shiftedModes F σ) a u y m (d + q) r =
        firstTerm B (shiftedModes F (σ + (d : ℂ))) a u y m q r := by
    funext k
    simp only [firstTerm, firstIndex, modeIndex]
  have second_eq :
      secondTerm C (shiftedModes F σ) a u y m (d + q) r =
        secondTerm C (shiftedModes F (σ + (d : ℂ))) a u y m q r := by
    funext k
    simp only [secondTerm, secondIndex, modeIndex]
  simpa only [iterate_eq, first_eq, second_eq] using h a u y m (d + q) r

end

end D5.S3.VertexAlgebra.IntertwinerZhuTop

/--
info: 'D5.S3.VertexAlgebra.IntertwinerZhuTop.Borcherds.project' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms D5.S3.VertexAlgebra.IntertwinerZhuTop.Borcherds.project

/--
info: 'D5.S3.VertexAlgebra.IntertwinerZhuTop.Borcherds.reindex_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms D5.S3.VertexAlgebra.IntertwinerZhuTop.Borcherds.reindex_physical
