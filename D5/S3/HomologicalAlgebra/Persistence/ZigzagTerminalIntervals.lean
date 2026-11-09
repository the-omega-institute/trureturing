/- GID: D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Terminal interval coordinates and actual right-filtration multiplicities. -/

import D5.S3.HomologicalAlgebra.Persistence.ZigzagNaturalLift
import D5.S3.HomologicalAlgebra.FilteredVectorSpaceComplement
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.List.Pairwise

namespace D5.S3.HomologicalAlgebra.Persistence.ZigzagTerminalIntervals

open CategoryTheory CategoryTheory.Limits
open ZigzagNaturalLift

universe u v

variable {K : Type u} [Field K]

/-- Both the input and interval diagrams take values in `ModuleCat.{max u v} K`.
The source category and its actual generating edges are unchanged. -/
def liftedDiagram (D : Zigzag.{u,v} K) (n : ℕ) :
    Paths (Vertex D n) ⥤ ModuleCat.{max u v} K :=
  diagram D n ⋙ ModuleCat.uliftFunctor.{u} K

/-- The coefficient module on a supported vertex, and the zero module elsewhere. -/
def intervalSpace (b i : ℕ) : ModuleCat.{max u v} K :=
  if b ≤ i then ModuleCat.of K (ULift.{v} K)
  else ModuleCat.of K PUnit.{max u v + 1}

/-- Identity between two supported vertices; zero whenever an endpoint is absent. -/
def intervalMap (b s t : ℕ) :
    intervalSpace (K := K) b s ⟶ intervalSpace (K := K) b t := by
  unfold intervalSpace
  split <;> split
  · exact 𝟙 _
  · exact 0
  · exact 0
  · exact 0

/-- Terminal intervals use the native path category of `D`, including its actual arrows. -/
def terminalInterval (D : Zigzag.{u,v} K) (n : ℕ) (b : Fin (n + 1)) :
    Paths (Vertex D n) ⥤ ModuleCat.{max u v} K :=
  Paths.lift {
    obj := fun i => intervalSpace b.val i.val
    map := fun {i j} _ => intervalMap b.val i.val j.val }

/-- A finite categorical biproduct of terminal intervals, with repeated births retained. -/
noncomputable def intervalSum (D : Zigzag.{u,v} K) (n r : ℕ)
    (birth : Fin r → Fin (n + 1)) : Paths (Vertex D n) ⥤ ModuleCat.{max u v} K := by
  letI : HasFiniteBiproducts (Paths (Vertex D n) ⥤ ModuleCat.{max u v} K) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact ⨁ (fun j => terminalInterval D n (birth j))

private theorem filtration_length (D : Zigzag.{u,v} K) (n : ℕ) :
    (rightFiltration D n).length = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : D.arrow n <;> simp [rightFiltration, h, ih, Nat.add_assoc]

private theorem filtration_pairwise (D : Zigzag.{u,v} K) (n : ℕ) :
    (rightFiltration D n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [rightFiltration]
  | succ n ih =>
    cases h : D.arrow n with
    | inl f =>
      simp only [rightFiltration, h, List.pairwise_append, List.pairwise_singleton,
        and_true, List.mem_singleton]
      constructor
      · exact ih.map (fun _ _ h => Submodule.map_mono h)
      · intro _ _ _ ht
        subst ht
        exact le_top
    | inr g =>
      simp only [rightFiltration, h, List.pairwise_cons]
      exact ⟨fun _ _ => bot_le, ih.map (fun _ _ h => Submodule.comap_mono h)⟩

/-- The indexed layers are precisely the native list, with both endpoint layers retained. -/
def terminalFiltrationLayer (D : Zigzag.{u,v} K) (n : ℕ) (i : Fin (n + 2)) :
    Submodule K (D.space n) :=
  (rightFiltration D n).get ⟨i.val, by rw [filtration_length]; exact i.isLt⟩

private theorem layer_monotone (D : Zigzag.{u,v} K) (n : ℕ) :
    Monotone (terminalFiltrationLayer D n) := by
  intro i j hij
  exact (filtration_pairwise D n).rel_get_of_le hij

/-- The actual inclusion of one filtration layer in its successor. -/
def filtrationInclusion (D : Zigzag.{u,v} K) (n : ℕ) (i : Fin (n + 1)) :
    terminalFiltrationLayer D n i.castSucc →ₗ[K]
      terminalFiltrationLayer D n i.succ :=
  Submodule.inclusion (layer_monotone D n (Fin.castSucc_le_succ i))

/-- The quotient is taken inside the actual next layer, along its actual subtype map. -/
def successiveFactor (D : Zigzag.{u,v} K) (n : ℕ) (i : Fin (n + 1)) :=
  terminalFiltrationLayer D n i.succ ⧸
    (terminalFiltrationLayer D n i.castSucc).comap
      (terminalFiltrationLayer D n i.succ).subtype

/-- Birth order appends at an actual forward arrow and prepends at an actual backward arrow. -/
def birthList (D : Zigzag.{u,v} K) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => match D.arrow n with
    | Sum.inl _ => birthList D n ++ [n + 1]
    | Sum.inr _ => (n + 1) :: birthList D n

private theorem birth_length (D : Zigzag.{u,v} K) (n : ℕ) :
    (birthList D n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : D.arrow n <;> simp [birthList, h, ih]

private theorem birth_bound (D : Zigzag.{u,v} K) (n : ℕ) :
    ∀ b ∈ birthList D n, b < n + 1 := by
  induction n with
  | zero => simp [birthList]
  | succ n ih =>
    cases h : D.arrow n <;> simp only [birthList, h, List.mem_append,
      List.mem_singleton, List.mem_cons]
    · intro b hb
      rcases hb with hb | rfl
      · exact Nat.lt.step (ih b hb)
      · exact Nat.lt_succ_self _
    · intro b hb
      rcases hb with rfl | hb
      · exact Nat.lt_succ_self _
      · exact Nat.lt.step (ih b hb)

/-- Filtration positions are mapped to birth vertices, rather than confused with them. -/
def birthOrder (D : Zigzag.{u,v} K) (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  let j : Fin (birthList D n).length := ⟨i.val, by rw [birth_length]; exact i.isLt⟩
  ⟨(birthList D n).get j, birth_bound D n _ (List.get_mem _ _)⟩

/-- The original positive-length endpoint, including every quotient count. -/
def TerminalIntervalDecomposition (D : Zigzag.{u,v} K) (n : ℕ) : Prop :=
  ∃ r : ℕ, ∃ birth : Fin r → Fin (n + 1),
    Nonempty (liftedDiagram D n ≅ intervalSum D n r birth) ∧
      ∀ i : Fin (n + 1),
        Fintype.card {j : Fin r // birth j = birthOrder D n i} =
          Module.finrank K (successiveFactor D n i)

end D5.S3.HomologicalAlgebra.Persistence.ZigzagTerminalIntervals
