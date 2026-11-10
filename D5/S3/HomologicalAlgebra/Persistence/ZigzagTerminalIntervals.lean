/- GID: D5/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/ZigzagTerminalIntervals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Terminal interval coordinates and actual right-filtration multiplicities. -/

import D5.S3.HomologicalAlgebra.Persistence.ZigzagNaturalLift
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.PathCategory.MorphismProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.List.Pairwise

namespace D5.S3.HomologicalAlgebra.Persistence.ZigzagTerminalIntervals

open CategoryTheory CategoryTheory.Limits
open ZigzagNaturalLift


universe u v

variable {K : Type u} [Field K]

/-- Both the input and interval diagrams take values in `ModuleCat.{max u v} K`.
The source category and its actual generating edges are unchanged. -/
def liftedDiagram (D : Zigzag.{u, v} K) (n : ℕ) :
    Paths (Vertex D n) ⥤ ModuleCat.{max u v} K :=
  diagram D n ⋙ ModuleCat.uliftFunctor.{u} K

/-- The coefficient module on a supported vertex, and the zero module elsewhere. -/
def intervalSpace (b i : ℕ) : ModuleCat.{max u v} K :=
  if b ≤ i then ModuleCat.of K (ULift.{v} K)
  else ModuleCat.of K PUnit.{max u v + 1}

private def supportedEquiv (b i : ℕ) (h : b ≤ i) :
    ULift.{v} K ≃ₗ[K] intervalSpace.{u, v} (K := K) b i :=
  (eqToIso (show ModuleCat.of K (ULift.{v} K) = intervalSpace b i by
    simp [intervalSpace, h])).toLinearEquiv

/-- Identity between two supported vertices; zero whenever an endpoint is absent. -/
def intervalMap (b s t : ℕ) :
    intervalSpace (K := K) b s ⟶ intervalSpace (K := K) b t :=
  if h : b ≤ s ∧ b ≤ t then
    ModuleCat.ofHom ((supportedEquiv b t h.2).toLinearMap.comp
      (supportedEquiv b s h.1).symm.toLinearMap)
  else 0

/-- Terminal intervals use the native path category of `D`, including its actual arrows. -/
def terminalInterval (D : Zigzag.{u, v} K) (n : ℕ) (b : Fin (n + 1)) :
    Paths (Vertex D n) ⥤ ModuleCat.{max u v} K :=
  Paths.lift {
    obj := fun i => intervalSpace b.val i.val
    map := fun {i j} _ => intervalMap b.val i.val j.val }

/-- A finite categorical biproduct of terminal intervals, with repeated births retained. -/
noncomputable def intervalSum (D : Zigzag.{u, v} K) (n r : ℕ)
    (birth : Fin r → Fin (n + 1)) : Paths (Vertex D n) ⥤ ModuleCat.{max u v} K := by
  letI : HasFiniteBiproducts (Paths (Vertex D n) ⥤ ModuleCat.{max u v} K) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact ⨁ (fun j => terminalInterval D n (birth j))

private theorem filtration_length (D : Zigzag.{u, v} K) (n : ℕ) :
    (rightFiltration D n).length = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : D.arrow n <;> simp [rightFiltration, h, ih, Nat.add_assoc]

private theorem filtration_pairwise (D : Zigzag.{u, v} K) (n : ℕ) :
    (rightFiltration D n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [rightFiltration]
  | succ n ih =>
    cases h : D.arrow n with
    | inl f =>
      simp only [rightFiltration, h, List.pairwise_append, List.pairwise_singleton,
        List.mem_singleton]
      constructor
      · exact List.Pairwise.map (Submodule.map f) (fun _ _ h => Submodule.map_mono h) ih
      · refine ⟨trivial, ?_⟩
        intro _ _ _ ht
        subst ht
        exact le_top
    | inr g =>
      simp only [rightFiltration, h, List.pairwise_cons]
      exact ⟨fun _ _ => bot_le, List.Pairwise.map (Submodule.comap g) (fun _ _ h => Submodule.comap_mono h) ih⟩

/-- The indexed layers are precisely the native list, with both endpoint layers retained. -/
def terminalFiltrationLayer (D : Zigzag.{u, v} K) (n : ℕ) (i : Fin (n + 2)) :
    Submodule K (D.space n) :=
  (rightFiltration D n).get ⟨i.val, by rw [filtration_length]; exact i.isLt⟩

private theorem layer_monotone (D : Zigzag.{u, v} K) (n : ℕ) :
    Monotone (terminalFiltrationLayer D n) := by
  intro i j hij
  exact (filtration_pairwise D n).rel_get_of_le hij

/-- The actual inclusion of one filtration layer in its successor. -/
def filtrationInclusion (D : Zigzag.{u, v} K) (n : ℕ) (i : Fin (n + 1)) :
    terminalFiltrationLayer D n i.castSucc →ₗ[K]
      terminalFiltrationLayer D n i.succ :=
  Submodule.inclusion (layer_monotone D n (Fin.castSucc_le_succ i))

/-- The quotient is taken inside the actual next layer, along its actual subtype map. -/
abbrev successiveFactor (D : Zigzag.{u, v} K) (n : ℕ) (i : Fin (n + 1)) :=
  terminalFiltrationLayer D n i.succ ⧸ LinearMap.range (filtrationInclusion D n i)

/-- Birth order appends at an actual forward arrow and prepends at an actual backward arrow. -/
def birthList (D : Zigzag.{u, v} K) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => match D.arrow n with
    | Sum.inl _ => birthList D n ++ [n + 1]
    | Sum.inr _ => (n + 1) :: birthList D n

private theorem birth_length (D : Zigzag.{u, v} K) (n : ℕ) :
    (birthList D n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : D.arrow n <;> simp [birthList, h, ih]

private theorem birth_bound (D : Zigzag.{u, v} K) (n : ℕ) :
    ∀ b ∈ birthList D n, b < n + 1 := by
  induction n with
  | zero => simp [birthList]
  | succ n ih =>
    cases h : D.arrow n <;> simp only [birthList, h, List.mem_append,
      List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    · intro b hb
      rcases hb with hb | rfl
      · exact Nat.lt_succ_of_lt (ih b hb)
      · exact Nat.lt_succ_self _
    · intro b hb
      rcases hb with rfl | hb
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (ih b hb)

/-- Filtration positions are mapped to birth vertices, rather than confused with them. -/
def birthOrder (D : Zigzag.{u, v} K) (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  let j : Fin (birthList D n).length := ⟨i.val, by rw [birth_length]; exact i.isLt⟩
  ⟨(birthList D n).get j, birth_bound D n _ (List.get_mem _ _)⟩

/-- The original positive-length endpoint, including every quotient count. -/
def TerminalIntervalDecomposition (D : Zigzag.{u, v} K) (n : ℕ) : Prop :=
  ∃ r : ℕ, ∃ birth : Fin r → Fin (n + 1),
    Nonempty (liftedDiagram D n ≅ intervalSum D n r birth) ∧
      ∀ i : Fin (n + 1),
        Fintype.card {j : Fin r // birth j = birthOrder D n i} =
          Module.finrank K (successiveFactor D n i)

private abbrev Coordinates {J : Type} (birth : J → ℕ) (i : ℕ) :=
  {j : J // birth j ≤ i} → K

private def coordinateInclusion {J : Type} (birth : J → ℕ) (i : ℕ) :
    Coordinates (K := K) birth i →ₗ[K] Coordinates (K := K) birth (i + 1) := by
  classical
  exact {
    toFun := fun x j => if h : birth j.val ≤ i then x ⟨j.val, h⟩ else 0
    map_add' := by intros; funext j; by_cases h : birth j.val ≤ i <;> simp [h]
    map_smul' := by intros; funext j; by_cases h : birth j.val ≤ i <;> simp [h] }

private def coordinateProjection {J : Type} (birth : J → ℕ) (i : ℕ) :
    Coordinates (K := K) birth (i + 1) →ₗ[K] Coordinates (K := K) birth i where
  toFun x j := x ⟨j.val, Nat.le_succ_of_le j.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def extendedBirth {J C : Type} (birth : J → ℕ) (n : ℕ) : J ⊕ C → ℕ :=
  Sum.elim birth (fun _ => n + 1)

private def oldIndex {J C : Type} (birth : J → ℕ) (n i : ℕ) (hi : i ≤ n) :
    {j : J ⊕ C // extendedBirth birth n j ≤ i} ≃ {j : J // birth j ≤ i} where
  toFun j := by
    rcases j with ⟨j | c, hj⟩
    · exact ⟨j, hj⟩
    · simp only [extendedBirth, Sum.elim_inr] at hj
      omega
  invFun j := ⟨Sum.inl j.val, j.property⟩
  left_inv := by
    rintro ⟨j | c, hj⟩
    · rfl
    · simp only [extendedBirth, Sum.elim_inr] at hj
      omega
  right_inv _ := rfl

private def oldCoordinates {J C : Type} (birth : J → ℕ) (n i : ℕ) (hi : i ≤ n) :
    Coordinates (K := K) birth i ≃ₗ[K]
      Coordinates (K := K) (extendedBirth (C := C) birth n) i :=
  LinearEquiv.funCongrLeft K K (oldIndex birth n i hi)

private def appendCoordinates {J C : Type} (birth : J → ℕ) (n : ℕ)
    (hb : ∀ j, birth j ≤ n) :
    Coordinates (K := K) (extendedBirth (C := C) birth n) (n + 1) ≃ₗ[K]
      Coordinates (K := K) birth n × (C → K) where
  toFun x := (fun j => x ⟨Sum.inl j.val, Nat.le_succ_of_le j.property⟩,
    fun c => x ⟨Sum.inr c, le_rfl⟩)
  invFun x j := match j.val with
    | Sum.inl a => x.1 ⟨a, hb a⟩
    | Sum.inr c => x.2 c
  left_inv x := by funext j; rcases j with ⟨j | c, hj⟩ <;> rfl
  right_inv x := by rcases x with ⟨x, y⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private structure StepSplit (D : Zigzag.{u, v} K) (i : ℕ) where
  fresh : Submodule K (D.space (i + 1))
  equiv : (D.space i × fresh) ≃ₗ[K] D.space (i + 1)
  forward : ∀ f, D.arrow i = Sum.inl f → ∀ x, equiv (x, 0) = f x
  backward : ∀ g, D.arrow i = Sum.inr g → ∀ x y, g (equiv (x, y)) = x

private theorem exists_step_split (D : Zigzag.{u, v} K) (i : ℕ)
    (hs : match D.arrow i with
      | Sum.inl f => Function.Injective f
      | Sum.inr g => Function.Surjective g) : Nonempty (StepSplit D i) := by
  classical
  cases h : D.arrow i with
  | inl f =>
    have hf : Function.Injective f := by simpa [h] using hs
    obtain ⟨C, hC⟩ := (LinearMap.range f).exists_isCompl
    let e := (LinearEquiv.ofInjective f hf).prodCongr (LinearEquiv.refl K C) ≪≫ₗ
      (LinearMap.range f).prodEquivOfIsCompl C hC
    refine ⟨⟨C, e, ?_, ?_⟩⟩
    · intro f' hf' x
      have : f' = f := Sum.inl.inj (hf'.symm.trans h)
      subst f'
      simp [e, Submodule.coe_prodEquivOfIsCompl']
    · intro g hg
      simp [h] at hg
  | inr g =>
    have hg : Function.Surjective g := by simpa [h] using hs
    obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
    let f := s.coprod (LinearMap.ker g).subtype
    have hsx : ∀ x, g (s x) = x := fun x => LinearMap.congr_fun hs x
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨x, y⟩ ⟨x', y'⟩ heq
        have hx : x = x' := by
          have h' := congrArg g heq
          simpa [f, LinearMap.coprod_apply, hsx] using h'
        subst x'
        have hy : y = y' := by
          apply Subtype.ext
          exact add_left_cancel heq
        subst y'
        rfl
      · intro y
        refine ⟨(g y, ⟨y - s (g y), ?_⟩), ?_⟩
        · simp [LinearMap.mem_ker, hsx]
        · simp [f, LinearMap.coprod_apply]
    let e := LinearEquiv.ofBijective f hf
    refine ⟨⟨LinearMap.ker g, e, ?_, ?_⟩⟩
    · intro f' hf'
      simp [h] at hf'
    · intro g' hg' x y
      have : g' = g := Sum.inr.inj (hg'.symm.trans h)
      subst g'
      change g (s x + y.val) = x
      simp [hsx]

private structure CoordinateSystem (D : Zigzag.{u, v} K) (n : ℕ) where
  index : Type
  finite : Fintype index
  birth : index → ℕ
  bound : ∀ j, birth j ≤ n
  equiv : ∀ i : Fin (n + 1), D.space i.val ≃ₗ[K] Coordinates (K := K) birth i.val
  forward : ∀ (i : Fin n) f, D.arrow i.val = Sum.inl f → ∀ x,
    equiv i.succ (f x) = coordinateInclusion birth i.val (equiv i.castSucc x)
  backward : ∀ (i : Fin n) g, D.arrow i.val = Sum.inr g → ∀ x,
    equiv i.castSucc (g x) = coordinateProjection birth i.val (equiv i.succ x)

private theorem old_inclusion {J C : Type} (birth : J → ℕ) (n i : ℕ)
    (hi : i + 1 ≤ n) (x : Coordinates (K := K) birth i) :
    oldCoordinates (C := C) birth n (i + 1) hi (coordinateInclusion birth i x) =
      coordinateInclusion (extendedBirth birth n) i
        (oldCoordinates birth n i (by omega) x) := by
  classical
  funext j
  rcases j with ⟨j | c, hj⟩
  · rfl
  · change n + 1 ≤ i + 1 at hj
    omega

private theorem old_projection {J C : Type} (birth : J → ℕ) (n i : ℕ)
    (hi : i + 1 ≤ n) (x : Coordinates (K := K) birth (i + 1)) :
    oldCoordinates (C := C) birth n i (by omega) (coordinateProjection birth i x) =
      coordinateProjection (extendedBirth birth n) i
        (oldCoordinates birth n (i + 1) hi x) := by
  funext j
  rcases j with ⟨j | c, hj⟩
  · rfl
  · change n + 1 ≤ i at hj
    omega

private def allIndices {J : Type} (birth : J → ℕ) (n : ℕ) (hb : ∀ j, birth j ≤ n) :
    {j : J // birth j ≤ n} ≃ J where
  toFun := Subtype.val
  invFun j := ⟨j, hb j⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def extendSystem (D : Zigzag.{u, v} K) (n : ℕ)
    (A : CoordinateSystem D n) (S : StepSplit D n)
    [FiniteDimensional K (D.space (n + 1))] : CoordinateSystem D (n + 1) := by
  classical
  letI := A.finite
  let C := Fin (Module.finrank K S.fresh)
  let basis := Module.finBasis K S.fresh
  let birth : A.index ⊕ C → ℕ := extendedBirth A.birth n
  let lastEquiv : D.space (n + 1) ≃ₗ[K] Coordinates (K := K) birth (n + 1) :=
    S.equiv.symm ≪≫ₗ (A.equiv (Fin.last n)).prodCongr basis.equivFun ≪≫ₗ
      (appendCoordinates A.birth n A.bound).symm
  let e : ∀ i : Fin (n + 2), D.space i.val ≃ₗ[K] Coordinates (K := K) birth i.val :=
    Fin.lastCases lastEquiv (fun i =>
      A.equiv i ≪≫ₗ oldCoordinates A.birth n i.val (Nat.le_of_lt_succ i.isLt))
  refine {
    index := A.index ⊕ C
    finite := inferInstance
    birth := birth
    bound := ?_
    equiv := e
    forward := ?_
    backward := ?_ }
  · rintro (j | c)
    · exact Nat.le_succ_of_le (A.bound j)
    · exact le_rfl
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro f hf x
      have hx : S.equiv.symm (f x) = (x, 0) := by
        rw [← S.forward f hf x]
        exact S.equiv.symm_apply_apply _
      simp only [e, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
      change lastEquiv (f x) = coordinateInclusion birth n
        (oldCoordinates A.birth n n le_rfl (A.equiv (Fin.last n) x))
      simp only [lastEquiv, LinearEquiv.trans_apply, hx, LinearEquiv.prodCongr_apply,
        map_zero]
      funext j
      rcases j with ⟨j | c, hj⟩
      · change (A.equiv (Fin.last n) x) ⟨j, A.bound j⟩ =
          if h : A.birth j ≤ n then (A.equiv (Fin.last n) x) ⟨j, h⟩ else 0
        simp [A.bound j]
      · change (0 : K) = if h : n + 1 ≤ n then _ else 0
        simp
    · intro f hf x
      have hs := A.forward i f hf x
      have hi : i.val + 1 ≤ n := i.isLt
      simpa only [e, birth, Fin.succ_castSucc, Fin.lastCases_castSucc,
        Fin.val_castSucc, Fin.val_succ, LinearEquiv.trans_apply]
        using (congrArg (oldCoordinates (C := C) A.birth n (i.val + 1) hi) hs).trans
          (old_inclusion A.birth n i.val hi (A.equiv i.castSucc x))
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro g hg x
      have hx : g x = (S.equiv.symm x).1 := by
        calc
          g x = g (S.equiv (S.equiv.symm x)) :=
            congrArg g (S.equiv.apply_symm_apply x).symm
          _ = (S.equiv.symm x).1 := S.backward g hg _ _
      simp only [e, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
      change oldCoordinates A.birth n n le_rfl (A.equiv (Fin.last n) (g x)) =
        coordinateProjection birth n (lastEquiv x)
      rw [hx]
      funext j
      rcases j with ⟨j | c, hj⟩
      · rfl
      · change n + 1 ≤ n at hj
        omega
    · intro g hg x
      have hs := A.backward i g hg x
      have hi : i.val + 1 ≤ n := i.isLt
      simpa only [e, birth, Fin.succ_castSucc, Fin.lastCases_castSucc,
        Fin.val_castSucc, Fin.val_succ, LinearEquiv.trans_apply]
        using (congrArg (oldCoordinates (C := C) A.birth n i.val (by omega)) hs).trans
          (old_projection A.birth n i.val hi (A.equiv i.succ x))

private theorem exists_coordinates (D : Zigzag.{u, v} K) (n : ℕ)
    (hs : RightStreamlined D n)
    (hf : ∀ i : Fin (n + 1), FiniteDimensional K (D.space i.val)) :
    Nonempty (CoordinateSystem D n) := by
  classical
  induction n with
  | zero =>
    letI : FiniteDimensional K (D.space 0) := hf 0
    let J := Fin (Module.finrank K (D.space 0))
    let birth : J → ℕ := fun _ => 0
    let e : D.space 0 ≃ₗ[K] Coordinates (K := K) birth 0 :=
      (Module.finBasis K (D.space 0)).equivFun ≪≫ₗ
        LinearEquiv.funCongrLeft K K (allIndices birth 0 (fun _ => le_rfl))
    refine ⟨{
      index := J
      finite := inferInstance
      birth := birth
      bound := fun _ => le_rfl
      equiv := fun i => ?_
      forward := fun i => Fin.elim0 i
      backward := fun i => Fin.elim0 i }⟩
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact e
  | succ n ih =>
    obtain ⟨A⟩ := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi)) (fun i => hf i.castSucc)
    obtain ⟨S⟩ := exists_step_split D n (hs n (Nat.lt_succ_self n))
    letI : FiniteDimensional K (D.space (n + 1)) := hf (Fin.last (n + 1))
    exact ⟨extendSystem D n A S⟩

private noncomputable def subspaceDim {V : Type*} [AddCommGroup V] [Module K V]
    (P : Submodule K V) : ℕ := Module.finrank K P

private def dimensionGaps : List ℕ → List ℕ
  | a :: b :: l => (b - a) :: dimensionGaps (b :: l)
  | _ => []

private theorem gaps_append (l : List ℕ) (a b : ℕ) :
    dimensionGaps (l ++ [a, b]) = dimensionGaps (l ++ [a]) ++ [b - a] := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    cases l with
    | nil => rfl
    | cons d l => simpa [dimensionGaps] using congrArg (List.cons (d - c)) ih

private theorem gaps_add (l : List ℕ) (c : ℕ) :
    dimensionGaps (l.map (· + c)) = dimensionGaps l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simpa [dimensionGaps, Nat.add_sub_add_right] using congrArg (List.cons (b - a)) ih

private theorem filtration_endpoints (D : Zigzag.{u, v} K) (n : ℕ) :
    ∃ l, rightFiltration D n = ⊥ :: (l ++ [⊤]) := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih
    cases h : D.arrow n with
    | inl f =>
      refine ⟨l.map (Submodule.map f) ++ [(⊤ : Submodule K (D.space n)).map f], ?_⟩
      simp [rightFiltration, h, hl, List.map_append, List.append_assoc]
    | inr g =>
      refine ⟨(⊥ : Submodule K (D.space n)).comap g :: l.map (Submodule.comap g), ?_⟩
      simp [rightFiltration, h, hl, List.map_append]

private theorem finrank_comap_of_surjective
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (g : V →ₗ[K] W) (hg : Function.Surjective g)
    (P : Submodule K W) :
    Module.finrank K (P.comap g) = Module.finrank K P + Module.finrank K (LinearMap.ker g) := by
  let f : P.comap g →ₗ[K] P :=
    (g.comp (P.comap g).subtype).codRestrict P (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hg y.val
    exact ⟨⟨x, by change g x ∈ P; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hk : LinearMap.ker f = (LinearMap.ker g).comap (P.comap g).subtype := by
    ext x
    change (f x = 0) ↔ g x.val = 0
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have hle : LinearMap.ker g ≤ P.comap g := by
    intro x hx
    change g x ∈ P
    rw [LinearMap.mem_ker.mp hx]
    exact P.zero_mem
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hk,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hd
  exact hd.symm

/-- The dimension gained at an actual birth vertex. -/
private noncomputable def birthDimension (D : Zigzag.{u, v} K) : ℕ → ℕ
  | 0 => Module.finrank K (D.space 0)
  | b + 1 => Module.finrank K (D.space (b + 1)) - Module.finrank K (D.space b)

private theorem filtration_dimension_gaps (D : Zigzag.{u, v} K) (n : ℕ)
    (hs : RightStreamlined D n)
    (hf : ∀ i : Fin (n + 1), FiniteDimensional K (D.space i.val)) :
    dimensionGaps ((rightFiltration D n).map (subspaceDim (K := K))) =
      (birthList D n).map (birthDimension D) := by
  classical
  induction n with
  | zero =>
    letI : FiniteDimensional K (D.space 0) := hf 0
    simp [rightFiltration, dimensionGaps, birthList, birthDimension, subspaceDim]
  | succ n ih =>
    have hp : RightStreamlined D n := fun i hi => hs i (Nat.lt_succ_of_lt hi)
    have hfp : ∀ i : Fin (n + 1), FiniteDimensional K (D.space i.val) :=
      fun i => hf i.castSucc
    have hind := ih hp hfp
    letI : FiniteDimensional K (D.space n) := hf (Fin.last n).castSucc
    letI : FiniteDimensional K (D.space (n + 1)) := hf (Fin.last (n + 1))
    obtain ⟨l, hl⟩ := filtration_endpoints D n
    cases h : D.arrow n with
    | inl f =>
      have hinj : Function.Injective f := by simpa [h] using hs n (Nat.lt_succ_self n)
      have hdim : ∀ P : Submodule K (D.space n),
          Module.finrank K (P.map f) = Module.finrank K P :=
        fun P => (Submodule.equivMapOfInjective f hinj P).finrank_eq.symm
      have heq : ((rightFiltration D (n + 1)).map (subspaceDim (K := K))) =
          ((rightFiltration D n).map (subspaceDim (K := K))) ++
            [Module.finrank K (D.space (n + 1))] := by
        simp [rightFiltration, h, List.map_map, Function.comp_def, subspaceDim, hdim]
      rw [heq]
      have hend : ((rightFiltration D n).map (subspaceDim (K := K))) =
          (0 :: l.map (subspaceDim (K := K))) ++ [Module.finrank K (D.space n)] := by
        simp [hl, subspaceDim]
      rw [hend, List.append_assoc]
      change dimensionGaps ((0 :: l.map (subspaceDim (K := K))) ++
        [Module.finrank K (D.space n), Module.finrank K (D.space (n + 1))]) = _
      rw [gaps_append, ← hend, hind]
      simp [birthList, h, birthDimension]
    | inr g =>
      have hsurj : Function.Surjective g := by simpa [h] using hs n (Nat.lt_succ_self n)
      let c := Module.finrank K (LinearMap.ker g)
      have hdim : ∀ P : Submodule K (D.space n),
          Module.finrank K (P.comap g) = Module.finrank K P + c :=
        finrank_comap_of_surjective g hsurj
      have htotal := g.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at htotal
      have hc : c = birthDimension D (n + 1) := by dsimp [c, birthDimension]; omega
      have heq : ((rightFiltration D (n + 1)).map (subspaceDim (K := K))) =
          0 :: (((rightFiltration D n).map (subspaceDim (K := K))).map (· + c)) := by
        simp [rightFiltration, h, List.map_map, Function.comp_def, subspaceDim, hdim]
      have hstart : ((rightFiltration D n).map (subspaceDim (K := K))) =
          0 :: (l ++ [⊤]).map (subspaceDim (K := K)) := by
        simp [hl, subspaceDim]
      rw [heq, hstart]
      simp only [List.map_cons, zero_add, dimensionGaps, Nat.sub_zero]
      have hg := gaps_add (0 :: (l ++ [⊤]).map (subspaceDim (K := K))) c
      simp only [List.map_cons, zero_add] at hg
      rw [hg, ← hstart, hind]
      simp [birthList, h, hc]

private theorem gaps_length (l : List ℕ) : (dimensionGaps l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [dimensionGaps, List.length_cons] at *; omega

private theorem gaps_get (l : List ℕ) (i : ℕ) (hi : i + 1 < l.length) :
    (dimensionGaps l)[i]'(by rw [gaps_length]; omega) =
      l[i + 1] - l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases l with
    | nil => simp at hi
    | cons b l =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)

private theorem factor_dimension (D : Zigzag.{u, v} K) (n : ℕ)
    [FiniteDimensional K (D.space n)] (i : Fin (n + 1)) :
    Module.finrank K (successiveFactor D n i) =
      subspaceDim (terminalFiltrationLayer D n i.succ) -
        subspaceDim (terminalFiltrationLayer D n i.castSucc) := by
  unfold successiveFactor filtrationInclusion
  rw [Submodule.range_inclusion, Submodule.finrank_quotient,
    (Submodule.comapSubtypeEquivOfLe (layer_monotone D n (Fin.castSucc_le_succ i))).finrank_eq]
  rfl

private theorem factor_birth_dimension (D : Zigzag.{u, v} K) (n : ℕ)
    (hs : RightStreamlined D n)
    (hf : ∀ i : Fin (n + 1), FiniteDimensional K (D.space i.val))
    (i : Fin (n + 1)) :
    Module.finrank K (successiveFactor D n i) = birthDimension D (birthOrder D n i).val := by
  letI : FiniteDimensional K (D.space n) := hf (Fin.last n)
  have hi : i.val + 1 < ((rightFiltration D n).map (subspaceDim (K := K))).length := by
    rw [List.length_map, filtration_length]
    omega
  have hg := gaps_get ((rightFiltration D n).map (subspaceDim (K := K))) i.val hi
  have heq := congrArg (fun l : List ℕ => l[i.val]!) (filtration_dimension_gaps D n hs hf)
  rw [getElem!_pos _ _ (by rw [gaps_length, List.length_map, filtration_length]; omega),
    getElem!_pos _ _ (by rw [List.length_map, birth_length]; exact i.isLt)] at heq
  rw [hg] at heq
  rw [factor_dimension]
  simpa only [List.getElem_map, terminalFiltrationLayer, List.get_eq_getElem,
    birthOrder, Fin.val_mk, Fin.val_succ, Fin.val_castSucc] using heq

private theorem coordinate_count (D : Zigzag.{u, v} K) (n : ℕ)
    (A : CoordinateSystem D n) (b : Fin (n + 1)) :
    letI := A.finite
    Fintype.card {j : A.index // A.birth j = b.val} = birthDimension D b.val := by
  classical
  letI := A.finite
  have hd : ∀ i : Fin (n + 1), Module.finrank K (D.space i.val) =
      Fintype.card {j : A.index // A.birth j ≤ i.val} := by
    intro i
    exact (A.equiv i).finrank_eq.trans (Module.finrank_pi K)
  cases h : b.val with
  | zero =>
    have hdim := hd ⟨0, by omega⟩
    simpa only [h, birthDimension, Nat.le_zero_eq] using hdim.symm
  | succ k =>
    have hk : k < n + 1 := by omega
    have hcard : Fintype.card {j : A.index // A.birth j ≤ k + 1} =
        Fintype.card {j : A.index // A.birth j ≤ k} +
          Fintype.card {j : A.index // A.birth j = k + 1} := by
      have hp : (fun j : A.index => A.birth j ≤ k + 1) =
          (fun j => A.birth j ≤ k ∨ A.birth j = k + 1) := by
        funext j; apply propext; omega
      calc
        _ = Fintype.card {j : A.index // A.birth j ≤ k ∨ A.birth j = k + 1} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun j => by omega))
        _ = _ := Fintype.card_subtype_or_disjoint _ _ (by
          intro j hle heq x hx
          have h1 := hle x hx
          have h2 := heq x hx
          omega)
    have hnew := hd ⟨k + 1, by omega⟩
    have hold := hd ⟨k, hk⟩
    simp only [h] at hnew ⊢
    simp only [Fin.val_mk] at hnew hold
    rw [birthDimension, hnew, hold, hcard]
    omega

private def valueProjection {J : Type} (birth : J → ℕ) (j : J) (i : ℕ) :
    Coordinates (K := K) birth i →ₗ[K] intervalSpace.{u, v} (K := K) (birth j) i := by
  classical
  exact if h : birth j ≤ i then
    (supportedEquiv (birth j) i h).toLinearMap.comp
      (ULift.moduleEquiv.symm.toLinearMap.comp (LinearMap.proj ⟨j, h⟩))
    else 0

private def scalarExtract (b i : ℕ) (h : b ≤ i) :
    intervalSpace.{u, v} (K := K) b i →ₗ[K] K :=
  ULift.moduleEquiv.toLinearMap.comp (supportedEquiv b i h).symm.toLinearMap

private noncomputable def coordinateProductEquiv {J : Type} (birth : J → ℕ) (i : ℕ) :
    Coordinates (K := K) birth i ≃ₗ[K] ∀ j, intervalSpace.{u, v} (K := K) (birth j) i := by
  classical
  let f := LinearMap.pi (fun j => valueProjection (K := K) birth j i)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    funext j
    have heq := congrArg (fun z => scalarExtract (K := K) (birth j.val) i j.property (z j.val)) hxy
    simpa [f, valueProjection, scalarExtract, j.property] using heq
  · intro y
    refine ⟨fun j => scalarExtract (K := K) (birth j.val) i j.property (y j.val), ?_⟩
    funext j
    by_cases h : birth j ≤ i
    · simp only [f, LinearMap.pi_apply, valueProjection, dif_pos h,
        LinearMap.comp_apply, LinearEquiv.coe_coe, scalarExtract]
      change (supportedEquiv (birth j) i h) ((supportedEquiv (K := K) (birth j) i h).symm (y j)) = y j
      exact (supportedEquiv (birth j) i h).apply_symm_apply _
    · haveI : Subsingleton (intervalSpace.{u, v} (K := K) (birth j) i) := by
        simp only [intervalSpace, if_neg h]
        infer_instance
      exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem value_forward {J : Type} (birth : J → ℕ) (j : J) (i : ℕ)
    (x : Coordinates (K := K) birth i) :
    valueProjection birth j (i + 1) (coordinateInclusion birth i x) =
      (intervalMap.{u, v} (K := K) (birth j) i (i + 1)).hom (valueProjection birth j i x) := by
  classical
  by_cases h0 : birth j ≤ i <;> by_cases h1 : birth j ≤ i + 1
  · simp only [valueProjection, intervalMap, dif_pos h0, dif_pos h1,
      dif_pos (And.intro h0 h1), dif_pos (And.intro h1 h0)]
    simp only [dif_pos h0, dif_pos h1, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply]
    dsimp only [coordinateInclusion]
    change (supportedEquiv (K := K) (birth j) (i + 1) h1)
        (ULift.up (if h : birth j ≤ i then x ⟨j, h⟩ else 0)) =
      (supportedEquiv (K := K) (birth j) (i + 1) h1)
        ((supportedEquiv (K := K) (birth j) i h0).symm
          ((supportedEquiv (K := K) (birth j) i h0) (ULift.up (x ⟨j, h0⟩))))
    rw [dif_pos h0, LinearEquiv.symm_apply_apply]
  · omega
  · have hz : intervalMap.{u,v} (K := K) (birth j) i (i + 1) = 0 := by
      simp [intervalMap, h0]
    rw [hz]
    simp only [valueProjection, dif_pos h1, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.proj_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    change (supportedEquiv (K := K) (birth j) (i + 1) h1)
      (ULift.up (if h : birth j ≤ i then x ⟨j, h⟩ else 0)) = 0
    simp [h0]
    rfl
  · simp [valueProjection, intervalMap, intervalSpace, coordinateInclusion, h0, h1]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem value_backward {J : Type} (birth : J → ℕ) (j : J) (i : ℕ)
    (x : Coordinates (K := K) birth (i + 1)) :
    valueProjection birth j i (coordinateProjection birth i x) =
      (intervalMap.{u, v} (K := K) (birth j) (i + 1) i).hom (valueProjection birth j (i + 1) x) := by
  classical
  by_cases h0 : birth j ≤ i <;> by_cases h1 : birth j ≤ i + 1
  · simp only [valueProjection, intervalMap, dif_pos h0, dif_pos h1,
      dif_pos (And.intro h0 h1), dif_pos (And.intro h1 h0)]
    simp only [dif_pos h0, dif_pos h1, ModuleCat.hom_ofHom,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply]
    dsimp only [coordinateProjection]
    change (supportedEquiv (K := K) (birth j) i h0) (ULift.up (x ⟨j, h1⟩)) =
      (supportedEquiv (K := K) (birth j) i h0)
        ((supportedEquiv (K := K) (birth j) (i + 1) h1).symm
          ((supportedEquiv (K := K) (birth j) (i + 1) h1) (ULift.up (x ⟨j, h1⟩))))
    rw [LinearEquiv.symm_apply_apply]
  · omega
  · simp [valueProjection, intervalMap, intervalSpace, h0, h1]
    rfl
  · simp [valueProjection, intervalMap, intervalSpace, h0, h1]
    rfl

private def coefficientComponent (D : Zigzag.{u, v} K) (n : ℕ)
    (A : CoordinateSystem D n) (j : A.index) (i : Paths (Vertex D n)) :
    (liftedDiagram D n).obj i ⟶ intervalSpace.{u, v} (K := K) (A.birth j) (pathVertexVal i) := by
  change ModuleCat.of K (ULift.{u} (D.space (pathVertexVal i))) ⟶ _
  exact ModuleCat.ofHom ((valueProjection A.birth j (pathVertexVal i)).comp
    ((A.equiv (pathVertex i)).toLinearMap.comp
      (ULift.moduleEquiv : ULift.{u} (D.space (pathVertexVal i)) ≃ₗ[K]
        D.space (pathVertexVal i)).toLinearMap))

private def coefficient (D : Zigzag.{u, v} K) (n : ℕ)
    (A : CoordinateSystem D n) (j : A.index) :
    liftedDiagram D n ⟶ terminalInterval D n ⟨A.birth j, Nat.lt_succ_of_le (A.bound j)⟩ :=
  Paths.liftNatTrans (coefficientComponent D n A j) (by
    intro i k e
    cases e with
    | forward i f actual =>
      apply ModuleCat.hom_ext
      ext x
      change valueProjection A.birth j (i.val + 1) (A.equiv i.succ (f x.down)) =
        (intervalMap.{u, v} (A.birth j) i.val (i.val + 1)).hom
          (valueProjection A.birth j i.val (A.equiv i.castSucc x.down))
      exact (congrArg (valueProjection A.birth j (i.val + 1))
        (A.forward i f actual x.down)).trans (value_forward A.birth j i.val _)
    | backward i g actual =>
      apply ModuleCat.hom_ext
      ext x
      change valueProjection A.birth j i.val (A.equiv i.castSucc (g x.down)) =
        (intervalMap.{u, v} (A.birth j) (i.val + 1) i.val).hom
          (valueProjection A.birth j (i.val + 1) (A.equiv i.succ x.down))
      exact (congrArg (valueProjection A.birth j i.val)
        (A.backward i g actual x.down)).trans (value_backward A.birth j i.val _))

private theorem positive_decomposition (D : Zigzag.{u, v} K) (n : ℕ)
    (hs : RightStreamlined D n)
    (hf : ∀ i : Fin (n + 1), FiniteDimensional K (D.space i.val)) :
    TerminalIntervalDecomposition D n := by
  classical
  obtain ⟨A⟩ := exists_coordinates D n hs hf
  letI := A.finite
  let r := Fintype.card A.index
  let E : Fin r ≃ A.index := (Fintype.equivFin A.index).symm
  let birth : Fin r → Fin (n + 1) :=
    fun k => ⟨A.birth (E k), Nat.lt_succ_of_le (A.bound (E k))⟩
  refine ⟨r, birth, ?_, ?_⟩
  · letI : HasFiniteBiproducts (Paths (Vertex D n) ⥤ ModuleCat.{max u v} K) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    let F := fun k : Fin r => terminalInterval D n (birth k)
    let η : liftedDiagram D n ⟶ ∏ᶜ F := Pi.lift (fun k => coefficient D n A (E k))
    haveI : ∀ i, IsIso (η.app i) := by
      intro i
      let q := piObjIso F i ≪≫ ModuleCat.piIsoPi (fun k => (F k).obj i)
      let l : ULift.{u} (D.space (pathVertexVal i)) ≃ₗ[K]
          ∀ k : Fin r, intervalSpace.{u, v} (K := K) (A.birth (E k)) (pathVertexVal i) :=
        ULift.moduleEquiv ≪≫ₗ A.equiv (pathVertex i) ≪≫ₗ
          coordinateProductEquiv A.birth (pathVertexVal i) ≪≫ₗ
            (LinearEquiv.piCongrLeft K
              (fun j => intervalSpace.{u, v} (K := K) (A.birth j) (pathVertexVal i)) E).symm
      let li : (liftedDiagram D n).obj i ≅ ModuleCat.of K (∀ k : Fin r, (F k).obj i) :=
        l.toModuleIso
      have he : η.app i ≫ q.hom = li.hom := by
        apply ModuleCat.hom_ext
        ext x k
        have hq : q.hom ≫ ModuleCat.ofHom (LinearMap.proj k) = (Pi.π F k).app i := by
          dsimp [q]
          rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype, piObjIso_hom_comp_π]
        have hc : η.app i ≫ q.hom ≫ ModuleCat.ofHom (LinearMap.proj k) =
            (coefficient D n A (E k)).app i := by
          rw [hq, ← NatTrans.comp_app]
          simp [η]
        change ((η.app i ≫ q.hom).hom x) k = ((coefficient D n A (E k)).app i).hom x
        exact congrArg (fun f => f.hom x) hc
      let ei : (liftedDiagram D n).obj i ≅ (∏ᶜ F).obj i := li ≪≫ q.symm
      have hei : η.app i = ei.hom := by
        apply (cancel_mono q.hom).mp
        change η.app i ≫ q.hom = (li.hom ≫ q.inv) ≫ q.hom
        rw [Category.assoc, q.inv_hom_id, Category.comp_id]
        exact he
      rw [hei]
      infer_instance
    haveI : IsIso η := NatIso.isIso_of_isIso_app η
    exact ⟨asIso η ≪≫ (biproduct.isoProduct F).symm⟩
  · intro i
    let e : {k : Fin r // birth k = birthOrder D n i} ≃
        {j : A.index // A.birth j = (birthOrder D n i).val} := {
      toFun := fun k => ⟨E k.val, congrArg Fin.val k.property⟩
      invFun := fun j => ⟨E.symm j.val, Fin.ext (by simpa [birth] using j.property)⟩
      left_inv := by intro k; apply Subtype.ext; exact E.symm_apply_apply k.val
      right_inv := by intro j; apply Subtype.ext; exact E.apply_symm_apply j.val }
    exact (Fintype.card_congr e).trans ((coordinate_count D n A (birthOrder D n i)).trans
      (factor_birth_dimension D n hs hf i).symm)

/-- The zero-vertex source is empty; it is distinct from the native one-vertex prefix. -/
inductive EmptyVertex : Type

instance : Quiver.{0} EmptyVertex := ⟨fun _ _ => Empty⟩

/-- The unique diagram on the genuinely empty path category. -/
def emptyDiagram : Paths EmptyVertex ⥤ ModuleCat.{max u v} K :=
  Paths.lift {
    obj := fun i => nomatch i
    map := fun {i} _ => nomatch i }

/-- The empty occurrence family has an actual empty categorical biproduct. -/
noncomputable def emptyIntervalSum : Paths EmptyVertex ⥤ ModuleCat.{max u v} K := by
  letI : HasFiniteBiproducts (Paths EmptyVertex ⥤ ModuleCat.{max u v} K) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact ⨁ (fun j : Fin 0 => Fin.elim0 j)

/-- Zero length uses the empty source and empty sum. Positive length uses the
native actual-arrow source and all terminal-filtration quotient multiplicities. -/
def FullTerminalIntervalDecomposition (D : Zigzag.{u, v} K) : ℕ → Prop
  | 0 => Nonempty (emptyDiagram.{u, v} (K := K) ≅ emptyIntervalSum.{u, v} (K := K))
  | n + 1 => TerminalIntervalDecomposition D n

/-- A finite-dimensional right-streamlined zigzag is naturally isomorphic to a
finite sum of terminal intervals, with the multiplicities of its actual terminal
right filtration in the actual birth order. No basis or splitting is assumed. -/
theorem exists_terminal_interval_decomposition (D : Zigzag.{u, v} K) (m : ℕ)
    (finite : ∀ i, i < m → FiniteDimensional K (D.space i))
    (streamlined : ∀ i, i + 1 < m → match D.arrow i with
      | Sum.inl f => Function.Injective f
      | Sum.inr g => Function.Surjective g) :
    FullTerminalIntervalDecomposition D m := by
  cases m with
  | zero =>
    exact ⟨NatIso.ofComponents (fun i => nomatch i) (fun {i} => nomatch i)⟩
  | succ n =>
    exact positive_decomposition D n (fun i hi => streamlined i (by omega))
      (fun i => finite i.val i.isLt)

end D5.S3.HomologicalAlgebra.Persistence.ZigzagTerminalIntervals
