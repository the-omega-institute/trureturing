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
def liftedDiagram (D : Zigzag.{u, v} K) (n : ℕ) :
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
  terminalFiltrationLayer D n i.succ ⧸
    (terminalFiltrationLayer D n i.castSucc).comap
      (terminalFiltrationLayer D n i.succ).subtype

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

end D5.S3.HomologicalAlgebra.Persistence.ZigzagTerminalIntervals
