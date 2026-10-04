/- GID: D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Right filtrations reconstruct natural endomorphisms of streamlined zigzags. -/

import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Isomorphisms

namespace D5.S3.HomologicalAlgebra.Persistence.ZigzagNaturalLift

open CategoryTheory

universe u v

variable {K : Type u} [Field K]

/-- A sequence of actual spaces and a chosen actual arrow at each adjacent pair.
Only its finite prefix is used by a finite diagram. -/
structure Zigzag (K : Type u) [Field K] where
  space : ℕ → ModuleCat.{v} K
  arrow : ∀ i, (space i →ₗ[K] space (i + 1)) ⊕ (space (i + 1) →ₗ[K] space i)

/-- The right filtration at vertex `n`, hence on a prefix of length `n + 1`. -/
def rightFiltration (D : Zigzag.{u, v} K) : (n : ℕ) → List (Submodule K (D.space n))
  | 0 => [⊥, ⊤]
  | n + 1 => match D.arrow n with
    | Sum.inl f => (rightFiltration D n).map (Submodule.map f) ++ [⊤]
    | Sum.inr g => ⊥ :: (rightFiltration D n).map (Submodule.comap g)

/-- Every active forward arrow is injective and every active backward arrow is surjective. -/
def RightStreamlined (D : Zigzag K) (n : ℕ) : Prop :=
  ∀ i, i < n → match D.arrow i with
    | Sum.inl f => Function.Injective f
    | Sum.inr g => Function.Surjective g

/-- Preservation of all recursively generated layers, including zero and the whole space. -/
def Preserves (D : Zigzag K) (n : ℕ) (a : D.space n →ₗ[K] D.space n) : Prop :=
  ∀ R ∈ rightFiltration D n, ∀ x ∈ R, a x ∈ R

/-- The vertices retain the zigzag identity in the type of their quiver. -/
abbrev Vertex (D : Zigzag.{u, v} K) (n : ℕ) := Fin (n + 1)

/- The path-category object type is a reducible synonym, but elaboration can
   retain the synonym at implicit-transparency boundaries. -/
def pathVertex {K : Type u} [Field K] {D : Zigzag.{u, v} K} {n : ℕ}
    (i : Paths (Vertex D n)) : Vertex D n :=
  cast (show Paths (Vertex D n) = Vertex D n from rfl) i

def pathVertexVal {K : Type u} [Field K] {D : Zigzag.{u, v} K} {n : ℕ}
    (i : Paths (Vertex D n)) : ℕ :=
  (cast (show Paths (Vertex D n) = Vertex D n from rfl) i).val

/-- Generating edges of the finite oriented path, with their actual arrow identities. -/
inductive Edge (D : Zigzag.{u, v} K) (n : ℕ) : Vertex D n → Vertex D n →
    Type (max (u + 1) (v + 1) + 1)
  | forward (i : Fin n) (f : D.space i.val →ₗ[K] D.space (i.val + 1))
      (actual : D.arrow i.val = Sum.inl f) : Edge D n i.castSucc i.succ
  | backward (i : Fin n) (g : D.space (i.val + 1) →ₗ[K] D.space i.val)
      (actual : D.arrow i.val = Sum.inr g) : Edge D n i.succ i.castSucc

instance (D : Zigzag.{u, v} K) (n : ℕ) : Quiver (Vertex D n) := ⟨Edge D n⟩

/-- The generating-arrow diagram uses exactly the chosen linear arrows. -/
def arrows (D : Zigzag.{u, v} K) (n : ℕ) : Vertex D n ⥤q ModuleCat.{v} K :=
  {
    obj := fun i => D.space i.val
    map := fun e => match e with
      | Edge.forward _ f _ => ModuleCat.ofHom f
      | Edge.backward _ g _ => ModuleCat.ofHom g }

/-- The finite diagram sends paths to compositions of the chosen actual arrows. -/
def diagram (D : Zigzag.{u, v} K) (n : ℕ) : Paths (Vertex D n) ⥤ ModuleCat.{v} K :=
  Paths.lift (arrows D n)

/-- Terminal filtration preservation suffices to reconstruct all components and all path squares.
There is no assumed compatible family or natural transformation in the hypotheses. -/
theorem exists_unique_natural_endomorphism (D : Zigzag.{u,v} K) (n : ℕ)
    (streamlined : RightStreamlined D n)
    (a : D.space n →ₗ[K] D.space n) (preserves : Preserves D n a) :
    ∃! η : diagram D n ⟶ diagram D n, (η.app (Fin.last n)).hom = a := by
  classical
  let Compatible := fun (b : ∀ i, D.space i →ₗ[K] D.space i) i =>
    match D.arrow i with
    | Sum.inl f => f.comp (b i) = (b (i + 1)).comp f
    | Sum.inr g => g.comp (b (i + 1)) = (b i).comp g
  have top_member : ∀ m, (⊤ : Submodule K (D.space m)) ∈ rightFiltration D m := by
    intro m
    induction m with
    | zero => simp [rightFiltration]
    | succ m ih =>
      cases h : D.arrow m with
      | inl f => simp [rightFiltration, h]
      | inr g =>
        simp only [rightFiltration, h, List.mem_cons, List.mem_map]
        exact Or.inr ⟨⊤, ih, Submodule.comap_top g⟩
  have bot_member : ∀ m, (⊥ : Submodule K (D.space m)) ∈ rightFiltration D m := by
    intro m
    induction m with
    | zero => simp [rightFiltration]
    | succ m ih =>
      cases h : D.arrow m with
      | inl f =>
        simp only [rightFiltration, h, List.mem_append, List.mem_map, List.mem_singleton]
        exact Or.inl ⟨⊥, ih, Submodule.map_bot f⟩
      | inr g => simp [rightFiltration, h]
  have build : ∀ m, RightStreamlined D m →
      ∀ A : D.space m →ₗ[K] D.space m, Preserves D m A →
      ∃ b : ∀ i, D.space i →ₗ[K] D.space i,
        b m = A ∧ ∀ i, i < m → Compatible b i := by
    intro m
    induction m with
    | zero =>
      intro _ A _
      refine ⟨Function.update (fun _ => 0) 0 A, ?_, ?_⟩
      · simp
      · intro i hi; omega
    | succ m ih =>
      intro hs A hA
      have hp : RightStreamlined D m := fun i hi => hs i (Nat.lt.step hi)
      have extend : ∀ B : D.space m →ₗ[K] D.space m, Preserves D m B →
          (match D.arrow m with
          | Sum.inl f => f.comp B = A.comp f
          | Sum.inr g => g.comp A = B.comp g) →
          ∃ b : ∀ i, D.space i →ₗ[K] D.space i,
            b (m + 1) = A ∧ ∀ i, i < m + 1 → Compatible b i := by
        intro B hB square
        obtain ⟨b, hb, hc⟩ := ih hp B hB
        refine ⟨Function.update b (m + 1) A, ?_, ?_⟩
        · simp
        · intro i hi
          by_cases last : i = m
          · subst i
            simpa [Compatible, hb] using square
          · have earlier : i < m := by omega
            have ne₁ : i ≠ m + 1 := by omega
            have ne₂ : i + 1 ≠ m + 1 := by omega
            simpa only [Compatible, Function.update_of_ne ne₁,
              Function.update_of_ne ne₂] using hc i earlier
      cases actual : D.arrow m with
      | inl f =>
        have injective : Function.Injective f := by
          simpa only [RightStreamlined, actual] using hs m (Nat.lt_succ_self m)
        have in_range : ∀ x, (A.comp f) x ∈ LinearMap.range f := by
          intro x
          have layer : (⊤ : Submodule K (D.space m)).map f ∈ rightFiltration D (m + 1) := by
            simp only [rightFiltration, actual, List.mem_append, List.mem_map]
            exact Or.inl ⟨⊤, top_member m, rfl⟩
          have hx : f x ∈ (⊤ : Submodule K (D.space m)).map f := ⟨x, trivial, rfl⟩
          simpa only [LinearMap.comp_apply, Submodule.map_top] using hA _ layer _ hx
        let B := LinearMap.codRestrictOfInjective (A.comp f) f injective in_range
        have square : f.comp B = A.comp f :=
          LinearMap.codRestrictOfInjective_comp _ _ _ _
        have hB : Preserves D m B := by
          intro R hR x hx
          have layer : R.map f ∈ rightFiltration D (m + 1) := by
            simp only [rightFiltration, actual, List.mem_append, List.mem_map]
            exact Or.inl ⟨R, hR, rfl⟩
          obtain ⟨y, hy, heq⟩ := hA _ layer (f x) ⟨x, hx, rfl⟩
          have equal : y = B x := injective
            (heq.trans (LinearMap.congr_fun square x).symm)
          rw [← equal]
          exact hy
        apply extend B hB
        simpa only [actual] using square
      | inr g =>
        have surjective : Function.Surjective g := by
          simpa only [RightStreamlined, actual] using hs m (Nat.lt_succ_self m)
        have kernel_layer : LinearMap.ker g ∈ rightFiltration D (m + 1) := by
          simp only [rightFiltration, actual, List.mem_cons, List.mem_map]
          exact Or.inr ⟨⊥, bot_member m, Submodule.comap_bot g⟩
        have kills : LinearMap.ker g ≤ LinearMap.ker (g.comp A) := by
          intro x hx
          simpa only [LinearMap.mem_ker, LinearMap.comp_apply] using
            hA _ kernel_layer x hx
        let quotient := (LinearMap.ker g).liftQ (g.comp A) kills
        let equivalence := g.quotKerEquivOfSurjective surjective
        let B := quotient.comp equivalence.symm.toLinearMap
        have square : g.comp A = B.comp g := by
          ext x
          simp [B, quotient, equivalence]
        have hB : Preserves D m B := by
          intro R hR x hx
          obtain ⟨y, rfl⟩ := surjective x
          have layer : R.comap g ∈ rightFiltration D (m + 1) := by
            simp only [rightFiltration, actual, List.mem_cons, List.mem_map]
            exact Or.inr ⟨R, hR, rfl⟩
          have hy := hA _ layer y hx
          change (B.comp g) y ∈ R
          rw [← LinearMap.congr_fun square y]
          exact hy
        apply extend B hB
        simpa only [actual] using square
  have unique : ∀ m, RightStreamlined D m →
      ∀ b c : ∀ i, D.space i →ₗ[K] D.space i,
        b m = c m → (∀ i, i < m → Compatible b i) →
        (∀ i, i < m → Compatible c i) → ∀ i, i ≤ m → b i = c i := by
    intro m
    induction m with
    | zero =>
      intro _ b c heq _ _ i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      rw [hi0]
      exact heq
    | succ m ih =>
      intro hs b c heq hb hc
      have terminal : b m = c m := by
        have sb := hb m (Nat.lt_succ_self m)
        have sc := hc m (Nat.lt_succ_self m)
        cases actual : D.arrow m with
        | inl f =>
          have inj : Function.Injective f := by simpa [RightStreamlined, actual] using hs m (Nat.lt_succ_self m)
          simp only [Compatible, actual] at sb sc
          ext x
          apply inj
          exact (LinearMap.congr_fun sb x).trans
            ((congrArg (fun z : D.space (m + 1) →ₗ[K] D.space (m + 1) => z (f x)) heq).trans
              (LinearMap.congr_fun sc x).symm)
        | inr g =>
          have surj : Function.Surjective g := by simpa [RightStreamlined, actual] using hs m (Nat.lt_succ_self m)
          simp only [Compatible, actual] at sb sc
          ext x
          obtain ⟨y, rfl⟩ := surj x
          exact (LinearMap.congr_fun sb y).symm.trans
            ((congrArg (fun z : D.space (m + 1) →ₗ[K] D.space (m + 1) => g (z y)) heq).trans
              (LinearMap.congr_fun sc y))
      intro i hi
      by_cases last : i = m + 1
      · subst i; exact heq
      · exact ih (fun j hj => hs j (Nat.lt.step hj)) b c terminal
          (fun j hj => hb j (Nat.lt.step hj)) (fun j hj => hc j (Nat.lt.step hj)) i (by omega)
  obtain ⟨b, terminal, squares⟩ := build n streamlined a preserves
  -- `Paths V` is definitionally the same type as `V`, but the path-category
  -- API deliberately keeps the wrapper visible.  Keep the coercion explicit
  -- at every object boundary so elaboration does not mix path objects with
  -- the underlying finite vertices.
  let component : ∀ i : Paths (Vertex D n),
      (diagram D n).obj i →ₗ[K] (diagram D n).obj i := fun i =>
    cast (by
      change (D.space (pathVertexVal i) →ₗ[K] D.space (pathVertexVal i)) =
        ((diagram D n).obj i →ₗ[K] (diagram D n).obj i)
      rfl) (b (pathVertexVal i))
  let η : diagram D n ⟶ diagram D n := {
    app := fun i => ModuleCat.ofHom (component i)
    naturality := by
      intro i j p
      refine Paths.induction (V := Vertex D n)
        (P := fun {i j} p =>
          (diagram D n).map p ≫
              ModuleCat.ofHom (component j) =
            ModuleCat.ofHom (component i) ≫
              (diagram D n).map p) ?_ ?_ p
      · intro i
        rw [(diagram D n).map_id]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · intro i j k q e ih
        have edge_square :
            (diagram D n).map ((Paths.of (Vertex D n)).map e) ≫
                ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj k)) =
              ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj j)) ≫
                (diagram D n).map ((Paths.of (Vertex D n)).map e) := by
          cases e with
          | forward i f actual =>
            apply ModuleCat.hom_ext
            have hs := squares i.val i.isLt
            simp only [Compatible, actual] at hs
            change b (i.val + 1) ∘ₗ f = f ∘ₗ b i.val
            exact hs.symm
          | backward i g actual =>
            apply ModuleCat.hom_ext
            have hs := squares i.val i.isLt
            simp only [Compatible, actual] at hs
            change b i.val ∘ₗ g = g ∘ₗ b (i.val + 1)
            exact hs.symm
        calc
          (diagram D n).map (q ≫ (Paths.of (Vertex D n)).map e) ≫
                ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj k)) =
              ((diagram D n).map q ≫
                (diagram D n).map ((Paths.of (Vertex D n)).map e)) ≫
                ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj k)) := by
                rw [Functor.map_comp]
          _ = (diagram D n).map q ≫
                ((diagram D n).map ((Paths.of (Vertex D n)).map e) ≫
                  ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj k))) := by
                exact Category.assoc _ _ _
          _ = (diagram D n).map q ≫
                (ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj j)) ≫
                  (diagram D n).map ((Paths.of (Vertex D n)).map e)) := by
                exact congrArg (fun z => (diagram D n).map q ≫ z) edge_square
          _ = ((diagram D n).map q ≫
                ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj j))) ≫
                (diagram D n).map ((Paths.of (Vertex D n)).map e) := by
                exact (Category.assoc _ _ _).symm
          _ = (ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj i)) ≫
                (diagram D n).map q) ≫
                (diagram D n).map ((Paths.of (Vertex D n)).map e) := by
                rw [ih]
          _ = ModuleCat.ofHom (component ((Paths.of (Vertex D n)).obj i)) ≫
                ((diagram D n).map q ≫
                  (diagram D n).map ((Paths.of (Vertex D n)).map e)) := by
                exact Category.assoc _ _ _ }
  refine ⟨η, terminal, ?_⟩
  intro θ hθ
  let thetaAt : ∀ i, i ≤ n → D.space i →ₗ[K] D.space i := fun i hi =>
    (θ.app (⟨i, Nat.lt_succ_of_le hi⟩ : Vertex D n)).hom
  let c : ∀ i, D.space i →ₗ[K] D.space i := fun i =>
    if hi : i ≤ n then thetaAt i hi else 0
  have c_terminal : c n = b n := by
    by_cases hn : n ≤ n
    · simp only [c, dif_pos hn]
      have hlast :
          (⟨n, Nat.lt_succ_of_le hn⟩ : Vertex D n) = Fin.last n := by
        apply Fin.ext
        rfl
      unfold thetaAt
      have hcomp :
          HEq
            (ModuleCat.Hom.hom
              (θ.app (⟨n, Nat.lt_succ_of_le hn⟩ : Vertex D n)))
            (ModuleCat.Hom.hom (θ.app (Fin.last n))) := by
        cases hlast
        rfl
      exact eq_of_heq (hcomp.trans (heq_of_eq (hθ.trans terminal.symm)))
    · exact False.elim (hn le_rfl)
  have c_squares : ∀ i, i < n → Compatible c i := by
    intro i hi
    let index : Fin n := ⟨i, hi⟩
    cases actual : D.arrow i with
    | inl f =>
      have h := congrArg ModuleCat.Hom.hom
        (θ.naturality ((Paths.of (Vertex D n)).map (Edge.forward index f actual)))
      simp only [Compatible, actual]
      change f ∘ₗ c i = c (i + 1) ∘ₗ f
      have hobj0 :
          (Paths.of (Vertex D n)).obj (⟨i, Nat.lt_succ_of_lt hi⟩ : Vertex D n) =
            (Paths.of (Vertex D n)).obj index.castSucc := by
        apply Fin.ext
        rfl
      have hobj1 :
          (Paths.of (Vertex D n)).obj
              (⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ : Vertex D n) =
            (Paths.of (Vertex D n)).obj index.succ := by
        apply Fin.ext
        rfl
      have h0 : c i = (θ.app ((Paths.of (Vertex D n)).obj index.castSucc)).hom := by
        by_cases hc : i ≤ n
        · simp only [c, dif_pos hc]
          unfold thetaAt
          cases hobj0
          rfl
        · exact False.elim (hc (Nat.le_of_lt hi))
      have h1 : c (i + 1) =
          (θ.app ((Paths.of (Vertex D n)).obj index.succ)).hom := by
        by_cases hc : i + 1 ≤ n
        · simp only [c, dif_pos hc]
          unfold thetaAt
          cases hobj1
          rfl
        · exact False.elim (hc (Nat.succ_le_of_lt hi))
      rw [h0, h1]
      change ModuleCat.Hom.hom (θ.app ((Paths.of (Vertex D n)).obj index.succ)) ∘ₗ f =
        f ∘ₗ ModuleCat.Hom.hom (θ.app ((Paths.of (Vertex D n)).obj index.castSucc)) at h
      exact h.symm
    | inr g =>
      have h := congrArg ModuleCat.Hom.hom
        (θ.naturality ((Paths.of (Vertex D n)).map (Edge.backward index g actual)))
      simp only [Compatible, actual]
      change g ∘ₗ c (i + 1) = c i ∘ₗ g
      have hobj0 :
          (Paths.of (Vertex D n)).obj (⟨i, Nat.lt_succ_of_lt hi⟩ : Vertex D n) =
            (Paths.of (Vertex D n)).obj index.castSucc := by
        apply Fin.ext
        rfl
      have hobj1 :
          (Paths.of (Vertex D n)).obj
              (⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ : Vertex D n) =
            (Paths.of (Vertex D n)).obj index.succ := by
        apply Fin.ext
        rfl
      have h0 : c i = (θ.app ((Paths.of (Vertex D n)).obj index.castSucc)).hom := by
        by_cases hc : i ≤ n
        · simp only [c, dif_pos hc]
          unfold thetaAt
          cases hobj0
          rfl
        · exact False.elim (hc (Nat.le_of_lt hi))
      have h1 : c (i + 1) =
          (θ.app ((Paths.of (Vertex D n)).obj index.succ)).hom := by
        by_cases hc : i + 1 ≤ n
        · simp only [c, dif_pos hc]
          unfold thetaAt
          cases hobj1
          rfl
        · exact False.elim (hc (Nat.succ_le_of_lt hi))
      rw [h1, h0]
      change ModuleCat.Hom.hom (θ.app ((Paths.of (Vertex D n)).obj index.castSucc)) ∘ₗ g =
        g ∘ₗ ModuleCat.Hom.hom (θ.app ((Paths.of (Vertex D n)).obj index.succ)) at h
      exact h.symm
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  have h := unique n streamlined c b c_terminal c_squares squares (pathVertexVal i)
    (Nat.le_of_lt_succ (pathVertex i).isLt)
  dsimp [η]
  change (θ.app i).hom = b (pathVertexVal i)
  have hci : c (pathVertexVal i) = (θ.app i).hom := by
    have hobj :
        (Paths.of (Vertex D n)).obj
            (⟨pathVertexVal i,
              Nat.lt_succ_of_le (Nat.le_of_lt_succ (pathVertex i).isLt)⟩ :
              Vertex D n) = i := by
      apply Fin.ext
      rfl
    by_cases hc : pathVertexVal i ≤ n
    · simp only [c, dif_pos hc]
      unfold thetaAt
      cases hobj
      rfl
    · exact False.elim (hc (Nat.le_of_lt_succ (pathVertex i).isLt))
  rw [← hci]
  exact h

end D5.S3.HomologicalAlgebra.Persistence.ZigzagNaturalLift
