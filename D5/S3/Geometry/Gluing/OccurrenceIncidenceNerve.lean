/- GID: D5/S3/Geometry/Gluing/OccurrenceIncidenceNerve
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/OccurrenceIncidenceNerve
   mirror-E: none(waiver:occurrence-labelled-incidence-nerve)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialSet.Nerve]
   utility: none
   digest: Parallel incidence arrows define a finite nonsingular nerve with exact simplex counts. -/

import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Whiskering
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace D5.S3.Geometry.Gluing.OccurrenceIncidenceNerve

namespace IdentityDeletion

open CategoryTheory CategoryTheory.Category Simplicial

universe u v

variable {C : Type u} [Category.{v} C]

-- This hypothesis constrains endomorphisms only. Parallel arrows between
-- different objects remain permitted and are preserved by naturality below.
private theorem hom_eq_transport
    (hendo : ∀ (X : C) (a : X ⟶ X), a = 𝟙 X)
    {X Y : C} (h : X = Y) (a : X ⟶ Y) : a = eqToHom h := by
  subst Y
  exact hendo X a

private theorem elementary_degeneracy_of_repeated_object
    (hendo : ∀ (X : C) (a : X ⟶ X), a = 𝟙 X)
    {n : ℕ} (s : (nerve C) _⦋n + 1⦌) (i : Fin (n + 1))
    (hs : s.obj i.castSucc = s.obj i.succ) :
    s ∈ Set.range ((nerve C).σ i) := by
  let U : Fin (n + 2) ⥤ Fin (n + 2) :=
    (SimplexCategory.toCat.map (SimplexCategory.σ i)).toFunctor ⋙
      (SimplexCategory.toCat.map (SimplexCategory.δ i.castSucc)).toFunctor
  have hU (j : Fin (n + 2)) :
      U.obj j = i.castSucc.succAbove (i.predAbove j) := rfl
  have hU_self : U.obj i.castSucc = i.succ := by
    rw [hU, Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
  have hU_other (j : Fin (n + 2)) (hj : j ≠ i.castSucc) : U.obj j = j := by
    rw [hU]
    exact Fin.succAbove_predAbove hj
  have hle (j : Fin (n + 2)) : j ≤ U.obj j := by
    by_cases hj : j = i.castSucc
    · subst j
      rw [hU_self]
      exact i.castSucc_le_succ
    · simpa only [hU_other j hj] using (le_refl j)
  let eta : 𝟭 (Fin (n + 2)) ⟶ U := {
    app := fun j => homOfLE (hle j)
    naturality := by intros; subsingleton
  }
  let alpha : s ⟶ U ⋙ s := Functor.whiskerRight eta s
  have hobj (j : Fin (n + 2)) : s.obj j = (U ⋙ s).obj j := by
    change s.obj j = s.obj (U.obj j)
    by_cases hj : j = i.castSucc
    · subst j
      rw [hU_self]
      exact hs
    · rw [hU_other j hj]
  have happ (j : Fin (n + 2)) : alpha.app j = eqToHom (hobj j) :=
    hom_eq_transport hendo (hobj j) (alpha.app j)
  let e : s ≅ U ⋙ s := NatIso.ofComponents (fun j => eqToIso (hobj j)) (by
    intro X Y f
    simpa only [eqToIso.hom, ← happ X, ← happ Y] using alpha.naturality f)
  have heq : s = U ⋙ s := Functor.ext_of_iso e hobj (by intro j; rfl)
  refine ⟨(nerve C).δ i.castSucc s, ?_⟩
  change U ⋙ s = s
  exact heq.symm

private theorem elementary_degeneracy_iff_repeated_object
    (hendo : ∀ (X : C) (a : X ⟶ X), a = 𝟙 X)
    {n : ℕ} (s : (nerve C) _⦋n + 1⦌) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve C).σ i) ↔ s.obj i.castSucc = s.obj i.succ := by
  constructor
  · rintro ⟨s, rfl⟩
    change s.obj (i.predAbove i.castSucc) = s.obj (i.predAbove i.succ)
    rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
  · exact elementary_degeneracy_of_repeated_object hendo s i

theorem nondegenerate_iff_adjacent_objects_distinct
    (hendo : ∀ (X : C) (a : X ⟶ X), a = 𝟙 X)
    {n : ℕ} (s : (nerve C) _⦋n + 1⦌) :
    s ∈ (nerve C).nonDegenerate (n + 1) ↔
      ∀ i : Fin (n + 1), s.obj i.castSucc ≠ s.obj i.succ := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate,
    SSet.degenerate_eq_iUnion_range_σ]
  simp only [Set.mem_iUnion, elementary_degeneracy_iff_repeated_object hendo,
    not_exists]

end IdentityDeletion




open CategoryTheory

universe u

open Simplicial

-- Strict rank prevents every elementary degeneracy, without requiring thinness.
private theorem nondegenerate_of_strict_rank {C : Type*} [Category* C]
    (r : C → ℕ) {n : ℕ} (s : (nerve C) _⦋n⦌)
    (h : StrictMono (fun i => r (s.obj i))) :
    s ∈ (nerve C).nonDegenerate n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate,
      SSet.degenerate_eq_iUnion_range_σ]
    intro hs
    simp only [Set.mem_iUnion, Set.mem_range] at hs
    obtain ⟨i, t, rfl⟩ := hs
    have hlt := h i.castSucc_lt_succ
    change r (t.obj (i.predAbove i.castSucc)) < r (t.obj (i.predAbove i.succ)) at hlt
    simpa only [Fin.predAbove_castSucc_self,
      Fin.predAbove_succ_self, lt_self_iff_false] using hlt


inductive Object (V E F : Type u) where
  | vertex (v : V)
  | edge (e : E)
  | face (f : F)

structure Incidence (V E F : Type u) where
  endpoint : E → Fin 2 → V
  side : F → Fin 3 → E
  corner : F → Fin 3 → V
  cornerOfFlag : F → Fin 3 → Fin 2 → Fin 3
  compatible : ∀ f s i,
    corner f (cornerOfFlag f s i) = endpoint (side f s) i

namespace Incidence

variable {V E F : Type u} (P : Incidence V E F)

inductive Arrow : Object V E F → Object V E F → Type u where
  | identity (X : Object V E F) : Arrow X X
  | endpoint (e : E) (i : Fin 2) :
      Arrow (.vertex (P.endpoint e i)) (.edge e)
  | side (f : F) (s : Fin 3) :
      Arrow (.edge (P.side f s)) (.face f)
  | corner (f : F) (c : Fin 3) :
      Arrow (.vertex (P.corner f c)) (.face f)

def compose {X Y Z : Object V E F}
    (a : P.Arrow X Y) (b : P.Arrow Y Z) : P.Arrow X Z := by
  cases a with
  | identity X => exact b
  | endpoint e i =>
    cases b with
    | identity X => exact .endpoint e i
    | side f s =>
      exact (congrArg Object.vertex (P.compatible f s i)) ▸
        Arrow.corner (P := P) f (P.cornerOfFlag f s i)
  | side f s =>
    cases b with
    | identity X => exact .side f s
  | corner f c =>
    cases b with
    | identity X => exact .corner f c


private theorem compose_identity {X Y : Object V E F} (a : P.Arrow X Y) :
    P.compose a (.identity Y) = a := by
  cases a <;> rfl

@[instance_reducible]
def category : Category (Object V E F) where
  Hom := P.Arrow
  id := Arrow.identity (P := P)
  comp := P.compose
  id_comp := by
    intros
    rfl
  comp_id := by
    intro X Y a
    exact compose_identity P a
  assoc := by
    intro W X Y Z a b c
    cases a with
    | identity W => rfl
    | endpoint e i =>
      cases b with
      | identity X =>
        cases c <;> rfl
      | side f s =>
        cases c
        exact compose_identity P _
    | side f s =>
      cases b
      cases c
      rfl
    | corner f s =>
      cases b
      cases c
      rfl

def rank : Object V E F → Fin 3
  | .vertex _ => 0
  | .edge _ => 1
  | .face _ => 2

private theorem endomorphism_eq_identity (X : Object V E F) (a : P.Arrow X X) :
    a = Arrow.identity (P := P) X := by
  cases X <;> cases a <;> rfl

def Carrier (_P : Incidence V E F) : Type u := Object V E F

section General

local instance : Category (Carrier P) := P.category

private theorem rank_lt_of_ne {X Y : Carrier P} (a : X ⟶ Y) (hne : X ≠ Y) :
    (rank X).val < (rank Y).val := by
  change P.Arrow X Y at a
  cases a with
  | identity X => exact False.elim (hne rfl)
  | endpoint e i => simp [rank]
  | side f s => simp [rank]
  | corner f c => simp [rank]

theorem nondegenerate_iff_strict_rank {n : ℕ}
    (s : (nerve (Carrier P)) _⦋n⦌) :
    s ∈ (nerve (Carrier P)).nonDegenerate n ↔
      StrictMono (fun i => (rank (s.obj i)).val) := by
  constructor
  · intro hs
    cases n with
    | zero =>
      change StrictMono (fun i : Fin 1 => (rank (s.obj i)).val)
      exact Subsingleton.strictMono _
    | succ n =>
      have hadj :=
        (IdentityDeletion.nondegenerate_iff_adjacent_objects_distinct (C := Carrier P)
          (fun X a => endomorphism_eq_identity P X a) s).1 hs
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      exact rank_lt_of_ne P (s.map (homOfLE i.castSucc_le_succ)) (hadj i)
  · exact nondegenerate_of_strict_rank (C := Carrier P) (fun X => (rank X).val) s

private theorem dimension_lt_three {n : ℕ}
    (s : (nerve (Carrier P)) _⦋n⦌)
    (hs : s ∈ (nerve (Carrier P)).nonDegenerate n) : n < 3 := by
  have hm := (nondegenerate_iff_strict_rank P s).1 hs
  have hi : Function.Injective (fun i => rank (s.obj i)) := by
    intro i j h
    exact hm.injective (congrArg Fin.val h)
  have hc := Fintype.card_le_of_injective _ hi
  simp only [Fintype.card_fin] at hc
  omega

instance nonsingular : (nerve (Carrier P)).Nonsingular where
  mono := by
    intro n ⟨s, hs⟩
    have hinj : Function.Injective s.obj := by
      intro i j hij
      exact ((nondegenerate_iff_strict_rank P s).1 hs).injective
        (congrArg (fun X => (rank X).val) hij)
    simp only [CategoryTheory.NatTrans.mono_iff_mono_app,
      CategoryTheory.mono_iff_injective]
    intro ⟨⟨k⟩⟩ i j hij
    ext l : 1
    exact hinj (Functor.congr_obj hij l)

abbrev NonidentityLabels :=
  (E × Fin 2) ⊕ ((F × Fin 3) ⊕ (F × Fin 3))

-- The code retains the entire endpoint, side or corner occurrence label.
def totalCode {X Y : Object V E F} (a : P.Arrow X Y) :
    Object V E F ⊕ (NonidentityLabels (E := E) (F := F)) :=
  match a with
  | .identity X => .inl X
  | .endpoint e i => .inr (.inl (e, i))
  | .side f s => .inr (.inr (.inl (f, s)))
  | .corner f c => .inr (.inr (.inr (f, c)))

def flagSimplex (t : F × Fin 3 × Fin 2) :
    (nerve (Carrier P)).nonDegenerate 2 :=
  ⟨ComposableArrows.mk₂ (C := Carrier P) (Arrow.endpoint (P := P) (P.side t.1 t.2.1) t.2.2)
    (Arrow.side (P := P) t.1 t.2.1), by
      apply nondegenerate_of_strict_rank (C := Carrier P) (fun X => (rank X).val)
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      · change (0 : ℕ) < 1; decide
      · change (1 : ℕ) < 2; decide⟩

private theorem flagSimplex_injective : Function.Injective (flagSimplex P) := by
  rintro ⟨f, s, i⟩ ⟨g, t, j⟩ h
  have hv := congrArg Subtype.val h
  have ha := congrArg (fun x : ComposableArrows (Carrier P) 2 =>
    totalCode P (x.map' 0 1)) hv
  have hb := congrArg (fun x : ComposableArrows (Carrier P) 2 =>
    totalCode P (x.map' 1 2)) hv
  have he : (P.side f s, i) = (P.side g t, j) := by
    change Sum.inr (Sum.inl (P.side f s, i)) = Sum.inr (Sum.inl (P.side g t, j)) at ha
    exact Sum.inl.inj (Sum.inr.inj ha)
  have hf : (f, s) = (g, t) := by
    change Sum.inr (Sum.inr (Sum.inl (f, s))) = Sum.inr (Sum.inr (Sum.inl (g, t))) at hb
    exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj hb))
  have hi := congrArg Prod.snd he
  have hfg := congrArg Prod.fst hf
  have hst := congrArg Prod.snd hf
  cases hfg
  cases hst
  cases hi
  rfl

private theorem flagSimplex_surjective : Function.Surjective (flagSimplex P) := by
  intro x
  obtain ⟨X, Y, Z, a, b, h⟩ := ComposableArrows.mk₂_surjective x.val
  have hs := (nondegenerate_iff_strict_rank P x.val).1 x.property
  rw [h] at hs
  have h01 := hs (by decide : (0 : Fin 3) < 1)
  have h12 := hs (by decide : (1 : Fin 3) < 2)
  change (rank X).val < (rank Y).val at h01
  change (rank Y).val < (rank Z).val at h12
  change P.Arrow X Y at a
  change P.Arrow Y Z at b
  cases a with
  | identity X => exact False.elim ((lt_irrefl _) h01)
  | endpoint e i =>
    cases b with
    | identity Y => exact False.elim ((lt_irrefl _) h12)
    | side f s =>
      refine ⟨(f, s, i), ?_⟩
      apply Subtype.ext
      exact h.symm
  | side f s =>
    cases b
    exact False.elim ((lt_irrefl _) h12)
  | corner f c =>
    cases b
    exact False.elim ((lt_irrefl _) h12)

noncomputable def flagEquiv :
    (F × Fin 3 × Fin 2) ≃ (nerve (Carrier P)).nonDegenerate 2 :=
  Equiv.ofBijective (flagSimplex P) ⟨flagSimplex_injective P, flagSimplex_surjective P⟩

def objectEquiv : Object V E F ≃ V ⊕ (E ⊕ F) where
  toFun X := match X with
    | .vertex v => .inl v
    | .edge e => .inr (.inl e)
    | .face f => .inr (.inr f)
  invFun X := match X with
    | .inl v => .vertex v
    | .inr (.inl e) => .edge e
    | .inr (.inr f) => .face f
  left_inv X := by cases X <;> rfl
  right_inv X := by rcases X with v | X; rfl; rcases X with e | f <;> rfl

instance finiteObjects [Finite V] [Finite E] [Finite F] : Finite (Object V E F) :=
  Finite.of_equiv (V ⊕ (E ⊕ F)) objectEquiv.symm

instance finiteCarrier [Finite V] [Finite E] [Finite F] : Finite (Carrier P) := by
  change Finite (Object V E F)
  infer_instance

def zeroEquiv : Object V E F ≃ (nerve (Carrier P)).nonDegenerate 0 where
  toFun X := ⟨(nerveEquiv (C := Carrier P)).symm X, by simp <;> exact Set.mem_univ _⟩
  invFun x := (nerveEquiv (C := Carrier P)) x.val
  left_inv X := (nerveEquiv (C := Carrier P)).apply_symm_apply X
  right_inv x := Subtype.ext ((nerveEquiv (C := Carrier P)).symm_apply_apply x.val)

def oneSimplex (l : NonidentityLabels (E := E) (F := F)) :
    (nerve (Carrier P)).nonDegenerate 1 := by
  rcases l with ⟨e, i⟩ | l
  · refine ⟨ComposableArrows.mk₁ (C := Carrier P) (Arrow.endpoint (P := P) e i), ?_⟩
    apply nondegenerate_of_strict_rank (C := Carrier P) (fun X => (rank X).val)
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    fin_cases j
    change (0 : ℕ) < 1
    decide
  rcases l with ⟨f, s⟩ | ⟨f, c⟩
  · refine ⟨ComposableArrows.mk₁ (C := Carrier P) (Arrow.side (P := P) f s), ?_⟩
    apply nondegenerate_of_strict_rank (C := Carrier P) (fun X => (rank X).val)
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    fin_cases j
    change (1 : ℕ) < 2
    decide
  · refine ⟨ComposableArrows.mk₁ (C := Carrier P) (Arrow.corner (P := P) f c), ?_⟩
    apply nondegenerate_of_strict_rank (C := Carrier P) (fun X => (rank X).val)
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    fin_cases j
    change (0 : ℕ) < 2
    decide

private theorem oneSimplex_code (l : NonidentityLabels (E := E) (F := F)) :
    totalCode P (oneSimplex P l).val.hom = .inr l := by
  rcases l with ⟨e, i⟩ | l
  · rfl
  rcases l with ⟨f, s⟩ | ⟨f, c⟩ <;> rfl

private theorem oneSimplex_injective : Function.Injective (oneSimplex P) := by
  intro l m h
  have hh := congrArg (fun x : (nerve (Carrier P)).nonDegenerate 1 =>
    totalCode P x.val.hom) h
  rw [oneSimplex_code, oneSimplex_code] at hh
  exact Sum.inr.inj hh

private theorem oneSimplex_surjective : Function.Surjective (oneSimplex P) := by
  intro x
  obtain ⟨X, Y, a, h⟩ := ComposableArrows.mk₁_surjective x.val
  have hs := (nondegenerate_iff_strict_rank P x.val).1 x.property
  rw [h] at hs
  have h01 := hs (by decide : (0 : Fin 2) < 1)
  change (rank X).val < (rank Y).val at h01
  change P.Arrow X Y at a
  cases a with
  | identity X => exact False.elim ((lt_irrefl _) h01)
  | endpoint e i => exact ⟨.inl (e, i), Subtype.ext h.symm⟩
  | side f s => exact ⟨.inr (.inl (f, s)), Subtype.ext h.symm⟩
  | corner f c => exact ⟨.inr (.inr (f, c)), Subtype.ext h.symm⟩

noncomputable def oneEquiv :
    NonidentityLabels (E := E) (F := F) ≃
      (nerve (Carrier P)).nonDegenerate 1 :=
  Equiv.ofBijective (oneSimplex P) ⟨oneSimplex_injective P, oneSimplex_surjective P⟩

instance hasDimensionLT : (nerve (Carrier P)).HasDimensionLT 3 where
  degenerate_eq_top n hn := Set.eq_univ_of_forall (fun x => by
    by_contra hx
    have hnd := (SSet.mem_nonDegenerate_iff_notMem_degenerate (nerve (Carrier P)) x).2 hx
    have hlt := dimension_lt_three P x hnd
    omega)

instance finiteNerve [Finite V] [Finite E] [Finite F] :
    (nerve (Carrier P)).Finite := by
  apply SSet.finite_of_hasDimensionLT _ 3
  intro n hn
  interval_cases n
  · exact Finite.of_equiv (Object V E F) (zeroEquiv P)
  · exact Finite.of_equiv (NonidentityLabels (E := E) (F := F)) (oneEquiv P)
  · exact Finite.of_equiv (F × Fin 3 × Fin 2) (flagEquiv P)

private theorem nondegenerate_zero_card [Finite V] [Finite E] [Finite F] :
    Nat.card ((nerve (Carrier P)).nonDegenerate 0) =
      Nat.card V + Nat.card E + Nat.card F := by
  rw [← Nat.card_congr (zeroEquiv P), Nat.card_congr objectEquiv]
  simp [Nat.card_sum, add_assoc]

private theorem nondegenerate_one_card [Finite V] [Finite E] [Finite F] :
    Nat.card ((nerve (Carrier P)).nonDegenerate 1) =
      2 * Nat.card E + 6 * Nat.card F := by
  rw [← Nat.card_congr (oneEquiv P)]
  simp only [NonidentityLabels, Nat.card_sum, Nat.card_prod, Nat.card_fin]
  ring

private theorem nondegenerate_two_card [Finite V] [Finite E] [Finite F] :
    Nat.card ((nerve (Carrier P)).nonDegenerate 2) = 6 * Nat.card F := by
  rw [← Nat.card_congr (flagEquiv P)]
  simp only [Nat.card_prod, Nat.card_fin]
  ring

/-- Exact numbers of nondegenerate simplices, retaining all occurrence labels. -/
theorem simplex_counts [Finite V] [Finite E] [Finite F] :
    Nat.card ((nerve (Carrier P)).nonDegenerate 0) =
        Nat.card V + Nat.card E + Nat.card F ∧
      Nat.card ((nerve (Carrier P)).nonDegenerate 1) =
        2 * Nat.card E + 6 * Nat.card F ∧
      Nat.card ((nerve (Carrier P)).nonDegenerate 2) = 6 * Nat.card F :=
  ⟨nondegenerate_zero_card P, nondegenerate_one_card P, nondegenerate_two_card P⟩

end General

end Incidence
end D5.S3.Geometry.Gluing.OccurrenceIncidenceNerve
