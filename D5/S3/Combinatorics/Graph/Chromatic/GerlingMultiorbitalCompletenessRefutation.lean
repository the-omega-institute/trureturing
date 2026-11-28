/- GID: D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.claim; result=D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.result; claim=D5/S3/Combinatorics/Graph/Chromatic/GerlingMultiorbitalCompletenessRefutation.claim
   digest: Two faithful cyclic actions on six vertices share a multiorbital polynomial. -/

import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Gerling's completeness question for multiorbital bivariate chromatic polynomials. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option Elab.async false

namespace D5.S3.Combinatorics.Graph.Chromatic.GerlingMultiorbitalCompletenessRefutation

open Finset

abbrev Edge (V : Type) := V × V

variable {V : Type} [Fintype V] [DecidableEq V]

private def bad {x : ℕ} (y : ℕ) (f : V → Fin x) (e : Edge V) : Prop :=
  f e.1 = f e.2 ∧ (f e.1).val < y

private instance {x : ℕ} (y : ℕ) (f : V → Fin x) (e : Edge V) :
    Decidable (bad y f e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Palette {x : ℕ} (y : ℕ) (E : Finset (Edge V)) (f : V → Fin x) : Prop :=
  ∀ e ∈ E, ¬ bad y f e

private instance {x : ℕ} (y : ℕ) (E : Finset (Edge V)) (f : V → Fin x) :
    Decidable (Palette y E f) :=
  inferInstanceAs (Decidable (∀ e ∈ E, ¬ bad y f e))

def paletteCount (E : Finset (Edge V)) (x y : ℕ) : ℕ :=
  (univ.filter (Palette (x := x) y E)).card

private def intersectionCount (S : Finset (Edge V)) (x y : ℕ) : ℕ :=
  (univ.filter fun f : V → Fin x => ∀ e ∈ S, bad y f e).card

private theorem palette_inclusion_exclusion (E : Finset (Edge V)) (x y : ℕ) :
    (paletteCount E x y : ℤ) =
      ∑ S ∈ E.powerset, (-1 : ℤ) ^ S.card * (intersectionCount S x y : ℤ) := by
  have product_indicator (S : Finset (Edge V)) (p : Edge V → Prop) [DecidablePred p] :
      (∏ e ∈ S, if p e then (1 : ℤ) else 0) = if ∀ e ∈ S, p e then 1 else 0 := by
    by_cases h : ∀ e ∈ S, p e
    · rw [ite_eq_left h]
      exact prod_eq_one fun e he => ite_eq_left (h e he)
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨e, he, hn⟩ := h
      exact prod_eq_zero he (ite_eq_right hn)
  calc
    _ = ∑ f : V → Fin x, ∏ e ∈ E, (1 - if bad y f e then (1 : ℤ) else 0) := by
      rw [paletteCount, ← sum_boole]
      apply sum_congr rfl
      intro f _
      change (if ∀ e ∈ E, ¬ bad y f e then 1 else 0) = _
      rw [← product_indicator E (fun e => ¬ bad y f e)]
      apply prod_congr rfl
      intro e _
      by_cases h : bad y f e <;> simp [h]
    _ = ∑ f : V → Fin x, ∑ S ∈ E.powerset,
        (-1 : ℤ) ^ S.card * ∏ e ∈ S, if bad y f e then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro f _
      simp only [prod_sub, prod_const_one, mul_one]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro S _
      rw [← mul_sum]
      simp only [product_indicator, intersectionCount, sum_boole]

private def merge (a b : V) (v : V) : V := if v = b then a else v

private def representatives : List (Edge V) → V → V
  | [] => id
  | (u,v) :: es =>
    let r := representatives es
    fun w => merge (r u) (r v) (r w)

omit [Fintype V] in
private theorem representatives_idempotent (es : List (Edge V)) :
    ∀ v, representatives es (representatives es v) = representatives es v := by
  induction es with
  | nil => intro v; rfl
  | cons e es ih =>
    intro v
    change merge (representatives es e.1) (representatives es e.2)
      (representatives es (merge (representatives es e.1) (representatives es e.2)
        (representatives es v))) =
      merge (representatives es e.1) (representatives es e.2) (representatives es v)
    by_cases hv : representatives es v = representatives es e.2
    · simp only [merge, ite_eq_left hv, ih]
      split <;> rfl
    · simp [merge, hv, ih]

omit [Fintype V] in
private theorem collapse_iff {C : Type} (es : List (Edge V)) (f : V → C) :
    (∀ e ∈ es, f e.1 = f e.2) ↔ ∀ v, f (representatives es v) = f v := by
  induction es with
  | nil => simp [representatives]
  | cons e es ih =>
    simp only [List.mem_cons, forall_eq_or_imp, representatives]
    constructor
    · rintro ⟨he, hs⟩ v
      have h := ih.mp hs
      by_cases hv : representatives es v = representatives es e.2
      · rw [merge, ite_eq_left hv, h e.1, he, ← h e.2, ← hv, h v]
      · simp [merge, hv, h]
    · intro h
      have he : f e.1 = f e.2 := by
        rw [← h e.1, ← h e.2]
        by_cases hc : representatives es e.1 = representatives es e.2 <;> simp [merge, hc]
      refine ⟨he, ih.mpr fun v => ?_⟩
      calc
        f (representatives es v) = _ := (h (representatives es v)).symm
        _ = f (representatives ((e.1,e.2) :: es) v) := by
          simp only [representatives, representatives_idempotent]
        _ = f v := h v

private def edgeList {n : ℕ} (S : Finset (Edge (Fin n))) : List (Edge (Fin n)) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).map (i, ·)).filter (· ∈ S)

private theorem mem_edgeList {n : ℕ} {S : Finset (Edge (Fin n))} {e : Edge (Fin n)} :
    e ∈ edgeList S ↔ e ∈ S := by
  rcases e with ⟨u,v⟩
  simp [edgeList]

private def rep {n : ℕ} (S : Finset (Edge (Fin n))) : Fin n → Fin n :=
  representatives (edgeList S)

private def allReps {n : ℕ} (S : Finset (Edge (Fin n))) : Finset (Fin n) :=
  univ.image (rep S)

private def properReps {n : ℕ} (S : Finset (Edge (Fin n))) : Finset (Fin n) :=
  S.image (fun e => rep S e.1)

private theorem rep_eq {n : ℕ} {S : Finset (Edge (Fin n))} {e : Edge (Fin n)} (he : e ∈ S) :
    rep S e.1 = rep S e.2 :=
  (collapse_iff (edgeList S) (rep S)).mpr (representatives_idempotent _) e (mem_edgeList.mpr he)

private noncomputable def intersectionEquiv {n x y : ℕ} (S : Finset (Edge (Fin n))) :
    {f : Fin n → Fin x // ∀ e ∈ S, bad y f e} ≃
      (∀ r : allReps S, {c : Fin x // r.val ∈ properReps S → c.val < y}) where
  toFun f r := ⟨f.val r.val, by
    intro hr
    obtain ⟨e, he, hrep⟩ := mem_image.mp hr
    rw [← hrep]
    have hc := (collapse_iff (edgeList S) f.val).mp
      (fun d hd => (f.property d (mem_edgeList.mp hd)).1)
    exact (hc e.1).symm ▸ (f.property e he).2⟩
  invFun g := ⟨fun v => (g ⟨rep S v, mem_image_of_mem _ (mem_univ _)⟩).val, by
    intro e he
    refine ⟨?_, (g _).property (mem_image_of_mem _ he)⟩
    exact congrArg (fun a : allReps S => (g a).val) (Subtype.ext (rep_eq he))⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    exact (collapse_iff (edgeList S) f.val).mp
      (fun d hd => (f.property d (mem_edgeList.mp hd)).1) v
  right_inv g := by
    funext r
    apply Subtype.ext
    apply congrArg (fun a : allReps S => (g a).val)
    apply Subtype.ext
    obtain ⟨v, _, hv⟩ := mem_image.mp r.property
    change rep S r.val = r.val
    rw [← hv]
    exact representatives_idempotent _ v

private theorem intersection_card {n x y : ℕ} (S : Finset (Edge (Fin n))) (hxy : y ≤ x) :
    intersectionCount S x y =
      x ^ ((allReps S).card - (properReps S).card) * y ^ (properReps S).card := by
  classical
  have sub : properReps S ⊆ allReps S := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := mem_image.mp hr
    exact mem_image_of_mem _ (mem_univ _)
  have fiber (r : allReps S) :
      Fintype.card {c : Fin x // r.val ∈ properReps S → c.val < y} =
        if r.val ∈ properReps S then y else x := by
    by_cases hr : r.val ∈ properReps S
    · rw [ite_eq_left hr]
      let e : {c : Fin x // r.val ∈ properReps S → c.val < y} ≃ Fin y :=
        ⟨fun c => ⟨c.val.val, c.property hr⟩,
         fun c => ⟨Fin.castLE hxy c, fun _ => c.isLt⟩,
         fun _ => rfl, fun _ => rfl⟩
      simpa using Fintype.card_congr e
    · rw [ite_eq_right hr]
      let e : {c : Fin x // r.val ∈ properReps S → c.val < y} ≃ Fin x :=
        ⟨Subtype.val, fun c => ⟨c, fun h => (hr h).elim⟩, fun _ => rfl, fun _ => rfl⟩
      simpa using Fintype.card_congr e
  rw [intersectionCount, ← Fintype.card_subtype, Fintype.card_congr (intersectionEquiv S),
    Fintype.card_pi]
  simp_rw [fiber]
  rw [prod_ite, prod_const, prod_const, mul_comm]
  have h₁ : (univ.filter fun r : allReps S => r.val ∈ properReps S).card =
      (properReps S).card := by
    rw [← Fintype.card_subtype]
    let e : {r : allReps S // r.val ∈ properReps S} ≃ properReps S :=
      ⟨fun r => ⟨r.val.val, r.property⟩, fun r => ⟨⟨r.val, sub r.property⟩, r.property⟩,
        fun _ => rfl, fun _ => rfl⟩
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have h₂ := card_filter_add_card_filter_not (s := (univ : Finset (allReps S)))
    (fun r => r.val ∈ properReps S)
  rw [h₁]
  congr 1
  congr 1
  rw [h₁] at h₂
  simpa using (Nat.eq_sub_of_add_eq' h₂)

private def subsetExponent {n : ℕ} (S : Finset (Edge (Fin n))) : ℕ × ℕ :=
  ((allReps S).card - (properReps S).card, (properReps S).card)

private theorem palette_count_formula {n x y : ℕ} (E : Finset (Edge (Fin n))) (hxy : y ≤ x) :
    (paletteCount E x y : ℤ) = ∑ S ∈ E.powerset,
      (-1 : ℤ) ^ S.card * (x : ℤ) ^ (subsetExponent S).1 * (y : ℤ) ^ (subsetExponent S).2 := by
  rw [palette_inclusion_exclusion]
  apply sum_congr rfl
  intro S _
  rw [intersection_card S hxy]
  push_cast
  exact (mul_assoc _ _ _).symm

private def normalized {V : Type} [LinearOrder V] (u v : V) : Edge V :=
  (min u v, max u v)

/-- The undirected simple graph of an ordered edge list. -/
def graph {n : ℕ} (E : Finset (Edge (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => (u,v) ∈ E)

/-- A finite simple graph action, with each undirected edge listed once. -/
structure GraphAction (G : Type) [Group G] (n : ℕ) where
  edges : Finset (Edge (Fin n))
  ordered : ∀ e ∈ edges, e.1 < e.2
  action : G →* Equiv.Perm (Fin n)
  preserves : ∀ g u v, (graph edges).Adj (action g u) (action g v) ↔ (graph edges).Adj u v

/-- An isomorphism is a vertex bijection preserving adjacency and intertwining the action. -/
def ActionIso {G : Type} [Group G] {n m : ℕ}
    (A : GraphAction G n) (B : GraphAction G m) : Prop :=
  ∃ e : graph A.edges ≃g graph B.edges, ∀ g v, e (A.action g v) = B.action g (e v)

private def fixedCount {n : ℕ} (E : Finset (Edge (Fin n))) (g : Equiv.Perm (Fin n))
    (x y : ℕ) : ℕ :=
  (univ.filter fun f : Fin n → Fin x => Palette y E f ∧ ∀ v, f (g v) = f v).card

private def cycleSetoid {n : ℕ} (g : Equiv.Perm (Fin n)) : Setoid (Fin n) :=
  Relation.EqvGen.setoid (fun u v => g u = v)

private theorem constant_on_cycle {n : ℕ} {C : Type} {g : Equiv.Perm (Fin n)} {f : Fin n → C}
    (hf : ∀ v, f (g v) = f v) {u v : Fin n} (h : (cycleSetoid g).r u v) : f u = f v := by
  change Relation.EqvGen (fun a b => g a = b) u v at h
  induction h with
  | rel a _ h => exact (hf a).symm.trans (congrArg f h)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private def quotientEdges {n m : ℕ} (E : Finset (Edge (Fin n))) (q : Fin n → Fin m) :
    Finset (Edge (Fin m)) :=
  E.image (fun e => normalized (q e.1) (q e.2))

private theorem bad_normalized {m x y : ℕ} (f : Fin m → Fin x) (u v : Fin m) :
    bad y f (normalized u v) ↔ bad y f (u,v) := by
  rcases le_total u v with h | h
  · simp [normalized, min_eq_left h, max_eq_right h]
  · simp only [normalized, min_eq_right h, max_eq_left h, bad]
    constructor <;> rintro ⟨he, hc⟩ <;> exact ⟨he.symm, he ▸ hc⟩

private theorem palette_quotient_iff {n m x y : ℕ} (E : Finset (Edge (Fin n)))
    (q : Fin n → Fin m) (f : Fin m → Fin x) :
    Palette y (quotientEdges E q) f ↔ Palette y E (f ∘ q) := by
  constructor
  · intro h e he
    exact fun hb => h _ (mem_image_of_mem _ he) ((bad_normalized _ _ _).mpr hb)
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    exact fun hb => h d hd ((bad_normalized f (q d.1) (q d.2)).mp hb)

private theorem fixed_count_quotient {n m : ℕ} (E : Finset (Edge (Fin n)))
    (g : Equiv.Perm (Fin n)) (q : Fin n → Fin m) (hq : Function.Surjective q)
    (hfiber : ∀ u v, q u = q v ↔ (cycleSetoid g).r u v) (x y : ℕ) :
    fixedCount E g x y = paletteCount (quotientEdges E q) x y := by
  classical
  let s := Function.surjInv hq
  have hs := Function.rightInverse_surjInv hq
  have factor (f : Fin n → Fin x) (hf : ∀ v, f (g v) = f v) (v : Fin n) :
      f (s (q v)) = f v := by
    exact constant_on_cycle hf ((hfiber (s (q v)) v).mp (hs (q v)))
  let e : {f : Fin n → Fin x // Palette y E f ∧ ∀ v, f (g v) = f v} ≃
      {f : Fin m → Fin x // Palette y (quotientEdges E q) f} :=
    { toFun := fun f => ⟨f.val ∘ s, (palette_quotient_iff E q _).mpr (by
        have he : (f.val ∘ s) ∘ q = f.val := funext (factor f.val f.property.2)
        rw [he]
        exact f.property.1)⟩
      invFun := fun f => ⟨f.val ∘ q, (palette_quotient_iff E q _).mp f.property,
        fun v => congrArg f.val ((hfiber v (g v)).mpr (Relation.EqvGen.rel v (g v) rfl)).symm⟩
      left_inv := fun f => Subtype.ext (funext (factor f.val f.property.2))
      right_inv := fun f => Subtype.ext (funext (fun v => congrArg f.val (hs v))) }
  rw [fixedCount, paletteCount, ← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr e

/-- A polynomial in x with coefficients in the rational polynomial ring in y. -/
abbrev Bivariate := Polynomial (Polynomial ℚ)

private noncomputable def evaluate (x y : ℚ) : Bivariate →+* ℚ :=
  (Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (Polynomial.evalRingHom y))

private noncomputable def bivariate {n : ℕ} (E : Finset (Edge (Fin n))) : Bivariate :=
  ∑ S ∈ E.powerset, (-1 : Bivariate) ^ S.card * Polynomial.X ^ (subsetExponent S).1 *
    (Polynomial.C Polynomial.X) ^ (subsetExponent S).2

private theorem evaluate_bivariate {n x y : ℕ} (E : Finset (Edge (Fin n))) (h : y ≤ x) :
    evaluate x y (bivariate E) = (paletteCount E x y : ℚ) := by
  have sum_eq := congrArg (Int.castRingHom ℚ) (palette_count_formula E h)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at sum_eq
  rw [sum_eq]
  simp only [bivariate, map_sum, map_mul, map_pow, map_neg, map_one, evaluate,
    RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
    Polynomial.eval_map, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval_X]

private noncomputable def cycleLabels {n : ℕ} (g : Equiv.Perm (Fin n)) :
    Quotient (cycleSetoid g) ≃ Fin (Nat.card (Quotient (cycleSetoid g))) := by
  letI := Fintype.ofFinite (Quotient (cycleSetoid g))
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card).symm

private noncomputable def cyclePolynomial {n : ℕ} (E : Finset (Edge (Fin n)))
    (g : Equiv.Perm (Fin n)) : Bivariate :=
  bivariate (quotientEdges E (cycleLabels g ∘ Quotient.mk _))

private theorem evaluate_cyclePolynomial {n x y : ℕ} (E : Finset (Edge (Fin n)))
    (g : Equiv.Perm (Fin n)) (hxy : y ≤ x) :
    evaluate x y (cyclePolynomial E g) = (fixedCount E g x y : ℚ) := by
  have surj : Function.Surjective (cycleLabels g ∘ Quotient.mk _) :=
    (cycleLabels g).surjective.comp Quotient.mk_surjective
  have fibers (u v : Fin n) :
      (cycleLabels g ∘ Quotient.mk _) u = (cycleLabels g ∘ Quotient.mk _) v ↔
        (cycleSetoid g).r u v :=
    ⟨fun h => Quotient.exact ((cycleLabels g).injective h),
     fun h => congrArg (cycleLabels g) (Quotient.sound h)⟩
  rw [cyclePolynomial, evaluate_bivariate _ hxy, fixed_count_quotient E g _ surj fibers]

/-- Gerling's subgroup sum of bivariate chromatic polynomials on cyclic orbit quotients. -/
noncomputable def multiorbital {G : Type} [Group G] [Fintype G] {n : ℕ}
    (A : GraphAction G n) : Bivariate := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofInjective SetLike.coe SetLike.coe_injective
  exact ∑ H : Subgroup G, Polynomial.C (Polynomial.C ((Nat.card H : ℚ)⁻¹)) *
    ∑ g ∈ univ.filter (· ∈ H), cyclePolynomial A.edges (A.action g)

/-- The universal completeness assertion for faithful actions of the same finite group. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (n m : ℕ) (A : GraphAction G n) (B : GraphAction G m),
    Function.Injective A.action → Function.Injective B.action →
    multiorbital A = multiorbital B → ActionIso A B

private theorem evaluate_ext {p q : Bivariate}
    (h : ∀ x y : ℕ, y ≤ x → evaluate x y p = evaluate x y q) : p = q := by
  have fixedY (y : ℕ) :
      p.map (Polynomial.evalRingHom (y : ℚ)) = q.map (Polynomial.evalRingHom (y : ℚ)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (f := fun k : ℕ => ((k + y : ℕ) : ℚ))
      (fun a b hab => Nat.add_right_cancel (Nat.cast_injective hab))).mono ?_
    rintro _ ⟨k, rfl⟩
    exact h (k+y) y (by omega)
  apply Polynomial.ext
  intro i
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_range_of_injective (f := fun k : ℕ => (k : ℚ)) Nat.cast_injective).mono ?_
  rintro _ ⟨y, rfl⟩
  simpa only [Set.mem_setOf_eq, Polynomial.coeff_map, Polynomial.coe_evalRingHom] using
    congrArg (fun p : Polynomial ℚ => p.coeff i) (fixedY y)

private abbrev C2 := Multiplicative (ZMod 2)
private def generator : C2 := Multiplicative.ofAdd 1

private def swap : Equiv.Perm (Fin 6) := Equiv.swap 0 1

private def representation : C2 →* Equiv.Perm (Fin 6) where
  toFun g := if g = 1 then 1 else swap
  map_one' := by simp
  map_mul' := by
    intro a b
    fin_cases a <;> fin_cases b <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> decide

private theorem representation_faithful : Function.Injective representation := by
  intro a b h
  have h₀ := congrArg (fun e : Equiv.Perm (Fin 6) => e 0) h
  clear h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert h₀; decide)

private def edgesA : Finset (Edge (Fin 6)) :=
  {(0,3), (1,3), (0,4), (1,4), (2,3), (2,4), (2,5), (3,4)}

private def edgesB : Finset (Edge (Fin 6)) :=
  {(0,2), (1,2), (0,5), (1,5), (2,3), (2,4), (2,5), (3,4)}

private instance graphDecidable {n : ℕ} (E : Finset (Edge (Fin n))) :
    DecidableRel (graph E).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

private def actionA : GraphAction C2 6 :=
  ⟨edgesA, by decide, representation, by
    intro g u v
    fin_cases g <;> fin_cases u <;> fin_cases v <;> decide⟩

private def actionB : GraphAction C2 6 :=
  ⟨edgesB, by decide, representation, by
    intro g u v
    fin_cases g <;> fin_cases u <;> fin_cases v <;> decide⟩

private def orbitMap (v : Fin 6) : Fin 5 := ⟨v.val - 1, by omega⟩

private theorem orbit_surjective : Function.Surjective orbitMap := by
  intro i
  exact ⟨⟨i + 1, by omega⟩, Fin.ext (by simp [orbitMap])⟩

private theorem orbit_fibers : ∀ u v : Fin 6,
    orbitMap u = orbitMap v ↔ (cycleSetoid (representation generator)).r u v := by
  have fibers : ∀ u v : Fin 6,
      orbitMap u = orbitMap v ↔ u = v ∨ representation generator u = v := by decide
  intro u v
  constructor
  · intro h
    rcases (fibers u v).mp h with rfl | hstep
    · exact Relation.EqvGen.refl u
    · exact Relation.EqvGen.rel u v hstep
  · exact constant_on_cycle (fun w => ((fibers w (representation generator w)).mpr
      (Or.inr rfl)).symm)

private def quotientA : Finset (Edge (Fin 5)) :=
  {(0,2), (0,3), (1,2), (1,3), (1,4), (2,3)}

private def quotientB : Finset (Edge (Fin 5)) :=
  {(0,1), (0,4), (1,2), (1,3), (1,4), (2,3)}

private theorem actual_quotientA : quotientEdges edgesA orbitMap = quotientA := by decide
private theorem actual_quotientB : quotientEdges edgesB orbitMap = quotientB := by decide

private def exponentSupport {n : ℕ} (E : Finset (Edge (Fin n))) : Finset (ℕ × ℕ) :=
  E.powerset.image subsetExponent

private def coefficient {n : ℕ} (E : Finset (Edge (Fin n))) (k : ℕ × ℕ) : ℤ :=
  ∑ S ∈ E.powerset.filter (fun S => subsetExponent S = k), (-1 : ℤ) ^ S.card

private theorem palette_coefficients {n x y : ℕ} (E : Finset (Edge (Fin n))) (hxy : y ≤ x) :
    (paletteCount E x y : ℤ) =
      ∑ k ∈ exponentSupport E, coefficient E k * ((x : ℤ) ^ k.1 * (y : ℤ) ^ k.2) := by
  rw [palette_count_formula E hxy]
  simp only [coefficient, sum_mul]
  rw [← sum_fiberwise_of_maps_to (g := subsetExponent)
    (t := exponentSupport E) (fun S hS => mem_image_of_mem _ hS)]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro S hS
  rw [(mem_filter.mp hS).2, mul_assoc]

private def terms6 : Finset (ℕ × ℕ) :=
  {(6,0), (4,1), (3,1), (2,2), (2,1), (1,2), (1,1), (0,3), (0,2), (0,1)}

private def terms5 : Finset (ℕ × ℕ) :=
  {(5,0), (3,1), (2,1), (1,2), (1,1), (0,2), (0,1)}

private def coefficients6 (k : ℕ × ℕ) : ℤ :=
  match k with
  | (6,0) => 1
  | (4,1) => -8
  | (3,1) => 14
  | (2,2) => 11
  | (2,1) => -20
  | (1,2) => -16
  | (1,1) => 18
  | (0,3) => -2
  | (0,2) => 10
  | (0,1) => -8
  | _ => 0

private def coefficients5 (k : ℕ × ℕ) : ℤ :=
  match k with
  | (5,0) => 1
  | (3,1) => -6
  | (2,1) => 8
  | (1,2) => 5
  | (1,1) => -8
  | (0,2) => -4
  | (0,1) => 4
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the full eight-edge subset expansion in the kernel.
private theorem coefficientsA :
    exponentSupport edgesA = terms6 ∧ ∀ k ∈ terms6, coefficient edgesA k = coefficients6 k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the full eight-edge subset expansion in the kernel.
private theorem coefficientsB :
    exponentSupport edgesB = terms6 ∧ ∀ k ∈ terms6, coefficient edgesB k = coefficients6 k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the six-edge subset expansion in the kernel.
private theorem coefficientsQuotientA :
    exponentSupport quotientA = terms5 ∧
      ∀ k ∈ terms5, coefficient quotientA k = coefficients5 k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the six-edge subset expansion in the kernel.
private theorem coefficientsQuotientB :
    exponentSupport quotientB = terms5 ∧
      ∀ k ∈ terms5, coefficient quotientB k = coefficients5 k := by
  decide +kernel

private theorem palette_matches {n x y : ℕ} {E : Finset (Edge (Fin n))}
    {support : Finset (ℕ × ℕ)} {coeff : ℕ × ℕ → ℤ} (hxy : y ≤ x)
    (h : exponentSupport E = support ∧ ∀ k ∈ support, coefficient E k = coeff k) :
    (paletteCount E x y : ℤ) =
      ∑ k ∈ support, coeff k * ((x : ℤ) ^ k.1 * (y : ℤ) ^ k.2) := by
  rw [palette_coefficients E hxy, h.1]
  exact sum_congr rfl fun k hk => by rw [h.2 k hk]

private theorem fixed_count_one {n : ℕ} (E : Finset (Edge (Fin n))) (x y : ℕ) :
    fixedCount E 1 x y = paletteCount E x y := by
  unfold fixedCount paletteCount
  congr 1
  ext f
  simp

private theorem c2_elements : ∀ g : C2, g = 1 ∨ g = generator := by decide

private theorem multiorbital_c2 {n x y : ℕ} (A : GraphAction C2 n) (hxy : y ≤ x) :
    evaluate x y (multiorbital A) =
      (3 * (paletteCount A.edges x y : ℚ) + fixedCount A.edges (A.action generator) x y) / 2 := by
  classical
  unfold multiorbital
  simp only [map_sum, map_mul, evaluate_cyclePolynomial _ _ hxy]
  have eval_scalar (r : ℚ) : evaluate x y (Polynomial.C (Polynomial.C r)) = r := by
    simp [evaluate]
  simp only [eval_scalar]
  letI : Fintype (Subgroup C2) := Fintype.ofInjective SetLike.coe SetLike.coe_injective
  have subgroups : (univ : Finset (Subgroup C2)) = {⊥, ⊤} := by
    ext H
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    by_cases hg : generator ∈ H
    · right
      apply top_unique
      intro g _
      rcases c2_elements g with rfl | rfl
      · exact H.one_mem
      · exact hg
    · left
      apply bot_unique
      intro g hg'
      rcases c2_elements g with rfl | rfl
      · exact Subgroup.one_mem _
      · exact (hg hg').elim
  have distinctSubgroups : (⊥ : Subgroup C2) ≠ ⊤ := by
    intro he
    have hg : generator ∈ (⊤ : Subgroup C2) := Subgroup.mem_top _
    rw [← he] at hg
    exact (by decide : generator ≠ 1) (Subgroup.mem_bot.mp hg)
  have allElements : (univ : Finset C2) = {1, generator} := by
    ext g
    simp only [mem_univ, mem_insert, mem_singleton, true_iff]
    exact c2_elements g
  have distinctElements : (1 : C2) ≠ generator := by decide
  have filterTop : (univ : Finset C2).filter (· ∈ (⊤ : Subgroup C2)) = univ := by simp
  have filterBot : (univ : Finset C2).filter (· ∈ (⊥ : Subgroup C2)) = {1} := by ext g; simp
  rw [subgroups, sum_pair distinctSubgroups, filterBot, filterTop, sum_singleton,
    allElements, sum_pair distinctElements, map_one, fixed_count_one]
  have hc : Nat.card C2 = 2 := by rw [Nat.card_eq_fintype_card]; decide
  simp only [Subgroup.card_bot, Subgroup.card_top, hc, Nat.cast_one, Nat.cast_ofNat,
    inv_one, one_mul]
  ring

private theorem same_multiorbital (x y : ℕ) (hxy : y ≤ x) :
    evaluate x y (multiorbital actionA) = evaluate x y (multiorbital actionB) := by
  rw [multiorbital_c2 _ hxy, multiorbital_c2 _ hxy]
  change
    (3 * (paletteCount edgesA x y : ℚ) + fixedCount edgesA (representation generator) x y) / 2 =
    (3 * (paletteCount edgesB x y : ℚ) + fixedCount edgesB (representation generator) x y) / 2
  rw [fixed_count_quotient edgesA _ orbitMap orbit_surjective orbit_fibers,
    fixed_count_quotient edgesB _ orbitMap orbit_surjective orbit_fibers,
    actual_quotientA, actual_quotientB]
  have h₆ := (palette_matches hxy coefficientsA).trans (palette_matches hxy coefficientsB).symm
  have h₅ := (palette_matches hxy coefficientsQuotientA).trans
    (palette_matches hxy coefficientsQuotientB).symm
  exact_mod_cast congrArg₂ (fun a b : ℚ => (3*a+b)/2)
    (show (paletteCount edgesA x y : ℚ) = paletteCount edgesB x y by exact_mod_cast h₆)
    (show (paletteCount quotientA x y : ℚ) = paletteCount quotientB x y by exact_mod_cast h₅)

private theorem connectedA : (graph edgesA).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨2, ?_⟩
  intro v
  fin_cases v
  · exact (SimpleGraph.Adj.reachable (show (graph edgesA).Adj 2 3 by decide)).trans
      (SimpleGraph.Adj.reachable (show (graph edgesA).Adj 3 0 by decide))
  · exact (SimpleGraph.Adj.reachable (show (graph edgesA).Adj 2 3 by decide)).trans
      (SimpleGraph.Adj.reachable (show (graph edgesA).Adj 3 1 by decide))
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (show (graph edgesA).Adj 2 3 by decide)
  · exact SimpleGraph.Adj.reachable (show (graph edgesA).Adj 2 4 by decide)
  · exact SimpleGraph.Adj.reachable (show (graph edgesA).Adj 2 5 by decide)

private theorem connectedB : (graph edgesB).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨2, ?_⟩
  intro v
  fin_cases v
  · exact SimpleGraph.Adj.reachable (show (graph edgesB).Adj 2 0 by decide)
  · exact SimpleGraph.Adj.reachable (show (graph edgesB).Adj 2 1 by decide)
  · exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (show (graph edgesB).Adj 2 3 by decide)
  · exact SimpleGraph.Adj.reachable (show (graph edgesB).Adj 2 4 by decide)
  · exact SimpleGraph.Adj.reachable (show (graph edgesB).Adj 2 5 by decide)

private def degreeMultiset {n : ℕ} (E : Finset (Edge (Fin n))) : Multiset ℕ :=
  univ.val.map fun v : Fin n => ((univ : Finset (Fin n)).filter ((graph E).Adj v)).card

private theorem degree_obstruction : degreeMultiset edgesA ≠ degreeMultiset edgesB := by
  have ha : degreeMultiset edgesA = ([1, 2, 2, 3, 4, 4] : List ℕ) := by decide
  have hb : degreeMultiset edgesB = ([2, 2, 2, 2, 3, 5] : List ℕ) := by decide
  rw [ha, hb]
  decide

private theorem nonisomorphic : ¬ Nonempty (graph edgesA ≃g graph edgesB) := by
  rintro ⟨e⟩
  apply degree_obstruction
  let degree (E : Finset (Edge (Fin 6))) (v : Fin 6) :=
    ((univ : Finset (Fin 6)).filter ((graph E).Adj v)).card
  have h (v : Fin 6) : degree edgesA v = degree edgesB (e v) := by
    unfold degree
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (e.mapNeighborSet v)
  change univ.val.map (degree edgesA) = univ.val.map (degree edgesB)
  rw [show degree edgesA = degree edgesB ∘ e.toEquiv from funext h,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

private theorem counterexample :
    (graph actionA.edges).Connected ∧ (graph actionB.edges).Connected ∧
    Function.Injective actionA.action ∧ Function.Injective actionB.action ∧
    multiorbital actionA = multiorbital actionB ∧
    ¬ Nonempty (graph actionA.edges ≃g graph actionB.edges) :=
  ⟨connectedA, connectedB, representation_faithful, representation_faithful,
    evaluate_ext same_multiorbital, nonisomorphic⟩

/-- Equal multiorbital invariants do not force isomorphic graph actions. -/
theorem result : ¬ claim := by
  intro complete
  obtain ⟨_, _, faithfulA, faithfulB, equal, different⟩ := counterexample
  obtain ⟨e, _⟩ := complete C2 6 6 actionA actionB faithfulA faithfulB equal
  exact different ⟨e⟩

end D5.S3.Combinatorics.Graph.Chromatic.GerlingMultiorbitalCompletenessRefutation
