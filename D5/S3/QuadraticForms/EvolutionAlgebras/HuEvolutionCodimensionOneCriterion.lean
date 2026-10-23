/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionCodimensionOneCriterion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionCodimensionOneCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nilpotent cyclic shifted operator characterizes minimal perfectness. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Artinian.Module

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily (minimalPerfect)

/-- The quotient coordinate is zero; the remaining coordinates form the square-zero ideal. -/
def codimOneProduct (m : ℕ) (a : ℂ) (c : Coord m)
    (T : Matrix (Fin m) (Fin m) ℂ) (x y : Coord (m + 1)) : Coord (m + 1) :=
  Fin.cases (a * x 0 * y 0) (fun i =>
    x 0 * (T.mulVec (fun j => y j.succ)) i +
    y 0 * (T.mulVec (fun j => x j.succ)) i + c i * x 0 * y 0)

private abbrev tail {m : ℕ} (x : Coord (m + 1)) : Coord m := fun i => x i.succ

private def incl (m : ℕ) : Coord m →ₗ[ℂ] Coord (m + 1) where
  toFun z := Fin.cons 0 z
  map_add' := by intros; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' := by intros; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

private abbrev point {m : ℕ} (z : Coord m) : Coord (m + 1) := Fin.cons 1 z

private theorem decompose {m : ℕ} (x : Coord (m + 1)) (z : Coord m) :
    x = x 0 • point z + incl m (tail x - x 0 • z) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [incl, point]

private theorem product_head {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) (x y : Coord (m + 1)) :
    (μ x y) 0 = a * x 0 * y 0 := by simp [hl, codimOneProduct]

private theorem product_tail {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) (x y : Coord (m + 1)) :
    tail (μ x y) = x 0 • T.mulVec (tail y) + y 0 • T.mulVec (tail x) +
      (x 0 * y 0) • c := by
  ext i; simp [hl, codimOneProduct, tail]; ring

private theorem left_injective {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (ha : a ≠ 0) (hT : T.det ≠ 0)
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y)
    (q : Coord (m + 1)) (hq : q 0 = 1) : Function.Injective (μ q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hx0 : x 0 = 0 := by
    have h := congr_fun hx 0
    rw [product_head hl, hq, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  have ht : T.mulVec (tail x) = 0 := by
    have h := congr_arg tail hx
    change tail (μ q x) = 0 at h
    simpa [product_tail hl, hq, hx0] using h
  have hi : Function.Injective T.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hT))
  have hxw : tail x = 0 := hi (by simpa using ht)
  change x = 0
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx0
  · exact congr_fun hxw j

private theorem perfect_of_point {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (ha : a ≠ 0) (hT : T.det ≠ 0)
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y)
    (U : Submodule ℂ (Coord (m + 1))) (q : Coord (m + 1)) (hq : q ∈ U)
    (hq0 : q 0 = 1) (hc : ∀ x ∈ U, ∀ y ∈ U, μ x y ∈ U) : square μ U = U := by
  have hleft : ∀ x ∈ U, μ q x ∈ U := fun x hx => hc q hq x hx
  let L : U →ₗ[ℂ] U := (μ q).restrict hleft
  have hi : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    exact left_injective ha hT hl q hq0 (congr_arg Subtype.val h)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    exact hc x hx y hy
  · intro x hx
    obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hi ⟨x, hx⟩
    exact Submodule.subset_span ⟨q, hq, y, y.property, congr_arg Subtype.val hy⟩

private def shiftedSpace {m : ℕ} (S : Submodule ℂ (Coord m)) (z : Coord m) :
    Submodule ℂ (Coord (m + 1)) where
  carrier := {x | tail x - x 0 • z ∈ S}
  zero_mem' := by
    change tail 0 - (0 : ℂ) • z ∈ S
    simp only [zero_smul, sub_zero]
    exact S.zero_mem
  add_mem' := by
    intro x y hx hy
    change tail (x + y) - (x + y) 0 • z ∈ S
    convert S.add_mem hx hy using 1
    ext i; simp [tail]; ring
  smul_mem' := by
    intro b x hx
    change tail (b • x) - (b • x) 0 • z ∈ S
    convert S.smul_mem b hx using 1
    ext i; simp [tail]; ring

private theorem shifted_perfect {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (ha : a ≠ 0) (hT : T.det ≠ 0)
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y)
    (S : Submodule ℂ (Coord m)) (z : Coord m)
    (hS : ∀ w ∈ S, T.mulVec w ∈ S)
    (hz : c + (2 : ℂ) • (T.mulVec z - (a / 2) • z) ∈ S) :
    square μ (shiftedSpace S z) = shiftedSpace S z := by
  apply perfect_of_point ha hT hl _ (point z)
  · change z - (1 : ℂ) • z ∈ S; simp
  · simp [point]
  · intro x hx y hy
    change tail (μ x y) - (μ x y) 0 • z ∈ S
    have h := S.add_mem
      (S.add_mem (S.smul_mem (x 0) (hS _ hy)) (S.smul_mem (y 0) (hS _ hx)))
      (S.smul_mem (x 0 * y 0) hz)
    convert h using 1
    rw [product_head hl, product_tail hl]
    ext i
    simp [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

private theorem shifted_ne_bot {m : ℕ} (S : Submodule ℂ (Coord m)) (z : Coord m) :
    shiftedSpace S z ≠ ⊥ := by
  intro h
  have hp : point z ∈ shiftedSpace S z := by change z - (1 : ℂ) • z ∈ S; simp
  rw [h] at hp
  have hh := congr_fun (show point z = 0 from hp) 0
  simpa [point] using hh

private theorem shifted_eq_top_iff {m : ℕ} (S : Submodule ℂ (Coord m)) (z : Coord m) :
    shiftedSpace S z = ⊤ ↔ S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro w hw
    have hi : incl m w ∈ shiftedSpace S z := by rw [h]; trivial
    change w - (0 : ℂ) • z ∈ S at hi
    simpa using hi
  · intro h; subst S; apply top_unique; intro x hx; trivial

private theorem invariant_powers {m : ℕ} (N : Module.End ℂ (Coord m))
    (S : Submodule ℂ (Coord m)) (hS : ∀ x ∈ S, N x ∈ S) :
    ∀ k x, x ∈ S → (N ^ k) x ∈ S := by
  intro k; induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; simpa [pow_succ', Module.End.mul_apply] using hS _ (ih x hx)

/-- A nilpotent operator cannot be surjective modulo a proper invariant subspace. -/
private theorem nilpotent_lifting {m : ℕ} (N : Module.End ℂ (Coord m))
    (hn : N ^ m = 0) (S : Submodule ℂ (Coord m))
    (hS : ∀ x ∈ S, N x ∈ S)
    (hcover : ∀ v, ∃ s ∈ S, ∃ w, v = s + N w) : S = ⊤ := by
  have hiter : ∀ k v, ∃ s ∈ S, ∃ w, v = s + (N ^ k) w := by
    intro k; induction k with
    | zero => intro v; exact ⟨0, S.zero_mem, v, by simp⟩
    | succ k ih =>
      intro v
      obtain ⟨s, hs, w, hw⟩ := ih v
      obtain ⟨t, ht, r, hr⟩ := hcover w
      refine ⟨s + (N ^ k) t, S.add_mem hs (invariant_powers N S hS k t ht), r, ?_⟩
      rw [hw, hr, map_add, pow_succ, Module.End.mul_apply]
      abel
  apply top_unique
  intro v hv
  obtain ⟨s, hs, w, hw⟩ := hiter m v
  rw [show v = s by simpa [hn] using hw]
  exact hs

private theorem cyclic_perturbation {m : ℕ} (N : Module.End ℂ (Coord m))
    (hn : N ^ m = 0) (c z : Coord m)
    (hcyc : Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c)) = ⊤)
    (S : Submodule ℂ (Coord m)) (hS : ∀ x ∈ S, N x ∈ S)
    (hz : c + (2 : ℂ) • N z ∈ S) : S = ⊤ := by
  apply nilpotent_lifting N hn S hS
  have hct : c ∈ S ⊔ LinearMap.range N := by
    have he : c = (c + (2 : ℂ) • N z) + N (-(2 : ℂ) • z) := by simp
    rw [he]
    exact Submodule.add_mem_sup hz ⟨-(2 : ℂ) • z, rfl⟩
  have hstable : ∀ x ∈ S ⊔ LinearMap.range N, N x ∈ S ⊔ LinearMap.range N := by
    intro x hx
    exact Submodule.mem_sup_right ⟨x, rfl⟩
  have hsp : Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c)) ≤
      S ⊔ LinearMap.range N := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact invariant_powers N _ hstable j.val c hct
  rw [hcyc] at hsp
  intro v
  obtain ⟨s, hs, r, ⟨w, hw⟩, he⟩ := Submodule.mem_sup.mp (hsp Submodule.mem_top)
  exact ⟨s, hs, w, by rw [hw]; exact he.symm⟩

private theorem point_mul_incl {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) (z w : Coord m) :
    μ (point z) (incl m w) = incl m (T.mulVec w) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hl, codimOneProduct, point, incl]

private theorem point_square {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) (z : Coord m) :
    μ (point z) (point z) - a • point z =
      incl m (c + (2 : ℂ) • (T.mulVec z - (a / 2) • z)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [hl, codimOneProduct, point, incl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring

private theorem nonzero_perfect_point {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y)
    (U : Submodule ℂ (Coord (m + 1))) (hU : U ≠ ⊥) (hp : square μ U = U) :
    ∃ z : Coord m, point z ∈ U := by
  have hex : ∃ x ∈ U, x 0 ≠ 0 := by
    by_contra h
    push Not at h
    have hz : square μ U = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro v ⟨x, hx, y, hy, rfl⟩
      change μ x y = 0
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [hl, codimOneProduct, h x hx, h y hy]
    exact hU (hp.symm.trans hz)
  obtain ⟨x, hx, hx0⟩ := hex
  let q := (x 0)⁻¹ • x
  have hq : q ∈ U := U.smul_mem _ hx
  have hq0 : q 0 = 1 := by simp [q, hx0]
  refine ⟨tail q, ?_⟩
  have he : point (tail q) = q := by
    ext i; refine Fin.cases ?_ (fun j => ?_) i
    · simpa [point] using hq0.symm
    · simp [point, tail]
  rwa [he]

private theorem minimal_iff_shifted {m : ℕ} {a : ℂ} {c : Coord m}
    {T : Matrix (Fin m) (Fin m) ℂ} {μ : Product (m + 1)}
    (ha : a ≠ 0) (hT : T.det ≠ 0)
    (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) :
    minimalPerfect μ ↔ ∀ (S : Submodule ℂ (Coord m)) (z : Coord m),
      (∀ w ∈ S, T.mulVec w ∈ S) →
      c + (2 : ℂ) • (T.mulVec z - (a / 2) • z) ∈ S → S = ⊤ := by
  constructor
  · intro hm S z hs hz
    exact (shifted_eq_top_iff S z).mp
      (hm.2 _ (shifted_ne_bot S z) (shifted_perfect ha hT hl S z hs hz))
  · intro hm
    refine ⟨?_, ?_⟩
    · exact perfect_of_point ha hT hl ⊤ (point (0 : Coord m)) Submodule.mem_top
        (by simp [point]) (by intros; trivial)
    · intro U hU hp
      obtain ⟨z, hz⟩ := nonzero_perfect_point hl U hU hp
      have hmul : ∀ x ∈ U, ∀ y ∈ U, μ x y ∈ U := by
        intro x hx y hy
        rw [← hp]
        exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
      let S := U.comap (incl m)
      have hs : ∀ w ∈ S, T.mulVec w ∈ S := by
        intro w hw
        change incl m (T.mulVec w) ∈ U
        rw [← point_mul_incl hl z w]
        exact hmul _ hz _ hw
      have hpert : c + (2 : ℂ) • (T.mulVec z - (a / 2) • z) ∈ S := by
        change incl m _ ∈ U
        rw [← point_square hl z]
        exact U.sub_mem (hmul _ hz _ hz) (U.smul_mem a hz)
      have htop := hm S z hs hpert
      apply top_unique
      intro v hv
      rw [decompose v z]
      apply U.add_mem (U.smul_mem (v 0) hz)
      exact (show tail v - v 0 • z ∈ S by rw [htop]; trivial)

private theorem operator_cyclic_criterion {m : ℕ} (hm : 1 ≤ m)
    (N : Module.End ℂ (Coord m)) (c : Coord m) :
    (∀ (S : Submodule ℂ (Coord m)) (z : Coord m), (∀ w ∈ S, N w ∈ S) →
      c + (2 : ℂ) • N z ∈ S → S = ⊤) ↔
    N ^ m = 0 ∧ Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c)) = ⊤ := by
  constructor
  · intro h
    have hn : N ^ m = 0 := by
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp N.eventually_isCompl_ker_pow_range_pow
      let l := max k m
      have hlk : k ≤ l := le_max_left _ _
      have hlm : m ≤ l := le_max_right _ _
      have hlpos : 1 ≤ l := hm.trans hlm
      have hcomp := hk l hlk
      have hc : c ∈ LinearMap.ker (N ^ l) ⊔ LinearMap.range (N ^ l) := by
        rw [hcomp.sup_eq_top]; trivial
      obtain ⟨s, hs, r, ⟨w, hw⟩, he⟩ := Submodule.mem_sup.mp hc
      have hker : LinearMap.ker (N ^ l) = LinearMap.ker (N ^ m) := by
        simpa [Coord] using Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := N)
          (by simpa [Coord] using hlm)
      have hsN : ∀ v ∈ LinearMap.ker (N ^ l), N v ∈ LinearMap.ker (N ^ l) := by
        intro v hv
        change (N ^ l) (N v) = 0
        rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply,
          (show (N ^ l) v = 0 from hv), map_zero]
      let z := -(1/2 : ℂ) • (N ^ (l - 1)) w
      have hshift : c + (2 : ℂ) • N z = s := by
        have hr : N ((N ^ (l - 1)) w) = r := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hlpos]
          exact hw
        rw [show c = s + r from he.symm]
        simp only [z, map_smul, hr, smul_smul]
        norm_num
      have htop := h (LinearMap.ker (N ^ l)) z hsN (by rw [hshift]; exact hs)
      rw [hker] at htop
      exact LinearMap.ker_eq_top.mp htop
    refine ⟨hn, ?_⟩
    let S := Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c))
    have hs : ∀ w ∈ S, N w ∈ S := by
      intro w hw
      apply Submodule.span_induction (p := fun w _ => N w ∈ S) _ _ _ _ hw
      · rintro v ⟨j, rfl⟩
        by_cases hj : j.val + 1 < m
        · have he : N ((N ^ j.val) c) = (N ^ (j.val + 1)) c := by
            rw [pow_succ', Module.End.mul_apply]
          rw [he]
          exact Submodule.subset_span ⟨⟨j.val + 1, hj⟩, rfl⟩
        · have he : j.val + 1 = m := by omega
          have hz : N ((N ^ j.val) c) = 0 := by
            rw [← Module.End.mul_apply, ← pow_succ', he, hn]; rfl
          rw [hz]; exact S.zero_mem
      · simp
      · intro x y hx hy hxN hyN; simpa using S.add_mem hxN hyN
      · intro b x hx hxN; simpa using S.smul_mem b hxN
    have hc : c ∈ S := by
      simpa using (Submodule.subset_span
        (show (N ^ 0) c ∈ Set.range (fun j : Fin m => (N ^ j.val) c) from
          ⟨⟨0, by omega⟩, rfl⟩))
    exact h S 0 hs (by simpa using hc)
  · rintro ⟨hn, hc⟩ S z hs hz
    exact cyclic_perturbation N hn c z hc S hs hz

private theorem krylov_span_iff {m : ℕ} (N : Module.End ℂ (Coord m)) (c : Coord m) :
    Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c)) = ⊤ ↔
      Matrix.det (fun i j : Fin m => ((N ^ j.val) c) i) ≠ 0 := by
  let K : Matrix (Fin m) (Fin m) ℂ := fun i j => ((N ^ j.val) c) i
  have hr : LinearMap.range K.mulVecLin =
      Submodule.span ℂ (Set.range (fun j : Fin m => (N ^ j.val) c)) :=
    Matrix.range_mulVecLin K
  rw [← hr, LinearMap.range_eq_top]
  change Function.Surjective K.mulVec ↔ K.det ≠ 0
  rw [Matrix.mulVec_surjective_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- The complete criterion for every complex subspace and every permitted parameter. -/
theorem codimension_one_criterion (m : ℕ) (hm : 1 ≤ m) (a : ℂ) (ha : a ≠ 0)
    (c : Coord m) (T : Matrix (Fin m) (Fin m) ℂ) (hT : T.det ≠ 0)
    (μ : Product (m + 1)) (hl : ∀ x y, μ x y = codimOneProduct m a c T x y) :
    minimalPerfect μ ↔
      let N := T - (a / 2) • (1 : Matrix (Fin m) (Fin m) ℂ)
      N ^ m = 0 ∧ Matrix.det (fun i j : Fin m => ((N ^ j.val).mulVec c) i) ≠ 0 := by
  let N : Matrix (Fin m) (Fin m) ℂ := T - (a / 2) • 1
  let L : Module.End ℂ (Coord m) := Matrix.toLin' N
  have hL : ∀ w, L w = T.mulVec w - (a / 2) • w := by
    intro w; simp [L, N, Matrix.toLin'_apply]
  have hinv : ∀ S : Submodule ℂ (Coord m),
      (∀ w ∈ S, T.mulVec w ∈ S) ↔ (∀ w ∈ S, L w ∈ S) := by
    intro S
    constructor
    · intro h w hw; rw [hL]; exact S.sub_mem (h w hw) (S.smul_mem _ hw)
    · intro h w hw
      have he : T.mulVec w = L w + (a / 2) • w := by rw [hL]; abel
      rw [he]; exact S.add_mem (h w hw) (S.smul_mem _ hw)
  have hmin : minimalPerfect μ ↔
      ∀ (S : Submodule ℂ (Coord m)) (z : Coord m), (∀ w ∈ S, L w ∈ S) →
        c + (2 : ℂ) • L z ∈ S → S = ⊤ := by
    rw [minimal_iff_shifted ha hT hl]
    simp_rw [hinv, ← hL]
  rw [hmin, operator_cyclic_criterion hm L c, krylov_span_iff]
  have hp : L ^ m = 0 ↔ N ^ m = 0 := by
    rw [← Matrix.toLin'_pow]
    constructor
    · intro h
      apply Matrix.toLin'.injective
      simpa using h
    · intro h; simp [h]
  rw [hp]
  change (N ^ m = 0 ∧ Matrix.det (fun i j : Fin m => ((L ^ j.val) c) i) ≠ 0) ↔
    (N ^ m = 0 ∧ Matrix.det (fun i j : Fin m => ((N ^ j.val).mulVec c) i) ≠ 0)
  simp only [L, ← Matrix.toLin'_pow, Matrix.toLin'_apply]

#print axioms codimension_one_criterion

end D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCodimensionOneCriterion
