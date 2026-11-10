/- GID: D5/S3/FiniteGroups/GroupAlgebra/FiniteFieldTranslationProjectivityBoundary
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/FiniteFieldTranslationProjectivityBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Extension, mathlib/module/Mathlib.RingTheory.Polynomial.DegreeLT, mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Finite-coefficient polynomial translation gives dimension p*m, actual cyclic projectivity and an ambient norm obstruction, including proper additive subspaces and characteristic two. -/

import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic

/-!
Let K be any finite field of characteristic p, m > 0, r >= 2 and
r <= finrank_Fp(K)*m. Use the existing FiniteField.Extension K p m, called L.
A chosen finite Fp-basis constructs an injective coordinate map theta into L.
The carrier V = Polynomial.degreeLT L p has K-dimension p*m. Translations
f(X) |-> f(X + theta(g.toAdd)) define its actual K-representation.

On each actual nontrivial cyclic subgroup H, exponent p implies card H = p.
Lagrange interpolation on its p distinct theta-nodes gives V equivalent to
H -> L over L, then over K. The orientation is right translation h |-> h*g.
A one-coordinate projector has conjugation trace one. The accepted public
trace criterion proves projectivity, transported through an actual K[H]-linear
equivalence. The trivial subgroup is handled by the public norm criterion.
As a K[Cp]-module the function module has regular rank [L:K] = m, not f*m.

The full-group norm proof never identifies theta(E) with all of L. Summing
translations in one nonzero coordinate direction gives a polynomial of
degree < p whose values at p distinct nodes are all the same; hence it is
constant. The remaining r-1 coordinates repeat this constant p^(r-1) times,
which is zero in characteristic p. This proves the norm identity on every
additive subspace of rank at least two. Invariant polynomial 1 contradicts
the public necessary norm-surjectivity criterion if the module is projective.
In particular p=2,r=2,f=1,m=2 is retained despite dimension equalling |E|.

The ordinary mathematical input is the supplied Pro reasoning, with the
regular-rank typo corrected. The public trace owner's attribution is
Aljadeff--Ginosar (1996), Lemma 4, and Aljadeff--Kassel,
https://arxiv.org/abs/math/0012038. Mathlib owns finite extensions, Taylor
equivalences, finite bases, interpolation and polynomial determination.
No literature novelty, new lower bound or formal sharpness result is claimed.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldTranslationProjectivityBoundary

open scoped MonoidAlgebra Polynomial
open D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
open D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace

universe uK uG uW

-- Direct use of the public trace criterion; no private free-cover proof is copied.
private theorem function_projective_by_trace
    {k : Type uK} {G : Type uG} {W : Type uW}
    [Field k] [Group G] [Finite G] [AddCommGroup W] [Module k W] :
    Module.Projective k[G] (rightTranslate (R := k) (P := G) (W := W)).asModule := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let τ := rightTranslate (R := k) (P := G) (W := W)
  let t : Module.End k (G → W) :=
    { toFun := fun f h => if h = 1 then f 1 else 0
      map_add' := by
        intro f a
        funext h
        by_cases hh : h = 1 <;> simp [hh]
      map_smul' := by
        intro c f
        funext h
        by_cases hh : h = 1 <;> simp [hh] }
  apply (projective_iff_projective_and_conjugation_trace_one τ).mpr
  refine ⟨inferInstance, t, ?_⟩
  apply LinearMap.ext
  intro f
  funext h
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
    Finset.sum_apply]
  change (∑ g : G, if h * g = 1 then f (1 * g⁻¹) else 0) = f h
  rw [Finset.sum_eq_single h⁻¹]
  · simp
  · intro g _ hne
    have hmul : h * g ≠ 1 := by
      intro he
      apply hne
      calc
        g = h⁻¹ * (h * g) := by simp
        _ = h⁻¹ := by rw [he, mul_one]
    simp [hmul]
  · simp

section Construction

variable (K : Type uK) [Field K] [Finite K]
variable (p m r : ℕ) [Fact p.Prime] [CharP K p] [NeZero m]

-- ZMod.algebra is deliberately not a global Mathlib instance. This local
-- instance inserts the canonical prime-field embedding, adding no premise.
private abbrev primeFieldAlgebra : Algebra (ZMod p) K := ZMod.algebra K p
attribute [local instance] primeFieldAlgebra

local notation "F" => ZMod p
local notation "L" => FiniteField.Extension K p m
local notation "E" => Multiplicative (Fin r → ZMod p)
local notation "V" => Polynomial.degreeLT (FiniteField.Extension K p m) p

private def field_coordinates (hcap : r ≤ Module.finrank F K * m) :
    { θ : (Fin r → F) →ₗ[F] L // Function.Injective θ } := by
  classical
  let b := Module.finBasis F L
  have hc : r ≤ Module.finrank F L := by
    rw [FiniteField.finrank_zmod_extension K p m]
    exact hcap
  let ι : Fin r → Fin (Module.finrank F L) := Fin.castLE hc
  let θ : (Fin r → F) →ₗ[F] L :=
    (Pi.basisFun F (Fin r)).constr F (fun i => b (ι i))
  refine ⟨θ, ?_⟩
  exact (Pi.basisFun F (Fin r)).injective_constr_of_linearIndependent
    (b.linearIndependent.comp ι (Fin.castLE_injective hc))

private theorem elementary_pow (g : E) : g ^ p = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  exact ZModModule.char_nsmul_eq_zero p g.toAdd

private theorem elementary_isPGroup : IsPGroup p E := by
  intro g
  exact ⟨1, by simpa only [pow_one] using elementary_pow p r g⟩

-- V and L live in Type, while the arbitrary coefficient field K lives in
-- Type uK. Only scalar restriction is used; no universe equality is imposed.
private def translation (θ : (Fin r → F) →ₗ[F] L) : Representation K E V where
  toFun g :=
    (Polynomial.taylorLinearEquiv (θ g.toAdd) p).toLinearMap.restrictScalars K
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change Polynomial.taylor (θ (1 : E).toAdd) (f : L[X]) = (f : L[X])
    simp
  map_mul' g a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change Polynomial.taylor (θ (g * a).toAdd) (f : L[X]) =
      Polynomial.taylor (θ g.toAdd) (Polynomial.taylor (θ a.toAdd) (f : L[X]))
    simp only [toAdd_mul, map_add, Polynomial.taylor_taylor]

private theorem translation_eval (θ : (Fin r → F) →ₗ[F] L)
    (g : E) (f : V) (x : L) :
    ((translation K p m r θ g f : V) : L[X]).eval x =
      (f : L[X]).eval (x + θ g.toAdd) := by
  change (Polynomial.taylor (θ g.toAdd) (f : L[X])).eval x = _
  exact Polynomial.taylor_eval _ _ _

private theorem carrier_finrank : Module.finrank K V = p * m := by
  calc
    Module.finrank K V = Module.finrank K L * Module.finrank L V :=
      (Module.finrank_mul_finrank K L V).symm
    _ = m * p := by
      rw [FiniteField.finrank_extension K p m,
        (Polynomial.degreeLTEquiv L p).finrank_eq, Module.finrank_pi, Fintype.card_fin]
    _ = p * m := Nat.mul_comm _ _

private theorem cyclic_card (H : Subgroup E) [Fintype H] [IsCyclic H] [Nontrivial H] :
    Fintype.card H = p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hpow : g ^ p = 1 := by
    apply Subtype.ext
    change (g : E) ^ p = 1
    exact elementary_pow p r (g : E)
  have hdvd : Nat.card H ∣ p := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hne : Nat.card H ≠ 1 := ne_of_gt Finite.one_lt_card
  have hc : Nat.card H = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hne
  simpa only [Nat.card_eq_fintype_card] using hc

private def subgroup_evaluation (θ : (Fin r → F) →ₗ[F] L) (H : Subgroup E) :
    V →ₗ[L] (H → L) where
  toFun f h := (f : L[X]).eval (θ (h : E).toAdd)
  map_add' f a := by
    funext h
    exact Polynomial.eval_add
  map_smul' c f := by
    funext h
    simp

omit [Finite K] [NeZero m] in
private theorem subgroup_evaluation_bijective (θ : (Fin r → F) →ₗ[F] L)
    (hθ : Function.Injective θ) (H : Subgroup E) [Fintype H]
    (hc : Fintype.card H = p) :
    Function.Bijective (subgroup_evaluation K p m r θ H) := by
  classical
  let v : H → L := fun h => θ (h : E).toAdd
  have hv : Function.Injective v := by
    intro h a he
    apply Subtype.ext
    apply Multiplicative.ext
    exact hθ he
  constructor
  · intro f a he
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset H) hv.injOn
    · simpa only [Finset.card_univ, hc] using Polynomial.mem_degreeLT.mp f.property
    · simpa only [Finset.card_univ, hc] using Polynomial.mem_degreeLT.mp a.property
    · intro h _
      exact congrFun he h
  · intro a
    let f : L[X] := Lagrange.interpolate Finset.univ v a
    have hf : f ∈ Polynomial.degreeLT L p := by
      apply Polynomial.mem_degreeLT.mpr
      simpa only [Finset.card_univ, hc] using
        Lagrange.degree_interpolate_lt (s := Finset.univ) (v := v) a hv.injOn
    refine ⟨⟨f, hf⟩, ?_⟩
    funext h
    exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := v)
      a hv.injOn (Finset.mem_univ h)

private theorem cyclic_restriction_projective (θ : (Fin r → F) →ₗ[F] L)
    (hθ : Function.Injective θ) (H : Subgroup E) (hH : IsCyclic H) :
    Module.Projective K[H] (Representation.asModule ((translation K p m r θ).comp H.subtype)) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let : IsCyclic H := hH
  let σ : Representation K H V := (translation K p m r θ).comp H.subtype
  rcases subsingleton_or_nontrivial H with htr | hn
  · let : Subsingleton H := htr
    have hP : IsPGroup p H := IsPGroup.of_subsingleton p H
    apply (projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) (by simp) hP σ).mpr
    refine ⟨inferInstance, ?_⟩
    intro w
    refine ⟨(w : V), ?_⟩
    have hw (g : H) : σ g (w : V) = (w : V) :=
      (Representation.mem_invariants σ (w : V)).mp w.property g
    have hcard : Fintype.card H = 1 := by
      simpa only [Nat.card_eq_fintype_card] using Nat.card_of_subsingleton (1 : H)
    simp only [Representation.norm, LinearMap.sum_apply, hw]
    simp [hcard]
  · let : Nontrivial H := hn
    have hc : Fintype.card H = p := cyclic_card p r H
    let eL : V ≃ₗ[L] (H → L) :=
      LinearEquiv.ofBijective (subgroup_evaluation K p m r θ H)
        (subgroup_evaluation_bijective K p m r θ hθ H hc)
    let e : V ≃ₗ[K] (H → L) := eL.restrictScalars K
    let τ := rightTranslate (R := K) (P := H) (W := L)
    have he (g : H) (f : V) : e (σ g f) = τ g (e f) := by
      funext h
      change ((translation K p m r θ (g : E) f : V) : L[X]).eval
          (θ (h : E).toAdd) =
        (f : L[X]).eval (θ (((h : E) * (g : E)).toAdd))
      rw [translation_eval]
      simp only [toAdd_mul, map_add]
    let T : Representation.IntertwiningMap σ τ :=
      { toLinearMap := e.toLinearMap
        isIntertwining' g := by
          apply LinearMap.ext
          intro f
          exact he g f }
    let TA := Representation.IntertwiningMap.equivLinearMapAsModule σ τ T
    have hTA : Function.Bijective TA := by
      change Function.Bijective e
      exact e.bijective
    let EA := LinearEquiv.ofBijective TA hTA
    let : Module.Projective K[H] τ.asModule := function_projective_by_trace
    exact Module.Projective.of_equiv' EA.symm

-- The following cancellation uses just an injective coordinate map into L.
-- It does not require a basis of theta(E) to be a basis of all of L.
private def line_norm (a : L) (f : V) : V :=
  ∑ t : F, Polynomial.taylorLinearEquiv (t • a) p f

omit [Finite K] [NeZero m] in
private theorem line_norm_eval (a : L) (f : V) (x : L) :
    ((line_norm K p m a f : V) : L[X]).eval x =
      ∑ t : F, (f : L[X]).eval (x + t • a) := by
  classical
  let ev : V →ₗ[L] L := (Polynomial.leval x).comp (Polynomial.degreeLT L p).subtype
  change ev (∑ t : F, Polynomial.taylorLinearEquiv (t • a) p f) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  change (Polynomial.taylor (t • a) (f : L[X])).eval x = _
  exact Polynomial.taylor_eval _ _ _

private theorem line_norm_constant (a : L) (ha : a ≠ 0) (f : V) :
    ((line_norm K p m a f : V) : L[X]) =
      Polynomial.C (((line_norm K p m a f : V) : L[X]).eval 0) := by
  classical
  have hv : Function.Injective (fun t : F => t • a) := smul_left_injective F ha
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset F) hv.injOn
  · simpa only [Finset.card_univ, ZMod.card] using
      Polynomial.mem_degreeLT.mp (line_norm K p m a f).property
  · have hpos : (0 : WithBot ℕ) < (p : WithBot ℕ) :=
      WithBot.coe_lt_coe.mpr (Fact.out : p.Prime).pos
    simpa only [Finset.card_univ, ZMod.card] using Polynomial.degree_C_le.trans_lt hpos
  · intro u _
    rw [Polynomial.eval_C, line_norm_eval, line_norm_eval]
    simp only [zero_add]
    let shift : F ≃ F :=
      { toFun := fun t => u + t
        invFun := fun t => t - u
        left_inv := by intro t; simp
        right_inv := by intro t; simp }
    calc
      (∑ t : F, (f : L[X]).eval (u • a + t • a)) =
          ∑ t : F, (f : L[X]).eval ((u + t) • a) := by simp only [add_smul]
      _ = ∑ t : F, (f : L[X]).eval (t • a) := by
        refine Fintype.sum_bijective shift shift.bijective _ _ ?_
        intro t
        rfl

private theorem line_sum_independent (a : L) (ha : a ≠ 0) (f : V) (x : L) :
    (∑ t : F, (f : L[X]).eval (x + t • a)) =
      ∑ t : F, (f : L[X]).eval (t • a) := by
  calc
    (∑ t : F, (f : L[X]).eval (x + t • a)) =
        ((line_norm K p m a f : V) : L[X]).eval x := (line_norm_eval K p m a f x).symm
    _ = ((line_norm K p m a f : V) : L[X]).eval 0 := by
      rw [line_norm_constant K p m a ha f]
      simp only [Polynomial.eval_C]
    _ = ∑ t : F, (f : L[X]).eval (t • a) := by
      rw [line_norm_eval]
      simp only [zero_add]

private theorem coordinate_sum_zero (θ : (Fin r → F) →ₗ[F] L)
    (hθ : Function.Injective θ) (hr : 2 ≤ r) (f : V) (x : L) :
    (∑ z : Fin r → F, (f : L[X]).eval (x + θ z)) = 0 := by
  classical
  cases r with
  | zero => omega
  | succ n =>
    let b₀ : Fin (n + 1) → F := Fin.cons 1 0
    let a : L := θ b₀
    have hb₀ : b₀ ≠ 0 := by
      intro h
      have he := congrFun h 0
      simp [b₀] at he
    have ha : a ≠ 0 := by
      intro h
      apply hb₀
      apply hθ
      exact h.trans θ.map_zero.symm
    have hdecomp (t : F) (z : Fin n → F) :
        θ (Fin.cons t z) = t • a + θ (Fin.cons 0 z) := by
      calc
        θ (Fin.cons t z) = θ (t • b₀ + Fin.cons 0 z) := by
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp [b₀, smul_eq_mul]
        _ = t • a + θ (Fin.cons 0 z) := by rw [map_add, map_smul]
    let split : (F × (Fin n → F)) ≃ (Fin (n + 1) → F) :=
      Fin.consEquiv (fun _ => F)
    calc
      (∑ z : Fin (n + 1) → F, (f : L[X]).eval (x + θ z)) =
          ∑ tz : F × (Fin n → F),
            (f : L[X]).eval (x + θ (Fin.cons tz.1 tz.2)) := by
        symm
        refine Fintype.sum_bijective split split.bijective _ _ ?_
        intro tz
        rfl
      _ = ∑ t : F, ∑ z : Fin n → F, (f : L[X]).eval (x + θ (Fin.cons t z)) :=
        Fintype.sum_prod_type _
      _ = ∑ z : Fin n → F, ∑ t : F, (f : L[X]).eval (x + θ (Fin.cons t z)) :=
        Finset.sum_comm
      _ = ∑ z : Fin n → F, ∑ t : F,
          (f : L[X]).eval ((x + θ (Fin.cons 0 z)) + t • a) := by
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro t _
        rw [hdecomp]
        congr 1
        abel
      _ = ∑ _z : Fin n → F, ∑ t : F, (f : L[X]).eval (t • a) := by
        apply Finset.sum_congr rfl
        intro z _
        exact line_sum_independent K p m a ha f (x + θ (Fin.cons 0 z))
      _ = 0 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi_const, ZMod.card]
        cases n with
        | zero => omega
        | succ k =>
          rw [pow_succ, mul_nsmul, ZModModule.char_nsmul_eq_zero p]

private theorem translation_norm_zero (θ : (Fin r → F) →ₗ[F] L)
    (hθ : Function.Injective θ) (hr : 2 ≤ r) (f : V) :
    (translation K p m r θ).norm f = 0 := by
  classical
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpc : p ≤ Fintype.card (Fin r → F) := by
    rw [Fintype.card_pi_const, ZMod.card]
    calc
      p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ r := pow_le_pow_right' hp (by omega)
  apply Subtype.ext
  change (((translation K p m r θ).norm f : V) : L[X]) = 0
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
    (Finset.univ : Finset (Fin r → F)) hθ.injOn
  · have hd := Polynomial.mem_degreeLT.mp ((translation K p m r θ).norm f).property
    have hle : (p : WithBot ℕ) ≤ (Fintype.card (Fin r → F) : WithBot ℕ) :=
      WithBot.coe_le_coe.mpr hpc
    simpa only [Finset.card_univ] using hd.trans_le hle
  · intro z _
    let ev : V →ₗ[L] L :=
      (Polynomial.leval (θ z)).comp (Polynomial.degreeLT L p).subtype
    change ev ((translation K p m r θ).norm f) = 0
    rw [Representation.norm, LinearMap.sum_apply, map_sum]
    change (∑ g : E, ((translation K p m r θ g f : V) : L[X]).eval (θ z)) = 0
    simp_rw [translation_eval]
    calc
      (∑ g : E, (f : L[X]).eval (θ z + θ g.toAdd)) =
          ∑ y : Fin r → F, (f : L[X]).eval (θ z + θ y) := by
        let e : E ≃ (Fin r → F) := Multiplicative.toAdd
        refine Fintype.sum_bijective e e.bijective _ _ ?_
        intro g
        rfl
      _ = 0 := coordinate_sum_zero K p m r θ hθ hr f (θ z)

private theorem translation_not_projective (θ : (Fin r → F) →ₗ[F] L)
    (hθ : Function.Injective θ) (hr : 2 ≤ r) :
    ¬ Module.Projective K[E] (translation K p m r θ).asModule := by
  classical
  intro hproj
  let ρ := translation K p m r θ
  have hdegree : (1 : L[X]).degree < (p : WithBot ℕ) := by
    rw [Polynomial.degree_one]
    exact WithBot.coe_lt_coe.mpr (Fact.out : p.Prime).pos
  let c : V := ⟨1, Polynomial.mem_degreeLT.mpr hdegree⟩
  have hfixed : c ∈ ρ.invariants := by
    apply (Representation.mem_invariants ρ c).mpr
    intro g
    apply Subtype.ext
    change Polynomial.taylor (θ g.toAdd) (1 : L[X]) = 1
    simp
  let w : ρ.invariants := ⟨c, hfixed⟩
  have hsurj := ((projective_iff_projective_invariants_and_norm_surjective
    p 1 (by decide) (by simp) (elementary_isPGroup p r) ρ).mp hproj).2
  obtain ⟨f, hf⟩ := hsurj w
  have hc : c = 0 := hf.symm.trans (translation_norm_zero K p m r θ hθ hr f)
  have hc' : (1 : L[X]) = 0 := congrArg (fun a : V => (a : L[X])) hc
  exact one_ne_zero hc'

/-- The finite-coefficient translation family, including proper Fp-subspaces
and characteristic two. The coordinate injection is constructed, and every
restriction is through the actual subgroup's inclusion. The carrier has exact
K-dimension p*m. This endpoint proves the upper family and nonprojectivity;
it does not assert a lower bound or a sharp-minimum theorem. -/
theorem finite_field_translation_projectivity_boundary
    (hr : 2 ≤ r) (hcap : r ≤ Module.finrank F K * m) :
    ∃ θ : (Fin r → F) →ₗ[F] L, Function.Injective θ ∧
      ∃ ρ : Representation K E V,
        Module.finrank K V = p * m ∧
        (∀ (g : E) (f : V), (ρ g f : L[X]) =
          Polynomial.taylor (θ g.toAdd) (f : L[X])) ∧
        (∀ H : Subgroup E, IsCyclic H →
          Module.Projective K[H] (Representation.asModule (ρ.comp H.subtype))) ∧
        ¬ Module.Projective K[E] ρ.asModule := by
  classical
  let coords := field_coordinates K p m r hcap
  let θ := coords.val
  have hθ : Function.Injective θ := coords.property
  refine ⟨θ, hθ, translation K p m r θ, carrier_finrank K p m,
    ?_, cyclic_restriction_projective K p m r θ hθ,
    translation_not_projective K p m r θ hθ hr⟩
  intro g f
  rfl

end Construction

end D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldTranslationProjectivityBoundary
