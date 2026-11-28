/- GID: D5/S3/Geometry/Poisson/PaisPoissonNonisomorphism
   generality: G
   mirror-B: D5/B/S3/Geometry/Poisson/PaisPoissonNonisomorphism
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nonisomorphism of the two resonant real Poisson coordinate algebras for all odd exponents. -/

import D5.S3.Algebra.ResonantPoissonBracket
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism

open Omega.PaisPoisson Polynomial

variable {n m : ℕ}

private theorem no_poly_ode {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (a : R)
    (Q : R[X]) (h : (C a - X ^ 2) * derivative Q - X * Q = 0) : Q = 0 := by
  have hc := congrArg leadingCoeff (sub_eq_zero.mp h)
  have hlead : (C a - X ^ 2 : R[X]).leadingCoeff = -1 := by
    rw [show C a - X ^ 2 = -(X ^ 2 - C a) by ring]
    rw [leadingCoeff_neg, (monic_X_pow_sub_C a (by decide : 2 ≠ 0)).leadingCoeff]
  rw [leadingCoeff_mul, leadingCoeff_mul, hlead, leadingCoeff_X, leadingCoeff_derivative] at hc
  have hz : Q.leadingCoeff * ((↑(Q.natDegree + 1) : R)) = 0 := by
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination -hc
  exact leadingCoeff_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)))

section Derivation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℝ R] [Algebra ℝ S]

private theorem deriv_poly (F : R[X] →ₐ[ℝ] S) (D : Derivation ℝ S S)
    (hC : ∀ a, D (F (C a)) = 0) (p : R[X]) :
    D (F p) = F (derivative p) * D (F X) := by
  let _ : Algebra R S := (F.comp CAlgHom).toRingHom.toAlgebra
  let _ : IsScalarTower ℝ R S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap ℝ S r = F (C (algebraMap ℝ R r))
    rw [← algebraMap_apply, F.commutes]
  let D' : Derivation R S S :=
    Derivation.mk'
      { toFun := D
        map_add' := D.map_add
        map_smul' := fun a b => by
          change D (a • b) = a • D b
          have hz : D (algebraMap R S a) = 0 := hC a
          rw [Algebra.smul_def, Algebra.smul_def, D.leibniz, hz, smul_zero, add_zero,
            smul_eq_mul] }
      D.leibniz
  have hF : (aeval (F X) : R[X] →ₐ[R] S).restrictScalars ℝ = F := by
    apply algHom_ext'
    · ext a
      exact aeval_C _ _
    · exact aeval_X _
  have hmap (q : R[X]) : aeval (F X) q = F q := DFunLike.congr_fun hF q
  simpa only [hmap, smul_eq_mul, D', Derivation.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    using D'.map_aeval p (F X)

private theorem deriv_base (F : ℝ[X] →ₐ[ℝ] S) (D : Derivation ℝ S S) (p : ℝ[X]) :
    D (F p) = F (derivative p) * D (F X) := by
  have hF : aeval (F X) = F := algHom_ext (aeval_X _)
  simpa only [hF, smul_eq_mul] using D.map_aeval p (F X)

end Derivation

private theorem deriv_constant_C (D : Derivation ℝ (A n m) (A n m))
    (hc : D (u - v) = 0) (p : CPoly) : D (inclC p) = 0 := by
  have he := deriv_base (S := A n m) (inclC (n := n) (m := m)) D p
  rw [inclC_X, hc] at he
  simpa using he

private theorem deriv_formula_V (D : Derivation ℝ (A n m) (A n m))
    (hc : D (u - v) = 0) (p : UV) : D (inclV p) = inclV (derivative p) * D v := by
  change D (inclV p) = inclV (derivative p) * D (inclV X)
  exact deriv_poly (R := CPoly) (S := A n m) inclV D
    (fun a => deriv_constant_C D hc a) p

private theorem deriv_formula_X (D : Derivation ℝ (A n m) (A n m))
    (hc : D (u - v) = 0) (hv : D v = 0) (p : B) :
    D (incl p) = incl (derivative p) * D x := by
  change D (incl p) = incl (derivative p) * D (incl X)
  refine deriv_poly (R := UV) (S := A n m) incl D ?_ p
  intro a
  have he := deriv_formula_V D hc a
  rw [hv] at he
  simpa using he

private theorem deriv_vanish (D : Derivation ℝ (A n m) (A n m))
    (hu : D u = 0) (hv : D v = 0) (hx : D x = 0) (hy : D y = 0) (a : A n m) : D a = 0 := by
  have hc : D (u - v) = 0 := by simp [map_sub D, hu, hv]
  have hB (p : B) : D (incl p) = 0 := by rw [deriv_formula_X D hc hv, hx, mul_zero]
  rw [normal a, map_add D, leibniz_mul (S := A n m) D (incl a.im) y, hB, hy, hB]
  simp

private def central (b : SkewBiderivation (A n m)) (a : A n m) : Prop := ∀ z, b.ham a z = 0

/-- The six entries of (23), with the order of the arguments as printed. -/
private structure Canonical (b : SkewBiderivation (A n m)) (Ω : ℝ) : Prop where
  uv : b.ham u v = 0
  ux : b.ham u x = Ω • y
  vx : b.ham v x = Ω • y
  uy : b.ham u y = -(Ω • x)
  vy : b.ham v y = -(Ω • x)
  xy : b.ham x y = (-Ω / 2) •
    (u ^ (n - 1) * v ^ (m - 1) * ((n : A n m) * v + (m : A n m) * u))

/-- The six entries of (26) and (27), with the order of the arguments as printed. -/
private structure Alternative (b : SkewBiderivation (A n m)) (Ω : ℝ) : Prop where
  uv : b.ham u v = 0
  ux : b.ham u x = Ω • y
  vx : b.ham v x = -(Ω • y)
  uy : b.ham u y = -(Ω • x)
  vy : b.ham v y = Ω • x
  xy : b.ham x y = (-Ω / 2) •
    (u ^ (n - 1) * v ^ (m - 1) * ((n : A n m) * v - (m : A n m) * u))

private theorem alt_central {b : SkewBiderivation (A n m)} {Ω : ℝ}
    (h : Alternative b Ω) : central b (u + v) := by
  apply deriv_vanish (b.ham (u + v))
  · rw [b.left_add, b.skew v u, h.uv, b.self_zero]
    simp
  · rw [b.left_add, b.self_zero, h.uv]
    simp
  · rw [b.left_add, h.ux, h.vx]
    abel
  · rw [b.left_add, h.uy, h.vy]
    abel

private theorem canon_center_forward {b : SkewBiderivation (A n m)} {Ω : ℝ}
    (h : Canonical b Ω) (hΩ : Ω ≠ 0) {a : A n m} (ha : central b a) :
    ∃ p : CPoly, a = inclC p := by
  let D := b.ham u
  have hc : D (u - v) = 0 := by
    change b.ham u (u - v) = 0
    rw [map_sub (b.ham u), b.self_zero, h.uv]
    simp
  have hv : D v = 0 := h.uv
  have hd : D a = 0 := by
    change b.ham u a = 0
    rw [b.skew u a, ha u]
    simp
  have hformula : D a = Ω • (incl (derivative a.re) * y +
      incl ((rad n m) * derivative a.im - xb * a.im)) := by
    conv_lhs => rw [normal a]
    rw [map_add D, leibniz_mul (S := A n m) D (incl a.im) y,
      deriv_formula_X D hc hv a.re, deriv_formula_X D hc hv a.im,
      show D x = Ω • y from h.ux, show D y = -(Ω • x) from h.uy]
    have hs (z : A n m) : Ω • z = algebraMap ℝ (A n m) Ω * z := Algebra.smul_def Ω z
    simp only [hs]
    rw [map_sub (incl (n := n) (m := m)), map_mul (incl (n := n) (m := m)),
      map_mul (incl (n := n) (m := m)), ← y_sq]
    change _ = algebraMap ℝ (A n m) Ω *
      (incl (derivative a.re) * y + (y ^ 2 * incl (derivative a.im) - x * incl a.im))
    ring
  have hcoords : incl (derivative a.re) * y +
      incl (rad n m * derivative a.im - xb * a.im) = (0 : A n m) := by
    rw [hformula] at hd
    exact (smul_eq_zero_iff_right hΩ).mp hd
  have hp : derivative a.re = 0 := by
    have him := congrArg (fun z : A n m => z.im) hcoords
    simpa only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, incl,
      IsScalarTower.toAlgHom_apply, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      y, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, mul_one, mul_zero, zero_mul, zero_add,
      add_zero, QuadraticAlgebra.im_zero] using him
  have hq : a.im = 0 := by
    apply no_poly_ode (uu ^ n * vv ^ m)
    have hre := congrArg (fun z : A n m => z.re) hcoords
    simpa only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, incl,
      IsScalarTower.toAlgHom_apply, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      y, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, mul_zero, zero_mul, zero_add,
      QuadraticAlgebra.re_zero] using hre
  let p := a.re.coeff 0
  have hap : a = inclV p := by
    have he : a.re = C p := eq_C_of_derivative_eq_zero hp
    rw [normal a, he, incl_C, hq]
    simp
  let E := b.ham x
  have hEc : E (u - v) = 0 := by
    rw [map_sub E]
    change b.ham x u - b.ham x v = 0
    rw [b.skew x u, b.skew x v, h.ux, h.vx]
    simp
  have hEp : E a = 0 := by
    change b.ham x a = 0
    rw [b.skew x a, ha x]
    simp
  rw [hap, deriv_formula_V E hEc p] at hEp
  have hEv : E v = -(Ω • y) := (b.skew x v).trans (congrArg Neg.neg h.vx)
  rw [hEv] at hEp
  have hs : inclV (derivative p) * -(Ω • y) =
      -(Ω • ((inclV (derivative p) : A n m) * y)) := by
    have ht (z : A n m) : Ω • z = algebraMap ℝ (A n m) Ω * z := Algebra.smul_def Ω z
    simp only [ht]
    ring
  rw [hs] at hEp
  have hEp' : Ω • ((inclV (derivative p) : A n m) * y) = 0 := by
    exact (neg_eq_zero (α := A n m)).mp hEp
  have hprod := (smul_eq_zero_iff_right hΩ).mp hEp'
  have hdp : derivative p = 0 := by
    have him := congrArg (fun z : A n m => z.im) hprod
    have hC : (C (derivative p) : B) = 0 := by
      change (incl (C (derivative p)) * y).im = (0 : A n m).im at him
      simpa only [QuadraticAlgebra.im_mul, incl, IsScalarTower.toAlgHom_apply,
        QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, y, QuadraticAlgebra.re_omega,
        QuadraticAlgebra.im_omega, mul_one, mul_zero, zero_mul, add_zero,
        QuadraticAlgebra.im_zero] using him
    exact C_injective (hC.trans C_0.symm)
  exact ⟨p.coeff 0, hap.trans (congrArg inclV (eq_C_of_derivative_eq_zero hdp))⟩

private abbrev Character (n m : ℕ) := A n m →ₐ[ℝ] ℝ

private def origin (hn : 0 < n) (hm : 0 < m) : Character n m :=
  evaluate 0 0 0 0 (by simp [zero_pow hn.ne', zero_pow hm.ne'])

private theorem character_relation (f : Character n m) :
    f x ^ 2 + f y ^ 2 = f u ^ n * f v ^ m := by
  have h := congrArg f (relation (n := n) (m := m))
  change f (x ^ 2 + y ^ 2) = f (u ^ n * v ^ m) at h
  rw [map_add f, map_mul f] at h
  exact (f.toRingHom.map_pow x 2 ▸ f.toRingHom.map_pow y 2 ▸
    f.toRingHom.map_pow u n ▸ f.toRingHom.map_pow v m ▸ h)

private theorem alt_zero_fiber (hn : Odd n) (hm : Odd m) (f : Character n m)
    (hf : f (u + v) = 0) : f = origin (hn.pos) (hm.pos) := by
  rw [map_add f] at hf
  have hrel := character_relation f
  have hu : f u = 0 := by
    rcases lt_trichotomy (f u) 0 with hu | hu | hu
    · have hv : 0 < f v := by linarith
      have hneg := mul_neg_of_neg_of_pos (hn.pow_neg hu) (pow_pos hv m)
      nlinarith [sq_nonneg (f x), sq_nonneg (f y)]
    · exact hu
    · have hv : f v < 0 := by linarith
      have hneg := mul_neg_of_pos_of_neg (pow_pos hu n) (hm.pow_neg hv)
      nlinarith [sq_nonneg (f x), sq_nonneg (f y)]
  have hv : f v = 0 := by linarith
  rw [hu, zero_pow (hn.pos).ne', zero_mul] at hrel
  have hx : f x = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (f y)])
  have hy : f y = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (f x)])
  apply hom_ext <;> simp [origin, hu, hv, hx, hy]

private theorem canon_fiber (hn : 0 < n) (hm : 0 < m) (c : ℝ) :
    ∃ f g : Character n m, f ≠ g ∧ f (u - v) = c ∧ g (u - v) = c := by
  by_cases hc : c = 0
  · subst c
    let f := origin hn hm
    let g : Character n m := evaluate 1 1 1 0 (by simp)
    refine ⟨f, g, ?_, ?_, ?_⟩
    · intro h
      have hx := AlgHom.congr_fun h x
      simp [f, g, origin] at hx
    · rw [map_sub f]
      simp [f, origin]
    · simp only [map_sub g, g, evaluate_u, evaluate_v, sub_self]
  · let f : Character n m := evaluate c 0 0 0 (by simp [zero_pow hm.ne'])
    let g : Character n m := evaluate 0 (-c) 0 0 (by simp [zero_pow hn.ne'])
    refine ⟨f, g, ?_, ?_, ?_⟩
    · intro h
      have hu := AlgHom.congr_fun h u
      exact hc (by simpa [f, g] using hu)
    · simp only [map_sub f, f, evaluate_u, evaluate_v, sub_zero]
    · simp only [map_sub g, g, evaluate_u, evaluate_v, zero_sub, neg_neg]

private theorem character_center_eval {f g : Character n m}
    (h : f (u - v) = g (u - v)) (p : CPoly) : f (inclC p) = g (inclC p) := by
  have heq : f.comp inclC = g.comp inclC := by
    apply Polynomial.algHom_ext
    change f (inclC X) = g (inclC X)
    rwa [inclC_X]
  exact AlgHom.congr_fun heq p

/-- Both brackets may be any skew real biderivations with the indicated generator values. -/
private theorem no_isomorphism {can alt : SkewBiderivation (A n m)} {Ω : ℝ}
    (hn : Odd n) (hm : Odd m) (hΩ : Ω ≠ 0)
    (hcan : Canonical can Ω) (halt : Alternative alt Ω) :
    ¬ ∃ e : A n m ≃ₐ[ℝ] A n m, PreservesBracket e alt can := by
  rintro ⟨e, he⟩
  have ha : central can (e (u + v)) := by
    intro z
    rw [← e.apply_symm_apply z, ← he, alt_central halt, map_zero e]
  obtain ⟨p, hp⟩ := canon_center_forward hcan hΩ ha
  let f₀ : Character n m := (origin (hn.pos) (hm.pos)).comp e.symm.toAlgHom
  obtain ⟨f, g, hne, hf, hg⟩ :=
    canon_fiber (hn.pos) (hm.pos) (f₀ (u - v))
  have h₀ : f₀ (e (u + v)) = 0 := by
    change origin (hn.pos) (hm.pos) (e.symm (e (u + v))) = 0
    rw [e.symm_apply_apply, map_add (origin (hn.pos) (hm.pos))]
    simp [origin]
  have transported (k : Character n m) (hk : k (u - v) = f₀ (u - v)) :
      k.comp e.toAlgHom = origin (hn.pos) (hm.pos) := by
    apply alt_zero_fiber hn hm
    change k (e (u + v)) = 0
    rw [hp, character_center_eval hk p, ← hp, h₀]
  exact hne ((AlgHom.cancel_right e.surjective).mp ((transported f hf).trans (transported g hg).symm))


section Conjugate
variable {S T : Type*} [CommRing S] [CommRing T] [Algebra ℝ S] [Algebra ℝ T]

/-- Transport a bracket along a real algebra equivalence. -/
private def conjugate (e : S ≃ₐ[ℝ] T) (b : SkewBiderivation S) : SkewBiderivation T where
  ham f := Derivation.liftOfRightInverse (f := e.toAlgHom) (f_inv := e.symm)
    e.apply_symm_apply (by
      intro a ha
      have ha' : a = 0 := e.injective (by simpa using ha)
      simp [ha'])
  skew f g := by
    change e (b.ham (e.symm f) (e.symm g)) = -e (b.ham (e.symm g) (e.symm f))
    rw [b.skew, map_neg e]

private theorem conjugate_apply (e : S ≃ₐ[ℝ] T) (b : SkewBiderivation S) (f g : S) :
    (conjugate e b).ham (e f) (e g) = e (b.ham f g) := by
  change e (b.ham (e.symm (e f)) (e.symm (e g))) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

end Conjugate


private theorem generatorTable_conjugate {S T : Type*} [CommRing S] [CommRing T] [Algebra ℝ S] [Algebra ℝ T]
    {n m : ℕ} {b : SkewBiderivation S} {u v x y : S} {Ω s : ℝ}
    (h : GeneratorTable (n := n) (m := m) b u v x y Ω s) (e : S ≃ₐ[ℝ] T) :
    GeneratorTable (n := n) (m := m) (conjugate e b) (e u) (e v) (e x) (e y) Ω s := by
  constructor <;> simp only [conjugate_apply, ← map_smul e, ← map_neg e,
    ← map_mul e, ← map_add e, ← map_pow e, ← map_natCast e, ← map_zero e]
  · exact congrArg e h.uv
  · exact congrArg e h.ux
  · exact congrArg e h.vx
  · exact congrArg e h.uy
  · exact congrArg e h.vy
  · exact congrArg e h.xy

private theorem paper_canonical_to_model {n m : ℕ} {b : SkewBiderivation (Paper n m)} {Ω : ℝ}
    (h : PaperTable b Ω 1) : Canonical (conjugate (paperEquiv n m) b) Ω := by
  have h' := generatorTable_conjugate (S := Paper n m) (T := A n m) h (paperEquiv n m)
  simp only [paperEquiv_qu, paperEquiv_qv, paperEquiv_qx, paperEquiv_qy] at h'
  exact ⟨h'.uv, h'.ux, by simpa only [one_smul] using h'.vx, h'.uy,
    by simpa only [one_smul] using h'.vy, by simpa only [one_smul] using h'.xy⟩

private theorem paper_alternative_to_model {n m : ℕ} {b : SkewBiderivation (Paper n m)} {Ω : ℝ}
    (h : PaperTable b Ω (-1)) : Alternative (conjugate (paperEquiv n m) b) Ω := by
  have h' := generatorTable_conjugate (S := Paper n m) (T := A n m) h (paperEquiv n m)
  simp only [paperEquiv_qu, paperEquiv_qv, paperEquiv_qx, paperEquiv_qy] at h'
  have hs (z : A n m) : (-1 : ℝ) • z = -z := neg_one_smul ℝ z
  have hsn (z : A n m) : Ω • (-z) = -(Ω • z) := smul_neg Ω z
  have hnn (z : A n m) : -(-z) = z := neg_neg z
  have hsub (a b : A n m) : a - b = a + -b := sub_eq_add_neg a b
  exact ⟨h'.uv, h'.ux, by simpa only [hs, hsn] using h'.vx, h'.uy,
    by simpa only [hs, hsn, hnn] using h'.vy, by simpa only [hs, hsub] using h'.xy⟩

private theorem no_paper_isomorphism {n m : ℕ} {can alt : SkewBiderivation (Paper n m)} {Ω : ℝ}
    (hn : Odd n) (hm : Odd m) (hΩ : Ω ≠ 0)
    (hcan : PaperTable can Ω 1) (halt : PaperTable alt Ω (-1)) :
    ¬ ∃ e : Paper n m ≃ₐ[ℝ] Paper n m, PreservesBracket e alt can := by
  rintro ⟨e, he⟩
  let a := paperEquiv n m
  let e' := (a.symm.trans e).trans a
  apply no_isomorphism hn hm hΩ (paper_canonical_to_model hcan) (paper_alternative_to_model halt)
  refine ⟨e', ?_⟩
  intro f g
  obtain ⟨f, rfl⟩ := a.surjective f
  obtain ⟨g, rfl⟩ := a.surjective g
  have hq (p : Paper n m) : e' (a p) = a (e p) := by
    change a (e (a.symm (a p))) = _
    rw [a.symm_apply_apply]
  change e' ((conjugate a alt).ham (a f) (a g)) =
    (conjugate a can).ham (e' (a f)) (e' (a g))
  rw [conjugate_apply (S := Paper n m) (T := A n m) a alt f g,
    hq, hq, hq, conjugate_apply (S := Paper n m) (T := A n m) a can (e f) (e g), he f g]

/-- For odd natural exponents and any nonzero real frequency, the actual Poisson
brackets on the full real coordinate quotient admit no real algebra equivalence
preserving the bracket. -/
theorem result (n m : ℕ) (hn : Odd n) (hm : Odd m) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    ¬ ∃ e : Paper n m ≃ₐ[ℝ] Paper n m,
      PreservesBracket e
        (paperPoisson n m hn.pos hm.pos Ω (-1)).bracket
        (paperPoisson n m hn.pos hm.pos Ω 1).bracket :=
  no_paper_isomorphism hn hm hΩ (quotientBracket_table n m hn.pos hm.pos Ω 1)
    (quotientBracket_table n m hn.pos hm.pos Ω (-1))

end D5.S3.Geometry.Poisson.PaisPoissonNonisomorphism
