/- GID: D5/S3/Arith/CMJet/Correction
   generality: G
   mirror-B: none(waiver:cm-jet-native-arithmetic)
   mirror-E: none(waiver:cm-jet-native-arithmetic)
   anchors: []
   utility: none
   digest: The restricted iterate gives a two-term recurrence for all integer section jets. -/

import D5.S3.Arith.CMJet.JetReduction

/-! The correction term for the restricted iterate of the section. -/

noncomputable section

namespace D5.S3.Arith.CMJet.ActualRestricted

open Polynomial Function
open scoped Polynomial

variable {p : ℕ} [Fact p.Prime]

private abbrev F (p : ℕ) := ZMod p

private def scalar (p : ℕ) : F p →+* JetExt (F p) :=
  Polynomial.C.comp (Polynomial.C.comp (algebraMap (F p) (Base (F p))))

omit [Fact p.Prime] in
private lemma deriv_scalar (h : ℤ) (a : F p) :
    extendedDerivation (F p) h (scalar p a) = 0 := by
  simp [scalar, baseDerivation]

private lemma embed_smul (a : F p) (q : Base (F p)) :
    (C (C (a • q)) : JetExt (F p)) = scalar p a * C (C q) := by
  simp [scalar, Algebra.smul_def]

omit [Fact p.Prime] in
private lemma deriv_comm (h : ℤ) (q : JetExt (F p)) :
    extendedDerivation (F p) h ((extendedDerivation (F p) h)^[p] q) =
      (extendedDerivation (F p) h)^[p] (extendedDerivation (F p) h q) := by
  let d : JetExt (F p) → JetExt (F p) := extendedDerivation (F p) h
  exact (iterate_succ_apply' d p q).symm.trans (iterate_succ_apply d p q)

/-- The coefficient of the invariant derivative in the restricted base derivation. -/
def cmLambda (p : ℕ) : F p :=
  ((Q^[p / 2] (X : (F p)[X])).derivative).coeff 0

private lemma cmLambda_base (hp₂ : 2 < p) (hodd : p % 2 = 1)
    (h : ℤ) (q : Base (F p)) :
    (extendedDerivation (F p) h)^[p] (C (C q)) =
      scalar p (cmLambda p) * extendedDerivation (F p) h (C (C q)) := by
  obtain ⟨a, ha, hval⟩ := prime_iter_scalar (p := p) hp₂ hodd
  rw [← extendedIter_eq, extendedIter_base, ha, hval, embed_smul,
    extendedDerivation_C, zDerivation_C]
  rfl

/-- The quotient of the restricted derivative of S, corrected by its base scalar. -/
def correction (h : ℤ) (p : ℕ) : JetExt (F p) :=
  C (sectionQuotient (F p) h 1 p) - scalar p (cmLambda p) * C (sSpeed (F p) h)

private lemma cancel_X {A : Type*} [CommRing A] {u v : A[X]}
    (h : X * u = X * v) : u = v := by
  ext n
  simpa only [coeff_X_mul] using congrArg (fun q : A[X] => q.coeff (n + 1)) h

private lemma extendedIter_Z (h : ℤ) (n : ℕ) :
    extendedIter (F p) h (n + 1) (C (X : ZExt (F p))) =
      C (C (iter n (zSpeed (F p)))) := by
  rw [extendedIter_add, extendedIter_succ, extendedIter_zero, extendedDerivation_C,
    zDerivation_X, extendedIter_base]

private lemma quotient_deriv {A : Type*} [CommRing A]
    (d e : Derivation ℤ A A) (s z b : A) (h : ℤ)
    (cancel : ∀ u v : A, s * u = s * v → u = v)
    (comm : d (e s) = e (d s)) (ds : d s = (h • z) * s) (es : e s = s * b) :
    d b = h • e z := by
  apply cancel
  rw [es, ds, d.leibniz, e.leibniz, es, ds, map_zsmul] at comm
  simp only [smul_eq_mul, ← Int.cast_smul_eq_zsmul A] at comm ⊢
  linear_combination comm

private lemma correction_deriv (h : ℤ) :
    extendedDerivation (F p) h (correction h p) =
      h • ((extendedDerivation (F p) h)^[p] (C (X : ZExt (F p))) -
        scalar p (cmLambda p) * C (C (zSpeed (F p)))) := by
  let d := extendedDerivation (F p) h
  let e := extendedPrime p h
  let s : JetExt (F p) := X
  let z : JetExt (F p) := C X
  let b : JetExt (F p) := C (sectionQuotient (F p) h 1 p)
  have hes : e s = s * b := by
    change extendedPrime p h (X : JetExt (F p)) = _
    rw [extendedPrime_apply, ← extendedIter_eq, extendedIter_S]
  have hds : d s = (h • z) * s := by
    change extendedDerivation (F p) h (X : JetExt (F p)) = _
    rw [extendedDerivation_X, sSpeed, map_zsmul]
  have hcomm : d (e s) = e (d s) := by
    change d (extendedPrime p h s) = extendedPrime p h (d s)
    rw [extendedPrime_apply, extendedPrime_apply]
    exact deriv_comm h s
  have hc := quotient_deriv d e s z b h (fun _ _ => cancel_X) hcomm hds hes
  have hdz : d z = C (C (zSpeed (F p))) := by
    change extendedDerivation (F p) h (C (X : ZExt (F p))) = _
    rw [extendedDerivation_C, zDerivation_X]
  have hb : correction h p = b - scalar p (cmLambda p) * (h • z) := by
    rw [correction, sSpeed, map_zsmul]
  rw [hb, map_sub, Derivation.leibniz, map_zsmul, deriv_scalar]
  change d b - ((scalar p (cmLambda p)) * (h • d z) + (h • z) * 0) = _
  have hez : e z = (extendedDerivation (F p) h)^[p] (C (X : ZExt (F p))) :=
    extendedPrime_apply p h z
  calc
    _ = h • e z - (scalar p (cmLambda p) * (h • C (C (zSpeed (F p)))) + (h • z) * 0) :=
      congrArg₂ (fun u v => u - (scalar p (cmLambda p) * (h • v) + (h • z) * 0)) hc hdz
    _ = _ := by
      rw [hez]
      simp only [← Int.cast_smul_eq_zsmul (JetExt (F p)), smul_eq_mul]
      ring

/-- The derivative of the correction is constant along the derivation. -/
theorem correction_second (h : ℤ) (hp₂ : 2 < p) (hodd : p % 2 = 1) :
    extendedDerivation (F p) h (extendedDerivation (F p) h (correction h p)) = 0 := by
  rw [correction_deriv, map_zsmul, map_sub, deriv_comm, Derivation.leibniz,
    deriv_scalar, extendedDerivation_C, zDerivation_X,
    cmLambda_base hp₂ hodd h (zSpeed (F p))]
  simp [smul_eq_mul]

/-- The derivative of the correction at the origin is the exact residue coefficient. -/
theorem eval_correction_deriv (h : ℤ) :
    evalJet (F p) (extendedDerivation (F p) h (correction h p)) =
      2 * (h : F p) * atO (iter (p - 1) ((x (F p)) ^ 2)) := by
  have hp : (p - 1) + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hiter : (extendedDerivation (F p) h)^[p] (C (X : ZExt (F p))) =
      C (C (iter (p - 1) (zSpeed (F p)))) := by
    rw [← extendedIter_eq]
    exact (congrArg (fun n => extendedIter (F p) h n (C (X : ZExt (F p)))) hp).symm.trans
      (extendedIter_Z h (p - 1))
  have hx : atORingHom (F p) (x (F p)) = 0 := by
    change atO (x (F p)) = 0
    simp [x, atO_apply]
  have hz : atORingHom (F p) (zSpeed (F p)) = 0 := by
    simp [zSpeed, hx]
  rw [correction_deriv, hiter, map_zsmul, map_sub, map_mul, evalJet_C, evalZ_C,
    evalJet_C, evalZ_C, hz, mul_zero, sub_zero]
  change h • atO (iter (p - 1) (zSpeed (F p))) = _
  rw [show zSpeed (F p) = 2 • (x (F p)) ^ 2 by simp [zSpeed, two_mul],
    map_nsmul, map_nsmul]
  simp only [← Nat.cast_smul_eq_nsmul (F p), ← Int.cast_smul_eq_zsmul (F p), smul_eq_mul]
  ring

private def negX (R : Type*) [CommRing R] : R[X] →+* R[X] :=
  compRingHom (-X)

private theorem negX_X (R : Type*) [CommRing R] : negX R (X : R[X]) = -X :=
  X_comp

private theorem negX_W (R : Type*) [CommRing R] : negX R (W R) = W R := by
  rw [W, map_sub, map_one, map_pow, negX_X, neg_pow, show (-1 : R[X]) ^ 4 = 1 by ring, one_mul]

private def curveParity (R : Type*) [CommRing R] : Base R →+* Base R where
  toFun q := ⟨negX R q.re, negX R q.im⟩
  map_one' := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' u v := by apply QuadraticAlgebra.ext <;> simp
  map_mul' u v := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
        negX_W, map_zero]

private theorem deriv_negX {R : Type*} [CommRing R] (q : R[X]) :
    (negX R q).derivative = -negX R q.derivative := by
  change (q.comp (-X)).derivative = -(q.derivative.comp (-X))
  simp [derivative_comp]

private theorem curveParity_deriv {R : Type*} [CommRing R] (q : Base R) :
    curveParity R (D R q) = -(D R (curveParity R q)) := by
  apply QuadraticAlgebra.ext
  · change negX R (W R * q.im.derivative - 2 * X ^ 3 * q.im) =
      -(W R * (negX R q.im).derivative - 2 * X ^ 3 * negX R q.im)
    simp only [map_sub, map_mul, map_pow, map_ofNat, negX_W, deriv_negX, negX_X]
    ring
  · change negX R q.re.derivative = -(negX R q.re).derivative
    rw [deriv_negX, neg_neg]

private theorem curveParity_x (R : Type*) [CommRing R] :
    curveParity R (x R) = -(x R) := by
  apply QuadraticAlgebra.ext
  · exact negX_X R
  · change negX R 0 = -0
    simp

private def zParity (R : Type*) [CommRing R] : ZExt R →+* ZExt R :=
  eval₂RingHom (C.comp (curveParity R)) (-X)

private theorem zParity_C {R : Type*} [CommRing R] (q : Base R) :
    zParity R (C q) = C (curveParity R q) := eval₂_C _ _

private theorem zParity_X (R : Type*) [CommRing R] :
    zParity R (X : ZExt R) = -X := eval₂_X _ _

private theorem curveParity_zSpeed (R : Type*) [CommRing R] :
    curveParity R (zSpeed R) = zSpeed R := by
  rw [zSpeed, map_mul, map_ofNat, map_pow, curveParity_x, neg_sq]

private theorem zParity_deriv {R : Type*} [CommRing R] (q : ZExt R) :
    zParity R (zDerivation R q) = -(zDerivation R (zParity R q)) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [map_add, hq, hr, neg_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, zDerivation_C, zDerivation_X,
      map_add, map_mul, map_pow, map_nsmul, smul_eq_mul, zParity_C, zParity_X,
      curveParity_zSpeed, map_neg, baseDerivation, Derivation.restrictScalars_apply,
      curveParity_deriv]
    simp only [← Nat.cast_smul_eq_nsmul (ZExt R), smul_eq_mul]
    ring

private theorem curveParity_eval {R : Type*} [CommRing R] (q : Base R) :
    atORingHom R (curveParity R q) = atORingHom R q := by
  have hcoeff (f : R[X]) : (negX R f).coeff 0 = f.coeff 0 := by
    change (f.comp (-X)).coeff 0 = _
    simp [coeff_zero_eq_eval_zero, eval_comp]
  change (negX R q.re).coeff 0 + (negX R q.im).coeff 0 = q.re.coeff 0 + q.im.coeff 0
  rw [hcoeff, hcoeff]

private theorem zParity_eval {R : Type*} [CommRing R] (q : ZExt R) :
    evalZ R (zParity R q) = evalZ R q := by
  change evalZ R (q.eval₂ (C.comp (curveParity R)) (-X)) = _
  rw [hom_eval₂, map_neg]
  have hz : evalZ R (X : ZExt R) = 0 := eval₂_X _ _
  rw [hz, neg_zero]
  have heq : (evalZ R).comp (C.comp (curveParity R)) = atORingHom R :=
    RingHom.ext (fun a => by simpa only [RingHom.comp_apply, evalZ_C] using curveParity_eval a)
  rw [heq]
  rfl

/-- Reflection acts on each successive quotient by the sign of its derivative order. -/
private theorem sectionQuotient_parity (R : Type*) [CommRing R] (h : ℤ) (n : ℕ) :
    zParity R (sectionQuotient R h 1 n) =
      (-1 : ZExt R) ^ n * sectionQuotient R h 1 n := by
  induction n with
  | zero => simp [sectionQuotient]
  | succ n ih =>
    have hz : zDerivation R ((-1 : ZExt R) ^ n) = 0 := by
      simp
    simp only [sectionQuotient, map_add, map_mul, zParity_deriv, ih, sSpeed, map_zsmul,
      zParity_X, zsmul_neg, Derivation.leibniz, hz, smul_eq_mul, mul_zero, add_zero,
      pow_succ]
    simp only [← Int.cast_smul_eq_zsmul (ZExt R), smul_eq_mul]
    ring

/-- For odd primes, the concrete correction vanishes at the section's origin. -/
theorem eval_correction (p : ℕ) [Fact p.Prime] (hp₂ : 2 < p) (hodd : Odd p) (h : ℤ) :
    evalJet (ZMod p) (correction h p) = 0 := by
  have hval := congrArg (evalZ (ZMod p)) (sectionQuotient_parity (ZMod p) h p)
  rw [zParity_eval, map_mul, map_pow, map_neg, map_one, hodd.neg_pow, one_pow, neg_one_mul] at hval
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hp₂)
      ((ZMod.natCast_eq_zero_iff 2 p).mp he)
  have hzq : evalZ (ZMod p) (sectionQuotient (ZMod p) h 1 p) = 0 := by
    rw [eq_neg_iff_add_eq_zero, ← two_mul] at hval
    exact (mul_eq_zero.mp hval).resolve_left htwo
  have hz : evalZ (ZMod p) (X : ZExt (ZMod p)) = 0 := eval₂_X _ _
  rw [correction, map_sub, evalJet_C, hzq, map_mul, evalJet_C, sSpeed, map_zsmul, hz,
    smul_zero, mul_zero, sub_zero]

private theorem iterate_affine_succ {R : Type*} [CommRing R] (d : Derivation ℤ R R)
    (C F : R) (hc : d (d C) = 0) (k : ℕ) :
    d^[k + 1] (C * F) = C * d^[k + 1] F + (k + 1) • (d C * d^[k] F) := by
  induction k with
  | zero =>
    simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_add, d.leibniz, map_nsmul, d.leibniz, hc]
    simp only [smul_eq_mul, mul_zero, add_zero, Function.iterate_succ_apply',
      ← Nat.cast_smul_eq_nsmul R, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem iterate_affine {R : Type*} [CommRing R] (d : Derivation ℤ R R)
    (C F : R) (hc : d (d C) = 0) (k : ℕ) :
    d^[k] (C * F) = C * d^[k] F + k • (d C * d^[k - 1] F) := by
  cases k with
  | zero => simp
  | succ k => simpa only [Nat.add_sub_cancel] using iterate_affine_succ d C F hc k

private theorem iterate_mul_constant {R : Type*} [CommRing R] (d : Derivation ℤ R R)
    (a f : R) (ha : d a = 0) (k : ℕ) :
    d^[k] (a * f) = a * d^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, d.leibniz, ha, smul_eq_mul, mul_zero,
      add_zero]

private theorem eval_scalar (p : ℕ) (a : F p) : evalJet (F p) (scalar p a) = a := by
  simp only [scalar, RingHom.comp_apply, evalJet_C, evalZ_C]
  change atO (algebraMap (F p) (Base (F p)) a) = a
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  have hOne : atO (1 : Base (F p)) = 1 := (atORingHom (F p)).map_one
  simp only [hOne, smul_eq_mul, mul_one]

private theorem section_prime (hp₂ : 2 < p) (hodd : p % 2 = 1) (h : ℤ) (j : ℕ) :
    (extendedDerivation (F p) h)^[p] (sectionElement (F p) j) =
      scalar p (cmLambda p) * extendedDerivation (F p) h (sectionElement (F p) j) +
        correction h p * sectionElement (F p) j := by
  rw [← extendedPrime_apply, sectionElement, Derivation.leibniz]
  simp only [extendedPrime_apply, cmLambda_base hp₂ hodd h, smul_eq_mul]
  rw [← extendedIter_eq, extendedIter_S, Derivation.leibniz, extendedDerivation_X, correction]
  simp only [smul_eq_mul]
  ring

/-- For every odd prime and every order, the concrete integer jets satisfy the two-term
restricted derivative recurrence. The second term vanishes at order zero. -/
theorem integer_jet_recurrence (p : ℕ) [Fact p.Prime] (hp₂ : 2 < p) (hodd : Odd p)
    (h k j : ℕ) :
    (jet h (p + k) j : F p) =
      cmLambda p * (jet h (k + 1) j : F p) +
        (k : F p) * (2 * (h : F p) * atO (iter (p - 1) ((x (F p)) ^ 2))) *
          (jet h (k - 1) j : F p) := by
  have hpOdd : p % 2 = 1 := Nat.odd_iff.mp hodd
  simp only [jet_reduce_cast, extendedIter_eq]
  rw [Nat.add_comm p k, Function.iterate_add_apply, section_prime hp₂ hpOdd,
    ← extendedIter_eq, map_add, extendedIter_eq, extendedIter_eq]
  let d := extendedDerivation (F p) (h : ℤ)
  let f := sectionElement (F p) j
  let l := scalar p (cmLambda p)
  let c := correction (h : ℤ) p
  change evalJet (F p) (d^[k] (l * d f) + d^[k] (c * f)) = _
  have hl : d l = 0 := deriv_scalar (h : ℤ) (cmLambda p)
  have hc : d (d c) = 0 := correction_second (h : ℤ) hp₂ hpOdd
  have ht : d^[k] (l * d f) = l * d^[k + 1] f :=
    (iterate_mul_constant d l (d f) hl k).trans
      (congrArg (l * ·) (Function.iterate_succ_apply d k f).symm)
  calc
    _ = evalJet (F p)
        (l * d^[k + 1] f + (c * d^[k] f + k • (d c * d^[k - 1] f))) :=
      congrArg₂ (fun a b => evalJet (F p) (a + b)) ht (iterate_affine d c f hc k)
    _ = _ := by
      simp only [map_add, map_mul, map_nsmul, l, c, d, eval_scalar, eval_correction p hp₂ hodd,
        zero_mul, zero_add, eval_correction_deriv]
      simp only [← Nat.cast_smul_eq_nsmul (F p), smul_eq_mul, f, Int.cast_natCast]
      ring

end D5.S3.Arith.CMJet.ActualRestricted
