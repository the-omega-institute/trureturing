/- GID: D5/S1/Dynamics/Symbolic/KhetanDirectionalCoprimality
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Geometric line divisibility excludes transverse factors after coefficient localization. -/

import D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
import D5.S1.Dynamics.Symbolic.KhetanBinomialIrreducibility
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
The geometric hypothesis below quantifies over literal Laurent line embeddings
and divisibility in the original two-dimensional ring. It contains no localized
coprimality, eliminant or irreducibility assertion.

Only monic polynomial division is needed to return a localized binomial divisor
to the original ring. Laurent UFD descent is not used. Irreducibility of the
primitive rational-function binomials is supplied by
`KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime`.
Complex splitting is used only for the scalar polynomial `X^d-1`.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanDirectionalCoprimality

open D5.S1.Dynamics.Symbolic.KhetanLaurent
open D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra
open D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer

private abbrev D := LaurentPolynomial ℂ
private abbrev K := FractionRing D

/-- Every genuine line divisor is parallel to the displayed direction.
The nonunit condition is imposed on the one-variable Laurent polynomial over
the complex field, so scalar monomials do not count as line factors. -/
def OnlyLineDirection (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) : Prop :=
  ∀ (v : Lattice) (A : LaurentPolynomial ℂ), v ≠ 0 → A ≠ 0 → ¬ IsUnit A →
    lineLaurent v A ∣ P → u.1 * v.2 - u.2 * v.1 = 0

private noncomputable def localizeCoefficients :
    LaurentPolynomial D →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K)

private noncomputable def localized (u : Lattice) (hu : IsCoprime u.1 u.2) :
    AddMonoidAlgebra ℂ Lattice →+* LaurentPolynomial K :=
  localizeCoefficients.comp (primitiveLaurentCoordinates u hu).toRingHom

private noncomputable def scalar : ℂ →+* LaurentPolynomial K :=
  LaurentPolynomial.C.comp ((algebraMap D K).comp LaurentPolynomial.C)

private noncomputable def monomial (s k : ℤ) : LaurentPolynomial K :=
  AddMonoidAlgebra.single s (algebraMap D K (LaurentPolynomial.T k))

private noncomputable def binomial (s k : ℤ) (ξ : ℂ) : LaurentPolynomial D :=
  AddMonoidAlgebra.single s (LaurentPolynomial.T k) -
    LaurentPolynomial.C (LaurentPolynomial.C ξ)

private noncomputable def monicBinomial (m : ℕ) (k : ℤ) (ξ : ℂ) : Polynomial D :=
  Polynomial.X ^ m - Polynomial.C (LaurentPolynomial.C ξ * LaurentPolynomial.T (-k))

private theorem coordinates_single (u : Lattice) (hu : IsCoprime u.1 u.2)
    (v : Lattice) (a : ℂ) :
    primitiveLaurentCoordinates u hu (AddMonoidAlgebra.single v a) =
      AddMonoidAlgebra.single (primitiveCoordinates u hu v).1
        (AddMonoidAlgebra.single (primitiveCoordinates u hu v).2 a) := by
  change AddMonoidAlgebra.curryRingEquiv
      (AddMonoidAlgebra.mapDomainRingEquiv ℂ (primitiveCoordinates u hu)
        (AddMonoidAlgebra.single v a)) = _
  rw [AddMonoidAlgebra.mapDomainRingEquiv_single]
  exact AddMonoidAlgebra.curryRingEquiv_single
    (primitiveCoordinates u hu v).1 (primitiveCoordinates u hu v).2 a

private theorem coordinates_fst (u : Lattice) (hu : IsCoprime u.1 u.2)
    (v : Lattice) :
    (primitiveCoordinates u hu v).1 = u.1 * v.2 - u.2 * v.1 := by
  rfl

private theorem coordinates_line_binomial (u : Lattice) (hu : IsCoprime u.1 u.2)
    (s k : ℤ) (ξ : ℂ) :
    primitiveLaurentCoordinates u hu
      (lineLaurent ((primitiveCoordinates u hu).symm (s, k))
        (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ)) = binomial s k ξ := by
  rw [map_sub, map_sub, show LaurentPolynomial.T (1 : ℤ) =
    AddMonoidAlgebra.single (1 : ℤ) (1 : ℂ) from rfl, line_laurent_single,
    one_zsmul]
  change primitiveLaurentCoordinates u hu
      (AddMonoidAlgebra.single ((primitiveCoordinates u hu).symm (s, k)) 1) -
    primitiveLaurentCoordinates u hu
      (lineLaurent ((primitiveCoordinates u hu).symm (s, k))
        (AddMonoidAlgebra.single 0 ξ)) = _
  rw [line_laurent_single, zero_zsmul, coordinates_single, coordinates_single]
  simp only [AddEquiv.apply_symm_apply, map_zero]
  rfl

private theorem monic_binomial_laurent (m : ℕ) (k : ℤ) (ξ : ℂ) :
    (monicBinomial m k ξ).toLaurent =
      LaurentPolynomial.C (LaurentPolynomial.T (-k)) * binomial m k ξ := by
  simp only [monicBinomial, map_sub, Polynomial.toLaurent_X_pow,
    Polynomial.toLaurent_C, binomial, mul_sub, ← map_mul]
  congr 1
  · rw [LaurentPolynomial.single_eq_C_mul_T (LaurentPolynomial.T k) (m : ℤ),
      ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero,
      map_one, one_mul]
  · congr 1
    exact mul_comm _ _

private theorem line_binomial_ne_zero (ξ : ℂ) :
    (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ : D) ≠ 0 := by
  intro hz
  have he : AddMonoidAlgebra.single (1 : ℤ) (1 : ℂ) =
      AddMonoidAlgebra.single 0 ξ := sub_eq_zero.mp hz
  have h := congrArg (fun F : D => F.coeff 1) he
  norm_num [AddMonoidAlgebra.coeff_single_apply] at h

private theorem line_binomial_not_isUnit (ξ : ℂ) (hξ : ξ ≠ 0) :
    ¬ IsUnit (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ : D) := by
  intro hunit
  have h := hunit.map (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 ξ hξ))
  have hz : LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 ξ hξ)
      (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ) = 0 := by
    simp [LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_C]
  rw [hz] at h
  exact not_isUnit_zero h

private theorem map_toLaurent (p : Polynomial D) :
    localizeCoefficients p.toLaurent =
      (p.map (algebraMap D K)).toLaurent := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | monomial n a =>
    simpa only [localizeCoefficients, Polynomial.toLaurent_C_mul_T, Polynomial.map_monomial,
      ← LaurentPolynomial.single_eq_C_mul_T] using
      (AddMonoidAlgebra.mapRingHom_single (algebraMap D K) (n : ℤ) a)

/-- Monic division over the coefficient field descends to an actual transverse
line factor. The conclusion is divisibility in the original lattice ring. -/
private theorem line_divisor_of_monic_binomial_dvd
    (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (m : ℕ) (hm : 0 < m) (k : ℤ) (ξ : ℂ)
    (n : ℕ) (p : Polynomial D)
    (hp : p.toLaurent = primitiveLaurentCoordinates u hu P * LaurentPolynomial.T n)
    (hdiv : (monicBinomial m k ξ).map (algebraMap D K) ∣ p.map (algebraMap D K)) :
    lineLaurent ((primitiveCoordinates u hu).symm ((m : ℤ), k))
      (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ) ∣ P := by
  have hd : monicBinomial m k ξ ∣ p :=
    (Polynomial.map_dvd_map (algebraMap D K) (IsFractionRing.injective D K)
      (Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt hm))).mp hdiv
  have hbq : binomial m k ξ ∣ (monicBinomial m k ξ).toLaurent := by
    rw [monic_binomial_laurent, mul_comm]
    exact dvd_mul_right _ _
  have hbp : binomial m k ξ ∣
      primitiveLaurentCoordinates u hu P * LaurentPolynomial.T n := by
    rw [← hp]
    exact hbq.trans (map_dvd Polynomial.toLaurent hd)
  have hb : binomial m k ξ ∣ primitiveLaurentCoordinates u hu P := by
    have h := hbp.mul_right (LaurentPolynomial.T (-(n : ℤ)))
    simpa only [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, mul_one] using h
  obtain ⟨Q, hQ⟩ := hb
  refine ⟨(primitiveLaurentCoordinates u hu).symm Q, ?_⟩
  apply (primitiveLaurentCoordinates u hu).injective
  rw [map_mul, coordinates_line_binomial, RingEquiv.apply_symm_apply]
  exact hQ

private noncomputable def toRational : D →+* RatFunc ℂ :=
  LaurentPolynomial.eval₂ RatFunc.C (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

private theorem to_rational_polynomial (p : Polynomial ℂ) :
    toRational p.toLaurent = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    simp [toRational, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_monomial,
      RatFunc.algebraMap_monomial]

private theorem to_rational_injective : Function.Injective toRational := by
  apply (injective_iff_map_eq_zero _).mpr
  intro F hF
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow F
  have hz : algebraMap (Polynomial ℂ) (RatFunc ℂ) p = 0 := by
    rw [← to_rational_polynomial, hp, map_mul, hF, zero_mul]
  have hp0 : p = 0 := (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
    (hz.trans (map_zero _).symm)
  have hmul : F * LaurentPolynomial.T n = 0 := by rw [← hp, hp0, map_zero]
  exact (mul_eq_zero.mp hmul).resolve_right (LaurentPolynomial.isUnit_T _).ne_zero

private noncomputable def fractionToRational : K →+* RatFunc ℂ :=
  IsFractionRing.lift to_rational_injective

private theorem rational_monomial_degree (ξ : ℂ) (hξ : ξ ≠ 0) (k : ℤ) :
    (RatFunc.C ξ * RatFunc.X ^ k).intDegree = k := by
  have hC : RatFunc.C ξ ≠ 0 := (map_ne_zero RatFunc.C).mpr hξ
  have hpow (n : ℕ) : ((RatFunc.X : RatFunc ℂ) ^ n).intDegree = n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ RatFunc.X_ne_zero)
        RatFunc.X_ne_zero, ih, RatFunc.intDegree_X] <;>
        simp only [Nat.cast_add, Nat.cast_one]
  rw [RatFunc.intDegree_mul hC (zpow_ne_zero _ RatFunc.X_ne_zero), RatFunc.intDegree_C,
    zero_add]
  cases k with
  | ofNat n => simpa using hpow n
  | negSucc n =>
    simp [zpow_negSucc, RatFunc.intDegree_inv, hpow]
    omega

private theorem monic_binomial_irreducible (m : ℕ) (hm : 0 < m) (k : ℤ)
    (hcop : Int.gcd (m : ℤ) k = 1) (ξ : ℂ) (hξ : ξ ≠ 0) :
    Irreducible ((monicBinomial m k ξ).map (algebraMap D K)) := by
  let q := (monicBinomial m k ξ).map (algebraMap D K)
  have hmap : q.map fractionToRational =
      Polynomial.X ^ m - Polynomial.C (RatFunc.C ξ * RatFunc.X ^ (-k)) := by
    simp [q, monicBinomial, fractionToRational, toRational,
      LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_C,
      Units.val_zpow_eq_zpow_val]
  have ha : RatFunc.C ξ * RatFunc.X ^ (-k) ≠ 0 :=
    mul_ne_zero ((map_ne_zero RatFunc.C).mpr hξ) (zpow_ne_zero _ RatFunc.X_ne_zero)
  have hdegree : Int.gcd (m : ℤ)
      (RatFunc.C ξ * RatFunc.X ^ (-k)).intDegree = 1 := by
    rw [rational_monomial_degree ξ hξ (-k), ← Int.isCoprime_iff_gcd_eq_one]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr hcop).neg_right
  apply Polynomial.Monic.irreducible_of_irreducible_map fractionToRational q
    ((Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt hm)).map (algebraMap D K))
  rw [hmap]
  exact KhetanBinomialIrreducibility.X_pow_sub_C_irreducible_of_intDegree_coprime
    _ ha m hm hdegree

private theorem localize_binomial (s k : ℤ) (ξ : ℂ) :
    localizeCoefficients (binomial s k ξ) = monomial s k - scalar ξ := by
  change (AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K))
    (AddMonoidAlgebra.single s (LaurentPolynomial.T k) -
      AddMonoidAlgebra.single 0 (LaurentPolynomial.C ξ)) = _
  rw [map_sub, AddMonoidAlgebra.mapRingHom_single,
    AddMonoidAlgebra.mapRingHom_single]
  rfl

/-- The geometric exclusion supplies the missing coprimality for every
primitive binomial of positive transverse exponent. Neither irreducibility
nor coprimality is a premise. -/
private theorem positive_primitive_binomial_coprime
    (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (hline : OnlyLineDirection P u) (m : ℕ) (hm : 0 < m) (k : ℤ)
    (hcop : Int.gcd (m : ℤ) k = 1) (ξ : ℂ) (hξ : ξ ≠ 0) :
    IsCoprime (localized u hu P) (monomial m k - scalar ξ) := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow
    (primitiveLaurentCoordinates u hu P)
  have hnot : ¬ (monicBinomial m k ξ).map (algebraMap D K) ∣
      p.map (algebraMap D K) := by
    intro hdiv
    let v := (primitiveCoordinates u hu).symm ((m : ℤ), k)
    have hv : v ≠ 0 := by
      intro hz
      have he := congrArg (fun z => (primitiveCoordinates u hu z).1) hz
      have hmz : (m : ℤ) = 0 := by simpa [v] using he
      exact (Nat.ne_of_gt hm) (Int.natCast_eq_zero.mp hmz)
    have hd := line_divisor_of_monic_binomial_dvd P u hu m hm k ξ n p hp hdiv
    have hpar := hline v (LaurentPolynomial.T 1 - LaurentPolynomial.C ξ) hv
      (line_binomial_ne_zero ξ) (line_binomial_not_isUnit ξ hξ) hd
    have hfst : (primitiveCoordinates u hu v).1 = (m : ℤ) := by simp [v]
    rw [coordinates_fst, hpar] at hfst
    exact (Nat.ne_of_gt hm) (Int.natCast_eq_zero.mp hfst.symm)
  have hpoly : IsCoprime (p.map (algebraMap D K))
      ((monicBinomial m k ξ).map (algebraMap D K)) :=
    ((monic_binomial_irreducible m hm k hcop ξ hξ).coprime_iff_not_dvd.mpr hnot).symm
  have h := hpoly.map Polynomial.toLaurent
  rw [← map_toLaurent, hp, map_mul, ← map_toLaurent,
    monic_binomial_laurent, map_mul, localize_binomial] at h
  exact h.of_mul_left_left.of_mul_right_right

private theorem monomial_pow (s k : ℤ) (n : ℕ) :
    monomial s k ^ n = monomial ((n : ℤ) * s) ((n : ℤ) * k) := by
  simp only [monomial, AddMonoidAlgebra.single_pow, ← map_pow,
    LaurentPolynomial.T_pow, nsmul_eq_mul]

private theorem monomial_mul (s k t l : ℤ) :
    monomial s k * monomial t l = monomial (s + t) (k + l) := by
  simp only [monomial, AddMonoidAlgebra.single_mul_single, ← map_mul,
    ← LaurentPolynomial.T_add]

private theorem monomial_isUnit (s k : ℤ) : IsUnit (monomial s k) := by
  apply IsUnit.of_mul_eq_one (monomial (-s) (-k))
  rw [monomial_mul, add_neg_cancel, add_neg_cancel]
  simp [monomial, LaurentPolynomial.T_zero]

private theorem coordinate_difference_neg (s k : ℤ) :
    monomial s k - (1 : LaurentPolynomial K) =
      -(monomial s k * (monomial (-s) (-k) - 1)) := by
  rw [mul_sub, monomial_mul, add_neg_cancel, add_neg_cancel]
  simp [monomial, LaurentPolynomial.T_zero]

/-- Splitting the scalar polynomial first handles every multiplicity of a
primitive lattice direction, including repeated and composite factors. -/
private theorem positive_coordinate_difference_coprime
    (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (hline : OnlyLineDirection P u) (s k : ℤ) (hs : 0 < s) :
    IsCoprime (localized u hu P) (monomial s k - 1) := by
  have hg : 0 < Int.gcd s k := Int.gcd_pos_of_ne_zero_left k (ne_of_gt hs)
  obtain ⟨s₀, k₀, hprimitive, hs₀, hk₀⟩ := Int.exists_gcd_one hg
  let d := Int.gcd s k
  have hd : 0 < (d : ℤ) := by exact_mod_cast hg
  have hspos : 0 < s₀ :=
    pos_of_mul_pos_left (hs₀ ▸ hs) (le_of_lt hd)
  let m := s₀.toNat
  have hmcast : (m : ℤ) = s₀ := Int.toNat_of_nonneg (le_of_lt hspos)
  have hm : 0 < m := by
    have h : 0 < (m : ℤ) := by rw [hmcast]; exact hspos
    exact_mod_cast h
  have hmk : Int.gcd (m : ℤ) k₀ = 1 := by simpa only [hmcast] using hprimitive
  let f : Polynomial ℂ := Polynomial.X ^ d - 1
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_one (Nat.ne_of_gt hg)
  have hf : f = (f.roots.map (fun ξ => Polynomial.X - Polynomial.C ξ)).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hfmonic
  let ev : Polynomial ℂ →+* LaurentPolynomial K :=
    Polynomial.eval₂RingHom scalar (monomial m k₀)
  have hfactor : monomial s k - (1 : LaurentPolynomial K) =
      (f.roots.map (fun ξ => monomial m k₀ - scalar ξ)).prod := by
    have he := congrArg ev hf
    rw [map_multiset_prod] at he
    have hsd : (d : ℤ) * (m : ℤ) = s := by rw [hmcast, mul_comm]; exact hs₀.symm
    have hkd : (d : ℤ) * k₀ = k := by rw [mul_comm]; exact hk₀.symm
    simpa only [ev, f, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one,
      Multiset.map_map, Function.comp_def, Polynomial.eval₂_C, monomial_pow, hsd, hkd] using he
  have hroot (ξ : ℂ) (hξ : ξ ∈ f.roots) : ξ ≠ 0 := by
    intro hz
    have he := Polynomial.isRoot_of_mem_roots hξ
    simp [Polynomial.IsRoot, f, hz, show d ≠ 0 from Nat.ne_of_gt hg] at he
  rw [hfactor]
  have hall : ∀ ξ ∈ f.roots,
      IsCoprime (localized u hu P) (monomial m k₀ - scalar ξ) := by
    intro ξ hξ
    exact positive_primitive_binomial_coprime P u hu hline m hm k₀ hmk ξ (hroot ξ hξ)
  have hprod : ∀ roots : Multiset ℂ,
      (∀ ξ ∈ roots, IsCoprime (localized u hu P) (monomial m k₀ - scalar ξ)) →
        IsCoprime (localized u hu P)
          (roots.map (fun ξ => monomial m k₀ - scalar ξ)).prod := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty => intro _; simpa using (isCoprime_one_right (x := localized u hu P))
    | cons ξ roots ih =>
      intro hr
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (hr ξ (Multiset.mem_cons_self _ _)).mul_right
        (ih (fun μ hμ => hr μ (Multiset.mem_cons_of_mem hμ)))
  exact hprod _ hall

/-- An actual geometric restriction on line divisors implies coprimality with
every transverse difference after localization along the primitive direction. -/
theorem transverse_difference_coprime
    (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (hline : OnlyLineDirection P u) (v : Lattice)
    (hv : u.1 * v.2 - u.2 * v.1 ≠ 0) :
    IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K)
        (primitiveLaurentCoordinates u hu P))
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K)
        (primitiveLaurentCoordinates u hu (differenceFilter v))) := by
  let s := (primitiveCoordinates u hu v).1
  let k := (primitiveCoordinates u hu v).2
  have hs : s ≠ 0 := by simpa only [s, coordinates_fst] using hv
  have he : localized u hu (differenceFilter v) = monomial s k - 1 := by
    change localizeCoefficients (primitiveLaurentCoordinates u hu
      (AddMonoidAlgebra.single v 1 - 1)) = _
    rw [map_sub, map_one, coordinates_single]
    simp only [localizeCoefficients, map_sub, map_one,
      AddMonoidAlgebra.mapRingHom_single]
    rfl
  change IsCoprime (localized u hu P) (localized u hu (differenceFilter v))
  rw [he]
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hc := positive_coordinate_difference_coprime P u hu hline (-s) (-k) (by omega)
    rw [coordinate_difference_neg]
    apply IsCoprime.neg_right
    exact (isCoprime_mul_unit_left_right (monomial_isUnit s k) _ _).mpr hc
  · exact positive_coordinate_difference_coprime P u hu hline s k hpos

/-- All transverse supplier factors can be combined without a pairwise
nonparallel or squarefree hypothesis. -/
theorem transverse_product_coprime
    (P : AddMonoidAlgebra ℂ Lattice) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (hline : OnlyLineDirection P u) (transverse : List Lattice)
    (ht : ∀ v ∈ transverse, u.1 * v.2 - u.2 * v.1 ≠ 0) :
    IsCoprime
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K)
        (primitiveLaurentCoordinates u hu P))
      (AddMonoidAlgebra.mapRingHom ℤ (algebraMap D K)
        (primitiveLaurentCoordinates u hu
          ((transverse.map (fun v =>
            (differenceFilter v : AddMonoidAlgebra ℂ Lattice))).prod))) := by
  change IsCoprime (localized u hu P)
    (localized u hu ((transverse.map (fun v =>
      (differenceFilter v : AddMonoidAlgebra ℂ Lattice))).prod))
  revert ht
  induction transverse with
  | nil =>
    intro _
    simp only [List.map_nil, List.prod_nil, map_one]
    exact isCoprime_one_right
  | cons v vs ih =>
    intro ht
    simp only [List.map_cons, List.prod_cons, map_mul]
    exact (transverse_difference_coprime P u hu hline v (ht v (by simp))).mul_right
      (ih (fun w hw => ht w (by simp [hw])))

/-- A line-factor restriction now feeds the cleared Bezout action on the
original configuration; localized coprimality is proved internally. -/
theorem one_direction_periodic
    (h : Configuration ℂ) (hh : FiniteRange h) (u : Lattice) (hu : IsCoprime u.1 u.2)
    (P : AddMonoidAlgebra ℂ Lattice) (hline : OnlyLineDirection P u)
    (A : LaurentPolynomial ℂ) (hA : A ≠ 0) (transverse : List Lattice)
    (ht : ∀ v ∈ transverse, u.1 * v.2 - u.2 * v.1 ≠ 0)
    (c : ℂ) (hP : coefficientAct P h = fun _ => c)
    (hann : coefficientAct (lineLaurent u A *
      (transverse.map (fun v => (differenceFilter v : AddMonoidAlgebra ℂ Lattice))).prod) h = 0) :
    Periodic h := by
  let coordinates := primitiveLaurentCoordinates (R := ℂ) u hu
  let B := (transverse.map (fun v =>
    (differenceFilter v : AddMonoidAlgebra ℂ Lattice))).prod
  have hcu : primitiveCoordinates u hu u = (0, 1) := by
    apply Prod.ext
    · change u.1 * u.2 - u.2 * u.1 = 0
      ring
    · exact Classical.choose_spec (Classical.choose_spec hu)
  have hc_line (F : LaurentPolynomial ℂ) :
      coordinates (lineLaurent u F) = AddMonoidAlgebra.single 0 F := by
    induction F using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add F G hF hG => simp only [map_add, hF, hG, AddMonoidAlgebra.single_add]
    | single n a =>
      change primitiveLaurentCoordinates u hu (lineLaurent u
        (AddMonoidAlgebra.single n a)) = _
      rw [line_laurent_single, coordinates_single]
      have hcoord : primitiveCoordinates u hu (n • u) = (0, n) := by
        rw [map_zsmul, hcu]
        simp
      simp only [hcoord, Prod.fst, Prod.snd]
  have hunz : u ≠ 0 := by
    intro hz
    have he := hcu
    have he' := congrArg Prod.snd he
    simp [hz] at he'
  obtain ⟨ρ, hρ, α, β, hbezout⟩ := KhetanLaurentElimination.clear_laurent_bezout
    (K := K) (coordinates P) (coordinates B)
    (transverse_product_coprime P u hu hline transverse ht)
  apply cleared_bezout_periodic h hh u hunz P B (coordinates.symm α)
    (coordinates.symm β) A ρ hA hρ c hP hann
  apply coordinates.injective
  rw [hc_line]
  simpa only [map_add, map_mul, RingEquiv.apply_symm_apply] using hbezout

/-- The complete one-direction periodizer implication for finite-range integer
configurations. Product differences are supplied from the periodizer of this
same configuration; its complex Laurent line factors are the only geometric
hypothesis. The conclusion is an actual period of the given configuration. -/
theorem integer_one_direction_periodizer_periodic
    (h : Configuration ℤ) (hh : FiniteRange h)
    (P : IntegerLaurent) (hPne : P ≠ 0) (c : ℤ)
    (hP : coefficientAct P h = fun _ => c)
    (u : Lattice) (hu : IsCoprime u.1 u.2)
    (hline : OnlyLineDirection
      (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) P) u) :
    Periodic h := by
  obtain ⟨A, transverse, hA, ht, _, hann⟩ :=
    integer_periodizer_direction_split (R := ℂ) h hh P hPne c hP u hu
  have hPcomplex : coefficientAct
      (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) P)
      (Int.castRingHom ℂ ∘ h) = fun _ => (c : ℂ) := by
    rw [coefficientAct_map, hP] <;> rfl
  have hc := one_direction_periodic (Int.castRingHom ℂ ∘ h)
    (hh.map (Int.castRingHom ℂ)) u hu
    (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℂ) P)
    hline A hA transverse ht (c : ℂ) hPcomplex hann
  exact (periodic_map_iff h (f := Int.castRingHom ℂ)
    (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)).mp hc

end D5.S1.Dynamics.Symbolic.KhetanDirectionalCoprimality
