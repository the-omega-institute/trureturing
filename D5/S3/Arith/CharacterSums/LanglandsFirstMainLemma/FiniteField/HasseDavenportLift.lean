/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Exact upstream Hasse–Davenport lift theorem in Langlands normalization. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.CharacterAPI
import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.EulerProduct
import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.LocalField.Extension

/-!
# Hasse--Davenport lifting in Langlands's normalization

For the monic-polynomial weight

`w(P) = χ ((-1)^deg(P) * P(0)) * ψ (-P.nextCoeff)`,

this file identifies the degree-`f` closed-point power sum with the Gauss sum over a
degree-`f` finite extension.  The identification is performed on the quotient of extension-field
elements by conjugacy: every quotient class has one monic irreducible minimal polynomial, its
carrier has cardinality equal to that polynomial's degree, and its trace and norm give exactly
the corresponding polynomial weight.

The reusable Euler-product theorem then yields the ordinary signed power identity.  Applying it
to `χ⁻¹` and using `τ(χ, ψ) = -G(χ⁻¹, ψ)` proves the lift formula with no residual parity sign.
The argument includes the trivial multiplicative character and uses nontriviality only for the
additive character.
-/

open Polynomial
open scoped BigOperators

namespace LanglandsFirstMainLemma

noncomputable section

universe u v

/-- A monic irreducible whose degree divides `r`. -/
structure IrreducibleDivisorPolynomial (k : Type u) [Field k] (r : ℕ) where
  poly : k[X]
  monic : poly.Monic
  irreducible : Irreducible poly
  degree_mem_divisors : poly.natDegree ∈ r.divisors

namespace IrreducibleDivisorPolynomial

variable {k : Type u} [Field k] {r : ℕ}

@[ext]
theorem ext {P Q : IrreducibleDivisorPolynomial k r} (h : P.poly = Q.poly) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

noncomputable def divisorPrimeEquiv :
    IrreducibleDivisorPolynomial k r ≃ MonicWeight.DivisorPrimeIndex k r where
  toFun P :=
    ⟨⟨P.poly.natDegree, P.degree_mem_divisors⟩,
      ⟨⟨P.poly, P.monic, rfl⟩, P.irreducible⟩⟩
  invFun P := by
    rcases P with ⟨⟨d, hd⟩, ⟨⟨p, hpmonic, hpdeg⟩, hpirr⟩⟩
    change p.natDegree = d at hpdeg
    exact ⟨p, hpmonic, hpirr, by simpa only [hpdeg] using hd⟩
  left_inv P := by ext; rfl
  right_inv P := by
    rcases P with ⟨⟨d, hd⟩, ⟨⟨p, hpmonic, hpdeg⟩, hpirr⟩⟩
    change p.natDegree = d at hpdeg
    subst d
    rfl

noncomputable instance [Fintype k] : Fintype (IrreducibleDivisorPolynomial k r) :=
  Fintype.ofEquiv _ divisorPrimeEquiv.symm

end IrreducibleDivisorPolynomial

section ClosedPoints

variable (k : Type u) (K : Type v)
  [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]

noncomputable def conjugacyClassIrreducibleDivisorPolynomial
    (c : ConjRootClass k K) :
    IrreducibleDivisorPolynomial k (Module.finrank k K) :=
  ⟨c.minpoly, c.monic_minpoly, c.irreducible_minpoly,
    Nat.mem_divisors.mpr
      ⟨c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly,
        Module.finrank_pos.ne'⟩⟩

omit [Fintype k] in
theorem conjugacyClassIrreducibleDivisorPolynomial_injective :
    Function.Injective (conjugacyClassIrreducibleDivisorPolynomial k K) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg IrreducibleDivisorPolynomial.poly h

omit [Fintype k] in
theorem conjugacyClassIrreducibleDivisorPolynomial_surjective :
    Function.Surjective (conjugacyClassIrreducibleDivisorPolynomial k K) := by
  rintro ⟨p, hpmonic, hpirr, hd⟩
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  letI : Fact (Irreducible p) := ⟨hpirr⟩
  have hfinrank : Module.finrank k (AdjoinRoot p) = p.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hp0),
      AdjoinRoot.powerBasis_dim hp0]
  have hdvd : Module.finrank k (AdjoinRoot p) ∣ Module.finrank k K := by
    rw [hfinrank]
    exact (Nat.mem_divisors.mp hd).1
  let ι : AdjoinRoot p →ₐ[k] K :=
    Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd hdvd)
  let x : K := ι (AdjoinRoot.root p)
  have hroot : aeval x p = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero p ι
  have hminpoly : p = minpoly k x :=
    minpoly.eq_of_irreducible_of_monic hpirr hroot hpmonic
  refine ⟨ConjRootClass.mk k x, ?_⟩
  apply IrreducibleDivisorPolynomial.ext
  exact hminpoly.symm

noncomputable def conjugacyClassIrreducibleDivisorPolynomialEquiv :
    ConjRootClass k K ≃
      IrreducibleDivisorPolynomial k (Module.finrank k K) :=
  Equiv.ofBijective (conjugacyClassIrreducibleDivisorPolynomial k K)
    ⟨conjugacyClassIrreducibleDivisorPolynomial_injective k K,
      conjugacyClassIrreducibleDivisorPolynomial_surjective k K⟩

noncomputable def conjugacyClassDivisorPrimeEquiv :
    ConjRootClass k K ≃ MonicWeight.DivisorPrimeIndex k (Module.finrank k K) :=
  (conjugacyClassIrreducibleDivisorPolynomialEquiv k K).trans
    IrreducibleDivisorPolynomial.divisorPrimeEquiv

noncomputable local instance conjugacyClassFintype : Fintype (ConjRootClass k K) := by
  classical
  exact Fintype.ofSurjective (ConjRootClass.mk k) fun c ↦ by
    induction c with
    | h x => exact ⟨x, rfl⟩

noncomputable local instance conjugacyClassCarrierFintype
    (c : ConjRootClass k K) : Fintype c.carrier := by
  classical
  change Fintype {x : K // ConjRootClass.mk k x = c}
  infer_instance

def conjugacyClassCarrierEquivFiber (c : ConjRootClass k K) :
    c.carrier ≃ {x : K // ConjRootClass.mk k x = c} where
  toFun x := ⟨x.1, ConjRootClass.mem_carrier.mp x.2⟩
  invFun x := ⟨x.1, ConjRootClass.mem_carrier.mpr x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

theorem conjugacyClass_carrier_card (c : ConjRootClass k K) :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  classical
  calc
    Fintype.card c.carrier = c.carrier.toFinset.card :=
      (Set.toFinset_card c.carrier).symm
    _ = (c.minpoly.aroots K).card := by
      rw [ConjRootClass.carrier_eq_mk_aroots_minpoly]
      rfl
    _ = c.minpoly.natDegree := by
      rw [Polynomial.aroots_def,
        ← c.splits_minpoly.natDegree_eq_card_roots,
        Polynomial.natDegree_map]

omit [Fintype k] in
/-- The trace and norm of an element convert its minimal-polynomial weight into the lifted
Gauss-sum summand, with the tower degree as exponent. -/
theorem gaussPolynomialWeight_minpoly_power
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (x : K) :
    gaussPolynomialWeight χ ψ
        ⟨minpoly k x, minpoly.monic (Algebra.IsIntegral.isIntegral x)⟩ ^
          Module.finrank (↥(IntermediateField.adjoin k ({x} : Set K))) K =
      normMulChar k K χ x * traceAddChar k K ψ x := by
  let e := Module.finrank (↥(IntermediateField.adjoin k ({x} : Set K))) K
  let p := minpoly k x
  have hx : IsIntegral k x := Algebra.IsIntegral.isIntegral x
  have hnormBase :
      Algebra.norm k (IntermediateField.AdjoinSimple.gen k x) =
        (-1 : k) ^ p.natDegree * p.coeff 0 := by
    rw [← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
      IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.minpoly_gen]
  change (χ ((-1 : k) ^ p.natDegree * p.coeff 0) * ψ (-p.nextCoeff)) ^ e =
    χ (Algebra.norm k x) * ψ (Algebra.trace k K x)
  rw [Algebra.norm_eq_norm_adjoin, hnormBase, map_pow,
    trace_eq_finrank_mul_minpoly_nextCoeff k x, ← nsmul_eq_mul,
    AddChar.map_nsmul_eq_pow, mul_pow]

theorem sum_divisorPrimeIndex_eq_closedPointPowerSum
    (w : MonicWeight k ℂ) (r : ℕ) :
    (∑ x : MonicWeight.DivisorPrimeIndex k r,
        (x.1.1 : ℂ) * MonicWeight.exactPrimeWeight k w x.2 ^ (r / x.1.1)) =
      MonicWeight.closedPointPowerSum w r := by
  classical
  rw [Fintype.sum_sigma]
  unfold MonicWeight.closedPointPowerSum
  rw [show (Finset.univ : Finset {e : ℕ // e ∈ r.divisors}) =
      r.divisors.attach from Finset.univ_eq_attach _]
  calc
    (∑ e ∈ r.divisors.attach,
        ∑ p : MonicIrreducibleOfDegree k e.1,
          (e.1 : ℂ) * MonicWeight.exactPrimeWeight k w p ^ (r / e.1)) =
      ∑ e ∈ r.divisors,
        ∑ p : MonicIrreducibleOfDegree k e,
          (e : ℂ) * MonicWeight.exactPrimeWeight k w p ^ (r / e) :=
      Finset.sum_attach r.divisors (fun e ↦
        ∑ p : MonicIrreducibleOfDegree k e,
          (e : ℂ) * MonicWeight.exactPrimeWeight k w p ^ (r / e))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]

noncomputable def conjugacyClassGaussTerm
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (c : ConjRootClass k K) : ℂ :=
  (c.minpoly.natDegree : ℂ) *
    gaussPolynomialWeight χ ψ ⟨c.minpoly, c.monic_minpoly⟩ ^
      (Module.finrank k K / c.minpoly.natDegree)

theorem conjugacyClassGaussTerm_eq_sum_carrier
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (c : ConjRootClass k K) :
    conjugacyClassGaussTerm k K χ ψ c =
      ∑ x : c.carrier, normMulChar k K χ x.1 * traceAddChar k K ψ x.1 := by
  classical
  let A := gaussPolynomialWeight χ ψ ⟨c.minpoly, c.monic_minpoly⟩ ^
    (Module.finrank k K / c.minpoly.natDegree)
  have hcard : Fintype.card c.carrier = c.minpoly.natDegree :=
    conjugacyClass_carrier_card k K c
  calc
    conjugacyClassGaussTerm k K χ ψ c = c.minpoly.natDegree • A := by
      simp [conjugacyClassGaussTerm, A, nsmul_eq_mul]
    _ = ∑ _x : c.carrier, A := by simp [hcard]
    _ = ∑ x : c.carrier,
        normMulChar k K χ x.1 * traceAddChar k K ψ x.1 := by
      apply Fintype.sum_congr
      intro x
      have hx : IsIntegral k x.1 := Algebra.IsIntegral.isIntegral x.1
      have hmk : ConjRootClass.mk k x.1 = c :=
        ConjRootClass.mem_carrier.mp x.2
      have hminpoly : minpoly k x.1 = c.minpoly := by
        simpa using congrArg ConjRootClass.minpoly hmk
      have hexp :
          Module.finrank k K / c.minpoly.natDegree =
            Module.finrank
              (↥(IntermediateField.adjoin k ({x.1} : Set K))) K := by
        rw [← hminpoly, ← IntermediateField.adjoin.finrank hx,
          ← Module.finrank_mul_finrank k
            (↥(IntermediateField.adjoin k ({x.1} : Set K))) K,
          Nat.mul_div_right _ Module.finrank_pos]
      simpa [A, hminpoly, hexp] using
        gaussPolynomialWeight_minpoly_power k K χ ψ x.1

/-- The degree of the extension turns the closed-point power sum of the Gauss weight into the
ordinary Gauss sum of the norm and trace pullbacks. -/
theorem gaussPolynomialWeight_closedPointPowerSum
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) :
    MonicWeight.closedPointPowerSum (gaussPolynomialWeight χ ψ)
        (Module.finrank k K) =
      gaussSum (normMulChar k K χ) (traceAddChar k K ψ) := by
  classical
  let w := gaussPolynomialWeight χ ψ
  let term : MonicWeight.DivisorPrimeIndex k (Module.finrank k K) → ℂ :=
    fun x ↦ (x.1.1 : ℂ) * MonicWeight.exactPrimeWeight k w x.2 ^
      (Module.finrank k K / x.1.1)
  let lifted : K → ℂ := fun x ↦
    normMulChar k K χ x * traceAddChar k K ψ x
  calc
    MonicWeight.closedPointPowerSum w (Module.finrank k K) =
        ∑ x : MonicWeight.DivisorPrimeIndex k (Module.finrank k K), term x := by
      exact (sum_divisorPrimeIndex_eq_closedPointPowerSum k w
        (Module.finrank k K)).symm
    _ = ∑ c : ConjRootClass k K, conjugacyClassGaussTerm k K χ ψ c := by
      symm
      apply Fintype.sum_equiv (conjugacyClassDivisorPrimeEquiv k K)
      intro c
      rfl
    _ = ∑ c : ConjRootClass k K, ∑ x : c.carrier, lifted x.1 := by
      apply Fintype.sum_congr
      intro c
      exact conjugacyClassGaussTerm_eq_sum_carrier k K χ ψ c
    _ = ∑ c : ConjRootClass k K,
        ∑ x : {x : K // ConjRootClass.mk k x = c}, lifted x.1 := by
      apply Fintype.sum_congr
      intro c
      apply Fintype.sum_equiv (conjugacyClassCarrierEquivFiber k K c)
      intro x
      rfl
    _ = ∑ x : K, lifted x :=
      Fintype.sum_fiberwise (ConjRootClass.mk k) lifted
    _ = gaussSum (normMulChar k K χ) (traceAddChar k K ψ) := by
      rfl

end ClosedPoints

section DegreeSums

variable {k : Type u} [Field k] [Fintype k]

noncomputable def monicCoefficientEquiv (n : ℕ) :
    MonicPolynomialOfDegree k n ≃ (Fin n → k) :=
  (Polynomial.monicEquivDegreeLT n).trans
    (Polynomial.degreeLTEquiv k n).toEquiv

omit [Fintype k] in
@[simp]
theorem monicCoefficientEquiv_apply (n : ℕ) (p : MonicPolynomialOfDegree k n)
    (i : Fin n) :
    monicCoefficientEquiv n p i = p.1.coeff i := by
  change p.1.eraseLead.coeff i = p.1.coeff i
  rw [Polynomial.eraseLead_coeff_of_ne]
  intro h
  rw [p.2.2] at h
  exact i.isLt.ne h

def translateFunctionAt {n : ℕ} (i : Fin n) (t : k) :
    (Fin n → k) ≃ (Fin n → k) where
  toFun f j := if j = i then f j + t else f j
  invFun f j := if j = i then f j - t else f j
  left_inv f := by
    funext j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  right_inv f := by
    funext j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]

omit [Fintype k] in
@[simp]
theorem translateFunctionAt_same {n : ℕ} (i : Fin n) (t : k) (f : Fin n → k) :
    translateFunctionAt i t f i = f i + t := by
  simp [translateFunctionAt]

omit [Fintype k] in
@[simp]
theorem translateFunctionAt_of_ne {n : ℕ} (i j : Fin n) (t : k) (f : Fin n → k)
    (hji : j ≠ i) :
    translateFunctionAt i t f j = f j := by
  simp [translateFunctionAt, hji]

noncomputable def linearMonicEquiv : MonicPolynomialOfDegree k 1 ≃ k where
  toFun p := -p.1.coeff 0
  invFun x := ⟨X - C x, monic_X_sub_C x, natDegree_X_sub_C x⟩
  left_inv p := by
    apply Subtype.ext
    apply Polynomial.ext
    intro i
    by_cases hi0 : i = 0
    · subst i
      simp
    by_cases hi1 : i = 1
    · subst i
      have hp := p.2.1.coeff_natDegree
      rw [p.2.2] at hp
      simpa using hp.symm
    · have hip : p.1.coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simpa [p.2.2] using Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hi0, hi1⟩
      rw [coeff_sub, coeff_X_of_ne_one hi1, coeff_C, if_neg hi0, hip]
      simp
  right_inv x := by simp

/-- The linear coefficient of the Gauss polynomial Euler product is the ordinary Gauss sum. -/
theorem gaussPolynomialWeight_degreeSum_one
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) :
    MonicWeight.degreeSum (gaussPolynomialWeight χ ψ) 1 = gaussSum χ ψ := by
  classical
  rw [MonicWeight.degreeSum]
  calc
    (∑ p : MonicPolynomialOfDegree k 1,
        gaussPolynomialWeight χ ψ
          (⟨p.1, by change p.1.Monic; exact p.2.1⟩ : MonicPolynomial k)) =
        ∑ p : MonicPolynomialOfDegree k 1,
          χ (linearMonicEquiv p) * ψ (linearMonicEquiv p) := by
      apply Fintype.sum_congr
      intro p
      simp [linearMonicEquiv, gaussPolynomialWeight_apply,
        Polynomial.nextCoeff_of_natDegree_pos, p.2.2]
    _ = ∑ x : k, χ x * ψ x :=
      (linearMonicEquiv (k := k)).sum_comp (fun x : k ↦ χ x * ψ x)
    _ = gaussSum χ ψ := rfl

/-- For a nontrivial additive character, all Gauss polynomial degree sums from degree two on
vanish by translation of the freely varying next coefficient. -/
theorem gaussPolynomialWeight_degreeSum_eq_zero
    (χ : FiniteMulChar k) {ψ : FiniteAddChar k} (hψ : ψ ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    MonicWeight.degreeSum (gaussPolynomialWeight χ ψ) n = 0 := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have hi_ne : i0 ≠ ilast := by
    intro h
    have := congrArg Fin.val h
    dsimp [i0, ilast] at this
    omega
  let weight : (Fin n → k) → ℂ := fun f ↦
    χ ((-1 : k) ^ n * f i0) * ψ (-f ilast)
  have hdegreeSum :
      MonicWeight.degreeSum (gaussPolynomialWeight χ ψ) n = ∑ f, weight f := by
    rw [MonicWeight.degreeSum]
    calc
      (∑ p : MonicPolynomialOfDegree k n,
          gaussPolynomialWeight χ ψ
            (⟨p.1, by change p.1.Monic; exact p.2.1⟩ : MonicPolynomial k)) =
          ∑ p : MonicPolynomialOfDegree k n, weight (monicCoefficientEquiv n p) := by
        apply Fintype.sum_congr
        intro p
        change
          χ ((-1 : k) ^ p.1.natDegree * p.1.coeff 0) * ψ (-p.1.nextCoeff) =
            χ ((-1 : k) ^ n * monicCoefficientEquiv n p i0) *
              ψ (-monicCoefficientEquiv n p ilast)
        rw [Polynomial.nextCoeff_of_natDegree_pos (by omega)]
        rw [p.2.2]
        rw [show n - 1 = (ilast : ℕ) by rfl]
        rw [monicCoefficientEquiv_apply, monicCoefficientEquiv_apply]
      _ = ∑ f : Fin n → k, weight f :=
        (monicCoefficientEquiv (k := k) n).sum_comp weight
  obtain ⟨t, ht⟩ : ∃ t : k, ψ (-t) ≠ 1 := by
    by_contra h
    push Not at h
    apply hψ
    ext x
    have hx := h (-x)
    simpa using hx
  let e := translateFunctionAt ilast t
  have hweight (f : Fin n → k) : weight (e f) = ψ (-t) * weight f := by
    change
      χ ((-1 : k) ^ n * e f i0) * ψ (-(e f ilast)) =
        ψ (-t) * (χ ((-1 : k) ^ n * f i0) * ψ (-f ilast))
    rw [translateFunctionAt_of_ne ilast i0 t f hi_ne,
      translateFunctionAt_same]
    rw [show -(f ilast + t) = -t + -f ilast by ring]
    rw [ψ.map_add_eq_mul]
    ring
  rw [hdegreeSum]
  have hsum : (∑ f, weight f) = ψ (-t) * ∑ f, weight f := by
    calc
      (∑ f, weight f) = ∑ f, weight (e f) := (e.sum_comp weight).symm
      _ = ∑ f, ψ (-t) * weight f := by
        apply Fintype.sum_congr
        exact hweight
      _ = ψ (-t) * ∑ f, weight f := by rw [Finset.mul_sum]
  have hzero : (1 - ψ (-t)) * (∑ f, weight f) = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hsum
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ht.symm)

end DegreeSums

section Lift

variable {k : Type u} {K : Type v}
  [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]

/-- Hasse--Davenport lifting for Langlands-normalized Gauss sums.  The inverse-character and
leading minus sign are part of `langlandsGaussSum`; the Euler-product signs cancel for every
extension degree, including even degree. -/
theorem hasseDavenportLift
    (χ : FiniteMulChar k) (ψ : FiniteAddChar k) (hψ : ψ ≠ 1) :
    langlandsGaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
      langlandsGaussSum χ ψ ^ Module.finrank k K := by
  let w := gaussPolynomialWeight χ⁻¹ ψ
  have hpower := closedPoint_power_identity w
    (gaussPolynomialWeight_degreeSum_eq_zero χ⁻¹ hψ)
    (Module.finrank k K) Module.finrank_pos
  rw [gaussPolynomialWeight_closedPointPowerSum k K χ⁻¹ ψ,
    gaussPolynomialWeight_degreeSum_one] at hpower
  rw [langlandsGaussSum, langlandsGaussSum,
    ← normMulChar_inv k K χ]
  exact hpower

end Lift

end

end LanglandsFirstMainLemma
