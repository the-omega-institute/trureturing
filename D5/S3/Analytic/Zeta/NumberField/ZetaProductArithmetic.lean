/- GID: D5/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/NumberField/ZetaProductArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime ideals of norm coprime to a cyclotomic modulus are unramified. -/
module

public import D5.S3.Factorization.Galois.Chebotarev.Frobenius
public import D5.S3.Factorization.Galois.Chebotarev.CyclotomicNormResidue
public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCount
public import D5.S3.Arith.Lattices.Counting.LatticePointCount
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Zeta factorisation for an abelian extension

For an abelian Galois extension `L/K` of number fields, the Dedekind zeta
function `ζ_L(s)` factors as a product of Artin L-functions over the
characters of `Gal(L/K)`:

  ζ_L(s) = ∏_{χ : Gal(L/K) → ℂ^×} L(χ, s)   on Re s > 1.

The character `χ` is extended to a character on nonzero ideals of `𝓞 K` by
`χ(𝔭) = χ(σ_𝔭)` for `𝔭` unramified in `L`, and `0` otherwise. The
nontrivial-`χ` L-function is holomorphic and nonvanishing on `Re s ≥ 1`
(Sharifi §7.1.19); the trivial-character L-function is `ζ_K(s)`.

This factorisation is the analytic engine of the Chebotarev proof for the
cyclotomic case.

This file does **not** introduce a top-level `artinLSeries` definition —
the L-functions enter the argument only via existence statements packaged
as the theorems below, with the Euler-product / Dirichlet-series content
of each `L(χ, ·)` being an internal detail of the proof of
`dedekindZeta_eq_prod_artinLSeries`. The user can read the proof to see
how each `L(χ, ·)` is constructed.

## Main results

* `Chebotarev.exists_artinLSeries_eulerProduct_abelian` — the Euler product
  `L(χ,s) = ∏_𝔭 (1 - χ(𝔭) N𝔭⁻ˢ)⁻¹ = Σ_𝔞 χ(𝔞) N𝔞⁻ˢ` of an abelian character
  (Sharifi 7.1.18), with `χ(𝔞)` the multiplicative `galoisCharacterOnIdeal`.
* `Chebotarev.artinLSeries_one_ne_zero` — non-vanishing `L(χ,1) ≠ 0` for
  nontrivial `χ`, via the pole-order argument (Sharifi 7.1.19 step 2), modulo
  the geometry-of-numbers analytic extension `artinLSeries_analytic_extension`.

## References

* Sharifi, *Algebraic Number Theory*, §7.1.15–7.1.19 (`docs/algnum.pdf`).
* The analogous factorisation for the prime cyclotomic field `ℚ(μ_p)/ℚ`
  is available in `flt-regular-bernoulli`'s
  `BernoulliRegular.ZetaFactorisation.EulerProduct`; this module
  generalises it to an arbitrary abelian extension `L/K`.
-/

@[expose] public section

noncomputable section

open NumberField Classical

namespace Chebotarev

/-- A character of `Gal(L/K)` valued in `ℂ^×`. -/
abbrev galoisCharacter
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Type _ := Gal(L/K) →* ℂˣ

/-- The multiplicative extension of a Galois character `χ` to the nonzero ideals of `𝓞 K`
(Sharifi Notation 7.1.17): on a prime `𝔭` it is `χ(Frob 𝔭)` if `𝔭` is unramified in `L` and `0`
otherwise, extended completely multiplicatively via the prime factorisation. The L-function
coefficient `χ(𝔞)`. -/
noncomputable def galoisCharacterOnIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)) : ℂ :=
  ∏ 𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset,
    (if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0)
      ^ (UniqueFactorizationMonoid.normalizedFactors 𝔞).count 𝔭

/-! ### Sub-lemmas for `exists_dedekindZeta_factorisation`

Decomposed per Sharifi 7.1.16 (factorisation), 7.1.18 (abelian Euler
product), and 7.1.19 (analytic extension + non-vanishing). Each
sub-lemma is supported by a verbatim source quote in
`.mathlib-quality/chebotarev-decomposition.md`.

(i) Euler product for an abelian character (Sharifi 7.1.18, p. 141):
    `L(χ,s) = ∏_𝔭(1 - χ(𝔭) N𝔭^{-s})^{-1} = Σ_𝔞 χ(𝔞) N𝔞^{-s}` for `Re s > 1`.

(ii) Local Euler-factor decomposition at an unramified `𝔭`:
    `∏_{𝔓|𝔭}(1 - N𝔓^{-s})^{-1} = ∏_χ(1 - χ(σ_𝔭) N𝔭^{-s})^{-1}`. Standard
    identity from finite cyclic group theory applied to the residue
    Galois group.

(iii) Multiplicative assembly: combining (i) and (ii) over all unramified
    `𝔭` yields `ζ_L = ∏_χ L(χ, ·)` (Sharifi 7.1.16 in the abelian case).

(iv) Analytic extension via geometry of numbers (Sharifi 7.1.19 step 1,
    p. 142): `Σ_{N𝔞≤N} χ(𝔞) = O(N^{1-d^{-1}})` where `d = [K:ℚ]`. This
    gives convergence of `L(χ,·)` on `Z(1-d^{-1})` via Lemma 7.1.5.

(v) Non-vanishing `L(χ,1) ≠ 0` for nontrivial `χ` (Sharifi 7.1.19 step 2,
    p. 142): the bounded-function + vanishing-order contradiction
    argument.
-/

/-- Sharifi 7.1.18 (p. 141): Euler product for an abelian Galois
character `χ : Gal(L/K) → ℂ^×`. For `Re s > 1` the Euler product over unramified primes
equals the Dirichlet series `Σ_𝔞 χ(𝔞) N𝔞^{-s}`, where `χ(𝔞) = galoisCharacterOnIdeal K L χ 𝔞`
is the completely-multiplicative ideal character.

The proof instantiates the generic weighted prime-ideal Euler product
`weighted_eulerProduct_eq_tsum` with the weight `w = galoisCharacterOnIdeal K L χ`
(completely multiplicative with `‖w‖ ≤ 1`). The product on the left ranges over *unramified*
primes, whereas the weighted Euler product ranges over *all* nonzero primes; the two agree
because `w(𝔭) = 0` at a ramified prime, so its local factor `(1 - 0)⁻¹ = 1` drops out of the
product. At an unramified prime the normalized-factor computation gives `w(𝔭) = χ(Frob 𝔭)`. -/
theorem exists_artinLSeries_eulerProduct_abelian
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] [_hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L) :
    ∀ s : ℂ, 1 < s.re →
      (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
            galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  intro s hs
  set w : Ideal (𝓞 K) → ℂ := galoisCharacterOnIdeal K L χ with hw
  rw [← weighted_eulerProduct_eq_tsum K (s := s) hs w ((show ∀      
      (χ : galoisCharacter K L), galoisCharacterOnIdeal K L χ ⊤ = 1 from by
    intro χ
    rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count, ← Ideal.one_eq_top,
      UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]) χ)
    (fun {𝔞 𝔟} h𝔞 h𝔟 ↦ (show ∀      
        (χ : galoisCharacter K L) {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥), (galoisCharacterOnIdeal K L χ (𝔞 * 𝔟) = galoisCharacterOnIdeal K L χ 𝔞 * galoisCharacterOnIdeal K L χ 𝔟) from by
      intro χ 𝔞 𝔟 h𝔞 h𝔟
      classical
      rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
        galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
        galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
        UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟,
        Multiset.map_add, Multiset.prod_add]) χ h𝔞 h𝔟)
    ((show ∀      
        (χ : galoisCharacter K L) (𝔞 : Ideal (𝓞 K)), (‖galoisCharacterOnIdeal K L χ 𝔞‖ ≤ 1) from by
      intro χ 𝔞
      classical
      rw [galoisCharacterOnIdeal, norm_prod]
      refine Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) (fun 𝔭 _ ↦ ?_)
      rw [norm_pow]
      by_cases h : UnramifiedIn K L 𝔭
      · have hnorm : ‖(χ (frobeniusClass K L 𝔭).out : ℂ)‖ = 1 :=
          (((Units.coeHom ℂ).comp χ).isOfFinOrder
            (isOfFinOrder_of_finite (frobeniusClass K L 𝔭).out)).norm_eq_one
        rw [if_pos h, hnorm, one_pow]
      · rw [if_neg h, norm_zero]
        exact zero_pow_le_one _) χ)]
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} →
      {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := fun 𝔭 ↦ ⟨𝔭.1, 𝔭.2.1, 𝔭.2.2.1⟩ with hg
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ :=
    fun 𝔭 ↦ (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ with hf
  have hg_inj : Function.Injective g := fun _ _ hab ↦
    Subtype.ext (congrArg (fun x : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ x.1) hab)
  have hsupp : Function.mulSupport f ⊆ Set.range g := by
    intro 𝔭 hmem
    simp only [Function.mem_mulSupport, hf] at hmem
    haveI := 𝔭.2.1
    have hunr : UnramifiedIn K L 𝔭.1 := by
      by_contra hnr
      apply hmem
      rw [hw, (show ∀      
          (χ : galoisCharacter K L) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥), (galoisCharacterOnIdeal K L χ 𝔭 = if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0) from by
        intro χ 𝔭 cnrInstance0 h𝔭
        classical
        rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
          UniqueFactorizationMonoid.normalizedFactors_irreducible
          (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
          Multiset.prod_singleton]) χ 𝔭.1 𝔭.2.2, if_neg hnr, zero_mul, sub_zero,
        inv_one]
    exact ⟨⟨𝔭.1, 𝔭.2.1, hunr⟩, rfl⟩
  rw [← hg_inj.tprod_eq hsupp]
  refine tprod_congr fun 𝔭 ↦ ?_
  simp only [hf, hg, hw]
  haveI := 𝔭.2.1
  rw [(show ∀      
      (χ : galoisCharacter K L) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥), (galoisCharacterOnIdeal K L χ 𝔭 = if UnramifiedIn K L 𝔭 then (χ (frobeniusClass K L 𝔭).out : ℂ) else 0) from by
    intro χ 𝔭 cnrInstance0 h𝔭
    classical
    rw [galoisCharacterOnIdeal, ← Finset.prod_multiset_map_count,
      UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime h𝔭 ‹_›).irreducible, normalize_eq, Multiset.map_singleton,
      Multiset.prod_singleton]) χ 𝔭.1 𝔭.2.2.1, if_pos 𝔭.2.2]

/-! ### Sub-lemmas for `exists_card_galoisCharacterOnIdeal_eq_const_mul_add_pow` (leaf G)

The geometry-of-numbers bridge (Sharifi 7.1.19 step 1, p. 142).

For `L = K(μ_m)` cyclotomic, `galoisCharacterOnIdeal K L χ 𝔞 = χ(Frob_𝔞)` on
unramified-supported `𝔞` — i.e. on `𝔞` satisfying `U 𝔞 := ∀ 𝔭 ∈ normalizedFactors 𝔞,
UnramifiedIn K L 𝔭` — where `Frob_𝔞 ∈ Gal(L/K)` is the completely-multiplicative ideal Frobenius
(abelian, so a genuine group element, not just a conjugacy class). `U 𝔞` is the exact support
condition `χ(𝔞) ≠ 0`: a single ramified factor zeroes the product. Hence the value-fibre
`{𝔞 : χ(𝔞) = ζ}` (for `ζ ≠ 0`) equals the unramified-supported Frobenius-value-fibre
`{𝔞 : U 𝔞 ∧ χ(Frob_𝔞) = ζ}`, which in turn is a finite union of unramified-supported
Frobenius-fibres `{𝔞 : U 𝔞 ∧ Frob_𝔞 = g}` over `g` in the coset `χ⁻¹(ζ) ⊆ G`. The decomposition:

* `frobeniusIdeal` — the `G`-valued completely-multiplicative ideal Frobenius: the `Multiset.map`-
  product of `(frobeniusClass K L 𝔭).out` over the prime factors, like `galoisCharacterOnIdeal`.
* The cyclotomic identity `χ(𝔞) = χ(Frob_𝔞)` on unramified-supported `𝔞`
  (Sharifi p. 142) identifies the value-fibre with the unramified-supported
  Frobenius-value-fibre inside the geometry-of-numbers proof.
* L2 (`exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le`) — unramified-supported Frobenius-fibre
  equidistribution `∃ κ, ∀ g, |#{𝔞 ≠ ⊥ : N𝔞 ≤ N, U 𝔞, Frob_𝔞 = g} − κ·N| ≤ C·N^{1−1/d}` with `κ`
  independent of `g`. An unramified-supported `𝔞` splits as (bad part)·(good part), where the bad
  primes (unramified but with `N𝔭` not coprime to `m`) range over a finite set and the good part
  (coprime norm) is counted by the effective lattice-point count L1 on the ideal lattice intersected
  with each congruence sublattice (`exists_card_inter_smul_lattice_sub_volume_mul_pow_le`, fed the
  Lipschitz-frontier cover `normLeOne_frontier_lipschitz_cover`); summing over the bad-part set
  keeps `κ` independent of `g`.

The character-value count follows from this set equality and the Frobenius-fibre estimate
by coset counting. -/

/-- The `Gal(L/K)`-valued completely-multiplicative **ideal Frobenius**: on a prime `𝔭` it is the
chosen representative `(frobeniusClass K L 𝔭).out` of the Frobenius conjugacy class (a genuine
group element since `Gal(L/K)` is abelian, so the class is a singleton), extended completely
multiplicatively over the prime factorisation. Companion of `galoisCharacterOnIdeal`: the
character value is `χ` applied to this element (Helper 1). The `Multiset.prod` over the (unordered)
prime factors needs commutativity, supplied by `IsMulCommutative Gal(L/K)`. -/
noncomputable def frobeniusIdeal (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]
    (𝔞 : Ideal (𝓞 K)) : Gal(L/K) :=
  letI : CommGroup Gal(L/K) := { mul_comm := mul_comm' }
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map
    (fun 𝔭 ↦ (frobeniusClass K L 𝔭).out)).prod

/-! ### Sub-lemmas for `exists_card_frobeniusIdeal_fibre_sub_kappa_mul_le` (L2: the
unramified-supported Frobenius-fibre equidistribution)

The assembly route: (1) a prime with norm coprime to `m` is unramified in `L = K(μ_m)`
(different-ideal criterion + `minpoly ∣ X^m − 1`); (2) on coprime-norm ideals the cyclotomic
character sends `frobeniusIdeal` to the norm residue (multiplicative extension of
native cyclotomic character formula), and `autToPow` is injective, so the Frobenius fibre IS a
norm-residue class; (3) the per-residue count with one constant across the realized subgroup
is `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`; (4) an unramified-supported
ideal splits uniquely as (bad part)·(good part), where the bad primes — unramified but with
norm sharing a factor with `m` — divide `(m)` and are finitely many; the count regroups as a
sum over bad parts of shifted good counts; (5) with `hm : m % 4 ≠ 2`, either `d ≥ 2` (the
bad-part Euler tail converges) or the bad set is empty (`d = 1`), so the per-bad-part errors
sum to `O(N^{1−1/d})`. -/

section GapBAssembly

/-- A nonzero prime of `𝓞 K` whose norm is coprime to `m` is unramified in `L = K(μ_m)`:
a ramified prime would divide the different ideal, which divides
`(aeval ζ (minpoly 𝓞K ζ).derivative)` by the conductor formula; since `minpoly ∣ X^m − 1`,
that derivative value divides `m·ζ^{m−1}`, so `m ∈ 𝔓`, hence `(m) ≤ 𝔭` and
`N𝔭 ∣ N((m)) = m^d`, contradicting coprimality. -/
theorem unramifiedIn_of_coprime_absNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hcop : (Ideal.absNorm 𝔭).Coprime m) :
    UnramifiedIn K L 𝔭 := by
  classical
  refine ⟨h𝔭, fun 𝔓 h𝔓max h𝔓lo ↦ ?_⟩
  haveI := h𝔓lo
  haveI : 𝔓.IsPrime := h𝔓max.isPrime
  rw [← not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L)]
  intro hdvd
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) (NeZero.ne m)
  set ζ𝓞 : 𝓞 L := hζ.toInteger with hζ𝓞
  have hpow : ζ𝓞 ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hdvd_pol : minpoly (𝓞 K) ζ𝓞 ∣ Polynomial.X ^ m - 1 := by
    refine minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral ζ𝓞) ?_
    simp [hpow]
  obtain ⟨g, hg⟩ := hdvd_pol
  have hkey : (m : 𝓞 L) * ζ𝓞 ^ (m - 1)
      = Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))
        * Polynomial.aeval ζ𝓞 g := by
    have hder := congrArg (Polynomial.aeval ζ𝓞 ∘ Polynomial.derivative) hg
    simp only [Function.comp_apply, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.derivative_mul, map_sub, map_mul, map_add,
      map_pow, Polynomial.aeval_X, minpoly.aeval, zero_mul, add_zero,
      sub_zero, Polynomial.aeval_C] at hder
    simpa using hder
  have hadj : Algebra.adjoin K {algebraMap (𝓞 L) L ζ𝓞} = ⊤ := by
    have : algebraMap (𝓞 L) L ζ𝓞 = ζ := hζ.coe_toInteger
    rw [this]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hdiff_dvd : differentIdeal (𝓞 K) (𝓞 L)
      ∣ Ideal.span {Polynomial.aeval ζ𝓞 (Polynomial.derivative (minpoly (𝓞 K) ζ𝓞))} :=
    ⟨conductor (𝓞 K) ζ𝓞, by
      rw [← conductor_mul_differentIdeal (𝓞 K) K L ζ𝓞 hadj]; ring⟩
  have hmem : (m : 𝓞 L) * ζ𝓞 ^ (m - 1) ∈ 𝔓 := by
    rw [hkey]
    exact Ideal.mul_mem_right _ _
      ((Ideal.dvd_iff_le.mp (dvd_trans hdvd hdiff_dvd)) (Ideal.mem_span_singleton_self _))
  have hm𝔓 : ((m : ℕ) : 𝓞 L) ∈ 𝔓 := by
    rcases ‹𝔓.IsPrime›.mem_or_mem hmem with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h
        ((IsUnit.of_pow_eq_one hpow (NeZero.ne m)).pow _)) ‹𝔓.IsPrime›.ne_top
  have hm𝔭 : ((m : ℕ) : 𝓞 K) ∈ 𝔭 := by
    have hmap : algebraMap (𝓞 K) (𝓞 L) ((m : ℕ) : 𝓞 K) ∈ 𝔓 := by
      rwa [map_natCast]
    rw [h𝔓lo.over]
    exact Ideal.mem_comap.mpr hmap
  have hdvd_norm : Ideal.absNorm 𝔭 ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    have hle : Ideal.span {((m : ℕ) : 𝓞 K)} ≤ 𝔭 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hm𝔭
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rwa [Ideal.absNorm_span_singleton, show ((m : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by
        push_cast; rfl,
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hd
  exact absurd (Ideal.absNorm_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop.pow_right _) dvd_rfl hdvd_norm))
    ‹𝔭.IsPrime›.ne_top

end GapBAssembly
end Chebotarev
