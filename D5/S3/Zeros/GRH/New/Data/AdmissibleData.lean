/- GID: D5/S3/Zeros/GRH/New/Data/AdmissibleData
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/AdmissibleData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.AdmissibleData. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/AdmissibleData.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.ConjugateGenerator
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Record of admissible data; names for ranks, weights, the prime sum, the error budget and
the cost of one direction. -/

noncomputable section

open Set NumberField Real

/-- The constant C + 2d + 6 + N₀ + |`chowlaSelbergConst` d| + ∑_ξ |log |P₀'(ξ)||, with C chosen from
`Parameters.exists_isJetConjugate_generator` and ξ the roots of the cyclotomic polynomial P₀ of
order N₀. -/
def Parameters.c P := (exists_isJetConjugate_generator P).choose + (2 * P.d + 6) +
  (P.N₀ + |chowlaSelbergConst P.d| + ∑ w ∈ primitiveRoots
  P.N₀ ℂ, |‖(Polynomial.cyclotomic P.N₀ ℂ).derivative.eval w‖.log|)

/-- Admissible data: scales x, x₁, b; exponent s and numbers m, r; thick places with a
three-term condition; primes g₀ ≠ g₁ and an integer of K of norm g₀g₁; existence of primes ≡
1 mod M_ω² in short windows. -/
structure Data (P : Parameters) where
  /-- `logX = log x`, `logB = log b`, `logX₁ = log x₁`: the sizes are chosen on the logarithmic
  scale. -/
  (logX logB logX₁ : ℝ) (s m r : ℕ) s_le : s ≤ 32 * logX
  thick : Finset _
  g : Fin 2 → ℕ
  piG : 𝓞 P.K
  scale : 1e12 * P.c ≤ log logB ∧ 100 * log logB ≤ logX ∧ 1e6 * logX ≤ logX₁ ∧ 1e6 * logX₁ ≤ logB ∧
    6 * log logX₁ ≤ log logB
  m_mem : ↑m ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))
  r_mem : ↑r ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))
  m_pow : ∃ e, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22
  r_pow : ∃ e, r = 3 ^ (e + 1)
  thick_eq_neg_one_mod {m} (d : m ∣ P.N₁ s) : m ∣ P.N₀ * 3 ^ (.log 3 s + 5) → ∀ σ ∈ thick, P.placeClass d σ = -1
  three_term : let φ := P.placeClass P.two_pow_dvd_N₁; ∀ i j, 0 < i → i < j → j ≤ 324 * s →
         ∀ σ ∈ thick, ∀ τ ∈ thick, ∀ ρ ∈ thick, φ (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1
  g_prime i : (g i).Prime
  g_modEq_one i : g i ≡ 1 [MOD P.N₁ s * P.d]
  dvd_g_sub_one i : P.Mω s ^ 2 ∣ g i - 1
  g_injective : g.Injective
  g_mem i : ↑(g i) ∈ Icc (exp logB ^ 10) (exp logB ^ 11)
  norm_piG : piG * star piG = g 0 * g 1
  exists_prime_window : ∀ U ∈ Icc (100 * logB) (2 ^ s), ∃ p, p.Prime ∧ p ≡ 1 [MOD P.Mω s ^ 2] ∧
    log p ∈ Icc U (U + √logB)

namespace Data

variable {P} (D : Data P) (y : ℝ) (j)

/-- The scale x = exp(logX) of the data, which store its logarithm logX. -/
abbrev x := D.logX.exp

/-- The scale x₁ = exp(logX₁) of the data, which store its logarithm logX₁. -/
abbrev x₁ := D.logX₁.exp

/-- The scale b = exp(logB) of the data, which store its logarithm logB. -/
abbrev b := D.logB.exp

/-- The field E = K(ζ), ζ a primitive root of unity of order N₁ = 3^c 2^s N₀, for the exponent s
of the data. -/
@[reducible] def E := P.E D.s deriving NumberField, CharZero, IsCMField

/-- The set of infinite places of the field E of the data; it is a group, identified with
(ℤ/N₁)^× and with Gal(E/K). -/
protected abbrev Φ := InfinitePlace D.E

/-- The natural number N₁ = 3^c 2^s N₀ (`Parameters.N₁`) for the exponent s of the data. -/
abbrev N₁ := P.N₁ D.s

/-- The number of infinite places of the field E attached to the data. -/
abbrev f := numInfPlaces D.E

/-- The natural number N₁d; the field E embeds in the cyclotomic field of that order. -/
protected abbrev cycloConductor := D.N₁ * P.d

/-- The root discriminant of the number field E attached to the data. -/
abbrev rootDisc := rootDiscr D.E

/-- The rank k = r − m + 1 formed from the numbers r and m of the data, as a natural number: (r
+ 1) − m with truncated subtraction. -/
def k := D.r + 1 - D.m

/-- The natural number t = 5r, where r is the rank in the data. -/
def t := 5 * D.r

/-- The number N₁⌈y/N₁⌉, or 0 if y ≤ 0: the least natural multiple of N₁ that is at least y. -/
def roundUp := D.N₁ * ⌈y / D.N₁⌉₊

/-- The natural number h₂ = r⁸, with r the rank in the data; it is half of the gap between
successive weights. -/
def h₂ := D.r ^ 8

/-- The gap h = 2h₂, twice the half-gap h₂ = r⁸ of the data. -/
def h := 2 * D.h₂

/-- The natural number h₂ − ⌊(t+1)/2⌋, with h₂ half the gap and truncated subtraction. -/
def reducedHalfGap := D.h₂ - (D.t + 1) / 2

/-- The number a: the least multiple of N₁ that is at least xb, with x and b scales of the data. -/
def a := D.roundUp (D.x * D.b)

/-- The least multiple of N₁ that is at least a/x; it is the weight w₀⁻ (`Data.w` less h₂, at j = 0)
at thick places. -/
def b₁ := D.roundUp (D.a / D.x)

/-- The least multiple of N₁ that is at least a/x₁; the weight w₀⁻ (`Data.w` less h₂, at j = 0) at
places that are not thick. -/
def b₂ := D.roundUp (D.a / D.x₁)

/-- The infinite place of E named by the class of the integer ν modulo N₁ if ν is prime to N₁,
and the identity place otherwise. -/
abbrev placeOfInt : D.Φ := P.placeOfInt _ j

/-- The rank n_j = k + j(t + 1). -/
def n := D.k + j * (D.t + 1)

/-- The natural number k + j − 1, the number of positive basis vectors of W_j. -/
abbrev posRank := D.k + j - 1

instance : Fact (D.g j).Prime := ⟨g_prime ..⟩

/-- The product g = g₀g₁ of the two primes of the data. -/
def gProd := D.g 0 * D.g 1 deriving NeZero

/-- The tops: the infinite places of E whose class in (ℤ/N₁)^× is congruent to 1 modulo N₀. -/
def tops : Finset D.Φ := {τ | P.placeClass (P.N₀.dvd_mul_right _) τ = 1}

/-- The weight w_j(σ) = w_j⁻(σ) + h₂ at the infinite place σ, with h₂ half the gap h and
w_j⁻(σ) = b₁ + jh if σ is thick, b₂ + jh if not. -/
def w (σ : D.Φ) := ite (σ ∈ D.thick) D.b₁ D.b₂ + j * D.h + D.h₂

/-- The real weight w(σ), equal to a/x if the infinite place σ is thick and to a/x₁ otherwise. -/
def nominalWeight (σ : D.Φ) := D.a / ite (σ ∈ D.thick) D.x D.x₁

/-- For real y and a place σ, the sum over 1 ≤ ν ≤ a of Λ(ν)(1 − (ν/d))·max(y/ν − w(−ν·σ), 0), with
w = `Data.nominalWeight`. -/
def primeSum σ := ∑ ν ∈ .Icc 1 D.a,
  lambdaClass P.d 1 ν * (y / ν - D.nominalWeight (D.placeOfInt (-ν) * σ))⁺

/-- The error budget f·a·(log b)³, with f the number of infinite places of E, b a scale of the
data and a = `Data.a`. -/
abbrev budget := D.f * D.a * D.logB ^ 3

/-- For a natural number j, the real number log j! − j·log(Ω/g), with Ω = `Parameters.bigOmega` and
g = g₀g₁. -/
def jetSize := log (Nat.factorial j) - j * (P.bigOmega D.s / D.gProd).log

/-- The cost of one direction: the sum over infinite places σ of jetSize(w₀(σ)) − primeSum(w(σ), σ),
with `Data.jetSize`, `Data.primeSum` and the nominal weight w = `Data.nominalWeight`. -/
def dirCost := ∑ σ, (D.jetSize (D.w 0 σ) - D.primeSum (D.nominalWeight σ) σ)
