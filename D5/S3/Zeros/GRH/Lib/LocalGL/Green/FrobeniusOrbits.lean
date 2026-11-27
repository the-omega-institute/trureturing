/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Green/FrobeniusOrbits
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Green/FrobeniusOrbits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Green.FrobeniusOrbits. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Green/FrobeniusOrbits.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Green.CuspidalFunction
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Definitions for Green's characters of GL_n(k): τ_P, Ξ_c, labels, χ∘det, the reflection sum and
the idempotents e_c. Then general lemmas on powers and Frobenius orbits of roots (textbook or
folklore).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Definitions: labels, cuspidal Green characters, their products, determinant characters,
idempotents. Roots of an irreducible polynomial over a finite field form a Frobenius orbit. -/

noncomputable section

open Polynomial Classical Fint Function Real UniqueFactorizationMonoid FiniteField Nat Multiset
variable {k} [Field k] [Finite k] {K} [Field K] [Algebra k K] (T : MulChar K ℂ) {n} [Fintype n]
  (Q r : ℕ) (P c : k[X]) (χ : MulChar k ℂ)

/-- The finite set of monic polynomials of degree r over the finite field k. -/
def monicsOfDegree k [Field k] [Finite k] r := @Set.toFinset k[X] {_c | _}
    (.ofEquiv _ ((monicEquivDegreeLT r).trans (degreeLTEquiv ..).toEquiv).symm)

/-- A chosen injective multiplicative character from the algebraic closure of k to ℂ (arbitrary
if there is none). -/
def faithfulChar k [Field k] : MulChar (AlgebraicClosure k) ℂ := epsilon (Injective ·)

/-- The field K is algebraically closed and the multiplicative character T : K → ℂ is injective,
so it embeds K^× in ℂ^×. -/
class IsFaithfulMulChar K [Field K] (T :
  outParam (MulChar K ℂ)) extends IsAlgClosed K where injective : Injective T

/-- The character θ_x = T^a of K, where a is a chosen natural number with T(x) =
exp(2πi/(Q−1))^a. -/
def thetaChar x := T ^ epsilon (T x = .exp (2 * π * .I / (Q - 1 :)) ^ ·)

/-- Green's class function τ_P: (−1)^d times the rank d part of C_{θ_x}, where d = deg P, x is a
chosen root of P in K, and θ_x is taken for Q = |k|^d. -/
def greenTau := (-1 : ℂ) ^ P.natDegree • (Hall.greenCuspidal k
  (thetaChar T (.card k ^ P.natDegree) (epsilon (P.aeval · = 0)))).rankPart P.natDegree

/-- The multiplicative map c ↦ Ξ_c: the product, by parabolic induction, of τ_P over the monic
irreducible factors P of c with multiplicity; Ξ_0 = 0. -/
def labelChar : k[X] →* Hall k :=
    ⟨⟨fun c ↦ ite (c = 0) 0 ((normalizedFactors c).map (greenTau T)).prod, by simp⟩, by aesop⟩

/-- c is a label of degree r: a monic squarefree polynomial over k of degree r with nonzero
constant term. -/
def IsLabel := c.Monic ∧ Squarefree c ∧ c.natDegree = r ∧ c.coeff 0 ≠ 0

/-- The class function χ∘det on endomorphisms of every dimension, written through the constant
term of the characteristic polynomial. -/
def detChar : Hall k := fun c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)

/-- The element ∑ χ(det h)⁻¹ h of ℂ[GL_n(k)], summed over the invertible h of the form 1 + u lᵀ,
u a column vector. -/
def reflectionSum l := groupAlgElem fun h : GL n k ↦
  ite (∃ u, h.1 = 1 + .vecMulVec u l) (χ⁻¹ h.1.det) 0

/-- The element e_c = ∑ (Ξ_c(1)/|G|)·conj Ξ_c(g)·g of ℂ[G], G = GL_n(k), Ξ_c formed with
`faithfulChar`, if c is a label of degree |n|; zero otherwise. -/
def labelIdem n [Fintype n] (c : k[X]) := let Ξ := (labelChar (faithfulChar k) c).evalGL (n := n)
  ite (IsLabel (Fintype.card n) c) (groupAlgElem fun g ↦
    Ξ 1 / Nat.card (GL n k) * starRingEnd ℂ (Ξ g)) 0

variable {k K : _} [Field k] [Finite k] [Field K] [Algebra k K] {P : k[X]} (hP : Irreducible P) {x :
  K} (hx : aeval x P = 0)

@[simp] lemma pow_pred_eq_one_iff {Q} (hQ : 2 ≤ Q) : x ^ (Q - 1) = 1 ↔ x ≠ 0 ∧ x ^ Q = x := by
  grind [pow_sub₀, zero_pow]

@[simp] lemma algebraMap_pow_card_pred_eq_one (a : kˣ) : algebraMap k K a ^ (.card k - 1) = 1 :=
  card_units k ▸ mod_cast by simp

include hP hx

lemma root_pow_card_pow_eq_self_iff {n} : x ^ .card k ^ n = x ↔ P.natDegree ∣ n := by
  simp [hP.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← hP.dvd_iff_aeval_eq_zero hx]

lemma root_pow_card_pow_eq_iff_modEq {a b} : x ^ .card k ^ a = x ^ .card k ^ b ↔
  a ≡ b [MOD P.natDegree] := by
  have := @(frobeniusAlgHom k K).injective.eq_iff
  induction a, b using Nat.recDiagAux <;> simp_all [pow_succ, pow_mul, eq_comm, modEq_iff_dvd',
    ← root_pow_card_pow_eq_self_iff hP hx, modEq_zero_iff_dvd]

lemma aroots_eq_frobenius_orbit : P.aroots K = .map (x ^ .card k ^ ·) (range P.natDegree) := by
  have := (aeval_algHom <| frobeniusAlgHom k K ^ ·)
  apply roots_eq_of_degree_le_card_of_ne_zero (S := ⟨_, (nodup_range _).map_on _⟩) <;> simp_all
    [hP.ne_zero, coe_frobeniusAlgHom, ↓root_pow_card_pow_eq_iff_modEq hP, ModEq, mod_eq_of_lt]

lemma aroots_pow_eq_frobenius_orbit {j} : (P ^ j).aroots K =
  .map (x ^ .card k ^ ·) (range (P ^ j).natDegree) ∧ x ^ .card k ^ (P ^ j).natDegree =
  x := by induction j <;> simp_all [aroots_eq_frobenius_orbit _ hx, @pow_add ℕ, add_mul, add_smul,
  range_add, pow_mul, root_pow_card_pow_eq_self_iff hP, -card_eq_fintype_card]

lemma exists_pow_card_pow_eq_of_root {y} : aeval y P = 0 → ∃ i < P.natDegree, x ^ .card k ^ i = y :=
  by simpa [hP.ne_zero] using congr(y ∈ $(aroots_eq_frobenius_orbit hP hx)).mp
