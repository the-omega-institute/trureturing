/- GID: D5/S3/Combinatorics/Partitions/HemmerStraubWestrem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/HemmerStraubWestrem
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The alternating even-row Ev character sum equals the two-row Ev sum. -/

/-
result
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#17766; Proved)
Direct frozen dependencies: none (only pinned Mathlib imports).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18551.
frobChar uses AddMonoidAlgebra.coeff with polynomial before exponent.
All private proof helpers have proof_shape: bind-only and escape_witness: none.
Their direct frozen dependencies are none. Consumers:
powerSumProd_nil: bind-only; consumers: ev_plus, ev_minus
powerSumProd_cons: bind-only; consumers: ev_plus, ev_minus
ev_plus: bind-only; consumers: ev_right
ev_minus: bind-only; consumers: ev_left
psum_three: bind-only; consumers: psum_homogeneous, boundary_plus_factor, minus_factor
minus_factor: bind-only; consumers: principal_minus_factor
weight_even: bind-only; consumers: even_pair
weight_even_odd_odd: bind-only; consumers: sym_detector_two_odd
weight_odd_even_odd: bind-only; consumers: sym_detector_two_odd
weight_odd_odd_even: bind-only; consumers: sym_detector_two_odd
difference_even: bind-only; consumers: sym_detector_even
even_pair: bind-only; consumers: sym_detector_even
sym_detector_even: bind-only; consumers: sym_detector
sym_detector_two_odd: bind-only; consumers: sym_detector
sym_detector: bind-only; consumers: symMono_detector
altCoeff_apply: bind-only; consumers: alt_boundary
evenSum_apply: bind-only; consumers: ev_left, evenSum_mono
ev_left: bind-only; consumers: list_identity
ev_right: bind-only; consumers: list_identity
trip_apply_zero: bind-only; consumers: trip_apply_one, boundary_coeff
trip_apply_one: bind-only; consumers: trip_apply_two
trip_apply_two: bind-only; consumers: boundary_coeff
trip_add: bind-only; consumers: mono_mul
mono_eq: bind-only; consumers: boundary_mono, symmetrize_mono, vandermonde_mono, principal_mono
mono_mul: bind-only; consumers: evenSum_mono
vandermonde_mono: bind-only; consumers: evenSum_mono, alt_boundary
detector_apply: bind-only; consumers: principal_symMono, detector_minus
principal_mono: bind-only; consumers: principal_symMono
boundary_mono: bind-only; consumers: boundary_monomial
principal_minus_factor: bind-only; consumers: principal_minus
boundary_plus_factor: bind-only; consumers: boundary_plus
principal_minus: bind-only; consumers: detector_minus
boundary_plus: bind-only; consumers: right_coefficient
symmetrize_symmetric: bind-only; consumers: coefficient_detector
symmetrize_mono: bind-only; consumers: symmetrize_monomial
trip_coordinates: bind-only; consumers: boundary_coeff, boundary_monomial, symmetrize_monomial
symmetrize_monomial: bind-only; consumers: coefficient_detector
principal_symMono: bind-only; consumers: symMono_detector
rawSum_apply: bind-only; consumers: evenSum_mono, raw_mono
exponent_eq_trip: bind-only; consumers: alt_boundary, raw_mono
trip_inj: bind-only; consumers: boundary_coeff, raw_mono
r3_mem: bind-only; consumers: raw_mono
raw_mono: bind-only; consumers: evenSum_mono
evenSum_mono: bind-only; consumers: symMono_detector
trip_le: bind-only; consumers: coeff_mono_mul
trip_sub: bind-only; consumers: coeff_mono_mul
coeff_mono_mul: bind-only; consumers: alt_boundary
alt_boundary: bind-only; consumers: alt_boundary_homogeneous
homogeneous_support_coords: bind-only; consumers: boundary_coeff, coefficient_detector
boundary_monomial: bind-only; consumers: boundary_coeff
boundary_coeff: bind-only; consumers: alt_boundary_homogeneous
alt_boundary_homogeneous: bind-only; consumers: right_coefficient
psum_homogeneous: bind-only; consumers: minus_homogeneous, plus_homogeneous
minus_homogeneous: bind-only; consumers: left_coefficient
plus_homogeneous: bind-only; consumers: right_coefficient
minus_symmetric: bind-only; consumers: left_coefficient
symMono_detector: bind-only; consumers: coefficient_detector
coefficient_detector: bind-only; consumers: left_coefficient
detector_minus: bind-only; consumers: left_coefficient
left_coefficient: bind-only; consumers: list_identity
right_coefficient: bind-only; consumers: list_identity
list_identity: bind-only; consumers: result
The character interpretation of frobChar uses the classical Frobenius formula in
Hemmer–Straub–Westrem, Lemma 3.1; that representation-theoretic identification is not formalized.
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.HemmerStraubWestrem

open MvPolynomial

/-- The power-sum product `p_τ = ∏ᵢ p_{τᵢ}` in three variables, with Mathlib's power sum
`psum (Fin 3) ℤ k = x₀ᵏ + x₁ᵏ + x₂ᵏ`. -/
noncomputable def powerSumProd (τ : List ℕ) : MvPolynomial (Fin 3) ℤ :=
  (τ.map (MvPolynomial.psum (Fin 3) ℤ)).prod

/-- The Vandermonde alternant `a_δ = (x₀ − x₁)(x₀ − x₂)(x₁ − x₂)`, `δ = (2, 1, 0)`. -/
noncomputable def vandermonde3 : MvPolynomial (Fin 3) ℤ :=
  (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)

/-- The irreducible character `χ^μ_τ` of `S_m` for `μ` with at most three parts (padded by zeros),
at the cycle type `τ`, by the Frobenius character formula `χ^μ_τ = [x^{μ+δ}] a_δ p_τ`
(arXiv:2509.02796v1, Lemma 3.1, `χ^μ_λ = ⟨p_λ, s_μ⟩`). -/
noncomputable def frobChar (μ : Fin 3 → ℕ) (τ : List ℕ) : ℤ :=
  (vandermonde3 * powerSumProd τ).coeff
    (Finsupp.equivFunOnFinite.symm fun i => μ i + (2 - (i : ℕ)))

/-- `Ev(λ)` as a list with multiplicity: each part `a` is replaced independently by `(2a)` or by
`(a, a)`, giving `2^r` cycle types for `r` parts. -/
def evTypes : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => (evTypes l).map (2 * a :: ·) ++ (evTypes l).map (fun τ => a :: a :: τ)

/-- `R₃(m)`: the partitions of `m` with at most three parts, all even, as weakly decreasing
triples padded by zeros. -/
def R3 (m : ℕ) : Finset (Fin 3 → ℕ) :=
  (Finset.Nat.antidiagonalTuple 3 m).filter fun μ =>
    μ 1 ≤ μ 0 ∧ μ 2 ≤ μ 1 ∧ ∀ i, Even (μ i)

/-- Hemmer–Straub–Westrem, arXiv:2509.02796v1, Conjecture 2.3 (N = 1 version): for every
partition `λ ⊢ n`,
`∑_{λ̃ ∈ Ev(λ)} ∑_{μ ∈ R₃(2n)} (−1)^{ℓ(λ̃)} χ^μ_{λ̃} = ∑_{λ̃ ∈ Ev(λ)} χ^{(n,n)}_{λ̃}`. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ lam : Nat.Partition n,
    ((evTypes lam.parts.toList).map fun τ =>
        ∑ μ ∈ R3 (2 * n), (-1 : ℤ) ^ τ.length * frobChar μ τ).sum =
      ((evTypes lam.parts.toList).map fun τ => frobChar ![n, n, 0] τ).sum

@[simp] private theorem powerSumProd_nil : powerSumProd [] = 1 := by exact List.prod_nil
@[simp] private theorem powerSumProd_cons (a : ℕ) (l : List ℕ) :
    powerSumProd (a :: l) = psum (Fin 3) ℤ a * powerSumProd l := by exact List.prod_cons

private noncomputable def minusProd (l : List ℕ) : MvPolynomial (Fin 3) ℤ :=
  (l.map fun a => psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a)).prod
private noncomputable def plusProd (l : List ℕ) : MvPolynomial (Fin 3) ℤ :=
  (l.map fun a => psum (Fin 3) ℤ a ^ 2 + psum (Fin 3) ℤ (2*a)).prod

private theorem ev_plus (l : List ℕ) :
    ((evTypes l).map powerSumProd).sum = plusProd l := by
  induction l with
  | nil => simp [evTypes, plusProd]
  | cons a l ih =>
    simp only [evTypes, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, powerSumProd_cons, plusProd, List.map_cons, List.prod_cons]
    simp_rw [← mul_assoc, ← pow_two]
    rw [List.sum_map_mul_left, List.sum_map_mul_left]
    rw [ih]
    simp only [plusProd]
    ring

private theorem ev_minus (l : List ℕ) :
    ((evTypes l).map fun τ => (-1 : ℤ) ^ τ.length • powerSumProd τ).sum = minusProd l := by
  induction l with
  | nil => simp [evTypes, minusProd]
  | cons a l ih =>
    have h1 (τ : List ℕ) :
        (-1 : ℤ) ^ (τ.length+1) • (psum (Fin 3) ℤ (2*a) * powerSumProd τ) =
        -psum (Fin 3) ℤ (2*a) * ((-1 : ℤ)^τ.length • powerSumProd τ) := by
      simp only [pow_succ, smul_eq_C_mul, map_mul, map_neg, map_one]
      ring
    have h2 (τ : List ℕ) :
        (-1 : ℤ) ^ (τ.length+1+1) •
          (psum (Fin 3) ℤ a * (psum (Fin 3) ℤ a * powerSumProd τ)) =
        psum (Fin 3) ℤ a ^ 2 * ((-1 : ℤ)^τ.length • powerSumProd τ) := by
      simp only [pow_succ, smul_eq_C_mul, map_mul, map_neg, map_one]
      ring
    simp only [evTypes, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.length_cons, powerSumProd_cons, h1, h2, List.sum_map_mul_left]
    rw [ih]
    simp only [minusProd, List.map_cons, List.prod_cons]
    ring

private theorem psum_three (a : ℕ) : psum (Fin 3) ℤ a = X 0 ^ a + X 1 ^ a + X 2 ^ a := by
  exact Fin.sum_univ_three (fun i : Fin 3 => (MvPolynomial.X i : MvPolynomial (Fin 3) ℤ) ^ a)

private theorem minus_factor (a : ℕ) :
    psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a) =
      2 * ((X 0 * X 1)^a + (X 0 * X 2)^a + (X 1 * X 2)^a) := by
  simp only [psum_three, mul_pow, pow_mul, pow_two]
  ring

private abbrev orderedEven (a b c : ℤ) : Prop :=
  0 ≤ c ∧ c ≤ b ∧ b ≤ a ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0

private noncomputable def weight (a b c : ℤ) : ℤ :=
  (if orderedEven a b c then (1 : ℤ) else 0) - (if orderedEven a (b-1) (c+1) then (1 : ℤ) else 0) -
  (if orderedEven (a-1) (b+1) c then (1 : ℤ) else 0) + (if orderedEven (a-1) (b-1) (c+2) then (1 : ℤ) else 0) +
  (if orderedEven (a-2) (b+1) (c+1) then (1 : ℤ) else 0) - (if orderedEven (a-2) b (c+2) then (1 : ℤ) else 0)

private noncomputable def symWeight (a b c : ℤ) : ℤ :=
  weight a b c + weight a c b + weight b a c + weight b c a + weight c a b + weight c b a

private noncomputable def difference (a c : ℤ) : ℤ := (if a=c then (1 : ℤ) else 0) - (if a=c+1 then (1 : ℤ) else 0)
private noncomputable def symDifference (a b c : ℤ) : ℤ :=
  difference a c + difference a b + difference b c + difference b a +
  difference c b + difference c a

private theorem weight_even (a b c : ℕ) :
    weight (2*a) (2*b) (2*c) =
      (if c ≤ b ∧ b ≤ a then (1 : ℤ) else 0) - (if c < b ∧ b < a then (1 : ℤ) else 0) := by
  unfold weight orderedEven
  norm_num
  omega

private theorem weight_even_odd_odd (a b c : ℕ) :
    weight (2*a) (2*b+1) (2*c+1) =
      -(if c < b ∧ b ≤ a then (1 : ℤ) else 0) + (if c ≤ b ∧ b+2 ≤ a then (1 : ℤ) else 0) := by
  unfold weight orderedEven
  norm_num
  omega

private theorem weight_odd_even_odd (a b c : ℕ) :
    weight (2*a+1) (2*b) (2*c+1) = 0 := by
  simp [weight, orderedEven]

private theorem weight_odd_odd_even (a b c : ℕ) :
    weight (2*a+1) (2*b+1) (2*c) =
      -(if c ≤ b+1 ∧ b < a then (1 : ℤ) else 0) + (if c+1 ≤ b ∧ b ≤ a then (1 : ℤ) else 0) := by
  unfold weight orderedEven
  norm_num
  omega

private theorem difference_even (a c : ℕ) : difference (2*a) (2*c) = (if a=c then (1 : ℤ) else 0) := by
  unfold difference
  norm_num
  omega

private theorem even_pair (a b c : ℕ) :
    weight (2*a) (2*b) (2*c) + weight (2*c) (2*b) (2*a) =
      (if b=a then (1 : ℤ) else 0) + (if b=c then (1 : ℤ) else 0) := by
  simp only [weight_even]
  omega

private theorem sym_detector_even (a b c : ℕ) :
    symWeight (2*a) (2*b) (2*c) = symDifference (2*a) (2*b) (2*c) := by
  simp only [symWeight, symDifference, difference_even]
  linear_combination even_pair a b c + even_pair a c b + even_pair b a c

private theorem sym_detector_two_odd (a b c : ℕ) :
    symWeight (2*a) (2*b+1) (2*c+1) = symDifference (2*a) (2*b+1) (2*c+1) := by
  simp only [symWeight, weight_even_odd_odd, weight_odd_even_odd, weight_odd_odd_even,
    symDifference, difference]
  norm_num
  omega
private theorem sym_detector (a b c : ℕ) (h : (a+b+c)%2=0) :
    symWeight a b c = symDifference a b c := by
  have hap : a%2=0 ∨ a%2=1 := Nat.mod_two_eq_zero_or_one a
  have hbp : b%2=0 ∨ b%2=1 := Nat.mod_two_eq_zero_or_one b
  have hcp : c%2=0 ∨ c%2=1 := Nat.mod_two_eq_zero_or_one c
  rcases hap with ha|ha <;> rcases hbp with hb|hb <;> rcases hcp with hc|hc
  · convert sym_detector_even (a/2) (b/2) (c/2) using 1 <;> congr 1 <;> omega
  · omega
  · omega
  · convert sym_detector_two_odd (a/2) (b/2) (c/2) using 1 <;> congr 1 <;> omega
  · omega
  · have hh : symWeight (b:ℤ) a c = symDifference b a c := by
      convert sym_detector_two_odd (b/2) (a/2) (c/2) using 1 <;> congr 1 <;> omega
    unfold symWeight symDifference at *
    linear_combination hh
  · have hh : symWeight (c:ℤ) a b = symDifference c a b := by
      convert sym_detector_two_odd (c/2) (a/2) (b/2) using 1 <;> congr 1 <;> omega
    unfold symWeight symDifference at *
    linear_combination hh
  · omega

private noncomputable def exponent (μ : Fin 3 → ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => μ i + (2-(i:ℕ)))
private noncomputable def altCoeff (μ : Fin 3 → ℕ) : MvPolynomial (Fin 3) ℤ →+ ℤ :=
  (coeffAddMonoidHom (exponent μ)).comp (AddMonoidHom.mulLeft vandermonde3)
private noncomputable def evenSum (m : ℕ) : MvPolynomial (Fin 3) ℤ →+ ℤ :=
  ∑ μ ∈ R3 m, altCoeff μ

@[simp] private theorem altCoeff_apply (μ : Fin 3 → ℕ) (p : MvPolynomial (Fin 3) ℤ) :
    altCoeff μ p = (vandermonde3*p).coeff (exponent μ) := by
  exact AddMonoidHom.comp_apply (coeffAddMonoidHom (exponent μ)) (AddMonoidHom.mulLeft vandermonde3) p
@[simp] private theorem evenSum_apply (m : ℕ) (p : MvPolynomial (Fin 3) ℤ) :
    evenSum m p = ∑ μ ∈ R3 m, (vandermonde3*p).coeff (exponent μ) := by
  simp [evenSum]

private theorem ev_left (m : ℕ) (l : List ℕ) :
    ((evTypes l).map fun τ => ∑ μ ∈ R3 m, (-1 : ℤ)^τ.length * frobChar μ τ).sum =
      evenSum m (minusProd l) := by
  rw [← ev_minus]
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro τ _
  rw [map_zsmul]
  simp [evenSum_apply, frobChar, exponent, ← Finset.mul_sum]

private theorem ev_right (μ : Fin 3 → ℕ) (l : List ℕ) :
    ((evTypes l).map fun τ => frobChar μ τ).sum = altCoeff μ (plusProd l) := by
  rw [← ev_plus]
  simp [map_list_sum, List.map_map, Function.comp_def, frobChar, altCoeff_apply, exponent]

private noncomputable def trip (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a,b,c]
@[simp] private theorem trip_apply_zero (a b c : ℕ) : trip a b c 0 = a := by
  exact Matrix.cons_val_zero a ![b,c]
@[simp] private theorem trip_apply_one (a b c : ℕ) : trip a b c 1 = b := by exact trip_apply_zero b a c
@[simp] private theorem trip_apply_two (a b c : ℕ) : trip a b c 2 = c := by exact trip_apply_one a c b

private theorem trip_add (a b c d e f : ℕ) : trip a b c + trip d e f = trip (a+d) (b+e) (c+f) := by
  apply DFunLike.coe_injective
  exact Matrix.vec3_add a b c d e f

private noncomputable def mono (a b c : ℕ) : MvPolynomial (Fin 3) ℤ := monomial (trip a b c) 1

private theorem mono_eq (a b c : ℕ) : mono a b c = X 0 ^ a * X 1 ^ b * X 2 ^ c := by
  rw [mono, monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
  · exact Fin.prod_univ_three _
  · intro; simp

@[simp] private theorem mono_mul (a b c d e f : ℕ) : mono a b c * mono d e f = mono (a+d) (b+e) (c+f) := by
  simp [mono, trip_add]

private theorem vandermonde_mono : vandermonde3 =
    mono 2 1 0 - mono 2 0 1 - mono 1 2 0 + mono 1 0 2 + mono 0 2 1 - mono 0 1 2 := by
  simp only [mono_eq, pow_zero, pow_one, one_mul, mul_one, vandermonde3]
  ring

private noncomputable def principal : MvPolynomial (Fin 3) ℤ →+* Polynomial ℤ :=
  eval₂Hom Polynomial.C ![Polynomial.X^2,Polynomial.X,1]
private noncomputable def boundary : MvPolynomial (Fin 3) ℤ →+* Polynomial ℤ :=
  eval₂Hom Polynomial.C ![Polynomial.X,1,0]
private noncomputable def detector (m : ℕ) : MvPolynomial (Fin 3) ℤ →+ ℤ :=
  ((Polynomial.lcoeff ℤ m).toAddMonoidHom.comp principal.toAddMonoidHom) -
    ((Polynomial.lcoeff ℤ (m+1)).toAddMonoidHom.comp principal.toAddMonoidHom)

@[simp] private theorem detector_apply (m : ℕ) (p : MvPolynomial (Fin 3) ℤ) :
    detector m p = (principal p).coeff m - (principal p).coeff (m+1) := rfl

@[simp] private theorem principal_mono (a b c : ℕ) : principal (mono a b c) = Polynomial.X^(2*a+b) := by
  simp [principal, mono_eq]
  rw [← pow_mul, ← pow_add]

@[simp] private theorem boundary_mono (a b c : ℕ) :
    boundary (mono a b c) = if c=0 then Polynomial.X^a else 0 := by
  by_cases h : c=0 <;> simp [boundary,mono_eq,h]

private noncomputable def triProd (l : List ℕ) : Polynomial ℤ :=
  (l.map fun a => Polynomial.X^(2*a) + Polynomial.X^a + 1).prod

private theorem principal_minus_factor (a : ℕ) :
    principal (psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a)) =
    2 * Polynomial.X^a * (Polynomial.X^(2*a) + Polynomial.X^a + 1) := by
  rw [minus_factor]
  simp [principal, map_mul, mul_pow, ← pow_mul, ← pow_add]
  ring

private theorem boundary_plus_factor (a : ℕ) (ha : 0<a) :
    boundary (psum (Fin 3) ℤ a ^ 2 + psum (Fin 3) ℤ (2*a)) =
    2 * (Polynomial.X^(2*a) + Polynomial.X^a + 1) := by
  simp [boundary, psum_three, map_add, map_pow, zero_pow (by omega : a ≠ 0),
    pow_mul]
  ring

private theorem principal_minus (l : List ℕ) :
    principal (minusProd l) = 2^l.length * Polynomial.X^l.sum * triProd l := by
  induction l with
  | nil => simp [minusProd,triProd]
  | cons a l ih =>
    change principal ((psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a)) * minusProd l) = _
    rw [map_mul, principal_minus_factor, ih]
    simp only [triProd,List.map_cons,List.prod_cons,List.length_cons,List.sum_cons]
    rw [pow_succ, pow_add]
    ring

private theorem boundary_plus (l : List ℕ) (hl : ∀ a∈l, 0<a) :
    boundary (plusProd l) = 2^l.length * triProd l := by
  induction l with
  | nil => simp [plusProd,triProd]
  | cons a l ih =>
    have ha : 0<a := hl a (by simp)
    have ht : ∀ b∈l, 0<b := by intro b hb; exact hl b (by simp [hb])
    change boundary ((psum (Fin 3) ℤ a ^ 2 + psum (Fin 3) ℤ (2*a)) * plusProd l) = _
    rw [map_mul, boundary_plus_factor a ha, ih ht]
    simp only [triProd,List.map_cons,List.prod_cons,List.length_cons]
    rw [pow_succ]
    ring

private noncomputable def symMono (a b c : ℕ) : MvPolynomial (Fin 3) ℤ :=
  mono a b c + mono a c b + mono b a c + mono b c a + mono c a b + mono c b a
private noncomputable def symmetrize : MvPolynomial (Fin 3) ℤ →+ MvPolynomial (Fin 3) ℤ where
  toFun p := p + rename (Equiv.swap 1 2) p + rename (Equiv.swap 0 1) p +
    rename (Equiv.swap 1 2) (rename (Equiv.swap 0 1) p) +
    rename (Equiv.swap 0 1) (rename (Equiv.swap 1 2) p) + rename (Equiv.swap 0 2) p
  map_zero' := by simp
  map_add' p q := by simp; abel

private theorem symmetrize_symmetric (p : MvPolynomial (Fin 3) ℤ) (h : p.IsSymmetric) :
    symmetrize p = 6 • p := by
  change p + rename (Equiv.swap 1 2) p + rename (Equiv.swap 0 1) p +
    rename (Equiv.swap 1 2) (rename (Equiv.swap 0 1) p) +
    rename (Equiv.swap 0 1) (rename (Equiv.swap 1 2) p) + rename (Equiv.swap 0 2) p = _
  rw [h _,h _,h _]
  simp only [h _]
  module

private theorem symmetrize_mono (a b c : ℕ) : symmetrize (mono a b c) = symMono a b c := by
  simp [symmetrize, mono_eq, symMono, map_mul, map_pow, rename_X, Equiv.swap_apply_def]
  ring

private theorem trip_coordinates (d : Fin 3 →₀ ℕ) : trip (d 0) (d 1) (d 2) = d := by
  apply DFunLike.coe_injective
  exact List.ofFn_inj.mp rfl

private theorem symmetrize_monomial (d : Fin 3 →₀ ℕ) (r : ℤ) :
    symmetrize (monomial d r) = r • symMono (d 0) (d 1) (d 2) := by
  have hm : (monomial d r : MvPolynomial (Fin 3) ℤ) = r • mono (d 0) (d 1) (d 2) := by
    simp [mono, smul_monomial, trip_coordinates]
  rw [hm, map_zsmul, symmetrize_mono]

private theorem principal_symMono (m a b c : ℕ) (h : a+b+c=m) :
    detector m (symMono a b c) =
      ((if a=c then 1 else 0) - (if a=c+1 then 1 else 0)) +
      ((if a=b then 1 else 0) - (if a=b+1 then 1 else 0)) +
      ((if b=c then 1 else 0) - (if b=c+1 then 1 else 0)) +
      ((if b=a then 1 else 0) - (if b=a+1 then 1 else 0)) +
      ((if c=b then 1 else 0) - (if c=b+1 then 1 else 0)) +
      ((if c=a then 1 else 0) - (if c=a+1 then 1 else 0)) := by
  have hd (x y z : ℕ) (hh : x+y+z=m) : detector m (mono x y z) =
      ((if x=z then 1 else 0) - (if x=z+1 then 1 else 0) : ℤ) := by
    rw [detector_apply, principal_mono]
    simp only [Polynomial.coeff_X_pow]
    have he : (m=2*x+y) ↔ x=z := by omega
    have he' : (m+1=2*x+y) ↔ x=z+1 := by omega
    simp [he,he']
  simp only [symMono,map_add]
  rw [hd a b c h,hd a c b (by omega),hd b a c (by omega),hd b c a (by omega),
    hd c a b (by omega),hd c b a (by omega)]

private noncomputable def rawSum (m : ℕ) : MvPolynomial (Fin 3) ℤ →+ ℤ :=
  ∑ μ ∈ R3 m, coeffAddMonoidHom (exponent μ)

@[simp] private theorem rawSum_apply (m : ℕ) (p : MvPolynomial (Fin 3) ℤ) :
    rawSum m p = ∑ μ ∈ R3 m, p.coeff (exponent μ) := by simp [rawSum]

private theorem exponent_eq_trip (μ : Fin 3 → ℕ) :
    exponent μ = trip (μ 0+2) (μ 1+1) (μ 2) := by
  apply DFunLike.coe_injective
  exact List.ofFn_inj.mp rfl

private theorem trip_inj (a b c d e f : ℕ) : trip a b c = trip d e f ↔ a=d ∧ b=e ∧ c=f := by
  change (Finsupp.equivFunOnFinite.symm (![a,b,c] : Fin 3 → ℕ) =
    Finsupp.equivFunOnFinite.symm (![d,e,f] : Fin 3 → ℕ)) ↔ _
  rw [Finsupp.equivFunOnFinite.symm.injective.eq_iff]
  simp only [Matrix.vecCons_inj, and_true]

private theorem r3_mem (μ : Fin 3 → ℕ) (m : ℕ) : μ ∈ R3 m ↔
    μ 0 + μ 1 + μ 2 = m ∧ μ 1 ≤ μ 0 ∧ μ 2 ≤ μ 1 ∧
      μ 0 % 2 = 0 ∧ μ 1 % 2 = 0 ∧ μ 2 % 2 = 0 := by
  simp [R3, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three, Nat.even_iff,
    Fin.forall_fin_succ]

private theorem raw_mono (m a b c : ℕ) : rawSum m (mono a b c) =
    if a+b+c=m+3 ∧ orderedEven ((a:ℤ)-2) ((b:ℤ)-1) c then 1 else 0 := by
  classical
  by_cases ha : 2 ≤ a
  · by_cases hb : 1 ≤ b
    · have eqv (μ : Fin 3 → ℕ) : trip a b c = exponent μ ↔ μ = ![a-2,b-1,c] := by
        rw [exponent_eq_trip, trip_inj]
        constructor
        · rintro ⟨h0,h1,h2⟩
          ext i; fin_cases i <;> simp <;> omega
        · intro h; subst μ; simp; omega
      simp only [rawSum_apply, mono, coeff_monomial, eqv]
      rw [Finset.sum_ite_eq']
      congr 1
      apply propext
      rw [r3_mem]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, orderedEven]
      omega
    · have hz (μ : Fin 3 → ℕ) : trip a b c ≠ exponent μ := by
        simp only [exponent_eq_trip, ne_eq, trip_inj]; omega
      simp [rawSum_apply, mono, coeff_monomial, hz, orderedEven]
      intro; omega
  · have hz (μ : Fin 3 → ℕ) : trip a b c ≠ exponent μ := by
      simp only [exponent_eq_trip, ne_eq, trip_inj]; omega
    simp [rawSum_apply, mono, coeff_monomial, hz, orderedEven]
    intro; omega

private theorem evenSum_mono (m a b c : ℕ) (h : a+b+c=m) :
    evenSum m (mono a b c) = weight a b c := by
  rw [show evenSum m (mono a b c) = rawSum m (vandermonde3 * mono a b c) by simp]
  rw [vandermonde_mono]
  simp only [add_mul, sub_mul, mono_mul, zero_add, map_add, map_sub, raw_mono]
  have h1 : 2+a+(1+b)+c=m+3 := by omega
  have h2 : 2+a+b+(1+c)=m+3 := by omega
  have h3 : 1+a+(2+b)+c=m+3 := by omega
  have h4 : 1+a+b+(2+c)=m+3 := by omega
  have h5 : a+(2+b)+(1+c)=m+3 := by omega
  have h6 : a+(1+b)+(2+c)=m+3 := by omega
  simp only [h1,h2,h3,h4,h5,h6,true_and, Nat.cast_add, Nat.cast_ofNat]
  unfold weight
  congr 2 <;> congr 1 <;> push_cast <;> ring

private theorem trip_le (a b c d e f : ℕ) : trip a b c ≤ trip d e f ↔ a≤d ∧ b≤e ∧ c≤f := by
  change (∀ i : Fin 3, ![a,b,c] i ≤ ![d,e,f] i) ↔ _
  simp only [Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]

private theorem trip_sub (a b c d e f : ℕ) : trip a b c - trip d e f = trip (a-d) (b-e) (c-f) := by
  apply DFunLike.coe_injective
  change (![a,b,c] : Fin 3 → ℕ) - ![d,e,f] = ![a-d,b-e,c-f]
  simp only [Matrix.cons_sub_cons, Matrix.empty_sub_empty]

private theorem coeff_mono_mul (a b c d e f : ℕ) (p : MvPolynomial (Fin 3) ℤ) :
    (mono d e f * p).coeff (trip a b c) =
      if d≤a ∧ e≤b ∧ f≤c then p.coeff (trip (a-d) (b-e) (c-f)) else 0 := by
  simp [mono, coeff_monomial_mul', trip_le, trip_sub]

private theorem alt_boundary (n : ℕ) (hn : 1≤n) (p : MvPolynomial (Fin 3) ℤ) :
    altCoeff ![n,n,0] p = p.coeff (trip n n 0) - p.coeff (trip (n+1) (n-1) 0) := by
  rw [altCoeff_apply,exponent_eq_trip,vandermonde_mono]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_mul,sub_mul,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply,Finsupp.sub_apply,coeff_mono_mul]
  simp (disch := omega) only [le_refl, zero_le, Nat.reduceLeDiff,
    Nat.reduceLeDiff, Nat.add_sub_cancel_right, and_true, and_false, ite_true, ite_false,
    Nat.zero_sub, sub_zero, add_zero]
  have h1 : n+2-1=n+1 := Nat.succ_sub_one (n+1)
  have h2 : n+1-2=n-1 := Nat.add_sub_add_right n 1 1
  rw [h1,h2]
  simp [hn]

private theorem homogeneous_support_coords (m : ℕ) (p : MvPolynomial (Fin 3) ℤ)
    (hp : p.IsHomogeneous m) (d : Fin 3 →₀ ℕ) (hd : d ∈ p.support) :
    d 0 + d 1 + d 2 = m := by
  have h := hp.degree_eq_sum_deg_support hd
  change m = d.sum (fun _ e => e) at h
  rw [Finsupp.sum_fintype] at h
  · simpa only [Fin.sum_univ_three] using h.symm
  · intro; rfl

private theorem boundary_monomial (d : Fin 3 →₀ ℕ) (r : ℤ) :
    boundary (monomial d r) = if d 2=0 then Polynomial.C r * Polynomial.X^(d 0) else 0 := by
  have hm : (monomial d r : MvPolynomial (Fin 3) ℤ) = r • mono (d 0) (d 1) (d 2) := by
    simp [mono,smul_monomial,trip_coordinates]
  rw [hm,map_zsmul,boundary_mono]
  split_ifs <;> simp [Polynomial.smul_eq_C_mul]

private theorem boundary_coeff (m k : ℕ) (hk : k≤m) (p : MvPolynomial (Fin 3) ℤ)
    (hp : p.IsHomogeneous m) :
    (boundary p).coeff k = p.coeff (trip k (m-k) 0) := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum,Polynomial.finsetSum_coeff,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := homogeneous_support_coords m p hp d hd
  rw [boundary_monomial]
  by_cases hc : d 2=0
  · rw [ite_eq_left hc,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,coeff_monomial]
    have he : (d = trip k (m-k) 0) ↔ k=d 0 := by
      rw [← trip_coordinates d,trip_inj]
      simp only [trip_apply_zero]
      omega
    simp only [he]
    by_cases hkd : k=d 0 <;> simp only [hkd,ite_true,ite_false,mul_one,mul_zero]
  · rw [ite_eq_right hc,Polynomial.coeff_zero,coeff_monomial]
    have he : trip k (m-k) 0 ≠ d := by
      exact ne_of_apply_ne (fun v : Fin 3 →₀ ℕ => v 2) (by simpa only [trip_apply_two] using Ne.symm hc)
    simp [Ne.symm he]

private theorem alt_boundary_homogeneous (n : ℕ) (hn : 1≤n) (p : MvPolynomial (Fin 3) ℤ)
    (hp : p.IsHomogeneous (2*n)) :
    altCoeff ![n,n,0] p = (boundary p).coeff n - (boundary p).coeff (n+1) := by
  rw [alt_boundary n hn, boundary_coeff (2*n) n (by omega) p hp,
    boundary_coeff (2*n) (n+1) (by omega) p hp]
  have h1 : 2*n-n=n := by simpa only [two_mul] using Nat.add_sub_cancel_left n n
  have h2 : 2*n-(n+1)=n-1 := by simpa only [two_mul] using Nat.add_sub_add_left n n 1
  rw [h1,h2]

private theorem psum_homogeneous (a : ℕ) : (psum (Fin 3) ℤ a).IsHomogeneous a := by
  rw [psum_three]
  exact ((isHomogeneous_X_pow 0 a).add (isHomogeneous_X_pow 1 a)).add
    (isHomogeneous_X_pow 2 a)

private theorem minus_homogeneous (l : List ℕ) : (minusProd l).IsHomogeneous (2*l.sum) := by
  induction l with
  | nil => simpa [minusProd] using (isHomogeneous_one (Fin 3) ℤ : (1 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 0)
  | cons a l ih =>
    change ((psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a)) * minusProd l).IsHomogeneous _
    have hh : (psum (Fin 3) ℤ a ^ 2).IsHomogeneous (2*a) := by
      simpa [mul_comm] using (psum_homogeneous a).pow 2
    simpa only [List.sum_cons,Nat.mul_add] using (hh.sub (psum_homogeneous (2*a))).mul ih

private theorem plus_homogeneous (l : List ℕ) : (plusProd l).IsHomogeneous (2*l.sum) := by
  induction l with
  | nil => simpa [plusProd] using (isHomogeneous_one (Fin 3) ℤ : (1 : MvPolynomial (Fin 3) ℤ).IsHomogeneous 0)
  | cons a l ih =>
    change ((psum (Fin 3) ℤ a ^ 2 + psum (Fin 3) ℤ (2*a)) * plusProd l).IsHomogeneous _
    have hh : (psum (Fin 3) ℤ a ^ 2).IsHomogeneous (2*a) := by
      simpa [mul_comm] using (psum_homogeneous a).pow 2
    simpa only [List.sum_cons,Nat.mul_add] using (hh.add (psum_homogeneous (2*a))).mul ih

private theorem minus_symmetric (l : List ℕ) : (minusProd l).IsSymmetric := by
  induction l with
  | nil => simp [minusProd]
  | cons a l ih =>
    change ((psum (Fin 3) ℤ a ^ 2 - psum (Fin 3) ℤ (2*a)) * minusProd l).IsSymmetric
    have hh := (psum_isSymmetric (Fin 3) ℤ a).mul (psum_isSymmetric (Fin 3) ℤ a)
    rw [← pow_two] at hh
    exact (hh.sub (psum_isSymmetric (Fin 3) ℤ (2*a))).mul ih

private theorem symMono_detector (m a b c : ℕ) (h : a+b+c=m) (hm : m%2=0) :
    evenSum m (symMono a b c) = detector m (symMono a b c) := by
  have hl : evenSum m (symMono a b c) = symWeight a b c := by
    simp only [symMono,map_add]
    rw [evenSum_mono m a b c h, evenSum_mono m a c b (by omega),
      evenSum_mono m b a c (by omega), evenSum_mono m b c a (by omega),
      evenSum_mono m c a b (by omega), evenSum_mono m c b a (by omega)]
    rfl
  have hd (x z : ℕ) : difference (x:ℤ) z =
      ((if x=z then 1 else 0) - (if x=z+1 then 1 else 0) : ℤ) := by
    unfold difference
    have he : (x:ℤ)=(z:ℤ)+1 ↔ x=z+1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Int.natCast_inj (m := x) (n := z+1))
    simp [he]
  rw [hl,sym_detector a b c (by omega),principal_symMono m a b c h]
  simp only [symDifference,hd]

private theorem coefficient_detector (m : ℕ) (hm : m%2=0) (p : MvPolynomial (Fin 3) ℤ)
    (hp : p.IsHomogeneous m) (hs : p.IsSymmetric) :
    evenSum m p = detector m p := by
  have hc : evenSum m (symmetrize p) = detector m (symmetrize p) := by
    classical
    conv_lhs => rw [p.as_sum]
    conv_rhs => rw [p.as_sum]
    simp only [map_sum,symmetrize_monomial,map_zsmul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [symMono_detector m (d 0) (d 1) (d 2) (homogeneous_support_coords m p hp d hd) hm]
  rw [symmetrize_symmetric p hs,map_nsmul,map_nsmul] at hc
  simp only [nsmul_eq_mul] at hc
  omega

private theorem detector_minus (l : List ℕ) : detector (2*l.sum) (minusProd l) =
    (2:ℤ)^l.length * ((triProd l).coeff l.sum - (triProd l).coeff (l.sum+1)) := by
  have hc : (2:Polynomial ℤ)^l.length = Polynomial.C ((2:ℤ)^l.length) := by exact Polynomial.C_pow.symm
  have hk (k : ℕ) : (principal (minusProd l)).coeff (k+l.sum) =
      (2:ℤ)^l.length * (triProd l).coeff k := by
    rw [principal_minus,hc,mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul]
  have h0 := hk l.sum
  have h1 := hk (l.sum+1)
  rw [show l.sum+l.sum=2*l.sum by omega] at h0
  rw [show l.sum+1+l.sum=2*l.sum+1 by omega] at h1
  rw [detector_apply,h0,h1]
  ring

private theorem left_coefficient (l : List ℕ) : evenSum (2*l.sum) (minusProd l) =
    (2:ℤ)^l.length * ((triProd l).coeff l.sum - (triProd l).coeff (l.sum+1)) := by
  rw [coefficient_detector (2*l.sum) (by omega) (minusProd l)
    (minus_homogeneous l) (minus_symmetric l),detector_minus]

private theorem right_coefficient (l : List ℕ) (hn : 1≤l.sum) (hl : ∀ a∈l, 0<a) :
    altCoeff ![l.sum,l.sum,0] (plusProd l) =
      (2:ℤ)^l.length * ((triProd l).coeff l.sum - (triProd l).coeff (l.sum+1)) := by
  rw [alt_boundary_homogeneous l.sum hn (plusProd l) (plus_homogeneous l),boundary_plus l hl]
  have hc : (2:Polynomial ℤ)^l.length = Polynomial.C ((2:ℤ)^l.length) := by exact Polynomial.C_pow.symm
  rw [hc,Polynomial.coeff_C_mul,Polynomial.coeff_C_mul]
  ring

private theorem list_identity (l : List ℕ) (hn : 1≤l.sum) (hl : ∀ a∈l, 0<a) :
    ((evTypes l).map fun τ => ∑ μ ∈ R3 (2*l.sum), (-1:ℤ)^τ.length * frobChar μ τ).sum =
      ((evTypes l).map fun τ => frobChar ![l.sum,l.sum,0] τ).sum := by
  rw [ev_left,ev_right,left_coefficient,right_coefficient l hn hl]

theorem result : claim := by
  intro n hn lam
  have hsum : lam.parts.toList.sum=n := by simpa using lam.parts_sum
  have hpos : ∀ a∈lam.parts.toList, 0<a := by
    intro a ha
    exact lam.parts_pos (by simpa using ha)
  have hh := list_identity lam.parts.toList (by omega) hpos
  simpa only [hsum] using hh

end D5.S3.Combinatorics.Partitions.HemmerStraubWestrem
