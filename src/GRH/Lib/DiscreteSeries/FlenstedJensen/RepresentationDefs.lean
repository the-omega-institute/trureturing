import GRH.Lib.General.LinearAlgebra.PartialDerivComm
import GRH.Lib.DiscreteSeries.Haar.CompactDualMeasure
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

Part of: Lowest K-type and Casimir value determine a discrete series coefficient; analytic vectors
(known result; see Lib.DiscreteSeries.Rigidity.CasimirGrowth).

This file: Parameters, lowest K-type, Flensted-Jensen integral, coefficient, degree and kernel for
U(p,q). Holomorphic functions of weight u on G·B, highest coefficient, dominance, torus.
gl_n-modules, unitarisable Banach representations, derivatives, K-highest vectors, Casimir elements,
root cone. -/

noncomputable section

open Finset _root_.Int _root_.Matrix _root_.Module ComplexConjugate Equiv Fintype

variable {n : Type} [Fintype n] (J : Matrix n n ℂ) (l : n → ℤ) {ε : n → ℤˣ}

/-- The Lie algebra of U(J): the real vector space of complex matrices X with X*J + JX = 0. -/
def unitaryLie := (⟨⟨⟨{X | Xᴴ * J + J * X = 0}, by grind [conjTranspose_add, add_mul, mul_add]⟩, by
    simp⟩, by simp_all [star, ← smul_add]⟩ : Submodule ℝ _)

open Norms.Operator in
/-- For X with X*J+JX=0, the matrix exponential exp X as an element of the group U(J). -/
@[simps! coe_val] def expU {J} (X : @unitaryLie n _ J) : U J := ⟨X.1.isUnit_exp.unit, by
  simpa [U, ← exp_conjTranspose] using! SemiconjBy.exp_neg_mul_mul_exp_eq_self
    (neg_mul _ J ▸ eq_neg_of_add_eq_zero_right X.2 :)⟩

/-- The function m_l(g): the product over t ∈ ℤ of the principal minor of g on {i : l_i ≥ t},
each factor with t ≤ 0 divided by det g. -/
def weightMinors g := ∏ᶠ t, principalMinor g (t ≤ l ·) / ite (t ≤ 0) g.det 1

/-- For an index set of size n and a natural number A, the real number 500n³+A. -/
abbrev gapThreshold n [Fintype n] (A : ℕ) : ℝ := 500 * card n ^ 3 + A

/-- The vector with i-th entry #{j : r(i,j), l_j < l_i} − #{j : r(i,j), l_i < l_j}: the sum of
the roots selected by r that are positive for l. -/
def twoRho r [DecidableRel r] i := (#{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j} : ℤ)

/-- The integer vector μ with entries (l_i + 2ρ_i)/2 rounded down, ρ the half sum of roots
positive for l; it is λ+ρ for a parameter l = 2λ. -/
def paramAddRho i := (l i + twoRho l ⊤ i) / 2

/-- For l = 2λ, the product of λ_i − λ_j over all pairs of indices with λ_j < λ_i, divided by
∏_{i<n} i!. -/
def weylDimensionPoly := (∏ i, ∏ j with l j < l i, (l i - l j : ℝ) / 2) / ∏ i ∈ range (card n),
  ↑i.factorial

/-- The subgroup U(diag ε)∩U(n) of U(diag ε), consisting of the elements that are unitary
matrices. -/
def maxCompactU (ε : n → ℤˣ) := (U 1).subgroupOf (U (signMatrix ε))

instance (ε : n → ℤˣ) : CompactSpace (maxCompactU ε) :=
    ((isClosed_U _).isClosedEmbedding_subtypeVal.restrictPreimage _).compactSpace (Y := U 1)

/-- The Haar measure of total mass one on the compact group K=U(diag ε)∩U(n). -/
def haarK (ε : n → ℤˣ) : MeasureTheory.Measure (maxCompactU ε) := .haarMeasure ⊤

/-- For a relation r on indices, the continuous complex-linear map on matrices keeping entry
(i,j) when r(i,j) holds and replacing it by zero otherwise. -/
@[simp] def entryMask r [DecidableRel r] := (⟨⟨(of fun i j ↦ if r i j then · i j
  else 0), by aesop⟩, by aesop⟩ : Matrix n n ℂ →ₗ[ℂ] _).toContinuousLinearMap

/-- For signs ε and a matrix g, the matrix keeping the entries g_ij with ε_i=ε_j and having zero
elsewhere. -/
def blockDiagPart (ε : n → ℤˣ) := entryMask (ε · = ε ·)

/-- Integer vectors indexed by n, attached to the signs ε; they serve as doubled Harish-Chandra
parameters l = 2λ and as integral weights of U(diag ε). -/
abbrev HCParam {n : Type*} (_ : n → ℤˣ) := n → ℤ

/-- The integer vector l, regarded as a doubled parameter or weight for the signs ε. -/
abbrev toHCParam (ε : n → ℤˣ) (l : n → ℤ) : HCParam ε := l

/-- The same integer vector l, regarded for the signs all equal to 1, that is for the compact
group U(n). -/
abbrev HCParam.compactForm (l : HCParam ε) := toHCParam 1 l

/-- For an integral weight l, the number c_l = ∫_K |m_l(k)|² dk, with K = U(diag ε) ∩ U(n) of
mass one and m_l = `weightMinors`. -/
abbrev HCParam.kTypeNormSq (l : HCParam ε) := ∫ k, ‖weightMinors l k‖ ^ 2 ∂haarK ε

/-- l = 2λ is a parameter of gap h: λ has distinct entries in (n−1)/2 + ℤ, and |λ_i − λ_j| ≥ h
whenever ε_i ≠ ε_j. -/
class HCParam.HasGap (l : HCParam ε) (h : outParam ℝ) where
  injective : l.Injective
  parity i : Even (l i + card n - 1)
  gap i j : ε i ≠ ε j → 2 * h ≤ |l i - l j|

/-- l = 2λ is a parameter of gap 500n³ + A, where n is the size of the index set. -/
abbrev HCParam.HasLargeGap (l : HCParam ε) A := l.HasGap (gapThreshold n A)

/-- For a parameter l = 2λ, the weight Λ = λ + ρ − 2ρ_c, with ρ, ρ_c the half sums of all and of
the compact roots positive for λ. -/
def HCParam.lowestKType (l : HCParam ε) : HCParam ε := fun i ↦
  paramAddRho l i - twoRho l (ε · = ε ·) i

/-- For l = 2λ, the real number c(λ) = |λ|² − |ρ|², with ρ the half sum of the roots positive
for λ. -/
def HCParam.casimirValue (l : HCParam ε) := ∑ i, (l i ^ 2 - twoRho l ⊤ i ^ 2 : ℝ) / 4

/-- Flensted-Jensen's integral, normalised: c_Λ⁻¹ ∫_K m_Λ(gk) conj(m_Λ(k)) / m_{−μ}(k*zk) dk for
matrices g, z, with μ = λ + ρ, c_Λ = ∫_K |m_Λ|², l = 2λ. -/
def HCParam.flenstedJensen (l : HCParam ε) (g z : Matrix n n ℂ) :=
    (∫ k, weightMinors l.lowestKType (g * k) * conj (weightMinors l.lowestKType k) / weightMinors
  (-paramAddRho l) (k.1.1.1ᴴ * z * k) ∂haarK ε) / l.lowestKType.kTypeNormSq

/-- The function ψ_λ on matrices: the normalised Flensted-Jensen integral `HCParam.flenstedJensen`
at (a, a⁻¹g), with a the block diagonal part of g for the signs ε. -/
def HCParam.dsCoeff (l : HCParam ε) (g : Matrix n n ℂ) :=
  l.flenstedJensen (blockDiagPart ε g) ((blockDiagPart ε g)⁻¹ * g)

variable (l : HCParam ε) {α β} [Fintype α] [Fintype β] (a : α → ℤˣ) {b : β → ℤˣ}

/-- The degree deg_λ: the inverse of the integral of |ψ_λ(g)|² over U(diag ε), for l = 2λ. -/
def HCParam.formalDegree := (∫ g : USign ε, ‖l.dsCoeff g‖ ^ 2)⁻¹

/-- The function e_λ on U(diag ε) given by e_λ(g) = deg_λ times the complex conjugate of ψ_λ(g),
for l = 2λ. -/
def HCParam.dsKernel (g : USign ε) := l.formalDegree * conj (l.dsCoeff g)

export HCParam (kTypeNormSq HasGap lowestKType flenstedJensen dsCoeff formalDegree dsKernel)

/-- The number of indices i with sign a_i = −1. -/
@[local simp] def negCount := card {x // a x = -1}

lemma negCount_neg_add : negCount (-a) + negCount a =
  card α := by simp [← units_ne_iff_eq_neg, card_subtype_le]

@[simp] lemma negCount_sumElim : negCount (a ⊕ᵥ b) = negCount a + negCount b :=
  (card_congr subtypeSum).trans card_sum

@[simp] lemma negCount_one_and_neg_one : negCount (1 : α → ℤˣ) = 0 ∧ negCount (-1 : α → _) =
  card α := by simp

lemma exists_equiv_of_card_neg {a} (h : card α = card β) (h' : negCount a = negCount b) : ∃ e :
    α ≃ β, b ∘ e = a := ⟨_, funext (ofFiberEquiv_map fun c ↦ equivOfCardEq (by
  fin_cases c <;> simp_all [(@units_ne_iff_eq_neg _ 1).not_right]))⟩

/-- For an integer vector w and a complex square matrix b, the product over i of the diagonal
entries b_ii raised to the power w_i. -/
def diagChar (w : n → ℤ) (b : Matrix n n ℂ) := ∏ i, b i i ^ w i

/-- The matrix b is invertible and upper triangular for the order o: b_ij = 0 whenever o_j <
o_i. -/
def IsBorelMatrix (o : n → ℤ) (b : Matrix n n ℂ) := b.BlockTriangular o ∧ b.det ≠ 0

/-- The weight w is K-dominant for the order o: w_j ≤ w_i whenever ε_i = ε_j and o_i < o_j. -/
def IsKDominant (ε : n → ℤˣ) (o w : n → ℤ) := ∀ i j, ε i = ε j → o i < o j → w j ≤ w i

/-- The order o has distinct values and puts every index of sign +1 before every index of sign
−1. -/
def IsPosFirstOrder (ε : n → ℤˣ) (o : n → ℤ) := o.Injective ∧ ∀ i j, ε i = 1 → ε j = -1 → o i < o j

/-- The condition on signs ε, integer vector w and natural number γ that w_i + γ ≤ w_j whenever
ε_i = +1 and ε_j = −1. -/
def HasHolGap (ε : n → ℤˣ) (w : n → ℤ) (γ : ℕ) := ∀ i j, ε i = 1 → ε j = -1 → w i + γ ≤ w j

/-- The algebra of complex matrices commuting with diag(ε), that is the block diagonal matrices
for the signs ε. -/
def blockDiagAlg (ε : n → ℤˣ) := Subalgebra.centralizer ℂ {signMatrix ε}

open Norms.L2Operator

variable {Φ : Type} (ε : n → ℤˣ) (o : n → ℤ) [Fintype Φ] (b : Matrix n n ℂ)

/-- F on U(diag ε)^Φ is holomorphic of weight u: some F' is analytic at all hb with F'(hb) = b^u
F(h), for b invertible o-triangular and h, b commuting with diag(ε'). -/
def IsHolOfWeight (u : Φ → _) (F : _ → ℂ) (ε' : n → ℤˣ := 1) := ∃ F', ∀ h b : Φ → _,
  (∀ τ, IsBorelMatrix o (b τ)) →
  (∀ τ, ↑(h τ : USign ε) ∈ blockDiagAlg ε' ∧ b τ ∈ blockDiagAlg ε') → letI z τ := h τ * b τ
  AnalyticAt ℂ F' z ∧ F' z = (∏ τ, diagChar (u τ) (b τ)) * F h

/-- For signs ε, weight o and matrix b, the quotient m_{o+c·1₊}(b)/m_{c·1₊}(b) of products of
principal minors, with c = 2∑|o_j| and 1₊ indicating sign +1. -/
def holMinors := letI c i := ite (ε i = 1) (2 * ∑ j, |o j|) 0
         weightMinors (fun i ↦ o i + c i) b / weightMinors c b

/-- For weights u_τ and a tuple h in U(diag ε)^Φ, the product over τ of the quotients of minors
`holMinors` of weight u_τ at h_τ. -/
def holMinorsPi (u : Φ → _) (h : Φ → USign ε) := ∏ τ, holMinors ε (u τ) (h τ)

/-- For a tuple t of complex numbers of modulus one, the diagonal matrix diag(t) as an element
of U(diag ε). -/
def diagTorus (t : n → Circle) : USign ε := ⟨IsUnit.unit (a := diagonal (t ·))
  (by simp [Pi.isUnit_iff]), by simp [U, signMatrix, field, ← Circle.coe_inv_eq_conj]⟩

/-- A gl_n(ℂ)-module structure on a complex vector space M: a linear map from n×n matrices to
endomorphisms of M that respects commutators. -/
structure GlModule (n M) [Fintype n] [AddCommGroup M] [Module ℂ M] where
  ρ : Matrix n n ℂ →ₗ[ℂ] End ℂ M
  map_bracket X Y : ρ (X * Y - Y * X) = ρ X * ρ Y - ρ Y * ρ X

variable {X M} [NormedAddCommGroup X] [NormedSpace ℂ X] [AddCommGroup M] [Module ℂ M] {J : Matrix n
  n ℂ} (A) (π : U J →* X →L[ℂ] X) {ε : n → ℤˣ} (l : HCParam ε) (ι : M →ₗ[ℂ] X) (ρ : GlModule n M)

/-- The representation π of U(J) on X is strongly continuous with ‖π(g)‖ ≤ c‖g‖^A, and the
bounded form B is hermitian, positive definite and π-invariant. -/
structure IsUnitaryRep (B : X →L⋆[ℂ] X →L[ℂ] ℂ) where
  continuous x : Continuous (π · x)
  invariant g x y : B (π g x) (π g y) = B x y
  conj_symm x y : starRingEnd ℂ (B x y) = B y x
  pos : ∀ x ≠ 0, 0 < (B x x).re
  growth : ∃ c, ∀ g, ‖π g‖ ≤ c * ‖g.1.1‖ ^ A

instance : CoeFun (GlModule n M) fun _ ↦ Matrix n n ℂ → End ℂ M := ⟨(·.ρ)⟩

/-- For a gl_n-module and indices a, b, the endomorphism by which the elementary matrix E_{ab}
acts. -/
abbrev GlModule.E a b := ρ (.single a b 1)

/-- For a gl_n(ℂ)-module and a subspace stable under all X, the gl_n(ℂ)-module structure on that
subspace obtained by restricting the action. -/
def GlModule.restrictTo p (h : ∀ X, p ∈ (ρ X).invtSubmodule) : GlModule n p := by
  use! (.restrict _ <| h ·) <;> aesop (add simp map_bracket)

/-- The gl_n-module ρ on M is the derivative of π along ι: d/dt π(exp tY)ιv at t = 0 equals
ι(ρ(Y)v) for Y in Lie U(J), v in M. -/
def IsDerivedAction := ∀ Y v, HasDerivAt (fun t : ℝ ↦ π (expU (t • Y)) (ι v)) (ι (ρ Y v)) 0

/-- The vector x is killed by the compact raising operators for l: E_ab x = 0 whenever ε_a = ε_b
and l_b < l_a. -/
@[simp] abbrev GlModule.IsCompactPrimitive x := ∀ a b, ε a = ε b → l b < l a → ρ.E a b x = 0

/-- The vector x is K-highest of weight ν: E_aa x = ν_a x for all a, and E_ab x = 0 whenever ε_a
= ε_b and l_b < l_a. -/
def HCParam.IsKHighest (ν : n → ℤ) x := (∀ a, ρ.E a a x = (ν a : ℂ) • x) ∧ ρ.IsCompactPrimitive l x

/-- The set of integer vectors β with ⟨o, β⟩ ≤ 0 for every integer vector o such that o_i < o_j
whenever l_i > l_j. -/
def HCParam.rootCone := {β | ∀ o, (∀ i j, l j < l i → o i < o j) → o ⬝ᵥ β ≤ (0 : ℤ)}

/-- The maps c(g) : M → X form a coefficient map for ρ: for Y in Lie U(J), the derivative of t ↦
c(g exp tY)v is c(g exp tY)(ρ(Y)v). -/
def GlModule.IsCoeffMap (c : U J → M →ₗ[ℂ] X) := ∀ g Y v t, HasDerivAt (fun t : ℝ ↦
  c (g * expU (t • Y)) v) (c (g * expU (t • Y)) (ρ Y v)) t

/-- For a relation r on indices, the endomorphism Σ E_ab E_ba of a gl_n-module, summed over the
pairs (a,b) with r(a,b). -/
def GlModule.casimir r [DecidableRel r] := ∑ a, ∑ b with r a b, ρ.E a b * ρ.E b a

abbrev GlModule.casimirK (ε : n → ℤˣ) (ρ : GlModule n M) := ρ.casimir (ε · = ε ·)
