import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.FlenstedJensen.RepresentationDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics
(known result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Oscillator actions on Fock polynomials, matched parameters, joint harmonics. -/

noncomputable section


open Matrix Fintype MvPolynomial Sgn Finset GlModule
variable {R C ι : Type} [Fintype R] [Fintype C] [Fintype ι] (σ : ℤˣ) (ε : R → ℤˣ) (ε' : C → ℤˣ)

omit [Fintype R] in
lemma canonical_commutation η (a b : R) P : raiseOp η a (raiseOp η b P) =
  raiseOp η b (raiseOp η a P) ∧ lowerOp η a (lowerOp η b P) = lowerOp η b (lowerOp η a P) ∧
  lowerOp η a (raiseOp η b P) = raiseOp η b (lowerOp η a P) + ite (a = b) P 0 := by
  aesop (add simp [raiseOp, lowerOp, _root_.pderiv_comm, mul_left_comm])

/-- For a sign σ, sign vectors ε, ε' and an index pair (r,c), the sign σ ε_r ε'_c. -/
def pairSign i := σ * ε (Prod.fst i) * ε' i.2

/-- The data of a dual pair with signs ε, ε' in Fock space: a sign σ, integers γ, γ', and a
bijection naming the variable X_rc of row r and column c. -/
structure FockDualPair (ε : R → ℤˣ) (ε' : C → ℤˣ) ι where (σ : ℤˣ) (γ γ' : ℤ) (varEquiv : R × C ≃ ι)

/-- The dual pair data with sign σ = 1, integers γ and γ' + |R|, and variables indexed by R × C
itself. -/
abbrev FockDualPair.std γ γ' := (⟨1, γ, γ' + card R, .refl _⟩ : FockDualPair ε ε' _)

variable {ε ε'} (T : FockDualPair ε ε' ι) (l : HCParam ε) (l' : HCParam ε') (Φ : MvPolynomial ι ℂ)

namespace FockDualPair

/-- The dual pair data with rows and columns exchanged: sign −σ, integers γ', γ in this order,
and the same variables. -/
abbrev swap : FockDualPair ε' ε ι := ⟨-T.σ, T.γ', T.γ, .trans (.prodComm ..) T.varEquiv⟩

omit [Fintype R] [Fintype C] [Fintype ι] in
lemma swap_swap : T.swap.swap = T := by simp [swap]; rfl

/-- The sign σ ε_r ε'_c of the variable X_rc. -/
abbrev varSign := pairSign T.σ ε ε'

/-- The signs of the variables as a function on ι: the variable named by (r, c) has sign σ ε_r
ε'_c. -/
@[simp] abbrev η := T.varSign ∘ T.varEquiv.symm

/-- The weight of the vacuum on a row of sign s: γ minus the number of columns c with σ s ε'_c =
−1. -/
def vacuumWeight s := T.γ - #{c | T.σ * s * ε' c ≠ 1}

/-- The entry Λ_r of the lowest K-type for l = 2λ minus the weight of the vacuum on a row of
sign ε_r. -/
abbrev relWeight r := l.lowestKType r - T.vacuumWeight (ε r)

/-- The integer l_r − 2γ + |C|; for l = 2λ it is twice the centred parameter λ_r − γ + |C|/2. -/
@[simp] abbrev centredParam r := l r - 2 * T.γ + card C

attribute [local simp] add_mul mul_add ite_and mul_assoc glOp single_apply

/-- The row action of gl(R) on polynomials: E_ab acts by s·Σ_c A_(a,c)B_(b,c) + γδ_ab, A =
`raiseOp`, B = `lowerOp`, s = 1 if ε_a = ε_b, else σ. -/
def oscRows : GlModule R (MvPolynomial ι ℂ) := let U a b := ((if ε a = ε b then 1 else T.σ : ℂ) •
          ∑ c, glOp T.η (T.varEquiv (a, c)) (T.varEquiv (b, c)) + if a = b then ↑T.γ else 0)
  .mk (liftLinear ℂ (.smulRight .id <| U · ·)) (by
        repeat intro; induction ‹_› using Matrix.induction_on' <;> simp_all [add_sub_add_comm]
        simp [liftLinear_apply, mul_apply, mul_comm]
        simp [U, canonical_commutation, apply_ite (raiseOp ..), -ite_smul,
          DFunLike.ext_iff, -zsmul_eq_mul, ← ite_zero_smul, ite_add_zero, ← smul_sum]
        intro; rw [sum_comm]; match_scalars <;> norm_cast <;> aesop)

/-- The operator Σ A_(a,c)B_(b,c) over the columns c where X_ac has sign −1; for ε_a ≠ ε_b it is
the Laplacian −Σ ∂_ac∂_bc. -/
def fockLaplacian a b := ∑ c with T.varSign (a, c) = -1,
  glOp T.η (T.varEquiv (a, c)) (T.varEquiv (b, c))

/-- The polarisation Σ X_ac ∂Φ/∂X_bc of the polynomial Φ, summed over the columns c where X_bc
has sign s. -/
def polarisation a b s := ∑ c with T.varSign (b, c) = s,
  X (T.varEquiv (a, c)) * Φ.pderiv (T.varEquiv (b, c))

/-- Row r and column c are matched: ξ = l_r − 2γ + |C| equals −(l'_c − 2γ' + |R|), and σ ε_r
ε'_c ξ exceeds the absolute value of |R| − |C|. -/
abbrev IsMatchedPair r c := T.centredParam l r = -T.swap.centredParam l' c ∧
  |(card R - card C : ℤ)| < T.varSign (r, c) * T.centredParam l r

/-- Φ is harmonic for the row group: ∂_ac∂_bc Φ = 0 whenever ε_a ≠ ε_b, so no monomial has
variables of opposite signs in one column. -/
def IsHarmonic := ∀ a b c, ε a ≠ ε b → (Φ.pderiv (T.varEquiv (b, c))).pderiv (T.varEquiv (a, c)) = 0

/-- Φ is killed by the Laplacians of the row group: for ε_a ≠ ε_b, Σ ∂_ac∂_bc Φ = 0, summed over
the columns c where X_ac has sign −1. -/
def IsRowHarmonic := ∀ a b, ε a ≠ ε b → T.fockLaplacian a b Φ = 0

/-- The polynomial Φ is nonzero, killed by the row and column Laplacians
(`FockDualPair.IsRowHarmonic`), K-highest of weight Λ for l, and killed by the compact raising
column operators for l'. -/
def IsPreJointHarmonic := Φ ≠ 0 ∧ T.swap.oscRows.IsCompactPrimitive l' Φ ∧ T.IsRowHarmonic Φ ∧
  l.IsKHighest T.oscRows l.lowestKType Φ ∧ T.swap.IsRowHarmonic Φ

/-- Φ is a nonzero polynomial, harmonic for both groups (`FockDualPair.IsHarmonic`), K-highest of
weight ν for the row action and K'-highest of weight ν' for the column action. -/
def IsJointHighest ν ν' := Φ ≠ 0 ∧ l'.IsKHighest T.swap.oscRows ν' Φ ∧ T.IsHarmonic Φ ∧
  l.IsKHighest T.oscRows ν Φ ∧ T.swap.IsHarmonic Φ

omit [Fintype ι] in
/-- In the column action (row action of the swap of T), E_ab acts by −s·Σ_r B_(r,a) A_(r,b) +
γ'δ_ab, with A, B the operators `raiseOp`, `lowerOp` for the signs of the
variables, s = 1 if ε'_a = ε'_b, else σ. -/
lemma swap_oscRows_E a b : T.swap.oscRows.E a b = (ite (ε' a = ε' b) 1 T.σ : ℂ) • -∑ r,
  lowerOp T.η (T.varEquiv (r, a)) * raiseOp T.η (T.varEquiv (r, b)) + ite (a = b) ↑T.γ' 0 := by
  simp [oscRows, E, smul_sum, ← sum_neg_distrib, raiseOp, lowerOp, pairSign,
    mul_right_comm T.σ]; congr; aesop

end FockDualPair

export FockDualPair
  (vacuumWeight oscRows fockLaplacian polarisation IsMatchedPair IsHarmonic swap_oscRows_E)

/-- The parameters l = 2λ, l' = 2λ' have gap 500(n+n')³; with ξ_r = λ_r−γ+n'/2, ξ'_c = λ'_c−γ'+n/2,
each ξ_r is some −ξ'_c or |ξ_r| < (n−n')/2, symmetrically for ξ'_c, and matched pairs have
σε_rε'_cξ_r > |n−n'|/2. -/
structure IsMatch where
  gap : l.HasGap (500 * (card R + card C) ^ 3)
  gap' : l'.HasGap (500 * (card C + card R) ^ 3)
  left r : (∃ c, T.IsMatchedPair l l' r c) ∨ |T.centredParam l r| < card R - card C
  right c : (∃ r, T.IsMatchedPair l l' r c) ∨ |T.swap.centredParam l' c| < card C - card R

/-- Joint harmonic: l, l' match and Φ ≠ 0 is highest of weights Λ, Λ' for the row and column
actions and satisfies `IsHarmonic` along columns and along rows. -/
structure IsJointHarmonic extends IsMatch T l l' where
  isJointHighest : T.IsJointHighest l l' Φ l.lowestKType l'.lowestKType
