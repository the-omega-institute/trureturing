/- GID: D5/S3/Weil/Budget/FiniteWeylBudgetBounds
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/FiniteWeylBudgetBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Hermitian pencils converge monotonically to the two parity budget endpoints. -/

import D5.S3.Weil.Budget.OddTestBudgetUpperBound
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * D5 body-shape searches found the canonical finite odd quotient in
     `OddTestBudgetUpperBound` and the general parity interval in
     `ParityWeylInterval`; neither exposes both finite matrix pencils and both
     Galerkin limits.
   * Pinned Mathlib has no exact finite Weyl-budget theorem. The proof uses its
     rank-one positive-semidefinite matrix, conditional sup/inf, and monotone
     order-convergence lemmas directly.
   * Public Lean code searches for finite Hermitian-pencil Galerkin budget
     bounds found no exact third-party theorem. -/

open Filter Matrix Set Topology
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.FiniteWeylBudgetBounds

open D5.S3.Weil.Budget.OddTestBudgetUpperBound

/-- Kernel positivity makes the two finite rank-one Hermitian pencils cut out
their generalized Rayleigh interval. Nested quotient families that approximate
every full-test quotient from the appropriate side give monotone convergence to
the full endpoints; a crossed finite interval is therefore an explicit
incompatibility certificate. -/
theorem finite_weyl_budget_bounds
    {EvenTest OddTest : Type*}
    (evenDim oddDim : Nat -> Nat)
    (evenBase : forall N, Matrix (Fin (evenDim N)) (Fin (evenDim N)) Complex)
    (oddBase : forall N, Matrix (Fin (oddDim N)) (Fin (oddDim N)) Complex)
    (evenBoundary : forall N, Fin (evenDim N) -> Complex)
    (oddBoundary : forall N, Fin (oddDim N) -> Complex)
    (fullEvenBase : EvenTest -> Real) (fullEvenBoundary : EvenTest -> Complex)
    (fullOddBase : OddTest -> Real) (fullOddBoundary : OddTest -> Complex)
    (referenceBudget : Real) :
    let finiteEvenQuotients := fun N =>
      {q : Real | exists x : Fin (evenDim N) -> Complex,
        star (evenBoundary N) ⬝ᵥ x ≠ 0 /\
          q = -Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) /
            Complex.normSq (star (evenBoundary N) ⬝ᵥ x)}
    let finiteOddQuotients := fun N =>
      oddRayleighQuotients (oddDim N) (oddBase N) (oddBoundary N)
    let fullEvenQuotients :=
      {q : Real | exists x : EvenTest, fullEvenBoundary x ≠ 0 /\
        q = -fullEvenBase x / Complex.normSq (fullEvenBoundary x)}
    let fullOddQuotients :=
      {q : Real | exists x : OddTest, fullOddBoundary x ≠ 0 /\
        q = fullOddBase x / Complex.normSq (fullOddBoundary x)}
    let finiteLower := fun N => referenceBudget + sSup (finiteEvenQuotients N)
    let finiteUpper := fun N => referenceBudget + sInf (finiteOddQuotients N)
    let fullLower := referenceBudget + sSup fullEvenQuotients
    let fullUpper := referenceBudget + sInf fullOddQuotients
    let evenPencil := fun N R =>
      evenBase N + ((R - referenceBudget : Real) : Complex) •
        Matrix.vecMulVec (evenBoundary N) (star (evenBoundary N))
    let oddPencil := fun N R =>
      oddBase N - ((R - referenceBudget : Real) : Complex) •
        Matrix.vecMulVec (oddBoundary N) (star (oddBoundary N))
    let feasible := fun N R =>
      (evenPencil N R).PosSemidef /\ (oddPencil N R).PosSemidef
    ((forall N, (evenBase N).IsHermitian) /\
      (forall N, (oddBase N).IsHermitian) /\
      (forall N x, star (evenBoundary N) ⬝ᵥ x = 0 ->
        0 <= Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x))) /\
      (forall N x, star (oddBoundary N) ⬝ᵥ x = 0 ->
        0 <= Complex.re (star x ⬝ᵥ (oddBase N *ᵥ x))) /\
      (forall N, exists x : Fin (evenDim N) -> Complex,
        star (evenBoundary N) ⬝ᵥ x ≠ 0) /\
      (forall N, exists x : Fin (oddDim N) -> Complex,
        star (oddBoundary N) ⬝ᵥ x ≠ 0) /\
      (forall N, BddAbove (finiteEvenQuotients N)) /\
      (forall N, BddBelow (finiteOddQuotients N)) /\
      (exists x, fullEvenBoundary x ≠ 0) /\
      (exists x, fullOddBoundary x ≠ 0) /\
      BddAbove fullEvenQuotients /\ BddBelow fullOddQuotients /\
      (forall N, finiteEvenQuotients N ⊆ finiteEvenQuotients (N + 1)) /\
      (forall N, finiteOddQuotients N ⊆ finiteOddQuotients (N + 1)) /\
      (forall N, finiteEvenQuotients N ⊆ fullEvenQuotients) /\
      (forall N, finiteOddQuotients N ⊆ fullOddQuotients) /\
      (forall q, q ∈ fullEvenQuotients -> forall epsilon, epsilon > 0 ->
        exists N qN, qN ∈ finiteEvenQuotients N /\ q - epsilon < qN) /\
      (forall q, q ∈ fullOddQuotients -> forall epsilon, epsilon > 0 ->
        exists N qN, qN ∈ finiteOddQuotients N /\ qN < q + epsilon)) ->
    (forall N R, (evenPencil N R).IsHermitian /\ (oddPencil N R).IsHermitian) /\
    (forall N R, (evenPencil N R).PosSemidef <-> finiteLower N <= R) /\
    (forall N R, (oddPencil N R).PosSemidef <-> R <= finiteUpper N) /\
    Monotone finiteLower /\ Antitone finiteUpper /\
    Tendsto finiteLower atTop (nhds fullLower) /\
    Tendsto finiteUpper atTop (nhds fullUpper) /\
    (forall N R, feasible N R <-> R ∈ Icc (finiteLower N) (finiteUpper N)) /\
    (forall N, finiteLower N > finiteUpper N ->
      (forall R, (evenPencil N R).PosSemidef -> finiteLower N <= R) /\
      (forall R, (oddPencil N R).PosSemidef -> R <= finiteUpper N) /\
      ¬ exists R, feasible N R) := by
  let finiteEvenQuotients := fun N =>
    {q : Real | exists x : Fin (evenDim N) -> Complex,
      star (evenBoundary N) ⬝ᵥ x ≠ 0 /\
        q = -Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) /
          Complex.normSq (star (evenBoundary N) ⬝ᵥ x)}
  let finiteOddQuotients := fun N =>
    oddRayleighQuotients (oddDim N) (oddBase N) (oddBoundary N)
  let fullEvenQuotients :=
    {q : Real | exists x : EvenTest, fullEvenBoundary x ≠ 0 /\
      q = -fullEvenBase x / Complex.normSq (fullEvenBoundary x)}
  let fullOddQuotients :=
    {q : Real | exists x : OddTest, fullOddBoundary x ≠ 0 /\
      q = fullOddBase x / Complex.normSq (fullOddBoundary x)}
  let finiteLower := fun N => referenceBudget + sSup (finiteEvenQuotients N)
  let finiteUpper := fun N => referenceBudget + sInf (finiteOddQuotients N)
  let fullLower := referenceBudget + sSup fullEvenQuotients
  let fullUpper := referenceBudget + sInf fullOddQuotients
  let evenPencil := fun N R =>
    evenBase N + ((R - referenceBudget : Real) : Complex) •
      Matrix.vecMulVec (evenBoundary N) (star (evenBoundary N))
  let oddPencil := fun N R =>
    oddBase N - ((R - referenceBudget : Real) : Complex) •
      Matrix.vecMulVec (oddBoundary N) (star (oddBoundary N))
  let feasible := fun N R =>
    (evenPencil N R).PosSemidef /\ (oddPencil N R).PosSemidef
  change _ -> _
  rintro ⟨evenBaseHermitian, oddBaseHermitian, evenKernelNonnegative,
    oddKernelNonnegative, evenNontrivial, oddNontrivial, evenBounded,
    oddBounded, fullEvenNontrivial, fullOddNontrivial, fullEvenBounded,
    fullOddBounded, evenNested, oddNested, evenIncluded, oddIncluded,
    evenApproximation, oddApproximation⟩

  have finiteEvenNonempty (N : Nat) : (finiteEvenQuotients N).Nonempty := by
    obtain ⟨x, hx⟩ := evenNontrivial N
    exact ⟨_, x, hx, rfl⟩
  have finiteOddNonempty (N : Nat) : (finiteOddQuotients N).Nonempty := by
    obtain ⟨x, hx⟩ := oddNontrivial N
    exact ⟨_, x, hx, rfl⟩
  have fullEvenNonempty : fullEvenQuotients.Nonempty := by
    obtain ⟨x, hx⟩ := fullEvenNontrivial
    exact ⟨_, x, hx, rfl⟩
  have fullOddNonempty : fullOddQuotients.Nonempty := by
    obtain ⟨x, hx⟩ := fullOddNontrivial
    exact ⟨_, x, hx, rfl⟩

  have finiteEvenBounded (N : Nat) : BddAbove (finiteEvenQuotients N) :=
    evenBounded N
  have finiteOddBounded (N : Nat) : BddBelow (finiteOddQuotients N) :=
    oddBounded N

  have evenPencilHermitian (N : Nat) (R : Real) :
      (evenPencil N R).IsHermitian := by
    apply (evenBaseHermitian N).add
    apply (Matrix.posSemidef_vecMulVec_self_star (evenBoundary N)).isHermitian.smul
    simp [isSelfAdjoint_iff]
  have oddPencilHermitian (N : Nat) (R : Real) :
      (oddPencil N R).IsHermitian := by
    apply (oddBaseHermitian N).sub
    apply (Matrix.posSemidef_vecMulVec_self_star (oddBoundary N)).isHermitian.smul
    simp [isSelfAdjoint_iff]

  have evenQuadratic (N : Nat) (R : Real)
      (x : Fin (evenDim N) -> Complex) :
      Complex.re (star x ⬝ᵥ (evenPencil N R *ᵥ x)) =
        Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) +
          (R - referenceBudget) *
            Complex.normSq (star (evenBoundary N) ⬝ᵥ x) := by
    dsimp only [evenPencil]
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, Matrix.vecMulVec_mulVec]
    rw [star_dotProduct x (evenBoundary N)]
    simp only [op_smul_eq_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have oddQuadratic (N : Nat) (R : Real)
      (x : Fin (oddDim N) -> Complex) :
      Complex.re (star x ⬝ᵥ (oddPencil N R *ᵥ x)) =
        Complex.re (star x ⬝ᵥ (oddBase N *ᵥ x)) -
          (R - referenceBudget) *
            Complex.normSq (star (oddBoundary N) ⬝ᵥ x) := by
    dsimp only [oddPencil]
    rw [Matrix.sub_mulVec]
    simp only [dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.vecMulVec_mulVec, Complex.sub_re]
    rw [star_dotProduct x (oddBoundary N)]
    simp only [op_smul_eq_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring

  have evenFormIff (N : Nat) (R : Real) :
      (forall x : Fin (evenDim N) -> Complex,
        0 <= Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) +
          (R - referenceBudget) *
            Complex.normSq (star (evenBoundary N) ⬝ᵥ x)) <->
        finiteLower N <= R := by
    constructor
    · intro hForm
      have supBound : sSup (finiteEvenQuotients N) <= R - referenceBudget := by
        apply csSup_le (finiteEvenNonempty N)
        rintro q ⟨x, hx, rfl⟩
        have hPositive : 0 < Complex.normSq (star (evenBoundary N) ⬝ᵥ x) :=
          Complex.normSq_pos.mpr hx
        apply (div_le_iff₀ hPositive).2
        linarith [hForm x]
      dsimp only [finiteLower]
      linarith
    · intro hLower x
      by_cases hx : star (evenBoundary N) ⬝ᵥ x = 0
      · simpa [hx] using evenKernelNonnegative N x hx
      · have hPositive : 0 < Complex.normSq (star (evenBoundary N) ⬝ᵥ x) :=
          Complex.normSq_pos.mpr hx
        have quotientLeSup :
            -Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) /
                Complex.normSq (star (evenBoundary N) ⬝ᵥ x) <=
              sSup (finiteEvenQuotients N) :=
          le_csSup (finiteEvenBounded N) ⟨x, hx, rfl⟩
        have ratioBound :
            -Complex.re (star x ⬝ᵥ (evenBase N *ᵥ x)) /
                Complex.normSq (star (evenBoundary N) ⬝ᵥ x) <=
              R - referenceBudget := by
          dsimp only [finiteLower] at hLower
          linarith
        have scaled := (div_le_iff₀ hPositive).mp ratioBound
        linarith

  have evenPencilIff (N : Nat) (R : Real) :
      (evenPencil N R).PosSemidef <-> finiteLower N <= R := by
    constructor
    · intro hPencil
      apply (evenFormIff N R).mp
      intro x
      rw [← evenQuadratic N R x]
      exact hPencil.re_dotProduct_nonneg x
    · intro hLower
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (evenPencilHermitian N R)
      intro x
      rw [Complex.nonneg_iff]
      refine ⟨?_, (evenPencilHermitian N R).im_star_dotProduct_mulVec_self x |>.symm⟩
      rw [evenQuadratic N R x]
      exact (evenFormIff N R).mpr hLower x

  have oddPencilIff (N : Nat) (R : Real) :
      (oddPencil N R).PosSemidef <-> R <= finiteUpper N := by
    constructor
    · intro hPencil
      have hUpper := odd_test_budget_at_most_upper
        (oddDim N) (oddBase N) (oddBoundary N) referenceBudget R
        (oddNontrivial N) (oddBounded N)
        (fun x _ => by
          rw [← oddQuadratic N R x]
          exact hPencil.re_dotProduct_nonneg x)
      simpa only [finiteUpper, finiteOddQuotients, oddTestUpperEndpoint] using hUpper
    · intro hUpper
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (oddPencilHermitian N R)
      intro x
      rw [Complex.nonneg_iff]
      refine ⟨?_, (oddPencilHermitian N R).im_star_dotProduct_mulVec_self x |>.symm⟩
      rw [oddQuadratic N R x]
      by_cases hx : star (oddBoundary N) ⬝ᵥ x = 0
      · simpa [hx] using oddKernelNonnegative N x hx
      · have hPositive : 0 < Complex.normSq (star (oddBoundary N) ⬝ᵥ x) :=
          Complex.normSq_pos.mpr hx
        have infLeQuotient :
            sInf (finiteOddQuotients N) <=
              Complex.re (star x ⬝ᵥ (oddBase N *ᵥ x)) /
                Complex.normSq (star (oddBoundary N) ⬝ᵥ x) :=
          csInf_le (finiteOddBounded N) ⟨x, hx, rfl⟩
        have ratioBound :
            R - referenceBudget <=
              Complex.re (star x ⬝ᵥ (oddBase N *ᵥ x)) /
                Complex.normSq (star (oddBoundary N) ⬝ᵥ x) := by
          dsimp only [finiteUpper] at hUpper
          linarith
        have scaled := (le_div_iff₀ hPositive).mp ratioBound
        linarith

  have lowerMonotone : Monotone finiteLower := by
    apply monotone_nat_of_le_succ
    intro N
    dsimp only [finiteLower]
    simpa only [add_comm] using add_le_add_left
      (csSup_le_csSup (finiteEvenBounded (N + 1))
        (finiteEvenNonempty N) (evenNested N)) referenceBudget
  have upperAntitone : Antitone finiteUpper := by
    apply antitone_nat_of_succ_le
    intro N
    dsimp only [finiteUpper]
    simpa only [add_comm] using add_le_add_left
      (csInf_le_csInf (finiteOddBounded (N + 1))
        (finiteOddNonempty N) (oddNested N)) referenceBudget

  have lowerIsLUB : IsLUB (range finiteLower) fullLower := by
    constructor
    · rintro _ ⟨N, rfl⟩
      dsimp only [finiteLower, fullLower]
      simpa only [add_comm] using add_le_add_left
        (csSup_le_csSup fullEvenBounded (finiteEvenNonempty N) (evenIncluded N))
        referenceBudget
    · intro z hz
      have supLe : sSup fullEvenQuotients <= z - referenceBudget := by
        apply csSup_le fullEvenNonempty
        intro q hq
        apply le_of_forall_pos_le_add
        intro epsilon hEpsilon
        obtain ⟨N, qN, hqN, hApprox⟩ :=
          evenApproximation q hq epsilon hEpsilon
        have qNLeSup : qN <= sSup (finiteEvenQuotients N) :=
          le_csSup (finiteEvenBounded N) hqN
        have endpointLe : finiteLower N <= z := hz ⟨N, rfl⟩
        dsimp only [finiteLower] at endpointLe
        linarith
      dsimp only [fullLower]
      linarith
  have upperIsGLB : IsGLB (range finiteUpper) fullUpper := by
    constructor
    · rintro _ ⟨N, rfl⟩
      dsimp only [finiteUpper, fullUpper]
      simpa only [add_comm] using add_le_add_left
        (csInf_le_csInf fullOddBounded (finiteOddNonempty N) (oddIncluded N))
        referenceBudget
    · intro z hz
      have infGe : z - referenceBudget <= sInf fullOddQuotients := by
        apply le_csInf fullOddNonempty
        intro q hq
        apply le_of_forall_pos_le_add
        intro epsilon hEpsilon
        obtain ⟨N, qN, hqN, hApprox⟩ :=
          oddApproximation q hq epsilon hEpsilon
        have infLeQN : sInf (finiteOddQuotients N) <= qN :=
          csInf_le (finiteOddBounded N) hqN
        have lowerLeEndpoint : z <= finiteUpper N := hz ⟨N, rfl⟩
        dsimp only [finiteUpper] at lowerLeEndpoint
        linarith
      dsimp only [fullUpper]
      linarith

  have lowerTendsto : Tendsto finiteLower atTop (nhds fullLower) :=
    tendsto_atTop_isLUB lowerMonotone lowerIsLUB
  have upperTendsto : Tendsto finiteUpper atTop (nhds fullUpper) :=
    tendsto_atTop_isGLB upperAntitone upperIsGLB
  have intervalCharacterization (N : Nat) (R : Real) :
      feasible N R <-> R ∈ Icc (finiteLower N) (finiteUpper N) := by
    dsimp only [feasible]
    rw [evenPencilIff, oddPencilIff]
    rfl
  have finiteCertificate (N : Nat) (hCross : finiteLower N > finiteUpper N) :
      (forall R, (evenPencil N R).PosSemidef -> finiteLower N <= R) /\
      (forall R, (oddPencil N R).PosSemidef -> R <= finiteUpper N) /\
      ¬ exists R, feasible N R := by
    refine ⟨fun R h => (evenPencilIff N R).mp h,
      fun R h => (oddPencilIff N R).mp h, ?_⟩
    rintro ⟨R, hR⟩
    have hInterval := (intervalCharacterization N R).mp hR
    exact (not_le_of_gt hCross) (hInterval.1.trans hInterval.2)

  exact ⟨fun N R => ⟨evenPencilHermitian N R, oddPencilHermitian N R⟩,
    evenPencilIff, oddPencilIff, lowerMonotone, upperAntitone,
    lowerTendsto, upperTendsto, intervalCharacterization, finiteCertificate⟩

#print axioms finite_weyl_budget_bounds

end D5.S3.Weil.Budget.FiniteWeylBudgetBounds
