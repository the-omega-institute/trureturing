/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.claim; result=D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.result; claim=D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation.claim
   digest: An admissible Hildebrand matrix in dimension four violates negative-index one. -/

import D5.S3.Weil.ZetaLinear.FullRankInertiaPullback
import D5.S3.Analytic.ReflectedSpectrum.ConfluentNegativeJetBlock
import D5.S3.Arith.Lattices.Klartag.Walk.Increments
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootKernels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix
open D5.S3.Analytic.ReflectedSpectrum.ConfluentNegativeJetBlock
open D5.S3.Arith.Lattices.Klartag.Walk.Increments (UT)
open NikolovSegal.SLnRootAction (PositiveIndex)
open scoped BigOperators Matrix ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation

/-! ## Source carriers and orderings -/

abbrev PlusOrdering (d : ℕ) :=
  UT d ≃ Fin (Fintype.card (UT d))

abbrev MinusOrdering (d : ℕ) :=
  PositiveIndex d ≃ Fin (Fintype.card (PositiveIndex d))

def minusToPlus {d : ℕ} (p : PositiveIndex d) : UT d :=
  ⟨p.1, p.2.le⟩

/-- Hildebrand compatibility; product ordering is weak. -/
def Compatible {d : ℕ}
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d)
    (x : Fin d → ℝ) : Prop :=
  (∀ p q : UT d,
    sigmaP p < sigmaP q →
      x q.1.1 * x q.1.2 ≤ x p.1.1 * x p.1.2) ∧
  (∀ p q : PositiveIndex d,
    sigmaP (minusToPlus p) < sigmaP (minusToPlus q) →
      sigmaM p < sigmaM q)

/-- Membership in Hildebrand's Σ±. -/
def Admissible {d : ℕ}
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d) : Prop :=
  ∃ x : Fin d → ℝ,
    StrictAnti x ∧
    (∀ i, 0 < x i) ∧
    Compatible sigmaP sigmaM x

/-! ## Spectrum indexing and the source matrix -/

/-- Embed a plus rank into the full spectrum, then reverse it. -/
def plusIndex {d : ℕ}
    (r : Fin (Fintype.card (UT d))) : Fin (d * d) :=
  (Fin.castLE
    (by
      simpa only [UT, Fintype.card_prod, Fintype.card_fin] using
        (Fintype.card_subtype_le
          (fun p : Fin d × Fin d => p.1 ≤ p.2)))
    r).rev

/-- A zero-based minus rank is already the desired spectrum index. -/
def minusIndex {d : ℕ}
    (r : Fin (Fintype.card (PositiveIndex d))) : Fin (d * d) :=
  Fin.castLE
    (by
      simpa only [PositiveIndex, Fintype.card_prod, Fintype.card_fin] using
        (Fintype.card_subtype_le
          (fun p : Fin d × Fin d => p.1 < p.2)))
    r

/-- Hildebrand's Λ, with its real entries viewed in ℂ. -/
def hildebrandArray (d : ℕ)
    (lam : Fin (d * d) → ℝ)
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    if hij : i ≤ j then
      (lam (plusIndex (sigmaP ⟨(i, j), hij⟩)) : ℂ)
    else
      -(lam (minusIndex
        (sigmaM ⟨(j, i), lt_of_not_ge hij⟩)) : ℂ)

/-- The source's Λ + Λᵀ, using the equal adjoint of its real array. -/
def hildebrandMatrix (d : ℕ)
    (lam : Fin (d * d) → ℝ)
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d) :
    Matrix (Fin d) (Fin d) ℂ :=
  let A := hildebrandArray d lam sigmaP sigmaM
  A + Aᴴ

/-- Public Hermitian evidence used by the statement itself. -/
theorem hildebrandMatrix_isHermitian (d : ℕ)
    (lam : Fin (d * d) → ℝ)
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d) :
    (hildebrandMatrix d lam sigmaP sigmaM).IsHermitian :=
  Matrix.isHermitian_add_transpose_self
    (hildebrandArray d lam sigmaP sigmaM)

def OrderedSpectrum (d : ℕ)
    (lam : Fin (d * d) → ℝ) : Prop :=
  Antitone lam ∧
  (∀ i, 0 ≤ lam i) ∧
  (∑ i, lam i) = 1

/-- The universal persistence assertion recorded in issue #17687. -/
def claim : Prop :=
  ∀ d : ℕ, 3 < d →
    ∀ lam : Fin (d * d) → ℝ,
      OrderedSpectrum d lam →
      ∀ (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d),
        Admissible sigmaP sigmaM →
        RHLinalg.negIndex
          (hildebrandMatrix_isHermitian d lam sigmaP sigmaM) ≤ 1

/-! ## Explicit orderings at d = 4 -/

/-- Only the upper triangle is queried by this function. -/
private def plusRank (p : UT 4) : Fin 10 :=
  (!![0, 1, 3, 6;
      0, 2, 4, 7;
      0, 0, 5, 8;
      0, 0, 0, 9] :
    Matrix (Fin 4) (Fin 4) (Fin 10)) p.1.1 p.1.2

/-- Only the strict upper triangle is queried by this function. -/
private def minusRank (p : PositiveIndex 4) : Fin 6 :=
  (!![0, 0, 1, 3;
      0, 0, 2, 4;
      0, 0, 0, 5;
      0, 0, 0, 0] :
    Matrix (Fin 4) (Fin 4) (Fin 6)) p.1.1 p.1.2

private def sigmaPlus : PlusOrdering 4 :=
  Equiv.ofBijective
    (fun p : UT 4 =>
      Fin.cast
        (by decide : 10 = Fintype.card (UT 4))
        (plusRank p))
    (by decide)

private def sigmaMinus : MinusOrdering 4 :=
  Equiv.ofBijective
    (fun p : PositiveIndex 4 =>
      Fin.cast
        (by decide : 6 = Fintype.card (PositiveIndex 4))
        (minusRank p))
    (by decide)

private def witnessXNat : Fin 4 → ℕ :=
  ![8, 5, 3, 1]

private theorem witnessAdmissible :
    Admissible sigmaPlus sigmaMinus := by
  refine ⟨fun i => (witnessXNat i : ℝ), ?_, ?_, ?_⟩
  · have hx : StrictAnti witnessXNat := by decide
    intro i j hij
    dsimp only
    exact_mod_cast hx hij
  · have hx : ∀ i : Fin 4, 0 < witnessXNat i := by decide
    intro i
    dsimp only
    exact_mod_cast hx i
  · constructor
    · have hprod :
          ∀ p q : UT 4,
            sigmaPlus p < sigmaPlus q →
              witnessXNat q.1.1 * witnessXNat q.1.2 ≤
                witnessXNat p.1.1 * witnessXNat p.1.2 := by
        decide
      intro p q hpq
      dsimp only
      exact_mod_cast hprod p q hpq
    · decide

/-! ## Spectrum and matrix certificates -/

private def witnessSpectrum (i : Fin 16) : ℝ :=
  if i.val < 4 then 13 / 64 else 1 / 64

private theorem witnessSpectrum_ordered :
    OrderedSpectrum 4 witnessSpectrum := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val ≤ j.val := hij
    rw [witnessSpectrum.eq_1, witnessSpectrum.eq_1]
    split_ifs <;> norm_num
    omega
  · intro i
    dsimp only [witnessSpectrum]
    split_ifs <;> norm_num
  · norm_num [witnessSpectrum.eq_1, Fin.sum_univ_succ]

private def witnessM : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 1, -6, -6, -6;
     -6,  1, -6,  0;
     -6, -6,  1,  0;
     -6,  0,  0,  1]

private def witnessB : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1,  0;
     0,  1;
     0,  1;
     1, -2]

private def positiveBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 16 : ℂ) • !![5, 1; 1, 3]

private theorem witnessMatrix_eq :
    hildebrandMatrix 4 witnessSpectrum sigmaPlus sigmaMinus =
      (1 / 32 : ℂ) • witnessM := by
  rw [hildebrandMatrix.eq_1, witnessM.eq_1]
  ext i j
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    dsimp only [hildebrandArray, plusIndex, minusIndex, sigmaPlus, sigmaMinus,
      plusRank, minusRank, witnessSpectrum, Equiv.ofBijective, Fin.cast, Fin.castLE] <;>
    norm_num [Fin.rev, Fin.le_def, Matrix.conjTranspose_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]

private theorem witnessBlock_eq :
    witnessBᴴ *
        hildebrandMatrix 4 witnessSpectrum sigmaPlus sigmaMinus *
        witnessB =
      -positiveBlock := by
  rw [witnessMatrix_eq, witnessB.eq_1, positiveBlock.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [witnessM] <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, map_ofNat]

private theorem positiveBlock_posDef :
    positiveBlock.PosDef := by
  let D : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.diagonal
      ![((1 / 4 : ℝ) : ℂ), ((1 / 8 : ℝ) : ℂ)]
  let V : Matrix (Fin 1) (Fin 2) ℂ :=
    !![1 / 4, 1 / 4]
  have hD : D.PosDef := by
    dsimp only [D]
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> apply Complex.zero_lt_real.mpr <;> norm_num
  have hDecomp : positiveBlock = D + Vᴴ * V := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      dsimp only [positiveBlock, D, V] <;>
      norm_num [Matrix.diagonal_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, map_ofNat]
  rw [hDecomp]
  exact hD.add_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self V)

/-! ## Refutation -/

theorem result : ¬ claim := by
  intro hc
  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    hildebrandMatrix 4 witnessSpectrum sigmaPlus sigmaMinus
  have hA : A.IsHermitian :=
    hildebrandMatrix_isHermitian
      4 witnessSpectrum sigmaPlus sigmaMinus
  have hAtMostOne : RHLinalg.negIndex hA ≤ 1 :=
    hc 4 (by decide) witnessSpectrum witnessSpectrum_ordered
      sigmaPlus sigmaMinus witnessAdmissible
  let G : Matrix (Fin 2) (Fin 2) ℂ :=
    witnessBᴴ * A * witnessB
  have hG : G.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul witnessB hA
  have hFactor :
      G =
        -((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
          positiveBlock * 1) := by
    simpa [G, A] using witnessBlock_eq
  have hTwo : RHLinalg.negIndex hG = 2 :=
    (confluent_negative_jet_block
        2 positiveBlock 1 G
        positiveBlock_posDef isUnit_one hG hFactor).2
  have hImpossible : (2 : ℕ) ≤ 1 := by
    calc
      2 = RHLinalg.negIndex hG := hTwo.symm
      _ ≤ RHLinalg.negIndex hA :=
        RHLinalg.negIndex_conj_le hA witnessB
      _ ≤ 1 := hAtMostOne
  exact (by decide : ¬ ((2 : ℕ) ≤ 1)) hImpossible
end D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
end
