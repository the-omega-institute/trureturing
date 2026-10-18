/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/LiteralFourByNExactCheck
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/LiteralFourByNExactCheck
   mirror-E: none(waiver:transient-exact-application)
   anchors: []
   utility: none
   digest: Transient exact physical four-by-n purity, coordinate attainment, and least eventual threshold application. -/

/-
Transient exact physical application, retained as verification evidence outside
canonical source. Every private helper is consumed by the final application.
No declaration in this file is proposed for canonical retention or first freeze.

UNCOMPILED: the unchanged original all-N>=56 scalar theorem
QuadbitUniformSpectralBound.actual_k1_l4_purity_bound is applied here.
The supplied scalar0 receipt records selected 4.35 kernel exit zero for source
b48fb2becc344f55b58a6192e61986d7a45d8b176a3ccb1dba361560ec40ed0c.
Its complete axiom/Reg audit is pending. The diagonal APIs and actual rank-four
product-corner proof content reuse the archived suppliers. Their installation
and this physical application have no current kernel acceptance.
Historical n>=17 verification is source-bound evidence only. This n>=14
candidate and the anonymous n=13 application below have not been compiled.

The upper bound uses one spectrum returned from the actual density matrix.
Attainment uses the canonical ContractionBlocks theorem, positive normalization
and existing partial-transpose closure, with public Euclidean norm preservation.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformRankFourNecessary
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ContinuousSpectrumAssembly
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.AbsolutePPT
open QutritPerturbationAttainment QutritSpectralReduction

namespace LiteralFourByNTransient
noncomputable section

private def t (n : ℕ) : ℕ := (3 * (4 * n) + 4) / 8
private def d (n : ℕ) : ℝ := 12 * (n : ℝ) + 2 * (t n : ℝ)
private def F (n : ℕ) : ℝ :=
  (36 * (n : ℝ) + 16 * (t n : ℝ)) / (d n)^2

-- The actual row-major equivalence: e(i,j).val = j.val + n*i.val.
private def e (n : ℕ) : (Fin 4 × Fin n) ≃ Fin (4 * n) := finProdFinEquiv
private def P (n : ℕ) : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ :=
  diagonal (fun p => if (e n p).val < t n then 1 else 0)
private def rhoStar (n : ℕ) : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ :=
  ((1 / d n : ℝ) : ℂ) • ((3 : ℂ) • 1 + (2 : ℂ) • P n)

private theorem dimension (n : ℕ) (hn : 14 ≤ n) : 56 ≤ 4 * n := by omega

private theorem denominator_pos (n : ℕ) (hn : 14 ≤ n) : 0 < d n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp [d]
  positivity

/- Use one actual physical diagonal for literal K1 and rank-four L4.
No K2, L3, C3, strict-positivity or additional shape hypothesis is supplied
to the unchanged all-N>=56 scalar theorem. -/
private theorem upper (n : ℕ) (hn : 14 ≤ n)
    (rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)
    (hpos : rho.PosSemidef) (htr : rho.trace = 1) (ha : APPT rho) :
    (rho * rho).trace.re ≤ F n := by
  classical
  have hN := dimension n hn
  obtain ⟨l, ho, hnonneg, hmass, hdiag, hpur⟩ :=
    QuadbitQuintitMaximumPurity.diagonal_spectral_reduction (e n) rho hpos htr ha
  have h1 := (QuadbitQuintitMaximumPurity.diagonal_necessary_both
    (by omega : 3 ≤ 4) (by omega : 3 ≤ n) (e n) l hdiag).1
  let b : Fin 9 → ℝ :=
    QuadbitQuintitMaximumPurity.cornerBoundaryValues (4*n) (by omega) l
  change (K1 b).PosSemidef at h1
  have hb0 : b 0 = l ⟨0, by omega⟩ := by simp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
  have hb1 : b 1 = l ⟨1, by omega⟩ := by simp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
  have hb2 : b 2 = l ⟨2, by omega⟩ := by simp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
  have hb3 : b 3 = l ⟨4*n-6, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hb4 : b 4 = l ⟨4*n-5, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hb5 : b 5 = l ⟨4*n-4, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hb6 : b 6 = l ⟨4*n-3, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hb7 : b 7 = l ⟨4*n-2, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hb8 : b 8 = l ⟨4*n-1, by omega⟩ := by
    dsimp [b, QuadbitQuintitMaximumPurity.cornerBoundaryValues]
    congr 1 <;> apply Fin.ext <;> simp <;> omega
  have hK : (!![
      2*l ⟨4*n-1, by omega⟩, l ⟨4*n-2, by omega⟩-l ⟨0, by omega⟩,
        l ⟨4*n-4, by omega⟩-l ⟨1, by omega⟩;
      l ⟨4*n-2, by omega⟩-l ⟨0, by omega⟩, 2*l ⟨4*n-3, by omega⟩,
        l ⟨4*n-5, by omega⟩-l ⟨2, by omega⟩;
      l ⟨4*n-4, by omega⟩-l ⟨1, by omega⟩,
        l ⟨4*n-5, by omega⟩-l ⟨2, by omega⟩,
        2*l ⟨4*n-6, by omega⟩] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
    simpa only [K1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8] using h1
  have hL4 := UniformRankFourNecessary.uniform_rank_four_necessary
    (by omega : 4 ≤ 4) (by omega : 4 ≤ n) (e n) l hdiag
  have hf : UniformRankFourNecessary.sumFirst 6 l =
      ∑ i : Fin 6, l ⟨i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumFirst
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (show i.val < 4*n by omega)]
  have hl : UniformRankFourNecessary.sumLast 10 l =
      ∑ i : Fin 10, l ⟨4*n-10+i.val, by omega⟩ := by
    unfold UniformRankFourNecessary.sumLast
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos (show 4*n-10+i.val < 4*n by omega)]
  rw [hf, hl] at hL4
  have hs := QuadbitUniformSpectralBound.actual_k1_l4_purity_bound
    (4*n) hN l ho hnonneg hmass hL4 hK
  dsimp only [QuadbitUniformSpectralBound.target] at hs
  change (∑ i, (l i)^2) ≤
    (9*((4*n : ℕ) : ℝ)+16*(t n : ℝ))/(3*((4*n : ℕ) : ℝ)+2*(t n : ℝ))^2 at hs
  have hnum : 9*((4*n : ℕ) : ℝ)+16*(t n : ℝ) =
      36*(n : ℝ)+16*(t n : ℝ) := by push_cast; ring
  have hden : 3*((4*n : ℕ) : ℝ)+2*(t n : ℝ) =
      12*(n : ℝ)+2*(t n : ℝ) := by push_cast; ring
  rw [hnum, hden] at hs
  rw [hpur]
  exact hs

private theorem projector_data (n : ℕ) :
    (P n).PosSemidef ∧ P n * P n = P n ∧
    (P n).rank = t n ∧ (P n).trace = (t n : ℂ) ∧
    Fintype.card {p : Fin 4 × Fin n // (e n p).val < t n} = t n ∧
    Fintype.card {p : Fin 4 × Fin n // ¬ (e n p).val < t n} = 4*n-t n := by
  classical
  have htN : t n ≤ 4*n := by dsimp [t]; omega
  let cutEquiv : {p : Fin 4 × Fin n // (e n p).val < t n} ≃ Fin (t n) :=
    { toFun := fun p => ⟨(e n p.val).val, p.property⟩
      invFun := fun i => ⟨(e n).symm ⟨i.val, lt_of_lt_of_le i.isLt htN⟩, by simp⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro i; apply Fin.ext; simp }
  have hc : Fintype.card {p : Fin 4 × Fin n // (e n p).val < t n} = t n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr cutEquiv
  have hp : (P n).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro p
    split_ifs <;> norm_num
  have hpp : P n * P n = P n := by
    dsimp [P]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    split_ifs <;> norm_num
  refine ⟨hp, hpp, ?_, ?_, hc, ?_⟩
  · dsimp [P]
    rw [Matrix.rank_diagonal]
    calc
      _ = Fintype.card {p : Fin 4 × Fin n // (e n p).val < t n} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by
          by_cases h : (e n p).val < t n <;> simp [h]))
      _ = t n := hc
  · rw [Fintype.card_subtype] at hc
    simpa only [P, Matrix.trace_diagonal, Finset.sum_boole, hc] using
      (rfl : (t n : ℂ) = (t n : ℂ))
  · rw [Fintype.card_subtype_compl, hc]
    simp [Fintype.card_prod]

set_option maxHeartbeats 2000000 in
private theorem attainer_data (n : ℕ) (hn : 14 ≤ n) :
    rhoStar n = diagonal (fun p =>
      if (e n p).val < t n then (5 : ℂ) / (d n : ℂ) else (3 : ℂ) / (d n : ℂ)) ∧
    (rhoStar n).PosSemidef ∧ (rhoStar n).trace = 1 ∧ APPT (rhoStar n) ∧
    (rhoStar n * rhoStar n).trace.re = F n := by
  classical
  obtain ⟨hP, hPP, _hrank, hPtr, _hhigh, _hlow⟩ := projector_data n
  have hd : 0 < d n := denominator_pos n hn
  have hs : 0 ≤ (1 / d n : ℝ) := le_of_lt (one_div_pos.mpr hd)
  have hdc : (d n : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hi : (1 : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ).trace =
      (4 : ℂ) * n := by simp [Matrix.trace_one, Fintype.card_prod]
  have hden : (d n : ℂ) = 12 * (n : ℂ) + 2 * (t n : ℂ) := by
    simp only [d, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast]
  have hdiag : rhoStar n = diagonal (fun p =>
      if (e n p).val < t n then (5 : ℂ) / (d n : ℂ) else (3 : ℂ) / (d n : ℂ)) := by
    ext p q
    by_cases hpq : p = q
    · subst q
      by_cases h : (e n p).val < t n <;>
        simp [rhoStar, P, Matrix.diagonal_apply, Matrix.one_apply,
          Matrix.smul_apply, h, div_eq_mul_inv] <;> ring
    · simp [rhoStar, P, Matrix.diagonal_apply, Matrix.one_apply,
        Matrix.smul_apply, hpq]
  refine ⟨hdiag, ?_, ?_, ?_, ?_⟩
  · exact ((Matrix.PosSemidef.one.smul (by norm_num : (0 : ℂ) ≤ 3)).add
      (hP.smul (by norm_num : (0 : ℂ) ≤ 2))).smul
        (Complex.zero_le_real.mpr hs)
  · simp only [rhoStar, Matrix.trace_smul, Matrix.trace_add, hi, hPtr, smul_eq_mul]
    rw [show ((1 / d n : ℝ) : ℂ) = 1 / (d n : ℂ) by push_cast; rfl]
    rw [hden] at hdc ⊢
    field_simp [hdc]
    <;> ring
  · intro U
    let Q : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ :=
      (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) * P n * (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ
    have hQ : Q.IsHermitian := by
      exact Matrix.isHermitian_mul_mul_conjTranspose
        (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) hP.isHermitian
    have hu : (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ *
        (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    have hu' : (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) *
        (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    have hQQ : Q * Q = Q := by
      dsimp [Q]
      calc
        _ = (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) *
            (P n * ((U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ * (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)) * P n) *
              (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ := by simp only [Matrix.mul_assoc]
        _ = (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) * (P n * P n) * (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ := by
          rw [hu, Matrix.mul_one]
        _ = _ := by rw [hPP]
    let H : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ := (2 : ℂ) • Q - 1
    have hH : H.IsHermitian := by
      change Hᴴ = H
      simp [H, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hQ.eq]
    have hHH : Hᴴ * H = 1 := by
      rw [hH.eq]
      dsimp [H]
      noncomm_ring [hQQ]
      module
    have hunit : H ∈ unitary (Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) := by
      constructor <;> simpa only [Matrix.star_eq_conjTranspose, hH.eq] using hHH
    have hbound (x : Fin 4 × Fin n → ℂ) :
        ‖WithLp.toLp 2 (H *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
      have hnorm := ContinuousLinearMap.norm_map_of_mem_unitary
        (Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ)) hunit) (WithLp.toLp 2 x)
      have heq : ‖WithLp.toLp 2 (H *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
        simpa only [Matrix.toEuclideanCLM_toLp] using hnorm
      exact heq.le
    have hsep := D5.S3.Quantum.Entanglement.AbsoluteSeparability.ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one
      H hH hbound
    have hsep' : separableCone ((3 : ℂ) • 1 + (2 : ℂ) • Q) := by
      convert hsep using 1
      dsimp [H]
      module
    have hconj : (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) * rhoStar n *
        (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ =
        ((1 / d n : ℝ) : ℂ) • ((3 : ℂ) • 1 + (2 : ℂ) • Q) := by
      simp only [rhoStar, Q, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_one, hu']
    change (partialTranspose ((U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ) *
      rhoStar n * (U : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ)ᴴ)).PosSemidef
    rw [hconj]
    exact QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef
      (separableCone_smul (c := (1 / d n : ℝ)) hs hsep')
  · have hsq : ((3 : ℂ) • 1 + (2 : ℂ) • P n) *
        ((3 : ℂ) • 1 + (2 : ℂ) • P n) =
        (9 : ℂ) • 1 + (16 : ℂ) • P n := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, Matrix.one_mul, Matrix.mul_one, hPP]
      module
    have htrsq : (rhoStar n * rhoStar n).trace = (F n : ℂ) := by
      simp only [rhoStar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq,
        Matrix.trace_smul, Matrix.trace_add, hi, hPtr, smul_eq_mul]
      dsimp [F]
      push_cast
      field_simp [hdc]
      <;> ring
    rw [htrsq, Complex.ofReal_re]

private theorem ceiling (n : ℕ) (hn : 14 ≤ n) :
    t n = ⌈3 * (n : ℝ) / 2⌉₊ := by
  have ht : t n ≠ 0 := by dsimp [t]; omega
  have hlow : 2 * (t n - 1) < 3*n := by dsimp [t]; omega
  have hupp : 3*n ≤ 2 * t n := by dsimp [t]; omega
  symm
  apply (Nat.ceil_eq_iff ht).mpr
  constructor
  · have h : (2 : ℝ) * ((t n - 1 : ℕ) : ℝ) < 3 * (n : ℝ) := by exact_mod_cast hlow
    linarith
  · have h : 3 * (n : ℝ) ≤ 2 * (t n : ℝ) := by exact_mod_cast hupp
    linarith

private theorem parity (n : ℕ) (hn : 14 ≤ n) :
    (n % 2 = 0 → F n = 4 / (15 * (n : ℝ))) ∧
    (n % 2 = 1 → F n = (60 * (n : ℝ) + 8) / (15 * (n : ℝ) + 1)^2) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  constructor
  · intro heven
    have ht : 2 * t n = 3*n := by dsimp [t]; omega
    have ht' : (2 : ℝ) * (t n : ℝ) = 3 * (n : ℝ) := by exact_mod_cast ht
    have hD : d n = 15 * (n : ℝ) := by dsimp [d]; linarith
    have hnum : 36 * (n : ℝ) + 16 * (t n : ℝ) = 60 * (n : ℝ) := by linarith
    rw [F, hD, hnum]
    field_simp [hnr.ne']
    <;> ring
  · intro hodd
    have ht : 2 * t n = 3*n+1 := by dsimp [t]; omega
    have ht' : (2 : ℝ) * (t n : ℝ) = 3 * (n : ℝ) + 1 := by exact_mod_cast ht
    have hD : d n = 15 * (n : ℝ) + 1 := by dsimp [d]; linarith
    have hnum : 36 * (n : ℝ) + 16 * (t n : ℝ) = 60 * (n : ℝ) + 8 := by linarith
    rw [F, hD, hnum]

/- Clause-complete physical application. The existential matrices below really
live on Fin 4 × Fin n. Orthogonal projector means Hermitian and idempotent;
its complex matrix rank, complex trace, actual diagonal and normalization are
all asserted. The real sSup is over actual PSD trace-one APPT densities. -/
private theorem exact_physical_application (n : ℕ) (hn : 14 ≤ n) :
    let N : ℕ := 4*n
    let t : ℕ := (3*N+4)/8
    let D : ℝ := 12*(n : ℝ)+2*(t : ℝ)
    let F : ℝ := (36*(n : ℝ)+16*(t : ℝ))/D^2
    let e : (Fin 4 × Fin n) ≃ Fin (4*n) := finProdFinEquiv
    0 < D ∧ t = ⌈3*(n : ℝ)/2⌉₊ ∧
    (∀ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      rho.PosSemidef → rho.trace = 1 → APPT rho → (rho*rho).trace.re ≤ F) ∧
    sSup {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p} = F ∧
    (∃ P rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      P = diagonal (fun p => if (e p).val < t then (1 : ℂ) else 0) ∧
      P.IsHermitian ∧ P*P = P ∧ P.rank = t ∧ P.trace = (t : ℂ) ∧
      Fintype.card {p : Fin 4 × Fin n // (e p).val < t} = t ∧
      Fintype.card {p : Fin 4 × Fin n // ¬ (e p).val < t} = 4*n-t ∧
      rho = ((1/D : ℝ) : ℂ) • ((3 : ℂ) • 1 + (2 : ℂ) • P) ∧
      rho = diagonal (fun p => if (e p).val < t then (5 : ℂ)/(D : ℂ) else (3 : ℂ)/(D : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = F) ∧
    (n % 2 = 0 → F = 4/(15*(n : ℝ))) ∧
    (n % 2 = 1 → F = (60*(n : ℝ)+8)/(15*(n : ℝ)+1)^2) := by
  classical
  change 0 < d n ∧ t n = ⌈3*(n : ℝ)/2⌉₊ ∧ _
  obtain ⟨hdiag, hpos, htrace, happt, hpur⟩ := attainer_data n hn
  obtain ⟨hP, hPP, hrank, hPtr, hhigh, hlow⟩ := projector_data n
  have hattain : ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = F n :=
    ⟨rhoStar n, ⟨hpos, htrace⟩, happt, hpur⟩
  refine ⟨denominator_pos n hn, ceiling n hn, upper n hn, ?_, ?_, (parity n hn).1, (parity n hn).2⟩
  · refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
    · exact ⟨_, hattain⟩
    · rintro p ⟨rho, hdensity, ha, hp⟩
      rw [← hp]
      exact upper n hn rho hdensity.1 hdensity.2 ha
    · intro w hw
      exact ⟨_, hattain, hw⟩
  · exact ⟨P n, rhoStar n, rfl, hP.isHermitian, hPP, hrank, hPtr, hhigh, hlow,
      rfl, hdiag, ⟨hpos, htrace⟩, happt, hpur⟩

#print axioms exact_physical_application

/- Anonymous exact applications only: no canonical theorem, Describe or Reg
entry is proposed. At n=13, N=52, the all-N>=56 upper is never invoked. -/
private theorem exact_onset_application :
    (∃ rho : Matrix (Fin 4 × Fin 13) (Fin 4 × Fin 13) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 13 =>
        if ij = (0, 0) then (1 / 18 : ℂ) else (1 / 54 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
      (rho*rho).trace.re = (5 / 243 : ℝ) ∧
      F 13 = (197 / 9604 : ℝ) ∧
      (rho*rho).trace.re - F 13 = (149 / 2333772 : ℝ) ∧
      F 13 < (rho*rho).trace.re) ∧
    IsLeast {k : ℕ | ∀ n : ℕ, k ≤ n →
      IsGreatest {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
        (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p}
        (F n)} 14 := by
  classical
  have hmax (n : ℕ) (hn : 14 ≤ n) :
      IsGreatest {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
        (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p}
        (F n) := by
    obtain ⟨_hdiag, hpos, htrace, happt, hpur⟩ := attainer_data n hn
    refine ⟨⟨rhoStar n, ⟨hpos, htrace⟩, happt, hpur⟩, ?_⟩
    rintro p ⟨rho, hdensity, ha, hp⟩
    rw [← hp]
    exact upper n hn rho hdensity.1 hdensity.2 ha
  let v : Fin 4 × Fin 13 → ℂ := Pi.single (0, 0) 1
  have hv : star v ⬝ᵥ v = (1 : ℂ) := by
    simp [v, dotProduct, Pi.single_apply]
  obtain ⟨hd, ht, ha, hp⟩ := QuadbitQuintitMaximumPurity.normalized_ray v hv
  norm_num at hp
  have heq : QuadbitQuintitMaximumPurity.normalizedRay v =
      diagonal (fun ij : Fin 4 × Fin 13 =>
        if ij = (0, 0) then (1 / 18 : ℂ) else (1 / 54 : ℂ)) := by
    convert QuadbitQuintitMaximumPurity.normalized_basis_diagonal
      ((0, 0) : Fin 4 × Fin 13) using 1 <;> norm_num [v]
  have hF13 : F 13 = (197 / 9604 : ℝ) := by norm_num [F, d, t]
  have hgap : (5 / 243 : ℝ) - F 13 = (149 / 2333772 : ℝ) := by
    rw [hF13]
    norm_num
  have hstrict : F 13 < (5 / 243 : ℝ) := by rw [hF13]; norm_num
  have hmember : (5 / 243 : ℝ) ∈
      {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin 13) (Fin 4 × Fin 13) ℂ,
        (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p} :=
    ⟨QuadbitQuintitMaximumPurity.normalizedRay v, ⟨hd, ht⟩, ha, hp⟩
  refine ⟨?_, hmax, ?_⟩
  · refine ⟨QuadbitQuintitMaximumPurity.normalizedRay v, heq, ⟨hd, ht⟩, ha,
      hp, hF13, ?_, ?_⟩
    · rw [hp]
      exact hgap
    · rw [hp]
      exact hstrict
  · intro k hk
    by_contra h
    have hk13 : k ≤ 13 := by omega
    have hu : (5 / 243 : ℝ) ≤ F 13 := (hk 13 hk13).2 hmember
    linarith


/- The final anonymous application consumes the complete n=13 and onset proof. -/
example :
    (∃ rho : Matrix (Fin 4 × Fin 13) (Fin 4 × Fin 13) ℂ,
      rho = diagonal (fun ij : Fin 4 × Fin 13 =>
        if ij = (0, 0) then (1 / 18 : ℂ) else (1 / 54 : ℂ)) ∧
      (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧
      (rho*rho).trace.re = (5 / 243 : ℝ) ∧
      F 13 = (197 / 9604 : ℝ) ∧
      (rho*rho).trace.re - F 13 = (149 / 2333772 : ℝ) ∧
      F 13 < (rho*rho).trace.re) ∧
    IsLeast {k : ℕ | ∀ n : ℕ, k ≤ n →
      IsGreatest {p : ℝ | ∃ rho : Matrix (Fin 4 × Fin n) (Fin 4 × Fin n) ℂ,
        (rho.PosSemidef ∧ rho.trace = 1) ∧ APPT rho ∧ (rho*rho).trace.re = p}
        (F n)} 14 := exact_onset_application

/- Axiom coverage plan, after the final anonymous example:
The example is exactly `exact_onset_application`; inspect that complete proof's
transitive axiom closure, including its local hmax and n=13 normalized-ray
specialization. Also inspect `exact_physical_application`, which covers the
coordinate projector, trace normalization, all-unitary APPT, real sSup, ceiling
and parity clauses. Root must obtain current source-bound 4.35 kernel zero and
accepted axiom closure for both complete proofs and their imports. The prints
below request that evidence; this source-only installation provides none.
The original literal scalar telescope retains zeros, repetitions and singular
PSD. No scalar upper is applied at N=52. This threshold concerns only F; no
maximum classification for 7..13, general-m theorem or APPT=AS claim follows.
No literature priority or official/unique acceptance follows from these checks.
-/
#print axioms exact_onset_application
#print axioms exact_physical_application
#print axioms dimension
#print axioms denominator_pos
#print axioms upper
#print axioms projector_data
#print axioms attainer_data
#print axioms ceiling
#print axioms parity
#print axioms QuadbitUniformSpectralBound.actual_k1_l4_purity_bound
#print axioms QuadbitQuintitMaximumPurity.diagonal_spectral_reduction
#print axioms QuadbitQuintitMaximumPurity.diagonal_necessary_both
#print axioms UniformRankFourNecessary.uniform_rank_four_necessary
#print axioms D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality
#print axioms QuadbitQuintitMaximumPurity.normalized_ray
#print axioms QuadbitQuintitMaximumPurity.normalized_basis_diagonal

end
end LiteralFourByNTransient
