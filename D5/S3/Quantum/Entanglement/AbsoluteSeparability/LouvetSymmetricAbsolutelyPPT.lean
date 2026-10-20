/- GID: D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The symmetric qudit p-spectrum is absolutely PPT above the conjectured threshold. -/

/-
admission_basis: open-problem-resolution (#19125; Proved)
escape_witness: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19210
Direct frozen dependencies (declaration statement_id):
F1: D5/S3/Quantum/Entanglement/OccupancyWordSectors.Word; statement_id=sha256:ca13ed0bb809eb9e0bcec28de917d6e1af84494bf87b4d48233eeb00ad8f61f7
F2: D5/S3/Quantum/Entanglement/OccupancyWordSectors.occupation; statement_id=sha256:7a25f213e509fae5658b7cd5566e2226a6cc4a14df4b9b97298939adea75b3ed
F3: D5/S3/Quantum/Entanglement/OccupancyWordSectors.occupation_card; statement_id=sha256:d4c90ec2b70002060f9fd0af26e6463340c64365b1831fd9cf277de0f7387a4d
F4: D5/S3/Quantum/Entanglement/OccupancyWordSectors.occupation_representative; statement_id=sha256:5ed5d17757681024151f506565b5410b7c65ace94c948b52061ac867105a0da3
F5: D5/S3/Quantum/Entanglement/OccupancyWordSectors.representative; statement_id=sha256:6c957a8f5271a177adae31fde622dfecd975e889b2b29e6620b8caf85f335e30
proof_shape: IsSymmetricOperator: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.claim, LouvetSymmetricAbsolutelyPPT.operator_mulVec_symmetric, LouvetSymmetricAbsolutelyPPT.P_mul_operator, LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank, LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum, LouvetSymmetricAbsolutelyPPT.symmetric_conjugate, LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: IsSymmetricUnitary: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.IsSAPPT, LouvetSymmetricAbsolutelyPPT.symmetric_conjugate, LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: IsFullyPPT: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.IsSAPPT, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: IsSAPPT: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.claim; escape_witness: none; Direct frozen dependencies: none.
proof_shape: D: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.pmin, LouvetSymmetricAbsolutelyPPT.claim, LouvetSymmetricAbsolutelyPPT.P_rank_le, LouvetSymmetricAbsolutelyPPT.D_pos, LouvetSymmetricAbsolutelyPPT.pmin_pos, LouvetSymmetricAbsolutelyPPT.threshold_coefficient, LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum, LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pmin: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.claim, LouvetSymmetricAbsolutelyPPT.pmin_pos, LouvetSymmetricAbsolutelyPPT.threshold_coefficient, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum, LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: claim: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: occupation_fiber_card: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.occupation_same_orbit; escape_witness: none; Direct frozen dependencies: F2.
proof_shape: occupation_same_orbit: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant; escape_witness: none; Direct frozen dependencies: F2.
proof_shape: symmetric_occupation_constant: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.occupationEval_injective; escape_witness: none; Direct frozen dependencies: F2.
proof_shape: occupationEval: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.occupationEval_injective, LouvetSymmetricAbsolutelyPPT.P_rank_le; escape_witness: none; Direct frozen dependencies: F5, F1.
proof_shape: occupationEval_injective: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.P_rank_le; escape_witness: none; Direct frozen dependencies: F5, F1, F4, F2, F3.
proof_shape: P_rank_le: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank; escape_witness: none; Direct frozen dependencies: F5, F1, F4, F2, F3.
proof_shape: Spectral.roots_shape: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.Spectral.rank_shape, LouvetSymmetricAbsolutelyPPT.Spectral.trace_shape, LouvetSymmetricAbsolutelyPPT.Spectral.eigenvalue_choices; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.rank_filter_roots: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.Spectral.rank_shape; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.rank_shape: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.trace_shape: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.eigenvalue_choices: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.hermitian_ker_of_range: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.Spectral.projection_eigenvector; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.projection_trace_rank: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.projection_eigenvector: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.Spectral.spectral_residual_psd; escape_witness: none; Direct frozen dependencies: none.
proof_shape: Spectral.spectral_residual_psd: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: D_pos: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.threshold_coefficient, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: pmin_pos: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.threshold_coefficient, LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: threshold_coefficient: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: operator_mulVec_symmetric: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.range_P_eq_of_rank, LouvetSymmetricAbsolutelyPPT.symmetric_conjugate; escape_witness: none; Direct frozen dependencies: none.
proof_shape: P_mul_operator: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.PiS_operator_sandwich; escape_witness: none; Direct frozen dependencies: none.
proof_shape: range_P_eq_of_rank: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: F5, F1, F4, F2, F3.
proof_shape: PiS_operator_sandwich: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.fullyPPT_of_spectrum; escape_witness: none; Direct frozen dependencies: none.
proof_shape: fullyPPT_of_spectrum: content; consumer: LouvetSymmetricAbsolutelyPPT.result; escape_witness: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; Direct frozen dependencies: F5, F1, F4, F2, F3.
proof_shape: symmetric_conjugate: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: unitary_conjugate_charpoly: bind-only; consumer: LouvetSymmetricAbsolutelyPPT.result; escape_witness: none; Direct frozen dependencies: none.
proof_shape: result: content; consumer: none (settling result); escape_witness: SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor; Direct frozen dependencies: F5, F1, F4, F2, F3.
-/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
import D5.S3.Quantum.Entanglement.OccupancyWordSectors

open scoped BigOperators Matrix ComplexOrder
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
/-- A symmetric `N`-qudit operator: every column lies in the symmetric subspace. -/
def IsSymmetricOperator {N d : ℕ} (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop :=
  ∀ y, IsSymmetricVector (fun x => ρ x y)

/-- A symmetric unitary `U_S`: a unitary that maps the symmetric subspace into itself. -/
def IsSymmetricUnitary {N d : ℕ} (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ ∧
    ∀ v, IsSymmetricVector v → IsSymmetricVector (U *ᵥ v)

/-- Positive partial transpose with respect to every bipartition of the `N` sites. -/
def IsFullyPPT {N d : ℕ} (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop :=
  ∀ S : Finset (Fin N), (partialTransposeOn S ρ).PosSemidef

/-- Symmetric absolutely PPT: `U_S ρ U_S†` is fully PPT for every symmetric unitary `U_S`. -/
def IsSAPPT {N d : ℕ} (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop :=
  ∀ U, IsSymmetricUnitary U → IsFullyPPT (U * ρ * Uᴴ)

/-- `D = binom(N + d - 1, d - 1)`, the dimension of `Sym^N(ℂ^d)`. -/
def D (N d : ℕ) : ℕ := (N + d - 1).choose (d - 1)

/-- `p_min = 1 / (1 + 2 [D binom(N, ⌊N/2⌋)]^{-1})`. -/
noncomputable def pmin (N d : ℕ) : ℝ :=
  1 / (1 + 2 * ((D N d : ℝ) * (N.choose (N / 2) : ℝ))⁻¹)

/-- Conjecture 1 of arXiv:2411.16461v2: every symmetric `N`-qudit state whose spectrum consists of
the `D` nonzero eigenvalues `(1 - (D - 1) p / D, p / D, …, p / D)` (and `d^N - D` zeros on the full
space) with `p ∈ [p_min, 1]` is SAPPT. -/
def claim : Prop :=
  ∀ N d : ℕ, 2 ≤ N → 2 ≤ d → ∀ p : ℝ, pmin N d ≤ p → p ≤ 1 →
    ∀ ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ,
      ρ.PosSemidef → IsSymmetricOperator ρ →
      ρ.charpoly =
        (Polynomial.X - Polynomial.C (((1 - ((D N d : ℝ) - 1) * p / D N d) : ℝ) : ℂ)) *
          (Polynomial.X - Polynomial.C (((p / D N d) : ℝ) : ℂ)) ^ (D N d - 1) *
          Polynomial.X ^ (d ^ N - D N d) →
      IsSAPPT ρ

end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open Matrix Module
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}
private lemma occupation_fiber_card (x : Fin N → Fin d) (a : Fin d) :
    Fintype.card {i // x i = a} = (occupation x).count a := by
  rw [Fintype.subtype_card]
  simp only [occupation, ← Fin.univ_val_map, Multiset.count_map, ← Finset.filter_val,
    Finset.card_def, eq_comm]
private lemma occupation_same_orbit (x y : Fin N → Fin d) (h : occupation x = occupation y) :
    ∃ σ : Equiv.Perm (Fin N), y ∘ σ = x := by
  have hc (a : Fin d) : Fintype.card {i // x i = a} = Fintype.card {i // y i = a} := by
    rw [occupation_fiber_card, occupation_fiber_card, h]
  let e (a : Fin d) := Fintype.equivOfCardEq (hc a)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i
private lemma symmetric_occupation_constant (v : (Fin N → Fin d) → ℂ)
    (hv : IsSymmetricVector v) (x y : Fin N → Fin d) (h : occupation x = occupation y) :
    v x = v y := by
  obtain ⟨σ,hσ⟩ := occupation_same_orbit x y h
  rw [← hσ]
  exact hv σ y
private noncomputable def occupationEval (N d : ℕ) :
    LinearMap.range (P (Fin N) (Fin d)).mulVecLin →ₗ[ℂ] (Sym (Fin d) N → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun a : Sym (Fin d) N => representative a.1 a.2)).domRestrict
    (LinearMap.range (P (Fin N) (Fin d)).mulVecLin)
private lemma occupationEval_injective (N d : ℕ) : Function.Injective (occupationEval N d) := by
  intro u v h
  apply Subtype.ext
  funext x
  let a : Sym (Fin d) N := ⟨occupation x,occupation_card x⟩
  have he := congrFun h a
  have huSym : IsSymmetricVector u.val := by
    obtain ⟨w,hw⟩ := u.2
    rw [← hw]
    exact P_mulVec_symmetric w
  have hvSym : IsSymmetricVector v.val := by
    obtain ⟨w,hw⟩ := v.2
    rw [← hw]
    exact P_mulVec_symmetric w
  have hu := symmetric_occupation_constant u.val huSym (representative a.1 a.2) x
    (occupation_representative a.1 a.2)
  have hv := symmetric_occupation_constant v.val hvSym (representative a.1 a.2) x
    (occupation_representative a.1 a.2)
  change u.val (representative a.1 a.2) = v.val (representative a.1 a.2) at he
  exact hu.symm.trans (he.trans hv)
private lemma P_rank_le (N d : ℕ) (hd : 1 ≤ d) :
    (P (Fin N) (Fin d)).rank ≤ D N d := by
  have hh := LinearMap.finrank_le_finrank_of_injective (occupationEval_injective N d)
  simp only [Module.finrank_pi, Module.finrank_self, mul_one] at hh
  have hc : Fintype.card (Sym (Fin d) N) = D N d := by
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    have hn : d + N - 1 - N = d-1 := by omega
    have he := (Nat.choose_symm (n := d+N-1) (k := N) (by omega)).symm
    rw [hn] at he
    simpa only [D, Nat.add_comm] using he
  rwa [hc] at hh
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open scoped BigOperators Matrix ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral
open Matrix Polynomial
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma roots_shape (A : Matrix ι ι ℂ) (a b : ℝ) (r z : ℕ)
    (h : A.charpoly = (X-C (b:ℂ)) * (X-C (a:ℂ))^r * X^z) :
    A.charpoly.roots = ({(b:ℂ)} : Multiset ℂ) + r • {(a:ℂ)} + z • {0} := by
  rw [h, roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero _
    (X_sub_C_ne_zero _))) (pow_ne_zero _ X_ne_zero)),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero _ (X_sub_C_ne_zero _))),
    roots_X_sub_C, roots_pow, roots_X_sub_C, roots_X_pow]
private lemma rank_filter_roots (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    A.rank = (A.charpoly.roots.filter (· ≠ 0)).card := by
  rw [hA.rank_eq_card_non_zero_eigs, hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.filter_map, Function.comp_def, Complex.ofReal_eq_zero,
    Multiset.card_map, ← Finset.filter_val, ← Finset.card_def, Fintype.subtype_card]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_congr Complex.ofReal_eq_zero.symm
private lemma rank_shape (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (a b : ℝ) (r z : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : A.charpoly = (X-C (b:ℂ)) * (X-C (a:ℂ))^r * X^z) :
    A.rank = r+1 := by
  rw [rank_filter_roots A hA, roots_shape A a b r z h]
  have hf (n : ℕ) (c : ℂ) :
      (n • ({c} : Multiset ℂ)).filter (· ≠ 0) = n • (({c} : Multiset ℂ).filter (· ≠ 0)) := by
    exact Multiset.filter_nsmul (fun x => x ≠ 0) {c} n
  simp [Multiset.filter_add, hf, Multiset.filter_singleton, ha, hb, Nat.add_comm]
private lemma trace_shape (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (a b : ℝ) (r z : ℕ)
    (h : A.charpoly = (X-C (b:ℂ)) * (X-C (a:ℂ))^r * X^z) :
    A.trace = (b:ℂ) + r * (a:ℂ) := by
  rw [Matrix.trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly,
    roots_shape A a b r z h]
  simp [Multiset.sum_nsmul, nsmul_eq_mul]
private lemma eigenvalue_choices (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (a b : ℝ) (r z : ℕ)
    (h : A.charpoly = (X-C (b:ℂ)) * (X-C (a:ℂ))^r * X^z) (i : ι) :
    hA.eigenvalues i = b ∨ hA.eigenvalues i = a ∨ hA.eigenvalues i = 0 := by
  have hm : (hA.eigenvalues i : ℂ) ∈ A.charpoly.roots := by
    rw [hA.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i,Finset.mem_univ_val i,rfl⟩
  rw [roots_shape A a b r z h] at hm
  simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_nsmul,
    Complex.ofReal_inj, Complex.ofReal_eq_zero] at hm
  tauto
private lemma hermitian_ker_of_range (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hr : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin)
    (v : ι → ℂ) (hv : A *ᵥ v = 0) : B *ᵥ v = 0 := by
  have hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hr' : LinearMap.range (Matrix.toEuclideanLin B) ≤ LinearMap.range (Matrix.toEuclideanLin A) := by
    rintro w ⟨u,rfl⟩
    obtain ⟨y,hy⟩ := hr ⟨WithLp.ofLp u,rfl⟩
    refine ⟨WithLp.toLp 2 y,?_⟩
    exact congrArg (WithLp.toLp 2) hy
  have hk := LinearMap.ker_le_ker_of_range hS hT hr'
  have he := hk (show WithLp.toLp 2 v ∈ LinearMap.ker (Matrix.toEuclideanLin A) by
    simpa only [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.ofLp_toLp, hv, WithLp.toLp_zero])
  simpa only [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    WithLp.toLp_eq_zero] using he
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral

namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral
open Matrix
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma projection_trace_rank (P : Matrix ι ι ℂ) (hP : P*P=P) : P.trace = (P.rank : ℂ) := by
  have hId : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul,hP]
  exact (Matrix.trace_toLin'_eq P).symm.trans
    (LinearMap.IsIdempotentElem.isProj_range _ hId).trace
private lemma projection_eigenvector (A P : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hr : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) (i : ι) :
    P *ᵥ (fun x => hA.eigenvectorBasis i x) =
      if hA.eigenvalues i = 0 then 0 else (fun x => hA.eigenvectorBasis i x) := by
  by_cases hi : hA.eigenvalues i = 0
  · simp only [if_pos hi]
    apply hermitian_ker_of_range A P hA hP hr.le
    simp only [hA.mulVec_eigenvectorBasis,hi,zero_smul]
  · simp only [if_neg hi]
    have hm : (fun x => hA.eigenvectorBasis i x) ∈ LinearMap.range A.mulVecLin := by
      refine ⟨(hA.eigenvalues i)⁻¹ • (fun x => hA.eigenvectorBasis i x),?_⟩
      change A *ᵥ _ = _
      rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, smul_smul, inv_mul_cancel₀ hi, one_smul]
    rw [← hr] at hm
    obtain ⟨v,hv⟩ := hm
    change P *ᵥ v = _ at hv
    rw [← hv, Matrix.mulVec_mulVec,hPP]
private lemma spectral_residual_psd (A P : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPP : P*P=P)
    (hr : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) (a : ℝ)
    (hmin : ∀ i, hA.eigenvalues i ≠ 0 → a ≤ hA.eigenvalues i) :
    (A - a • P).PosSemidef := by
  let δ (i : ι) : ℝ := hA.eigenvalues i - a * if hA.eigenvalues i = 0 then 0 else 1
  have hδ (i : ι) : 0 ≤ δ i := by
    dsimp [δ]
    split_ifs with hi
    · simp [hi]
    · simpa using sub_nonneg.mpr (hmin i hi)
  have hdiag : (Matrix.diagonal (fun i => (δ i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ (δ i : ℂ)
      exact_mod_cast hδ i)
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hcol (i : ι) : (A-a • P) *ᵥ (fun x => hA.eigenvectorBasis i x) =
      δ i • (fun x => hA.eigenvectorBasis i x) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hA.mulVec_eigenvectorBasis,
      projection_eigenvector A P hA hP hPP hr i]
    dsimp [δ]
    split_ifs with hi
    · simp [hi]
    · module
  have he : (A-a • P)*U = U * diagonal (fun i => (δ i : ℂ)) := by
    ext x i
    change ((A-a • P) *ᵥ (fun x => hA.eigenvectorBasis i x)) x =
      (U * diagonal (fun i => (δ i : ℂ))) x i
    rw [hcol, Matrix.mul_diagonal]
    change (δ i : ℂ) * (hA.eigenvectorBasis i).ofLp x =
      (hA.eigenvectorBasis i).ofLp x * (δ i : ℂ)
    exact mul_comm _ _
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hf : A-a • P = U * diagonal (fun i => (δ i : ℂ)) * Uᴴ := by
    rw [← he, Matrix.mul_assoc,hu,Matrix.mul_one]
  rw [hf]
  exact hdiag.mul_mul_conjTranspose_same U
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
private lemma D_pos {N d : ℕ} (hd : 2 ≤ d) : 0 < D N d := by
  unfold D
  exact Nat.choose_pos (by omega)
private lemma pmin_pos (N d : ℕ) : 0 < pmin N d := by
  unfold pmin
  positivity
private lemma threshold_coefficient {N d : ℕ} (hd : 2 ≤ d)
    (p : ℝ) (hp : pmin N d ≤ p) (k : ℕ) (hk : k ≤ N) :
    0 ≤ p / ((D N d : ℝ) * (N.choose k : ℝ)) - (1-p)/2 := by
  have ha : (0 : ℝ) < D N d := by exact_mod_cast D_pos (N := N) hd
  have hb : (0 : ℝ) < N.choose k := by exact_mod_cast Nat.choose_pos hk
  have hc : (0 : ℝ) < N.choose (N/2) := by exact_mod_cast Nat.choose_pos (Nat.div_le_self N 2)
  have hbc : (N.choose k : ℝ) ≤ N.choose (N/2) := by exact_mod_cast Nat.choose_le_middle k N
  have hp0 : 0 ≤ p := (pmin_pos N d).le.trans hp
  have hden : 0 < 1+2*((D N d : ℝ)*(N.choose (N/2) : ℝ))⁻¹ := by positivity
  have h := (div_le_iff₀ hden).mp hp
  have hbase : (1-p)/2 ≤ p / ((D N d : ℝ) * (N.choose (N/2) : ℝ)) := by
    simp only [div_eq_mul_inv]
    nlinarith
  have hratio : p / ((D N d : ℝ)*(N.choose (N/2) : ℝ)) ≤
      p / ((D N d : ℝ)*(N.choose k : ℝ)) :=
    div_le_div_of_nonneg_left hp0 (mul_pos ha hb) (mul_le_mul_of_nonneg_left hbc ha.le)
  linarith
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
namespace D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open Matrix Polynomial Module
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}
private lemma operator_mulVec_symmetric (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hA : IsSymmetricOperator A) (v : (Fin N → Fin d) → ℂ) :
    IsSymmetricVector (A *ᵥ v) := by
  intro σ x
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro y _
  exact congrArg (· * v y) (hA y σ x)
private lemma P_mul_operator (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hA : IsSymmetricOperator A) : P (Fin N) (Fin d) * A = A := by
  ext x y
  exact congrFun (P_mulVec_of_symmetric (fun x => A x y) (hA y)) x
private lemma range_P_eq_of_rank (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hA : IsSymmetricOperator A) (hrank : A.rank = D N d) (hd : 1 ≤ d) :
    LinearMap.range (P (Fin N) (Fin d)).mulVecLin = LinearMap.range A.mulVecLin := by
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.range (P (Fin N) (Fin d)).mulVecLin := by
    rintro v ⟨w,rfl⟩
    exact ⟨A *ᵥ w, P_mulVec_of_symmetric _ (operator_mulVec_symmetric A hA w)⟩
  have he : finrank ℂ (LinearMap.range A.mulVecLin) = finrank ℂ (LinearMap.range (P (Fin N) (Fin d)).mulVecLin) := by
    apply le_antisymm (Submodule.finrank_mono hle)
    change (P (Fin N) (Fin d)).rank ≤ A.rank
    rw [hrank]
    exact P_rank_le N d hd
  exact (Submodule.eq_of_le_of_finrank_eq hle he).symm
private lemma PiS_operator_sandwich (S : Finset (Fin N))
    (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hA : IsSymmetricOperator A) (hH : A.IsHermitian) : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * A * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S = A := by
  have hleft : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * A = A := by
    calc
      D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * A = D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * (P (Fin N) (Fin d) * A) := by rw [P_mul_operator A hA]
      _ = A := by rw [← Matrix.mul_assoc,PiS_mul_P,P_mul_operator A hA]
  have hright : A * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S = A := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul,hH.eq,(PiS_hermitian (L := Fin d) S).eq] using h
  rw [hleft,hright]
private lemma fullyPPT_of_spectrum {N d : ℕ} (hd : 2 ≤ d) (p : ℝ)
    (hp : pmin N d ≤ p) (hp1 : p ≤ 1)
    (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hρ : ρ.PosSemidef) (hS : IsSymmetricOperator ρ)
    (hχ : ρ.charpoly =
      (Polynomial.X - Polynomial.C (((1 - ((D N d : ℝ) - 1) * p / D N d) : ℝ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((p / D N d) : ℝ) : ℂ)) ^ (D N d - 1) *
        Polynomial.X ^ (d ^ N - D N d)) : IsFullyPPT ρ := by
  let a : ℝ := p / D N d
  let b : ℝ := 1 - ((D N d : ℝ)-1)*p/D N d
  have hD : (0 : ℝ) < D N d := by exact_mod_cast D_pos (N := N) hd
  have hDn : 0 < D N d := D_pos hd
  have hp0 : 0 < p := (pmin_pos N d).trans_le hp
  have ha : 0 < a := div_pos hp0 hD
  have hba : b-a = 1-p := by dsimp [a,b]; field_simp [hD.ne']; ring
  have hb : 0 < b := by linarith
  have hrank : ρ.rank = D N d := by
    have h := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral.rank_shape ρ hρ.1 a b (D N d-1) (d^N-D N d) ha.ne' hb.ne' hχ
    omega
  have hrange := range_P_eq_of_rank ρ hS hrank (Nat.one_le_of_lt hd)
  have hmin (i) (hi : hρ.1.eigenvalues i ≠ 0) : a ≤ hρ.1.eigenvalues i := by
    rcases D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral.eigenvalue_choices ρ hρ.1 a b (D N d-1) (d^N-D N d) hχ i with h|h|h
    · rw [h]; linarith
    · rw [h]
    · exact (hi h).elim
  let B := ρ - a • P (Fin N) (Fin d)
  have hB : B.PosSemidef := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral.spectral_residual_psd ρ (P (Fin N) (Fin d))
    hρ.1 (P_hermitian (Fin N) (Fin d)) (P_idempotent (Fin N) (Fin d)) hrange a hmin
  have hPTrace : (P (Fin N) (Fin d)).trace = (D N d : ℂ) := by
    rw [D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral.projection_trace_rank _ (P_idempotent (Fin N) (Fin d))]
    congr 1
    change finrank ℂ (LinearMap.range (P (Fin N) (Fin d)).mulVecLin) = _
    rw [hrange]
    exact hrank
  have htrace : ρ.trace = 1 := by
    rw [D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.Spectral.trace_shape ρ hρ.1 a b (D N d-1) (d^N-D N d) hχ]
    have hcast : ((D N d-1 : ℕ) : ℝ) = (D N d : ℝ)-1 := Nat.cast_pred hDn
    have he : b + ((D N d-1 : ℕ) : ℝ)*a = 1 := by
      rw [hcast]
      dsimp [a,b]
      field_simp [hD.ne']
      ring
    exact_mod_cast he
  have hBtrace : B.trace.re = 1-p := by
    simp only [B,Matrix.trace_sub, Matrix.trace_smul,htrace,hPTrace,
      Complex.sub_re,Complex.one_re,Complex.real_smul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,
      mul_zero,sub_zero]
    dsimp [a]
    field_simp [hD.ne']
  intro S
  have hBS : IsSymmetricOperator B := by
    intro y σ x
    change ρ (x ∘ σ) y - a • P (Fin N) (Fin d) (x ∘ σ) y = ρ x y - a • P (Fin N) (Fin d) x y
    have hr : ρ (x ∘ σ) y = ρ x y := hS y σ x
    rw [hr]
    have he := P_mulVec_symmetric (I := Fin N) (L := Fin d) (Pi.single y 1) σ x
    simpa only [Matrix.mulVec_single_one,Matrix.col,Matrix.transpose_apply] using congrArg (ρ x y - a • ·) he
  have hcomp := PiS_operator_sandwich S B hBS hB.1
  have hPTcomp : D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S * partialTransposeOn S B * D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S = partialTransposeOn S B := by
    rw [← partialTranspose_PiS_sandwich,hcomp]
  have hm := compress_lower (partialTransposeOn S B) (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S) (B.trace.re/2)
    (PiS_hermitian S) (PiS_idempotent S) hPTcomp (psd_partialTranspose_half_trace S B hB)
  rw [hBtrace] at hm
  have hf : (partialTransposeOn S (P (Fin N) (Fin d)) - (N.choose S.card : ℝ)⁻¹ • D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP S).PosSemidef := by
    simpa only [Fintype.card_fin,RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.natCast_re,Complex.natCast_im] using
      symmetrizer_partialTranspose_floor (L := Fin d) S
  have hcard : S.card ≤ N := card_finset_fin_le S
  have hcoef : 0 ≤ a*(N.choose S.card : ℝ)⁻¹-(1-p)/2 := by
    simpa only [a,div_eq_mul_inv,mul_inv,mul_assoc] using threshold_coefficient hd p hp S.card hcard
  have hpos := ((hf.smul ha.le).add hm).add ((PiS_psd S).smul hcoef)
  convert hpos using 1
  ext x y
  simp only [partialTransposeOn, B, Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
    smul_add,smul_sub,smul_smul]
  module
private lemma symmetric_conjugate (ρ U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hρ : IsSymmetricOperator ρ) (hU : IsSymmetricUnitary U) :
    IsSymmetricOperator (U*ρ*Uᴴ) := by
  rw [Matrix.mul_assoc]
  intro y
  change IsSymmetricVector (U *ᵥ (ρ *ᵥ Uᴴ.col y))
  exact hU.2 _ (operator_mulVec_symmetric ρ hρ _)

private lemma unitary_conjugate_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (U*A*Uᴴ).charpoly = A.charpoly := by
  have h := Matrix.charpoly_units_conj (Unitary.toUnits ⟨U, hU⟩) A
  change (U * A * U⁻¹).charpoly = A.charpoly at h
  rwa [Matrix.inv_eq_left_inv (Unitary.mem_iff.mp hU).1] at h
theorem result : D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.claim := by
  intro N d hN hd p hp hp1 ρ hρ hS hχ U hU
  apply fullyPPT_of_spectrum hd p hp hp1 (U*ρ*Uᴴ)
  · exact hρ.mul_mul_conjTranspose_same U
  · exact symmetric_conjugate ρ U hS hU
  · rw [unitary_conjugate_charpoly ρ U hU.1]
    exact hχ
end D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
