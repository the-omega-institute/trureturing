/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.claim; result=D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.result; claim=D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction.claim
   digest: Kernel isolation for the native width-three scalar-Gram obstruction. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The global scalar-Gram equation retains the native rectangular tensor grouping. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

open Matrix Module
open scoped ComplexConjugate

/-- The ordered-cone flat-spectrum assertion, with both Gram identities at equality. -/
def claim : Prop :=
  ∀ (a b c d : ℕ), 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (lam : ℝ), 0 < lam ∧
      (b * c ≤ a * d →
        (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
          (lam : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) ∧
      (a * d ≤ b * c →
        QuantumMaxFlowBound.flow M N * (QuantumMaxFlowBound.flow M N)ᴴ =
          (lam : ℂ) • (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))

private def otherMap {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (r : Fin 3) :=
  LinearMap.pi (fun s : {s : Fin 3 // s ≠ r} => M s.val)

private theorem isolated_pair {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (hM : ∀ x, (∀ r, M r x = 0) → x = 0) (hab : 5 * a < 2 * b)
    (i j : Fin 3) :
    ∃ x y, (∀ r, r ≠ i → M r x = 0) ∧
      (∀ r, r ≠ j → M r y = 0) ∧ inner ℂ (M i x) (M j y) ≠ 0 := by
  classical
  let K (r : Fin 3) := LinearMap.ker (otherMap M r)
  let f (r : Fin 3) := (M r).domRestrict (K r)
  let L (r : Fin 3) := LinearMap.range (f r)
  have memK (r : Fin 3) (x : EuclideanSpace ℂ (Fin b)) :
      x ∈ K r ↔ ∀ s, s ≠ r → M s x = 0 := by
    simp [K, otherMap, LinearMap.mem_ker, funext_iff]
  have hf (r : Fin 3) : Function.Injective (f r) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    apply hM
    intro s
    by_cases hs : s = r
    · subst s
      exact hx
    · exact (memK r x.val).mp x.property s hs
  have hdim (r : Fin 3) : b ≤ finrank ℂ (L r) + 2 * a := by
    have hn := (otherMap M r).finrank_range_add_finrank_ker
    have hr := Submodule.finrank_le (LinearMap.range (otherMap M r))
    have hc : Fintype.card {s : Fin 3 // s ≠ r} = 2 := by
      simp
    have hp : finrank ℂ ({s : Fin 3 // s ≠ r} → EuclideanSpace ℂ (Fin a)) = 2 * a := by
      simp [Module.finrank_pi_fintype, hc]
    rw [hp] at hr
    have he : finrank ℂ (L r) = finrank ℂ (K r) :=
      LinearMap.finrank_range_of_inj (hf r)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hn
    dsimp [K] at he
    omega
  by_contra h
  have hz : ∀ x : K i, ∀ y : K j, inner ℂ (f i x) (f j y) = 0 := by
    intro x y
    by_contra hxy
    exact h ⟨x.val, y.val, (memK i x.val).mp x.property,
      (memK j y.val).mp y.property, hxy⟩
  have hle : L j ≤ (L i)ᗮ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    exact hz x y
  have hd := Submodule.finrank_mono hle
  have ho := (L i).finrank_add_finrank_orthogonal
  simp only [finrank_euclideanSpace, Fintype.card_fin] at ho
  have hi := hdim i
  have hj := hdim j
  omega

private theorem gram_independent {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (hM : ∀ x, (∀ r, M r x = 0) → x = 0) (hab : 5 * a < 2 * b) :
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1).adjoint.comp (M p.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro z hz ⟨i, j⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := isolated_pair M hM hab i j
  have he := congrArg (fun T : EuclideanSpace ℂ (Fin b) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin b) => inner ℂ x (T y)) hz
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, LinearMap.adjoint_inner_right,
    LinearMap.zero_apply, inner_zero_right] at he
  have hs : (∑ p : Fin 3 × Fin 3, z p * inner ℂ (M p.1 x) (M p.2 y)) =
      z (i, j) * inner ℂ (M i x) (M j y) := by
    apply Finset.sum_eq_single (i, j)
    · intro p _ hp
      by_cases hpi : p.1 = i
      · have hpj : p.2 ≠ j := by
          intro hpj
          exact hp (Prod.ext hpi hpj)
        simp [hy _ hpj]
      · simp [hx _ hpi]
    · simp
  rw [hs] at he
  exact (mul_eq_zero.mp he).resolve_right hxy

private theorem matrix_gram_independent {a b : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hM : ∀ x : EuclideanSpace ℂ (Fin b),
      (∀ r, (M r).toEuclideanLin x = 0) → x = 0) (hab : 5 * a < 2 * b) :
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1)ᴴ * M p.2) := by
  have h := gram_independent (fun r => (M r).toEuclideanLin) hM hab
  have he : (fun p : Fin 3 × Fin 3 => (M p.1).toEuclideanLin.adjoint.comp
      (M p.2).toEuclideanLin) =
      fun p => Matrix.toEuclideanLin ((M p.1)ᴴ * M p.2) := by
    funext p
    simp [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [he] at h
  exact h.of_comp

private theorem scalar_gram_injective {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (F : Matrix m n ℂ) {lam : ℂ} (hlam : lam ≠ 0)
    (hF : Fᴴ * F = lam • 1) : Function.Injective F.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h : lam • x = 0 := by
    calc
      lam • x = (Fᴴ * F) *ᵥ x := by
        rw [hF, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = Fᴴ *ᵥ (F *ᵥ x) := (Matrix.mulVec_mulVec x Fᴴ F).symm
      _ = 0 := by change F *ᵥ x = 0 at hx; rw [hx]; simp
  exact (smul_eq_zero.mp h).resolve_left hlam

theorem flow_common_kernel {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (hc : 0 < c)
    {lam : ℂ} (hlam : lam ≠ 0)
    (hF : (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1) :
    ∀ x : EuclideanSpace ℂ (Fin b),
      (∀ r, (M r).toEuclideanLin x = 0) → x = 0 := by
  intro x hx
  let k : Fin c := ⟨0, hc⟩
  let v : Fin b × Fin c → ℂ := fun p => x p.1 * (if p.2 = k then (1 : ℂ) else 0)
  have hv : QuantumMaxFlowBound.flow M N *ᵥ v = 0 := by
    funext p
    rcases p with ⟨u, w⟩
    simp only [QuantumMaxFlowBound.flow, Matrix.sum_mulVec, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    have hm : (M r) *ᵥ WithLp.ofLp x = 0 := by
      exact congrArg WithLp.ofLp (hx r)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kronecker, Matrix.kroneckerMap_apply, v]
    simp_rw [show ∀ j l, M r u j * N r w l * (x j * (if l = k then (1 : ℂ) else 0)) =
      (M r u j * x j) * (N r w l * (if l = k then (1 : ℂ) else 0)) by intros; ring]
    rw [← Finset.sum_mul_sum]
    have hh := congrFun hm u
    change (∑ j, M r u j * x j) = 0 at hh
    rw [hh, zero_mul]
  have hz : v = 0 := scalar_gram_injective _ hlam hF (by simpa using hv)
  apply WithLp.ofLp_injective 2
  funext j
  have h := congrFun hz (j, k)
  simpa [v] using h

private theorem flow_gram {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) :
    (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
      ∑ p : Fin 3 × Fin 3, Matrix.kronecker ((M p.1)ᴴ * M p.2)
        ((N p.1)ᴴ * N p.2) := by
  simp only [QuantumMaxFlowBound.flow, Matrix.kronecker, Matrix.conjTranspose_sum,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem scalar_cross_grams {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (k : Fin c)
    (hLI : LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1)ᴴ * M p.2))
    {lam : ℂ}
    (hF : (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1) :
    ∀ r s, (N r)ᴴ * N s = (((N r)ᴴ * N s) k k) • 1 := by
  classical
  rw [flow_gram] at hF
  have he (u v : Fin b) (l m : Fin c) :
      (∑ p : Fin 3 × Fin 3, ((M p.1)ᴴ * M p.2) u v *
        ((N p.1)ᴴ * N p.2) l m) =
      lam * (if u = v then 1 else 0) * (if l = m then 1 else 0) := by
    have h := congrArg (fun A : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ =>
      A (u, l) (v, m)) hF
    by_cases huv : u = v <;> by_cases hlm : l = m <;>
      simpa [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq, huv, hlm] using h
  intro r s
  ext l m
  let z (p : Fin 3 × Fin 3) := ((N p.1)ᴴ * N p.2) l m -
    ((N p.1)ᴴ * N p.2) k k * (if l = m then 1 else 0)
  have hz : ∑ p, z p • ((M p.1)ᴴ * M p.2) = 0 := by
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, z,
      sub_mul, Finset.sum_sub_distrib, Matrix.zero_apply]
    simp_rw [mul_comm (((N _)ᴴ * N _) l m),
      show ∀ p : Fin 3 × Fin 3,
        (((N p.1)ᴴ * N p.2) k k * (if l = m then 1 else 0)) *
          ((M p.1)ᴴ * M p.2) u v =
        (((M p.1)ᴴ * M p.2) u v * ((N p.1)ᴴ * N p.2) k k) *
          (if l = m then 1 else 0) by intro p; ring]
    rw [← Finset.sum_mul, he, he]
    simp
  have h := (Fintype.linearIndependent_iff.mp hLI) z hz (r, s)
  have h' := sub_eq_zero.mp h
  simpa [z, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] using h'

theorem rank_kronecker_one (H : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ) :
    (Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ)).rank = n * H.rank := by
  classical
  let e : (Fin 3 × Fin n) ≃ (Σ _ : Fin n, Fin 3) :=
    (Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm
  have he : (Matrix.blockDiagonal' (fun _ : Fin n => H)).submatrix e e =
      Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨r, i⟩ ⟨s, j⟩
    by_cases hij : i = j
    · subst j
      simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply]
    · simp [e, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.blockDiagonal'_apply_ne, hij]
  rw [← he, Matrix.rank_submatrix,
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Blocks.rank_block]
  simp

def stack {a b : ℕ} (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ) :
    Matrix (Fin 3 × Fin a) (Fin b) ℂ := fun p j => M p.1 p.2 j

def concat {c d : ℕ} (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) :
    Matrix (Fin d) (Fin 3 × Fin c) ℂ := fun i p => N p.1 i p.2

theorem concat_gram {c d : ℕ}
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (H : Matrix (Fin 3) (Fin 3) ℂ)
    (hN : ∀ r s, (N r)ᴴ * N s = H r s • 1) :
    (concat N)ᴴ * concat N = Matrix.kronecker H (1 : Matrix (Fin c) (Fin c) ℂ) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  have h := congrArg (fun A : Matrix (Fin c) (Fin c) ℂ => A i j) (hN r s)
  simpa [concat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul] using h

theorem stack_gram {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (k : Fin c) {lam : ℂ}
    (hF : (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1) :
    (stack M)ᴴ * Matrix.kronecker (fun r s => ((N r)ᴴ * N s) k k)
      (1 : Matrix (Fin a) (Fin a) ℂ) * stack M = lam • 1 := by
  rw [flow_gram] at hF
  ext u v
  have h := congrArg (fun A : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ =>
    A (u, k) (v, k)) hF
  simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq, and_true] at h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, stack]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum] at h ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [← h]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]

/-- A native width-three scalar column Gram forces the opposite dimension to be at least `3c`.
Only positivity of `c` is needed in addition to the strict dimension threshold. -/
theorem obstruction {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (hc : 0 < c)
    (hab : 5 * a < 2 * b) (lam : ℝ) (hlam : 0 < lam)
    (hF : (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
      (lam : ℂ) • 1) : 3 * c ≤ d := by
  classical
  have hlam' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  have hLI := matrix_gram_independent M (flow_common_kernel M N hc hlam' hF) hab
  let k : Fin c := ⟨0, hc⟩
  let H : Matrix (Fin 3) (Fin 3) ℂ := fun r s => ((N r)ᴴ * N s) k k
  have hN : ∀ r s, (N r)ᴴ * N s = H r s • 1 :=
    scalar_cross_grams M N k hLI hF
  have hJ : (stack M)ᴴ * Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ) *
      stack M = (lam : ℂ) • 1 := stack_gram M N k hF
  have hbr : b ≤ a * H.rank := by
    calc
      b = ((lam : ℂ) • (1 : Matrix (Fin b) (Fin b) ℂ)).rank := by
        rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_of_ne_zero hlam'), Matrix.rank_one]
        simp
      _ = ((stack M)ᴴ * Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ) *
          stack M).rank := congrArg Matrix.rank hJ.symm
      _ ≤ (Matrix.kronecker H (1 : Matrix (Fin a) (Fin a) ℂ)).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ = a * H.rank := rank_kronecker_one H a
  have hr : H.rank = 3 := by
    have hle : H.rank ≤ 3 := by simpa using H.rank_le_card_width
    by_contra hne
    have htwo : H.rank ≤ 2 := by omega
    have hmul := Nat.mul_le_mul_left a htwo
    nlinarith
  calc
    3 * c = (Matrix.kronecker H (1 : Matrix (Fin c) (Fin c) ℂ)).rank := by
      rw [rank_kronecker_one, hr]
      omega
    _ = ((concat N)ᴴ * concat N).rank := congrArg Matrix.rank (concat_gram N H hN).symm
    _ ≤ (concat N).rank := Matrix.rank_mul_le_right _ _
    _ ≤ d := by simpa using (concat N).rank_le_card_height

/-- The ordered cone contains `(5,13,5,13)`, where the column-Gram obstruction applies. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨M, N, lam, hlam, hcol, _⟩ :=
    h 5 13 5 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hdim := obstruction M N (by norm_num) (by norm_num) lam hlam (hcol (by norm_num))
  norm_num at hdim

end D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
