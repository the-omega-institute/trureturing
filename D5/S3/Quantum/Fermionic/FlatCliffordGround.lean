/- GID: D5/S3/Quantum/Fermionic/FlatCliffordGround
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/FlatCliffordGround
   mirror-E: none(waiver:uniform-flat-Clifford-spectrum)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Hermitian]
   utility: none
   digest: A flat real skew coupling has an exact physical Clifford ground density. -/

/-
flat_clifford_ground:
  proof_shape: content
  escape_witness: orthogonally pair the flat skew matrix, transport its Clifford
    generators, and construct the joint minus density using independent reversals.
admission_basis: escape-witness
Same-delivery inlined content: CliffordGroundDensity, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/QuadraticForms/PositiveDefiniteWilliamson.skew_paired_basis_induction
    statement_id: sha256:54436ecddd85ddabca9cde51fd34930a3412b14577a5dd01f02b1f5f542233e1
  GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
    statement_id: sha256:b8e1957ba4f81600248989dc21f0a107bcdd5ce2e68546c38b9164c4a09ac337
  GID: D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity.meanEnergy
    statement_id: sha256:9968a03e56960da489176141fea72cbed63e67cc32e2fe1378c92e3fed11906b
  GID: D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
    statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
computational_content.kind: none; arbitrary finite flat skew couplings.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Fermionic.CliffordGroundDensity
import D5.S3.QuadraticForms.PositiveDefiniteWilliamson
open Matrix Module WithLp
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Fermionic.CliffordGroundDensity
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity
noncomputable section

namespace D5.S3.Quantum.Fermionic.FlatCliffordGround

theorem flat_clifford_ground {α Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (L : ℕ) (hα : Fintype.card α = 2*L) (hΩ : Fintype.card Ω = 2^L)
    (A : Matrix α α ℝ) (hskew : A.transpose = -A)
    (d : ℝ) (hd : 0 ≤ d) (hsq : A*A = (-d) • 1)
    (gamma : α → Matrix Ω Ω ℂ) (hherm : ∀ p, (gamma p).IsHermitian)
    (hcar : ∀ p q, gamma p * gamma q + gamma q * gamma p =
      if p = q then (2 : ℂ) • 1 else 0)
    (T : Matrix Ω Ω ℂ) (hpar : ∀ p, T * gamma p = -(gamma p * T)) :
    let Q := (Complex.I/2 : ℂ) • ∑ p, ∑ q, (A p q : ℂ) • (gamma p * gamma q)
    IsSelfAdjoint (CStarMatrix.ofMatrix Q) ∧
    ∃ rho : DensityState Ω,
      IsStarProjection (CStarMatrix.ofMatrix.symm rho.val) ∧
      Commute rho.val (CStarMatrix.ofMatrix T) ∧
      Q * CStarMatrix.ofMatrix.symm rho.val =
        (-(L : ℂ) * (Real.sqrt d : ℂ)) • CStarMatrix.ofMatrix.symm rho.val ∧
      ∀ omega : DensityState Ω,
        -(L : ℝ) * Real.sqrt d ≤ meanEnergy (CStarMatrix.ofMatrix Q) omega := by
  classical
  have hbasis
    (A : Matrix α α ℝ) (hskew : A.transpose = -A)
    (heven : Even (Fintype.card α)) (d : ℝ) (hd : 0 ≤ d)
    (hsq : A*A = (-d) • 1) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (O : Matrix α (κ ⊕ κ) ℝ),
      Fintype.card α = 2 * Fintype.card κ ∧ O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      (∀ k, A *ᵥ (fun i => O i (Sum.inl k)) =
        -Real.sqrt d • (fun i => O i (Sum.inr k))) ∧
      (∀ k, A *ᵥ (fun i => O i (Sum.inr k)) =
        Real.sqrt d • (fun i => O i (Sum.inl k))) := by
    classical
    let a := Matrix.toEuclideanLin A
    have ha (x y : EuclideanSpace ℝ α) : ⟪a x,y⟫_ℝ = -⟪x,a y⟫_ℝ := by
      simp only [a, PiLp.inner_apply, RCLike.inner_apply]
      change y ⬝ᵥ (A *ᵥ x) = -((A *ᵥ y) ⬝ᵥ x)
      rw [← Matrix.dotProduct_transpose_mulVec, hskew, Matrix.neg_mulVec]
      simp [dotProduct_neg, dotProduct_comm]
    have he : Even (finrank ℝ (EuclideanSpace ℝ α)) := by simpa using heven
    have hlin (x : EuclideanSpace ℝ α) : a (a x) = -d • x := by
      change toLp 2 (A *ᵥ (A *ᵥ x)) = _
      rw [Matrix.mulVec_mulVec,hsq]
      apply (WithLp.equiv 2 _).injective
      change ((-d) • (1 : Matrix α α ℝ)) *ᵥ ofLp x = (-d) • ofLp x
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    obtain ⟨κ,inst,b,ν,hν,hl,hr⟩ :=
      D5.S3.QuadraticForms.PositiveDefiniteWilliamson.skew_paired_basis_induction
        (finrank ℝ (EuclideanSpace ℝ α)) a ha rfl he
    letI : Fintype κ := inst
    letI : DecidableEq κ := Classical.decEq κ
    have hfreq (k : κ) : ν k = Real.sqrt d := by
      have hnonzero : b (Sum.inl k) ≠ 0 := b.orthonormal.ne_zero (Sum.inl k)
      have htwice := hlin (b (Sum.inl k))
      rw [hl k,map_smul,hr k,smul_smul] at htwice
      have hh := (smul_left_injective ℝ hnonzero) htwice
      nlinarith [Real.sq_sqrt hd,Real.sqrt_nonneg d,hν k]
    let O := (EuclideanSpace.basisFun α ℝ).toBasis.toMatrix b
    have hOt : O.transpose * O = 1 := by
      have h := (EuclideanSpace.basisFun α ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self b
      simpa [O] using h
    have hO : O * O.transpose = 1 := by
      have h := (EuclideanSpace.basisFun α ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose b
      simpa [O] using h
    have hcard : Fintype.card α = 2 * Fintype.card κ := by
      have hh := Module.finrank_eq_card_basis b.toBasis
      simpa [Fintype.card_sum,two_mul] using hh
    refine ⟨κ,inst,Classical.decEq κ,O,hcard,hOt,hO,?_,?_⟩
    · intro k
      have h := hl k
      rw [hfreq] at h
      have hh := congrArg (fun v : EuclideanSpace ℝ α => ofLp v) h
      simpa [a,O,Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr] using hh
    · intro k
      have h := hr k
      rw [hfreq] at h
      have hh := congrArg (fun v : EuclideanSpace ℝ α => ofLp v) h
      simpa [a,O,Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr] using hh
  have hcarChange {β : Type} [Fintype β] [DecidableEq β]
    (gamma : α → Matrix Ω Ω ℂ)
    (hgamma : ∀ p q, gamma p * gamma q + gamma q * gamma p =
      if p = q then (2 : ℂ) • 1 else 0)
    (O : Matrix α β ℝ) (hO : O.transpose * O = 1) :
    let eta := fun p => ∑ t, (O t p : ℂ) • gamma t
    ∀ p q, eta p * eta q + eta q * eta p =
      if p = q then (2 : ℂ) • 1 else 0 := by
    classical
    dsimp only
    intro p q
    have hentry : (∑ t, (O t p : ℂ) * (O t q : ℂ)) = if p = q then 1 else 0 := by
      have h := congrArg (fun M : Matrix β β ℝ => M p q) hO
      change (∑ t, O t p * O t q) = (1 : Matrix β β ℝ) p q at h
      rw [Matrix.one_apply] at h
      by_cases hpq : p = q
      · simpa [hpq] using congrArg Complex.ofReal h
      · simpa [hpq] using congrArg Complex.ofReal h
    calc
      _ = ∑ t, ∑ u, ((O t p : ℂ) * (O u q : ℂ)) •
          (gamma t * gamma u + gamma u * gamma t) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
          Matrix.mul_smul, Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro u _
        rw [mul_comm]
      _ = ∑ t, ((O t p : ℂ) * (O t q : ℂ) * 2) • (1 : Matrix Ω Ω ℂ) := by
        simp only [hgamma]
        apply Finset.sum_congr rfl
        intro t _
        simp [smul_smul]
      _ = (2 * ∑ t, (O t p : ℂ) * (O t q : ℂ)) • (1 : Matrix Ω Ω ℂ) := by
        rw [← Finset.sum_smul]
        congr 1
        simp_rw [mul_comm _ (2 : ℂ)]
        rw [Finset.mul_sum]
      _ = _ := by
        rw [hentry]
        split_ifs <;> simp
  have hquadChange {β : Type} [Fintype β] [DecidableEq β]
    (A : Matrix α α ℝ) (O : Matrix α β ℝ) (hO : O * O.transpose = 1)
    (gamma : α → Matrix Ω Ω ℂ) :
    let eta := fun p => ∑ t, (O t p : ℂ) • gamma t
    (∑ p, ∑ q, (A p q : ℂ) • (gamma p * gamma q)) =
      ∑ p, ∑ q, ((O.transpose * A * O) p q : ℂ) • (eta p * eta q) := by
    classical
    dsimp only
    have hinv (p q : α) : (∑ k, (O p k : ℂ) * (O q k : ℂ)) = if p=q then 1 else 0 := by
      have h := congrArg (fun M : Matrix α α ℝ => M p q) hO
      change (∑ k, O p k * O q k) = (1 : Matrix α α ℝ) p q at h
      split_ifs with hpq <;> simpa [Matrix.one_apply,hpq] using congrArg Complex.ofReal h
    have he (p q : β) : ((O.transpose * A * O) p q : ℂ) =
        ∑ i, ∑ j, (O i p : ℂ) * (A i j : ℂ) * (O j q : ℂ) := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply,Complex.ofReal_sum,
        Complex.ofReal_mul,Finset.sum_mul]
      rw [Finset.sum_comm]
    let eta := fun p => ∑ t, (O t p : ℂ) • gamma t
    have hback (i : α) : ∑ p, (O i p : ℂ) • eta p = gamma i := by
      simp only [eta,Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul,hinv]
      simp
    have hperm (f : β → β → α → α → Matrix Ω Ω ℂ) :
        (∑ p, ∑ q, ∑ i, ∑ j, f p q i j) = ∑ i, ∑ j, ∑ p, ∑ q, f p q i j := by
      calc
        _ = ∑ p, ∑ i, ∑ q, ∑ j, f p q i j := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ p, ∑ q, ∑ j, f p q i j := by rw [Finset.sum_comm]
        _ = ∑ i, ∑ p, ∑ j, ∑ q, f p q i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    change _ = ∑ p, ∑ q, ((O.transpose * A * O) p q : ℂ) • (eta p * eta q)
    simp_rw [he]
    simp only [Finset.sum_smul]
    rw [hperm]
    symm
    calc
      _ = ∑ i, ∑ j, (A i j : ℂ) •
          ((∑ p, (O i p : ℂ) • eta p) * (∑ q, (O j q : ℂ) • eta q)) := by
        simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,
          Finset.smul_sum,smul_smul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        congr 1
        ring
      _ = _ := by simp only [hback]
  have heven : Even (Fintype.card α) := by rw [hα]; exact even_two_mul L
  obtain ⟨κ,inst,deq,O,hcard,hOt,hO,hl,hr⟩ := hbasis A hskew heven d hd hsq
  letI : Fintype κ := inst
  letI : DecidableEq κ := deq
  have hκ : Fintype.card κ = L := by omega
  let eta := fun p => ∑ t, (O t p : ℂ) • gamma t
  have heta := hcarChange gamma hcar O hOt
  have hηherm (p : κ ⊕ κ) : (eta p).IsHermitian := by
    change IsSelfAdjoint (∑ t, (O t p : ℂ) • gamma t)
    apply isSelfAdjoint_sum
    intro t _
    exact (IsSelfAdjoint.all (O t p)).smul (hherm t).isSelfAdjoint
  have hηpar (p : κ ⊕ κ) : T * eta p = -(eta p * T) := by
    simp only [eta,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,hpar,
      smul_neg,Finset.sum_neg_distrib]
  let S := O.transpose * A * O
  have hleft (p : κ ⊕ κ) (k : κ) :
      S p (Sum.inl k) = -Real.sqrt d * (if p = Sum.inr k then 1 else 0) := by
    dsimp only [S]
    rw [Matrix.mul_assoc]
    change (∑ i, O i p * (A *ᵥ (fun j => O j (Sum.inl k))) i) = _
    rw [hl]
    have ho := congrArg (fun M : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ => M p (Sum.inr k)) hOt
    change (∑ i, O i p * O i (Sum.inr k)) = (if p = Sum.inr k then 1 else 0) at ho
    rw [← ho,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have hright (p : κ ⊕ κ) (k : κ) :
      S p (Sum.inr k) = Real.sqrt d * (if p = Sum.inl k then 1 else 0) := by
    dsimp only [S]
    rw [Matrix.mul_assoc]
    change (∑ i, O i p * (A *ᵥ (fun j => O j (Sum.inr k))) i) = _
    rw [hr]
    have ho := congrArg (fun M : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ => M p (Sum.inl k)) hOt
    change (∑ i, O i p * O i (Sum.inl k)) = (if p = Sum.inl k then 1 else 0) at ho
    rw [← ho,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  let B (k : κ) := Complex.I • (eta (Sum.inl k) * eta (Sum.inr k))
  have hQ : (Complex.I/2 : ℂ) • ∑ p, ∑ q, (A p q : ℂ) • (gamma p * gamma q) =
      (Real.sqrt d : ℂ) • ∑ k, B k := by
    rw [hquadChange A O hO gamma]
    change (Complex.I/2 : ℂ) • (∑ p, ∑ q, (S p q : ℂ) • (eta p * eta q)) = _
    simp only [Fintype.sum_sum_type,hleft,hright,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,if_false,mul_zero,Complex.ofReal_zero,zero_smul,
      Finset.sum_const_zero,zero_add,add_zero]
    have ha (k : κ) : eta (Sum.inr k) * eta (Sum.inl k) =
        -(eta (Sum.inl k) * eta (Sum.inr k)) := by
      have h := heta (Sum.inr k) (Sum.inl k)
      rw [if_neg (by simp)] at h
      exact eq_neg_of_add_eq_zero_left h
    simp only [Complex.ofReal_mul,Complex.ofReal_neg,apply_ite,
      Complex.ofReal_one,Complex.ofReal_zero,ite_smul,mul_one,mul_zero,zero_smul,
      smul_ite,smul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      ha,smul_neg,neg_smul,neg_neg]
    simp only [smul_add,Finset.smul_sum,smul_smul,B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    module
  obtain ⟨rho,hproj,hphys,hground,hlower⟩ := paired_clifford_ground
    (by simpa [hκ] using hΩ) eta hηherm heta T hηpar
  rw [hQ]
  dsimp only
  have hBherm (k : κ) : (B k).IsHermitian := by
    have hc := heta (Sum.inl k) (Sum.inr k)
    rw [if_neg (by simp)] at hc
    have ha : eta (Sum.inr k) * eta (Sum.inl k) =
        -(eta (Sum.inl k) * eta (Sum.inr k)) := eq_neg_of_add_eq_zero_right hc
    change (Complex.I • (eta (Sum.inl k) * eta (Sum.inr k)))ᴴ = _
    simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
      (hηherm _).eq,Complex.star_def,Complex.conj_I,ha,neg_smul,smul_neg,neg_neg]
    rfl
  have hHerm : IsSelfAdjoint (CStarMatrix.ofMatrix ((Real.sqrt d : ℂ) • ∑ k, B k)) := by
    have hh : IsSelfAdjoint (∑ k, B k) := isSelfAdjoint_sum _ (fun k _ => (hBherm k).isSelfAdjoint)
    have hg := (IsSelfAdjoint.all (Real.sqrt d)).smul hh
    exact hg.map CStarMatrix.ofMatrixStarAlgEquiv
  refine ⟨hHerm,rho,hproj,hphys,?_,?_⟩
  · rw [Matrix.smul_mul,hground,smul_smul,hκ,mul_comm]
  · intro omega
    have hh := mul_le_mul_of_nonneg_left (hlower omega) (Real.sqrt_nonneg d)
    rw [hκ] at hh
    unfold meanEnergy
    change -(L:ℝ)*Real.sqrt d ≤
      (Matrix.trace (((Real.sqrt d : ℂ) • (∑ k, B k)) * CStarMatrix.ofMatrix.symm omega.val)).re
    rw [Matrix.smul_mul,Matrix.trace_smul]
    simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    change -(L:ℝ)*Real.sqrt d ≤ Real.sqrt d * meanEnergy (CStarMatrix.ofMatrix (∑ k, B k)) omega
    nlinarith


end D5.S3.Quantum.Fermionic.FlatCliffordGround
