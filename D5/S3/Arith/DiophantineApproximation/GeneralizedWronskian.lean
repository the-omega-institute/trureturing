/- GID: D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/GeneralizedWronskian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Linearly independent polynomials admit a nonzero generalized Wronskian. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Data.Finsupp.Antidiagonal
public import D5.S3.Arith.DiophantineApproximation.PolynomialIndex
public import D5.S3.Arith.DiophantineApproximation.Wronskian
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

-- Used only by the acceptance criteria.

@[expose] public section


noncomputable section

namespace Finsupp

/-- **Kronecker's choice of weights.** Any finite set of exponent vectors is separated by a single
`ℕ`-valued weight. The weights `e t = x ^ ι t`, for an `ι` injective on the variables that occur,
separate `μ` from `ν` unless `x` is a root of `∑ t, (μ t - ν t) X ^ ι t`, which is not the zero
polynomial; finitely many nonzero polynomials have finitely many roots between them. -/
theorem exists_weight_injOn {σ : Type*} (T : Finset (σ →₀ ℕ)) :
    ∃ e : σ → ℕ, ∀ μ ∈ T, ∀ ν ∈ T, weight e μ = weight e ν → μ = ν := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Finset σ, V = T.biUnion fun μ ↦ μ.support := ⟨_, rfl⟩
  have hsupp : ∀ μ ∈ T, ∀ t : σ, t ∉ V → μ t = 0 := by
    intro μ hμ t ht
    by_contra hc
    exact ht (hV ▸ Finset.mem_biUnion.mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hc⟩)
  obtain ⟨ι, hι⟩ : ∃ ι : σ → ℕ,
      ∀ t₁ ∈ V, ∀ t₂ ∈ V, ι t₁ = ι t₂ → t₁ = t₂ := by
    refine ⟨fun t ↦ if h : t ∈ V then ((Fintype.equivFin V) ⟨t, h⟩ : ℕ) else 0,
      fun t₁ h₁ t₂ h₂ h ↦ ?_⟩
    simp only [h₁, h₂, dite_true] at h
    exact congrArg Subtype.val ((Fintype.equivFin V).injective (Fin.val_injective h))
  obtain ⟨P, hP⟩ : ∃ P : (σ →₀ ℕ) → (σ →₀ ℕ) → Polynomial ℤ, P = fun μ ν ↦
      ∑ t ∈ V, Polynomial.C ((μ t : ℤ) - (ν t : ℤ)) * Polynomial.X ^ ι t := ⟨_, rfl⟩
  have hcoeff : ∀ μ ν : σ →₀ ℕ, ∀ t ∈ V, (P μ ν).coeff (ι t) = (μ t : ℤ) - (ν t : ℤ) := by
    intro μ ν t ht
    rw [hP]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single t (fun b hb hbt ↦ ?_) fun h ↦ absurd ht h]
    · simp
    · have hne : ι t ≠ ι b := fun h ↦ hbt (hι b hb t ht h.symm)
      simp [hne]
  have hPne : ∀ μ ∈ T, ∀ ν ∈ T, μ ≠ ν → P μ ν ≠ 0 := by
    intro μ hμ ν hν hne h
    refine hne (Finsupp.ext fun t ↦ ?_)
    by_cases ht : t ∈ V
    · have hc := hcoeff μ ν t ht
      rw [h, Polynomial.coeff_zero] at hc
      omega
    · rw [hsupp μ hμ t ht, hsupp ν hν t ht]
  obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial ℤ,
      Q = ∏ p ∈ (T ×ˢ T).filter fun p ↦ p.1 ≠ p.2, P p.1 p.2 := ⟨_, rfl⟩
  have hQne : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
    obtain ⟨hmem, hne⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    exact hPne _ h1 _ h2 hne
  obtain ⟨x, hx⟩ : ∃ x : ℕ, ¬ Q.IsRoot (x : ℤ) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hQne (Polynomial.eq_zero_of_infinite_isRoot Q ?_)
    exact Set.Infinite.mono (fun y hy ↦ by obtain ⟨m, rfl⟩ := hy; exact hcon m)
      (Set.infinite_range_of_injective fun a b h ↦ Nat.cast_injective h)
  have hw : ∀ μ ∈ T, ((weight (fun t ↦ x ^ ι t) μ : ℕ) : ℤ)
      = ∑ t ∈ V, (μ t : ℤ) * (x : ℤ) ^ ι t := by
    intro μ hμ
    rw [Finsupp.weight_apply, Finsupp.sum]
    push_cast
    refine Finset.sum_subset (fun t ht ↦ hV ▸ Finset.mem_biUnion.mpr ⟨μ, hμ, ht⟩) fun t _ ht ↦ ?_
    rw [Finsupp.notMem_support_iff.mp ht]
    simp
  refine ⟨fun t ↦ x ^ ι t, fun μ hμ ν hν h ↦ ?_⟩
  by_contra hne
  have hdvd : P μ ν ∣ Q :=
    hQ ▸ Finset.dvd_prod_of_mem (fun p ↦ P p.1 p.2)
      (show ((μ, ν) : (σ →₀ ℕ) × (σ →₀ ℕ)) ∈ _ from
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hμ, hν⟩, hne⟩)
  refine hx (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd ?_)
  have hev : (P μ ν).eval (x : ℤ) = ∑ t ∈ V, ((μ t : ℤ) - (ν t : ℤ)) * (x : ℤ) ^ ι t := by
    rw [hP]
    simp [Polynomial.eval_finsetSum]
  rw [hev]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, ← hw μ hμ, ← hw ν hν, h, sub_self]

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] {n : ℕ}

/-- The **Kronecker substitution** `X s ↦ T ^ e s`, which turns several variables into one. -/
def kroneckerHom (e : σ → ℕ) : MvPolynomial σ R →ₐ[R] Polynomial R :=
  aeval fun s ↦ (Polynomial.X : Polynomial R) ^ e s

/-- The **translated Kronecker substitution** `X s ↦ (T + a) ^ e s - a ^ e s`. Each image has zero
constant term, which is what bounds the orders of differentiation that can appear. -/
def kroneckerShift (e : σ → ℕ) (a : R) : MvPolynomial σ R →ₐ[R] Polynomial R :=
  aeval fun s ↦ (Polynomial.X + Polynomial.C a) ^ e s - Polynomial.C (a ^ e s)

-- Not a `simp` lemma: `simp` proves it from `algHom_C` and `Polynomial.algebraMap_eq`.

/-- The **generalized Wronskian matrix** (Bombieri–Gubler, Proposition 6.3.10): the entry
`(i, j)` is the `μ i`-th Hasse derivative of `φ j`. -/
def genWronskianMatrix (μ : Fin n → (σ →₀ ℕ)) (φ : Fin n → MvPolynomial σ R) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ R) := .of fun i j ↦ hasseDeriv (μ i) (φ j)

/-- The **generalized Wronskian** of a family of polynomials at a family of orders. -/
def genWronskian (μ : Fin n → (σ →₀ ℕ)) (φ : Fin n → MvPolynomial σ R) : MvPolynomial σ R :=
  (genWronskianMatrix μ φ).det

/-- **The hard half.** A linearly independent family over a field of characteristic zero has a
nonzero generalized Wronskian of admissible orders: substitute `X s ↦ T ^ e s` for weights that
separate the exponents occurring, apply the one-variable criterion to the images, evaluate at a
point where that Wronskian survives, and expand each row in the several-variable Hasse derivatives
the chain rule produces — all of total order at most the row index. -/
theorem exists_genWronskian_ne_zero {K : Type*} [Field K] [CharZero K]
    {φ : Fin n → MvPolynomial σ K} (hφ : LinearIndependent K φ) :
    ∃ μ : Fin n → (σ →₀ ℕ), (∀ i, (μ i).degree ≤ (i : ℕ)) ∧ genWronskian μ φ ≠ 0 := by
  have coeff_kroneckerShift_monomial_eq_zero (e : σ → ℕ) (a : K) (ν : σ →₀ ℕ) {i : ℕ}
    (hi : i < ν.degree) : (MvPolynomial.kroneckerShift e a (MvPolynomial.monomial ν (1 : K))).coeff i = 0 := by
    refine Polynomial.X_pow_dvd_iff.mp ?_ i hi
    rw [MvPolynomial.kroneckerShift, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.degree_apply,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun s _ ↦ pow_dvd_pow_of_dvd ?_ _
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simp
  have kroneckerShift_taylorAt (e : σ → ℕ) (a : K) (f : MvPolynomial σ K) :
    MvPolynomial.kroneckerShift e a (MvPolynomial.taylorAt (fun s ↦ a ^ e s) f)
      = Polynomial.taylor a (MvPolynomial.kroneckerHom e f) := by
    have h : (MvPolynomial.kroneckerShift e a).comp (MvPolynomial.taylorAt fun s ↦ a ^ e s)
        = (Polynomial.aeval (Polynomial.X + Polynomial.C a)).comp (MvPolynomial.kroneckerHom (R := K) e) := by
      refine MvPolynomial.algHom_ext fun s ↦ ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, (fun α j ↦ (show MvPolynomial.taylorAt α (MvPolynomial.X j) = MvPolynomial.X j + MvPolynomial.C (α j) from MvPolynomial.aeval_X _ _)), map_add, (fun e a r ↦ (show MvPolynomial.kroneckerShift e a (MvPolynomial.C r) = Polynomial.C r from by
        rw [MvPolynomial.kroneckerShift, MvPolynomial.aeval_C, Polynomial.algebraMap_eq])),
        MvPolynomial.kroneckerShift, MvPolynomial.aeval_X, sub_add_cancel, (fun e s ↦ (show MvPolynomial.kroneckerHom e (MvPolynomial.X s) = Polynomial.X ^ e s from MvPolynomial.aeval_X _ _)), map_pow, Polynomial.aeval_X]
    rw [Polynomial.taylor_apply, Polynomial.comp_eq_aeval, ← AlgHom.comp_apply, h,
      AlgHom.comp_apply]
  have eval_hasseDeriv_kroneckerHom (e : σ → ℕ) (a : K) (f : MvPolynomial σ K)
    (s : Finset (σ →₀ ℕ)) (hs : (MvPolynomial.taylorAt (fun t ↦ a ^ e t) f).support ⊆ s) (i : ℕ) :
    Polynomial.eval a (Polynomial.hasseDeriv i (MvPolynomial.kroneckerHom e f))
      = ∑ ν ∈ s.filter fun ν ↦ ν.degree ≤ i,
          (MvPolynomial.kroneckerShift e a (MvPolynomial.monomial ν (1 : K))).coeff i
            * MvPolynomial.eval (fun t ↦ a ^ e t) (MvPolynomial.hasseDeriv ν f) := by
    classical
    rw [Finset.sum_filter_of_ne fun ν _ hne ↦ ?_]
    · rw [← Polynomial.taylor_coeff, ← kroneckerShift_taylorAt]
      conv_lhs => rw [show MvPolynomial.taylorAt (fun t ↦ a ^ e t) f
        = ∑ ν ∈ s, MvPolynomial.monomial ν ((MvPolynomial.taylorAt (fun t ↦ a ^ e t) f).coeff ν) from
          ((MvPolynomial.taylorAt (fun t ↦ a ^ e t) f).as_sum).trans
            (Finset.sum_subset hs fun ν _ hν ↦ by
              rw [notMem_support_iff.mp hν, MvPolynomial.monomial_zero])]
      rw [map_sum, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun ν _ ↦ ?_
      rw [← MvPolynomial.coeff_taylorAt, show (MvPolynomial.monomial ν ((MvPolynomial.taylorAt (fun t ↦ a ^ e t) f).coeff ν) :
          MvPolynomial σ K) = MvPolynomial.C ((MvPolynomial.taylorAt (fun t ↦ a ^ e t) f).coeff ν) * MvPolynomial.monomial ν 1 from by
        rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, (fun e a r ↦ (show MvPolynomial.kroneckerShift e a (MvPolynomial.C r) = Polynomial.C r from by
        rw [MvPolynomial.kroneckerShift, MvPolynomial.aeval_C, Polynomial.algebraMap_eq])), Polynomial.coeff_C_mul, mul_comm]
    · by_contra hdeg
      exact hne (by rw [coeff_kroneckerShift_monomial_eq_zero e a ν (by omega), zero_mul])
  have kroneckerHom_monomial (e : σ → ℕ) (μ : σ →₀ ℕ) (a : K) :
    MvPolynomial.kroneckerHom e (MvPolynomial.monomial μ a)
      = Polynomial.C a * Polynomial.X ^ Finsupp.weight e μ := by
    rw [MvPolynomial.kroneckerHom, MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod, Finsupp.weight_apply,
      Finsupp.sum]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun s _ ↦ by rw [← pow_mul, smul_eq_mul, mul_comm]
  have eq_zero_of_kroneckerHom_eq_zero {e : σ → ℕ} {T : Finset (σ →₀ ℕ)}
    (hT : ∀ μ ∈ T, ∀ ν ∈ T, Finsupp.weight e μ = Finsupp.weight e ν → μ = ν)
    {f : MvPolynomial σ K} (hf : f.support ⊆ T) (h : MvPolynomial.kroneckerHom e f = 0) : f = 0 := by
    classical
    by_contra h0
    obtain ⟨ν, hν⟩ := support_nonempty.mpr h0
    have hcoeff : (MvPolynomial.kroneckerHom e f).coeff (Finsupp.weight e ν) = f.coeff ν := by
      conv_lhs => rw [f.as_sum]
      rw [map_sum, Polynomial.finsetSum_coeff,
        Finset.sum_eq_single ν (fun μ hμ hne ↦ ?_) fun h ↦ absurd hν h]
      · rw [kroneckerHom_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp
      · have hw : Finsupp.weight e ν ≠ Finsupp.weight e μ := fun hw ↦
          hne (hT μ (hf hμ) ν (hf hν) hw.symm)
        rw [kroneckerHom_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp [hw]
    rw [h, Polynomial.coeff_zero] at hcoeff
    exact mem_support_iff.mp hν hcoeff.symm
  have linearIndependent_kroneckerHom {e : σ → ℕ} {T : Finset (σ →₀ ℕ)}
    (hT : ∀ μ ∈ T, ∀ ν ∈ T, Finsupp.weight e μ = Finsupp.weight e ν → μ = ν)
    {φ : Fin n → MvPolynomial σ K} (hsupp : ∀ j, (φ j).support ⊆ T)
    (hφ : LinearIndependent K φ) : LinearIndependent K fun j ↦ MvPolynomial.kroneckerHom e (φ j) := by
    classical
    rw [Fintype.linearIndependent_iff] at hφ ⊢
    intro c hc
    refine hφ c (eq_zero_of_kroneckerHom_eq_zero hT (fun μ hμ ↦ ?_) ?_)
    · by_contra hnot
      refine mem_support_iff.mp hμ ?_
      rw [MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul, notMem_support_iff.mp fun h ↦ hnot (hsupp j h), mul_zero]
    · rw [map_sum]
      simpa using hc
  classical
  obtain ⟨e, he⟩ := Finsupp.exists_weight_injOn (Finset.univ.biUnion fun j ↦ (φ j).support)
  have hsupp : ∀ j, (φ j).support ⊆ Finset.univ.biUnion fun j ↦ (φ j).support :=
    fun j μ hμ ↦ Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hμ⟩
  have hW := Polynomial.hasseWronskianDet_ne_zero (linearIndependent_kroneckerHom he hsupp hφ)
  obtain ⟨a, ha⟩ : ∃ a : K, Polynomial.eval a
      (Polynomial.hasseWronskianDet fun j ↦ kroneckerHom e (φ j)) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    refine hW (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    have huniv : {x : K | (Polynomial.hasseWronskianDet fun j ↦ kroneckerHom e (φ j)).IsRoot x}
        = Set.univ := Set.eq_univ_of_forall fun x ↦ hcon x
    rw [huniv]
    exact Set.infinite_univ
  obtain ⟨S, hS⟩ : ∃ S : Finset (σ →₀ ℕ),
      S = Finset.univ.biUnion fun j ↦ (taylorAt (fun t ↦ a ^ e t) (φ j)).support := ⟨_, rfl⟩
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Fin n → Finset (σ →₀ ℕ),
      Sf = fun (i : Fin n) ↦ S.filter fun ν ↦ ν.degree ≤ (i : ℕ) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → (σ →₀ ℕ) → K,
      lam = fun (i : Fin n) ν ↦ (kroneckerShift e a (monomial ν (1 : K))).coeff (i : ℕ) :=
    ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : (σ →₀ ℕ) → (Fin n → K),
      v = fun ν j ↦ eval (fun t ↦ a ^ e t) (hasseDeriv ν (φ j)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) K, A = (Polynomial.hasseWronskianMatrix
      fun j ↦ kroneckerHom e (φ j)).map (Polynomial.evalRingHom a) := ⟨_, rfl⟩
  have hAdet : A.det ≠ 0 := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ha
  have hrows : (fun i ↦ A i) = fun i ↦ ∑ ν ∈ Sf i, lam i ν • v ν := by
    funext i
    funext j
    rw [hA]
    simp only [Matrix.map_apply, Polynomial.hasseWronskianMatrix, Matrix.of_apply,
      Polynomial.coe_evalRingHom]
    rw [eval_hasseDeriv_kroneckerHom e a (φ j) S (hS ▸ fun ν hν ↦
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hν⟩) (i : ℕ)]
    rw [hSf, hlam, hv, Finset.sum_apply]
    rfl
  have hexp : A.det = ∑ p ∈ Fintype.piFinset Sf,
      (∏ i, lam i (p i)) * (Matrix.of fun i j ↦ v (p i) j).det := by
    calc A.det
        = Matrix.detRowAlternating.toMultilinearMap (fun i ↦ ∑ ν ∈ Sf i, lam i ν • v ν) := by
          rw [← hrows]; rfl
      _ = ∑ p ∈ Fintype.piFinset Sf,
            Matrix.detRowAlternating.toMultilinearMap (fun i ↦ lam i (p i) • v (p i)) :=
          MultilinearMap.map_sum_finset _ _ _
      _ = _ := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [MultilinearMap.map_smul_univ]
          rfl
  rw [hexp] at hAdet
  obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hAdet
  refine ⟨p, fun i ↦ ?_, fun hz ↦ right_ne_zero_of_mul hpne ?_⟩
  · rw [hSf] at hp
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hp i)).2
  · have hmat : (Matrix.of fun i j ↦ v (p i) j)
        = (genWronskianMatrix p φ).map (eval fun t ↦ a ^ e t) := by
      refine Matrix.ext fun i j ↦ ?_
      rw [hv]
      rfl
    rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← genWronskian, hz, map_zero]

end MvPolynomial

end

end
