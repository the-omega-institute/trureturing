/- GID: D5/S3/VertexAlgebra/LatticeGeneratingFieldProducts
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeGeneratingFieldProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual ordered lattice fields share a recipient-finite pair kernel. -/

/-
proof_shape: actual_lattice_field_products: content
admission_basis: escape-witness
escape_witness: Polynomial translation of the composed actual modes is
identified with the two-variable translated polynomial; finite coefficient
contraction gives both orders against the same common kernel.
Classical source: Bakalov--Kac, arXiv math/0402315v1, section 4.1,
printed pages 8--9, equations (4.12) and (4.14).
-/
import D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
import Mathlib.Algebra.BigOperators.Finprod

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeGeneratingFieldProducts

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open MvPolynomial
open scoped BigOperators

noncomputable section

/-- The integer binomial contraction coefficients of the actual fields. -/
def contractionCoeff (b : ℤ) (j : ℕ) : ℂ :=
  PowerSeries.coeff j (PowerSeries.rescale (-1 : ℂ)
    (PowerSeries.binomialSeries (R := ℤ) ℂ b))

attribute [-instance] PowerSeries.algebraPolynomial in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 250000 in
-- The proof combines nested polynomial maps with recipientwise finite coefficient sums.
theorem actual_lattice_field_products (D : LatticeData) :
    ∀ (α β : Charge D) (k l : ℤ) (v : Carrier D),
      Function.HasFiniteSupport (fun j : ℕ => contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) v) ∧
      Function.HasFiniteSupport (fun j : ℕ => contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-j) (l-bilinear D α β+j) v) ∧
      rawCoeff D α k (rawCoeff D β l v) = epsilon D α β •
        (∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
          commonKernel D α β (k-bilinear D α β+j) (l-j) v) ∧
      rawCoeff D β l (rawCoeff D α k v) = epsilon D β α •
        (∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
          commonKernel D α β (k-j) (l-bilinear D α β+j) v) := by
  classical
  let A (γ : Charge D) (n : ℤ) : Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
    (Finsupp.lsum (Oscillator D) (fun d : ℕ =>
      LinearMap.mulRight (Oscillator D) (creationCoeff D γ (n + d)))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear (Oscillator D)).toLinearMap)
  have hA (γ : Charge D) (n : ℤ) (q : Polynomial (Oscillator D)) :
      A γ n q = ∑ d ∈ q.support, q.coeff d * creationCoeff D γ (n + d) := by
    rfl
  have hAm (γ : Charge D) (n : ℤ) (a : Oscillator D) (r : ℕ) :
      A γ n (Polynomial.C a * Polynomial.X ^ r) = a * creationCoeff D γ (n+r) := by
    simp [A, Polynomial.C_mul_X_pow_eq_monomial]
  let T (γ : Charge D) : Oscillator D →+* Polynomial (Oscillator D) :=
    MvPolynomial.eval₂Hom
      ((Polynomial.C : Oscillator D →+* Polynomial (Oscillator D)).comp (algebraMap ℂ _))
      (fun i : Index D => translationVariable D γ i.1 i.2)
  have hT (γ : Charge D) (p : Oscillator D) : T γ p = translatedPolynomial D γ p := rfl
  have hTC (γ : Charge D) (c : ℂ) :
      T γ (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) = _
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  have hTX (γ : Charge D) (i : Index D) :
      T γ (MvPolynomial.X i) = translationVariable D γ i.1 i.2 := by
    exact MvPolynomial.eval₂Hom_X' _ _ i
  let E (α γ : Charge D) (n : ℤ) :
      Polynomial (Polynomial (Oscillator D)) →ₗ[Polynomial (Oscillator D)]
        Polynomial (Oscillator D) :=
    (Finsupp.lsum (Polynomial (Oscillator D)) (fun d : ℕ =>
      LinearMap.mulRight (Polynomial (Oscillator D)) (T α (creationCoeff D γ (n+d))))).comp
      ((AddMonoidAlgebra.coeffLinearEquiv (Polynomial (Oscillator D))).toLinearMap.comp
        (Polynomial.toFinsuppIsoLinear (Polynomial (Oscillator D))).toLinearMap)
  have hEm (α γ : Charge D) (n : ℤ) (a : Polynomial (Oscillator D)) (r : ℕ) :
      E α γ n (Polynomial.C a * Polynomial.X ^ r) = a * T α (creationCoeff D γ (n+r)) := by
    simp [E, Polynomial.C_mul_X_pow_eq_monomial]
  have hTE (α β : Charge D) (n : ℤ) (q : Polynomial (Oscillator D)) :
      T α (A β n q) = E α β n (q.map (T α)) := by
    conv_rhs => rw [q.as_sum_support_C_mul_X_pow]
    rw [hA, map_sum]
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, map_sum, hEm, map_mul]
  let Φ : PairPolynomial D →+* Polynomial (Polynomial (Oscillator D)) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
      (fun i : Fin 2 => if i = 0 then Polynomial.C Polynomial.X else Polynomial.X)
  have hΦC (a : Oscillator D) : Φ (MvPolynomial.C a) =
      Polynomial.C (Polynomial.C a) := by
    exact MvPolynomial.eval₂Hom_C _ _ a
  have hΦX (i : Fin 2) : Φ (MvPolynomial.X i) =
      if i = 0 then Polynomial.C Polynomial.X else Polynomial.X := by
    exact MvPolynomial.eval₂Hom_X' _ _ i
  have hΦm (e : Fin 2 →₀ ℕ) (a : Oscillator D) :
      Φ (MvPolynomial.monomial e a) =
        Polynomial.C (Polynomial.C a * Polynomial.X ^ (e 0)) * Polynomial.X ^ (e 1) := by
    simp only [Φ, MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    change Polynomial.C (Polynomial.C a) *
      ((Polynomial.C Polynomial.X) ^ (e 0) * Polynomial.X ^ (e 1)) = _
    rw [← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul]
  have hpair (α β : Charge D) (p : Oscillator D) :
      (T β p).map (T α) = Φ (translatedPairPolynomial D α β p) := by
    let Q : Oscillator D →+* PairPolynomial D := MvPolynomial.eval₂Hom
      ((MvPolynomial.C : Oscillator D →+* PairPolynomial D).comp (algebraMap ℂ _))
      (fun i : Index D =>
        MvPolynomial.C (X i : Oscillator D) -
          MvPolynomial.C ((bilinear D α (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
            MvPolynomial.X 0 ^ (i.2+1) -
          MvPolynomial.C ((bilinear D β (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
            MvPolynomial.X 1 ^ (i.2+1))
    have hh : (Polynomial.mapRingHom (T α)).comp (T β) = Φ.comp Q := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change (T β (MvPolynomial.C c)).map (T α) = Φ (Q (MvPolynomial.C c))
        simp only [hTC, Polynomial.map_C, Q, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, MvPolynomial.algebraMap_eq, hΦC]
      · intro i
        change (T β (MvPolynomial.X i)).map (T α) = Φ (Q (MvPolynomial.X i))
        rw [hTX]
        simp only [translationVariable, Polynomial.map_sub, Polynomial.map_mul,
          Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Q,
          MvPolynomial.eval₂Hom_X', map_sub, map_mul, map_pow, hΦC, hΦX,
          ← MvPolynomial.C_eq_smul_one, hTC, hTX, ↓reduceIte]
        rfl
    exact congrArg (fun f : Oscillator D →+* Polynomial (Polynomial (Oscillator D)) => f p) hh
  have hAshift (γ : Charge D) (n : ℤ) (a : Oscillator D) (r : ℕ)
      (q : Polynomial (Oscillator D)) :
      A γ n (Polynomial.C a * Polynomial.X ^ r * q) =
        ∑ d ∈ q.support, a * q.coeff d * creationCoeff D γ (n + r + d) := by
    conv_lhs => rw [q.as_sum_support_C_mul_X_pow]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [show Polynomial.C a * Polynomial.X ^ r *
        (Polynomial.C (q.coeff d) * Polynomial.X ^ d) =
        Polynomial.C (a * q.coeff d) * Polynomial.X ^ (r+d) by
      rw [Polynomial.C_mul, pow_add]; ring, hAm]
    congr 2
    omega
  have hfinite (α β : Charge D) (n t : ℤ) (a : Oscillator D) (r : ℕ) :
      Function.HasFiniteSupport (fun j : ℕ => a *
        (contractionCoeff (bilinear D α β) j • creationCoeff D β (t-j)) *
          creationCoeff D α (n+r+j)) := by
    apply (Finset.finite_toSet (Finset.range (t.toNat+1))).subset
    intro j hj
    have hj' := Function.mem_support.mp hj
    have ht : ¬ t - j < 0 := by
      intro ht
      simp only [creationCoeff, dif_pos ht, smul_zero, mul_zero, zero_mul] at hj'
      exact hj' rfl
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hcontraction (α β : Charge D) (n t : ℤ) (a : Oscillator D) (r : ℕ) :
      A α n (Polynomial.C a * Polynomial.X ^ r * T α (creationCoeff D β t)) =
        ∑ᶠ j : ℕ, a *
          (contractionCoeff (bilinear D α β) j • creationCoeff D β (t-j)) *
            creationCoeff D α (n+r+j) := by
    have hf := hfinite α β n t a r
    have hc (j : ℕ) : (T α (creationCoeff D β t)).coeff j =
        contractionCoeff (bilinear D α β) j • creationCoeff D β (t-j) := by
      exact (actual_creation_coefficient_transport D α β).2.1 t j
    rw [hAshift]
    symm
    calc
      _ = ∑ j ∈ (T α (creationCoeff D β t)).support,
          a * (contractionCoeff (bilinear D α β) j • creationCoeff D β (t-j)) *
            creationCoeff D α (n+r+j) := by
        apply finsum_eq_sum_of_support_subset
        intro j hj
        by_contra hmem
        have hz := Polynomial.notMem_support_iff.mp hmem
        have hj' := Function.mem_support.mp hj
        rw [← hc j, hz, mul_zero, zero_mul] at hj'
        exact hj' rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc j]
  have hpairExpansion (α β : Charge D) (l : ℤ) (p : Oscillator D) :
      T α (A β l (T β p)) =
        ∑ e ∈ (translatedPairPolynomial D α β p).support,
          Polynomial.C ((translatedPairPolynomial D α β p).coeff e) *
            Polynomial.X ^ (e 0) * T α (creationCoeff D β (l+e 1)) := by
    rw [hTE, hpair]
    conv_lhs => rw [(translatedPairPolynomial D α β p).as_sum]
    simp only [map_sum, hΦm, hEm]
  have hpairAction (α β : Charge D) (k l : ℤ) (p : Oscillator D) :
      A α k (T α (A β l (T β p))) =
        ∑ᶠ j : ℕ, ∑ e ∈ (translatedPairPolynomial D α β p).support,
          (translatedPairPolynomial D α β p).coeff e *
            (contractionCoeff (bilinear D α β) j • creationCoeff D β (l+e 1-j)) *
              creationCoeff D α (k+e 0+j) := by
    have hf (e : Fin 2 →₀ ℕ) :=
      hfinite α β k (l+e 1) ((translatedPairPolynomial D α β p).coeff e) (e 0)
    rw [hpairExpansion, map_sum]
    simp only [hcontraction]
    exact sum_finsum_comm _ _ (fun e he => hf e)
  have hBadd (α β δ : Charge D) : bilinear D α (β+δ) = bilinear D α β + bilinear D α δ := by
    simp only [bilinear, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hExpLeft (α β δ : Charge D) :
      lowerCocycleExponent D (α+β) δ =
        lowerCocycleExponent D α δ + lowerCocycleExponent D β δ := by
    simp only [lowerCocycleExponent, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring
  have hExpRight (α β δ : Charge D) :
      lowerCocycleExponent D α (β+δ) =
        lowerCocycleExponent D α β + lowerCocycleExponent D α δ := by
    simp only [lowerCocycleExponent, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hSign (m n : ℤ) : paritySign (m+n) = paritySign m * paritySign n := by
    simp only [paritySign, ← neg_one_zpow_eq_ite]
    exact zpow_add₀ (by norm_num) _ _
  have hEps (α β δ : Charge D) :
      epsilon D β δ * epsilon D α (β+δ) =
        epsilon D α β * epsilon D (α+β) δ := by
    simp only [epsilon, hExpRight, hExpLeft, hSign]
    ring
  have hraw (α : Charge D) (k : ℤ) (δ : Charge D) (p : Oscillator D) :
      rawCoeff D α k (Finsupp.single δ p) =
        epsilon D α δ • Finsupp.single (α+δ)
          (A α (k-bilinear D α δ) (T α p)) := by
    rw [(actual_creation_coefficient_transport D α α).2.2.1]
    rfl
  have hkernel (α β : Charge D) (u v : ℤ) (δ : Charge D) (p : Oscillator D) :
      commonKernel D α β u v (Finsupp.single δ p) =
        epsilon D (α+β) δ • Finsupp.single (α+β+δ)
          (∑ e ∈ (translatedPairPolynomial D α β p).support,
            (translatedPairPolynomial D α β p).coeff e *
              creationCoeff D α (u-bilinear D α δ+e 0) *
              creationCoeff D β (v-bilinear D β δ+e 1)) := by
    exact (actual_creation_coefficient_transport D α β).2.2.2 u v δ p
  have hkernelBoundSingle (α β : Charge D) (k l : ℤ) (δ : Charge D)
      (p : Oscillator D) (j : ℕ)
      (hj : l-bilinear D β δ+
        (translatedPairPolynomial D α β p).support.sup (fun e => e 1) < j) :
      commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p) = 0 := by
    rw [hkernel]
    have hsum : (∑ e ∈ (translatedPairPolynomial D α β p).support,
        (translatedPairPolynomial D α β p).coeff e *
          creationCoeff D α (k-bilinear D α β+j-bilinear D α δ+e 0) *
          creationCoeff D β (l-j-bilinear D β δ+e 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have he' := Finset.le_sup (f := fun e : Fin 2 →₀ ℕ => e 1) he
      rw [show creationCoeff D β (l-j-bilinear D β δ+e 1) = 0 by
        rw [creationCoeff, dif_pos (by omega)], mul_zero]
    rw [hsum, Finsupp.single_zero, smul_zero]
  have hkernelFiniteSingle (α β : Charge D) (k l : ℤ) (δ : Charge D) (p : Oscillator D) :
      Function.HasFiniteSupport (fun j : ℕ => contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)) := by
    apply (Finset.finite_toSet (Finset.range
      ((l-bilinear D β δ+
        (translatedPairPolynomial D α β p).support.sup (fun e => e 1)).toNat+1))).subset
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hbound
    exact (Function.mem_support.mp hj)
      (by rw [hkernelBoundSingle α β k l δ p j (by omega), smul_zero])
  have hsingleForward (α β : Charge D) (k l : ℤ) (δ : Charge D) (p : Oscillator D) :
      rawCoeff D α k (rawCoeff D β l (Finsupp.single δ p)) =
        epsilon D α β • (∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
          commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p)) := by
    let q := translatedPairPolynomial D α β p
    let n := k - bilinear D α β - bilinear D α δ
    let m := l - bilinear D β δ
    let f (j : ℕ) : Oscillator D := ∑ e ∈ q.support,
      q.coeff e * (contractionCoeff (bilinear D α β) j • creationCoeff D β (m+e 1-j)) *
        creationCoeff D α (n+e 0+j)
    have hf : Function.HasFiniteSupport f :=
      Function.HasFiniteSupport.sum (fun e => hfinite α β n (m+e 1) (q.coeff e) (e 0)) q.support
    let S : Oscillator D →ₗ[ℂ] Carrier D :=
      epsilon D (α+β) δ • Finsupp.lsingle (α+β+δ)
    have hpoint (j : ℕ) : S (f j) = contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p) := by
      have hpoly : f j = contractionCoeff (bilinear D α β) j •
          (∑ e ∈ q.support, q.coeff e *
            creationCoeff D α (k-bilinear D α β+j-bilinear D α δ+e 0) *
            creationCoeff D β (l-j-bilinear D β δ+e 1)) := by
        dsimp only [f]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro e he
        dsimp only [n, m]
        rw [show l-bilinear D β δ+e 1-j = l-j-bilinear D β δ+e 1 by omega,
          show k-bilinear D α β-bilinear D α δ+e 0+j =
            k-bilinear D α β+j-bilinear D α δ+e 0 by omega]
        simp only [Algebra.smul_def]
        ring
      rw [hkernel]
      change epsilon D (α+β) δ • Finsupp.single (α+β+δ) (f j) =
        contractionCoeff (bilinear D α β) j •
          (epsilon D (α+β) δ • Finsupp.single (α+β+δ)
            (∑ e ∈ q.support, q.coeff e *
              creationCoeff D α (k-bilinear D α β+j-bilinear D α δ+e 0) *
              creationCoeff D β (l-j-bilinear D β δ+e 1)))
      rw [hpoly]
      simp only [Finsupp.smul_single, smul_smul, mul_comm]
    have hsum : S (∑ᶠ j, f j) = ∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ p) := by
      rw [map_finsum S hf]
      exact finsum_congr hpoint
    rw [hraw, map_smul, hraw, hBadd]
    rw [show k-(bilinear D α β+bilinear D α δ) = n by dsimp [n]; omega,
      hpairAction]
    change epsilon D β δ • (epsilon D α (β+δ) •
      Finsupp.single (α+(β+δ)) (∑ᶠ j, f j)) = _
    rw [smul_smul, hEps, mul_smul, ← add_assoc]
    exact congrArg (fun x : Carrier D => epsilon D α β • x) hsum
  have hBsym (α β : Charge D) : bilinear D α β = bilinear D β α := by
    unfold bilinear
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [D.symmetric j i]
    ring
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  have hswap0 : swap 0 = 1 := by simp [swap]
  have hswap1 : swap 1 = 0 := by simp [swap]
  have hpairSwap (α β : Charge D) (p : Oscillator D) :
      translatedPairPolynomial D β α p =
        MvPolynomial.rename swap (translatedPairPolynomial D α β p) := by
    let Q (γ η : Charge D) : Oscillator D →+* PairPolynomial D :=
      MvPolynomial.eval₂Hom
        ((MvPolynomial.C : Oscillator D →+* PairPolynomial D).comp (algebraMap ℂ _))
        (fun i : Index D =>
          MvPolynomial.C (X i : Oscillator D) -
            MvPolynomial.C ((bilinear D γ (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
              MvPolynomial.X 0 ^ (i.2+1) -
            MvPolynomial.C ((bilinear D η (unitCharge D i.1) : ℂ) • (1 : Oscillator D)) *
              MvPolynomial.X 1 ^ (i.2+1))
    let ρ : PairPolynomial D →+* PairPolynomial D := (MvPolynomial.rename swap).toRingHom
    have hρC (a : Oscillator D) : ρ (MvPolynomial.C a) = MvPolynomial.C a := by
      change MvPolynomial.rename swap (MvPolynomial.C a) = MvPolynomial.C a
      exact MvPolynomial.rename_C swap a
    have hρX (i : Fin 2) : ρ (MvPolynomial.X i) = MvPolynomial.X (swap i) := by
      change MvPolynomial.rename swap (MvPolynomial.X i) = MvPolynomial.X (swap i)
      exact MvPolynomial.rename_X swap i
    have hh : Q β α = ρ.comp (Q α β) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [Q, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hρC]
      · intro i
        simp only [Q, RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
          map_sub, map_mul, map_pow, hρC, hρX, hswap0, hswap1]
        ring
    exact congrArg (fun f : Oscillator D →+* PairPolynomial D => f p) hh
  have hkernelSymSingle (α β : Charge D) (u v : ℤ) (δ : Charge D) (p : Oscillator D) :
      commonKernel D β α v u (Finsupp.single δ p) =
        commonKernel D α β u v (Finsupp.single δ p) := by
    rw [hkernel, hkernel, hpairSwap,
      MvPolynomial.support_rename_of_injective swap.injective]
    simp only [add_comm β α]
    congr 2
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e he
      rw [MvPolynomial.coeff_rename_mapDomain swap swap.injective]
      have h0 : (e.mapDomain swap) 0 = e 1 := by
        rw [← hswap1, Finsupp.mapDomain_apply swap.injective]
      have h1 : (e.mapDomain swap) 1 = e 0 := by
        rw [← hswap0, Finsupp.mapDomain_apply swap.injective]
      rw [h0, h1]
      ring
    · exact (Finsupp.mapDomain_injective swap.injective).injOn
  have hkernelFinite (α β : Charge D) (k l : ℤ) (v : Carrier D) :
      Function.HasFiniteSupport (fun j : ℕ => contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) v) := by
    have heq (j : ℕ) : contractionCoeff (bilinear D α β) j •
        commonKernel D α β (k-bilinear D α β+j) (l-j) v =
        ∑ δ ∈ v.support, contractionCoeff (bilinear D α β) j •
          commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ (v δ)) := by
      conv_lhs => rw [← Finsupp.sum_single v]
      simp only [Finsupp.sum, map_sum, Finset.smul_sum]
    simp_rw [heq]
    exact Function.HasFiniteSupport.sum
      (fun δ => hkernelFiniteSingle α β k l δ (v δ)) v.support
  have hforward (α β : Charge D) (k l : ℤ) (v : Carrier D) :
      rawCoeff D α k (rawCoeff D β l v) = epsilon D α β •
        (∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
          commonKernel D α β (k-bilinear D α β+j) (l-j) v) := by
    have hf (δ : Charge D) := hkernelFiniteSingle α β k l δ (v δ)
    calc
      _ = ∑ δ ∈ v.support, rawCoeff D α k
          (rawCoeff D β l (Finsupp.single δ (v δ))) := by
        conv_lhs => rw [← Finsupp.sum_single v]
        simp only [Finsupp.sum, map_sum]
      _ = epsilon D α β • ∑ δ ∈ v.support,
          (∑ᶠ j : ℕ, contractionCoeff (bilinear D α β) j •
            commonKernel D α β (k-bilinear D α β+j) (l-j) (Finsupp.single δ (v δ))) := by
        simp only [hsingleForward, Finset.smul_sum]
      _ = _ := by
        rw [sum_finsum_comm _ _ (fun δ hδ => hf δ)]
        congr 1
        apply finsum_congr
        intro j
        rw [← Finset.smul_sum, ← map_sum]
        congr 2
        exact Finsupp.sum_single v
  have hkernelSym (α β : Charge D) (u v : ℤ) (w : Carrier D) :
      commonKernel D β α v u w = commonKernel D α β u v w := by
    conv_lhs => rw [← Finsupp.sum_single w]
    conv_rhs => rw [← Finsupp.sum_single w]
    simp only [Finsupp.sum, map_sum, hkernelSymSingle]
  intro α β k l v
  refine ⟨hkernelFinite α β k l v, ?_, hforward α β k l v, ?_⟩
  · simpa only [hBsym β α, hkernelSym α β] using hkernelFinite β α l k v
  · simpa only [hBsym β α, hkernelSym α β] using hforward β α l k v

end
end D5.S3.VertexAlgebra.LatticeGeneratingFieldProducts
