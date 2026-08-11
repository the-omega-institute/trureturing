/- GID: D5/S3/ObserverMemory/PrimePowerTensorTower
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PrimePowerTensorTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose a finite window matrix algebra into all prime-power tensor factors. -/

/- Library-search audit trail (2026-08-11):
   * `ZMod.equivPi` supplies the canonical ring equivalence from `ZMod M` to
     the family of its prime-power residue rings.
   * `Matrix.kroneckerAlgEquiv` supplies the binary full-matrix algebra step,
     while `Basis.piTensorProduct` supplies its finite-family basis extension.
   * The frozen binary clock-and-shift specialization
     (`WindowRegisterCRT.window_register_crt_decomposition`) does not expose
     the full matrix-algebra equivalence needed here, so this module carries
     no D5 dependency: the construction is mathlib-only.
   * No theorem combining these APIs into the finite prime-power matrix tensor
     factorization was found in the repository or the pinned Mathlib tree.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.PiTensorProduct

namespace D5.S3.ObserverMemory.PrimePowerTensorTower

open scoped TensorProduct

noncomputable section

/-- The full complex matrix algebra on one prime-power address factor. -/
abbrev PrimePowerFactor (M : Nat) (p : M.primeFactors) :=
  Matrix (ZMod (p.1 ^ M.factorization p.1))
    (ZMod (p.1 ^ M.factorization p.1)) Complex

private instance primePowerNeZero (M : Nat) (p : M.primeFactors) :
    NeZero (p.1 ^ M.factorization p.1) :=
  ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- The finite tensor product of all prime-power full-matrix factors of `M`. -/
abbrev PrimePowerTensor (M : Nat) :=
  ⨂[Complex] p : M.primeFactors, PrimePowerFactor M p

/-- The basis-level finite-family Kronecker equivalence. -/
noncomputable def piKroneckerLinearEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → Type*)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (⨂[Complex] i, Matrix (n i) (n i) Complex) ≃ₗ[Complex]
      Matrix (∀ i, n i) (∀ i, n i) Complex :=
  (Basis.piTensorProduct
      (fun i => Matrix.stdBasis Complex (n i) (n i))).equiv
    (Matrix.stdBasis Complex (∀ i, n i) (∀ i, n i))
    (Equiv.arrowProdEquivProdArrow ι n n)

@[simp]
theorem pi_kronecker_linear_equiv_tprod_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → Type*)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (r s : ∀ i, n i) :
    piKroneckerLinearEquiv n
        (PiTensorProduct.tprod Complex
          (fun i => Matrix.single (r i) (s i) (1 : Complex))) =
      Matrix.single r s 1 := by
  let sourceBasis :=
    Basis.piTensorProduct
      (fun i => Matrix.stdBasis Complex (n i) (n i))
  let targetBasis := Matrix.stdBasis Complex (∀ i, n i) (∀ i, n i)
  have hsource :
      PiTensorProduct.tprod Complex
          (fun i => Matrix.single (r i) (s i) (1 : Complex)) =
        sourceBasis (fun i => (r i, s i)) := by
    rw [Basis.piTensorProduct_apply]
    congr 1
    funext i
    exact (Matrix.stdBasis_eq_single (R := Complex) (r i) (s i)).symm
  rw [hsource]
  change
    sourceBasis.equiv targetBasis (Equiv.arrowProdEquivProdArrow ι n n)
        (sourceBasis (fun i => (r i, s i))) = _
  rw [sourceBasis.equiv_apply]
  exact Matrix.stdBasis_eq_single (R := Complex) r s

/-- The finite-family Kronecker equivalence as a complex algebra equivalence. -/
noncomputable def piKroneckerAlgEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → Type*)
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (⨂[Complex] i, Matrix (n i) (n i) Complex) ≃ₐ[Complex]
      Matrix (∀ i, n i) (∀ i, n i) Complex := by
  let sourceBasis :=
    Basis.piTensorProduct
      (fun i => Matrix.stdBasis Complex (n i) (n i))
  let f := piKroneckerLinearEquiv n
  have hmul : ∀ x y, f (x * y) = f x * f y := by
    suffices hbilin :
        PiTensorProduct.mul.compr₂ₛₗ f.toLinearMap =
          (LinearMap.mul Complex
            (Matrix (∀ i, n i) (∀ i, n i) Complex)).compl₁₂
              f.toLinearMap f.toLinearMap by
      intro x y
      exact DFunLike.congr_fun (DFunLike.congr_fun hbilin x) y
    apply (LinearMap.ext_iff_basis sourceBasis sourceBasis).2
    intro a b
    rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_apply]
    simp only [LinearMap.compr₂ₛₗ_apply, LinearMap.compl₁₂_apply,
      LinearMap.mul_apply']
    rw [PiTensorProduct.mul_tprod_tprod]
    have ha :
        (fun i => (Matrix.stdBasis Complex (n i) (n i)) (a i)) =
          fun i => Matrix.single (a i).1 (a i).2 (1 : Complex) := by
      funext i
      exact Matrix.stdBasis_eq_single (R := Complex) (a i).1 (a i).2
    have hb :
        (fun i => (Matrix.stdBasis Complex (n i) (n i)) (b i)) =
          fun i => Matrix.single (b i).1 (b i).2 (1 : Complex) := by
      funext i
      exact Matrix.stdBasis_eq_single (R := Complex) (b i).1 (b i).2
    rw [ha, hb]
    by_cases h : (fun i => (a i).2) = fun i => (b i).1
    · have hpoint : ∀ i, (a i).2 = (b i).1 := fun i => congrFun h i
      simp_rw [hpoint]
      have hc :
          ((fun i => Matrix.single (a i).1 (b i).1 (1 : Complex)) *
              fun i => Matrix.single (b i).1 (b i).2 (1 : Complex)) =
            fun i => Matrix.single (a i).1 (b i).2 (1 : Complex) := by
        funext i
        change
          Matrix.single (a i).1 (b i).1 (1 : Complex) *
              Matrix.single (b i).1 (b i).2 (1 : Complex) =
            Matrix.single (a i).1 (b i).2 (1 : Complex)
        simp
      rw [hc]
      simp [f]
    · have hi : ∃ i, (a i).2 ≠ (b i).1 := by
        simpa only [Function.ne_iff] using h
      obtain ⟨i, hi⟩ := hi
      have hzero :
          (fun j =>
            Matrix.single (a j).1 (a j).2 (1 : Complex) *
              Matrix.single (b j).1 (b j).2 (1 : Complex)) i = 0 := by
        exact Matrix.single_mul_single_of_ne (1 : Complex)
          (a i).1 (a i).2 (b i).1 hi 1
      rw [(PiTensorProduct.tprod Complex).map_coord_zero i hzero]
      simp [f, h]
  refine AlgEquiv.ofLinearEquiv f ?_ hmul
  obtain ⟨x, hx⟩ :=
    f.surjective (1 : Matrix (∀ i, n i) (∀ i, n i) Complex)
  calc
    f 1 = 1 * f 1 := (one_mul _).symm
    _ = f x * f 1 := by rw [hx]
    _ = f (x * 1) := (hmul x 1).symm
    _ = f x := by rw [mul_one]
    _ = 1 := hx

/-- The canonical complex algebra equivalence obtained by first applying
`ZMod.equivPi`, then the inverse finite-family Kronecker equivalence. -/
noncomputable def primePowerTensorFactorization (M : Nat) [NeZero M] :
    Matrix (ZMod M) (ZMod M) Complex ≃ₐ[Complex] PrimePowerTensor M :=
  (Matrix.reindexAlgEquiv Complex Complex
      (ZMod.equivPi M (NeZero.ne M)).toEquiv).trans
    (piKroneckerAlgEquiv
      (fun p : M.primeFactors =>
        ZMod (p.1 ^ M.factorization p.1))).symm

/-- Every nonzero finite window full-matrix algebra is canonically equivalent
to the finite tensor product of all of its prime-power full-matrix factors. -/
theorem prime_power_tensor_factor_decomposition (M : Nat) [NeZero M] :
    Function.Bijective (primePowerTensorFactorization M) :=
  (primePowerTensorFactorization M).bijective

end

end D5.S3.ObserverMemory.PrimePowerTensorTower
