/- GID: D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour
   generality: I
   mirror-B: D5/B/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.claim; result=D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result; claim=D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.claim
   digest: The printed prime-power twisted-derivation criterion on actual cyclotomic integer rings. -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The printed criterion is encoded on the actual ring of integers. -/

namespace D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFourFour

noncomputable section

open NumberField Matrix

/-- Integral innerness, with the generator required to belong to the actual integer ring. -/
def IsInner {O : Type*} [CommRing O] (σ τ : O →ₐ[ℤ] O) (D : O →ₗ[ℤ] O) : Prop :=
  ∃ γ : O, ∀ x : O, D x = γ * τ x - σ x * γ

/-- The printed denominator is `p^e`, without replacing it by the determinant. -/
def PrintedIntegralTest {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p e : ℕ) (A : Matrix ι ι ℤ) (C : ι → ℤ) : Prop :=
  ∃ X : ι → ℤ, ∀ i,
    ((p : ℚ) ^ e)⁻¹ *
      ((A.adjugate.map (Int.castRingHom ℚ)) *ᵥ (fun j => (C j : ℚ))) i = (X i : ℚ)

/-- Conjecture 4.4, including both additional sufficient assertions.
The matrix is the actual multiplication operator; no integral solution of `D z` is assumed. -/
def claim : Prop :=
  ∀ (p k : ℕ), p.Prime → k ≠ 1 → 3 ≤ p ^ k →
  ∀ (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K]
    [NeZero (p ^ k)] (ζ : K) (hζ : IsPrimitiveRoot ζ (p ^ k)),
  let z := hζ.toInteger
  ∀ (pb : PowerBasis ℤ (RingOfIntegers K)),
    pb.gen = z → pb.dim = p ^ (k - 1) * (p - 1) →
  ∀ (σ τ : RingOfIntegers K →ₐ[ℤ] RingOfIntegers K), σ ≠ τ →
  ∀ (u v e m : ℕ),
    u < p ^ k → v < p ^ k → Nat.Coprime u (p ^ k) → Nat.Coprime v (p ^ k) →
    u ≠ v → σ z = z ^ u → τ z = z ^ v → 0 < m → ¬ p ∣ m →
    v = u + p ^ e * m →
  ∀ (D : RingOfIntegers K →ₗ[ℤ] RingOfIntegers K),
    (∀ x y, D (x * y) = D x * τ y + σ x * D y) →
  let A := Algebra.leftMulMatrix pb.basis (τ z - σ z)
  let C := fun i => pb.basis.repr (D z) i
  (IsInner σ τ D ↔ PrintedIntegralTest p e A C) ∧
    ((∀ i, (p : ℤ) ^ e ∣ C i) → IsInner σ τ D) ∧
    ((∀ i, (p : ℤ) ∣ C i) → IsInner σ τ D)

abbrev K4 := CyclotomicField 4 ℚ
private instance : IsCyclotomicExtension {4} ℚ K4 :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

abbrev O4 := RingOfIntegers K4

def root : K4 := IsCyclotomicExtension.zeta 4 ℚ K4
private theorem root_primitive : IsPrimitiveRoot root 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℚ K4

def z : O4 := root_primitive.toInteger

def pb : PowerBasis ℤ O4 := root_primitive.integralPowerBasis

private theorem z_sq : z * z = (-1 : O4) := by
  have h := root_primitive.toInteger_isPrimitiveRoot.pow_div_gcd 2 (by decide)
  have h2 : IsPrimitiveRoot (z ^ 2) 2 := by simpa [z] using h
  simpa [pow_two] using h2.eq_neg_one_of_two_right

private theorem pb_dim : pb.dim = 2 := by
  change root_primitive.integralPowerBasis.dim = 2
  rw [IsPrimitiveRoot.integralPowerBasis_dim]
  decide

private def b : Module.Basis (Fin 2) ℤ O4 := pb.basis.reindex (finCongr pb_dim)

private theorem b_apply (i : Fin 2) : b i = z ^ (i : ℕ) := by
  rw [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hg : pb.gen = z := root_primitive.integralPowerBasis_gen
  rw [hg]
  rfl

private def lift : GaussianInt →+* O4 := Zsqrtd.lift ⟨z, by simpa using z_sq⟩

private theorem lift_apply (a c : ℤ) : lift ⟨a,c⟩ = (a : O4) + (c : O4) * z := rfl

private theorem lift_bijective : Function.Bijective lift := by
  refine ⟨Zsqrtd.lift_injective _ ?_, ?_⟩
  · intro a h
    have := mul_self_nonneg a
    omega
  · intro x
    refine ⟨⟨b.repr x 0, b.repr x 1⟩, ?_⟩
    have hx := b.sum_repr x
    simpa [Fin.sum_univ_two, b_apply, pow_zero, pow_one, zsmul_eq_mul,
      lift_apply] using hx

/-- The Gaussian integer model is identified with the actual integer ring, preserving its root. -/
def gaussianEquiv : GaussianInt ≃ₐ[ℤ] O4 :=
  AlgEquiv.ofBijective lift.toIntAlgHom lift_bijective

private theorem gaussianEquiv_apply (a c : ℤ) :
    gaussianEquiv ⟨a,c⟩ = (a : O4) + (c : O4) * z := rfl

private theorem gaussianEquiv_i : gaussianEquiv (Zsqrtd.sqrtd : GaussianInt) = z := by
  simpa [Zsqrtd.sqrtd] using gaussianEquiv_apply 0 1

private def gaussianD : GaussianInt →ₗ[ℤ] GaussianInt :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => (x.im : GaussianInt)
      map_zero' := by simp
      map_add' := fun x y => by simp }

private theorem gaussianD_law (x y : GaussianInt) :
    gaussianD (x * y) = gaussianD x * star y + x * gaussianD y := by
  change ((x * y).im : GaussianInt) = (x.im : GaussianInt) * star y + x * (y.im : GaussianInt)
  ext <;> simp <;> ring

/-- Conjugation transported along the proved pointed integer-ring equivalence. -/
def tau : O4 →ₐ[ℤ] O4 :=
  ((gaussianEquiv.symm.trans (starRingAut.toIntAlgEquiv)).trans gaussianEquiv).toAlgHom

/-- The imaginary-coordinate derivation, with values in the actual integer ring. -/
def derivation : O4 →ₗ[ℤ] O4 :=
  gaussianEquiv.toLinearMap.comp (gaussianD.comp gaussianEquiv.symm.toLinearMap)

private theorem tau_equiv (x : GaussianInt) :
    tau (gaussianEquiv x) = gaussianEquiv (star x) := by
  simp [tau]

private theorem derivation_equiv (x : GaussianInt) :
    derivation (gaussianEquiv x) = gaussianEquiv (gaussianD x) := by
  simp [derivation]

/-- The required twisted law holds for every pair of actual algebraic integers. -/
private theorem derivation_twisted (x y : O4) :
    derivation (x * y) = derivation x * tau y + x * derivation y := by
  obtain ⟨a, rfl⟩ := gaussianEquiv.surjective x
  obtain ⟨c, rfl⟩ := gaussianEquiv.surjective y
  rw [← map_mul, derivation_equiv, derivation_equiv, derivation_equiv, tau_equiv]
  rw [gaussianD_law, map_add, map_mul, map_mul]

/-- The concrete root values use the proved generator-preserving bridge. -/
private theorem counterinstance_root_values : derivation z = 1 ∧ tau z = z ^ 3 := by
  constructor
  · rw [← gaussianEquiv_i, derivation_equiv]
    simp [gaussianD, Zsqrtd.sqrtd]
  · have hi : star (Zsqrtd.sqrtd : GaussianInt) = -Zsqrtd.sqrtd := by
      ext <;> simp [Zsqrtd.sqrtd]
    have ht : tau z = -z := by
      rw [← gaussianEquiv_i, tau_equiv, hi, map_neg]
    rw [ht, pow_succ, pow_two, z_sq]
    ring

/-- An integral inner generator would force an odd integer to equal an even integer. -/
private theorem derivation_not_inner : ¬ IsInner (AlgHom.id ℤ O4) tau derivation := by
  rintro ⟨γ, hγ⟩
  obtain ⟨g, rfl⟩ := gaussianEquiv.surjective γ
  have h := hγ (gaussianEquiv (Zsqrtd.sqrtd : GaussianInt))
  rw [derivation_equiv, tau_equiv] at h
  have hg : gaussianD (Zsqrtd.sqrtd : GaussianInt) =
      g * star Zsqrtd.sqrtd - Zsqrtd.sqrtd * g := by
    apply gaussianEquiv.injective
    simpa only [map_sub, map_mul, AlgHom.id_apply] using h
  have hr := congrArg Zsqrtd.re hg
  norm_num [gaussianD, Zsqrtd.sqrtd, Zsqrtd.re_mul] at hr
  omega

private theorem b_repr (a c : ℤ) (i : Fin 2) :
    b.repr (gaussianEquiv ⟨a,c⟩) i = ![a,c] i := by
  have h : gaussianEquiv ⟨a,c⟩ = a • b 0 + c • b 1 := by
    simp [gaussianEquiv_apply, b_apply, zsmul_eq_mul]
  rw [h, map_add, map_smul, map_smul]
  fin_cases i <;> simp

/-- The existing integral power basis, with its proved dimension made explicit. -/
private def orderedPb : PowerBasis ℤ O4 where
  gen := z
  dim := 2
  basis := b
  basis_eq_pow := b_apply

private theorem actual_matrix :
    Algebra.leftMulMatrix b (tau z - z) = !![(0 : ℤ),2;-2,0] := by
  have ht : tau z = -z := by
    rw [counterinstance_root_values.2, pow_succ, pow_two, z_sq]
    ring
  have hd : tau z - z = gaussianEquiv ⟨0,-2⟩ := by
    rw [ht, gaussianEquiv_apply]
    simp
    ring
  have hd1 : (tau z-z)*z = gaussianEquiv ⟨2,0⟩ := by
    rw [ht, gaussianEquiv_apply]
    simp only [Int.cast_ofNat, Int.cast_zero, zero_mul, add_zero]
    calc
      (-z-z)*z = -(z*z) - z*z := by ring
      _ = 2 := by rw [z_sq]; ring
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, b_apply]
  fin_cases j <;> simp only [pow_zero, pow_one, mul_one]
  · rw [hd, b_repr]
    fin_cases i <;> rfl
  · rw [hd1, b_repr]
    fin_cases i <;> rfl

private theorem actual_vector (i : Fin 2) : b.repr (derivation z) i = ![1,0] i := by
  rw [counterinstance_root_values.1, ← gaussianEquiv.map_one]
  exact b_repr 1 0 i

private theorem printed_test : PrintedIntegralTest 2 1
    (Algebra.leftMulMatrix orderedPb.basis (tau z-z))
    (fun i => orderedPb.basis.repr (derivation z) i) := by
  change PrintedIntegralTest 2 1 (Algebra.leftMulMatrix b (tau z-z))
    (fun i => b.repr (derivation z) i)
  rw [actual_matrix]
  refine ⟨![0,1], ?_⟩
  intro i
  simp only [actual_vector, Matrix.adjugate_fin_two_of]
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

/-- The complete printed Conjecture 4.4 is false on its actual cyclotomic domain. -/
theorem result : ¬ claim := by
  intro h
  have hne : (AlgHom.id ℤ O4) ≠ tau := by
    intro heq
    have hz : z = -z := by
      calc
        z = tau z := by rw [← heq]; rfl
        _ = -z := by rw [counterinstance_root_values.2, pow_succ, pow_two, z_sq]; ring
    have hi : (Zsqrtd.sqrtd : GaussianInt) = -Zsqrtd.sqrtd := by
      apply gaussianEquiv.injective
      simpa [gaussianEquiv_i] using hz
    have him := congrArg Zsqrtd.im hi
    norm_num [Zsqrtd.sqrtd] at him
  letI : IsCyclotomicExtension {2 ^ 2} ℚ K4 := by
    norm_num
    exact CyclotomicField.isCyclotomicExtension 4 ℚ
  have hc := h 2 2 (by decide) (by decide) (by decide)
    K4 root root_primitive orderedPb rfl (by decide)
    (AlgHom.id ℤ O4) tau hne
    1 3 1 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) counterinstance_root_values.2 (by decide) (by decide) (by decide)
    derivation (by simpa using derivation_twisted)
  exact derivation_not_inner (hc.1.mpr printed_test)

#print axioms claim
#print axioms gaussianEquiv
#print axioms result

end
end D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFourFour
