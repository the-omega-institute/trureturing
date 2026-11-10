/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Commutator.Basic]
   utility: none
   digest: Unrestricted Frobenius top maps embedded in the actual original kernel. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalGroup
import Mathlib.GroupTheory.Commutator.Basic

/-! The linearized coordinate supplier is adapted upstream CFSG mathematics;
its attribution and license remain in FiniteJetCoefficients. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop
open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open OddPrimeJetRadical OddPrimeJetRadicalGroup OddPrimeJetGroup FiniteJetCoefficients
open scoped BigOperators commutatorElement
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p

private theorem top_commutes (q : K →ₗ[F] K) (hq : q 1 = 0) (T : K →ₗ[F] K) : commutesOriginal q (topMap (p := p) (K := K) T) := by
  apply (actual_commutant_normal_form (p := p) (K := K) q hq _).mpr
  refine ⟨0,T,rfl,?_⟩
  simp [toeplitzDegree, scalarMap]

private def topElement (q : K →ₗ[F] K) (hq : q 1 = 0) (T : K →ₗ[F] K) : (commutantAlgebra (p := p) (K := K) q) := ⟨topMap (p := p) (K := K) T, top_commutes q hq T⟩

private theorem topElement_mul (q : K →ₗ[F] K) (hq : q 1 = 0) (T U : K →ₗ[F] K) :
    topElement (p := p) (K := K) q hq T * topElement (p := p) (K := K) q hq U = 0 :=
  Subtype.ext (top_top (p := p) (K := K) T U)

private theorem topElement_add (q : K →ₗ[F] K) (hq : q 1 = 0) (T U : K →ₗ[F] K) :
    topElement (p := p) (K := K) q hq (T+U) = topElement (p := p) (K := K) q hq T + topElement (p := p) (K := K) q hq U :=
  Subtype.ext (topMap_add (p := p) (K := K) T U)

private theorem topElement_zero (q : K →ₗ[F] K) (hq : q 1 = 0) : topElement (p := p) (K := K) q hq 0 = 0 := by
  apply Subtype.ext
  ext v
  simp [topElement, topMap]

private def topUnit (q : K →ₗ[F] K) (hq : q 1 = 0) (T : K →ₗ[F] K) : (commutantAlgebra (p := p) (K := K) q)ˣ where
  val := 1 + topElement (p := p) (K := K) q hq T
  inv := 1 - topElement (p := p) (K := K) q hq T
  val_inv := by
    simp only [mul_sub, add_mul, one_mul, mul_one, topElement_mul]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, topElement_mul]
    abel

private def topUnitsHom (q : K →ₗ[F] K) (hq : q 1 = 0) : Multiplicative (K →ₗ[F] K) →* (commutantAlgebra (p := p) (K := K) q)ˣ where
  toFun T := topUnit (p := p) (K := K) q hq T.toAdd
  map_one' := by apply Units.ext; simp [topUnit, topElement_zero]
  map_mul' T U := by
    apply Units.ext
    change 1 + topElement (p := p) (K := K) q hq (T.toAdd + U.toAdd) =
      (1 + topElement (p := p) (K := K) q hq T.toAdd) * (1 + topElement (p := p) (K := K) q hq U.toAdd)
    rw [topElement_add]
    simp only [mul_add, add_mul, one_mul, mul_one, topElement_mul]
    abel

/-- The actual embedding T ↦ (1+top(T),identity original label). -/
def topEmbedding (q : K →ₗ[F] K) (hq : q 1 = 0) : Multiplicative (K →ₗ[F] K) →* (project (p := p) (K := K) q).ker :=
  (commutantUnitsEquiv (p := p) (K := K) q).toMonoidHom.comp (topUnitsHom q hq)

private theorem topEmbedding_injective (q : K →ₗ[F] K) (hq : q 1 = 0) : Function.Injective (topEmbedding (p := p) (K := K) q hq) := by
  intro T U h
  have he := (commutantUnitsEquiv (p := p) (K := K) q).injective h
  have hv := congrArg (fun x : (commutantAlgebra (p := p) (K := K) q)ˣ => (x.val : Module.End F V)) he
  change 1 + topMap (p := p) (K := K) T.toAdd = 1 + topMap (p := p) (K := K) U.toAdd at hv
  have ht := add_left_cancel hv
  have ht' : toeplitzDegree (p := p) (K := K) (0 : Fin p → K) T.toAdd =
      toeplitzDegree (p := p) (K := K) 0 U.toAdd := by
    simpa [toeplitzDegree, scalarMap] using ht
  have H := (toeplitzDegree_injective (p := p) (K := K) 0 0 rfl rfl T.toAdd U.toAdd ht').2
  exact congrArg Multiplicative.ofAdd H

variable [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p^n)

private def linearizedMap : (Fin n → K) →ₗ[K] (K →ₗ[F] K) where
  toFun a := ∑ i, a i • frobLinear (p := p) (K := K) i.val
  map_add' a b := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, mul_smul]

private theorem linearizedMap_apply (a : Fin n → K) (x : K) :
    linearizedMap (p := p) (K := K) a x = ∑ i, a i * x^(p^i.val) := by
  simp [linearizedMap, frobLinear_apply]

private def linearizedEquiv : (Fin n → K) ≃ₗ[K] (K →ₗ[F] K) :=
  LinearEquiv.ofBijective (linearizedMap (p := p) (K := K)) ⟨by
    intro a b h
    apply (linearized_coordinates hn hK (linearizedMap (p := p) (K := K) a)).unique
    · exact linearizedMap_apply a
    · intro x
      rw [h, linearizedMap_apply], by
    intro T
    obtain ⟨a,ha,_⟩ := linearized_coordinates hn hK T
    refine ⟨a, ?_⟩
    ext x
    exact (linearizedMap_apply a x).trans (ha x).symm⟩

/-- W0 is precisely the sum of the nonidentity Frobenius summands. -/
def offDiagonal : Submodule K (K →ₗ[F] K) :=
  LinearMap.ker ((LinearMap.proj (⟨0, by omega⟩ : Fin n)).comp
    (linearizedEquiv (p := p) (K := K) hn hK).symm.toLinearMap)

/-- The subgroup consists of actual original-pair operators 1+top(T), T in W0. -/
def offDiagonalTop (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) : Subgroup (project (p := p) (K := K) q).ker :=
  ((offDiagonal hn hK).toAddSubgroup.toSubgroup).map (topEmbedding (p := p) (K := K) q hq)

private def zeroHeadEquiv {m : ℕ} :
    {a : Fin (m+1) → K // a 0 = 0} ≃ (Fin m → K) where
  toFun a := Fin.tail a.val
  invFun a := ⟨Fin.cons 0 a, rfl⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact a.property.symm
    · rfl
  right_inv a := rfl

private def offDiagonalCoordinates : offDiagonal hn hK ≃
    {a : Fin n → K // a ⟨0, by omega⟩ = 0} :=
  (linearizedEquiv (p := p) (K := K) hn hK).symm.toEquiv.subtypeEquiv (by intro T; rfl)

/-- The non-scalar Frobenius top maps have the required exact order in the actual kernel. -/
theorem offDiagonalTop_cardinality (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    Nat.card (offDiagonalTop q hq hn hK) = p^(n*(n-1)) := by
  have hmap : Nat.card (offDiagonalTop q hq hn hK) = Nat.card (offDiagonal hn hK) := by
    let e : offDiagonal hn hK ≃ (offDiagonal hn hK).toAddSubgroup.toSubgroup :=
      Multiplicative.ofAdd.subtypeEquiv (fun _ => Iff.rfl)
    exact (Nat.card_congr (e.trans
      ((offDiagonal hn hK).toAddSubgroup.toSubgroup.equivMapOfInjective
        (topEmbedding (p := p) (K := K) q hq) (topEmbedding_injective q hq)).toEquiv)).symm
  rw [hmap, Nat.card_congr (offDiagonalCoordinates hn hK)]
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change Nat.card {a : Fin (m+1) → K // a 0 = 0} = _
  rw [Nat.card_congr (zeroHeadEquiv (K := K) (m := m)), Nat.card_fun,
    Nat.card_fin, Nat.card_eq_fintype_card (α := K), hK, ← Nat.pow_mul]
  simp

private def scalarConjugate (a : Kˣ) (T : K →ₗ[F] K) : K →ₗ[F] K :=
  (fieldScalar (a : K)).comp (T.comp (fieldScalar ((a⁻¹ : Kˣ) : K)))

private def character (a : Kˣ) (i : Fin n) : K :=
  (a : K) * (((a⁻¹ : Kˣ) : K)) ^ (p ^ i.val)

private theorem linearized_conjugate (a : Kˣ) (b : Fin n → K) :
    scalarConjugate (p := p) (K := K) a (linearizedMap (p := p) (K := K) b) =
      linearizedMap (p := p) (K := K) (fun i => character (p := p) (K := K) a i * b i) := by
  ext x
  change (a : K) * (linearizedMap (p := p) (K := K) b (((a⁻¹ : Kˣ) : K)*x)) = _
  simp only [linearizedMap_apply, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [character, Units.val_inv_eq_inv_val, a.ne_zero]
  ring

private theorem inverse_conjugate (a : Kˣ) (T : K →ₗ[F] K) :
    (linearizedEquiv (p := p) (K := K) hn hK).symm (scalarConjugate (p := p) (K := K) a T) =
      fun i => character (p := p) (K := K) a i * (linearizedEquiv (p := p) (K := K) hn hK).symm T i := by
  apply (linearizedEquiv (p := p) (K := K) hn hK).injective
  rw [LinearEquiv.apply_symm_apply]
  have he : linearizedMap (p := p) (K := K) ((linearizedEquiv (p := p) (K := K) hn hK).symm T) = T :=
    (linearizedEquiv (p := p) (K := K) hn hK).apply_symm_apply T
  change scalarConjugate (p := p) a T = linearizedMap (p := p) _
  conv_lhs => rw [← he]
  exact linearized_conjugate a _

/-- Scalar-conjugation differences contain no identity-Frobenius coefficient. -/
private theorem scalar_difference_mem (a : Kˣ) (T : K →ₗ[F] K) :
    scalarConjugate (p := p) (K := K) a T - T ∈ offDiagonal hn hK := by
  change (linearizedEquiv (p := p) (K := K) hn hK).symm (scalarConjugate (p := p) (K := K) a T - T) ⟨0, by omega⟩ = 0
  rw [map_sub, inverse_conjugate]
  simp [character, Units.val_inv_eq_inv_val, a.ne_zero]

include hK in
private theorem exists_full_character : ∃ a : Kˣ,
    ∀ i : Fin n, i.val ≠ 0 → character (p := p) (K := K) a i - 1 ≠ 0 := by
  obtain ⟨a,ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = p^n-1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card (α := K), hK]
  refine ⟨a, ?_⟩
  intro i hi hz
  have hp : p.Prime := Fact.out
  have he : character (p := p) (K := K) a i = 1 := sub_eq_zero.mp hz
  have hm : 1 < p^i.val := by
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have hlt : p^i.val-1 < orderOf a := by
    rw [ha,hcard]
    have hpow : p^i.val < p^n := Nat.pow_lt_pow_right hp.one_lt i.isLt
    omega
  have hne : a^(p^i.val-1) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) hlt
  apply hne
  have he' : (a : K) / (a : K)^(p^i.val) = 1 := by
    simpa [character, inv_pow, div_eq_mul_inv] using he
  have hpow : a^(p^i.val) = a := by
    apply Units.ext
    exact ((div_eq_one_iff_eq (pow_ne_zero _ a.ne_zero)).mp he').symm
  apply mul_right_cancel (b := a)
  rw [one_mul, ← pow_succ, show p^i.val-1+1 = p^i.val by omega, hpow]

/-- Every off-diagonal top map is a scalar-conjugation difference, with one scalar
working simultaneously for every nonidentity Frobenius summand. -/
private theorem offDiagonal_scalar_difference : ∃ a : Kˣ,
    ∀ T ∈ offDiagonal hn hK, ∃ S : K →ₗ[F] K, scalarConjugate (p := p) (K := K) a S - S = T := by
  obtain ⟨a,ha⟩ := exists_full_character hK
  refine ⟨a, ?_⟩
  intro T hT
  let c := (linearizedEquiv (p := p) (K := K) hn hK).symm T
  have hc : c ⟨0, by omega⟩ = 0 := hT
  let b : Fin n → K := fun i => c i / (character (p := p) (K := K) a i - 1)
  refine ⟨linearizedEquiv (p := p) (K := K) hn hK b, ?_⟩
  apply (linearizedEquiv (p := p) (K := K) hn hK).symm.injective
  rw [map_sub, inverse_conjugate, LinearEquiv.symm_apply_apply]
  funext i
  change character (p := p) (K := K) a i * b i - b i = c i
  by_cases hi : i.val = 0
  · have he : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi
    simp [he, b, hc]
  · dsimp [b]
    field_simp [ha i hi] <;> ring

/-- One actual field scalar realizes W0 exactly as its conjugation-difference image. -/
theorem scalar_difference_range : ∃ a : Kˣ, ∀ T : K →ₗ[F] K,
    T ∈ offDiagonal hn hK ↔ ∃ S : K →ₗ[F] K, scalarConjugate (p := p) a S - S = T := by
  obtain ⟨a,ha⟩ := offDiagonal_scalar_difference hn hK
  refine ⟨a, fun T => ⟨ha T, ?_⟩⟩
  rintro ⟨S,rfl⟩
  exact scalar_difference_mem hn hK a S


private def scalarElement (q : K →ₗ[F] K) (hq : q 1 = 0) (a : K) : commutantAlgebra (p := p) q := by
  refine ⟨scalarMap (p := p) a, ?_⟩
  apply (actual_commutant_generated_bridge (p := p) q hq _).mpr
  constructor
  · intro v
    simp [scalarMap_apply, map_smul]
  · intro b v
    simp [scalarMap_apply, map_smul, smul_smul, mul_comm]

private theorem scalarElement_mul (q : K →ₗ[F] K) (hq : q 1 = 0) (a b : K) :
    scalarElement (p := p) (K := K) q hq a * scalarElement (p := p) (K := K) q hq b = scalarElement (p := p) (K := K) q hq (a*b) := by
  apply Subtype.ext
  ext v
  simp [scalarElement, Module.End.mul_apply, scalarMap_apply, smul_smul]

private theorem scalarElement_one (q : K →ₗ[F] K) (hq : q 1 = 0) : scalarElement (p := p) (K := K) q hq (1 : K) = 1 := by
  apply Subtype.ext
  ext v
  simp [scalarElement, scalarMap_apply]

private def scalarUnit (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) : (commutantAlgebra (p := p) q)ˣ where
  val := scalarElement (p := p) (K := K) q hq (a : K)
  inv := scalarElement (p := p) (K := K) q hq ((a⁻¹ : Kˣ) : K)
  val_inv := by rw [scalarElement_mul]; simpa using scalarElement_one q hq
  inv_val := by rw [scalarElement_mul]; simpa using scalarElement_one q hq

private def scalarEmbedding (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) : (project (p := p) (K := K) q).ker :=
  commutantUnitsEquiv (p := p) (K := K) q (scalarUnit (p := p) (K := K) q hq a)

private theorem scalar_top_conjugate (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) (T : K →ₗ[F] K) :
    scalarElement (p := p) (K := K) q hq (a : K) * topElement (p := p) (K := K) q hq T *
      scalarElement (p := p) (K := K) q hq ((a⁻¹ : Kˣ) : K) = topElement (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change (a : K) • (topMap (p := p) T (((a⁻¹ : Kˣ) : K) • v)) =
    topMap (p := p) (scalarConjugate a T) v
  simp only [topMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    restricted_derivative_pow_local, map_smul, scalarConjugate, fieldScalar, Algebra.lsmul_apply,
    smul_eq_mul]
  exact ((constantLinear (p := p) (K := K)).map_smul (a : K) _).symm

private theorem scalar_unit_conjugate (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) (T : K →ₗ[F] K) :
    scalarUnit (p := p) (K := K) q hq a * topUnit (p := p) (K := K) q hq T * (scalarUnit (p := p) (K := K) q hq a)⁻¹ =
      topUnit (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T) := by
  apply Units.ext
  change scalarElement (p := p) (K := K) q hq (a : K) * (1 + topElement (p := p) (K := K) q hq T) *
    scalarElement (p := p) (K := K) q hq ((a⁻¹ : Kˣ) : K) = 1 + topElement (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T)
  rw [mul_add, mul_one, add_mul, scalar_top_conjugate]
  rw [scalarElement_mul]
  simp [scalarElement_one]

private theorem topElement_sub (q : K →ₗ[F] K) (hq : q 1 = 0) (T U : K →ₗ[F] K) :
    topElement (p := p) (K := K) q hq (T-U) = topElement (p := p) (K := K) q hq T - topElement (p := p) (K := K) q hq U := by
  apply Subtype.ext
  ext v
  simp [topElement, topMap]

private theorem scalar_unit_commutator (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) (T : K →ₗ[F] K) :
    ⁅scalarUnit (p := p) (K := K) q hq a, topUnit (p := p) (K := K) q hq T⁆ =
      topUnit (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T - T) := by
  rw [commutatorElement_def, scalar_unit_conjugate]
  apply Units.ext
  change (1 + topElement (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T)) * (1 - topElement (p := p) (K := K) q hq T) =
    1 + topElement (p := p) (K := K) q hq (scalarConjugate (p := p) (K := K) a T - T)
  rw [topElement_sub]
  simp only [mul_sub, add_mul, one_mul, mul_one, topElement_mul]
  abel

private theorem scalar_top_commutator (q : K →ₗ[F] K) (hq : q 1 = 0) (a : Kˣ) (T : K →ₗ[F] K) :
    ⁅scalarEmbedding (p := p) (K := K) q hq a, topEmbedding (p := p) (K := K) q hq (Multiplicative.ofAdd T)⁆ =
      topEmbedding (p := p) (K := K) q hq (Multiplicative.ofAdd (scalarConjugate (p := p) (K := K) a T - T)) := by
  change ⁅commutantUnitsEquiv (p := p) q (scalarUnit q hq a),
    commutantUnitsEquiv (p := p) q (topUnit q hq T)⁆ =
      commutantUnitsEquiv (p := p) q (topUnit q hq (scalarConjugate a T - T))
  have h := congrArg (commutantUnitsEquiv (p := p) (K := K) q) (scalar_unit_commutator q hq a T)
  simpa only [map_commutatorElement] using h

/-- Every W0 top unit lies in the commutator subgroup of the actual kernel. -/
theorem offDiagonalTop_le_commutator (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    offDiagonalTop q hq hn hK ≤ commutator ((project (p := p) (K := K) q).ker) := by
  obtain ⟨a,ha⟩ := scalar_difference_range hn hK
  intro x hx
  obtain ⟨T,hT,rfl⟩ := hx
  obtain ⟨S,hS⟩ := (ha T.toAdd).mp hT
  change topEmbedding q hq (Multiplicative.ofAdd T.toAdd) ∈ _
  rw [← hS, ← scalar_top_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem linearized_right_scalar (a : K) (b : Fin n → K) :
    (linearizedMap (p := p) (K := K) b).comp (fieldScalar (p := p) a) =
      linearizedMap (p := p) (K := K) (fun i => b i * a^(p^i.val)) := by
  ext x
  change linearizedMap (p := p) (K := K) b (a*x) = _
  simp only [linearizedMap_apply, mul_pow]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem coordinates_right_scalar (a : K) (T : K →ₗ[F] K) :
    (linearizedEquiv (p := p) (K := K) hn hK).symm
        (T.comp (fieldScalar (p := p) a)) =
      fun i => (linearizedEquiv (p := p) (K := K) hn hK).symm T i * a^(p^i.val) := by
  apply (linearizedEquiv (p := p) (K := K) hn hK).injective
  rw [LinearEquiv.apply_symm_apply]
  conv_lhs => rw [← (linearizedEquiv (p := p) (K := K) hn hK).apply_symm_apply T]
  exact linearized_right_scalar a _

private theorem offDiagonal_right_scalar (a : K) (T : K →ₗ[F] K)
    (hT : T ∈ offDiagonal hn hK) :
    T.comp (fieldScalar (p := p) a) ∈ offDiagonal hn hK := by
  change (linearizedEquiv (p := p) (K := K) hn hK).symm
    (T.comp (fieldScalar (p := p) a)) ⟨0, by omega⟩ = 0
  rw [coordinates_right_scalar]
  dsimp only
  change (linearizedEquiv (p := p) (K := K) hn hK).symm T ⟨0, by omega⟩ = 0 at hT
  rw [hT, zero_mul]

private theorem offDiagonal_scalar_bracket (a : K) (T : K →ₗ[F] K) :
    (fieldScalar (p := p) a).comp T - T.comp (fieldScalar a) ∈ offDiagonal hn hK := by
  have hl : (fieldScalar (p := p) a).comp T = a • T := by
    ext x
    rfl
  change (linearizedEquiv (p := p) (K := K) hn hK).symm
    ((fieldScalar (p := p) a).comp T - T.comp (fieldScalar a)) ⟨0, by omega⟩ = 0
  rw [hl, map_sub, map_smul, coordinates_right_scalar]
  simp [mul_comm]

private theorem productFamily_comm (c d : Fin p → K) :
    productFamily c d = productFamily d c := by
  funext j
  unfold productFamily
  rw [Finset.sum_comm]
  simp only [add_comm, mul_comm]

private theorem topConvolution_comm (c d : Fin p → K) :
    topConvolution c d = topConvolution d c := by
  unfold topConvolution
  rw [Finset.sum_comm]
  simp only [add_comm, mul_comm]

private theorem commutant_additive_defect (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) (X Y : commutantAlgebra (p := p) q) :
    ∃ T ∈ offDiagonal hn hK, X*Y-Y*X = topElement (p := p) q hq T := by
  obtain ⟨c,T,hc,heX⟩ := (actual_commutant_normal_form (p := p) q hq X.val).mp X.property
  obtain ⟨d,U,hd,heY⟩ := (actual_commutant_normal_form (p := p) q hq Y.val).mp Y.property
  let A := (fieldScalar (p := p) (c (leadingIndex (p := p)))).comp U -
    U.comp (fieldScalar (p := p) (c (leadingIndex (p := p))))
  let B := (fieldScalar (p := p) (d (leadingIndex (p := p)))).comp T -
    T.comp (fieldScalar (p := p) (d (leadingIndex (p := p))))
  refine ⟨A-B, (offDiagonal hn hK).sub_mem
    (offDiagonal_scalar_bracket hn hK _ _) (offDiagonal_scalar_bracket hn hK _ _), ?_⟩
  apply Subtype.ext
  change X.val * Y.val - Y.val * X.val = topMap (p := p) (A-B)
  rw [heX, heY, toeplitzDegree_mul, toeplitzDegree_mul, productFamily_comm c d]
  simp only [toeplitzDegree, productTop]
  rw [topConvolution_comm c d]
  have he : (fieldScalar (p := p) (d (leadingIndex (p := p)))).comp T +
      U.comp (fieldScalar (p := p) (c (leadingIndex (p := p)))) +
      fieldScalar (p := p) (topConvolution d c) =
      ((fieldScalar (p := p) (c (leadingIndex (p := p)))).comp U +
        T.comp (fieldScalar (p := p) (d (leadingIndex (p := p)))) +
        fieldScalar (p := p) (topConvolution d c)) - (A-B) := by
    dsimp [A,B]
    abel
  rw [he]
  ext v
  simp [topMap] <;> abel

private theorem topElement_right_mul (q : K →ₗ[F] K) (hq : q 1 = 0) (T : K →ₗ[F] K)
    (X : commutantAlgebra (p := p) q) :
    topElement (p := p) q hq T * X =
      topElement (p := p) q hq (T.comp (fieldScalar
        (leadingHom (p := p) q hq X))) := by
  obtain ⟨c,U,hc,he⟩ := (actual_commutant_normal_form (p := p) q hq X.val).mp X.property
  have hl : leadingHom (p := p) q hq X = c (leadingIndex (p := p)) := by
    change coefficientZero (X.val (constantLinear (p := p) (K := K) 1)) = _
    rw [he, toeplitzDegree_constant]
    simp [coefficientZero, constantLinear]
  apply Subtype.ext
  change topMap (p := p) T * X.val = _
  have hzero : topMap (p := p) T = toeplitzDegree (p := p) (0 : Fin p → K) T := by
    simp [toeplitzDegree, scalarMap]
  rw [hzero, he, toeplitzDegree_mul, hl]
  simp [productFamily, productTop, topConvolution, toeplitzDegree, fieldScalar, scalarMap, topElement]

private theorem unit_commutator_top (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) (x y : (commutantAlgebra (p := p) q)ˣ) :
    ∃ T ∈ offDiagonal hn hK, ⁅x,y⁆ = topUnit (p := p) q hq T := by
  obtain ⟨T,hT,hdef⟩ := commutant_additive_defect q hq hn hK x.val y.val
  let a := leadingHom (p := p) q hq (x⁻¹).val
  let b := leadingHom (p := p) q hq (y⁻¹).val
  let S := (T.comp (fieldScalar (p := p) a)).comp (fieldScalar (p := p) b)
  refine ⟨S, offDiagonal_right_scalar hn hK _ _
    (offDiagonal_right_scalar hn hK _ _ hT), ?_⟩
  have he : ⁅x,y⁆.val - 1 = topElement (p := p) q hq S := by
    calc
      ⁅x,y⁆.val - 1 = (x.val*y.val-y.val*x.val)*(x⁻¹).val*(y⁻¹).val := by
        simp [commutatorElement_def, sub_mul, mul_assoc]
      _ = topElement (p := p) q hq S := by
        rw [hdef, topElement_right_mul, topElement_right_mul]
  apply Units.ext
  change ⁅x,y⁆.val = 1 + topElement (p := p) q hq S
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- Both inclusions identify the commutator of the actual original-label kernel. -/
private theorem actual_commutator_eq (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    commutator ((project (p := p) (K := K) q).ker) = offDiagonalTop q hq hn hK := by
  apply le_antisymm _ (offDiagonalTop_le_commutator q hq hn hK)
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨a,rfl⟩ := (commutantUnitsEquiv (p := p) q).surjective x
  obtain ⟨b,rfl⟩ := (commutantUnitsEquiv (p := p) q).surjective y
  obtain ⟨T,hT,he⟩ := unit_commutator_top q hq hn hK a b
  rw [← map_commutatorElement, he]
  exact ⟨Multiplicative.ofAdd T,hT,rfl⟩

/-- The derived subgroup has its precise required order, including n=1. -/
private theorem actual_commutator_cardinality (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    Nat.card (commutator ((project (p := p) (K := K) q).ker)) = p^(n*(n-1)) := by
  rw [actual_commutator_eq q hq hn hK]
  exact offDiagonalTop_cardinality q hq hn hK

/-- The exact actual commutator subgroup and its order. -/
theorem actual_commutator_structure (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    commutator ((project (p := p) (K := K) q).ker) = offDiagonalTop q hq hn hK ∧
    Nat.card (commutator ((project (p := p) (K := K) q).ker)) = p^(n*(n-1)) :=
  ⟨actual_commutator_eq q hq hn hK, actual_commutator_cardinality q hq hn hK⟩

#print axioms actual_commutator_structure

#print axioms offDiagonalTop_le_commutator

#print axioms scalar_difference_range

#print axioms offDiagonalTop_cardinality
end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop
