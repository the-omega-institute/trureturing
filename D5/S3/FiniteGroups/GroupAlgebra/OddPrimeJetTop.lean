/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetTop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Commutator.Basic]
   utility: none
   digest: Unrestricted Frobenius top maps embedded in the actual original kernel. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetGalois
import Mathlib.GroupTheory.Commutator.Basic

/-! The linearized coordinate supplier is adapted upstream CFSG mathematics;
its attribution and license remain in FiniteJetCoefficients. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop
open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open OddPrimeJetRadical OddPrimeJetRadicalGroup OddPrimeJetGroup FiniteJetCoefficients
open FiniteJetClassification
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

private theorem abelian_original_label (q : K →ₗ[F] K)
    (hcomm : IsMulCommutative (originalGroup (p := p) q))
    (z : originalGroup (p := p) q) : z.val.2 = 1 := by
  letI := hcomm
  let ρ := originalRepresentation (p := p) q
  let t (g : Multiplicative K) : originalGroup (p := p) q :=
    ⟨(LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g), 1), by
      intro a v
      change ρ g (ρ a v) = ρ a (ρ g v)
      exact congrArg (fun T : Module.End F V => T v)
        ((ρ.map_mul g a).symm.trans
          ((congrArg ρ (mul_comm g a)).trans (ρ.map_mul a g)))⟩
  ext g
  apply faithful_action (p := p) q
  apply LinearMap.ext
  intro v
  have he := congrArg (fun w : originalGroup (p := p) q =>
    w.val.1 (z.val.1.symm v)) (mul_comm' z (t g))
  change z.val.1 (ρ g (z.val.1.symm v)) = ρ g (z.val.1 (z.val.1.symm v)) at he
  rw [z.property, LinearEquiv.apply_symm_apply] at he
  exact he

/-- The actual original group is nonabelian for every normalized parameter,
including the prime-field boundary and the smallest odd prime. -/
theorem original_derived_one_ne_bot (q : K →ₗ[F] K) (hq : q 1 = 0)
    (hn : 1 ≤ n) (hK : Fintype.card K = p ^ n) :
    derivedSeries (originalGroup (p := p) q) 1 ≠ ⊥ := by
  intro hbot
  have hcomm : IsMulCommutative (originalGroup (p := p) q) :=
    (commutator_eq_bot_iff _).mp hbot
  by_cases h1 : n = 1
  · subst n
    let A : Fin (1 - 1) → K := fun i => Fin.elim0 i
    have hQ : Q (p := p) 1 A = 0 := by
      ext x
      change (coefficientMap (p := p) 1 A).val x = 0
      rw [coefficientMap_apply]
      simp
    have hq0 : q = 0 := by
      obtain ⟨B, hB⟩ := (coefficientMap_bijective hn hK).surjective ⟨q, hq⟩
      have he : Q (p := p) 1 B = q := congrArg Subtype.val hB
      rw [← he]
      ext x
      change (coefficientMap (p := p) 1 B).val x = 0
      rw [coefficientMap_apply]
      simp
    let φ : Multiplicative K ≃* Multiplicative K :=
      { toFun := fun x => Multiplicative.ofAdd (-x.toAdd)
        invFun := fun x => Multiplicative.ofAdd (-x.toAdd)
        left_inv := by intro x; simp
        right_inv := by intro x; simp
        map_mul' := by intro x y; change -(x.toAdd + y.toAdd) = -x.toAdd + -y.toAdd; abel }
    let c : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
    obtain ⟨P, hP⟩ := (FiniteJetClassification.fixed_automorphism_coefficients_iff
      hn hK A A φ).mpr ⟨c, 1, by intro a; simp [φ, c], by intro i; exact Fin.elim0 i⟩
    let z : originalGroup (Q (p := p) 1 A) := ⟨(P, φ), hP⟩
    have hparam : q = Q (p := p) 1 A := hq0.trans hQ.symm
    have hcommQ : IsMulCommutative (originalGroup (Q (p := p) 1 A)) :=
      hparam ▸ hcomm
    have hlabel := abelian_original_label (Q (p := p) 1 A)
      hcommQ z
    have hneg := congrArg (fun f : Multiplicative K ≃* Multiplicative K =>
      (f (Multiplicative.ofAdd 1)).toAdd) hlabel
    have he : (-1 : K) = 1 := hneg
    have htwo : (2 : K) = 0 := by
      calc
        (2 : K) = 1 + 1 := by norm_num
        _ = (-1) + 1 := by rw [he]
        _ = 0 := neg_add_cancel 1
    letI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
    exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (Fact.out : 2 < p))
      ((CharP.cast_eq_zero_iff K p 2).mp htwo)
  · letI := hcomm
    have hu : commutator ((project (p := p) (K := K) q).ker) = ⊥ :=
      (commutator_eq_bot_iff _).mpr inferInstance
    have hc := actual_commutator_cardinality q hq hn hK
    rw [hu, Subgroup.card_bot] at hc
    have hpow : 1 < p ^ (n * (n - 1)) :=
      Nat.one_lt_pow (Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega)))
        (Fact.out : p.Prime).one_lt
    omega

#print axioms original_derived_one_ne_bot

/-- The exact actual kernel structure and the nonabelian original-group boundary. -/
theorem actual_commutator_structure (q : K →ₗ[F] K) (hq : q 1 = 0) (hn : 1 ≤ n) (hK : Fintype.card K = p^n) :
    commutator ((project (p := p) (K := K) q).ker) = offDiagonalTop q hq hn hK ∧
    Nat.card (commutator ((project (p := p) (K := K) q).ker)) = p^(n*(n-1)) ∧
    (∀ x y : actualPrincipalUnits (p := p) q hq, x*y = y*x) ∧
    (∀ x : actualPrincipalUnits (p := p) q hq, x^p = 1) ∧
    Nat.card (actualPrincipalUnits (p := p) q hq) = p^(n*(p-2)+n*n) ∧
    derivedSeries (originalGroup (p := p) q) 1 ≠ ⊥ := by
  obtain ⟨hcomm, hpow, hcard⟩ := actual_principal_unit_structure q hq hK
  exact ⟨actual_commutator_eq q hq hn hK, actual_commutator_cardinality q hq hn hK,
    hcomm, hpow, hcard, original_derived_one_ne_bot q hq hn hK⟩

#print axioms actual_commutator_structure

#print axioms offDiagonalTop_le_commutator

#print axioms scalar_difference_range

#print axioms offDiagonalTop_cardinality

private theorem exists_moving_ratio (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    ∃ a : Kˣ, (σ (a : K) / (a : K)) ^ p ≠ σ (a : K) / (a : K) := by
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  by_contra! h
  have hcross (x : K) : (σ x)^p * x = σ x * x^p := by
    by_cases hx : x = 0
    · simp [hx]
    · have he := h (Units.mk0 x hx)
      change (σ x / x)^p = σ x / x at he
      rw [div_pow, div_eq_div_iff (pow_ne_zero p hx) hx] at he
      exact he
  apply hσ
  apply AlgEquiv.ext
  intro x
  have h0 := hcross x
  have h1 := hcross (x+1)
  rw [map_add, map_one, add_pow_char, add_pow_char, one_pow] at h1
  have hd : (σ x)^p - σ x = x^p-x := by
    linear_combination h1-h0
  have hp : (σ x-x)*(x^p-x) = 0 := by
    linear_combination -h0 + x*hd
  rcases mul_eq_zero.mp hp with he | he
  · exact sub_eq_zero.mp he
  · have hx : x ∈ (⊥ : Subfield K) :=
      (Subfield.mem_bot_iff_pow_eq_self K p).mpr (sub_eq_zero.mp he)
    exact (show (⊥ : Subfield K) ≤
      σ.toRingHom.eqLocusField (RingHom.id K) from bot_le) hx

private theorem frobenius_mem_offDiagonal (h2 : 2 ≤ n) :
    frobLinear (p := p) (K := K) 1 ∈ offDiagonal hn hK := by
  classical
  let j : Fin n := ⟨1, by omega⟩
  let b : Fin n → K := fun i => if i = j then 1 else 0
  have he : linearizedEquiv hn hK b = frobLinear (p := p) (K := K) 1 := by
    change linearizedMap b = _
    simp [linearizedMap, b, j]
  change (linearizedEquiv hn hK).symm (frobLinear (p := p) (K := K) 1)
    ⟨0, by omega⟩ = 0
  rw [← he, LinearEquiv.symm_apply_apply]
  simp [b, j, Fin.ext_iff]

#print axioms exists_moving_ratio

include hn hK in
private theorem scalar_commutator_leading (q : K →ₗ[F] K) (hq : q 1 = 0)
    (g : originalGroup (p := p) q) (a : Kˣ) :
    originalConstantScalar q ⁅g, (scalarEmbedding q hq a).val⁆ =
      originalGalois q hq g (a : K) / (a : K) := by
  let m := (scalarEmbedding q hq a).val
  have hm : originalGalois q hq m = 1 := originalGalois_of_label_one q hq m rfl
  have hc : originalConstantScalar q m = (a : K) := by
    change coefficientZero (scalarMap (p := p) (a : K) (constantLinear 1)) = _
    simp [scalarMap_apply, coefficientZero, constantLinear]
  have hci : originalConstantScalar q m⁻¹ = (a : K)⁻¹ := by
    apply mul_left_cancel₀ a.ne_zero
    have h := originalConstantScalar_mul hn hK q hq m m⁻¹
    rw [mul_inv_cancel, hc, hm, AlgEquiv.one_apply] at h
    rw [← h, mul_inv_cancel₀ a.ne_zero]
    simp [originalConstantScalar, coefficientZero, constantLinear]
  have hcancel : originalConstantScalar q g *
      originalGalois q hq g (originalConstantScalar q g⁻¹) = 1 := by
    have h := originalConstantScalar_mul hn hK q hq g g⁻¹
    simpa [originalConstantScalar, coefficientZero, constantLinear] using h.symm
  change originalConstantScalar q (g*m*g⁻¹*m⁻¹) = _
  rw [originalConstantScalar_mul hn hK q hq,
    originalConstantScalar_mul hn hK q hq,
    originalConstantScalar_mul hn hK q hq, hc, hci]
  simp only [map_mul, map_inv, hm, mul_one, mul_inv_cancel, AlgEquiv.one_apply,
    AlgEquiv.mul_apply]
  calc
    _ = (originalConstantScalar q g *
        originalGalois q hq g (originalConstantScalar q g⁻¹)) *
        originalGalois q hq g (a : K) * (a : K)⁻¹ := by ring
    _ = _ := by rw [hcancel, one_mul, div_eq_mul_inv]

private theorem topElement_left_mul (q : K →ₗ[F] K) (hq : q 1 = 0)
    (X : commutantAlgebra (p := p) q) (T : K →ₗ[F] K) :
    X * topElement q hq T = topElement q hq ((fieldScalar (leadingHom q hq X)).comp T) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change X.val (constantLinear (T _)) = constantLinear (leadingHom q hq X * T _)
  exact constant_action q hq X _

private theorem kernel_commuting_frobenius (q : K →ₗ[F] K) (hq : q 1 = 0)
    (x : (project (p := p) q).ker)
    (hx : x * topEmbedding q hq (Multiplicative.ofAdd (frobLinear (p := p) 1)) =
      topEmbedding q hq (Multiplicative.ofAdd (frobLinear (p := p) 1)) * x) :
    originalConstantScalar q x.val ^ p = originalConstantScalar q x.val := by
  let e := commutantUnitsEquiv (p := p) q
  obtain ⟨u,rfl⟩ := e.surjective x
  have hu : u * topUnit q hq (frobLinear (p := p) 1) =
      topUnit q hq (frobLinear (p := p) 1) * u := by
    apply e.injective
    rw [e.map_mul, e.map_mul]
    exact hx
  have he := congrArg Units.val hu
  change u.val * (1 + topElement q hq (frobLinear (p := p) 1)) =
    (1 + topElement q hq (frobLinear (p := p) 1)) * u.val at he
  simp only [mul_add, add_mul, mul_one, one_mul] at he
  have ht := add_left_cancel he
  rw [topElement_left_mul, topElement_right_mul] at ht
  have hv := congrArg (fun X : commutantAlgebra (p := p) q =>
    coefficientZero (X.val (topInput (p := p) (K := K) 1))) ht
  change originalConstantScalar q (e u).val ^ p = originalConstantScalar q (e u).val
  have hl : originalConstantScalar q (e u).val = leadingHom q hq u.val := rfl
  rw [hl]
  have hmap (T : K →ₗ[F] K) :
      coefficientZero ((topElement q hq T).val (topInput (p := p) 1)) = T 1 := by
    change coefficientZero (topMap T (topInput (p := p) 1)) = T 1
    rw [topMap_topInput, dividedMonomial_zero]
    simp [coefficientZero, constantLinear]
  rw [hmap, hmap] at hv
  simpa [LinearMap.comp_apply, fieldScalar, frobLinear_apply] using hv.symm

#print axioms scalar_commutator_leading
#print axioms kernel_commuting_frobenius

include hn hK in
/-- The second actual derived subgroup vanishes exactly when the actual
Galois image is trivial. No pure-Frobenius lift or splitting is assumed. -/
theorem original_derived_two_eq_bot_iff (q : K →ₗ[F] K) (hq : q 1 = 0) :
    derivedSeries (originalGroup (p := p) q) 2 = ⊥ ↔
      (originalGalois q hq).range = ⊥ := by
  constructor
  · intro hbot
    apply le_antisymm _ bot_le
    rintro σ ⟨g,rfl⟩
    change originalGalois q hq g = 1
    by_contra hσ
    obtain ⟨a, ha⟩ := exists_moving_ratio (originalGalois q hq g) hσ
    let b := originalGalois q hq g (a : K) / (a : K)
    have h2 : 2 ≤ n := by
      by_contra h2
      have hn1 : n = 1 := by omega
      have hc : Fintype.card K = p := by simpa [hn1] using hK
      apply ha
      change b ^ p = b
      rw [← hc]
      exact FiniteField.pow_card b
    let m := scalarEmbedding q hq a
    let x : (project q).ker := ⟨⁅g,m.val⁆, by
      change project q ⁅g,m.val⁆ = 1
      rw [map_commutatorElement, show project q m.val = 1 from m.property]
      simp [commutatorElement_def]⟩
    let t := topEmbedding q hq (Multiplicative.ofAdd (frobLinear (p := p) (K := K) 1))
    have hx : x.val ∈ derivedSeries (originalGroup (p := p) q) 1 :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have htK : t ∈ commutator ((project q).ker) :=
      offDiagonalTop_le_commutator q hq hn hK
        ⟨Multiplicative.ofAdd (frobLinear (p := p) (K := K) 1),
          frobenius_mem_offDiagonal hn hK h2, rfl⟩
    have ht : t.val ∈ derivedSeries (originalGroup (p := p) q) 1 :=
      map_derivedSeries_le_derivedSeries (project q).ker.subtype 1 ⟨t,htK,rfl⟩
    have hct : ⁅x.val,t.val⁆ ∈ derivedSeries (originalGroup (p := p) q) 2 :=
      Subgroup.commutator_mem_commutator hx ht
    rw [hbot] at hct
    have hcomm : x*t = t*x :=
      Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hct)
    have hfix := kernel_commuting_frobenius q hq x hcomm
    have hl : originalConstantScalar q x.val = b :=
      scalar_commutator_leading hn hK q hq g a
    rw [hl] at hfix
    exact ha hfix
  · exact original_derived_two_of_galois_trivial hn hK q hq

include hn hK in
/-- The unchanged universal actual original-group derived-series endpoint. -/
theorem original_derived_structure (q : K →ₗ[F] K) (hq : q 1 = 0) :
    derivedSeries (originalGroup (p := p) q) 3 = ⊥ ∧
    (derivedSeries (originalGroup (p := p) q) 2 = ⊥ ↔
      (originalGalois q hq).range = ⊥) ∧
    derivedSeries (originalGroup (p := p) q) 1 ≠ ⊥ :=
  ⟨original_derived_three_eq_bot hn hK q hq,
    original_derived_two_eq_bot_iff hn hK q hq,
    original_derived_one_ne_bot q hq hn hK⟩

#print axioms original_derived_structure

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop
