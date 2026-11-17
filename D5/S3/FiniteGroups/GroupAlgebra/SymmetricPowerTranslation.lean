/- GID: D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric, mathlib/module/Mathlib.LinearAlgebra.PiTensorProduct.Basis, mathlib/module/Mathlib.Data.Fintype.EquivFin, mathlib/module/Mathlib.Data.Fintype.Fin]
   utility: none
   digest: Genuine symmetric powers of a faithful two-dimensional action and their contragredients have polynomial translation coordinates in every degree. -/

import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
import D5.S3.FiniteGroups.GroupAlgebra.TwoDimensionalUnipotentNormalForm

/-!
The domain below is Mathlib's actual additive-congruence quotient
`SymmetricPower K (Fin n) V`.  Neither an averaging projector nor a
replacement coordinate definition of the symmetric power is used.

The coordinate construction first takes a genuine basis and two action
equations. The final existence theorem obtains these from the proved
two-dimensional normal form, with no basis premise on the caller.

Universe/API boundary: the current Mathlib declaration has
`(R ι : Type u)`, with the SAME universe for R and the index type.
Consequently the exact index `Fin n : Type` requires `K : Type` here.
V, N, and E retain independent universes.  There is no characteristic,
cardinality, or degree restriction on this small field.  A version for
`K : Type uK` with arbitrary uK would first require making the upstream
quotient's ring/index universe parameters independent; no such library
change is made or assumed by this source.

This is the classical coordinate construction underlying Elmer--Kadr,
Section 2.2, rather than a new classification theorem.  The final
tensor/direct-sum and relative-witness transport is outside this file.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
namespace SymmetricPowerTranslation

open Module Polynomial
open scoped TensorProduct

universe uV uN uE

variable {K : Type} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V]

/- Only the quotient helpers actually used by the induced action and
the polynomial coordinate map are introduced here. -/
section Quotient

variable {N : Type uN} [AddCommGroup N] [Module K N] {n : ℕ}

private def descend
    (L : (⨂[K] (_ : Fin n), V) →ₗ[K] N)
    (hL : ∀ (e : Equiv.Perm (Fin n)) (v : Fin n → V),
      L (PiTensorProduct.tprod K v) =
        L (PiTensorProduct.tprod K (fun j => v (e j)))) :
    SymmetricPower K (Fin n) V →ₗ[K] N where
  __ := AddCon.lift (addConGen (SymmetricPower.Rel K (Fin n) V))
    L.toAddMonoidHom (AddCon.addConGen_le.mpr (by
      intro x y h
      cases h with
      | perm e v => exact hL e v))
  map_smul' r z := AddCon.induction_on z (fun t => L.map_smul r t)

private theorem descend_mk
    (L : (⨂[K] (_ : Fin n), V) →ₗ[K] N)
    (hL : ∀ (e : Equiv.Perm (Fin n)) (v : Fin n → V),
      L (PiTensorProduct.tprod K v) =
        L (PiTensorProduct.tprod K (fun j => v (e j))))
    (t : ⨂[K] (_ : Fin n), V) :
    descend L hL (SymmetricPower.mk K (Fin n) V t) = L t := rfl

def liftSymmetric
    (F : MultilinearMap K (fun _ : Fin n => V) N)
    (hF : ∀ (e : Equiv.Perm (Fin n)) (v : Fin n → V),
      F (fun j => v (e j)) = F v) :
    SymmetricPower K (Fin n) V →ₗ[K] N :=
  descend (PiTensorProduct.lift F) (by
    intro e v
    simpa only [PiTensorProduct.lift.tprod] using (hF e v).symm)

theorem liftSymmetric_tprod
    (F : MultilinearMap K (fun _ : Fin n => V) N)
    (hF : ∀ (e : Equiv.Perm (Fin n)) (v : Fin n → V),
      F (fun j => v (e j)) = F v) (v : Fin n → V) :
    liftSymmetric F hF (SymmetricPower.tprod K v) = F v := by
  change descend _ _ (SymmetricPower.mk K (Fin n) V
    (PiTensorProduct.tprod K v)) = F v
  rw [descend_mk, PiTensorProduct.lift.tprod]

theorem ext_tprod
    {F G : SymmetricPower K (Fin n) V →ₗ[K] N}
    (h : ∀ v : Fin n → V,
      F (SymmetricPower.tprod K v) = G (SymmetricPower.tprod K v)) : F = G := by
  have hm : F.comp (SymmetricPower.mk K (Fin n) V) =
      G.comp (SymmetricPower.mk K (Fin n) V) := by
    apply PiTensorProduct.ext
    exact MultilinearMap.ext h
  apply LinearMap.ext
  intro z
  refine AddCon.induction_on z (fun t => ?_)
  exact LinearMap.congr_fun hm t

/-- The endomorphism induced on the actual quotient by applying f to every factor. -/
def map (n : ℕ) (f : V →ₗ[K] V) :
    Module.End K (SymmetricPower K (Fin n) V) :=
  liftSymmetric ((SymmetricPower.tprod K).compLinearMap (fun _ => f)) (by
    intro e v
    change SymmetricPower.tprod K (fun j => f (v (e j))) =
      SymmetricPower.tprod K (fun j => f (v j))
    exact SymmetricPower.tprod_equiv e (fun j => f (v j)))

@[simp] theorem map_tprod (n : ℕ) (f : V →ₗ[K] V) (v : Fin n → V) :
    map n f (SymmetricPower.tprod K v) =
      SymmetricPower.tprod K (fun j => f (v j)) :=
  liftSymmetric_tprod _ _ v

end Quotient

section Action

variable {E : Type uE} [AddGroup E]

/-- The genuine induced representation, obtained by descent of tensor powers of rho(g). -/
def action (ρ : Representation K (Multiplicative E) V) (n : ℕ) :
    Representation K (Multiplicative E) (SymmetricPower K (Fin n) V) where
  toFun g := map n (ρ g)
  map_one' := by
    apply ext_tprod
    intro v
    simp only [map_tprod, map_one, Module.End.one_apply]
  map_mul' g h := by
    apply ext_tprod
    intro v
    simp only [Module.End.mul_apply, map_tprod, map_mul]

@[simp] theorem action_tprod (ρ : Representation K (Multiplicative E) V)
    (n : ℕ) (g : Multiplicative E) (v : Fin n → V) :
    action ρ n g (SymmetricPower.tprod K v) =
      SymmetricPower.tprod K (fun j => ρ g (v j)) := map_tprod n (ρ g) v

end Action

section BinaryWords

/-- The number of b1 factors, as a cardinal of a genuine fiber. -/
def weight {n : ℕ} (f : Fin n → Fin 2) : ℕ := Fintype.card {j // f j = 1}

theorem weight_le {n : ℕ} (f : Fin n → Fin 2) : weight f ≤ n := by
  simpa only [weight, Fintype.card_fin] using
    Fintype.card_subtype_le (fun j : Fin n => f j = 1)

def weightIndex {n : ℕ} (f : Fin n → Fin 2) : Fin (n + 1) :=
  ⟨weight f, Nat.lt_succ_of_le (weight_le f)⟩

/-- The canonical word with i copies of 1, including the empty word when n=0. -/
def word {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : Fin 2 :=
  if j.val < i.val then 1 else 0

@[simp] theorem weight_word {n : ℕ} (i : Fin (n + 1)) : weight (word i) = i.val := by
  have hp : (fun j : Fin n => word i j = 1) = (fun j : Fin n => j.val < i.val) := by
    funext j
    apply propext
    simp only [word]
    split_ifs <;> simp_all
  unfold weight
  simp only [Fintype.card_subtype, hp]
  simp only [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt_succ i.isLt)]

@[simp] theorem weightIndex_word {n : ℕ} (i : Fin (n + 1)) :
    weightIndex (word i) = i := by
  apply Fin.ext
  exact weight_word i

private theorem fin_two_zero_iff_ne_one (c : Fin 2) : c = 0 ↔ ¬ c = 1 := by
  fin_cases c <;> decide

/-- Equal weights give an actual permutation of tensor positions.
The equivalence is assembled from both fibers, not from averaging. -/
theorem exists_perm_of_weight_eq {n : ℕ} (f g : Fin n → Fin 2)
    (h : weight f = weight g) :
    ∃ e : Equiv.Perm (Fin n), ∀ j, g (e j) = f j := by
  classical
  have hc : ∀ c : Fin 2,
      Fintype.card {j // f j = c} = Fintype.card {j // g j = c} := by
    intro c
    fin_cases c
    · change Fintype.card {j // f j = 0} = Fintype.card {j // g j = 0}
      have hfcard : Fintype.card {j // f j = 0} =
          Fintype.card {j // ¬ f j = 1} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun j => fin_two_zero_iff_ne_one (f j)))
      have hgcard : Fintype.card {j // g j = 0} =
          Fintype.card {j // ¬ g j = 1} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun j => fin_two_zero_iff_ne_one (g j)))
      rw [hfcard, hgcard, Fintype.card_subtype_compl, Fintype.card_subtype_compl]
      exact congrArg (Fintype.card (Fin n) - ·) h
    · exact h
  let ef : ∀ c : Fin 2, {j // f j = c} ≃ {j // g j = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

end BinaryWords

section Coordinates

variable (b : Basis (Fin 2) K V)

/-- Dehomogenization of a single vector: x0*b0+x1*b1 maps to x0+x1*X. -/
def linearPolynomial : V →ₗ[K] K[X] := b.constr K (fun c => if c = 0 then 1 else X)

@[simp] theorem linearPolynomial_b0 : linearPolynomial b (b 0) = 1 := by
  simp [linearPolynomial]

@[simp] theorem linearPolynomial_b1 : linearPolynomial b (b 1) = X := by
  simp [linearPolynomial]

private def polynomialMultilinear (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => V) K[X] :=
  (MultilinearMap.mkPiAlgebra K (Fin n) K[X]).compLinearMap
    (fun _ => linearPolynomial b)

/-- Product of the dehomogenized factors, descended to the genuine quotient. -/
def polynomialMap (n : ℕ) : SymmetricPower K (Fin n) V →ₗ[K] K[X] :=
  liftSymmetric (polynomialMultilinear b n) (by
    intro e v
    exact Equiv.prod_comp e (fun j => linearPolynomial b (v j)))

@[simp] theorem polynomialMap_tprod (n : ℕ) (v : Fin n → V) :
    polynomialMap b n (SymmetricPower.tprod K v) =
      ∏ j, linearPolynomial b (v j) :=
  liftSymmetric_tprod _ _ v

def pureBasis {n : ℕ} (f : Fin n → Fin 2) : SymmetricPower K (Fin n) V :=
  SymmetricPower.tprod K (fun j => b (f j))

theorem pureBasis_eq_of_weight_eq {n : ℕ} (f g : Fin n → Fin 2)
    (h : weight f = weight g) : pureBasis b f = pureBasis b g := by
  obtain ⟨e, he⟩ := exists_perm_of_weight_eq f g h
  calc
    pureBasis b f = SymmetricPower.tprod K (fun j => b (g (e j))) := by
      change SymmetricPower.tprod K (fun j => b (f j)) = _
      congr 1
      funext j
      rw [he j]
    _ = pureBasis b g := SymmetricPower.tprod_equiv e (fun j => b (g j))

theorem polynomialMap_pureBasis {n : ℕ} (f : Fin n → Fin 2) :
    polynomialMap b n (pureBasis b f) = X ^ weight f := by
  classical
  rw [pureBasis, polynomialMap_tprod]
  calc
    (∏ j, linearPolynomial b (b (f j))) =
        ∏ j, (X : K[X]) ^ (if f j = 1 then 1 else 0 : ℕ) := by
      apply Finset.prod_congr rfl
      intro j _
      generalize hf : f j = c
      fin_cases c <;> simp
    _ = X ^ (∑ j, if f j = 1 then 1 else 0 : ℕ) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = X ^ weight f := by simp [weight, Fintype.card_subtype]

private def tensorBasis (n : ℕ) :
    Basis (Fin n → Fin 2) K (⨂[K] (_ : Fin n), V) :=
  Basis.piTensorProduct (fun _ => b)

private theorem ext_pureBasis {n : ℕ}
    {N : Type uN} [AddCommGroup N] [Module K N]
    {F G : SymmetricPower K (Fin n) V →ₗ[K] N}
    (h : ∀ f : Fin n → Fin 2, F (pureBasis b f) = G (pureBasis b f)) : F = G := by
  have hm : F.comp (SymmetricPower.mk K (Fin n) V) =
      G.comp (SymmetricPower.mk K (Fin n) V) := by
    apply (tensorBasis b n).ext
    intro f
    simpa only [LinearMap.comp_apply, tensorBasis, Basis.piTensorProduct_apply,
      SymmetricPower.tprod, pureBasis, LinearMap.compMultilinearMap_apply] using h f
  apply LinearMap.ext
  intro z
  refine AddCon.induction_on z (fun t => ?_)
  exact LinearMap.congr_fun hm t

theorem polynomialMap_mem (n : ℕ) (z : SymmetricPower K (Fin n) V) :
    polynomialMap b n z ∈ Polynomial.degreeLT K (n + 1) := by
  classical
  refine AddCon.induction_on z (fun t => ?_)
  change polynomialMap b n (SymmetricPower.mk K (Fin n) V t) ∈ _
  rw [← (tensorBasis b n).sum_repr t]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro f _
  apply Submodule.smul_mem
  simp only [tensorBasis, Basis.piTensorProduct_apply]
  change polynomialMap b n (pureBasis b f) ∈ Polynomial.degreeLT K (n + 1)
  rw [polynomialMap_pureBasis]
  have hm := (Polynomial.degreeLT.basis K (n + 1) (weightIndex f)).property
  simpa only [Polynomial.degreeLT.basis_val, weightIndex] using hm

/-- The forward map to degree < n+1. -/
def toPolynomial (n : ℕ) : SymmetricPower K (Fin n) V →ₗ[K] Primal K (n + 1) :=
  (polynomialMap b n).codRestrict _ (polynomialMap_mem b n)

@[simp] theorem toPolynomial_coe (n : ℕ) (z : SymmetricPower K (Fin n) V) :
    (toPolynomial b n z : K[X]) = polynomialMap b n z := rfl

theorem toPolynomial_pureBasis {n : ℕ} (f : Fin n → Fin 2) :
    toPolynomial b n (pureBasis b f) =
      Polynomial.degreeLT.basis K (n + 1) (weightIndex f) := by
  apply Subtype.ext
  simp only [toPolynomial_coe, polynomialMap_pureBasis, Polynomial.degreeLT.basis_val,
    weightIndex]

/-- The inverse sends X^i to the real pure product with exactly i factors b1. -/
def fromPolynomial (n : ℕ) : Primal K (n + 1) →ₗ[K] SymmetricPower K (Fin n) V :=
  (Polynomial.degreeLT.basis K (n + 1)).constr K (fun i => pureBasis b (word i))

@[simp] theorem fromPolynomial_basis (n : ℕ) (i : Fin (n + 1)) :
    fromPolynomial b n (Polynomial.degreeLT.basis K (n + 1) i) =
      pureBasis b (word i) := by simp [fromPolynomial]

theorem toPolynomial_comp_fromPolynomial (n : ℕ) :
    (toPolynomial b n).comp (fromPolynomial b n) = LinearMap.id := by
  apply (Polynomial.degreeLT.basis K (n + 1)).ext
  intro i
  simp only [LinearMap.comp_apply, fromPolynomial_basis, toPolynomial_pureBasis,
    weightIndex_word, LinearMap.id_apply]

theorem fromPolynomial_comp_toPolynomial (n : ℕ) :
    (fromPolynomial b n).comp (toPolynomial b n) = LinearMap.id := by
  apply ext_pureBasis b
  intro f
  simp only [LinearMap.comp_apply, toPolynomial_pureBasis, fromPolynomial_basis,
    LinearMap.id_apply]
  apply pureBasis_eq_of_weight_eq b
  rw [weight_word]
  rfl

/-- Actual symmetric-power coordinates, valid in every characteristic and every degree. -/
def polynomialEquiv (n : ℕ) :
    SymmetricPower K (Fin n) V ≃ₗ[K] Primal K (n + 1) where
  __ := toPolynomial b n
  invFun := fromPolynomial b n
  left_inv z := LinearMap.congr_fun (fromPolynomial_comp_toPolynomial b n) z
  right_inv q := LinearMap.congr_fun (toPolynomial_comp_fromPolynomial b n) q

end Coordinates

section Translation

variable {E : Type uE} [AddGroup E]
variable (ρ : Representation K (Multiplicative E) V)
variable (b : Basis (Fin 2) K V) (α : E →+ K)
variable (h0 : ∀ e : E, ρ (Multiplicative.ofAdd e) (b 0) = b 0)
variable (h1 : ∀ e : E,
  ρ (Multiplicative.ofAdd e) (b 1) = α e • b 0 + b 1)

include h0 h1

theorem linearPolynomial_action (e : E) (v : V) :
    linearPolynomial b (ρ (Multiplicative.ofAdd e) v) =
      Polynomial.taylor (α e) (linearPolynomial b v) := by
  have h : (linearPolynomial b).comp (ρ (Multiplicative.ofAdd e)) =
      (Polynomial.taylor (α e)).comp (linearPolynomial b) := by
    apply b.ext
    intro c
    fin_cases c
    · change linearPolynomial b (ρ (Multiplicative.ofAdd e) (b 0)) =
        Polynomial.taylor (α e) (linearPolynomial b (b 0))
      rw [h0 e, linearPolynomial_b0, Polynomial.taylor_one, Polynomial.C_1]
    · change linearPolynomial b (ρ (Multiplicative.ofAdd e) (b 1)) =
        Polynomial.taylor (α e) (linearPolynomial b (b 1))
      rw [h1 e, map_add, map_smul, linearPolynomial_b0, linearPolynomial_b1,
        Polynomial.taylor_X]
      simp [Polynomial.smul_eq_C_mul, add_comm]
  exact LinearMap.congr_fun h v

theorem toPolynomial_intertwining (n : ℕ) (g : Multiplicative E) :
    (toPolynomial b n).comp (action ρ n g) =
      (((primalAction K (n + 1)).comp α.toMultiplicative) g).comp
        (toPolynomial b n) := by
  apply ext_tprod
  intro v
  apply Subtype.ext
  change polynomialMap b n (action ρ n g (SymmetricPower.tprod K v)) =
    Polynomial.taylor (α (Multiplicative.toAdd g))
      (polynomialMap b n (SymmetricPower.tprod K v))
  rw [action_tprod, polynomialMap_tprod, polynomialMap_tprod]
  change (∏ j, linearPolynomial b (ρ (Multiplicative.ofAdd (Multiplicative.toAdd g)) (v j))) = _
  simp_rw [linearPolynomial_action ρ b α h0 h1 (Multiplicative.toAdd g)]
  exact (map_prod (Polynomial.taylorAlgHom (α (Multiplicative.toAdd g)))
    (fun j : Fin n => linearPolynomial b (v j)) Finset.univ).symm

/-- The requested representation equivalence on the original quotient.
No injectivity of alpha, finiteness, or characteristic restriction is needed for this bridge. -/
def primalEquiv (n : ℕ) :
    (action ρ n).Equiv ((primalAction K (n + 1)).comp α.toMultiplicative) :=
  Representation.Equiv.mk (polynomialEquiv b n)
    (toPolynomial_intertwining ρ b α h0 h1 n)

/-- The dual coordinate change is pullback along the INVERSE primal equivalence. -/
def contragredientEquiv (n : ℕ) :
    (action ρ n).dual.Equiv ((dualAction K (n + 1)).comp α.toMultiplicative) := by
  let e := primalEquiv ρ b α h0 h1 n
  refine Representation.Equiv.mk e.toLinearEquiv.symm.dualMap ?_
  intro g
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro q
  change φ (action ρ n g⁻¹ (e.toLinearEquiv.symm q)) =
    φ (e.toLinearEquiv.symm
      (primalAction K (n + 1) ((α.toMultiplicative g)⁻¹) q))
  rw [← map_inv α.toMultiplicative g]
  exact congrArg φ (LinearMap.congr_fun
    (e.symm.toIntertwiningMap.isIntertwining' (g⁻¹)) q).symm

end Translation

section FaithfulModels

variable {E : Type uE} [AddCommGroup E] [Nontrivial E]

/-- Every faithful two-dimensional elementary-abelian action has one actual
injective additive parameter giving all symmetric-power and dual models.
The basis and its unipotent equations are conclusions of the normal-form
theorem, not additional assumptions. Relative-projective transport is separate. -/
theorem exists_faithful_polynomial_models
    {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional K V]
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K V = 2)
    (ρ : Representation K (Multiplicative E) V)
    (hρ : Function.Injective ρ) :
    ∃ α : E →+ K, Function.Injective α ∧
      (∀ n : ℕ, Nonempty ((action ρ n).Equiv
        ((primalAction K (n + 1)).comp α.toMultiplicative))) ∧
      (∀ n : ℕ, Nonempty ((action ρ n).dual.Equiv
        ((dualAction K (n + 1)).comp α.toMultiplicative))) := by
  obtain ⟨b, α, hα, h0, h1⟩ :=
    D5.S3.FiniteGroups.GroupAlgebra.TwoDimensionalUnipotentNormalForm.exists_faithful_unipotent_basis
      hE hdim ρ hρ
  exact ⟨α, hα, (fun n => ⟨primalEquiv ρ b α h0 h1 n⟩),
    (fun n => ⟨contragredientEquiv ρ b α h0 h1 n⟩)⟩

end FaithfulModels

end SymmetricPowerTranslation
end D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
