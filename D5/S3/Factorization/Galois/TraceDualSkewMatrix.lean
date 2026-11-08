/- GID: D5/S3/Factorization/Galois/TraceDualSkewMatrix
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/TraceDualSkewMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-dual coordinates identify an arbitrary semilinear Galois skew algebra with endomorphisms and ordinary matrices over its invariant algebra. -/

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Equiv.Opposite
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.SkewMonoidAlgebra.Lift
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Trace.Basic

noncomputable section

open scoped BigOperators
open MulOpposite

namespace D5.S3.Factorization.Galois.TraceDualSkewMatrix

universe uk uF uA uI

variable (k : Type uk) (F : Type uF) [Field k] [Field F] [Algebra k F]
  [FiniteDimensional k F] [IsGalois k F]

local notation "Γ" => F ≃ₐ[k] F

section Orthogonality

variable {I : Type uI} [Fintype I] [DecidableEq I] (b : Module.Basis I k F)

/-- The only field calculation: a rectangular left inverse is also a right inverse.
This is private glue consumed by the arbitrary-A coefficient inverse below. -/
private theorem automorphism_orthogonality (h g : Γ) :
    (∑ i, h (b i) * g (b.traceDual i)) = if h = g then 1 else 0 := by
  classical
  let P : Matrix Γ I F := fun g i => g (b i)
  let Q : Matrix I Γ F := fun i g => g (b.traceDual i)
  have hQP : Q * P = 1 := by
    ext i j
    change (∑ g : Γ, g (b.traceDual i) * g (b j)) = (1 : Matrix I I F) i j
    simp_rw [← map_mul]
    rw [← Algebra.trace_eq_sum_automorphisms]
    simp [b.trace_traceDual_mul, Matrix.one_apply, eq_comm]
  have hcard : Fintype.card I = Fintype.card Γ := by
    calc
      Fintype.card I = Module.finrank k F := (Module.finrank_eq_card_basis b).symm
      _ = Nat.card Γ := (IsGalois.card_aut_eq_finrank k F).symm
      _ = Fintype.card Γ := Fintype.card_eq_nat_card.symm
  let e : I ≃ Γ := (Fintype.card_eq.mp hcard).some
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp hQP
  simpa only [Matrix.mul_apply, P, Q, Matrix.one_apply] using
    congrArg (fun M : Matrix Γ Γ F => M h g) hPQ

end Orthogonality

variable (A : Type uA) [Ring A] [Algebra F A]
  [Algebra k A] [IsScalarTower k F A]
  [MulSemiringAction Γ A] [SMulDistribClass Γ F A]

/- The k-algebra structure on A can always be supplied by
   Algebra.restrictScalars k F A, with IsScalarTower.restrictScalars k F A.
   SMulDistribClass is actual semilinearity, not an effective-descent assumption. -/

private instance actionCommutesBase : SMulCommClass Γ k A where
  smul_comm g r x := by
    rw [← algebraMap_smul F r x, smul_distrib_smul]
    change g (algebraMap k F r) • (g • x) = r • (g • x)
    rw [g.commutes, algebraMap_smul]

/-- The fixed algebra, with no commutativity or nontriviality assumption on A. -/
def invariants : Subalgebra k A where
  carrier := {x | ∀ g : Γ, g • x = x}
  zero_mem' := fun g => smul_zero g
  one_mem' := fun g => smul_one g
  add_mem' := by
    intro x y hx hy g
    rw [smul_add, hx g, hy g]
  mul_mem' := by
    intro x y hx hy g
    rw [smul_mul', hx g, hy g]
  algebraMap_mem' := fun r g => smul_algebraMap g r

local notation "C" => ↥(invariants k F A)

@[simp] theorem invariant_fixed (c : C) (g : Γ) : g • (c : A) = c := c.property g

/-- Restrict the existing right regular A-module along C → A. -/
instance rightModule : Module Cᵐᵒᵖ A :=
  Module.compHom A (RingHom.op (invariants k F A).val.toRingHom)

@[simp] theorem right_smul (c : Cᵐᵒᵖ) (x : A) : c • x = x * (unop c : A) := rfl

instance rightTower : IsScalarTower k Cᵐᵒᵖ A where
  smul_assoc r c x := by
    change x * ((r • unop c : C) : A) = r • (x * (unop c : A))
    change x * (algebraMap k A r * (unop c : A)) =
      algebraMap k A r * (x * (unop c : A))
    rw [← mul_assoc, ← Algebra.commutes r x, mul_assoc]

private theorem sigma_scalar (g : Γ) (z : F) :
    g • algebraMap F A z = algebraMap F A (g z) :=
  (algebraMap.smul' g z A).symm

/-- Coefficients act by left multiplication, on the right C-module. -/
private def coefficientAction : A →ₐ[k] Module.End Cᵐᵒᵖ A := by
  letI : SMulCommClass A Cᵐᵒᵖ A := ⟨fun a c x => by
    change a * (x * (unop c : A)) = (a * x) * (unop c : A)
    exact (mul_assoc a x (unop c : A)).symm⟩
  exact Algebra.lsmul k Cᵐᵒᵖ A

private def groupAction : Γ →* Module.End Cᵐᵒᵖ A where
  toFun g :=
    { toFun := fun x => g • x
      map_add' := fun x y => smul_add g x y
      map_smul' := fun c x => by
        change g • (x * (unop c : A)) = (g • x) * (unop c : A)
        rw [smul_mul', invariant_fixed] }
  map_one' := by ext x; exact one_smul Γ x
  map_mul' g h := by ext x; exact mul_smul g h x

/-- The basis-independent skew action. Its multiplicativity is Mathlib's liftNCAlgHom. -/
def Phi : SkewMonoidAlgebra A Γ →ₐ[k] Module.End Cᵐᵒᵖ A :=
  SkewMonoidAlgebra.liftNCAlgHom (coefficientAction k F A) (groupAction k F A)
    (by
      intro a g
      ext x
      exact (smul_mul' g a x).symm)

@[simp] theorem Phi_single (g : Γ) (a x : A) :
    Phi k F A (SkewMonoidAlgebra.single g a) x = a * (g • x) := by
  change SkewMonoidAlgebra.liftNC
    ((coefficientAction k F A).toRingHom.toAddMonoidHom) (groupAction k F A)
    (SkewMonoidAlgebra.single g a) x = _
  rw [SkewMonoidAlgebra.liftNC_single]
  rfl

theorem Phi_apply (r : SkewMonoidAlgebra A Γ) (x : A) :
    Phi k F A r x = ∑ g : Γ, r.coeff g * (g • x) := by
  classical
  induction r using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g a => simp [Phi_single, Finsupp.single_apply]
  | add r s hr hs =>
    simp only [map_add, LinearMap.add_apply, SkewMonoidAlgebra.coeff_add,
      Finsupp.add_apply, add_mul, Finset.sum_add_distrib, hr, hs]

section Coordinates

variable {I : Type uI} [Fintype I] [DecidableEq I] (b : Module.Basis I k F)

def u (i : I) : A := algebraMap F A (b i)
def v (i : I) : A := algebraMap F A (b.traceDual i)

private theorem coefficient_orthogonality (h g : Γ) :
    (∑ i, (h • u k F A b i) * (g • v k F A b i)) =
      if h = g then 1 else 0 := by
  have H := congrArg (algebraMap F A) (automorphism_orthogonality k F b h g)
  simpa [u, v, sigma_scalar, map_sum, map_mul] using H

private theorem coefficient_orthogonality_one (g : Γ) :
    (∑ i, u k F A b i * (g • v k F A b i)) = if g = 1 then 1 else 0 := by
  simpa only [one_smul, eq_comm] using coefficient_orthogonality k F A b 1 g

/-- d_i(x) as an A-valued additive map, before restricting its range to C. -/
def dRaw (i : I) : A →+ A where
  toFun x := ∑ g : Γ, g • (v k F A b i * x)
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, smul_add, Finset.sum_add_distrib]

theorem dRaw_fixed (i : I) (x : A) (h : Γ) :
    h • dRaw k F A b i x = dRaw k F A b i x := by
  change h • (∑ g : Γ, g • (v k F A b i * x)) = _
  simp only [Finset.smul_sum, ← mul_smul]
  exact (Equiv.mulLeft h).sum_comp (fun g : Γ => g • (v k F A b i * x))

def d (i : I) (x : A) : C := ⟨dRaw k F A b i x, dRaw_fixed k F A b i x⟩

@[simp] theorem coe_d (i : I) (x : A) :
    (d k F A b i x : A) = ∑ g : Γ, g • (v k F A b i * x) := rfl

private theorem dRaw_mul (i : I) (x : A) (c : C) :
    dRaw k F A b i (x * c) = dRaw k F A b i x * c := by
  change (∑ g : Γ, g • (v k F A b i * (x * c))) =
    (∑ g : Γ, g • (v k F A b i * x)) * c
  simp only [← mul_assoc, smul_mul', invariant_fixed, Finset.sum_mul]

/-- Right C-linearity is expressed as left Cᵐᵒᵖ-linearity. -/
def dLinear (i : I) : A →ₗ[Cᵐᵒᵖ] C where
  toFun := d k F A b i
  map_add' x y := Subtype.ext ((dRaw k F A b i).map_add x y)
  map_smul' c x := by
    apply Subtype.ext
    exact dRaw_mul k F A b i x (unop c)

theorem d_sum {J : Type*} (s : Finset J) (f : J → A) (i : I) :
    d k F A b i (∑ j ∈ s, f j) = ∑ j ∈ s, d k F A b i (f j) :=
  map_sum (dLinear k F A b i) f s

private theorem dRaw_basis_mul (j i : I) (c : C) :
    dRaw k F A b j (u k F A b i * c) = if j = i then (c : A) else 0 := by
  classical
  calc
    dRaw k F A b j (u k F A b i * c) =
        ∑ g : Γ, algebraMap F A (g (b.traceDual j * b i)) * (c : A) := by
      apply Finset.sum_congr rfl
      intro g hg
      change g • (algebraMap F A (b.traceDual j) * (algebraMap F A (b i) * c)) = _
      rw [← mul_assoc, ← map_mul, smul_mul', sigma_scalar, invariant_fixed]
    _ = algebraMap F A (algebraMap k F (Algebra.trace k F (b.traceDual j * b i))) * c := by
      rw [← Finset.sum_mul, ← map_sum, ← Algebra.trace_eq_sum_automorphisms]
    _ = if j = i then (c : A) else 0 := by
      rw [b.trace_traceDual_mul]
      by_cases h : j = i <;> simp [h, eq_comm]

theorem d_basis_mul (j i : I) (c : C) :
    d k F A b j (u k F A b i * c) = if j = i then c else 0 := by
  apply Subtype.ext
  by_cases h : j = i <;> simpa [d, h] using dRaw_basis_mul k F A b j i c

/-- The invariant-coordinate reconstruction, derived from O(1,g). -/
theorem reconstruct (x : A) :
    (∑ i, u k F A b i * (d k F A b i x : A)) = x := by
  classical
  calc
    (∑ i, u k F A b i * (d k F A b i x : A)) =
        ∑ g : Γ, (∑ i, u k F A b i * (g • v k F A b i)) * (g • x) := by
      simp only [coe_d, smul_mul', Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = x := by
      simp_rw [coefficient_orthogonality_one]
      simp

/-- Effective right-module coordinates, with both inverse identities proved above. -/
def coordinates : A ≃ₗ[Cᵐᵒᵖ] (I → C) where
  toFun x i := d k F A b i x
  invFun c := ∑ i, u k F A b i * (c i : A)
  left_inv := reconstruct k F A b
  right_inv c := by
    funext j
    change d k F A b j (∑ i, u k F A b i * (c i : A)) = c j
    rw [d_sum]
    simp_rw [d_basis_mul]
    simp
  map_add' x y := by
    funext i
    exact (dLinear k F A b i).map_add x y
  map_smul' c x := by
    funext i
    exact (dLinear k F A b i).map_smul c x

/-- A genuine basis, using Mathlib's general coordinate-to-basis constructor. -/
def rightBasis : Module.Basis I Cᵐᵒᵖ A :=
  Module.Basis.ofEquivFun ((coordinates k F A b).trans
    (LinearEquiv.piCongrRight (fun _ : I =>
      MulOpposite.opLinearEquiv Cᵐᵒᵖ (M := C))))

/- Pointwise op is linear here: op(c*r) = op(r)*op(c). Thus it takes
   C with its right regular action to Cᵐᵒᵖ with its left regular action. -/

theorem rightBasis_apply (i : I) : rightBasis k F A b i = u k F A b i := by
  classical
  rw [rightBasis, Module.Basis.coe_ofEquivFun]
  change (∑ l, u k F A b l *
    ((unop (Pi.single i (1 : Cᵐᵒᵖ) l) : C) : A)) = u k F A b i
  simp [Pi.single_apply]

private theorem end_reconstruct (T : Module.End Cᵐᵒᵖ A) (x : A) :
    (∑ i, T (u k F A b i) * (d k F A b i x : A)) = T x := by
  calc
    _ = T (∑ i, u k F A b i * (d k F A b i x : A)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (T.map_smul (op (d k F A b i x)) (u k F A b i)).symm
    _ = T x := congrArg T (reconstruct k F A b x)

/-- The explicit inverse coefficient, preserving the noncommutative order. -/
def PsiCoeff (T : Module.End Cᵐᵒᵖ A) (g : Γ) : A :=
  ∑ i, T (u k F A b i) * (g • v k F A b i)

def Psi (T : Module.End Cᵐᵒᵖ A) : SkewMonoidAlgebra A Γ :=
  SkewMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (PsiCoeff k F A b T))

@[simp] theorem Psi_coeff (T : Module.End Cᵐᵒᵖ A) (g : Γ) :
    (Psi k F A b T).coeff g = ∑ i, T (u k F A b i) * (g • v k F A b i) := rfl

theorem Phi_Psi (T : Module.End Cᵐᵒᵖ A) : Phi k F A (Psi k F A b T) = T := by
  classical
  ext x
  rw [Phi_apply]
  simp_rw [Psi_coeff]
  calc
    (∑ g : Γ, (∑ i, T (u k F A b i) * (g • v k F A b i)) * (g • x)) =
        ∑ i, T (u k F A b i) * (d k F A b i x : A) := by
      simp only [coe_d, smul_mul', Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    _ = T x := end_reconstruct k F A b T x

theorem Psi_Phi (r : SkewMonoidAlgebra A Γ) : Psi k F A b (Phi k F A r) = r := by
  classical
  apply SkewMonoidAlgebra.coeff_injective
  ext g
  rw [Psi_coeff]
  simp_rw [Phi_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ h : Γ, ∑ i, (r.coeff h * (h • u k F A b i)) * (g • v k F A b i)) =
        ∑ h : Γ, r.coeff h * (∑ i, (h • u k F A b i) * (g • v k F A b i)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = r.coeff g := by
      simp_rw [coefficient_orthogonality]
      simp

end Coordinates

/-- The canonical action equivalence. A chosen field basis supplies the proof/inverse;
the forward map is exactly Phi and contains no basis choice. -/
def skewEndEquiv : SkewMonoidAlgebra A Γ ≃ₐ[k] Module.End Cᵐᵒᵖ A where
  __ := Phi k F A
  invFun := Psi k F A (Module.finBasis k F)
  left_inv := Psi_Phi k F A (Module.finBasis k F)
  right_inv := Phi_Psi k F A (Module.finBasis k F)

@[simp] theorem skewEndEquiv_apply (r : SkewMonoidAlgebra A Γ) :
    skewEndEquiv k F A r = Phi k F A r := rfl

section Matrix

variable {I : Type uI} [Fintype I] [DecidableEq I] (b : Module.Basis I k F)

theorem skewEndEquiv_symm_coeff (T : Module.End Cᵐᵒᵖ A) (g : Γ) :
    ((skewEndEquiv k F A).symm T).coeff g =
      ∑ i, T (u k F A b i) * (g • v k F A b i) := by
  have H := Psi_Phi k F A b ((skewEndEquiv k F A).symm T)
  rw [← skewEndEquiv_apply, AlgEquiv.apply_symm_apply] at H
  exact (congrArg (fun r : SkewMonoidAlgebra A Γ => r.coeff g) H).symm

/-- Ordinary matrices over C, via End(right C on C) ≃ C. -/
def endMatrixEquiv : Module.End Cᵐᵒᵖ A ≃ₐ[k] Matrix I I C :=
  ((coordinates k F A b).conjAlgEquiv k).trans
    ((endVecAlgEquivMatrixEnd I k Cᵐᵒᵖ C).trans
      (AlgEquiv.moduleEndSelfOp (A := C) k).symm.mapMatrix)

/-- Columns are the invariant coordinates of images of u_i. -/
theorem endMatrixEquiv_apply (T : Module.End Cᵐᵒᵖ A) (j i : I) :
    endMatrixEquiv k F A b T j i = d k F A b j (T (u k F A b i)) := by
  change d k F A b j (T ((coordinates k F A b).symm (Pi.single i 1))) = _
  have hb : (coordinates k F A b).symm (Pi.single i 1) = rightBasis k F A b i := by
    rw [rightBasis, Module.Basis.coe_ofEquivFun]
    change (∑ l, u k F A b l * ((Pi.single i (1 : C) l : C) : A)) =
      ∑ l, u k F A b l * ((unop (Pi.single i (1 : Cᵐᵒᵖ) l) : C) : A)
    simp [Pi.single_apply]
  rw [hb, rightBasis_apply]

/-- The basis-dependent matrix presentation of the arbitrary-coefficient skew algebra. -/
def skewMatrixEquiv : SkewMonoidAlgebra A Γ ≃ₐ[k] Matrix I I C :=
  (skewEndEquiv k F A).trans (endMatrixEquiv k F A b)

theorem skewMatrixEquiv_apply (r : SkewMonoidAlgebra A Γ) (j i : I) :
    skewMatrixEquiv k F A b r j i =
      d k F A b j (∑ g : Γ, r.coeff g * (g • u k F A b i)) := by
  rw [skewMatrixEquiv, AlgEquiv.trans_apply, endMatrixEquiv_apply,
    skewEndEquiv_apply, Phi_apply]

end Matrix

end D5.S3.Factorization.Galois.TraceDualSkewMatrix
