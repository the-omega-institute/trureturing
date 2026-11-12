/-
SOURCE CANDIDATE, UNCOMPILED AND UNACCEPTED.
Actual finite-support flattening and the literal iterate-to-product associator.
Every product below is the pinned UniversalField.targetModule / P.
There is no representing equivalence or input bifunctor in this file.
No primitive three/five-channel field, unit field identity, or coherence
consumer is assumed. Those remain separate parent work.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductMultiplicity
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleAssociator

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes (sectorModule sectorModule_mode)
open ActualWeakModuleUniversalField (P PairSector targetModule)
open ActualWeakModuleProductMultiplicity
open LatticeChargedQuotientScalar (carry)

universe u v w x y z t
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section FiniteAlgebra
variable {ι : Type t} {V : Type u} {H : Type v} {Z : Type w} {T : Type x}
variable {W : ι → Type y}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup Z] [Module ℂ Z] [AddCommGroup T] [Module ℂ T]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Direct-sum elimination in the middle slot of a trilinear map. -/
private def sumEval (f : ∀ i, V →ₗ[ℂ] W i →ₗ[ℂ] Z →ₗ[ℂ] T) :
    V →ₗ[ℂ] (⨁ i, W i) →ₗ[ℂ] Z →ₗ[ℂ] T where
  toFun v := DirectSum.toModule ℂ ι (Z →ₗ[ℂ] T) (fun i => f i v)
  map_add' v v' := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply,DirectSum.toModule_lof,map_add,LinearMap.add_apply]
  map_smul' a v := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply,DirectSum.toModule_lof,map_smul,
      LinearMap.smul_apply,RingHom.id_apply]

private def sumMiddle (f : ∀ i, V →ₗ[ℂ] W i →ₗ[ℂ] Z →ₗ[ℂ] T)
    (mu : H →ₗ[ℂ] ⨁ i, W i) : V →ₗ[ℂ] H →ₗ[ℂ] Z →ₗ[ℂ] T where
  toFun v := (sumEval f v).comp mu
  map_add' v v' := by rw [map_add,LinearMap.add_comp]
  map_smul' a v := by simp only [map_smul,LinearMap.smul_comp,RingHom.id_apply]

/-- This uses the same linear uncurry API as the pinned U72 construction. -/
private def liftThree (f : V →ₗ[ℂ] H →ₗ[ℂ] Z →ₗ[ℂ] T) :
    V ⊗[ℂ] (H ⊗[ℂ] Z) →ₗ[ℂ] T :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) H Z T).comp f)

@[simp] private theorem liftThree_tmul (f : V →ₗ[ℂ] H →ₗ[ℂ] Z →ₗ[ℂ] T)
    (v : V) (h : H) (z : Z) :
    liftThree f (v ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] z)) = f v h z := by
  simp [liftThree]

private theorem finite_sum_closed {N : Type z} [AddCommGroup N]
    (Q : N → Prop) (h0 : Q 0) (ha : ∀ a b, Q a → Q b → Q (a+b))
    {κ : Type t} (s : Finset κ) (f : κ → N) (hf : ∀ i ∈ s, Q (f i)) :
    Q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ha _ _ (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end FiniteAlgebra

section ActualProducts
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

abbrev LeftP := P (targetModule A B) C
abbrev RightP := P A (targetModule B C)
abbrev Triple (D : LatticeData) := Discriminant D × Discriminant D × Discriminant D
abbrev LeftMultiplicity (i : Triple D) :=
  (Multiplicity A i.1 ⊗[ℂ] Multiplicity B i.2.1) ⊗[ℂ] Multiplicity C i.2.2
abbrev RightMultiplicity (i : Triple D) :=
  Multiplicity A i.1 ⊗[ℂ] (Multiplicity B i.2.1 ⊗[ℂ] Multiplicity C i.2.2)
abbrev LeftSector (i : Triple D) := Carrier D ⊗[ℂ] LeftMultiplicity A B C i
abbrev RightSector (i : Triple D) := Carrier D ⊗[ℂ] RightMultiplicity A B C i
abbrev LeftTriple := ⨁ i : Triple D, LeftSector A B C i
abbrev RightTriple := ⨁ i : Triple D, RightSector A B C i

/-- Both triples use the SAME original representative, with parentheses fixed. -/
def leftTripleModule : FullJacobiLatticeModule D (LeftTriple A B C) :=
  directSumModule (fun i : Triple D =>
    tensorModule (sectorModule D (representative D ((i.1+i.2.1)+i.2.2)))
      (LeftMultiplicity A B C i))
def rightTripleModule : FullJacobiLatticeModule D (RightTriple A B C) :=
  directSumModule (fun i : Triple D =>
    tensorModule (sectorModule D (representative D ((i.1+i.2.1)+i.2.2)))
      (RightMultiplicity A B C i))

/-- Elementary maps linear in the ORIGINAL full carrier state. -/
def leftElementary (c d e : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (z : Multiplicity C e) :
    Carrier D →ₗ[ℂ] LeftP A B C :=
  (DirectSum.lof ℂ _ (PairSector (targetModule A B) C) (c+d,e)).comp
    ((TensorProduct.mk ℂ (Carrier D) _).flip (j A B hD c d w ⊗ₜ[ℂ] z))

def rightElementary (c d e : Discriminant D)
    (x : Multiplicity A c) (w : PairMultiplicity B C (d,e)) :
    Carrier D →ₗ[ℂ] RightP A B C :=
  (DirectSum.lof ℂ _ (PairSector A (targetModule B C)) (c,d+e)).comp
    ((TensorProduct.mk ℂ (Carrier D) _).flip (x ⊗ₜ[ℂ] j B C hD d e w))

abbrev E_L (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :=
  leftElementary A B C hD c d e (x ⊗ₜ[ℂ] y) z v
abbrev E_R (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :=
  rightElementary A B C hD c d e x (y ⊗ₜ[ℂ] z) v

/-- Visible inner epsilon(-p,p)^-1, without changing the subtype j. -/
theorem inner_left_normalization (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) :
    (j A B hD c d w).val.val =
      (epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ •
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (Finsupp.single (-carry D hD c d) (1 : Oscillator D) ⊗ₜ[ℂ] w) := by
  rw [j_val,ground_single,← TensorProduct.smul_tmul',map_smul]

/-- Visible inner epsilon(-q,q)^-1 on the right. -/
theorem inner_right_normalization (d e : Discriminant D)
    (w : PairMultiplicity B C (d,e)) :
    (j B C hD d e w).val.val =
      (epsilon D (-carry D hD d e) (carry D hD d e))⁻¹ •
      DirectSum.lof ℂ _ (PairSector B C) (d,e)
        (Finsupp.single (-carry D hD d e) (1 : Oscillator D) ⊗ₜ[ℂ] w) := by
  rw [j_val,ground_single,← TensorProduct.smul_tmul',map_smul]

private def leftSeed (h e : Discriminant D) (i : Fiber (D := D) h) :
    Carrier D →ₗ[ℂ] PairMultiplicity A B i.val →ₗ[ℂ] Multiplicity C e →ₗ[ℂ]
      LeftTriple A B C where
  toFun v :=
    { toFun w :=
        { toFun z := DirectSum.lof ℂ _ (LeftSector A B C) (i.val.1,i.val.2,e)
            (transport D (representative D (h+e)) (carry D hD h e) v ⊗ₜ[ℂ]
              (w ⊗ₜ[ℂ] z))
          map_add' z z' := by simp only [TensorProduct.tmul_add,map_add,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
          map_smul' a z := by simp only [TensorProduct.tmul_smul,map_smul,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl }
      map_add' w w' := by
        apply LinearMap.ext; intro z
        simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,LinearMap.add_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
      map_smul' a w := by
        apply LinearMap.ext; intro z
        simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,map_smul,LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl }
  map_add' v v' := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro z
    simp only [map_add,TensorProduct.add_tmul,LinearMap.add_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
  map_smul' a v := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro z
    simp only [map_smul,← TensorProduct.smul_tmul',LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl

private def rightSeed (c h : Discriminant D) (i : Fiber (D := D) h) :
    Carrier D →ₗ[ℂ] PairMultiplicity B C i.val →ₗ[ℂ] Multiplicity A c →ₗ[ℂ]
      RightTriple A B C where
  toFun v :=
    { toFun w :=
        { toFun x := DirectSum.lof ℂ _ (RightSector A B C) (c,i.val.1,i.val.2)
            (transport D (representative D (c+h)) (carry D hD c h) v ⊗ₜ[ℂ]
              (x ⊗ₜ[ℂ] w))
          map_add' x x' := by simp only [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
          map_smul' a x := by
            simp only [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,map_smul,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl }
      map_add' w w' := by
        apply LinearMap.ext; intro x
        simp only [TensorProduct.tmul_add,map_add,LinearMap.add_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
      map_smul' a w := by
        apply LinearMap.ext; intro x
        simp only [TensorProduct.tmul_smul,map_smul,LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl }
  map_add' v v' := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    simp only [map_add,TensorProduct.add_tmul,LinearMap.add_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
  map_smul' a v := by
    apply LinearMap.ext; intro w
    apply LinearMap.ext; intro x
    simp only [map_smul,← TensorProduct.smul_tmul',LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl

private def leftBlock (h e : Discriminant D) :
    PairSector (targetModule A B) C (h,e) →ₗ[ℂ] LeftTriple A B C := by
  letI : AddCommGroup (Multiplicity (targetModule A B) h) :=
    Module.addCommMonoidToAddCommGroup ℂ
  exact liftThree (H := Multiplicity (targetModule A B) h)
    (sumMiddle (H := Multiplicity (targetModule A B) h)
      (leftSeed A B C hD h e) (mu A B hD h))

private def rightBlock (c h : Discriminant D) :
    PairSector A (targetModule B C) (c,h) →ₗ[ℂ] RightTriple A B C := by
  letI : AddCommGroup (Multiplicity (targetModule B C) h) :=
    Module.addCommMonoidToAddCommGroup ℂ
  exact liftThree (H := Multiplicity A c) (Z := Multiplicity (targetModule B C) h)
    { toFun v := (sumMiddle (H := Multiplicity (targetModule B C) h)
        (rightSeed A B C hD c h) (mu B C hD h) v).flip
      map_add' v v' := by
        apply LinearMap.ext; intro x
        apply LinearMap.ext; intro w
        simp only [map_add,LinearMap.add_apply,LinearMap.flip_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl
      map_smul' a v := by
        apply LinearMap.ext; intro x
        apply LinearMap.ext; intro w
        simp only [map_smul,LinearMap.smul_apply,LinearMap.flip_apply,RingHom.id_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk] <;> rfl }

/-- Genuine forward maps, defined before proving their inverse laws. -/
def flattenLeft : LeftP A B C →ₗ[ℂ] LeftTriple A B C :=
  DirectSum.toModule ℂ _ _ (fun he => leftBlock A B C hD he.1 he.2)
def flattenRight : RightP A B C →ₗ[ℂ] RightTriple A B C :=
  DirectSum.toModule ℂ _ _ (fun ch => rightBlock A B C hD ch.1 ch.2)

/-- Inverse: actual inverse outer transport and actual inner j. -/
def unflattenLeft : LeftTriple A B C →ₗ[ℂ] LeftP A B C :=
  DirectSum.toModule ℂ _ _ (fun i : Triple D =>
    (DirectSum.lof ℂ _ (PairSector (targetModule A B) C) (i.1+i.2.1,i.2.2)).comp
      (TensorProduct.map
        (transportInverse D (representative D ((i.1+i.2.1)+i.2.2))
          (carry D hD (i.1+i.2.1) i.2.2))
        (TensorProduct.map (j A B hD i.1 i.2.1) LinearMap.id)))

def unflattenRight : RightTriple A B C →ₗ[ℂ] RightP A B C :=
  DirectSum.toModule ℂ _ _ (fun i : Triple D =>
    (DirectSum.lof ℂ _ (PairSector A (targetModule B C)) (i.1,i.2.1+i.2.2)).comp
      (TensorProduct.map
        (transportInverse D (representative D (i.1+(i.2.1+i.2.2)))
          (carry D hD i.1 (i.2.1+i.2.2)))
        (TensorProduct.map LinearMap.id (j B C hD i.2.1 i.2.2))))

@[simp] theorem flattenLeft_elementary (c d e : Discriminant D) (v : Carrier D)
    (w : PairMultiplicity A B (c,d)) (z : Multiplicity C e) :
    flattenLeft A B C hD (leftElementary A B C hD c d e w z v) =
      DirectSum.lof ℂ _ (LeftSector A B C) (c,d,e)
        (transport D (representative D ((c+d)+e)) (carry D hD (c+d) e) v ⊗ₜ[ℂ]
          (w ⊗ₜ[ℂ] z)) := by
  have hm := mu_jAt A B hD (c+d) ⟨(c,d),rfl⟩ w
  change mu A B hD (c+d) (j A B hD c d w) = _ at hm
  simp only [leftElementary, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, flattenLeft, DirectSum.toModule_lof, leftBlock,
    liftThree_tmul]
  change (sumEval (leftSeed A B C hD (c+d) e) v
    (mu A B hD (c+d) (j A B hD c d w))) z = _
  rw [hm]
  exact congrArg (fun k : Multiplicity C e →ₗ[ℂ] LeftTriple A B C => k z)
    (DirectSum.toModule_lof ℂ
      (φ := fun i => leftSeed A B C hD (c+d) e i v) ⟨(c,d), rfl⟩ w)

@[simp] theorem flattenRight_elementary (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (w : PairMultiplicity B C (d,e)) :
    flattenRight A B C hD (rightElementary A B C hD c d e x w v) =
      DirectSum.lof ℂ _ (RightSector A B C) (c,d,e)
        (transport D (representative D (c+(d+e))) (carry D hD c (d+e)) v ⊗ₜ[ℂ]
          (x ⊗ₜ[ℂ] w)) := by
  have hm := mu_jAt B C hD (d+e) ⟨(d,e),rfl⟩ w
  change mu B C hD (d+e) (j B C hD d e w) = _ at hm
  simp only [rightElementary, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, flattenRight, DirectSum.toModule_lof, rightBlock,
    liftThree_tmul]
  change (sumEval (rightSeed A B C hD c (d+e)) v
    (mu B C hD (d+e) (j B C hD d e w))) x = _
  rw [hm]
  exact congrArg (fun k : Multiplicity A c →ₗ[ℂ] RightTriple A B C => k x)
    (DirectSum.toModule_lof ℂ
      (φ := fun i => rightSeed A B C hD c (d+e) i v) ⟨(d,e), rfl⟩ w)

@[simp] theorem unflattenLeft_elementary (c d e : Discriminant D) (v : Carrier D)
    (w : PairMultiplicity A B (c,d)) (z : Multiplicity C e) :
    unflattenLeft A B C hD (DirectSum.lof ℂ _ (LeftSector A B C) (c,d,e)
      (v ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z))) =
      leftElementary A B C hD c d e w z
        (transportInverse D (representative D ((c+d)+e)) (carry D hD (c+d) e) v) := by
  simp only [unflattenLeft,DirectSum.toModule_lof,LinearMap.comp_apply,
    TensorProduct.map_tmul,LinearMap.id_apply,leftElementary,LinearMap.flip_apply,
    TensorProduct.mk_apply]

@[simp] theorem unflattenRight_elementary (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (w : PairMultiplicity B C (d,e)) :
    unflattenRight A B C hD (DirectSum.lof ℂ _ (RightSector A B C) (c,d,e)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] w))) =
      rightElementary A B C hD c d e x w
        (transportInverse D (representative D (c+(d+e))) (carry D hD c (d+e)) v) := by
  simp only [unflattenRight,DirectSum.toModule_lof,LinearMap.comp_apply,
    TensorProduct.map_tmul,LinearMap.id_apply,rightElementary,LinearMap.flip_apply,
    TensorProduct.mk_apply]

/-- Finite-support generation, including EVERY tensor zero branch. -/
theorem left_induction (Q : LeftP A B C → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ c d e v w z, Q (leftElementary A B C hD c d e w z v))
    (x : LeftP A B C) : Q x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add a b h1 h2 => exact ha a b h1 h2
  | of i x =>
    rcases i with ⟨h,e⟩
    change Q (DirectSum.lof ℂ _ (PairSector (targetModule A B) C) (h,e) x)
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using h0
    | add x y hx hy => simpa only [map_add] using ha _ _ hx hy
    | tmul v w =>
      induction w using TensorProduct.induction_on with
      | zero => simpa only [TensorProduct.tmul_zero,map_zero] using h0
      | add x y hx hy => simpa only [TensorProduct.tmul_add,map_add] using ha _ _ hx hy
      | tmul z t =>
        rw [← nu_mu A B hD h z,nu_expansion]
        simp only [TensorProduct.sum_tmul,TensorProduct.tmul_sum,map_sum]
        apply finite_sum_closed Q h0 ha
        intro i hi
        rcases i with ⟨⟨c,d⟩,hcd⟩
        subst h
        exact he c d e v _ t

theorem right_induction (Q : RightP A B C → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ c d e v x w, Q (rightElementary A B C hD c d e x w v))
    (x : RightP A B C) : Q x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add a b h1 h2 => exact ha a b h1 h2
  | of i x =>
    rcases i with ⟨c,h⟩
    change Q (DirectSum.lof ℂ _ (PairSector A (targetModule B C)) (c,h) x)
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using h0
    | add x y hx hy => simpa only [map_add] using ha _ _ hx hy
    | tmul v w =>
      induction w using TensorProduct.induction_on with
      | zero => simpa only [TensorProduct.tmul_zero,map_zero] using h0
      | add x y hx hy => simpa only [TensorProduct.tmul_add,map_add] using ha _ _ hx hy
      | tmul t z =>
        rw [← nu_mu B C hD h z,nu_expansion]
        simp only [TensorProduct.tmul_sum,map_sum]
        apply finite_sum_closed Q h0 ha
        intro i hi
        rcases i with ⟨⟨d,e⟩,hde⟩
        subst h
        exact he c d e v t _

/-- Generation by the literal E_L with three ORIGINAL multiplicity vectors. -/
theorem E_L_induction (Q : LeftP A B C → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ c d e v x y z, Q (E_L A B C hD c d e v x y z))
    (x : LeftP A B C) : Q x := by
  apply left_induction A B C hD Q h0 ha ?_ x
  intro c d e v w z
  induction w using TensorProduct.induction_on with
  | zero => simpa [leftElementary] using h0
  | add w w' hw hw' =>
    simpa [leftElementary,TensorProduct.add_tmul,TensorProduct.tmul_add] using ha _ _ hw hw'
  | tmul x y => exact he c d e v x y z

theorem E_R_induction (Q : RightP A B C → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ c d e v x y z, Q (E_R A B C hD c d e v x y z))
    (x : RightP A B C) : Q x := by
  apply right_induction A B C hD Q h0 ha ?_ x
  intro c d e v x w
  induction w using TensorProduct.induction_on with
  | zero => simpa [rightElementary] using h0
  | add w w' hw hw' =>
    simpa [rightElementary,TensorProduct.tmul_add] using ha _ _ hw hw'
  | tmul y z => exact he c d e v x y z

theorem unflatten_flatten_left (x : LeftP A B C) :
    unflattenLeft A B C hD (flattenLeft A B C hD x) = x := by
  apply left_induction A B C hD
    (fun x => unflattenLeft A B C hD (flattenLeft A B C hD x) = x)
    (by simp) (fun a b ha hb => by simp only [map_add,ha,hb]) ?_ x
  intro c d e v w z
  rw [flattenLeft_elementary,unflattenLeft_elementary]
  exact congrArg (leftElementary A B C hD c d e w z)
    ((transportLinearEquiv D _ _).symm_apply_apply v)

theorem unflatten_flatten_right (x : RightP A B C) :
    unflattenRight A B C hD (flattenRight A B C hD x) = x := by
  apply right_induction A B C hD
    (fun x => unflattenRight A B C hD (flattenRight A B C hD x) = x)
    (by simp) (fun a b ha hb => by simp only [map_add,ha,hb]) ?_ x
  intro c d e v w z
  rw [flattenRight_elementary,unflattenRight_elementary]
  exact congrArg (rightElementary A B C hD c d e w z)
    ((transportLinearEquiv D _ _).symm_apply_apply v)

theorem flatten_unflatten_left (x : LeftTriple A B C) :
    flattenLeft A B C hD (unflattenLeft A B C hD x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | of i x =>
    rcases i with ⟨c,d,e⟩
    change flattenLeft A B C hD (unflattenLeft A B C hD
      (DirectSum.lof ℂ _ (LeftSector A B C) (c,d,e) x)) = _
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul v w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,hx,hy]
      | tmul w z =>
        rw [unflattenLeft_elementary,flattenLeft_elementary]
        have ht := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
          (transportInverse_right D (representative D ((c+d)+e)) (carry D hD (c+d) e))
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at ht
        rw [ht]
        rfl

theorem flatten_unflatten_right (x : RightTriple A B C) :
    flattenRight A B C hD (unflattenRight A B C hD x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | of i x =>
    rcases i with ⟨c,d,e⟩
    change flattenRight A B C hD (unflattenRight A B C hD
      (DirectSum.lof ℂ _ (RightSector A B C) (c,d,e) x)) = _
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul v w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,hx,hy]
      | tmul x w =>
        rw [unflattenRight_elementary,flattenRight_elementary]
        have ht := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
          (transportInverse_right D (representative D (c+(d+e))) (carry D hD c (d+e)))
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at ht
        rw [ht]
        rfl

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- All-state modes on the actual elementary vectors. -/
theorem leftElementary_modes (c d e : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (z : Multiplicity C e)
    (a v : Carrier D) (m : ℤ) :
    mode (targetModule (targetModule A B) C) a m
      (leftElementary A B C hD c d e w z v) =
      leftElementary A B C hD c d e w z
        (mode (sectorModule D (representative D (c+d)+representative D e)) a m v) := by
  simpa only [leftElementary, ActualWeakModuleUniversalField.tag_apply,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    sectorModule_mode] using
    ActualWeakModuleUniversalField.target_action_tag (targetModule A B) C (c+d) e
      (j A B hD c d w) z a v m

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem rightElementary_modes (c d e : Discriminant D)
    (x : Multiplicity A c) (w : PairMultiplicity B C (d,e))
    (a v : Carrier D) (m : ℤ) :
    mode (targetModule A (targetModule B C)) a m
      (rightElementary A B C hD c d e x w v) =
      rightElementary A B C hD c d e x w
        (mode (sectorModule D (representative D c+representative D (d+e))) a m v) := by
  simpa only [rightElementary, ActualWeakModuleUniversalField.tag_apply,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    sectorModule_mode] using
    ActualWeakModuleUniversalField.target_action_tag A (targetModule B C) c (d+e)
      x (j B C hD d e w) a v m

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem flattenLeft_modes (a : Carrier D) (m : ℤ) (x : LeftP A B C) :
    flattenLeft A B C hD (mode (targetModule (targetModule A B) C) a m x) =
      mode (leftTripleModule A B C) a m (flattenLeft A B C hD x) := by
  apply left_induction A B C hD
    (fun x => flattenLeft A B C hD (mode (targetModule (targetModule A B) C) a m x) =
      mode (leftTripleModule A B C) a m (flattenLeft A B C hD x)) (by simp)
    (fun x y hx hy => by simp only [map_add,hx,hy]) ?_ x
  intro c d e v w z
  rw [leftElementary_modes,flattenLeft_elementary,flattenLeft_elementary]
  rw [leftTripleModule,directSumModule_mode,DirectSum.lmap_lof,
    tensorModule_mode,TensorProduct.map_tmul,LinearMap.id_apply]
  congr 2
  rw [sectorModule_mode,← pair_shift hD (c+d) e]
  exact transport_all_modes D _ _ a v m

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem flattenRight_modes (a : Carrier D) (m : ℤ) (x : RightP A B C) :
    flattenRight A B C hD (mode (targetModule A (targetModule B C)) a m x) =
      mode (rightTripleModule A B C) a m (flattenRight A B C hD x) := by
  apply right_induction A B C hD
    (fun x => flattenRight A B C hD (mode (targetModule A (targetModule B C)) a m x) =
      mode (rightTripleModule A B C) a m (flattenRight A B C hD x)) (by simp)
    (fun x y hx hy => by simp only [map_add,hx,hy]) ?_ x
  intro c d e v w z
  rw [rightElementary_modes,flattenRight_elementary,flattenRight_elementary]
  rw [rightTripleModule,directSumModule_mode,DirectSum.lmap_lof,
    tensorModule_mode,TensorProduct.map_tmul,LinearMap.id_apply]
  congr 2
  rw [add_assoc,sectorModule_mode,← pair_shift hD c (d+e)]
  exact transport_all_modes D _ _ a v m

def leftIso : ModuleIso (targetModule (targetModule A B) C) (leftTripleModule A B C) where
  linearEquiv :=
    { toLinearMap := flattenLeft A B C hD
      invFun := unflattenLeft A B C hD
      left_inv := unflatten_flatten_left A B C hD
      right_inv := flatten_unflatten_left A B C hD }
  intertwines := flattenLeft_modes A B C hD

def rightIso : ModuleIso (targetModule A (targetModule B C)) (rightTripleModule A B C) where
  linearEquiv :=
    { toLinearMap := flattenRight A B C hD
      invFun := unflattenRight A B C hD
      left_inv := unflatten_flatten_right A B C hD
      right_inv := flatten_unflatten_right A B C hD }
  intertwines := flattenRight_modes A B C hD

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- These readbacks cover every original vector, not just elementary tensors. -/
theorem unflattenLeft_modes (a : Carrier D) (m : ℤ) (x : LeftTriple A B C) :
    unflattenLeft A B C hD (mode (leftTripleModule A B C) a m x) =
      mode (targetModule (targetModule A B) C) a m (unflattenLeft A B C hD x) :=
by
  have hm := flattenLeft_modes A B C hD a m (unflattenLeft A B C hD x)
  rw [flatten_unflatten_left] at hm
  calc
    _ = unflattenLeft A B C hD (flattenLeft A B C hD
      (mode (targetModule (targetModule A B) C) a m (unflattenLeft A B C hD x))) :=
      congrArg (unflattenLeft A B C hD) hm.symm
    _ = _ := unflatten_flatten_left A B C hD _

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem unflattenRight_modes (a : Carrier D) (m : ℤ) (x : RightTriple A B C) :
    unflattenRight A B C hD (mode (rightTripleModule A B C) a m x) =
      mode (targetModule A (targetModule B C)) a m (unflattenRight A B C hD x) :=
by
  have hm := flattenRight_modes A B C hD a m (unflattenRight A B C hD x)
  rw [flatten_unflatten_right] at hm
  calc
    _ = unflattenRight A B C hD (flattenRight A B C hD
      (mode (targetModule A (targetModule B C)) a m (unflattenRight A B C hD x))) :=
      congrArg (unflattenRight A B C hD) hm.symm
    _ = _ := unflatten_flatten_right A B C hD _

/-- Literal tensor associativity; the original carrier is untouched. -/
def carrierRebracket (i : Triple D) :
    LeftSector A B C i ≃ₗ[ℂ] RightSector A B C i :=
  TensorProduct.congr (LinearEquiv.refl ℂ (Carrier D))
    (TensorProduct.assoc ℂ (Multiplicity A i.1) (Multiplicity B i.2.1) (Multiplicity C i.2.2))

/-- This F is SOURCE 13, in iterate-to-product orientation. -/
abbrev F (c d e : Discriminant D) := LatticeChargedQuotientScalar.associator D hD c d e

def middle : LeftTriple A B C →ₗ[ℂ] RightTriple A B C :=
  DirectSum.lmap (fun i : Triple D =>
    F hD i.1 i.2.1 i.2.2 • (carrierRebracket A B C i).toLinearMap)

def middleInverse : RightTriple A B C →ₗ[ℂ] LeftTriple A B C :=
  DirectSum.lmap (fun i : Triple D =>
    (F hD i.1 i.2.1 i.2.2)⁻¹ • (carrierRebracket A B C i).symm.toLinearMap)

theorem middle_inverse_left (x : LeftTriple A B C) :
    middleInverse A B C hD (middle A B C hD x) = x := by
  apply DFinsupp.ext
  intro i
  change (F hD i.1 i.2.1 i.2.2)⁻¹ • (carrierRebracket A B C i).symm
    (F hD i.1 i.2.1 i.2.2 • carrierRebracket A B C i (x i)) = x i
  rw [map_smul,LinearEquiv.symm_apply_apply,smul_smul,
    inv_mul_cancel₀ (LatticeChargedQuotientScalar.associator_nonzero D hD _ _ _),one_smul]

theorem middle_inverse_right (x : RightTriple A B C) :
    middle A B C hD (middleInverse A B C hD x) = x := by
  apply DFinsupp.ext
  intro i
  change F hD i.1 i.2.1 i.2.2 • carrierRebracket A B C i
    ((F hD i.1 i.2.1 i.2.2)⁻¹ • (carrierRebracket A B C i).symm (x i)) = x i
  rw [map_smul,LinearEquiv.apply_symm_apply,smul_smul,
    mul_inv_cancel₀ (LatticeChargedQuotientScalar.associator_nonzero D hD _ _ _),one_smul]

def middleEquiv : LeftTriple A B C ≃ₗ[ℂ] RightTriple A B C where
  toLinearMap := middle A B C hD
  invFun := middleInverse A B C hD
  left_inv := middle_inverse_left A B C hD
  right_inv := middle_inverse_right A B C hD

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem middle_modes (a : Carrier D) (m : ℤ) (x : LeftTriple A B C) :
    middle A B C hD (mode (leftTripleModule A B C) a m x) =
      mode (rightTripleModule A B C) a m (middle A B C hD x) := by
  have hm (i : Triple D) (y : LeftSector A B C i) :
      carrierRebracket A B C i
        (mode (tensorModule (sectorModule D (representative D ((i.1+i.2.1)+i.2.2)))
          (LeftMultiplicity A B C i)) a m y) =
      mode (tensorModule (sectorModule D (representative D ((i.1+i.2.1)+i.2.2)))
          (RightMultiplicity A B C i)) a m (carrierRebracket A B C i y) := by
    induction y using TensorProduct.inductionOn with
    | tmul v w =>
        simp only [tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply,
          carrierRebracket, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  apply DFinsupp.ext
  intro i
  simp only [middle, leftTripleModule, rightTripleModule, directSumModule_mode,
    DirectSum.lmap_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul]
  exact congrArg (fun y => F hD i.1 i.2.1 i.2.2 • y) (hm i (x i))

/-- Actual associator = R^-1 * (literal F * carrier-id/tensor-assoc) * L. -/
def associatorEquiv : LeftP A B C ≃ₗ[ℂ] RightP A B C :=
  ((leftIso A B C hD).linearEquiv.trans (middleEquiv A B C hD)).trans
    (rightIso A B C hD).linearEquiv.symm

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
def associatorIso : ModuleIso (targetModule (targetModule A B) C)
    (targetModule A (targetModule B C)) where
  linearEquiv := associatorEquiv A B C hD
  intertwines a m x := by
    change unflattenRight A B C hD (middle A B C hD
      (flattenLeft A B C hD (mode (targetModule (targetModule A B) C) a m x))) = _
    rw [flattenLeft_modes,middle_modes,unflattenRight_modes]
    rfl

abbrev alpha := (associatorEquiv A B C hD).toLinearMap
abbrev alphaInverse := (associatorEquiv A B C hD).symm.toLinearMap

/-- BOTH inverse laws on ALL original vectors. -/
theorem alphaInverse_alpha (x : LeftP A B C) :
    alphaInverse A B C hD (alpha A B C hD x) = x :=
  (associatorEquiv A B C hD).symm_apply_apply x

theorem alpha_alphaInverse (x : RightP A B C) :
    alpha A B C hD (alphaInverse A B C hD x) = x :=
  (associatorEquiv A B C hD).apply_symm_apply x

theorem alpha_modes (a : Carrier D) (m : ℤ) (x : LeftP A B C) :
    alpha A B C hD (mode (targetModule (targetModule A B) C) a m x) =
      mode (targetModule A (targetModule B C)) a m (alpha A B C hD x) :=
  (associatorIso A B C hD).intertwines a m x

theorem alphaInverse_modes (a : Carrier D) (m : ℤ) (x : RightP A B C) :
    alphaInverse A B C hD (mode (targetModule A (targetModule B C)) a m x) =
      mode (targetModule (targetModule A B) C) a m (alphaInverse A B C hD x) :=
  (associatorIso A B C hD).inverse_intertwines a m x

/-- Exact all-state elementary formula, with forward F, not F^-1. -/
theorem alpha_E_L (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :
    alpha A B C hD (E_L A B C hD c d e v x y z) =
      F hD c d e • E_R A B C hD c d e
        (transportInverse D (representative D (c+(d+e))) (carry D hD c (d+e))
          (transport D (representative D ((c+d)+e)) (carry D hD (c+d) e) v)) x y z := by
  change unflattenRight A B C hD (middle A B C hD
    (flattenLeft A B C hD (leftElementary A B C hD c d e (x ⊗ₜ[ℂ] y) z v))) = _
  rw [flattenLeft_elementary]
  simp only [middle,DirectSum.lmap_lof,LinearMap.smul_apply,LinearEquiv.coe_coe,
    carrierRebracket,TensorProduct.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.assoc_tmul,map_smul]
  rw [unflattenRight_elementary]

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- The inverse has F^-1 and the opposite ORDER of the two transports. -/
theorem alphaInverse_E_R (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :
    alphaInverse A B C hD (E_R A B C hD c d e v x y z) =
      (F hD c d e)⁻¹ • E_L A B C hD c d e
        (transportInverse D (representative D ((c+d)+e)) (carry D hD (c+d) e)
          (transport D (representative D (c+(d+e))) (carry D hD c (d+e)) v)) x y z := by
  apply (associatorEquiv A B C hD).injective
  change alpha A B C hD (alphaInverse A B C hD (E_R A B C hD c d e v x y z)) =
    alpha A B C hD ((F hD c d e)⁻¹ • E_L A B C hD c d e
      (transportInverse D (representative D ((c+d)+e)) (carry D hD (c+d) e)
        (transport D (representative D (c+(d+e))) (carry D hD c (d+e)) v)) x y z)
  rw [alpha_alphaInverse,map_smul,alpha_E_L]
  have ht : transportInverse D (representative D (c+(d+e))) (carry D hD c (d+e))
      (transport D (representative D ((c+d)+e)) (carry D hD (c+d) e)
        (transportInverse D (representative D ((c+d)+e)) (carry D hD (c+d) e)
          (transport D (representative D (c+(d+e))) (carry D hD c (d+e)) v))) = v := by
    have hl := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D =>
      f (transport D (representative D (c+(d+e))) (carry D hD c (d+e)) v))
      (transportInverse_right D (representative D ((c+d)+e)) (carry D hD (c+d) e))
    have hr := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f v)
      (transportInverse_left D (representative D (c+(d+e))) (carry D hD c (d+e)))
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hl hr
    rw [hl,hr]
  rw [ht,smul_smul,inv_mul_cancel₀
    (LatticeChargedQuotientScalar.associator_nonzero D hD c d e),one_smul]

/-- Literal finite-charge formula with all THREE outer cocycle factors. -/
theorem alpha_single (c d e : Discriminant D) (l : Charge D) (p : Oscillator D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :
    alpha A B C hD (E_L A B C hD c d e (Finsupp.single l p) x y z) =
      (F hD c d e * epsilon D l (carry D hD (c+d) e) *
        (epsilon D (-carry D hD c (d+e)) (carry D hD c (d+e)))⁻¹ *
        epsilon D (l+carry D hD (c+d) e) (-carry D hD c (d+e))) •
      E_R A B C hD c d e
        (Finsupp.single (l+carry D hD (c+d) e-carry D hD c (d+e)) p) x y z := by
  rw [alpha_E_L,transport_single,map_smul,transportInverse_single]
  simp only [E_R,map_smul,smul_smul]
  congr 1
  ring

theorem alphaInverse_single (c d e : Discriminant D) (l : Charge D) (p : Oscillator D)
    (x : Multiplicity A c) (y : Multiplicity B d) (z : Multiplicity C e) :
    alphaInverse A B C hD (E_R A B C hD c d e (Finsupp.single l p) x y z) =
      ((F hD c d e)⁻¹ * epsilon D l (carry D hD c (d+e)) *
        (epsilon D (-carry D hD (c+d) e) (carry D hD (c+d) e))⁻¹ *
        epsilon D (l+carry D hD c (d+e)) (-carry D hD (c+d) e)) •
      E_L A B C hD c d e
        (Finsupp.single (l+carry D hD c (d+e)-carry D hD (c+d) e) p) x y z := by
  rw [alphaInverse_E_R,transport_single,map_smul,transportInverse_single]
  simp only [E_L,map_smul,smul_smul]
  congr 1
  ring

end ActualProducts
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleAssociator
