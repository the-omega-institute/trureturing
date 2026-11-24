/- GID: D5/S3/VertexAlgebra/BRST/MonsterPositiveCocycle
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/MonsterPositiveCocycle
   mirror-E: none(waiver:algebraic-positive-presentation)
   anchors: []
   utility: none
   digest: Tensor cocycle and Serre descent for the direct positive Monster presentation. -/

import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Lie.Extension
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
Borcherds, *Monstrous moonshine and monstrous Lie superalgebras* (1992), and
Jurisich, *Generalized Kac–Moody Lie algebras, free Lie algebras and the structure of the
Monster Lie algebra* (1998), give the presentation context. The tensor extension and
lifted Serre coefficient here follow §4, equations (12)–(13), of the direct-presentation
Oracle derivation dated 2026-11-24.

The degree lattice below uses paper coordinates `(m,n)`. The repository's hyperbolic-plane
charge has coordinates `(m,-n)`, so the real root has native charge `(1,1)`.
-/

set_option autoImplicit false

noncomputable section

open scoped DirectSum TensorProduct
open LieModule.Cohomology

namespace D5.S3.VertexAlgebra.MonsterPositiveCocycle

variable {R A Γ : Type*} [CommRing R] [LieRing A] [LieAlgebra R A]

/-- The antisymmetrized pure tensor, as a bilinear map. -/
def altTensor : A →ₗ[R] A →ₗ[R] A ⊗[R] A :=
  TensorProduct.mk R A A - (TensorProduct.mk R A A).flip

theorem altTensor_apply (x y : A) :
    altTensor (R := R) x y = x ⊗ₜ[R] y - y ⊗ₜ[R] x :=
  rfl

private theorem altTensor_swap (x y : A) :
    altTensor (R := R) x y = -altTensor (R := R) y x := by
  simp only [altTensor_apply, neg_sub]

/-- The diagonal adjoint action distributes over the two slots of an antisymmetrized tensor. -/
theorem lie_altTensor (x y z : A) :
    ⁅x, altTensor (R := R) y z⁆ =
      altTensor (R := R) ⁅x, y⁆ z + altTensor (R := R) y ⁅x, z⁆ := by
  simp only [altTensor_apply, lie_sub, TensorProduct.LieModule.lie_tmul_right]
  abel

section Graded

variable [AddCommMonoid Γ]
variable (B : Γ →+ Γ →+ R)

/-- The defect on a pair with specified degrees. -/
def homogeneousEta (a b : Γ) (x y : A) : A ⊗[R] A :=
  B a b • altTensor x y

/-- The homogeneous Chevalley–Eilenberg differential is zero. The three tensor
coefficients are the two additive expansions of the relevant summed degrees. -/
theorem homogeneous_cocycle (hB : ∀ a b, B a b = B b a)
    (a b c : Γ) (x y z : A) :
    ⁅x, homogeneousEta B b c y z⁆ - ⁅y, homogeneousEta B a c x z⁆ +
        ⁅z, homogeneousEta B a b x y⁆ -
        homogeneousEta B (a + b) c ⁅x, y⁆ z +
        homogeneousEta B (a + c) b ⁅x, z⁆ y -
        homogeneousEta B (b + c) a ⁅y, z⁆ x = 0 := by
  have hxy : ⁅y, x⁆ = -⁅x, y⁆ := (lie_skew y x).symm
  have hxz : ⁅z, x⁆ = -⁅x, z⁆ := (lie_skew z x).symm
  have hyz : ⁅z, y⁆ = -⁅y, z⁆ := (lie_skew z y).symm
  have hc₁ : B (a + b) c = B a c + B b c := by simp
  have hc₂ : B (a + c) b = B a b + B b c := by
    rw [map_add, AddMonoidHom.add_apply, hB c b]
  have hc₃ : B (b + c) a = B a b + B a c := by
    rw [hB (b + c) a, map_add]
  simp only [homogeneousEta, lie_smul, lie_altTensor, hxy, hxz, hyz, map_neg,
    LinearMap.neg_apply, altTensor_swap (R := R) y ⁅x, z⁆,
    altTensor_swap (R := R) x ⁅y, z⁆, hc₁, hc₂, hc₃, smul_add, smul_neg,
    add_smul, neg_neg]
  abel

variable [DecidableEq Γ]
variable (grade : Γ → Submodule R A) [DirectSum.Decomposition grade]

private def fromGrades {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ∀ i, grade i →ₗ[R] M) : A →ₗ[R] M :=
  (DirectSum.toModule R Γ M f).comp (DirectSum.decomposeLinearEquiv grade).toLinearMap

omit [AddCommMonoid Γ] in
private theorem fromGrades_apply_coe {M : Type*} [AddCommMonoid M] [Module R M]
    (f : ∀ i, grade i →ₗ[R] M) (i : Γ) (x : grade i) :
    fromGrades grade f (x : A) = f i x := by
  simp [fromGrades]

omit [AddCommMonoid Γ] in
private theorem ext_grades {M : Type*} [AddCommMonoid M] [Module R M] {f g : A →ₗ[R] M}
    (h : ∀ (i : Γ) (x : grade i), f (x : A) = g (x : A)) : f = g :=
  DirectSum.decompose_lhom_ext grade fun i => LinearMap.ext (h i)

/-- Extend the componentwise defect by linearity in each of its finite direct-sum inputs. -/
def eta : A →ₗ[R] A →ₗ[R] A ⊗[R] A :=
  fromGrades grade fun i =>
    (fromGrades grade fun j =>
      B i j • ((altTensor.comp (grade i).subtype).flip.comp (grade j).subtype)).flip

theorem eta_of_mem {a b : Γ} {x y : A} (hx : x ∈ grade a) (hy : y ∈ grade b) :
    eta B grade x y = homogeneousEta B a b x y := by
  let u : grade a := ⟨x, hx⟩
  let v : grade b := ⟨y, hy⟩
  change eta B grade (u : A) (v : A) = _
  rw [eta, fromGrades_apply_coe grade _ a u, LinearMap.flip_apply,
    fromGrades_apply_coe grade _ b v]
  rfl

private theorem eta_swap (hB : ∀ a b, B a b = B b a) (x y : A) :
    eta B grade y x = -eta B grade x y := by
  have hs : (eta B grade).flip = -eta B grade := by
    apply ext_grades grade
    intro i u
    apply ext_grades grade
    intro j v
    change eta B grade (v : A) (u : A) = -eta B grade (u : A) (v : A)
    rw [eta_of_mem B grade v.property u.property, eta_of_mem B grade u.property v.property]
    simp only [homogeneousEta, hB j i, altTensor_swap (R := R) (v : A) (u : A), smul_neg]
  exact DFunLike.congr_fun (DFunLike.congr_fun hs x) y

private theorem eta_self (hB : ∀ a b, B a b = B b a) (x : A) : eta B grade x x = 0 := by
  let assemble := (DirectSum.decomposeLinearEquiv grade).symm
  obtain ⟨u, rfl⟩ := assemble.surjective x
  induction u using DirectSum.induction_on with
  | zero => simp
  | of i u =>
      rw [show assemble (DirectSum.of _ i u) = (u : A) by
        simpa only [DirectSum.lof_eq_of] using DirectSum.decomposeLinearEquiv_symm_lof grade i u]
      rw [eta_of_mem B grade u.property u.property]
      simp [homogeneousEta, altTensor_apply]
  | add u v hu hv =>
      simp only [map_add, LinearMap.add_apply, hu, hv, zero_add, add_zero]
      rw [eta_swap B grade hB (assemble u) (assemble v), neg_add_cancel]

variable (hB : ∀ a b, B a b = B b a)
variable (hBracket : ∀ ⦃a b : Γ⦄ ⦃x y : A⦄, x ∈ grade a → y ∈ grade b → ⁅x, y⁆ ∈ grade (a + b))

/-- The tensor defect as a Mathlib Lie 2-cocycle with coefficients in the adjoint tensor module. -/
def tensorCocycle : twoCocycle R A (A ⊗[R] A) where
  val := ⟨eta B grade, eta_self B grade hB⟩
  property := by
    rw [mem_twoCocycle_iff]
    apply ext_grades grade
    intro a x
    apply ext_grades grade
    intro b y
    apply ext_grades grade
    intro c z
    simp only [d₂₃_apply, LinearMap.zero_apply]
    change ⁅(x : A), eta B grade y z⁆ - ⁅(y : A), eta B grade x z⁆ +
        ⁅(z : A), eta B grade x y⁆ - eta B grade ⁅(x : A), (y : A)⁆ z +
        eta B grade ⁅(x : A), (z : A)⁆ y - eta B grade ⁅(y : A), (z : A)⁆ x = 0
    rw [eta_of_mem B grade y.property z.property, eta_of_mem B grade x.property z.property,
      eta_of_mem B grade x.property y.property,
      eta_of_mem B grade (hBracket x.property y.property) z.property,
      eta_of_mem B grade (hBracket x.property z.property) y.property,
      eta_of_mem B grade (hBracket y.property z.property) x.property]
    exact homogeneous_cocycle B hB a b c (x : A) (y : A) (z : A)

/-- The tensor extension with abelian kernel and diagonal adjoint action. -/
abbrev TensorExtension :=
  LieAlgebra.ofTwoCocycle (tensorCocycle B grade hB hBracket)

theorem extension_bracket (x y : TensorExtension B grade hB hBracket) :
    (⁅x, y⁆ : TensorExtension B grade hB hBracket).carrier =
      (⁅x.carrier.1, y.carrier.1⁆,
       eta B grade x.carrier.1 y.carrier.1 + ⁅x.carrier.1, y.carrier.2⁆ -
         ⁅y.carrier.1, x.carrier.2⁆) :=
  rfl

theorem tensor_ideal_abelian (u v : A ⊗[R] A) :
    ⁅(⟨(0, u)⟩ : TensorExtension B grade hB hBracket),
      (⟨(0, v)⟩ : TensorExtension B grade hB hBracket)⁆ = 0 := by
  apply (LieAlgebra.ofProd (tensorCocycle B grade hB hBracket)).symm.injective
  change (⁅(⟨(0, u)⟩ : TensorExtension B grade hB hBracket),
      (⟨(0, v)⟩ : TensorExtension B grade hB hBracket)⁆ :
    TensorExtension B grade hB hBracket).carrier = (0, 0)
  rw [extension_bracket]
  simp

/-- The linear lift of a presentation generator with zero tensor component. -/
def zeroLift (x : A) : TensorExtension B grade hB hBracket := ⟨(x, 0)⟩

end Graded

/-- The iterated left adjoint, with the generator in depth zero. -/
def adIter {L : Type*} [Bracket L L] (e : L) : ℕ → L → L
  | 0, y => y
  | k + 1, y => ⁅e, adIter e k y⁆

private theorem map_adIter {L M : Type*} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) (e y : L) (k : ℕ) :
    f (adIter e k y) = adIter (f e) k (f y) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adIter, adIter, LieHom.map_lie, ih]

section Serre

variable [AddCommMonoid Γ] [DecidableEq Γ]
variable (B : Γ →+ Γ →+ R)
variable (grade : Γ → Submodule R A) [DirectSum.Decomposition grade]
variable (hB : ∀ a b, B a b = B b a)
variable (hBracket : ∀ ⦃a b : Γ⦄ ⦃x y : A⦄, x ∈ grade a → y ∈ grade b → ⁅x, y⁆ ∈ grade (a + b))

omit [DecidableEq Γ] [DirectSum.Decomposition grade] in
include hBracket in
private theorem adIter_mem {a b : Γ} {e y : A} (he : e ∈ grade a) (hy : y ∈ grade b) (k : ℕ) :
    adIter e k y ∈ grade (k • a + b) := by
  induction k with
  | zero => simpa [adIter] using hy
  | succ k ih => simpa only [adIter, succ_nsmul', add_assoc] using hBracket he ih

/-- The tensor coefficient accumulates one defect for each adjoint step. The previous
tensor contribution advances by the same adjoint because `⁅e,e⁆ = 0`. -/
theorem lifted_adIter_succ {a b : Γ} {e y : A} (he : e ∈ grade a) (hy : y ∈ grade b)
    (C : ℕ → R) (hC₀ : C 0 = 0)
    (hC : ∀ k : ℕ, C (k + 1) = C k + B a (k • a + b)) (k : ℕ) :
    (adIter (zeroLift B grade hB hBracket e) (k + 1)
      (zeroLift B grade hB hBracket y)).carrier =
      (adIter e (k + 1) y, C (k + 1) • altTensor (R := R) e (adIter e k y)) := by
  induction k with
  | zero =>
      change (⁅zeroLift B grade hB hBracket e,
        (zeroLift B grade hB hBracket y)⁆ : TensorExtension B grade hB hBracket).carrier = _
      rw [extension_bracket]
      change (⁅e, y⁆, eta B grade e y + ⁅e, (0 : A ⊗[R] A)⁆ -
        ⁅y, (0 : A ⊗[R] A)⁆) = (⁅e, y⁆, C (0 + 1) • altTensor (R := R) e y)
      rw [eta_of_mem B grade he hy, hC 0, hC₀]
      simp [homogeneousEta]
  | succ k ih =>
      change (⁅zeroLift B grade hB hBracket e,
        adIter (zeroLift B grade hB hBracket e) (k + 1) (zeroLift B grade hB hBracket y)⁆ :
        TensorExtension B grade hB hBracket).carrier = _
      rw [extension_bracket, ih]
      change (⁅e, adIter e (k + 1) y⁆, eta B grade e (adIter e (k + 1) y) +
        ⁅e, C (k + 1) • altTensor (R := R) e (adIter e k y)⁆ -
        ⁅adIter e (k + 1) y, (0 : A ⊗[R] A)⁆) =
        (⁅e, adIter e (k + 1) y⁆, C (k + 1 + 1) • altTensor (R := R) e (adIter e (k + 1) y))
      rw [eta_of_mem B grade he (adIter_mem grade hBracket he hy (k + 1)), hC (k + 1)]
      simp only [homogeneousEta, lie_smul, lie_altTensor, lie_self, map_zero, LinearMap.zero_apply,
        zero_add, lie_zero, sub_zero, add_smul, adIter]
      rw [add_comm]

end Serre

/-- The rank-two weight lattice in paper coordinates. -/
abbrev Weight := ℤ × ℤ

/-- The symmetric Lorentzian form in paper coordinates. -/
def weightForm : Weight →+ Weight →+ ℝ where
  toFun p :=
    { toFun q := -((p.1 : ℝ) * (q.2 : ℝ) + (p.2 : ℝ) * (q.1 : ℝ))
      map_zero' := by simp
      map_add' := by intro q r; simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring }
  map_zero' := by ext q; simp
  map_add' := by
    intro p q
    ext r
    change -((((p + q).1 : ℤ) : ℝ) * (r.2 : ℝ) + (((p + q).2 : ℤ) : ℝ) * (r.1 : ℝ)) =
      -((p.1 : ℝ) * (r.2 : ℝ) + (p.2 : ℝ) * (r.1 : ℝ)) +
      -((q.1 : ℝ) * (r.2 : ℝ) + (q.2 : ℝ) * (r.1 : ℝ))
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

theorem weightForm_symm (p q : Weight) : weightForm p q = weightForm q p := by
  change -((p.1 : ℝ) * (q.2 : ℝ) + (p.2 : ℝ) * (q.1 : ℝ)) =
    -((q.1 : ℝ) * (p.2 : ℝ) + (q.2 : ℝ) * (p.1 : ℝ))
  ring

def realRoot : Weight := (1, -1)

def imaginaryRoot (n : ℕ) : Weight := (1, n)

private theorem weightForm_on_string (n k : ℕ) :
    weightForm realRoot (k • realRoot + imaginaryRoot n) = 1 - (n : ℝ) + 2 * (k : ℝ) := by
  have haa : weightForm realRoot realRoot = 2 := by
    norm_num [weightForm, realRoot]
  have hab : weightForm realRoot (imaginaryRoot n) = 1 - (n : ℝ) := by
    simp [weightForm, realRoot, imaginaryRoot]
    ring
  rw [map_add, map_nsmul, haa, hab, nsmul_eq_mul]
  ring

section Monster

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (grade : Weight → Submodule ℝ L) [DirectSum.Decomposition grade]
variable (hBracket : ∀ ⦃a b : Weight⦄ ⦃x y : L⦄,
  x ∈ grade a → y ∈ grade b → ⁅x, y⁆ ∈ grade (a + b))

/-- For depth `k + 1`, the second component is `(k + 1)(k + 1 - n)` times the antisymmetric
tensor formed from the previous string member. -/
theorem lifted_monster_string {n : ℕ} {e y : L}
    (he : e ∈ grade realRoot) (hy : y ∈ grade (imaginaryRoot n)) (k : ℕ) :
    (adIter (zeroLift weightForm grade weightForm_symm hBracket e) (k + 1)
      (zeroLift weightForm grade weightForm_symm hBracket y)).carrier =
      (adIter e (k + 1) y, (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - (n : ℝ))) •
        altTensor (R := ℝ) e (adIter e k y)) := by
  apply lifted_adIter_succ weightForm grade weightForm_symm hBracket he hy
    (fun j => (j : ℝ) * ((j : ℝ) - (n : ℝ)))
  · simp
  · intro j
    rw [weightForm_on_string, Nat.cast_succ]
    ring

/-- Both components of the lifted Serre relation vanish at depth `n`. -/
theorem lifted_monster_serre {n : ℕ} {e y : L}
    (he : e ∈ grade realRoot) (hy : y ∈ grade (imaginaryRoot n))
    (hSerre : adIter e n y = 0) :
    adIter (zeroLift weightForm grade weightForm_symm hBracket e) n
      (zeroLift weightForm grade weightForm_symm hBracket y) = 0 := by
  apply (LieAlgebra.ofProd (tensorCocycle weightForm grade weightForm_symm hBracket)).symm.injective
  cases n with
  | zero =>
      change (y, (0 : L ⊗[ℝ] L)) = (0, 0)
      rw [show y = 0 from hSerre]
  | succ k =>
      change (adIter (zeroLift weightForm grade weightForm_symm hBracket e) (k + 1)
        (zeroLift weightForm grade weightForm_symm hBracket y)).carrier = (0, 0)
      rw [lifted_monster_string grade hBracket he hy k, hSerre]
      simp

end Monster

section Presentation

variable {J : Type*} (order : J → ℕ+)

local notation "F" => FreeLieAlgebra ℝ (Option J)

/-- The ideal generated by the positive Monster Serre words. The index type `J`
can carry the full positive imaginary simple-root multiplicities. -/
def serreIdeal : LieIdeal ℝ F :=
  LieSubmodule.lieSpan ℝ F <| Set.range fun j : J =>
    adIter (FreeLieAlgebra.of ℝ none) (order j : ℕ) (FreeLieAlgebra.of ℝ (some j))

/-- The positive presentation with one real generator and the indexed imaginary generators. -/
abbrev PositivePresentation := F ⧸ serreIdeal order

/-- The quotient map from the free Lie algebra. -/
def presentationQuotient : F →ₗ⁅ℝ⁆ PositivePresentation order :=
  { (serreIdeal order).toSubmodule.mkQ with
    map_lie' := fun {x y} => LieSubmodule.Quotient.mk_bracket (serreIdeal order) x y }

/-- The positive simple generators in the quotient. -/
def generator (j : Option J) : PositivePresentation order :=
  presentationQuotient order (FreeLieAlgebra.of ℝ j)

private theorem presentation_serre (j : J) :
    adIter (generator order none) (order j : ℕ) (generator order (some j)) = 0 := by
  unfold generator
  rw [← map_adIter (presentationQuotient order)]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan (Set.mem_range_self j))

variable (grade : Weight → Submodule ℝ (PositivePresentation order)) [DirectSum.Decomposition grade]
variable (hBracket : ∀ ⦃a b : Weight⦄ ⦃x y : PositivePresentation order⦄,
  x ∈ grade a → y ∈ grade b → ⁅x, y⁆ ∈ grade (a + b))
variable (he : generator order none ∈ grade realRoot)
variable (hE : ∀ j, generator order (some j) ∈ grade (imaginaryRoot (order j : ℕ)))

local notation "P" => PositivePresentation order
local notation "Ext" => TensorExtension weightForm grade weightForm_symm hBracket

private def freeLift : F →ₗ⁅ℝ⁆ Ext :=
  FreeLieAlgebra.lift ℝ fun j => zeroLift weightForm grade weightForm_symm hBracket (generator order j)

include he hE in
private theorem serreIdeal_le_freeLift_ker : serreIdeal order ≤ (freeLift order grade hBracket).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro _ ⟨j, rfl⟩
  change freeLift order grade hBracket
    (adIter (FreeLieAlgebra.of ℝ none) (order j : ℕ) (FreeLieAlgebra.of ℝ (some j))) = 0
  rw [map_adIter]
  simp only [freeLift, FreeLieAlgebra.lift_of_apply]
  exact lifted_monster_serre grade hBracket he (hE j) (presentation_serre order j)

/-- The Lie homomorphism obtained by lifting simple generators with zero tensor component. -/
def presentationLift : P →ₗ⁅ℝ⁆ Ext :=
  { (serreIdeal order).toSubmodule.liftQ (freeLift order grade hBracket).toLinearMap
      (serreIdeal_le_freeLift_ker order grade hBracket he hE) with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y => exact (freeLift order grade hBracket).map_lie x y }

theorem presentationLift_generator (j : Option J) :
    presentationLift order grade hBracket he hE (generator order j) =
      zeroLift weightForm grade weightForm_symm hBracket (generator order j) := by
  change freeLift order grade hBracket (FreeLieAlgebra.of ℝ j) = _
  exact FreeLieAlgebra.lift_of_apply _ _

private def projection : Ext →ₗ⁅ℝ⁆ P where
  toFun x := x.carrier.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := by intro x y; rfl

theorem projection_presentationLift (x : P) :
    (presentationLift order grade hBracket he hE x).carrier.1 = x := by
  have hFree : (projection order grade hBracket).comp
      ((presentationLift order grade hBracket he hE).comp (presentationQuotient order)) =
      presentationQuotient order := by
    apply FreeLieAlgebra.hom_ext
    intro j
    change (presentationLift order grade hBracket he hE (generator order j)).carrier.1 = _
    rw [presentationLift_generator]
    rfl
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact DFunLike.congr_fun hFree x

/-- The presentation-side tensor map `Δ_P` of the direct Monster argument. -/
def presentationDelta : P →ₗ[ℝ] P ⊗[ℝ] P where
  toFun x := (presentationLift order grade hBracket he hE x).carrier.2
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

/-- The presentation tensor component vanishes on every simple generator. -/
theorem presentation_tensor_generator (j : Option J) :
    presentationDelta order grade hBracket he hE (generator order j) = 0 := by
  change (presentationLift order grade hBracket he hE (generator order j)).carrier.2 = 0
  rw [presentationLift_generator]
  rfl

/-- The presentation tensor component satisfies the split-tensor bracket identity in
equation (10) on all homogeneous pairs. -/
theorem presentation_tensor_bracket {a b : Weight} {x y : P}
    (hx : x ∈ grade a) (hy : y ∈ grade b) :
    presentationDelta order grade hBracket he hE ⁅x, y⁆ =
      ⁅x, presentationDelta order grade hBracket he hE y⁆ -
        ⁅y, presentationDelta order grade hBracket he hE x⁆ +
        homogeneousEta weightForm a b x y := by
  simp only [presentationDelta, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LieHom.map_lie, extension_bracket]
  simp only [projection_presentationLift, eta_of_mem weightForm grade hx hy]
  abel

end Presentation

end D5.S3.VertexAlgebra.MonsterPositiveCocycle
