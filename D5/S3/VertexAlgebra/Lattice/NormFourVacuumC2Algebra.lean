/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual coefficient multiplication on the literal norm-four vacuum C2 quotient. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Exact
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Algebra.Defs
import Batteries.Tactic.OpenPrivate

/-! The actual minus-one product descends to the literal vacuum C2 quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualStateFieldCalculus
open NormFourVirasoroVector NormFourVacuumIrreducible NormFourVacuumC2
open scoped BigOperators VertexOperator

open private full_field_closed finite_sum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private higher_product_mem generator_mem vacuum_mem c2_le
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2

noncomputable section

private theorem commutator_evaluated (D : LatticeData) (u v w : Carrier D)
    (p q : ℤ) :
    mu D u p (mu D v q w) - mu D v q (mu D u p w) =
      ∑ᶠ j : ℕ, commutatorTerm D u v p q j w := by
  have h := congrArg (fun A : Module.End ℂ (Carrier D) => A w)
    (mode_commutator D u v p q)
  have evaluation : (∑ᶠ j : ℕ, commutatorTerm D u v p q j) w =
      ∑ᶠ j : ℕ, commutatorTerm D u v p q j w :=
    map_finsum (LinearMap.applyₗ w) (commutator_terms_finite D u v p q)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, evaluation, mu] using h

-- An arbitrary actual state's -1 coefficient preserves C2, not only the axis.
private theorem product_c2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (z : Carrier D) (hz : z ∈ C2 D a s) : mu D u (-1) z ∈ C2 D a s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v,w,hv,hw,rfl⟩ := hz
      let t (j : ℕ) : Carrier D := commutatorTerm D u v (-1) (-2) j w
      have finite : Function.HasFiniteSupport t :=
        (commutator_terms_finite D u v (-1) (-2)).fun_comp
          (map_zero (LinearMap.applyₗ w))
      have each (j : ℕ) : t j ∈ C2 D a s := by
        change StateFieldResidueReconstruction.integerBinomial (-1) j •
          mu D (mu D u j v) (-1 + -2 - j) w ∈ C2 D a s
        apply (C2 D a s).smul_mem
        have inner := full_field_closed D a ha s hs u hu j v hv
        simpa only [show -1 + -2 - (j:ℤ) = -(((j+1:ℕ):ℤ)+2) by omega] using
          higher_product_mem D a ha s hs (j+1) (mu D u j v) w inner hw
      have correction := finite_sum_mem (C2 D a s) t finite each
      have base := generator_mem D a s v (mu D u (-1) w) hv
        (full_field_closed D a ha s hs u hu (-1) w hw)
      have h := commutator_evaluated D u v w (-1) (-2)
      change _ = ∑ᶠ j, t j at h
      exact (by simpa only [← h,sub_add_cancel] using
        (C2 D a s).add_mem correction base)
  | zero => simp [mu]
  | add z w _ _ hz hw =>
      simpa only [mu,map_add] using (C2 D a s).add_mem hz hw
  | smul c z _ hz =>
      simpa only [mu,map_smul] using (C2 D a s).smul_mem c hz

-- The full integer commutator applied to vacuum gives commutativity modulo C2.
private theorem commutative_mod_c2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (hv : v ∈ vacuumDescendants D a s) :
    mu D u (-1) v - mu D v (-1) u ∈ C2 D a s := by
  let t (j : ℕ) : Carrier D := commutatorTerm D u v (-1) (-1) j (vacuum D)
  have finite : Function.HasFiniteSupport t :=
    (commutator_terms_finite D u v (-1) (-1)).fun_comp
      (map_zero (LinearMap.applyₗ (vacuum D)))
  have each (j : ℕ) : t j ∈ C2 D a s := by
    change StateFieldResidueReconstruction.integerBinomial (-1) j •
      mu D (mu D u j v) (-1 + -1 - j) (vacuum D) ∈ C2 D a s
    apply (C2 D a s).smul_mem
    have inner := full_field_closed D a ha s hs u hu j v hv
    simpa only [show -1 + -1 - (j:ℤ) = -((j:ℤ)+2) by omega] using
      higher_product_mem D a ha s hs j (mu D u j v) (vacuum D)
        inner (vacuum_mem D a s)
  have total := finite_sum_mem (C2 D a s) t finite each
  have h := commutator_evaluated D u v (vacuum D) (-1) (-1)
  change _ = ∑ᶠ j, t j at h
  have left : mu D v (-1) (vacuum D) = v := stateField_creation D v
  have right : mu D u (-1) (vacuum D) = u := stateField_creation D u
  rw [left,right] at h
  simpa only [← h] using total

-- The other argument descends as a consequence of actual commutativity.
private theorem c2_product (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z u : Carrier D) (hz : z ∈ C2 D a s)
    (hu : u ∈ vacuumDescendants D a s) : mu D z (-1) u ∈ C2 D a s := by
  have difference := commutative_mod_c2 D a ha s hs z u (c2_le D a ha s hs hz) hu
  have base := product_c2 D a ha s hs u hu z hz
  simpa only [sub_add_cancel] using (C2 D a s).add_mem difference base

-- Both complete iterate families are consumed. No formal tail is discarded.
private theorem associative_mod_c2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v w : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (hv : v ∈ vacuumDescendants D a s) (hw : w ∈ vacuumDescendants D a s) :
    mu D (mu D u (-1) v) (-1) w - mu D u (-1) (mu D v (-1) w) ∈ C2 D a s := by
  classical
  let C := C2 D a s
  let q := C.mkQ
  let first (i : ℕ) : Carrier D :=
    (((-1:ℂ)^i) * ((Ring.choose (-1:ℤ) i : ℤ):ℂ)) •
      mu D u (-1-(i:ℤ)) (mu D v (-1+(i:ℤ)) w)
  let second (i : ℕ) : Carrier D :=
    (((-1:ℂ)^i) * ((Ring.choose (-1:ℤ) i : ℤ):ℂ)) •
      mu D v (-1 + -1 - (i:ℤ)) (mu D u i w)
  have it := stateField_iterate D u v w (-1) (-1)
  change Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
    mu D (mu D u (-1) v) (-1) w =
      (∑ᶠ i, first i) - ((-1:ℂ)^(-1:ℤ)) • (∑ᶠ i, second i) at it
  have first_high (i : ℕ) (hi : i ≠ 0) : first i ∈ C := by
    apply C.smul_mem
    have inner := full_field_closed D a ha s hs v hv (-1+(i:ℤ)) w hw
    have product := higher_product_mem D a ha s hs (i-1) u
      (mu D v (-1+(i:ℤ)) w) hu inner
    simpa only [show -1-(i:ℤ) = -(((i-1:ℕ):ℤ)+2) by omega] using product
  have second_all (i : ℕ) : second i ∈ C := by
    apply C.smul_mem
    have inner := full_field_closed D a ha s hs u hu i w hw
    have product := higher_product_mem D a ha s hs i v (mu D u i w) hv inner
    simpa only [show -1 + -1 - (i:ℤ) = -((i:ℤ)+2) by omega] using product
  have first_image : q (∑ᶠ i, first i) = q (mu D u (-1) (mu D v (-1) w)) := by
    rw [map_finsum q it.1]
    rw [finsum_eq_single _ 0]
    · simp [first]
    · intro i hi
      exact (Submodule.Quotient.mk_eq_zero C).mpr (first_high i hi)
  have second_image : q (∑ᶠ i, second i) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero C).mpr
      (finite_sum_mem C second it.2.1 second_all)
  have image := congrArg q it.2.2
  rw [map_sub,map_smul,first_image,second_image,smul_zero,sub_zero] at image
  apply (Submodule.Quotient.mk_eq_zero C).mp
  change q (_ - _) = 0
  rw [map_sub,image,sub_self]

private abbrev Space (D : LatticeData) (a : Charge D) (s : ℂ) :=
  vacuumDescendants D a s

private abbrev Ideal (D : LatticeData) (a : Charge D) (s : ℂ) :=
  (C2 D a s).comap (Space D a s).subtype

private abbrev QuotientSpace (D : LatticeData) (a : Charge D) (s : ℂ) :=
  Space D a s ⧸ Ideal D a s

private def product (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Space D a s →ₗ[ℂ] Space D a s →ₗ[ℂ] Space D a s where
  toFun u :=
    { toFun := fun v => ⟨mu D u.val (-1) v.val,
        full_field_closed D a ha s hs u.val u.property (-1) v.val v.property⟩
      map_add' := by intro v w; apply Subtype.ext; simp [mu]
      map_smul' := by intro c v; apply Subtype.ext; simp [mu] }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [mu]
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [mu]

private def seed (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Space D a s →ₗ[ℂ] Space D a s →ₗ[ℂ] QuotientSpace D a s :=
  (product D a ha s hs).compr₂ (Ideal D a s).mkQ

private theorem seed_left_kernel (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Ideal D a s ≤ (seed D a ha s hs).ker := by
  intro z hz
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro u
  apply (Submodule.Quotient.mk_eq_zero (Ideal D a s)).mpr
  exact c2_product D a ha s hs z.val u.val hz u.property

private theorem seed_right_kernel (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Ideal D a s ≤ (seed D a ha s hs).flip.ker := by
  intro z hz
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro u
  apply (Submodule.Quotient.mk_eq_zero (Ideal D a s)).mpr
  exact product_c2 D a ha s hs u.val u.property z.val hz

/-- The product descends from the actual -1 coefficient, with
both argument kernels proved from actual field identities. -/
def quotientProduct (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    QuotientSpace D a s →ₗ[ℂ] QuotientSpace D a s →ₗ[ℂ] QuotientSpace D a s :=
  (seed D a ha s hs).liftQ₂ (Ideal D a s) (Ideal D a s)
    (seed_left_kernel D a ha s hs) (seed_right_kernel D a ha s hs)

private def unitClass (D : LatticeData) (a : Charge D) (s : ℂ) :
    QuotientSpace D a s :=
  (Ideal D a s).mkQ ⟨vacuum D,vacuum_mem D a s⟩

private theorem product_mk (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u v : Space D a s) :
    quotientProduct D a ha s hs ((Ideal D a s).mkQ u) ((Ideal D a s).mkQ v) =
      (Ideal D a s).mkQ (product D a ha s hs u v) := rfl

private theorem quotient_comm (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (x y : QuotientSpace D a s) :
    quotientProduct D a ha s hs x y = quotientProduct D a ha s hs y x := by
  obtain ⟨u,rfl⟩ := (Ideal D a s).mkQ_surjective x
  obtain ⟨v,rfl⟩ := (Ideal D a s).mkQ_surjective y
  rw [product_mk,product_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (Ideal D a s)).mpr
  exact commutative_mod_c2 D a ha s hs u.val v.val u.property v.property

private theorem quotient_assoc (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (x y z : QuotientSpace D a s) :
    quotientProduct D a ha s hs (quotientProduct D a ha s hs x y) z =
      quotientProduct D a ha s hs x (quotientProduct D a ha s hs y z) := by
  obtain ⟨u,rfl⟩ := (Ideal D a s).mkQ_surjective x
  obtain ⟨v,rfl⟩ := (Ideal D a s).mkQ_surjective y
  obtain ⟨w,rfl⟩ := (Ideal D a s).mkQ_surjective z
  simp only [product_mk]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (Ideal D a s)).mpr
  exact associative_mod_c2 D a ha s hs u.val v.val w.val
    u.property v.property w.property

private theorem quotient_unit (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (x : QuotientSpace D a s) : quotientProduct D a ha s hs (unitClass D a s) x = x := by
  obtain ⟨u,rfl⟩ := (Ideal D a s).mkQ_surjective x
  rw [unitClass,product_mk]
  congr 1
  apply Subtype.ext
  simp [product,mu,stateField_vacuum,identity_modes]

/-- A genuine commutative ring on the existing quotient, preserving
its existing additive group. Multiplication is the actual coefficient product. -/
@[instance_reducible]
def quotientRing (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    CommRing (QuotientSpace D a s) where
  __ := (inferInstance : AddCommGroup (QuotientSpace D a s))
  mul := fun x y => quotientProduct D a ha s hs x y
  one := unitClass D a s
  mul_assoc := quotient_assoc D a ha s hs
  one_mul := quotient_unit D a ha s hs
  mul_one x := (quotient_comm D a ha s hs x (unitClass D a s)).trans
    (quotient_unit D a ha s hs x)
  mul_comm := quotient_comm D a ha s hs
  left_distrib x y z := (quotientProduct D a ha s hs x).map_add y z
  right_distrib x y z := by
    exact congrArg (fun f : QuotientSpace D a s →ₗ[ℂ] QuotientSpace D a s => f z)
      ((quotientProduct D a ha s hs).map_add x y)
  zero_mul x := by
    exact congrArg (fun f : QuotientSpace D a s →ₗ[ℂ] QuotientSpace D a s => f x)
      (map_zero (quotientProduct D a ha s hs))
  mul_zero x := map_zero (quotientProduct D a ha s hs x)

/-- The existing complex module and descended product define an
actual complex algebra, with scalars acting as scalar multiples of vacuum. -/
@[instance_reducible]
def quotientAlgebra (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    letI := quotientRing D a ha s hs
    Algebra ℂ (QuotientSpace D a s) := by
  letI := quotientRing D a ha s hs
  apply Algebra.ofModule
  · intro c x y
    exact congrArg (fun f : QuotientSpace D a s →ₗ[ℂ] QuotientSpace D a s => f y)
      ((quotientProduct D a ha s hs).map_smul c x)
  · intro c x y
    exact (quotientProduct D a ha s hs x).map_smul c y

/-- The actual C2 quotient has a unital commutative associative
complex-algebra structure with literal representative compatibility. Its
exact dimension is inherited from the accepted actual low-weight separation.
The polynomial presentation is constructed in the companion module. -/
theorem actual_vacuum_c2_algebra (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := Space D a s
    let C := Ideal D a s
    letI := quotientRing D a ha s hs
    letI := quotientAlgebra D a ha s hs
    (∀ u v : S, C.mkQ (product D a ha s hs u v) = C.mkQ u * C.mkQ v) ∧
      (1 : QuotientSpace D a s) = C.mkQ ⟨vacuum D,vacuum_mem D a s⟩ ∧
      FiniteDimensional ℂ (QuotientSpace D a s) ∧
        Module.finrank ℂ (QuotientSpace D a s) = 3 := by
  letI := quotientRing D a ha s hs
  letI := quotientAlgebra D a ha s hs
  obtain ⟨finite,dimension⟩ := NormFourVacuumC2Exact.actual_vacuum_c2_dimension D a ha s hs
  exact ⟨fun u v => (product_mk D a ha s hs u v).symm,rfl,finite,dimension⟩

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
