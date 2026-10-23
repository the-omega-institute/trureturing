/- GID: D5/S3/FiniteGroups/SuccessorQuotient
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SuccessorQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least successor-compatible quotient controls assignments and relation symmetries. -/

import Mathlib.Order.Setoid.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A directed relation may have loops and multiple successors. Its least
successor-compatible equivalence is defined by the complete lattice of setoids.
Assignments respecting an update descend through this quotient without any
prior assumption that they are constant on its classes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.SuccessorQuotient

variable {V : Type*} (R : V → V → Prop)

def Admissible (E : Setoid V) : Prop :=
  (∀ x y z, R x y → R x z → E y z) ∧
  (∀ x x' y y', E x x' → R x y → R x' y' → E y y')

def least : Setoid V := sInf {E : Setoid V | Admissible R E}

private theorem least_admissible : Admissible R (least R) := by
  constructor
  · intro x y z hxy hxz
    rw [least, Setoid.sInf_iff]
    intro E hE
    exact hE.1 x y z hxy hxz
  · intro x x' y y' hxx' hxy hx'y'
    rw [least, Setoid.sInf_iff] at hxx' ⊢
    intro E hE
    exact hE.2 x x' y y' (hxx' E hE) hxy hx'y'

private theorem least_le {E : Setoid V} (hE : Admissible R E) : least R ≤ E :=
  sInf_le hE

abbrev Blocks := Quotient (least R)

def project (x : V) : Blocks R := Quotient.mk'' x

noncomputable def chosen (hout : ∀ x, ∃ y, R x y) (x : V) : V :=
  Classical.choose (hout x)

private theorem chosen_arrow (hout : ∀ x, ∃ y, R x y) (x : V) :
    R x (chosen R hout x) := Classical.choose_spec (hout x)

noncomputable def successor (hout : ∀ x, ∃ y, R x y) : Blocks R → Blocks R :=
  Quotient.lift (fun x => project R (chosen R hout x)) (by
    intro x x' h
    exact Quotient.sound ((least_admissible R).2 x x' _ _ h
      (chosen_arrow R hout x) (chosen_arrow R hout x')))

theorem successor_project (hout : ∀ x, ∃ y, R x y) {x y : V} (hxy : R x y) :
    successor R hout (project R x) = project R y := by
  exact Quotient.sound ((least_admissible R).1 x _ _ (chosen_arrow R hout x) hxy)

private theorem successor_surjective (hout : ∀ x, ∃ y, R x y)
    (hin : ∀ y, ∃ x, R x y) : Function.Surjective (successor R hout) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro y
  obtain ⟨x, hxy⟩ := hin y
  exact ⟨project R x, successor_project R hout hxy⟩

noncomputable def beta [Finite V] (hout : ∀ x, ∃ y, R x y)
    (hin : ∀ y, ∃ x, R x y) : Equiv.Perm (Blocks R) :=
  Equiv.ofBijective (successor R hout)
    ⟨Finite.injective_iff_surjective.mpr (successor_surjective R hout hin),
      successor_surjective R hout hin⟩

def Assignments {K : Type*} (update : K → K) :=
  {t : V → K // ∀ x y, R x y → t y = update (t x)}

def QuotientAssignments {K : Type*} (update : K → K)
    (hout : ∀ x, ∃ y, R x y) :=
  {v : Blocks R → K // ∀ q, v (successor R hout q) = update (v q)}

private theorem assignment_constant {K : Type*} (update : K → K)
    (t : Assignments R update) : least R ≤ Setoid.ker t.val := by
  apply least_le R
  constructor
  · intro x y z hxy hxz
    exact (t.property x y hxy).trans (t.property x z hxz).symm
  · intro x x' y y' hxx' hxy hx'y'
    change t.val x = t.val x' at hxx'
    change t.val y = t.val y'
    rw [t.property x y hxy, t.property x' y' hx'y', hxx']

/-- Exact descent of every compatible assignment through the least quotient. -/
noncomputable def assignmentEquiv {K : Type*} (update : K → K)
    (hout : ∀ x, ∃ y, R x y) :
    Assignments R update ≃ QuotientAssignments R update hout where
  toFun t := ⟨Quotient.lift t.val (fun _ _ h => assignment_constant R update t h), by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact t.property x _ (chosen_arrow R hout x)⟩
  invFun v := ⟨fun x => v.val (project R x), by
    intro x y hxy
    change v.val (project R y) = update (v.val (project R x))
    exact (congrArg v.val (successor_project R hout hxy)).symm.trans
      (v.property (project R x))⟩
  left_inv t := by rfl
  right_inv v := by
    apply Subtype.ext
    funext q
    exact Quotient.inductionOn q (fun _ => rfl)

/-- All permutations preserving the directed relation, including its loops. -/
def relationAut : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ x y, R (σ x) (σ y) ↔ R x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro σ τ hσ hτ x y
    exact (hσ (τ x) (τ y)).trans (hτ x y)
  inv_mem' := by
    intro σ hσ x y
    change R (σ.symm x) (σ.symm y) ↔ R x y
    simpa only [Equiv.apply_symm_apply] using
      (hσ (σ.symm x) (σ.symm y)).symm

private theorem aut_preserves_least (σ : relationAut R) {x y : V}
    (hxy : least R x y) : least R (σ.val x) (σ.val y) := by
  have hc : Admissible R (Setoid.comap σ.val (least R)) := by
    constructor
    · intro x y z hxy hxz
      exact (least_admissible R).1 (σ.val x) (σ.val y) (σ.val z)
        ((σ.property x y).mpr hxy) ((σ.property x z).mpr hxz)
    · intro x x' y y' hxx' hxy hx'y'
      exact (least_admissible R).2 (σ.val x) (σ.val x') (σ.val y) (σ.val y') hxx'
        ((σ.property x y).mpr hxy) ((σ.property x' y').mpr hx'y')
  exact least_le R hc hxy

noncomputable def blockPerm (σ : relationAut R) : Equiv.Perm (Blocks R) where
  toFun := Quotient.map σ.val (fun _ _ h => aut_preserves_least R σ h)
  invFun := Quotient.map σ.val.symm (fun _ _ h => aut_preserves_least R σ⁻¹ h)
  left_inv q := Quotient.inductionOn q (fun x => by
    change project R (σ.val.symm (σ.val x)) = project R x
    rw [Equiv.symm_apply_apply])
  right_inv q := Quotient.inductionOn q (fun x => by
    change project R (σ.val (σ.val.symm x)) = project R x
    rw [Equiv.apply_symm_apply])

noncomputable def blockHom : relationAut R →* Equiv.Perm (Blocks R) where
  toFun := blockPerm R
  map_one' := by
    ext q
    exact Quotient.inductionOn q (fun _ => rfl)
  map_mul' σ τ := by
    ext q
    exact Quotient.inductionOn q (fun _ => rfl)

/-- The block action commutes with the canonical successor. -/
theorem block_successor_commute (hout : ∀ x, ∃ y, R x y) (σ : relationAut R)
    (q : Blocks R) :
    blockHom R σ (successor R hout q) = successor R hout (blockHom R σ q) := by
  refine Quotient.inductionOn q ?_
  intro x
  change project R (σ.val (chosen R hout x)) = successor R hout (project R (σ.val x))
  exact (successor_project R hout ((σ.property x _).mpr
    (chosen_arrow R hout x))).symm

abbrev Fiber (q : Blocks R) := {x : V // project R x = q}

private theorem kernel_project (σ : (blockHom R).ker) (x : V) :
    project R (σ.val.val x) = project R x := by
  exact congrArg (fun p : Equiv.Perm (Blocks R) => p (project R x)) σ.property

/-- Restriction to each actual block, with no faithfulness assumption on the block action. -/
noncomputable def kernelRestriction (σ : (blockHom R).ker) (q : Blocks R) :
    Equiv.Perm (Fiber R q) where
  toFun x := ⟨σ.val.val x.val, (kernel_project R σ x.val).trans x.property⟩
  invFun x := ⟨σ.val.val.symm x.val, (kernel_project R σ⁻¹ x.val).trans x.property⟩
  left_inv x := Subtype.ext (σ.val.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (σ.val.val.apply_symm_apply x.val)

private theorem kernelRestriction_injective : Function.Injective (kernelRestriction R) := by
  intro σ τ h
  apply Subtype.ext
  apply Subtype.ext
  ext x
  have hh := congrArg (fun F => (F (project R x)) ⟨x, rfl⟩) h
  exact congrArg Subtype.val hh

/-- Both symmetry controls apply to the entire relation automorphism group. -/
theorem relation_aut_joint_bound [Finite V]
    (hout : ∀ x, ∃ y, R x y) (hin : ∀ y, ∃ x, R x y) :
    Nat.card (relationAut R) ≤
      Nat.card (Subgroup.centralizer ({beta R hout hin} : Set (Equiv.Perm (Blocks R)))) *
      Nat.card (∀ q : Blocks R, Equiv.Perm (Fiber R q)) := by
  have hk : Nat.card (blockHom R).ker ≤
      Nat.card (∀ q : Blocks R, Equiv.Perm (Fiber R q)) :=
    Nat.card_le_card_of_injective (kernelRestriction R) (kernelRestriction_injective R)
  let C := Subgroup.centralizer ({beta R hout hin} : Set (Equiv.Perm (Blocks R)))
  have hr : (blockHom R).range ≤ C := by
    rintro σ ⟨g, rfl⟩
    intro τ hτ
    have hτ' : τ = beta R hout hin := Set.mem_singleton_iff.mp hτ
    subst τ
    ext q
    exact (block_successor_commute R hout g q).symm
  have hc : Nat.card (blockHom R).range ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun σ : (blockHom R).range => (⟨σ.val, hr σ.property⟩ : C))
      (fun x y h => Subtype.ext (show x.val = y.val from congrArg (fun z : C => z.val) h))
  rw [← Subgroup.card_ker_mul_card_range (blockHom R)]
  exact (Nat.mul_le_mul hk hc).trans_eq (Nat.mul_comm _ _)

end D5.S3.FiniteGroups.SuccessorQuotient
