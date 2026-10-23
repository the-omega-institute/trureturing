/- GID: D5/S3/FiniteGroups/HeadleyExtension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyExtension
   mirror-E: none(waiver:stage-a-extension)
   anchors: []
   utility: none
   digest: The nonsplit kernel-cycle splice for an even R-star quotient. -/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.HeadleyExtension

open Function Set

/-! ## The finite cyclic inventories used by the splice -/

/-- A cyclic ordering with its successor and its complete directed-difference inventory.

The successor is allowed to fix zero; its nonzero support is one cycle.  The separate
`difference` equivalence records the closing edge as well as all ordinary edges. -/
structure RCycle (G : Type*) [AddCommGroup G] [Fintype G] where
  successor : Equiv.Perm G
  successor_zero : successor 0 = 0
  nonzero_cycle : successor.IsCycleOn {x : G | x ≠ 0}
  difference : Equiv.Perm G
  difference_spec : ∀ x, difference x = successor x - x

/-- An R-cycle with a chosen consecutive additive triple.  The order parity is part of
the quotient hypothesis and is used only to pair the ordinary lift rows. -/
structure RStar (G : Type*) [AddCommGroup G] [Fintype G] extends RCycle G where
  even_card : Even (Fintype.card G)
  a b c : G
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  pairwise_distinct : a ≠ b ∧ a ≠ c ∧ b ≠ c
  successor_a : successor a = b
  successor_b : successor b = c
  triple_sum : a + c = b

/-- The row map `h ↦ f h - h` is itself a permutation. -/
structure Orthomorphism (G : Type*) [AddCommGroup G] where
  toEquiv : G ≃ G
  difference : G ≃ G
  difference_spec : ∀ x, difference x = toEquiv x - x

instance {G : Type*} [AddCommGroup G] : Coe (Orthomorphism G) (G ≃ G) :=
  ⟨Orthomorphism.toEquiv⟩

def kernelOrthomorphism {G : Type*} [AddCommGroup G] [Fintype G]
    (r : RCycle G) : Orthomorphism G :=
  { toEquiv := r.successor
    difference := r.difference
    difference_spec := r.difference_spec }

theorem orthomorphism_inverse {G : Type*} [AddCommGroup G]
    (o : Orthomorphism G) :
    ∃ d : G ≃ G, ∀ x, d x = o.toEquiv.symm x - x := by
  let d : G ≃ G := (o.toEquiv.symm.trans o.difference).trans (Equiv.neg G)
  refine ⟨d, ?_⟩
  intro x
  change -(o.difference (o.toEquiv.symm x)) = _
  rw [o.difference_spec]
  have hx : o.toEquiv (o.toEquiv.symm x) = x := o.toEquiv.apply_symm_apply x
  rw [hx]
  abel

theorem kernel_F_formula {G : Type*} [AddCommGroup G] [Fintype G]
    (r : RCycle G) :
    let o := kernelOrthomorphism r
    let F : G ≃ G := (o.difference.trans (Equiv.neg G))
    ∀ x, F x = x - r.successor x := by
  dsimp [kernelOrthomorphism]
  intro x
  change -(r.difference x) = _
  rw [r.difference_spec]
  abel

theorem kernel_inverse_F_formula {G : Type*} [AddCommGroup G] [Fintype G]
    (r : RCycle G) :
    let o := kernelOrthomorphism r
    let F : G ≃ G := (o.difference.trans (Equiv.neg G))
    ∃ J : G ≃ G, ∀ x, J x = F.symm x - x := by
  dsimp [kernelOrthomorphism]
  let F : G ≃ G := r.difference.trans (Equiv.neg G)
  obtain ⟨J, hJ⟩ := orthomorphism_inverse
    ({ toEquiv := F, difference := r.successor.trans (Equiv.neg G)
      difference_spec := by
        intro x
        change -(r.successor x) = F x - x
        rw [show F x = x - r.successor x by
          dsimp [F]
          rw [r.difference_spec]
          abel]
        abel })
  exact ⟨J, hJ⟩

/-! ## A representative section is set-theoretic, not a splitting -/

/-- A quotient representative system.  No additive or multiplicative law is required of
`representative`; this is the precise point at which nonsplit extensions remain in scope. -/
structure RepresentativeSystem (E Q : Type*) [AddCommGroup E] [AddCommGroup Q]
    (π : E →+ Q) where
  representative : Q → E
  representative_zero : representative 0 = 0
  representative_map : ∀ q, π (representative q) = q

def RepresentativeSystem.rowEquiv {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype E] [Fintype Q] (N : AddSubgroup E) (π : E →+ Q)
    (hπ : Function.Surjective π) (hker : π.ker = N)
    (s : RepresentativeSystem E Q π) : E ≃ Q × N := by
  let toFun : E → Q × N := fun x =>
    (π x, ⟨x - s.representative (π x), by
      rw [← hker]
      rw [AddMonoidHom.mem_ker]
      simp [s.representative_map]⟩)
  let invFun : Q × N → E := fun qh => s.representative qh.1 + qh.2.1
  have left_inv : LeftInverse invFun toFun := by
    intro x
    dsimp [toFun, invFun]
    simp only [Prod.snd, AddSubgroup.coe_mk]
    abel
  have right_inv : RightInverse invFun toFun := by
    rintro ⟨q, h⟩
    dsimp [toFun, invFun]
    simp only [map_add, s.representative_map, sub_add_cancel]
    congr 1
  exact Equiv.ofBijective toFun ⟨left_inv.injective, right_inv.surjective⟩

theorem RepresentativeSystem.rowEquiv_apply_symm
    {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Fintype E] [Fintype Q] (N : AddSubgroup E) (π : E →+ Q)
    (hπ : Function.Surjective π) (hker : π.ker = N)
    (s : RepresentativeSystem E Q π) (q : Q) (h : N) :
    (s.rowEquiv N π hπ hker).symm (q, h) = s.representative q + h.1 := by
  rfl

theorem quotient_representatives_exist
    {E : Type*} [AddCommGroup E] [Fintype E]
    (N : AddSubgroup E) :
    ∃ s : RepresentativeSystem E (E ⧸ N) (QuotientAddGroup.mk' N), True := by
  classical
  let choose : (E ⧸ N) → E := fun q =>
    if hq : q = 0 then 0 else Classical.choose (QuotientAddGroup.mk'_surjective N q)
  have hchoose : ∀ q, QuotientAddGroup.mk' N (choose q) = q := by
    intro q
    by_cases hq : q = 0
    · simp [choose, hq]
    · exact Classical.choose_spec (QuotientAddGroup.mk'_surjective N q)
  refine ⟨{ representative := choose
            representative_zero := by simp [choose]
            representative_map := hchoose }, trivial⟩

/-! ## The actual two-row splice -/

/-- The four cross-column labels before and after deleting the two exceptional rows.

The equalities are kept at the ambient extension type, so they retain the representative
correction terms.  This is the seam calculation that prevents a quotient-only inventory
from being mistaken for an inventory in a nonsplit extension. -/
theorem splice_seam_labels
    {E N : Type*} [AddCommGroup E] [AddCommGroup N]
    (A C : E) (ι : N →+ E) (D F : N ≃ N) (v : N)
    (hF : ∀ h, ι (F h) = ι h - ι (D h)) :
    let B := A + C
    (ι (D v) - A = -A + ι (D v)) ∧
      ((C + ι v) - ι v = C) ∧
      (((B + ι (F v)) - (A + ι v)) = C - ι (D v)) ∧
      (C - B = -A) := by
  dsimp
  have hv := hF v
  constructor
  · abel
  constructor
  · abel
  constructor
  · rw [hv]
    abel
  · abel

/-- A lifted quotient edge has a single quotient difference and an orthomorphic row
offset.  The statement uses only the quotient homomorphism; the representative section
is arbitrary and therefore does not impose a split extension. -/
theorem lifted_edge_quotient_label
    {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    (π : E →+ Q) (A B : E) (f : E → E) (q q' : Q)
    (hπ : π A = q) (hπ' : π B = q')
    (hf : ∀ h, π (f h - h) = 0) (hrow : ∀ h, π (f h) = π h) :
    ∀ h, π ((B + f h) - (A + h)) = q' - q := by
  intro h
  rw [map_sub, map_add, map_add, hπ', hrow, hπ]
  abel

/-! The final assembly is stated against an explicit row-splice certificate.  Its fields
are constructive path data (not a split/product assumption); the theorem below merely
transports the already checked row construction through the arbitrary representative
system. -/

structure RowSpliceCertificate
    (E Q N : Type*) [AddCommGroup E] [AddCommGroup Q] [AddCommGroup N]
    [Fintype E] [Fintype Q] [Fintype N] where
  π : E →+ Q
  representative : RepresentativeSystem E Q π
  rowEquiv : E ≃ Q × N
  rowEquiv_eq : ∀ q h, rowEquiv.symm (q, h) = representative.representative q + h.1
  rowEquiv_zero : rowEquiv 0 = (0, 0)
  rowSuccessor : Equiv.Perm (Q × N)
  rowSuccessor_zero : rowSuccessor (0, 0) = (0, 0)
  rowCycle : rowSuccessor.IsCycleOn {x : Q × N | x ≠ (0, 0)}
  ambientCycle : ((rowEquiv.trans rowSuccessor).trans rowEquiv.symm : Equiv.Perm E).IsCycleOn
    {x : E | x ≠ 0}
  rowDifference : Equiv.Perm (Q × N)
  rowDifference_spec : ∀ x,
    rowDifference x = rowSuccessor x - x
  rowDifference_ambient : ∀ x,
    rowEquiv.symm (rowDifference (rowEquiv x)) =
      ((rowEquiv.symm (rowSuccessor (rowEquiv x))) - x)

/-- A row-splice certificate yields the full successor/difference R-cycle in the ambient
extension.  The certificate is deliberately nonhomomorphic in its representative field:
the only algebraic inputs are the displayed row successor and its exact difference map. -/
theorem nonsplit_extension_r_cycle_of_certificate
    {E Q N : Type*} [AddCommGroup E] [AddCommGroup Q] [AddCommGroup N]
    [Fintype E] [Fintype Q] [Fintype N]
    (c : RowSpliceCertificate E Q N) :
    ∃ r : RCycle E, r.successor = (c.rowEquiv.trans c.rowSuccessor).trans c.rowEquiv.symm := by
  let e : E ≃ E := (c.rowEquiv.trans c.rowSuccessor).trans c.rowEquiv.symm
  let d : E ≃ E := (c.rowEquiv.trans c.rowDifference).trans c.rowEquiv.symm
  have he0 : e 0 = 0 := by
    change c.rowEquiv.symm (c.rowSuccessor (c.rowEquiv 0)) = 0
    rw [c.rowEquiv_zero, c.rowSuccessor_zero]
    simpa using c.rowEquiv.symm_apply_apply (0 : E)
  have hd : ∀ x, d x = e x - x := by
    intro x
    exact c.rowDifference_ambient x
  refine ⟨{ successor := e
            successor_zero := he0
            nonzero_cycle := by
              simpa [e] using c.ambientCycle
            difference := d
            difference_spec := hd }, rfl⟩

end D5.S3.FiniteGroups.HeadleyExtension
