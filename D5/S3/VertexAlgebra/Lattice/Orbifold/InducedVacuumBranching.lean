/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/InducedVacuumBranching
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/InducedVacuumBranching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Induced-vacuum evaluation transports the actual lattice modes and grades. -/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Invariants
import OmegaBuild.Commands

/-!
The identity sector in Evans–Gannon, arXiv:1804.11145, (3.5) has
representation `Ind_K^G 1`. Evaluation at the induced unit identifies its
multiplicity space in the lattice carrier with the subgroup-fixed states,
with their actual modes and, for a grading-preserving action, their grades.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.InducedVacuumBranching

open CategoryTheory
open LatticeGeneratingFieldLocality (LatticeData Carrier)
open LatticeAllStateField (Y)
open LatticePositiveEnergy (grade positive_actual_mode_grade)
open scoped VertexOperator

noncomputable section

variable {G : Type} [Group G]

local notation "IndTrivial" K => Rep.ind (Subgroup.subtype K) (Rep.trivial ℂ ↥K ℂ)
local notation "inducedUnit" K =>
  Representation.IndV.mk (Subgroup.subtype K) (Representation.trivial ℂ ↥K ℂ) 1 (1 : ℂ)

private def trivialHomToInvariants {H : Type} [Group H] (B : Rep ℂ H) :
    (Rep.trivial ℂ H ℂ ⟶ B) ≃ₗ[ℂ] ↥B.ρ.invariants where
  toEquiv := ((Rep.invariantsAdjunction ℂ H).homEquiv (ModuleCat.of ℂ ℂ) B).trans
    ((ModuleCat.homLinearEquiv (R := ℂ) (S := ℂ)).trans
      (LinearMap.ringLmapEquivSelf ℂ ℂ ↥B.ρ.invariants)).toEquiv
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable (D : LatticeData) (K : Subgroup G) (ρ : Representation ℂ G (Carrier D))

/-- Evaluation at the class of `1 ⊗ 1` identifies the actual induced-vacuum
multiplicity space with the states fixed by `K`. -/
def evaluate : ((IndTrivial K) ⟶ Rep.of ρ) ≃ₗ[ℂ]
    ↥(Representation.invariants (ρ.comp K.subtype)) :=
  (Rep.indResHomEquiv K.subtype (Rep.trivial ℂ K ℂ) (Rep.of ρ)).trans
    (trivialHomToInvariants (Rep.res K.subtype (Rep.of ρ)))

/-- The induction and invariants adjunctions evaluate at the induced unit. -/
@[simp] theorem evaluate_apply (f : (IndTrivial K) ⟶ Rep.of ρ) :
    (evaluate D K ρ f : Carrier D) = f.hom (inducedUnit K) := rfl

variable (hmode : ∀ (g : G) (a b : Carrier D) (q : ℤ),
    ρ g (((Y D a)[[q]]) b) = ((Y D (ρ g a))[[q]]) (ρ g b))

private def modeRepHom (a : ρ.invariants) (q : ℤ) : Rep.of ρ ⟶ Rep.of ρ :=
  Rep.ofHom ⟨(Y D (a : Carrier D))[[q]], fun g => LinearMap.ext fun b => by
    change ((Y D (a : Carrier D))[[q]]) (ρ g b) = ρ g (((Y D (a : Carrier D))[[q]]) b)
    simpa only [a.property g] using (hmode g (a : Carrier D) b q).symm⟩

/-- A fixed state's actual mode acts on the multiplicity space by postcomposition. -/
def postcompMode (a : ρ.invariants) (q : ℤ) : Module.End ℂ ((IndTrivial K) ⟶ Rep.of ρ) :=
  Linear.rightComp ℂ (IndTrivial K) (modeRepHom D ρ hmode a q)

/-- A `G`-fixed state's actual lattice mode restricted to `V^K`. -/
def invariantMode (a : ρ.invariants) (q : ℤ) :
    Module.End ℂ ↥(Representation.invariants (ρ.comp K.subtype)) :=
  ((Y D (a : Carrier D))[[q]]).restrict
    (p := Representation.invariants (ρ.comp K.subtype))
    (q := Representation.invariants (ρ.comp K.subtype)) fun b hb k => by
      have hkb : ρ (k : G) b = b := hb k
      change ρ (k : G) (((Y D (a : Carrier D))[[q]]) b) = ((Y D (a : Carrier D))[[q]]) b
      simpa only [a.property (k : G), hkb] using hmode (k : G) (a : Carrier D) b q

/-- Evaluation intertwines postcomposition with the actual mode on the fixed lattice carrier. -/
theorem evaluate_postcompMode (a : ρ.invariants) (q : ℤ) (f : (IndTrivial K) ⟶ Rep.of ρ) :
    evaluate D K ρ (postcompMode D K ρ hmode a q f) =
      invariantMode D K ρ hmode a q (evaluate D K ρ f) := by
  apply Subtype.ext
  rfl

/-- The weight of the evaluated state detects whether the whole image of the
intertwiner lands in that grade. In particular this applies to weight two. -/
theorem evaluate_mem_grade_iff
    (hgrade : ∀ (g : G) (n : ℤ) (v : Carrier D), v ∈ grade D n → ρ g v ∈ grade D n)
    (f : (IndTrivial K) ⟶ Rep.of ρ) (n : ℤ) :
    (evaluate D K ρ f : Carrier D) ∈ grade D n ↔
      ∀ x : IndTrivial K, f.hom x ∈ grade D n := by
  rw [evaluate_apply]
  refine ⟨fun hu => ?_, fun hf => hf (inducedUnit K)⟩
  have hzero : (grade D n).mkQ.comp f.hom.toLinearMap = 0 := by
    apply Representation.IndV.hom_ext (φ := K.subtype) (ρ := Representation.trivial ℂ K ℂ)
    intro g
    apply LinearMap.ext_ring
    change (grade D n).mkQ (f.hom
      (Representation.IndV.mk K.subtype (Representation.trivial ℂ K ℂ) g 1)) = 0
    have hcomm := Rep.hom_comm_apply f g⁻¹ (inducedUnit K)
    change f.hom (Representation.ind K.subtype (Representation.trivial ℂ K ℂ) g⁻¹
      (inducedUnit K)) = ρ g⁻¹ (f.hom (inducedUnit K)) at hcomm
    rw [Representation.ind_mk, inv_inv, one_mul] at hcomm
    rw [hcomm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hgrade g⁻¹ n _ hu
  intro x
  exact (Submodule.Quotient.mk_eq_zero (grade D n)).mp (LinearMap.congr_fun hzero x)

/-- The actual mode shifts the multiplicity grading by the ordinary lattice mode law. -/
theorem postcompMode_mem_grade
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hgrade : ∀ (g : G) (n : ℤ) (v : Carrier D), v ∈ grade D n → ρ g v ∈ grade D n)
    (a : ρ.invariants) (f : (IndTrivial K) ⟶ Rep.of ρ) (m n q : ℤ)
    (ha : (a : Carrier D) ∈ grade D m) (hf : ∀ x : IndTrivial K, f.hom x ∈ grade D n) :
    ∀ x : IndTrivial K, (postcompMode D K ρ hmode a q f).hom x ∈ grade D (m + n - q - 1) := by
  apply (evaluate_mem_grade_iff D K ρ hgrade
    (postcompMode D K ρ hmode a q f) (m + n - q - 1)).mp
  rw [evaluate_postcompMode]
  exact positive_actual_mode_grade D hD m n q (a : Carrier D) (evaluate D K ρ f)
    ha ((evaluate_mem_grade_iff D K ρ hgrade f n).mpr hf)

#print axioms evaluate
#print axioms evaluate_postcompMode
#print axioms evaluate_mem_grade_iff
#print axioms postcompMode_mem_grade

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.InducedVacuumBranching
