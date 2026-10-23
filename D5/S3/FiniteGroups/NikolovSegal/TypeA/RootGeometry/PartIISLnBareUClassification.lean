/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareUClassification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareUClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareRootGraph
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnUGeneration
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootDiagonal
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnStandardRootActions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Genuine root graph/field coordinates extend to the WHOLE literal U,
using the proved simple-root generation, with a single diagonal tuple. -/
theorem root_graph_coordinates_full_U {K : Type*} [Group K]
    (f q : SpecialLinearGroup (Fin n) F →* K)
    (chi : PositiveIndex n → Fˣ) (phi : RingAut F) (eps : Bool)
    (hroot : ∀ r t, f (root r t)=q (root (if eps then reflectRoot r else r) ((chi r:F)*phi t))) :
    ∃ a : Fin n → Fˣ, ∀ x ∈ Uplus n F, f x=q (diagonalFieldGraph a phi eps x) := by
  classical
  obtain ⟨a,ha⟩ := exists_diagonal_simple_coefficients chi eps
  refine ⟨a,?_⟩
  apply hom_ext_on_simple_roots f (q.comp (diagonalFieldGraph a phi eps).toMonoidHom)
  intro r t
  change f (root (simpleRoot r) t)=q (diagonalFieldGraph a phi eps (root (simpleRoot r) t))
  rw [hroot,diagonalFieldGraph_simple_root]
  let s := if eps then reflectRoot (simpleRoot r) else simpleRoot r
  change q (root s ((chi (simpleRoot r):F)*phi t))=
    q (root s ((a s.val.1:F)*phi t*(((a s.val.2)⁻¹:Fˣ):F)))
  have he : (a s.val.1:F)*(((a s.val.2)⁻¹:Fˣ):F)=(chi (simpleRoot r):F) :=
    congrArg (fun z : Fˣ => (z:F)) (ha r)
  congr 2
  calc
    (chi (simpleRoot r):F)*phi t = ((a s.val.1:F)*(((a s.val.2)⁻¹:Fˣ):F))*phi t := by rw [he]
    _ = _ := by ring

variable [Fintype F]

/-- Bare actual SLn automorphisms have the prescribed diagonal/field/graph
restriction on the FULL upper-unitriangular subgroup, in rank>=3 and
finite field size>4. The inner correction precedes every U target; no
root-preservation or classification premise is supplied. -/
theorem sl_bare_full_U_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
    (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F, ∃ a : Fin n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom=Uplus n F ∧
      (diagonalTorus n F).map beta.toMonoidHom=diagonalTorus n F ∧
      ∀ x ∈ Uplus n F, beta x=diagonalFieldGraph a phi eps x := by
  classical
  obtain ⟨c,chi,phi,eps,hU,hT,hb⟩ := sl_bare_root_graph_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (root r t)=root (if eps then reflectRoot r else r) ((chi r:F)*phi t) at hb
  obtain ⟨a,ha⟩ := root_graph_coordinates_full_U beta.toMonoidHom (MonoidHom.id _) chi phi eps hb
  exact ⟨c,a,phi,eps,hU,hT,ha⟩
end NikolovSegal.SLnRootAction

namespace NikolovSegal.PSLnRootAction
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}

/-- Intrinsic bare PSLn classification on the full projective U, expressed
by literal quotient equalities for EVERY actual U representative. No SL
lift of the bare projective automorphism is assumed or constructed. -/
theorem psl_bare_full_U_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
    (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F, ∃ a : Fin n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
      (projectiveUplus n F).map beta.toMonoidHom=projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom=projectiveDiagonalTorus n F ∧
      ∀ x ∈ Uplus n F, beta (q x)=q (diagonalFieldGraph a phi eps x) := by
  classical
  obtain ⟨c,chi,phi,eps,hU,hT,hb⟩ := psl_bare_root_graph_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  change ∀ r t, beta (projectiveRootValue r t)=
    projectiveRootValue (if eps then reflectRoot r else r) ((chi r:F)*phi t) at hb
  have hroot : ∀ r t, (beta.toMonoidHom.comp q) (root r t)=
      q (root (if eps then reflectRoot r else r) ((chi r:F)*phi t)) := hb
  obtain ⟨a,ha⟩ := root_graph_coordinates_full_U (beta.toMonoidHom.comp q) q chi phi eps hroot
  exact ⟨c,a,phi,eps,hU,hT,ha⟩
end NikolovSegal.PSLnRootAction
