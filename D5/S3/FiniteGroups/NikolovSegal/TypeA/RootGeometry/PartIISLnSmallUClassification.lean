/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallUClassification
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallUClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnSmallPositiveImages
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Actual common field/graph and whole-U action in rank>=5/cardF>2.
The accepted triangle/graph/generation kernels are reused unchanged. -/
namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F
variable [Fintype F]

theorem sl_bare_root_field_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F, ∃ sigma : Equiv.Perm (PositiveIndex n),
      ∃ chi : PositiveIndex n → Fˣ, ∃ phi : RingAut F,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (diagonalTorus n F).map beta.toMonoidHom = diagonalTorus n F ∧
      (∀ r, (rootSubgroup r).map beta.toMonoidHom = rootSubgroup (F := F) (sigma r)) ∧
      ∀ r t, beta (root r t) = root (sigma r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,f,hU,hT,hs,hb⟩ := sl_bare_positive_root_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (root r t) = root (sigma r) (f r t) at hb
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k) (t u : F),
      root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t) *
        root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u) *
        (root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t))⁻¹ *
        (root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u))⁻¹ =
        root (sigma ⟨(i,k),hij.trans hjk⟩) (f ⟨(i,k),hij.trans hjk⟩ (t*u)) := by
    intro i j k hij hjk t u
    have hc : root ⟨(i,j),hij⟩ t*root ⟨(j,k),hjk⟩ u*
        (root ⟨(i,j),hij⟩ t)⁻¹*(root ⟨(j,k),hjk⟩ u)⁻¹ = root ⟨(i,k),hij.trans hjk⟩ (t*u) :=
      transvection_commutator_chain hij hjk t u
    simpa only [map_mul,map_inv,hb] using congrArg beta hc
  obtain ⟨phi,hphi⟩ := common_root_field (by omega) sigma f hinc
  let chi : PositiveIndex n → Fˣ := fun r => Units.mk0 (f r 1)
    (fun h => one_ne_zero ((f r).map_eq_zero_iff.mp h))
  refine ⟨c,sigma,chi,phi,hU,hT,hs,?_⟩
  intro r t
  change beta (root r t) = root (sigma r) ((chi r:F)*phi t)
  rw [hb,hphi]
  rfl

theorem sl_bare_root_graph_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F, ∃ chi : PositiveIndex n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (diagonalTorus n F).map beta.toMonoidHom = diagonalTorus n F ∧
      ∀ r t, beta (root r t) = root (if eps then reflectRoot r else r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,chi,phi,hU,hT,hs,hb⟩ := sl_bare_root_field_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (root r t)=root (sigma r) ((chi r:F)*phi t) at hb
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩) := by
    intro i j k hij hjk
    have he0 := transvection_commutator_chain hij hjk (1:F) 1
    change root ⟨(i,j),hij⟩ 1*root ⟨(j,k),hjk⟩ 1*(root ⟨(i,j),hij⟩ 1)⁻¹*
      (root ⟨(j,k),hjk⟩ 1)⁻¹=root ⟨(i,k),hij.trans hjk⟩ (1*1) at he0
    have he := congrArg beta he0
    simp only [map_mul,map_inv,hb,map_one,mul_one,one_mul] at he
    exact root_commutator_compose _ _ _ _ _ _ (chi _).ne_zero (chi _).ne_zero (chi _).ne_zero he
  rcases root_permutation_identity_or_reflection (by omega) sigma hinc with hid|hrev
  · refine ⟨c,chi,phi,false,hU,hT,?_⟩
    simpa only [Bool.false_eq_true,ite_false,hid] using hb
  · refine ⟨c,chi,phi,true,hU,hT,?_⟩
    simpa only [ite_true,hrev] using hb

theorem sl_bare_full_U_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
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

end NikolovSegal.SLnSmallField

namespace NikolovSegal.PSLnSmallField
open Matrix NikolovSegal.SLnRootAction NikolovSegal.PSLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.SLnSmallField NikolovSegal.PartIIProposition6_5
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)
local notation "T" => diagonalTorus n F
variable [Fintype F]

theorem psl_bare_root_field_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F, ∃ sigma : Equiv.Perm (PositiveIndex n),
      ∃ chi : PositiveIndex n → Fˣ, ∃ phi : RingAut F,
      let beta := MulAut.conj c * alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      (∀ r, (projectiveRoot r).map beta.toMonoidHom = projectiveRoot (F := F) (sigma r)) ∧
      ∀ r t, beta (projectiveRootValue r t) = projectiveRootValue (sigma r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,f,hU,hT,hs,hb⟩ := psl_bare_positive_root_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (projectiveRootValue r t) = projectiveRootValue (sigma r) (f r t) at hb
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k) (t u : F),
      root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t) *
        root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u) *
        (root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t))⁻¹ *
        (root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u))⁻¹ =
        root (sigma ⟨(i,k),hij.trans hjk⟩) (f ⟨(i,k),hij.trans hjk⟩ (t*u)) := by
    intro i j k hij hjk t u
    have hproj : projectiveRootValue ⟨(i,j),hij⟩ t*projectiveRootValue ⟨(j,k),hjk⟩ u*
        (projectiveRootValue ⟨(i,j),hij⟩ t)⁻¹*(projectiveRootValue ⟨(j,k),hjk⟩ u)⁻¹ =
        projectiveRootValue ⟨(i,k),hij.trans hjk⟩ (t*u) := by
      simpa [q,root,projectiveRootValue,map_mul,map_inv] using
        congrArg q (transvection_commutator_chain hij hjk t u)
    have he := congrArg beta hproj
    simp only [map_mul,map_inv,hb] at he
    let A := root (sigma ⟨(i,j),hij⟩) (f ⟨(i,j),hij⟩ t)
    let B := root (sigma ⟨(j,k),hjk⟩) (f ⟨(j,k),hjk⟩ u)
    have hx : A*B*A⁻¹*B⁻¹ ∈ Uplus n F :=
      (Uplus n F).mul_mem
        ((Uplus n F).mul_mem ((Uplus n F).mul_mem (root_mem_Uplus _ _) (root_mem_Uplus _ _))
          ((Uplus n F).inv_mem (root_mem_Uplus _ _)))
        ((Uplus n F).inv_mem (root_mem_Uplus _ _))
    exact quotient_injective_on_U _ _ hx (root_mem_Uplus _ _)
      (by simpa only [projectiveRootValue,map_mul,map_inv] using he)
  obtain ⟨phi,hphi⟩ := common_root_field (by omega) sigma f hinc
  let chi : PositiveIndex n → Fˣ := fun r => Units.mk0 (f r 1)
    (fun h => one_ne_zero ((f r).map_eq_zero_iff.mp h))
  refine ⟨c,sigma,chi,phi,hU,hT,hs,?_⟩
  intro r t
  change beta (projectiveRootValue r t) = projectiveRootValue (sigma r) ((chi r:F)*phi t)
  rw [hb,hphi]
  rfl

theorem psl_bare_root_graph_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
    (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F, ∃ chi : PositiveIndex n → Fˣ,
      ∃ phi : RingAut F, ∃ eps : Bool,
      let beta := MulAut.conj c * alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      ∀ r t, beta (projectiveRootValue r t) =
        projectiveRootValue (if eps then reflectRoot r else r) ((chi r:F)*phi t) := by
  classical
  obtain ⟨c,sigma,chi,phi,hU,hT,hs,hb⟩ := psl_bare_root_field_coordinates p hn hF alpha
  let beta := MulAut.conj c * alpha
  change ∀ r t, beta (projectiveRootValue r t)=projectiveRootValue (sigma r) ((chi r:F)*phi t) at hb
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  have hinc : ∀ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩) := by
    intro i j k hij hjk
    have he0 := congrArg q (transvection_commutator_chain hij hjk (1:F) 1)
    have he1 : projectiveRootValue ⟨(i,j),hij⟩ (1:F)*projectiveRootValue ⟨(j,k),hjk⟩ 1*
        (projectiveRootValue ⟨(i,j),hij⟩ 1)⁻¹*(projectiveRootValue ⟨(j,k),hjk⟩ 1)⁻¹ =
        projectiveRootValue ⟨(i,k),hij.trans hjk⟩ 1 := by
      simpa [q,projectiveRootValue,root,map_mul,map_inv] using he0
    have he := congrArg beta he1
    simp only [map_mul,map_inv,hb,map_one,mul_one] at he
    let A := root (sigma ⟨(i,j),hij⟩) (chi ⟨(i,j),hij⟩:F)
    let B := root (sigma ⟨(j,k),hjk⟩) (chi ⟨(j,k),hjk⟩:F)
    have hx : A*B*A⁻¹*B⁻¹ ∈ Uplus n F := (Uplus n F).mul_mem
      ((Uplus n F).mul_mem ((Uplus n F).mul_mem (root_mem_Uplus _ _) (root_mem_Uplus _ _))
        ((Uplus n F).inv_mem (root_mem_Uplus _ _))) ((Uplus n F).inv_mem (root_mem_Uplus _ _))
    have hc := quotient_injective_on_U _ _ hx (root_mem_Uplus _ _)
      (by simpa only [projectiveRootValue,map_mul,map_inv] using he)
    exact root_commutator_compose _ _ _ _ _ _ (chi _).ne_zero (chi _).ne_zero (chi _).ne_zero hc
  rcases root_permutation_identity_or_reflection (by omega) sigma hinc with hid|hrev
  · refine ⟨c,chi,phi,false,hU,hT,?_⟩
    simpa only [Bool.false_eq_true,ite_false,hid] using hb
  · refine ⟨c,chi,phi,true,hU,hT,?_⟩
    simpa only [ite_true,hrev] using hb

theorem psl_bare_full_U_diagonal_field_graph (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 4 < n) (hF : 2 < Fintype.card F)
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

end NikolovSegal.PSLnSmallField
