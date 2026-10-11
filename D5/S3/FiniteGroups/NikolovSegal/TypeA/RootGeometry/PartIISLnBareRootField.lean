/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareRootField
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnBareRootField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}

/-- Actual bare SLn positive-root semilinearity, in every rank>=3 and finite
field of size>4. ALL root images and ONE common multiplicative field map are
derived; the remaining permutation-to-graph identification is not asserted. -/
theorem sl_bare_root_field_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
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
  obtain ⟨phi,hphi⟩ := common_root_field hn sigma f hinc
  let chi : PositiveIndex n → Fˣ := fun r => Units.mk0 (f r 1)
    (fun h => one_ne_zero ((f r).map_eq_zero_iff.mp h))
  refine ⟨c,sigma,chi,phi,hU,hT,hs,?_⟩
  intro r t
  change beta (root r t) = root (sigma r) ((chi r:F)*phi t)
  rw [hb,hphi]
  rfl

end NikolovSegal.SLnRootAction

namespace NikolovSegal.PSLnRootAction
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnTorusAlignment
open NikolovSegal.SLnRootAction
universe u
variable {F : Type u} [Field F] [Fintype F] {n : ℕ}

/-- Actual bare PSLn root semilinearity with ONE field automorphism, with no
SL lift. All commutator equalities lift only on genuine U representatives. -/
theorem psl_bare_root_field_coordinates (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2 < n) (hF : 4 < Fintype.card F)
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
  obtain ⟨phi,hphi⟩ := common_root_field hn sigma f hinc
  let chi : PositiveIndex n → Fˣ := fun r => Units.mk0 (f r 1)
    (fun h => one_ne_zero ((f r).map_eq_zero_iff.mp h))
  refine ⟨c,sigma,chi,phi,hU,hT,hs,?_⟩
  intro r t
  change beta (projectiveRootValue r t) = projectiveRootValue (sigma r) ((chi r:F)*phi t)
  rw [hb,hphi]
  rfl

end NikolovSegal.PSLnRootAction
