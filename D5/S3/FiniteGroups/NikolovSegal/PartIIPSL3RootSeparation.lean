/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3RootSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3TorusAlignment
import D5.S3.FiniteGroups.NikolovSegal.PartIIA2RootSeparation

/-! Actual projective A2 root separation for Nikolov--Segal Part II
Inn D Phi Gamma normalization. Genuine quotient torus preimages and
actual SL3 kernel arithmetic are consumed; no automorphism lift is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "psl3Known%" id:ident : term => do
  let env ← getEnv
  let owner := if id.getId == `center_le_torus then "PartIIPSL3TorusAlignment"
    else if id.getId == `mem_projectiveCentralRoot_iff then "PartIIPSL3RootGeometry"
    else "PartIIA2RootSeparation"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal." ++ owner
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual projective root kernel {id} not found"
namespace NikolovSegal.PartIIPSL3RootSeparation
open PartIIPSL3Unipotent PartIIPSL3UnipotentNormalizer PartIIPSL3RootGeometry
open PartIIPSL3TorusAlignment PartIIA2Orbital PartIIA2RootNormalization
open PartIIA2TorusAlignment PartIIA2RootSeparation Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev pi : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (Subgroup.center _)
private abbrev rt (r : Fin 3) (t : F) : SL(3,F) := (a2Kernel% root) r t
private abbrev prt (r : Fin 3) (t : F) : PSL(3,F) := pi (rt r t)
private abbrev K (r : Fin 2) : Subgroup SL(3,F) := (psl3Known% kernel) r

private theorem prt_injective (r : Fin 3) : Function.Injective (prt (F := F) r) := by
  intro t s h
  have hh : (⟨rt r t,(a2Kernel% root_mem) r t⟩ : PartIISL3UnipotentSylow.U3)=
      ⟨rt r s,(a2Kernel% root_mem) r s⟩ := quotient_U3_injective h
  exact (psl3Known% rt_injective) r (congrArg Subtype.val hh)

private theorem card_projective_root (r : Fin 3) : Nat.card (projectivePositiveRoot (F := F) r)=Nat.card F := by
  let f : F → projectivePositiveRoot (F := F) r := fun t => ⟨prt r t,rt r t,⟨t,rfl⟩,rfl⟩
  have hi : Function.Injective f := fun _ _ h => prt_injective r (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    rintro ⟨g,z,⟨t,rfl⟩,rfl⟩
    exact ⟨t,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

private theorem noncentral_prt (r : Fin 2) : prt (F := F) r.castSucc 1 ∉ projectivePositiveRoot (F := F) 2 := by
  rintro ⟨z,⟨t,rfl⟩,h⟩
  have hh : (⟨rt 2 t,(a2Kernel% root_mem) 2 t⟩ : PartIISL3UnipotentSylow.U3)=
      ⟨rt r.castSucc 1,(a2Kernel% root_mem) _ _⟩ := quotient_U3_injective h
  exact (psl3Known% noncentral_simple_root) r ⟨t,congrArg Subtype.val hh⟩

private theorem center_le_kernel (r : Fin 2) : (pi (F := F)).ker ≤ K r := by
  intro g hg
  have ht : g ∈ diagonalTorus := (psl3Known% center_le_torus) hg
  have hc : g ∈ Subgroup.center SL(3,F) := (QuotientGroup.eq_one_iff g).mp hg
  have hs := scalar_eq_self_of_mem_center hc 0
  have h01 : g 0 0=g 1 1 := by rw [← hs]; simp
  have h12 : g 1 1=g 2 2 := by rw [← hs]; simp
  fin_cases r
  · exact (psl3Known% torus_equal_first_mem) g ht h01
  · exact (psl3Known% torus_equal_second_mem) g ht h12

private theorem lift_commutation (w z : SL(3,F)) (hz : z ∈ upperUnipotent (F := F))
    (h : pi w*pi z=pi z*pi w) : w*z=z*w := by
  have hp : pi (w*z*w⁻¹)=pi z := by rw [map_mul,map_mul,map_inv,h]; group
  have hh := conjugate_eq_of_quotient_eq w z z hz hz hp
  calc
    w*z=(w*z*w⁻¹)*w := by group
    _ = z*w := by rw [hh]

private theorem simple_root_image [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (alpha : MulAut PSL(3,F))
    (hU : (projectiveUpperUnipotent (F := F)).map alpha.toMonoidHom=projectiveUpperUnipotent)
    (hT : (projectiveDiagonalTorus (F := F)).map alpha.toMonoidHom=projectiveDiagonalTorus)
    (hZ : (projectivePositiveRoot (F := F) 2).map alpha.toMonoidHom=projectivePositiveRoot 2)
    (r : Fin 2) :
    (projectivePositiveRoot r.castSucc).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 0 ∨
    (projectivePositiveRoot r.castSucc).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 1 := by
  let P := (K (F := F) r).map pi
  let L := P.map alpha.toMonoidHom
  let W := L.comap pi
  have hcW : Nat.card W=Nat.card Fˣ := by
    have hi : W.index=(K (F := F) r).index := by
      dsimp only [W,L]
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
      have hh : L.index=P.index := Subgroup.index_map_equiv _ alpha
      rw [hh]
      exact Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (center_le_kernel r)
    have hc : Nat.card W=Nat.card (K (F := F) r) := by
      apply (mul_left_inj' (K (F := F) r).index_ne_zero_of_finite).mp
      calc
        Nat.card W*(K (F := F) r).index=Nat.card W*W.index := by rw [hi]
        _ = Nat.card SL(3,F) := W.card_mul_index
        _ = Nat.card (K (F := F) r)*(K (F := F) r).index := (K (F := F) r).card_mul_index.symm
    exact hc.trans ((psl3Known% card_kernel) r)
  have hWT : W ≤ diagonalTorus := by
    intro w hw
    have hPL : L ≤ (projectiveDiagonalTorus (F := F)).map alpha.toMonoidHom :=
      Subgroup.map_mono (Subgroup.map_mono ((psl3Known% kernel_le_torus) r))
    have hp : pi w ∈ projectiveDiagonalTorus := by rw [← hT]; exact hPL hw
    have he : (projectiveDiagonalTorus (F := F)).comap pi=diagonalTorus :=
      Subgroup.comap_map_eq_self (psl3Known% center_le_torus)
    exact he ▸ hp
  have hmem : ∀ t, alpha (prt r.castSucc t) ∈ projectiveUpperUnipotent := by
    intro t
    rw [← hU]
    exact Subgroup.mem_map_of_mem alpha.toMonoidHom
      (Subgroup.mem_map_of_mem pi ((a2Kernel% root_mem) _ _))
  have hcomm : ∀ t w, w ∈ W → pi w*alpha (prt r.castSucc t)=alpha (prt r.castSucc t)*pi w := by
    intro t w hw
    obtain ⟨p,⟨k,hk,rfl⟩,hp⟩ := hw
    change alpha (pi k)=pi w at hp
    have hh := congrArg alpha (congrArg pi (((psl3Known% fixed_kernel_iff) hF r _
      ((a2Kernel% root_mem) _ _)).mpr ⟨t,rfl⟩ k hk))
    simpa only [map_mul,hp] using hh
  obtain ⟨a,b,c,hchart⟩ := (mem_projectiveUpperUnipotent _).mp (hmem 1)
  have hnz : alpha (prt r.castSucc 1) ∉ projectivePositiveRoot (F := F) 2 := by
    intro h
    rw [← hZ] at h
    exact noncentral_prt r ((Subgroup.mem_map_iff_mem alpha.injective).mp h)
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    have ha : a=0 := by tauto
    have hb : b=0 := by tauto
    apply hnz
    apply (psl3Known% mem_projectiveCentralRoot_iff) _ |>.mpr
    exact ⟨c,by simpa only [ha,hb] using hchart⟩
  have hWcomm : ∀ w : W, (w:SL(3,F))*upper3 a b c=upper3 a b c*(w:SL(3,F)) := by
    intro w
    apply lift_commutation _ _ ⟨a,b,c,rfl⟩
    change pi w.val*projectiveUpper3 a b c=projectiveUpper3 a b c*pi w.val
    rw [hchart]
    exact hcomm 1 w w.prop
  obtain hw|hw := actual_torus_kernel_classification W hWT hcW a b c hab hWcomm
  all_goals
    have hidx : ∃ s : Fin 2, W=K (F := F) s := by
      first | exact ⟨0,hw⟩ | exact ⟨1,hw⟩
    obtain ⟨s,hs⟩ := hidx
    have hle : (projectivePositiveRoot r.castSucc).map alpha.toMonoidHom ≤
        projectivePositiveRoot (F := F) s.castSucc := by
      rintro g ⟨z,⟨w,⟨t,rfl⟩,rfl⟩,rfl⟩
      obtain ⟨A,B,C,hv⟩ := (mem_projectiveUpperUnipotent _).mp (hmem t)
      have hroot : upper3 A B C ∈ positiveRoot (F := F) s.castSucc := by
        apply ((psl3Known% fixed_kernel_iff) hF s _ ⟨A,B,C,rfl⟩).mp
        intro k hk
        apply lift_commutation _ _ ⟨A,B,C,rfl⟩
        change pi k*projectiveUpper3 A B C=projectiveUpper3 A B C*pi k
        rw [hv]
        exact hcomm t k (hs.symm ▸ hk)
      exact ⟨upper3 A B C,hroot,hv⟩
    have heq : (projectivePositiveRoot r.castSucc).map alpha.toMonoidHom=
        projectivePositiveRoot (F := F) s.castSucc := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [card_projective_root,← Nat.card_congr ((projectivePositiveRoot r.castSucc).equivMapOfInjective
        alpha.toMonoidHom alpha.injective).toEquiv,card_projective_root]
    fin_cases s
    · exact Or.inl heq
    · exact Or.inr heq

private theorem same_projective_root_commute (r : Fin 3) (g h : PSL(3,F))
    (hg : g ∈ projectivePositiveRoot (F := F) r) (hh : h ∈ projectivePositiveRoot (F := F) r) : g*h=h*g := by
  obtain ⟨x,hx,rfl⟩ := hg
  obtain ⟨y,hy,rfl⟩ := hh
  exact (congrArg pi ((psl3Known% same_root_commute) r x y hx hy)).trans (by simp only [map_mul])

private theorem simple_prt_not_commute : prt (F := F) 0 1*prt 1 1 ≠ prt 1 1*prt 0 1 := by
  intro h
  have hh : (⟨rt (F := F) 0 1*rt 1 1,upperUnipotent.mul_mem ((a2Kernel% root_mem) 0 1)
      ((a2Kernel% root_mem) 1 1)⟩ : PartIISL3UnipotentSylow.U3)=
    ⟨rt (F := F) 1 1*rt 0 1,upperUnipotent.mul_mem ((a2Kernel% root_mem) 1 1) ((a2Kernel% root_mem) 0 1)⟩ := by
    apply quotient_U3_injective
    simpa only [map_mul] using h
  exact (psl3Known% simple_roots_not_commute) (congrArg Subtype.val hh)

/-- Actual projective simple-root preservation/interchange. Whole preimages
of the true torus kernels retain the scalar centre and their exact orders.
Projective commutation is lifted using the accepted trace/determinant law,
then the proved actual SL3 kernel classification is consumed unchanged. -/
theorem actual_normalized_projective_simple_root_permutation [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (alpha : MulAut PSL(3,F))
    (hU : (projectiveUpperUnipotent (F := F)).map alpha.toMonoidHom=projectiveUpperUnipotent)
    (hT : (projectiveDiagonalTorus (F := F)).map alpha.toMonoidHom=projectiveDiagonalTorus)
    (hZ : (projectivePositiveRoot (F := F) 2).map alpha.toMonoidHom=projectivePositiveRoot 2) :
    ((projectivePositiveRoot 0).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 0 ∧
      (projectivePositiveRoot 1).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 1) ∨
    ((projectivePositiveRoot 0).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 1 ∧
      (projectivePositiveRoot 1).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 0) := by
  have h0 := simple_root_image hF alpha hU hT hZ 0
  have h1 := simple_root_image hF alpha hU hT hZ 1
  have hne : ∀ s : Fin 3, ¬ ((projectivePositiveRoot 0).map alpha.toMonoidHom=projectivePositiveRoot (F := F) s ∧
      (projectivePositiveRoot 1).map alpha.toMonoidHom=projectivePositiveRoot (F := F) s) := by
    rintro s ⟨hs0,hs1⟩
    have hm0 : alpha (prt 0 1) ∈ projectivePositiveRoot (F := F) s := by
      rw [← hs0]; exact Subgroup.mem_map_of_mem alpha.toMonoidHom ⟨rt 0 1,⟨1,rfl⟩,rfl⟩
    have hm1 : alpha (prt 1 1) ∈ projectivePositiveRoot (F := F) s := by
      rw [← hs1]; exact Subgroup.mem_map_of_mem alpha.toMonoidHom ⟨rt 1 1,⟨1,rfl⟩,rfl⟩
    apply simple_prt_not_commute (F := F)
    apply alpha.injective
    simpa only [map_mul] using same_projective_root_commute s _ _ hm0 hm1
  rcases h0 with h0|h0 <;> rcases h1 with h1|h1
  · exact (hne 0 ⟨h0,h1⟩).elim
  · exact Or.inl ⟨h0,h1⟩
  · exact Or.inr ⟨h0,h1⟩
  · exact (hne 1 ⟨h0,h1⟩).elim

/-- Every bare PSL3 auto over |F|>4 has ONE actual inner normalization
preserving U,Z and preserving or interchanging the two actual simple roots.
No SL3 lift, root-image, torus-image or semilinearity input is assumed. -/
theorem actual_bare_PSL3_root_normalization [Fintype F] [DecidableEq F]
    (hF : 4 < Fintype.card F) (beta : MulAut PSL(3,F)) :
    ∃ g : PSL(3,F), let alpha := MulAut.conj g⁻¹*beta
      (projectiveUpperUnipotent (F := F)).map alpha.toMonoidHom=projectiveUpperUnipotent ∧
      (projectivePositiveRoot (F := F) 2).map alpha.toMonoidHom=projectivePositiveRoot 2 ∧
      (((projectivePositiveRoot 0).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 0 ∧
        (projectivePositiveRoot 1).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 1) ∨
       ((projectivePositiveRoot 0).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 1 ∧
        (projectivePositiveRoot 1).map alpha.toMonoidHom=projectivePositiveRoot (F := F) 0)) := by
  obtain ⟨g,hU,hT,hZ⟩ := actual_bare_PSL3_U_T_central_root_normalization beta
  exact ⟨g,hU,hZ,actual_normalized_projective_simple_root_permutation hF _ hU hT hZ⟩
end NikolovSegal.PartIIPSL3RootSeparation
