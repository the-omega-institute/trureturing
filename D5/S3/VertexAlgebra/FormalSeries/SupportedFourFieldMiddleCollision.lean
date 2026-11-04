/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFourFieldMiddleCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native middle collision with the original first and fourth spectators. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedFourFieldCollision

/-! Only native power series are substituted. Signed spectator and active
coordinates are handled by the existing four-field collision theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedFourFieldMiddleCollision
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open SupportedFourFieldCollision
noncomputable section

private def sigma : Fin 4 ≃ Fin 4 := (Equiv.swap 1 2).trans (Equiv.swap 1 3)

private theorem rename_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (σ : Fin 4 ≃ Fin 4) (P : MvPowerSeries (Fin 4) R) (e : Exponent 4) :
    signedExtend (MvPowerSeries.rename σ P) e = signedExtend P (e ∘ σ) := by
  classical
  have nn : (∀ i, 0 ≤ e i) ↔ (∀ i, 0 ≤ (e ∘ σ) i) := by
    constructor
    · intro h i; exact h (σ i)
    · intro h i; simpa only [Function.comp_apply,σ.apply_symm_apply] using h (σ.symm i)
  by_cases h : ∀ i, 0 ≤ e i
  · rw [signedExtend,ite_eq_left h,signedExtend,ite_eq_left (nn.mp h)]
    have idx : signedIndex e = (signedIndex (e ∘ σ)).embDomain σ.toEmbedding := by
      ext i
      simp [Finsupp.embDomain_eq_mapDomain,Finsupp.mapDomain_equiv_apply,signedIndex]
    rw [idx]
    exact MvPowerSeries.coeff_embDomain_rename σ.toEmbedding P _
  · simp only [signedExtend,ite_eq_right h,ite_eq_right (fun h' => h (nn.mpr h'))]

/-- Original numerator arguments in x,b,z,y coordinates. -/
def middleFourArguments (R : Type*) [CommRing R] : Fin 4 → MvPowerSeries (Fin 4) R :=
  ![MvPowerSeries.X 0,MvPowerSeries.X 1 + MvPowerSeries.X 2,MvPowerSeries.X 2,MvPowerSeries.X 3]

/-- The slice fixes original labels u and q. -/
def middleSlice {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y : ℤ) : MvPowerSeries (Fin 2) R :=
  slice (MvPowerSeries.rename sigma P) x y

theorem middleSlice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y v t : ℤ) :
    extend (middleSlice P x y) v t = signedExtend P ![x,v,t,y] := by
  rw [middleSlice,slice_extend,rename_signed]
  congr 1
  funext i
  fin_cases i <;> simp [sigma,Equiv.swap_apply_def]

private theorem native_permutation {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 4) R) :
    MvPowerSeries.subst (middleFourArguments R) P =
      MvPowerSeries.rename sigma.symm (fourInnerCollision (MvPowerSeries.rename sigma P)) := by
  let r : Fin 4 → MvPowerSeries (Fin 4) R := MvPowerSeries.X ∘ sigma
  let s : Fin 4 → MvPowerSeries (Fin 4) R := MvPowerSeries.X ∘ sigma.symm
  have hr : MvPowerSeries.HasSubst r := MvPowerSeries.HasSubst.X_comp _
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.HasSubst.X_comp _
  have ho := fourInner_hasSubst R
  have hc : MvPowerSeries.HasSubst (fun i => MvPowerSeries.subst (fourInnerArguments R) (r i)) := by
    simpa only [MvPowerSeries.substAlgHom_apply] using hr.comp ho
  rw [MvPowerSeries.rename_eq_subst]
  unfold fourInnerCollision
  rw [MvPowerSeries.rename_eq_subst]
  change _ = MvPowerSeries.subst s (MvPowerSeries.subst (fourInnerArguments R) (MvPowerSeries.subst r P))
  rw [MvPowerSeries.subst_comp_subst_apply hr ho,MvPowerSeries.subst_comp_subst_apply hc hs]
  congr 1
  funext i
  simp only [r,Function.comp_apply,MvPowerSeries.subst_X ho]
  fin_cases i
  · change MvPowerSeries.X 0 = MvPowerSeries.subst s (MvPowerSeries.X 0)
    rw [MvPowerSeries.subst_X hs]
    simp [s,sigma,Equiv.swap_apply_def]
  · change MvPowerSeries.X 1 + MvPowerSeries.X 2 =
      MvPowerSeries.subst s (MvPowerSeries.X 2 + MvPowerSeries.X 3)
    rw [MvPowerSeries.subst_add hs,MvPowerSeries.subst_X hs,MvPowerSeries.subst_X hs]
    simp [s,sigma,Equiv.swap_apply_def]
  · change MvPowerSeries.X 2 = MvPowerSeries.subst s (MvPowerSeries.X 3)
    rw [MvPowerSeries.subst_X hs]
    simp [s,sigma,Equiv.swap_apply_def]
  · change MvPowerSeries.X 3 = MvPowerSeries.subst s (MvPowerSeries.X 1)
    rw [MvPowerSeries.subst_X hs]
    simp [s,sigma,Equiv.swap_apply_def]

theorem middleCollision_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x b z y : ℤ) :
    signedExtend (MvPowerSeries.subst (middleFourArguments R) P) ![x,b,z,y] =
      extend (collision (middleSlice P x y)) b z := by
  rw [native_permutation,rename_signed]
  have coords : ((![x,b,z,y] : Exponent 4) ∘ sigma.symm) = ![x,y,b,z] := by
    funext i
    fin_cases i <;> simp [sigma,Equiv.swap_apply_def]
  rw [coords,fourInnerCollision_signed]
  rfl

end
end D5.S3.VertexAlgebra.SupportedFourFieldMiddleCollision
