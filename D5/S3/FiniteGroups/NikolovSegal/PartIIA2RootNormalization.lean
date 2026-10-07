/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2RootNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2RootNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2GraphSupply
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace NikolovSegal.PartIIA2RootNormalization
open PartIIA2Orbital Matrix.SpecialLinearGroup PartIITransvectionSupply
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
private abbrev root (r : Fin 3) (t : F) : SL(3,F) := transvection ((a2Kernel% root_ne) r) t

private theorem positive_commutator (t s : F) :
    root 0 t * root 1 s *
      (root 0 t)⁻¹ * (root 1 s)⁻¹ =
        root 2 (t*s) := by
  have h0 : root 0 t = upper3 t 0 0 := by
    change transvection (show (0:Fin 3) ≠ 1 by decide) t = upper3 t 0 0
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  have h1 : root 1 s = upper3 0 s 0 := by
    change transvection (show (1:Fin 3) ≠ 2 by decide) s = upper3 0 s 0
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  have h2 : root 2 (t*s) = upper3 0 0 (t*s) := by
    change transvection (show (0:Fin 3) ≠ 2 by decide) (t*s) = upper3 0 0 (t*s)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper3,transvection_coe]
  rw [h0,h1,h2,(a2Kernel% upper3_inv),(a2Kernel% upper3_inv),
    (a2Kernel% upper3_mul),(a2Kernel% upper3_mul),(a2Kernel% upper3_mul)]
  congr 1 <;> ring

private theorem root_injective (r : Fin 3) :
    Function.Injective (fun t : F => root r t) := by
  intro t s h
  have hh := congrArg (fun g : SL(3,F) => g ((a2Kernel% rootI) r) ((a2Kernel% rootJ) r)) h
  simpa only [root,transvection_coe,Matrix.add_apply,Matrix.single_apply,ite_true,eq_self,and_self,add_left_cancel_iff] using hh

/-- Actual A2 commutator incidence reconstructs ONE field automorphism from
three additive root coordinates. The field law is proved via the genuine
multiplication t*s in the central root, not assumed. -/
theorem actual_positive_root_field (beta : MulAut SL(3,F))
    (f : Fin 3 → F ≃+ F)
    (hb : ∀ r t, beta (root r t) = root r (f r t)) :
    ∃ phi : RingAut F,
      (∀ t, f 0 t = f 0 1*phi t) ∧
      (∀ t, f 1 t = f 1 1*phi t) ∧
      (∀ t, f 2 t = f 0 1*f 1 1*phi t) := by
  have hf0 : f 0 1 ≠ 0 := by intro h; exact one_ne_zero ((f 0).map_eq_zero_iff.mp h)
  have hf1 : f 1 1 ≠ 0 := by intro h; exact one_ne_zero ((f 1).map_eq_zero_iff.mp h)
  have hmul : ∀ t s, f 2 (t*s) = f 0 t*f 1 s := by
    intro t s
    have hh := congrArg beta (positive_commutator t s)
    simp only [map_mul,map_inv,hb] at hh
    rw [positive_commutator] at hh
    exact (root_injective 2 hh).symm
  have h20 : ∀ t, f 2 t = f 0 t*f 1 1 := by intro t; simpa only [mul_one] using hmul t 1
  have h21 : ∀ t, f 2 t = f 0 1*f 1 t := by intro t; simpa only [one_mul] using hmul 1 t
  have hg : ∀ t, f 1 t = (f 0 1)⁻¹*f 0 t*f 1 1 := by
    intro t
    have h := (h21 t).symm.trans (h20 t)
    calc
      _ = (f 0 1)⁻¹*(f 0 1*f 1 t) := by rw [← mul_assoc,inv_mul_cancel₀ hf0,one_mul]
      _ = _ := by rw [h,mul_assoc]
  let fn : F ≃+ F :=
    { toFun := fun t => (f 0 1)⁻¹*f 0 t
      invFun := fun t => (f 0).symm (f 0 1*t)
      left_inv := by intro t; simp [mul_assoc,hf0]
      right_inv := by intro t; simp [mul_assoc,hf0]
      map_add' := by intro t s; simp [map_add,mul_add] }
  have hfnmul : ∀ t s, fn (t*s) = fn t*fn s := by
    intro t s
    have hh := hmul t s
    rw [h20 (t*s),hg s] at hh
    have hff : f 0 (t*s) = f 0 t*((f 0 1)⁻¹*f 0 s) := by
      apply mul_right_cancel₀ hf1
      simpa only [mul_assoc] using hh
    change (f 0 1)⁻¹*f 0 (t*s)=((f 0 1)⁻¹*f 0 t)*((f 0 1)⁻¹*f 0 s)
    rw [hff,mul_assoc]
  let phi : RingAut F := {fn with map_mul' := hfnmul}
  have hf0t : ∀ t, f 0 t = f 0 1*phi t := by
    intro t
    change f 0 t = f 0 1*((f 0 1)⁻¹*f 0 t)
    rw [← mul_assoc,mul_inv_cancel₀ hf0,one_mul]
  refine ⟨phi,hf0t,?_,?_⟩
  · intro t
    rw [hg]
    change (f 0 1)⁻¹*f 0 t*f 1 1 = f 1 1*((f 0 1)⁻¹*f 0 t)
    ring
  · intro t
    rw [h20,hf0t]
    ring
/-- The literal three actual positive root subgroups, with additive coordinates. -/
def positiveRoot (r : Fin 3) : Subgroup SL(3,F) where
  carrier := {g | ∃ t : F, root r t = g}
  one_mem' := ⟨0,transvection_coeff_zero ((a2Kernel% root_ne) r)⟩
  mul_mem' := by
    rintro g h ⟨t,rfl⟩ ⟨s,rfl⟩
    exact ⟨t+s,transvection_add ((a2Kernel% root_ne) r) t s⟩
  inv_mem' := by
    rintro g ⟨t,rfl⟩
    exact ⟨-t,(transvection_inv ((a2Kernel% root_ne) r) t).symm⟩

private theorem root_additive_coordinates (beta : MulAut SL(3,F)) (r : Fin 3)
    (hmap : (positiveRoot r).map beta.toMonoidHom = positiveRoot (F := F) r) :
    ∃ f : F ≃+ F, ∀ t, beta (root r t) = root r (f t) := by
  classical
  have hmem : ∀ t : F, beta (root r t) ∈ positiveRoot r := by
    intro t
    rw [← hmap]
    exact Subgroup.mem_map_of_mem beta.toMonoidHom ⟨t,rfl⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro t s h
    apply root_injective r
    apply beta.injective
    rw [← hf t,← hf s,h]
  have hsurj : Function.Surjective f := by
    intro s
    have hs : root r s ∈ (positiveRoot r).map beta.toMonoidHom := by
      rw [hmap]
      exact ⟨s,rfl⟩
    obtain ⟨g,⟨t,rfl⟩,ht⟩ := hs
    refine ⟨t,root_injective r ?_⟩
    change root r (f t)=root r s
    rw [hf t]
    exact ht
  have hadd : ∀ t s, f (t+s)=f t+f s := by
    intro t s
    apply root_injective r
    change root r (f (t+s))=root r (f t+f s)
    have hradd : ∀ t s : F, root r (t+s)=root r t*root r s :=
      fun t s => transvection_add ((a2Kernel% root_ne) r) t s
    rw [hf (t+s),hradd,map_mul,← hf t,← hf s,← hradd]
  let fa : F →+ F :=
    { toFun := f
      map_zero' := by
        have h := hadd 0 0
        simp only [zero_add] at h
        linear_combination -h
      map_add' := hadd }
  let fe := AddEquiv.ofBijective fa ⟨hinj,hsurj⟩
  exact ⟨fe,fun t => (hf t).symm⟩

/-- Genuine orbital VALUE PRODUCT for arbitrary actual SL3 automorphisms
preserving the three literal positive root subgroups. Additive coordinates,
ONE common field automorphism and the coupled central coefficient are DERIVED
from the subgroup images and the actual A2 commutator. No scalar/semilinear
coverage premise. Root preservation itself remains a geometric normalization
hypothesis, to be supplied for bare automorphisms; it is not claimed here. -/
theorem actual_root_preserving_A2_orbital_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (beta : Fin (3*M) → MulAut SL(3,F))
    (hroot : ∀ j r, (positiveRoot r).map (beta j).toMonoidHom = positiveRoot (F := F) r)
    (e : Fin (3*M) → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q) :
    ∃ y : Fin (3*M) → SL(3,F), ∀ target ∈ upperUnipotent (F := F),
      ∃ c : Fin (3*M) → SL(3,F), (∀ j, c j ∈ upperUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹ *
          (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (c j))) = target := by
  classical
  choose f hf using fun j r => root_additive_coordinates (beta j) r (hroot j r)
  choose phi h0 h1 h2 using fun j => actual_positive_root_field (beta j) (f j) (hf j)
  let chi : Fin (3*M) → Fin 3 → F := fun j => ![f j 0 1,f j 1 1,f j 0 1*f j 1 1]
  have hchi : ∀ j r, chi j r ≠ 0 := by
    intro j r
    have h0 : f j 0 1 ≠ 0 := by intro h; exact one_ne_zero ((f j 0).map_eq_zero_iff.mp h)
    have h1 : f j 1 1 ≠ 0 := by intro h; exact one_ne_zero ((f j 1).map_eq_zero_iff.mp h)
    fin_cases r
    · exact h0
    · exact h1
    · exact mul_ne_zero h0 h1
  have hb : ∀ j r t, beta j (root r t) =
      root r (chi j r*phi j t) := by
    intro j r t
    rw [hf j r]
    fin_cases r
    · exact congrArg (root 0) (h0 j t)
    · exact congrArg (root 1) (h1 j t)
    · exact congrArg (root 2) (h2 j t)
  let b := fun (r : Fin 3) (j : Fin M) => finProdFinEquiv (r,j)
  let d := fun j => q/e j
  have hd : ∀ j, 0 < d j ∧ d j ∣ q := by
    intro j
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,Nat.div_dvd_of_dvd (he j).2⟩
  choose y hy using fun r : Fin 3 => actual_transvection_scalar_product ((a2Kernel% root_ne) r)
    hq hM hF (fun j => beta (b r j)) (fun j => phi (b r j))
    (fun j => chi (b r j) r) (fun j => hchi _ _) (fun j => d (b r j))
    (fun j => hd _) (fun j t => hb (b r j) r t)
  let yall := fun k : Fin (3*M) => y (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hyall : ∀ r j, yall (b r j)=y r j := by
    intro r j
    simp only [yall,b,Equiv.symm_apply_apply]
  refine ⟨yall,?_⟩
  intro target ht
  obtain ⟨A,B,C,rfl⟩ := ht
  let w : Fin 3 → F := ![A,B,C-A*B]
  choose t ht using fun r : Fin 3 => hy r (w r)
  let c := fun k : Fin (3*M) => root (finProdFinEquiv.symm k).1
      (t (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  have hc : ∀ r j, c (b r j)=root r (t r j) := by
    intro r j
    simp only [c,b,Equiv.symm_apply_apply]
  refine ⟨c,fun j => (a2Kernel% root_mem) _ _,?_⟩
  rw [(a2Kernel% ordered_blocks)]
  change orderedProduct (fun r : Fin 3 => orderedProduct (fun j : Fin M =>
    (c (b r j))⁻¹ * (((beta (b r j)*MulAut.conj (yall (b r j))⁻¹)^(q/e (b r j)))
      (c (b r j))))) = upper3 A B C
  have hblocks : ∀ r, orderedProduct (fun j : Fin M => (c (b r j))⁻¹ *
      (((beta (b r j)*MulAut.conj (yall (b r j))⁻¹)^(q/e (b r j))) (c (b r j)))) =
      root r (w r) := by
    intro r
    simpa only [hc,hyall,d] using ht r
  calc
    _ = orderedProduct (fun r : Fin 3 => root r (w r)) :=
      congrArg orderedProduct (funext hblocks)
    _ = upper3 A B C := by
      have hprod : root 0 A*root 1 B*root 2 (C-A*B)=upper3 A B C :=
        (a2Kernel% three_root_product) A B C
      simpa [orderedProduct,List.ofFn_succ,w,mul_assoc] using hprod
end NikolovSegal.PartIIA2RootNormalization
