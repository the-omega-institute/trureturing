/- GID: D5/S3/VertexAlgebra/LatticeDualCosetConformalShift
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetConformalShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite normal-mode expansion and inverse-Gram contraction of the actual original-omega action. -/

import D5.S3.VertexAlgebra.LatticeDualCosetConformal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeDualCosetConformal
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeFiniteNegativeGeneration LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticeDualCosetModule FieldNormalProduct
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData) (β : Charge D)

/-- Each cross term appears once, including at the zero-mode normal-order boundary. -/
theorem normal_current_shift (i j : Fin D.rank) (m : ℤ) :
    ((normalMinusOne (action D β (currentState D i))
      (action D β (currentState D j))).1)[[m + 1]] =
    (quadraticSummand D i j)[[m + 1]] + (β j : ℂ) • neutralMode D i m +
      (β i : ℂ) • neutralMode D j m +
      (if m = 0 then (β i : ℂ) * (β j : ℂ) else 0) •
        (1 : Module.End ℂ (Carrier D)) := by
  classical
  apply LinearMap.ext
  intro v
  let f (k : ℕ) := neutralMode D i (-(k : ℤ)-1)
    (neutralMode D j (m+1+k) v)
  let g (k : ℕ) := neutralMode D j (m-k) (neutralMode D i k v)
  let x (k : ℕ) := if m+1+(k : ℤ)=0 then (β j : ℂ) • neutralMode D i m v else 0
  let y (k : ℕ) := if k=0 then (β i : ℂ) • neutralMode D j m v else 0
  let z (k : ℕ) := if m-(k : ℤ)=0 then (β j : ℂ) • neutralMode D i m v else 0
  let t (k : ℕ) := if m=0 ∧ k=0 then ((β i : ℂ)*(β j : ℂ)) • v else 0
  have hf : Function.HasFiniteSupport f := by
    have h := (normalSummand_finite D i j m v).comp_of_injective
      (show Function.Injective (fun k : ℕ => -(k : ℤ)-1) by
        intro a b hab; omega)
    convert h using 1
    ext k
    simp [f, normalSummand, show -(k : ℤ)-1 < 0 by omega,
      show m-(-(k : ℤ)-1)=m+1+k by omega]
  have hg : Function.HasFiniteSupport g := by
    have h := (normalSummand_finite D i j m v).comp_of_injective Int.natCast_injective
    convert h using 1
    ext k
    simp [g, normalSummand, show ¬ (k : ℤ)<0 by omega]
  have hx : Function.HasFiniteSupport x := by
    apply (Set.finite_singleton (-m-1).toNat).subset
    intro k hk
    have h : m+1+(k : ℤ)=0 := by by_contra h; exact hk (by simp [x,h])
    simp only [Set.mem_singleton_iff]
    omega
  have hy : Function.HasFiniteSupport y := by
    apply (Set.finite_singleton 0).subset
    intro k hk
    by_contra h
    exact hk (by simp [y,h])
  have hz : Function.HasFiniteSupport z := by
    apply (Set.finite_singleton m.toNat).subset
    intro k hk
    have h : m-(k : ℤ)=0 := by by_contra h; exact hk (by simp [z,h])
    simp only [Set.mem_singleton_iff]
    omega
  have ht : Function.HasFiniteSupport t := by
    apply (Set.finite_singleton 0).subset
    intro k hk
    by_contra h
    exact hk (by simp [t,h])
  have first (k : ℕ) :
      ((action D β (currentState D i))[[-(k : ℤ)-1]])
        (((action D β (currentState D j))[[m+1+k]]) v) = f k + x k := by
    rw [action_current, action_current]
    by_cases h : m+1+(k : ℤ)=0
    · have hi : -(k : ℤ)-1=m := by omega
      simp [f,x,h,show -(k : ℤ)-1 ≠ 0 by omega,hi,map_add,map_smul]
    · simp [f,x,h,show -(k : ℤ)-1 ≠ 0 by omega]
  have second (k : ℕ) :
      ((action D β (currentState D j))[[m+1-k-1]])
        (((action D β (currentState D i))[[k]]) v) = g k + y k + z k + t k := by
    rw [show m+1-(k : ℤ)-1=m-k by omega, action_current, action_current]
    by_cases hk : k=0 <;> by_cases hm : m-(k : ℤ)=0
    · subst k
      have hm0 : m=0 := by simpa using hm
      subst m
      simp [g,y,z,t,map_add,map_smul,add_smul,smul_add,smul_smul,mul_comm]
      abel
    · subst k
      simp only [sub_zero] at hm
      simp [g,y,z,t,hm,map_add,map_smul]
    · have hkm : (k : ℤ)=m := by omega
      simp [g,y,z,t,hk,hm,hkm,show m ≠ 0 by omega,map_add,map_smul]
    · simp [g,y,z,t,hk,hm,show (k : ℤ) ≠ 0 by omega]
  have sx : (∑ᶠ k, x k) = if m<0 then (β j : ℂ) • neutralMode D i m v else 0 := by
    by_cases hm : m<0
    · rw [finsum_eq_single _ (-m-1).toNat]
      · simp [x,hm,show m+1+((-m-1).toNat : ℤ)=0 by omega]
      · intro k hk
        simp [x,show m+1+(k : ℤ) ≠ 0 by omega]
    · simp [x,hm,show ∀ k : ℕ, m+1+(k : ℤ) ≠ 0 by intro k; omega]
  have sy : (∑ᶠ k, y k) = (β i : ℂ) • neutralMode D j m v := by
    rw [finsum_eq_single _ 0 (fun k hk => by simp [y,hk])]
    simp [y]
  have sz : (∑ᶠ k, z k) = if 0≤m then (β j : ℂ) • neutralMode D i m v else 0 := by
    by_cases hm : 0≤m
    · rw [finsum_eq_single _ m.toNat]
      · simp [z,hm]
      · intro k hk
        simp [z,show m-(k : ℤ) ≠ 0 by omega]
    · simp [z,hm,show ∀ k : ℕ, m-(k : ℤ) ≠ 0 by intro k; omega]
  have st : (∑ᶠ k, t k) =
      (if m=0 then (β i : ℂ)*(β j : ℂ) else 0) • v := by
    rw [finsum_eq_single _ 0 (fun k hk => by simp [t,hk])]
    by_cases hm : m=0 <;> simp [t,hm]
  rw [(normalMinusOne (action D β (currentState D i))
    (action D β (currentState D j))).2]
  simp_rw [first,second]
  rw [finsum_add_distrib hf hx, finsum_add_distrib ((hg.add hy).add hz) ht,
    finsum_add_distrib (hg.add hy) hz, finsum_add_distrib hg hy,sx,sy,sz,st]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]
  have old : ((quadraticSummand D i j)[[m+1]]) v = (∑ᶠ k,f k)+(∑ᶠ k,g k) := by
    rw [quadraticSummand,(normalMinusOne (neutralField D i) (neutralField D j)).2]
    simp_rw [neutralField_ncoeff]
    congr 1
    apply finsum_congr
    intro k
    dsimp [g]
    congr 2
    omega
  rw [old]
  by_cases hm : m<0
  · simp only [hm,ite_true,show ¬ 0≤m by omega,ite_false]
    abel
  · simp only [hm,ite_false,show 0≤m by omega,ite_true]
    abel

end
end D5.S3.VertexAlgebra.LatticeDualCosetConformal
