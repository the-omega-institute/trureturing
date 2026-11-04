/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleInverseKernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldMiddleInverseKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Outer native binomial factors of the middle inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleNativeInverse
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleLaurentFiber
import Batteries.Tactic.OpenPrivate

/-! Carnahan's native binomial series provides all three outer inverses.
The balanced three-index kernel is reused unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FourFieldMiddleInverseKernel
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldBalancedNativeInverse ThreeFieldBalancedInverseKernel
open FourFieldMiddleNativeInverse FourFieldMiddleLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]
open private factor_inverse binomial_coeff coeff_mul_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalInverseCoefficients
open private plus_pow from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance

private def outerBase (R : Type*) [CommRing R] (i : Fin 3) : MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 2+MvPowerSeries.X 0*MvPowerSeries.X 1*MvPowerSeries.X 2,
    MvPowerSeries.X 2,MvPowerSeries.X 1*MvPowerSeries.X 2] i

private theorem outer_legal (i : Fin 3) : PowerSeries.HasSubst (-outerBase R i) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  fin_cases i <;> simp [outerBase]

private def outerKernel (k : ℕ) (i : Fin 3) : MvPowerSeries (Fin 3) R :=
  PowerSeries.subst (-outerBase R i) (PowerSeries.binomialSeries R (-(k : ℤ)))

private theorem outer_inverse (k A : ℕ) :
    (↑((middleUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) =
      (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) *
        outerKernel k 0 * outerKernel k 1 * outerKernel k 2 := by
  have h0 := factor_inverse (-outerBase R 0) (outer_legal 0) k
  have h1 := factor_inverse (-outerBase R 1) (outer_legal 1) k
  have h2 := factor_inverse (-outerBase R 2) (outer_legal 2) k
  have hb : balancedUnitSeries R k A *
    (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)=1 := (balancedUnit R k A).val_inv
  have cancel : middleUnitSeries R k A *
      ((↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)*
        outerKernel k 0*outerKernel k 1*outerKernel k 2)=1 := by
    have eq0 : 1- MvPowerSeries.X 2-MvPowerSeries.X 0*MvPowerSeries.X 1*MvPowerSeries.X 2 =
        (1 : MvPowerSeries (Fin 3) R)+ -outerBase R 0 := by dsimp [outerBase]; ring
    dsimp only [outerKernel] at *
    rw [middleUnitSeries,eq0]
    rw [show (1-MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R)=1+-outerBase R 1 by simp [outerBase,sub_eq_add_neg],
      show (1-MvPowerSeries.X 1*MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R)=1+-outerBase R 2 by simp [outerBase,sub_eq_add_neg]]
    change balancedUnitSeries R k A * (1+-outerBase R 0)^k *
      (1+-outerBase R 1)^k*(1+-outerBase R 2)^k * _=1
    calc
      _ = (balancedUnitSeries R k A * (↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)) *
        ((1+-outerBase R 0)^k*PowerSeries.subst (-outerBase R 0) (PowerSeries.binomialSeries R (-(k : ℤ)))) *
        ((1+-outerBase R 1)^k*PowerSeries.subst (-outerBase R 1) (PowerSeries.binomialSeries R (-(k : ℤ)))) *
        ((1+-outerBase R 2)^k*PowerSeries.subst (-outerBase R 2) (PowerSeries.binomialSeries R (-(k : ℤ)))) := by ring
      _ = 1 := by rw [hb,h0,h1,h2]; simp
  calc
    _ = (↑((middleUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R) *
      (middleUnitSeries R k A * ((↑((balancedUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)*
        outerKernel k 0*outerKernel k 1*outerKernel k 2)) := by rw [cancel,mul_one]
    _ = _ := by rw [← mul_assoc,show (↑((middleUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)*
      middleUnitSeries R k A=1 from (middleUnit R k A).inv_val,one_mul]

private theorem base_pow_coeff (i : Fin 3) (q r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (outerBase R i ^ q) =
      if i=0 then (if r=s ∧ t=q then (q.choose r : R) else 0)
      else if i=1 then (if r=0 ∧ s=0 ∧ t=q then 1 else 0)
      else (if r=0 ∧ s=q ∧ t=q then 1 else 0) := by
  classical
  fin_cases i <;> simp only [Fin.isValue,reduceIte]
  · change MvPowerSeries.coeff (index3 r s t) (outerBase R 0^q) =
      if r=s ∧ t=q then (q.choose r : R) else 0
    have expand : outerBase R 0 ^ q =
      ∑ h∈Finset.range (q+1), (q.choose h : ℂ) •
        MvPowerSeries.monomial (index3 h h q) (1 : R) := by
      change (MvPowerSeries.X 2+MvPowerSeries.X 0*MvPowerSeries.X 1*MvPowerSeries.X 2)^q=_
      rw [add_comm,plus_pow]
      apply Finset.sum_congr rfl
      intro h hh
      have hhq : h≤q := by simpa using Finset.mem_range.mp hh
      congr 1
      simp only [mul_pow,MvPowerSeries.X_pow_eq,MvPowerSeries.monomial_mul_monomial]
      simp only [mul_one]
      apply congrArg (fun d : Fin 3 →₀ ℕ => MvPowerSeries.monomial d (1 : R))
      ext c
      fin_cases c <;> simp [index3] <;> omega
    rw [expand,map_sum]
    simp only [LinearMap.map_smul_of_tower,MvPowerSeries.coeff_monomial]
    have eq (h : ℕ) : index3 r s t=index3 h h q ↔ r=h ∧ s=h ∧ t=q := by
      constructor
      · intro he
        exact ⟨by simpa [index3] using congrArg (fun d => d 0) he,
          by simpa [index3] using congrArg (fun d => d 1) he,
          by simpa [index3] using congrArg (fun d => d 2) he⟩
      · rintro ⟨rfl,rfl,rfl⟩; rfl
    simp only [eq,smul_ite,smul_zero,smul_eq_mul]
    by_cases h : r=s ∧ t=q
    · rw [ite_eq_left h]
      obtain ⟨hrs,htq⟩ := h
      subst s
      subst t
      by_cases hr : r≤q
      · rw [Finset.sum_eq_single r]
        · simp [Algebra.smul_def]
        · intro j hj hne; simp [hne,Ne.symm hne]
        · simp only [Finset.mem_range,not_lt]; omega
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp only [Nat.cast_zero]
        apply Finset.sum_eq_zero
        intro j hj
        have hjq := Finset.mem_range.mp hj
        have hne : r≠j := by omega
        simp [hne]
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro j hj
      have hh : ¬(r=j ∧ s=j ∧ t=q) := by omega
      simp [hh]
  · change MvPowerSeries.coeff (index3 r s t) (MvPowerSeries.X 2^q)=_
    rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_monomial]
    have eq : index3 r s t=Finsupp.single 2 q ↔ r=0 ∧ s=0 ∧ t=q := by
      constructor
      · intro h
        exact ⟨by simpa [index3] using congrArg (fun d => d 0) h,
          by simpa [index3] using congrArg (fun d => d 1) h,
          by simpa [index3] using congrArg (fun d => d 2) h⟩
      · rintro ⟨rfl,rfl,rfl⟩; simp [index3]
    simp [eq]
  · change MvPowerSeries.coeff (index3 r s t) ((MvPowerSeries.X 1*MvPowerSeries.X 2)^q)=_
    rw [mul_pow,MvPowerSeries.X_pow_eq,MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial,MvPowerSeries.coeff_monomial]
    have eq : index3 r s t=Finsupp.single 1 q+Finsupp.single 2 q ↔ r=0 ∧ s=q ∧ t=q := by
      constructor
      · intro h
        exact ⟨by simpa [index3] using congrArg (fun d => d 0) h,
          by simpa [index3] using congrArg (fun d => d 1) h,
          by simpa [index3] using congrArg (fun d => d 2) h⟩
      · rintro ⟨rfl,rfl,rfl⟩; simp [index3]
    simp [eq]

private theorem kernel_coeff (k : ℕ) (i : Fin 3) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (outerKernel (R := R) k i) =
      if i=0 then (if r=s then
        (((-1 : ℂ)^t)*integerBinomial (-(k : ℤ)) t*(t.choose r : ℂ)) • (1 : R) else 0)
      else if i=1 then (if r=0 ∧ s=0 then
        (((-1 : ℂ)^t)*integerBinomial (-(k : ℤ)) t) • (1 : R) else 0)
      else (if r=0 ∧ s=t then
        (((-1 : ℂ)^t)*integerBinomial (-(k : ℤ)) t) • (1 : R) else 0) := by
  classical
  have negpower (q : ℕ) : (-outerBase R i)^q =
      MvPowerSeries.C ((-1 : R)^q)*outerBase R i^q := by
    calc
      _ = ((-1 : MvPowerSeries (Fin 3) R)*outerBase R i)^q := by rw [neg_one_mul]
      _ = _ := by rw [mul_pow]; simp
  rw [outerKernel,PowerSeries.coeff_subst (outer_legal i),finsum_eq_single _ t]
  · rw [negpower,MvPowerSeries.coeff_C_mul,binomial_coeff,base_pow_coeff]
    fin_cases i <;> simp [Algebra.smul_def,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]
  · intro q hq
    rw [negpower,MvPowerSeries.coeff_C_mul,base_pow_coeff]
    fin_cases i <;> simp [hq,Ne.symm hq]

private theorem single_mul_coeff (k n m t : ℕ) (G : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.coeff (index3 n m t) (outerKernel k 1*G) =
      ∑ T∈Finset.range (t+1),
        (((-1 : ℂ)^T)*integerBinomial (-(k : ℤ)) T) •
          MvPowerSeries.coeff (index3 n m (t-T)) G := by
  classical
  rw [coeff_mul_box,Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp [kernel_coeff,smul_mul_assoc]
    · intro v hv hne
      apply Finset.sum_eq_zero
      intro w hw
      simp [kernel_coeff,hne]
    · simp
  · intro u hu hne
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    simp [kernel_coeff,hne]
  · simp

private theorem diagonal_mul_coeff (k n m t : ℕ) (G : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.coeff (index3 n m t) (outerKernel k 2*G) =
      ∑ S∈Finset.range (t+1), if S≤m then
        (((-1 : ℂ)^S)*integerBinomial (-(k : ℤ)) S) •
          MvPowerSeries.coeff (index3 n (m-S) (t-S)) G else 0 := by
  rw [coeff_mul_box]
  simp only [kernel_coeff,show (2 : Fin 3)≠0 by decide,
    show (2 : Fin 3)≠1 by decide,ite_false,ite_mul,zero_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.sub_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases h : S≤m
    · rw [ite_eq_left h,Finset.sum_eq_single S]
      · simp [smul_mul_assoc]
      · intro v hv hne
        simp [hne]
      · simp only [Finset.mem_range,not_lt]
        omega
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro v hv
      have hne : v≠S := by have := Finset.mem_range.mp hv; omega
      simp [hne]
  · intro u hu hne
    apply Finset.sum_eq_zero
    intro v hv
    apply Finset.sum_eq_zero
    intro w hw
    simp [hne]
  · simp

private theorem coupled_mul_coeff (k n m t : ℕ) (G : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.coeff (index3 n m t) (outerKernel k 0*G) =
      ∑ H∈Finset.range (n+1), if H≤m then
        ∑ Q∈Finset.range (t+1),
          (((-1 : ℂ)^Q)*integerBinomial (-(k : ℤ)) Q*(Q.choose H : ℂ)) •
            MvPowerSeries.coeff (index3 (n-H) (m-H) (t-Q)) G else 0 := by
  rw [coeff_mul_box]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases h : H≤m
  · rw [ite_eq_left h,Finset.sum_eq_single H]
    · apply Finset.sum_congr rfl
      intro Q hQ
      simp [kernel_coeff,smul_mul_assoc]
    · intro v hv hne
      apply Finset.sum_eq_zero
      intro w hw
      simp [kernel_coeff,hne,Ne.symm hne]
    · simp only [Finset.mem_range,not_lt]
      omega
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : H≠v := by have := Finset.mem_range.mp hv; omega
    apply Finset.sum_eq_zero
    intro w hw
    simp [kernel_coeff,hne]

private def outerSigma (n m t : ℕ) :
    Finset (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) := by
  classical
  exact (Finset.range (n+1)).sigma fun H =>
    (Finset.range (t+1)).sigma fun Q =>
      (Finset.range (t-Q+1)).sigma fun T =>
        (Finset.range (t-Q-T+1)).filter fun S => H≤m ∧ H≤Q ∧ S≤m-H

private def outerFiber (n m t : ℕ) : Finset OuterIndex := by
  classical
  exact ((Finset.range (n+1)).product ((Finset.range (t+1)).product
    ((Finset.range (t+1)).product (Finset.range (m+1))))).filter
      (fun i => i.1≤n ∧ i.1+i.2.2.2≤m ∧ i.1+i.2.1+i.2.2.1+i.2.2.2≤t)

private theorem mem_outerFiber (n m t : ℕ) (i : OuterIndex) :
    i∈outerFiber n m t ↔ i.1≤n ∧ i.1+i.2.2.2≤m ∧
      i.1+i.2.1+i.2.2.1+i.2.2.2≤t := by
  classical
  simp only [outerFiber,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_range]
  omega

private theorem outer_sigma_coeff (k n m t : ℕ) (G : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.coeff (index3 n m t)
      (outerKernel k 0*(outerKernel k 1*(outerKernel k 2*G))) =
    ∑ i∈outerSigma n m t,
      outerWeight k (i.1,(i.2.1-i.1,i.2.2.1,i.2.2.2)) •
        MvPowerSeries.coeff (index3 (n-i.1) (m-i.1-i.2.2.2)
          (t-i.2.1-i.2.2.1-i.2.2.2)) G := by
  classical
  rw [coupled_mul_coeff]
  simp_rw [single_mul_coeff,diagonal_mul_coeff]
  simp only [outerSigma,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hm : H≤m
  · rw [ite_eq_left hm]
    apply Finset.sum_congr rfl
    intro Q hQ
    by_cases hq : H≤Q
    · simp only [Finset.smul_sum,Finset.sum_filter,hm,hq,true_and,smul_ite,
        smul_zero,smul_smul]
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs with hs
      · congr 1
        dsimp [outerWeight]
        rw [show H+(Q-H)=Q by omega]
        simp only [pow_add]
        ring
      · rfl
    · have zero : (Q.choose H : ℂ)=0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      simp [zero,Finset.sum_filter,hq]
  · rw [ite_eq_right hm]
    simp [Finset.sum_filter,hm]

private theorem outer_box_coeff (k n m t : ℕ) (G : MvPowerSeries (Fin 3) R) :
    MvPowerSeries.coeff (index3 n m t)
      (outerKernel k 0*(outerKernel k 1*(outerKernel k 2*G))) =
    ∑ i∈outerFiber n m t, outerWeight k i •
      MvPowerSeries.coeff (index3 (n-i.1) (m-i.1-i.2.2.2)
        (t-i.1-i.2.1-i.2.2.1-i.2.2.2)) G := by
  classical
  rw [outer_sigma_coeff]
  refine Finset.sum_bij (fun i _ => (i.1,(i.2.1-i.1,i.2.2.1,i.2.2.2))) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [outerSigma,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hi
    rw [mem_outerFiber]
    dsimp
    omega
  · intro i hi j hj he
    simp only [outerSigma,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hi hj
    have h0 := congrArg (fun i : OuterIndex => i.1) he
    have h1 := congrArg (fun i : OuterIndex => i.2.1) he
    have h2 := congrArg (fun i : OuterIndex => i.2.2.1) he
    have h3 := congrArg (fun i : OuterIndex => i.2.2.2) he
    dsimp at h0 h1 h2 h3
    apply Sigma.ext h0
    apply heq_of_eq
    apply Sigma.ext (by omega)
    apply heq_of_eq
    apply Sigma.ext h2
    exact heq_of_eq h3
  · intro i hi
    rw [mem_outerFiber] at hi
    refine ⟨⟨i.1,i.1+i.2.1,i.2.2.1,i.2.2.2⟩,?_,?_⟩
    · simp only [outerSigma,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range]
      omega
    · exact Prod.ext rfl (Prod.ext (by simp) (Prod.ext rfl rfl))
  · intro i hi
    simp only [outerSigma,Finset.mem_sigma,Finset.mem_filter,Finset.mem_range] at hi
    apply congrArg (fun v : R => outerWeight k
      (i.1,(i.2.1-i.1,i.2.2.1,i.2.2.2)) • v)
    apply congrArg (fun d => MvPowerSeries.coeff d G)
    ext c
    fin_cases c <;> simp [index3] <;> omega

end
end D5.S3.VertexAlgebra.FourFieldMiddleInverseKernel
