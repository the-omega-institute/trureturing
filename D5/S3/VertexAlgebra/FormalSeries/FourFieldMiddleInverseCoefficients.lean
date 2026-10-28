/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddleInverseCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldMiddleInverseCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven-index finite coefficient readout of the native middle inverse. -/
import D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleInverseKernel
import Batteries.Tactic.OpenPrivate

/-! The accepted three-index balanced inverse is composed with the four
outer binomial indices. Reindexing retains every signed numerator coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FourFieldMiddleInverseCoefficients
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldBalancedNativeInverse ThreeFieldBalancedLaurentFiber
open FourFieldMiddleNativeInverse FourFieldMiddleLaurentFiber FourFieldMiddleInverseKernel
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℂ R]
open private W numerator_coeff from D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleNativeInverse
open private outerKernel outer_inverse outerFiber mem_outerFiber outer_box_coeff from
  D5.S3.VertexAlgebra.FormalSeries.FourFieldMiddleInverseKernel
open private box weight native_inverse_box from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldBalancedInverseCoefficients

private def nativeFiber (n m t : ℕ) : Finset (Σ _ : BalancedIndex,OuterIndex) := by
  classical
  exact ((box n m).filter (fun i => i.1+i.2.2≤n ∧ i.1+i.2.1+i.2.2≤m)).sigma
    (fun i => outerFiber (n-i.1-i.2.2) (m-i.1-i.2.1-i.2.2) t)

private theorem mem_nativeFiber (n m t : ℕ) (i : Σ _ : BalancedIndex,OuterIndex) :
    i∈nativeFiber n m t ↔
      i.1.1+i.1.2.2+i.2.1≤n ∧
      i.1.1+i.1.2.1+i.1.2.2+i.2.1+i.2.2.2.2≤m ∧
      i.2.1+i.2.2.1+i.2.2.2.1+i.2.2.2.2≤t := by
  classical
  simp only [nativeFiber,Finset.mem_sigma,Finset.mem_filter,box,
    Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range,mem_outerFiber]
  omega

private theorem native_coeff (G : MvPowerSeries (Fin 3) R) (k A n m t : ℕ) :
    MvPowerSeries.coeff (index3 n m t)
      ((↑((middleUnit R k A)⁻¹) : MvPowerSeries (Fin 3) R)*G) =
      ∑ i∈nativeFiber n m t,
        (balancedWeight k (fun _ => A) i.1*outerWeight k i.2) •
          MvPowerSeries.coeff
            (index3 (n-i.1.1-i.1.2.2-i.2.1)
              (m-i.1.1-i.1.2.1-i.1.2.2-i.2.1-i.2.2.2.2)
              (t-i.2.1-i.2.2.1-i.2.2.2.1-i.2.2.2.2)) G := by
  classical
  rw [outer_inverse]
  simp only [mul_assoc]
  rw [native_inverse_box]
  simp_rw [outer_box_coeff,Finset.smul_sum,smul_smul]
  simp only [nativeFiber,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

private theorem native_readout (P : MvPowerSeries (Fin 4) R) (k : ℕ)
    (a : Fin 4 → ℕ) (e : Exponent 4) (n m t : ℕ)
    (hn : (n : ℤ)=e 1+k) (hm : (m : ℤ)=e 1+e 3+k+a 3)
    (ht : (t : ℤ)=e 1+e 3+e 2+a 1+a 2+a 3+3*k)
    (i : Σ _ : BalancedIndex,OuterIndex) (hi : i∈nativeFiber n m t) :
    MvPowerSeries.coeff
      (index3 (n-i.1.1-i.1.2.2-i.2.1)
        (m-i.1.1-i.1.2.1-i.1.2.2-i.2.1-i.2.2.2.2)
        (t-i.2.1-i.2.2.1-i.2.2.2.1-i.2.2.2.2))
      (numeratorSlice P (total e+degree k a)) =
        signedExtend P (middleInput k a e (i.1,i.2)) := by
  rw [numerator_coeff]
  rw [mem_nativeFiber] at hi
  congr 1
  funext c
  fin_cases c <;> dsimp [middleInput,total,degree] <;> push_cast <;> omega

/-- The genuine native inverse equals the explicit seven-index finite fiber,
including all negative-target and negative-numerator branches. -/
theorem raw_middle_coefficients (P : MvPowerSeries (Fin 4) R) (k : ℕ)
    (a : Fin 4 → ℕ) (e : Exponent 4) :
    rawMiddleCoefficient P k a e=middleCoefficient P k a e := by
  classical
  let w := W e+middleShift k a
  by_cases hw : ∀ c,0≤w c
  · let n : Fin 3 → ℕ := fun c => (w c).toNat
    have hn : (n 0 : ℤ)=e 1+k := Int.toNat_of_nonneg (hw 0)
    have hm : (n 1 : ℤ)=e 1+e 3+k+a 3 := by
      have h := Int.toNat_of_nonneg (hw 1)
      change (n 1 : ℤ)=w 1 at h
      dsimp [w,W,middleShift] at h
      omega
    have ht : (n 2 : ℤ)=e 1+e 3+e 2+a 1+a 2+a 3+3*k := by
      have h := Int.toNat_of_nonneg (hw 2)
      change (n 2 : ℤ)=w 2 at h
      dsimp [w,W,middleShift] at h
      omega
    have idx : signedIndex w=index3 (n 0) (n 1) (n 2) := by
      ext c
      fin_cases c <;> simp [signedIndex,index3,n]
    change signedExtend _ w=_
    rw [signedExtend,ite_eq_left hw]
    change MvPowerSeries.coeff (signedIndex w)
      ((↑((middleUnit R k (a 1))⁻¹) : MvPowerSeries (Fin 3) R)*
        numeratorSlice P (total e+degree k a))=_
    rw [idx,native_coeff]
    have hread :
        (∑ i∈nativeFiber (n 0) (n 1) (n 2),
          (balancedWeight k (fun _ => a 1) i.1*outerWeight k i.2) •
            MvPowerSeries.coeff
              (index3 (n 0-i.1.1-i.1.2.2-i.2.1)
                (n 1-i.1.1-i.1.2.1-i.1.2.2-i.2.1-i.2.2.2.2)
                (n 2-i.2.1-i.2.2.1-i.2.2.2.1-i.2.2.2.2))
              (numeratorSlice P (total e+degree k a))) =
        ∑ i∈nativeFiber (n 0) (n 1) (n 2),
          (balancedWeight k (fun _ => a 1) i.1*outerWeight k i.2) •
            signedExtend P (middleInput k a e (i.1,i.2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [native_readout P k a e (n 0) (n 1) (n 2) hn hm ht i hi]
    rw [hread]
    unfold middleCoefficient
    refine Finset.sum_bij_ne_zero (fun i _ _ => (i.1,i.2)) ?_ ?_ ?_ ?_
    · intro i hi hne
      rw [mem_middleFiber_iff]
      by_contra ha
      apply hne
      have hz : signedExtend P (middleInput k a e (i.1,i.2)) = 0 := by
        apply ite_eq_right
        exact ha
      rw [hz,smul_zero]
    · intro i hi hne j hj hnej he
      exact Sigma.ext (congrArg Prod.fst he) (heq_of_eq (congrArg Prod.snd he))
    · intro i hi hne
      have ha := (mem_middleFiber_iff k a e i).mp hi
      have hb := middle_bounds k a e i ha
      refine ⟨⟨i.1,i.2⟩,?_,?_,rfl⟩
      · rw [mem_nativeFiber]
        dsimp
        omega
      · simpa only [middleWeight,balancedWeight,Fin.succ_zero_eq_one] using hne
    · intro i hi hne
      rfl
  · change signedExtend _ w=_
    rw [signedExtend,ite_eq_right hw]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hb := middle_bounds k a e i ((mem_middleFiber_iff k a e i).mp hi)
    exfalso
    apply hw
    intro c
    fin_cases c <;> dsimp [w,W,middleShift] <;> omega

end
end D5.S3.VertexAlgebra.FourFieldMiddleInverseCoefficients
