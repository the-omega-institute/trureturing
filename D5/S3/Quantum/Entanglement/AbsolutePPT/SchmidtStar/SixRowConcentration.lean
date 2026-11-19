/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowConcentration
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowConcentration
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual 15/21 gap concentration, heterogeneous moments and original equality. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAllNScalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-!
The 15/21 boundary moments belong to the original spectrum. Concentration
bounds its purity using auxiliary gap vectors with their own masses. The
strict summand argument transfers equality back to every original entry.
-/
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowConcentration
open Finset
open UniformSpectralBound.SharedSpectral
open SixRowScalarData
noncomputable section

def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => 14 ≤ i.val ∧ i.val < N-21)
def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ i ∈ middle N, g i
def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  ∑ i ∈ univ.filter (fun i => i ∉ middle N), g i • step N (i.val+1)
def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ :=
  frozen g + middleMass g • step N (j.val+1)

def U {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨N-21,by omega⟩
def B {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨14,by omega⟩
def V {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := B hN l-U hN l
def r {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := V hN l/U hN l
def heads {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : Fin 15 → ℝ :=
  fun i => (l ⟨i.val,by omega⟩-B hN l)/U hN l
def tails {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : Fin 21 → ℝ :=
  fun i => (U hN l-l ⟨N-21+i.val,by omega⟩)/U hN l
def H {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,heads hN l i
def D {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,tails hN l i
def a {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,(heads hN l i)^2
def q {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,(tails hN l i)^2

private theorem split_gaps {N : ℕ} (g : Fin N → ℝ) :
    frozen g+∑ i ∈ middle N,g i • step N (i.val+1) =
      ∑ i,g i • step N (i.val+1) := by
  classical
  have hs : (∑ i ∈ middle N,g i • step N (i.val+1)) =
      ∑ i,if i ∈ middle N then g i • step N (i.val+1) else 0 := by
    rw [← sum_filter]
    congr 1
    ext i
    simp
  rw [hs]
  simp only [frozen,sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ middle N <;> simp [hi]

theorem reconstruction {N : ℕ} (l : Fin N → ℝ) :
    frozen (spectralGap l)+
      ∑ i ∈ middle N,spectralGap l i • step N (i.val+1)=l := by
  rw [split_gaps,gap_reconstruct]

private theorem middle_nonempty {N : ℕ} (hN : 36 ≤ N) : (middle N).Nonempty := by
  refine ⟨⟨14,by omega⟩,?_⟩
  simp only [middle,mem_filter,mem_univ,true_and]
  omega

theorem middle_mass_actual {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) :
    middleMass (spectralGap l)=V hN l := by
  classical
  unfold middleMass middle
  simp only [sum_filter,spectralGap]
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
    if 14 ≤ i ∧ i < N-21 then extend l i-extend l (i+1) else 0)]
  rw [sum_ite]
  simp only [sum_const_zero,add_zero]
  have hf : (range N).filter (fun i => 14 ≤ i ∧ i < N-21)=Ico 14 (N-21) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l 14 (N-21) (by omega)]
  simp [extend,V,B,U,show 14 < N by omega,show N-21 < N by omega]

/-- Precisely the original first 15 and last 21 labelled entries. -/
theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N)
    (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 15 ∨ N-21 ≤ k.val) :
    concentrated (spectralGap l) j k=l k := by
  classical
  have hs := reconstruction l
  have hstep (i : Fin N) (hi : i ∈ middle N) :
      step N (i.val+1) k=step N (j.val+1) k := by
    have hmi := (mem_filter.mp hi).2
    have hmj := (mem_filter.mp hj).2
    rcases hk with hk | hk
    · simp [step,show k.val < i.val+1 by omega,show k.val < j.val+1 by omega]
    · simp [step,show ¬k.val < i.val+1 by omega,show ¬k.val < j.val+1 by omega]
  have hsum : (∑ i ∈ middle N,spectralGap l i • step N (i.val+1)) k =
      middleMass (spectralGap l)*step N (j.val+1) k := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,middleMass]
    rw [sum_mul]
    exact sum_congr rfl (fun i hi => by rw [hstep i hi])
  have hv := congrFun hs k
  simpa [concentrated,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsum] using hv

theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l)
    (hl : ∀ k,0 ≤ l k) (j : Fin N) : ∀ k,0 ≤ concentrated (spectralGap l) j k := by
  have hg := spectralGap_nonneg l ho hl
  have ht (i k : Fin N) : 0 ≤ step N (i.val+1) k := by
    unfold step
    split_ifs <;> norm_num
  have hm : 0 ≤ middleMass (spectralGap l) := sum_nonneg (fun i _ => hg i)
  intro k
  unfold concentrated frozen
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  exact add_nonneg (sum_nonneg (fun i _ => mul_nonneg (hg i) (ht i k)))
    (mul_nonneg hm (ht j k))

private theorem middle_contribution {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (k : Fin N) (hk : 15 ≤ k.val ∧ k.val < N-21) :
    (∑ i ∈ middle N,spectralGap l i • step N (i.val+1)) k=l k-U hN l := by
  classical
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,middle,sum_filter]
  have he (i : Fin N) :
      (if 14 ≤ i.val ∧ i.val < N-21 then
        spectralGap l i*step N (i.val+1) k else 0) =
      (if k.val ≤ i.val ∧ i.val < N-21 then
        extend l i.val-extend l (i.val+1) else 0) := by
    by_cases hi : k.val ≤ i.val ∧ i.val < N-21
    · have hm : 14 ≤ i.val ∧ i.val < N-21 := by omega
      simp only [if_pos hi,if_pos hm,spectralGap,step,
        if_pos (show k.val < i.val+1 by omega)]
      ring
    · by_cases hm : 14 ≤ i.val ∧ i.val < N-21
      · simp only [if_neg hi,if_pos hm,step,
          if_neg (show ¬k.val < i.val+1 by omega),mul_zero]
      · simp only [if_neg hi,if_neg hm]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
    if k.val ≤ i ∧ i < N-21 then extend l i-extend l (i+1) else 0)]
  rw [sum_ite]
  simp only [sum_const_zero,add_zero]
  have hf : (range N).filter (fun i => k.val ≤ i ∧ i < N-21)=Ico k.val (N-21) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l k.val (N-21) (by omega)]
  simp [extend,U,k.isLt,show N-21 < N by omega]

private theorem concentrated_interior {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (j k : Fin N) (hk : 15 ≤ k.val ∧ k.val < N-21) :
    concentrated (spectralGap l) j k=U hN l+V hN l*step N (j.val+1) k := by
  have hs := congrFun (reconstruction l) k
  have hm := middle_contribution hN l k hk
  change frozen (spectralGap l) k+
    (∑ i ∈ middle N,spectralGap l i • step N (i.val+1)) k=l k at hs
  have hf : frozen (spectralGap l) k=U hN l := by linarith
  simp [concentrated,middle_mass_actual hN l,hf]

private def headPad {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) (k : Fin N) : ℝ :=
  if hk : k.val < 15 then heads hN l ⟨k.val,hk⟩ else 0
private def tailPad {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) (k : Fin N) : ℝ :=
  if hk : N-21 ≤ k.val then tails hN l ⟨k.val-(N-21),by omega⟩ else 0

private theorem headPad_sum {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ k,F (headPad hN l k))=∑ i : Fin 15,F (heads hN l i) := by
  classical
  calc
    _ = ∑ k ∈ univ.filter (fun k : Fin N => k.val < 15),F (headPad hN l k) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : k.val < 15 <;> simp [headPad,hk,hF]
    _ = _ := by
      symm
      apply sum_bij (fun (i : Fin 15) _ => (⟨i.val,by omega⟩ : Fin N))
      · intro i _
        simp [i.isLt]
      · intro i _ j _ hij
        exact Fin.ext (congrArg (fun z : Fin N => z.val) hij)
      · intro k hk
        have hk' : k.val < 15 := (mem_filter.mp hk).2
        exact ⟨⟨k.val,hk'⟩,mem_univ _,Fin.ext rfl⟩
      · intro i _
        simp [headPad,i.isLt]

private theorem tailPad_sum {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ k,F (tailPad hN l k))=∑ i : Fin 21,F (tails hN l i) := by
  classical
  calc
    _ = ∑ k ∈ univ.filter (fun k : Fin N => N-21 ≤ k.val),F (tailPad hN l k) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : N-21 ≤ k.val <;> simp [tailPad,hk,hF]
    _ = _ := by
      symm
      apply sum_bij (fun (i : Fin 21) _ => (⟨N-21+i.val,by omega⟩ : Fin N))
      · intro i _
        simp only [mem_filter,mem_univ,true_and]
        omega
      · intro i _ j _ hij
        apply Fin.ext
        have hi := congrArg Fin.val hij
        dsimp at hi
        omega
      · intro k hk
        have hk' : N-21 ≤ k.val := (mem_filter.mp hk).2
        refine ⟨⟨k.val-(N-21),by omega⟩,mem_univ _,?_⟩
        apply Fin.ext
        dsimp
        omega
      · intro i _
        simp [tailPad,show N-21 ≤ N-21+i.val by omega]

private theorem concentrated_polynomials {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (hU : 0 < U hN l) (j : Fin N) (hj : j ∈ middle N) (k : Fin N) :
    concentrated (spectralGap l) j k =
      U hN l*(1+r hN l*step N (j.val+1) k+headPad hN l k-tailPad hN l k) ∧
    (concentrated (spectralGap l) j k)^2 = (U hN l)^2*
      (1+(2*r hN l+(r hN l)^2)*step N (j.val+1) k+
        2*(1+r hN l)*headPad hN l k-2*tailPad hN l k+
        (headPad hN l k)^2+(tailPad hN l k)^2) := by
  have hu : U hN l ≠ 0 := ne_of_gt hU
  have hj' : 14 ≤ j.val ∧ j.val < N-21 := (mem_filter.mp hj).2
  by_cases hh : k.val < 15
  · have ht : ¬N-21 ≤ k.val := by omega
    rw [concentrated_boundary l j hj k (Or.inl hh)]
    simp only [headPad,tailPad,dif_pos hh,dif_neg ht,step,
      if_pos (show k.val < j.val+1 by omega)]
    dsimp only [heads,r,V]
    have hi : (⟨k.val,by omega⟩ : Fin N)=k := Fin.ext rfl
    simp only [hi]
    constructor <;> field_simp [hu] <;> ring
  · by_cases ht : N-21 ≤ k.val
    · rw [concentrated_boundary l j hj k (Or.inr ht)]
      simp only [headPad,tailPad,dif_neg hh,dif_pos ht,step,
        if_neg (show ¬k.val < j.val+1 by omega)]
      have hi : (⟨N-21+(k.val-(N-21)),by omega⟩ : Fin N)=k := by
        apply Fin.ext
        dsimp
        omega
      simp only [tails,hi]
      constructor <;> field_simp [hu] <;> ring
    · rw [concentrated_interior hN l j k (by omega)]
      simp only [headPad,tailPad,dif_neg hh,dif_neg ht]
      dsimp only [r]
      unfold step
      split_ifs <;> constructor <;> field_simp [hu] <;> ring

/-- Actual heterogeneous raw moments, with the exact scalar definitions. -/
theorem concentrated_raw_moments {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ)
    (hU : 0 < U hN l) (j : Fin N) (hj : j ∈ middle N) :
    (∑ k,concentrated (spectralGap l) j k) =
      U hN l*mass (N:ℝ) (j.val+1:ℕ) (r hN l) (H hN l) (D hN l) ∧
    (∑ k,(concentrated (spectralGap l) j k)^2) =
      (U hN l)^2*energy (N:ℝ) (j.val+1:ℕ)
        (r hN l) (H hN l) (D hN l) (a hN l) (q hN l) := by
  have hJ : j.val+1 ≤ N := by omega
  have hh := headPad_sum hN l (fun x => x) rfl
  have hd := tailPad_sum hN l (fun x => x) rfl
  have ha := headPad_sum hN l (fun x => x^2) (by norm_num)
  have hq := tailPad_sum hN l (fun x => x^2) (by norm_num)
  change (∑ k,headPad hN l k)=H hN l at hh
  change (∑ k,tailPad hN l k)=D hN l at hd
  change (∑ k,(headPad hN l k)^2)=a hN l at ha
  change (∑ k,(tailPad hN l k)^2)=q hN l at hq
  have hp (k : Fin N) := (concentrated_polynomials hN l hU j hj k).1
  have hs (k : Fin N) := (concentrated_polynomials hN l hU j hj k).2
  constructor
  · simp_rw [hp]
    rw [← mul_sum]
    simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,hh,hd,sum_step N (j.val+1) hJ,mass]
    ring
  · simp_rw [hs]
    rw [← mul_sum]
    simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,hh,hd,ha,hq,sum_step N (j.val+1) hJ,
      energy,mass,SixRowMiddlePolynomial.W]
    ring

/-- The positive-middle-gap mixture; no equal-mass premise. -/
theorem mixture_identity {N : ℕ} (g : Fin N → ℝ) (hV : 0 < middleMass g) :
    (∑ i ∈ middle N,(g i/middleMass g) • concentrated g i) =
      frozen g+∑ i ∈ middle N,g i • step N (i.val+1) := by
  simp only [concentrated,smul_add,smul_smul,sum_add_distrib]
  rw [← sum_smul,← sum_div]
  rw [show (∑ i ∈ middle N, g i) = middleMass g from rfl]
  simp only [div_self (ne_of_gt hV),one_smul,
    div_mul_cancel₀ _ (ne_of_gt hV)]

private theorem zero_middle {N : ℕ} (g : Fin N → ℝ) (hg : ∀ i,0 ≤ g i)
    (hz : middleMass g=0) (j : Fin N) :
    concentrated g j=frozen g+∑ i ∈ middle N,g i • step N (i.val+1) := by
  have hgi : ∀ i ∈ middle N,g i=0 :=
    (sum_eq_zero_iff_of_nonneg (fun i _ => hg i)).mp hz
  have hs : (∑ i ∈ middle N,g i • step N (i.val+1))=0 := by
    apply sum_eq_zero
    intro i hi
    rw [hgi i hi,zero_smul]
  simp [concentrated,hz,hs]

private theorem concentration_transfer {N : ℕ} (hN : 36 ≤ N) (theta : ℝ)
    (ht : 0 ≤ theta) (l : Fin N → ℝ) (ho : Antitone l) (hl : ∀ i,0 ≤ l i)
    (hb : ∀ j ∈ middle N,
      ∑ i,(concentrated (spectralGap l) j i)^2 ≤
        theta*(∑ i,concentrated (spectralGap l) j i)^2) :
    ∑ i,(l i)^2 ≤ theta*(∑ i,l i)^2 := by
  have hg := spectralGap_nonneg l ho hl
  have hgood : spectralGood (Real.sqrt theta) l := by
    have hfixed (j : Fin N) (hj : j ∈ middle N) :
        spectralGood (Real.sqrt theta) (concentrated (spectralGap l) j) := by
      apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
        (sum_nonneg (fun i _ => concentrated_nonnegative l ho hl j i))
      simpa [Real.sq_sqrt ht] using hb j hj
    have hm := mixture_transfer (spectralGood (Real.sqrt theta))
      (spectralGood_zero N _) (fun x y hx hy => spectralGood_add _ x y hx hy)
      (fun t x ht' hx => spectralGood_smul _ t x ht' hx)
      (middle N) (middle_nonempty hN) (spectralGap l) (fun i => step N (i.val+1))
      (frozen (spectralGap l)) (fun i _ => hg i) hfixed
    rwa [reconstruction] at hm
  have hb' := spectralGood_square (Real.sqrt theta) l (Real.sqrt_nonneg _)
    (sum_nonneg (fun i _ => hl i)) hgood
  simpa [Real.sq_sqrt ht] using hb'

/-- A strict active scalar summand prevents original equality before the
triangle step. This proves only active individual equality, and uses no
classification of equality in the triangle inequality. -/
private theorem active_square_equality {N : ℕ} (theta : ℝ) (ht : 0 ≤ theta)
    (l : Fin N → ℝ) (ho : Antitone l) (hl : ∀ k,0 ≤ l k)
    (hV : 0 < middleMass (spectralGap l))
    (hb : ∀ j ∈ middle N,
      ∑ k,(concentrated (spectralGap l) j k)^2 ≤
        theta*(∑ k,concentrated (spectralGap l) j k)^2)
    (he : ∑ k,(l k)^2=theta*(∑ k,l k)^2)
    (j : Fin N) (hj : j ∈ middle N) (hgj : 0 < spectralGap l j) :
    ∑ k,(concentrated (spectralGap l) j k)^2 =
      theta*(∑ k,concentrated (spectralGap l) j k)^2 := by
  classical
  let g := spectralGap l
  let mu := concentrated g
  let t : Fin N → ℝ := fun i => g i/middleMass g
  let c := Real.sqrt theta
  have hg : ∀ i,0 ≤ g i := spectralGap_nonneg l ho hl
  have hw (i : Fin N) : 0 ≤ t i := div_nonneg (hg i) (le_of_lt hV)
  have hgood (i : Fin N) (hi : i ∈ middle N) : spectralGood c (mu i) := by
    apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
      (sum_nonneg (fun k _ => concentrated_nonnegative l ho hl i k))
    simpa [c,Real.sq_sqrt ht] using hb i hi
  have hid : (∑ i ∈ middle N,t i • mu i)=l := by
    rw [mixture_identity g hV,reconstruction]
  have hmass : (∑ i ∈ middle N,t i*(∑ k,mu i k))=∑ k,l k := by
    calc
      _ = ∑ k,(∑ i ∈ middle N,t i • mu i) k := by
        simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum]
        rw [sum_comm]
      _ = _ := by rw [hid]
  have htriangle : ‖WithLp.toLp 2 l‖ ≤ ∑ i ∈ middle N,t i*‖WithLp.toLp 2 (mu i)‖ := by
    calc
      _ = ‖∑ i ∈ middle N,t i • WithLp.toLp 2 (mu i)‖ := by
        rw [← hid]
        simp only [WithLp.toLp_sum,WithLp.toLp_smul]
      _ ≤ ∑ i ∈ middle N,‖t i • WithLp.toLp 2 (mu i)‖ := norm_sum_le _ _
      _ = _ := sum_congr rfl (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw i)])
  have hnorm : ‖WithLp.toLp 2 l‖=c*(∑ k,l k) := by
    have hs : ‖WithLp.toLp 2 l‖^2=(c*(∑ k,l k))^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,mul_pow]
      simpa [c,Real.sq_sqrt ht] using he
    have hm : 0 ≤ c*(∑ k,l k) :=
      mul_nonneg (Real.sqrt_nonneg _) (sum_nonneg (fun k _ => hl k))
    exact (sq_eq_sq₀ (norm_nonneg _) hm).mp hs
  let delta : Fin N → ℝ := fun i =>
    t i*(c*(∑ k,mu i k)-‖WithLp.toLp 2 (mu i)‖)
  have hd (i : Fin N) (hi : i ∈ middle N) : 0 ≤ delta i :=
    mul_nonneg (hw i) (sub_nonneg.mpr (hgood i hi))
  have hdecomp : (∑ i ∈ middle N,t i*‖WithLp.toLp 2 (mu i)‖)+
      (∑ i ∈ middle N,delta i)=c*(∑ k,l k) := by
    rw [← hmass,← sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only [delta]
    ring
  have hd0 : (∑ i ∈ middle N,delta i)=0 := by
    have hnonneg := sum_nonneg hd
    linarith only [hdecomp,htriangle,hnorm,hnonneg]
  have hj0 := (sum_eq_zero_iff_of_nonneg hd).mp hd0 j hj
  have htj : 0 < t j := div_pos hgj hV
  have hmu : ‖WithLp.toLp 2 (mu j)‖=c*(∑ k,mu j k) := by
    have hz := (mul_eq_zero.mp hj0).resolve_left (ne_of_gt htj)
    linarith only [hz]
  have hs := congrArg (fun z : ℝ => z^2) hmu
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow] at hs
  simpa [c,Real.sq_sqrt ht] using hs

private theorem theta_pos (n : ℕ) (hn : 23 ≤ n) : 0 < theta n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold theta
  split_ifs <;> positivity

private theorem concentrated_bounds (n : ℕ) (hn : 23 ≤ n) (hN : 36 ≤ 6*n)
    (l : Fin (6*n) → ℝ) (hU : 0 < U hN l)
    (hphys : PhysicalScalarHyp (r hN l) (H hN l) (D hN l) (a hN l) (q hN l))
    (j : Fin (6*n)) (hj : j ∈ middle (6*n)) :
    0 < (∑ k,concentrated (spectralGap l) j k) ∧
    (∑ k,(concentrated (spectralGap l) j k)^2) ≤
      theta n*(∑ k,concentrated (spectralGap l) j k)^2 ∧
    ((∑ k,(concentrated (spectralGap l) j k)^2) =
      theta n*(∑ k,concentrated (spectralGap l) j k)^2 ↔
      r hN l=2/5 ∧ H hN l=0 ∧ D hN l=0 ∧ a hN l=0 ∧ q hN l=0 ∧
        j.val+1=centralIndex n) := by
  have hj' : 14 ≤ j.val ∧ j.val < 6*n-21 := (mem_filter.mp hj).2
  have hs := SixRowAllNScalar.concentrated_scalar n (j.val+1) hn
    (by omega) (by omega) (r hN l) (H hN l) (D hN l) (a hN l) (q hN l) hphys
  have hm := concentrated_raw_moments hN l hU j hj
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hm
  let M := mass (6*(n:ℝ)) (j.val+1:ℕ) (r hN l) (H hN l) (D hN l)
  let E := energy (6*(n:ℝ)) (j.val+1:ℕ)
    (r hN l) (H hN l) (D hN l) (a hN l) (q hN l)
  change 0 < M ∧ E ≤ theta n*M^2 ∧
    (E=theta n*M^2 ↔ _) at hs
  change (∑ k,concentrated (spectralGap l) j k)=U hN l*M ∧
    (∑ k,(concentrated (spectralGap l) j k)^2)=(U hN l)^2*E at hm
  rw [hm.1,hm.2]
  refine ⟨mul_pos hU hs.1,?_,?_⟩
  · calc
      (U hN l)^2*E ≤ (U hN l)^2*(theta n*M^2) :=
        mul_le_mul_of_nonneg_left hs.2.1 (sq_nonneg _)
      _ = theta n*(U hN l*M)^2 := by ring
  · have hc : (U hN l)^2*E=theta n*(U hN l*M)^2 ↔ E=theta n*M^2 := by
      constructor
      · intro he
        have he' : (U hN l)^2*(E-theta n*M^2)=0 := by nlinarith only [he]
        have he'' := (mul_eq_zero.mp he').resolve_left (ne_of_gt (sq_pos_of_pos hU))
        linarith only [he'']
      · intro he
        rw [he]
        ring
    exact hc.trans hs.2.2

private theorem equality_support (n : ℕ) (hn : 23 ≤ n) (hN : 36 ≤ 6*n)
    (l : Fin (6*n) → ℝ) (ho : Antitone l) (hl : ∀ k,0 ≤ l k)
    (hU : 0 < U hN l)
    (hphys : PhysicalScalarHyp (r hN l) (H hN l) (D hN l) (a hN l) (q hN l))
    (he : ∑ k,(l k)^2=theta n*(∑ k,l k)^2) :
    0 < V hN l ∧ r hN l=2/5 ∧ H hN l=0 ∧ D hN l=0 ∧
      a hN l=0 ∧ q hN l=0 ∧
      ∀ i ∈ middle (6*n),i.val+1 ≠ centralIndex n → spectralGap l i=0 := by
  classical
  have hg := spectralGap_nonneg l ho hl
  have hV0 : 0 ≤ V hN l := by
    rw [← middle_mass_actual hN l]
    exact sum_nonneg (fun i _ => hg i)
  have hV : 0 < V hN l := by
    by_contra hv
    have hz : V hN l=0 := le_antisymm (le_of_not_gt hv) hV0
    obtain ⟨j,hj⟩ := middle_nonempty hN
    have hmu := zero_middle (spectralGap l) hg
      (by rw [middle_mass_actual hN l,hz]) j
    rw [reconstruction] at hmu
    have hme : (∑ k,(concentrated (spectralGap l) j k)^2) =
        theta n*(∑ k,concentrated (spectralGap l) j k)^2 := by rw [hmu]; exact he
    have hr := ((concentrated_bounds n hn hN l hU hphys j hj).2.2.mp hme).1
    have hr0 : r hN l=0 := by simp [r,hz]
    rw [hr0] at hr
    norm_num at hr
  have hVp : 0 < middleMass (spectralGap l) := by rwa [middle_mass_actual hN l]
  have hactive (i : Fin (6*n)) (hi : i ∈ middle (6*n)) (hgi : 0 < spectralGap l i) :
      r hN l=2/5 ∧ H hN l=0 ∧ D hN l=0 ∧ a hN l=0 ∧ q hN l=0 ∧
        i.val+1=centralIndex n := by
    apply (concentrated_bounds n hn hN l hU hphys i hi).2.2.mp
    exact active_square_equality (theta n) (le_of_lt (theta_pos n hn)) l ho hl hVp
      (fun j hj => (concentrated_bounds n hn hN l hU hphys j hj).2.1) he i hi hgi
  obtain ⟨j,hj,hgj⟩ := (sum_pos_iff_of_nonneg (fun i _ => hg i)).mp hVp
  obtain ⟨hr,hH,hD,ha,hq,hjstar⟩ := hactive j hj hgj
  refine ⟨hV,hr,hH,hD,ha,hq,?_⟩
  intro i hi hne
  by_contra hgi
  have hip : 0 < spectralGap l i := lt_of_le_of_ne (hg i) (Ne.symm hgi)
  exact hne (hactive i hi hip).2.2.2.2.2

def centralSpectrum (n : ℕ) : Fin (6*n) → ℝ := fun k =>
  if k.val < centralIndex n then
    7/(30*(n:ℝ)+2*(centralIndex n:ℝ))
  else 5/(30*(n:ℝ)+2*(centralIndex n:ℝ))

private theorem central_index_bounds (n : ℕ) (hn : 23 ≤ n) :
    15 ≤ centralIndex n ∧ centralIndex n ≤ 6*n-21 := by
  dsimp only [centralIndex]
  omega

private theorem equality_vector (n : ℕ) (hn : 23 ≤ n) (hN : 36 ≤ 6*n)
    (l : Fin (6*n) → ℝ) (ho : Antitone l) (hl : ∀ k,0 ≤ l k)
    (hs : ∑ k,l k=1) (hU : 0 < U hN l)
    (hphys : PhysicalScalarHyp (r hN l) (H hN l) (D hN l) (a hN l) (q hN l))
    (he : ∑ k,(l k)^2=theta n) : l=centralSpectrum n := by
  classical
  have he' : ∑ k,(l k)^2=theta n*(∑ k,l k)^2 := by simpa [hs] using he
  obtain ⟨hV,hr,hH,hD,ha,hq,hgap⟩ := equality_support n hn hN l ho hl hU hphys he'
  have hh : ∀ i,heads hN l i=0 := by
    intro i
    have hz := (sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ univ) =>
      sq_nonneg (heads hN l k))).mp ha i (mem_univ i)
    exact sq_eq_zero_iff.mp hz
  have hd : ∀ i,tails hN l i=0 := by
    intro i
    have hz := (sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ univ) =>
      sq_nonneg (tails hN l k))).mp hq i (mem_univ i)
    exact sq_eq_zero_iff.mp hz
  have hhp (k : Fin (6*n)) : headPad hN l k=0 := by
    unfold headPad
    split_ifs <;> simp [hh]
  have hdp (k : Fin (6*n)) : tailPad hN l k=0 := by
    unfold tailPad
    split_ifs <;> simp [hd]
  have hb := central_index_bounds n hn
  let j : Fin (6*n) := ⟨centralIndex n-1,by omega⟩
  have hjval : j.val+1=centralIndex n := by dsimp only [j]; omega
  have hj : j ∈ middle (6*n) := by
    simp only [middle,mem_filter,mem_univ,true_and]
    dsimp only [j]
    omega
  have hmid : (∑ i ∈ middle (6*n),spectralGap l i • step (6*n) (i.val+1)) =
      middleMass (spectralGap l) • step (6*n) (j.val+1) := by
    rw [middleMass,sum_smul]
    apply sum_congr rfl
    intro i hi
    by_cases hidx : i.val+1=centralIndex n
    · rw [hidx,hjval]
    · rw [hgap i hi hidx,zero_smul,zero_smul]
  have hlmu : l=concentrated (spectralGap l) j := by
    have hs' := reconstruction l
    rw [hmid] at hs'
    exact hs'.symm
  have hpoint (k : Fin (6*n)) :
      l k=U hN l*(1+(2/5)*step (6*n) (centralIndex n) k) := by
    calc
      l k=concentrated (spectralGap l) j k := congrFun hlmu k
      _ = _ := by
        have hp := (concentrated_polynomials hN l hU j hj k).1
        simpa only [hr,hhp,hdp,hjval,add_zero,sub_zero] using hp
  have hmass : U hN l*((6*n:ℕ)+(2/5)*(centralIndex n:ℝ))=1 := by
    rw [← hs]
    simp_rw [hpoint]
    rw [← mul_sum]
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← mul_sum,sum_step (6*n) (centralIndex n) (by omega)]
    ring
  let den : ℝ := 30*(n:ℝ)+2*(centralIndex n:ℝ)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < den := by dsimp only [den]; positivity
  have hu : U hN l=5/den := by
    apply (eq_div_iff (ne_of_gt hden)).mpr
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hmass
    dsimp only [den]
    nlinarith only [hmass]
  funext k
  rw [hpoint,hu]
  change (5/den)*(1+(2/5)*step (6*n) (centralIndex n) k)=
    if k.val < centralIndex n then 7/den else 5/den
  unfold step
  split_ifs <;> ring

/-- Direct central scalar evaluation gives the reverse ordered-spectrum
equality. Literal APPT attainment of this vector remains a separate job. -/
private theorem central_purity (n : ℕ) (hn : 23 ≤ n) :
    ∑ k,(centralSpectrum n k)^2=theta n := by
  let den : ℝ := 30*(n:ℝ)+2*(centralIndex n:ℝ)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < den := by dsimp only [den]; positivity
  have hidx : centralIndex n ≤ 6*n := (central_index_bounds n hn).2.trans (by omega)
  have hp (k : Fin (6*n)) : (centralSpectrum n k)^2 =
      (25+24*step (6*n) (centralIndex n) k)/den^2 := by
    change (if k.val < centralIndex n then 7/den else 5/den)^2 = _
    unfold step
    split_ifs <;> simp only [div_pow] <;> ring
  have hs : (∑ k,(centralSpectrum n k)^2)=
      (25*(6*(n:ℝ))+24*(centralIndex n:ℝ))/den^2 := by
    simp_rw [hp]
    rw [← sum_div]
    congr 1
    simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← mul_sum,sum_step (6*n) (centralIndex n) hidx,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hg := SixRowAllNScalar.central_gap_zero n hn
  dsimp only [gap,energy,mass,SixRowMiddlePolynomial.W] at hg
  have hrel : theta n*den^2=25*(6*(n:ℝ))+24*(centralIndex n:ℝ) := by
    dsimp only [den]
    nlinarith only [hg]
  rw [hs]
  exact (div_eq_iff (pow_ne_zero 2 (ne_of_gt hden))).mpr hrel.symm

/-- Live original-spectrum consumer. The explicit physical record is of
the ORIGINAL boundary values defined above, and is not literal APPT input.
An independent literal APPT supplier must produce hU and hphys. -/
theorem original_upper_and_equality (n : ℕ) (hn : 23 ≤ n) (hN : 36 ≤ 6*n)
    (l : Fin (6*n) → ℝ) (ho : Antitone l) (hl : ∀ k,0 ≤ l k)
    (hs : ∑ k,l k=1) (hU : 0 < U hN l)
    (hphys : PhysicalScalarHyp (r hN l) (H hN l) (D hN l) (a hN l) (q hN l)) :
    (∑ k,(l k)^2 ≤ theta n) ∧
      ((∑ k,(l k)^2=theta n) ↔ l=centralSpectrum n) := by
  constructor
  · have hb := concentration_transfer hN (theta n) (le_of_lt (theta_pos n hn)) l ho hl
      (fun j hj => (concentrated_bounds n hn hN l hU hphys j hj).2.1)
    simpa [hs] using hb
  · constructor
    · exact equality_vector n hn hN l ho hl hs hU hphys
    · intro he
      rw [he]
      exact central_purity n hn

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowConcentration
