/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1Physical
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual five-row APPT P1 extraction and unequal-mass concentration lift. -/

/-
The physical input is one ordered nonnegative spectrum with literal APPT of
its labelled diagonal. Its head and tail defects produce the complete P1 Hyp;
neither a scalar certificate nor the desired purity bound is an input.
The positive-u normalization retains the original scale, and zero u is
disposed of before division. Concentration keeps the boundary pools fixed
and transports the bound through the existing norm cone with unequal masses.

proof_shape: top_three_moment: content (the unrestricted top-three estimate).
  pool_hyp, actual_to_hyp, physical_upper: content after inlining that live
  estimate. Locally, normalization and scalar/concentration application are
  bind-only steps; those steps provide no separate escape witness.
The tail moment estimate is consumed through Hyp.tail by scalar_bound, then
by FiveRowMaximumPurity.result on the original small-n upper-bound path.
utility:none: the new estimate and physical transfer are symbolic inequalities
over arbitrary real spectra. The exact finite checks belong to FiveRowP1.
-/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
import Mathlib.Data.Fin.Rev
set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
open UniformSchmidtIncidence UniformSchmidtBell QutritPerturbationAttainment
open FiveRowP2Lift FiveRowP1Algebra
open UniformSpectralBound.SharedSpectral
noncomputable section

private def localEdgeAt : Fin 10 → Edge 5 :=
  ![⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
    ⟨(0,4),by decide⟩,⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,
    ⟨(1,4),by decide⟩,⟨(2,3),by decide⟩,⟨(2,4),by decide⟩,
    ⟨(3,4),by decide⟩]

private def localEdgeEquiv : Fin 10 ≃ Edge 5 :=
  Equiv.ofBijective localEdgeAt (by decide)

private def localEdgeSlots : Edge 5 ≃ Fin 10 := localEdgeEquiv.symm

private def localTailSlots : BottomSlot 5 ≃ Fin 15 :=
  (Equiv.sumCongr (Equiv.refl (Fin 5)) localEdgeSlots).trans finSumFinEquiv

private theorem localFamilyQuadratic (u v : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (π : Edge 5 ≃ Fin 10) (σ : BottomSlot 5 ≃ Fin 15) (x : Fin 5 → ℝ) :
    x ⬝ᵥ (FiveRowP2Star.family u v h d π σ)*ᵥ x =
      (∑ i : Fin 5, 2*(u-d (σ (.inl i)))*(x i)^2) -
      ∑ e : Edge 5, 2*(v+h (π e)+d (σ (.inr e)))*x e.val.1*x e.val.2 := by
  simp only [FiveRowP2Star.family, K,dotProduct,mulVec]
  simp_rw [← localEdgeEquiv.sum_comp]
  norm_num [Fin.sum_univ_succ,localEdgeEquiv,localEdgeAt,edge]
  <;> ring

private theorem localFamilyUniformSubsets (r : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hf : FiveRowP2Star.FullPSD 1 r h d) :
    h 0 + (d 14+d 13+d 12) ≤ 2-r ∧
    (h 0+h 1+h 2) + (d 14+d 13+d 12+d 11+d 10+d 9) ≤ 3-3*r ∧
    (h 0+h 1+h 2+h 3+h 4+h 5) +
      (d 14+d 13+d 12+d 11+d 10+d 9+d 8+d 7+d 6+d 5) ≤ 4-6*r := by
  let hp2 : Equiv.Perm (Fin 10) := Equiv.refl _
  let hp3 : Equiv.Perm (Fin 10) :=
    Equiv.ofBijective ![0,1,3,4,2,5,6,7,8,9] (by decide)
  let hp4 : Equiv.Perm (Fin 10) :=
    Equiv.ofBijective ![0,1,2,6,3,4,7,5,8,9] (by decide)
  let tp2 : Equiv.Perm (Fin 15) :=
    Equiv.ofBijective ![14,13,0,1,2,12,3,4,5,6,7,8,9,10,11] (by decide)
  let tp3 : Equiv.Perm (Fin 15) :=
    Equiv.ofBijective ![14,13,12,0,1,11,10,2,3,9,4,5,6,7,8] (by decide)
  let tp4 : Equiv.Perm (Fin 15) :=
    Equiv.ofBijective ![14,13,12,11,0,10,9,8,1,7,6,2,5,3,4] (by decide)
  have h2 := (hf (localEdgeSlots.trans hp2) (localTailSlots.trans tp2)).dotProduct_mulVec_nonneg
    ![1,1,0,0,0]
  have h3 := (hf (localEdgeSlots.trans hp3) (localTailSlots.trans tp3)).dotProduct_mulVec_nonneg
    ![1,1,1,0,0]
  have h4 := (hf (localEdgeSlots.trans hp4) (localTailSlots.trans tp4)).dotProduct_mulVec_nonneg
    ![1,1,1,1,0]
  simp only [star_trivial] at h2 h3 h4
  rw [localFamilyQuadratic,← localEdgeEquiv.sum_comp] at h2 h3 h4
  simp only [Equiv.trans_apply,localTailSlots,localEdgeSlots,
    Equiv.symm_apply_apply,Equiv.sumCongr_apply,Equiv.refl_apply,Sum.map_inl,Sum.map_inr,
    finSumFinEquiv_apply_left (m:=5) (n:=10),
      finSumFinEquiv_apply_right (m:=5) (n:=10)] at h2 h3 h4
  norm_num [Fin.sum_univ_succ,localEdgeEquiv,localEdgeAt,
    hp2,hp3,hp4,tp2,tp3,tp4,
    finSumFinEquiv_apply_left (m:=5) (n:=10),
    finSumFinEquiv_apply_right (m:=5) (n:=10)] at h2 h3 h4
  exact ⟨by linarith only [h2], by linarith only [h3], by linarith only [h4]⟩

/-- A top-three moment bound for a finite ordered nonnegative list. It is
independent of the unit box and includes c=0 and zero total mass. -/
private theorem top_three_moment (d : Fin 15 → ℝ) (c : ℝ)
    (hd : ∀ i, 0 ≤ d i) (ho : Monotone d)
    (hc : d 14+d 13+d 12 ≤ c) :
    (∑ i, (d i)^2) ≤ max (c^2) (c*(∑ i,d i)/3) := by
  let A := d 14
  let B := d 13
  let t := d 12
  let D := ∑ i, d i
  let E := max (c^2) (c*D/3)
  change A+B+t ≤ c at hc
  have ht : 0 ≤ t := hd 12
  have hA : t ≤ A := ho (by decide)
  have hB : t ≤ B := ho (by decide)
  have ht' : t ≤ c/3 := by linarith only [hc,hA,hB]
  have hpoint (i : Fin 15) : (d i)^2 ≤ t*d i +
      (if i=14 then A^2-t*A else 0) + (if i=13 then B^2-t*B else 0) := by
    by_cases hi : i=14
    · subst i; simp only [if_pos rfl,if_neg (by decide : (14:Fin 15) ≠ 13)]
      dsimp [A]; nlinarith only []
    · by_cases hj : i=13
      · subst i; simp only [if_pos rfl,if_neg (by decide : (13:Fin 15) ≠ 14)]
        dsimp [B]; nlinarith only []
      · have hic : d i ≤ t := ho (by change i.val ≤ 12; omega)
        simp only [if_neg hi,if_neg hj]
        nlinarith only [mul_nonneg (hd i) (sub_nonneg.mpr hic)]
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 15))) => hpoint i)
  simp only [sum_add_distrib,← mul_sum,sum_ite_eq',mem_univ,if_true] at hsum
  have hab : A^2+B^2 ≤ (A+B)^2-2*t*(A+B)+2*t^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hinc := mul_nonneg (show 0 ≤ c-t-(A+B) by linarith only [hc])
    (show 0 ≤ c+(A+B)-4*t by linarith only [hc,hA,hB,ht])
  have hp : (∑ i,(d i)^2) ≤ c^2+(D-5*c)*t+6*t^2 := by
    dsimp only [D] at *
    nlinarith only [hsum,hab,hinc]
  have he0 : c^2 ≤ E := le_max_left _ _
  have he1 : c*D/3 ≤ E := le_max_right _ _
  have hend := D5.S0.Certificates.BoxCover.QuadraticCorner.quadratic_upper
    (c^2) (D-5*c) 6 0 (c/3) t E ht ht'
    (by simpa using he0) (by nlinarith only [he1])
  norm_num only [max_eq_right (by norm_num : (-6:ℝ) ≤ 0),
    zero_mul,zero_div,add_zero] at hend
  exact hp.trans hend

/-- Head maximum and tail prefix consequences, all on one labelled family.
The variance field is supplied by the actual-spectrum literal variance theorem
at the caller; no target energy inequality is assumed here. -/
private theorem pool_hyp (r : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hr : 0 ≤ r) (hh : ∀ i, 0 ≤ h i) (hd : ∀ i, 0 ≤ d i)
    (hdu : ∀ i, d i ≤ 1) (hho : Antitone h) (hdo : Monotone d)
    (hhz : h 9=0) (hdz : d 0=0)
    (hf : FiveRowP2Star.FullPSD 1 r h d)
    (hvar : (2/3)*((∑ i,(h i)^2)-(∑ i,h i)^2/10)+
      ((∑ i,(d i)^2)-(∑ i,d i)^2/15) ≤
      4*(5-10*r-(∑ i,h i)-(∑ i,d i))-
        (2/5)*(5-10*r-(∑ i,h i)-(∑ i,d i))^2) :
    Hyp r (∑ i,h i) (∑ i,d i) (∑ i,(d i)^2) (∑ i,(h i)^2) := by
  let H := ∑ i,h i
  let D := ∑ i,d i
  let a := ∑ i,(h i)^2
  let q := ∑ i,(d i)^2
  let M := h 0
  let T := d 14+d 13+d 12
  let F := d 14+d 13+d 12+d 11+d 10
  have hH : 0 ≤ H := sum_nonneg (fun i _ => hh i)
  have hD : 0 ≤ D := sum_nonneg (fun i _ => hd i)
  have ha : 0 ≤ a := sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ q := sum_nonneg (fun i _ => sq_nonneg _)
  have hM : 0 ≤ M := hh 0
  have hbudget : H+D ≤ 5-10*r := by
    simpa only [H, D, mul_one] using
      (FiveRowP2Star.family_mass_budget 1 r h d hf)
  have hD5 : D ≤ 5 := by linarith only [hbudget,hH,hr]
  have hrhalf : r ≤ 1/2 := by linarith only [hbudget,hH,hD]
  have hamin := FiveRowP2Physical.zero_slot_cauchy h 9 hhz
  have hqmin := FiveRowP2Physical.zero_slot_cauchy d 0 hdz
  have hamax := sum_sq_le_sq_sum_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin 10))) => hh i)
  have hqsq := sum_sq_le_sq_sum_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin 15))) => hd i)
  have hqD : q ≤ D := by
    apply sum_le_sum
    intro i _
    nlinarith only [mul_nonneg (hd i) (sub_nonneg.mpr (hdu i))]
  have hamaxM : a ≤ H*M := by
    have hp (i : Fin 10) : (h i)^2 ≤ h i*M := by
      have hi : h i ≤ M := hho (Fin.zero_le i)
      nlinarith only [mul_nonneg (hh i) (sub_nonneg.mpr hi)]
    simpa only [a,H,sum_mul] using sum_le_sum
      (fun i (_ : i ∈ (univ : Finset (Fin 10))) => hp i)
  have hsub := localFamilyUniformSubsets r h d hf
  have htop : M+T ≤ 2-r := hsub.1
  have hqF : q ≤ F := by
    let dr : Fin 15 → ℝ := fun i => d (Fin.rev i)
    have hor : Antitone dr := by
      intro i j hij
      apply hdo
      change (Fin.rev j).val ≤ (Fin.rev i).val
      dsimp only [Fin.rev]
      omega
    have hmass : ∑ i,dr i ≤ 5 := by
      change (∑ i, d (Fin.rev i)) ≤ 5
      have hrev' : (∑ i : Fin 15, d (Fin.rev i)) = ∑ i : Fin 15, d i := by
        simpa only [Fin.revPerm_apply] using
          (Equiv.sum_comp (Fin.revPerm : Fin 15 ≃ Fin 15) d)
      have hD5' := hD5
      change (∑ i : Fin 15, d i) ≤ 5 at hD5'
      calc
        (∑ i, d (Fin.rev i)) = ∑ i, d i := hrev'
        _ ≤ 5 := hD5'
    have hc := FiveRowP2Star.capped_tail_squares 1 dr (by norm_num)
      (fun i => hd _) (fun i => hdu _) hor (by simpa using hmass)
    have hsq : (∑ i,(dr i)^2)=q := by
      change (∑ i, (d (Fin.rev i))^2) = q
      have hrev' : (∑ i : Fin 15, (d (Fin.rev i))^2) = ∑ i : Fin 15, (d i)^2 := by
        simpa only [Fin.revPerm_apply] using
          (Equiv.sum_comp (Fin.revPerm : Fin 15 ≃ Fin 15) (fun i => (d i)^2))
      simpa only [q] using hrev'
    rw [hsq] at hc
    simpa [dr,F,Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hc
  have hq3 : q ≤ 3-3*r := by
    dsimp only [M,T,F] at *
    linarith only [hsub.2.1,hqF,hM,hh 1,hh 2,hd 9]
  have hq4 : q ≤ 4-6*r := by
    dsimp only [M,T,F] at *
    linarith only [hsub.2.2,hqF,hM,hh 1,hh 2,hh 3,hh 4,hh 5,
      hd 9,hd 8,hd 7,hd 6,hd 5]
  have hsubset3 : a ≤ H*(3-3*r-q) := by
    have hMbound : M ≤ 3-3*r-q := by
      dsimp only [M,F] at *
      linarith only [hsub.2.1,hqF,hh 1,hh 2,hd 9]
    exact hamaxM.trans (mul_le_mul_of_nonneg_left hMbound hH)
  have hsubset4 : a ≤ H*(4-6*r-q) := by
    have hMbound : M ≤ 4-6*r-q := by
      dsimp only [M,F] at *
      linarith only [hsub.2.2,hqF,hh 1,hh 2,hh 3,hh 4,hh 5,
        hd 9,hd 8,hd 7,hd 6,hd 5]
    exact hamaxM.trans (mul_le_mul_of_nonneg_left hMbound hH)
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    linarith only [hd 14, hd 13, hd 12]
  have htT : 3*d 12 ≤ T := by
    dsimp [T]
    linarith only [hdo (by decide : (12:Fin 15) ≤ 14),
      hdo (by decide : (12:Fin 15) ≤ 13)]
  have hDT : 3*D ≤ 14*T := by
    have hpoint (i : Fin 15) : d i ≤
        (if i=14 then d 14 else if i=13 then d 13 else if i=0 then 0 else d 12) := by
      by_cases hi : i=14
      · subst i; simp
      · by_cases hj : i=13
        · subst i; simp
        · by_cases hz : i=0
          · subst i; simp [hdz]
          · simp only [if_neg hi,if_neg hj,if_neg hz]
            exact hdo (by change i.val ≤ 12; omega)
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 15))) => hpoint i)
    norm_num [Fin.sum_univ_succ] at hs
    dsimp only [D,T] at *
    have hDexp := hD
    norm_num [Fin.sum_univ_succ] at hDexp ⊢
    have h13 : d 12 ≤ d 13 := hdo (by decide)
    have h14 : d 12 ≤ d 14 := hdo (by decide)
    nlinarith only [hs,htT,hdz,h13,h14,hDexp]
  have hqT : 3*q ≤ 5*T := by
    have h11 : d 11 ≤ d 12 := hdo (by decide)
    have h10 : d 10 ≤ d 12 := hdo (by decide)
    dsimp only [F] at hqF
    dsimp only [T] at *
    linarith only [hqF,h11,h10,htT]
  have htopD : a ≤ H*(2-r-3*D/14) :=
    hamaxM.trans (mul_le_mul_of_nonneg_left (by linarith only [htop,hDT]) hH)
  have htopQ : a ≤ H*(2-r-3*q/5) :=
    hamaxM.trans (mul_le_mul_of_nonneg_left (by linarith only [htop,hqT]) hH)
  have htopQ0 : 0 ≤ 2-r-3*q/5 := by linarith only [htop,hqT,hM]
  have hbox : q ≤ max 2 (2*D/3) := by
    have hp := FiveRowP2Physical.top_three_psd 1 r h d hr hh hd hf
    have hc := FiveRowP2Physical.monotone_tail_square_cap d (max 3 D)
      (le_max_left _ _) hd hdu hdo (le_max_right _ _) hp
    change q ≤ 2*max 3 D/3 at hc
    rcases le_total D 3 with h | h
    · rw [max_eq_left h] at hc
      have hc' : q ≤ (2:ℝ) := by convert hc using 1 <;> norm_num
      exact hc'.trans (le_max_left _ _)
    · rw [max_eq_right h] at hc
      exact hc.trans (le_max_right _ _)
  have hstar := FiveRowP2Star.family_star_charges 1 r h d (by norm_num)
    hr hh hd hdu (by simpa using hD5) hf
  have hroot : (∑ i,(r+h i)^2)=a+2*r*H+10*r^2 := by
    simp_rw [add_sq]
    simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,H,a]
    ring
  rw [hroot] at hstar
  have hF0 : 0 ≤ a+2*r*H+10*r^2 := by positivity
  have hstarQ : a ≤ (2-q/2)^2-2*r*H-10*r^2 := by
    have hh : Real.sqrt (a+2*r*H+10*r^2) ≤ 2-q/2 := by
      simpa only [one_mul,mul_one] using (le_sub_iff_add_le.mpr hstar.1)
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hh)).mpr hh
    rw [Real.sq_sqrt hF0] at hs
    linarith only [hs]
  have hstarD : a ≤ (2-D/5)^2-2*r*H-10*r^2 := by
    have hh : Real.sqrt (a+2*r*H+10*r^2) ≤ 2-D/5 := by
      simpa only [mul_one] using (le_sub_iff_add_le.mpr hstar.2)
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hh)).mpr hh
    rw [Real.sq_sqrt hF0] at hs
    linarith only [hs]
  have hcT : T ≤ charge r H a := by
    by_cases hz : H=0
    · simp only [charge,if_pos hz]
      linarith only [htop,hM]
    · have hHp : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
      have haH : a/H ≤ M := (div_le_iff₀ hHp).mpr (by simpa [mul_comm] using hamaxM)
      simp only [charge,if_neg hz]
      linarith only [htop,haH]
  have hc0 : 0 ≤ charge r H a := hT0.trans hcT
  have htail := top_three_moment d (charge r H a) hd hdo hcT
  have hdisj : q ≤ (charge r H a)^2 ∨ 3*q ≤ charge r H a*D := by
    rcases le_max_iff.mp htail with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith only [h])
  refine {
    r0 := hr, H0 := hH, D0 := hD, q0 := hq, a0 := ha,
    rhalf := hrhalf, budget := hbudget,
    amin := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 9)).2
      simpa [mul_comm] using hamin,
    amax := hamax,
    qmin := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 14)).2
      simpa [mul_comm] using hqmin,
    qD := hqD, qsq := hqsq, starQ := hstarQ, starD := hstarD,
    variance := hvar, topD := htopD, topQ := htopQ,
    subset3 := hsubset3, subset4 := hsubset4,
    q3 := hq3, q4 := hq4, topQ0 := htopQ0,
    boxTail := hbox, charge0 := hc0, tail := hdisj }

/-- The complete P1 Hyp of ONE actual spectrum, with only the physical
hypotheses and positive normalization scale. Zero scale is handled separately
by homogeneous_zero_actual, before this theorem is used. -/
theorem actual_to_hyp (n : ℕ) (hn : 5 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i, 0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (hu : 0 < FiveRowP2Physical.u (by omega : 25 ≤ 5*n) l) :
    Hyp
      (FiveRowP2Physical.v (by omega) l / FiveRowP2Physical.u (by omega) l)
      (FiveRowP2Physical.H (by omega) l / FiveRowP2Physical.u (by omega) l)
      (FiveRowP2Physical.D (by omega) l / FiveRowP2Physical.u (by omega) l)
      (FiveRowP2Physical.tailEnergy (by omega) l / (FiveRowP2Physical.u (by omega) l)^2)
      (FiveRowP2Physical.headEnergy (by omega) l / (FiveRowP2Physical.u (by omega) l)^2) := by
  let hN : 25 ≤ 5*n := by omega
  let U := FiveRowP2Physical.u hN l
  let V := FiveRowP2Physical.v hN l
  let HH := FiveRowP2Physical.H hN l
  let DD := FiveRowP2Physical.D hN l
  let A := FiveRowP2Physical.headEnergy hN l
  let Q := FiveRowP2Physical.tailEnergy hN l
  let r := V/U
  let hh : Fin 10 → ℝ := fun i => FiveRowP2Physical.heads hN l i/U
  let dd : Fin 15 → ℝ := fun i => FiveRowP2Physical.tails hN l i/U
  have hU : U ≠ 0 := ne_of_gt hu
  have hU2 : 0 < U^2 := sq_pos_of_pos hu
  have hs := FiveRowP2Physical.actual_pool_signs hN l hl h0
  have hf := FiveRowP2Physical.literal_defect_family n hn e l h
  change FiveRowP2Star.FullPSD U V (FiveRowP2Physical.heads hN l)
    (FiveRowP2Physical.tails hN l) at hf
  have hfn : FiveRowP2Star.FullPSD 1 r hh dd := by
    intro π σ
    have hscale : FiveRowP2Star.family 1 r hh dd π σ =
        (U⁻¹ : ℝ) • FiveRowP2Star.family U V
          (FiveRowP2Physical.heads hN l) (FiveRowP2Physical.tails hN l) π σ := by
      ext i j
      by_cases hij : i = j
      · simp only [FiveRowP2Star.family, K, dif_pos hij,
          Matrix.smul_apply, smul_eq_mul]
        dsimp only [dd]
        field_simp [hU] <;> ring
      · simp only [FiveRowP2Star.family, K, dif_neg hij,
          Matrix.smul_apply, smul_eq_mul]
        dsimp only [r, hh, dd]
        field_simp [hU] <;> ring
    rw [hscale]
    exact (hf π σ).smul (inv_nonneg.mpr hu.le)
  have hr : 0 ≤ r := div_nonneg hs.2.1 hu.le
  have hhh (i : Fin 10) : 0 ≤ hh i := div_nonneg (hs.2.2.1 i) hu.le
  have hdd (i : Fin 15) : 0 ≤ dd i := div_nonneg (hs.2.2.2.1 i).1 hu.le
  have hdu (i : Fin 15) : dd i ≤ 1 := (div_le_one hu).mpr (hs.2.2.2.1 i).2
  have hho : Antitone hh := by
    intro i j hij
    apply (div_le_div_iff_of_pos_right hu).mpr
    have hhij := hl (show (⟨i.val,by omega⟩ : Fin (5*n)) ≤ ⟨j.val,by omega⟩ from hij)
    dsimp [FiveRowP2Physical.heads]
    linarith only [hhij]
  have hdo : Monotone dd := by
    intro i j hij
    apply (div_le_div_iff_of_pos_right hu).mpr
    have hhij := hl (show (⟨5*n-15+i.val,by omega⟩ : Fin (5*n)) ≤
      ⟨5*n-15+j.val,by omega⟩ by exact Nat.add_le_add_left hij _)
    dsimp [FiveRowP2Physical.tails]
    linarith only [hhij]
  have hhz : hh 9=0 := by simp [hh,hs.2.2.2.2.1]
  have hdz : dd 0=0 := by simp [dd,hs.2.2.2.2.2]
  have hH : (∑ i,hh i)=HH/U := by simp only [hh,← sum_div,HH,FiveRowP2Physical.H]
  have hD : (∑ i,dd i)=DD/U := by simp only [dd,← sum_div,DD,FiveRowP2Physical.D]
  have hA : (∑ i,(hh i)^2)=A/U^2 := by
    simp only [hh,div_pow,← sum_div,A,FiveRowP2Physical.headEnergy]
  have hQ : (∑ i,(dd i)^2)=Q/U^2 := by
    simp only [dd,div_pow,← sum_div,Q,FiveRowP2Physical.tailEnergy]
  have hvar := FiveRowP2Physical.actual_variance n hn e l hl h
  dsimp only at hvar
  change (2/3)*(A-HH^2/10)+(Q-DD^2/15) ≤
    4*U*(5*U-10*V-HH-DD)-(2/5)*(5*U-10*V-HH-DD)^2 at hvar
  have hvarn : (2/3)*((∑ i,(hh i)^2)-(∑ i,hh i)^2/10)+
      ((∑ i,(dd i)^2)-(∑ i,dd i)^2/15) ≤
      4*(5-10*r-(∑ i,hh i)-(∑ i,dd i))-
        (2/5)*(5-10*r-(∑ i,hh i)-(∑ i,dd i))^2 := by
    rw [hH,hD,hA,hQ]
    apply (mul_le_mul_iff_of_pos_right hU2).mp
    convert hvar using 1 <;> (try dsimp [r]) <;> field_simp [hU] <;> ring_nf
  have hout := pool_hyp r hh dd hr hhh hdd hdu hho hdo hhz hdz hfn hvarn
  rw [hH,hD,hA,hQ] at hout
  exact hout

/-- Unconditioned physical P1 upper branch, in the original ordered spectrum
and arbitrary mass. The coefficient uses casts of the natural product 5*n;
there is no natural-number division in the displayed bound. -/
theorem physical_upper (n : ℕ) (hn : 5 ≤ n) (hn' : n ≤ 18)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i, 0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    (∑ i, (l i)^2) ≤
      ((((5*n : ℕ) : ℝ)+8)/((((5*n : ℕ) : ℝ)+2)^2))*(∑ i,l i)^2 := by
  let hN : 25 ≤ 5*n := by omega
  let U := FiveRowP2Physical.u hN l
  by_cases hz : U=0
  · have hlz := FiveRowP2Physical.homogeneous_zero_actual n hn e l hl h0 h hz
    rw [hlz]
    simp
  have hu0 : 0 ≤ U := (FiveRowP2Physical.actual_pool_signs hN l hl h0).1
  have hu : 0 < U := lt_of_le_of_ne hu0 (Ne.symm hz)
  have hU0 : FiveRowP2Physical.u hN l ≠ 0 := ne_of_gt hu
  let r := FiveRowP2Physical.v hN l/U
  let HH := FiveRowP2Physical.H hN l/U
  let DD := FiveRowP2Physical.D hN l/U
  let aa := FiveRowP2Physical.headEnergy hN l/U^2
  let qq := FiveRowP2Physical.tailEnergy hN l/U^2
  have hHyp : Hyp r HH DD qq aa := actual_to_hyp n hn e l hl h0 h hu
  let θ : ℝ := (((5*n : ℕ) : ℝ)+8)/((((5*n : ℕ) : ℝ)+2)^2)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  apply concentration_transfer hN θ hθ l hl h0
  · intro j hj
    exact sum_nonneg (fun i _ => concentrated_nonnegative l hl h0 j i)
  · intro j hj
    have hjv : 9 ≤ j.val ∧ j.val < 5*n-15 := by
      simpa only [middle, mem_filter, mem_univ, true_and] using hj
    have hleft : (10:ℝ) ≤ ((j.val+1:ℕ):ℝ) := by
      exact_mod_cast (show 10 ≤ j.val+1 by omega)
    have hright : ((j.val+1:ℕ):ℝ) ≤ ((5*n:ℕ):ℝ)-15 := by
      have hnat : j.val+1+15 ≤ 5*n := by omega
      have hr' : ((j.val+1:ℕ):ℝ)+15 ≤ ((5*n:ℕ):ℝ) := by exact_mod_cast hnat
      linarith only [hr']
    have hb := FiveRowP1.scalar_bound n hn hn' ((j.val+1:ℕ):ℝ)
      r HH DD qq aa hleft hright hHyp
    have hscalar : energy ((5*n:ℕ):ℝ) ((j.val+1:ℕ):ℝ) r HH DD qq aa ≤
        θ*(mass ((5*n:ℕ):ℝ) ((j.val+1:ℕ):ℝ) r HH DD)^2 := by
      simpa only [energy,mass,θ] using hb
    have hm := FiveRowP2Physical.concentrated_raw_moments hN l j hj
    have hmass : (∑ i,concentrated (spectralGap l) j i) =
        U*mass ((5*n:ℕ):ℝ) ((j.val+1:ℕ):ℝ) r HH DD := by
      rw [hm.1]
      dsimp [mass,r,HH,DD,U]
      push_cast
      field_simp [hU0] <;> ring_nf
    have henergy : (∑ i,(concentrated (spectralGap l) j i)^2) =
        U^2*energy ((5*n:ℕ):ℝ) ((j.val+1:ℕ):ℝ) r HH DD qq aa := by
      rw [hm.2]
      dsimp [energy,r,HH,DD,aa,qq,U]
      push_cast
      field_simp [hU0] <;> ring_nf
    rw [hmass,henergy]
    have hp := mul_le_mul_of_nonneg_left hscalar (sq_nonneg U)
    nlinarith only [hp]
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Physical
