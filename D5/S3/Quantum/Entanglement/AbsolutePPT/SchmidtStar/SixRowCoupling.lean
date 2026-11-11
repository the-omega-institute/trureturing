/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowCoupling
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Literal independently labelled K6 matrices couple the same head vector to all twenty-one tail deficits. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowTail
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Matrix Finset
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowCoupling
open UniformSchmidtIncidence UniformSchmidtSpectrum UniformSchmidtBell
open QutritPerturbationAttainment (APPT)
open SixRowTail
noncomputable section

/-- The unnormalized PSD test z=(1,p), with the actual K entries. -/
theorem quadratic_identity (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ)
    (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21)
    (hn : ∑ i, (p i)^2=1) :
    (Fin.cases 1 p : Fin 6 → ℝ) ⬝ᵥ
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))) *ᵥ
        (Fin.cases 1 p : Fin 6 → ℝ) =
      2*U*(2-SixRowHead.headValue (fun i => r+h i) p π-tailCharge d p σ) := by
  have hid : (Fin.cases 1 p : Fin 6 → ℝ) ⬝ᵥ
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))) *ᵥ
        (Fin.cases 1 p : Fin 6 → ℝ) =
      2*U*((∑ i : Fin 6, (Fin.cases 1 p i)^2)-
        SixRowHead.headValue (fun i => r+h i) p π-tailCharge d p σ) := by
    have hv : (Fin.cases 1 p : Fin 6 → ℝ) = ![1, p 0, p 1, p 2, p 3, p 4] := by
      funext i
      fin_cases i <;> rfl
    simp only [K,SixRowHead.headValue,tailCharge,coefficient,dotProduct,mulVec,
      Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hv]
    simp_rw [← SixRowHead.edgeEquiv.sum_comp]
    norm_num [Fin.sum_univ_succ,SixRowHead.edgeEquiv,SixRowHead.edgeAt,edge]
    <;> ring
  have hnorm : (∑ i : Fin 6, (Fin.cases (1 : ℝ) p i)^2)=(2 : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,one_pow]
    rw [hn]
    norm_num
  rwa [hnorm] at hid

/-- The K-family premise is a generic matrix supplier, discharged below by
literal_assignment_psd. Neither scalar conclusion is assumed. -/
theorem family_coupled (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ)
    (hU : 0 < U) (hr : 0 ≤ r) (hh : ∀ i, 0 ≤ h i)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (hdo : Monotone d) (hm : ∑ i, d i ≤ 6)
    (hf : ∀ (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21),
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))).PosSemidef) :
    Real.sqrt (∑ i, (r+h i)^2)+(∑ i, (d i)^2)/2 ≤ 2 ∧
      (∑ i, (h i)^2)+2*r*(∑ i, h i)+15*r^2 ≤ (2-(∑ i, (d i)^2)/2)^2 := by
  obtain ⟨p,π,hp,hpn,hhead⟩ := SixRowHead.head_exists (fun i => r+h i)
    (fun i => add_nonneg hr (hh i))
  obtain ⟨σ,htail⟩ := tail_exists d p hd0 hd1 hdo hm hp hpn
  have hpos := (hf π σ).dotProduct_mulVec_nonneg (Fin.cases 1 p)
  simp only [star_trivial] at hpos
  rw [quadratic_identity U r h d p π σ hpn] at hpos
  have hcharge : SixRowHead.headValue (fun i => r+h i) p π+tailCharge d p σ ≤ 2 := by
    have ht : 0 ≤ 2-SixRowHead.headValue (fun i => r+h i) p π-tailCharge d p σ :=
      (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < 2*U)).mp hpos
    linarith only [ht]
  have hbound : Real.sqrt (∑ i, (r+h i)^2)+(∑ i, (d i)^2)/2 ≤ 2 := by
    linarith only [hcharge,hhead,htail]
  refine ⟨hbound,?_⟩
  have hroot0 : 0 ≤ Real.sqrt (∑ i, (r+h i)^2) := Real.sqrt_nonneg _
  have hb : 0 ≤ 2-(∑ i, (d i)^2)/2 := by linarith only [hbound,hroot0]
  have hs : (Real.sqrt (∑ i, (r+h i)^2))^2 ≤ (2-(∑ i, (d i)^2)/2)^2 :=
    (sq_le_sq₀ hroot0 hb).mpr (by linarith only [hbound])
  rw [Real.sq_sqrt (sum_nonneg (fun i _ => sq_nonneg _))] at hs
  have he : (∑ i : Fin 15, (r+h i)^2)=
      (∑ i, (h i)^2)+2*r*(∑ i, h i)+15*r^2 := by
    simp_rw [add_sq]
    simp [sum_add_distrib,← mul_sum]
    <;> ring
  rwa [he] at hs

/-- Exact finite pool transport. The two equalities identify every literal
top/bottom entry; the independent permutations are never synchronized. -/
private theorem literal_family_psd (n : ℕ) (hn : 6 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ))))
    (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ)
    (htop : ∀ i : Fin 15, U*(1+r+h i)=l ⟨i.val,by omega⟩)
    (hbot : ∀ j : Fin 21, U*(1-d j)=l ⟨6*n-21+j.val,by omega⟩) :
    ∀ (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21),
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))).PosSemidef := by
  have ha : a 6=15 := by
    have hc := edge_card_real 6
    norm_num at hc
    exact_mod_cast hc
  have hb : b 6=21 := by
    have hc := bottom_card_real 6
    norm_num at hc
    exact_mod_cast hc
  let hpool : a 6+b 6 ≤ 6*n :=
    (pool_card_sum 6).trans_le (Nat.mul_le_mul (by rfl) hn)
  intro π σ
  let π' : Equiv.Perm (Fin (a 6)) :=
    (Fintype.equivFin (Edge 6)).symm.trans (π.trans (finCongr ha).symm)
  let σ' : Equiv.Perm (Fin (b 6)) :=
    (Fintype.equivFin (BottomSlot 6)).symm.trans (σ.trans (finCongr hb).symm)
  have hpsd := literal_assignment_psd (by rfl : 6 ≤ 6) hn e l happt π' σ'
  dsimp only at hpsd
  have hti (E : Edge 6) : assignedTopIndex hpool π' E=⟨(π E).val,by omega⟩ := by
    apply Fin.ext
    simp [assignedTopIndex,topIndex,π',Equiv.trans_apply]
  have hbi (B : BottomSlot 6) :
      assignedBottomIndex hpool σ' B=⟨6*n-21+(σ B).val,by omega⟩ := by
    apply Fin.ext
    simp [assignedBottomIndex,bottomIndex,σ',Equiv.trans_apply]
    change 6*n - b 6 = 6*n - 21
    rw [hb]
  have hid : K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))=
      assignedK hpool l π' σ' := by
    unfold assignedK
    congr 1 <;> funext z
    · rw [hti]
      exact htop (π z)
    · rw [hbi]
      exact hbot (σ z)
  rwa [hid]

/-- Uniform charge gives the actual normalized mass bound, before selecting p. -/
private theorem family_mass (U r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ)
    (hU : 0 < U) (hr : 0 ≤ r) (hh : ∀ i, 0 ≤ h i)
    (hf : ∀ (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21),
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))).PosSemidef) :
    ∑ i, d i ≤ 6 := by
  have hb : b 6=21 := by
    have hc := bottom_card_real 6
    norm_num at hc
    exact_mod_cast hc
  let π : Edge 6 ≃ Fin 15 := SixRowHead.edgeEquiv.symm
  let σ : BottomSlot 6 ≃ Fin 21 := (Fintype.equivFin _).trans (finCongr hb)
  have hpos := (hf π σ).dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have hcharge : 0 ≤ UniformSchmidtDefectMoment.uniformCharge
      (K (fun E => U*(1+r+h (π E))) (fun B => U*(1-d (σ B)))) := by
    simpa [UniformSchmidtDefectMoment.uniformCharge,UniformSchmidtDefectMoment.rowSum,
      dotProduct,mulVec] using hpos
  rw [K_charge,σ.sum_comp (fun i => U*(1-d i)),
    π.sum_comp (fun i => U*(1+r+h i))] at hcharge
  have he : 2*((∑ i : Fin 21, U*(1-d i))-(∑ i : Fin 15, U*(1+r+h i)))=
      2*U*(6-15*r-(∑ i, h i)-(∑ i, d i)) := by
    simp only [← mul_sum,sum_sub_distrib,sum_add_distrib,sum_const,
      card_univ,Fintype.card_fin,nsmul_eq_mul]
    <;> ring
  rw [he] at hcharge
  have hs : 0 ≤ 6-15*r-(∑ i, h i)-(∑ i, d i) :=
    (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < 2*U)).mp hcharge
  have hH : 0 ≤ ∑ i, h i := sum_nonneg (fun i _ => hh i)
  linarith only [hs,hH,hr]

/-- Literal APPT consumer for the ACTUAL first 15 and last 21 entries.
Only positivity of the scale is left to the existing physical head supplier;
the normalized deficit mass bound is derived from literal K_charge here. -/
theorem literal_coupled (n : ℕ) (hn : 23 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i, 0 ≤ l i)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ))))
    (hU : 0 < l ⟨6*n-21,by omega⟩) :
    let U := l ⟨6*n-21,by omega⟩
    let b := l ⟨14,by omega⟩
    let r := (b-U)/U
    let h : Fin 15 → ℝ := fun i => (l ⟨i.val,by omega⟩-b)/U
    let d : Fin 21 → ℝ := fun j => (U-l ⟨6*n-21+j.val,by omega⟩)/U
    Real.sqrt (∑ i, (r+h i)^2)+(∑ j, (d j)^2)/2 ≤ 2 ∧
      (∑ i, (h i)^2)+2*r*(∑ i, h i)+15*r^2 ≤ (2-(∑ j, (d j)^2)/2)^2 := by
  dsimp only
  let U := l ⟨6*n-21,by omega⟩
  let b := l ⟨14,by omega⟩
  let r := (b-U)/U
  let h : Fin 15 → ℝ := fun i => (l ⟨i.val,by omega⟩-b)/U
  let d : Fin 21 → ℝ := fun j => (U-l ⟨6*n-21+j.val,by omega⟩)/U
  have hu : 0 < U := hU
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr (hl (by change 14 ≤ 6*n-21; omega))) hu.le
  have hh (i : Fin 15) : 0 ≤ h i := by
    apply div_nonneg _ hu.le
    exact sub_nonneg.mpr (hl (by change i.val ≤ 14; omega))
  have hd0 (j : Fin 21) : 0 ≤ d j := by
    apply div_nonneg _ hu.le
    exact sub_nonneg.mpr (hl (by change 6*n-21 ≤ 6*n-21+j.val; omega))
  have hd1 (j : Fin 21) : d j ≤ 1 := by
    apply (div_le_one hu).mpr
    dsimp [U]
    linarith only [h0 ⟨6*n-21+j.val,by omega⟩]
  have hdo : Monotone d := by
    intro i j hij
    apply (div_le_div_iff_of_pos_right hu).mpr
    have ho := hl (show (⟨6*n-21+i.val,by omega⟩ : Fin (6*n)) ≤
      ⟨6*n-21+j.val,by omega⟩ by change 6*n-21+i.val ≤ 6*n-21+j.val; omega)
    linarith only [ho]
  have ht (i : Fin 15) : U*(1+r+h i)=l ⟨i.val,by omega⟩ := by
    dsimp [r,h]
    field_simp [ne_of_gt hu]
    <;> ring
  have hb (j : Fin 21) : U*(1-d j)=l ⟨6*n-21+j.val,by omega⟩ := by
    dsimp [d]
    field_simp [ne_of_gt hu]
    <;> ring
  have hf := literal_family_psd n (by omega) e l happt U r h d ht hb
  have hm := family_mass U r h d hu hr hh hf
  exact family_coupled U r h d hu hr hh hd0 hd1 hdo hm hf

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowCoupling
