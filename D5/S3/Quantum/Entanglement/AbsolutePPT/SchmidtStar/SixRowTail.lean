/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Six distinct coefficient labels and a total cyclic assignment of all twenty-one deficits. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Group.Units.Equiv
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowTail
open UniformSchmidtIncidence
noncomputable section

/-- The actual diagonal/edge coefficient at the unchanged head vector. -/
def coefficient (p : Fin 5 → ℝ) : BottomSlot 6 → ℝ :=
  Sum.elim (fun i => (Fin.cases 1 p i)^2)
    (fun e => (Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2))

def tailCharge (d : Fin 21 → ℝ) (p : Fin 5 → ℝ)
    (σ : BottomSlot 6 ≃ Fin 21) : ℝ :=
  ∑ B, d (σ B)*coefficient p B

private theorem coefficient_nonneg (p : Fin 5 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (B : BottomSlot 6) : 0 ≤ coefficient p B := by
  have hz (i : Fin 6) : (0 : ℝ) ≤ Fin.cases (1 : ℝ) p i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · norm_num
    · simpa only [Fin.cases_succ] using hp j
  rcases B with i | e
  · exact sq_nonneg _
  · exact mul_nonneg (hz e.val.1) (hz e.val.2)

private def centre (i : Fin 5) : Edge 6 :=
  ⟨(0,i.succ), by change 0 < i.val+1; omega⟩

private theorem centre_injective : Function.Injective centre := by
  intro i j hij
  have hh := congrArg (fun e : Edge 6 => e.val.2) hij
  exact Fin.succ_injective 5 hh

@[simp] private theorem centre_inj (i j : Fin 5) : centre i = centre j ↔ i=j :=
  centre_injective.eq_iff

private def largeLabels (τ : Equiv.Perm (Fin 5)) : Fin 6 → BottomSlot 6 :=
  Fin.cases (.inl 0) (fun i => .inr (centre (τ i)))

private theorem largeLabels_injective (τ : Equiv.Perm (Fin 5)) :
    Function.Injective (largeLabels τ) := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun a => ?_) i <;>
    refine Fin.cases ?_ (fun b => ?_) j
  · intro _; rfl
  · intro h; cases h
  · intro h; cases h
  · intro h
    exact congrArg Fin.succ (τ.injective (centre_injective (Sum.inr.inj h)))

private def smallLabels (τ : Equiv.Perm (Fin 5)) : Fin 6 → BottomSlot 6 :=
  ![.inl 0, .inr (centre (τ 0)), .inr (centre (τ 1)),
    .inr (centre (τ 2)), .inl (τ 0).succ, .inl (τ 1).succ]

private theorem smallLabels_injective (τ : Equiv.Perm (Fin 5)) :
    Function.Injective (smallLabels τ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [smallLabels, centre_inj]
  all_goals
    have h := congrArg Fin.val hij
    simp only [Fin.val_zero, Fin.val_succ] at h
    omega

private theorem mass_of_labels (p : Fin 5 → ℝ) (f : Fin 6 → BottomSlot 6)
    (hf : Function.Injective f) (hm : 3 ≤ ∑ i, coefficient p (f i)) :
    ∃ S : Finset (BottomSlot 6), S.card=6 ∧ 3 ≤ ∑ B ∈ S, coefficient p B := by
  classical
  let e : Fin 6 ↪ BottomSlot 6 := ⟨f,hf⟩
  refine ⟨univ.map e, by simp, ?_⟩
  simpa [e] using hm

/-- Scalar part of the small-sum branch; only coordinate LABELS are sorted. -/
private theorem small_mass (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ho : Antitone w) (hn : ∑ i, (w i)^2=1) (hL : ∑ i, w i ≤ 2) :
    2 ≤ w 0+w 1+w 2+(w 0)^2+(w 1)^2 := by
  have hn' : (w 0)^2+(w 1)^2+(w 2)^2+(w 3)^2+(w 4)^2=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hn
  have hL' : w 0+w 1+w 2+w 3+w 4 ≤ 2 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hL
  have h01 : w 1 ≤ w 0 := ho (by decide)
  have h02 : w 2 ≤ w 0 := ho (by decide)
  have h03 : w 3 ≤ w 0 := ho (by decide)
  have h04 : w 4 ≤ w 0 := ho (by decide)
  have h12 : w 2 ≤ w 1 := ho (by decide)
  have h13 : w 3 ≤ w 1 := ho (by decide)
  have h14 : w 4 ≤ w 1 := ho (by decide)
  have h23 : w 3 ≤ w 2 := ho (by decide)
  have h24 : w 4 ≤ w 2 := ho (by decide)
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have h3 := hw 3
  have h4 := hw 4
  have hhalf : 1/2 ≤ w 0 := by
    have hA := mul_nonneg h1 (sub_nonneg.mpr h01)
    have hB := mul_nonneg h2 (sub_nonneg.mpr h02)
    have hC := mul_nonneg h3 (sub_nonneg.mpr h03)
    have hD := mul_nonneg h4 (sub_nonneg.mpr h04)
    have hE := mul_nonneg h0 (show 0 ≤ 2-(w 0+w 1+w 2+w 3+w 4) by linarith)
    nlinarith only [hn',hA,hB,hC,hD,hE]
  have hab : 1 ≤ w 0+w 1 := by
    by_contra hh
    have hab' : w 0+w 1 < 1 := lt_of_not_ge hh
    have ha1 : w 0 < 1 := by linarith only [hab',h1]
    have hA := mul_nonneg h2 (sub_nonneg.mpr h12)
    have hB := mul_nonneg h3 (sub_nonneg.mpr h13)
    have hC := mul_nonneg h4 (sub_nonneg.mpr h14)
    have hD := mul_nonneg h1 (show 0 ≤ 2-(w 0+w 1+w 2+w 3+w 4) by linarith)
    have hE := mul_pos (show 0 < 1-w 0-w 1 by linarith)
      (show 0 < 2-w 0 by linarith)
    have hF := mul_nonneg (show 0 ≤ 1-w 0 by linarith)
      (show 0 ≤ 2*w 0-1 by linarith)
    nlinarith only [hn',hA,hB,hC,hD,hE,hF]
  have hA := mul_nonneg h3 (sub_nonneg.mpr h23)
  have hB := mul_nonneg h4 (sub_nonneg.mpr h24)
  have hC := mul_nonneg h2 (show 0 ≤ 2-(w 0+w 1+w 2+w 3+w 4) by linarith)
  have hD := mul_nonneg (show 0 ≤ 1+w 2 by linarith) (sub_nonneg.mpr hab)
  nlinarith only [hn',hA,hB,hC,hD]

/-- Six DISTINCT slots, including ties and zero coordinates. No p is replaced. -/
theorem six_coefficient_mass (p : Fin 5 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hn : ∑ i, (p i)^2=1) :
    ∃ S : Finset (BottomSlot 6), S.card=6 ∧ 3 ≤ ∑ B ∈ S, coefficient p B := by
  classical
  let τ := Tuple.sort (fun i => -p i)
  let w : Fin 5 → ℝ := fun i => p (τ i)
  have hw : ∀ i, 0 ≤ w i := fun i => hp (τ i)
  have hwo : Antitone w := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -p i) hij
    change -w i ≤ -w j at hh
    linarith only [hh]
  have hwn : ∑ i, (w i)^2=1 := by
    change (∑ i, (p (τ i))^2)=1
    exact (Equiv.sum_comp τ (fun i => (p i)^2)).trans hn
  by_cases hL : 2 ≤ ∑ i, w i
  · apply mass_of_labels p (largeLabels τ) (largeLabels_injective τ)
    have he : (∑ i, coefficient p (largeLabels τ i))=1+∑ i, w i := by
      simp [largeLabels,coefficient,centre,w,Fin.sum_univ_succ]
    rw [he]
    linarith only [hL]
  · apply mass_of_labels p (smallLabels τ) (smallLabels_injective τ)
    have hs := small_mass w hw hwo hwn (le_of_not_ge hL)
    have he : (∑ i, coefficient p (smallLabels τ i))=
        1+w 0+w 1+w 2+(w 0)^2+(w 1)^2 := by
      simp [smallLabels,coefficient,centre,w,Fin.sum_univ_succ]
      <;> ring
    rw [he]
    linarith only [hs]

/-- All 21 terms are charged before the mass inequality is used. -/
theorem capped_tail_squares (x : Fin 21 → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (ho : Antitone x) (hm : ∑ i, x i ≤ 6) :
    (∑ i, (x i)^2) ≤ ∑ i, if i.val < 6 then x i else 0 := by
  let t := x 5
  have ht : 0 ≤ t := h0 5
  have hpoint (i : Fin 21) : (x i)^2 ≤
      (if i.val < 6 then x i else 0)+t*x i-t*(if i.val < 6 then 1 else 0) := by
    by_cases hi : i.val < 6
    · have hit : t ≤ x i := ho (by change i.val ≤ 5; omega)
      have hh := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hit) (sub_nonpos.mpr (h1 i))
      simp only [if_pos hi]
      nlinarith only [hh]
    · have hit : x i ≤ t := ho (by change 5 ≤ i.val; omega)
      have hh := mul_nonneg (h0 i) (sub_nonneg.mpr hit)
      simp only [if_neg hi]
      nlinarith only [hh]
  have hc : (∑ i : Fin 21, if i.val < 6 then (1:ℝ) else 0)=6 := by
    simp only [Fin.sum_univ_succ]
    norm_num
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 21))) => hpoint i)
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum] at hs
  rw [hc] at hs
  have hmass := mul_nonneg ht (sub_nonneg.mpr hm)
  nlinarith only [hs,hmass]

/-- Enumerations of six selected labels and their fifteen-label complement. -/
private def selectedSlots (S : Finset (BottomSlot 6)) (hS : S.card=6) :
    Fin 6 ⊕ Fin 15 ≃ BottomSlot 6 := by
  classical
  have he : Fintype.card (Edge 6)=15 := by
    simpa using (Fintype.card_congr SixRowHead.edgeEquiv).symm
  have hc : Fintype.card (BottomSlot 6)=21 := by
    simp [BottomSlot,he]
  let es : S ≃ Fin 6 := S.equivFinOfCardEq hS
  let ec : (Sᶜ : Finset (BottomSlot 6)) ≃ Fin 15 :=
    (Sᶜ).equivFinOfCardEq (by simp [card_compl,hS,hc])
  let f : Fin 6 ⊕ Fin 15 → BottomSlot 6 :=
    Sum.elim (fun i => (es.symm i).val) (fun i => (ec.symm i).val)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · exact congrArg Sum.inl (es.symm.injective (Subtype.ext hxy))
    · change (es.symm i).val=(ec.symm j).val at hxy
      exact ((mem_compl.mp (ec.symm j).property)
        (hxy ▸ (es.symm i).property)).elim
    · change (ec.symm i).val=(es.symm j).val at hxy
      exact ((mem_compl.mp (ec.symm i).property)
        (hxy.symm ▸ (es.symm j).property)).elim
    · exact congrArg Sum.inr (ec.symm.injective (Subtype.ext hxy))
  · intro x
    by_cases hx : x ∈ S
    · refine ⟨.inl (es ⟨x,hx⟩),?_⟩
      simp [f]
    · refine ⟨.inr (ec ⟨x,mem_compl.mpr hx⟩),?_⟩
      simp [f]

private theorem selected_sum (S : Finset (BottomSlot 6)) (hS : S.card=6)
    (c : BottomSlot 6 → ℝ) :
    (∑ i : Fin 6, c (selectedSlots S hS (.inl i)))=∑ B ∈ S, c B := by
  classical
  let es : S ≃ Fin 6 := S.equivFinOfCardEq hS
  change (∑ i : Fin 6, c (es.symm i).val)=_
  rw [es.symm.sum_comp (fun i : S => c i.val),sum_coe_sort]

private theorem good_cycle (x c : Fin 6 → ℝ) (b : ℝ)
    (hb : 6*b ≤ (∑ i, x i)*(∑ i, c i)) :
    ∃ k : Fin 6, b ≤ ∑ i, x (i+k)*c i := by
  classical
  have hav : (∑ k : Fin 6, ∑ i : Fin 6, x (i+k)*c i)=
      (∑ i, x i)*(∑ i, c i) := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    have hs (i : Fin 6) : (∑ k : Fin 6, x (i+k))=∑ k, x k :=
      Equiv.sum_comp (Equiv.addLeft i) x
    simp_rw [hs]
    rw [mul_sum]
  obtain ⟨k,_,hk⟩ := exists_le_of_sum_le
    (s := (univ : Finset (Fin 6))) univ_nonempty
    (f := fun _ => b) (g := fun k => ∑ i, x (i+k)*c i) (by simpa [hav] using hb)
  exact ⟨k,hk⟩

/-- A TOTAL bottom equivalence at the very same arbitrary p as the head.
The selected slots go to 15..20, and the complement to 0..14. -/
theorem tail_exists (d : Fin 21 → ℝ) (p : Fin 5 → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (hdo : Monotone d) (hm : ∑ i, d i ≤ 6)
    (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, (p i)^2=1) :
    ∃ σ : BottomSlot 6 ≃ Fin 21, (∑ i, (d i)^2)/2 ≤ tailCharge d p σ := by
  classical
  let s : Equiv.Perm (Fin 21) := Fin.revPerm
  let x : Fin 21 → ℝ := fun i => d (s i)
  have hx0 : ∀ i, 0 ≤ x i := fun i => hd0 (s i)
  have hxo : Antitone x := by
    intro i j hij
    exact hdo (Fin.rev_le_rev.mpr hij)
  have hxm : ∑ i, x i ≤ 6 := by
    change (∑ i, d (s i)) ≤ 6
    rw [Equiv.sum_comp]
    exact hm
  have hcap := capped_tail_squares x hx0 (fun i => hd1 (s i)) hxo hxm
  let T : ℝ := ∑ i : Fin 6, x (Fin.castAdd 15 i)
  have hT : 0 ≤ T := sum_nonneg (fun i _ => hx0 _)
  have hT_eq : (∑ i : Fin 21, if i.val < 6 then x i else 0)=T := by
    simp [T,Fin.sum_univ_succ]
  have hsq : (∑ i, (x i)^2)=∑ i, (d i)^2 :=
    Equiv.sum_comp s (fun i => (d i)^2)
  rw [hsq,hT_eq] at hcap
  obtain ⟨S,hS,hcoeff⟩ := six_coefficient_mass p hp hn
  let E := selectedSlots S hS
  have hcs : 3 ≤ ∑ i : Fin 6, coefficient p (E (.inl i)) := by
    simpa only [E,selected_sum] using hcoeff
  have hav : (6:ℝ)*(T/2) ≤ T*(∑ i : Fin 6, coefficient p (E (.inl i))) := by
    nlinarith only [mul_nonneg hT (sub_nonneg.mpr hcs)]
  obtain ⟨k,hk⟩ := good_cycle (fun i => x (Fin.castAdd 15 i))
    (fun i => coefficient p (E (.inl i))) (T/2) hav
  let σ : BottomSlot 6 ≃ Fin 21 := E.symm.trans
    ((Equiv.sumCongr (Equiv.addRight k) (Equiv.refl (Fin 15))).trans
      (finSumFinEquiv.trans (Fin.revPerm : Equiv.Perm (Fin 21))))
  have hv : tailCharge d p σ =
      (∑ i : Fin 6, x (Fin.castAdd 15 (i+k))*coefficient p (E (.inl i)))+
      ∑ j : Fin 15, x (Fin.natAdd 6 j)*coefficient p (E (.inr j)) := by
    unfold tailCharge
    rw [← E.sum_comp (fun B => d (σ B)*coefficient p B)]
    simp [σ,x,s,Fintype.sum_sum_type,
      finSumFinEquiv_apply_left (m:=6) (n:=15),
      finSumFinEquiv_apply_right (m:=6) (n:=15)]
  have hrest : 0 ≤ ∑ j : Fin 15,
      x (Fin.natAdd 6 j)*coefficient p (E (.inr j)) :=
    sum_nonneg (fun j _ => mul_nonneg (hx0 _) (coefficient_nonneg p hp _))
  refine ⟨σ,?_⟩
  rw [hv]
  linarith only [hcap,hk,hrest]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowTail
