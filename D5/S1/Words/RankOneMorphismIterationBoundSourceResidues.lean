/- GID: D5/S1/Words/RankOneMorphismIterationBoundSourceResidues
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundSourceResidues
   mirror-E: none(waiver:binary-source-translation)
   anchors: []
   digest: Actual source block starts and the binary d-translation argument. -/
import D5.S1.Words.RankOneMorphismIterationBoundResidues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
open AbelianBorders.AbelianBorderQuestionDefs (factor)
namespace Parameters
variable {f : Morphism} (p : Parameters f)

def startState (c : Letter) : State f := ⟨c,⟨0,by
  rw [p.image_length]
  have hm : 0 < p.mult c := by fin_cases c <;> simp [mult,p.n_pos,p.m_pos]
  exact Nat.mul_pos hm p.d_pos⟩⟩

def expandedPosition (i : ℕ) : ℕ := (expand (f := f) (factor p.fixedWord 0 i)).length

theorem expandedPosition_succ (i : ℕ) :
    p.expandedPosition (i+1) = p.expandedPosition i + (f (p.fixedWord i)).length := by
  rw [expandedPosition, factor_append]
  simp [factor,expandedPosition]

theorem indexedFixedWord_start (hp : Prolongable f) (i : ℕ) :
    p.indexedFixedWord (p.expandedPosition i) = p.startState (p.fixedWord i) := by
  let K := i+2
  have hig : i+1 ≤ (image f K 0).length := by
    have hh : i+1 < (image f K 0).length := p.image_growth (i+1)
    exact hh.le
  have hfac : factor p.fixedWord 0 (i+1) = (image f K 0).take (i+1) := by
    rw [← p.fixedWord_prefix hp K, factor_take _ _ _ _ hig]
  have hex := expand_prefix (f := f) (List.take_prefix (i+1) (image f K 0))
  rw [← hfac, factor_append] at hex
  have hprefix : expand (f := f) (factor p.fixedWord 0 i) ++ indexed (f := f) (p.fixedWord i) <+:
      expand (f := f) (image f K 0) := by
    simpa [factor] using hex
  have hm : p.expandedPosition i <
      (expand (f := f) (factor p.fixedWord 0 i) ++ indexed (f := f) (p.fixedWord i)).length := by
    simp only [List.length_append,indexed_length]
    have hh : 0 < (f (p.fixedWord i)).length := (p.startState (p.fixedWord i)).2.isLt
    exact Nat.lt_add_of_pos_right hh
  have hget := hprefix.getElem hm
  rw [p.indexedFixedWord_eq_image hp K _ (hm.trans_le hprefix.length_le)]
  rw [← hget]
  simp [expandedPosition,indexed,startState]

theorem fixedWord_zero (hp : Prolongable f) : p.fixedWord 0 = 0 := by
  simpa using p.fixedWord_eq_image hp 0 0 (by simp)

/-- An ordered change between two distinct binary letters gives an actual
    adjacent transition. All indices remain one-sided. -/
private theorem letter_cases (c : Letter) : c = 0 ∨ c = 1 := by
  fin_cases c <;> simp

private theorem transition_between (x : ℕ → Letter) (a b : Letter) (hab : a ≠ b)
    (i j : ℕ) (hij : i < j) (hi : x i = a) (hj : x j = b) :
    ∃ k, i ≤ k ∧ k < j ∧ x k = a ∧ x (k+1) = b := by
  induction j using Nat.strong_induction_on generalizing i with
  | h j ih =>
    by_cases hx : x (j-1) = a
    · refine ⟨j-1,by omega,by omega,hx,?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hj
    · have hxb : x (j-1) = b := by
        fin_cases a <;> fin_cases b <;>
          rcases letter_cases (x (j-1)) with hh | hh <;> simp_all
      have hsmall : i < j-1 := by
        by_contra hh
        have he : i = j-1 := by omega
        rw [← he,hi] at hx
        exact hx rfl
      obtain ⟨k,hki,hkj,hka,hkb⟩ := ih (j-1) (by omega) i hsmall hi hxb
      exact ⟨k,hki,by omega,hka,hkb⟩

/-- Both directed letter changes occur in an actual finite source iterate. -/
theorem source_transitions (hp : Prolongable f) :
    (∃ i, p.fixedWord i = 0 ∧ p.fixedWord (i+1) = 1) ∧
    (∃ i, p.fixedWord i = 1 ∧ p.fixedWord (i+1) = 0) := by
  have hp0 := hp
  obtain ⟨v,hv,hf⟩ := hp
  obtain ⟨c,w,hv'⟩ := List.exists_cons_of_ne_nil hv
  rw [hv'] at hf
  obtain ⟨i,hi,hione⟩ := List.mem_iff_getElem.mp (p.source_letter_mem 0 1)
  obtain ⟨j,hj,hjzero⟩ := List.mem_iff_getElem.mp (p.source_letter_mem c 0)
  have hwhole : image f 2 0 = f 0 ++ (f c ++ subst f w) := by
    rw [image_succ f 1 0,image_one]
    conv_lhs => rw [hf,subst_cons,subst_cons]
  have hiword : p.fixedWord i = 1 := by
    rw [p.fixedWord_eq_image hp0 2 i (by rw [hwhole]; simp only [List.length_append]; omega)]
    simp only [hwhole,List.getElem_append_left hi,hione]
  have hjword : p.fixedWord ((f 0).length+j) = 0 := by
    rw [p.fixedWord_eq_image hp0 2 _ (by rw [hwhole]; simp only [List.length_append]; omega)]
    simp only [hwhole]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getElem_append_left hj,hjzero]
  have hzero := p.fixedWord_zero hp0
  have hi0 : 0 < i := by
    by_contra hh
    have : i = 0 := by omega
    subst i; rw [hzero] at hiword; contradiction
  obtain ⟨a,ha,ha',ha0,ha1⟩ := transition_between p.fixedWord 0 1 (by decide) 0 i hi0 hzero hiword
  obtain ⟨b,hb,hb',hb1,hb0⟩ := transition_between p.fixedWord 1 0 (by decide) i ((f 0).length+j)
    (by omega) hiword hjword
  exact ⟨⟨a,ha0,ha1⟩,⟨b,hb1,hb0⟩⟩

private theorem start_difference (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) (c : Letter) (i j : ℕ)
    (hi : p.fixedWord i = c) (hj : p.fixedWord j = c) :
    (p.expandedPosition i : ZMod q)-(p.expandedPosition j : ZMod q) ∈
      p.returnSubgroup hp q hq hcop := by
  apply p.occurrence_difference hp p.allStatesReturn q hq hcop (p.startState c)
  · exact ⟨i |> p.expandedPosition,by rw [p.indexedFixedWord_start hp,hi],rfl⟩
  · exact ⟨j |> p.expandedPosition,by rw [p.indexedFixedWord_start hp,hj],rfl⟩

/-- Opposite changes give the sum of the two real image lengths in the return subgroup. -/
theorem length_sum_mem (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) :
    (((f 0).length+(f 1).length : ℕ) : ZMod q) ∈ p.returnSubgroup hp q hq hcop := by
  obtain ⟨⟨i,hi0,hi1⟩,⟨j,hj1,hj0⟩⟩ := p.source_transitions hp
  have ha := p.start_difference hp q hq hcop 0 (j+1) i hj0 hi0
  have hb := p.start_difference hp q hq hcop 1 j (i+1) hj1 hi1
  have hh := (p.returnSubgroup hp q hq hcop).sub_mem ha hb
  simp only [p.expandedPosition_succ,hi0,hj1,Nat.cast_add] at hh
  convert hh using 1 <;> push_cast <;> ring

/-- The exceptional no-double case is treated by bounded actual heights. -/
theorem equal_parameters_of_no_double (hp : Prolongable f)
    (hno : ¬ ∃ i : ℕ, p.fixedWord (i+1) = p.fixedWord i) : p.A = p.B := by
  have hc (j : ℕ) : p.charge (factor p.fixedWord (2*j) 2) = (p.B : ℤ)-p.A := by
    have hn : p.fixedWord (2*j+1) ≠ p.fixedWord (2*j) := by
      intro hh; exact hno ⟨2*j,hh⟩
    rcases letter_cases (p.fixedWord (2*j)) with ha | ha <;>
      rcases letter_cases (p.fixedWord (2*j+1)) with hb | hb <;>
      simp_all [factor,charge,parikh,AbelianBorders.AbelianBorderQuestionDefs.letterCount,List.range_succ]
  have he (j : ℕ) : p.height p.fixedWord (2*j) = (j : ℤ)*((p.B : ℤ)-p.A) := by
    induction j with
    | zero => simp [height,factor]
    | succ j ih =>
      rw [show 2*(j+1) = 2*j+2 by ring,p.height_add,hc,ih]
      push_cast; ring
  have hnot : ¬ Function.Injective (fun j : ℕ => p.height p.fixedWord (2*j)) := by
    intro hinj
    have hf := (p.fixedWord_height_finite hp).subset (show
      Set.range (fun j : ℕ => p.height p.fixedWord (2*j)) ⊆ Set.range (p.height p.fixedWord) by
        rintro _ ⟨j,rfl⟩; exact ⟨2*j,rfl⟩)
    exact Set.infinite_range_of_injective hinj hf
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  rw [he,he] at hij
  have hdiff : (i : ℤ)-j ≠ 0 := by
    apply sub_ne_zero.mpr; exact_mod_cast hne
  have hz : ((i : ℤ)-j)*((p.B : ℤ)-p.A) = 0 := by nlinarith
  have hab := (mul_eq_zero.mp hz).resolve_left hdiff
  have : (p.A : ℤ) = p.B := by omega
  exact_mod_cast this

/-- The source-specific translation by d is proved in both the double-letter
    and alternating cases. -/
theorem d_mem_return (hp : Prolongable f) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.lam q) :
    (p.d : ZMod q) ∈ p.returnSubgroup hp q hq hcop := by
  let S := p.returnSubgroup hp q hq hcop
  have hsum : (((f 0).length+(f 1).length : ℕ) : ZMod q) ∈ S := p.length_sum_mem hp q hq hcop
  by_cases hdoub : ∃ i : ℕ, p.fixedWord (i+1) = p.fixedWord i
  · obtain ⟨i,hi⟩ := hdoub
    have hd := p.start_difference hp q hq hcop (p.fixedWord i) (i+1) i hi rfl
    simp only [p.expandedPosition_succ,Nat.cast_add,add_sub_cancel_left] at hd
    have hboth : ((f 0).length : ZMod q) ∈ S ∧ ((f 1).length : ZMod q) ∈ S := by
      rcases letter_cases (p.fixedWord i) with hc | hc
      · rw [hc] at hd
        refine ⟨hd,?_⟩
        have hh := S.sub_mem hsum hd
        simpa only [Nat.cast_add,add_sub_cancel_left] using hh
      · rw [hc] at hd
        refine ⟨?_,hd⟩
        have hh := S.sub_mem hsum hd
        simpa only [Nat.cast_add,add_sub_cancel_right] using hh
    have hg : Nat.gcd (f 0).length (f 1).length = p.d := by
      simpa only [Nat.zero_add,image_one,pow_zero,mul_one] using p.iterated_gcd 0
    have he := congrArg (fun z : ℤ => (z : ZMod q))
      (Nat.gcd_eq_gcd_ab (f 0).length (f 1).length)
    simp only [Int.cast_natCast,Int.cast_add,Int.cast_mul,hg] at he
    rw [he]
    simpa only [zsmul_eq_mul,mul_comm] using S.add_mem
      (S.zsmul_mem hboth.1 (Nat.gcdA (f 0).length (f 1).length))
      (S.zsmul_mem hboth.2 (Nat.gcdB (f 0).length (f 1).length))
  · have hab := p.equal_parameters_of_no_double hp hdoub
    have hlen : (f 0).length+(f 1).length = 2*p.lam := by
      rw [p.image_length,p.image_length]
      simp only [mult,ite_true,show (1 : Letter) ≠ 0 by decide,ite_false,d,lam,hab]
      ring
    rw [hlen] at hsum
    have he := congrArg (fun z : ℤ => (z : ZMod q)) (Nat.gcd_eq_gcd_ab p.lam q)
    simp only [Int.cast_natCast,Int.cast_add,Int.cast_mul,hcop.gcd_eq_one,
      Nat.cast_one,Int.cast_one,ZMod.natCast_self,zero_mul,add_zero] at he
    have htwo : (2 : ZMod q) ∈ S := by
      have hh := S.zsmul_mem hsum (Nat.gcdA p.lam q)
      simp only [zsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hh
      convert hh using 1
      calc
        (2 : ZMod q) = 2*((p.lam : ZMod q)*(Nat.gcdA p.lam q : ZMod q)) := by rw [← he,mul_one]
        _ = _ := by ring
    have hh := S.nsmul_mem htwo p.A
    simpa only [nsmul_eq_mul,d,hab,Nat.cast_add,mul_two] using hh

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
