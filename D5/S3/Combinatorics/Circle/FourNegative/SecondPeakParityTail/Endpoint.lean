/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Full-domain parity-tail physical source construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalStrips
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

/-!
A joint physical source order on the full parity-tail parameter domain.
The prefix argument uses the matched-charge decomposition of the LowX
construction. The integral selector produces alpha, S and delta; the six
strip margins control the physical banks, whose last bank ends in wLast.
The unrestricted four-gap problem remains open.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private physicalDomain
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalSelection
open private physicalBank physical_internal physical_disjoint physical_cover physical_mem
  terminal terminal_inventory localBits wLast w_last_inventory physical_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalBanks
open private physicalRow bank_mass_cast terminal_cast selected_six physical_modulus terminal_index physical_heads
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalStrips
open private parityMass parityPeak
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.StripAlgebra
open private qTerminal qModulus
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private size seed sourceMod base newBase chainLength chainStart
  oldValue newValue negatives chain_values source_signs source_totals new_base_bounds actual_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private sum_linear prefix_nonneg_le strip_of_prefix
  from D5.S3.Combinatorics.Circle.PeriodicShortening
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

-- The final bank ends with its W subword, whose last occurrence is q's bit.
-- No change is made to the physical inventory or either actual bank mass.
private noncomputable def bankList (a b c d alpha S : ℕ) (r : Fin 4) : List ℕ :=
  if r=3 then
    (physicalBank a b c d alpha S r \ (wLast a b c d S).toFinset).toList ++ wLast a b c d S
  else (physicalBank a b c d alpha S r).toList

private theorem bankList_perm (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hS2 : 2 ≤ S) (hSh : S < 2^(d-a)) (r : Fin 4) :
    (bankList a b c d alpha S r).Perm (physicalBank a b c d alpha S r).toList := by
  classical
  by_cases hr : r=3
  · subst r
    obtain ⟨hnd,hw,hlow⟩ := w_last_inventory a b c d alpha S h hS2 hSh
    have hsub : (wLast a b c d S).toFinset ⊆ physicalBank a b c d alpha S 3 := by
      intro i hi
      rw [hw] at hi
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      exact (physical_mem a b c d alpha S _ 3).mpr ⟨2,e,he,rfl⟩
    have hdis : List.Disjoint
        (physicalBank a b c d alpha S 3 \ (wLast a b c d S).toFinset).toList
        (wLast a b c d S) := by
      apply List.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2 (List.mem_toFinset.mpr hj)
    apply List.perm_of_nodup_nodup_toFinset_eq
      (by simpa only [bankList,↓reduceIte] using
        (Finset.nodup_toList _).append hnd hdis) (Finset.nodup_toList _)
    simp only [bankList,↓reduceIte,List.toFinset_append,Finset.toList_toFinset]
    exact Finset.sdiff_union_of_subset hsub
  · simp only [bankList,if_neg hr]
    exact List.Perm.refl _

private noncomputable def bankSum (a b c d alpha S : ℕ) (isNew : Bool) (r : Fin 4) : ℤ :=
  ((bankList a b c d alpha S r).map (physicalRow a b c d isNew)).sum

private noncomputable def physicalPeak (a b c d alpha S : ℕ) (isNew : Bool) : Fin 4 → ℤ :=
  let m := bankSum a b c d alpha S isNew
  let f := physicalRow a b c d isNew
  let t := terminal a b c d
  let H := if isNew then base a b c d 0 else 0
  ![H+m 0,H+m 0+f (t 0)+m 1,
    H+m 0+f (t 0)+m 1+f (t 1)+m 2,
    H+m 0+f (t 0)+m 1+f (t 1)+m 2+f (t 2)+m 3]

private noncomputable def physicalWord (a b c d alpha S : ℕ) : List ℕ :=
  bankList a b c d alpha S 0 ++ terminal a b c d 0 ::
  bankList a b c d alpha S 1 ++ terminal a b c d 1 ::
  bankList a b c d alpha S 2 ++ terminal a b c d 2 ::
  bankList a b c d alpha S 3 ++ [terminal a b c d 3]

private theorem bankSum_cast (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (isNew : Bool) (r : Fin 4) :
    (bankSum a b c d alpha S isNew r : ℚ)=
      (parityMass
        ((2:ℚ)^(a-c)) (2^c) (2^(d-a)) (2^(b-d-1)) alpha S isNew r) := by
  have he : bankSum a b c d alpha S isNew r =
      ∑ i ∈ physicalBank a b c d alpha S r, physicalRow a b c d isNew i := by
    rw [bankSum,((bankList_perm a b c d alpha S h hS2 hSh r).map _).sum_eq]
    change (((physicalBank a b c d alpha S r).toList : Multiset ℕ).map
      (physicalRow a b c d isNew)).sum = _
    rw [Finset.coe_toList]
    rfl
  rw [he]
  exact bank_mass_cast a b c d alpha S h hAlpha hS2 hSh isNew r

private theorem peak_cast (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (isNew : Bool) (r : Fin 4) :
    (physicalPeak a b c d alpha S isNew r : ℚ)=
      parityPeak ((2:ℚ)^(a-c)) (2^c) (2^(d-a)) (2^(b-d-1)) alpha S isNew r := by
  have hA := (physical_heads a b c d h).1 0
  cases isNew <;> fin_cases r <;>
    simp [physicalPeak,parityPeak,bankSum_cast a b c d alpha S h hAlpha hS2 hSh,
      terminal_cast a b c d h,hA]

private theorem physical_six (a b c d alpha S : ℕ) (delta : ℤ)
    (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (hS4 : 4*S ≤ 7*2^c) (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*((2:ℤ)^(a-c)-1))
    (hid : 2*(2:ℤ)^(a-c)*(2^c+1)*(alpha:ℤ)=
      (((2:ℤ)^(a-c))^2*2^c+1)*2^(d-a)+((2:ℤ)^(a-c)*2^c+1)*(S:ℤ)-
        15*(2:ℤ)^(a-c)*2^c/8+delta)
    (hB : 8*(15*(2:ℤ)^(a-c)*2^c/8)=15*(2:ℤ)^(a-c)*2^c) :
    (∀ r : Fin 4, r.val < 3 → 0 ≤ physicalPeak a b c d alpha S false r+
      physicalRow a b c d false (terminal a b c d r)) ∧
    (∀ r : Fin 4, r.val < 3 → physicalPeak a b c d alpha S true r ≤ sourceMod a b c d) := by
  have hm := selected_six a b c d alpha S delta h hS2 hS4 hd0 hdJ hid hB
  constructor
  · intro r hr
    have hh := hm.1 r hr
    rw [←peak_cast a b c d alpha S h hAlpha hS2 hSh false r,
      ←terminal_cast a b c d h false r] at hh
    exact_mod_cast hh
  · intro r hr
    have hh := hm.2 r hr
    rw [physical_modulus a b c d h false,
      ←peak_cast a b c d alpha S h hAlpha hS2 hSh true r] at hh
    simp only [Bool.false_eq_true,↓reduceIte] at hh
    exact_mod_cast hh

private theorem physical_perm (a b c d alpha S : ℕ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a)) :
    (physicalWord a b c d alpha S).Perm (List.range (size a b c d)) := by
  classical
  let B := physicalBank a b c d alpha S
  let t := terminal a b c d
  let k := size a b c d
  obtain ⟨htinj,htbound,htset⟩ := terminal_inventory a b c d h
  have htneg (r : Fin 4) : t r ∈ negatives a b c d := by
    apply List.mem_toFinset.mp
    rw [← htset]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have good (r : Fin 4) (i : ℕ) (hi : i ∈ B r) :
      i < k ∧ i ≠ t 0 ∧ i ≠ t 1 ∧ i ≠ t 2 ∧ i ≠ t 3 := by
    obtain ⟨hib,hin⟩ := physical_internal a b c d alpha S h hAlpha hS2 hSh r i hi
    refine ⟨hib, ?_, ?_, ?_, ?_⟩
    all_goals
      intro he
      apply hin
      rw [he]
      exact htneg _
  have hn : ([t 0,t 1,t 2,t 3] : List ℕ).Nodup := by
    rcases h with ⟨hc,ha,hd,hb⟩
    simp [t, terminal, size] <;> omega
  have htb : ∀ i ∈ ([t 0,t 1,t 2,t 3] : List ℕ), i < k := by
    intro i hi
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hi
    rcases hi with hi|hi|hi|hi <;> subst i <;> exact htbound _
  have hcover (i : ℕ) : (∃ r : Fin 4, i ∈ B r) ↔
      i < k ∧ i ∉ negatives a b c d := by
    have hh := Finset.ext_iff.mp (physical_cover a b c d alpha S h hAlpha hS2 hSh) i
    simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_range, List.mem_toFinset] using hh
  have hG : Finset.range k \ (B 0 ∪ B 1 ∪ B 2 ∪ {t 0,t 1,t 2,t 3}) = B 3 := by
    ext i
    constructor
    · intro hi
      obtain ⟨hib,hin⟩ := Finset.mem_sdiff.mp hi
      have hn : i ∉ negatives a b c d := by
        intro hh
        have hh' : i ∈ Finset.univ.image (terminal a b c d) := by
          rw [htset]; exact List.mem_toFinset.mpr hh
        obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hh'
        apply hin
        apply Finset.mem_union_right
        fin_cases r <;> simp [t, ← hr]
      obtain ⟨r,hr⟩ := (hcover i).mpr ⟨Finset.mem_range.mp hib,hn⟩
      fin_cases r
      · change i ∈ B 0 at hr
        exact (hin (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ hr)))).elim
      · change i ∈ B 1 at hr
        exact (hin (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hr)))).elim
      · change i ∈ B 2 at hr
        exact (hin (Finset.mem_union_left _ (Finset.mem_union_right _ hr))).elim
      · exact hr
    · intro hi
      have hh := good 3 i hi
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr hh.1, ?_⟩
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      have h0 := physical_disjoint a b c d alpha S h hAlpha hS2 hSh 3 0 (by decide)
      have h1 := physical_disjoint a b c d alpha S h hAlpha hS2 hSh 3 1 (by decide)
      have h2 := physical_disjoint a b c d alpha S h hAlpha hS2 hSh 3 2 (by decide)
      have hn0 : i ∉ B 0 := fun hx => Finset.disjoint_left.mp h0 hi hx
      have hn1 : i ∉ B 1 := fun hx => Finset.disjoint_left.mp h1 hi hx
      have hn2 : i ∉ B 2 := fun hx => Finset.disjoint_left.mp h2 hi hx
      tauto
  have hp := four_perm k (t 0) (t 1) (t 2) (t 3) (B 0) (B 1) (B 2)
    (good 0) (good 1) (good 2)
    (physical_disjoint a b c d alpha S h hAlpha hS2 hSh 0 1 (by decide))
    (physical_disjoint a b c d alpha S h hAlpha hS2 hSh 0 2 (by decide))
    (physical_disjoint a b c d alpha S h hAlpha hS2 hSh 1 2 (by decide)) hn htb
  dsimp only at hp
  rw [hG] at hp
  have hl := bankList_perm a b c d alpha S h hS2 hSh
  have ph : (physicalWord a b c d alpha S).Perm
      ((B 0).toList ++ t 0 :: (B 1).toList ++ t 1 ::
        (B 2).toList ++ t 2 :: (B 3).toList ++ [t 3]) := by
    simpa only [physicalWord,B,t,List.append_assoc,List.cons_append] using
      (hl 0).append (List.Perm.cons (t 0) ((hl 1).append
        (List.Perm.cons (t 1) ((hl 2).append
          (List.Perm.cons (t 2) ((hl 3).append_right [t 3]))))))
  exact ph.trans hp

private theorem matched_data (a b c d : ℕ) (h : physicalDomain a b c d) :
    seed a b c ≤ 2^(size a b c d-1)-1 ∧
    ∀ i : Fin (size a b c d),
      0 ≤ PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i ∧
      2*oldValue a b c d i.val-newValue a b c d i.val =
        PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hk : 2 ≤ size a b c d := by dsimp [size]; omega
  have hwa : 1 < (2:ℕ)^a := lt_of_lt_of_le (by decide : 1 < (2:ℕ)^2)
    (pow_le_pow_right₀ (by decide) ha)
  have hab : 2*(2:ℕ)^a ≤ 2^(a+b) := by
    calc
      _ = (2:ℕ)^(a+1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by decide) (by omega)
  have hbc : 2*(2:ℕ)^(a+b) ≤ 2^(a+b+c) := by
    calc
      _ = (2:ℕ)^(a+b+1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by decide) (by omega)
  have hlast : 2*(2:ℕ)^(a+b+c) ≤ 2^(size a b c d-1) := by
    calc
      _ = (2:ℕ)^(a+b+c+1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by decide) (by dsimp [size]; omega)
  have hw : seed a b c ≤ 2^(size a b c d-1)-1 := by
    dsimp [seed]
    omega
  refine ⟨hw,?_⟩
  intro i
  have digit := PeriodicShorteningArithmetic.digit_data (size a b c d) (seed a b c) hk hw i
  have shift : actualSource (size a b c d+1) (2*seed a b c) i.castSucc =
      actualSource (size a b c d+1) (seed a b c)
        ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩ := by
    dsimp [actualSource]
    push_cast
    rw [pow_succ]
    congr 1 <;> ring
  have he := shift.trans digit.2.2
  rw [(actual_values a b c d).2 i.castSucc, (actual_values a b c d).1 i] at he
  simp only [Fin.val_castSucc] at he
  exact ⟨digit.1,by omega⟩

private theorem last_bounds (a b c d : ℕ) (h : physicalDomain a b c d) :
    (0 ≤ -oldValue a b c d (terminal a b c d 3) ∧
      -oldValue a b c d (terminal a b c d 3) ≤ sourceMod a b c d / 2) ∧
    (0 ≤ -newValue a b c d (terminal a b c d 3) ∧
      -newValue a b c d (terminal a b c d 3) ≤ sourceMod a b c d) := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hn := native_masses a b c d ha hb hc hd 1
  dsimp only at hn
  have hi := terminal_index a b c d h 3
  change terminal a b c d 3 = chainStart b c d 1+(chainLength a b c d 1-1) at hi
  have ho := hn.2.2.1
  have hg := hn.2.2.2
  change 2*oldValue a b c d (chainStart b c d 1+(chainLength a b c d 1-1)) =
    base a b c d 2-sourceMod a b c d at ho
  change 2*newValue a b c d (chainStart b c d 1+(chainLength a b c d 1-1)) =
    newBase a b c d 2-(2*sourceMod a b c d+1) at hg
  rw [← hi] at ho hg
  have hB := (chain_values a b c d ha hb hc hd).1 2
  have hBn := new_base_bounds a b c d ha hb hc hd 2
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

private theorem physical_prefixes (a b c d alpha S : ℕ) (delta : ℤ) (h : physicalDomain a b c d)
    (hAlpha : alpha < 2^(d-1)-1) (hS2 : 2 ≤ S) (hSh : S < 2^(d-a))
    (hS4 : 4*S ≤ 7*2^c) (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*((2:ℤ)^(a-c)-1))
    (hid : 2*(2:ℤ)^(a-c)*(2^c+1)*(alpha:ℤ)=
      (((2:ℤ)^(a-c))^2*2^c+1)*2^(d-a)+((2:ℤ)^(a-c)*2^c+1)*(S:ℤ)-
        15*(2:ℤ)^(a-c)*2^c/8+delta)
    (hB : 8*(15*(2:ℤ)^(a-c)*2^c/8)=15*(2:ℤ)^(a-c)*2^c) :
    (physicalWord a b c d alpha S).Perm (List.range (size a b c d)) ∧
    (∀ n : ℕ,
      0 ≤ (((physicalWord a b c d alpha S).take n).map (oldValue a b c d)).sum ∧
      (((physicalWord a b c d alpha S).take n).map (oldValue a b c d)).sum ≤
        sourceMod a b c d / 2) ∧
    (∀ n : ℕ,
      0 ≤ (((size a b c d :: physicalWord a b c d alpha S).take n).map
        (newValue a b c d)).sum ∧
      (((size a b c d :: physicalWord a b c d alpha S).take n).map
        (newValue a b c d)).sum ≤ sourceMod a b c d) := by
  classical
  let B := physicalBank a b c d alpha S
  let L := bankList a b c d alpha S
  let t := terminal a b c d
  let k := size a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  let A := base a b c d 0
  let N := sourceMod a b c d
  let word := physicalWord a b c d alpha S
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := by have := h.1; omega
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hp : word.Perm (List.range k) := physical_perm a b c d alpha S h hAlpha hS2 hSh
  have tab := chain_values a b c d ha hb hc hd
  have hA : 0 ≤ A := by have hh := (tab.1 0).1; omega
  have hN : 0 ≤ N := by have hh := tab.1 0; omega
  have totals := source_totals a b c d ha hb hc hd
  have hfzero : (word.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hgtotal : (word.map g).sum = -A := (hp.map g).sum_eq.trans totals.2.1
  have hfresh : g k=A := totals.2.2
  have pos (r : Fin 4) (i : ℕ) (hi : i ∈ (L r)) :
      0 ≤ f i ∧ 0 ≤ g i := by
    have hi' : i ∈ (B r).toList :=
      (bankList_perm a b c d alpha S h hS2 hSh r).mem_iff.mp hi
    obtain ⟨hib,hin⟩ := physical_internal a b c d alpha S h hAlpha hS2 hSh r i (Finset.mem_toList.mp hi')
    have hs := source_signs a b c d ha hb hc hd i hib
    rw [if_neg hin] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  obtain ⟨lower,upper⟩ := physical_six a b c d alpha S delta h hAlpha hS2 hSh hS4 hd0 hdJ hid hB
  obtain ⟨lastold,lastnew⟩ := last_bounds a b c d h
  -- First establish only the old lower side, using an unrestricted finite C.
  let C := max (physicalPeak a b c d alpha S false 0)
    (max (physicalPeak a b c d alpha S false 1)
      (max (physicalPeak a b c d alpha S false 2) (-f (t 3))))
  have c0 : physicalPeak a b c d alpha S false 0 ≤ C := le_max_left _ _
  have c1 : physicalPeak a b c d alpha S false 1 ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have c2 : physicalPeak a b c d alpha S false 2 ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have c3 : -f (t 3) ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have oldLoose : InStrip f C 0 word := by
    apply four_strip f (L 0) (L 1) (L 2) (L 3)
      (t 0) (t 1) (t 2) (t 3) C 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) (by omega)
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,f] using c0,
        by simpa [physicalPeak,bankSum,physicalRow,f] using lower 0 (by decide)⟩
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,f] using c1,
        by simpa [physicalPeak,bankSum,physicalRow,f] using lower 1 (by decide)⟩
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,f] using c2,
        by simpa [physicalPeak,bankSum,physicalRow,f] using lower 2 (by decide)⟩
    · exact ⟨lastold.1,c3⟩
    · simpa only [zero_add,word,physicalWord,L,B,t] using hfzero
  have old_nonneg (n : ℕ) : 0 ≤ ((word.take n).map f).sum := by
    simpa only [zero_add] using (inStrip_prefix oldLoose n).1
  have data := matched_data a b c d h
  let chi : ℕ → ℤ := fun i => 2*f i-g i
  have chi_nonneg : ∀ i ∈ word, 0 ≤ chi i := by
    intro i hi
    have hib : i < k := List.mem_range.mp ((hp.mem_iff).mp hi)
    have hh := data.2 ⟨i,hib⟩
    change 0 ≤ 2*oldValue a b c d i-newValue a b c d i
    rw [hh.2]
    exact hh.1
  have chi_sum : (word.map chi).sum=A := by
    have hk : 2 ≤ k := by dsimp [k,size]; omega
    have hcast : (seed a b c : ℤ)=A := by
      simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [A,base]
      ring
    rw [(hp.map chi).sum_eq]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    calc
      _ = ∑ i : Fin k, chi i.val := (Fin.sum_univ_eq_sum_range chi k).symm
      _ = ∑ i : Fin k, PeriodicShorteningArithmetic.charge k (seed a b c) i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (data.2 i).2
      _ = (seed a b c : ℤ) := PeriodicShorteningArithmetic.charge_sum k (seed a b c) hk data.1
      _ = A := hcast
  have remaining (n : ℕ) :
      0 ≤ A+((word.take n).map g).sum-2*((word.take n).map f).sum := by
    have hc := (prefix_nonneg_le word chi chi_nonneg n).2
    rw [chi_sum] at hc
    have he := sum_linear (word.take n) f g 2 (-1)
    have hform : (fun i => (2:ℤ)*f i+(-1)*g i)=chi := by
      funext i; dsimp [chi]; ring
    rw [hform] at he
    linarith only [hc,he]
  have new_nonneg (n : ℕ) : 0 ≤ A+((word.take n).map g).sum := by
    linarith only [remaining n,old_nonneg n]
  have new_lower_append (pre post : List ℕ) (he : word=pre++post) :
      0 ≤ A+(pre.map g).sum := by
    have hh := new_nonneg pre.length
    simpa only [he,List.take_append,List.take_length,Nat.sub_self,
      List.take_zero,List.append_nil] using hh
  have s0 : 0 ≤ A+((L 0).map g).sum+g (t 0) := by
    have hh := new_lower_append ((L 0)++[t 0])
      ((L 1)++t 1::(L 2)++t 2::(L 3)++[t 3])
      (by simp [word,physicalWord,L,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have s1 : 0 ≤ A+((L 0).map g).sum+g (t 0)+
      ((L 1).map g).sum+g (t 1) := by
    have hh := new_lower_append ((L 0)++t 0::(L 1)++[t 1])
      ((L 2)++t 2::(L 3)++[t 3])
      (by simp [word,physicalWord,L,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have s2 : 0 ≤ A+((L 0).map g).sum+g (t 0)+
      ((L 1).map g).sum+g (t 1)+((L 2).map g).sum+g (t 2) := by
    have hh := new_lower_append
      ((L 0)++t 0::(L 1)++t 1::(L 2)++[t 2])
      ((L 3)++[t 3])
      (by simp [word,physicalWord,L,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have shiftedNew : InStrip g N A word := by
    apply four_strip g (L 0) (L 1) (L 2) (L 3)
      (t 0) (t 1) (t 2) (t 3) N A
      (fun i hi => (pos 0 i hi).2) (fun i hi => (pos 1 i hi).2)
      (fun i hi => (pos 2 i hi).2) (fun i hi => (pos 3 i hi).2) hA
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,g,A] using upper 0 (by decide),s0⟩
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,g,A] using upper 1 (by decide),s1⟩
    · exact ⟨by simpa [physicalPeak,bankSum,physicalRow,g,A] using upper 2 (by decide),s2⟩
    · exact lastnew
    · change A+(word.map g).sum=0
      rw [hgtotal]
      ring
  have oldSharp : InStrip f (N/2) 0 word := by
    apply strip_of_prefix
    intro n
    have hn := (inStrip_prefix shiftedNew n).2
    have hr := remaining n
    have hl := old_nonneg n
    constructor <;> omega
  have newSharp : InStrip g N 0 (k::word) := by
    change 0 ≤ (0:ℤ) ∧ 0 ≤ N ∧ InStrip g N (0+g k) word
    refine ⟨by omega,hN,?_⟩
    simpa only [zero_add,hfresh] using shiftedNew
  refine ⟨hp,?_,?_⟩
  · intro n
    simpa only [zero_add] using inStrip_prefix oldSharp n
  · intro n
    simpa only [zero_add] using inStrip_prefix newSharp n

-- Zero totals extend the individual physical bounds to every number of periods
-- and every natural prefix length; there is no finite-period cutoff.
private theorem repeated_prefixes {α : Type*} (f : α → ℤ) (B : ℤ) (word : List α)
    (hs : InStrip f B 0 word) (hz : (word.map f).sum=0) :
    (∀ m n : ℕ, 0 ≤ ((((List.replicate m word).flatten).take n).map f).sum ∧
      ((((List.replicate m word).flatten).take n).map f).sum ≤ B) ∧
    (∀ m : ℕ, (((List.replicate m word).flatten).map f).sum=0) := by
  have cycles (m : ℕ) : InStrip f B 0 (List.replicate m word).flatten ∧
      (((List.replicate m word).flatten).map f).sum=0 := by
    induction m with
    | zero =>
      constructor
      · simpa [InStrip] using inStrip_prefix hs 0
      · simp
    | succ m ih =>
      simp only [List.replicate_succ,List.flatten_cons]
      refine ⟨inStrip_append hs (by simpa only [hz,zero_add] using ih.1),?_⟩
      simp only [List.map_append,List.sum_append,hz,ih.2,add_zero]
  constructor
  · intro m n
    simpa only [zero_add] using inStrip_prefix (cycles m).1 n
  · intro m
    exact (cycles m).2

/-- One physical sigma, the literal cut zero, both actual
orders, every individual repeated prefix and exact totals on the full domain. -/
theorem actualSource_second_peak_parity_tail_joint_lift (a b c d : ℕ)
    (hc : 4 ≤ c) (ha : c+2 ≤ a) (hd : a+c+1 ≤ d) (hb : d+1 ≤ b) :
    ∃ sigma : List (Fin (a+b+c+d)),
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma 0) ∧
      (∀ m n : ℕ,
        (((((List.replicate m sigma).flatten).take n).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ,
        (((((List.replicate m (earWord (a+b+c+d) sigma 0)).flatten).take n).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))))).sum ∈
            Set.Icc (0:ℤ) (modulus (a+b+c+d+1)/2)) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum=0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma 0)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum=0) := by
  have h : physicalDomain a b c d := ⟨hc,ha,hd,hb⟩
  obtain ⟨alpha,S,delta,ha0,hAlpha,hS2,hS4,hSh,hd0,hdJ,hid,hB,hphysical⟩ :=
    physical_selection a b c d h
  obtain ⟨hp,hold,hnew⟩ := physical_prefixes a b c d alpha S delta h
    hAlpha hS2 hSh hS4 hd0 hdJ hid hB
  let k := a+b+c+d
  let A := 1+2^a+2^(a+b)+2^(a+b+c)
  let word := physicalWord a b c d alpha S
  have hk : 0 < k := by dsimp [k]; omega
  have hmod : modulus k=sourceMod a b c d := by dsimp [k,modulus,sourceMod]; ring
  have hmod' : modulus (k+1)=2*sourceMod a b c d+1 := by
    dsimp [k,modulus,sourceMod]; ring
  have hhalf : (2*sourceMod a b c d+1)/2=sourceMod a b c d := by omega
  have hseed : (A:ℤ)=base a b c d 0 := by
    dsimp [A]; push_cast; dsimp [base]; ring
  have hseed' : ((2*A:ℕ):ℤ)=2*base a b c d 0 := by push_cast; rw [hseed]
  have oldstrip : InStrip (fun i => centered (modulus k) ((2:ℤ)^i*A))
      (modulus k/2) 0 word := by
    apply strip_of_prefix
    intro n
    have hrow : oldValue a b c d =
        (fun i => centered (sourceMod a b c d) ((2:ℤ)^i*base a b c d 0)) := rfl
    simpa only [hmod,hseed,hrow,zero_add,word] using hold n
  have newstrip : InStrip (fun i => centered (modulus (k+1)) ((2:ℤ)^i*(2*A)))
      (modulus (k+1)/2) 0 (k::word) := by
    apply strip_of_prefix
    intro n
    have hrow : newValue a b c d =
        (fun i => centered (2*sourceMod a b c d+1) ((2:ℤ)^i*(2*base a b c d 0))) := rfl
    simpa only [hmod',hhalf,hseed,hseed',hrow,zero_add,word,k,size] using hnew n
  let sigma := word.map (label k hk)
  have ho : OriginalOrder k A sigma := by
    apply lift_order k A hk word hp oldstrip
    exact ThreeNegativeEqualOuterSourceBridge.source_zero k A (by dsimp [k]; omega)
  have hn : OriginalOrder (k+1) (2*A) (earWord k sigma 0) := by
    have hp' : (k::word).Perm (List.range (k+1)) := by
      have hpappend := hp.append_right [k]
      exact (List.perm_append_singleton k word).symm.trans
        (by simpa only [List.range_succ,word,k,size] using hpappend)
    have horder : OriginalOrder (k+1) (2*A)
        ((k::word).map (label (k+1) (by omega))) := by
      apply lift_order (k+1) (2*A) (by omega) (k::word) hp' newstrip
      exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*A) (by omega)
    have hear := marked_word k 0 hk [] word rfl hp
    have hear' : earWord k (word.map (label k hk)) 0 =
        (k::word).map (label (k+1) (by omega)) := by
      simpa only [List.nil_append] using hear
    change OriginalOrder (k+1) (2*A) (earWord k (word.map (label k hk)) 0)
    rw [hear']
    exact horder
  have hos : InStrip (actualSource k A) (modulus k/2) 0 sigma := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using ho.2.2 n
  have hns : InStrip (actualSource (k+1) (2*A)) (modulus (k+1)/2) 0 (earWord k sigma 0) := by
    apply strip_of_prefix
    intro n
    simpa only [zero_add,Set.mem_Icc] using hn.2.2 n
  obtain ⟨oldAll,oldZero⟩ := repeated_prefixes _ _ _ hos ho.2.1
  obtain ⟨newAll,newZero⟩ := repeated_prefixes _ _ _ hns hn.2.1
  refine ⟨sigma,ho,hn,?_,?_,?_⟩
  · intro m n
    exact oldAll m n
  · intro m n
    exact newAll m n
  · intro m
    exact ⟨oldZero m,newZero m⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
