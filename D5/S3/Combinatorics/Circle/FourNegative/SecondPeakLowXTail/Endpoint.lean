/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Endpoint
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A shared physical low-X permutation and its doubled-source ear order at cut zero. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Selection
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Terminals
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

/-! A physical low-X joint lift; the unrestricted problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private physicalDomain rWeight eWeight
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic
open private qHead qModulus qMass qTerminal qPeak qSeam qSlack margin
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private physicalBank physical_internal physical_disjoint physical_cover
  terminal terminal_inventory physicalValue physical_heads physical_mass
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalBanks
open private physical_moduli terminal_index physical_terminal_values
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Terminals
open private physical_margins
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Selection
open private seed sourceMod base newBase charge nextBase nextNewBase oldValue newValue chainOf chain_index chain_values source_signs source_totals new_base_bounds actual_values from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size chainLength chainStart negatives)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private sum_linear prefix_nonneg_le strip_of_prefix
  from D5.S3.Combinatorics.Circle.PeriodicShortening
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private def physicalRow (a b c d : ℕ) (isNew : Bool) : ℕ → ℤ :=
  if isNew then newValue a b c d else oldValue a b c d

private noncomputable def bankSum (a b c d : ℕ) (isNew : Bool) (r : Fin 4) : ℤ :=
  ((physicalBank a b c d r).toList.map (physicalRow a b c d isNew)).sum

-- These are the actual integer prefix peaks, in terminal order U,X,W,V.
private noncomputable def physicalPeak (a b c d : ℕ) (isNew : Bool) : Fin 4 → ℤ :=
  let m := bankSum a b c d isNew
  let f := physicalRow a b c d isNew
  let t := terminal a b c d
  let H := if isNew then base a b c d 0 else 0
  ![H+m 0, H+m 0+f (t 0)+m 1,
    H+m 0+f (t 0)+m 1+f (t 1)+m 2,
    H+m 0+f (t 0)+m 1+f (t 1)+m 2+f (t 2)+m 3]

private noncomputable def physicalWord (a b c d : ℕ) : List ℕ :=
  (physicalBank a b c d 0).toList ++ terminal a b c d 0 ::
  (physicalBank a b c d 1).toList ++ terminal a b c d 1 ::
  (physicalBank a b c d 2).toList ++ terminal a b c d 2 ::
  (physicalBank a b c d 3).toList ++ [terminal a b c d 3]

private theorem sum_toList (S : Finset ℕ) (f : ℕ → ℚ) :
    (S.toList.map f).sum = ∑ i ∈ S, f i := by
  change ((S.toList : Multiset ℕ).map f).sum = _
  rw [Finset.coe_toList]
  rfl

private theorem bankSum_cast (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (r : Fin 4) :
    (bankSum a b c d isNew r : ℚ) =
      qMass ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) isNew r := by
  rw [bankSum, Int.cast_list_sum, List.map_map]
  change ((physicalBank a b c d r).toList.map
    (fun i => (physicalRow a b c d isNew i : ℚ))).sum = _
  have hf : (fun i => (physicalRow a b c d isNew i : ℚ)) =
      physicalValue a b c d isNew := by
    funext i
    cases isNew <;> rfl
  rw [hf,sum_toList]
  exact physical_mass a b c d h isNew r


private theorem terminal_cast (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (r : Fin 4) :
    (physicalRow a b c d isNew (terminal a b c d r) : ℚ) =
      qTerminal ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1)) isNew r := by
  have ht := physical_terminal_values a b c d h isNew r
  cases isNew <;> simpa [physicalRow, physicalValue] using ht

private theorem peak_cast (a b c d : ℕ) (h : physicalDomain a b c d)
    (isNew : Bool) (r : Fin 4) :
    (physicalPeak a b c d isNew r : ℚ) =
      qPeak ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) isNew r := by
  have hA := (physical_heads a b c d h).1 0
  cases isNew <;> fin_cases r <;>
    simp [physicalPeak, qPeak, bankSum_cast a b c d h,
      terminal_cast a b c d h, hA]

-- Transfer only the six certified sides. The other sides below come from
-- positivity and remaining charge, rather than assumed strip conclusions.
private theorem physical_six (a b c d : ℕ) (h : physicalDomain a b c d) :
    (∀ r : Fin 4, r.val < 3 →
      0 ≤ physicalPeak a b c d false r +
        physicalRow a b c d false (terminal a b c d r)) ∧
    (∀ r : Fin 4, r.val < 3 →
      physicalPeak a b c d true r ≤ sourceMod a b c d) := by
  have hm := physical_margins a b c d h
  constructor
  · intro r hr
    have hh := hm ⟨r.val, by omega⟩
    have he : margin ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) ⟨r.val, by omega⟩ =
        qSeam ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
          (rWeight a b c d) (eWeight a b) false r := by
      fin_cases r <;> first | rfl | norm_num at hr
    rw [he, qSeam, ← peak_cast a b c d h false r,
      ← terminal_cast a b c d h false r] at hh
    exact_mod_cast hh
  · intro r hr
    have hh := hm ⟨r.val+3, by omega⟩
    have he : margin ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
        (rWeight a b c d) (eWeight a b) ⟨r.val+3, by omega⟩ =
        qSlack ((2:ℚ)^c) (2^a) (2^(d-a)) (2^(b-a-1))
          (rWeight a b c d) (eWeight a b) true r := by
      fin_cases r <;> first | rfl | norm_num at hr
    rw [he, qSlack, physical_moduli a b c d h true,
      ← peak_cast a b c d h true r] at hh
    simp only [↓reduceIte] at hh
    have hh' : (physicalPeak a b c d true r : ℚ) ≤
        (sourceMod a b c d : ℚ) := by linarith only [hh]
    exact_mod_cast hh'

private theorem physical_perm (a b c d : ℕ) (h : physicalDomain a b c d) :
    (physicalWord a b c d).Perm (List.range (size a b c d)) := by
  classical
  let B := physicalBank a b c d
  let t := terminal a b c d
  let k := size a b c d
  obtain ⟨htinj,htbound,htset⟩ := terminal_inventory a b c d h
  have htneg (r : Fin 4) : t r ∈ negatives a b c d := by
    apply List.mem_toFinset.mp
    rw [← htset]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  have good (r : Fin 4) (i : ℕ) (hi : i ∈ B r) :
      i < k ∧ i ≠ t 0 ∧ i ≠ t 1 ∧ i ≠ t 2 ∧ i ≠ t 3 := by
    obtain ⟨hib,hin⟩ := physical_internal a b c d h r i hi
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
    have hh := Finset.ext_iff.mp (physical_cover a b c d h) i
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
      have h0 := physical_disjoint a b c d h 3 0 (by decide)
      have h1 := physical_disjoint a b c d h 3 1 (by decide)
      have h2 := physical_disjoint a b c d h 3 2 (by decide)
      have hn0 : i ∉ B 0 := fun hx => Finset.disjoint_left.mp h0 hi hx
      have hn1 : i ∉ B 1 := fun hx => Finset.disjoint_left.mp h1 hi hx
      have hn2 : i ∉ B 2 := fun hx => Finset.disjoint_left.mp h2 hi hx
      tauto
  have hp := four_perm k (t 0) (t 1) (t 2) (t 3) (B 0) (B 1) (B 2)
    (good 0) (good 1) (good 2)
    (physical_disjoint a b c d h 0 1 (by decide))
    (physical_disjoint a b c d h 0 2 (by decide))
    (physical_disjoint a b c d h 1 2 (by decide)) hn htb
  dsimp only at hp
  rw [hG] at hp
  exact hp

-- Native digit data retain the common physical phase of the old and new rows.
private theorem matched_data (a b c d : ℕ) (h : physicalDomain a b c d) :
    seed a b c ≤ 2^(size a b c d-1)-1 ∧
    ∀ i : Fin (size a b c d),
      0 ≤ PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i ∧
      2*oldValue a b c d i.val-newValue a b c d i.val =
        PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
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

-- Final terminal V: exact doubled integer identities, not a floor/division cast.
private theorem last_bounds (a b c d : ℕ) (h : physicalDomain a b c d) :
    (0 ≤ -oldValue a b c d (terminal a b c d 3) ∧
      -oldValue a b c d (terminal a b c d 3) ≤ sourceMod a b c d / 2) ∧
    (0 ≤ -newValue a b c d (terminal a b c d 3) ∧
      -newValue a b c d (terminal a b c d 3) ≤ sourceMod a b c d) := by
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
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

-- A concrete permutation and every natural prefix bound, with the fresh label
-- literally prepended. This is the substantive natural certificate for the lift.
private theorem physical_prefixes (a b c d : ℕ) (h : physicalDomain a b c d) :
    (physicalWord a b c d).Perm (List.range (size a b c d)) ∧
    (∀ n : ℕ,
      0 ≤ (((physicalWord a b c d).take n).map (oldValue a b c d)).sum ∧
      (((physicalWord a b c d).take n).map (oldValue a b c d)).sum ≤
        sourceMod a b c d / 2) ∧
    (∀ n : ℕ,
      0 ≤ (((size a b c d :: physicalWord a b c d).take n).map
        (newValue a b c d)).sum ∧
      (((size a b c d :: physicalWord a b c d).take n).map
        (newValue a b c d)).sum ≤ sourceMod a b c d) := by
  classical
  let B := physicalBank a b c d
  let t := terminal a b c d
  let k := size a b c d
  let f := oldValue a b c d
  let g := newValue a b c d
  let A := base a b c d 0
  let N := sourceMod a b c d
  let word := physicalWord a b c d
  have ha : 2 ≤ a := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hb : 2 ≤ b := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hc : 2 ≤ c := h.1
  have hd : 2 ≤ d := by rcases h with ⟨hc,ha,hd,hb⟩; omega
  have hp : word.Perm (List.range k) := physical_perm a b c d h
  have tab := chain_values a b c d ha hb hc hd
  have hA : 0 ≤ A := by have hh := (tab.1 0).1; omega
  have hN : 0 ≤ N := by have hh := tab.1 0; omega
  have totals := source_totals a b c d ha hb hc hd
  have hfzero : (word.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hgtotal : (word.map g).sum = -A := (hp.map g).sum_eq.trans totals.2.1
  have hfresh : g k=A := totals.2.2
  have pos (r : Fin 4) (i : ℕ) (hi : i ∈ (B r).toList) :
      0 ≤ f i ∧ 0 ≤ g i := by
    obtain ⟨hib,hin⟩ := physical_internal a b c d h r i (Finset.mem_toList.mp hi)
    have hs := source_signs a b c d ha hb hc hd i hib
    rw [if_neg hin] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  obtain ⟨lower,upper⟩ := physical_six a b c d h
  obtain ⟨lastold,lastnew⟩ := last_bounds a b c d h
  -- First establish only the old lower side, using an unrestricted finite C.
  let C := max (physicalPeak a b c d false 0)
    (max (physicalPeak a b c d false 1)
      (max (physicalPeak a b c d false 2) (-f (t 3))))
  have c0 : physicalPeak a b c d false 0 ≤ C := le_max_left _ _
  have c1 : physicalPeak a b c d false 1 ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have c2 : physicalPeak a b c d false 2 ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have c3 : -f (t 3) ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have oldLoose : InStrip f C 0 word := by
    apply four_strip f (B 0).toList (B 1).toList (B 2).toList (B 3).toList
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
    · simpa only [zero_add,word,physicalWord,B,t] using hfzero
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
  have s0 : 0 ≤ A+((B 0).toList.map g).sum+g (t 0) := by
    have hh := new_lower_append ((B 0).toList++[t 0])
      ((B 1).toList++t 1::(B 2).toList++t 2::(B 3).toList++[t 3])
      (by simp [word,physicalWord,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have s1 : 0 ≤ A+((B 0).toList.map g).sum+g (t 0)+
      ((B 1).toList.map g).sum+g (t 1) := by
    have hh := new_lower_append ((B 0).toList++t 0::(B 1).toList++[t 1])
      ((B 2).toList++t 2::(B 3).toList++[t 3])
      (by simp [word,physicalWord,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have s2 : 0 ≤ A+((B 0).toList.map g).sum+g (t 0)+
      ((B 1).toList.map g).sum+g (t 1)+((B 2).toList.map g).sum+g (t 2) := by
    have hh := new_lower_append
      ((B 0).toList++t 0::(B 1).toList++t 1::(B 2).toList++[t 2])
      ((B 3).toList++[t 3])
      (by simp [word,physicalWord,B,t,List.append_assoc])
    simpa [List.map_append,List.sum_append,add_assoc] using hh
  have shiftedNew : InStrip g N A word := by
    apply four_strip g (B 0).toList (B 1).toList (B 2).toList (B 3).toList
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

/-- The physical construction gives one actual old order and its actual
    doubled-source ear order. The natural witness uses the literal cut j=0. -/
theorem actualSource_second_peak_low_x_joint_lift (a b c d : ℕ)
    (hc : 2 ≤ c) (ha : 2*c+1 ≤ a) (hd : a ≤ d) (hb : d+1 ≤ b) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  have h : physicalDomain a b c d := ⟨hc,ha,hd,hb⟩
  obtain ⟨hp,hold,hnew⟩ := physical_prefixes a b c d h
  apply (actual_nat_joint_iff a b c d (by omega) (by omega) hc (by omega)).mpr
  refine ⟨physicalWord a b c d,hp,?_,0,by omega,?_⟩
  · apply strip_of_prefix
    intro n
    simpa only [zero_add] using hold n
  · apply strip_of_prefix
    intro n
    simpa [insertAt] using hnew n

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
