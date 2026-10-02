/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSeven
   mirror-E: none(waiver:triple-avoidance-combinatorial-enumeration)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: Reversible decompositions and word recurrences prove all three Fishburn counts. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenDefs
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenACEquiv
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBEquiv
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSeven

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenWords FishburnTenSevenWords.Letter
open FishburnTenSevenACEquiv FishburnTenSevenBEquiv FishburnTenSevenBParameters
open FishburnTenSevenBStructure FishburnTenSevenAuxiliary

theorem result : FishburnTenSevenDefs.claim107 := by
  classical
  have hfiniteH (total : ℕ) : Finite (↥(avoiders total [[2, 1, 3]])) := by
    have hf : (avoiders total [[2, 1, 3]]).Finite := by
      apply (List.finite_toSet (List.range' 1 total).permutations).subset
      intro p hp
      exact List.mem_permutations.mpr hp.1
    exact hf.to_subtype
  have hauxCard (size : ℕ) :
    Nat.card (↥(avoiders size [[2, 1, 3]])) = if size = 0 then 1 else 2 ^ (size - 1) := by
    let (total : ℕ) : Finite (↥(avoiders total [[2, 1, 3]])) := hfiniteH total
    have hzero : Nat.card (↥(avoiders 0 [[2, 1, 3]])) = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      let hempty : ↥(avoiders 0 [[2, 1, 3]]) := by
        refine ⟨[], by simp, ?_, ?_⟩
        · intro before later hgap hlater
          simp at hlater
        · simp only [List.mem_singleton, forall_eq]
          rintro ⟨values, _, _, hsub, _⟩
          have := hsub.length_le
          simp at this
      refine ⟨hempty, ?_⟩
      intro p
      apply Subtype.ext
      have hl := p.property.1.length_eq
      simpa [hempty] using List.length_eq_zero_iff.mp hl
    have hone : Nat.card (↥(avoiders 1 [[2, 1, 3]])) = 1 := by
      rw [Nat.card_congr (H_maximum_equiv 1 (by omega)), Nat.card_sigma]
      simp [hzero]
    have hdouble (total : ℕ) (ht : 1 ≤ total) :
        Nat.card (↥(avoiders (total + 1) [[2, 1, 3]])) =
          Nat.card (↥(avoiders total [[2, 1, 3]])) +
            Nat.card (↥(avoiders total [[2, 1, 3]])) := by
      rw [Nat.card_congr (H_maximum_equiv (total + 1) (by omega)), Nat.card_sigma,
        Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, Fin.val_succ]
      congr 1
      rw [Nat.card_congr (H_maximum_equiv total ht), Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro cut _
      have hs : total + 1 - (cut.val + 1) - 1 = total - cut.val - 1 := by omega
      rw [hs]
    induction size with
    | zero => simpa using hzero
    | succ size ih =>
        by_cases hz : size = 0
        · subst size
          simpa using hone
        · rw [hdouble size (by omega), ih]
          simp only [hz, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
            Nat.add_sub_cancel]
          have hexponent : size = size - 1 + 1 := by omega
          conv_rhs => rw [hexponent, pow_succ]
          omega
  have hbCount (size : ℕ) (hsize : 1 ≤ size) :
    Finite (BParameters size) ∧ Nat.card (BParameters size) = 2 ^ size - size := by
    have hstartOneCard (size : ℕ) (hsize : 1 ≤ size) :
        Nat.card (HStart size) = if size = 1 then 1 else 2 ^ (size - 2) := by
      have hinitial (total : ℕ) (ht : 1 ≤ total) (p : HStart (total + 1)) :
          ∃ q : ↥(avoiders total [[2, 1, 3]]), p.val.val = 1 :: q.val.map (· + 1) := by
        obtain ⟨q, hq | hq⟩ := (H_head_decomposition total p.val.val).mp p.val.property
        · have hhead := p.property
          rw [hq] at hhead
          simp only [List.head?_cons, Option.some.injEq] at hhead
          omega
        · exact ⟨q, hq⟩
      have hencode (total : ℕ) (ht : 1 ≤ total) :
          HStart (total + 1) ≃ ↥(avoiders total [[2, 1, 3]]) := by
        let encode (p : HStart (total + 1)) : ↥(avoiders total [[2, 1, 3]]) :=
          Classical.choose (hinitial total ht p)
        have he (p : HStart (total + 1)) : p.val.val = 1 :: (encode p).val.map (· + 1) :=
          Classical.choose_spec (hinitial total ht p)
        let decode (q : ↥(avoiders total [[2, 1, 3]])) : HStart (total + 1) :=
          ⟨⟨1 :: q.val.map (· + 1), (H_head_decomposition total _).mpr ⟨q, Or.inr rfl⟩⟩,
            rfl⟩
        refine
          { toFun := encode
            invFun := decode
            left_inv := ?_
            right_inv := ?_ }
        · intro p
          apply Subtype.ext
          exact Subtype.ext (he p).symm
        · intro q
          apply Subtype.ext
          have hmap := (List.cons.inj (he (decode q))).2
          exact ((List.map_inj_right (fun first second he => Nat.add_right_cancel he)).mp
            hmap).symm
      by_cases hone : size = 1
      · subst size
        simp only [↓reduceIte]
        apply Nat.card_eq_one_iff_exists.mpr
        let hempty : ↥(avoiders 0 [[2, 1, 3]]) := by
          refine ⟨[], by simp, ?_, ?_⟩
          · intro before later hgap hlater
            simp at hlater
          · simp only [List.mem_singleton, forall_eq]
            rintro ⟨values, _, _, hsub, _⟩
            have := hsub.length_le
            simp at this
        let one : HStart 1 :=
          ⟨⟨[1], (H_head_decomposition 0 [1]).mpr ⟨hempty, Or.inl (by simp [hempty])⟩⟩,
            rfl⟩
        refine ⟨one, ?_⟩
        intro p
        apply Subtype.ext
        apply Subtype.ext
        have hp := p.val.property.1
        have hl : p.val.val.length = 1 := by simpa using hp.length_eq
        obtain ⟨value, he⟩ := List.length_eq_one_iff.mp hl
        have hh := p.property
        rw [he] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        change p.val.val = [1]
        rw [he, hh]
      · obtain ⟨total, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
        rw [Nat.card_congr (hencode total (by omega)), hauxCard]
        simp only [show total ≠ 0 by omega, hone, ↓reduceIte]
        congr 1
    let (total : ℕ) : Finite (↥(avoiders total [[2, 1, 3]])) := hfiniteH total
    let (total : ℕ) : Finite (HStart total) := by dsimp only [HStart]; infer_instance
    let (low high : ℕ) : Finite {value : ℕ // low ≤ value ∧ value < high} :=
      (Set.finite_Ico low high).to_subtype
    let (low high : ℕ) : Finite {value : ℕ // low ≤ value ∧ value ≤ high} :=
      (Set.finite_Icc low high).to_subtype
    let (low high : ℕ) : Fintype {value : ℕ // low ≤ value ∧ value < high} :=
      Fintype.ofFinite _
    let (low high : ℕ) : Fintype {value : ℕ // low ≤ value ∧ value ≤ high} :=
      Fintype.ofFinite _
    let Tail (maximum : ℕ) :=
      Σ low : {low : ℕ // 2 ≤ low ∧ low < maximum},
        Σ high : {high : ℕ // low.val ≤ high ∧ high < maximum},
          ↥(avoiders (low.val - 2) [[2, 1, 3]])
    let Layer (maximum : ℕ) :=
      Σ low : {low : ℕ // 2 ≤ low ∧ low ≤ maximum}, ↥(avoiders (low.val - 2) [[2, 1, 3]])
    let Slice (maximum : ℕ) := HStart maximum ⊕ Tail maximum
    let (maximum : ℕ) : Finite (Tail maximum) := by
      dsimp only [Tail]
      infer_instance
    let (maximum : ℕ) : Finite (Layer maximum) := by
      dsimp only [Layer]
      infer_instance
    let (maximum : ℕ) : Finite (Slice maximum) := by
      dsimp only [Slice]
      infer_instance
    have hfinite (total : ℕ) : Finite (BParameters total) := by
      dsimp only [BParameters]
      infer_instance
    let (total : ℕ) : Finite (BParameters total) := hfinite total
    have htailSplit (maximum : ℕ) : Tail (maximum + 1) ≃ Tail maximum ⊕ Layer maximum := by
      refine
        { toFun := fun ⟨low, high, q⟩ =>
            if hh : high.val < maximum then
              Sum.inl ⟨⟨low.val, low.property.1, by
                have := high.property.1; omega⟩, ⟨high.val, high.property.1, hh⟩, q⟩
            else Sum.inr ⟨⟨low.val, low.property.1, by
              have := low.property.2; omega⟩, q⟩
          invFun := fun data => match data with
            | Sum.inl ⟨low, high, q⟩ =>
              ⟨⟨low.val, low.property.1, by have := low.property.2; omega⟩,
                ⟨high.val, high.property.1, by have := high.property.2; omega⟩, q⟩
            | Sum.inr ⟨low, q⟩ =>
              ⟨⟨low.val, low.property.1, by have := low.property.2; omega⟩,
                ⟨maximum, low.property.2, by omega⟩, q⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨⟨low, hl⟩, ⟨⟨high, hh⟩, q⟩⟩
        dsimp only
        by_cases hlt : high < maximum
        · simp only [hlt, ↓reduceDIte]
        · have he : high = maximum := by omega
          subst high
          simp only [lt_self_iff_false, ↓reduceDIte]
      · rintro (⟨⟨low, hl⟩, ⟨⟨high, hh⟩, q⟩⟩ | ⟨⟨low, hl⟩, q⟩)
        · dsimp only
          simp only [hh.2, ↓reduceDIte]
        · dsimp only
          simp only [lt_self_iff_false, ↓reduceDIte]
    have hlayerCard (maximum : ℕ) (hm : 2 ≤ maximum) :
        Nat.card (Layer maximum) = Nat.card (↥(avoiders (maximum - 1) [[2, 1, 3]])) := by
      let index : {low : ℕ // 2 ≤ low ∧ low ≤ maximum} ≃ Fin (maximum - 1) :=
        { toFun := fun low => ⟨maximum - low.val, by have := low.property; omega⟩
          invFun := fun cut => ⟨maximum - cut.val, by have := cut.is_lt; omega⟩
          left_inv := by
            intro low
            apply Subtype.ext
            dsimp only
            have := low.property
            omega
          right_inv := by
            intro cut
            apply Fin.ext
            dsimp only
            have := cut.is_lt
            omega }
      change Nat.card (Σ low : {low : ℕ // 2 ≤ low ∧ low ≤ maximum},
        ↥(avoiders (low.val - 2) [[2, 1, 3]])) =
        Nat.card (↥(avoiders (maximum - 1) [[2, 1, 3]]))
      rw [Nat.card_sigma]
      conv_rhs =>
        rw [Nat.card_congr (H_maximum_equiv (maximum - 1) (by omega)), Nat.card_sigma]
      apply Fintype.sum_equiv index
      intro low
      have he : maximum - 1 - (maximum - low.val) - 1 = low.val - 2 := by
        have := low.property
        omega
      change Nat.card (↥(avoiders (low.val - 2) [[2, 1, 3]])) =
        Nat.card (↥(avoiders (maximum - 1 - (maximum - low.val) - 1) [[2, 1, 3]]))
      rw [he]
    have hmaximumSplit (total : ℕ) :
        BParameters (total + 1) ≃ BParameters total ⊕ Slice (total + 1) := by
      refine
        { toFun := fun ⟨maximum, data⟩ =>
            if hm : maximum.val ≤ total then
              Sum.inl ⟨⟨maximum.val, maximum.property.1, hm⟩, data⟩
            else Sum.inr (cast (congrArg Slice (by
              have := maximum.property; omega : maximum.val = total + 1)) data)
          invFun := fun data => match data with
            | Sum.inl ⟨maximum, body⟩ =>
              ⟨⟨maximum.val, maximum.property.1, by
                have := maximum.property.2; omega⟩, body⟩
            | Sum.inr body => ⟨⟨total + 1, by omega, by omega⟩, body⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨⟨maximum, hm⟩, body⟩
        dsimp only
        by_cases hle : maximum ≤ total
        · simp only [hle, ↓reduceDIte]
          rfl
        · have he : maximum = total + 1 := by omega
          subst maximum
          simp only [Nat.not_succ_le_self, ↓reduceDIte, cast_eq]
          rfl
      · rintro (⟨⟨maximum, hm⟩, body⟩ | body)
        · dsimp only
          simp only [hm.2, ↓reduceDIte]
        · dsimp only
          simp only [Nat.not_succ_le_self, ↓reduceDIte, cast_eq]
    have htailSmall (maximum : ℕ) (hm : maximum ≤ 2) : Nat.card (Tail maximum) = 0 := by
      let : IsEmpty (Tail maximum) := ⟨fun data => by have := data.1.property; omega⟩
      simp
    have hsliceOne : Nat.card (Slice 1) = 1 := by
      change Nat.card (HStart 1 ⊕ Tail 1) = 1
      rw [Nat.card_sum, hstartOneCard 1 (by omega), htailSmall 1 (by omega)]
      simp
    have hslice (index : ℕ) : Nat.card (Slice (index + 2)) + 1 = 2 ^ (index + 1) := by
      induction index with
      | zero =>
          change Nat.card (HStart 2 ⊕ Tail 2) + 1 = 2 ^ 1
          rw [Nat.card_sum, hstartOneCard 2 (by omega), htailSmall 2 (by omega)]
          norm_num
      | succ index ih =>
          have htailCount : Nat.card (Tail (index + 3)) =
              Nat.card (Tail (index + 2)) + 2 ^ index := by
            have htail := Nat.card_congr (htailSplit (index + 2))
            rw [Nat.card_sum, hlayerCard (index + 2) (by omega)] at htail
            change Nat.card (Tail (index + 3)) =
              Nat.card (Tail (index + 2)) + Nat.card (↥(avoiders (index + 1) [[2, 1, 3]])) at htail
            rw [hauxCard] at htail
            simpa [show index + 1 ≠ 0 by omega] using htail
          have hpreviousOne : Nat.card (HStart (index + 2)) = 2 ^ index := by
            simpa [show index + 2 ≠ 1 by omega] using
              hstartOneCard (index + 2) (by omega)
          have hnextOne : Nat.card (HStart (index + 3)) = 2 ^ (index + 1) := by
            have he : index + 3 - 2 = index + 1 := by omega
            simpa [show index + 3 ≠ 1 by omega, he] using
              hstartOneCard (index + 3) (by omega)
          have hprevious : Nat.card (Slice (index + 2)) =
              Nat.card (HStart (index + 2)) + Nat.card (Tail (index + 2)) := Nat.card_sum
          have hnext : Nat.card (Slice (index + 3)) =
              Nat.card (HStart (index + 3)) + Nat.card (Tail (index + 3)) := Nat.card_sum
          rw [hpreviousOne] at hprevious
          rw [hnextOne, htailCount] at hnext
          change Nat.card (Slice (index + 3)) + 1 = 2 ^ (index + 2)
          rw [pow_succ]
          omega
    have hzero : Nat.card (BParameters 0) = 0 := by
      let : IsEmpty (BParameters 0) := ⟨fun data => by have := data.1.property; omega⟩
      simp
    have hone : Nat.card (BParameters 1) = 1 := by
      rw [Nat.card_congr (hmaximumSplit 0), Nat.card_sum, hzero, hsliceOne]
    have htotal (index : ℕ) : Nat.card (BParameters (index + 1)) + (index + 1) =
        2 ^ (index + 1) := by
      induction index with
      | zero => simp [hone]
      | succ index ih =>
          have hstep := Nat.card_congr (hmaximumSplit (index + 1))
          rw [Nat.card_sum] at hstep
          change Nat.card (BParameters (index + 2)) =
            Nat.card (BParameters (index + 1)) + Nat.card (Slice (index + 2)) at hstep
          have hsliceStep := hslice index
          change Nat.card (BParameters (index + 2)) + (index + 2) = 2 ^ (index + 2)
          rw [pow_succ]
          omega
    refine ⟨hfinite size, ?_⟩
    obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
    change Nat.card (BParameters (index + 1)) = 2 ^ (index + 1) - (index + 1)
    have := htotal index
    omega
  have hbEquiv (n : ℕ) (hn : 1 ≤ n) :
      {p : List ℕ // p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]} ≃
        BParameters n := by
    have htypeIMem (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (s : HStart m) :
        (List.range' (m + 1) (n - m)).reverse ++ s.val.val ∈
          avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]] := by
      have hfull : ∀ size, m ≤ size →
          ((List.range' (m + 1) (size - m)).reverse ++ s.val.val).Perm
              (List.range' 1 size) ∧
            IsFishburn ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) ∧
            ¬ NonnestingDefs.Occurs [2, 1, 3]
              ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) := by
        intro size
        induction size with
        | zero => omega
        | succ size ih =>
          intro hbound
          by_cases heq : m = size + 1
          · subst m
            simpa [avoiders] using s.val.property
          · have hprev := ih (by omega)
            have hword : (List.range' (m + 1) (size + 1 - m)).reverse ++ s.val.val =
                (size + 1) :: ((List.range' (m + 1) (size - m)).reverse ++ s.val.val) := by
              rw [show size + 1 - m = size - m + 1 by omega, List.range'_concat]
              simp [List.reverse_append, show m + 1 + (size - m) = size + 1 by omega]
            rw [hword]
            simpa [avoiders] using (H_head_decomposition size _).mpr
              ⟨⟨_, by simpa [avoiders] using hprev⟩, Or.inl rfl⟩
      obtain ⟨hperm, hfish, h213⟩ := hfull n hmn
      refine ⟨hperm, hfish, ?_⟩
      have htriple (low middle high : ℕ) (hlm : low < middle) (hmh : middle < high)
          (hsub : [middle, low, high].Sublist
            ((List.range' (m + 1) (n - m)).reverse ++ s.val.val)) : False := by
        apply h213
        change ArrowWilfDefs.Contains [2, 1, 3] [] 3 _
        let values : ℕ → ℕ := fun rank => if rank = 1 then low
          else if rank = 2 then middle else high
        refine ⟨values, ?_, ?_, by simpa [values] using hsub, by simp⟩
        · intro rank hl hh
          have : rank = 1 ∨ rank = 2 := by omega
          rcases this with rfl | rfl <;> simp [values] <;> omega
        · intro rank hl hh
          have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases this with rfl | rfl | rfl <;>
            simp only [values, ↓reduceIte, Nat.reduceEqDiff] <;> apply hsub.subset <;> simp
      intro pattern hpattern hoccurs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
        apply htriple (values 2) (values 3) (values 4)
          (hstep 2 (by omega) (by change 2 < 4; omega))
          (hstep 3 (by omega) (by change 3 < 4; omega))
        have ht : [3, 2, 4].Sublist [1, 3, 2, 4] := by decide
        simpa using (ht.map values).trans hsub
      · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
        apply htriple (values 1) (values 2) (values 4)
          (hstep 1 (by omega) (by change 1 < 4; omega)) (by
            have h23 : values 2 < values 3 := hstep 2 (by omega) (by change 2 < 4; omega)
            have h34 : values 3 < values 4 := hstep 3 (by omega) (by change 3 < 4; omega)
            omega)
        have ht : [2, 1, 4].Sublist [2, 1, 4, 3] := by decide
        simpa using (ht.map values).trans hsub
      · obtain ⟨values, hstep, _, hsub, _⟩ := hoccurs
        apply htriple (values 1) (values 3) (values 4) (by
            have h12 : values 1 < values 2 := hstep 1 (by omega) (by change 1 < 4; omega)
            have h23 : values 2 < values 3 := hstep 2 (by omega) (by change 2 < 4; omega)
            omega) (hstep 3 (by omega) (by change 3 < 4; omega))
        have ht : [3, 1, 4].Sublist [3, 1, 2, 4] := by decide
        simpa using (ht.map values).trans hsub
    let initial (code : BParameters n) : List ℕ :=
      (List.range' (code.1.val + 1) (n - code.1.val)).reverse ++
        match code.2 with
        | Sum.inl _ => []
        | Sum.inr data => (List.range' data.1.val (data.2.1.val + 1 - data.1.val)).reverse
    let suffix (code : BParameters n) : List ℕ :=
      match code.2 with
      | Sum.inl s => s.val.val
      | Sum.inr data => 1 :: (List.range' (data.2.1.val + 1)
          (code.1.val - data.2.1.val - 1) ++ code.1.val :: data.2.2.val.map (· + 1))
    let word (code : BParameters n) := initial code ++ suffix code
    have hwordMem (code : BParameters n) :
        word code ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]] := by
      rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩
      · simpa [word, initial, suffix] using
          htypeIMem n maximum.val maximum.property.1 maximum.property.2 s
      · simpa [word, initial, suffix, List.append_assoc] using
          B_typeII_mem n maximum.val low.val high.val low.property.1 high.property.1
            high.property.2 maximum.property.2 q
    have hspec (code : BParameters n) : (suffix code).head? = some 1 ∧
        code.1.val ∈ suffix code ∧ ∀ value ∈ suffix code, value ≤ code.1.val := by
      rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩
      · refine ⟨s.property, ?_, ?_⟩
        · apply s.val.property.1.mem_iff.mpr
          simp only [List.mem_range'_1]
          omega
        · intro value hv
          change value ≤ maximum.val
          have := s.val.property.1.mem_iff.mp hv
          simp only [List.mem_range'_1] at this
          omega
      · refine ⟨by simp [suffix], by simp [suffix], ?_⟩
        intro value hv
        change value ≤ maximum.val
        simp only [suffix, List.mem_cons, List.mem_append, List.mem_map] at hv
        rcases hv with rfl | hv | rfl | ⟨old, hold, rfl⟩
        · exact maximum.property.1
        · obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hv
          simp only [Nat.one_mul] at *
          have := high.property.2
          omega
        · exact le_rfl
        · have := q.property.1.mem_iff.mp hold
          simp only [List.mem_range'_1] at this
          have := low.property.2
          omega
    have hnotOne (code : BParameters n) : 1 ∉ initial code := by
      rcases code with ⟨maximum, s | ⟨low, high, q⟩⟩ <;>
        simp only [initial, List.mem_append, List.mem_reverse, List.not_mem_nil, or_false,
          List.mem_range', Nat.one_mul]
      · rintro ⟨offset, _, heq⟩
        have := maximum.property.1
        omega
      · rintro (⟨offset, _, heq⟩ | ⟨offset, _, heq⟩)
        · have := maximum.property.1
          omega
        · have := low.property.1
          omega
    have hindex (code : BParameters n) : (word code).idxOf 1 = (initial code).length := by
      obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp (hspec code).1
      dsimp only [word]
      rw [List.idxOf_append, if_neg (hnotOne code), htail]
      simp
    have hinterval (low high value : ℕ) (hle : low ≤ high) :
        value ∈ (List.range' low (high + 1 - low)).reverse ↔
          low ≤ value ∧ value ≤ high := by
      simp only [List.mem_reverse, List.mem_range', Nat.one_mul]
      constructor
      · rintro ⟨offset, hoffset, rfl⟩
        omega
      · rintro ⟨hlo, hhi⟩
        exact ⟨value - low, by omega, by omega⟩
    have hinjective : Function.Injective word := by
      intro first second heq
      have hlength : (initial first).length = (initial second).length := by
        rw [← hindex first, ← hindex second, heq]
      obtain ⟨hprefix, hsuffix⟩ := List.append_inj heq hlength
      have hfirstMem := (hspec first).2.1
      have hsecondMem := (hspec second).2.1
      rw [hsuffix] at hfirstMem
      rw [← hsuffix] at hsecondMem
      have hle := (hspec second).2.2 _ hfirstMem
      have hge := (hspec first).2.2 _ hsecondMem
      rcases first with ⟨maximum, body⟩
      rcases second with ⟨maximum', body'⟩
      have hmaximum : maximum = maximum' := Subtype.ext (by simpa using Nat.le_antisymm hle hge)
      subst maximum'
      have hbody : body = body' := by
        rcases body with s | ⟨low, high, q⟩ <;> rcases body' with s' | ⟨low', high', q'⟩
        · apply congrArg Sum.inl
          apply Subtype.ext
          apply Subtype.ext
          exact hsuffix
        · simp only [initial, List.length_append, List.length_reverse,
            List.length_range', List.length_nil, Nat.add_zero] at hlength
          have := high'.property.1
          omega
        · simp only [initial, List.length_append, List.length_reverse,
            List.length_range', List.length_nil, Nat.add_zero] at hlength
          have := high.property.1
          omega
        · have hblocks : (List.range' low.val (high.val + 1 - low.val)).reverse =
              (List.range' low'.val (high'.val + 1 - low'.val)).reverse := by
            exact List.append_cancel_left hprefix
          have hlow : low.val ∈ (List.range' low.val (high.val + 1 - low.val)).reverse :=
            (hinterval _ _ _ high.property.1).mpr ⟨le_rfl, high.property.1⟩
          have hlow' : low'.val ∈
              (List.range' low'.val (high'.val + 1 - low'.val)).reverse :=
            (hinterval _ _ _ high'.property.1).mpr ⟨le_rfl, high'.property.1⟩
          rw [hblocks] at hlow
          rw [← hblocks] at hlow'
          have hbound := (hinterval _ _ _ high'.property.1).mp hlow
          have hbound' := (hinterval _ _ _ high.property.1).mp hlow'
          have hloweq : low = low' := Subtype.ext (by omega)
          subst low'
          have hhigh : high.val ∈ (List.range' low.val (high.val + 1 - low.val)).reverse :=
            (hinterval _ _ _ high.property.1).mpr ⟨high.property.1, le_rfl⟩
          have hhigh' : high'.val ∈
              (List.range' low.val (high'.val + 1 - low.val)).reverse :=
            (hinterval _ _ _ high'.property.1).mpr ⟨high'.property.1, le_rfl⟩
          rw [hblocks] at hhigh
          rw [← hblocks] at hhigh'
          have hbound := (hinterval _ _ _ high'.property.1).mp hhigh
          have hbound' := (hinterval _ _ _ high.property.1).mp hhigh'
          have hhigheq : high = high' := Subtype.ext (by omega)
          subst high'
          have htail := (List.cons.inj hsuffix).2
          have hpeak := List.append_cancel_left htail
          have hshift := (List.cons.inj hpeak).2
          have hq : q = q' := by
            apply Subtype.ext
            have ht := congrArg (List.map (· - 1)) hshift
            simpa [List.map_map, Function.comp_def] using ht
          subst q'
          rfl
      exact congrArg (Sigma.mk maximum) hbody
    have hexists (p : {p : List ℕ //
        p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :
        ∃ code : BParameters n, word code = p.val := by
      obtain ⟨maximum, hpositive, hbound, hform⟩ := B_interval_normalForm n p.val hn p.property
      rcases hform with ⟨s, hhead, heq⟩ | ⟨low, high, hlo, hlh, hhm, q, heq⟩
      · refine ⟨⟨⟨maximum, hpositive, hbound⟩, Sum.inl ⟨s, hhead⟩⟩, ?_⟩
        simpa [word, initial, suffix] using heq.symm
      · refine ⟨⟨⟨maximum, hpositive, hbound⟩,
          Sum.inr ⟨⟨low, hlo, by change low < maximum; omega⟩,
            ⟨high, hlh, hhm⟩, q⟩⟩, ?_⟩
        simpa [word, initial, suffix, List.append_assoc] using heq.symm
    let encode (p : {p : List ℕ //
        p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :=
      Classical.choose (hexists p)
    have hencode (p : {p : List ℕ //
        p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]}) :
        word (encode p) = p.val := Classical.choose_spec (hexists p)
    refine
      { toFun := encode
        invFun := fun code => ⟨word code, hwordMem code⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro p
      exact Subtype.ext (hencode p)
    · intro code
      exact hinjective (hencode ⟨word code, hwordMem code⟩)
  have hwordcounts (size : ℕ) :
      (languageA size).Finite ∧ (languageC size).Finite ∧
      (languageA size).ncard = 2 ^ (size + 1) - 1 ∧
      (languageC size).ncard = 2 ^ (size + 1) - 1 := by
    let binary (length : ℕ) : Set (List Letter) :=
      {word | word.length = length ∧ j ∉ word}
    let run (length : ℕ) : Set (List Letter) :=
      {word | j :: word ∈ languageA (length + 1)}
    have hbinary_valid (word : List Letter) (hword : j ∉ word) :
        word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before j d word := by
      induction word with
      | nil => simp [Before]
      | cons letter tail ih =>
        have hletter : letter ≠ j := by
          intro heq
          exact hword (by simp [heq])
        have htail : j ∉ tail := fun hmem => hword (List.mem_cons_of_mem _ hmem)
        rcases ih htail with ⟨hchain, hbefore⟩
        refine ⟨hchain.cons (fun _ _ => Or.inl hletter), ?_⟩
        exact List.pairwise_cons.mpr
          ⟨fun next hnext => Or.inr (fun heq => htail (heq ▸ hnext)), hbefore⟩
    have hi (length : ℕ) (word : List Letter) :
        i :: word ∈ languageA (length + 1) ↔ word ∈ languageA length := by
      cases word with
      | nil => simp [languageA, Before, eq_comm]
      | cons letter tail =>
        simp [languageA, Before, List.pairwise_cons, List.isChain_cons_cons]
    have hd (length : ℕ) (word : List Letter) :
        d :: word ∈ languageA (length + 1) ↔ word ∈ binary length := by
      change ((d :: word).length = length + 1 ∧
        (d :: word).IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧
        Before j d (d :: word)) ↔ word.length = length ∧ j ∉ word
      constructor
      · rintro ⟨hlen, _, hbefore⟩
        refine ⟨by simpa using hlen, ?_⟩
        intro hmem
        have hrel := (List.pairwise_cons.mp hbefore).1 j hmem
        simp at hrel
      · rintro ⟨hlen, hnot⟩
        rcases hbinary_valid word hnot with ⟨hchain, hbefore⟩
        refine ⟨by simpa using hlen, hchain.cons (fun _ _ => Or.inl (by decide)), ?_⟩
        exact List.pairwise_cons.mpr
          ⟨fun next hnext => Or.inr (fun heq => hnot (heq ▸ hnext)), hbefore⟩
    have hj (length : ℕ) (word : List Letter) :
        j :: word ∈ languageA (length + 1) ↔
          word ∈ languageA length ∧ word.head? ≠ some i := by
      cases word with
      | nil => simp [languageA, Before, eq_comm]
      | cons letter tail =>
        cases letter <;>
          simp [languageA, Before, List.pairwise_cons, List.isChain_cons_cons]
    have hbinary_step (length : ℕ) :
        binary (length + 1) =
          List.cons d '' binary length ∪ List.cons i '' binary length := by
      ext word
      cases word with
      | nil => simp [binary]
      | cons letter tail => cases letter <;> simp [binary]
    have hrun_step (length : ℕ) :
        run (length + 1) =
          List.cons d '' binary length ∪ List.cons j '' run length := by
      ext word
      change (j :: word ∈ languageA ((length + 1) + 1)) ↔ _
      rw [hj]
      cases word with
      | nil => simp [languageA]
      | cons letter tail => cases letter <;> simp [hi, hd, run]
    have hlanguage_step (length : ℕ) :
        languageA (length + 1) = List.cons i '' languageA length ∪
          (List.cons d '' binary length ∪ List.cons j '' run length) := by
      ext word
      cases word with
      | nil => simp [languageA]
      | cons letter tail => cases letter <;> simp [hi, hd, run]
    have hdisjoint (left right : Letter) (hne : left ≠ right)
        (source target : Set (List Letter)) :
        Disjoint (List.cons left '' source) (List.cons right '' target) := by
      rw [Set.disjoint_left]
      rintro _ ⟨first, _, rfl⟩ ⟨second, _, heq⟩
      exact hne (List.cons.inj heq).1.symm
    have hcard_cons (letter : Letter) (source : Set (List Letter)) :
        (List.cons letter '' source).ncard = source.ncard :=
      Set.ncard_image_of_injective source (fun _ _ heq => (List.cons.inj heq).2)
    have hzero : binary 0 = {[]} ∧ run 0 = {[]} ∧ languageA 0 = {[]} := by
      constructor
      · ext word
        cases word <;> simp [binary]
      constructor
      · ext word
        cases word <;> simp [run, languageA, Before]
      · ext word
        cases word <;> simp [languageA, Before]
    have hinduction (length : ℕ) :
        (binary length).Finite ∧ (run length).Finite ∧ (languageA length).Finite ∧
        (binary length).ncard = 2 ^ length ∧ (run length).ncard = 2 ^ length ∧
        (languageA length).ncard = 2 ^ (length + 1) - 1 := by
      induction length with
      | zero => simp [hzero.1, hzero.2.1, hzero.2.2]
      | succ length ih =>
        rcases ih with ⟨hbinary, hrun, hlanguage, hbinary_count, hrun_count, hlanguage_count⟩
        have hdb := hbinary.image (List.cons d)
        have hib := hbinary.image (List.cons i)
        have hjr := hrun.image (List.cons j)
        have hia := hlanguage.image (List.cons i)
        have hd_i := hdisjoint d i (by decide) (binary length) (binary length)
        have hd_j := hdisjoint d j (by decide) (binary length) (run length)
        have hi_rest : Disjoint (List.cons i '' languageA length)
            (List.cons d '' binary length ∪ List.cons j '' run length) := by
          exact Set.disjoint_union_right.mpr
            ⟨hdisjoint i d (by decide) _ _, hdisjoint i j (by decide) _ _⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hbinary_step]
          exact hdb.union hib
        · rw [hrun_step]
          exact hdb.union hjr
        · rw [hlanguage_step]
          exact hia.union (hdb.union hjr)
        · rw [hbinary_step, Set.ncard_union_eq hd_i hdb hib, hcard_cons, hcard_cons,
            hbinary_count, Nat.pow_succ]
          omega
        · rw [hrun_step, Set.ncard_union_eq hd_j hdb hjr, hcard_cons, hcard_cons,
            hbinary_count, hrun_count, Nat.pow_succ]
          omega
        · rw [hlanguage_step, Set.ncard_union_eq hi_rest hia (hdb.union hjr),
            Set.ncard_union_eq hd_j hdb hjr, hcard_cons, hcard_cons, hcard_cons,
            hlanguage_count, hbinary_count, hrun_count]
          have hpositive := Nat.two_pow_pos (length + 1)
          simp only [Nat.pow_succ] at hpositive ⊢
          omega
    rcases hinduction size with ⟨_, _, hfinite, _, _, hcount⟩
    have hinverse : Function.Involutive phi := by
      have hswap (letter : Letter) : swap (swap letter) = letter := by
        cases letter <;> rfl
      intro word
      simp [phi, List.map_map, Function.comp_def, hswap]
    have hforward (word : List Letter) :
        word ∈ languageA size ↔ phi word ∈ languageC size := by
      have hchain (left right : Letter) :
          (swap right ≠ j ∨ swap left ≠ i) ↔ (left ≠ j ∨ right ≠ i) := by
        cases left <;> cases right <;> simp [swap]
      have horder (left right : Letter) :
          (swap right ≠ i ∨ swap left ≠ d) ↔ (left ≠ d ∨ right ≠ j) := by
        cases left <;> cases right <;> simp [swap]
      simp only [languageA, languageC, Set.mem_ofPred_eq, phi, List.length_reverse,
        List.length_map, List.isChain_reverse, List.isChain_map, Before,
        List.pairwise_reverse, List.pairwise_map]
      simp_rw [hchain, horder]
    let correspondence : languageA size ≃ languageC size :=
      { toFun := fun word => ⟨phi word.val, (hforward word.val).mp word.property⟩
        invFun := fun word => ⟨phi word.val, (hforward (phi word.val)).mpr
          (by simpa only [hinverse word.val] using word.property)⟩
        left_inv := fun word => Subtype.ext (hinverse word.val)
        right_inv := fun word => Subtype.ext (hinverse word.val) }
    have himage : phi '' languageA size = languageC size := by
      ext word
      constructor
      · rintro ⟨original, horiginal, rfl⟩
        exact hforward original |>.mp horiginal
      · intro hword
        refine ⟨phi word, ?_, hinverse word⟩
        apply (hforward (phi word)).mpr
        simpa only [hinverse word] using hword
    refine ⟨hfinite, ?_, hcount, ?_⟩
    · rw [← himage]
      exact hfinite.image phi
    · rw [← Set.ncard_congr' correspondence]
      exact hcount
  have hac_count (third : Bool) (size : ℕ) (hsize : 1 ≤ size) :
      Nat.card (ACParameters third size) = 2 ^ size - size := by
    let language (length : ℕ) := if third then languageC length else languageA length
    have hwords (length : ℕ) :
        (language length).Finite ∧ (language length).ncard = 2 ^ (length + 1) - 1 := by
      cases third
      · exact ⟨(hwordcounts length).1, (hwordcounts length).2.2.1⟩
      · exact ⟨(hwordcounts length).2.1, (hwordcounts length).2.2.2⟩
    let (length : ℕ) : Finite (language length) := (hwords length).1.to_subtype
    let (total : ℕ) : Finite {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ total} :=
      (Set.finite_Icc 2 total).to_subtype
    let (total : ℕ) : Fintype {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ total} :=
      Fintype.ofFinite _
    let codes : (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
        language (maximum.val - 2)) ≃ Σ index : Fin (size - 1), language index.val := by
      refine
        { toFun := fun ⟨maximum, word⟩ =>
            ⟨⟨maximum.val - 2, by have := maximum.property; omega⟩, word⟩
          invFun := fun ⟨index, word⟩ =>
            ⟨⟨index.val + 2, by have := index.is_lt; omega⟩,
              ⟨word.val, by simpa only [Nat.add_sub_cancel_right] using word.property⟩⟩
          left_inv := ?_
          right_inv := ?_ }
      · rintro ⟨⟨maximum, hmaximum⟩, ⟨word, hword⟩⟩
        dsimp only
        refine Sigma.ext (Subtype.ext (by dsimp; omega)) ?_
        exact (Subtype.heq_iff_coe_eq (fun candidate => by
          simp only [Nat.add_sub_cancel_right])).mpr rfl
      · rintro ⟨⟨index, hindex⟩, ⟨word, hword⟩⟩
        dsimp only
        refine Sigma.ext (Fin.ext (by dsimp; omega)) ?_
        exact (Subtype.heq_iff_coe_eq (fun candidate => by
          simp only [Nat.add_sub_cancel_right])).mpr rfl
    have hcount (length : ℕ) :
        (∑ index ∈ Finset.range length, (2 ^ (index + 1) - 1)) + length + 2 =
          2 ^ (length + 1) := by
      induction length with
      | zero => simp
      | succ length ih =>
        rw [Finset.sum_range_succ]
        have hpositive := Nat.two_pow_pos (length + 1)
        have hpower : 2 ^ (length + 1 + 1) = 2 ^ (length + 1) * 2 := Nat.pow_succ _ _
        omega
    have hcard :
        Nat.card (Unit ⊕ (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
          language (maximum.val - 2))) =
        1 + ∑ index ∈ Finset.range (size - 1), (2 ^ (index + 1) - 1) := by
      rw [Nat.card_sum, Nat.card_unique, Nat.card_congr codes, Nat.card_sigma]
      simp_rw [Nat.card_coe_set_eq, (hwords _).2]
      rw [Fin.sum_univ_eq_sum_range (fun index : ℕ => 2 ^ (index + 1) - 1) (size - 1)]
    have hsum := hcount (size - 1)
    have hexponent : size - 1 + 1 = size := by omega
    rw [hexponent] at hsum
    change Nat.card (Unit ⊕ (Σ maximum : {maximum : ℕ // 2 ≤ maximum ∧ maximum ≤ size},
      language (maximum.val - 2))) = _
    omega
  intro size hsize
  obtain ⟨firstCorrespondence, _, _⟩ := ac_equivalence false size hsize
  obtain ⟨thirdCorrespondence, _, _⟩ := ac_equivalence true size hsize
  have hfirst :
      (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]) = _
    exact (Nat.card_congr firstCorrespondence).trans (hac_count false size hsize)
  have hsecond :
      (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]) = _
    exact (Nat.card_congr (hbEquiv size hsize)).trans
      (hbCount size hsize).2
  have hthird :
      (avoiders size [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]]).ncard =
        2 ^ size - size := by
    change Nat.card (avoiders size [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]]) = _
    exact (Nat.card_congr thirdCorrespondence).trans (hac_count true size hsize)
  exact ⟨hfirst, hsecond, hthird⟩

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSeven
