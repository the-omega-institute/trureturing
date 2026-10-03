/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenACount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenACount
   mirror-E: none(waiver:fishburn-a-positive-cut-counting-bijection)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Unique live addresses bijectively count the positive maximum-insertion cuts of A. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenAAddresses
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenACount

open D5.S3.Combinatorics Nonnesting FishburnDefs
open FishburnTenTenAMonotone FishburnTenTenALayered FishburnTenTenAValley
open FishburnTenTenAAddresses

set_option maxHeartbeats 2400000 in
theorem a_positive_cut_count (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {entry : List ℕ × ℕ //
      entry.1 ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
      0 < entry.2 ∧ entry.2 ≤ n ∧ entry.1.insertIdx entry.2 (n + 1) ∈
        avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]} =
      1 + 2 * n.choose 2 := by
  classical
  let layered := fun pair : ℕ × ℕ =>
    List.range' 1 pair.1 ++ (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++
      List.range' (pair.2 + 1) (n - pair.2)
  let valley := fun pair : ℕ × ℕ =>
    (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++ [1] ++
      List.range' (pair.2 + 1) (n - pair.2) ++ (List.range' 2 (pair.1 - 1)).reverse
  let Layer := {pair : ℕ × ℕ // pair.1 + 2 ≤ pair.2 ∧ pair.2 ≤ n}
  let Valley := {pair : ℕ × ℕ // 2 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n}
  let Address := Unit ⊕ (Layer ⊕ Valley)
  let decode : Address → List ℕ := fun entry =>
    match entry with
    | .inl _ => List.range' 1 n
    | .inr (.inl pair) => layered pair.val
    | .inr (.inr pair) => valley pair.val
  have hinj : Function.Injective decode := by
    intro first second heq
    apply (a_live_addresses n hn).1
    rcases first with first | (first | first) <;>
      rcases second with second | (second | second) <;> exact heq
  have hcover (p : List ℕ) :
      (p ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
        ∃ site, 0 < site ∧ site ≤ n ∧ p.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]) ↔
        p ∈ Set.range decode := by
    constructor
    · intro hp
      obtain ⟨entry, heq⟩ := ((a_live_addresses n hn).2 p).mp hp
      refine ⟨entry, ?_⟩
      cases entry with
      | inl entry => exact heq
      | inr entry => cases entry <;> exact heq
    · rintro ⟨entry, heq⟩
      apply ((a_live_addresses n hn).2 p).mpr
      refine ⟨entry, ?_⟩
      cases entry with
      | inl entry => exact heq
      | inr entry => cases entry <;> exact heq
  let Extra := Fin 2 ⊕ (Layer ⊕ (Fin (n - 2) ⊕ Valley))
  let key : Extra → Address := fun entry =>
    match entry with
    | .inl _ => .inl ()
    | .inr (.inl pair) => .inr (.inl pair)
    | .inr (.inr (.inl cut)) => .inr (.inl ⟨(cut.val + 1, n), by
        have := cut.is_lt
        exact ⟨by omega, le_rfl⟩⟩)
    | .inr (.inr (.inr pair)) => .inr (.inr pair)
  let slot : Extra → ℕ := fun entry =>
    match entry with
    | .inl index => if index.val = 0 then n else n - 1
    | .inr (.inl _) => n
    | .inr (.inr (.inl cut)) => cut.val + 1
    | .inr (.inr (.inr pair)) => n - pair.val.1 + 1
  let Entries := {entry : List ℕ × ℕ //
    entry.1 ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
    0 < entry.2 ∧ entry.2 ≤ n ∧ entry.1.insertIdx entry.2 (n + 1) ∈
      avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]}
  have hvalid (entry : Extra) :
      decode (key entry) ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
      0 < slot entry ∧ slot entry ≤ n ∧
      (decode (key entry)).insertIdx (slot entry) (n + 1) ∈
        avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
    cases entry with
    | inl index =>
      dsimp only [decode, key, slot]
      refine ⟨(a_monotone_forms n).1, ?_, ?_, ?_⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · apply ((a_monotone_forms n).2.2 _ (by split_ifs <;> omega)).1.mpr
        right
        split_ifs <;> omega
    | inr entry =>
      cases entry with
      | inl pair =>
        have hh := a_layered_forms n pair.val.1 pair.val.2 pair.property.1 pair.property.2
        exact ⟨hh.1, by dsimp [slot]; omega, le_rfl,
          (hh.2 n le_rfl).mpr (Or.inr (Or.inl rfl))⟩
      | inr entry =>
        cases entry with
        | inl cut =>
          have hc := cut.is_lt
          have hh := a_layered_forms n (cut.val + 1) n (by omega) le_rfl
          exact ⟨hh.1, by dsimp [slot]; omega, by dsimp [slot]; omega,
            (hh.2 (cut.val + 1) (by omega)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        | inr pair =>
          have hh := a_valley_forms n pair.val.1 pair.val.2 pair.property.1
            pair.property.2.1 pair.property.2.2
          exact ⟨hh.1, by dsimp [slot]; omega, by dsimp [slot]; omega,
            (hh.2 (n - pair.val.1 + 1) (by have := pair.property; omega)).mpr
              (Or.inr rfl)⟩
  let build : Extra → Entries := fun entry => ⟨(decode (key entry), slot entry), hvalid entry⟩
  have hbuild : Function.Bijective build := by
    constructor
    · intro first second heq
      have hkey : key first = key second := hinj
        (congrArg (fun entry : Entries => entry.val.1) heq)
      have hslot : slot first = slot second :=
        congrArg (fun entry : Entries => entry.val.2) heq
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          congr 1
          apply Fin.ext
          have hf := first.is_lt
          have hs := second.is_lt
          dsimp [slot] at hslot
          split_ifs at hslot <;> omega
        | inr second =>
          cases second with
          | inl second => cases hkey
          | inr second => cases second <;> cases hkey
      | inr first =>
        cases first with
        | inl first =>
          cases second with
          | inl second => cases hkey
          | inr second =>
            cases second with
            | inl second =>
              have hh : first = second := Sum.inl.inj (Sum.inr.inj hkey)
              subst second
              rfl
            | inr second =>
              cases second with
              | inl second =>
                have hs := second.is_lt
                dsimp [slot] at hslot
                omega
              | inr second => cases hkey
        | inr first =>
          cases first with
          | inl first =>
            cases second with
            | inl second => cases hkey
            | inr second =>
              cases second with
              | inl second =>
                have hf := first.is_lt
                dsimp [slot] at hslot
                omega
              | inr second =>
                cases second with
                | inl second =>
                  congr 3
                  apply Fin.ext
                  dsimp [slot] at hslot
                  omega
                | inr second => cases hkey
          | inr first =>
            cases second with
            | inl second => cases hkey
            | inr second =>
              cases second with
              | inl second => cases hkey
              | inr second =>
                cases second with
                | inl second => cases hkey
                | inr second =>
                  have hh : first = second := Sum.inr.inj (Sum.inr.inj hkey)
                  subst second
                  rfl
    · intro entry
      obtain ⟨label, heq⟩ := (hcover entry.val.1).mp
        ⟨entry.property.1, entry.val.2, entry.property.2⟩
      have hs := entry.property.2.1
      have hb := entry.property.2.2.1
      have ha := entry.property.2.2.2
      rw [← heq] at ha
      cases label with
      | inl label =>
        have hcuts := ((a_monotone_forms n).2.2 entry.val.2 hb).1.mp ha
        by_cases hend : entry.val.2 = n
        · refine ⟨.inl 0, ?_⟩
          apply Subtype.ext
          exact Prod.ext heq (by simpa [build, slot] using hend.symm)
        · have hcut : entry.val.2 = n - 1 := by rcases hcuts with hz | he <;> omega
          refine ⟨.inl 1, ?_⟩
          apply Subtype.ext
          exact Prod.ext heq (by simpa [build, slot] using hcut.symm)
      | inr label =>
        cases label with
        | inl pair =>
          have hcuts := (a_layered_forms n pair.val.1 pair.val.2 pair.property.1
            pair.property.2).2 entry.val.2 hb |>.mp ha
          rcases hcuts with hzero | hend | ⟨hhigh, hlow⟩
          · omega
          · refine ⟨.inr (.inl pair), ?_⟩
            apply Subtype.ext
            exact Prod.ext heq hend.symm
          · have hpositive : 0 < pair.val.1 := by omega
            let cut : Fin (n - 2) := ⟨pair.val.1 - 1, by have := pair.property.1; omega⟩
            refine ⟨.inr (.inr (.inl cut)), ?_⟩
            apply Subtype.ext
            have hp : (cut.val + 1, n) = pair.val := by
              apply Prod.ext <;> dsimp [cut] <;> omega
            change (layered (cut.val + 1, n), cut.val + 1) = entry.val
            apply Prod.ext
            · rw [hp]
              exact heq
            · dsimp [cut]
              omega
        | inr pair =>
          have hcuts := (a_valley_forms n pair.val.1 pair.val.2 pair.property.1
            pair.property.2.1 pair.property.2.2).2 entry.val.2 hb |>.mp ha
          have hcut : entry.val.2 = n - pair.val.1 + 1 := by
            rcases hcuts with hz | he <;> omega
          refine ⟨.inr (.inr (.inr pair)), ?_⟩
          apply Subtype.ext
          exact Prod.ext heq hcut.symm
  let layerCode : (Σ upper : Fin (n - 1), Fin (upper.val + 1)) → Layer := fun code =>
    ⟨(code.2.val, code.1.val + 2), by
      have := code.1.is_lt
      have := code.2.is_lt
      exact ⟨by omega, by omega⟩⟩
  have hlayerCode : Function.Bijective layerCode := by
    constructor
    · intro first second heq
      have hpair := congrArg Subtype.val heq
      have hupper : first.1 = second.1 := by
        apply Fin.ext
        have := congrArg Prod.snd hpair
        dsimp [layerCode] at this
        omega
      cases first with
      | mk upper lower =>
        cases second with
        | mk upper' lower' =>
          dsimp only at hupper
          subst upper'
          congr 1
          apply Fin.ext
          exact congrArg Prod.fst hpair
    · intro pair
      let upper : Fin (n - 1) := ⟨pair.val.2 - 2, by have := pair.property; omega⟩
      let lower : Fin (upper.val + 1) := ⟨pair.val.1, by
        dsimp [upper]
        have := pair.property
        omega⟩
      refine ⟨⟨upper, lower⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · dsimp [layerCode, upper]
        have := pair.property
        omega
  let valleyCode : (Σ upper : Fin (n - 2), Fin (upper.val + 1)) → Valley := fun code =>
    ⟨(code.2.val + 2, code.1.val + 3), by
      have := code.1.is_lt
      have := code.2.is_lt
      exact ⟨by omega, by omega, by omega⟩⟩
  have hvalleyCode : Function.Bijective valleyCode := by
    constructor
    · intro first second heq
      have hpair := congrArg Subtype.val heq
      have hupper : first.1 = second.1 := by
        apply Fin.ext
        have := congrArg Prod.snd hpair
        dsimp [valleyCode] at this
        omega
      cases first with
      | mk upper lower =>
        cases second with
        | mk upper' lower' =>
          dsimp only at hupper
          subst upper'
          congr 1
          apply Fin.ext
          have := congrArg Prod.fst hpair
          dsimp [valleyCode] at this
          omega
    · intro pair
      let upper : Fin (n - 2) := ⟨pair.val.2 - 3, by have := pair.property; omega⟩
      let lower : Fin (upper.val + 1) := ⟨pair.val.1 - 2, by
        dsimp [upper]
        have := pair.property
        omega⟩
      refine ⟨⟨upper, lower⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> dsimp [valleyCode, upper, lower] <;>
        have := pair.property <;> omega
  letI : Finite Layer := Finite.of_surjective layerCode hlayerCode.2
  letI : Finite Valley := Finite.of_surjective valleyCode hvalleyCode.2
  have htri (size : ℕ) : Nat.card (Σ upper : Fin size, Fin (upper.val + 1)) =
      (size + 1).choose 2 := by
    rw [Nat.card_sigma]
    simp only [Nat.card_fin]
    change (∑ upper : Fin size, (fun index : ℕ => index + 1) upper.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun index : ℕ => index + 1) size]
    cases size with
    | zero => simp
    | succ size =>
      have hh := Nat.sum_range_add_choose size 1
      simpa only [Nat.choose_one_right, Nat.reduceAdd, Nat.succ_eq_add_one,
        Nat.add_assoc] using hh
  have hcl : Nat.card Layer = n.choose 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective layerCode hlayerCode), htri]
    congr 1
    omega
  have hcv : Nat.card Valley = (n - 1).choose 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective valleyCode hvalleyCode), htri]
    congr 1
    omega
  have hcard : Nat.card Entries = 2 + n.choose 2 + (n - 2) + (n - 1).choose 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective build hbuild)]
    dsimp only [Extra]
    rw [Nat.card_sum, Nat.card_sum, Nat.card_sum, Nat.card_fin, Nat.card_fin, hcl, hcv]
    omega
  change Nat.card Entries = _
  rw [hcard]
  have hpascal := Nat.choose_succ_succ (n - 1) 1
  change (n - 1 + 1).choose 2 = (n - 1).choose 1 + (n - 1).choose 2 at hpascal
  have hnext : n - 1 + 1 = n := by omega
  rw [hnext, Nat.choose_one_right] at hpascal
  omega

end D5.S3.Combinatorics.Fishburn.FishburnTenTenACount
