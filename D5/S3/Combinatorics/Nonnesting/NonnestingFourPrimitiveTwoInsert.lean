/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoInsert
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoInsert
   mirror-E: none(waiver:row-four-two-first-construction)
   anchors: []
   utility: none
   digest: Inserts a fixed two-first prefix around an increasing tail. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount

theorem two_insert (r : List ℕ) (m : ℕ)
    (hv : (1 :: r) ∈ NonnestingDefs.avoiders m
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]) :
    (2 :: 1 :: 3 :: 2 :: 1 :: shift 2 r) ∈
      NonnestingDefs.avoiders (m + 2)
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
  let v := 1 :: r
  let w := 2 :: 1 :: 3 :: 2 :: 1 :: shift 2 r
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hperm0 := directSum_perm 2 m [1, 1, 2, 2] v (by decide) hv.1
  have hperm : w.Perm ((List.range' 1 (m + 2)).flatMap fun i => [i, i]) := by
    have hswap : w.Perm (1 :: 1 :: 2 :: 2 :: 3 :: shift 2 r) := by
      exact (show [2, 1, 3, 2, 1].Perm [1, 1, 2, 2, 3] by decide).append_right _
    have hbase : (1 :: 1 :: 2 :: 2 :: 3 :: shift 2 r).Perm
        ((List.range' 1 (m + 2)).flatMap fun i => [i, i]) := by
      simpa [directSum, shift, v, Nat.add_comm] using hperm0
    exact hswap.trans hbase
  have hpositive : ∀ x ∈ r, 1 ≤ x := by
    intro x hx
    have hxv : x ∈ v := by simp [v, hx]
    have hxbase := hv.1.mem_iff.mp hxv
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hshiftPos : ∀ x ∈ shift 2 r, 3 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := hpositive y hy
    omega
  have hposition (p x : ℕ) (hp : w[p]? = some x) :
      (p = 0 ∧ x = 2) ∨ (p = 1 ∧ x = 1) ∨
      (p = 2 ∧ x = 3) ∨ (p = 3 ∧ x = 2) ∨
      (p = 4 ∧ x = 1) ∨ (5 ≤ p ∧ 3 ≤ x) := by
    by_cases hp0 : p = 0
    · subst p
      simp [w] at hp
      omega
    by_cases hp1 : p = 1
    · subst p
      simp [w] at hp
      omega
    by_cases hp2 : p = 2
    · subst p
      simp [w] at hp
      omega
    by_cases hp3 : p = 3
    · subst p
      simp [w] at hp
      omega
    by_cases hp4 : p = 4
    · subst p
      simp [w] at hp
      omega
    have hpge : 5 ≤ p := by omega
    have heq : p = 5 + (p - 5) := by omega
    rw [heq] at hp
    have hp' : (shift 2 r)[p - 5]? = some x := by
      simpa [w, Nat.add_comm 5 (p - 5)] using hp
    have hxmem : x ∈ shift 2 r := List.mem_of_getElem? hp'
    have hxge := hshiftPos x hxmem
    omega
  have hfour (a b c d : ℕ) (hsub : List.Sublist [a, b, c, d] w) :
      ∃ p₀ p₁ p₂ p₃ : ℕ,
        p₀ < p₁ ∧ p₁ < p₂ ∧ p₂ < p₃ ∧
          w[p₀]? = some a ∧ w[p₁]? = some b ∧
          w[p₂]? = some c ∧ w[p₃]? = some d := by
    obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    refine ⟨(f 0).val, (f 1).val, (f 2).val, (f 3).val,
      (show (f 0).val < (f 1).val from
        f.strictMono (show (0 : Fin 4) < 1 by decide)),
      (show (f 1).val < (f 2).val from
        f.strictMono (show (1 : Fin 4) < 2 by decide)),
      (show (f 2).val < (f 3).val from
        f.strictMono (show (2 : Fin 4) < 3 by decide)),
      ?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem (f 0).isLt]
      simpa using (hf (0 : Fin 4)).symm
    · rw [List.getElem?_eq_getElem (f 1).isLt]
      simpa using (hf (1 : Fin 4)).symm
    · rw [List.getElem?_eq_getElem (f 2).isLt]
      simpa using (hf (2 : Fin 4)).symm
    · rw [List.getElem?_eq_getElem (f 3).isLt]
      simpa using (hf (3 : Fin 4)).symm
  have hfilter : w.filter (fun x => decide (2 < x)) = shift 2 v := by
    have hrFilter : (shift 2 r).filter (fun x => decide (2 < x)) = shift 2 r := by
      apply List.filter_eq_self.mpr
      intro x hx
      have hx2 : 2 < x := by have := hshiftPos x hx; omega
      simp [hx2]
    change (2 :: 1 :: 3 :: 2 :: 1 :: shift 2 r).filter
      (fun x => decide (2 < x)) = 3 :: shift 2 r
    simpa using congrArg (List.cons 3) hrFilter
  have hnoLow (σ : List ℕ)
      (hσ : σ ∈ [[1, 2, 2, 1], [2, 1, 1, 2],
        [1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (x : ℕ → ℕ) (hx1 : x 1 ≤ 2)
      (hx12 : x 1 < x 2)
      (hx23 : NonnestingDefs.letters σ = 3 → x 2 < x 3)
      (hsub : List.Sublist (σ.map x) w) : False := by
    have hcases : σ = [1, 2, 2, 1] ∨ σ = [2, 1, 1, 2] ∨
        σ = [1, 2, 3, 1] ∨ σ = [1, 3, 1, 2] ∨
        σ = [2, 2, 3, 1] ∨ σ = [3, 2, 2, 1] := by
      simpa using hσ
    rcases hcases with h | h | h | h | h | h
    all_goals subst σ
    all_goals
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, h23,
        hp₀, hp₁, hp₂, hp₃⟩ := hfour _ _ _ _ (by simpa using hsub)
      have hp0 := hposition p₀ _ hp₀
      have hp1 := hposition p₁ _ hp₁
      have hp2 := hposition p₂ _ hp₂
      have hp3 := hposition p₃ _ hp₃
      have hx23' : x 2 < x 3 := by
        first | exact hx23 (by decide) | omega
      omega
  have htransfer (σ : List ℕ) (x : ℕ → ℕ)
      (hxlt : ∀ i, 1 ≤ i → i < NonnestingDefs.letters σ → x i < x (i + 1))
      (hxmem : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → x i ∈ w)
      (hpattern : ∀ a ∈ σ, 1 ≤ a ∧ a ≤ NonnestingDefs.letters σ)
      (hmin : 3 ≤ x 1) (hsub : List.Sublist (σ.map x) w) :
      NonnestingDefs.Occurs σ v := by
    have hxge : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → 3 ≤ x i := by
      intro i hi hile
      induction i with
      | zero => omega
      | succ j ih =>
        by_cases hj : j = 0
        · subst j
          simpa using hmin
        · have hjge : 1 ≤ j := by omega
          have hprev := ih hjge (by omega)
          have hlt := hxlt j hjge (by omega)
          omega
    have hmapPos : ∀ a ∈ σ.map x, 2 < a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hxge b (hpattern b hb).1 (hpattern b hb).2
    have hσfilter : (σ.map x).filter (fun a => decide (2 < a)) = σ.map x := by
      apply List.filter_eq_self.mpr
      intro a ha
      simp [hmapPos a ha]
    have hsubShift : List.Sublist (σ.map x) (shift 2 v) := by
      have hf := hsub.filter (fun a => decide (2 < a))
      simpa [hσfilter, hfilter] using hf
    let y : ℕ → ℕ := fun i => x i - 2
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨y, ?_, ?_, ?_, by simp⟩
    · intro i hi hlt
      have hxi := hxge i hi (by omega)
      have hxi1 := hxge (i + 1) (by omega) (by omega)
      have hlt' := hxlt i hi hlt
      dsimp [y]
      omega
    · intro i hi hle
      have hxi : x i ∈ shift 2 v := by
        rw [← hfilter]
        apply List.mem_filter.mpr
        exact ⟨hxmem i hi hle, by have := hxge i hi hle; simp; omega⟩
      obtain ⟨a, ha, hia⟩ := List.mem_map.mp hxi
      have hy : y i = a := by dsimp [y]; omega
      exact hy ▸ ha
    · have hm := hsubShift.map (fun a => a - 2)
      simpa [y, shift, List.map_map, Function.comp_def] using hm
  have hwPositive : ∀ z ∈ w, 1 ≤ z := by
    intro z hz
    simp only [w, List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | hz
    all_goals try omega
    exact le_trans (by omega) (hshiftPos z hz)
  have havoid (σ : List ℕ)
      (hσ : σ ∈ [[1, 2, 2, 1], [2, 1, 1, 2],
        [1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hvavoid : ¬ NonnestingDefs.Occurs σ v) :
      ¬ NonnestingDefs.Occurs σ w := by
    intro hocc
    obtain ⟨x, hxlt, hxmem, hxsub, _⟩ := hocc
    have hpattern : ∀ a ∈ σ, 1 ≤ a ∧ a ≤ NonnestingDefs.letters σ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with hσ | hσ | hσ | hσ | hσ | hσ <;> subst σ <;> decide
    have hletters : 2 ≤ NonnestingDefs.letters σ := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with hσ | hσ | hσ | hσ | hσ | hσ <;> subst σ <;> decide
    have hx12 : x 1 < x 2 := hxlt 1 (by omega) (by omega)
    have hx23 : NonnestingDefs.letters σ = 3 → x 2 < x 3 := by
      intro hletter
      exact hxlt 2 (by omega) (by omega)
    have hx1mem : x 1 ∈ w := hxmem 1 (by omega) (by omega)
    by_cases hx1 : x 1 ≤ 2
    · exact hnoLow σ hσ x hx1 hx12 hx23 hxsub
    · have hmin : 3 ≤ x 1 := by
        have := hwPositive (x 1) hx1mem
        omega
      exact hvavoid (htransfer σ x hxlt hxmem hpattern hmin hxsub)
  change w ∈ NonnestingDefs.avoiders (m + 2) Λ
  refine ⟨hperm, ?_, ?_, ?_⟩
  · exact havoid [1, 2, 2, 1] (by simp) hv.2.1
  · exact havoid [2, 1, 1, 2] (by simp) hv.2.2.1
  · intro σ hσ
    have hσ' : σ ∈ [[1, 2, 2, 1], [2, 1, 1, 2],
        [1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
      dsimp [Λ] at hσ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ ⊢
      tauto
    exact havoid σ hσ' (hv.2.2.2 σ hσ)

end D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert.two_insert
