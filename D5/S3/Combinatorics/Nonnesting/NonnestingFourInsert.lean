/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourInsert
   mirror-E: none(waiver:row-four-crossing-insertion)
   anchors: []
   utility: none
   digest: Inserting a new least value around the first old letter preserves avoidance. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

theorem crossing_insert (r : List ℕ) (n : ℕ)
    (hv : (1 :: r) ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]) :
    (1 :: 2 :: 1 :: shift 1 r) ∈ NonnestingDefs.avoiders (n + 1)
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
  let v := 1 :: r
  let w := 1 :: 2 :: 1 :: shift 1 r
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hperm0 := directSum_perm 1 n [1, 1] v (by simp) hv.1
  have hperm : w.Perm ((List.range' 1 (n + 1)).flatMap fun i => [i, i]) := by
    have hswap : w.Perm (1 :: 1 :: 2 :: shift 1 r) := by
      exact ((List.Perm.swap 2 1 (shift 1 r)).cons 1).symm
    have hbase : (1 :: 1 :: 2 :: shift 1 r).Perm
        ((List.range' 1 (n + 1)).flatMap fun i => [i, i]) := by
      simpa [directSum, shift, v, Nat.add_comm] using hperm0
    exact hswap.trans hbase
  have hshiftPos : ∀ z ∈ shift 1 r, 1 < z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    have haBase : a ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
      hv.1.mem_iff.mp (by simp [ha])
    obtain ⟨i, hi, hai⟩ := List.mem_flatMap.mp haBase
    have heq : a = i := by simpa using hai
    subst a
    have hir : 1 ≤ i ∧ i < 1 + n := by simpa using hi
    omega
  have hfilter : w.filter (fun z => decide (1 < z)) = shift 1 v := by
    have ht : (shift 1 r).filter (fun z => decide (1 < z)) = shift 1 r := by
      apply List.filter_eq_self.mpr
      intro z hz
      simp [hshiftPos z hz]
    change (1 :: 2 :: 1 :: shift 1 r).filter (fun z => decide (1 < z)) =
      2 :: shift 1 r
    simp [ht]
  have hones (p : ℕ) (hp : w[p]? = some 1) : p = 0 ∨ p = 2 := by
    cases p with
    | zero => exact Or.inl rfl
    | succ p =>
      cases p with
      | zero => simp [w] at hp
      | succ p =>
        cases p with
        | zero => exact Or.inr rfl
        | succ p =>
          have ht : (shift 1 r)[p]? = some 1 := by
            simpa [w] using hp
          have hmem : 1 ∈ shift 1 r := List.mem_of_getElem? ht
          exact (Nat.not_lt_of_ge (by omega) (hshiftPos 1 hmem)).elim
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
      have h := hf (0 : Fin 4)
      simpa using h.symm
    · rw [List.getElem?_eq_getElem (f 1).isLt]
      have h := hf (1 : Fin 4)
      simpa using h.symm
    · rw [List.getElem?_eq_getElem (f 2).isLt]
      have h := hf (2 : Fin 4)
      simpa using h.symm
    · rw [List.getElem?_eq_getElem (f 3).isLt]
      have h := hf (3 : Fin 4)
      simpa using h.symm
  have hnoLow (σ : List ℕ)
      (hσ : σ ∈ [[1, 2, 2, 1], [2, 1, 1, 2],
        [1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (x : ℕ → ℕ) (hx1 : x 1 = 1) (hx12 : x 1 < x 2)
      (hx23 : σ = [1, 3, 1, 2] → x 2 < x 3)
      (hsub : List.Sublist (σ.map x) w) : False := by
    have hcases : σ.map x = [x 1, x 2, x 2, x 1] ∨
        σ.map x = [x 2, x 1, x 1, x 2] ∨
        σ.map x = [x 1, x 2, x 3, x 1] ∨
        σ.map x = [x 1, x 3, x 1, x 2] ∨
        σ.map x = [x 2, x 2, x 3, x 1] ∨
        σ.map x = [x 3, x 2, x 2, x 1] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    rcases hcases with h | h | h | h | h | h
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, h23, _, _, _, hlast⟩ :=
        hfour _ _ _ _ hsub
      have hp3 := hones p₃ (by simpa [hx1] using hlast)
      rcases hp3 with hp3 | hp3 <;> omega
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, _, _, hmid, hmid2, _⟩ :=
        hfour _ _ _ _ hsub
      have hp1 := hones p₁ (by simpa [hx1] using hmid)
      have hp2 := hones p₂ (by simpa [hx1] using hmid2)
      rcases hp1 with hp1 | hp1 <;> rcases hp2 with hp2 | hp2 <;> omega
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, h23, _, _, _, hlast⟩ :=
        hfour _ _ _ _ hsub
      have hp3 := hones p₃ (by simpa [hx1] using hlast)
      rcases hp3 with hp3 | hp3 <;> omega
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, _, hstart, hbetweenVal, hmid, _⟩ :=
        hfour _ _ _ _ hsub
      have hp0 := hones p₀ (by simpa [hx1] using hstart)
      have hp2 := hones p₂ (by simpa [hx1] using hmid)
      have hbetween : x 3 = 2 := by
        have hp0' : p₀ = 0 := by rcases hp0 with h | h <;> omega
        have hp2' : p₂ = 2 := by rcases hp2 with h | h <;> omega
        have hp1' : p₁ = 1 := by omega
        subst p₁
        simpa [w] using hbetweenVal.symm
      have hσ' : σ = [1, 3, 1, 2] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
        rcases hσ with hσ | hσ | hσ | hσ | hσ | hσ
        · subst σ; simp at h; omega
        · subst σ; simp at h; omega
        · subst σ; simp at h; omega
        · exact hσ
        · subst σ; simp at h; omega
        · subst σ; simp at h; omega
      have h23 := hx23 hσ'
      omega
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, h23, _, _, _, hlast⟩ :=
        hfour _ _ _ _ hsub
      have hp3 := hones p₃ (by simpa [hx1] using hlast)
      rcases hp3 with hp3 | hp3 <;> omega
    · rw [h] at hsub
      obtain ⟨p₀, p₁, p₂, p₃, h01, h12, h23, _, _, _, hlast⟩ :=
        hfour _ _ _ _ hsub
      have hp3 := hones p₃ (by simpa [hx1] using hlast)
      rcases hp3 with hp3 | hp3 <;> omega
  have htransfer (σ : List ℕ) (x : ℕ → ℕ)
      (hxlt : ∀ i, 1 ≤ i → i < NonnestingDefs.letters σ → x i < x (i + 1))
      (hxmem : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → x i ∈ w)
      (hpattern : ∀ a ∈ σ, 1 ≤ a ∧ a ≤ NonnestingDefs.letters σ)
      (hmin : 2 ≤ x 1) (hsub : List.Sublist (σ.map x) w) :
      NonnestingDefs.Occurs σ v := by
    have hxge : ∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → 2 ≤ x i := by
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
    have hmapPos : ∀ a ∈ σ.map x, 1 < a := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have hb' := hpattern b hb
      exact hxge b hb'.1 hb'.2
    have hσfilter : (σ.map x).filter (fun a => decide (1 < a)) = σ.map x := by
      apply List.filter_eq_self.mpr
      intro a ha
      simp [hmapPos a ha]
    have hsubShift : List.Sublist (σ.map x) (shift 1 v) := by
      have hf := hsub.filter (fun a => decide (1 < a))
      simpa [hσfilter, hfilter] using hf
    let y : ℕ → ℕ := fun i => x i - 1
    unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
    refine ⟨y, ?_, ?_, ?_, by simp⟩
    · intro i hi hlt
      have hxi := hxge i hi (by omega)
      have hxi1 := hxge (i + 1) (by omega) (by omega)
      have hlt' := hxlt i hi hlt
      dsimp [y]
      omega
    · intro i hi hle
      have hxi : x i ∈ shift 1 v := by
        rw [← hfilter]
        apply List.mem_filter.mpr
        exact ⟨hxmem i hi hle, by have := hxge i hi hle; simp; omega⟩
      obtain ⟨a, ha, hia⟩ := List.mem_map.mp hxi
      have hy : y i = a := by dsimp [y]; omega
      exact hy ▸ ha
    · have hm := hsubShift.map (fun a => a - 1)
      simpa [y, shift, List.map_map, Function.comp_def] using hm
  have hwPositive : ∀ z ∈ w, 1 ≤ z := by
    intro z hz
    simp only [w, List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | hz
    · omega
    · omega
    · omega
    · exact le_of_lt (hshiftPos z hz)
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
    have hx23 : σ = [1, 3, 1, 2] → x 2 < x 3 := by
      intro he
      subst σ
      exact hxlt 2 (by omega) (by decide)
    have hx1mem : x 1 ∈ w := hxmem 1 (by omega) (by omega)
    by_cases hx1 : x 1 = 1
    · exact hnoLow σ hσ x hx1 hx12 hx23 hxsub
    · have hmin : 2 ≤ x 1 := by
        have := hwPositive (x 1) hx1mem
        omega
      exact hvavoid (htransfer σ x hxlt hxmem hpattern hmin hxsub)
  change w ∈ NonnestingDefs.avoiders (n + 1) Λ
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

theorem crossing_insert_first_order (r : List ℕ) (n : ℕ)
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
      ((1 :: r)).idxOf a <
        ((1 :: r)).idxOf b) :
    ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
      ((1 :: 2 :: 1 :: shift 1 r)).idxOf a <
        ((1 :: 2 :: 1 :: shift 1 r)).idxOf b := by
  have hidx (l : List ℕ) (x : ℕ) :
      (shift 1 l).idxOf (x + 1) = l.idxOf x := by
    induction l with
    | nil => simp [shift]
    | cons y ys ih =>
      by_cases hy : y = x
      · subst y
        simp [shift]
      · have hne : y + 1 ≠ x + 1 := by omega
        change List.idxOf (x + 1) (List.map (fun z => z + 1) ys) =
          List.idxOf x ys at ih
        simpa [shift, List.idxOf_cons_ne _ hne,
          List.idxOf_cons_ne _ hy] using congrArg Nat.succ ih
  have hpos (z : ℕ) (hz : 3 ≤ z) :
      ((1 :: 2 :: 1 :: shift 1 r)).idxOf z =
        3 + r.idxOf (z - 1) := by
    have hne1 : 1 ≠ z := by omega
    have hne2 : 2 ≠ z := by omega
    have heq : z - 1 + 1 = z := by omega
    have hm := hidx r (z - 1)
    rw [heq] at hm
    simp [List.idxOf_cons_ne,
      hne1, hne2, hm]
    omega
  intro a b ha hab hbn
  by_cases ha1 : a = 1
  · subst a
    have hfirst1 : ((1 :: 2 :: 1 :: shift 1 r)).idxOf 1 = 0 := by
      simp []
    by_cases hb2 : b = 2
    · subst b
      simp []
    · have hbg : 3 ≤ b := by omega
      rw [hfirst1, hpos b hbg]
      omega
  have hag : 2 ≤ a := by omega
  by_cases ha2 : a = 2
  · subst a
    have hbg : 3 ≤ b := by omega
    rw [hpos b hbg]
    simp []
    omega
  have hag3 : 3 ≤ a := by omega
  have hbg3 : 3 ≤ b := by omega
  have hva : ((1 :: r)).idxOf (a - 1) =
      1 + r.idxOf (a - 1) := by
    have hne : 1 ≠ a - 1 := by omega
    simp [List.idxOf_cons_ne _ hne]
    omega
  have hvb : ((1 :: r)).idxOf (b - 1) =
      1 + r.idxOf (b - 1) := by
    have hne : 1 ≠ b - 1 := by omega
    simp [List.idxOf_cons_ne _ hne]
    omega
  have hlt := hfirst (a - 1) (b - 1) (by omega) (by omega) (by omega)
  rw [hva, hvb] at hlt
  rw [hpos a hag3, hpos b hbg3]
  omega

theorem cut_insert_first_order (v : List ℕ) (n : ℕ)
    (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n →
      (v).idxOf a < (v).idxOf b) :
    ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
      ((1 :: 1 :: shift 1 v)).idxOf a <
        ((1 :: 1 :: shift 1 v)).idxOf b := by
  have hidx (l : List ℕ) (x : ℕ) :
      (shift 1 l).idxOf (x + 1) = l.idxOf x := by
    induction l with
    | nil => simp [shift]
    | cons y ys ih =>
      by_cases hy : y = x
      · subst y
        simp [shift]
      · have hne : y + 1 ≠ x + 1 := by omega
        change List.idxOf (x + 1) (List.map (fun z => z + 1) ys) =
          List.idxOf x ys at ih
        simpa [shift, List.idxOf_cons_ne _ hne,
          List.idxOf_cons_ne _ hy] using congrArg Nat.succ ih
  have hpos (z : ℕ) (hz : 2 ≤ z) :
      ((1 :: 1 :: shift 1 v)).idxOf z =
        2 + v.idxOf (z - 1) := by
    have hne : 1 ≠ z := by omega
    have heq : z - 1 + 1 = z := by omega
    have hm := hidx v (z - 1)
    rw [heq] at hm
    simp [
      List.idxOf_cons_ne _ hne, hm]
    omega
  intro a b ha hab hbn
  by_cases ha1 : a = 1
  · subst a
    have hbg : 2 ≤ b := by omega
    rw [hpos b hbg]
    simp []
  have hag : 2 ≤ a := by omega
  have hbg : 2 ≤ b := by omega
  have hlt := hfirst (a - 1) (b - 1) (by omega) (by omega) (by omega)
  rw [hpos a hag, hpos b hbg]
  change v.idxOf (a - 1) < v.idxOf (b - 1) at hlt
  omega

end D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert.crossing_insert
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert.crossing_insert_first_order
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert.cut_insert_first_order
