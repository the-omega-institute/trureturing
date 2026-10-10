/- GID: D5/S3/Combinatorics/Games/NestedMexStabilization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/NestedMexStabilization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Nonempty finite compositions of nested mex maps stabilize after two applications. -/

/- proof_shape: content
   admission_basis: escape-witness
   escape_witness: The derived nested pair minimum invariant and its equality clause
     persist through composition and exclude positive swaps.
   Direct frozen dependency: CrimGrundyRefutation.mex_spec. -/

import D5.S0.Certificates.Games.CrimGrundyRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.NestedMexStabilization

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

/-- Four arbitrary finite coefficient sets, each containing zero. -/
structure Coefficients where
  E1 : Finset ℕ
  E2 : Finset ℕ
  E3 : Finset ℕ
  K : Finset ℕ
  zero_E1 : 0 ∈ E1
  zero_E2 : 0 ∈ E2
  zero_E3 : 0 ∈ E3
  zero_K : 0 ∈ K

/-- The intervening odd value is recomputed from the first mex. -/
def step (c : Coefficients) (x : ℕ) : ℕ :=
  let a := mex (insert x c.E1)
  let v := mex (insert a c.K)
  let b := mex (insert a (insert v c.E2))
  mex (insert a (insert b c.E3))

/-- List order is application order: the head acts first. -/
def run : List Coefficients → ℕ → ℕ
  | [], x => x
  | c :: cs, x => run cs (step c x)

/-- No size, value, or length bound is imposed on the coefficients. -/
theorem result (L : List Coefficients) (hL : L ≠ []) (x : ℕ) (hx : 0 < x) :
    run L (run L (run L x)) = run L (run L x) := by
  classical
  -- Agreement below a threshold transports the least omitted value below it.
  have below_agreement : ∀ (S T : Finset ℕ) (t : ℕ),
      (∀ n < t, n ∈ S ↔ n ∈ T) →
      (mex S < t → mex T = mex S) ∧ (t ≤ mex S → t ≤ mex T) := by
    intro S T t h
    have hs := mex_spec S
    have ht := mex_spec T
    constructor
    · intro hst
      apply Nat.le_antisymm
      · by_contra hn
        exact hs.1 ((h _ hst).mpr (ht.2 _ (by omega)))
      · by_contra hn
        exact ht.1 ((h _ (by omega)).mp (hs.2 _ (by omega)))
    · intro hst
      by_contra hn
      exact ht.1 ((h _ (by omega)).mp (hs.2 _ (by omega)))
  have keep : ∀ (S : Finset ℕ) (t : ℕ), t ≠ mex S → mex (insert t S) = mex S := by
    intro S t h
    have hs := mex_spec S
    have ht := mex_spec (insert t S)
    apply Nat.le_antisymm
    · by_contra hn
      have := ht.2 (mex S) (by omega)
      simp only [Finset.mem_insert] at this
      rcases this with he | he
      · exact h he.symm
      · exact hs.1 he
    · by_contra hn
      exact ht.1 (Finset.mem_insert_of_mem (hs.2 _ (by omega)))
  have positive : ∀ (c : Coefficients) (z : ℕ), 0 < step c z := by
    intro c z
    have h := (mex_spec (insert (mex (insert z c.E1))
      (insert (mex (insert (mex (insert z c.E1))
        (insert (mex (insert (mex (insert z c.E1)) c.K)) c.E2))) c.E3))).1
    change 0 < mex _
    by_contra hn
    have he : mex (insert (mex (insert z c.E1))
      (insert (mex (insert (mex (insert z c.E1))
        (insert (mex (insert (mex (insert z c.E1)) c.K)) c.E2))) c.E3)) = 0 := by omega
    rw [he] at h
    exact h (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem c.zero_E3))
  -- This is the nested dependence argument, including the equality clause.
  have component : ∀ c : Coefficients, ∃ α o e : ℕ,
      0 < α ∧ (∀ z, step c z = if z = α then e else o) ∧
      (o ≠ e → α ≤ o ∧ α ≤ e ∧ o ≠ α) := by
    intro c
    let α := mex c.E1
    let β := mex (insert α c.E1)
    have ha : 0 < α := by
      have h := (mex_spec c.E1).1
      by_contra hn
      have he : α = 0 := by omega
      exact h (by change α ∈ c.E1; rw [he]; exact c.zero_E1)
    have hab : α < β := by
      have hb := mex_spec (insert α c.E1)
      have hα := mex_spec c.E1
      have hne : β ≠ α := fun he => hb.1 (by
        change β ∈ insert α c.E1
        rw [he]
        exact Finset.mem_insert_self _ _)
      have hle : α ≤ β := by
        by_contra hn
        exact hb.1 (Finset.mem_insert_of_mem (hα.2 _ (by omega)))
      omega
    let vo := mex (insert α c.K)
    let ve := mex (insert β c.K)
    have hv : ∀ n < α, n = vo ↔ n = ve := by
      have ho := below_agreement c.K (insert α c.K) α (by
        intro n hn
        simp only [Finset.mem_insert, ne_of_lt hn, false_or])
      have he := below_agreement c.K (insert β c.K) α (by
        intro n hn
        simp only [Finset.mem_insert, ne_of_lt (hn.trans hab), false_or])
      by_cases hl : mex c.K < α
      · have hvo : vo = mex c.K := ho.1 hl
        have hve : ve = mex c.K := he.1 hl
        intro n hn
        rw [hvo, hve]
      · have hvo : α ≤ vo := ho.2 (by omega)
        have hve : α ≤ ve := he.2 (by omega)
        intro n hn
        constructor <;> intro hn' <;> omega
    let bo := mex (insert α (insert vo c.E2))
    let be := mex (insert β (insert ve c.E2))
    have hb := below_agreement (insert α (insert vo c.E2)) (insert β (insert ve c.E2)) α (by
      intro n hn
      simp only [Finset.mem_insert, ne_of_lt hn, ne_of_lt (hn.trans hab), false_or]
      exact or_congr (hv n hn) Iff.rfl)
    have hbs : ∀ n < α, n = bo ↔ n = be := by
      by_cases hl : bo < α
      · have he : be = bo := hb.1 hl
        intro n hn
        rw [he]
      · have he : α ≤ be := hb.2 (by omega)
        intro n hn
        constructor <;> intro hn' <;> omega
    let o := mex (insert α (insert bo c.E3))
    let e := mex (insert β (insert be c.E3))
    have hm := below_agreement (insert α (insert bo c.E3)) (insert β (insert be c.E3)) α (by
      intro n hn
      simp only [Finset.mem_insert, ne_of_lt hn, ne_of_lt (hn.trans hab), false_or]
      exact or_congr (hbs n hn) Iff.rfl)
    refine ⟨α, o, e, ha, ?_, ?_⟩
    · intro z
      by_cases hz : z = α
      · subst z
        simp only [step]
        rfl
      · have hz' : mex (insert z c.E1) = α := keep c.E1 z hz
        simp only [step, hz', if_neg hz]
        rfl
    · intro hoe
      have hαo : α ≤ o := by
        by_contra hn
        exact hoe (hm.1 (by omega)).symm
      have hαe : α ≤ e := hm.2 hαo
      have hno : o ≠ α := by
        intro he
        have := (mex_spec (insert α (insert bo c.E3))).1
        exact this (by
          change o ∈ insert α (insert bo c.E3)
          rw [he]
          exact Finset.mem_insert_self _ _)
      exact ⟨hαo, hαe, hno⟩
  have pair : ∀ (c : Coefficients) (r s : ℕ), 0 < r → r < s →
      step c r ≠ step c s →
      r ≤ min (step c r) (step c s) ∧
      (min (step c r) (step c s) = r → step c r = r) := by
    intro c r s hr hrs hne
    obtain ⟨α, o, e, ha, hshape, hbounds⟩ := component c
    have he : r = α ∨ s = α := by
      by_contra hn
      have hnr : r ≠ α := (not_or.mp hn).1
      have hns : s ≠ α := (not_or.mp hn).2
      exact hne (by rw [hshape r, hshape s, if_neg hnr, if_neg hns])
    have hoe : o ≠ e := by
      intro ho
      apply hne
      rw [hshape r, hshape s, ho]
      simp
    obtain ⟨hao, hae, hno⟩ := hbounds hoe
    rcases he with he | he
    · subst r
      have hs : s ≠ α := by omega
      rw [hshape α, hshape s, if_pos rfl, if_neg hs]
      constructor
      · exact le_min hae hao
      · intro hm
        omega
    · subst s
      have hr' : r ≠ α := by omega
      rw [hshape r, hshape α, if_neg hr', if_pos rfl]
      constructor
      · exact le_min (by omega) (by omega)
      · intro hm
        omega
  -- Compositions preserve the same ordered-pair invariant.
  have composed : ∀ cs : List Coefficients,
      (∀ z, 0 < z → 0 < run cs z) ∧
      (∀ r s, 0 < r → r < s → run cs r ≠ run cs s →
        r ≤ min (run cs r) (run cs s) ∧
        (min (run cs r) (run cs s) = r → run cs r = r)) := by
    intro cs
    induction cs with
    | nil =>
      exact ⟨fun z hz => hz, fun r s hr hrs hne =>
        ⟨le_min (le_refl r) (Nat.le_of_lt hrs), fun _ => rfl⟩⟩
    | cons c cs ih =>
      refine ⟨fun z hz => ih.1 _ (positive c z), ?_⟩
      intro r s hr hrs hne
      change run cs (step c r) ≠ run cs (step c s) at hne
      have hdiff : step c r ≠ step c s := fun he => hne (congrArg (run cs) he)
      obtain ⟨hlo, hfix⟩ := pair c r s hr hrs hdiff
      rcases lt_or_gt_of_ne hdiff with hlt | hgt
      · obtain ⟨hlo', hfix'⟩ := ih.2 _ _ (positive c r) hlt hne
        change r ≤ min (run cs (step c r)) (run cs (step c s)) ∧
          (min (run cs (step c r)) (run cs (step c s)) = r → run cs (step c r) = r)
        have hm : min (step c r) (step c s) = step c r := min_eq_left (by omega)
        rw [hm] at hlo hfix
        refine ⟨by omega, ?_⟩
        intro he
        have he' : min (run cs (step c r)) (run cs (step c s)) = step c r := by omega
        have hh := hfix' he'
        have hh' := hfix (by omega)
        change run cs (step c r) = r
        omega
      · obtain ⟨hlo', hfix'⟩ := ih.2 _ _ (positive c s) hgt (Ne.symm hne)
        have hm : min (step c r) (step c s) = step c s := min_eq_right (by omega)
        rw [hm] at hlo hfix
        change r ≤ min (run cs (step c r)) (run cs (step c s)) ∧
          (min (run cs (step c r)) (run cs (step c s)) = r → run cs (step c r) = r)
        rw [min_comm (run cs (step c r)) (run cs (step c s))]
        refine ⟨by omega, ?_⟩
        intro he
        have hh' := hfix (by omega)
        omega
  have image_two : ∃ p q : ℕ, ∀ z, run L z = p ∨ run L z = q := by
    cases L with
    | nil => exact False.elim (hL rfl)
    | cons c cs =>
      obtain ⟨α, o, e, ha, hshape, hbounds⟩ := component c
      refine ⟨run cs o, run cs e, ?_⟩
      intro z
      simp only [run, hshape z]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hp := (composed L).1
  have hpair := (composed L).2
  have no_swap : ∀ r s, 0 < r → 0 < s → run L r = s → run L s = r → r = s := by
    intro r s hr hs hRr hRs
    rcases lt_trichotomy r s with hlt | he | hgt
    · have hn : run L r ≠ run L s := by omega
      have hh := (hpair r s hr hlt hn).2
      rw [hRr, hRs, min_eq_right (by omega)] at hh
      have := hh rfl
      omega
    · exact he
    · have hn : run L s ≠ run L r := by omega
      have hh := (hpair s r hs hgt hn).2
      rw [hRs, hRr, min_eq_right (by omega)] at hh
      have := hh rfl
      omega
  obtain ⟨p, q, himage⟩ := image_two
  have h1 := himage x
  have h2 := himage (run L x)
  have h3 := himage (run L (run L x))
  have hx1 := hp x hx
  have hx2 := hp _ hx1
  by_cases he : run L (run L x) = run L x
  · exact congrArg (run L) he
  · have hc : run L (run L (run L x)) = run L x ∨
        run L (run L (run L x)) = run L (run L x) := by omega
    rcases hc with hc | hc
    · have hh := no_swap (run L x) (run L (run L x)) hx1 hx2 rfl hc
      exact False.elim (he hh.symm)
    · exact hc

end D5.S3.Combinatorics.Games.NestedMexStabilization
