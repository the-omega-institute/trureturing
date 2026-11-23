/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Rank-three omitted triangle gaps identify normalized three-torsion potentials. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

private theorem cycle_torsion {A : Type*} [AddCommGroup A] (u v w : A)
    (h₁ : v - u = w - v) (h₂ : w - v = u - w) :
    3 • (v - u) = 0 ∧ 3 • (w - v) = 0 ∧ 3 • (u - w) = 0 := by
  have h : 3 • (v - u) = 0 := calc
    3 • (v - u) = (v - u) + (v - u) + (v - u) := by abel
    _ = (v - u) + (w - v) + (u - w) := by
      exact congrArg₂ (· + ·) (congrArg ((v - u) + ·) h₁) (h₁.trans h₂)
    _ = 0 := by abel
  exact ⟨h, h₁ ▸ h, (h₁.trans h₂) ▸ h⟩

private theorem triangle_gaps_torsion {A : Type*} [AddCommGroup A] (u : Fin 3 → A)
    (h₁ : u 1 - u 0 = u 2 - u 1) (h₂ : u 2 - u 1 = u 0 - u 2) :
    ∀ i j : Fin 3, 3 • (u j - u i) = 0 := by
  obtain ⟨ha, hb, hc⟩ := cycle_torsion (u 0) (u 1) (u 2) h₁ h₂
  have ha' : 3 • (u 0 - u 1) = 0 := by
    calc
      3 • (u 0 - u 1) = (-((3 : ℕ) • (u 1 - u 0)) : A) := by abel
      _ = 0 := by rw [ha, neg_zero]
  have hb' : 3 • (u 1 - u 2) = 0 := by
    calc
      3 • (u 1 - u 2) = (-((3 : ℕ) • (u 2 - u 1)) : A) := by abel
      _ = 0 := by rw [hb, neg_zero]
  have hc' : 3 • (u 2 - u 0) = 0 := by
    calc
      3 • (u 2 - u 0) = (-((3 : ℕ) • (u 0 - u 2)) : A) := by abel
      _ = 0 := by rw [hc, neg_zero]
  intro i j
  fin_cases i <;> fin_cases j <;> first | assumption | simp

/-- After fixing one point's potential to zero, constant cyclic gaps on omitted
triangles and zero gaps on uncovered edges become three-torsion line sums. -/
theorem normalized_potential_iff {I T A : Type*} [AddCommGroup A]
    (points : T → Fin 3 → I) (u : I → A) (root : I) :
    let uncovered (i j : I) := ¬ ∃ t a b, points t a = i ∧ points t b = j
    let v (i : I) := u i - u root
    ( (∀ i j, uncovered i j → u i = u j) ∧
      (∀ t, u (points t 1) - u (points t 0) = u (points t 2) - u (points t 1) ∧
        u (points t 2) - u (points t 1) = u (points t 0) - u (points t 2))) ↔
    ( (∀ i, 3 • v i = 0) ∧ (∀ i j, uncovered i j → v i = v j) ∧
      (∀ t, v (points t 0) + v (points t 1) + v (points t 2) = 0)) := by
  classical
  intro uncovered v
  have gap (i j : I) : v j - v i = u j - u i := by dsimp [v]; abel
  have eq_shift (i j : I) : u i = u j ↔ v i = v j := by
    constructor
    · intro h
      simp only [v, h]
    · intro h
      apply sub_eq_zero.mp
      rw [← gap j i, h, sub_self]
  constructor
  · rintro ⟨hedge, hcycle⟩
    have htorsion (i : I) : 3 • v i = 0 := by
      by_cases h : uncovered root i
      · simp [v, hedge root i h]
      · obtain ⟨t, a, b, ha, hb⟩ :
            ∃ t a b, points t a = root ∧ points t b = i := by
          exact not_not.mp h
        have hc := triangle_gaps_torsion (u ∘ points t) (hcycle t).1 (hcycle t).2 a b
        simpa [Function.comp_apply, v, ha, hb] using hc
    refine ⟨htorsion, fun i j h => (eq_shift i j).mp (hedge i j h), ?_⟩
    intro t
    have h : v (points t 1) - v (points t 0) = v (points t 2) - v (points t 1) := by
      simp only [gap]
      exact (hcycle t).1
    calc
      v (points t 0) + v (points t 1) + v (points t 2) =
          3 • v (points t 1) + ((v (points t 2) - v (points t 1)) -
            (v (points t 1) - v (points t 0))) := by abel
      _ = 0 := by rw [← h, sub_self, add_zero, htorsion]
  · rintro ⟨htorsion, hedge, hline⟩
    refine ⟨fun i j h => (eq_shift i j).mpr (hedge i j h), ?_⟩
    intro t
    simp only [← gap]
    constructor
    · calc
        v (points t 1) - v (points t 0) =
            (v (points t 2) - v (points t 1)) + (3 • v (points t 1) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]
    · calc
        v (points t 2) - v (points t 1) =
            (v (points t 0) - v (points t 2)) + (3 • v (points t 2) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]

private def forward {I : Type*} (triangle : Fin 3 → I) (i j : I) : Prop :=
  (triangle 0 = i ∧ triangle 1 = j) ∨
  (triangle 1 = i ∧ triangle 2 = j) ∨
  (triangle 2 = i ∧ triangle 0 = j)

private def covers {I : Type*} (triangle : Fin 3 → I) (i j : I) : Prop :=
  ∃ a b, triangle a = i ∧ triangle b = j

private theorem covers_iff_forward {I : Type*} (triangle : Fin 3 → I) {i j : I}
    (hne : i ≠ j) : covers triangle i j ↔ forward triangle i j ∨ forward triangle j i := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hne (ha.symm.trans hb)).elim
      | exact Or.inl (Or.inl ⟨ha, hb⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨ha, hb⟩))
      | exact Or.inr (Or.inl ⟨hb, ha⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨hb, ha⟩))
  · intro h
    rcases h with (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩) | (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact ⟨0, 1, ha, hb⟩
    · exact ⟨1, 2, ha, hb⟩
    · exact ⟨2, 0, ha, hb⟩
    · exact ⟨1, 0, hb, ha⟩
    · exact ⟨2, 1, hb, ha⟩
    · exact ⟨0, 2, hb, ha⟩

private noncomputable def row {I A : Type*} [AddCommGroup A]
    (triangle : Fin 3 → I) (value : A) (i j : I) : A :=
  open Classical in
  if forward triangle i j then value else if forward triangle j i then -value else 0

private theorem row_eq_zero {I A : Type*} [AddCommGroup A]
    (triangle : Fin 3 → I) (value : A) {i j : I}
    (hne : i ≠ j) (h : ¬ covers triangle i j) : row triangle value i j = 0 := by
  classical
  have h' := fun hf => h ((covers_iff_forward triangle hne).mpr hf)
  have hf : ¬ forward triangle i j := fun hf => h' (Or.inl hf)
  have hr : ¬ forward triangle j i := fun hr => h' (Or.inr hr)
  rw [row, ite_eq_right hf, ite_eq_right hr]

private theorem not_reverse {I : Type*} {triangle : Fin 3 → I}
    (hinj : Function.Injective triangle) {i j : I}
    (hf : forward triangle i j) : ¬ forward triangle j i := by
  intro hr
  rcases hf with (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩) <;>
    rcases hr with (⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨hc,hd⟩) <;>
    first
    | have hf := hinj (ha.trans hd.symm); exact absurd hf (by decide)
    | have hf := hinj (hb.trans hc.symm); exact absurd hf (by decide)

/-- For disjoint triangle edge supports, the gap of a point potential is a
sum of oriented triangle rows exactly for normalized three-torsion potentials
with zero uncovered gaps and zero sums on each triangle. -/
theorem edge_rows_iff {I T A : Type*} [Fintype T] [AddCommGroup A]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (u : I → A) (root : I) :
    let v (i : I) := u i - u root
    (∃ c : T → A, ∀ i j, i ≠ j → u j - u i = ∑ t, row (points t) (c t) i j) ↔
    ((∀ i, 3 • v i = 0) ∧
      (∀ i j, (¬ ∃ t a b, points t a = i ∧ points t b = j) → v i = v j) ∧
      (∀ t, v (points t 0) + v (points t 1) + v (points t 2) = 0)) := by
  classical
  intro v
  have normalize := normalized_potential_iff points u root
  dsimp only at normalize
  refine Iff.trans ?_ normalize
  have single (c : T → A) (t : T) (i j : I) (hne : i ≠ j)
      (ht : covers (points t) i j) :
      (∑ s, row (points s) (c s) i j) = row (points t) (c t) i j := by
    apply Finset.sum_eq_single_of_mem t (Finset.mem_univ _)
    intro s _ hst
    exact row_eq_zero _ _ hne fun hs => hst (hdis s t i j hne hs ht)
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨?_, ?_⟩
    · intro i j huncovered
      by_cases hne : i = j
      · exact congrArg u hne
      · have hz : u j - u i = 0 := by
          rw [hc i j hne]
          apply Finset.sum_eq_zero
          intro t _
          exact row_eq_zero _ _ hne (fun ⟨a,b,ha,hb⟩ => huncovered ⟨t,a,b,ha,hb⟩)
        exact (sub_eq_zero.mp hz).symm
    · intro t
      have eval (i j : I) (hne : i ≠ j) (hf : forward (points t) i j) :
          u j - u i = c t := by
        rw [hc i j hne, single c t i j hne
          ((covers_iff_forward _ hne).mpr (Or.inl hf)), row, ite_eq_left hf]
      have h01 := eval _ _ ((hinj t).ne (by decide : (0 : Fin 3) ≠ 1))
        (Or.inl ⟨rfl, rfl⟩)
      have h12 := eval _ _ ((hinj t).ne (by decide : (1 : Fin 3) ≠ 2))
        (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have h20 := eval _ _ ((hinj t).ne (by decide : (2 : Fin 3) ≠ 0))
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact ⟨h01.trans h12.symm, h12.trans h20.symm⟩
  · rintro ⟨hedge, hcycle⟩
    let c := fun t => u (points t 1) - u (points t 0)
    refine ⟨c, ?_⟩
    intro i j hne
    by_cases h : ∃ t, covers (points t) i j
    · obtain ⟨t, ht⟩ := h
      rw [single c t i j hne ht]
      have eval (i j : I) (hf : forward (points t) i j) : u j - u i = c t := by
        rcases hf with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · rfl
        · exact (hcycle t).1.symm
        · exact ((hcycle t).1.trans (hcycle t).2).symm
      rcases (covers_iff_forward _ hne).mp ht with hf | hf
      · rw [row, ite_eq_left hf]
        exact eval i j hf
      · rw [row, ite_eq_right (not_reverse (hinj t) hf), ite_eq_left hf, ← eval j i hf]
        exact (neg_sub _ _).symm
    · have he := hedge i j fun ⟨t,a,b,ha,hb⟩ => h ⟨t,a,b,ha,hb⟩
      rw [he, sub_self]
      symm
      apply Finset.sum_eq_zero
      intro t _
      exact row_eq_zero _ _ hne (fun ht => h ⟨t, ht⟩)

/-- Zero row sums determine the edges at an omitted vertex. When the point
count kills the coefficients, restoring those edges gives a zero-sum potential. -/
theorem restore_potential {I A : Type*} [Fintype I] [AddCommGroup A]
    (edge : I → I → A) (root anchor : I) (hne : anchor ≠ root)
    (hdiag : ∀ i, edge i i = 0) (hflip : ∀ i j, edge i j = -edge j i)
    (hsum : ∀ i, ∑ j, edge i j = 0) (hann : ∀ x : A, Fintype.card I • x = 0)
    (hrest : ∀ i j, i ≠ root → j ≠ root → edge i j = edge anchor j - edge anchor i) :
    ∃! u : I → A, u anchor = 0 ∧ (∑ j, u j) = 0 ∧ ∀ i j, edge i j = u j - u i := by
  classical
  let partialSum : A := ∑ j ∈ Finset.univ.erase root, edge anchor j
  let u : I → A := fun j => if j = root then -partialSum else edge anchor j
  have hu (j : I) (hj : j ≠ root) : u j = edge anchor j := by simp [u, hj]
  have hanchor : u anchor = 0 := (hu anchor hne).trans (hdiag anchor)
  have htotal : (∑ j, u j) = 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)]
    have hpart : (∑ j ∈ Finset.univ.erase root, u j) = partialSum := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hu j (Finset.ne_of_mem_erase hj)
    rw [hpart]
    simp [u]
  have hdiffsum (i : I) : (∑ j, (u j - u i)) = 0 := by
    rw [Finset.sum_sub_distrib, htotal, Finset.sum_const, Finset.card_univ, hann, sub_zero]
  have hnonroot (i j : I) (hi : i ≠ root) (hj : j ≠ root) :
      edge i j = u j - u i := by rw [hu i hi, hu j hj, hrest i j hi hj]
  have hroot (i : I) (hi : i ≠ root) : edge i root = u root - u i := by
    have hpart : (∑ j ∈ Finset.univ.erase root, edge i j) =
        ∑ j ∈ Finset.univ.erase root, (u j - u i) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hnonroot i j hi (Finset.ne_of_mem_erase hj)
    have left := hsum i
    have right := hdiffsum i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root), hpart] at left
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)] at right
    exact add_left_cancel (left.trans right.symm)
  refine ⟨u, ⟨hanchor, htotal, ?_⟩, ?_⟩
  · intro i j
    by_cases hi : i = root
    · subst i
      by_cases hj : j = root
      · subst j
        rw [hdiag, sub_self]
      · rw [hflip root j, hroot j hj, neg_sub]
    · by_cases hj : j = root
      · subst j
        exact hroot i hi
      · exact hnonroot i j hi hj
  · intro w hw
    funext j
    have he := hw.2.2 anchor j
    rw [hw.1, sub_zero] at he
    by_cases hj : j = root
    · subst j
      exact he.symm.trans (by simpa [hanchor] using hroot anchor hne)
    · exact he.symm.trans (hu j hj).symm

private theorem row_flip {I A : Type*} [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i j : I) :
    row triangle value i j = -row triangle value j i := by
  classical
  by_cases hf : forward triangle i j
  · simp [row, hf, not_reverse hinj hf]
  · by_cases hr : forward triangle j i <;> simp [row, hf, hr]

private theorem row_diag {I A : Type*} [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i : I) :
    row triangle value i i = 0 := by
  classical
  have hf : ¬ forward triangle i i := fun h => not_reverse hinj h h
  simp [row, hf]

private theorem row_sum {I A : Type*} [Fintype I] [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i : I) :
    (∑ j, row triangle value i j) = 0 := by
  classical
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  have h20 := hinj.ne (by decide : (2 : Fin 3) ≠ 0)
  have indicator (a b : I) (hab : a ≠ b) :
      (∑ j : I, if j = a then value else if j = b then -value else 0) = 0 := by
    have split (j : I) :
        (if j = a then value else if j = b then -value else 0) =
          (if j = a then value else 0) + (if j = b then -value else 0) := by
      by_cases ha : j = a
      · subst j
        simp [hab]
      · simp [ha]
    simp only [split, Finset.sum_add_distrib]
    simp
  by_cases h0 : triangle 0 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 1) (triangle 2) h12
  by_cases h1 : triangle 1 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 2) (triangle 0) h20
  by_cases h2 : triangle 2 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 0) (triangle 1) h01
  simp [row, forward, h0, h1, h2]

/-- A linear relation among the non-root triangle edge rows that is a potential
difference on those edges has a unique normalized potential on the whole ground
set. Both the potential values and the relation coefficients are killed by three. -/
theorem triangle_relation_potential {I T A : Type*} [Fintype I] [Fintype T]
    [AddCommGroup A] (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (root anchor : I) (hne : anchor ≠ root) (hann : ∀ x : A, Fintype.card I • x = 0)
    (c : T → A) :
    let e (i j : I) := ∑ t, row (points t) (c t) i j
    (∀ i j, i ≠ root → j ≠ root → e i j = e anchor j - e anchor i) →
      (∀ t, 3 • c t = 0) ∧
      ∃! u : I → A, u anchor = 0 ∧ (∑ j, u j) = 0 ∧
        (∀ i, 3 • u i = 0) ∧ (∀ i j, e i j = u j - u i) := by
  classical
  intro e hrest
  have hdiag (i : I) : e i i = 0 := Finset.sum_eq_zero fun t _ => row_diag (hinj t) (c t) i
  have hflip (i j : I) : e i j = -e j i := by
    dsimp [e]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => row_flip (hinj t) (c t) i j)
  have hsum (i : I) : (∑ j, e i j) = 0 := by
    dsimp [e]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => row_sum (hinj t) (c t) i
  obtain ⟨u, hu, unique⟩ := restore_potential e root anchor hne hdiag hflip hsum hann hrest
  have hex : ∃ d : T → A, ∀ i j, i ≠ j → u j - u i = ∑ t, row (points t) (d t) i j :=
    ⟨c, fun i j _ => (hu.2.2 i j).symm⟩
  have ht := ((edge_rows_iff points hinj hdis u anchor).mp hex).1
  have kill (i : I) : 3 • u i = 0 := by simpa [hu.1] using ht i
  refine ⟨?_, u, ⟨hu.1, hu.2.1, kill, hu.2.2⟩, fun v hv => unique v ⟨hv.1, hv.2.1, hv.2.2.2⟩⟩
  intro t
  let i := points t 0
  let j := points t 1
  have hne' : i ≠ j := (hinj t).ne (by decide : (0 : Fin 3) ≠ 1)
  have ht' : covers (points t) i j := ⟨0, 1, rfl, rfl⟩
  have hsum' : e i j = row (points t) (c t) i j := by
    apply Finset.sum_eq_single_of_mem t (Finset.mem_univ _)
    intro s _ hst
    exact row_eq_zero _ _ hne' fun hs => hst (hdis s t i j hne' hs ht')
  have hfor : forward (points t) i j := Or.inl ⟨rfl, rfl⟩
  rw [row, ite_eq_left hfor, hu.2.2] at hsum'
  rw [← hsum']
  have he : (3 : ℕ) • (u j - u i) = (3 : ℕ) • u j - (3 : ℕ) • u i := by abel
  rw [he, kill, kill, sub_self]

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials
