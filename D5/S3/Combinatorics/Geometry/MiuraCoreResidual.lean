/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreResidual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreResidual
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Frozen deletion preserves the exact residual class on physical grids. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreExtremum
public import D5.S3.Combinatorics.Geometry.MiuraCoreBoundary
public import D5.S3.Combinatorics.Geometry.MiuraResidualCount

/-! Finite signed contraction and its exact full-grid invariants. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreResidual

open MiuraHeightEnvelope MiuraResidualCount MiuraCoreFrozenSlope MiuraCoreColumns
  MiuraCoreBoundary MiuraCoreContract MiuraCoreCellExpand MiuraCoreExtremum

variable {m n : ℕ}

/-- Actual membership of one physical side, with zero-based cell indices. -/
def cellOnSide (sd : Side) (p : Cell m n) : Prop :=
  match sd with
  | .top => p.1.val = 0
  | .bottom => p.1.val + 1 = m
  | .left => p.2.val = 0
  | .right => p.2.val + 1 = n

/-- Internal signed deletion preserves membership of all four physical sides. -/
theorem cellExpand_on_side (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (p : Cell m (n - 1)) (sd : Side) :
    cellOnSide sd (cellExpand j p hj0 hj1) ↔ cellOnSide sd p := by
  have hp := p.2.isLt
  by_cases hlt : p.2.val < j.val
  · rw [cellExpand_left j p hj0 hj1 hlt]
    cases sd <;> simp only [cellOnSide] <;> omega
  · rw [cellExpand_right j p hj0 hj1 hlt]
    cases sd <;> simp only [cellOnSide] <;> omega

/-- A side contains all minima exactly when each minimum has that side membership. -/
theorem all_minima_side_iff (h : Cell m n → ℤ) (sd : Side) :
    AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima h) (m : ℤ) (n : ℤ) sd ↔
      ∀ v, IsStrictLocalMin h v → cellOnSide sd v := by
  classical
  cases sd <;> simp only [AllOnSide, minima, Finset.mem_filter, Finset.mem_univ,
    true_and, cellOnSide] <;> constructor
  all_goals
    intro hside v hv
    have hp := hside v hv
    omega

/-- Signed deletion preserves the cardinality of minima independently of maxima. -/
theorem contractAt_minima_card (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) :
    (minima (contractAt h hm j hfrz)).card = (minima h).card := by
  classical
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  apply Finset.card_bij (fun p _ => cellExpand j p hj0 hj1)
  · intro p hp
    simp only [minima, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact h_min_of_contractAt_isSLm h hh hm j ⟨hj0, hj1, hsym⟩ p hp
  · intro p _ q _ heq
    exact cellExpand_injective j hj0 hj1 heq
  · intro u hu
    simp only [minima, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hne : u.2 ≠ j := by
      intro e
      have he : u = (u.1, j) := Prod.ext rfl e
      exact frozenColumn_no_extremum h j ⟨hj0, hj1, hsym⟩ u.1
        (he ▸ Or.inr hu)
    obtain ⟨p, hp⟩ := cellExpand_surjOn j hj0 hj1 u hne
    refine ⟨p, ?_, hp⟩
    simp only [minima, Finset.mem_filter, Finset.mem_univ, true_and]
    exact contractAt_isSLm_of_h_min h hh hm j ⟨hj0, hj1, hsym⟩ p (hp ▸ hu)

/-- Signed deletion preserves the cardinality of maxima independently of minima. -/
theorem contractAt_maxima_card (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) :
    (maxima (contractAt h hm j hfrz)).card = (maxima h).card := by
  classical
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  apply Finset.card_bij (fun p _ => cellExpand j p hj0 hj1)
  · intro p hp
    simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact h_max_of_contractAt_isSLM h hh hm j ⟨hj0, hj1, hsym⟩ p hp
  · intro p _ q _ heq
    exact cellExpand_injective j hj0 hj1 heq
  · intro u hu
    simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hne : u.2 ≠ j := by
      intro e
      have he : u = (u.1, j) := Prod.ext rfl e
      exact frozenColumn_no_extremum h j ⟨hj0, hj1, hsym⟩ u.1
        (he ▸ Or.inl hu)
    obtain ⟨p, hp⟩ := cellExpand_surjOn j hj0 hj1 u hne
    refine ⟨p, ?_, hp⟩
    simp only [maxima, Finset.mem_filter, Finset.mem_univ, true_and]
    exact contractAt_isSLM_of_h_max h hh hm j ⟨hj0, hj1, hsym⟩ p (hp ▸ hu)

/-- The same one physical side contains all minima before and after deletion. -/
theorem contractAt_all_minima_side_iff
    (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (sd : Side) :
    AllOnSide (fun v : Cell m (n - 1) => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima (contractAt h hm j hfrz)) (m : ℤ) ((n - 1 : ℕ) : ℤ) sd ↔
    AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima h) (m : ℤ) (n : ℤ) sd := by
  rw [all_minima_side_iff, all_minima_side_iff]
  constructor
  · intro hside u hu
    have hne : u.2 ≠ j := by
      intro e
      have he : u = (u.1, j) := Prod.ext rfl e
      exact frozenColumn_no_extremum h j hfrz u.1 (he ▸ Or.inr hu)
    obtain ⟨p, hp⟩ := cellExpand_surjOn j hfrz.1 hfrz.2.1 u hne
    have hmin := contractAt_isSLm_of_h_min h hh hm j hfrz p (hp ▸ hu)
    have hmem := (cellExpand_on_side j hfrz.1 hfrz.2.1 p sd).mpr (hside p hmin)
    exact hp ▸ hmem
  · intro hside p hp
    apply (cellExpand_on_side j hfrz.1 hfrz.2.1 p sd).mp
    exact hside _ (h_min_of_contractAt_isSLm h hh hm j hfrz p hp)

/-- Atomic contraction of an actual residual array preserves its exact original class. -/
theorem contractAt_residual (a b : ℕ) (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (hr : Residual a b h) :
    Residual a b (contractAt h hm j hfrz) := by
  refine ⟨contractAt_isCanonicalHeight h hr.1.1 hm j hfrz hr.1,
    ?_, ?_, ?_⟩
  · exact (contractAt_minima_card h hr.1.1 hm j hfrz).trans hr.2.1
  · exact (contractAt_maxima_card h hr.1.1 hm j hfrz).trans hr.2.2.1
  · rintro ⟨sd, hsd⟩
    exact hr.2.2.2 ⟨sd, (contractAt_all_minima_side_iff h hr.1.1 hm j hfrz sd).mp hsd⟩


/-- Inactivity excludes both occupied physical boundary columns. -/
theorem inactive_internal (h : Cell m n → ℤ) (hn : 0 < n)
    (hends : activeColumn h ⟨0, hn⟩ ∧ activeColumn h ⟨n - 1, by omega⟩)
    (j : Fin n) (hj : ¬ activeColumn h j) :
    0 < j.val ∧ j.val + 1 < n := by
  have hjlt := j.isLt
  constructor
  · by_contra h
    have he : j = ⟨0, hn⟩ := Fin.ext (show j.val = 0 by omega)
    exact hj (he.symm ▸ hends.1)
  · by_contra h
    have he : j = ⟨n - 1, by omega⟩ := Fin.ext (show j.val = n - 1 by omega)
    exact hj (he.symm ▸ hends.2)

/-- Beyond the core width bound, two consecutive columns are genuinely frozen. -/
theorem exists_adjacent_frozen_of_width (h : Cell m n → ℤ) (hh : IsHeight h)
    (hm : 0 < m) (hn : 2 ≤ n) (d : ℕ) (hd : numExtrema h ≤ d)
    (hwide : 2 * d - 1 < n) :
    ∃ j k : Fin n, j.val + 1 = k.val ∧ frozenColumn h j ∧ frozenColumn h k := by
  classical
  have hends := boundary_columns_active h hh hm hn
  have hactive : numActiveColumns h ≤ d :=
    (numActiveColumns_le_numExtrema h).trans hd
  have hruns : numFrozenRuns h + 1 ≤ d :=
    (numFrozenRuns_lt_numExtrema h (by omega) hends.1 hends.2).trans hd
  have hpairs : ∃ j k : Fin n, j.val + 1 = k.val ∧
      ¬ activeColumn h j ∧ ¬ activeColumn h k := by
    by_contra hnone
    have heq : numFrozenRuns h =
        (Finset.univ.filter (fun j : Fin n => ¬ activeColumn h j)).card := by
      unfold numFrozenRuns
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · exact fun hj => hj.1
      · intro hj
        have hjpos := (inactive_internal h (by omega) hends j hj).1
        refine ⟨hj, Or.inr ⟨hjpos, ?_⟩⟩
        by_contra hprev
        apply hnone
        refine ⟨⟨j.val - 1, by omega⟩, j, by simp only [Fin.val_mk]; omega,
          hprev, hj⟩
    have hpartition :
        numActiveColumns h +
          (Finset.univ.filter (fun j : Fin n => ¬ activeColumn h j)).card = n := by
      simpa [numActiveColumns] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (p := activeColumn h))
    omega
  obtain ⟨j, k, hjk, hj, hk⟩ := hpairs
  have hij := inactive_internal h (by omega) hends j hj
  have hik := inactive_internal h (by omega) hends k hk
  exact ⟨j, k, hjk,
    inactive_imp_frozenColumn h hh j hij.1 hij.2 hm hj,
    inactive_imp_frozenColumn h hh k hik.1 hik.2 hm hk⟩

/-- The union of both actual extremum sets bounds their combined count. -/
theorem numExtrema_le_split (h : Cell m n → ℤ) :
    numExtrema h ≤ (minima h).card + (maxima h).card := by
  classical
  have heq : Finset.univ.filter (IsStrictLocalExtremum h) = maxima h ∪ minima h := by
    ext v
    simp [maxima, minima, IsStrictLocalExtremum]
  rw [numExtrema, heq]
  exact (Finset.card_union_le _ _).trans_eq (Nat.add_comm _ _)

/-- An oversized residual rectangle admits a signed deletion inside a frozen run. -/
theorem residual_width_reduction (a b : ℕ) (h : Cell m n → ℤ)
    (hm : 0 < m) (hn : 2 ≤ n) (hr : Residual a b h)
    (hwide : 2 * (a + b) - 1 < n) :
    ∃ (j k : Fin n) (hfrz : frozenColumn h j),
      j.val + 1 = k.val ∧ frozenColumn h k ∧
      Residual a b (contractAt h hm j hfrz) := by
  have hd : numExtrema h ≤ a + b := by
    simpa only [hr.2.1, hr.2.2.1] using numExtrema_le_split h
  obtain ⟨j, k, hjk, hj, hk⟩ :=
    exists_adjacent_frozen_of_width h hr.1.1 hm hn (a + b) hd hwide
  exact ⟨j, k, hj, hjk, hk, contractAt_residual a b h hm j hj hr⟩

end D5.S3.Combinatorics.Geometry.MiuraCoreResidual
