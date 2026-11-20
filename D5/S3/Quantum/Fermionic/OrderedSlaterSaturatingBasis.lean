/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank criterion for attaining the ordered Slater purity drop bound. -/

import D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality

/-! # Existence of a saturating basis for an ordered Slater marginal

The deletion test identifies nonbalanced discarded columns whose coordinates
are forced to be one on the feasible fiber. Each adds one dimension to the
span of the balanced discarded columns. Attainment also requires the
retained-row coset condition and that the combined columns span the full
restricted column space.
-/

open scoped BigOperators Matrix
open Module
open D5.S3.Quantum.Fermionic OrderedSlaterCut SlaterPairCutRank
open D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound
open D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality

namespace D5.S3.Quantum.Fermionic.OrderedSlaterSaturatingBasis

private theorem sum_columns_eq_mulVec {L T : Type*} [Fintype L]
    (C : Matrix T L (ZMod 2)) (x : L → ZMod 2) :
    (∑ j, x j • C.col j) = C *ᵥ x := by
  funext t
  simp [Matrix.mulVec, dotProduct, Matrix.col_apply, mul_comm]

open Classical in
private theorem column_deletion_iff {L T : Type*} [Fintype L]
    (C : Matrix T L (ZMod 2)) (e : T → ZMod 2) (j : L) :
    e ∈ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) ↔
      ∃ x, C *ᵥ x = e ∧ x j = 0 := by
  have herase : (↑(Finset.univ.erase j) : Set L) = {k | k ≠ j} := by
    ext k
    simp
  rw [← herase, Submodule.mem_span_image_finset_iff_exists_fun']
  constructor
  · rintro ⟨x, hx⟩
    let y := Function.update x j 0
    have hy : y j = 0 := Function.update_self j 0 x
    refine ⟨y, ?_, hy⟩
    rw [← sum_columns_eq_mulVec]
    calc
      ∑ k, y k • C.col k = ∑ k ∈ Finset.univ.erase j, y k • C.col k := by
        have h := Finset.sum_erase_add Finset.univ (fun k => y k • C.col k)
          (Finset.mem_univ j)
        simpa only [hy, zero_smul, add_zero] using h.symm
      _ = e := hx ▸ Finset.sum_congr rfl (fun k hk => by
        change Function.update x j 0 k • C.col k = x k • C.col k
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])
  · rintro ⟨x, hx, hzero⟩
    have h := Finset.sum_erase_add Finset.univ (fun k => x k • C.col k)
      (Finset.mem_univ j)
    exact ⟨x, by simpa only [hzero, zero_smul, add_zero, sum_columns_eq_mulVec, hx] using h⟩

open Classical in
private theorem forced_coordinate_iff {L T : Type*} [Fintype L]
    (C : Matrix T L (ZMod 2)) (e : T → ZMod 2) (j : L) :
    (∀ x, C *ᵥ x = e → x j = 1) ↔ e ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) := by
  rw [column_deletion_iff]
  constructor
  · rintro h ⟨x, hx, hzero⟩
    exact zero_ne_one (hzero.symm.trans (h x hx))
  · intro h x hx
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (x j) with hz | ho
    · exact (h ⟨x, hx, hz⟩).elim
    · exact ho

open Classical in
private theorem column_indispensable_of_target {L T : Type*}
    (C : Matrix T L (ZMod 2)) (e : T → ZMod 2) (j : L)
    (hsol : e ∈ Submodule.span (ZMod 2) (Set.range C.col))
    (hdel : e ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j})) :
    C.col j ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) := by
  intro hj
  apply hdel
  apply Submodule.span_le.mpr _ hsol
  rintro _ ⟨k, rfl⟩
  by_cases hk : k = j
  · subst k
    exact SetLike.mem_coe.mpr hj
  · exact Submodule.subset_span ⟨k, hk, rfl⟩

open Classical in
private theorem rank_with_indispensable_columns {L T : Type*} [Finite T]
    (C : Matrix T L (ZMod 2)) (fair forced : Finset L) (hdis : Disjoint fair forced)
    (hforced : ∀ j ∈ forced, C.col j ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j})) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (C.col '' (↑(fair ∪ forced) : Set L))) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (C.col '' (↑fair : Set L))) + forced.card := by
  let := Fintype.ofFinite T
  induction forced using Finset.induction_on with
  | empty => rw [Finset.union_empty, Finset.card_empty, Nat.add_zero]
  | @insert j forced hj ih =>
      have hj_fair : j ∉ fair := fun hjQ =>
        Finset.disjoint_left.mp hdis hjQ (Finset.mem_insert_self j forced)
      have hne : (↑(fair ∪ forced) : Set L) ⊆ {k | k ≠ j} := by
        intro k hk heq
        subst k
        exact (Finset.mem_union.mp hk).elim hj_fair hj
      have hjspan : C.col j ∉ Submodule.span (ZMod 2)
          (C.col '' (↑(fair ∪ forced) : Set L)) := fun h =>
        hforced j (Finset.mem_insert_self j forced)
          (Submodule.span_mono (Set.image_mono hne) h)
      have hdis' : Disjoint fair forced := hdis.mono_right (Finset.subset_insert j forced)
      have hforced' := fun k hk => hforced k (Finset.mem_insert_of_mem hk)
      have hunion : (↑(fair ∪ insert j forced) : Set L) = insert j (↑(fair ∪ forced) : Set L) := by
        ext k
        simp
      rw [hunion, Set.image_insert_eq, Submodule.span_insert, sup_comm,
        Submodule.finrank_sup_span_singleton hjspan, ih hdis' hforced',
        Finset.card_insert_of_notMem hj, Nat.add_assoc]

open Classical in
private theorem extend_with_indispensable_columns {L T : Type*}
    (C : Matrix T L (ZMod 2)) (J : Set L) (forced : Finset L)
    (hJ : LinearIndepOn (ZMod 2) C.col J) (hdis : Disjoint J (↑forced : Set L))
    (hforced : ∀ j ∈ forced, C.col j ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j})) :
    LinearIndepOn (ZMod 2) C.col (J ∪ ↑forced) := by
  induction forced using Finset.induction_on with
  | empty => simpa using hJ
  | @insert j forced hj ih =>
      have hsubset : (↑forced : Set L) ⊆ (↑(insert j forced) : Set L) :=
        fun _ hk => Finset.mem_insert_of_mem hk
      have hne : J ∪ (↑forced : Set L) ⊆ {k | k ≠ j} := by
        intro k hk heq
        subst k
        exact hk.elim (fun hjJ =>
          Set.disjoint_left.mp hdis hjJ (Finset.mem_insert_self j forced)) hj
      have hjspan : C.col j ∉ Submodule.span (ZMod 2) (C.col '' (J ∪ ↑forced)) :=
        fun h => hforced j (Finset.mem_insert_self j forced)
          (Submodule.span_mono (Set.image_mono hne) h)
      have hli := ih (hdis.mono_right hsubset) (fun k hk => hforced k (hsubset hk))
      have hunion : J ∪ (↑(insert j forced) : Set L) = insert j (J ∪ ↑forced) := by
        ext k
        simp
      rw [hunion]
      exact hli.insert hjspan

open Classical in
private theorem saturating_basis_rank_iff {L T : Type*} [Fintype L] [Finite T]
    (C : Matrix T L (ZMod 2)) (e : T → ZMod 2) (fair forced : Finset L)
    (hforced : ∀ j, j ∈ forced ↔ j ∉ fair ∧
      e ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}))
    (hsol : e ∈ Submodule.span (ZMod 2) (Set.range C.col)) :
    (∃ J : Set L, LinearIndepOn (ZMod 2) C.col J ∧
      Submodule.span (ZMod 2) (C.col '' J) = Submodule.span (ZMod 2) (Set.range C.col) ∧
      ∀ j ∈ J, j ∈ fair ∨ ∀ x, C *ᵥ x = e → x j = 1) ↔
    finrank (ZMod 2) (Submodule.span (ZMod 2) (C.col '' (↑fair : Set L))) + forced.card =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.col)) := by
  let := Fintype.ofFinite T
  let eligible : Set L := ↑(fair ∪ forced)
  let allColumns := Submodule.span (ZMod 2) (Set.range C.col)
  have heligible (j : L) : j ∈ eligible ↔ j ∈ fair ∨ ∀ x, C *ᵥ x = e → x j = 1 := by
    rw [forced_coordinate_iff]
    simp only [eligible, Finset.mem_coe, Finset.mem_union, hforced]
    tauto
  have hdis : Disjoint fair forced := Finset.disjoint_left.mpr fun j hj hK =>
    ((hforced j).mp hK).1 hj
  have hrank := rank_with_indispensable_columns C fair forced hdis
    (fun j hj => column_indispensable_of_target C e j hsol ((hforced j).mp hj).2)
  change _ ↔ _ = finrank (ZMod 2) allColumns
  rw [← hrank]
  change _ ↔ finrank (ZMod 2) (Submodule.span (ZMod 2) (C.col '' eligible)) =
    finrank (ZMod 2) allColumns
  have hle : Submodule.span (ZMod 2) (C.col '' eligible) ≤ allColumns :=
    Submodule.span_mono (Set.image_subset_range _ _)
  constructor
  · rintro ⟨J, _, hspan, hgood⟩
    have hsub : J ⊆ eligible := fun j hj => (heligible j).mpr (hgood j hj)
    have hfull : allColumns ≤ Submodule.span (ZMod 2) (C.col '' eligible) := by
      change Submodule.span (ZMod 2) (Set.range C.col) ≤ _
      rw [← hspan]
      exact Submodule.span_mono (Set.image_mono hsub)
    rw [le_antisymm hle hfull]
  · intro h
    have hfull := Submodule.eq_of_le_of_finrank_le hle h.ge
    obtain ⟨B, hB, _, hgen, hli⟩ :=
      exists_linearIndepOn_extension (show LinearIndepOn (ZMod 2) C.col ∅ by simp)
        (Set.empty_subset (↑fair : Set L))
    let J := B ∪ (↑forced : Set L)
    have hdis' : Disjoint B (↑forced : Set L) :=
      Set.disjoint_left.mpr fun j hjB hjK => Finset.disjoint_left.mp hdis (hB hjB) hjK
    have hcol (j : L) (hj : j ∈ forced) :
        C.col j ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) :=
      column_indispensable_of_target C e j hsol ((hforced j).mp hj).2
    have hsub : J ⊆ eligible := by
      intro j hj
      exact Finset.mem_union.mpr (hj.imp (fun hjB => hB hjB) id)
    refine ⟨J, extend_with_indispensable_columns C B forced hli hdis' hcol, ?_,
      fun j hj => (heligible j).mp (hsub hj)⟩
    have hspanB : Submodule.span (ZMod 2) (C.col '' B) =
        Submodule.span (ZMod 2) (C.col '' (↑fair : Set L)) :=
      le_antisymm (Submodule.span_mono (Set.image_mono hB)) (Submodule.span_le.mpr hgen)
    change Submodule.span (ZMod 2) (C.col '' J) = allColumns
    rw [← hfull]
    change Submodule.span (ZMod 2) (C.col '' (B ∪ ↑forced)) =
      Submodule.span (ZMod 2) (C.col '' (↑(fair ∪ forced) : Set L))
    rw [Finset.coe_union, Set.image_union, Set.image_union, Submodule.span_union,
      Submodule.span_union, hspanB]


open Classical in
private theorem pivot_coset_iff_column_deletion {L T : Type*} [Finite L] [Finite T]
    [DecidableEq L] [DecidableEq T]
    (C : Matrix T L (ZMod 2)) (i : T) (j : L)
    (hsol : Pi.single i 1 ∈ Submodule.span (ZMod 2) (Set.range C.col)) :
    Pi.single j 1 - C i ∈
      Submodule.span (ZMod 2) (Set.range fun k : {k : T // k ≠ i} => C k.val) ↔
    Pi.single i 1 ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) := by
  let := Fintype.ofFinite L
  let := Fintype.ofFinite T
  let S := Submodule.span (ZMod 2) (Set.range fun k : {k : T // k ≠ i} => C k.val)
  let D := Submodule.span (ZMod 2) (C.col '' {k | k ≠ j})
  change _ ∈ S ↔ _ ∉ D
  constructor
  · intro hrow hdel
    obtain ⟨x, hx, hz⟩ := (column_deletion_iff C (Pi.single i 1) j).mp hdel
    have hvanish : S ≤ LinearMap.ker ((dotProductBilin (ZMod 2) (ZMod 2)).flip x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change (C *ᵥ x) k = 0
      rw [hx, Pi.single_eq_of_ne k.property]
    have heval := LinearMap.mem_ker.mp (hvanish hrow)
    change (Pi.single j 1 - C i) ⬝ᵥ x = 0 at heval
    rw [sub_dotProduct, single_one_dotProduct, hz] at heval
    have hi : C i ⬝ᵥ x = 1 := by simpa [Matrix.mulVec] using congrFun hx i
    rw [hi] at heval
    exact (by decide : (0 : ZMod 2) - 1 ≠ 0) heval
  · intro hdel
    obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hdel inferInstance
    have binary : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have hei : f (Pi.single i 1) = 1 := (binary _).resolve_left hf
    have hzero (k : L) (hk : k ≠ j) : f (C.col k) = 0 := by
      have hmem : f (C.col k) ∈ D.map f := ⟨C.col k, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩
      rwa [hker, Submodule.mem_bot] at hmem
    have hj : f (C.col j) = 1 := by
      refine (binary _).resolve_left ?_
      intro h
      have htop : Submodule.span (ZMod 2) (Set.range C.col) ≤ LinearMap.ker f := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        by_cases hk : k = j
        · simpa [hk] using h
        · exact hzero k hk
      exact hf (LinearMap.mem_ker.mp (htop hsol))
    let coeff : T → ZMod 2 := fun k => f (Pi.single k 1)
    have hcoeff (y : T → ZMod 2) : f y = coeff ⬝ᵥ y := by
      let b := Pi.basisFun (ZMod 2) T
      calc
        f y = f (∑ k, b.repr y k • b k) := congrArg f (b.sum_repr y).symm
        _ = _ := by
          simp only [map_sum, map_smul, b, Pi.basisFun_repr, Pi.basisFun_apply, smul_eq_mul]
          simp only [dotProduct, coeff, mul_comm]
    have hrepr : coeff ᵥ* C = Pi.single j 1 := by
      funext k
      change coeff ⬝ᵥ C.col k = (@Pi.single L (fun _ => ZMod 2) _ _ j 1) k
      rw [← hcoeff]
      by_cases hk : k = j
      · subst k
        simp [hj]
      · rw [hzero k hk, Pi.single_eq_of_ne hk]
    have hdecomp : Pi.single j 1 - C i = ∑ k ∈ Finset.univ.erase i, coeff k • C k := by
      rw [← hrepr, Matrix.vecMul_eq_sum]
      have h := Finset.sum_erase_add Finset.univ (fun k => coeff k • C k) (Finset.mem_univ i)
      change coeff i = 1 at hei
      rw [hei, one_smul] at h
      rw [← h, add_sub_cancel_right]
    rw [hdecomp]
    exact Submodule.sum_mem S (fun k hk =>
      Submodule.smul_mem S _ (Submodule.subset_span ⟨⟨k, Finset.ne_of_mem_erase hk⟩, rfl⟩))

set_option maxHeartbeats 1200000 in
-- The exact application compares two dependent cut matrices and arbitrary column subtypes.
open Classical in
/-- Under strict purity decrease, an attaining column basis exists precisely when
the retained-row conditions hold and the rank of the balanced discarded columns,
plus the number of indispensable nonbalanced columns, reaches the full rank. -/
theorem orderedMarginal_exists_saturating_basis_iff {ι : Type*} [LinearOrder ι] [Fintype ι]
    {m n : ℕ} {I : Set ι} (left : (Fin m × Bool) ↪ I) (right : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hl : ∀ k, (left (k, false) : ι) < left (k, true))
    (hr : ∀ j, (right (j, false) : ι) < right (j, true))
    (before after : Fin (m + n) → Bool → ℂ) (p : Fin m → ℝ) (q : Fin n → ℝ) (i : Fin m)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hp : ∀ k e, before (Fin.castAdd n k) e * star (before (Fin.castAdd n k) e) =
      endpointMass (p k) e)
    (hq : ∀ j e, before (Fin.natAdd m j) e * star (before (Fin.natAdd m j) e) =
      endpointMass (q j) e)
    (hp' : ∀ k e, after (Fin.castAdd n k) e * star (after (Fin.castAdd n k) e) =
      endpointMass (Function.update p i (1 / 2) k) e)
    (hq' : ∀ j e, after (Fin.natAdd m j) e * star (after (Fin.natAdd m j) e) =
      endpointMass (q j) e) :
    let A := alternationMatrix (fun k e => (left (k, e) : ι)) (fun j e => (right (j, e) : ι))
    let L := {j : Fin n // 0 < q j ∧ q j < 1}
    let active : Matrix (Fin m) L (ZMod 2) := fun k j => A k j
    let T := {k : Fin m // k = i ∨ p k = 1 / 2}
    let C : Matrix T L (ZMod 2) := fun k j => A k j
    let t : T := ⟨i, Or.inl rfl⟩
    let other := Finset.univ.filter fun k => k ≠ i ∧ p k ≠ 1 / 2
    let S := Submodule.span (ZMod 2) (Set.range fun k : {t' : T // t' ≠ t} => C k.val)
    let purity (weight : Fin (m + n) → Bool → ℂ) :=
      let B := orderedCut I (cutPairOrbitals left right weight)
      (((B * Bᴴ) ^ 2).trace).re
    let drop := purity before - purity after
    let fair := Finset.univ.filter fun j : L => q j = 1 / 2
    let e : T → ZMod 2 := Pi.single t 1
    let forced := Finset.univ.filter fun j : L =>
      j ∉ fair ∧ e ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j})
    0 < drop →
      ((∃ J : Set L, LinearIndepOn (ZMod 2) C.col J ∧
        Submodule.span (ZMod 2) (C.col '' J) = Submodule.span (ZMod 2) (Set.range C.col) ∧
        drop = squaredBias (p i) * ((∏ k ∈ other, squaredBias (p k)) *
          ∏ j : J, 2 * q j * (1 - q j))) ↔
      (∀ k : Fin m, k ∈ other → 0 < p k → p k < 1 → active k - C t ∈ S) ∧
      finrank (ZMod 2) (Submodule.span (ZMod 2) (C.col '' (↑fair : Set L))) + forced.card =
        finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.col))) := by
  intro A L active T C t other S purity drop fair e forced hdrop
  have hbefore : purity before = puritySum A p q :=
    marginal_eq_real left right hl hr before p q hp hq
  have hafter : purity after = puritySum A (Function.update p i (1 / 2)) q :=
    marginal_eq_real left right hl hr after _ q hp' hq'
  have hpositive : 0 < puritySum A p q - puritySum A (Function.update p i (1 / 2)) q := by
    rw [← hbefore, ← hafter]
    exact hdrop
  obtain ⟨⟨w, hw⟩, _⟩ := balancing_difference_ge_fiber A p q i hp0 hp1 hq0 hq1 hpositive
  have heq : C *ᵥ w = e := by
    funext k
    have h := congrFun hw k
    change (C *ᵥ w) k = if k.val = i then 1 else 0 at h
    rw [h]
    by_cases hk : k.val = i
    · have hkt : k = t := Subtype.ext hk
      simp [e, hkt, t]
    · have hkt : k ≠ t := fun h => hk (congrArg Subtype.val h)
      simp [e, hk, Pi.single_eq_of_ne hkt]
  have hsol : e ∈ Submodule.span (ZMod 2) (Set.range C.col) := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.mem_range.mpr ⟨w, heq⟩
  have hfair (j : L) : j ∈ fair ↔ q j = 1 / 2 := by simp [fair]
  have hpivot (j : L) :
      (q j ≠ 1 / 2 → Pi.single j 1 - C t ∈ S) ↔
        j ∈ fair ∨ ∀ x, C *ᵥ x = e → x j = 1 := by
    rw [hfair, forced_coordinate_iff, ← pivot_coset_iff_column_deletion C t j hsol]
    tauto
  have hbasis (J : Set L) (hlin : LinearIndepOn (ZMod 2) C.col J)
      (hspan : Submodule.span (ZMod 2) (C.col '' J) = Submodule.span (ZMod 2) (Set.range C.col)) :
      (drop = squaredBias (p i) * ((∏ k ∈ other, squaredBias (p k)) *
        ∏ j : J, 2 * q j * (1 - q j))) ↔
      (∀ k : Fin m, k ∈ other → 0 < p k → p k < 1 → active k - C t ∈ S) ∧
      (∀ j ∈ J, j ∈ fair ∨ ∀ x, C *ᵥ x = e → x j = 1) := by
    have hspan' : Submodule.span (ZMod 2) (Set.range fun j : J => C.col j) =
        Submodule.span (ZMod 2) (Set.range C.col) := by
      rw [← Set.image_eq_range]
      exact hspan
    have h := orderedMarginal_purity_drop_eq_iff left right hl hr before after p q i hp0 hp1
      hq0 hq1 hp hq hp' hq' (Equiv.Set.sumCompl J) hlin hspan' hdrop
    simp only [Equiv.Set.sumCompl_apply_inl] at h
    rw [h]
    constructor
    · rintro ⟨hJ, hR⟩
      exact ⟨hR, fun j hj => (hpivot j).mp (hJ ⟨j, hj⟩)⟩
    · rintro ⟨hR, hJ⟩
      exact ⟨fun j => (hpivot j).mpr (hJ j j.property), hR⟩
  have hforced (j : L) : j ∈ forced ↔ j ∉ fair ∧
      e ∉ Submodule.span (ZMod 2) (C.col '' {k | k ≠ j}) := by
    simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrank := saturating_basis_rank_iff C e fair forced hforced hsol
  constructor
  · rintro ⟨J, hlin, hspan, hequal⟩
    obtain ⟨hR, hJ⟩ := (hbasis J hlin hspan).mp hequal
    exact ⟨hR, hrank.mp ⟨J, hlin, hspan, hJ⟩⟩
  · rintro ⟨hR, hdim⟩
    obtain ⟨J, hlin, hspan, hJ⟩ := hrank.mpr hdim
    exact ⟨J, hlin, hspan, (hbasis J hlin hspan).mpr ⟨hR, hJ⟩⟩

end D5.S3.Quantum.Fermionic.OrderedSlaterSaturatingBasis
