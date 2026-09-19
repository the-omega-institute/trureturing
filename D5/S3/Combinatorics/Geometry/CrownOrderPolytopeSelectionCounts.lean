/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Actual odd-block selections are counted with explicit nonnegative binomial support. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeMarkedCuts
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEndpointRecovery
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope
open scoped BigOperators

/-- The actual contribution to `A_(d+2)` from partitions with `i` blocks and
    `2m` odd blocks.  The guard is essential: when `i < d` the count is zero,
    rather than the erroneous value obtained by truncating a negative lower index. -/
theorem crownOddBlockSelection_profile_card (n i m d : ℕ) [NeZero (2 * n)]
    (hn : 2 ≤ n) (hi : 2 ≤ i) (hm : 1 ≤ m) :
    i * Nat.card {a : CrownOddBlockSelectionOfCard n (d + 2) //
      (cycleBoundaryCuts a.val.val.1).card = i ∧
        (actualOddCycleBlocks a.val.val.1).card = 2 * m} =
      (2 * n * Nat.choose i (2 * m) * Nat.choose (n + m - 1) (i - 1)) *
        (if d ≤ i then Nat.choose (2 * m) (i - d) else 0) := by
  classical
  have card_oddSelections {N d : ℕ} (P : ConnectedCyclePartition N) :
      Nat.card {S : Finset (Quotient P.toSetoid) //
        (∀ C ∈ S, Set.ncard {v : Fin N | Quotient.mk'' v = C} % 2 = 1) ∧
          Nat.card (Quotient P.toSetoid) - S.card = d} =
        if d ≤ Nat.card (Quotient P.toSetoid) then
          Nat.choose (actualOddCycleBlocks P).card (Nat.card (Quotient P.toSetoid) - d)
        else 0 := by
    classical
    let i := Nat.card (Quotient P.toSetoid)
    let O := actualOddCycleBlocks P
    have hmem (C : Quotient P.toSetoid) : C ∈ O ↔
        Set.ncard {v : Fin N | Quotient.mk'' v = C} % 2 = 1 := by
      obtain ⟨v, rfl⟩ := Quotient.exists_rep C
      simp [O, actualOddCycleBlocks, Nat.odd_iff]
    have hsub (S : Finset (Quotient P.toSetoid)) :
        (∀ C ∈ S, Set.ncard {v : Fin N | Quotient.mk'' v = C} % 2 = 1) ↔ S ⊆ O := by
      simp only [Finset.subset_iff, hmem]
    have hbound (S : Finset (Quotient P.toSetoid)) : S.card ≤ i := by
      simpa [i, Nat.card_eq_fintype_card] using Finset.card_le_univ S
    by_cases hd : d ≤ i
    · rw [if_pos hd]
      let e : {S : Finset (Quotient P.toSetoid) //
          (∀ C ∈ S, Set.ncard {v : Fin N | Quotient.mk'' v = C} % 2 = 1) ∧
            i - S.card = d} ≃ {S // S ∈ O.powersetCard (i - d)} :=
        { toFun := fun S => ⟨S.val, Finset.mem_powersetCard.mpr
            ⟨(hsub S.val).mp S.property.1, by have := hbound S.val; have := S.property.2; omega⟩⟩
          invFun := fun S => ⟨S.val, (hsub S.val).mpr (Finset.mem_powersetCard.mp S.property).1,
            by have := (Finset.mem_powersetCard.mp S.property).2; omega⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans (by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard])
    · rw [if_neg hd]
      let : IsEmpty {S : Finset (Quotient P.toSetoid) //
          (∀ C ∈ S, Set.ncard {v : Fin N | Quotient.mk'' v = C} % 2 = 1) ∧
            i - S.card = d} := ⟨fun S => by have := S.property.2; omega⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
  let A := PrescribedOddConnectedCyclePartition (2 * n) i (2 * m)
  let F (P : A) := {S : Finset (Quotient P.val.toSetoid) //
    (∀ C ∈ S, Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1) ∧
      Nat.card (Quotient P.val.toSetoid) - S.card = d}
  have hcompatible (P : A) : crownCycleCompatible P.val := by
    have hnontrivial : ∃ u v, ¬ P.val.toSetoid.r u v := by
      by_contra h
      push Not at h
      have he := (cycleBoundaryCuts_eq_empty_iff (by omega) P.val).mpr h
      have hc := P.property.1
      rw [he, Finset.card_empty] at hc
      omega
    have hpos : 0 < (actualOddCycleBlocks P.val).card := by rw [P.property.2]; omega
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
    apply (crownCycleCompatible_iff_exists_oddBlock hn P.val hnontrivial).mpr
    exact ⟨C, Nat.odd_iff.mp (Finset.mem_filter.mp hC).2⟩
  let e : {a : CrownOddBlockSelectionOfCard n (d + 2) //
      (cycleBoundaryCuts a.val.val.1).card = i ∧
        (actualOddCycleBlocks a.val.val.1).card = 2 * m} ≃ Σ P : A, F P :=
    { toFun := fun a => ⟨⟨a.val.val.val.1, a.property⟩,
        ⟨a.val.val.val.2, a.val.val.property.2, by simpa using a.val.property⟩⟩
      invFun := fun a => ⟨⟨⟨⟨a.1.val, a.2.val⟩, hcompatible a.1, a.2.property.1⟩,
        by simpa using a.2.property.2⟩, a.1.property⟩
      left_inv := fun a => by cases a; rfl
      right_inv := fun a => by cases a; rfl }
  let : Finite (ConnectedCyclePartition (2 * n)) :=
    Finite.of_injective (fun P : ConnectedCyclePartition (2 * n) => P.toSetoid.r) (by
      intro P Q h
      have hs : P.toSetoid = Q.toSetoid := Setoid.ext fun u v =>
        Iff.of_eq (congrFun (congrFun h u) v)
      cases P
      cases Q
      cases hs
      rfl)
  letI : Fintype A := Fintype.ofFinite A
  have hf (P : A) : Nat.card (F P) =
      if d ≤ i then Nat.choose (2 * m) (i - d) else 0 := by
    have hq := quotient_card_eq_boundaryCuts_card (by omega) P.val
      (by rw [P.property.1]; exact hi)
    have hc := card_oddSelections (d := d) P.val
    change Nat.card (F P) = _ at hc
    simpa only [hq, P.property.1, P.property.2] using hc
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    ← Nat.mul_assoc]
  exact congrArg (fun x => x * (if d ≤ i then Nat.choose (2 * m) (i - d) else 0))
    (card_prescribedOddConnectedCyclePartition_identity n i m hn hi)

/-- The unique one-block cycle partition contributes only its empty selection,
    and therefore contributes exactly one element to `A₃` and none to other `A_k`. -/
theorem crownOddBlockSelection_oneBlock_card (n d : ℕ) (hn : 0 < n) :
    Nat.card {a : CrownOddBlockSelectionOfCard n (d + 2) //
      Nat.card (Quotient a.val.val.1.toSetoid) = 1} = if d = 1 then 1 else 0 := by
  classical
  let T := {a : CrownOddBlockSelectionOfCard n (d + 2) //
    Nat.card (Quotient a.val.val.1.toSetoid) = 1}
  let P : ConnectedCyclePartition (2 * n) :=
    { toSetoid := ⊤
      connected := by
        intro u v _
        exact (SimpleGraph.cycleGraph_preconnected u v).mono (fun _ _ h => ⟨trivial, h⟩) }
  have hPcard : Nat.card (Quotient P.toSetoid) = 1 := by
    letI : Subsingleton (Quotient P.toSetoid) := ⟨by
      intro C D
      induction C using Quotient.inductionOn with | h u =>
        induction D using Quotient.inductionOn with | h v => exact Quotient.sound trivial⟩
    exact Nat.card_of_subsingleton (Quotient.mk'' (⟨0, by omega⟩ : Fin (2 * n)))
  have hPcompat : crownCycleCompatible P := by
    intro C D _ _
    induction C using Quotient.inductionOn with | h u =>
      induction D using Quotient.inductionOn with | h v => exact Quotient.sound trivial
  have hshape (a : T) : a.val.val.val.1 = P ∧ a.val.val.val.2 = ∅ ∧ d = 1 := by
    let Q := a.val.val.val.1
    have hqcard : Nat.card (Quotient Q.toSetoid) = 1 := a.property
    have hsingle := (Nat.card_eq_one_iff_unique.mp hqcard).1
    have hall (u v : Fin (2 * n)) : Q.toSetoid.r u v :=
      Quotient.exact (hsingle.elim (Quotient.mk'' u) (Quotient.mk'' v))
    have hQP : Q = P := by
      have hs : Q.toSetoid = P.toSetoid := Setoid.ext fun u v =>
        ⟨fun _ => trivial, fun _ => hall u v⟩
      have hext (R S : ConnectedCyclePartition (2 * n))
          (h : R.toSetoid = S.toSetoid) : R = S := by
        cases R
        cases S
        cases h
        rfl
      exact hext _ _ hs
    have hempty : a.val.val.val.2 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro C hC
      have hc := a.val.val.property.2 C hC
      have hset : {v : Fin (2 * n) | (Quotient.mk'' v : Quotient Q.toSetoid) = C} =
          Set.univ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact hsingle.elim _ _
      change Set.ncard {v : Fin (2 * n) |
        (Quotient.mk'' v : Quotient Q.toSetoid) = C} % 2 = 1 at hc
      rw [hset, Set.ncard_univ, Nat.card_fin] at hc
      omega
    refine ⟨hQP, hempty, ?_⟩
    have hc := a.val.property
    rw [hempty, Finset.card_empty, Nat.sub_zero] at hc
    have := a.property
    omega
  by_cases hd : d = 1
  · rw [if_pos hd]
    let t : T := ⟨⟨⟨⟨P, ∅⟩, hPcompat, by simp⟩,
      by simp only [Finset.card_empty, Nat.sub_zero, Nat.add_sub_cancel, hPcard, hd]⟩, hPcard⟩
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨t, ?_⟩
    intro a
    obtain ⟨hP, hS, _⟩ := hshape a
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext hP
    rw [hS]
    exact (show ∀ Q R : ConnectedCyclePartition (2 * n), Q = R →
      HEq (∅ : Finset (Quotient Q.toSetoid)) (∅ : Finset (Quotient R.toSetoid)) from by
        intro Q R h
        cases h
        rfl) _ _ hP
  · rw [if_neg hd]
    let : IsEmpty T := ⟨fun a => hd (hshape a).2.2⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- The full source count, obtained from actual partitions and selected odd
    blocks.  The isolated `A₃` contribution is separate from the nontrivial
    profiles; every binomial lower index has its nonnegative support guard. -/
theorem crownOddBlockSelection_card (n d : ℕ) [NeZero (2 * n)] (hn : 2 ≤ n) :
    Nat.card (CrownOddBlockSelectionOfCard n (d + 2)) =
      (if d = 1 then 1 else 0) +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 2 (2 * n)},
          ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (i.val / 2)},
            ((2 * n * Nat.choose i.val (2 * m.val) *
              Nat.choose (n + m.val - 1) (i.val - 1)) *
                (if d ≤ i.val then Nat.choose (2 * m.val) (i.val - d) else 0)) / i.val := by
  classical
  let A := CrownOddBlockSelectionOfCard n (d + 2)
  let I := {i : ℕ // i ∈ Finset.Icc 2 (2 * n)}
  let J (i : I) := {m : ℕ // m ∈ Finset.Icc 1 (i.val / 2)}
  let O := {a : A // Nat.card (Quotient a.val.val.1.toSetoid) = 1}
  let F (i : I) (m : J i) := {a : A //
    (cycleBoundaryCuts a.val.val.1).card = i.val ∧
      (actualOddCycleBlocks a.val.val.1).card = 2 * m.val}
  let toA : O ⊕ (Σ i : I, Σ m : J i, F i m) → A :=
    Sum.elim Subtype.val (fun a => a.2.2.val)
  have hq (i : I) (m : J i) (a : F i m) :
      Nat.card (Quotient a.val.val.val.1.toSetoid) = i.val := by
    rw [quotient_card_eq_boundaryCuts_card (by omega) _
      (by rw [a.property.1]; exact (Finset.mem_Icc.mp i.property).1), a.property.1]
  have hbij : Function.Bijective toA := by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
          cases y with
          | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
          | inr y =>
              have hx := x.property
              change Nat.card (Quotient x.val.val.val.1.toSetoid) = 1 at hx
              change x.val = y.2.2.val at hxy
              rw [hxy, hq] at hx
              have := (Finset.mem_Icc.mp y.1.property).1
              omega
      | inr x =>
          cases y with
          | inl y =>
              have hy := y.property
              change x.2.2.val = y.val at hxy
              rw [← hxy, hq] at hy
              have := (Finset.mem_Icc.mp x.1.property).1
              omega
          | inr y =>
              rcases x with ⟨i, m, x⟩
              rcases y with ⟨j, l, y⟩
              change x.val = y.val at hxy
              have hij : i = j := by
                apply Subtype.ext
                have h := congrArg (fun a : A => (cycleBoundaryCuts a.val.val.1).card) hxy
                exact x.property.1.symm.trans (h.trans y.property.1)
              cases hij
              have hml : m = l := by
                apply Subtype.ext
                have h := congrArg (fun a : A => (actualOddCycleBlocks a.val.val.1).card) hxy
                have hx := x.property.2
                have hy := y.property.2
                omega
              cases hml
              have heq : x = y := Subtype.ext hxy
              cases heq
              rfl
    · intro a
      by_cases hone : Nat.card (Quotient a.val.val.1.toSetoid) = 1
      · exact ⟨Sum.inl ⟨a, hone⟩, rfl⟩
      · let P := a.val.val.1
        have hnontrivial : ∃ u v, ¬ P.toSetoid.r u v := by
          by_contra h
          push Not at h
          have hsingle : Subsingleton (Quotient P.toSetoid) := ⟨by
            intro C D
            induction C using Quotient.inductionOn with | h u =>
              induction D using Quotient.inductionOn with | h v => exact Quotient.sound (h u v)⟩
          letI := hsingle
          exact hone (Nat.card_of_subsingleton
            (Quotient.mk'' (⟨0, by omega⟩ : Fin (2 * n))))
        have hcuts := cycleBoundaryCuts_card_ge_two_of_crownCycleCompatible hn P
          hnontrivial a.val.property.1
        have hcutsLe : (cycleBoundaryCuts P).card ≤ 2 * n := by
          simpa using Finset.card_le_univ (cycleBoundaryCuts P)
        let i : I := ⟨(cycleBoundaryCuts P).card, Finset.mem_Icc.mpr ⟨hcuts, hcutsLe⟩⟩
        have heven := actualOddCycleBlocks_card_even n P
        have htwice : 2 * ((actualOddCycleBlocks P).card / 2) =
            (actualOddCycleBlocks P).card := Nat.two_mul_div_two_of_even heven
        obtain ⟨C, hC⟩ := (crownCycleCompatible_iff_exists_oddBlock hn P hnontrivial).mp
          a.val.property.1
        have hCmem : C ∈ actualOddCycleBlocks P := by
          obtain ⟨v, rfl⟩ := Quotient.exists_rep C
          simpa [actualOddCycleBlocks, Nat.odd_iff] using hC
        have hpos := Finset.card_pos.mpr ⟨C, hCmem⟩
        have hoddLe : (actualOddCycleBlocks P).card ≤ i.val := by
          have h := Finset.card_le_univ (actualOddCycleBlocks P)
          rw [← Nat.card_eq_fintype_card,
            quotient_card_eq_boundaryCuts_card (by omega) P hcuts] at h
          exact h
        let m : J i := ⟨(actualOddCycleBlocks P).card / 2,
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
        exact ⟨Sum.inr ⟨i, m, ⟨a, rfl, htwice.symm⟩⟩, rfl⟩
  let : Finite (ConnectedCyclePartition (2 * n)) :=
    Finite.of_injective (fun P : ConnectedCyclePartition (2 * n) => P.toSetoid.r) (by
      intro P Q h
      have hs : P.toSetoid = Q.toSetoid := Setoid.ext fun u v =>
        Iff.of_eq (congrFun (congrFun h u) v)
      cases P
      cases Q
      cases hs
      rfl)
  letI : Fintype I := Fintype.ofFinset (Finset.Icc 2 (2 * n)) (fun _ => Iff.rfl)
  letI (i : I) : Fintype (J i) :=
    Fintype.ofFinset (Finset.Icc 1 (i.val / 2)) (fun _ => Iff.rfl)
  have hcard := (Nat.card_congr (Equiv.ofBijective toA hbij)).symm
  rw [Nat.card_sum, Nat.card_sigma] at hcard
  change Nat.card A = _
  rw [hcard, crownOddBlockSelection_oneBlock_card n d (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro m _
  have h := crownOddBlockSelection_profile_card n i.val m.val d hn
    (Finset.mem_Icc.mp i.property).1 (Finset.mem_Icc.mp m.property).1
  have hi : 0 < i.val := by have := (Finset.mem_Icc.mp i.property).1; omega
  have hdiv := congrArg (fun x => x / i.val) h
  rw [Nat.mul_div_cancel_left _ hi] at hdiv
  exact hdiv

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
