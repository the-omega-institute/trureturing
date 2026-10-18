import D5.S3.ConceptDynamics.Coding.OriginalRoot.OriginalRootPeriod6Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding
open CountedOrderTypeGyration.SignedSupport
  (prunedShard keyWeight sourceKeys targetKeys middleWords rankVectors vectorTerm
    SkeletonMinimal rankWidth coefficient vectorTerm_zero_of_nonminimal sSlots KeyLT skeleton
    Key KeyWordLT KeyLeast)
open ResetQ4LocalizedGyrationCharacter (originalAdjacency)
open scoped BigOperators Matrix

theorem middleWords_one {d : ℕ} [NeZero d]
    (R : Matrix (Fin 8) (Fin 8) ℤ) (a : Fin d → Fin 8) :
    middleWords R (1 : Matrix (Fin 8) (Fin 8) ℤ) a =
      if h : ∀ t, R (a t) (a (t + 1)) ≠ 0 then {nextWord a} else ∅ := by
  classical
  ext b
  simp only [middleWords, Fintype.mem_piFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs with hv
  · simp only [Finset.mem_singleton]
    change (∀ t, R (a t) (b t) ≠ 0 ∧
      (1 : Matrix (Fin 8) (Fin 8) ℤ) (b t) (a (t + 1)) ≠ 0) ↔ b = nextWord a
    constructor
    · intro hb
      funext t
      have hs := (hb t).2
      by_contra hne
      have hne' : b t ≠ a (t + 1) := by
        intro heq
        apply hne
        simpa [nextWord] using heq
      apply hs
      simp [Matrix.one_apply, hne']
    · intro hb
      subst b
      intro t
      constructor
      · exact hv t
      · simp [Matrix.one_apply, nextWord]
  · constructor
    · intro hb
      obtain ⟨t, ht⟩ := not_forall.mp hv
      have hs := (hb t).2
      have hba : b t = a (t + 1) := by
        by_contra hne
        have hne' : b t ≠ a (t + 1) := hne
        apply hs
        simp [Matrix.one_apply, hne']
      exfalso
      apply ht
      simpa [hba] using (hb t).1
    · intro hb
      have : False := by simpa using hb
      exact this.elim

theorem rankVectors_one_next {d : ℕ} [NeZero d] (a : Fin d → Fin 8) :
    rankVectors (1 : Matrix (Fin 8) (Fin 8) ℤ) (a, nextWord a) = {zeroRanks} := by
  classical
  ext l
  constructor
  · intro hl
    have hlt (t : Fin d) : l t < 1 := by
      have ht := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hl).1) t
      simpa [Matrix.one_apply, nextWord] using ht
    have hz : l = zeroRanks := by
      funext t
      have hlt' := hlt t
      have hzero : l t = 0 := by omega
      simpa [zeroRanks, hzero]
    simpa [hz]
  · intro hl
    have hz : l = zeroRanks := by simpa using hl
    subst l
    rw [rankVectors, Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro t
      simp [Matrix.one_apply, nextWord, zeroRanks]
    · intro t
      unfold rankWidth
      apply Finset.card_pos.mpr
      refine ⟨0, Finset.mem_image.mpr ⟨t, ?_, rfl⟩⟩
      simp [sSlots, nextWord]

theorem vectorTerm_one_next {d : ℕ} [NeZero d] (a : Fin d → Fin 8) :
    vectorTerm (1 : Matrix (Fin 8) (Fin 8) ℤ) (a, nextWord a) zeroRanks =
      keyWeight (sourceKeys (a, nextWord a) zeroRanks)
        (targetKeys (a, nextWord a) zeroRanks) := by
  classical
  unfold vectorTerm
  have hcoeff : coefficient (1 : Matrix (Fin 8) (Fin 8) ℤ)
      (a, nextWord a) zeroRanks = 1 := by
    unfold coefficient
    apply Finset.prod_eq_one
    intro e _
    by_cases he : e.1 = e.2 <;> simp [Matrix.one_apply, he]
  rw [hcoeff, mul_one]

theorem prunedShard_time_eq_fast (i : Fin 8) :
    prunedShard 5 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
      fastTimeShard i := by
  classical
  unfold prunedShard fastTimeShard
  have hterm (a : Fin 6 → Fin 8) :
      (∑ b ∈ (middleWords originalAdjacency
          (1 : Matrix (Fin 8) (Fin 8) ℤ) a).filter
            (fun b => SkeletonMinimal (a,b)),
        ∑ l ∈ rankVectors (1 : Matrix (Fin 8) (Fin 8) ℤ) (a,b),
          vectorTerm (1 : Matrix (Fin 8) (Fin 8) ℤ) (a,b) l) =
        if h : validAdj6 originalAdjacency a then
          keyWeight (sourceKeys (a, nextWord a) zeroRanks)
            (targetKeys (a, nextWord a) zeroRanks)
        else 0 := by
    by_cases hv : validAdj6 originalAdjacency a
    · have hv' : ∀ t, originalAdjacency (a t) (a (t + 1)) ≠ 0 :=
        (validAdj6_iff _ _).mp hv
      have hmiddle : middleWords originalAdjacency
          (1 : Matrix (Fin 8) (Fin 8) ℤ) a = {nextWord a} := by
        rw [middleWords_one]
        simp [hv']
      rw [hmiddle]
      by_cases hs : SkeletonMinimal (a, nextWord a)
      · have hfilter :
            ({nextWord a} : Finset (Fin 6 → Fin 8)).filter
                (fun b => SkeletonMinimal (a,b)) = {nextWord a} := by
          apply Finset.filter_eq_self.2
          intro b hb
          have hb' : b = nextWord a := by simpa only [Finset.mem_singleton] using hb
          subst b
          exact hs
        rw [hfilter]
        simp only [Finset.sum_singleton]
        rw [rankVectors_one_next]
        simp [vectorTerm_one_next, hv]
      · have hzero : keyWeight (sourceKeys (a, nextWord a) zeroRanks)
            (targetKeys (a, nextWord a) zeroRanks) = 0 := by
          rw [← vectorTerm_one_next a]
          exact vectorTerm_zero_of_nonminimal (1 : Matrix (Fin 8) (Fin 8) ℤ)
            (a, nextWord a) zeroRanks hs
        have hfilter :
            ({nextWord a} : Finset (Fin 6 → Fin 8)).filter
                (fun b => SkeletonMinimal (a,b)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro b hb
          have hb' : b = nextWord a := by simpa only [Finset.mem_singleton] using hb
          subst b
          exact hs
        rw [hfilter]
        simp [hv, hzero]
    · have hv' : ¬∀ t, originalAdjacency (a t) (a (t + 1)) ≠ 0 := by
        intro h
        exact hv ((validAdj6_iff _ _).mpr h)
      have hmiddle : middleWords originalAdjacency
          (1 : Matrix (Fin 8) (Fin 8) ℤ) a = ∅ := by
        rw [middleWords_one]
        simp [hv']
      rw [hmiddle]
      simp [hv]
  apply Finset.sum_congr rfl
  intro tail _
  exact hterm (Fin.cons i tail)

theorem prunedShard_time_eq_fast6 (i : Fin 8) :
    prunedShard 5 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
      fastTimeShardFast i := by
  calc
    prunedShard 5 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
        fastTimeShard i := prunedShard_time_eq_fast i
    _ = fastTimeShardFast i := by
      unfold fastTimeShard fastTimeShardFast
      apply Finset.sum_congr rfl
      intro tail _
      dsimp
      split_ifs <;> simp [keyWeightFast6_eq]


end D5.S3.ConceptDynamics.Coding
