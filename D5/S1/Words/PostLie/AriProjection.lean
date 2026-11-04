/- GID: D5/S1/Words/PostLie/AriProjection
   generality: I
   mirror-B: D5/B/S1/Words/PostLie/AriProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ordinary pure-word coefficient projection controls ari action support. -/


import D5.S1.Words.PostLie.AriWordOperations

/-! Pure-word projections and the level support of the original letter action. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section
namespace D5.S1.Words.PostLie.AriProjection

open scoped BigOperators
open D5.S1.Words.PostLie.AriWordOperations

private theorem lift_word_coeff (k d : ℕ) (w : List ℕ) :
    ((FreeMonoid.lift (fun s => if s = k then (Polynomial.X : Polynomial ℚ) else 0))
      (FreeMonoid.ofList w)).coeff d = if w = List.replicate d k then 1 else 0 := by
  induction w generalizing d with
  | nil => cases d <;> simp [FreeMonoid.lift_ofList, Polynomial.coeff_one]
  | cons a w ih =>
    by_cases ha : a = k
    · subst a
      cases d with
      | zero => simp [FreeMonoid.lift_ofList]
      | succ d =>
        simpa [FreeMonoid.lift_ofList, List.replicate_succ, Polynomial.coeff_X_mul] using ih d
    · simp [FreeMonoid.lift_ofList, ha]
      intro h
      cases d <;> simp_all [List.replicate_succ]

/-- The ordinary coefficient of `X^d` is exactly the pure-word coefficient,
including the empty word and arbitrary rational coefficients. -/
theorem pureProjection_coeff (k d : ℕ) (p : H) :
    (pureProjection k p).coeff d = p.coeff (FreeMonoid.ofList (List.replicate d k)) := by
  classical
  have h : (Polynomial.lcoeff ℚ d).comp (pureProjection k).toLinearMap =
      (Finsupp.lapply (FreeMonoid.ofList (List.replicate d k))).comp
        (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap := by
    apply wordBasis.ext
    intro w
    change (pureProjection k (wordBasis w)).coeff d =
      (MonoidAlgebra.single w (1 : ℚ)).coeff (FreeMonoid.ofList (List.replicate d k))
    simp only [pureProjection, wordBasis, MonoidAlgebra.basis_apply,
      MonoidAlgebra.lift_single, one_smul, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    have hs := lift_word_coeff k d w.toList
    rw [FreeMonoid.ofList_toList] at hs
    by_cases hw : w = FreeMonoid.ofList (List.replicate d k)
    · have hl : w.toList = List.replicate d k := by
        simpa only [FreeMonoid.toList_ofList] using congrArg FreeMonoid.toList hw
      simpa only [hw, hl, FreeMonoid.toList_ofList, ite_true] using hs
    · have hl : w.toList ≠ List.replicate d k := by
        intro he
        exact hw (FreeMonoid.toList.injective he)
      simpa only [hw, hl, ite_false] using hs
  exact LinearMap.congr_fun h p

/-- Every ordinary commutator is annihilated by the commutative projection. -/
theorem pureProjection_commutator (k : ℕ) (p q : H) :
    pureProjection k (commutator p q) = 0 := by
  simp [AriWordOperations.commutator, mul_comm]

private theorem nested_zero_projection (k : ℕ) (ls : List ℕ) (p : H)
    (hp : pureProjection k p = 0) : pureProjection k (nestedBracket p ls) = 0 := by
  induction ls generalizing p with
  | nil => exact hp
  | cons l ls ih => exact ih _ (pureProjection_commutator k p (letter l))

private theorem nested_nonempty_projection (k : ℕ) (ls : List ℕ) (p : H)
    (hls : ls ≠ []) : pureProjection k (nestedBracket p ls) = 0 := by
  cases ls with
  | nil => contradiction
  | cons l ls => exact nested_zero_projection k ls _ (pureProjection_commutator k p (letter l))

/-- Every nonempty left word acts on every generator with zero pure projection. -/
theorem letterAction_projection (k : ℕ) (A : Word) (s : ℕ) (ha : A ≠ 1) :
    pureProjection k (letterAction A s) = 0 := by
  classical
  unfold letterAction
  rw [ite_eq_right ha]
  split_ifs with hs
  · exact map_zero _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro l hl
  rw [map_smul, nested_nonempty_projection, smul_zero]
  intro h
  have hz : A.toList.length = 0 := by simpa using congrArg List.length h
  exact ha (by apply FreeMonoid.toList.injective; exact List.length_eq_zero_iff.mp hz)

private theorem level_zero_replicate (k : ℕ) (w : Word) (hw : level k w = 0) :
    w = FreeMonoid.ofList (List.replicate w.toList.length k) := by
  apply FreeMonoid.toList.injective
  apply List.eq_replicate_length.mpr
  have h : ∀ a ∈ w.toList, ¬a ≠ k := by simpa only [decide_eq_true_eq, not_not] using (List.countP_eq_zero.mp hw)
  intro a ha
  exact not_not.mp (h a ha)

/-- For every `k` and input generator `s`, the actual letter action has at least
as many non-`v_k` letters as the generator on which it acts. -/
theorem letterAction_above (k : ℕ) (A : Word) (s : ℕ) :
    letterAction A s ∈ above k (level k (FreeMonoid.of s)) := by
  classical
  by_cases ha : A = 1
  · simpa [letterAction, ha, letter] using above_basis k (FreeMonoid.of s)
  intro w hw
  change level k (FreeMonoid.of s) ≤ level k w
  by_cases hs : s = k
  · simp [hs]
  rw [level_of, ite_eq_right hs]
  by_contra h
  have hz : level k w = 0 := by omega
  have hp := congrArg (fun p : Polynomial ℚ => p.coeff w.toList.length)
    (letterAction_projection k A s ha)
  rw [pureProjection_coeff] at hp
  rw [← level_zero_replicate k w hz] at hp
  exact hw hp

end D5.S1.Words.PostLie.AriProjection
