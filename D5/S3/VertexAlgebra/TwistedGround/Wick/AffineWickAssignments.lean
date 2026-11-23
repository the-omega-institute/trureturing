/- GID: D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite linear transport of affine Wick words by occurrence assignments. -/

import D5.S3.VertexAlgebra.TwistedGround.Wick.AffineOccurrenceWick

/-! A finite transport matrix assigns a compact native label independently
to each occurrence of a surviving Wick word. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.AffineWickAssignments

open AffineOccurrenceWick (wick)
open NativeAffineTransport (transportCovariance transportMean)

variable {X J : Type*} [Fintype J]

/-- Sum over independent native labels at every position, with the
transport coefficient of the label assigned at that position. -/
def assign (U : Matrix X J ℂ) : List X → (List J → ℂ) → ℂ
  | [], f => f []
  | a :: l, f => ∑ j, U a j * assign U l (fun w => f (j :: w))

private theorem assign_congr (U : Matrix X J ℂ) (l : List X) (f g : List J → ℂ)
    (h : ∀ w, w.length = l.length → f w = g w) :
    assign U l f = assign U l g := by
  induction l generalizing f g with
  | nil => exact h [] rfl
  | cons a l ih =>
    simp only [assign]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih _ _ (fun w hw => h (j :: w) (by simp [hw]))]

private theorem assign_mul (U : Matrix X J ℂ) (l : List X) (f : List J → ℂ) (c : ℂ) :
    assign U l (fun w => c * f w) = c * assign U l f := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [assign, Finset.mul_sum, ih]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem assign_add (U : Matrix X J ℂ) (l : List X) (f g : List J → ℂ) :
    assign U l (fun w => f w + g w) = assign U l f + assign U l g := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    simp only [assign, ih, mul_add, Finset.sum_add_distrib]

private theorem assign_sum (U : Matrix X J ℂ) (l : List X) {K : Type*}
    (s : Finset K) (f : K → List J → ℂ) :
    assign U l (fun w => ∑ j ∈ s, f j w) = ∑ j ∈ s, assign U l (f j) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [assign, ih, Finset.mul_sum]
    exact Finset.sum_comm

private theorem assign_erase (U : Matrix X J ℂ) (l : List X) (i : Fin l.length)
    (k : Option J → ℂ) (F : List J → ℂ) :
    assign U l (fun w => k w[i.val]? * F (w.eraseIdx i)) =
      (∑ j, U (l.get i) j * k (some j)) * assign U (l.eraseIdx i) F := by
  induction l generalizing k F with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    refine Fin.cases ?_ (fun t => ?_) i
    · simp only [assign, Fin.val_zero, List.get_cons_zero, List.eraseIdx_cons_zero,
        List.getElem?_cons_zero, assign_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [assign, Fin.val_succ, List.get_cons_succ', List.eraseIdx_cons_succ,
        List.getElem?_cons_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih t k (fun w => F (j :: w))]
      ring

omit [Fintype J] in
private theorem wick_cons_at_length (A : Matrix J J ℂ) (μ : J → ℂ) (a : J)
    (l : List X) (w : List J) (hw : w.length = l.length) :
    wick A μ (a :: w) = μ a * wick A μ w +
      ∑ i : Fin l.length, (w[i.val]?.elim 0 (A a)) * wick A μ (w.eraseIdx i) := by
  rw [wick]
  congr 1
  apply Finset.sum_equiv (finCongr hw)
  · simp
  · intro i _
    simp [List.get_eq_getElem, i.isLt]

/-- The Wick value of a transported affine source is the exact finite
sum of native Wick values over all independent surviving mode assignments. -/
theorem wick_transport
    (U : Matrix X J ℂ) (A : Matrix J J ℂ) (μ : J → ℂ) (l : List X) :
    wick (transportCovariance U A) (transportMean U μ) l = assign U l (wick A μ) := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [wick, assign]
    | cons a l =>
      have hT (b : X) : transportCovariance U A a b = ∑ j, ∑ k, U a j * A j k * U b k := rfl
      have hM : transportMean U μ a = ∑ j, U a j * μ j := rfl
      rw [wick, assign, hM, ih l (Nat.lt_succ_self _)]
      simp only [hT]
      have he (j : J) : assign U l (fun w => wick A μ (j :: w)) =
          μ j * assign U l (wick A μ) +
          ∑ i : Fin l.length,
            (∑ k, U (l.get i) k * A j k) * assign U (l.eraseIdx i) (wick A μ) := by
        rw [assign_congr U l _ _ (fun w hw => wick_cons_at_length A μ j l w hw),
          assign_add, assign_mul, assign_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Option.elim_some] using assign_erase U l i (fun y => y.elim 0 (A j)) (wick A μ)
      simp only [he, mul_add, Finset.sum_add_distrib]
      let F (j : J) (i : Fin l.length) :=
        (∑ k, U (l.get i) k * A j k) * assign U (l.eraseIdx i) (wick A μ)
      have hswap : (∑ j, U a j * ∑ i, F j i) = ∑ i, ∑ j, U a j * F j i := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      rw [hswap]
      congr 1
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        rw [ih (l.eraseIdx i) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..)), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [F]
        simp only [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring

end D5.S3.VertexAlgebra.TwistedGround.AffineWickAssignments
