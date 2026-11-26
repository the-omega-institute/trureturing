/- GID: D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite affine Wick expansion by occurrence positions. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient

/-! The native affine moment as a sum over ordered occurrence matchings. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick

open NativeAffineExternalCoefficient (jetOccupation)
open OriginalChargedRowSource (affineMoment affineMoment_step affineMoment_zero)

variable {X I : Type*}

/-- Affine Wick evaluation removes the head as a singleton or pairs it with
one tail position. Even equal labels at different positions give separate terms. -/
def wick (A : Matrix X X ℂ) (μ : X → ℂ) : List X → ℂ
  | [] => 1
  | a :: l => μ a * wick A μ l +
      ∑ j : Fin l.length, A a (l.get j) * wick A μ (l.eraseIdx j)
termination_by l => l.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem occupation_erase_add (f : X → I) (l : List X) (j : Fin l.length) :
    jetOccupation ((l.eraseIdx j).map f) + Finsupp.single (f (l.get j)) 1 =
      jetOccupation (l.map f) := by
  induction l with
  | nil => exact Fin.elim0 j
  | cons a l ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [jetOccupation]
    · simp only [Fin.val_succ, List.eraseIdx_cons_succ, List.get_cons_succ',
        List.map_cons, jetOccupation]
      rw [add_right_comm, ih k]

open scoped Classical in
private theorem occupation_count (f : X → I) (l : List X) (i : I) :
    jetOccupation (l.map f) i = (Finset.univ.filter fun j : Fin l.length => f (l.get j) = i).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  induction l with
  | nil => simp [jetOccupation]
  | cons a l ih =>
    change _ = ∑ j : Fin (l.length + 1), if f ((a :: l).get j) = i then 1 else 0
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero, List.get_cons_succ', List.map_cons, jetOccupation,
      Finsupp.add_apply, Finsupp.single_apply, ih]
    by_cases h : f a = i <;> simp [h, eq_comm, add_comm]

variable [Fintype I]

private theorem sum_partners (A : Matrix I I ℂ) (μ : I → ℂ) (f : X → I)
    (a : X) (l : List X) :
    (∑ i, (jetOccupation (l.map f) i : ℂ) * A (f a) i *
      affineMoment A μ (jetOccupation (l.map f) - Finsupp.single i 1)) =
      ∑ j : Fin l.length, A (f a) (f (l.get j)) *
        affineMoment A μ (jetOccupation ((l.eraseIdx j).map f)) := by
  classical
  let F (i : I) := A (f a) i *
    affineMoment A μ (jetOccupation (l.map f) - Finsupp.single i 1)
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin l.length => f (l.get j) = i), F i := by
      simp only [Finset.sum_const, nsmul_eq_mul, ← occupation_count, F, mul_assoc]
    _ = ∑ j : Fin l.length, F (f (l.get j)) :=
      Finset.sum_fiberwise' Finset.univ (fun j : Fin l.length => f (l.get j)) F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [F]
      rw [tsub_eq_of_eq_add (occupation_erase_add f l j).symm]

/-- Pulling back the compact covariance and mean computes the exact native
moment of the mapped occupation. No injectivity condition on the labels is needed. -/
theorem affineMoment_eq_wick (A : Matrix I I ℂ) (μ : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (f : X → I) (l : List X) :
    affineMoment A μ (jetOccupation (l.map f)) =
      wick (A.submatrix f f) (μ ∘ f) l := by
  classical
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [jetOccupation, wick, affineMoment_zero]
    | cons a l =>
      simp only [List.map_cons, jetOccupation, affineMoment_step A μ hs,
        sum_partners, wick, Function.comp_apply, Matrix.submatrix_apply]
      rw [ih l (Nat.lt_succ_self _)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))]

/-- Both native moments agree under an arbitrary map of occurrence labels,
including collisions on a diagonal covariance entry. -/
theorem affineMoment_pullback [Fintype X] (A : Matrix I I ℂ)
    (μ : I → ℂ) (hs : ∀ i j, A i j = A j i) (f : X → I) (l : List X) :
    affineMoment (A.submatrix f f) (μ ∘ f) (jetOccupation l) =
      affineMoment A μ (jetOccupation (l.map f)) := by
  rw [affineMoment_eq_wick A μ hs f l]
  simpa only [List.map_id, Matrix.submatrix_id_id, Function.comp_id] using
    (affineMoment_eq_wick (A.submatrix f f) (μ ∘ f) (fun i j => hs (f i) (f j)) id l)

end D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick
