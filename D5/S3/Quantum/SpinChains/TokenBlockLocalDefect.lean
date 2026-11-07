/- GID: D5/S3/Quantum/SpinChains/TokenBlockLocalDefect
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/TokenBlockLocalDefect
   mirror-E: none(waiver:exact-counting-space)
   anchors: []
   utility: none
   digest: Actual outside-occupancy slices of coefficient-one block lowering. -/
import D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open scoped BigOperators InnerProductSpace
namespace D5.S3.Quantum.SpinChains.TokenBlockLocalDefect

set_option maxHeartbeats 800000

abbrev Sites (m s : ℕ) := Fin m × Fin s
abbrev Outside (m s : ℕ) (i : Fin m) := {u : Sites m s // u.1 ≠ i}
abbrev Rank (m s r : ℕ) := {S : Finset (Sites m s) // S.card = r}
abbrev PreviousRank (m s r : ℕ) := {S : Finset (Sites m s) // S.card + 1 = r}
abbrev Space (m s r : ℕ) := EuclideanSpace ℂ (Rank m s r)
abbrev PreviousSpace (m s r : ℕ) := EuclideanSpace ℂ (PreviousRank m s r)

/-- The outside index is a set of occupied vertices, rather than its cardinality. -/
abbrev Fiber (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i)) :=
  {A : Finset (Fin s) // R.card + A.card = r}
abbrev PreviousFiber (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i)) :=
  {B : Finset (Fin s) // R.card + B.card + 1 = r}
abbrev FiberSpace (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i)) :=
  EuclideanSpace ℂ (Fiber m s r i R)
abbrev PreviousFiberSpace (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i)) :=
  EuclideanSpace ℂ (PreviousFiber m s r i R)

/-- The exact partition of the original vertex set into outside and inside vertices. -/
def siteSplit (m s : ℕ) (i : Fin m) : Outside m s i ⊕ Fin s ≃ Sites m s where
  toFun u := Sum.elim Subtype.val (fun a => (i,a)) u
  invFun u := if h : u.1 = i then Sum.inr u.2 else Sum.inl ⟨u,h⟩
  left_inv u := by
    rcases u with u | a
    · simp [u.property]
    · simp
  right_inv u := by
    dsimp
    split_ifs with h
    · exact Prod.ext h.symm rfl
    · rfl

private def subsetSplit (m s : ℕ) (i : Fin m) :
    Finset (Sites m s) ≃ Finset (Outside m s i) × Finset (Fin s) :=
  ((siteSplit m s i).symm.finsetCongr).trans Finset.sumEquiv.toEquiv

private lemma subsetSplit_card (m s : ℕ) (i : Fin m) (S : Finset (Sites m s)) :
    (subsetSplit m s i S).1.card + (subsetSplit m s i S).2.card = S.card := by
  have h := congrArg Finset.card ((subsetSplit m s i).symm_apply_apply S)
  simpa [subsetSplit, Equiv.finsetCongr, Finset.sumEquiv] using h

/-- The additive rank equation omits every invalid source fiber. -/
def rankSplit (m s r : ℕ) (i : Fin m) :
    Rank m s r ≃ Σ R : Finset (Outside m s i), Fiber m s r i R :=
  ((subsetSplit m s i).subtypeEquiv (fun S => by
    change S.card = r ↔ (subsetSplit m s i S).1.card +
      (subsetSplit m s i S).2.card = r
    rw [subsetSplit_card])).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun R A => R.card + A.card = r))

/-- The entire predecessor carrier, including fibers with no source states. -/
def previousSplit (m s r : ℕ) (i : Fin m) :
    PreviousRank m s r ≃ Σ R : Finset (Outside m s i), PreviousFiber m s r i R :=
  ((subsetSplit m s i).subtypeEquiv (fun S => by
    change S.card + 1 = r ↔ (subsetSplit m s i S).1.card +
      (subsetSplit m s i S).2.card + 1 = r
    rw [subsetSplit_card])).trans
      (Equiv.subtypeProdEquivSigmaSubtype (fun R A => R.card + A.card + 1 = r))

/-- Counting measure is transported without weights or normalization factors. -/
def split (m s r : ℕ) (i : Fin m) :
    Space m s r ≃ₗᵢ[ℂ] PiLp 2 (fun R : Finset (Outside m s i) => FiberSpace m s r i R) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (rankSplit m s r i)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (R : Finset (Outside m s i))
      (_ : Fiber m s r i R) => ℂ))

def previousCountingSplit (m s r : ℕ) (i : Fin m) :
    PreviousSpace m s r ≃ₗᵢ[ℂ]
      PiLp 2 (fun R : Finset (Outside m s i) => PreviousFiberSpace m s r i R) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (previousSplit m s r i)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (R : Finset (Outside m s i))
      (_ : PreviousFiber m s r i R) => ℂ))

/-- The source's coefficient-one block annihilation, on the full predecessor space. -/
def lower (m s r : ℕ) (i : Fin m) : Space m s r →ₗ[ℂ] PreviousSpace m s r where
  toFun f := WithLp.toLp 2 fun T => ∑ a : Fin s,
    if ha : (i,a) ∈ T.val then 0 else
      f ⟨insert (i,a) T.val, by rw [Finset.card_insert_of_notMem ha]; exact T.property⟩
  map_add' f g := by
    ext T
    simp only [PiLp.add_apply, PiLp.toLp_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  map_smul' c f := by ext T; simp [Finset.mul_sum]

/-- Diagonal physical block number, defined directly on the original subsets. -/
def number (m s r : ℕ) (i : Fin m) : Module.End ℂ (Space m s r) where
  toFun f := WithLp.toLp 2 fun S => ((S.val.filter (fun u => u.1 = i)).card : ℂ) * f S
  map_add' f g := by ext S; simp [mul_add]
  map_smul' c f := by ext S; simp [mul_left_comm]

/-- The physical defect uses the independently defined number and actual counting adjoint. -/
def defect (m s r : ℕ) (i : Fin m) : Module.End ℂ (Space m s r) :=
  (number m s r i).comp (((s : ℂ) + 1) • 1 - number m s r i) -
    (lower m s r i).adjoint.comp (lower m s r i)

end D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
