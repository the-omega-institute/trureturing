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

/-! Actual subset coordinates and the local coefficient-one block operators. -/

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
  ((subsetSplit m s i).subtypeEquiv
    (q := fun RA : Finset (Outside m s i) × Finset (Fin s) => RA.1.card + RA.2.card = r)
    (fun S => by rw [subsetSplit_card])).trans
      (Equiv.subtypeProdEquivSigmaSubtype
        (fun (R : Finset (Outside m s i)) (A : Finset (Fin s)) => R.card + A.card = r))

/-- The entire predecessor carrier, including fibers with no source states. -/
def previousSplit (m s r : ℕ) (i : Fin m) :
    PreviousRank m s r ≃ Σ R : Finset (Outside m s i), PreviousFiber m s r i R :=
  ((subsetSplit m s i).subtypeEquiv
    (q := fun RA : Finset (Outside m s i) × Finset (Fin s) => RA.1.card + RA.2.card + 1 = r)
    (fun S => by rw [subsetSplit_card])).trans
      (Equiv.subtypeProdEquivSigmaSubtype
        (fun (R : Finset (Outside m s i)) (A : Finset (Fin s)) => R.card + A.card + 1 = r))

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
    simp only [PiLp.add_apply]
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

/-- Assemble the two actual occupied sets in the original vertex labeling. -/
def assemble (m s : ℕ) (i : Fin m) (R : Finset (Outside m s i)) (A : Finset (Fin s)) :
    Finset (Sites m s) :=
  (R.disjSum A).map (siteSplit m s i).toEmbedding

private lemma assemble_card (m s : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (A : Finset (Fin s)) :
    (assemble m s i R A).card = R.card + A.card := by simp [assemble]

private lemma assemble_mem_inside (m s : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (A : Finset (Fin s)) (a : Fin s) :
    (i,a) ∈ assemble m s i R A ↔ a ∈ A := by
  change (siteSplit m s i) (Sum.inr a) ∈
    (R.disjSum A).map (siteSplit m s i).toEmbedding ↔ _
  simp

private lemma assemble_insert_inside (m s : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (A : Finset (Fin s)) (a : Fin s) :
    assemble m s i R (insert a A) = insert (i,a) (assemble m s i R A) := by
  have h : R.disjSum (insert a A) = insert (Sum.inr a) (R.disjSum A) := by
    ext u
    rcases u with u | b <;> simp
  simp only [assemble, h, Finset.map_insert]
  rfl

private lemma split_apply (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) (A : Fiber m s r i R) :
    split m s r i f R A = f ⟨assemble m s i R A.val, by
      rw [assemble_card]; exact A.property⟩ := rfl

private lemma previousCountingSplit_apply (m s r : ℕ) (i : Fin m) (f : PreviousSpace m s r)
    (R : Finset (Outside m s i)) (B : PreviousFiber m s r i R) :
    previousCountingSplit m s r i f R B = f ⟨assemble m s i R B.val, by
      rw [assemble_card]; exact B.property⟩ := rfl

private def fiberLower (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i)) :
    FiberSpace m s r i R →ₗ[ℂ] PreviousFiberSpace m s r i R where
  toFun f := WithLp.toLp 2 fun B => ∑ a : Fin s,
    if ha : a ∈ B.val then 0 else
      f ⟨insert a B.val, by rw [Finset.card_insert_of_notMem ha]; omega⟩
  map_add' f g := by
    ext B
    simp only [PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  map_smul' c f := by ext B; simp [Finset.mul_sum]

private lemma lower_slices (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) :
    previousCountingSplit m s r i (lower m s r i f) R =
      fiberLower m s r i R (split m s r i f R) := by
  ext B
  rw [previousCountingSplit_apply]
  change (∑ a : Fin s, _) = ∑ a : Fin s, _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ B.val
  · simp [assemble_mem_inside, ha]
  · have hn : (i,a) ∉ assemble m s i R B.val := by
      simpa only [assemble_mem_inside] using ha
    simp only [ha, hn, ↓reduceDIte]
    rw [split_apply]
    exact congrArg (fun S : Rank m s r => f S)
      (Subtype.ext (assemble_insert_inside m s i R B.val a).symm)

private def fiberNativeEquiv (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) : Fiber m s r i R ≃ NativeJohnsonCoercivity.Rank s (r-R.card) :=
  Equiv.subtypeEquivRight (fun A => by omega)

private def previousFiberNativeEquiv (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) : PreviousFiber m s r i R ≃
      NativeJohnsonCoercivity.PreviousRank s (r-R.card) :=
  Equiv.subtypeEquivRight (fun A => by omega)

private def nativeSlice (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) : FiberSpace m s r i R ≃ₗᵢ[ℂ] NativeJohnsonCoercivity.Layer s (r-R.card) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (fiberNativeEquiv m s r i R hR)

private def nativePreviousSlice (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) : PreviousFiberSpace m s r i R ≃ₗᵢ[ℂ]
      NativeJohnsonCoercivity.PreviousLayer s (r-R.card) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (previousFiberNativeEquiv m s r i R hR)

private lemma lower_native (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) (f : FiberSpace m s r i R) :
    nativePreviousSlice m s r i R hR (fiberLower m s r i R f) =
      NativeJohnsonCoercivity.lower s (r-R.card) (nativeSlice m s r i R hR f) := by
  ext B
  rfl

/-- The actual within-block permutation of occupied subsets. -/
def rankPermutation (m s r : ℕ) (i : Fin m) (π : Equiv.Perm (Fin s)) :
    Equiv.Perm (Rank m s r) :=
  ((Equiv.Perm.prodExtendRight i π).finsetCongr).subtypeEquiv (fun S => by simp)

/-- Pullback by the inverse permutation, with the original counting norm. -/
def permutationAction (m s r : ℕ) (i : Fin m) (π : Equiv.Perm (Fin s)) :
    Space m s r ≃ₗᵢ[ℂ] Space m s r :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (rankPermutation m s r i π)

/-- The independently specified invariant subspace on the full occupancy carrier. -/
def invariantSubspace (m s r : ℕ) (i : Fin m) : Submodule ℂ (Space m s r) where
  carrier := {f | ∀ π : Equiv.Perm (Fin s), permutationAction m s r i π f = f}
  zero_mem' := by intro π; exact map_zero _
  add_mem' := by
    intro f g hf hg π
    rw [map_add, hf π, hg π]
  smul_mem' := by
    intro c f hf π
    rw [map_smul, hf π]

/-- Orthogonal projection is specified before any arithmetic averaging formula. -/
def projection (m s r : ℕ) (i : Fin m) : Module.End ℂ (Space m s r) :=
  (invariantSubspace m s r i).starProjection.toLinearMap

private lemma assemble_block_card (m s : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (A : Finset (Fin s)) :
    ((assemble m s i R A).filter (fun u => u.1 = i)).card = A.card := by
  let j : Fin s ↪ Sites m s := ⟨fun a => (i,a), fun a b h => (Prod.mk.inj h).2⟩
  have he : (assemble m s i R A).filter (fun u => u.1 = i) = A.map j := by
    ext u
    rcases u with ⟨k,a⟩
    by_cases h : k = i
    · subst k
      constructor
      · intro ht
        exact Finset.mem_map.mpr
          ⟨a, (assemble_mem_inside m s i R A a).mp (Finset.mem_filter.mp ht).1, rfl⟩
      · intro ht
        rcases Finset.mem_map.mp ht with ⟨b, hb, hba⟩
        have heq : b = a := congrArg Prod.snd hba
        subst b
        exact Finset.mem_filter.mpr ⟨(assemble_mem_inside m s i R A a).mpr hb, rfl⟩
    · constructor
      · intro ht
        exact False.elim (h (Finset.mem_filter.mp ht).2)
      · intro ht
        rcases Finset.mem_map.mp ht with ⟨b, _, hba⟩
        exact False.elim (h (congrArg Prod.fst hba).symm)
  rw [he, Finset.card_map]

private lemma number_slices (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) (A : Fiber m s r i R) :
    split m s r i (number m s r i f) R A = (A.val.card : ℂ) * split m s r i f R A := by
  rw [split_apply, split_apply]
  change (((assemble m s i R A.val).filter (fun u => u.1 = i)).card : ℂ) * _ = _
  rw [assemble_block_card]

private lemma output_only_zero (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) (hR : R.card + s + 1 = r) :
    previousCountingSplit m s r i (lower m s r i f) R = 0 := by
  rw [lower_slices]
  have hz : split m s r i f R = 0 := by
    ext A
    have hc := Finset.card_le_univ A.val
    have ha := A.property
    simp only [Fintype.card_fin] at hc
    omega
  rw [hz, map_zero]

private def fiberPermutation (m s r : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (π : Equiv.Perm (Fin s)) :
    Equiv.Perm (Fiber m s r i R) :=
  π.finsetCongr.subtypeEquiv (fun A => by simp)

private lemma assemble_permutation (m s : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (A : Finset (Fin s)) (π : Equiv.Perm (Fin s)) :
    (assemble m s i R A).map (Equiv.Perm.prodExtendRight i π).toEmbedding =
      assemble m s i R (A.map π.toEmbedding) := by
  let e := Equiv.sumCongr (Equiv.refl (Outside m s i)) π
  have he : (R.disjSum A).map e.toEmbedding = R.disjSum (A.map π.toEmbedding) := by
    ext u
    rcases u with u | a <;> simp [e]
  simp only [assemble, Finset.map_map]
  rw [← he, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro u
  rcases u with u | a
  · exact Equiv.Perm.prodExtendRight_apply_ne π u.property u.val.2
  · simp [siteSplit, e]

private lemma action_slices_forward (m s r : ℕ) (i : Fin m)
    (π : Equiv.Perm (Fin s)) (f : Space m s r)
    (R : Finset (Outside m s i)) (A : Fiber m s r i R) :
    split m s r i (permutationAction m s r i π f) R (fiberPermutation m s r i R π A) =
      split m s r i f R A := by
  rw [split_apply, split_apply]
  change f ((rankPermutation m s r i π).symm _) = f _
  apply congrArg (fun S : Rank m s r => f S)
  apply (rankPermutation m s r i π).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (assemble_permutation m s i R A.val π).symm

private lemma invariant_iff_constant (m s r : ℕ) (i : Fin m) (f : Space m s r) :
    f ∈ invariantSubspace m s r i ↔
      ∀ (R : Finset (Outside m s i)) (A B : Fiber m s r i R),
        split m s r i f R A = split m s r i f R B := by
  constructor
  · intro hf R A B
    obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq A.val B.val (by
      have := A.property
      have := B.property
      omega)
    have he : fiberPermutation m s r i R π A = B := Subtype.ext hπ
    have h := action_slices_forward m s r i π f R A
    rw [show permutationAction m s r i π f = f from hf π, he] at h
    exact h.symm
  · intro hf π
    apply (split m s r i).injective
    ext R A
    let B := (fiberPermutation m s r i R π).symm A
    have h := action_slices_forward m s r i π f R B
    rw [show fiberPermutation m s r i R π B = A from
      (fiberPermutation m s r i R π).apply_symm_apply A] at h
    exact h.trans (hf R B A)

private def countingAverage (m s r : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (f : FiberSpace m s r i R) : FiberSpace m s r i R :=
  WithLp.toLp 2 fun _ => (Fintype.card (Fiber m s r i R) : ℂ)⁻¹ * ∑ A, f A

private lemma sum_sub_average (m s r : ℕ) (i : Fin m)
    (R : Finset (Outside m s i)) (f : FiberSpace m s r i R) :
    ∑ A, (f - countingAverage m s r i R f) A = 0 := by
  classical
  by_cases h : Nonempty (Fiber m s r i R)
  · letI := h
    have hc : (Fintype.card (Fiber m s r i R) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [PiLp.sub_apply, countingAverage, PiLp.toLp_apply,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_self]
  · haveI : IsEmpty (Fiber m s r i R) := not_nonempty_iff.mp h
    exact Finset.sum_eq_zero (fun A _ => isEmptyElim A)

/-- The independently defined all-permutation projection is counting average on every outside set. -/
theorem projection_counting_slices (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) :
    split m s r i (projection m s r i f) R =
      WithLp.toLp 2 (fun _ : Fiber m s r i R =>
        (Fintype.card (Fiber m s r i R) : ℂ)⁻¹ * ∑ A, split m s r i f R A) := by
  classical
  let a := WithLp.toLp 2 (fun R : Finset (Outside m s i) =>
    countingAverage m s r i R (split m s r i f R))
  let v := (split m s r i).symm a
  have hv : split m s r i v = a := (split m s r i).apply_symm_apply a
  have hmem : v ∈ invariantSubspace m s r i := by
    rw [invariant_iff_constant]
    intro R A B
    rw [hv]
    rfl
  have horth : ∀ w ∈ invariantSubspace m s r i, inner ℂ (f-v) w = 0 := by
    intro w hw
    rw [← (split m s r i).inner_map_map, PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro R _
    by_cases h : Nonempty (Fiber m s r i R)
    · let A₀ := Classical.choice h
      have hc := (invariant_iff_constant m s r i w).mp hw R
      rw [map_sub, hv]
      change inner ℂ (split m s r i f R -
        countingAverage m s r i R (split m s r i f R)) (split m s r i w R) = 0
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply]
      simp_rw [hc _ A₀]
      have hz := sum_sub_average m s r i R (split m s r i f R)
      rw [← Finset.mul_sum, ← map_sum, hz, map_zero, mul_zero]
    · haveI : IsEmpty (Fiber m s r i R) := not_nonempty_iff.mp h
      rw [PiLp.inner_apply]
      exact Finset.sum_eq_zero (fun A _ => isEmptyElim A)
  have hp := (invariantSubspace m s r i).eq_starProjection_of_mem_of_inner_eq_zero hmem horth
  change split m s r i ((invariantSubspace m s r i).starProjection f) R = _
  rw [hp, hv]
  rfl

private lemma number_polynomial_slices (m s r : ℕ) (i : Fin m) (f : Space m s r)
    (R : Finset (Outside m s i)) :
    split m s r i (number m s r i (((s : ℂ)+1) • f - number m s r i f)) R =
      (((r-R.card : ℕ) : ℂ) * ((s : ℂ)+1-(r-R.card : ℕ))) • split m s r i f R := by
  ext A
  rw [number_slices]
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [number_slices]
  have hq : A.val.card = r-R.card := by have := A.property; omega
  rw [hq]
  ring

/-- Exact physical energy, with the entire original predecessor norm. -/
theorem energy (m s r : ℕ) (i : Fin m) (f : Space m s r) :
    (inner ℂ f (defect m s r i f)).re =
      (∑ R : Finset (Outside m s i),
        ((r-R.card : ℕ) : ℝ) * ((s : ℝ)+1-(r-R.card : ℕ)) * ‖split m s r i f R‖^2) -
        ‖lower m s r i f‖^2 := by
  have he : inner ℂ f (number m s r i (((s : ℂ)+1) • f - number m s r i f)) =
      ∑ R : Finset (Outside m s i),
        (((r-R.card : ℕ) : ℂ) * ((s : ℂ)+1-(r-R.card : ℕ))) *
          inner ℂ (split m s r i f R) (split m s r i f R) := by
    rw [← (split m s r i).inner_map_map, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro R _
    rw [number_polynomial_slices, inner_smul_right]
  unfold defect
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Module.End.one_apply, inner_sub_right]
  rw [(lower m s r i).adjoint_inner_right, inner_self_eq_norm_sq_to_K, he]
  simp [Complex.re_sum, inner_self_eq_norm_sq_to_K, Complex.mul_re, pow_two]

private lemma average_native (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (hR : R.card ≤ r) (f : FiberSpace m s r i R) :
    nativeSlice m s r i R hR (countingAverage m s r i R f) =
      NativeJohnsonCoercivity.average s (r-R.card) (nativeSlice m s r i R hR f) := by
  ext A
  change (Fintype.card (Fiber m s r i R) : ℂ)⁻¹ * ∑ B, f B =
    (Fintype.card (NativeJohnsonCoercivity.Rank s (r-R.card)) : ℂ)⁻¹ *
      ∑ B, nativeSlice m s r i R hR f B
  rw [Fintype.card_congr (fiberNativeEquiv m s r i R hR)]
  congr 1
  exact ((fiberNativeEquiv m s r i R hR).symm.sum_comp (fun B => f B)).symm

private lemma fiber_coercivity (m s r : ℕ) (i : Fin m) (R : Finset (Outside m s i))
    (f : FiberSpace m s r i R) :
    (s : ℝ) * ‖f-countingAverage m s r i R f‖^2 ≤
      ((r-R.card : ℕ) : ℝ) * ((s : ℝ)+1-(r-R.card : ℕ)) * ‖f‖^2 -
        ‖fiberLower m s r i R f‖^2 := by
  classical
  by_cases hn : Nonempty (Fiber m s r i R)
  · obtain ⟨A⟩ := hn
    have hA := A.property
    have hc := Finset.card_le_univ A.val
    simp only [Fintype.card_fin] at hc
    have hR : R.card ≤ r := by omega
    have hq : r-R.card ≤ s := by omega
    let g := nativeSlice m s r i R hR f
    have hh := NativeJohnsonCoercivity.result s (r-R.card) hq g
    have he : (inner ℂ g (NativeJohnsonCoercivity.defect s (r-R.card) g)).re =
        ((r-R.card : ℕ) : ℝ) * ((s : ℝ)+1-(r-R.card : ℕ)) * ‖g‖^2 -
          ‖NativeJohnsonCoercivity.lower s (r-R.card) g‖^2 := by
      simp only [NativeJohnsonCoercivity.defect, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, LinearMap.comp_apply,
        inner_sub_right, inner_smul_right]
      rw [(NativeJohnsonCoercivity.lower s (r-R.card)).adjoint_inner_right]
      simp [inner_self_eq_norm_sq_to_K, Complex.mul_re, pow_two]
    rw [he] at hh
    change (s : ℝ) * ‖nativeSlice m s r i R hR f -
      NativeJohnsonCoercivity.average s (r-R.card) (nativeSlice m s r i R hR f)‖^2 ≤ _ at hh
    rw [← average_native, ← map_sub, ← lower_native] at hh
    simpa only [LinearIsometryEquiv.norm_map, g] using hh
  · haveI : IsEmpty (Fiber m s r i R) := not_nonempty_iff.mp hn
    have hf : f = 0 := by ext A; exact isEmptyElim A
    have ha : countingAverage m s r i R f = 0 := by ext A; exact isEmptyElim A
    simp [hf, ha]

/-- Physical local coercivity for arbitrary complex states, all ranks, and every outside set. -/
theorem result (m s r : ℕ) (i : Fin m) (f : Space m s r) :
    (s : ℝ) * ‖f-projection m s r i f‖^2 ≤ (inner ℂ f (defect m s r i f)).re := by
  rw [energy, ← (split m s r i).norm_map (f-projection m s r i f),
    PiLp.norm_sq_eq_of_L2, Finset.mul_sum,
    ← (previousCountingSplit m s r i).norm_map (lower m s r i f),
    PiLp.norm_sq_eq_of_L2, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro R _
  simpa only [map_sub, PiLp.sub_apply, projection_counting_slices, lower_slices,
    countingAverage] using fiber_coercivity m s r i R (split m s r i f R)

end D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
