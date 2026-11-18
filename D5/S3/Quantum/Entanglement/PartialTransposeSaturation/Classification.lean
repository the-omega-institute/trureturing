/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Schmidt-rank-two partial-transpose saturation classification. -/

/- admission_basis: open-problem-resolution
   Preregistered external problem: Wang--Chen 2025 Section VI, issue #30687.
   proof_shape: result inherits the constructive chain splitting, regular
   pairing and singular-rank content through its live helper declarations. -/

import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Decomposition
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Singular
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open scoped BigOperators

/-- Orientation and index of a singular pencil block. Index zero contributes
only a common zero row or column. -/
structure SingularIndex where
  right : Bool
  degree : ℕ
  deriving DecidableEq

namespace SingularIndex

def horizontal (a : SingularIndex) : ℕ :=
  if a.degree = 0 then 0 else if a.right then a.degree else a.degree + 1

def vertical (a : SingularIndex) : ℕ :=
  if a.degree = 0 then 0 else if a.right then a.degree + 1 else a.degree

def tensor (a b : SingularIndex) : ℕ :=
  a.degree * b.degree + if a.right = b.right then 0 else min a.degree b.degree

def transposed (a b : SingularIndex) : ℕ :=
  a.degree * b.degree + if a.right = b.right then min a.degree b.degree else 0

def defect (a b : SingularIndex) : ℕ :=
  if a.right = b.right then a.degree * b.degree - min a.degree b.degree
  else a.degree * b.degree + 2 * min a.degree b.degree

private theorem min_le_product (r s : ℕ) : min r s ≤ r * s := by
  by_cases hr : r = 0
  · simp [hr]
  · have h := Nat.min_le_right r s
    have hr' : 1 ≤ r := by omega
    nlinarith

/-- Every singular block pair has a nonnegative additive defect. -/
private theorem defect_identity (a b : SingularIndex) :
    a.transposed b + a.defect b = 2 * a.tensor b := by
  unfold transposed defect tensor
  split_ifs <;> have h := min_le_product a.degree b.degree <;> omega

/-- For positive indices, vanishing forces both index one and the same
orientation. This is the strict part of the singular-block calculation. -/
private theorem defect_zero_iff (a b : SingularIndex)
    (ha : 0 < a.degree) (hb : 0 < b.degree) :
    a.defect b = 0 ↔ a.right = b.right ∧ a.degree = 1 ∧ b.degree = 1 := by
  unfold defect
  by_cases he : a.right = b.right
  · simp only [he, ↓reduceIte, true_and]
    constructor
    · intro hz
      have hle := min_le_product a.degree b.degree
      have hprod : a.degree * b.degree = min a.degree b.degree := by omega
      have h₁ := Nat.min_le_left a.degree b.degree
      have h₂ := Nat.min_le_right a.degree b.degree
      have ha' : 1 ≤ a.degree := ha
      have hb' : 1 ≤ b.degree := hb
      have hamul : a.degree ≤ a.degree * b.degree := by nlinarith
      have hbmul : b.degree ≤ a.degree * b.degree := by nlinarith
      have hab : a.degree = b.degree := by omega
      constructor <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      simp [h₁, h₂]
  · simp only [he, ↓reduceIte, false_and, iff_false]
    have hp : 0 < a.degree * b.degree := Nat.mul_pos ha hb
    omega

end SingularIndex

section FiniteFamilies

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A finite sum can saturate only when each block-pair defect vanishes. -/
private theorem block_defects_zero_of_saturation (a : ι → SingularIndex) (b : κ → SingularIndex)
    (hsat : (∑ i, ∑ j, (a i).transposed (b j)) =
      2 * ∑ i, ∑ j, (a i).tensor (b j)) :
    ∀ i j, (a i).defect (b j) = 0 := by
  classical
  have hid : (∑ i, ∑ j, (a i).transposed (b j)) +
      (∑ i, ∑ j, (a i).defect (b j)) =
      2 * ∑ i, ∑ j, (a i).tensor (b j) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, SingularIndex.defect_identity]
    simp_rw [Finset.mul_sum]
  have hz : (∑ i, ∑ j, (a i).defect (b j)) = 0 := by omega
  intro i j
  have hi := (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_univ i)
  exact (Finset.sum_eq_zero_iff.mp hi) j (Finset.mem_univ j)

/-- Once each coefficient pair has a positive singular block, saturation
forces a common orientation and index one for every positive block. -/
private theorem singular_support_of_saturation (a : ι → SingularIndex) (b : κ → SingularIndex)
    (ha : ∃ i, 0 < (a i).degree) (hb : ∃ j, 0 < (b j).degree)
    (hsat : (∑ i, ∑ j, (a i).transposed (b j)) =
      2 * ∑ i, ∑ j, (a i).tensor (b j)) :
    ∃ o : Bool,
      (∀ i, 0 < (a i).degree → (a i).right = o ∧ (a i).degree = 1) ∧
      (∀ j, 0 < (b j).degree → (b j).right = o ∧ (b j).degree = 1) := by
  obtain ⟨i₀, hi₀⟩ := ha
  obtain ⟨j₀, hj₀⟩ := hb
  have hz := block_defects_zero_of_saturation a b hsat
  have h₀ := (SingularIndex.defect_zero_iff (a i₀) (b j₀) hi₀ hj₀).mp (hz i₀ j₀)
  refine ⟨(b j₀).right, ?_, ?_⟩
  · intro i hi
    have h := (SingularIndex.defect_zero_iff (a i) (b j₀) hi hj₀).mp (hz i j₀)
    exact ⟨h.1, h.2.1⟩
  · intro j hj
    have h := (SingularIndex.defect_zero_iff (a i₀) (b j) hi₀ hj).mp (hz i₀ j)
    exact ⟨h.1.symm.trans h₀.1, h.2.2⟩

/-- The common-orientation classification gives precisely the two possible
concatenation-rank ratios on both sides. -/
private theorem singular_weights_of_saturation (a : ι → SingularIndex) (b : κ → SingularIndex)
    (ha : ∃ i, 0 < (a i).degree) (hb : ∃ j, 0 < (b j).degree)
    (hsat : (∑ i, ∑ j, (a i).transposed (b j)) =
      2 * ∑ i, ∑ j, (a i).tensor (b j)) :
    ((∑ i, (a i).vertical) = 2 * ∑ i, (a i).horizontal ∧
      (∑ j, (b j).vertical) = 2 * ∑ j, (b j).horizontal) ∨
    ((∑ i, (a i).horizontal) = 2 * ∑ i, (a i).vertical ∧
      (∑ j, (b j).horizontal) = 2 * ∑ j, (b j).vertical) := by
  classical
  obtain ⟨o, hA, hB⟩ := singular_support_of_saturation a b ha hb hsat
  have weight (c : SingularIndex) (hc : 0 < c.degree → c.right = o ∧ c.degree = 1) :
      (if o then c.vertical else c.horizontal) =
        2 * (if o then c.horizontal else c.vertical) := by
    by_cases hz : c.degree = 0
    · simp [SingularIndex.horizontal, SingularIndex.vertical, hz]
    · obtain ⟨ho, hd⟩ := hc (by omega)
      cases o <;> simp [SingularIndex.horizontal, SingularIndex.vertical, hd, ho]
  cases ho : o
  · right
    constructor
    · simpa [ho, Finset.mul_sum] using
        Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
          (fun i _ => weight (a i) (hA i))
    · simpa [ho, Finset.mul_sum] using
        Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
          (fun j _ => weight (b j) (hB j))
  · left
    constructor
    · simpa [ho, Finset.mul_sum] using
        Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
          (fun i _ => weight (a i) (hA i))
    · simpa [ho, Finset.mul_sum] using
        Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
          (fun j _ => weight (b j) (hB j))

end FiniteFamilies

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open LinearMap Submodule Module
open scoped BigOperators TensorProduct
open ChainSplitting.FinitePair

/-- A piece retains its actual chain projections or its proved regularity. -/
inductive PencilAtom
  | right {p : Pencil ℂ} {r : ℕ} (split : SplitData p r)
  | left {p : Pencil ℂ} {r : ℕ} (split : SplitData p r)
  | regular (p : Pencil ℂ) (reduced : RightReduced p)
      (square : finrank ℂ p.domain = finrank ℂ p.codomain)

namespace PencilAtom

def pencil : PencilAtom → Pencil ℂ
  | .right s => s.block
  | .left s => s.block.dual
  | .regular p _ _ => p

def singularIndex : PencilAtom → SingularIndex
  | .right (r := r) _ => ⟨true, r⟩
  | .left (r := r) _ => ⟨false, r⟩
  | .regular _ _ _ => ⟨true, 0⟩

/-- After saturation is imposed, every remaining regular piece is zero. -/
def Effective : PencilAtom → Prop
  | .regular p _ _ => p.first = 0 ∧ p.second = 0
  | _ => True

private theorem regular_rank (p q : Pencil ℂ) (hp : RightReduced p)
    (hs : finrank ℂ p.domain = finrank ℂ p.codomain) :
    p.dual.tensorRank q = p.tensorRank q :=
  Regularity.tensor_rank_dual_eq_of_reduced p q hp hs

/-- A regular second factor also leaves the tensor rank unchanged. -/
private theorem regular_right_rank (p q : Pencil ℂ) (hq : RightReduced q)
    (hs : finrank ℂ q.domain = finrank ℂ q.codomain) :
    p.dual.tensorRank q = p.tensorRank q := by
  rw [Pencil.tensorRank_dual_left_exchange, Pencil.tensorRank_comm,
    regular_rank q p hq hs, Pencil.tensorRank_comm]

private theorem tensorRank_zero_left (p q : Pencil ℂ)
    (hf : p.first = 0) (hg : p.second = 0) : p.tensorRank q = 0 := by
  unfold Pencil.tensorRank
  rw [hf, hg]
  simp

private theorem tensorRank_zero_right (p q : Pencil ℂ)
    (hf : q.first = 0) (hg : q.second = 0) : p.tensorRank q = 0 := by
  unfold Pencil.tensorRank
  rw [hf, hg]
  simp

private theorem tensorRank_zero_dual_left (p q : Pencil ℂ)
    (hf : p.first = 0) (hg : p.second = 0) : p.dual.tensorRank q = 0 := by
  change finrank ℂ (LinearMap.range
    (TensorProduct.map p.first.dualMap q.first +
      TensorProduct.map p.second.dualMap q.second)) = 0
  rw [hf, hg]
  have hd : (0 : p.domain →ₗ[ℂ] p.codomain).dualMap = 0 := by
    ext φ x
    simp
  rw [hd]
  simp

/-- Effective pieces have exactly the concatenation weights of their singular
index, including the zero-index cases. -/
private theorem effective_weights (a : PencilAtom) (ha : a.Effective) :
    a.pencil.horizontalRank = a.singularIndex.horizontal ∧
      a.pencil.verticalRank = a.singularIndex.vertical := by
  cases a with
  | regular p hp hs =>
    obtain ⟨hf, hg⟩ := ha
    change p.horizontalRank = 0 ∧ p.verticalRank = 0
    have hcoprod : p.first.coprod p.second = 0 := by
      rw [hf, hg]
      apply LinearMap.ext
      intro x
      simp [LinearMap.coprod_apply]
    have hprod : p.first.prod p.second = 0 := by rw [hf, hg]; rfl
    change finrank ℂ (LinearMap.range (p.first.coprod p.second)) = 0 ∧
      finrank ℂ (LinearMap.range (p.first.prod p.second)) = 0
    rw [hcoprod, hprod]
    simp
  | right s =>
    constructor
    · change finrank ℂ (LinearMap.range (s.firstBlock.coprod s.secondBlock)) = _
      rw [LinearMap.range_coprod, s.horizontal_rank]
      simp [singularIndex, SingularIndex.horizontal]
    · change finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) = _
      rw [s.vertical_rank]
      simp [singularIndex, SingularIndex.vertical]
  | left s =>
    change s.block.dual.horizontalRank = _ ∧ s.block.dual.verticalRank = _
    rw [Pencil.horizontalRank_dual, Pencil.verticalRank_dual]
    constructor
    · change finrank ℂ (LinearMap.range (s.firstBlock.prod s.secondBlock)) = _
      rw [s.vertical_rank]
      simp [singularIndex, SingularIndex.horizontal]
    · change finrank ℂ (LinearMap.range (s.firstBlock.coprod s.secondBlock)) = _
      rw [LinearMap.range_coprod, s.horizontal_rank]
      simp [singularIndex, SingularIndex.vertical]

/-- The tensor ranks of effective atoms are the numerical singular-block ranks. -/
private theorem effective_ranks (a b : PencilAtom) (ha : a.Effective) (hb : b.Effective) :
    a.pencil.tensorRank b.pencil = a.singularIndex.tensor b.singularIndex ∧
      a.pencil.dual.tensorRank b.pencil = a.singularIndex.transposed b.singularIndex := by
  cases a with
  | regular p hp hs =>
    obtain ⟨hf, hg⟩ := ha
    change p.tensorRank b.pencil = _ ∧ p.dual.tensorRank b.pencil = _
    rw [tensorRank_zero_left p b.pencil hf hg, tensorRank_zero_dual_left p b.pencil hf hg]
    simp [singularIndex, SingularIndex.tensor, SingularIndex.transposed]
  | right s =>
    cases b with
    | regular q hq hs =>
      obtain ⟨hf, hg⟩ := hb
      change s.block.tensorRank q = _ ∧ s.block.dual.tensorRank q = _
      rw [tensorRank_zero_right s.block q hf hg, tensorRank_zero_right s.block.dual q hf hg]
      simp [singularIndex, SingularIndex.tensor, SingularIndex.transposed]
    | right t =>
      change s.block.tensorRank t.block = _ ∧ s.block.dual.tensorRank t.block = _
      constructor
      · exact s.tensor_rank t
      · exact s.partialTranspose_rank t
    | left t =>
      change s.block.tensorRank t.block.dual = _ ∧
        s.block.dual.tensorRank t.block.dual = _
      rw [Pencil.tensorRank_dual_dual]
      exact ⟨s.mixed_tensor_rank t, s.tensor_rank t⟩
  | left s =>
    cases b with
    | regular q hq hs =>
      obtain ⟨hf, hg⟩ := hb
      change s.block.dual.tensorRank q = _ ∧ s.block.dual.dual.tensorRank q = _
      rw [tensorRank_zero_right s.block.dual q hf hg,
        tensorRank_zero_right s.block.dual.dual q hf hg]
      simp [singularIndex, SingularIndex.tensor, SingularIndex.transposed]
    | right t =>
      change s.block.dual.tensorRank t.block = _ ∧
        s.block.dual.dual.tensorRank t.block = _
      rw [Pencil.tensorRank_dual_dual_left]
      exact ⟨s.partialTranspose_rank t, s.tensor_rank t⟩
    | left t =>
      change s.block.dual.tensorRank t.block.dual = _ ∧
        s.block.dual.dual.tensorRank t.block.dual = _
      rw [Pencil.tensorRank_dual_dual, Pencil.tensorRank_dual_dual_left]
      exact ⟨s.tensor_rank t, s.mixed_tensor_rank t⟩

private theorem rank_bound_of_effective (a b : PencilAtom) (ha : a.Effective)
    (hb : b.Effective) :
    a.pencil.dual.tensorRank b.pencil ≤ 2 * a.pencil.tensorRank b.pencil := by
  have h := SingularIndex.defect_identity a.singularIndex b.singularIndex
  obtain ⟨h₁, h₂⟩ := effective_ranks a b ha hb
  rw [← h₁, ← h₂] at h
  omega

/-- Each actual block pair satisfies the rank inequality. -/
private theorem rank_bound (a b : PencilAtom) :
    a.pencil.dual.tensorRank b.pencil ≤ 2 * a.pencil.tensorRank b.pencil := by
  by_cases ha : a.Effective
  · by_cases hb : b.Effective
    · exact rank_bound_of_effective a b ha hb
    · cases b with
      | right s => exact (hb trivial).elim
      | left s => exact (hb trivial).elim
      | regular q hq hs =>
        change a.pencil.dual.tensorRank q ≤ 2 * a.pencil.tensorRank q
        rw [regular_right_rank a.pencil q hq hs]
        omega
  · cases a with
    | right s => exact (ha trivial).elim
    | left s => exact (ha trivial).elim
    | regular p hp hs =>
      change p.dual.tensorRank b.pencil ≤ 2 * p.tensorRank b.pencil
      rw [regular_rank p b.pencil hp hs]
      omega

end PencilAtom

/-- The expansion records ranks against every other pencil, so it can be used
independently in both tensor factors. No canonical-form axiom is assumed. -/
structure PencilExpansion (p : Pencil ℂ) where
  index : Type
  [finite : Fintype index]
  atom : index → PencilAtom
  tensorRank : ∀ q : Pencil ℂ, p.tensorRank q = ∑ i, (atom i).pencil.tensorRank q
  horizontalRank : p.horizontalRank = ∑ i, (atom i).pencil.horizontalRank
  verticalRank : p.verticalRank = ∑ i, (atom i).pencil.verticalRank

attribute [instance] PencilExpansion.finite

namespace PencilExpansion

private theorem dual_tensorRank {p : Pencil ℂ} (e : PencilExpansion p) (q : Pencil ℂ) :
    p.dual.tensorRank q = ∑ i, (e.atom i).pencil.dual.tensorRank q := by
  rw [Pencil.tensorRank_dual_left_exchange, e.tensorRank]
  apply Finset.sum_congr rfl
  intro i _
  exact (Pencil.tensorRank_dual_left_exchange _ _).symm

private theorem second_tensorRank {q : Pencil ℂ} (e : PencilExpansion q) (p : Pencil ℂ) :
    p.tensorRank q = ∑ i, p.tensorRank (e.atom i).pencil := by
  rw [Pencil.tensorRank_comm, e.tensorRank]
  apply Finset.sum_congr rfl
  intro i _
  exact Pencil.tensorRank_comm _ _

private theorem pair_tensorRank {p q : Pencil ℂ} (e : PencilExpansion p)
    (f : PencilExpansion q) :
    p.tensorRank q = ∑ i, ∑ j, (e.atom i).pencil.tensorRank (f.atom j).pencil := by
  rw [e.tensorRank]
  exact Finset.sum_congr rfl (fun i _ => f.second_tensorRank _)

private theorem pair_dual_tensorRank {p q : Pencil ℂ} (e : PencilExpansion p)
    (f : PencilExpansion q) :
    p.dual.tensorRank q = ∑ i, ∑ j, (e.atom i).pencil.dual.tensorRank (f.atom j).pencil := by
  rw [e.dual_tensorRank]
  exact Finset.sum_congr rfl (fun i _ => f.second_tensorRank _)

private def singleton (p : Pencil ℂ) (hp : RightReduced p)
    (hs : finrank ℂ p.domain = finrank ℂ p.codomain) : PencilExpansion p where
  index := Unit
  atom := fun _ => .regular p hp hs
  tensorRank := by intro q; simp [PencilAtom.pencil]
  horizontalRank := by simp [PencilAtom.pencil]
  verticalRank := by simp [PencilAtom.pencil]

private theorem horizontalRank_eq (p : Pencil ℂ) : p.horizontalRank =
    finrank ℂ ↥(LinearMap.range p.first ⊔ LinearMap.range p.second) :=
  congrArg (fun W : Submodule ℂ p.codomain => finrank ℂ W)
    (LinearMap.range_coprod p.first p.second)

private def add_right {p : Pencil ℂ} {r : ℕ} (s : SplitData p r)
    (e : PencilExpansion s.remainder) : PencilExpansion p where
  index := Option e.index
  atom := fun i => i.elim (.right s) e.atom
  tensorRank := by
    intro q
    have h := s.tensor_split q
    change p.tensorRank q = s.block.tensorRank q + s.remainder.tensorRank q at h
    rw [e.tensorRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h
  horizontalRank := by
    have h : p.horizontalRank = s.block.horizontalRank + s.remainder.horizontalRank := by
      rw [horizontalRank_eq p, horizontalRank_eq s.block, horizontalRank_eq s.remainder]
      exact s.horizontal_split
    rw [e.horizontalRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h
  verticalRank := by
    have h := s.vertical_split
    change p.verticalRank = s.block.verticalRank + s.remainder.verticalRank at h
    rw [e.verticalRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h

private def add_left {p : Pencil ℂ} {r : ℕ} (s : SplitData p.dual r)
    (e : PencilExpansion s.remainder.dual) : PencilExpansion p where
  index := Option e.index
  atom := fun i => i.elim (.left s) e.atom
  tensorRank := by
    intro q
    have h := s.tensor_split q.dual
    change p.dual.tensorRank q.dual =
      s.block.tensorRank q.dual + s.remainder.tensorRank q.dual at h
    rw [Pencil.tensorRank_dual_dual,
      ← Pencil.tensorRank_dual_left_exchange s.block,
      ← Pencil.tensorRank_dual_left_exchange s.remainder, e.tensorRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h
  horizontalRank := by
    have h := s.vertical_split
    change p.dual.verticalRank = s.block.verticalRank + s.remainder.verticalRank at h
    rw [Pencil.verticalRank_dual, ← Pencil.horizontalRank_dual s.block,
      ← Pencil.horizontalRank_dual s.remainder, e.horizontalRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h
  verticalRank := by
    have h : p.dual.horizontalRank = s.block.horizontalRank + s.remainder.horizontalRank := by
      rw [horizontalRank_eq p.dual, horizontalRank_eq s.block, horizontalRank_eq s.remainder]
      exact s.horizontal_split
    rw [Pencil.horizontalRank_dual, ← Pencil.verticalRank_dual s.block,
      ← Pencil.verticalRank_dual s.remainder, e.verticalRank] at h
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some,
      PencilAtom.pencil] using h

end PencilExpansion

/-- Actual shortest-chain splits yield a finite additive block expansion. -/
private theorem exists_pencil_expansion (p : Pencil ℂ) : Nonempty (PencilExpansion p) := by
  have h := two_sided_reduction p
  induction h with
  | left reduction =>
    induction reduction with
    | reduced p hr hl hs => exact ⟨PencilExpansion.singleton p hr hs⟩
    | split hr s remainder ih =>
      obtain ⟨e⟩ := ih
      exact ⟨PencilExpansion.add_left s e⟩
  | right s remainder ih =>
    obtain ⟨e⟩ := ih
    exact ⟨PencilExpansion.add_right s e⟩

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open LinearMap Submodule Module
open scoped BigOperators TensorProduct
open ChainSplitting.FinitePair

/-- The finite actual block expansion proves the rank bound in arbitrary
dimensions, including zero-dimensional and dependent coefficient pairs. -/
private theorem pencil_rank_bound (p q : Pencil ℂ) :
    p.dual.tensorRank q ≤ 2 * p.tensorRank q := by
  obtain ⟨e⟩ := exists_pencil_expansion p
  obtain ⟨f⟩ := exists_pencil_expansion q
  rw [e.pair_dual_tensorRank f, e.pair_tensorRank f]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    PencilAtom.rank_bound (e.atom i) (f.atom j)))

namespace PencilExpansion

/-- Equality of the sum of nonnegative defects is equality on every piece. -/
private theorem atom_saturated {p : Pencil ℂ} (e : PencilExpansion p) (q : Pencil ℂ)
    (hs : p.dual.tensorRank q = 2 * p.tensorRank q) :
    ∀ i, (e.atom i).pencil.dual.tensorRank q =
      2 * (e.atom i).pencil.tensorRank q := by
  rw [e.dual_tensorRank, e.tensorRank, Finset.mul_sum] at hs
  intro i
  exact (Finset.sum_eq_sum_iff_of_le
    (fun j _ => pencil_rank_bound (e.atom j).pencil q)).mp hs i (Finset.mem_univ i)

/-- A regular piece of a saturated pair must vanish: otherwise independence
of the other pair makes its unchanged tensor rank strictly positive. -/
private theorem effective_of_saturated {p : Pencil ℂ} (e : PencilExpansion p) (q : Pencil ℂ)
    (hq : LinearIndependent ℂ ![q.first, q.second])
    (hs : p.dual.tensorRank q = 2 * p.tensorRank q) :
    ∀ i, (e.atom i).Effective := by
  intro i
  have hi := e.atom_saturated q hs i
  cases he : e.atom i with
  | right s => trivial
  | left s => trivial
  | regular a ha hdim =>
    rw [he] at hi
    change a.dual.tensorRank q = 2 * a.tensorRank q at hi
    have hr : a.dual.tensorRank q = a.tensorRank q :=
      Regularity.tensor_rank_dual_eq_of_reduced a q ha hdim
    have hz : a.tensorRank q = 0 := by omega
    have hd : finrank ℂ a.domain = 0 := by
      by_contra hn
      have hpos := Regularity.tensor_rank_pos_of_reduced a q ha hdim
        (Nat.pos_of_ne_zero hn) hq
      change 0 < a.tensorRank q at hpos
      omega
    letI : Subsingleton a.domain := (Module.finrank_zero_iff).mp hd
    change a.first = 0 ∧ a.second = 0
    constructor <;> ext x <;> have hx : x = 0 := Subsingleton.elim _ _ <;> simp [hx]

private theorem effective_horizontalRank {p : Pencil ℂ} (e : PencilExpansion p)
    (he : ∀ i, (e.atom i).Effective) :
    p.horizontalRank = ∑ i, (e.atom i).singularIndex.horizontal := by
  rw [e.horizontalRank]
  exact Finset.sum_congr rfl (fun i _ => ((e.atom i).effective_weights (he i)).1)

private theorem effective_verticalRank {p : Pencil ℂ} (e : PencilExpansion p)
    (he : ∀ i, (e.atom i).Effective) :
    p.verticalRank = ∑ i, (e.atom i).singularIndex.vertical := by
  rw [e.verticalRank]
  exact Finset.sum_congr rfl (fun i _ => ((e.atom i).effective_weights (he i)).2)

private theorem effective_positive_support {p : Pencil ℂ} (e : PencilExpansion p)
    (he : ∀ i, (e.atom i).Effective) (hp : 0 < p.horizontalRank) :
    ∃ i, 0 < (e.atom i).singularIndex.degree := by
  by_contra hn
  push_neg at hn
  have hz : ∀ i, (e.atom i).singularIndex.degree = 0 := fun i => Nat.eq_zero_of_le_zero (hn i)
  rw [e.effective_horizontalRank he] at hp
  simp [SingularIndex.horizontal, hz] at hp

end PencilExpansion

private theorem horizontalRank_pos_of_independent (p : Pencil ℂ)
    (hp : LinearIndependent ℂ ![p.first, p.second]) : 0 < p.horizontalRank := by
  by_contra hn
  have hz : LinearMap.range (p.first.coprod p.second) = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn)
  have hf : p.first = 0 := by
    ext x
    have h := LinearMap.congr_fun (LinearMap.range_eq_bot.mp hz) (x, 0)
    simpa using h
  have hne := hp.ne_zero (0 : Fin 2)
  exact hne (by simpa using hf)

/-- The full necessity argument for finite-dimensional linear maps. -/
private theorem pencil_saturation_necessary (p q : Pencil ℂ)
    (hp : LinearIndependent ℂ ![p.first, p.second])
    (hq : LinearIndependent ℂ ![q.first, q.second])
    (hs : p.dual.tensorRank q = 2 * p.tensorRank q) :
    (p.verticalRank = 2 * p.horizontalRank ∧ q.verticalRank = 2 * q.horizontalRank) ∨
      (p.horizontalRank = 2 * p.verticalRank ∧ q.horizontalRank = 2 * q.verticalRank) := by
  obtain ⟨e⟩ := exists_pencil_expansion p
  obtain ⟨f⟩ := exists_pencil_expansion q
  have hsq : q.dual.tensorRank p = 2 * q.tensorRank p := by
    calc
      q.dual.tensorRank p = q.tensorRank p.dual := Pencil.tensorRank_dual_left_exchange q p
      _ = p.dual.tensorRank q := Pencil.tensorRank_comm _ _
      _ = 2 * p.tensorRank q := hs
      _ = 2 * q.tensorRank p := congrArg (fun n => 2 * n) (Pencil.tensorRank_comm p q)
  have he := e.effective_of_saturated q hq hs
  have hf := f.effective_of_saturated p hp hsq
  have hea := e.effective_positive_support he (horizontalRank_pos_of_independent p hp)
  have hfb := f.effective_positive_support hf (horizontalRank_pos_of_independent q hq)
  have hnum : (∑ i, ∑ j,
      (e.atom i).singularIndex.transposed (f.atom j).singularIndex) =
      2 * ∑ i, ∑ j, (e.atom i).singularIndex.tensor (f.atom j).singularIndex := by
    rw [e.pair_dual_tensorRank f, e.pair_tensorRank f] at hs
    simpa only [fun i j => ((e.atom i).effective_ranks (f.atom j) (he i) (hf j)).1,
      fun i j => ((e.atom i).effective_ranks (f.atom j) (he i) (hf j)).2] using hs
  have h := singular_weights_of_saturation
    (fun i => (e.atom i).singularIndex) (fun j => (f.atom j).singularIndex) hea hfb hnum
  rwa [← e.effective_horizontalRank he, ← e.effective_verticalRank he,
    ← f.effective_horizontalRank hf, ← f.effective_verticalRank hf] at h

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open Matrix Module LinearMap
open scoped Kronecker TensorProduct
open ChainSplitting.FinitePair

/-- Coordinate realization of a rectangular coefficient pair as a pencil. -/
private def matrixPencil {m n : ℕ} (A₁ A₂ : Matrix (Fin m) (Fin n) ℂ) : Pencil ℂ where
  domain := Fin n → ℂ
  codomain := Fin m → ℂ
  first := Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin m)) A₁
  second := Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin m)) A₂

variable {m₁ n₁ m₂ n₂ : ℕ}

private theorem matrixPencil_independent (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (hA : LinearIndependent ℂ ![A₁, A₂]) :
    LinearIndependent ℂ ![(matrixPencil A₁ A₂).first, (matrixPencil A₁ A₂).second] := by
  let e := Matrix.toLin (Pi.basisFun ℂ (Fin n₁)) (Pi.basisFun ℂ (Fin m₁))
  have h := hA.map' e.toLinearMap e.ker
  have he : e.toLinearMap ∘ ![A₁, A₂] = ![e A₁, e A₂] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem matrixPencil_horizontal (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ) :
    (matrixPencil A₁ A₂).horizontalRank = hRank A₁ A₂ := by
  rw [Pencil.horizontalRank_matrix (matrixPencil A₁ A₂)
    (Pi.basisFun ℂ (Fin n₁)) (Pi.basisFun ℂ (Fin m₁))]
  simp only [matrixPencil, LinearMap.toMatrix_toLin]

private theorem matrixPencil_vertical (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ) :
    (matrixPencil A₁ A₂).verticalRank = vRank A₁ A₂ := by
  rw [Pencil.verticalRank_matrix (matrixPencil A₁ A₂)
    (Pi.basisFun ℂ (Fin n₁)) (Pi.basisFun ℂ (Fin m₁))]
  simp only [matrixPencil, LinearMap.toMatrix_toLin]

private theorem matrixPencil_tensor (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B₁ B₂ : Matrix (Fin m₂) (Fin n₂) ℂ) :
    (matrixPencil A₁ A₂).tensorRank (matrixPencil B₁ B₂) =
      (tensorSum A₁ A₂ B₁ B₂).rank := by
  rw [Pencil.tensorRank_matrix (matrixPencil A₁ A₂) (matrixPencil B₁ B₂)
    (Pi.basisFun ℂ (Fin n₁)) (Pi.basisFun ℂ (Fin m₁))
    (Pi.basisFun ℂ (Fin n₂)) (Pi.basisFun ℂ (Fin m₂))]
  simp only [matrixPencil, LinearMap.toMatrix_toLin]

private theorem matrixPencil_partialTranspose (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B₁ B₂ : Matrix (Fin m₂) (Fin n₂) ℂ) :
    (matrixPencil A₁ A₂).dual.tensorRank (matrixPencil B₁ B₂) =
      (partialTranspose A₁ A₂ B₁ B₂).rank := by
  rw [Pencil.tensorRank_matrix (matrixPencil A₁ A₂).dual (matrixPencil B₁ B₂)
    (Pi.basisFun ℂ (Fin m₁)).dualBasis (Pi.basisFun ℂ (Fin n₁)).dualBasis
    (Pi.basisFun ℂ (Fin n₂)) (Pi.basisFun ℂ (Fin m₂))]
  change (tensorSum
    (LinearMap.toMatrix _ _ ((matrixPencil A₁ A₂).first.dualMap))
    (LinearMap.toMatrix _ _ ((matrixPencil A₁ A₂).second.dualMap)) _ _).rank = _
  simp only [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, matrixPencil,
    LinearMap.toMatrix_toLin, partialTranspose]

/-- For every rectangular Schmidt-rank-two tensor, partial-transpose rank
saturates the factor-two bound exactly in the two concatenation-rank families. -/
theorem result (A₁ A₂ : Matrix (Fin m₁) (Fin n₁) ℂ)
    (B₁ B₂ : Matrix (Fin m₂) (Fin n₂) ℂ)
    (hA : LinearIndependent ℂ ![A₁, A₂])
    (hB : LinearIndependent ℂ ![B₁, B₂]) :
    (partialTranspose A₁ A₂ B₁ B₂).rank = 2 * (tensorSum A₁ A₂ B₁ B₂).rank ↔
      (vRank A₁ A₂ = 2 * hRank A₁ A₂ ∧ vRank B₁ B₂ = 2 * hRank B₁ B₂) ∨
      (hRank A₁ A₂ = 2 * vRank A₁ A₂ ∧ hRank B₁ B₂ = 2 * vRank B₁ B₂) := by
  constructor
  · intro hs
    have hs' : (matrixPencil A₁ A₂).dual.tensorRank (matrixPencil B₁ B₂) =
        2 * (matrixPencil A₁ A₂).tensorRank (matrixPencil B₁ B₂) := by
      simpa only [matrixPencil_partialTranspose, matrixPencil_tensor] using hs
    have h := pencil_saturation_necessary (matrixPencil A₁ A₂) (matrixPencil B₁ B₂)
      (matrixPencil_independent A₁ A₂ hA) (matrixPencil_independent B₁ B₂ hB) hs'
    simpa only [matrixPencil_horizontal, matrixPencil_vertical] using h
  · exact sufficient A₁ A₂ B₁ B₂

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation
