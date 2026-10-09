/- GID: D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization
   mirror-E: none(waiver:registration-paused)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization.source22_4FixedFactorQuestion; instance=D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization.source22_4Certificate
   digest: Constructive fixed-subgroup factorization from one ordered natural allocation. -/

import D5.S3.Combinatorics.Transportation.OrderedMarginAllocation
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.OrderedSubgroupFactorization

open scoped BigOperators

open D5.S3.Combinatorics.Transportation.OrderedMarginAllocation

universe u

section NativeCosets

variable {H : Type u} [Group H] [Fintype H] [LinearOrder H]
  (K : Subgroup H) [DecidablePred (fun h : H => h ∈ K)]

/-- Source C=hK is Mathlib's left coset; this definition uses its actual members. -/
def sourceRightCoset (h : H) : Finset H :=
  Finset.univ.filter (fun x => h⁻¹ * x ∈ K)

/-- Source L=Kh is Mathlib's right coset; no commutation is used. -/
def sourceLeftCoset (h : H) : Finset H :=
  Finset.univ.filter (fun x => x * h⁻¹ ∈ K)

/-- The actual set KhK, enumerated by the two subgroup multipliers in their order. -/
def sourceDoubleCoset (h : H) : Finset H :=
  ((Finset.univ.filter (fun k : H => k ∈ K)) ×ˢ
    (Finset.univ.filter (fun k : H => k ∈ K))).image
    (fun pair => pair.1 * h * pair.2)

/-- Least representatives depend only on the prescribed order of actual members. -/
def leastRightRepresentative (h : H) : H :=
  (sourceRightCoset K h).min' ⟨h, by simp [sourceRightCoset]⟩

def leastLeftRepresentative (h : H) : H :=
  (sourceLeftCoset K h).min' ⟨h, by simp [sourceLeftCoset]⟩

def leastDoubleRepresentative (h : H) : H :=
  (sourceDoubleCoset K h).min' (by
    refine ⟨h, Finset.mem_image.mpr ?_⟩
    exact ⟨(1, 1), by simp, by simp⟩)

/-- Image removes repeated cosets before ordering their least representatives. -/
def rightRepresentatives : Finset H := Finset.univ.image (leastRightRepresentative K)
def leftRepresentatives : Finset H := Finset.univ.image (leastLeftRepresentative K)
def doubleRepresentatives : Finset H := Finset.univ.image (leastDoubleRepresentative K)

def blockRows (d : H) : Finset H :=
  (rightRepresentatives K).filter (fun r => r ∈ sourceDoubleCoset K d)

def blockColumns (d : H) : Finset H :=
  (leftRepresentatives K).filter (fun c => c ∈ sourceDoubleCoset K d)

/-- Sorting the representative subtypes is sorting by their actual least group elements. -/
def blockAllocation (a : MonoidAlgebra ℕ H) (b : ℕ) (d : H) :
    AllocationState (blockRows K d) (blockColumns K d) :=
  orderedAllocation
    ((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·))
    ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))
    (fun r => a.coeff r.val) (fun _ => b)

/-- The coefficient table records only the least actual cell member.
An empty cell contributes zero; the factorization theorem proves that actual
block cells in a double coset are nonempty. -/
def blockMass (a : MonoidAlgebra ℕ H) (b : ℕ) (d : H) : H → ℕ :=
  let table := blockAllocation K a b d
  fun h => ∑ r : blockRows K d, ∑ c : blockColumns K d,
    let cell := sourceRightCoset K r.val ∩ sourceLeftCoset K c.val
    if hc : cell.Nonempty then
      if cell.min' hc = h then table.2.2 (r, c) else 0
    else 0

/-- Native coefficients are assembled directly, without a second allocation algorithm. -/
def orderedFactor (a : MonoidAlgebra ℕ H) (b : ℕ) : MonoidAlgebra ℕ H :=
  let blocks := ((doubleRepresentatives K).sort (· ≤ ·)).map (blockMass K a b)
  let mass := fun h => (blocks.map (fun f => f h)).sum
  MonoidAlgebra.ofCoeff {
    support := Finset.univ.filter (fun h => mass h ≠ 0)
    toFun := mass
    mem_support_toFun := by intro h; simp }

def subgroupUniform : MonoidAlgebra ℕ H :=
  MonoidAlgebra.ofCoeff {
    support := Finset.univ.filter (fun k : H => k ∈ K)
    toFun := fun k => if k ∈ K then 1 else 0
    mem_support_toFun := by intro k; simp }

def groupUniform : MonoidAlgebra ℕ H :=
  MonoidAlgebra.ofCoeff {
    support := Finset.univ
    toFun := fun _ => 1
    mem_support_toFun := by intro h; simp }

/-- Exact finite failures retain two actual unequal coefficients or an actual block. -/
def firstCoefficientMismatch (a : MonoidAlgebra ℕ H) : Option (H × H) :=
  ((Finset.univ : Finset H).sort (· ≤ ·)).findSome? (fun h =>
    (((sourceRightCoset K h).filter (fun x => a.coeff h ≠ a.coeff x)).sort
      (· ≤ ·)).head?.map (fun x => (h, x)))

def firstBalanceMismatch (a : MonoidAlgebra ℕ H) (b : ℕ) : Option H :=
  (((doubleRepresentatives K).filter (fun d =>
    (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b)).sort (· ≤ ·)).head?

/-- This is the prescribed finite inspection and producer, not an abstract feasible witness.
The factorization theorem verifies both products, both fixed-factor criteria,
and the actual finite failure witnesses. -/
def inspectAndConstruct (a : MonoidAlgebra ℕ H) (b : ℕ) :
    Sum (Sum (H × H) H) (MonoidAlgebra ℕ H) :=
  match firstCoefficientMismatch K a with
  | some pair => .inl (.inl pair)
  | none => match firstBalanceMismatch K a b with
    | some d => .inl (.inr d)
    | none => .inr (orderedFactor K a b)

/-- The actual least-cell producer solves exactly the fixed subgroup-factor problem.
Both group-ring criteria, every inspection branch, and the zero-inclusive cell count
refer to this same natural allocation. -/
theorem ordered_subgroup_factorization_correct (a : MonoidAlgebra ℕ H) (b : ℕ) :
    let C := ∀ h x : H, x ∈ sourceRightCoset K h → a.coeff x = a.coeff h
    let B := ∀ d : H, (∑ r ∈ blockRows K d, a.coeff r) = (blockRows K d).card * b
    let F := ∃ p : MonoidAlgebra ℕ H,
      a = p * subgroupUniform K ∧ b • (groupUniform : MonoidAlgebra ℕ H) = subgroupUniform K * p
    let P := a * subgroupUniform K = (Finset.univ.filter (fun k : H => k ∈ K)).card • a ∧
      subgroupUniform K * a = ((Finset.univ.filter (fun k : H => k ∈ K)).card * b) •
        (groupUniform : MonoidAlgebra ℕ H)
    let N := (((doubleRepresentatives K).sort (· ≤ ·)).map (fun d =>
      (((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·)) ×ˢ
        ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))).length)).sum =
      ∑ d ∈ doubleRepresentatives K, (blockRows K d).card ^ 2
    (F ↔ C ∧ B) ∧
    (C → (subgroupUniform K * a =
      ((Finset.univ.filter (fun k : H => k ∈ K)).card * b) •
        (groupUniform : MonoidAlgebra ℕ H) ↔ B)) ∧
    (F ↔ P) ∧
    (firstCoefficientMismatch K a = none ↔ C) ∧
    (firstBalanceMismatch K a b = none ↔ B) ∧
    (∀ pair, firstCoefficientMismatch K a = some pair →
      pair.2 ∈ sourceRightCoset K pair.1 ∧ a.coeff pair.1 ≠ a.coeff pair.2) ∧
    (∀ d, firstBalanceMismatch K a b = some d →
      d ∈ doubleRepresentatives K ∧
      (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b) ∧
    (∀ p, inspectAndConstruct K a b = .inr p ↔ p = orderedFactor K a b ∧ C ∧ B) ∧
    (∀ p, inspectAndConstruct K a b = .inr p →
      a = p * subgroupUniform K ∧
      b • (groupUniform : MonoidAlgebra ℕ H) = subgroupUniform K * p ∧ N) ∧
    (∀ bad, inspectAndConstruct K a b = .inl bad →
      (match bad with
       | .inl pair => pair.2 ∈ sourceRightCoset K pair.1 ∧ a.coeff pair.1 ≠ a.coeff pair.2
       | .inr d => d ∈ doubleRepresentatives K ∧
         (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b) ∧ ¬ F) := by
  classical

  have supplied :
      (∀ d : H, let t := (sourceRightCoset K d ∩ sourceLeftCoset K d).card
        ((blockRows K d).biUnion (sourceRightCoset K) = sourceDoubleCoset K d) ∧
        ((blockColumns K d).biUnion (sourceLeftCoset K) = sourceDoubleCoset K d) ∧
        (∀ x ∈ sourceDoubleCoset K d, ∃! r : blockRows K d,
          x ∈ sourceRightCoset K r.val) ∧
        (∀ x ∈ sourceDoubleCoset K d, ∃! c : blockColumns K d,
          x ∈ sourceLeftCoset K c.val) ∧
        (∀ r ∈ sourceDoubleCoset K d, ∀ c ∈ sourceDoubleCoset K d,
          (sourceRightCoset K r ∩ sourceLeftCoset K c).Nonempty ∧
          (sourceRightCoset K r ∩ sourceLeftCoset K c).card = t) ∧
        (blockRows K d).card = (blockColumns K d).card ∧
        0 < t ∧
        (Finset.univ.filter (fun k : H => k ∈ K)).card = t * (blockRows K d).card) ∧
      (∀ (a : MonoidAlgebra ℕ H) (b : ℕ),
        (∀ h x : H, x ∈ sourceRightCoset K h → a.coeff x = a.coeff h) →
        (∀ d : H, (∑ r ∈ blockRows K d, a.coeff r) = (blockRows K d).card * b) →
      a = orderedFactor K a b * subgroupUniform K ∧
      b • (groupUniform : MonoidAlgebra ℕ H) = subgroupUniform K * orderedFactor K a b ∧
      ((((doubleRepresentatives K).sort (· ≤ ·)).map (fun d =>
        (((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·)) ×ˢ
          ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))).length)).sum =
        ∑ d ∈ doubleRepresentatives K, (blockRows K d).card ^ 2) ∧
      (∀ p h, (p * subgroupUniform K).coeff h = ∑ x ∈ sourceRightCoset K h, p.coeff x) ∧
      (∀ p h, (subgroupUniform K * p).coeff h = ∑ x ∈ sourceLeftCoset K h, p.coeff x)) ∧
      (∀ x y, y ∈ sourceRightCoset K x → sourceRightCoset K y = sourceRightCoset K x) ∧
      (∀ x y, y ∈ sourceDoubleCoset K x → sourceDoubleCoset K y = sourceDoubleCoset K x) ∧
      (∀ x, sourceLeftCoset K x ⊆ sourceDoubleCoset K x) ∧
      (∀ x, x ∈ sourceDoubleCoset K x) := by
    classical
    classical
    have selfR (x : H) : x ∈ sourceRightCoset K x := by simp [sourceRightCoset]
    have selfL (x : H) : x ∈ sourceLeftCoset K x := by simp [sourceLeftCoset]
    have memD (d x : H) : x ∈ sourceDoubleCoset K d ↔
        x ∈ DoubleCoset.doubleCoset d K K := by
      rw [DoubleCoset.mem_doubleCoset]
      constructor
      · intro hx
        obtain ⟨⟨l,r⟩, hp, he⟩ := Finset.mem_image.mp hx
        have hp' : l ∈ K ∧ r ∈ K := by simpa using hp
        exact ⟨l,hp'.1,r,hp'.2,he.symm⟩
      · rintro ⟨l,hl,r,hr,he⟩
        exact Finset.mem_image.mpr ⟨(l,r),by simpa using And.intro hl hr,he.symm⟩
    have selfD (x : H) : x ∈ sourceDoubleCoset K x :=
      (memD x x).mpr (DoubleCoset.mem_doubleCoset_self K K x)
    have eqR (x y : H) (hy : y ∈ sourceRightCoset K x) :
        sourceRightCoset K y = sourceRightCoset K x := by
      have hy' : x⁻¹ * y ∈ K := by simpa [sourceRightCoset] using hy
      have he := (leftCoset_eq_iff K).mpr hy'
      ext z
      simpa [sourceRightCoset, mem_leftCoset_iff] using (Set.ext_iff.mp he z).symm
    have eqL (x y : H) (hy : y ∈ sourceLeftCoset K x) :
        sourceLeftCoset K y = sourceLeftCoset K x := by
      have hy' : y * x⁻¹ ∈ K := by simpa [sourceLeftCoset] using hy
      have he := (rightCoset_eq_iff K).mpr hy'
      ext z
      simpa [sourceLeftCoset, mem_rightCoset_iff] using (Set.ext_iff.mp he z).symm
    have eqD (x y : H) (hy : y ∈ sourceDoubleCoset K x) :
        sourceDoubleCoset K y = sourceDoubleCoset K x := by
      have he := DoubleCoset.doubleCoset_eq_of_mem ((memD x y).mp hy)
      ext z
      exact (memD y z).trans ((Set.ext_iff.mp he z).trans (memD x z).symm)
    have subR (x : H) : sourceRightCoset K x ⊆ sourceDoubleCoset K x := by
      intro y hy
      apply (memD x y).mpr
      apply DoubleCoset.mem_doubleCoset.mpr
      exact ⟨1,K.one_mem,x⁻¹*y,by simpa [sourceRightCoset] using hy,by simp⟩
    have subL (x : H) : sourceLeftCoset K x ⊆ sourceDoubleCoset K x := by
      intro y hy
      apply (memD x y).mpr
      apply DoubleCoset.mem_doubleCoset.mpr
      exact ⟨y*x⁻¹,by simpa [sourceLeftCoset] using hy,1,K.one_mem,by simp⟩
    have native (d : H) (a : MonoidAlgebra ℕ H) (b : ℕ)
        (sourceBalance : (∑ r ∈ blockRows K d, a.coeff r) = (blockRows K d).card * b) :
        let t := (sourceRightCoset K d ∩ sourceLeftCoset K d).card
        ((blockRows K d).biUnion (sourceRightCoset K) = sourceDoubleCoset K d) ∧
        ((blockColumns K d).biUnion (sourceLeftCoset K) = sourceDoubleCoset K d) ∧
        (∀ x ∈ sourceDoubleCoset K d, ∃! r : blockRows K d,
          x ∈ sourceRightCoset K r.val) ∧
        (∀ x ∈ sourceDoubleCoset K d, ∃! c : blockColumns K d,
          x ∈ sourceLeftCoset K c.val) ∧
        (∀ r ∈ sourceDoubleCoset K d, ∀ c ∈ sourceDoubleCoset K d,
          (sourceRightCoset K r ∩ sourceLeftCoset K c).Nonempty ∧
          (sourceRightCoset K r ∩ sourceLeftCoset K c).card = t) ∧
        (blockRows K d).card = (blockColumns K d).card ∧
        0 < t ∧
        (Finset.univ.filter (fun k : H => k ∈ K)).card = t * (blockRows K d).card ∧
        (∀ r : blockRows K d, (blockAllocation K a b d).1 r = 0 ∧
          (∑ c : blockColumns K d, (blockAllocation K a b d).2.2 (r, c)) = a.coeff r.val) ∧
        (∀ c : blockColumns K d, (blockAllocation K a b d).2.1 c = 0 ∧
          (∑ r : blockRows K d, (blockAllocation K a b d).2.2 (r, c)) = b) ∧
        (∀ r : blockRows K d, (∑ h ∈ sourceRightCoset K r.val, blockMass K a b d h) = a.coeff r.val) ∧
        (∀ c : blockColumns K d, (∑ h ∈ sourceLeftCoset K c.val, blockMass K a b d h) = b) ∧
        (∀ h, h ∉ sourceDoubleCoset K d → blockMass K a b d h = 0) ∧
        (((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·)) ×ˢ
          ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))).length = (blockRows K d).card ^ 2 := by
      have partitions (F : H → Finset H) (rep : H → H)
          (self : ∀ x, x ∈ F x)
          (eq : ∀ x y, y ∈ F x → F y = F x)
          (repmem : ∀ x, rep x ∈ F x)
          (stable : ∀ x y, y ∈ F x → rep y = rep x)
          (sub : ∀ x, F x ⊆ sourceDoubleCoset K x) :
          let reps := (Finset.univ.image rep).filter (fun r => r ∈ sourceDoubleCoset K d)
          reps.biUnion F = sourceDoubleCoset K d ∧
          (∀ x ∈ sourceDoubleCoset K d, ∃! r : reps, x ∈ F r.val) ∧
          (∀ r ∈ reps, ∀ x, x ∈ F r ↔ rep x = r) := by
        let reps := (Finset.univ.image rep).filter (fun r => r ∈ sourceDoubleCoset K d)
        have fixed (r : H) (hr : r ∈ reps) : rep r = r := by
          obtain ⟨y,_,hy⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
          subst r
          exact stable y (rep y) (repmem y)
        have fibers (r : H) (hr : r ∈ reps) (x : H) : x ∈ F r ↔ rep x = r := by
          constructor
          · intro hx
            exact (stable r x hx).trans (fixed r hr)
          · intro hx
            have he := eq x (rep x) (repmem x)
            rw [hx] at he
            rw [he]
            exact self x
        have cover (x : H) (hx : x ∈ sourceDoubleCoset K d) : rep x ∈ reps := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,?_⟩
          rw [← eqD d x hx]
          exact sub x (repmem x)
        refine ⟨?_,?_,fibers⟩
        · ext x
          constructor
          · intro hx
            obtain ⟨r,hr,hxr⟩ := Finset.mem_biUnion.mp hx
            rw [← eqD d r (Finset.mem_filter.mp hr).2]
            exact sub r hxr
          · intro hx
            exact Finset.mem_biUnion.mpr ⟨rep x,cover x hx,
              (fibers (rep x) (cover x hx) x).mpr rfl⟩
        · intro x hx
          refine ⟨⟨rep x,cover x hx⟩,(fibers _ (cover x hx) x).mpr rfl,?_⟩
          intro r hr
          apply Subtype.ext
          exact ((fibers r.val r.property x).mp hr).symm
      have repRmem (x : H) : leastRightRepresentative K x ∈ sourceRightCoset K x :=
        Finset.min'_mem _ _
      have repLmem (x : H) : leastLeftRepresentative K x ∈ sourceLeftCoset K x :=
        Finset.min'_mem _ _
      have stableR (x y : H) (hy : y ∈ sourceRightCoset K x) :
          leastRightRepresentative K y = leastRightRepresentative K x := by
        have he := eqR x y hy
        exact le_antisymm (Finset.min'_le _ _ (he.symm ▸ repRmem x))
          (Finset.min'_le _ _ (he ▸ repRmem y))
      have stableL (x y : H) (hy : y ∈ sourceLeftCoset K x) :
          leastLeftRepresentative K y = leastLeftRepresentative K x := by
        have he := eqL x y hy
        exact le_antisymm (Finset.min'_le _ _ (he.symm ▸ repLmem x))
          (Finset.min'_le _ _ (he ▸ repLmem y))
      have rows := partitions (sourceRightCoset K) (leastRightRepresentative K)
        selfR eqR repRmem stableR subR
      have columns := partitions (sourceLeftCoset K) (leastLeftRepresentative K)
        selfL eqL repLmem stableL subL
      change (blockRows K d).biUnion (sourceRightCoset K) = _ ∧ _ ∧ _ at rows
      change (blockColumns K d).biUnion (sourceLeftCoset K) = _ ∧ _ ∧ _ at columns
      have cellCard (r c : H) (hr : r ∈ sourceDoubleCoset K d)
          (hc : c ∈ sourceDoubleCoset K d) :
          (sourceRightCoset K r ∩ sourceLeftCoset K c).card =
            (sourceRightCoset K d ∩ sourceLeftCoset K d).card := by
        obtain ⟨k1,hk1,k2,hk2,er⟩ := DoubleCoset.mem_doubleCoset.mp ((memD d r).mp hr)
        obtain ⟨k3,hk3,k4,hk4,ec⟩ := DoubleCoset.mem_doubleCoset.mp ((memD d c).mp hc)
        have rmem : r ∈ sourceRightCoset K (k1*d) := by
          simpa [sourceRightCoset,er,mul_assoc] using hk2
        have cmem : c ∈ sourceLeftCoset K (d*k4) := by
          simpa [sourceLeftCoset,ec,mul_assoc] using hk3
        rw [eqR (k1*d) r rmem,eqL (d*k4) c cmem]
        apply (Finset.card_nbij' (fun x : H => k1*x*k4)
          (fun y : H => k1⁻¹*y*k4⁻¹) ?_ ?_ ?_ ?_).symm
        · intro x hx
          have hx' : d⁻¹*x ∈ K ∧ x*d⁻¹ ∈ K := by
            simpa [sourceRightCoset,sourceLeftCoset] using hx
          have h1 := K.mul_mem hx'.1 hk4
          have h2 := K.mul_mem hk1 hx'.2
          simpa [sourceRightCoset,sourceLeftCoset,mul_assoc] using And.intro h1 h2
        · intro y hy
          have hy' : (k1*d)⁻¹*y ∈ K ∧ y*(d*k4)⁻¹ ∈ K := by
            simpa [sourceRightCoset,sourceLeftCoset] using hy
          have h1 := K.mul_mem hy'.1 (K.inv_mem hk4)
          have h2 := K.mul_mem (K.inv_mem hk1) hy'.2
          simpa [sourceRightCoset,sourceLeftCoset,mul_assoc] using And.intro h1 h2
        · intro x _; simp [mul_assoc]
        · intro y _; simp [mul_assoc]
      have tpos : 0 < (sourceRightCoset K d ∩ sourceLeftCoset K d).card :=
        Finset.card_pos.mpr ⟨d,Finset.mem_inter.mpr ⟨selfR d,selfL d⟩⟩
      have cells (r : H) (hr : r ∈ sourceDoubleCoset K d)
          (c : H) (hc : c ∈ sourceDoubleCoset K d) :
          (sourceRightCoset K r ∩ sourceLeftCoset K c).Nonempty ∧
          (sourceRightCoset K r ∩ sourceLeftCoset K c).card =
            (sourceRightCoset K d ∩ sourceLeftCoset K d).card := by
        have hcard := cellCard r c hr hc
        exact ⟨Finset.card_pos.mp (by omega),hcard⟩
      have cardR (x : H) : (sourceRightCoset K x).card =
          (Finset.univ.filter (fun k : H => k ∈ K)).card := by
        apply Finset.card_nbij' (fun y => x⁻¹*y) (fun k => x*k)
        · intro y hy; simpa [sourceRightCoset] using hy
        · intro k hk; simpa [sourceRightCoset,mul_assoc] using hk
        · intro y _; simp
        · intro k _; simp
      have cardL (x : H) : (sourceLeftCoset K x).card =
          (Finset.univ.filter (fun k : H => k ∈ K)).card := by
        apply Finset.card_nbij' (fun y => y*x⁻¹) (fun k => k*x)
        · intro y hy; simpa [sourceLeftCoset] using hy
        · intro k hk; simpa [sourceLeftCoset,mul_assoc] using hk
        · intro y _; simp
        · intro k _; simp
      have countR : (Finset.univ.filter (fun k : H => k ∈ K)).card =
          (sourceRightCoset K d ∩ sourceLeftCoset K d).card * (blockRows K d).card := by
        have maps : ∀ x ∈ sourceLeftCoset K d, leastRightRepresentative K x ∈ blockRows K d := by
          intro x hx
          obtain ⟨r,hr,_⟩ := rows.2.1 x (subL d hx)
          rw [(rows.2.2 r.val r.property x).mp hr]
          exact r.property
        have hf := Finset.card_eq_sum_card_fiberwise (f := leastRightRepresentative K)
          (s := sourceLeftCoset K d) (t := blockRows K d) maps
        have fibers (r : H) (hr : r ∈ blockRows K d) :
            (sourceLeftCoset K d).filter (fun x => leastRightRepresentative K x = r) =
              sourceRightCoset K r ∩ sourceLeftCoset K d := by
          ext x
          simp only [Finset.mem_filter,Finset.mem_inter]
          rw [← rows.2.2 r hr x]
          exact and_comm
        rw [cardL d] at hf
        rw [hf]
        rw [Finset.sum_congr rfl (fun x hx => congrArg Finset.card (fibers x hx))]
        rw [Finset.sum_congr (s₁ := blockRows K d) rfl (fun r hr => cellCard r d (Finset.mem_filter.mp hr).2 (selfD d))]
        simp [Nat.mul_comm]
      have countL : (Finset.univ.filter (fun k : H => k ∈ K)).card =
          (sourceRightCoset K d ∩ sourceLeftCoset K d).card * (blockColumns K d).card := by
        have maps : ∀ x ∈ sourceRightCoset K d, leastLeftRepresentative K x ∈ blockColumns K d := by
          intro x hx
          obtain ⟨c,hc,_⟩ := columns.2.1 x (subR d hx)
          rw [(columns.2.2 c.val c.property x).mp hc]
          exact c.property
        have hf := Finset.card_eq_sum_card_fiberwise (f := leastLeftRepresentative K)
          (s := sourceRightCoset K d) (t := blockColumns K d) maps
        have fibers (c : H) (hc : c ∈ blockColumns K d) :
            (sourceRightCoset K d).filter (fun x => leastLeftRepresentative K x = c) =
              sourceRightCoset K d ∩ sourceLeftCoset K c := by
          ext x
          simp only [Finset.mem_filter,Finset.mem_inter]
          rw [← columns.2.2 c hc x]
        rw [cardR d] at hf
        rw [hf]
        rw [Finset.sum_congr rfl (fun x hx => congrArg Finset.card (fibers x hx))]
        rw [Finset.sum_congr (s₁ := blockColumns K d) rfl (fun c hc => cellCard d c (selfD d) (Finset.mem_filter.mp hc).2)]
        simp [Nat.mul_comm]
      have counts : (blockRows K d).card = (blockColumns K d).card :=
        Nat.eq_of_mul_eq_mul_left tpos (countR.symm.trans countL)
      have balanced : (∑ r : blockRows K d, a.coeff r.val) =
          ∑ _ : blockColumns K d, b := by
        simpa [Finset.sum_attach,counts] using sourceBalance
      have allocation := ordered_allocation_complete
        ((Finset.univ : Finset (blockRows K d)).sort (· ≤ ·))
        ((Finset.univ : Finset (blockColumns K d)).sort (· ≤ ·))
        (fun r => by simp) (fun c => by simp)
        (fun r => a.coeff r.val) (fun _ => b) balanced
      let T := (blockAllocation K a b d).2.2
      let μ (r : blockRows K d) (c : blockColumns K d) : H :=
        (sourceRightCoset K r.val ∩ sourceLeftCoset K c.val).min'
          (cells r.val (Finset.mem_filter.mp r.property).2
            c.val (Finset.mem_filter.mp c.property).2).1
      have muMem (r : blockRows K d) (c : blockColumns K d) :
          μ r c ∈ sourceRightCoset K r.val ∧ μ r c ∈ sourceLeftCoset K c.val :=
        Finset.mem_inter.mp (Finset.min'_mem _ _)
      have muRow (r r0 : blockRows K d) (c : blockColumns K d) :
          μ r c ∈ sourceRightCoset K r0.val ↔ r = r0 := by
        constructor
        · intro h
          apply Subtype.ext
          exact ((rows.2.2 r.val r.property _).mp (muMem r c).1).symm.trans
            ((rows.2.2 r0.val r0.property _).mp h)
        · intro h; subst r0; exact (muMem r c).1
      have muColumn (r : blockRows K d) (c c0 : blockColumns K d) :
          μ r c ∈ sourceLeftCoset K c0.val ↔ c = c0 := by
        constructor
        · intro h
          apply Subtype.ext
          exact ((columns.2.2 c.val c.property _).mp (muMem r c).2).symm.trans
            ((columns.2.2 c0.val c0.property _).mp h)
        · intro h; subst c0; exact (muMem r c).2
      have massEq (h : H) : blockMass K a b d h =
          ∑ r : blockRows K d, ∑ c : blockColumns K d,
            if μ r c = h then T (r,c) else 0 := by
        unfold blockMass
        dsimp only
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro c _
        rw [dif_pos (cells r.val (Finset.mem_filter.mp r.property).2
          c.val (Finset.mem_filter.mp c.property).2).1]
      have massRow (r0 : blockRows K d) :
          (∑ h ∈ sourceRightCoset K r0.val, blockMass K a b d h) = ∑ c, T (r0,c) := by
        simp_rw [massEq]
        rw [Finset.sum_comm]
        calc
          _ = ∑ r : blockRows K d, ∑ c : blockColumns K d,
              ∑ h ∈ sourceRightCoset K r0.val, if μ r c = h then T (r,c) else 0 := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.sum_comm]
          _ = ∑ r : blockRows K d, ∑ c : blockColumns K d,
              if r = r0 then T (r,c) else 0 := by
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro c _
                simp [muRow]
          _ = _ := by simp
      have massColumn (c0 : blockColumns K d) :
          (∑ h ∈ sourceLeftCoset K c0.val, blockMass K a b d h) = ∑ r, T (r,c0) := by
        simp_rw [massEq]
        rw [Finset.sum_comm]
        calc
          _ = ∑ r : blockRows K d, ∑ c : blockColumns K d,
              ∑ h ∈ sourceLeftCoset K c0.val, if μ r c = h then T (r,c) else 0 := by
                apply Finset.sum_congr rfl
                intro r _
                rw [Finset.sum_comm]
          _ = ∑ r : blockRows K d, ∑ c : blockColumns K d,
              if c = c0 then T (r,c) else 0 := by
                apply Finset.sum_congr rfl
                intro r _
                apply Finset.sum_congr rfl
                intro c _
                simp [muColumn]
          _ = _ := by simp
      have outside (h : H) (hh : h ∉ sourceDoubleCoset K d) : blockMass K a b d h = 0 := by
        rw [massEq]
        apply Finset.sum_eq_zero
        intro r _
        apply Finset.sum_eq_zero
        intro c _
        have hn : μ r c ≠ h := by
          intro he
          apply hh
          rw [← he,← eqD d r.val (Finset.mem_filter.mp r.property).2]
          exact subR r.val (muMem r c).1
        simp [hn]
      refine ⟨rows.1,columns.1,rows.2.1,columns.2.1,cells,counts,tpos,countR,
        allocation.1,allocation.2.1,?_,?_,outside,?_⟩
      · intro r; exact (massRow r).trans (allocation.1 r).2
      · intro c; exact (massColumn c).trans (allocation.2.1 c).2
      · simp [List.length_product,counts,pow_two]
    refine ⟨?_, ?_,eqR,eqD,subL,selfD⟩
    · intro d
      rcases native d 0 0 (by simp) with
        ⟨rows,columns,uniqueR,uniqueL,cells,counts,tpos,q,_,_,_,_,_,_⟩
      exact ⟨rows,columns,uniqueR,uniqueL,cells,counts,tpos,q⟩
    · intro a b constant balance
      have blockOutside (d h : H) (hh : h ∉ sourceDoubleCoset K d) :
          blockMass K a b d h = 0 := by
        rcases native d a b (balance d) with
          ⟨_,_,_,_,_,_,_,_,_,_,_,_,outside,_⟩
        exact outside h hh
      have repDmem (h : H) : leastDoubleRepresentative K h ∈ sourceDoubleCoset K h :=
        Finset.min'_mem _ _
      have stableD (h x : H) (hx : x ∈ sourceDoubleCoset K h) :
          leastDoubleRepresentative K x = leastDoubleRepresentative K h := by
        have he := eqD h x hx
        exact le_antisymm (Finset.min'_le _ _ (he.symm ▸ repDmem h))
          (Finset.min'_le _ _ (he ▸ repDmem x))
      have repIn (h : H) : leastDoubleRepresentative K h ∈ doubleRepresentatives K :=
        Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩
      have fixedD (r : H) (hr : r ∈ doubleRepresentatives K) : leastDoubleRepresentative K r = r := by
        obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hr
        subst r
        exact stableD x _ (repDmem x)
      have fiberD (r : H) (hr : r ∈ doubleRepresentatives K) (x : H) :
          x ∈ sourceDoubleCoset K r ↔ leastDoubleRepresentative K x = r := by
        constructor
        · intro hx; exact (stableD r x hx).trans (fixedD r hr)
        · intro hx
          have he := eqD x _ (repDmem x)
          rw [hx] at he
          rw [he]
          exact selfD x
      have factorCoeff (h : H) : (orderedFactor K a b).coeff h =
          ∑ d ∈ doubleRepresentatives K, blockMass K a b d h := by
        simpa [orderedFactor,List.map_map,Function.comp_def] using
          (List.sum_toFinset (fun d => blockMass K a b d h)
            (Finset.sort_nodup (doubleRepresentatives K) (· ≤ ·))).symm
      have wholeMass (F : H → Finset H) (sub : ∀ h, F h ⊆ sourceDoubleCoset K h) (h : H) :
          (∑ x ∈ F h, (orderedFactor K a b).coeff x) =
            ∑ x ∈ F h, blockMass K a b (leastDoubleRepresentative K h) x := by
        simp_rw [factorCoeff]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_single (leastDoubleRepresentative K h)
        · intro d hd hne
          apply Finset.sum_eq_zero
          intro x hx
          apply blockOutside d x
          intro hxd
          have he := (fiberD d hd x).mp hxd
          have hrep := stableD h x (sub h hx)
          exact hne (he.symm.trans hrep)
        · intro hn
          exact (hn (repIn h)).elim
      have coeffRight (p : MonoidAlgebra ℕ H) (h : H) :
          (p * subgroupUniform K).coeff h = ∑ x ∈ sourceRightCoset K h, p.coeff x := by
        rw [MonoidAlgebra.coeff_mul_apply_right]
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        calc
          _ = ∑ k ∈ Finset.univ.filter (fun k : H => k ∈ K), p.coeff (h*k⁻¹) := by
            simp [subgroupUniform,Finset.sum_filter]
          _ = _ := by
            apply Finset.sum_nbij' (fun k : H => h*k⁻¹) (fun x : H => x⁻¹*h)
            · intro k hk
              have hk' : k ∈ K := by simpa using hk
              simpa [sourceRightCoset] using K.inv_mem hk'
            · intro x hx
              have hx' : h⁻¹*x ∈ K := by simpa [sourceRightCoset] using hx
              simpa [mul_inv_rev] using K.inv_mem hx'
            · intro k _; simp [mul_assoc]
            · intro x _; simp [mul_assoc]
            · intro k _; rfl
      have coeffLeft (p : MonoidAlgebra ℕ H) (h : H) :
          (subgroupUniform K * p).coeff h = ∑ x ∈ sourceLeftCoset K h, p.coeff x := by
        rw [MonoidAlgebra.coeff_mul_apply_left]
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        calc
          _ = ∑ k ∈ Finset.univ.filter (fun k : H => k ∈ K), p.coeff (k⁻¹*h) := by
            simp [subgroupUniform,Finset.sum_filter]
          _ = _ := by
            apply Finset.sum_nbij' (fun k : H => k⁻¹*h) (fun x : H => h*x⁻¹)
            · intro k hk
              have hk' : k ∈ K := by simpa using hk
              simpa [sourceLeftCoset] using K.inv_mem hk'
            · intro x hx
              have hx' : x*h⁻¹ ∈ K := by simpa [sourceLeftCoset] using hx
              simpa [mul_inv_rev] using K.inv_mem hx'
            · intro k _; simp [mul_assoc]
            · intro x _; simp [mul_assoc]
            · intro k _; rfl
      refine ⟨?_,?_,?_,coeffRight,coeffLeft⟩
      · apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro h
        rcases native (leastDoubleRepresentative K h) a b (balance _) with
          ⟨_,_,unique,_,_,_,_,_,_,_,massRow,_,_,_⟩
        have hd := (fiberD _ (repIn h) h).mpr rfl
        obtain ⟨r,hr,_⟩ := unique h hd
        rw [coeffRight,wholeMass (sourceRightCoset K) subR h,eqR r.val h hr]
        exact (constant r.val h hr).trans (massRow r).symm
      · apply MonoidAlgebra.ext
        apply Finsupp.ext
        intro h
        rcases native (leastDoubleRepresentative K h) a b (balance _) with
          ⟨_,_,_,unique,_,_,_,_,_,_,_,massColumn,_,_⟩
        have hd := (fiberD _ (repIn h) h).mpr rfl
        obtain ⟨c,hc,_⟩ := unique h hd
        rw [coeffLeft,wholeMass (sourceLeftCoset K) subL h,eqL c.val h hc]
        rw [MonoidAlgebra.coeff_smul]
        simpa [groupUniform] using (massColumn c).symm
      · rw [← List.sum_toFinset _ (Finset.sort_nodup (doubleRepresentatives K) (· ≤ ·))]
        simp only [Finset.sort_toFinset]
        apply Finset.sum_congr rfl
        intro d _
        rcases native d a b (balance d) with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,count⟩
        exact count
  have rightEq (a : MonoidAlgebra ℕ H) :
      a * subgroupUniform K = (Finset.univ.filter (fun k : H => k ∈ K)).card • a ↔
        ∀ h x : H, x ∈ sourceRightCoset K h → a.coeff x = a.coeff h := by
    classical
    let ks : Finset H := Finset.univ.filter (fun k => k ∈ K)
    have coeffRight (p : MonoidAlgebra ℕ H) (h : H) :
        (p * subgroupUniform K).coeff h = ∑ x ∈ sourceRightCoset K h, p.coeff x := by
      rw [MonoidAlgebra.coeff_mul_apply_right]
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      calc
        _ = ∑ k ∈ ks, p.coeff (h*k⁻¹) := by
          simp [subgroupUniform,ks,Finset.sum_filter]
        _ = _ := by
          apply Finset.sum_nbij' (fun k : H => h*k⁻¹) (fun x : H => x⁻¹*h)
          · intro k hk
            have hk' : k ∈ K := by simpa [ks] using hk
            simpa [sourceRightCoset] using K.inv_mem hk'
          · intro x hx
            have hx' : h⁻¹*x ∈ K := by simpa [sourceRightCoset] using hx
            simpa [ks,mul_inv_rev] using K.inv_mem hx'
          · intro k _; simp [mul_assoc]
          · intro x _; simp [mul_assoc]
          · intro k _; rfl
    have eqCoset (h x : H) (hx : x ∈ sourceRightCoset K h) :
        sourceRightCoset K x = sourceRightCoset K h := by
      have hx' : h⁻¹*x ∈ K := by simpa [sourceRightCoset] using hx
      have he := (leftCoset_eq_iff K).mpr hx'
      ext y
      simpa [sourceRightCoset,mem_leftCoset_iff] using (Set.ext_iff.mp he y).symm
    have cardCoset (h : H) : (sourceRightCoset K h).card = ks.card := by
      apply Finset.card_nbij' (fun x : H => h⁻¹*x) (fun k : H => h*k)
      · intro x hx; simpa [ks,sourceRightCoset] using hx
      · intro k hk; simpa [ks,sourceRightCoset] using hk
      · intro x _; simp
      · intro k _; simp
    have qpos : 0 < ks.card := Finset.card_pos.mpr ⟨1,by simp [ks]⟩
    constructor
    · intro he h x hx
      have hh := congrArg (fun p : MonoidAlgebra ℕ H => p.coeff h) he
      have hxx := congrArg (fun p : MonoidAlgebra ℕ H => p.coeff x) he
      simp only [coeffRight,MonoidAlgebra.coeff_smul,smul_eq_mul] at hh hxx
      rw [eqCoset h x hx] at hxx
      exact Nat.eq_of_mul_eq_mul_left qpos (hxx.symm.trans hh)
    · intro hc
      apply MonoidAlgebra.ext
      apply Finsupp.ext
      intro h
      rw [coeffRight]
      calc
        _ = ∑ _x ∈ sourceRightCoset K h, a.coeff h :=
          Finset.sum_congr rfl (fun x hx => hc h x hx)
        _ = _ := by rw [MonoidAlgebra.coeff_smul]; simp [cardCoset,ks,smul_eq_mul]

  let C := ∀ h x : H, x ∈ sourceRightCoset K h → a.coeff x = a.coeff h
  let B := ∀ d : H, (∑ r ∈ blockRows K d, a.coeff r) = (blockRows K d).card * b
  let F := ∃ p : MonoidAlgebra ℕ H,
    a = p * subgroupUniform K ∧ b • (groupUniform : MonoidAlgebra ℕ H) = subgroupUniform K * p
  let q := (Finset.univ.filter (fun k : H => k ∈ K)).card
  have coefficients := supplied.2.1 0 0 (by simp) (by simp)
  have coeffRight := coefficients.2.2.2.1
  have coeffLeft := coefficients.2.2.2.2
  have eqR := supplied.2.2.1
  have eqD := supplied.2.2.2.1
  have subL := supplied.2.2.2.2.1
  have selfD := supplied.2.2.2.2.2
  have sumPartition (d : H) (reps : Finset H) (sets : H → Finset H)
      (cover : reps.biUnion sets = sourceDoubleCoset K d)
      (unique : ∀ x ∈ sourceDoubleCoset K d, ∃! r : reps, x ∈ sets r.val)
      (f : H → ℕ) :
      (∑ r ∈ reps, ∑ x ∈ sets r, f x) = ∑ x ∈ sourceDoubleCoset K d, f x := by
    rw [← cover]
    symm
    apply Finset.sum_biUnion
    intro r hr s hs hne
    apply Finset.disjoint_left.mpr
    intro x hxr hxs
    have hx : x ∈ sourceDoubleCoset K d :=
      cover ▸ Finset.mem_biUnion.mpr ⟨r, hr, hxr⟩
    obtain ⟨z, hz, hu⟩ := unique x hx
    have he : (⟨r, hr⟩ : reps) = (⟨s, hs⟩ : reps) :=
      (hu ⟨r, hr⟩ hxr).trans (hu ⟨s, hs⟩ hxs).symm
    exact hne (congrArg Subtype.val he)
  have uniformCoeff (n : ℕ) (h : H) :
      (n • (groupUniform : MonoidAlgebra ℕ H)).coeff h = n := by
    rw [MonoidAlgebra.coeff_smul]
    change n • (1 : ℕ) = n
    simp
  have necessary : F → C ∧ B := by
    rintro ⟨p, ha, hb⟩
    refine ⟨?_, ?_⟩
    · intro h x hx
      rw [ha, coeffRight, coeffRight, eqR h x hx]
    · intro d
      rcases supplied.1 d with ⟨rows, columns, uniqueR, uniqueL, cells, counts, tpos, qcard⟩
      calc
        (∑ r ∈ blockRows K d, a.coeff r) =
            ∑ r ∈ blockRows K d, ∑ x ∈ sourceRightCoset K r, p.coeff x := by
              simp_rw [ha, coeffRight]
        _ = ∑ x ∈ sourceDoubleCoset K d, p.coeff x :=
          sumPartition d _ _ rows uniqueR p.coeff
        _ = ∑ c ∈ blockColumns K d, ∑ x ∈ sourceLeftCoset K c, p.coeff x :=
          (sumPartition d _ _ columns uniqueL p.coeff).symm
        _ = ∑ _c ∈ blockColumns K d, b := by
          apply Finset.sum_congr rfl
          intro c _
          have hc := congrArg (fun z : MonoidAlgebra ℕ H => z.coeff c) hb
          rw [uniformCoeff, coeffLeft] at hc
          exact hc.symm
        _ = (blockRows K d).card * b := by simp [counts]
  have fixedIff : F ↔ C ∧ B := by
    refine ⟨necessary, ?_⟩
    rintro ⟨hc, hb⟩
    have constructed := supplied.2.1 a b hc hb
    exact ⟨orderedFactor K a b, constructed.1, constructed.2.1⟩
  have secondIff (hc : C) : subgroupUniform K * a =
      (q * b) • (groupUniform : MonoidAlgebra ℕ H) ↔ B := by
    have formula (h : H) : (subgroupUniform K * a).coeff h =
        (sourceRightCoset K h ∩ sourceLeftCoset K h).card *
          (∑ r ∈ blockRows K h, a.coeff r) := by
      rcases supplied.1 h with ⟨rows, columns, uniqueR, uniqueL, cells, counts, tpos, qcard⟩
      have cover : (blockRows K h).biUnion
          (fun r => sourceRightCoset K r ∩ sourceLeftCoset K h) = sourceLeftCoset K h := by
        ext x
        constructor
        · intro hx
          obtain ⟨r, _, hx⟩ := Finset.mem_biUnion.mp hx
          exact (Finset.mem_inter.mp hx).2
        · intro hx
          have hu : x ∈ (blockRows K h).biUnion (sourceRightCoset K) :=
            rows.symm ▸ subL h hx
          obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hu
          exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_inter.mpr ⟨hxr, hx⟩⟩
      have disjoint : Set.PairwiseDisjoint (↑(blockRows K h))
          (fun r => sourceRightCoset K r ∩ sourceLeftCoset K h) := by
        intro r hr s hs hne
        apply Finset.disjoint_left.mpr
        intro x hxr hxs
        have hd := subL h (Finset.mem_inter.mp hxr).2
        obtain ⟨z, hz, hu⟩ := uniqueR x hd
        have he : (⟨r, hr⟩ : blockRows K h) = (⟨s, hs⟩ : blockRows K h) :=
          (hu ⟨r, hr⟩ (Finset.mem_inter.mp hxr).1).trans
            (hu ⟨s, hs⟩ (Finset.mem_inter.mp hxs).1).symm
        exact hne (congrArg Subtype.val he)
      rw [coeffLeft]
      conv_lhs => rw [← cover, Finset.sum_biUnion disjoint]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ x ∈ sourceRightCoset K r ∩ sourceLeftCoset K h, a.coeff x) =
            ∑ _x ∈ sourceRightCoset K r ∩ sourceLeftCoset K h, a.coeff r :=
              Finset.sum_congr rfl (fun x hx => hc r x (Finset.mem_inter.mp hx).1)
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul,
            (cells r (Finset.mem_filter.mp hr).2 h (selfD h)).2]
          simp
    constructor
    · intro he d
      rcases supplied.1 d with ⟨_, _, _, _, _, _, tpos, qcard⟩
      have hd := congrArg (fun z : MonoidAlgebra ℕ H => z.coeff d) he
      rw [formula, uniformCoeff] at hd
      rw [show q = _ from qcard, mul_assoc] at hd
      exact Nat.eq_of_mul_eq_mul_left tpos hd
    · intro hb
      apply MonoidAlgebra.ext
      apply Finsupp.ext
      intro h
      rcases supplied.1 h with ⟨_, _, _, _, _, _, _, qcard⟩
      rw [formula, hb h, uniformCoeff]
      rw [show q = _ from qcard]
      simp [mul_assoc]
  have pureIff : F ↔
      a * subgroupUniform K = q • a ∧
      subgroupUniform K * a = (q * b) • (groupUniform : MonoidAlgebra ℕ H) := by
    rw [fixedIff, rightEq a]
    constructor
    · rintro ⟨hc, hb⟩
      exact ⟨hc, (secondIff hc).mpr hb⟩
    · rintro ⟨hc, he⟩
      exact ⟨hc, (secondIff hc).mp he⟩
  have coefficientNone : firstCoefficientMismatch K a = none ↔ C := by
    constructor
    · intro hn h x hx
      by_contra hne
      have hz := (List.findSome?_eq_none_iff.mp hn) h (by simp)
      have hz' : (((sourceRightCoset K h).filter (fun x => a.coeff h ≠ a.coeff x)).sort
          (· ≤ ·)).head? = none := by simpa using hz
      have empty := List.head?_eq_none_iff.mp hz'
      have hm : x ∈ (((sourceRightCoset K h).filter
          (fun x => a.coeff h ≠ a.coeff x)).sort (· ≤ ·)) := by
        simpa using And.intro hx (Ne.symm hne)
      simpa [empty] using hm
    · intro hc
      apply List.findSome?_eq_none_iff.mpr
      intro h _
      have empty : (sourceRightCoset K h).filter (fun x => a.coeff h ≠ a.coeff x) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (Finset.mem_filter.mp hx).2 (hc h x (Finset.mem_filter.mp hx).1).symm
      simp [empty]
  have coefficientSome (pair : H × H) (hs : firstCoefficientMismatch K a = some pair) :
      pair.2 ∈ sourceRightCoset K pair.1 ∧ a.coeff pair.1 ≠ a.coeff pair.2 := by
    obtain ⟨h, hh, he⟩ := List.exists_of_findSome?_eq_some hs
    cases hz : (((sourceRightCoset K h).filter (fun x => a.coeff h ≠ a.coeff x)).sort
        (· ≤ ·)).head? with
    | none => simp [hz] at he
    | some x =>
        have ep : (h, x) = pair := by simpa [hz] using he
        have hx := List.mem_of_head? hz
        have hx' : x ∈ sourceRightCoset K h ∧ a.coeff h ≠ a.coeff x := by simpa using hx
        simpa [← ep] using hx'
  have balanceSome (d : H) (hs : firstBalanceMismatch K a b = some d) :
      d ∈ doubleRepresentatives K ∧
      (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b := by
    have hd := List.mem_of_head? hs
    simpa using hd
  have balanceNone : firstBalanceMismatch K a b = none ↔ B := by
    have blockEq (d : H) : blockRows K (leastDoubleRepresentative K d) = blockRows K d := by
      have he := eqD d (leastDoubleRepresentative K d) (Finset.min'_mem _ _)
      simp only [blockRows, he]
    constructor
    · intro hn d
      have empty := List.head?_eq_none_iff.mp hn
      have hd : leastDoubleRepresentative K d ∈ doubleRepresentatives K :=
        Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
      by_contra hne
      have hm : leastDoubleRepresentative K d ∈
          (((doubleRepresentatives K).filter (fun d =>
            (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b)).sort (· ≤ ·)) := by
        simpa [blockEq d] using And.intro hd hne
      simpa [empty] using hm
    · intro hb
      have empty : (doubleRepresentatives K).filter (fun d =>
          (∑ r ∈ blockRows K d, a.coeff r) ≠ (blockRows K d).card * b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        exact (Finset.mem_filter.mp hd).2 (hb d)
      simp [firstBalanceMismatch, empty]
  have inspectIff (p : MonoidAlgebra ℕ H) : inspectAndConstruct K a b = .inr p ↔
      p = orderedFactor K a b ∧ C ∧ B := by
    constructor
    · intro hs
      cases hc : firstCoefficientMismatch K a with
      | some pair => simp [inspectAndConstruct, hc] at hs
      | none =>
          cases hb : firstBalanceMismatch K a b with
          | some d => simp [inspectAndConstruct, hc, hb] at hs
          | none =>
              have hp : orderedFactor K a b = p := by simpa [inspectAndConstruct, hc, hb] using hs
              exact ⟨hp.symm, coefficientNone.mp hc, balanceNone.mp hb⟩
    · rintro ⟨rfl, hc, hb⟩
      simp [inspectAndConstruct, coefficientNone.mpr hc, balanceNone.mpr hb]
  refine ⟨fixedIff, secondIff, pureIff, coefficientNone, balanceNone,
    coefficientSome, balanceSome, inspectIff, ?_, ?_⟩
  · intro p hp
    obtain ⟨rfl, hc, hb⟩ := (inspectIff p).mp hp
    have constructed := supplied.2.1 a b hc hb
    exact ⟨constructed.1, constructed.2.1, constructed.2.2.1⟩
  · intro bad hs
    cases hc : firstCoefficientMismatch K a with
    | some pair =>
        have he : Sum.inl pair = bad := by simpa [inspectAndConstruct, hc] using hs
        subst bad
        refine ⟨coefficientSome pair hc, ?_⟩
        intro hf
        have hn := coefficientNone.mpr (necessary hf).1
        simp [hc] at hn
    | none =>
        cases hb : firstBalanceMismatch K a b with
        | some d =>
            have he : Sum.inr d = bad := by simpa [inspectAndConstruct, hc, hb] using hs
            subst bad
            refine ⟨balanceSome d hb, ?_⟩
            intro hf
            have hn := balanceNone.mpr (necessary hf).2
            simp [hb] at hn
        | none => simp [inspectAndConstruct, hc, hb] at hs

end NativeCosets


/-- The source C2 presentation uses e before g; the order is independent of multiplication. -/
instance sourceC2Order : LinearOrder (Multiplicative (ZMod 2)) :=
  LinearOrder.lift' (fun x => x.toAdd.val)
    (fun x y h => show x = y from ZMod.val_injective 2 h)

instance sourceC2TopMembership :
    DecidablePred (fun h : Multiplicative (ZMod 2) => h ∈ (⊤ : Subgroup _)) :=
  fun h => isTrue (Subgroup.mem_top h)

/-- The actual upper-right entry 2(e+g)+(e-g)=3e+g of source Proposition 22.4. -/
def source22_4Input : MonoidAlgebra ℕ (Multiplicative (ZMod 2)) :=
  MonoidAlgebra.ofCoeff {
    support := Finset.univ
    toFun := fun h => if h.toAdd = 0 then 3 else 1
    mem_support_toFun := by intro h; split_ifs <;> simp }

/-- The actual inspection result for the original entry and prescribed source budget. -/
def source22_4Certificate :
    Sum (Sum (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2))) (MonoidAlgebra ℕ (Multiplicative (ZMod 2))) :=
  inspectAndConstruct (⊤ : Subgroup (Multiplicative (ZMod 2))) source22_4Input 2

/-- The fixed-K question for that original entry, with K=C2 and b=2.
Its answer concerns this prescribed factor, not unrestricted shift equivalence. -/
def source22_4FixedFactorQuestion : Prop :=
  ¬ ∃ p : MonoidAlgebra ℕ (Multiplicative (ZMod 2)),
    source22_4Input = p * subgroupUniform (⊤ : Subgroup (Multiplicative (ZMod 2))) ∧
    2 • (groupUniform : MonoidAlgebra ℕ (Multiplicative (ZMod 2))) =
      subgroupUniform (⊤ : Subgroup (Multiplicative (ZMod 2))) * p

#print axioms ordered_subgroup_factorization_correct

end D5.S3.ConceptDynamics.Coding.OrderedSubgroupFactorization
