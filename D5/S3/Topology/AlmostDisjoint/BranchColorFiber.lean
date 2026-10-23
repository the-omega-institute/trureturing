/- GID: D5/S3/Topology/AlmostDisjoint/BranchColorFiber
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/BranchColorFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual branch-tail closed slices upgrade partitioner color fibers to continuum. -/

import D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal
import Mathlib.Topology.MetricSpace.Perfect

open Set Filter Topology
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily
open D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal
open D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal
open scoped Cardinal

namespace D5.S3.Topology.AlmostDisjoint.BranchColorFiber

private noncomputable def prefixNat (x : Branch) (k : ℕ) : ℕ :=
  wordEquivNat (wordPrefix x k)

private theorem prefix_mem (x : Branch) (k : ℕ) : prefixNat x k ∈ natBranch x :=
  ⟨wordPrefix x k, ⟨k, rfl⟩, rfl⟩

private theorem natBranch_infinite (x : Branch) : (natBranch x).Infinite :=
  ((branch_system 0).2.1 x).image wordEquivNat.injective.injOn

private theorem partitioner_tail_iff (M : Branch → Set ℕ)
    (hbranch : ∀ x, natBranch x ⊆ M x) (D : Set ℕ) (hp : Partitions M D)
    (x : Branch) :
    (M x \ D).Finite ↔ ∃ m : ℕ, ∀ k ≥ m, prefixNat x k ∈ D := by
  constructor
  · intro hfinite
    let lengthOf : ℕ → ℕ := fun n => (wordEquivNat.symm n).val.length
    obtain ⟨m, hm⟩ := (hfinite.image lengthOf).bddAbove
    refine ⟨m, ?_⟩
    intro k hk
    by_contra hbad
    have hlen := hm (mem_image_of_mem lengthOf
      (show prefixNat x k ∈ M x \ D from ⟨hbranch x (prefix_mem x k), hbad⟩))
    have heq : lengthOf (prefixNat x k) = k + 1 := by
      simp [lengthOf, prefixNat, wordPrefix]
    rw [heq] at hlen
    omega
  · rintro ⟨m, hm⟩
    rcases hp x with h | h
    · exact h
    · exfalso
      apply natBranch_infinite x
      apply (((finite_lt_nat m).image (prefixNat x)).union h).subset
      rintro n ⟨s, ⟨k, rfl⟩, rfl⟩
      by_cases hk : k < m
      · exact Or.inl ⟨k, hk, rfl⟩
      · exact Or.inr ⟨hbranch x (prefix_mem x k), hm k (Nat.le_of_not_gt hk)⟩

private theorem prefix_color_closed (D : Set ℕ) (k : ℕ) :
    IsClosed {x : Branch | prefixNat x k ∈ D} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  apply Filter.mem_of_superset
    ((PiNat.isOpen_cylinder (fun _ => Letter) x (k + 1)).mem_nhds
      (PiNat.self_mem_cylinder x (k + 1)))
  intro y hy
  have hres : PiNat.res y (k + 1) = PiNat.res x (k + 1) := by
    simpa only [PiNat.cylinder_eq_res, mem_setOf_eq] using hy
  have hpref : wordPrefix y k = wordPrefix x k := Subtype.ext hres
  change prefixNat x k ∉ D at hx
  change prefixNat y k ∉ D
  simpa only [prefixNat, hpref] using hx

/-- Each closed slice uses the actual finite prefixes of the four-letter branch,
not membership in an arbitrary enlarged maximal-family member. -/
def TailSlice (D : Set ℕ) (r : unitInterval) (m : ℕ) : Set Branch :=
  {x | limitValue x = r} ∩ ⋂ k : ℕ, ⋂ (_ : m ≤ k), {x | prefixNat x k ∈ D}

private theorem tailSlice_closed (D : Set ℕ) (r : unitInterval) (m : ℕ) :
    IsClosed (TailSlice D r m) :=
  (isClosed_eq (branch_system 0).2.2.2.2.1 continuous_const).inter
    (isClosed_iInter fun k => isClosed_iInter fun _ => prefix_color_closed D k)

private theorem colorFiber_eq_slices (M : Branch → Set ℕ)
    (hbranch : ∀ x, natBranch x ⊆ M x) (D : Set ℕ) (hp : Partitions M D)
    (r : unitInterval) :
    {x | limitValue x = r ∧ (M x \ D).Finite} = ⋃ m : ℕ, TailSlice D r m := by
  ext x
  simp only [mem_setOf_eq, mem_iUnion, TailSlice, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hl, hcolor⟩
    obtain ⟨m, hm⟩ := (partitioner_tail_iff M hbranch D hp x).mp hcolor
    exact ⟨m, hl, hm⟩
  · rintro ⟨m, hl, hm⟩
    exact ⟨hl, (partitioner_tail_iff M hbranch D hp x).mpr ⟨m, hm⟩⟩

/-- For the actual branch labeling and the actual binary limit map, the
eventual-color fiber at a support point has continuum cardinality. Branch
containment is essential for its closed-tail description. -/
theorem partitioner_fiber_continuum (M : Branch → Set ℕ)
    (hbranch : ∀ x, natBranch x ⊆ M x) (hmad : MADFamily (range M))
    (hc : ∀ x, ConvergesOn natValue (M x) (limitValue x))
    (D : Set ℕ) (hp : Partitions M D) (r : unitInterval)
    (hr : r ∈ ColorSupport M natValue D) :
    Cardinal.mk {x : Branch // limitValue x = r ∧ (M x \ D).Finite} =
      Cardinal.continuum := by
  classical
  have hunc := color_support_fiber_uncountable M natValue limitValue hmad hc D hp r hr
  have heq := colorFiber_eq_slices M hbranch D hp r
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ¬ (TailSlice D r m).Countable := by
    by_contra h
    push Not at h
    apply hunc
    rw [heq]
    exact countable_iUnion h
  obtain ⟨f, hf, _, hinj⟩ :=
    (tailSlice_closed D r m).exists_nat_bool_injection_of_not_countable hm
  apply le_antisymm
  · let g : {x : Branch // limitValue x = r ∧ (M x \ D).Finite} →
        {x : Branch // limitValue x = r} := fun x => ⟨x.val, x.property.1⟩
    have hg : Function.Injective g := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {x : Branch // limitValue x = r} => z.val) h
    exact (Cardinal.mk_le_of_injective hg).trans_eq ((branch_system 0).2.2.2.2.2.2 r)
  · have hfiber : range f ⊆ {x | limitValue x = r ∧ (M x \ D).Finite} := by
      rw [heq]
      exact hf.trans (subset_iUnion (TailSlice D r) m)
    let g : (ℕ → Bool) → {x : Branch // limitValue x = r ∧ (M x \ D).Finite} :=
      fun x => ⟨f x, hfiber (mem_range_self x)⟩
    have hg : Function.Injective g := by
      intro x y h
      exact hinj (congrArg Subtype.val h)
    have hle := Cardinal.mk_le_of_injective hg
    simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.lift_id, Cardinal.two_power_aleph0] using hle

end D5.S3.Topology.AlmostDisjoint.BranchColorFiber
