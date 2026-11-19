/- GID: D5/S1/Words/Complexity/SubshiftTopology
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/SubshiftTopology
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Word subshifts are closed orbit closures, and the golden subshift is perfect of continuum cardinality. -/

import D5.S1.Words.Complexity.SubshiftHausdorffDimension
import D5.S1.Words.GoldenRecurrence
import Mathlib.Topology.MetricSpace.Perfect

namespace D5.S1.Words.Complexity.SubshiftTopology

open D5.S1.Words
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open Set SymbolicDynamics Topology
open scoped Cardinal

noncomputable section

variable {A : Type*} [Fintype A] [nonemptyA : Nonempty A] [TopologicalSpace A]
  [DiscreteTopology A]

/-- The prefix-language subshift is closed in the product topology. -/
theorem isClosed_wordSubshift (x : ℕ → A) : IsClosed (wordSubshift x) := by
  classical
  have hsubshift : wordSubshift x =
      ⋂ n : ℕ, {y : ℕ → A | (fun k : Fin n ↦ y k.val) ∈ wordFactorSet x n} := by
    ext y
    simp [wordSubshift]
  rw [hsubshift]
  change IsClosed (⋂ n : ℕ, {y : ℕ → A | (fun k : Fin n ↦ y k.val) ∈ wordFactorSet x n})
  refine isClosed_iInter fun n ↦ ?_
  let I := {u : Fin n → A // u ∈ wordFactorSet x n}
  have hlevel :
      {y : ℕ → A | (fun k : Fin n ↦ y k.val) ∈ wordFactorSet x n} =
        ⋃ u : I, FullShift.cylinder (Finset.range n)
          (Fin.val.extend u.1 fun _ ↦ Classical.choice nonemptyA) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hy
      refine ⟨⟨fun k : Fin n ↦ y k.val, hy⟩, ?_⟩
      rw [FullShift.mem_cylinder]
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      simpa using
        (Fin.val_injective.extend_apply (fun k : Fin n ↦ y k.val)
          (fun _ ↦ Classical.choice nonemptyA) ⟨i, hi'⟩).symm
    · rintro ⟨u, hyu⟩
      have hprefix : (fun k : Fin n ↦ y k.val) = u.1 := by
        funext k
        have hyk := FullShift.mem_cylinder.mp hyu k.val (Finset.mem_range.mpr k.isLt)
        exact hyk.trans
          (Fin.val_injective.extend_apply u.1 (fun _ ↦ Classical.choice nonemptyA) k)
      rw [hprefix]
      exact u.2
  rw [hlevel]
  exact isClosed_iUnion_of_finite fun u ↦ FullShift.isClosed_cylinder (Finset.range n) _

omit nonemptyA [TopologicalSpace A] [DiscreteTopology A] in
private theorem shift_mem_wordSubshift (x : ℕ → A) (i : ℕ) :
    FullShift.shift i x ∈ wordSubshift x := by
  induction i with
  | zero => simpa using self_mem_wordSubshift x
  | succ i ih =>
      have hshift : FullShift.shift (Nat.succ i) x =
          fun j ↦ FullShift.shift i x (j + 1) := by
        funext j
        simp only [FullShift.shift_apply]
        congr 1
        omega
      rw [hshift]
      exact wordSubshift_shift_invariant x ih

/-- The closure of the forward shift orbit is exactly the prefix-language subshift. -/
theorem closure_shift_orbit_eq_wordSubshift (x : ℕ → A) :
    closure (Set.range fun i : ℕ ↦ FullShift.shift i x) = wordSubshift x := by
  apply Set.Subset.antisymm
  · apply (isClosed_wordSubshift x).closure_subset_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact shift_mem_wordSubshift x i
  · intro y hy
    rw [mem_closure_iff]
    intro U hU hyU
    obtain ⟨_, ⟨z, n, rfl⟩, hyc, hcU⟩ :=
      (PiNat.isTopologicalBasis_cylinders fun _ : ℕ ↦ A).exists_subset_of_mem_open hyU hU
    obtain ⟨i, hi⟩ := mem_wordFactorSet.mp (hy n)
    refine ⟨FullShift.shift i x, hcU ?_, ⟨i, rfl⟩⟩
    rw [PiNat.mem_cylinder_iff]
    intro k hk
    have hyk := PiNat.mem_cylinder_iff.mp hyc k hk
    have hik := congrFun hi ⟨k, hk⟩
    simpa [FullShift.shift, wordFactor] using hik.symm.trans hyk

private theorem golden_wordFactorSet_card (n : ℕ) :
    (wordFactorSet goldenWord n).card = n + 1 := by
  classical
  have himg : goldenFactorSet n = (wordFactorSet goldenWord n).image List.ofFn := by
    ext w
    simp only [Finset.mem_image, mem_goldenFactorSet, mem_wordFactorSet]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wordFactor goldenWord n i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  calc
    (wordFactorSet goldenWord n).card = (goldenFactorSet n).card := by
      rw [himg, Finset.card_image_of_injective _ List.ofFn_injective]
    _ = n + 1 := golden_factor_complexity n

private theorem golden_shift_injective :
    Function.Injective (fun i : ℕ ↦ FullShift.shift i goldenWord) := by
  intro i j hij
  by_contra hne
  wlog hijlt : i < j generalizing i j with hsymm
  · have hjilt : j < i := lt_of_le_of_ne (Nat.le_of_not_gt hijlt) (Ne.symm hne)
    exact hsymm hij.symm (Ne.symm hne) hjilt
  let p := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hijlt
  have hip : i + p = j := Nat.add_sub_of_le hijlt.le
  have hperiodic : Function.Periodic (fun t : ℕ ↦ goldenWord (i + t)) p := by
    intro t
    have ht : goldenWord (i + t) = goldenWord (j + t) := by
      simpa only [FullShift.shift_apply] using congrFun hij t
    calc
      goldenWord (i + (t + p)) = goldenWord ((i + p) + t) := by congr 1; omega
      _ = goldenWord (j + t) := by rw [hip]
      _ = goldenWord (i + t) := ht.symm
  let representatives : Finset (Fin j → Bool) :=
    (Finset.range j).image fun k ↦ wordFactor goldenWord j k
  have hsubset : wordFactorSet goldenWord j ⊆ representatives := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_wordFactorSet.mp hw
    by_cases hki : k < i
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (hki.trans hijlt), rfl⟩
    · let r := i + (k - i) % p
      have hrj : r < j := by
        calc
          r = i + (k - i) % p := rfl
          _ < i + p := Nat.add_lt_add_left (Nat.mod_lt (k - i) hp) i
          _ = j := hip
      refine Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hrj, ?_⟩
      funext q
      have hmap := (hperiodic.add_const q.val).map_mod_nat (k - i)
      change goldenWord (i + ((k - i) % p + q.val)) =
        goldenWord (i + ((k - i) + q.val)) at hmap
      change goldenWord (r + q.val) = goldenWord (k + q.val)
      rw [show k = i + (k - i) by omega]
      simpa [r, Nat.add_assoc] using hmap
  have hcard_le : (wordFactorSet goldenWord j).card ≤ j :=
    (Finset.card_le_card hsubset).trans
      (Finset.card_image_le.trans_eq (Finset.card_range j))
  rw [golden_wordFactorSet_card] at hcard_le
  omega

private theorem exists_later_shift_mem_cylinder {y : ℕ → Bool}
    (hy : y ∈ wordSubshift goldenWord) (n B : ℕ) :
    ∃ j, B < j ∧ FullShift.shift j goldenWord ∈ PiNat.cylinder y n := by
  obtain ⟨i, hi⟩ := mem_wordFactorSet.mp (hy n)
  have hfactor : goldenFactor n i ∈ goldenFactorSet n :=
    mem_goldenFactorSet.mpr ⟨i, rfl⟩
  obtain ⟨j, hBj, hj⟩ := golden_factor_recurrent hfactor B
  refine ⟨j, hBj, PiNat.mem_cylinder_iff.mpr fun k hk ↦ ?_⟩
  have hfunctions : wordFactor goldenWord n i = wordFactor goldenWord n j := by
    have hj' : List.ofFn (wordFactor goldenWord n i) =
        List.ofFn (wordFactor goldenWord n j) := by
      change goldenFactor n i = goldenFactor n j
      exact hj
    exact List.ofFn_inj.mp hj'
  have hyi := congrFun hi ⟨k, hk⟩
  have hij := congrFun hfunctions ⟨k, hk⟩
  simpa [FullShift.shift, wordFactor] using hij.symm.trans hyi.symm

/-- The golden prefix-language subshift is perfect. -/
theorem golden_wordSubshift_perfect : Perfect (wordSubshift goldenWord) := by
  refine ⟨isClosed_wordSubshift goldenWord, preperfect_iff_nhds.mpr ?_⟩
  intro y hy U hU
  obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
  obtain ⟨_, ⟨z, n, rfl⟩, hyc, hcV⟩ :=
    (PiNat.isTopologicalBasis_cylinders fun _ : ℕ ↦ Bool).exists_subset_of_mem_open
      hyV hVopen
  have hcy : PiNat.cylinder y n = PiNat.cylinder z n :=
    PiNat.mem_cylinder_iff_eq.mp hyc
  have hcU : PiNat.cylinder y n ⊆ U := by
    rw [hcy]
    exact hcV.trans hVU
  obtain ⟨j, hjpos, hjc⟩ := exists_later_shift_mem_cylinder hy n 0
  obtain ⟨k, hjk, hkc⟩ := exists_later_shift_mem_cylinder hy n j
  by_cases hjy : FullShift.shift j goldenWord = y
  · refine ⟨FullShift.shift k goldenWord, ⟨hcU hkc, shift_mem_wordSubshift _ _⟩, ?_⟩
    intro hky
    have hkj : FullShift.shift k goldenWord = FullShift.shift j goldenWord :=
      hky.trans hjy.symm
    exact (Nat.ne_of_gt hjk) (golden_shift_injective hkj)
  · exact ⟨FullShift.shift j goldenWord, ⟨hcU hjc, shift_mem_wordSubshift _ _⟩, hjy⟩

/-- The golden prefix-language subshift has cardinality continuum. -/
theorem golden_wordSubshift_cardinal_eq_continuum :
    Cardinal.mk (wordSubshift goldenWord) = Cardinal.continuum := by
  apply le_antisymm
  · simpa using Cardinal.mk_set_le (wordSubshift goldenWord)
  · letI : MetricSpace (ℕ → Bool) :=
      PiNat.metricSpaceOfDiscreteUniformity fun _ ↦ rfl
    letI : CompleteSpace (ℕ → Bool) := inferInstance
    obtain ⟨f, hfsub, _, hfinj⟩ :=
      golden_wordSubshift_perfect.exists_nat_bool_injection
        ⟨goldenWord, self_mem_wordSubshift goldenWord⟩
    let g : (ℕ → Bool) → wordSubshift goldenWord := fun b ↦
      ⟨f b, hfsub ⟨b, rfl⟩⟩
    have hginj : Function.Injective g := by
      intro a b hab
      apply hfinj
      exact congrArg Subtype.val hab
    simpa using Cardinal.mk_le_of_injective hginj

#print axioms isClosed_wordSubshift
#print axioms closure_shift_orbit_eq_wordSubshift
#print axioms golden_wordSubshift_perfect
#print axioms golden_wordSubshift_cardinal_eq_continuum

end

end D5.S1.Words.Complexity.SubshiftTopology
