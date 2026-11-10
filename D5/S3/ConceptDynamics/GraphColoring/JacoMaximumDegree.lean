/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty]
   utility: none
   digest: Recursive finite Jaco maximum degrees equal literal same-index Zeckendorf deletion. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
import D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
import D5.S1.Words.Powers.ZeckendorfDeletion

/-! Ordinary maximum degree on the original positive-index recursive graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S1.Words
open D5.S1.Words.Powers
open D5.S1.Words.Powers.ZeckendorfDeletion
open D5.S1.Deficit.ZeckendorfDisplacementReading
open GoldenDesubstitutionZeckendorf

private instance (n : ℕ) : DecidableRel (jaco n).Adj := by
  intro a b
  simp only [jaco, Adj]
  infer_instance

private theorem endpoint_start (i : ℕ) : jacoRight i = goldenSubstStart i := by
  have h := displacement_decode_eq_beatty_floor i
  rw [← golden_subst_start_eq_displacement_decode] at h
  have hfloor : ⌊((i : ℝ) + 1) * Real.goldenRatio⌋₊ = i + 1 + beattyOut i := by
    have hphi : Real.goldenRatio = 1 + 1 / Real.goldenRatio := by
      rw [one_div, Real.inv_goldenRatio]
      linarith [Real.goldenRatio_add_goldenConj]
    have he : ((i : ℝ) + 1) * Real.goldenRatio =
        ((i : ℝ) + 1) / Real.goldenRatio + (i + 1 : ℕ) := by
      conv_lhs => rw [hphi]
      push_cast
      ring
    rw [he, Nat.floor_add_natCast (by positivity)]
    dsimp [beattyOut]
    omega
  rw [← Int.natCast_floor_eq_floor (by positivity), hfloor] at h
  rw [endpoint_eq_beatty]
  exact_mod_cast (by omega : (i : ℤ) + beattyOut i = goldenSubstStart i)

private theorem out_mono : Monotone beattyOut := by
  intro i j hij
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ Real.goldenRatio_pos.le
  exact_mod_cast Nat.add_le_add_right hij 1

/-- The ordinary finite degree, with both incoming and truncated outgoing edges. -/
theorem degree_formula (n : ℕ) (v : Vertex n) :
    (jaco n).degree v = min v.1 (n - beattyOut v.1) := by
  let i := v.1
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp v.2).1
  have hin : i ≤ n := (Finset.mem_Icc.mp v.2).2
  have hb := beatty_bounds i hi1
  let emb : Vertex n ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hlabels : ((jaco n).neighborFinset v).map emb =
      Finset.Ico (beattyOut i) i ∪ Finset.Icc (i + 1) (min n (jacoRight i)) := by
    ext j
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_Icc]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (beattyOut i ≤ w.1 ∧ w.1 < i) ∨
        (i + 1 ≤ w.1 ∧ w.1 ≤ min n (jacoRight i))
      have hw1 := (Finset.mem_Icc.mp w.2).1
      have hwn := (Finset.mem_Icc.mp w.2).2
      change Adj i w.1 at hw
      rcases hw with h | h
      · exact Or.inr ⟨by omega, le_min hwn h.2⟩
      · left
        rw [endpoint_eq_beatty] at h
        exact ⟨(beatty_threshold i w.1).mp h.2, h.1⟩
    · intro hj
      have hj1 : 1 ≤ j := by
        rcases hj with hj | hj <;> omega
      have hjn : j ≤ n := by
        rcases hj with hj | hj
        · omega
        · exact (le_min_iff.mp hj.2).1
      refine ⟨⟨j, Finset.mem_Icc.mpr ⟨hj1, hjn⟩⟩, ?_, rfl⟩
      change Adj i j
      rcases hj with hj | hj
      · right
        refine ⟨hj.2, ?_⟩
        rw [endpoint_eq_beatty]
        exact (beatty_threshold i j).mpr hj.1
      · exact Or.inl ⟨by omega, (le_min_iff.mp hj.2).2⟩
  have hdisj : Disjoint (Finset.Ico (beattyOut i) i)
      (Finset.Icc (i + 1) (min n (jacoRight i))) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have := Finset.mem_Ico.mp hj
    have := Finset.mem_Icc.mp hj'
    omega
  have hcard := congrArg Finset.card hlabels
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree,
    Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.card_Icc,
    endpoint_eq_beatty] at hcard
  change (jaco n).degree v = min i (n - beattyOut i)
  omega

private theorem deletion_floor (n : ℕ) :
    deleteLeast n = beattyOut (n + 1) - 1 := by
  obtain ⟨hlo, hhi⟩ := deletion_block n
  rw [← endpoint_start] at hlo hhi
  rw [endpoint_eq_beatty] at hlo hhi
  have h1 : ¬ n + 1 ≤ deleteLeast n + beattyOut (deleteLeast n) := by omega
  have h2 : n + 1 ≤ (deleteLeast n + 1) + beattyOut (deleteLeast n + 1) := by omega
  rw [beatty_threshold] at h1 h2
  omega

/-- Every positive-order source graph realizes the literal deletion at its
actual sequence index, including the singleton at index one. -/
theorem max_degree_eq_deletion (n : ℕ) (hn : 1 ≤ n) :
    (jaco n).maxDegree = deleteLeast n := by
  by_cases hsingle : n = 1
  · subst n
    haveI : Subsingleton (Vertex 1) := ⟨by
      intro a b
      apply Subtype.ext
      have ha := Finset.mem_Icc.mp a.2
      have hb := Finset.mem_Icc.mp b.2
      omega⟩
    rw [SimpleGraph.maxDegree_of_subsingleton]
    have hd : D5.S0.Conventions.wdigits 1 = [2] := by
      symm
      apply D5.S0.Conventions.wdigits_unique
      · norm_num [List.IsZeckendorfRep]
      · norm_num [Nat.fib]
    simp [deleteLeast, hd]
  · have hn2 : 2 ≤ n := by omega
    let k := deleteLeast n
    obtain ⟨hlo, hhi⟩ := deletion_block n
    rw [← endpoint_start] at hlo hhi
    change jacoRight k ≤ n at hlo
    change n < jacoRight (k + 1) at hhi
    have hk1 : 1 ≤ k := by
      by_contra hk
      have hk0 : k = 0 := by omega
      have htwo : jacoRight 1 = 2 := by decide +kernel
      rw [hk0] at hhi
      change n < jacoRight 1 at hhi
      rw [htwo] at hhi
      omega
    have hkn : k ≤ n := by rw [endpoint_eq_beatty] at hlo; omega
    have hlodeg : (jaco n).degree ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkn⟩⟩ = k := by
      rw [degree_formula]
      rw [endpoint_eq_beatty] at hlo
      simp only
      omega
    apply le_antisymm
    · apply SimpleGraph.maxDegree_le_of_forall_degree_le
      intro v
      rw [degree_formula]
      by_cases hv : v.1 ≤ k
      · exact (min_le_left _ _).trans hv
      · have hm := out_mono (by omega : k + 1 ≤ v.1)
        rw [endpoint_eq_beatty] at hhi
        omega
    · have h := (jaco n).degree_le_maxDegree ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkn⟩⟩
      rw [hlodeg] at h
      exact h

/-- The complete maximum-degree and same-index sequence assertions of Kok's
Conjecture 2.2, with the positive-order family clause retaining its singleton. -/
theorem result :
    (∀ n : ℕ, 2 ≤ n →
      (jaco n).maxDegree = ⌊2 * ((n : ℝ) + 2) / (1 + Real.sqrt 5)⌋₊ - 1 ∧
      (jaco n).maxDegree = deleteLeast n) ∧
    (∀ n : ℕ, 1 ≤ n → (jaco n).maxDegree = deleteLeast n) := by
  refine ⟨?_, max_degree_eq_deletion⟩
  intro n hn
  have hd := max_degree_eq_deletion n (by omega)
  refine ⟨?_, hd⟩
  rw [hd, deletion_floor]
  unfold beattyOut
  have he : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [he, Real.goldenRatio]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

#print axioms degree_formula
#print axioms max_degree_eq_deletion
#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
