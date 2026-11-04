/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoUniqueMaximumValues
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree]
   utility: none
   digest: Unique positive Jaco degree values and one infinite realizing family. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
import Mathlib.NumberTheory.Rayleigh

/-! All-order degree fibers, positive Beatty complements, and the complete indexed family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues

open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
open scoped symmDiff

/-- Uniqueness of a positive degree value across graph orders, excluding zero. -/
def UniqueValue (k : ℤ) : Prop :=
  1 ≤ k ∧ ∃ n : ℕ, 2 ≤ n ∧ ((jaco n).maxDegree : ℤ) = k ∧
    ∀ m : ℕ, 2 ≤ m → ((jaco m).maxDegree : ℤ) = k → m = n

/-- The source formula, with the source's positive starting index. -/
noncomputable def sequenceValue (t : ℕ) : ℤ :=
  ⌊(t : ℝ) * Real.goldenRatio ^ 2⌋ - 1

private noncomputable def B (q : ℤ) : ℤ := ⌊(q : ℝ) * Real.goldenRatio⌋
private noncomputable def C (q : ℤ) : ℤ := ⌊(q : ℝ) / Real.goldenRatio⌋

/-- A single explicitly selected order for every sequence index. -/
noncomputable def realizingOrder (t : ℕ) : ℕ :=
  (B ⌊(t : ℝ) * Real.goldenRatio ^ 2⌋ - 1).toNat

private theorem split (q : ℤ) : B q = q + C q := by
  have hp : Real.goldenRatio = 1 + 1 / Real.goldenRatio := by
    rw [one_div, Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have he : (q : ℝ) * Real.goldenRatio = (q : ℝ) / Real.goldenRatio + q := by
    conv_lhs => rw [hp]
    ring
  unfold B C
  rw [he, Int.floor_add_intCast]
  omega

private theorem C_mono : Monotone C := by
  intro a b h
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) Real.goldenRatio_pos.le

private theorem B_step (q : ℤ) : B q + 1 ≤ B (q + 1) := by
  rw [split q, split (q + 1)]
  have := C_mono (show q ≤ q + 1 by omega)
  omega

private theorem B_lower (q : ℤ) (hq : 2 ≤ q) : 3 ≤ B q := by
  apply Int.le_floor.mpr
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hp : (3 : ℝ) < 2 * Real.goldenRatio := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have hn := Real.sqrt_nonneg 5
    rw [Real.goldenRatio]
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hq' Real.goldenRatio_pos.le
  exact hp.le.trans hm

private theorem degree_floor (n : ℕ) (hn : 2 ≤ n) :
    ((jaco n).maxDegree : ℤ) = ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ - 1 := by
  have h := ((D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree.result).1 n hn).1
  have he : 2 * ((n : ℝ) + 2) / (1 + Real.sqrt 5) =
      ((n : ℝ) + 2) / Real.goldenRatio := by
    simp only [Real.goldenRatio, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [he] at h
  have hf : 1 ≤ ⌊((n : ℝ) + 2) / Real.goldenRatio⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    rw [le_div_iff₀ Real.goldenRatio_pos]
    have hp := Real.goldenRatio_lt_two
    norm_num
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [h, Nat.cast_sub hf, Int.natCast_floor_eq_floor (by positivity)]
  simp

private theorem inverse_floor (q : ℤ) (hq : 2 ≤ q) (n : ℕ) :
    ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ = q ↔
      B q - 1 ≤ (n : ℤ) ∧ (n : ℤ) ≤ B (q + 1) - 2 := by
  have hirr := (Real.goldenRatio_irrational.intCast_mul (by omega : q ≠ 0)).ne_int (n + 2)
  rw [Int.floor_eq_iff, le_div_iff₀ Real.goldenRatio_pos,
    div_lt_iff₀ Real.goldenRatio_pos]
  have hlo : B q < (n : ℤ) + 2 ↔ (q : ℝ) * Real.goldenRatio < (n : ℤ) + 2 := by
    simpa only [B, Int.cast_add, Int.cast_natCast, Int.cast_ofNat] using
      (Int.floor_lt (a := (q : ℝ) * Real.goldenRatio) (z := (n : ℤ) + 2))
  have hhi : (n : ℤ) + 2 ≤ B (q + 1) ↔
      (((n : ℤ) + 2 : ℤ) : ℝ) ≤ ((q : ℝ) + 1) * Real.goldenRatio := by
    simpa only [B, Int.cast_add, Int.cast_one] using
      (Int.le_floor (a := ((q + 1 : ℤ) : ℝ) * Real.goldenRatio) (z := (n : ℤ) + 2))
  have hirr2 := (Real.goldenRatio_irrational.intCast_mul (by omega : q + 1 ≠ 0)).ne_int (n + 2)
  push_cast at hirr hirr2 hhi
  constructor
  · rintro ⟨hl, hh⟩
    have hl' : (q : ℝ) * Real.goldenRatio < (n : ℝ) + 2 :=
      lt_of_le_of_ne hl (by intro he; exact hirr he)
    have hh' : (n : ℤ) + 2 ≤ B (q + 1) := hhi.mpr hh.le
    have := hlo.mpr hl'
    omega
  · rintro ⟨hl, hh⟩
    have hl' := hlo.mp (by omega : B q < (n : ℤ) + 2)
    have hh' := hhi.mp (by omega : (n : ℤ) + 2 ≤ B (q + 1))
    exact ⟨hl'.le, lt_of_le_of_ne hh' (by intro he; exact hirr2 he.symm)⟩

private theorem fiber (k : ℤ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    ((jaco n).maxDegree : ℤ) = k ↔
      B (k + 1) - 1 ≤ (n : ℤ) ∧ (n : ℤ) ≤ B (k + 2) - 2 := by
  rw [degree_floor n hn]
  have hi := inverse_floor (k + 1) (by omega) n
  rw [show k + 1 + 1 = k + 2 by ring] at hi
  constructor
  · intro h; exact hi.mp (by omega)
  · intro h; have := hi.mpr h; omega

private theorem unique_iff_jump (k : ℤ) (hk : 1 ≤ k) :
    UniqueValue k ↔ C (k + 2) = C (k + 1) := by
  have hb := B_lower (k + 1) (by omega)
  have hs := B_step (k + 1)
  have hs' : B (k + 1) + 1 ≤ B (k + 2) := by
    simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using hs
  let n := (B (k + 1) - 1).toNat
  have hn : (n : ℤ) = B (k + 1) - 1 := Int.toNat_of_nonneg (by omega)
  have hn2 : 2 ≤ n := by omega
  have hdn : ((jaco n).maxDegree : ℤ) = k := (fiber k hk n hn2).mpr (by omega)
  have he : B (k + 2) = B (k + 1) + 1 ↔ C (k + 2) = C (k + 1) := by
    rw [split (k + 2), split (k + 1)]
    omega
  rw [← he]
  constructor
  · rintro ⟨_, m, hm, hdm, hu⟩
    have hnm := hu n hn2 hdn
    by_contra hne
    have hdnext : ((jaco (n + 1)).maxDegree : ℤ) = k :=
      (fiber k hk (n + 1) (by omega)).mpr (by push_cast; omega)
    have := hu (n + 1) (by omega) hdnext
    omega
  · intro h
    refine ⟨hk, n, hn2, hdn, ?_⟩
    intro m hm hdm
    have := (fiber k hk m hm).mp hdm
    omega

private theorem lower_hit (q : ℤ) (hq : 2 ≤ q) :
    (∃ t : ℤ, 0 < t ∧ beattySeq Real.goldenRatio t = q) ↔ C q < C (q + 1) := by
  have hp := Real.goldenRatio_pos
  constructor
  · rintro ⟨t, ht, he⟩
    have hf := Int.floor_eq_iff.mp he
    change (q : ℝ) ≤ (t : ℝ) * Real.goldenRatio ∧
      (t : ℝ) * Real.goldenRatio < (q : ℝ) + 1 at hf
    have hirr := (Real.goldenRatio_irrational.intCast_mul ht.ne').ne_int q
    have hlow : (q : ℝ) / Real.goldenRatio < t := by
      rw [div_lt_iff₀ hp]
      exact lt_of_le_of_ne hf.1 (by intro h; exact hirr h.symm)
    have hhigh : (t : ℝ) ≤ ((q : ℝ) + 1) / Real.goldenRatio := by
      exact ((le_div_iff₀ hp).mpr hf.2.le)
    have h1 : C q < t := Int.floor_lt.mpr hlow
    have h2 : t ≤ C (q + 1) := Int.le_floor.mpr (by simpa using hhigh)
    omega
  · intro h
    let t := C (q + 1)
    have htpos : 0 < t := by
      have hqr : (0 : ℝ) ≤ q := by exact_mod_cast (by omega : 0 ≤ q)
      have h0 : 0 ≤ C q := Int.floor_nonneg.mpr (by positivity)
      dsimp [t]; omega
    refine ⟨t, htpos, ?_⟩
    apply Int.floor_eq_iff.mpr
    have hl : (q : ℝ) / Real.goldenRatio < t := Int.floor_lt.mp h
    have hh : (t : ℝ) ≤ ((q : ℝ) + 1) / Real.goldenRatio := by
      simpa [t, C] using Int.floor_le (((q + 1 : ℤ) : ℝ) / Real.goldenRatio)
    have hn := (Real.goldenRatio_irrational.intCast_div (by omega : q + 1 ≠ 0)).ne_int t
    have hh' : (t : ℝ) < ((q : ℝ) + 1) / Real.goldenRatio :=
      lt_of_le_of_ne hh (by intro he; exact hn (by simpa using he.symm))
    exact ⟨((div_lt_iff₀ hp).mp hl).le, (lt_div_iff₀ hp).mp hh'⟩

private theorem upper_complement (q : ℤ) (hq : 2 ≤ q) :
    C (q + 1) = C q ↔ ∃ t : ℤ, 0 < t ∧ beattySeq (Real.goldenRatio ^ 2) t = q := by
  have hc : Real.goldenRatio.HolderConjugate (Real.goldenRatio ^ 2) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨Real.one_lt_goldenRatio, ?_⟩
    have hp := Real.goldenRatio_pos.ne'
    have hs := Real.goldenRatio_sq
    field_simp [hp]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have partition := Irrational.beattySeq_symmDiff_beattySeq_pos hc Real.goldenRatio_irrational
  have hmem : q ∈ {beattySeq Real.goldenRatio t | t > 0} ∆
        {beattySeq (Real.goldenRatio ^ 2) t | t > 0} := by
    rw [partition]
    exact (by omega : 0 < q)
  simp only [Set.mem_symmDiff, Set.mem_ofPred_eq] at hmem
  have hm := C_mono (show q ≤ q + 1 by omega)
  have hh := lower_hit q hq
  rcases hmem with ⟨hl, hnu⟩ | ⟨hu, hnl⟩
  · have hj := hh.mp hl
    constructor
    · intro he; omega
    · intro hu; exact (hnu hu).elim
  · constructor
    · intro _; exact hu
    · intro _
      have hn : ¬ C q < C (q + 1) := fun hj => hnl (hh.mpr hj)
      omega

private theorem classification (k : ℤ) (hk : 1 ≤ k) :
    UniqueValue k ↔ ∃ t : ℕ, 1 ≤ t ∧ k = sequenceValue t := by
  rw [unique_iff_jump k hk]
  have h := upper_complement (k + 1) (by omega)
  constructor
  · intro hc
    obtain ⟨t, ht, he⟩ := h.mp (by simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using hc)
    refine ⟨t.toNat, by omega, ?_⟩
    have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
    have hr : (t.toNat : ℝ) = t := by exact_mod_cast htcast
    dsimp [sequenceValue]
    rw [hr]
    dsimp [beattySeq] at he
    omega
  · rintro ⟨t, ht, he⟩
    have : C ((k + 1) + 1) = C (k + 1) := h.mpr ⟨t, by omega, by
      dsimp [beattySeq, sequenceValue] at *
      push_cast
      omega⟩
    simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using this

private theorem sequence_positive (t : ℕ) (ht : 1 ≤ t) : 1 ≤ sequenceValue t := by
  have hf : 2 ≤ ⌊(t : ℝ) * Real.goldenRatio ^ 2⌋ := by
    apply Int.le_floor.mpr
    have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hm := mul_le_mul_of_nonneg_right htr (sq_nonneg Real.goldenRatio)
    have htwo : (2 : ℝ) ≤ Real.goldenRatio ^ 2 := by
      rw [Real.goldenRatio_sq]
      linarith [Real.one_lt_goldenRatio]
    exact htwo.trans (by simpa only [one_mul] using hm)
  dsimp [sequenceValue]
  omega

private theorem realizing (t : ℕ) (ht : 1 ≤ t) :
    2 ≤ realizingOrder t ∧ 1 ≤ sequenceValue t ∧
    ((jaco (realizingOrder t)).maxDegree : ℤ) = sequenceValue t ∧
    ∀ m : ℕ, 1 ≤ m → ((jaco m).maxDegree : ℤ) = sequenceValue t → m = realizingOrder t := by
  have hk := sequence_positive t ht
  have hu := (classification (sequenceValue t) hk).mpr ⟨t, ht, rfl⟩
  have hb := B_lower (sequenceValue t + 1) (by omega)
  have hn : ((realizingOrder t : ℕ) : ℤ) = B (sequenceValue t + 1) - 1 := by
    unfold realizingOrder
    have he : ⌊(t : ℝ) * Real.goldenRatio ^ 2⌋ = sequenceValue t + 1 := by
      simp [sequenceValue]
    rw [he]
    exact Int.toNat_of_nonneg (by omega)
  have hn2 : 2 ≤ realizingOrder t := by omega
  have hs := B_step (sequenceValue t + 1)
  have hs' : B (sequenceValue t + 1) + 1 ≤ B (sequenceValue t + 2) := by
    simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using hs
  have hd : ((jaco (realizingOrder t)).maxDegree : ℤ) = sequenceValue t :=
    (fiber _ hk _ hn2).mpr (by omega)
  refine ⟨hn2, hk, hd, ?_⟩
  intro m hm hdm
  by_cases hm2 : 2 ≤ m
  · obtain ⟨_, n, hn, hdn, huniq⟩ := hu
    exact (huniq m hm2 hdm).trans (huniq _ hn2 hd).symm
  · have hm1 : m = 1 := by omega
    subst m
    have hzero : (jaco 1).maxDegree = 0 := by
      haveI : Subsingleton (Vertex 1) := ⟨by
        intro a b
        apply Subtype.ext
        have ha := Finset.mem_Icc.mp a.2
        have hb := Finset.mem_Icc.mp b.2
        omega⟩
      exact SimpleGraph.maxDegree_of_subsingleton (jaco 1)
    rw [hzero] at hdm
    omega

/-- The complete positive-value classification and one whole infinite indexed
family of the original recursive source graphs, with uniqueness even at order one. -/
theorem result :
    (∀ k : ℤ, 1 ≤ k → (UniqueValue k ↔ ∃ t : ℕ, 1 ≤ t ∧ k = sequenceValue t)) ∧
    (∃ r : ℕ → ℕ, r = realizingOrder ∧ ∀ t : ℕ, 1 ≤ t →
      2 ≤ r t ∧ 1 ≤ sequenceValue t ∧ ((jaco (r t)).maxDegree : ℤ) = sequenceValue t ∧
      ∀ m : ℕ, 1 ≤ m → ((jaco m).maxDegree : ℤ) = sequenceValue t → m = r t) := by
  exact ⟨classification, realizingOrder, rfl, realizing⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoUniqueMaximumValues
