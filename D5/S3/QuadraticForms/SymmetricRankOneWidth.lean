/- GID: D5/S3/QuadraticForms/SymmetricRankOneWidth
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SymmetricRankOneWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Width bounds and exact saturation criteria for a rank-one coupling of child blocks. -/

module

public import D5.S3.QuadraticForms.SymmetricRankOneKernel
import all D5.S3.QuadraticForms.SymmetricRankOneKernel
import Mathlib.Data.Finset.Card

/-! The numerical width recurrence for finite families of symmetric child blocks. -/

public section

set_option autoImplicit false

namespace D5.S3.QuadraticForms.SymmetricRankOneKernel

open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)]

/-- The updated nullity is bounded by the node width. At equality the updated kernel has
a nonzero pairing. For width above one, equality forces one nonleaf child, with deficit
one, and resonance of the sum of the child responses. -/
theorem update_block_width (A : ∀ i, F i →ₗ[ℝ] F i) (hA : ∀ i, (A i).IsSymmetric)
    (u : PiLp 2 F) (nonleaves : Finset ι) (w : ι → ℕ) {t : ℝ} (ht : t ≠ 0)
    (hleaf : ∀ i ∉ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = 0)
    (hbound : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) ≤ w i)
    (hsat : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = w i →
      HasNonzeroPairing (A i) (u i)) :
    let W := max 1 (∑ i ∈ nonleaves, w i)
    let B := update (blockDiagonal A) u t
    let k := Module.finrank ℝ (LinearMap.ker B)
    k ≤ W ∧ (k = W → HasNonzeroPairing B u) ∧
      (1 < W → (k = W ↔ ∃ i, nonleaves = {i} ∧
        Module.finrank ℝ (LinearMap.ker (A i)) + 1 = w i ∧
        ∃ g : ι → ℝ, (∀ j, ScalarResponse (A j) (u j) (g j)) ∧
          1 + t * (∑ j, g j) = 0)) := by
  classical
  dsimp only
  let k : ι → ℕ := fun i => Module.finrank ℝ (LinearMap.ker (A i))
  let W := ∑ i ∈ nonleaves, w i
  let K := ∑ i ∈ nonleaves, k i
  let k' := Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u t))
  obtain ⟨hSymm, hsum, hflag, hresponse⟩ := blockDiagonal_states A hA u
  have hK : Module.finrank ℝ (LinearMap.ker (blockDiagonal A)) = K := by
    rw [hsum]
    exact (Finset.sum_subset (Finset.subset_univ nonleaves) fun i _ hi => hleaf i hi).symm
  have hKW : K ≤ W := Finset.sum_le_sum hbound
  have hwidth (hwide : 1 < max 1 W) : 1 < W := by omega
  have hnonempty (hW : 1 < W) : nonleaves.Nonempty := by
    by_contra h
    have hzero : W = 0 := by simp [W, Finset.not_nonempty_iff_eq_empty.mp h]
    omega
  by_cases h : ∃ i, HasNonzeroPairing (A i) (u i)
  · have hloss : k' + 1 = K :=
      (update_of_nonzero_pairing hSymm ht (hflag.mpr h)).1.trans hK
    refine ⟨by omega, ?_, fun _ => ?_⟩
    · intro heq
      change k' = max 1 W at heq
      omega
    · constructor
      · intro heq
        change k' = max 1 W at heq
        omega
      · rintro ⟨_, _, _, g, hg, _⟩
        obtain ⟨i, hi⟩ := h
        exact ((solvable_iff_no_nonzero_pairing (hA i)).mp (hg i).1 hi).elim
  · have hchoose (i : ι) : ∃ g, ScalarResponse (A i) (u i) g := by
      rcases nonzero_pairing_or_unique_scalar (hA i) (e := u i) with hi | ⟨g, hg, _⟩
      · exact (h ⟨i, hi⟩).elim
      · exact ⟨g, hg⟩
    choose g hg using hchoose
    have hdeficit (i) (hi : i ∈ nonleaves) : k i + 1 ≤ w i := by
      have hne : k i ≠ w i := fun heq => h ⟨i, hsat i hi heq⟩
      have hle : k i ≤ w i := hbound i hi
      omega
    have hbudget : K + nonleaves.card ≤ W := calc
      K + nonleaves.card = ∑ i ∈ nonleaves, (k i + 1) := by
        simp [Finset.sum_add_distrib, K]
      _ ≤ W := Finset.sum_le_sum hdeficit
    by_cases hRes : 1 + t * (∑ j, g j) = 0
    · obtain ⟨hgain, hnewflag⟩ := update_of_resonance hSymm (hresponse g hg) hRes
      have hgain' : k' = K + 1 := by simpa only [hK] using hgain
      have hle : k' ≤ max 1 W := by
        by_cases he : nonleaves = ∅
        · have : K = 0 := by simp [K, he]
          omega
        · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
          omega
      refine ⟨hle, fun _ => hnewflag, fun hwide => ?_⟩
      have hW := hwidth hwide
      have hmax : max 1 W = W := by omega
      change k' = max 1 W ↔ _
      constructor
      · intro heq
        have hpos := Finset.card_pos.mpr (hnonempty hW)
        have hone : nonleaves.card = 1 := by omega
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
        have hWi : W = w i := by simp [W, hi]
        have hKi : K = k i := by simp [K, hi]
        refine ⟨i, hi, ?_, g, hg, hRes⟩
        change k i + 1 = w i
        omega
      · rintro ⟨i, hi, hki, _, _, _⟩
        have hWi : W = w i := by simp [W, hi]
        have hKi : K = k i := by simp [K, hi]
        change k i + 1 = w i at hki
        omega
    · have hsame : k' = K := by
        dsimp [k']
        rw [(update_of_nonresonance hSymm (hresponse g hg) hRes).1, hK]
      have hlt : k' < max 1 W := by
        by_cases he : nonleaves = ∅
        · have : K = 0 := by simp [K, he]
          omega
        · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
          omega
      refine ⟨hlt.le, fun heq => (hlt.ne heq).elim, fun _ => ?_⟩
      constructor
      · exact fun heq => (hlt.ne heq).elim
      · rintro ⟨_, _, _, g', hg', hRes'⟩
        have heq : g' = g := by
          funext i
          obtain ⟨y, hy⟩ := (hg i).1
          exact ((hg' i).2 y hy).symm.trans ((hg i).2 y hy)
        exact (hRes (heq ▸ hRes')).elim

/-- At a width-greater-than-one root with coupling one, the leaf responses enter the
equality criterion only through the number of leaf children. -/
theorem update_block_root_iff [DecidableEq ι]
    (A : ∀ i, F i →ₗ[ℝ] F i) (hA : ∀ i, (A i).IsSymmetric)
    (u : PiLp 2 F) (nonleaves : Finset ι) (w : ι → ℕ) (x : ℝ)
    (hchildren : 2 ≤ Fintype.card ι) (hwide : 1 < max 1 (∑ i ∈ nonleaves, w i))
    (hleaf : ∀ i ∉ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = 0 ∧
      ScalarResponse (A i) (u i) (-1 / (x + 1)))
    (hbound : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) ≤ w i)
    (hsat : ∀ i ∈ nonleaves, Module.finrank ℝ (LinearMap.ker (A i)) = w i →
      HasNonzeroPairing (A i) (u i)) :
    let ℓ := (Finset.univ \ nonleaves).card
    Module.finrank ℝ (LinearMap.ker (update (blockDiagonal A) u 1)) =
      max 1 (∑ i ∈ nonleaves, w i) ↔
      ∃ i, nonleaves = {i} ∧ 0 < ℓ ∧
        Module.finrank ℝ (LinearMap.ker (A i)) + 1 = w i ∧
        ∃ g, ScalarResponse (A i) (u i) g ∧ 1 + g - (ℓ : ℝ) / (x + 1) = 0 := by
  dsimp only
  have hcriterion := (update_block_width A hA u nonleaves w one_ne_zero
    (fun i hi => (hleaf i hi).1) hbound hsat).2.2 hwide
  have hsum {i} (hi : nonleaves = {i}) (g : ι → ℝ)
      (hg : ∀ j ∉ nonleaves, g j = -1 / (x + 1)) :
      ∑ j, g j = g i - ((Finset.univ \ nonleaves).card : ℝ) / (x + 1) := by
    have hsplit := Finset.sum_sdiff (f := g) (Finset.subset_univ nonleaves)
    rw [show ∑ j ∈ nonleaves, g j = g i by simp [hi]] at hsplit
    rw [← hsplit, Finset.sum_congr rfl (fun j hj => hg j (Finset.mem_sdiff.mp hj).2),
      Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    ring
  constructor
  · intro hk
    obtain ⟨i, hi, hki, g, hg, hRes⟩ := hcriterion.mp hk
    have hleafcount : 0 < (Finset.univ \ nonleaves).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ nonleaves), hi,
        Finset.card_singleton, Finset.card_univ]
      omega
    have hleafg (j) (hj : j ∉ nonleaves) : g j = -1 / (x + 1) := by
      obtain ⟨y, hy⟩ := (hg j).1
      exact ((hg j).2 y hy).symm.trans ((hleaf j hj).2.2 y hy)
    refine ⟨i, hi, hleafcount, hki, g i, hg i, ?_⟩
    rw [hsum hi g hleafg, one_mul] at hRes
    linarith
  · rintro ⟨i, hi, _, hki, g, hg, hRes⟩
    let responses (j : ι) := if j = i then g else -1 / (x + 1)
    have hleafg (j) (hj : j ∉ nonleaves) : responses j = -1 / (x + 1) := by
      have hne : j ≠ i := by simpa [hi] using hj
      simp [responses, hne]
    refine hcriterion.mpr ⟨i, hi, hki, responses, ?_, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j
        simpa [responses] using hg
      · have hj : j ∉ nonleaves := by simpa [hi] using he
        rw [hleafg j hj]
        exact (hleaf j hj).2
    · rw [hsum hi responses hleafg, one_mul]
      simp only [responses, ite_eq_left rfl]
      linarith

end D5.S3.QuadraticForms.SymmetricRankOneKernel
