/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeAnalyticWeightTwelve
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeAnalyticWeightTwelve
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeRadialSmallKernel]
   utility: none
   digest: Classify the nonzero binary cube adjacency kernel words of weight at most twelve. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeRadialSmallKernel
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSplitReconstruction

/-! Below weight twelve, the radial alternative gives one shell. At weight
twelve a coordinate swap moves a sharp split to the first two coordinates,
where the fixed-split theorem reconstructs both centers. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
namespace BinaryCubeAnalyticWeightTwelve
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_apply_same flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open BinaryCubeKernelSupport (binarySites)
open BinaryCubeRadialSmallKernel (hammingWeight supportWeight no_split_small_kernel_one_shell)
open BinaryCubeSharpSplit (twoSection)
open BinaryCubeSplitReconstruction (delta sharp_split_two_shells)
open BinaryCubeSwapConjugation (translate translate_involutive)
open BinaryCubeRadialSmallKernel (trueCoords)
open BinaryCubeSplitReconstruction (adjacency_delta neighborhood)

private abbrev permute {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Q n) :=
  Equiv.arrowCongr σ (Equiv.refl Bool)

private theorem permute_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Q n) (i : Fin n) :
    permute σ x i = x (σ.symm i) := rfl

private theorem permute_flip {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Q n) (i : Fin n) :
    permute σ (flip x i) = flip (permute σ x) (σ i) := by
  funext k
  rw [permute_apply]
  by_cases hk : k = σ i
  · subst k
    simp only [Equiv.symm_apply_apply, flip_apply_same, permute_apply]
  · have hki : σ.symm k ≠ i := by
      intro h
      apply hk
      simpa only [Equiv.apply_symm_apply] using congrArg σ h
    simp only [BalancedCriticalSpectrum.flip, Function.update_of_ne hki,
      Function.update_of_ne hk, permute_apply]

private theorem adjacency_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Q n → ZMod 2) (x : Q n) :
    adjacency (fun y => f (permute σ y)) x = adjacency f (permute σ x) := by
  calc
    adjacency (fun y => f (permute σ y)) x =
        ∑ i : Fin n, f (flip (permute σ x) (σ i)) := by
      simp only [adjacency, permute_flip]
    _ = adjacency f (permute σ x) :=
      Equiv.sum_comp σ (fun i => f (flip (permute σ x) i))

private theorem binarySites_card_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Q n → ZMod 2) :
    (binarySites (fun x => f (permute σ x))).card = (binarySites f).card := by
  unfold binarySites
  calc
    _ = ∑ x : Q n, if f (permute σ x) ≠ 0 then (1 : ℕ) else 0 :=
      (Finset.sum_boole (R := ℕ) (fun x : Q n => f (permute σ x) ≠ 0) Finset.univ).symm
    _ = ∑ x : Q n, if f x ≠ 0 then (1 : ℕ) else 0 :=
      Equiv.sum_comp (permute σ) (fun x => if f x ≠ 0 then (1 : ℕ) else 0)
    _ = _ := Finset.sum_boole (R := ℕ) (fun x : Q n => f x ≠ 0) Finset.univ

private theorem double_flip_front (a b : Bool) (x : Q 6) :
    flip (flip (Fin.cons a (Fin.cons b x)) 0) 1 = Fin.cons (!a) (Fin.cons (!b) x) := by
  change flip (flip (Fin.cons a (Fin.cons b x)) 0) (0 : Fin 7).succ = _
  simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
    Fin.cons_succ, ← Fin.cons_update]

private theorem invariant_of_opposite_sum_zero {f : Q 8 → ZMod 2} {a b : Bool}
    (h : twoSection f a b + twoSection f (!a) (!b) = 0) (z : Q 8)
    (hz : (z 0 = a ∧ z 1 = b) ∨ (z 0 = !a ∧ z 1 = !b)) :
    f (flip (flip z 0) 1) = f z := by
  let x : Q 6 := Fin.tail (Fin.tail z)
  have hpoint : f (Fin.cons a (Fin.cons b x)) +
      f (Fin.cons (!a) (Fin.cons (!b) x)) = 0 := congrFun h x
  have he := (show ∀ u v : ZMod 2, u + v = 0 → v = u from by decide) _ _ hpoint
  have hcons : Fin.cons (z 0) (Fin.cons (z 1) x) = z := by
    change Fin.cons (z 0) (Fin.cons (Fin.tail z 0) (Fin.tail (Fin.tail z))) = z
    simp only [Fin.cons_self_tail]
  rcases hz with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1] at hcons
    rw [← hcons, double_flip_front]
    exact he
  · rw [h0, h1] at hcons
    rw [← hcons, double_flip_front]
    simpa only [Bool.not_not] using he.symm

private abbrev NoSplitAtZero (f : Q 8 → ZMod 2) : Prop :=
  ∀ j : Fin 8, j ≠ 0 →
    (∀ x : Q 8, x 0 ≠ x j → f (flip (flip x 0) j) = f x) ∨
    (∀ x : Q 8, x 0 = x j → f (flip (flip x 0) j) = f x)

private theorem split_two_shells (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hw : (binarySites f).card ≤ 12) (hsplit : ¬ NoSplitAtZero f) :
    (binarySites f).card = 12 ∧
    ∃ x y : Q 8, (∃ i j : Fin 8, i ≠ j ∧ y = flip (flip x i) j) ∧
      f = adjacency (delta x + delta y) := by
  classical
  obtain ⟨j, hj⟩ := Classical.not_forall.mp hsplit
  have hj0 : j ≠ 0 := fun h => hj (fun hj' => (hj' h).elim)
  let σ : Equiv.Perm (Fin 8) := Equiv.swap 1 j
  let g : Q 8 → ZMod 2 := fun x => f (permute σ x)
  have hσ0 : σ 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 8) ≠ 1) hj0.symm
  have hσ1 : σ 1 = j := Equiv.swap_apply_left 1 j
  have hgker : adjacency g = 0 := by
    funext x
    calc
      adjacency g x = adjacency f (permute σ x) := adjacency_permute σ f x
      _ = 0 := congrFun hf (permute σ x)
  have hcard : (binarySites g).card = (binarySites f).card := binarySites_card_permute σ f
  have hwg : (binarySites g).card ≤ 12 := hcard.trans_le hw
  have transport_invariance (R : Bool → Bool → Prop)
      (h : ∀ z : Q 8, R (z 0) (z 1) → g (flip (flip z 0) 1) = g z) :
      ∀ x : Q 8, R (x 0) (x j) → f (flip (flip x 0) j) = f x := by
    intro x hx
    obtain ⟨z, rfl⟩ := (permute σ).surjective x
    have hcoord (i : Fin 8) : permute σ z (σ i) = z i := by
      simp only [permute_apply, Equiv.symm_apply_apply]
    have h0 : permute σ z 0 = z 0 := by simpa only [hσ0] using hcoord 0
    have h1 : permute σ z j = z 1 := by simpa only [hσ1] using hcoord 1
    rw [h0, h1] at hx
    simpa only [g, permute_flip, hσ0, hσ1] using h z hx
  have heven : twoSection g false false + twoSection g true true ≠ 0 := by
    intro hzero
    apply hj
    intro _
    refine Or.inr (transport_invariance (· = ·) ?_)
    intro z hz
    apply invariant_of_opposite_sum_zero (a := false) (b := false) hzero z
    cases h0 : z 0 <;> cases h1 : z 1 <;> simp [h0, h1] at hz ⊢
  have hodd : twoSection g true false + twoSection g false true ≠ 0 := by
    intro hzero
    apply hj
    intro _
    refine Or.inl (transport_invariance (· ≠ ·) ?_)
    intro z hz
    apply invariant_of_opposite_sum_zero (a := true) (b := false) hzero z
    cases h0 : z 0 <;> cases h1 : z 1 <;> simp [h0, h1] at hz ⊢
  obtain ⟨hwg', x, y, ⟨i, k, hik, hy⟩, hg⟩ :=
    sharp_split_two_shells g hgker hwg heven hodd
  refine ⟨hcard.symm.trans hwg', permute σ x, permute σ y,
    ⟨σ i, σ k, fun h => hik (σ.injective h), ?_⟩, ?_⟩
  · simp only [hy, permute_flip]
  · have hpull :
        (fun w => (delta (permute σ x) + delta (permute σ y)) (permute σ w)) =
          delta x + delta y := by
      funext w
      simp only [Pi.add_apply, delta, Equiv.apply_eq_iff_eq]
    funext z
    obtain ⟨w, rfl⟩ := (permute σ).surjective z
    calc
      f (permute σ w) = adjacency (delta x + delta y) w := congrFun hg w
      _ = adjacency (delta (permute σ x) + delta (permute σ y)) (permute σ w) := by
        rw [← adjacency_permute σ _ w, hpull]

/-- Every weight-twelve binary adjacency kernel word on the eight-cube is
the adjacency of two singleton words whose centers differ in exactly two coordinates. -/
theorem weight_twelve_two_shells (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hw : (binarySites f).card = 12) :
    ∃ x y : Q 8, (∃ i j : Fin 8, i ≠ j ∧ y = flip (flip x i) j) ∧
      f = adjacency (delta x + delta y) := by
  classical
  have hweight : supportWeight f = 12 := hw
  have hsplit : ¬ NoSplitAtZero f := by
    intro hnosplit
    have hpos : 0 < supportWeight f := by rw [hweight]; decide
    obtain ⟨_, _, _, _, _, h8⟩ :=
      no_split_small_kernel_one_shell 0 f hnosplit hf hpos hweight.le
    exact (by decide : (12 : ℕ) ≠ 8) (hweight.symm.trans h8)
  exact (split_two_shells f hf hw.le hsplit).2

private theorem weight_one_iff_mem_neighborhood {n : ℕ} (p x : Q n) :
    hammingWeight (translate p x) = 1 ↔ x ∈ neighborhood p := by
  classical
  have hcoords : trueCoords (translate p x) = Finset.univ.filter (fun i => p i ≠ x i) := by
    ext i
    simp only [trueCoords, Finset.mem_filter, Finset.mem_univ, true_and]
    change Bool.xor (p i) (x i) = true ↔ p i ≠ x i
    cases p i <;> cases x i <;> decide
  rw [hammingWeight, hcoords]
  change (hypercube n).Adj p x ↔ x ∈ neighborhood p
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := adjacent_exists_flip hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact flip_adj p i

private theorem weight_translate_antipode {n : ℕ} (t x : Q n) :
    hammingWeight (translate t x) + hammingWeight (translate (fun i => !t i) x) = n := by
  classical
  have hcoords : trueCoords (translate (fun i => !t i) x) =
      Finset.univ.filter (fun i => ¬ (translate t x i = true)) := by
    ext i
    simp only [trueCoords, Finset.mem_filter, Finset.mem_univ, true_and]
    change Bool.xor (!t i) (x i) = true ↔ ¬ (Bool.xor (t i) (x i) = true)
    cases t i <;> cases x i <;> decide
  unfold hammingWeight
  rw [hcoords]
  simpa only [trueCoords, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => translate t x i = true))

private theorem eq_adjacency_delta_of_weight_one {n : ℕ} {f : Q n → ZMod 2} (p : Q n)
    (hs : ∀ x, f x ≠ 0 ↔ hammingWeight (translate p x) = 1) :
    f = adjacency (delta p) := by
  classical
  funext x
  have hmem := (hs x).trans (weight_one_iff_mem_neighborhood p x)
  rw [adjacency_delta]
  by_cases hx : x ∈ neighborhood p
  · simp only [ite_eq_left hx]
    exact (show ∀ v : ZMod 2, v ≠ 0 → v = 1 from by decide) _ (hmem.mpr hx)
  · simp only [ite_eq_right hx]
    exact not_ne_iff.mp (fun hn => hx (hmem.mp hn))

/-- A nonzero binary adjacency kernel word of weight below twelve on the
eight-cube has weight eight and is the adjacency of a singleton word. -/
theorem weight_less_twelve_one_shell (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hwpos : 0 < (binarySites f).card) (hw : (binarySites f).card < 12) :
    (binarySites f).card = 8 ∧ ∃ p : Q 8, f = adjacency (delta p) := by
  classical
  have hnosplit : NoSplitAtZero f := by
    by_contra hsplit
    exact hw.ne (split_two_shells f hf hw.le hsplit).1
  obtain ⟨t, _, k, hk, hs, hweight⟩ :=
    no_split_small_kernel_one_shell 0 f hnosplit hf hwpos hw.le
  refine ⟨hweight, ?_⟩
  have hsupport (x : Q 8) : f x ≠ 0 ↔ hammingWeight (translate t x) = k := by
    simpa only [translate_involutive t x] using hs (translate t x)
  rcases hk with rfl | rfl
  · exact ⟨t, eq_adjacency_delta_of_weight_one t hsupport⟩
  · refine ⟨fun i => !t i, eq_adjacency_delta_of_weight_one _ ?_⟩
    intro x
    rw [hsupport x]
    have hsum := weight_translate_antipode t x
    omega

#print axioms weight_twelve_two_shells
#print axioms weight_less_twelve_one_shell

end BinaryCubeAnalyticWeightTwelve
end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves
