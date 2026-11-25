/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeRadialSmallKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel]
   utility: none
   digest: A radial small binary cube kernel word is an open shell. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSwapConjugation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

/-! In the no-split branch, affine conjugation gives a radial word. Four
binary adjacency equations and the sizes of the Hamming layers determine
every nonzero radial kernel word of weight at most twelve on `Q 8`. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeRadialSmallKernel

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip flip_apply_same)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open BinaryCubeSwapConjugation
  (translate translate_involutive exists_translation_hamming_layer_constant)

/-- Coordinates at which a cube vertex equals true. -/
def trueCoords {n : ℕ} (x : Q n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

/-- Hamming weight of a vertex relative to the all-false vertex. -/
def hammingWeight {n : ℕ} (x : Q n) : ℕ := (trueCoords x).card

private def wordSupport {n : ℕ} (f : Q n → ZMod 2) : Finset (Q n) :=
  Finset.univ.filter fun x => f x ≠ 0

/-- Number of nonzero entries of a binary cube word. -/
def supportWeight {n : ℕ} (f : Q n → ZMod 2) : ℕ := (wordSupport f).card

private theorem mem_wordSupport {n : ℕ} {f : Q n → ZMod 2} {x : Q n} :
    x ∈ wordSupport f ↔ f x ≠ 0 := by simp [wordSupport]

private theorem hammingWeight_le {n : ℕ} (x : Q n) : hammingWeight x ≤ n := by
  simpa [hammingWeight, trueCoords] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i = true)

private theorem hammingWeight_flip_true {n : ℕ} (x : Q n) (i : Fin n) (hi : x i = true) :
    hammingWeight (flip x i) = hammingWeight x - 1 := by
  have hcoords : trueCoords (flip x i) = (trueCoords x).erase i := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [trueCoords, hi]
    · have hflip : flip x i j = x j := by
        simp [BalancedCriticalSpectrum.flip, Function.update_of_ne, hj]
      simp [trueCoords, hflip, hj]
  have him : i ∈ trueCoords x := by simp [trueCoords, hi]
  simp only [hammingWeight, hcoords, Finset.card_erase_of_mem him]

private theorem hammingWeight_flip_false {n : ℕ} (x : Q n) (i : Fin n) (hi : x i = false) :
    hammingWeight (flip x i) = hammingWeight x + 1 := by
  have hcoords : trueCoords (flip x i) = insert i (trueCoords x) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [trueCoords, hi]
    · have hflip : flip x i j = x j := by
        simp [BalancedCriticalSpectrum.flip, Function.update_of_ne, hj]
      simp [trueCoords, hflip, hj]
  have him : i ∉ trueCoords x := by simp [trueCoords, hi]
  simp only [hammingWeight, hcoords, Finset.card_insert_of_notMem him]

/-- Coordinates at which a cube vertex equals true. -/
def trueCoordsEquiv (n : ℕ) : Q n ≃ Finset (Fin n) where
  toFun := trueCoords
  invFun s i := decide (i ∈ s)
  left_inv x := by
    funext i
    cases h : x i <;> simp [trueCoords, h]
  right_inv s := by
    ext i
    simp [trueCoords]

private def layer {n : ℕ} (k : ℕ) : Finset (Q n) :=
  Finset.univ.filter fun x => hammingWeight x = k

private theorem mem_layer {n k : ℕ} {x : Q n} :
    x ∈ layer k ↔ hammingWeight x = k := by simp [layer]

private theorem layer_card {n : ℕ} (k : ℕ) : (layer (n := n) k).card = n.choose k := by
  calc
    (layer (n := n) k).card =
        ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
      apply Finset.card_equiv (trueCoordsEquiv n)
      intro x
      rw [mem_layer, Finset.mem_powersetCard]
      simp [hammingWeight, trueCoordsEquiv]
    _ = n.choose k := by simp

private theorem exists_vertex_of_weight {n k : ℕ} (hk : k ≤ n) :
    ∃ x : Q n, hammingWeight x = k := by
  have hc : 0 < (layer (n := n) k).card := by
    rw [layer_card]
    exact Nat.choose_pos hk
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hc
  exact ⟨x, mem_layer.mp hx⟩

private theorem exists_profile {f : Q 8 → ZMod 2}
    (hrad : ∀ x y : Q 8, hammingWeight x = hammingWeight y → f x = f y) :
    ∃ a : ℕ → ZMod 2, ∀ x : Q 8, f x = a (hammingWeight x) := by
  classical
  refine ⟨fun k => if hk : k ≤ 8 then f (Classical.choose (exists_vertex_of_weight hk)) else 0, ?_⟩
  intro x
  have hx := hammingWeight_le x
  simp only [dite_eq_left hx]
  exact hrad x _ (Classical.choose_spec (exists_vertex_of_weight hx)).symm

private theorem adjacency_radial {n : ℕ} {f : Q n → ZMod 2} {a : ℕ → ZMod 2}
    (hprofile : ∀ x : Q n, f x = a (hammingWeight x)) (x : Q n) :
    adjacency f x = (hammingWeight x : ZMod 2) * a (hammingWeight x - 1) +
      ((n - hammingWeight x : ℕ) : ZMod 2) * a (hammingWeight x + 1) := by
  have hcard : ((Finset.univ : Finset (Fin n)).filter fun i => x i ≠ true).card =
      n - hammingWeight x := by
    have hsum : hammingWeight x +
        ((Finset.univ : Finset (Fin n)).filter fun i => x i ≠ true).card = n := by
      simpa [hammingWeight, trueCoords] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
          (fun i => x i = true))
    omega
  calc
    adjacency f x = ∑ i : Fin n, if x i = true then a (hammingWeight x - 1)
        else a (hammingWeight x + 1) := by
      unfold adjacency
      apply Finset.sum_congr rfl
      intro i _
      rw [hprofile]
      cases hi : x i with
      | false => simp [hammingWeight_flip_false x i hi]
      | true => simp [hammingWeight_flip_true x i hi]
    _ = _ := by
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hcard,
        hammingWeight, trueCoords]

/-- The kernel equations at radii `1, 3, 5, 7` link the five even layers. -/
theorem radial_kernel_even_profile {f : Q 8 → ZMod 2} {a : ℕ → ZMod 2}
    (hprofile : ∀ x : Q 8, f x = a (hammingWeight x)) (hf : adjacency f = 0) :
    a 0 = a 2 ∧ a 2 = a 4 ∧ a 4 = a 6 ∧ a 6 = a 8 := by
  have hchar : ∀ u v : ZMod 2, u + v = 0 → u = v := by decide
  have hstep (k : ℕ) (hk : k ≤ 8) (hdown : (k : ZMod 2) = 1)
      (hup : ((8 - k : ℕ) : ZMod 2) = 1) : a (k - 1) = a (k + 1) := by
    obtain ⟨x, hx⟩ := exists_vertex_of_weight hk
    have he : adjacency f x = 0 := congrFun hf x
    rw [adjacency_radial hprofile x, hx, hdown, hup, one_mul, one_mul] at he
    exact hchar _ _ he
  exact ⟨hstep 1 (by decide) (by decide) (by decide),
    hstep 3 (by decide) (by decide) (by decide),
    hstep 5 (by decide) (by decide) (by decide),
    hstep 7 (by decide) (by decide) (by decide)⟩

/-- A nonzero radial kernel word of weight at most twelve has exactly one
active layer, of radius `1` or `7`, and has weight eight. -/
theorem radial_small_kernel_one_shell {f : Q 8 → ZMod 2}
    (hrad : ∀ x y : Q 8, hammingWeight x = hammingWeight y → f x = f y)
    (hf : adjacency f = 0) (hwpos : 0 < supportWeight f) (hw : supportWeight f ≤ 12) :
    ∃ k : ℕ, (k = 1 ∨ k = 7) ∧ (∀ x : Q 8, f x ≠ 0 ↔ hammingWeight x = k) ∧
      supportWeight f = 8 := by
  obtain ⟨a, hprofile⟩ := exists_profile hrad
  obtain ⟨h02, h24, h46, h68⟩ := radial_kernel_even_profile hprofile hf
  have hsubset {k : ℕ} (hk : a k ≠ 0) : layer k ⊆ wordSupport f := by
    intro x hx
    apply mem_wordSupport.mpr
    rw [hprofile x, mem_layer.mp hx]
    exact hk
  have hlarge (k : ℕ) (hk : 12 < Nat.choose 8 k) : a k = 0 := by
    by_contra h
    have hle : Nat.choose 8 k ≤ supportWeight f := by
      rw [← layer_card (n := 8) k]
      exact Finset.card_le_card (hsubset h)
    omega
  have h2 := hlarge 2 (by decide)
  have h3 := hlarge 3 (by decide)
  have h5 := hlarge 5 (by decide)
  have h0 := h02.trans h2
  have h4 := h24.symm.trans h2
  have h6 := h46.symm.trans h4
  have h8 := h68.symm.trans h6
  have hallowed {k : ℕ} (hk : k ≤ 8) (ha : a k ≠ 0) : k = 1 ∨ k = 7 := by
    by_cases h1 : k = 1
    · exact Or.inl h1
    by_cases h7 : k = 7
    · exact Or.inr h7
    exfalso
    have hcases : k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 8 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha h0
    · exact ha h2
    · exact ha h3
    · exact ha h4
    · exact ha h5
    · exact ha h6
    · exact ha h8
  have hnotBoth : ¬ (a 1 ≠ 0 ∧ a 7 ≠ 0) := by
    rintro ⟨h1, h7⟩
    have hd : Disjoint (layer (n := 8) 1) (layer (n := 8) 7) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx7
      have h1x := mem_layer.mp hx1
      have h7x := mem_layer.mp hx7
      omega
    have hb : (layer (n := 8) 1 ∪ layer 7).card ≤ supportWeight f :=
      Finset.card_le_card (Finset.union_subset (hsubset h1) (hsubset h7))
    simp only [Finset.card_union_of_disjoint hd, layer_card] at hb
    have h16 : Nat.choose 8 1 + Nat.choose 8 7 = 16 := by decide
    omega
  have hunique {i j : ℕ} (hi : i = 1 ∨ i = 7) (hj : j = 1 ∨ j = 7)
      (hai : a i ≠ 0) (haj : a j ≠ 0) : i = j := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact (hnotBoth ⟨hai, haj⟩).elim
    · exact (hnotBoth ⟨haj, hai⟩).elim
    · rfl
  change 0 < (wordSupport f).card at hwpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hwpos
  have ha : a (hammingWeight x) ≠ 0 := by
    simpa only [hprofile x] using (mem_wordSupport.mp hx)
  have hxRadius := hallowed (hammingWeight_le x) ha
  have hs (y : Q 8) : f y ≠ 0 ↔ hammingWeight y = hammingWeight x := by
    rw [hprofile y]
    constructor
    · intro hy
      exact hunique (hallowed (hammingWeight_le y) hy) hxRadius hy ha
    · intro hy
      simpa only [hy] using ha
  refine ⟨hammingWeight x, hxRadius, hs, ?_⟩
  have hset : wordSupport f = layer (hammingWeight x) := by
    ext y
    exact (mem_wordSupport.trans (hs y)).trans mem_layer.symm
  change (wordSupport f).card = 8
  rw [hset, layer_card]
  rcases hxRadius with h | h <;> rw [h] <;> decide

private theorem translate_flip {n : ℕ} (t x : Q n) (i : Fin n) :
    translate t (flip x i) = flip (translate t x) i := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [flip_apply_same, translate]
    cases t i <;> cases x i <;> rfl
  · simp [translate, BalancedCriticalSpectrum.flip, hj]

private theorem adjacency_translate_zero {n : ℕ} (t : Q n) {f : Q n → ZMod 2}
    (hf : adjacency f = 0) : adjacency (fun x => f (translate t x)) = 0 := by
  funext x
  calc
    adjacency (fun y => f (translate t y)) x = adjacency f (translate t x) := by
      simp only [adjacency, translate_flip]
    _ = 0 := congrFun hf (translate t x)

private theorem supportWeight_translate {n : ℕ} (t : Q n) (f : Q n → ZMod 2) :
    supportWeight (fun x => f (translate t x)) = supportWeight f := by
  unfold supportWeight
  apply Finset.card_equiv ((translate_involutive t).toPerm (translate t))
  intro x
  simp only [mem_wordSupport, Function.Involutive.coe_toPerm]

/-- The no-split star hypothesis forces the support to be a single
eight-point shell after the translation supplied by the group action. -/
theorem no_split_small_kernel_one_shell (r : Fin 8) (f : Q 8 → ZMod 2)
    (hnosplit : ∀ j : Fin 8, j ≠ r →
      (∀ x : Q 8, x r ≠ x j → f (flip (flip x r) j) = f x) ∨
      (∀ x : Q 8, x r = x j → f (flip (flip x r) j) = f x))
    (hf : adjacency f = 0) (hwpos : 0 < supportWeight f) (hw : supportWeight f ≤ 12) :
    ∃ t : Q 8, t r = false ∧ ∃ k : ℕ, (k = 1 ∨ k = 7) ∧
      (∀ x : Q 8, f (translate t x) ≠ 0 ↔ hammingWeight x = k) ∧ supportWeight f = 8 := by
  obtain ⟨t, ht, hrad⟩ := exists_translation_hamming_layer_constant r f hnosplit
  have hweight := supportWeight_translate t f
  have hrad' (x y : Q 8) (hxy : hammingWeight x = hammingWeight y) :
      f (translate t x) = f (translate t y) := hrad x y hxy
  obtain ⟨k, hk, hs, h8⟩ := radial_small_kernel_one_shell hrad'
    (adjacency_translate_zero t hf) (by rwa [hweight]) (by rwa [hweight])
  exact ⟨t, ht, k, hk, hs, hweight.symm.trans h8⟩

#print axioms radial_kernel_even_profile
#print axioms no_split_small_kernel_one_shell

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeRadialSmallKernel
