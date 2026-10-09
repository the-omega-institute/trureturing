/- GID: D5/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/LongRangeSwap/LeeReductionInvertibility
   mirror-E: none(waiver:abstract-matrix-family)
   anchors: []
   utility: none
   digest: All Lee reduction operators are units on the closed parameter cube. -/

/-
proof_shape: result: content.
escape_witness: extend constructs a harmonic chain with prescribed last vector;
  pivots_isUnit uses it on result's live path.
Private helpers extend and pivots_isUnit: content.
Private helpers weighted_exit, decode_encode, decode_swap, lifted_interval,
  lifted_harmonic, harmonic_chain_zero and pivot_eq_A: bind-only, with live consumers.
admission_basis: open-problem-resolution (#14343; Proved)
Direct frozen dependencies: none on the baseline.
Intra-delivery dependencies: LeeCollisionExit.Path.exits and
  FiniteBinaryDirichletMaximum.maximum_zero_of_two_successor_exit.
Information-escape registration is paused under CLAUDE.md §3.9.
Utility: none; all parameters are arbitrary, with no finite-instance certificate or enumeration.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import D5.S3.StatisticalMechanics.RandomWalks.FiniteBinaryDirichletMaximum
import D5.S3.StatisticalMechanics.LongRangeSwap.LeeCollisionExit

namespace D5.S3.StatisticalMechanics.LongRangeSwap.LeeReductionInvertibility
open Matrix
open D5.S3.StatisticalMechanics.RandomWalks.FiniteBinaryDirichletMaximum D5.S3.StatisticalMechanics.LongRangeSwap.LeeCollisionExit
noncomputable section
variable {N n : ℕ}

def A {N n : ℕ} (μ : Fin N → ℝ) (j : ℕ) : ℕ → Matrix (Fin n → Fin N) (Fin n → Fin N) ℝ
  | 0 => 1
  | k + 1 => 1 - calB μ j (k + 2) * (A μ j k)⁻¹ * calBprime μ j (k + 1)

def claim : Prop := ∀ (N n j k : ℕ), 1 ≤ N → 2 ≤ n → 1 ≤ j →
  j + k + 1 ≤ n → ∀ μ : Fin N → ℝ, (∀ a, 0 ≤ μ a ∧ μ a ≤ 1) →
    IsUnit (A (n := n) μ j k)
private theorem weighted_exit (μ : Fin N → ℝ) (m : ℕ) (s : ℤ × (ℤ → Fin N)) :
    ∃ t, ¬Path.interior m t ∧ Relation.ReflTransGen
      (fun a b => Path.interior m a ∧
        ((0 < B μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ Path.leftState a = b) ∨
         (0 < Bprime μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ Path.rightState a = b))) s t := by
  obtain ⟨l, _, ht, _, _, hp⟩ := Path.exits μ m s
  exact ⟨_, ht, hp⟩

private def decode (j : ℕ) (w : ℤ → Fin N) : (Fin n → Fin N) :=
  fun r => w ((r.val : ℤ)-((j:ℤ)-1))

private def encode (hN : 1 ≤ N) (j : ℕ) (w : (Fin n → Fin N)) : ℤ → Fin N := fun x =>
  if h : 0 ≤ x + ((j:ℤ)-1) ∧ x + ((j:ℤ)-1) < n then
    w ⟨(x + ((j:ℤ)-1)).toNat, by omega⟩ else ⟨0, by omega⟩

private theorem decode_encode (hN : 1 ≤ N) (j : ℕ) (w : (Fin n → Fin N)) : decode j (encode hN j w) = w := by
  apply funext; intro r
  have he : (r.val:ℤ)-((j:ℤ)-1) + ((j:ℤ)-1) = r.val := by ring
  simp only [decode, encode, he]
  rw [dif_pos (by constructor <;> omega)]
  congr 1

private theorem decode_swap (j s : ℕ) (h : s + 1 < n) (p : ℤ)
    (hp : p = (s : ℤ) - ((j : ℤ) - 1)) (w : ℤ → Fin N) :
    decode j (Path.swap w p) = swapWord s h (decode j w) := by
  funext r
  simp only [decode, Path.swap, swapWord, Function.comp_apply]
  by_cases h₁ : r.val = s
  · have hr : r = ⟨s, by omega⟩ := Fin.ext h₁
    rw [hr, Equiv.swap_apply_left]
    rw [show ((⟨s, by omega⟩ : Fin n).val : ℤ) - ((j : ℤ) - 1) = p by omega,
      Equiv.swap_apply_left]
    congr 1
    simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
    omega
  · by_cases h₂ : r.val = s + 1
    · have hr : r = ⟨s + 1, h⟩ := Fin.ext h₂
      rw [hr, Equiv.swap_apply_right]
      rw [show ((⟨s + 1, h⟩ : Fin n).val : ℤ) - ((j : ℤ) - 1) = p + 1 by omega,
        Equiv.swap_apply_right]
      congr 1
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
        Equiv.swap_apply_of_ne_of_ne (by intro he; exact h₁ (congrArg Fin.val he))
          (by intro he; exact h₂ (congrArg Fin.val he))]

private def lifted (j m : ℕ) (f : ℕ → (Fin n → Fin N) → ℝ) (s : (ℤ × (ℤ → Fin N))) : ℝ := by
  classical
  exact if Path.interior m s then f (s.1 + 1).toNat (decode j s.2) else 0

private theorem lifted_interval (j m : ℕ) (f : ℕ → (Fin n → Fin N) → ℝ)
    (hf0 : f 0 = 0) (hfm : f (m + 1) = 0) (s : (ℤ × (ℤ → Fin N)))
    (hs : -1 ≤ s.1 ∧ s.1 ≤ m) :
    lifted j m f s = f (s.1 + 1).toNat (decode j s.2) := by
  by_cases hi : Path.interior m s
  · simp [lifted, hi]
  · have he : s.1 = -1 ∨ s.1 = m := by unfold Path.interior at hi; omega
    rcases he with he | he
    · simp [lifted, hi, he, hf0]
    · simp [lifted, hi, he, hfm]

private theorem lifted_harmonic (μ : Fin N → ℝ) (j m : ℕ) (hj : 1 ≤ j) (hm : j + m ≤ n)
    (f : ℕ → (Fin n → Fin N) → ℝ) (hf0 : f 0 = 0) (hfm : f (m + 1) = 0)
    (hf : ∀ i, 1 ≤ i → i ≤ m →
      f i = calB μ j i *ᵥ f (i-1) + calBprime μ j i *ᵥ f (i + 1))
    (s : (ℤ × (ℤ → Fin N))) (hs : Path.interior m s) :
    lifted j m f s = (B μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1)) * lifted j m f (Path.leftState s) +
      (Bprime μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1)) * lifted j m f (Path.rightState s) := by
  have hsi := hs
  unfold Path.interior at hsi
  let i := (s.1 + 1).toNat
  have hi : 1 ≤ i := by dsimp [i]; omega
  have him : i ≤ m := by dsimp [i]; omega
  have hcast : (i:ℤ) = s.1 + 1 := by dsimp [i]; omega
  have hslot : j + i-2 + 1 < n := by omega
  have hp : s.1 = ((j + i-2:ℕ):ℤ)-((j:ℤ)-1) := by omega
  have hp' : ((j + i-2 + 1:ℕ):ℤ)-((j:ℤ)-1) = s.1 + 1 := by omega
  rw [lifted_interval j m f hf0 hfm s (by omega),
    lifted_interval j m f hf0 hfm (Path.leftState s) (by simp only [Path.leftState]; omega),
    lifted_interval j m f hf0 hfm (Path.rightState s) (by simp only [Path.rightState]; omega)]
  have hl : ((Path.leftState s).1 + 1).toNat = i-1 := by simp only [Path.leftState]; omega
  have hr : ((Path.rightState s).1 + 1).toNat = i + 1 := by simp only [Path.rightState]; omega
  rw [hl, hr]
  have hrec := congrFun (hf i hi him) (decode j s.2)
  simp only [Pi.add_apply, calB_mulVec μ j i hslot, calBprime_mulVec μ j i hslot] at hrec
  simp only [decode, ← hp, hp'] at hrec
  simpa only [i, Path.leftState, Path.rightState, decode_swap j (j + i-2) hslot s.1 hp s.2] using hrec

/-- Zero boundary values force every block value to vanish. -/
private theorem harmonic_chain_zero (μ : Fin N → ℝ) (hμ : ∀ a, 0 ≤ μ a ∧ μ a ≤ 1)
    (hN : 1 ≤ N) (j m : ℕ) (hj : 1 ≤ j) (hm : j + m ≤ n)
    (f : ℕ → (Fin n → Fin N) → ℝ) (hf0 : f 0 = 0) (hfm : f (m + 1) = 0)
    (hf : ∀ i, 1 ≤ i → i ≤ m →
      f i = calB μ j i *ᵥ f (i-1) + calBprime μ j i *ᵥ f (i + 1)) :
    ∀ i, i ≤ m + 1 → f i = 0 := by
  classical
  letI : NeZero N := ⟨by omega⟩
  let val : Fin (m + 2) × (Fin n → Fin N) → ℝ := fun s => |f s.1.val s.2|
  obtain ⟨r, _, hmax⟩ := Finset.exists_max_image Finset.univ val Finset.univ_nonempty
  let M := val r
  have hM : 0 ≤ M := abs_nonneg _
  have hb : ∀ s : (ℤ × (ℤ → Fin N)), |lifted j m f s| ≤ M := by
    intro s
    by_cases hs : Path.interior m s
    · have hsi := hs
      unfold Path.interior at hsi
      have hh := hmax (⟨(s.1 + 1).toNat, by omega⟩, decode j s.2) (Finset.mem_univ _)
      simpa [lifted, hs, val, M] using hh
    · simpa [lifted, hs] using hM
  have hat : ∃ s : (ℤ × (ℤ → Fin N)), |lifted j m f s| = M := by
    refine ⟨((r.1.val:ℤ)-1, encode hN j r.2), ?_⟩
    rw [lifted_interval j m f hf0 hfm _ (by constructor <;> omega), decode_encode]
    simp [M, val]
  have hz : M = 0 := maximum_zero_of_two_successor_exit (lifted j m f) M
    (fun s => ¬Path.interior m s) Path.leftState Path.rightState (fun s => B μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1)) (fun s => Bprime μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1))
    hb hat (fun s hs => by simp [lifted, hs])
    (fun s hs => weights_nonneg_sum μ hμ (s.2 s.1, s.2 (s.1 + 1)))
    (fun s hs => lifted_harmonic μ j m hj hm f hf0 hfm hf s (not_not.mp hs))
    (fun s => by simpa using weighted_exit μ m s)
  intro i hi
  apply funext; intro w
  have hh := hmax (⟨i, by omega⟩, w) (Finset.mem_univ _)
  have he : |f i w|=0 := le_antisymm (by simpa [val, M, hz] using hh) (abs_nonneg _)
  exact abs_eq_zero.mp he
variable {W : Type*} [Fintype W] [DecidableEq W]

private def pivot (L R : ℕ → Matrix W W ℝ) : ℕ → Matrix W W ℝ
  | 0 => 1
  | k + 1 => 1-L (k + 2)*(pivot L R k)⁻¹*R (k + 1)

private theorem extend (L R : ℕ → Matrix W W ℝ) (k : ℕ)
    (hu : ∀ i, i < k → IsUnit (pivot L R i)) (v : (W → ℝ)) :
    ∃ f : ℕ → (W → ℝ), f 0 = 0 ∧ f (k + 1) = v ∧
      (∀ i, 1 ≤ i → i ≤ k → (f i = L i *ᵥ f (i-1) + R i *ᵥ f (i + 1))) ∧
      L (k + 1) *ᵥ f k = (1-pivot L R k) *ᵥ v := by
  classical
  induction k generalizing v with
  | zero =>
    refine ⟨fun i => if i = 0 then 0 else v, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro i hi hik; omega
    · simp [pivot]
  | succ k ih =>
    have hk := hu k (by omega)
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hk
    let u := (pivot L R k)⁻¹ *ᵥ (R (k + 1) *ᵥ v)
    obtain ⟨f, hf0, hflast, hfharm, hfedge⟩ := ih
      (fun i hi => hu i (by omega)) u
    let g := Function.update f (k + 2) v
    have hgold (i : ℕ) (hi : i ≤ k + 1) : g i = f i := by
      simp [g, show i ≠ k + 2 by omega]
    have hglast : g (k + 2) = v := by simp [g]
    have hsolve : pivot L R k *ᵥ u = R (k + 1) *ᵥ v := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    refine ⟨g, (hgold 0 (by omega)).trans hf0, hglast, ?_, ?_⟩
    · intro i hi hik
      by_cases he : i = k + 1
      · subst i
        simp only [Nat.add_sub_cancel, show k + 1 + 1 = k + 2 by omega]
        rw [hgold (k + 1) (by omega), hgold k (by omega), hglast, hflast]
        rw [hfedge]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        rw [hsolve]
        simp
      · rw [hgold i (by omega), hgold (i-1) (by omega), hgold (i + 1) (by omega)]
        exact hfharm i hi (by omega)
    · rw [hgold (k + 1) (by omega), hflast]
      simp only [pivot, sub_sub_cancel, ← Matrix.mulVec_mulVec]
      rfl

/-- Dirichlet uniqueness for every leading chain forces every elimination pivot to be a unit. -/
private theorem pivots_isUnit (L R : ℕ → Matrix W W ℝ) (K : ℕ)
    (hunique : ∀ m, 1 ≤ m → m ≤ K + 1 → ∀ f : ℕ → (W → ℝ),
      f 0 = 0 → f (m + 1) = 0 →
      (∀ i, 1 ≤ i → i ≤ m → (f i = L i *ᵥ f (i-1) + R i *ᵥ f (i + 1))) → f m = 0) :
    ∀ k, k ≤ K → IsUnit (pivot L R k) := by
  classical
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply Matrix.mulVec_injective_iff_isUnit.mp
    suffices hz : ∀ v : (W → ℝ), pivot L R k *ᵥ v = 0 → v = 0 by
      intro x y hxy
      have he : pivot L R k *ᵥ (x-y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
      exact sub_eq_zero.mp (hz (x-y) he)
    intro v hv
    obtain ⟨f, hf0, hflast, hfharm, hfedge⟩ := extend L R k
      (fun i hi => ih i hi (by omega)) v
    let g := Function.update f (k + 2) 0
    have hgold (i : ℕ) (hi : i ≤ k + 1) : g i = f i := by
      simp [g, show i ≠ k + 2 by omega]
    have hglast : g (k + 2) = 0 := by simp [g]
    have hg : ∀ i, 1 ≤ i → i ≤ k + 1 → (g i = L i *ᵥ g (i-1) + R i *ᵥ g (i + 1)) := by
      intro i hi hik
      by_cases he : i = k + 1
      · subst i
        simp only [Nat.add_sub_cancel, show k + 1 + 1 = k + 2 by omega]
        rw [hgold (k + 1) (by omega), hgold k (by omega), hglast, hflast]
        rw [hfedge, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_zero, Matrix.mulVec_zero, add_zero]
      · rw [hgold i (by omega), hgold (i-1) (by omega), hgold (i + 1) (by omega)]
        exact hfharm i hi (by omega)
    have hz := hunique (k + 1) (by omega) (by omega) g
      ((hgold 0 (by omega)).trans hf0) hglast hg
    rw [hgold (k + 1) (by omega), hflast] at hz
    exact hz
private theorem pivot_eq_A {N n : ℕ} (μ : Fin N → ℝ) (j k : ℕ) :
    pivot (calB (n := n) μ j) (calBprime μ j) k = A μ j k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pivot, A, ih]

theorem result : claim := by
  intro N n j k hN hn hj hbound μ hμ
  have hp := pivots_isUnit (calB (n := n) μ j) (calBprime μ j) k
    (fun m hm hmk f hf0 hfm hf => harmonic_chain_zero μ hμ hN j m hj
      (by omega) f hf0 hfm hf m (by omega)) k (by omega)
  rwa [pivot_eq_A] at hp
end
end D5.S3.StatisticalMechanics.LongRangeSwap.LeeReductionInvertibility
