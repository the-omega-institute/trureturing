/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedXorTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two overlapping four-axis eigenvectors satisfy exact signed XOR transfer by parity. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum

/-! Signed transfer between overlapping four-axis masks for Hong, Wu and Xia's
Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer

noncomputable section

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip flip_apply_same flip_adj gamma gamma_apply)
open TwentyPointEightWord (gamma_square)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MaskedGram (maskWeight)
open private mask_weight_sq from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum
open Q9SignedContactCells (parityPart weighted_square)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private parityPart_apply gamma_selfAdjoint weighted_selfAdjoint weighted_sum
  from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

private abbrev Vec := Q 9 → ℝ

/-- The sum of the signed flips in a coordinate mask. -/
def maskOperator (I : Finset (Fin 9)) : Vec →ₗ[ℝ] Vec :=
  weightedLinear (maskWeight I)

private def bitPart (k : Fin 9) (t : Bool) : Vec →ₗ[ℝ] Vec :=
  LinearMap.pi fun x => if x k = t then LinearMap.proj x else 0

private theorem bitPart_apply (k : Fin 9) (t : Bool) (f : Vec) (x : Q 9) :
    bitPart k t f x = if x k = t then f x else 0 := by
  by_cases h : x k = t <;> simp [bitPart, h]

/-- Retain the entries on the cell with the specified two coordinate bits. -/
def cellPart (a b : Fin 9) (p q : Bool) : Vec →ₗ[ℝ] Vec :=
  (bitPart a p).comp (bitPart b q)

private theorem cellPart_comm (a b : Fin 9) (p q : Bool) (f : Vec) :
    cellPart a b p q f = bitPart b q (bitPart a p f) := by
  funext x
  by_cases ha : x a = p <;> by_cases hb : x b = q <;>
    simp [cellPart, bitPart_apply, ha, hb]

/-- The ordered signed XOR pairing between the two opposite cell traces. -/
def signedXorPair (a b : Fin 9) (fg : Vec × Vec) : ℝ :=
  fg.1 ⬝ᵥ gamma a (gamma b fg.2)

private theorem bitPart_gamma {a k : Fin 9} (h : a ≠ k) (t : Bool) (f : Vec) :
    bitPart a t (gamma k f) = gamma k (bitPart a t f) := by
  funext x
  have hbit : flip x k a = x a := by
    simp [BalancedCriticalSpectrum.flip, h]
  by_cases hx : x a = t <;> simp [bitPart_apply, gamma_apply, hbit, hx]

private theorem bitPart_gamma_same (k : Fin 9) (t : Bool) (f : Vec) :
    bitPart k t (gamma k f) = gamma k (bitPart k (!t) f) := by
  funext x
  cases t <;> cases hx : x k <;> simp [bitPart_apply, gamma_apply, flip_apply_same, hx]

private theorem bitPart_mask {I : Finset (Fin 9)} {a : Fin 9} (ha : a ∉ I)
    (p : Bool) (f : Vec) :
    bitPart a p (maskOperator I f) = maskOperator I (bitPart a p f) := by
  simp only [maskOperator, weighted_sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ∈ I
  · have hak : a ≠ k := fun h => ha (h.symm ▸ hk)
    rw [bitPart_gamma hak]
  · simp [maskWeight, hk]

private theorem mask_square (I : Finset (Fin 9)) (hI : I.card = 3) (f : Vec) :
    maskOperator I (maskOperator I f) = (3 : ℝ) • f := by
  simp only [maskOperator, weighted_square, mask_weight_sq, hI, Nat.cast_ofNat]

private theorem restrict_eigen {I : Finset (Fin 9)} {a b : Fin 9}
    (hab : a ≠ b) (hb : b ∉ I) (q : Bool) (f : Vec)
    (he : maskOperator I f + gamma a f = (2 : ℝ) • f) :
    maskOperator I (bitPart b q f) + gamma a (bitPart b q f) =
      (2 : ℝ) • bitPart b q f := by
  have h := congrArg (bitPart b q) he
  simpa only [map_add, map_smul, bitPart_mask hb, bitPart_gamma hab.symm] using h

private theorem trace_transfer {I : Finset (Fin 9)} {a : Fin 9} (ha : a ∉ I) (p : Bool)
    (f : Vec) (he : maskOperator I f + gamma a f = (2 : ℝ) • f) :
    bitPart a (!p) f = gamma a ((2 : ℝ) • bitPart a p f - maskOperator I (bitPart a p f)) := by
  have h := congrArg (bitPart a p) he
  simp only [map_add, map_smul, bitPart_mask ha, bitPart_gamma_same] at h
  have h' := eq_sub_of_add_eq' h
  rw [← h', gamma_square]

private theorem parityPart_gamma (t : Bool) (k : Fin 9) (f : Vec) :
    parityPart t (gamma k f) = gamma k (parityPart (!t) f) := by
  funext x
  have hx := cubeParity_ne_of_adj (flip_adj x k)
  cases t <;> cases h₁ : parity x <;> cases h₂ : parity (flip x k) <;>
    simp_all [parityPart_apply, gamma_apply]

private theorem parityPart_mask (I : Finset (Fin 9)) (t : Bool) (f : Vec) :
    parityPart t (maskOperator I f) = maskOperator I (parityPart (!t) f) := by
  simp only [maskOperator, weighted_sum, map_sum, map_smul, parityPart_gamma]

private theorem parityPart_split (t : Bool) (f : Vec) :
    parityPart t f + parityPart (!t) f = f := by
  funext x
  cases t <;> cases hx : parity x <;> simp [parityPart_apply, hx]

private theorem parityPair_eq (t : Bool) (f g : Vec) :
    parityPart t f ⬝ᵥ parityPart t g = parityPart t f ⬝ᵥ g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : parity x = t <;> simp [parityPart_apply, hx]

private theorem xor_cancel (a b : Fin 9) (f g : Vec) :
    signedXorPair a b (gamma a f, gamma b g) = f ⬝ᵥ g := by
  change gamma a f ⬝ᵥ gamma a (gamma b (gamma b g)) = _
  rw [gamma_selfAdjoint, gamma_square, gamma_square]

private theorem transfer_pair (I : Finset (Fin 9)) (hI : I.card = 3) (f g : Vec) :
    ((2 : ℝ) • f - maskOperator I f) ⬝ᵥ ((2 : ℝ) • g - maskOperator I g) =
      f ⬝ᵥ ((7 : ℝ) • g - (4 : ℝ) • maskOperator I g) := by
  have hself (u v : Vec) : maskOperator I u ⬝ᵥ v = u ⬝ᵥ maskOperator I v :=
    weighted_selfAdjoint _ _ _
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, hself,
    mask_square I hI, smul_eq_mul]
  ring

private theorem transfer_parity (I : Finset (Fin 9)) (hI : I.card = 3) (t : Bool) (f g : Vec) :
    parityPart (!t) ((2 : ℝ) • f - maskOperator I f) ⬝ᵥ
      parityPart (!t) ((2 : ℝ) • g - maskOperator I g) =
      3 * (parityPart t f ⬝ᵥ parityPart t g) +
        4 * (parityPart (!t) f ⬝ᵥ parityPart (!t) g) - 2 * (f ⬝ᵥ maskOperator I g) := by
  have hself (u v : Vec) : maskOperator I u ⬝ᵥ v = u ⬝ᵥ maskOperator I v :=
    weighted_selfAdjoint _ _ _
  have hcross := congrArg (fun u => u ⬝ᵥ maskOperator I g) (parityPart_split t f)
  change (parityPart t f + parityPart (!t) f) ⬝ᵥ maskOperator I g =
    f ⬝ᵥ maskOperator I g at hcross
  rw [add_dotProduct] at hcross
  simp only [parityPair_eq, map_sub, map_smul, parityPart_mask, Bool.not_not,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    hself, mask_square I hI, smul_eq_mul]
  have hodd : maskOperator I (parityPart t g) = parityPart (!t) (maskOperator I g) := by
    simpa only [Bool.not_not] using (parityPart_mask I (!t) g).symm
  rw [← parityPart_mask I t g, hodd, parityPair_eq, parityPair_eq]
  linarith

/-- Two eigenvectors for three common axes and one distinct axis each have an exact signed
XOR coupling. The two parity formulas use the same cross-parity correction. -/
theorem overlapping_mask_signed_xor
    (I : Finset (Fin 9)) (a b : Fin 9) (hab : a ≠ b) (hI : I.card = 3)
    (ha : a ∉ I) (hb : b ∉ I) (p q : Bool) (f g : Vec)
    (hf : maskOperator I f + gamma a f = (2 : ℝ) • f)
    (hg : maskOperator I g + gamma b g = (2 : ℝ) • g) :
    let pair := fun fg => signedXorPair a b fg
    let B := maskOperator I
    let f₀ := cellPart a b p q f
    let g₀ := cellPart a b p q g
    let f₁ := cellPart a b (!p) q f
    let g₁ := cellPart a b p (!q) g
    let S := fun t => parityPart t f₀ ⬝ᵥ parityPart t g₀
    let D := fun t => pair (parityPart t f₁, parityPart t g₁)
    let L := f₀ ⬝ᵥ B g₀
    f₁ = gamma a ((2 : ℝ) • f₀ - B f₀) ∧
    g₁ = gamma b ((2 : ℝ) • g₀ - B g₀) ∧
    pair (f₁, g₁) = f₀ ⬝ᵥ ((7 : ℝ) • g₀ - (4 : ℝ) • B g₀) ∧
    (∀ t, D t = 3 * S t + 4 * S (!t) - 2 * L) ∧
    D false - D true = S true - S false := by
  dsimp only
  have hF := trace_transfer ha p _ (restrict_eigen hab hb q f hf)
  change cellPart a b (!p) q f =
    gamma a ((2 : ℝ) • cellPart a b p q f - maskOperator I (cellPart a b p q f)) at hF
  have hG := trace_transfer hb q _ (restrict_eigen hab.symm ha p g hg)
  rw [← cellPart_comm a b p (!q), ← cellPart_comm a b p q] at hG
  have hParity (t : Bool) :
      signedXorPair a b
        (parityPart t (cellPart a b (!p) q f), parityPart t (cellPart a b p (!q) g)) =
        3 * (parityPart t (cellPart a b p q f) ⬝ᵥ parityPart t (cellPart a b p q g)) +
        4 * (parityPart (!t) (cellPart a b p q f) ⬝ᵥ parityPart (!t) (cellPart a b p q g)) -
        2 * (cellPart a b p q f ⬝ᵥ maskOperator I (cellPart a b p q g)) := by
    rw [hF, hG, parityPart_gamma, parityPart_gamma, xor_cancel]
    exact transfer_parity I hI t _ _
  refine ⟨hF, hG, ?_, hParity, ?_⟩
  · rw [hF, hG, xor_cancel]
    exact transfer_pair I hI _ _
  · rw [hParity false, hParity true]
    simp only [Bool.not_false, Bool.not_true]
    ring

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer.overlapping_mask_signed_xor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms overlapping_mask_signed_xor

end

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedXorTransfer
