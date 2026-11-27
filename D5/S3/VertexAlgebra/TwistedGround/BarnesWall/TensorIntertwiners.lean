/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorIntertwiners
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/TensorIntertwiners
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual odd-slot ground has quaternion covariant operators with the uniform trace product. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddWeylTrace
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorGround
import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.WeylCovariantOperator

/-! Covariant quaternion intertwiners on the odd-slot Barnes–Wall ground representation. -/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorIntertwiners

open LatticeTwistedGroundRealization (Ground)
open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign)
open TailPauliPairing (Word parity)
open OddWeylTrace (evenDisplacement mem_evenDisplacement_iff tensor_displacement_ranges
  separates_outside_evenDisplacement tensorPairing_perfect normalized_tensor_trace_mul)
open private actionI actionJ actionI_eq actionJ_eq lift_phase_polar wordI wordJ
  from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddGaussSum
open private fixed_and_phase_zero from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.OddWeylTrace

noncomputable section

variable {ι : Type} [Fintype ι] [LinearOrder ι] [order : LinearOrder (Word ι)]

private abbrev A (ι : Type) := Word ι → F₂
private abbrev H : LinearMap.BilinForm F₂ (A ι) := TensorGram.halfGram.toBilin'

private theorem displacement_ker (t : ι) (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 3 ≤ Fintype.card ι) (g : A ι →ₗ[F₂] A ι) (q : A ι → F₂)
    (himage : LinearMap.range (g + LinearMap.id) = evenDisplacement t)
    (hfix : ∀ x ∈ evenDisplacement t, g x = x)
    (hpolar : ∀ x y, q (x + y) = q x + q y + (H x y + H (g x) (g y))) :
    LinearMap.ker (g + LinearMap.id) = evenDisplacement t := by
  apply le_antisymm
  · intro x hx
    have hzero : g x + x = 0 := LinearMap.mem_ker.mp hx
    have hfixx : g x = x := by
      funext u
      exact CharTwo.add_eq_zero.mp (congrFun hzero u)
    by_contra hn
    obtain ⟨w, hw, hs⟩ := separates_outside_evenDisplacement t hodd hm x hn
    obtain ⟨y, hy⟩ : ∃ y, g y + y = w := by
      have hw' : w ∈ LinearMap.range (g + LinearMap.id) := himage.symm ▸ hw
      exact LinearMap.mem_range.mp hw'
    have h := hpolar x y
    have h' := hpolar y x
    rw [add_comm y x, add_comm (q y) (q x), hfixx] at h'
    rw [hfixx, h'] at h
    have hc := add_left_cancel h
    have hz : H x (g y) + H x y + (H (g y) x + H y x) = 0 := by
      calc
        _ = (H x y + H x (g y)) + (H y x + H (g y) x) := by abel
        _ = 0 := by rw [hc, CharTwo.add_self_eq_zero]
    change H x w + H w x = 1 at hs
    rw [← hy, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hz] at hs
    exact zero_ne_one hs
  · intro x hx
    apply LinearMap.mem_ker.mpr
    change g x + x = 0
    rw [hfix x hx]
    funext u
    exact CharTwo.add_self_eq_zero _

private theorem displacement_halfGram_zero (t : ι) (hodd : (Fintype.card ι : F₂) = 1)
    (hm : 5 ≤ Fintype.card ι) (x y : A ι) (hx : x ∈ evenDisplacement t)
    (hy : y ∈ evenDisplacement t) : H x y = 0 := by
  change TensorGram.halfGram.toBilin' x y = 0
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  by_cases hu : x u = 0
  · simp [hu]
  by_cases hv : y v = 0
  · simp [hv]
  have hpu : parity u = 0 := by
    rcases (show ∀ z : F₂, z = 0 ∨ z = 1 by decide) (parity u) with h | h
    · exact h
    · exact (hu ((mem_evenDisplacement_iff t x).mp hx u h)).elim
  have hpv : parity v = 0 := by
    rcases (show ∀ z : F₂, z = 0 ∨ z = 1 by decide) (parity v) with h | h
    · exact h
    · exact (hv ((mem_evenDisplacement_iff t y).mp hy v h)).elim
  have hz : TensorGram.halfGram u v = 0 := by
    by_cases huv : v = u
    · subst v
      exact TensorGram.halfGram_eq_zero_of_agree_outside hodd hm t t u u (fun _ _ _ => rfl)
    · unfold TensorGram.halfGram
      by_cases hlt : @LT.lt _ order.toLT v u <;>
        simp [hlt, huv, TensorGram.gram_mod_two_of_even_even hodd u v hpu hpv]
  simp [hz]

/-- The abstract ground representation of the actual odd-slot reflection quotient
has covariant Pauli-word operators whose normalized product trace is the tensor
Gauss sum. -/
theorem exists_tensor_intertwiners (r₁ r₂ t : ι)
    (h₁₂ : r₁ ≠ r₂) (ht₁ : t ≠ r₁) (ht₂ : t ≠ r₂)
    (hodd : (Fintype.card ι : F₂) = 1) (hm : 5 ≤ Fintype.card ι) :
    ∃ (n : ℕ) (P : A ι → Module.End ℂ (Ground n)) (Ui Uj : Module.End ℂ (Ground n)),
      P 0 = 1 ∧ (∀ x y, P x * P y = complexSign (H x y) • P (x + y)) ∧
      Ui ≠ 0 ∧ Uj ≠ 0 ∧
      (∀ x, Ui * P x = complexSign (TensorLift.wordLiftExponent (wordI r₁) x) •
        (P (actionI r₁ x) * Ui)) ∧
      (∀ x, Uj * P x = complexSign (TensorLift.wordLiftExponent (wordJ r₁ r₂) x) •
        (P (actionJ r₁ r₂ x) * Uj)) ∧
      ((Module.finrank ℂ (Ground n) : ℂ) * LinearMap.trace ℂ (Ground n) (Ui * Uj)) /
        (LinearMap.trace ℂ (Ground n) Ui * LinearMap.trace ℂ (Ground n) Uj) =
      (2 : ℂ) ^ (2 ^ (Fintype.card ι - 2)) := by
  classical
  have hm₃ : 3 ≤ Fintype.card ι := by omega
  obtain ⟨n, P, _, hd, hzero, hmul⟩ := TensorGround.exists_tensor_ground hodd hm₃
  have hcard : Fintype.card (Word ι) / 2 = 2 ^ (Fintype.card ι - 1) := by
    rw [Fintype.card_fun, Fintype.card_bool]
    have he : (2 : ℕ) ^ Fintype.card ι = 2 ^ (Fintype.card ι - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ Fintype.card ι by omega)]
    rw [he]
    omega
  have hdim : Module.finrank ℂ (Ground n) = 2 ^ (2 ^ (Fintype.card ι - 1)) := by rw [hd, hcard]
  have hfix := fixed_and_phase_zero r₁ r₂ t hodd hm
  have hrange := tensor_displacement_ranges r₁ r₂ t h₁₂
  have hI := lift_phase_polar hodd hm₃ (wordI r₁)
  have hJ := lift_phase_polar hodd hm₃ (wordJ r₁ r₂)
  simp only [← actionI_eq hodd r₁] at hI
  simp only [← actionJ_eq hodd r₁ r₂] at hJ
  have htr (w : evenDisplacement t) (hw : (w : A ι) ≠ 0) : LinearMap.trace ℂ (Ground n) (P w) = 0 :=
    WeylIntertwinerTraceProduct.displacement_trace_eq_zero hzero hmul (tensorPairing_perfect t hodd hm₃) hw
  have hiso (x) (hx : x ∈ evenDisplacement t) (y) (hy : y ∈ evenDisplacement t) : H x y = 0 :=
    displacement_halfGram_zero t hodd hm x y hx hy
  obtain ⟨Ui, hUi, hcovI, _⟩ := WeylCovariantOperator.exists_covariant_operator
    (g := actionI r₁) (H := H) (q := TensorLift.wordLiftExponent (wordI r₁))
    (displacement_ker t hodd hm₃ _ _ hrange.1 (fun w hw => (hfix w hw).1.1) hI)
    hiso (fun w hw => (hfix w hw).1.2) hI hrange.1 hzero hmul htr
  obtain ⟨Uj, hUj, hcovJ, _⟩ := WeylCovariantOperator.exists_covariant_operator
    (g := actionJ r₁ r₂) (H := H) (q := TensorLift.wordLiftExponent (wordJ r₁ r₂))
    (displacement_ker t hodd hm₃ _ _ hrange.2 (fun w hw => (hfix w hw).2.1) hJ)
    hiso (fun w hw => (hfix w hw).2.2) hJ hrange.2 hzero hmul htr
  refine ⟨n, P, Ui, Uj, hzero, hmul, hUi, hUj, hcovI, hcovJ, ?_⟩
  apply normalized_tensor_trace_mul r₁ r₂ t h₁₂ ht₁ ht₂ hodd hm P hzero hmul hdim hUi hUj
  · simpa only [actionI_eq hodd, wordI] using hcovI
  · simpa only [actionJ_eq hodd, wordJ] using hcovJ

end
end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TensorIntertwiners
