/- GID: D5/S3/VertexAlgebra/Sectors/VBKMSingularVector
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/VBKMSingularVector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.VertexAlgebra.Sectors.VBKMSingularVector.positive_modes_kill
Direct frozen dependencies: none; all D5 prerequisites are in this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30339
Definitions are labelled bind-only as encodings, not as proofs of new propositions.
Declarations (consumer names are qualified by their owning module):
singularWord: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: VBKMSingularVector.singularWord_cartan, VBKMSingularVector.singularWord_commute, VBKMSingularVector.singularWord_mode_one, VBKMSingularVector.singularWord_mode_two, VBKMSingularVector.singularWord_eigen, ZverykIdealRigidityRefutation.presentedSingular, ZverykIdealRigidityRefutation.presented_e_singular.
singularWord_cartan: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_e_singular.
singularWord_commute: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_e_singular.
singularWord_mode_one: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
singularWord_mode_two: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
positive_modes_kill: proof_shape: content; frozen: none; escape_witness: VBKMSingularVector.positive_modes_kill; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
singularWord_eigen: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_singular_eigen.
-/


import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
namespace D5.S3.VertexAlgebra.Sectors.VBKMSingularVector

variable {A : Type*} [LieRing A] [LieAlgebra ℂ A]

noncomputable def singularWord (L : ℤ → A) (w : A) : A :=
  ⁅L (-1), ⁅L (-1), ⁅L (-1), ⁅L (-1), w⁆⁆⁆⁆ -
  (3 : ℂ) • ⁅L (-2), ⁅L (-1), ⁅L (-1), w⁆⁆⁆ -
  (7 / 4 : ℂ) • ⁅L (-2), ⁅L (-2), w⁆⁆ +
  (3 : ℂ) • ⁅L (-3), ⁅L (-1), w⁆⁆ +
  (3 / 2 : ℂ) • ⁅L (-4), w⁆

theorem singularWord_cartan (L : ℤ → A) (C H : A) (δ : ℂ)
    (hH : ∀ r : ℤ, ⁅L (-r), H⁆ = ((r : ℂ) * δ) • L (-r))
    (hLL : ∀ n m : ℤ, ⁅L n, L m⁆ = ((n-m : ℤ) : ℂ) • L (n+m) +
      if n = -m then ((n^3-n : ℤ) : ℂ) • C else 0) :
    singularWord L H = 0 := by
  unfold singularWord
  simp only [hH, lie_smul, hLL, smul_lie, smul_zero, zero_smul, lie_zero]
  norm_num
  module


theorem singularWord_commute (L : ℤ → A) (e w : A)
    (he : ∀ n : ℤ, n < 0 → ⁅e, L n⁆ = 0) :
    ⁅e, singularWord L w⁆ = singularWord L ⁅e,w⁆ := by
  simp only [singularWord, lie_add, lie_sub, lie_smul, leibniz_lie e,
    he (-1) (by norm_num), he (-2) (by norm_num),
    he (-3) (by norm_num), he (-4) (by norm_num), zero_lie, zero_add]

theorem singularWord_mode_one (L : ℤ → A) (C w : A)
    (hvir : ∀ n m : ℤ, ⁅L n, L m⁆ = ((n-m : ℤ) : ℂ) • L (n+m) +
      if n = -m then ((n^3-n : ℤ) : ℂ) • C else 0)
    (h0 : ⁅L 0,w⁆ = (-3/8 : ℂ) • w)
    (h1 : ⁅L 1,w⁆ = 0) :
    ⁅L 1, singularWord L w⁆ = 0 := by
  have hn12 : ⁅L (-1), ⁅L (-2), w⁆⁆ =
      ⁅L (-2), ⁅L (-1), w⁆⁆ + ⁅L (-3), w⁆ := by
    rw [leibniz_lie, hvir]
    norm_num
    module
  simp [singularWord, lie_add, lie_sub, lie_smul, leibniz_lie (L 1),
    leibniz_lie (L 0), hvir, add_lie, smul_lie, lie_add, lie_smul,
    h0, h1, lie_zero, zero_lie, zero_smul, smul_zero, add_zero, zero_add]
  norm_num
  simp only [leibniz_lie (L 0), h0, lie_smul, hn12]
  module

theorem singularWord_mode_two (L : ℤ → A) (C w : A)
    (hvir : ∀ n m : ℤ, ⁅L n, L m⁆ = ((n-m : ℤ) : ℂ) • L (n+m) +
      if n = -m then ((n^3-n : ℤ) : ℂ) • C else 0)
    (h0 : ⁅L 0,w⁆ = (-3/8 : ℂ) • w)
    (h1 : ⁅L 1,w⁆ = 0) (h2 : ⁅L 2,w⁆ = 0)
    (hc : ⁅C,w⁆ = (1/3 : ℂ) • w)
    (hcentral : ∀ n : ℤ, ⁅C,L n⁆ = 0) :
    ⁅L 2, singularWord L w⁆ = 0 := by
  simp [singularWord, lie_add, lie_sub, lie_smul, leibniz_lie (L 2),
    leibniz_lie (L 1), leibniz_lie (L 0), leibniz_lie C, hcentral,
    hvir, add_lie, smul_lie, lie_add, lie_smul,
    h0, h1, h2, hc, lie_zero, zero_lie, zero_smul, smul_zero, add_zero, zero_add]
  norm_num
  try simp only [leibniz_lie (L 1), leibniz_lie (L 0), leibniz_lie C, hcentral,
    hvir, h0, h1, h2, hc, add_lie, smul_lie, lie_add, lie_smul,
    zero_lie, lie_zero, zero_smul, smul_zero, add_zero, zero_add]
  norm_num
  module

theorem positive_modes_kill (L : ℤ → A) (C v : A)
    (hvir : ∀ n m : ℤ, ⁅L n,L m⁆ = ((n-m : ℤ) : ℂ) • L (n+m) +
      if n = -m then ((n^3-n : ℤ) : ℂ) • C else 0)
    (h1 : ⁅L 1,v⁆ = 0) (h2 : ⁅L 2,v⁆ = 0) :
    ∀ n : ℤ, 0 < n → ⁅L n,v⁆ = 0 := by
  have hnat (n : ℕ) : ⁅L (n+1),v⁆ = 0 := by
    induction n using Nat.twoStepInduction with
    | zero => simpa using h1
    | one => simpa using h2
    | more n hn hn1 =>
      have hh : ⁅⁅L 1,L (n+2)⁆,v⁆ = 0 := by
        rw [lie_lie]
        have hprev : ⁅L (n+2),v⁆ = 0 := by
          exact (AddSemiconjBy.eq_zero_iff ⁅L (n+2),v⁆ rfl).mp hn1
        rw [hprev,h1,lie_zero,lie_zero,sub_self]
      rw [hvir,add_lie,smul_lie] at hh
      have hneq : (1 : ℤ) ≠ -(n+2) := by exact not_eq_of_beq_eq_false rfl
      rw [if_neg hneq,zero_lie,add_zero] at hh
      have hcoeff : (((1-(n+2) : ℤ) : ℂ)) ≠ 0 := by
        exact_mod_cast (show (1-(n+2) : ℤ) ≠ 0 by omega)
      have hz := (smul_eq_zero.mp hh).resolve_left hcoeff
      convert hz using 1 <;> push_cast <;> ring
  intro n hn
  obtain ⟨k,hk⟩ : ∃ k : ℕ, n = k+1 := by
    refine ⟨(n-1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  rw [hk]
  exact hnat k

theorem singularWord_eigen (L : ℤ → A) (H w : A) (δ μ : ℂ)
    (hHL : ∀ n : ℤ, ⁅H,L n⁆ = ((n : ℂ)*δ) • L n)
    (hHw : ⁅H,w⁆ = μ • w) :
    ⁅H,singularWord L w⁆ = (μ-4*δ) • singularWord L w := by
  simp only [singularWord,lie_add,lie_sub,lie_smul,leibniz_lie H,hHL,hHw,
    smul_lie,lie_smul]
  push_cast
  module



end D5.S3.VertexAlgebra.Sectors.VBKMSingularVector
