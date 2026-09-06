/- GID: D5/S3/Resource/SeparableConeResidualWitness
   generality: I
   mirror-B: D5/B/S3/Resource/SeparableConeResidualWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unique separable matrix argmin is the cone projection and gives its canonical negative residual witness. -/

import D5.S3.Resource.SeparableConeClosed
import D5.S3.Observer.Separation.MoreauDecomposition

/- Search: current D5 supplies finite PSD tensor sums, their closedness and duality,
   and generic cone projection/Moreau decomposition; no matrix argmin binding was found.
   Pinned Mathlib supplies EuclideanSpace.equiv, PiLp.inner_apply, nonnegative conic
   hulls and the projection variational characterization. The coordinate companions
   below serve only this domain bridge; no matrix norm or inner-product instance is added.
   Classification: bind-only, atom-required-bridge; no escape witness. -/

namespace D5.S3.Resource.SeparableConeResidualWitness

open D5.S3.Resource.CompositeCones
open D5.S3.Resource.CompositeConeDuality
open D5.S3.Resource.EntanglementWitness (separableCone_zero separableCone_add separableCone_smul)
open D5.S3.Resource.SeparableConeClosed (isClosed_separableCone)
open D5.S3.Observer.Separation.ConeResidualWitness
open D5.S3.Observer.Separation.MoreauDecomposition
open scoped RealInnerProductSpace Kronecker ComplexOrder

noncomputable section
variable {m n : ℕ}

/-- Standard complex entry coordinates, carrying their existing real Hilbert structure. -/
abbrev EntrySpace (m n : ℕ) :=
  EuclideanSpace ℂ ((Fin m × Fin n) × (Fin m × Fin n))

private def entryLinear : CompositeMatrix m n ≃ₗ[ℝ]
    (((Fin m × Fin n) × (Fin m × Fin n)) → ℂ) where
  toFun A ij := A ij.1 ij.2
  invFun v i j := v (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entries give a real linear equivalence continuous in both directions. -/
def entryEquiv : CompositeMatrix m n ≃L[ℝ] EntrySpace m n :=
  entryLinear.toContinuousLinearEquiv.trans
    (((EuclideanSpace.equiv _ _).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv).symm

@[simp] theorem entryEquiv_apply (A : CompositeMatrix m n) (i j : Fin m × Fin n) :
    entryEquiv A (i, j) = A i j := rfl

/-- The metric is Hilbert--Schmidt, independently of the default matrix norm. -/
theorem entry_inner (S W : CompositeMatrix m n) :
    inner ℝ (entryEquiv S) (entryEquiv W) = pairing S W := by
  simp only [PiLp.inner_apply, Complex.inner]
  change (∑ ij : (Fin m × Fin n) × (Fin m × Fin n),
    (W ij.1 ij.2 * star (S ij.1 ij.2)).re) = _
  simp only [pairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, RCLike.re_to_complex]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [mul_comm, Complex.star_def]

theorem pairing_symm (S W : CompositeMatrix m n) : pairing S W = pairing W S := by
  rw [← entry_inner, ← entry_inner, real_inner_comm]

/-- The source's matrix optimization objective, with no projection in its definition. -/
def distanceSq (R P : CompositeMatrix m n) : ℝ := pairing (R - P) (R - P)

theorem distanceSq_eq (R P : CompositeMatrix m n) :
    distanceSq R P = ‖entryEquiv (R - P)‖ ^ 2 := by
  rw [distanceSq, ← entry_inner, real_inner_self_eq_norm_sq]

/-- Independent positive semidefinite factors generate the source cone. -/
def sourceGenerators (m n : ℕ) : Set (CompositeMatrix m n) :=
  {S | ∃ A : Matrix (Fin m) (Fin m) ℂ, ∃ B : Matrix (Fin n) (Fin n) ℂ,
    A.PosSemidef ∧ B.PosSemidef ∧ S = A ⊗ₖ B}

private def matrixCone (m n : ℕ) : PointedCone ℝ (CompositeMatrix m n) where
  carrier := {S | separableCone S}
  zero_mem' := separableCone_zero
  add_mem' := separableCone_add
  smul_mem' c _ h := separableCone_smul c.2 h

private theorem generator_separable {S : CompositeMatrix m n}
    (h : S ∈ sourceGenerators m n) : separableCone S := by
  obtain ⟨A, B, hA, hB, rfl⟩ := h
  exact ⟨1, fun _ => A, fun _ => B, fun _ => ⟨hA, hB⟩, by simp⟩

private theorem hull_eq :
    (PointedCone.hull ℝ (sourceGenerators m n) : Set (CompositeMatrix m n)) =
      {S | separableCone S} := by
  apply Set.Subset.antisymm
  · exact (Submodule.span_le.mpr fun _ h => generator_separable h :
      PointedCone.hull ℝ (sourceGenerators m n) ≤ matrixCone m n)
  · rintro S ⟨k, A, B, hAB, rfl⟩
    apply Submodule.sum_mem
    intro i _
    exact PointedCone.subset_hull ⟨A i, B i, (hAB i).1, (hAB i).2, rfl⟩

/-- Identification of the closed nonnegative conic hull; closedness is reused. -/
theorem closed_conic_hull_eq_separable :
    closure (PointedCone.hull ℝ (sourceGenerators m n) : Set (CompositeMatrix m n)) =
      {S | separableCone S} := by
  rw [hull_eq, isClosed_separableCone.closure_eq]

/-- The actual separable cone transported into standard Hilbert coordinates. -/
def separableProperCone (m n : ℕ) : ProperCone ℝ (EntrySpace m n) where
  carrier := {v | separableCone ((entryEquiv (m := m) (n := n)).symm v)}
  zero_mem' := by simpa using (separableCone_zero (m := m) (n := n))
  add_mem' := by
    intro x y hx hy
    simpa using separableCone_add hx hy
  smul_mem' := by
    intro c x hx
    change separableCone ((entryEquiv (m := m) (n := n)).symm ((c : ℝ) • x))
    rw [map_smul]
    exact separableCone_smul c.2 hx
  isClosed' := isClosed_separableCone.preimage
    (entryEquiv (m := m) (n := n)).symm.continuous

@[simp] theorem mem_separableProperCone (v : EntrySpace m n) :
    v ∈ separableProperCone m n ↔
      separableCone ((entryEquiv (m := m) (n := n)).symm v) := Iff.rfl

@[simp] theorem entry_mem_separableProperCone (S : CompositeMatrix m n) :
    entryEquiv S ∈ separableProperCone m n ↔ separableCone S := by simp

/-- Inner duality has the nonnegative sign and imposes no extra Hermiticity premise. -/
theorem entry_mem_innerDual_iff (W : CompositeMatrix m n) :
    entryEquiv W ∈ ProperCone.innerDual (separableProperCone m n : Set (EntrySpace m n)) ↔
      blockPositive W := by
  rw [blockPositive_iff_forall_separable_pairing_nonneg, ProperCone.mem_innerDual]
  constructor
  · intro h S hS
    simpa only [entry_inner] using h ((entry_mem_separableProperCone S).mpr hS)
  · intro h v hv
    obtain ⟨S, rfl⟩ := entryEquiv.surjective v
    simpa only [entry_inner] using h S ((entry_mem_separableProperCone S).mp hv)

/-- Independent minimization over the original matrix cone. -/
def Argmin (R P : CompositeMatrix m n) : Prop :=
  separableCone P ∧ ∀ Q, separableCone Q → distanceSq R P ≤ distanceSq R Q

private theorem argmin_iff_minimal (R P : CompositeMatrix m n) :
    Argmin R P ↔ entryEquiv P ∈ separableProperCone m n ∧
      ‖entryEquiv R - entryEquiv P‖ =
        ⨅ v : (separableProperCone m n : Set (EntrySpace m n)), ‖entryEquiv R - v‖ := by
  have hb : BddBelow (Set.range fun v : (separableProperCone m n : Set (EntrySpace m n)) =>
      ‖entryEquiv R - v‖) := ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩
  constructor
  · rintro ⟨hP, hmin⟩
    refine ⟨(entry_mem_separableProperCone P).mpr hP, le_antisymm ?_ ?_⟩
    · apply le_ciInf
      intro v
      have h := hmin (entryEquiv.symm v) v.property
      rw [distanceSq_eq, distanceSq_eq, map_sub, map_sub,
        ContinuousLinearEquiv.apply_symm_apply] at h
      nlinarith [norm_nonneg (entryEquiv R - entryEquiv P), norm_nonneg (entryEquiv R - v)]
    · exact ciInf_le hb ⟨entryEquiv P, (entry_mem_separableProperCone P).mpr hP⟩
  · rintro ⟨hP, hmin⟩
    refine ⟨(entry_mem_separableProperCone P).mp hP, fun Q hQ => ?_⟩
    have h := ciInf_le hb ⟨entryEquiv Q, (entry_mem_separableProperCone Q).mpr hQ⟩
    rw [← hmin] at h
    rw [distanceSq_eq, distanceSq_eq, map_sub, map_sub]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem projection_argmin (R : CompositeMatrix m n) :
    Argmin R ((entryEquiv (m := m) (n := n)).symm
      (coneProjection (separableProperCone m n) (entryEquiv R))) := by
  rw [argmin_iff_minimal, ContinuousLinearEquiv.apply_symm_apply]
  exact Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (separableProperCone m n).nonempty (separableProperCone m n).isClosed.isComplete
    (separableProperCone m n).convex (entryEquiv R))

private theorem argmin_moreau {R P : CompositeMatrix m n} (h : Argmin R P) :
    entryEquiv P ∈ separableProperCone m n ∧
      -entryEquiv (R - P) ∈ ProperCone.innerDual
        (separableProperCone m n : Set (EntrySpace m n)) ∧
      inner ℝ (entryEquiv P) (entryEquiv (R - P)) = 0 ∧
      entryEquiv R = entryEquiv P + entryEquiv (R - P) := by
  obtain ⟨hp, hm⟩ := (argmin_iff_minimal R P).mp h
  have hv := (norm_eq_iInf_iff_real_inner_le_zero (separableProperCone m n).convex hp).mp hm
  have hz := hv 0 (separableProperCone m n).zero_mem
  have ht := hv ((2 : ℝ) • entryEquiv P) ((separableProperCone m n).smul_mem hp (by norm_num))
  simp only [zero_sub, inner_neg_right] at hz
  simp only [two_smul, add_sub_cancel_right] at ht
  have ho : inner ℝ (entryEquiv (R - P)) (entryEquiv P) = 0 := by
    rw [map_sub]
    linarith
  refine ⟨hp, ?_, by rw [real_inner_comm]; exact ho, by rw [map_sub]; abel⟩
  rw [ProperCone.mem_innerDual]
  intro v hv'
  have hvv := hv (v + entryEquiv P) ((separableProperCone m n).add_mem hv' hp)
  simp only [add_sub_cancel_right] at hvv
  rw [inner_neg_right, real_inner_comm, map_sub]
  exact neg_nonneg.mpr hvv

/-- Existence and uniqueness follow from the existing unique Moreau decomposition. -/
theorem existsUnique_argmin (R : CompositeMatrix m n) : ∃! P, Argmin R P := by
  refine ⟨_, projection_argmin R, fun Q hQ => ?_⟩
  apply entryEquiv.injective
  have heq := (moreau_decomposition (separableProperCone m n) (entryEquiv R)).unique
    (y₁ := (entryEquiv Q, entryEquiv (R - Q)))
    (y₂ := (entryEquiv (entryEquiv.symm (coneProjection (separableProperCone m n) (entryEquiv R))),
      entryEquiv (R - entryEquiv.symm (coneProjection (separableProperCone m n) (entryEquiv R)))))
    (argmin_moreau hQ) (argmin_moreau (projection_argmin R))
  exact congrArg Prod.fst heq

/-- Chosen from the independent unique-argmin characterization. -/
def nearestSeparable (R : CompositeMatrix m n) : CompositeMatrix m n :=
  (existsUnique_argmin R).exists.choose

theorem nearestSeparable_spec (R : CompositeMatrix m n) : Argmin R (nearestSeparable R) :=
  (existsUnique_argmin R).exists.choose_spec

theorem nearestSeparable_unique {R P : CompositeMatrix m n} (h : Argmin R P) :
    P = nearestSeparable R :=
  (existsUnique_argmin R).unique h (nearestSeparable_spec R)

/-- Identification, proved after defining and solving the independent matrix problem. -/
theorem nearestSeparable_projection (R : CompositeMatrix m n) :
    entryEquiv (nearestSeparable R) = coneProjection (separableProperCone m n) (entryEquiv R) := by
  rw [← nearestSeparable_unique (projection_argmin R), ContinuousLinearEquiv.apply_symm_apply]

/-- The canonical matrix pair is the unique orthogonal decomposition with polar residual.
    The minus sign converts the polar cone into Mathlib's nonnegative inner dual. -/
theorem separable_moreau_decomposition (R : CompositeMatrix m n) :
    let P := nearestSeparable R
    let r := R - P
    (separableCone P ∧ blockPositive (-r) ∧ pairing P r = 0 ∧ R = P + r) ∧
      ∀ Q s : CompositeMatrix m n,
        separableCone Q → blockPositive (-s) → pairing Q s = 0 → R = Q + s →
          Q = P ∧ s = r := by
  dsimp only
  have h := argmin_moreau (nearestSeparable_spec R)
  have hc : separableCone (nearestSeparable R) ∧ blockPositive (-(R - nearestSeparable R)) ∧
      pairing (nearestSeparable R) (R - nearestSeparable R) = 0 ∧
      R = nearestSeparable R + (R - nearestSeparable R) := by
    refine ⟨(nearestSeparable_spec R).1, ?_, ?_, by abel⟩
    · apply (entry_mem_innerDual_iff _).mp
      simpa only [map_neg] using h.2.1
    · simpa only [entry_inner] using h.2.2.1
  refine ⟨hc, fun Q s hQ hs hQs hR => ?_⟩
  have hs' := (entry_mem_innerDual_iff (-s)).mpr hs
  rw [map_neg] at hs'
  have hother : entryEquiv Q ∈ separableProperCone m n ∧
      -entryEquiv s ∈ ProperCone.innerDual (separableProperCone m n : Set (EntrySpace m n)) ∧
      inner ℝ (entryEquiv Q) (entryEquiv s) = 0 ∧ entryEquiv R = entryEquiv Q + entryEquiv s :=
    ⟨(entry_mem_separableProperCone Q).mpr hQ, hs', by rwa [entry_inner], by rw [hR, map_add]⟩
  have heq := (moreau_decomposition (separableProperCone m n) (entryEquiv R)).unique
    (y₁ := (entryEquiv Q, entryEquiv s))
    (y₂ := (entryEquiv (nearestSeparable R), entryEquiv (R - nearestSeparable R))) hother h
  exact ⟨entryEquiv.injective (congrArg Prod.fst heq),
    entryEquiv.injective (congrArg Prod.snd heq)⟩

/-- On a PSD input the negative residual is Hermitian and block positive. Its strict
    separation statement requires nonseparability; the exact negative square does not. -/
theorem separable_cone_residual_witness {R : CompositeMatrix m n} (hR : R.PosSemidef) :
    let P := nearestSeparable R
    let r := R - P
    let W := P - R
    separableCone P ∧ R = P + r ∧ W.IsHermitian ∧ blockPositive W ∧
      pairing P r = 0 ∧
      (∀ S, separableCone S → pairing S r ≤ 0 ∧ 0 ≤ pairing S W) ∧
      pairing R W = -pairing r r ∧ pairing R W = -‖entryEquiv r‖ ^ 2 ∧
      (¬separableCone R → pairing R W < 0) := by
  dsimp only
  let P := nearestSeparable R
  have hP : separableCone P := (nearestSeparable_spec R).1
  have ho : pairing P (R - P) = 0 := (separable_moreau_decomposition R).1.2.2.1
  have hd := (cone_residual_observer_duality (separableProperCone m n) (entryEquiv R)).1
  rw [← nearestSeparable_projection R, ← map_sub, ← map_neg] at hd
  have hW : blockPositive (P - R) := by
    have := (entry_mem_innerDual_iff (-(R - P))).mp hd
    simpa only [neg_sub] using this
  have hsquare : pairing R (P - R) = -pairing (R - P) (R - P) := by
    have he : entryEquiv R = entryEquiv P + entryEquiv (R - P) := by rw [map_sub]; abel
    rw [← entry_inner, show P - R = -(R - P) by abel, map_neg, he, inner_neg_right,
      inner_add_left, entry_inner, entry_inner, ho, zero_add]
  refine ⟨hP, by abel, (separable_isPosSemidef hP).isHermitian.sub hR.isHermitian,
    hW, ho, ?_, hsquare, ?_, ?_⟩
  · intro S hS
    have hnonneg := (blockPositive_iff_forall_separable_pairing_nonneg _).mp hW S hS
    refine ⟨?_, hnonneg⟩
    have hneg : pairing S (P - R) = -pairing S (R - P) := by
      rw [← entry_inner, show P - R = -(R - P) by abel, map_neg, inner_neg_right, entry_inner]
    rw [hneg] at hnonneg
    linarith
  · rw [hsquare, ← entry_inner, real_inner_self_eq_norm_sq]
  · intro hnot
    have hx : entryEquiv R ∉ separableProperCone m n := by simpa using hnot
    have hstrict := (cone_residual_observer_duality (separableProperCone m n) (entryEquiv R)).2 hx
    have h := hstrict.2.2
    rw [← nearestSeparable_projection R, ← map_sub, ← map_neg, entry_inner,
      neg_sub, pairing_symm] at h
    exact h

theorem nearestSeparable_of_separable {R : CompositeMatrix m n} (hR : separableCone R) :
    nearestSeparable R = R := by
  apply Eq.symm
  apply nearestSeparable_unique
  refine ⟨hR, fun Q _ => ?_⟩
  simp only [distanceSq_eq, sub_self, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact sq_nonneg _

/-- The inside-cone branch includes both signs of the residual. -/
theorem separable_zero_residual {R : CompositeMatrix m n} (hR : separableCone R) :
    nearestSeparable R = R ∧ R - nearestSeparable R = 0 ∧ nearestSeparable R - R = 0 := by
  simp [nearestSeparable_of_separable hR]

theorem zero_residual_iff (R : CompositeMatrix m n) :
    R - nearestSeparable R = 0 ↔ separableCone R := by
  constructor
  · intro h
    rw [sub_eq_zero.mp h]
    exact (nearestSeparable_spec R).1
  · intro h
    exact (separable_zero_residual h).2.1

#print axioms entry_inner
#print axioms closed_conic_hull_eq_separable
#print axioms existsUnique_argmin
#print axioms nearestSeparable_projection
#print axioms separable_moreau_decomposition
#print axioms separable_cone_residual_witness
#print axioms zero_residual_iff

end
end D5.S3.Resource.SeparableConeResidualWitness
