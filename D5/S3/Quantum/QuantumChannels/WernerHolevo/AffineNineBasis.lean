/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A pivot coordinate identifies every affine direction and its parallel lines, giving the edge partition and the assembleable finite basis. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.AffineNineAssembly
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Affine classes over a finite field

Removing the pivot coordinate after normalization identifies the lines of
each class with a field element and the remaining coordinates.
-/

open scoped BigOperators
open Module

namespace AffineNine

noncomputable section

/-- The normalized representative of an affine direction, with its first
nonzero coordinate set to one. -/
structure Direction (F : Type*) [Field F] (d : ℕ) where
  pivot : Fin d
  vector : Fin d → F
  at_pivot : vector pivot = 1
  below_pivot : ∀ i, i < pivot → vector i = 0

variable {F G : Type*} [Field F] [AddCommGroup G]

private theorem Direction.ext_data {d : ℕ} {u v : Direction F d}
    (hp : u.pivot = v.pivot) (hv : u.vector = v.vector) : u = v := by
  cases u
  cases v
  cases hp
  cases hv
  rfl

private def Direction.data {d : ℕ} : Direction F d → Fin d × (Fin d → F) :=
  fun u => (u.pivot, u.vector)

instance [Fintype F] (d : ℕ) : Fintype (Direction F d) :=
  Fintype.ofInjective Direction.data
    (fun _ _ h => Direction.ext_data (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Split a vertex into its pivot coordinate and the coordinates of the
representative of its line whose pivot coordinate is zero. -/
def Direction.lineCoords {k : ℕ} (u : Direction F (k + 1)) :
    (Fin (k + 1) → F) ≃ F × (Fin k → F) where
  toFun x := (x u.pivot, fun j =>
    x (u.pivot.succAbove j) - x u.pivot * u.vector (u.pivot.succAbove j))
  invFun p := u.pivot.insertNth p.1 (fun j =>
    p.2 j + p.1 * u.vector (u.pivot.succAbove j))
  left_inv x := by
    funext i
    rcases u.pivot.eq_self_or_eq_succAbove i with rfl | ⟨j, rfl⟩
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      simp

/-- Equality of the quotient coordinates is equivalent to the difference of
the two vertices being the indicated multiple of the direction. -/
theorem Direction.sameLine_iff {k : ℕ} (u : Direction F (k + 1))
    (x y : Fin (k + 1) → F) :
    (u.lineCoords x).2 = (u.lineCoords y).2 ↔
      ∀ i, x i - y i = (x u.pivot - y u.pivot) * u.vector i := by
  constructor
  · intro h i
    rcases u.pivot.eq_self_or_eq_succAbove i with rfl | ⟨j, rfl⟩
    · simp [u.at_pivot]
    · have he := congrFun h j
      change x (u.pivot.succAbove j) - x u.pivot * u.vector (u.pivot.succAbove j) =
        y (u.pivot.succAbove j) - y u.pivot * u.vector (u.pivot.succAbove j) at he
      linear_combination he
  · intro h
    funext j
    change x (u.pivot.succAbove j) - x u.pivot * u.vector (u.pivot.succAbove j) =
      y (u.pivot.succAbove j) - y u.pivot * u.vector (u.pivot.succAbove j)
    linear_combination h (u.pivot.succAbove j)

/-- Distinct points share a line in exactly one direction. -/
theorem Direction.unique_line {k : ℕ} (x y : Fin (k + 1) → F) (hxy : x ≠ y) :
    ∃! u : Direction F (k + 1), (u.lineCoords x).2 = (u.lineCoords y).2 := by
  classical
  let z : Fin (k + 1) → F := fun i => x i - y i
  let support := Finset.univ.filter fun i => z i ≠ 0
  have hs : support.Nonempty := by
    by_contra he
    apply hxy
    funext i
    apply sub_eq_zero.mp
    by_contra hi
    exact he ⟨i, by simp [support, z, hi]⟩
  let p := support.min' hs
  have hp : z p ≠ 0 := by simpa [support] using support.min'_mem hs
  have hbelow (i : Fin (k + 1)) (hi : i < p) : z i = 0 := by
    by_contra hne
    have hm : i ∈ support := by simp [support, hne]
    exact (not_le_of_gt hi) (support.min'_le i hm)
  let u : Direction F (k + 1) :=
    ⟨p, fun i => z i / z p, div_self hp, fun i hi => by rw [hbelow i hi, zero_div]⟩
  refine ⟨u, u.sameLine_iff x y |>.mpr ?_, ?_⟩
  · intro i
    change z i = z p * (z i / z p)
    rw [mul_comm, div_mul_cancel₀ _ hp]
  · intro v hv
    have hvz : ∀ i, z i = z v.pivot * v.vector i := (v.sameLine_iff x y).mp hv
    have hvp : z v.pivot ≠ 0 := by
      intro hzero
      exact hp (by simp [hvz p, hzero])
    have hpv : p ≤ v.pivot := support.min'_le v.pivot (by simp [support, hvp])
    have hvp' : v.pivot ≤ p := by
      by_contra! hlt
      exact hp (by simp [hvz p, v.below_pivot p hlt])
    have he : v.pivot = p := le_antisymm hvp' hpv
    apply Direction.ext_data he
    funext i
    change v.vector i = z i / z p
    apply (eq_div_iff hp).mpr
    simpa [he, mul_comm] using (hvz i).symm

/-- A class uses one block per line, with the quotient coordinates written as
a field element followed by k further coordinates. -/
def affineClasses (F : Type*) [Field F] (k : ℕ) :
    ParallelClasses (Fin (k + 2) → F) (Direction F (k + 2)) F (F × (Fin k → F)) where
  coords u := u.lineCoords.trans ((Equiv.refl F).prodCongr
    (Fin.consEquiv (fun _ : Fin (k + 1) => F)).symm)
  unique_class x y hxy := by
    let e := (Fin.consEquiv (fun _ : Fin (k + 1) => F)).symm
    change ∃! u : Direction F (k + 2), e (u.lineCoords x).2 = e (u.lineCoords y).2
    simpa only [e.injective.eq_iff] using Direction.unique_line x y hxy

/-- Extend the nine-block labeling by half of the additional block index. -/
def EdgeLabeling.extend (L : EdgeLabeling F F G) (h₂ : (2 : F) ≠ 0) (k : ℕ) :
    EdgeLabeling F (F × (Fin k → F)) (G × (Fin k → F)) where
  label b x := (L.label b.1 x, fun j => b.2 j / 2)
  edgeEquiv :=
    (Equiv.prodAssoc F (Fin k → F) (Edge F)).trans
      (((Equiv.refl F).prodCongr (Equiv.prodComm (Fin k → F) (Edge F))).trans
        ((Equiv.prodAssoc F (Edge F) (Fin k → F)).symm.trans
          (L.edgeEquiv.prodCongr (Equiv.refl (Fin k → F)))))
  edgeEquiv_apply b x y h := by
    apply Prod.ext
    · exact L.edgeEquiv_apply b.1 x y h
    · funext j
      change b.2 j = b.2 j / 2 + b.2 j / 2
      rw [← add_div, ← two_mul, mul_comm, mul_div_cancel_right₀ _ h₂]

section Basis

variable [Fintype F] [DecidableEq F] [Fintype G]

abbrev AffineIndex (F G : Type*) [Field F] [AddCommGroup G] (k : ℕ) :=
  Index (Fin (k + 2) → F) (Direction F (k + 2)) (G × (Fin k → F))

/-- The affine symmetric unitary basis in every dimension 9^(k+2) when
instantiated with the supplied nine-element field and local data. -/
def affineBasis (C : FlatHollow F) (L : EdgeLabeling F F G)
    (h₂ : (2 : F) ≠ 0) (k : ℕ) :
    Basis (AffineIndex F G k) ℂ (symmetric (Fin (k + 2) → F)) :=
  assemble C (L.extend h₂ k) (affineClasses F k)

theorem affineBasis_unitary (C : FlatHollow F) (L : EdgeLabeling F F G)
    (h₂ : (2 : F) ≠ 0) (k : ℕ) (i : AffineIndex F G k) :
    (affineBasis C L h₂ k i : Matrix (Fin (k + 2) → F) (Fin (k + 2) → F) ℂ) ∈
      Matrix.unitaryGroup (Fin (k + 2) → F) ℂ := by
  rw [affineBasis, assemble_apply]
  exact family_unitary C _ _ i

open scoped Classical in
theorem affineBasis_hs (C : FlatHollow F) (L : EdgeLabeling F F G)
    (h₂ : (2 : F) ≠ 0) (h₉ : Fintype.card F = 9) (k : ℕ)
    (i j : AffineIndex F G k) :
    hs (affineBasis C L h₂ k i : Matrix (Fin (k + 2) → F) (Fin (k + 2) → F) ℂ)
      (affineBasis C L h₂ k j : Matrix (Fin (k + 2) → F) (Fin (k + 2) → F) ℂ) =
      if i = j then ((9 ^ (k + 2) : ℕ) : ℂ) else 0 := by
  classical
  rw [affineBasis, assemble_apply, assemble_apply, family_hs]
  simp [h₉]

theorem affineBasis_card (L : EdgeLabeling F F G) (h₂ : (2 : F) ≠ 0)
    (h₉ : Fintype.card F = 9) (k : ℕ) :
    Fintype.card (AffineIndex F G k) = (9 ^ (k + 2) + 1).choose 2 := by
  simpa [Fintype.card_fun, h₉] using (affineClasses F k).card_index (L.extend h₂ k)

private def symmetricReindex {X Y : Type*} (e : Y ≃ X) :
    symmetric X ≃ₗ[ℂ] symmetric Y where
  toFun A := ⟨A.1.submatrix e e, Matrix.IsSymm.ext fun i j => A.2.apply (e i) (e j)⟩
  invFun A := ⟨A.1.submatrix e.symm e.symm,
    Matrix.IsSymm.ext fun i j => A.2.apply (e.symm i) (e.symm j)⟩
  left_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  right_inv A := Subtype.ext (Matrix.ext fun i j => by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem hs_reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : Y ≃ X)
    (A B : Matrix X X ℂ) : hs (A.submatrix e e) (B.submatrix e e) = hs A B := by
  unfold hs
  apply Fintype.sum_equiv e
  intro i
  exact Fintype.sum_equiv e _ _ fun _ => rfl

open scoped Classical in
/-- For every exponent d ≥ 2, the symmetric matrices of order 9^d have an
orthogonal basis consisting of unitary matrices. Both index sets are explicit
finite ordinals. -/
theorem exists_affineBasis (C : FlatHollow F) (L : EdgeLabeling F F G)
    (h₂ : (2 : F) ≠ 0) (h₉ : Fintype.card F = 9) (d : ℕ) (hd : 2 ≤ d) :
    ∃ b : Basis (Fin ((9 ^ d + 1).choose 2)) ℂ (symmetric (Fin (9 ^ d))),
      (∀ i, (b i : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ) ∈
        Matrix.unitaryGroup (Fin (9 ^ d)) ℂ) ∧
      ∀ i j, hs (b i : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ)
        (b j : Matrix (Fin (9 ^ d)) (Fin (9 ^ d)) ℂ) =
        if i = j then ((9 ^ d : ℕ) : ℂ) else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 2 := ⟨d - 2, by omega⟩
  let e : (Fin (k + 2) → F) ≃ Fin (9 ^ (k + 2)) :=
    Fintype.equivFinOfCardEq (by simp [h₉])
  let eIndex := Fintype.equivFinOfCardEq (affineBasis_card L h₂ h₉ k)
  refine ⟨((affineBasis C L h₂ k).map (symmetricReindex e.symm)).reindex eIndex, ?_, ?_⟩
  · intro i
    rw [Basis.reindex_apply, Basis.map_apply]
    change (↑(affineBasis C L h₂ k (eIndex.symm i)) : Matrix _ _ ℂ).submatrix e.symm e.symm ∈ _
    rw [Matrix.submatrix_equiv_mem_unitary]
    exact affineBasis_unitary C L h₂ k _
  · intro i j
    rw [Basis.reindex_apply, Basis.reindex_apply, Basis.map_apply, Basis.map_apply]
    change hs ((↑(affineBasis C L h₂ k (eIndex.symm i)) : Matrix _ _ ℂ).submatrix e.symm e.symm)
      ((↑(affineBasis C L h₂ k (eIndex.symm j)) : Matrix _ _ ℂ).submatrix e.symm e.symm) = _
    rw [hs_reindex, affineBasis_hs C L h₂ h₉]
    simp

end Basis

end
end AffineNine
