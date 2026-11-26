import OmegaMath.NumberTheory.GRH.Lib.General.Measure.HaarModulus
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Generalised index is invariant under the involution; lattice index is index of the
determinant. -/

variable {A} [CommRing A] {R : Subring A} {n} [Fintype n] {M : Matrix n n A}

lemma IsIntMatrix.det_mem (h : IsIntMatrix R M) : M.det ∈ R :=
  R.subtype.map_det (⟨_, h · ·⟩) ▸ by simp

lemma IsIntMatrix.adjugate (h : IsIntMatrix R M) :
    IsIntMatrix R M.adjugate := R.subtype.map_adjugate (⟨_, h · ·⟩) ▸ by aesop_cat

variable [StarRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [PolishSpace A] [H : IsAdelic R] (a : A) {M : GL n A}

lemma one_le_genIndex {u} (h : u ∈ R) (i : IsUnit u) : 1 ≤ genIndex u := by
  simpa [H.exists_topology.elim genIndex_eq_card, *] using! genIndex_pos i.unit

include R

@[simp] lemma genIndex_star : genIndex (star a) = genIndex a := by
  obtain h | ⟨a, rfl⟩ := em' (IsUnit a); simp [genIndex.map_nonunit, h]
  simp [← Units.coe_star, ← genIndex_eq_inv_distribHaarChar,
    H.exists_topology.elim (inv_distribHaarChar_eq_relIndex_div R.toAddSubgroup)]
  congr 2 <;> rw [← AddSubgroup.relIndex_pointwise_smul (@starRingAut A ..)] <;> congr 1 with <;>
    simp [AddSubgroup.pointwise_smul_def] <;> grind [H.1.1, star_star]

/-- For M in GL_n(A) and L = MRⁿ the lattice spanned by its columns, [Rⁿ : Rⁿ ∩ L]/[L : Rⁿ ∩ L]
equals the generalised index [R : (det M)R], when R ⊂ A satisfies `IsAdelic`. -/
lemma submoduleIndex_colLattice_div : submoduleIndex (colLattice R M.1) (intVectors R n) /
  submoduleIndex (intVectors R n) (colLattice R M.1) = genIndex M.1.det := by cases H; erw
  [← inv_distribHaarChar_eq_relIndex_div _ isOpen_intVectors (isCompact_pi_infinite (by tauto)) M,
  distribHaarChar_GL_eq_det] <;> tauto

lemma submoduleIndex_colLattice_intVectors (h : IsIntMatrix R M.1) :
  submoduleIndex (colLattice R M.1) (intVectors R n) = genIndex M.1.det := by
  rw [← submoduleIndex_colLattice_div, submoduleIndex.eq_1 (intVectors ..),
    AddSubgroup.relIndex_eq_one.2 (colLattice_le (by tauto))]; simp
