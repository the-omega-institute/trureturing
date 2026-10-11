/- GID: D5/S3/Quantum/SpinChains/NilpotentBlockCounts
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/NilpotentBlockCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Intrinsic nilpotent block counts are determined by iterate ranks. -/

import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace D5.S3.Quantum.SpinChains.NilpotentBlockCounts

open Module

/-- The intrinsic subspace of vectors in the kernel of `N` that come from the
range of the preceding power. -/
def C {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V) (j : ℕ) : Submodule K V :=
  LinearMap.ker N ⊓ LinearMap.range (N ^ (j - 1))

/-- The number of blocks of length `j`, as the dimension of the successive
quotient of the intrinsic subspaces. -/
noncomputable def blockCount {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (N : Module.End K V) (j : ℕ) [FiniteDimensional K V] : ℕ :=
  Module.finrank K (C N j ⧸ (C N (j + 1)).comap (C N j).subtype)

/-- The dimension identity obtained from the map `N` on the preceding range. -/
theorem blockCount_rank_formula
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (N : Module.End K V) {j : ℕ} (hj : 1 ≤ j) :
    (blockCount N j : ℤ) =
      (Module.finrank K (LinearMap.range (N ^ (j - 1))) : ℤ) -
        2 * (Module.finrank K (LinearMap.range (N ^ j)) : ℤ) +
          (Module.finrank K (LinearMap.range (N ^ (j + 1))) : ℤ) := by
  have hpow : LinearMap.range (N ^ j) ≤ LinearMap.range (N ^ (j - 1)) := by
    calc
      LinearMap.range (N ^ j) = LinearMap.range ((N ^ (j - 1)).comp N) := by
        rw [← Module.End.iterate_succ (j - 1), Nat.sub_add_cancel hj]
      _ ≤ LinearMap.range (N ^ (j - 1)) := LinearMap.range_comp_le_range _ _
  have hCmono : C N (j + 1) ≤ C N j := by
    simpa [C] using (inf_le_inf_left (LinearMap.ker N) hpow)
  have dim_identity (m : ℕ) (hm : 1 ≤ m) :
      Module.finrank K (C N m) +
          Module.finrank K (LinearMap.range (N ^ m)) =
        Module.finrank K (LinearMap.range (N ^ (m - 1))) := by
    let S : Submodule K V := LinearMap.range (N ^ (m - 1))
    let f : S →ₗ[K] V := N.domRestrict S
    have hrange : LinearMap.range f = LinearMap.range (N ^ m) := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        rcases x with ⟨x, hx⟩
        rcases hx with ⟨z, rfl⟩
        refine ⟨z, ?_⟩
        change (N ^ m) z = N ((N ^ (m - 1)) z)
        calc
          (N ^ m) z = (N ^ (m - 1 + 1)) z := by rw [Nat.sub_add_cancel hm]
          _ = (N.comp (N ^ (m - 1))) z := by rw [Module.End.iterate_succ']
          _ = N ((N ^ (m - 1)) z) := rfl
      · rintro y ⟨z, rfl⟩
        refine ⟨⟨(N ^ (m - 1)) z, ⟨z, rfl⟩⟩, ?_⟩
        change N ((N ^ (m - 1)) z) = (N ^ m) z
        calc
          N ((N ^ (m - 1)) z) = (N.comp (N ^ (m - 1))) z := rfl
          _ = (N ^ (m - 1 + 1)) z := by rw [Module.End.iterate_succ']
          _ = (N ^ m) z := by rw [Nat.sub_add_cancel hm]
    have hker : LinearMap.ker f = (LinearMap.ker N).comap S.subtype := by
      ext x
      simp [f, LinearMap.mem_ker]
    have hkdim : Module.finrank K (LinearMap.ker f) = Module.finrank K (C N m) := by
      calc
        Module.finrank K (LinearMap.ker f) =
            Module.finrank K ((LinearMap.ker N).comap S.subtype) := by rw [hker]
        _ = Module.finrank K (((LinearMap.ker N).comap S.subtype).map S.subtype) :=
          (Submodule.equivSubtypeMap S ((LinearMap.ker N).comap S.subtype)).finrank_eq
        _ = Module.finrank K (C N m) := by
          rw [Submodule.map_comap_subtype]
          have hsub : S ⊓ LinearMap.ker N = C N m := by
            simp [C, S, inf_comm]
          rw [hsub]
    calc
      Module.finrank K (C N m) + Module.finrank K (LinearMap.range (N ^ m)) =
          Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.range f) := by
            rw [hkdim, hrange]
      _ = Module.finrank K S := by
        simpa [add_comm] using LinearMap.finrank_range_add_finrank_ker f
      _ = Module.finrank K (LinearMap.range (N ^ (m - 1))) := rfl
  have hquotNat : blockCount N j + Module.finrank K (C N (j + 1)) =
      Module.finrank K (C N j) := by
    have hq := Submodule.finrank_quotient_add_finrank
      ((C N (j + 1)).comap (C N j).subtype)
    have hcomap : Module.finrank K ((C N (j + 1)).comap (C N j).subtype) =
        Module.finrank K (C N (j + 1)) :=
      (Submodule.comapSubtypeEquivOfLe hCmono).finrank_eq
    simpa [blockCount, hcomap] using hq
  have hqZ : (blockCount N j : ℤ) + (Module.finrank K (C N (j + 1)) : ℤ) =
      (Module.finrank K (C N j) : ℤ) := by
    exact_mod_cast hquotNat
  have hdimj := dim_identity j hj
  have hdimnext := dim_identity (j + 1) (by omega)
  have hdimjZ : (Module.finrank K (C N j) : ℤ) +
      (Module.finrank K (LinearMap.range (N ^ j)) : ℤ) =
        (Module.finrank K (LinearMap.range (N ^ (j - 1))) : ℤ) := by
    exact_mod_cast hdimj
  have hdimnextZ : (Module.finrank K (C N (j + 1)) : ℤ) +
      (Module.finrank K (LinearMap.range (N ^ (j + 1))) : ℤ) =
        (Module.finrank K (LinearMap.range (N ^ j)) : ℤ) := by
    exact_mod_cast hdimnext
  linarith

/-- Equal dimensions of all powers imply equal intrinsic block counts. -/
theorem blockCount_eq_of_range_finrank_eq
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (N : Module.End K V) (N' : Module.End K W)
    (hρ : ∀ r : ℕ,
      Module.finrank K (LinearMap.range (N ^ r)) =
        Module.finrank K (LinearMap.range (N' ^ r))) :
    ∀ j : ℕ, blockCount N j = blockCount N' j := by
  have hzeroN : Module.finrank K (C N 1 ⧸ (C N 1).comap (C N 1).subtype) = 0 := by
    have hq := Submodule.finrank_quotient_add_finrank ((C N 1).comap (C N 1).subtype)
    rw [Submodule.comap_subtype_self, finrank_top] at hq
    have hz : Module.finrank K (C N 1 ⧸ (⊤ : Submodule K (C N 1))) = 0 := by omega
    rw [Submodule.comap_subtype_self]
    exact hz
  have hzeroN' : Module.finrank K (C N' 1 ⧸ (C N' 1).comap (C N' 1).subtype) = 0 := by
    have hq := Submodule.finrank_quotient_add_finrank ((C N' 1).comap (C N' 1).subtype)
    rw [Submodule.comap_subtype_self, finrank_top] at hq
    have hz : Module.finrank K (C N' 1 ⧸ (⊤ : Submodule K (C N' 1))) = 0 := by omega
    rw [Submodule.comap_subtype_self]
    exact hz
  intro j
  by_cases hj : j = 0
  · subst j
    have hC0 : C N 0 = C N 1 := by simp [C]
    have hC0' : C N' 0 = C N' 1 := by simp [C]
    change Module.finrank K (C N 0 ⧸ (C N 1).comap (C N 0).subtype) =
      Module.finrank K (C N' 0 ⧸ (C N' 1).comap (C N' 0).subtype)
    rw [hC0, hC0']
    exact hzeroN.trans hzeroN'.symm
  · have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have hN := blockCount_rank_formula N hj'
    have hN' := blockCount_rank_formula N' hj'
    have hcast : (blockCount N j : ℤ) = (blockCount N' j : ℤ) := by
      rw [hN, hN']
      simp [hρ]
    exact_mod_cast hcast

#print axioms blockCount_rank_formula
#print axioms blockCount_eq_of_range_finrank_eq

end D5.S3.Quantum.SpinChains.NilpotentBlockCounts
