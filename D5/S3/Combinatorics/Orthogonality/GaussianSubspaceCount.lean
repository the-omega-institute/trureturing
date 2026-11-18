/- GID: D5/S3/Combinatorics/Orthogonality/GaussianSubspaceCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/GaussianSubspaceCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card]
   utility: none
   digest: Gaussian-binomial enumeration of the actual binary submodule lattice. -/

import D5.S3.Combinatorics.Orthogonality.NikandishClique
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Orthogonality.GaussianSubspaceCount

open Module
open D5.S3.Combinatorics.Orthogonality.NikandishClique

/-- The usual Gaussian binomial at q=2, as a quotient of the ordered-frame
counts. The denominator counts bases of the d-dimensional binary space. -/
def gaussian (n d : ℕ) : ℕ :=
  (∏ i : Fin d, (2 ^ n - 2 ^ i.val)) / (∏ i : Fin d, (2 ^ d - 2 ^ i.val))

private theorem frame_span {n d : ℕ}
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hd : finrank (ZMod 2) U = d)
    (s : Fin d → U) (hs : LinearIndependent (ZMod 2) s) :
    Submodule.span (ZMod 2) (Set.range (fun i => (s i : Fin n → ZMod 2))) = U := by
  apply (Submodule.span_range_subtype_eq_top_iff U (fun i => (s i).2)).mp
  exact hs.span_eq_top_of_card_eq_finrank' (by simpa using hd.symm)

/-- Count all ordered independent d-frames by their actual span. This is the
missing fiber decomposition behind the Gaussian coefficient, rather than a
cardinality of subspaces introduced as a new name for that coefficient. -/
private theorem frame_count (n d : ℕ) (hd : d ≤ n) :
    Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) // finrank (ZMod 2) U = d} *
      (∏ i : Fin d, (2 ^ d - 2 ^ i.val)) =
      ∏ i : Fin d, (2 ^ n - 2 ^ i.val) := by
  classical
  let V := Fin n → ZMod 2
  let S := {U : Submodule (ZMod 2) V // finrank (ZMod 2) U = d}
  let F (U : S) := {s : Fin d → U.1 // LinearIndependent (ZMod 2) s}
  letI : Fintype S := Fintype.ofFinite S
  let f : (Σ U : S, F U) → {s : Fin d → V // LinearIndependent (ZMod 2) s} :=
    fun z => ⟨fun i => (z.2.1 i : V), z.2.2.map' z.1.1.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨U, s⟩ ⟨W, t⟩ h
      have he : (fun i => (s.1 i : V)) = (fun i => (t.1 i : V)) :=
        congrArg Subtype.val h
      have hUW : U = W := by
        apply Subtype.ext
        calc
          U.1 = Submodule.span (ZMod 2) (Set.range (fun i => (s.1 i : V))) :=
            (frame_span U.1 U.2 s.1 s.2).symm
          _ = Submodule.span (ZMod 2) (Set.range (fun i => (t.1 i : V))) := by rw [he]
          _ = W.1 := frame_span W.1 W.2 t.1 t.2
      subst W
      apply congrArg (Sigma.mk U)
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrFun he i)
    · intro s
      let U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (Set.range s.1)
      have hr : finrank (ZMod 2) U = d := by
        simpa using finrank_span_eq_card s.2
      let t : Fin d → U := fun i => ⟨s.1 i, Submodule.subset_span (Set.mem_range_self i)⟩
      exact ⟨⟨⟨U, hr⟩, ⟨t, s.2.codRestrict U (fun i =>
        Submodule.subset_span (Set.mem_range_self i))⟩⟩, Subtype.ext rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  have hF (U : S) : Nat.card (F U) = ∏ i : Fin d, (2 ^ d - 2 ^ i.val) := by
    have h := card_linearIndependent (K := ZMod 2) (V := U.1)
      (k := d) (by rw [U.2])
    simpa only [ZMod.card, U.2] using h
  rw [Nat.card_sigma] at hc
  simp_rw [hF] at hc
  have ha := card_linearIndependent (K := ZMod 2) (V := V) (k := d)
    (by simpa [V] using hd)
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ZMod.card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, V, S, Nat.card_fin, Nat.card_zmod] using hc.trans ha

private theorem basis_count_pos (d : ℕ) :
    0 < ∏ i : Fin d, (2 ^ d - 2 ^ i.val) := by
  apply Finset.prod_pos
  intro i _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by decide) i.isLt)

/-- Every d-dimensional submodule of the binary n-space is counted once by
its independent frames, with the full basis fiber divided out. -/
theorem dimension_card (n d : ℕ) (hd : d ≤ n) :
    Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) // finrank (ZMod 2) U = d} =
      gaussian n d := by
  exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt (basis_count_pos d))
    (frame_count n d hd)

/-- The original complete nonzero-subspace invariant equals the displayed
sum of Gaussian binomials, including N(0)=0. -/
theorem result (n : ℕ) :
    nonzeroSubspaceCount n = ∑ d ∈ Finset.Icc 1 n, gaussian n d := by
  classical
  let S (d : ↥(Finset.Icc 1 n)) :=
    {U : Submodule (ZMod 2) (Fin n → ZMod 2) // finrank (ZMod 2) U = d.1}
  let f : (Σ d : ↥(Finset.Icc 1 n), S d) → Vertex n := fun z =>
    ⟨z.2.1, Submodule.one_le_finrank_iff.mp (by
      rw [z.2.2]
      exact (Finset.mem_Icc.mp z.1.2).1)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨d, U⟩ ⟨e, W⟩ h
      have hUW : U.1 = W.1 := congrArg Subtype.val h
      have hde : d = e := Subtype.ext (U.2.symm.trans ((congrArg
        (fun P : Submodule (ZMod 2) (Fin n → ZMod 2) => finrank (ZMod 2) P) hUW).trans W.2))
      subst e
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hUW))
    · intro U
      have hl : 1 ≤ finrank (ZMod 2) U.1 := Submodule.one_le_finrank_iff.mpr U.2
      have hu : finrank (ZMod 2) U.1 ≤ n := by
        simpa using Submodule.finrank_le U.1
      exact ⟨⟨⟨finrank (ZMod 2) U.1, Finset.mem_Icc.mpr ⟨hl, hu⟩⟩,
        ⟨U.1, rfl⟩⟩, Subtype.ext rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma] at hc
  simp_rw [S, dimension_card n _ (Finset.mem_Icc.mp (Subtype.property _)).2] at hc
  change (∑ d : ↥(Finset.Icc 1 n), gaussian n d.1) = nonzeroSubspaceCount n at hc
  simpa only [Finset.sum_coe_sort] using hc.symm

#print axioms dimension_card
#print axioms result

end D5.S3.Combinatorics.Orthogonality.GaussianSubspaceCount
