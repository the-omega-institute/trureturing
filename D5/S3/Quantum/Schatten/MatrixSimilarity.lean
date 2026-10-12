/- GID: D5/S3/Quantum/Schatten/MatrixSimilarity
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/MatrixSimilarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral permutation under unitary similarity. -/

/-
Attributed source: leanprover-community/physlib, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Original modules: QuantumInfo/ForMathlib/Matrix.lean and Misc.lean.
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Retire this transplant when an equivalent consumed declaration exists in the
repository-pinned Mathlib, replacing it by direct application.
No mathematical originality is claimed for the attributed source.
-/
module

public import Mathlib

@[expose] public section

/--
If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions.
-/
lemma Multiset.map_univ_eq_iff {α β : Type*} [Fintype α] (f g : α → β) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val ↔ ∃ (e : α ≃ α), f = g ∘ e := by
  apply Iff.intro
  · intro a
    classical
    -- Since these two multisets are equal, their elements must be equal up to permutation.
    have h_perm : ∃ e : α ≃ α, ∀ x, f x = g (e x) := by
      have h_count_eq : ∀ y : β, Finset.card (Finset.filter (fun x => f x = y) Finset.univ) = Finset.card (Finset.filter (fun x => g x = y) Finset.univ) := by
        intro y;
        replace a := congr_arg ( fun m => m.count y ) a;
        simp_all ( config := { decide := Bool.true } ) [ Multiset.count_map ];
        simp_all [ eq_comm ]
        exact a
      have h_perm : ∀ y : β, ∃ e : { x : α // f x = y } ≃ { x : α // g x = y }, True := by
        intro y
        simp_all only [exists_const_iff, and_true]
        exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_count_eq y ⟩;
      choose e he using h_perm;
      refine' ⟨ _, _ ⟩;
      exact ( Equiv.sigmaFiberEquiv f ).symm.trans ( Equiv.sigmaCongrRight e ) |> Equiv.trans <| Equiv.sigmaFiberEquiv g;
      intro x
      specialize e ( f x )
      rename_i e_1
      simp_all only [implies_true, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Equiv.sigmaFiberEquiv_apply]
      exact Eq.symm ( e_1 ( f x ) ⟨ x, rfl ⟩ |>.2 );
    exact ⟨ h_perm.choose, funext h_perm.choose_spec ⟩;
  · intro a
    obtain ⟨w, h⟩ := a
    subst h
    simp_all only [Function.comp_apply, Finset.univ]
    -- Since $w$ is a bijection, the multiset of $w(x)$ for $x$ in the original multiset is just a permutation of the original multiset.
    have h_perm : Multiset.map (fun x => w x) (Finset.val Fintype.elems) = Finset.val Fintype.elems := by
      exact Multiset.map_univ_val_equiv w;
    conv_rhs => rw [ ← h_perm ];
    simp +zetaDelta at *

namespace Matrix

set_option maxHeartbeats 0 in
--Should be combined the above...? TODO Cleanup
/--
If a Hermitian matrix A is unitarily similar to a diagonal matrix with real entries f, then the eigenvalues of A are a permutation of f.
-/
lemma IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal {d 𝕜 : Type*}
    [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.IsHermitian)
    {U : Matrix d d 𝕜} (hU : U ∈ Matrix.unitaryGroup d 𝕜)
    {f : d → ℝ}
    (h : A = U * Matrix.diagonal (fun i => (RCLike.ofReal (f i) : 𝕜)) * Matrix.conjTranspose U) :
    ∃ σ : d ≃ d, hA.eigenvalues ∘ σ = f := by
  -- Since A is unitarily similar to D, they have the same characteristic polynomial.
  have h_char_poly : Matrix.charpoly A = Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜)) := by
    have h_char_poly : Matrix.charpoly (U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.charpoly (Matrix.diagonal (fun i => (f i : 𝕜))) := by
      have h_det : ∀ (t : 𝕜), Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) := by
        intro t
        have h_det : Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (U * (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) * Uᴴ) := by
          simp [ mul_sub, sub_mul, Matrix.mul_assoc ];
          rw [ show U * Uᴴ = 1 from by exact hU.2 ];
        rw [h_det, Matrix.det_mul_comm, ← mul_assoc]
        rw [← star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self ⟨U, hU⟩]
        simp
      refine' Polynomial.funext fun t => _;
      convert h_det t using 1 <;> simp [ Matrix.charpoly, Matrix.det_apply' ];
      · simp [ Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
      · simp [ Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
    rw [ h, h_char_poly ];
  -- The roots of the characteristic polynomial of A are its eigenvalues (by `IsHermitian.charpoly_roots_eq_eigenvalues`).
  have h_eigenvalues : (Matrix.charpoly A).roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
    exact Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hA;
  -- The roots of the characteristic polynomial of D are the diagonal entries f.
  have h_diag_roots : (Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜))).roots = Multiset.map (fun i => (f i : 𝕜)) Finset.univ.val := by
    simp [ Matrix.charpoly, Matrix.det_diagonal ];
    rw [ Polynomial.roots_prod ];
    · aesop;
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _;
  have := Multiset.map_univ_eq_iff ( RCLike.ofReal ∘ hA.eigenvalues ) f
  subst h
  simp_all only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, CompTriple.comp_eq]
  refine' this.mp _ |> fun ⟨ e, he ⟩ => ⟨ e.symm, _ ⟩
  · simpa [ Function.comp ] using congr_arg ( Multiset.map ( RCLike.re : 𝕜 → ℝ ) ) h_eigenvalues.symm
  · exact funext fun x => by simpa using congr_fun he ( e.symm x ) ;


end Matrix
