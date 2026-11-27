/- GID: D5/S3/Zeros/GRH/Lib/General/Groups/ResidualIrreducibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Groups/ResidualIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Groups.ResidualIrreducibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Groups/ResidualIrreducibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.Valuation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of group theory (textbook or folklore).

This file: Tame pair with residually distinct conjugate eigenvalues spans all matrices of a
lattice. -/

open Matrix IsLocalRing Fintype Module Submodule Set End

/-- Let u be an O-lattice for R of rank n, R(γ^q) = R(φ⁻¹γφ), R(γ^{qⁿ}) = R(γ), and ζ ∈ O an
eigenvalue of R(γ) with ζ^{q^i} (i < n) residually distinct. Then u(G) spans all matrices
over O and u(φ^{−n}) is scalar. -/
lemma IsLatticeIn.span_eq_top_of_tame_pair {G n} [Group G] [Fintype n] {γ φ q ℓ} [ThePrime ℓ] {O :
  CoeffRing ℓ} {R} {u : G →* Matrix n n O} {ζ : ↑O} (h : IsLatticeIn R u) (hφ : R γ ^ q =
  R (φ⁻¹ * γ * φ)) (hq : ∀ i < card n,
  ∀ j < card n, i ≠ j → ‖ζ.1 ^ q ^ i - ζ ^ q ^ j‖ = 1) (hζ : (R γ).1.charpoly.IsRoot ζ) (hγ : R (γ ^
  q ^ card n) = R γ) : Submodule.span O (range u) = ⊤ ∧ ∃ α : ↑O, u (φ⁻¹ ^ card n) = α • 1 := by
  have U {a b} (e : _ = R b) := map_injective (by simp) (h.choose_spec a ▸ e ▸ h.choose_spec b)
  let τ := (toLinAlgEquiv'.toRingHom.comp (residue _).mapMatrix).1.comp u
  obtain ⟨I, v, hv⟩ := iterate_injective (Representation.apply_bijective τ φ).1,
    ((hasEigenvalue_iff_isRoot_charpoly (τ γ) _).2 (by
    erw [charpoly_toLin', charpoly_map]
    exact .map (.of_map (h.charpoly_eq_map γ ▸ hζ) (by simp)))).exists_hasEigenvector
  have S k : R (γ * φ ^ k) = R (φ ^ k * γ ^ q ^ k) := by
    induction k <;> simp_all [pow_succ, pow_mul', ← mul_assoc, inv_inv (R φ) ▸ conj_pow]
  have he j : HasEigenvector .. := ⟨by simpa [hv.pow_apply] using (congr(.map $(U (S j))
    _ *ᵥ v) : τ _ v = τ _ v), by simp [I, hv.2]⟩
  specialize S (card n)
  refine (fun H ↦ ⟨eq_top_mono (span_mono (by grind)) H, by simpa [eq_comm,
    smul_one_eq_diagonal] using (centralizer_subset H.ge (Commute.span_left fun _ ⟨_, e⟩ ↦ e ▸ by
    simpa [commute_iff_eq, ← map_mul] using U (by simp_all [← commute_iff_eq, Commute.pow_pow])))⟩)
    (((stdBasis ..).reindex ((equivFin n).prodCongr (equivFin _))).is_basis_iff_det (v := u ∘
    Prod.rec (φ ^ ·.1 * γ ^ ·.1)).2 (.of_map _ _ (((residue _).map_det _).substr (.map detMonoidHom
    (linearIndependent_col_iff_isUnit.1 <| linearIndependent_iff.2 fun c H (a, b) ↦ congrFun
    (eq_zero_of_forall_index_sum_mul_pow_eq_zero ?i fun l ↦ linearIndependent_iff.1
    (eigenvectors_linearIndependent' _ _ ?i _ (he ·)) (∑ k, c ⟨·, k⟩ * _ ^ k.1) (I l ?_) a) b))))).2
  exact .of_lt_imp_ne (by simp_all [← sub_ne_zero, ← map_pow, ← map_sub, O.isUnit_iff_norm_eq_one,
    ne_of_lt])
  simpa [sum_prod_type, Finset.sum_smul, mul_smul, (he l).pow_apply, ← mul_apply (_ ^ l.1),
    pow_mul_comm _ l] using congr($(((by ext; simpa [τ] using! congr($H (equivFin _ _,
    equivFin _ _)) : ∑ p, c p • τ _ = 0) :)) ((τ φ ^ l.1) v))
