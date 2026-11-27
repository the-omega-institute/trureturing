/- GID: D5/S3/Zeros/GRH/New/Exchange/SteepParameters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/SteepParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.SteepParameters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/SteepParameters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.DiscreteSeries.RestrictionLemma
import D5.S3.Zeros.GRH.New.Trace.GoodIdempotent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: The chosen parameters satisfy the steepness hypothesis of the Laplace-method lemma. -/

local grind_pattern Data.w_add_gap_le => D.w a τ, D.w b τ

/-- For either grid z, one ordering e of the indices gives the signs and parameter of the node
(0, 0), offset 0, the shape `IsSteep` with bound w₀(τ) = `Data.w` 0 τ at every
infinite place τ. -/
lemma Data.exists_isSteep {P} (D : Data P) z : ∃ e : D.InitIndex 0 ⊕ Fin (2 * D.ϱ + 2 + z.toNat) ≃
  _, ∀ τ, IsSteep (D.gridParam z 0 0 0 τ) (D.w 0 τ) e := by
  let ν : D.GridIndex z 0 0 ≃ _ := D.gridNumber z
  use finSumFinEquiv.trans ((finCongr (by grind [n])).trans ν.symm), fun τ ↦ ?_
  have p x : D.gridSigns z 0 0 0 x = entrySign 0 0 (ν x + 1 - D.k) ∧ D.gridParam z 0 0 0 τ x =
    2 * D.rowParameter τ (ν x) + z.toNat := by cases z <;> aesop
  have : D.w D.h τ ≤ 2 * D.w 0 τ := by grind [(D.nat_le_of_hasLogBound : D.h ^ 2 ≤ D.w 0 τ)]
  have g
    y : let L := 2 * D.rowParameter τ (ν y) + z.toNat - 2 * (D.gridParam z 0 0 0 τ).lowestKType y
    let N := D.r + z.toNat; |L| ≤ N ∧
    (ν y + 1 < D.k → L + N = ↑(N + N ⊓ D.k - 1 - 2 * ν y - (N - D.k) % 2)) := by
    simp_rw [two_mul_lowestKType (hasGap_gridParam ..), twoRho, Finset.card_filter,
      reindex_equiv ν.symm, p, ν.apply_symm_apply, entrySign_eq]; generalize (ν y).1 = a
    induction D.r + _ <;> simp [Finset.univ_eq_empty, ↓Fin.sum_univ_castSucc,
      eq_ite_iff] at *; grind (splits:=20) [rowParameter]
  constructor <;> simp [StrictAnti, neg_one_pow_eq_ite] <;> norm_cast <;> grind [rowParameter, Bool,
    entrySign_eq]
