/- GID: D5/S3/Zeros/GRH/New/Exchange/RowLadder
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/RowLadder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.RowLadder. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/RowLadder.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.OneSquare
import D5.S3.Zeros.GRH.New.Exchange.CostOfSquares
import D5.S3.Zeros.GRH.New.Exchange.GridMove
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

Part of: Crude rows: integral twisted lifts and bounded conjugates (see New.Exchange.CrudeRows).

This file: The one-square lemma applied to a grid square, constant costing one square. -/

variable {P} {D : Data P} {a b}

/-- For a, b < m, lift-then-descent and descent-then-lift from node (a, b+1) to (a+1, b) of grid
z, as functions of the point data under any functional, satisfy `SquareLaw` with constant
κ/c(ϑ): κ is free of ϑ, and c ≠ 0 costs one square (`Data.CostsSquares`). -/
lemma Data.exists_squareLaw_grid z (h : a < D.m) (m : b < D.m) : ∃ κ σ, ∃ c : _ → ℂˣ, D.CostsSquares
  1 (c ·) ∧ ∀ ϑ (l : _ × (GridForm z (a + 1) b →ₗ[ℂ] ℂ)), SquareLaw (edgeChar ϑ (verticalEdge z a
  b) * edgeChar ϑ (rowEdge z a b))⁻¹ σ (κ / c ϑ) (fun x ↦ l.2 (descentMove x.toCols₂
  (liftMove x.toCols₁ l.1))) fun y ↦ l.2 (liftMove y.toRows₂ (descentMove y.toRows₁ l.1)) := by
  obtain ⟨x, T⟩ := exists_isTameFor_costsSquares_one ⟨_, D.w _ + D.w _, _, D.t, by
    simpa [← zpow_add] using! (D.mu₀_hasWeight a.succ).mul
      (D.mu₀_hasWeight b.succ), by simp_all, by grind, by simp; grind, by simp; grind
    [w_le_two_mul_b]⟩ (D.omega_zpow_ne_one _) D.b₁ ⟨ite z a b + 1, by grind⟩
  have := one_square (D.gridSpace 0 z a b) (gridSpace ..) (gridSpace ..) (gridSpace ..)
    (isEdgeFamily_grid id false rfl) (isEdgeFamily_grid id _ rfl) (isEdgeFamily_grid _ _ rfl)
    (isEdgeFamily_grid _ _ rfl) (Fintype.equivOfCardEq ?_) ?_ D.t ?_ ?_ (by simp; grw
    [card_gridIndex_le, card_gridIndex_le, (D.nat_le_of_hasLogBound : D.n _ ≤ D.h₂)] <;> grind) x ?_
  choose C κ c n hc H using this
  use κ, ?_, (.mk0 _ <| n ·), T hc, fun ϑ l ↦ ?_; swap
  convert! ← H ..; rw [(?_ : _ * _ = _ * _)]
  ext; apply finprod_mul_distrib <;> toFinite_tac
  all_goals clear * -; cases z <;> intros <;> (try apply_fun Additive.ofMul) <;> simp_all [gridChar,
    liftChar, liftTamePart, card_gridIndex, rankTwist, TameChar.pow, twist_one_spec,
    card_neg_gridSigns, show (1 : D.Twist).ψ = 1 by rfl] <;> first | match_scalars <;> grind | grind

/-- A descent moves past a lifts. For a ≤ b < m there are κ and c(ϑ) ≠ 0 costing a squares such
that, if each edge of w avoids grid z or is (i, b) → (i+1, b) with i ≥ a, every tidy Λ of
order n has a tidy Φ of order n + 2a with Λ(path to (a, b)) = (κ/c(ϑ))·Φ(path to (a, b+1),
then descent), under linear functionals reading only w. -/
lemma Data.descent_past_gridPathMap {P} {D : Data P} {a b} (h : b < D.m) z (h' : a ≤ b) : ∃ κ, ∃ c :
    _ → ℂˣ, D.CostsSquares a (c ·) ∧ ∀ ϑ n w Λ,
  (∀ e ∈ w, z ∉ [e.1.1, e.2.1] ∨ ∃ i ≥ a, e = rowEdge z i b) → IsTidy n (w ∪ D.gridPath z a b) Λ →
  ∃ Φ, IsTidy (n + 2 * a) (insert (verticalEdge z a b) (D.gridPath z a (b + 1)) ∪ w) Φ ∧ ∀ F
  (l : EdgeTuple ϑ → _ →ₗ[ℂ] ℂ), DependsOn l w → Λ (fun S ↦ l S (gridPathMap S z a b F)) =
  κ / c ϑ * Φ fun S ↦ l S (descentMove (S (verticalEdge z a b)) (gridPathMap S z a _ F)) := by
  induction' a with a i
  · use 1, 1, .one, fun _ _ w Λ _ C ↦ ⟨Λ, by
      convert! C using 1; simp [gridPath, legEdges]; grind, by simp [gridPathMap,
      legDescents.eq_1 _ z b, h]⟩
  choose κ' c' g' H' using i (by lia)
  choose κ σ c g Q using exists_squareLaw_grid z (h.trans' h') h
  use κ' * κ, c' * c, g'.mul g .refl, fun ϑ n w Λ _ C ↦ ?_
  simp [gridPath, Finset.range_add_one] at C ⊢
  obtain ⟨Φ, C, M⟩ := H' ϑ _ _ Λ (by grind) (w.insert_union .. ▸ C)
  simp [↓Finset.insert_union, gridPath] at C
  refine (C.exists_square_move _ (.refl _) (.sumEmpty ..) (.sumEmpty _ Empty) 1 (Q ϑ) (by
    simp [IsAdmissibleFamily, Units.ext_iff, ← Matrix.ext_iff]; grind)
    (by simp [-Prod.forall]; grind [legEdges])).imp
    fun Φ' ↦ .imp_right fun M' F l hl ↦ (M F (l · ∘ₗ _) (by grind [DependsOn])).trans ?_
  simpa [Fintype.card_congr Matrix.of.symm, ← mul_assoc, div_mul_div_comm] using! congr(κ' / _ *
    $(M' (fun S _ ↦ (gridPathMap S z a _ F, l S)) (by clear * - hl; grind [DependsOn,
    gridPathMap_congr, gridPath])))
