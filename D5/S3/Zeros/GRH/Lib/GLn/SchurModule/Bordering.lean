/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Bordering
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/Bordering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.Bordering. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/Bordering.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.Nabla
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

Part of: Weyl character and dimension formulas for U(n) and products of unitary groups (known
result; see Lib.DiscreteSeries.Character.KTypeMultiplicity).

This file: Leading terms in one row, bordering of minors, recursion for alternants. -/

noncomputable section

open MvPolynomial Finset MonomialOrder Finsupp Matrix Fin

namespace PolyRep

variable {Φ J m R ι : Type} [CommRing R] {F δ G : ι → _} {t : Finset ι} {γ} {a : R}

/-- The lexicographic monomial order on variables indexed by ℕ that compares exponents at the
highest index first, so that x₀ ≺ x₁ ≺ …. -/
def columnOrder : MonomialOrder ℕ := @lex ℕᵒᵈ _ _

lemma columnOrder_lt_of_eq_above i δ : (∀ j > i, γ j = δ j) → γ i < δ i → γ ≺[columnOrder] δ :=
  (⟨_, ·, ·⟩)

/-- No monomial of F exceeds x^γ in the order `PolyRep.columnOrder`, and the coefficient of x^γ in F
is G (G = 0 is allowed). -/
abbrev HasLeadingTerm F γ (G : R) := columnOrder.degree F ≼[columnOrder] γ ∧ F.coeff γ = G

lemma HasLeadingTerm.mul {F F' γ' a'} : HasLeadingTerm F γ a → HasLeadingTerm F' γ' a' →
  HasLeadingTerm (F * F') (γ + γ') (a * a') := by
    grind [degree_mul_le, coeff_mul_of_add_of_degree_le]

lemma HasLeadingTerm.of_monomial : HasLeadingTerm (monomial γ a) γ a :=
  ⟨degree_monomial_le _, by simp⟩

lemma HasLeadingTerm.prod (h : ∀ i, HasLeadingTerm (F i) (δ i) (G i : R)) :
  HasLeadingTerm (t.prod F) (t.sum δ) (t.prod G) := t.induction (by bound) (by grind [mul])

lemma HasLeadingTerm.sum (h : ∀ i, HasLeadingTerm (F i) (δ i) (G i : R)) j (H : ∀ i ∈ t, i ≠ j →
  δ i ≺[columnOrder] δ j) (hj : j ∉ t → G j = 0 := by simp) :
  HasLeadingTerm (t.sum F) (δ j) (G j) := by grw [HasLeadingTerm, degree_sum_le,
  coeff_sum, sum_eq_ite j, t.sup_le_iff] <;> grind [coeff_eq_zero_of_lt]

variable [Fintype J] (c : m → Φ) (τ h : J → _) (x : m) (l : ℕ →₀ ℕ)

/-- For a row x, the R-algebra isomorphism writing a polynomial in the y_{a,i} as a polynomial
in the y_{x,i}, i ∈ ℕ, over the polynomials in the other rows. -/
def rowExpansion : MatrixPoly m R ≃ₐ[R] MvPolynomial ℕ (MatrixPoly {a // a ≠ x} R) := (renameEquiv R
  (((Equiv.optionSubtypeNe x).symm.prodCongr 1).trans optionProdEquiv)).trans (sumAlgEquiv ..)

/-- For a finitely supported l : ℕ → ℕ, the finite set of finitely supported γ with γ(i) ≤ l(i)
− l(i+1) for all i, the subtraction truncated at 0. -/
def interlacing := Icc 0 (l - l.comapDomain .succ (by simp))

/-- For finitely many columns j with colour τ_j and height h_j, the weight whose value at (τ,i)
counts the columns of colour τ with height exceeding i. -/
def columnWeight := ∑ j, ∑ i ∈ range (h j), single ((τ j : Φ), i) 1

/-- The type of assignments giving each column j an h_j-tuple of rows, all of colour τ_j. -/
abbrev ColouredTableau := ∀ j, Fin (h j) → {a // c a = τ j}

variable {c τ h x} (S) [CommRing S] (I : ColouredTableau c τ h)

/-- For a coloured column filling I, the polynomial over S that is the product over columns j of
the minor with rows I_j on the first h_j columns. -/
def minorProduct := ∏ j, minor S (I j · |>.1)

attribute [local simp] columnWeight minor Finsupp.le_def sum_range_succ det_apply'
  prod_pow_eq_pow_sum

/-- The weight `diagramWeight` of N and κ equals the weight `PolyRep.columnWeight` of the family
having κ_τ(h) columns of colour τ and height h, for every τ and h < N_τ. -/
lemma diagramWeight_eq_columnWeight [Fintype Φ] N κ : diagramWeight N κ =
  @columnWeight Φ (Σ τ, Σ h : Fin (N τ), Fin (κ τ h)) _ (·.1)
  (·.2.1) := by simp [↓Fintype.sum_sigma, diagramWeight, sum_range]

/-- For an assignment I of h_j rows of colour τ_j to each column j, the product of minors
`PolyRep.minorProduct` of I is a Borel semi-invariant: it lies in `nabla` for the weight
`PolyRep.columnWeight` of τ, h. -/
lemma minorProduct_mem_nabla : minorProduct R I ∈ nabla R c (columnWeight τ h) :=
  SetLike.prod_mem_graded _ _ _ fun _ _ ↦ minor_mem_nabla (by grind)

/-- Bordering: if γ interlaces the columns' weight at x's colour, some heights k have weight
smaller by γ, and each filling I avoiding row x lifts to K, with |γ| more entries x, whose
minor product has leading term y_x^γ times I's over every ring. -/
lemma exists_bordering h (H : γ ∈ interlacing ((columnWeight τ h).curry (c x))) : ∃ k,
  columnWeight τ h = γ.mapDomain (c x, ·) + columnWeight τ k ∧ ∀ I : ColouredTableau (c ∘ (↑)) τ k,
  ∃ K : ColouredTableau c τ h, (∀ R [CommRing R], HasLeadingTerm (rowExpansion x (minorProduct R
  K)) γ (minorProduct R I)) ∧ ∀ y : m → ℂ, ∏ j, ∏ s, y (K j s) = y x ^ degree γ * ∏ j, ∏ s,
  y (I j s) := by
  simp [interlacing, Finsupp.single_apply, sum_ite, ite_and] at H
  choose S _ a using (exists_subset_card_eq <| H · |>.trans (le_card_sdiff ..))
  let e j := ite (∀ i, j ∉ S i) 0 1
  choose k K using fun j ↦ le_iff_exists_add'.1 (by grind : e j ≤ h j)
  cases funext K; cases show γ = ∑ j, single (k j) (e j) by
    ext; simp [← a, card_eq_sum_ones, ← sum_ite_mem_eq]; grind
  use k, by simp [mapDomain_finsetSum, ← sum_add_distrib, e]; congr!; split <;> simp; grind, fun I ↦
    ⟨(⟨if h : _ then I · ⟨·, h⟩ else x, by grind⟩), fun R _ ↦ ?_, by simp [prod_univ_add]; grind⟩
  erw [map_prod]; refine .prod fun j ↦ ?_; dsimp +instances; rcases h : e j with _ | ⟨⟨⟩⟩ <;>
    [convert HasLeadingTerm.of_monomial; convert HasLeadingTerm.sum (t := univ) (fun s ↦
    @.of_monomial (MatrixPoly _ R) _ (single s.1 1) ((-1) ^ (k j + s.1) * det
    (of (X ⟨I j · |>.1, s.succAbove ·⟩)))) (last _) (by grind [columnOrder_lt_of_eq_above (k
    j)]); lia] <;> simp [rowExpansion, (I ..).1.2, ↓det_succ_row' _ (last _), monomial_eq]; ac_rfl

lemma alternant_succ {N} (A : Antitone l) i x : @alternant (N + 1) x l = (-1) ^ i.1 * (∏ a, (x
  (i.succAbove a) - x i)) * ∑ γ ∈ interlacing l,
  x i ^ degree γ * alternant (x ∘ i.succAbove) (l - γ) := by
  have := @A (N + 1); erw [alternant, interlacing, ← det_classical,
    det_eq_of_forall_col_eq_smul_add_pred (B := fun _ ↦ vecCons _ _) _ (by tauto) fun _ _ ↦ by erw
    [← sub_eq_iff_eq_add, mul_comm, ← mul_geom_sum₂_Ico _ (x i)
    (by gcongr <;> first | exact A (by grind) | grind),
    cons_val_succ], det_classical, det_succ_row' _ i, sum_univ_succ, det_mul_column, det_apply']
  simp [alternant, prod_univ_sum, Finset.mul_sum, -val_rev]
  rw [univ.sum_comm, ite_sum_zero, ← sum_filter, ← sum_filter]
  refine' sum_bij' (fun g _ ↦ onFinset (range (N + 1)) (fun n ↦ l n - (List.ofFn ((g - (↑)) ∘
    rev))[n]!) _) (fun γ _ j ↦ (l - γ) j.rev + j) .. <;> simp [degree_eq_weight_one, -val_rev,
    sum_range, weight_apply, le_tsub_iff_left (A _), ← rev_bijective.sum_comp (l · - _)] <;> grind
