/- GID: D5/S3/Zeros/GRH/New/Exchange/GridParameters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/GridParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.GridParameters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/GridParameters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.IndexTypes
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Edge
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Index sets, signs, parameters of grids and triangles; gaps, interlacing and
matching. -/

noncomputable section

namespace Data

open Fintype Function Finset BlockIndex
variable {j : ℕ} {P} (D : Data P) (z : Bool) (o i : ℕ) (τ : D.Φ)

/-- The index set of the node (i, j): of V_{i,j}, rank r + (i+j)t, for z false; of Z_{j,i}, rank
r + 1 + i(t+1) + j(t−1), for z true. -/
protected def GridIndex j := BlockIndex (BlockIndex (BlockIndex D.RowIndex Unit z.toNat)
  (Fin (D.t + z.toNat)) i) (Fin (D.t - z.toNat)) j deriving Fintype

/-- The numbering of the base index set by natural numbers: the given numbering on R, and r for
the extra point. -/
def gridNumber : BlockIndex D.RowIndex Unit z.toNat ≃ Fin (D.r + z.toNat) :=
  z.rec D.basisNumber ((D.basisNumber.sumCongr finOneEquiv.symm).trans finSumFinEquiv)

/-- A bijection listing the indices of node (i, j) of grid z: r + z base indices, i blocks of
size t + z, j blocks of size t − z (z = 0 or 1). -/
def gridBlockEquiv {z i} := show D.GridIndex z i j ≃ _ from equivSum (equivSum (D.gridNumber z) i) j

/-- The sign `Data.entrySign` at (o, j, a) is −1 if o + a + min(a − o, j) is odd and 1 otherwise,
with truncated subtraction of natural numbers. -/
lemma entrySign_eq j a : entrySign o j a = ite ((o + a + min (a - o) j) % 2 = 1) (-1) 1 := by
  fun_induction entrySign <;> grind [neg_neg, neg_one_pow_eq_ite]

/-- The signs at node (i, j) of grid z with offset o: `Data.entrySign` o j on the r (in Z, r+1)
base indices, and +1 on all added blocks. -/
def gridSigns j (x : D.GridIndex z i j) :=
  (D.gridBlockEquiv x).elim (Sum.elim (entrySign o j <| ·.1 + 1 - D.k) 1) 1

/-- Doubled parameter at node (i, j), offset o. V: ς, blocks at w_l (l ≤ i), −w_{o+l} (l ≤ j),
lowered by ½ if i+j is odd. Z: ς + ½, blocks at w_l, −w_{o+l}. Here ς = `Data.rowParameter`,
w = `Data.w`. -/
def gridParam j (τ : D.Φ) : HCParam (D.gridSigns z o i j) := fun x ↦
  let y := (D.gridBlockEquiv x).elim (Sum.elim (2 * D.rowParameter τ ·.1) fun (l, b) ↦ 2 * D.w
    (l + 1) τ + D.t - 1 - 2 * b) fun (l, b) ↦ D.t - 1 - 2 * (D.w (l + 1 + o) τ + z.toNat) - 2 * b
  bif z then y + 1 else ite ((j + i) % 2 = 1) (y - 1) y

/-- The signs on the basis indices of Y_j: −1 exactly at the i in block R with num(i) − k − j
non-negative and even, +1 elsewhere. -/
def signsY j : D.Y j → ℤˣ := D.gridSigns false 0 0 j

/-- Doubled parameter of Y_j at τ: 2ς on block R, t − 1 − 2w_l − 2b (0 ≤ b < t) on block l, all
lowered by 1 when j is odd. -/
def paramY j : D.Φ → D.Y j → ℤ := D.gridParam false 0 0 j

variable {z o i}

/-- The weight at τ of the character `Data.gridChar`: ⌊|n|/2⌋ − w_{l+1}(τ) if c is true, ⌈|n|/2⌉ −
w_{l+1}(τ) if c is false. -/
def gridWeight c l (n : Type) [Fintype n] τ := (((card n + (!c).toNat) / 2 :) - D.w (l + 1) τ : ℤ)

/-- The product over the infinite places of the chosen joint harmonics for the nodes (a, b), (i,
j) of grid z, weights `Data.gridWeight`, parameters negated if d is true. -/
def gridHarmonic o d c l z a b i j := jointHarmonic (D.gridWeight c l (D.GridIndex z a b))
  (D.gridWeight c l (D.GridIndex z i j)) (negIf d (D.gridParam z o a b))
  (negIf d (D.gridParam z o i j)) (D.gridSigns z o a b) (D.gridSigns z o i j)

/-- The index set of the node (i, j) has r + 1 + i(t+1) + j(t−1) elements in the grid Z (z true)
and r + jt + it elements in the grid V (z false). -/
lemma card_gridIndex : card (D.GridIndex z i j) =
  D.r + z.toNat + i * (D.t + z.toNat) + j * (D.t - z.toNat) := by simp [card_congr D.gridBlockEquiv]

lemma card_neg_gridSigns_eq_sum : negCount (D.gridSigns z o i j) = ∑ n ∈ range (D.r + z.toNat), ite
  (entrySign o j (n + 1 - D.k) = -1) 1 0 := by simp [negCount, ↓Fintype.card_subtype, ↓card_filter,
  reindex_equiv D.gridBlockEquiv.symm, gridSigns, sum_range, -sum_boole]; rfl

attribute [local grind] Bool rowParameter sum_range_zero sum_range_succ

/-- For offset 0, the number of signs −1 at the node (i, j) is ⌊(m − j + 1)/2⌋ in the grid Z and
⌊(m − j)/2⌋ in the grid V, with m − j truncated at 0. -/
lemma card_neg_gridSigns z i j : negCount (D.gridSigns z 0 i j) = (D.m - j + z.toNat) / 2 := by
  rw [card_neg_gridSigns_eq_sum]; trans (D.r + z.toNat + 1 - D.k - j) / 2; induction D.r + _
  repeat grind [entrySign_eq, units_ne_neg_self]

/-- For offset 0, the signs of Z_{0,0} are those of Y₀ followed by +1 on the extra index. -/
lemma gridSigns_zero : D.gridSigns true 0 0 0 = Sum.elim (D.signsY 0) 1 :=
  funext <| Sum.rec (by tauto) fun _ ↦ Even.neg_one_pow (by erw [Fin.val_natAdd]; grind)

/-- A bijection from the index set of V_{j,j} plus one point to that of Z_{j,j}: the identity
for j = 0, otherwise chosen to keep signs, the point having sign (−1)^{min(j,m)}. -/
def gridDiagEquiv : ∀ j, D.GridIndex false j j ⊕ Unit ≃ D.GridIndex true j j
  | 0 => .refl _ | j + 1 => (exists_equiv_of_card_neg (b := Sum.elim _ fun _ ↦ (-1) ^ min (j + 1)
    D.m) (by simp [card_gridIndex]; zify [D.t_odd.pos]; lia) (by
    rw [negCount_sumElim, card_neg_gridSigns, card_neg_gridSigns, negCount, neg_one_pow_eq_ite]
    split <;> simp <;> grind)).choose.symm

/-- For j ≤ m and offset 0, the signs of Z_{j,j} are, through the bijection `Data.gridDiagEquiv`,
those of V_{j,j} together with the sign (−1)^j on the extra index. -/
lemma gridDiagEquiv_spec (h : j ≤ D.m) :
  Sum.elim (D.gridSigns false 0 j j) (fun _ ↦ (-1) ^ j) ∘ (D.gridDiagEquiv j).symm =
  D.gridSigns true 0 j j := by cases j; use D.gridSigns_zero.symm; grind [gridDiagEquiv]

attribute [local grind norm] ite_mul card_gridIndex

lemma card_gridIndex_mod_two z i j : card (D.GridIndex z i j) % 2 = ite z 0 ((i + j + 1) % 2) := by
  induction i <;> induction j <;> grind

lemma w_add_gap_le a b (h : a < b) : D.w a τ + ite (a + 1 < b) 2 1 * D.h ≤ D.w b τ := by
  induction h <;> grind [w]

local grind_pattern w_add_gap_le => D.w a τ, D.w b τ
attribute [local typevec] gridParam gridSigns ite_odd_eq_sub_emod entrySign_eq pairSign
  Equiv.apply_symm_apply Sum.elim Pi.one_apply Injective ite_mul neg_mul one_mul Bool.cond_true
  Bool.cond_false IsMatchedPair FockDualPair.centredParam gridWeight Pi.neg_apply

lemma gridSigns_eq_one (h : D.m ≤ j) : D.gridSigns z 0 i j = 1 :=
  funext (by simp [reindex_equiv D.gridBlockEquiv.symm, typevec]; grind)

/-- If o = 0 or i = 0, then at each infinite place τ the doubled parameter `Data.gridParam` at node
(i, j) of grid z, offset o, is a Harish-Chandra parameter with gap h (`HCParam.HasGap`). -/
lemma hasGap_gridParam z i j (o := 0) (H : o = 0 ∨ i = 0 := by simp) : (D.gridParam z o i j
  τ).HasGap D.h := by constructor <;> norm_cast <;> push_cast [typevec,
  le_abs, reindex_equiv D.gridBlockEquiv.symm, Sum.forall,
  Int.even_iff] <;> grind -ring (splits := 60) [D.card_gridIndex_mod_two z i j, D.w_add_gap_le τ 0]

/-- At the node (m, m) the negated parameter of one grid and the parameter of the other interlace:
for each x the numbers of entries above x differ by 0 or 1. -/
lemma gridParam_interlace x : (#{j | x < -D.gridParam true 0 D.m D.m τ j} - #{i | x < D.gridParam
  false 0 D.m D.m τ i} : ℤ) ∈ Icc 0 1 := by
  let φ y : ℤ := ite (x < y) 1 0; let g n y := max 0 (min n ((y - x) / 2))
  have C A n : ∑ i ∈ range n, φ (A - 2 * i) = g n (A + 1) ∧ ∑ i ∈ range n, φ (-1 + -(A - 2 * i)) =
      g n (2 * n - A - 2) := by induction n <;> grind -funext
  apply (by grind : ∀ s, Icc (φ s) (φ (-1 + -s)) ⊆ _) (2 * D.rowParameter τ D.r)
  push_cast [card_filter]; show ∑ _, φ _ - ∑ _, φ _ ∈ _
  simp [reindex_equiv D.gridBlockEquiv.symm, gridParam, sum_prod_type,
    sum_fin_eq_sum_range, ↓← mem_range, sum_range_succ, -neg_sub, ← two_mul, C]
  rw [(by grind : D.r = D.k - 1 + D.m)]; induction D.m
  · simp +contextual [rowParameter, ↓← Nat.lt_sub_iff_add_lt, ← mem_range, mul_sub, -neg_sub,
      C]; grind
  grind -ring -funext (splits := 40)

lemma abs_gridParam_le : i ≤ D.m → j ≤ D.m → ∀ x, |D.gridParam z 0 i j τ x| ≤ ⌈20 * D.b⌉₊ := by
  have : 10 * D.w (2 * D.m) τ ≤ ⌈20 * D.b⌉₊ := by rify; grind [Nat.le_ceil, w_le_two_mul_b]
  simp [gridParam, reindex_equiv D.gridBlockEquiv.symm]; grind

lemma card_gridIndex_le (h : i ≤ D.m ∧ j ≤ D.m) : card (D.GridIndex z i j) ≤ 2 * D.n D.m := by
  grw [card_gridIndex, h.1, h.2, n]; grind [mul_tsub]

instance : Nonempty (D.GridIndex z i j) := card_pos_iff.1 (by grind)

/-- Every step of either grid is an edge (`ParamsCorrespond`): from (i,j) to (i+1,j) with both
parameters negated, or to (i,j+1) with them unchanged, provided the target indices i', j'
are at most m and o = 0 or i' = 0. -/
lemma paramsCorrespond_grid d z o i j {c l i' j'} (e : (c, l, i', j') = bif d then (z, i, i + 1,
  j) else (!z, j + o, i, j + 1)) (hi : i' ≤ D.m := by lia) (hj : j' ≤ D.m := by lia) (H : o = 0 ∨
  i' = 0 := by lia) : ParamsCorrespond (D.gridWeight c l (D.GridIndex z i j))
  (D.gridWeight c l (D.GridIndex z i' j')) (negIf d (D.gridParam z o i j))
  (negIf d (D.gridParam z o i' j')) (D.gridSigns z o i j) (D.gridSigns z o i' j') := fun τ ↦ by
  refine ⟨?_, .neg ?_, ?_, ?_⟩
  iterate 2 exact .mono (d.rec id .neg (D.hasGap_gridParam τ _ _ _ _ (by lia))) (by
    grw [card_gridIndex_le, card_gridIndex_le] <;> first | lia | use D.le_of_hasLogBound)
  all_goals cases d <;> cases e <;> simp_rw [reindex_equiv D.gridBlockEquiv.symm] <;> use Sum.rec
              (Sum.rec (.inl ⟨.inl <| .inl ·, ?_⟩) fun (l, y) ↦ (em _).imp (⟨.inl <| .inr
    ⟨⟨l, ·⟩, y⟩, ?_⟩) ?_) (fun (l, y) ↦ (em _).imp (⟨.inr ⟨⟨l, ·⟩, y⟩, ?_⟩) ?_) <;> push_cast
    [typevec, apply_ite Units.val] <;> grind -linarith [D.card_gridIndex_mod_two z i j]

lemma paramsCorrespond_first_arrow z (h : i + j < D.m) :
    let δ n τ := card (D.GridIndex z 0 n) - D.gridWeight (!z) (0 + i) (D.GridIndex z 0 n) τ
    let P o j o' j' := ParamsCorrespond (δ j) (δ j') (-D.gridParam z o 0 j) (-D.gridParam z o' 0 j')
      (D.gridSigns z o 0 j)
      (D.gridSigns z o' 0 j'); P (i + 1) j i (j + 1) ∧ P i (j + 1) (i + 1) j := by
  have g o := D.paramsCorrespond_grid false z o 0 j rfl
  use fun _ ↦ ⟨(g ..).1.neg, (g ..).2.neg, ?_, ?_⟩, fun _ ↦ ⟨(g ..).2, (g ..).1.neg.neg, ?_, ?_⟩
    <;> simp_rw [reindex_equiv D.gridBlockEquiv.symm] <;> use Sum.rec (Sum.rec (.inl ⟨.inl <|
    .inl ·, ?_⟩) nofun) (fun (l, y) ↦ (em _).imp (⟨.inr ⟨.rev ⟨l.rev, ·⟩, y⟩, ?_⟩) ?_) <;> push_cast
    [typevec, apply_ite Units.val] <;> grind -linarith [D.card_gridIndex_mod_two z 0 j]
