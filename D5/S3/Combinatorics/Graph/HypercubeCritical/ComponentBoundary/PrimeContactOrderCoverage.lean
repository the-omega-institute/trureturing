/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactOrderCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.ViaEmbedding, mathlib/module/Mathlib.Data.Fintype.Perm]
   utility: none
   digest: Independent block permutations count the coordinate orders covered by integer exponent steps. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactTransport
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Permutation covers from exponent steps

Disjoint coordinate blocks have independent permutations. Acting on coordinate
orders by inverse precomposition gives a bijection between any two fibers of the
block-maxima map. Integer exponent steps ensure that the fibers specified by
the targets of the columns cover all coordinate orders.

For eight axes and four non-target axes in blocks of size two or three, this
gives the integer form of the permutation-cover inequality in the Pro argument.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactOrderCoverage

open scoped BigOperators
open PrimeContactTransport (Exponent axis)

variable {n : ℕ}

/-- A finite family of pairwise disjoint coordinate blocks, each with a target axis. -/
structure StarFamily (n : ℕ) where
  blocks : Finset (Finset (Fin n))
  target : ∀ b : ↥blocks, ↥b.val
  disjoint : ∀ ⦃b d : ↥blocks⦄, b ≠ d → Disjoint b.val d.val

namespace StarFamily

/-- A choice of one axis in each block. -/
abbrev Selection (S : StarFamily n) := ∀ b : ↥S.blocks, ↥b.val

/-- The number of possible choices of block maxima. -/
def blockSizeProduct (S : StarFamily n) : ℕ :=
  ∏ b : ↥S.blocks, b.val.card

/-- The number of blocks of size three. -/
def tripleCount (S : StarFamily n) : ℕ :=
  (Finset.univ.filter fun b : ↥S.blocks => b.val.card = 3).card

private def IsMaximum (S : StarFamily n) (c : Equiv.Perm (Fin n)) (a : S.Selection) : Prop :=
  ∀ (b : ↥S.blocks) (i : ↥b.val), c i.val ≤ c (a b).val

private theorem exists_block_max (S : StarFamily n) (c : Equiv.Perm (Fin n))
    (b : ↥S.blocks) : ∃ a : ↥b.val, ∀ i : ↥b.val, c i.val ≤ c a.val := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image b.val (fun i => c i)
    ⟨(S.target b).val, (S.target b).property⟩
  exact ⟨⟨a, ha⟩, fun i => hmax i.val i.property⟩

private def maxima (S : StarFamily n) (c : Equiv.Perm (Fin n)) : S.Selection :=
  fun b => Classical.choose (S.exists_block_max c b)

private theorem maxima_eq_iff (S : StarFamily n) (c : Equiv.Perm (Fin n)) (a : S.Selection) :
    S.maxima c = a ↔ S.IsMaximum c a := by
  have hmax : S.IsMaximum c (S.maxima c) :=
    fun b => Classical.choose_spec (S.exists_block_max c b)
  constructor
  · rintro rfl
    exact hmax
  · intro ha
    funext b
    exact Subtype.ext (c.injective (le_antisymm (ha b (S.maxima c b)) (hmax b (a b))))

/-- Coordinate orders whose maxima in the blocks are the given axes. -/
def ordersWithMaxima (S : StarFamily n) (a : S.Selection) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun c => S.maxima c = a

private theorem mem_ordersWithMaxima (S : StarFamily n) (a : S.Selection)
    (c : Equiv.Perm (Fin n)) : c ∈ S.ordersWithMaxima a ↔ S.IsMaximum c a := by
  classical
  simpa [ordersWithMaxima] using S.maxima_eq_iff c a

/-- Coordinate orders whose maximum in every block is its specified target. -/
def localOrders (S : StarFamily n) : Finset (Equiv.Perm (Fin n)) :=
  S.ordersWithMaxima S.target

theorem mem_localOrders_iff (S : StarFamily n) (c : Equiv.Perm (Fin n)) :
    c ∈ S.localOrders ↔
      ∀ (b : ↥S.blocks) (i : ↥b.val), i ≠ S.target b → c i.val < c (S.target b).val := by
  rw [localOrders, S.mem_ordersWithMaxima]
  constructor
  · intro h b i hi
    refine lt_of_le_of_ne (h b i) ?_
    exact fun he => hi (Subtype.ext (c.injective he))
  · intro h b i
    by_cases hi : i = S.target b
    · subst i
      exact le_rfl
    · exact (h b i hi).le

private def axesEmbedding (S : StarFamily n) :
    (Σ b : ↥S.blocks, ↥b.val) ↪ Fin n where
  toFun x := x.2.val
  inj' := by
    rintro ⟨b, i⟩ ⟨d, j⟩ h
    change i.val = j.val at h
    have hbd : b = d := by
      by_contra hne
      have hj : i.val ∈ d.val := h.symm ▸ j.property
      exact (Finset.disjoint_left.mp (S.disjoint hne) i.property) hj
    subst d
    have hij : i = j := Subtype.ext h
    cases hij
    rfl

/-- Extend the product of the permutations of the individual blocks to all axes. -/
private def blockPerm (S : StarFamily n) :
    (∀ b : ↥S.blocks, Equiv.Perm (↥b.val)) →* Equiv.Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom S.axesEmbedding).comp
    (Equiv.Perm.sigmaCongrRightHom fun b : ↥S.blocks => ↥b.val)

private theorem blockPerm_apply (S : StarFamily n)
    (g : ∀ b : ↥S.blocks, Equiv.Perm (↥b.val)) (b : ↥S.blocks) (i : ↥b.val) :
    S.blockPerm g i.val = (g b i).val :=
  Equiv.Perm.viaEmbedding_apply (Equiv.Perm.sigmaCongrRight g) S.axesEmbedding ⟨b, i⟩

/-- The product group acts on ranks by precomposition with the inverse axis permutation. -/
private def rankAction (S : StarFamily n) :
    (∀ b : ↥S.blocks, Equiv.Perm (↥b.val)) →* Equiv.Perm (Equiv.Perm (Fin n)) where
  toFun g := Equiv.mulRight ((S.blockPerm g)⁻¹)
  map_one' := by
    apply Equiv.ext
    intro c
    change c * (S.blockPerm 1)⁻¹ = c
    rw [map_one, inv_one, mul_one]
  map_mul' g h := by
    apply Equiv.ext
    intro c
    change c * (S.blockPerm (g * h))⁻¹ =
      (c * (S.blockPerm h)⁻¹) * (S.blockPerm g)⁻¹
    rw [map_mul, mul_inv_rev, mul_assoc]

private theorem rankAction_apply (S : StarFamily n)
    (g : ∀ b : ↥S.blocks, Equiv.Perm (↥b.val)) (c : Equiv.Perm (Fin n))
    (b : ↥S.blocks) (i : ↥b.val) :
    S.rankAction g c (g b i).val = c i.val := by
  change c ((S.blockPerm g).symm (g b i).val) = c i.val
  rw [← S.blockPerm_apply g b i, Equiv.symm_apply_apply]

/-- Independent swaps take any assignment of maxima to any other assignment. -/
theorem card_ordersWithMaxima_eq (S : StarFamily n) (a d : S.Selection) :
    (S.ordersWithMaxima a).card = (S.ordersWithMaxima d).card := by
  classical
  let g (b : ↥S.blocks) : Equiv.Perm (↥b.val) := Equiv.swap (a b) (d b)
  have hswap (b : ↥S.blocks) : g b (a b) = d b := Equiv.swap_apply_left _ _
  refine Finset.card_equiv (S.rankAction g) ?_
  intro c
  simp only [mem_ordersWithMaxima]
  constructor
  · intro ha b i
    obtain ⟨j, rfl⟩ := (g b).surjective i
    simpa only [← hswap b, rankAction_apply] using ha b j
  · intro hd b i
    simpa only [← hswap b, rankAction_apply] using hd b (g b i)

/-- The cardinality of each fiber times the product of block sizes is the total
number of coordinate permutations. -/
theorem card_ordersWithMaxima_mul (S : StarFamily n) (a : S.Selection) :
    (S.ordersWithMaxima a).card * S.blockSizeProduct = Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hchoices : Fintype.card S.Selection = S.blockSizeProduct := by
    change Fintype.card (∀ b : ↥S.blocks, ↥b.val) = S.blockSizeProduct
    simp only [Fintype.card_pi, Fintype.card_coe, blockSizeProduct]
  have hfibers : (Finset.univ : Finset (Equiv.Perm (Fin n))).card =
      ∑ d : S.Selection, (S.ordersWithMaxima d).card := by
    unfold ordersWithMaxima
    exact Finset.card_eq_sum_card_fiberwise
      (f := S.maxima) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  calc
    _ = S.blockSizeProduct * (S.ordersWithMaxima a).card := Nat.mul_comm _ _
    _ = (Finset.univ : Finset S.Selection).card * (S.ordersWithMaxima a).card := by
      rw [Finset.card_univ, hchoices]
    _ = ∑ d : S.Selection, (S.ordersWithMaxima d).card :=
      (Finset.sum_const_nat fun d _ => S.card_ordersWithMaxima_eq d a).symm
    _ = _ := hfibers.symm

/-- The fiber specified by the targets has the same cardinality formula. -/
theorem card_localOrders_mul (S : StarFamily n) :
    S.localOrders.card * S.blockSizeProduct = Fintype.card (Equiv.Perm (Fin n)) :=
  S.card_ordersWithMaxima_mul S.target

/-- With four non-target axes, the block-size product is sixteen, twelve, or nine
according to the number of blocks of size three. -/
theorem blockSizeProduct_of_four_sources (S : StarFamily n)
    (hsize : ∀ b : ↥S.blocks, b.val.card = 2 ∨ b.val.card = 3)
    (hfour : (∑ b : ↥S.blocks, (b.val.card - 1)) = 4) :
    S.blockSizeProduct = (if S.tripleCount = 0 then 16 else if S.tripleCount = 1 then 12 else 9)
      ∧ S.tripleCount ≤ 2 := by
  let T := (Finset.univ : Finset ↥S.blocks).filter fun b => b.val.card = 3
  let D := (Finset.univ : Finset ↥S.blocks).filter fun b => ¬ b.val.card = 3
  have hT (b : ↥S.blocks) (hb : b ∈ T) : b.val.card = 3 := (Finset.mem_filter.mp hb).2
  have hD (b : ↥S.blocks) (hb : b ∈ D) : b.val.card = 2 :=
    (hsize b).resolve_right (Finset.mem_filter.mp hb).2
  have hsumT : (∑ b ∈ T, (b.val.card - 1)) = T.card * 2 :=
    Finset.sum_const_nat fun b hb => by rw [hT b hb] <;> decide
  have hsumD : (∑ b ∈ D, (b.val.card - 1)) = D.card * 1 :=
    Finset.sum_const_nat fun b hb => by rw [hD b hb] <;> decide
  have hsum : T.card * 2 + D.card * 1 = 4 := by
    rw [← hsumT, ← hsumD]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : ↥S.blocks => b.val.card = 3) (fun b => b.val.card - 1)).trans hfour
  have hprod : S.blockSizeProduct = 3 ^ T.card * 2 ^ D.card := by
    calc
      _ = (∏ b ∈ T, b.val.card) * ∏ b ∈ D, b.val.card :=
        (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun b : ↥S.blocks => b.val.card = 3) (fun b => b.val.card)).symm
      _ = (∏ _b ∈ T, (3 : ℕ)) * ∏ _b ∈ D, (2 : ℕ) :=
        congrArg₂ (· * ·) (Finset.prod_congr rfl hT) (Finset.prod_congr rfl hD)
      _ = _ := by simp only [Finset.prod_const]
  change S.blockSizeProduct = (if T.card = 0 then 16 else if T.card = 1 then 12 else 9)
    ∧ T.card ≤ 2
  refine ⟨?_, by omega⟩
  have ht : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases ht with h | h | h
  · have hd : D.card = 4 := by omega
    norm_num [hprod, h, hd]
  · have hd : D.card = 2 := by omega
    norm_num [hprod, h, hd]
  · have hd : D.card = 0 := by omega
    norm_num [hprod, h, hd]

end StarFamily

variable {Q : Type*}

/-- Every non-target axis has a neighbor column that realizes its exponent step. -/
def HasExponentSteps (K : Finset Q) (S : Q → StarFamily n) (v : Q → Exponent n) : Prop :=
  ∀ q ∈ K, ∀ (b : ↥(S q).blocks) (i : ↥b.val), i ≠ (S q).target b →
    ∃ p ∈ K, v p = v q + axis i.val - axis ((S q).target b).val

private def score (c : Equiv.Perm (Fin n)) (v : Exponent n) : ℤ :=
  ∑ i, ((c i).val : ℤ) * v i

private theorem score_axis (c : Equiv.Perm (Fin n)) (j : Fin n) :
    score c (axis j) = ((c j).val : ℤ) := by
  calc
    _ = ((c j).val : ℤ) * axis j j := by
      unfold score
      refine Finset.sum_eq_single j ?_ ?_
      · intro i _ hi
        simp [axis, hi]
      · simp
    _ = _ := by simp [axis]

private theorem score_step (c : Equiv.Perm (Fin n)) (w : Exponent n) (i j : Fin n) :
    score c (w + axis i - axis j) =
      score c w + ((c i).val : ℤ) - ((c j).val : ℤ) := by
  change (∑ k : Fin n, ((c k).val : ℤ) * (w k + axis i k - axis j k)) = _
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  change score c w + score c (axis i) - score c (axis j) = _
  simp only [score_axis]

/-- Maximizing the rank-weighted exponent score gives a column whose targets
strictly outrank their non-target axes. -/
theorem exists_mem_localOrders (K : Finset Q) (hK : K.Nonempty)
    (S : Q → StarFamily n) (v : Q → Exponent n) (hstep : HasExponentSteps K S v)
    (c : Equiv.Perm (Fin n)) : ∃ q ∈ K, c ∈ (S q).localOrders := by
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image K (fun q => score c (v q)) hK
  refine ⟨q, hq, ((S q).mem_localOrders_iff c).2 ?_⟩
  intro b i hi
  obtain ⟨p, hp, hgain⟩ := hstep q hq b i hi
  have hle : score c (v p) ≤ score c (v q) := hmax p hp
  rw [hgain, score_step] at hle
  have hne : (c i.val).val ≠ (c ((S q).target b).val).val :=
    fun h => hi (Subtype.ext (c.injective (Fin.val_injective h)))
  change (c i.val).val < (c ((S q).target b).val).val
  omega

/-- The total size of the local cover is at least the number of permutations. -/
theorem card_perm_le_sum_card_localOrders (K : Finset Q) (hK : K.Nonempty)
    (S : Q → StarFamily n) (v : Q → Exponent n) (hstep : HasExponentSteps K S v) :
    Fintype.card (Equiv.Perm (Fin n)) ≤ ∑ q ∈ K, (S q).localOrders.card := by
  classical
  have hcover : (Finset.univ : Finset (Equiv.Perm (Fin n))) = K.biUnion (fun q => (S q).localOrders) := by
    apply Finset.Subset.antisymm
    · intro c _
      exact Finset.mem_biUnion.mpr (exists_mem_localOrders K hK S v hstep c)
    · exact Finset.subset_univ _
  calc
    _ = (K.biUnion fun q => (S q).localOrders).card :=
      (Finset.card_univ).symm.trans (congrArg Finset.card hcover)
    _ ≤ _ := Finset.card_biUnion_le

private theorem card_perm_eight : Fintype.card (Equiv.Perm (Fin 8)) = 40320 := by
  rw [Fintype.card_perm, Fintype.card_fin] <;> decide

private def orderWeight (t : ℕ) : ℕ :=
  (if t = 0 then 9 else 0) + (if t = 1 then 12 else 0) + (if t = 2 then 16 else 0)

private theorem card_localOrders_eight (S : StarFamily 8)
    (hsize : ∀ b : ↥S.blocks, b.val.card = 2 ∨ b.val.card = 3)
    (hfour : (∑ b : ↥S.blocks, (b.val.card - 1)) = 4) :
    S.localOrders.card = 280 * orderWeight S.tripleCount := by
  obtain ⟨hprod, ht⟩ := S.blockSizeProduct_of_four_sources hsize hfour
  have hcard := S.card_localOrders_mul
  rw [hprod, card_perm_eight] at hcard
  have hcases : S.tripleCount = 0 ∨ S.tripleCount = 1 ∨ S.tripleCount = 2 := by omega
  rcases hcases with h | h | h <;>
    norm_num [h, orderWeight] at hcard ⊢ <;> omega

/-- The weighted permutation-cover inequality for eight axes. The three
filtered cardinalities are the counts of columns with zero, one, and two
blocks of size three. -/
theorem weighted_order_coverage (K : Finset Q) (hK : K.Nonempty)
    (S : Q → StarFamily 8) (v : Q → Exponent 8) (hstep : HasExponentSteps K S v)
    (hsize : ∀ q ∈ K, ∀ b : ↥(S q).blocks, b.val.card = 2 ∨ b.val.card = 3)
    (hfour : ∀ q ∈ K, (∑ b : ↥(S q).blocks, (b.val.card - 1)) = 4) :
    144 ≤ 9 * (K.filter fun q => (S q).tripleCount = 0).card
      + 12 * (K.filter fun q => (S q).tripleCount = 1).card
      + 16 * (K.filter fun q => (S q).tripleCount = 2).card := by
  have hcount : (∑ q ∈ K, (S q).localOrders.card) = 280 * ∑ q ∈ K, orderWeight (S q).tripleCount := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q hq => card_localOrders_eight (S q) (hsize q hq) (hfour q hq)
  have hcover := card_perm_le_sum_card_localOrders K hK S v hstep
  rw [card_perm_eight, hcount] at hcover
  have hweight : 144 ≤ ∑ q ∈ K, orderWeight (S q).tripleCount := by omega
  have hsum : (∑ q ∈ K, orderWeight (S q).tripleCount) =
      9 * (K.filter fun q => (S q).tripleCount = 0).card
        + 12 * (K.filter fun q => (S q).tripleCount = 1).card
        + 16 * (K.filter fun q => (S q).tripleCount = 2).card := by
    simp only [orderWeight, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
      add_zero, Finset.sum_const, Nat.nsmul_eq_mul]
    omega
  exact hweight.trans_eq hsum

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactOrderCoverage
