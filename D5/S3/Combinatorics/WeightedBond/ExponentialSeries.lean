/- GID: D5/S3/Combinatorics/WeightedBond/ExponentialSeries
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WeightedBond/ExponentialSeries
   mirror-E: none(waiver:kernel-checked-source-model)
   anchors: []
   utility: none
   digest: Labeled block series, Möbius inverse and its Vandermonde factorization. -/

import D5.S3.Combinatorics.WeightedBond.PartitionExpansion
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Data.Nat.Choose.Vandermonde

/-! Labeled block series, Möbius inverse and its Vandermonde factorization. -/

set_option autoImplicit false
open Finset PowerSeries

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {V : Type*} [DecidableEq V]

abbrev RootBlock (S : Finset V) (x : V) := {B : Finset V // B ⊆ S ∧ x ∈ B}

private theorem avoid_parts (S : Finset V) (p : Finpartition S) {B : Finset V}
    (hB : B ∈ p.parts) :
    (p.avoid B).parts = p.parts.erase B := by
  have hdis (D : Finset V) (hD : D ∈ p.parts) (hne : D ≠ B) : Disjoint D B :=
    p.disjoint hD hB hne
  ext D
  rw [Finpartition.mem_avoid, mem_erase]
  constructor
  · rintro ⟨E, hE, hsub, rfl⟩
    have hne : E ≠ B := fun h => hsub h.le
    simpa only [(sdiff_eq_left.mpr (hdis E hE hne))] using And.intro hne hE
  · rintro ⟨hne, hD⟩
    refine ⟨D, hD, ?_, sdiff_eq_left.mpr (hdis D hD hne)⟩
    exact fun hs => hne (p.disjoint.eq_of_le hD hB (p.ne_bot hD) hs)

private def addRoot (S : Finset V) {x : V} (B : RootBlock S x)
    (p : Finpartition (S \ B.val)) : Finpartition S :=
  p.extend (nonempty_iff_ne_empty.mp ⟨x, B.property.2⟩)
    disjoint_sdiff_self_left ((sdiff_sup_cancel B.property.1))

private theorem addRoot_parts (S : Finset V) {x : V} (B : RootBlock S x)
    (p : Finpartition (S \ B.val)) : (addRoot S B p).parts = insert B.val p.parts := rfl

private theorem root_notMem (S : Finset V) {x : V} (B : RootBlock S x)
    (p : Finpartition (S \ B.val)) : B.val ∉ p.parts := by
  intro hB
  exact (mem_sdiff.mp (p.le hB B.property.2)).2 B.property.2

private def rootEquiv (S : Finset V) (x : V) (hx : x ∈ S) :
    Finpartition S ≃ Σ B : RootBlock S x, Finpartition (S \ B.val) where
  toFun p := ⟨⟨p.part x, p.part_subset x, p.mem_part hx⟩, p.avoid (p.part x)⟩
  invFun q := addRoot S q.1 q.2
  left_inv p := by
    apply Finpartition.ext
    rw [addRoot_parts, avoid_parts _ _ (p.part_mem.mpr hx), insert_erase (p.part_mem.mpr hx)]
  right_inv q := by
    obtain ⟨B,p⟩ := q
    let a := addRoot S B p
    have hB : B.val ∈ a.parts := by simp [a, addRoot_parts]
    have he : a.part x = B.val := a.part_eq_of_mem hB B.property.2
    have he' : (⟨a.part x, a.part_subset x, a.mem_part hx⟩ : RootBlock S x) = B :=
      Subtype.ext he
    have hp : (a.avoid B.val) = p := by
      apply Finpartition.ext
      rw [avoid_parts _ _ hB, addRoot_parts, erase_insert (root_notMem S B p)]
    change @Sigma.mk (RootBlock S x) (fun D => Finpartition (S \ D.val)) ⟨a.part x, a.part_subset x, a.mem_part hx⟩ (a.avoid (a.part x)) = ⟨B, p⟩
    have hh {D E : RootBlock S x} (heq : D = E) : HEq (a.avoid D.val) (a.avoid E.val) := by
      cases heq
      rfl
    exact Sigma.ext he' ((hh he').trans (heq_of_eq hp))

instance (S : Finset V) (x : V) : Fintype (RootBlock S x) :=
  Fintype.ofFinset (S.powerset.filter (x ∈ ·)) (by intro B; change B ∈ _ ↔ B ⊆ S ∧ x ∈ B; simp [Finset.mem_powerset])

variable {R : Type*} [CommRing R]

def labeledWeight (w : ℕ → R) (S : Finset V) (k : ℕ) : R :=
  ∑ p : Finpartition S, if p.parts.card = k then ∏ B ∈ p.parts, w B.card else 0

theorem labeledWeight_root (w : ℕ → R) (S : Finset V) (x : V) (hx : x ∈ S) (k : ℕ) :
    labeledWeight w S (k + 1) =
      ∑ B : RootBlock S x, w B.val.card * labeledWeight w (S \ B.val) k := by
  let f := fun p : Finpartition S =>
    if p.parts.card = k + 1 then ∏ B ∈ p.parts, w B.card else 0
  calc
    _ = ∑ q : (Σ B : RootBlock S x, Finpartition (S \ B.val)), f (addRoot S q.1 q.2) := by
      apply Fintype.sum_equiv (rootEquiv S x hx)
      intro p
      exact congrArg f ((rootEquiv S x hx).symm_apply_apply p).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply sum_congr rfl
      intro B _
      rw [labeledWeight, mul_sum]
      apply sum_congr rfl
      intro p _
      simp only [f, addRoot_parts, card_insert_of_notMem (root_notMem S B p),
        prod_insert (root_notMem S B p), Nat.add_right_cancel_iff]
      split_ifs <;> simp

private def rootSupports (S : Finset V) (x : V) (hx : x ∈ S) :
    RootBlock S x ≃ ↥((S.erase x).powerset) where
  toFun B := ⟨B.val.erase x, mem_powerset.mpr (fun _ h =>
    mem_erase.mpr ⟨(mem_erase.mp h).1, B.property.1 (mem_erase.mp h).2⟩)⟩
  invFun D := ⟨insert x D.val, (by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hx
      · exact (mem_erase.mp (mem_powerset.mp D.property ha)).2), mem_insert_self _ _⟩
  left_inv B := Subtype.ext (insert_erase B.property.2)
  right_inv D := Subtype.ext (erase_insert (fun h =>
    (mem_erase.mp (mem_powerset.mp D.property h)).1 rfl))

private theorem root_sum (S : Finset V) (x : V) (hx : x ∈ S) (f : ℕ → R) :
    (∑ B : RootBlock S x, f B.val.card) =
      ∑ i ∈ range S.card, (S.card - 1).choose i * f (i + 1) := by
  calc
    _ = ∑ D : ↥((S.erase x).powerset), f (D.val.card + 1) := by
      apply Fintype.sum_equiv (rootSupports S x hx)
      intro B
      change f B.val.card = f ((B.val.erase x).card + 1)
      rw [card_erase_of_mem B.property.2]
      have := card_pos.mpr ⟨x, B.property.2⟩
      congr 1
      omega
    _ = _ := by
      rw [sum_coe_sort _ (fun D : Finset V => f (D.card + 1)), sum_powerset]
      simp_rw [sum_powersetCard _ _ (fun j => f (j + 1)), nsmul_eq_mul, card_erase_of_mem hx]
      have := card_pos.mpr ⟨x, hx⟩
      congr 2
      omega

variable [Algebra ℚ R]

def blockSeries (w : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else algebraMap ℚ R (1 / (n.factorial : ℚ)) * w n

@[simp] theorem blockSeries_zero (w : ℕ → R) : constantCoeff (blockSeries w) = 0 := by
  simp [blockSeries]

private theorem coeff_blockSeries_succ (w : ℕ → R) (j : ℕ) :
    coeff (j+1) (blockSeries w) = algebraMap ℚ R (1 / ((j+1).factorial : ℚ)) * w (j+1) := by
  simp [blockSeries]

omit [Algebra ℚ R] in
private theorem labeledWeight_zero (w : ℕ → R) (S : Finset V) :
    labeledWeight w S 0 = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S
    have h (p : Finpartition (∅ : Finset V)) : p.parts = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      exact p.ne_bot hB (subset_empty.mp (p.le hB))
    let : Subsingleton (Finpartition (∅ : Finset V)) :=
      ⟨fun p q => Finpartition.ext ((h p).trans (h q).symm)⟩
    have hc : Fintype.card (Finpartition (∅ : Finset V)) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨Finpartition.empty (Finset V), fun _ => Subsingleton.elim _ _⟩
    simp [labeledWeight, h, hc]
  · rw [ite_eq_right hS, labeledWeight]
    apply sum_eq_zero
    intro p _
    have h : p.parts.card ≠ 0 := by
      intro hz
      exact hS (by simpa [card_eq_zero.mp hz] using p.sup_parts.symm)
    simp [h]

omit [Algebra ℚ R] in
private theorem labeledWeight_empty_succ (w : ℕ → R) (k : ℕ) :
    labeledWeight w (∅ : Finset V) (k+1) = 0 := by
  apply sum_eq_zero
  intro p _
  have hp : p.parts = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    exact p.ne_bot hB (subset_empty.mp (p.le hB))
  simp [hp]

def scale (R : Type*) [CommRing R] [Algebra ℚ R] (n k : ℕ) : R :=
  algebraMap ℚ R ((n.factorial : ℚ) / (k.factorial : ℚ))

omit [DecidableEq V] in
private theorem scale_succ (n k : ℕ) :
    scale R (n+1) (k+1) * (k+1 : R) = (n+1 : R) * scale R n k := by
  unfold scale
  have h : ((n+1).factorial : ℚ) / ((k+1).factorial : ℚ) * (k+1) =
      (n+1) * ((n.factorial : ℚ) / (k.factorial : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
  simpa only [map_mul, map_add, map_one, map_natCast] using congrArg (algebraMap ℚ R) h

omit [DecidableEq V] in
private theorem scale_choose (n j k : ℕ) (hj : j ≤ n) :
    (n.choose j : R) * scale R (n-j) k =
      scale R n k * algebraMap ℚ R (1 / (j.factorial : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial hj
  have hq : (n.choose j : ℚ) * j.factorial * (n-j).factorial = n.factorial := by
    exact_mod_cast h
  have he : (n.choose j : ℚ) * ((n-j).factorial / (k.factorial : ℚ)) =
      ((n.factorial : ℚ) / (k.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
    field_simp
    linear_combination hq
  simpa only [scale, map_mul, map_natCast] using congrArg (algebraMap ℚ R) he

private theorem coeff_derivative_blockSeries (w : ℕ → R) (j : ℕ) :
    coeff j (derivative (R := R) (blockSeries w)) =
      algebraMap ℚ R (1 / (j.factorial : ℚ)) * w (j+1) := by
  rw [coeff_derivative, coeff_blockSeries_succ]
  have h : ((j+1 : ℕ) : ℚ) * (1 / ((j+1).factorial : ℚ)) = 1 / (j.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have he := congrArg (algebraMap ℚ R) h
  simp only [Nat.cast_succ, map_mul, map_add, map_natCast, map_one] at he
  rw [mul_comm (algebraMap ℚ R _ * _) _, ← mul_assoc, he]

/-- The sum for exactly k blocks is the normalized coefficient of the k-th power. -/
theorem labeledWeight_coeff (w : ℕ → R) (S : Finset V) (k : ℕ) :
    labeledWeight w S k = scale R S.card k * coeff S.card (blockSeries w ^ k) := by
  induction k generalizing S with
  | zero =>
    rw [labeledWeight_zero, pow_zero]
    rcases eq_empty_or_nonempty S with rfl | h
    · simp [scale]
    · simp [scale, coeff_one, h.ne_empty, h.card_pos.ne']
  | succ k ih =>
    rcases eq_empty_or_nonempty S with rfl | ⟨x,hx⟩
    · rw [labeledWeight_empty_succ, card_empty, coeff_zero_eq_constantCoeff, map_pow, blockSeries_zero]
      simp
    · have hS : 0 < S.card := card_pos.mpr ⟨x,hx⟩
      set n := S.card - 1 with hn
      have hn' : S.card = n + 1 := by omega
      rw [labeledWeight_root w S x hx]
      have hdif (B : RootBlock S x) : (S \ B.val).card = S.card - B.val.card :=
        card_sdiff_of_subset B.property.1
      simp_rw [ih, hdif]
      rw [root_sum S x hx (fun b => w b * (scale R (S.card - b) k * coeff (S.card - b) (blockSeries w ^ k)))]
      simp only [hn', Nat.add_sub_cancel, Nat.add_sub_add_right]
      let A := blockSeries w
      change _ = scale R (n+1) (k+1) * coeff (n+1) (A ^ (k+1))
      have hsum : (∑ j ∈ range (n+1),
          (n.choose j : R) * (w (j+1) * (scale R (n-j) k * coeff (n-j) (A^k)))) =
          scale R n k * coeff n (derivative (R := R) A * A^k) := by
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (derivative (R := R) A) * coeff j (A ^ k)), mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [coeff_derivative_blockSeries]
        have he := scale_choose (R := R) n j k (by simpa using hj)
        linear_combination he * w (j+1) * coeff (n-j) (A^k)
      rw [hsum]
      have hder : derivative (R := R) (A^(k+1)) =
          PowerSeries.C (k+1 : R) * (derivative (R := R) A * A^k) := by
        rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul R,
          smul_eq_C_mul, Nat.cast_succ, mul_comm (A^k)]
      have hcoef := congrArg (coeff n) hder
      rw [coeff_derivative, coeff_C_mul] at hcoef
      have hu : IsUnit ((n+1 : ℕ) : R) := by
        simpa only [map_natCast] using
          (isUnit_iff_ne_zero.mpr (by positivity : ((n+1 : ℕ) : ℚ) ≠ 0)).map (algebraMap ℚ R)
      apply hu.mul_left_cancel
      simp only [Nat.cast_succ]
      calc
        _ = scale R (n+1) (k+1) * ((k+1 : R) * coeff n (derivative (R := R) A * A^k)) := by
          have he := scale_succ (R := R) n k
          linear_combination -he * coeff n (derivative (R := R) A * A^k)
        _ = _ := by rw [← hcoef]; ac_rfl

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
open Finset PowerSeries

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section
open scoped Classical

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def assemblyKernel (f : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun k => algebraMap ℚ R (1 / (k.factorial : ℚ)) * f k

theorem coeff_subst_blockSeries (H : PowerSeries R) (w : ℕ → R) (n : ℕ) :
    coeff n (H.subst (blockSeries w)) =
      ∑ k ∈ range (n+1), coeff k H * coeff n (blockSeries w ^ k) := by
  rw [coeff_subst' (.of_constantCoeff_zero (blockSeries_zero w))]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  by_contra! hn
  have hlt : n < k := by simpa using hn
  have hz : coeff n (blockSeries w ^ k) = 0 := by
    apply coeff_of_lt_order
    exact (show (n : ENat) < (k : ENat) by exact_mod_cast hlt).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k (blockSeries_zero w))
  exact hk (by simp [hz])

/-- Arbitrary weights on the number of blocks can be applied before substitution. -/
theorem labeled_subst {V : Type*} [DecidableEq V] (S : Finset V) (f w : ℕ → R) :
    (∑ p : Finpartition S, f p.parts.card * ∏ B ∈ p.parts, w B.card) =
      (S.card.factorial : R) * coeff S.card ((assemblyKernel f).subst (blockSeries w)) := by
  rw [coeff_subst_blockSeries, mul_sum]
  have hsplit : (∑ k ∈ range (S.card+1), f k * labeledWeight w S k) =
      ∑ p : Finpartition S, f p.parts.card * ∏ B ∈ p.parts, w B.card := by
    simp only [labeledWeight, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [sum_eq_single p.parts.card]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact False.elim (h (mem_range.mpr (Nat.lt_succ_of_le p.card_parts_le_card)))
  rw [← hsplit]
  apply sum_congr rfl
  intro k _
  rw [labeledWeight_coeff, assemblyKernel, coeff_mk]
  have he : scale R S.card k = (S.card.factorial : R) * algebraMap ℚ R (1 / (k.factorial : ℚ)) := by
    unfold scale
    rw [div_eq_mul_one_div, map_mul, map_natCast]
  rw [he]
  ac_rfl

theorem assemblyKernel_one : assemblyKernel (fun _ => (1 : R)) = PowerSeries.exp R := by
  ext k
  simp [assemblyKernel, coeff_exp]

def oneBlockEGF (r : ℕ) : PowerSeries ℚ := blockSeries (fun n => (muComplete r n : ℚ))

def inverseCoefficient (r k : ℕ) : ℕ :=
  if k = 0 then 0 else (k - 1 + r - 1).choose (r - 1)

def inverseEGF (r : ℕ) : PowerSeries ℚ :=
  assemblyKernel (fun k => (inverseCoefficient r k : ℚ))

@[simp] theorem inverseEGF_zero (r : ℕ) : constantCoeff (inverseEGF r) = 0 := by
  simp [inverseEGF, assemblyKernel, inverseCoefficient]

theorem inverseEGF_subst_oneBlockEGF (r : ℕ) (hr : 0 < r) :
    (inverseEGF r).subst (oneBlockEGF r) = X := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff]
    change MvPowerSeries.constantCoeff ((inverseEGF r).subst (oneBlockEGF r)) =
      constantCoeff (X : PowerSeries ℚ)
    rw [constantCoeff_subst_of_constantCoeff_zero
      (show constantCoeff (oneBlockEGF r) = 0 from blockSeries_zero _)]
    simp
  | succ n =>
    have h := labeled_subst (R := ℚ) (univ : Finset (Fin (n+1)))
      (fun k => (inverseCoefficient r k : ℚ)) (fun j => (muComplete r j : ℚ))
    simp only [card_univ, Fintype.card_fin] at h
    change _ = ((n+1).factorial : ℚ) * coeff (n+1) ((inverseEGF r).subst (oneBlockEGF r)) at h
    have hsum : (∑ p : Partitions (Fin (n+1)), (inverseCoefficient r p.parts.card : ℚ) *
        ∏ B ∈ p.parts, (muComplete r B.card : ℚ)) = if n+1 = 1 then 1 else 0 := by
      have hpos (p : Partitions (Fin (n+1))) : p.parts.card ≠ 0 := by
        intro he
        have hp := p.sum_card_parts
        simp [card_eq_zero.mp he] at hp
      calc
        _ = ∑ p : Partitions (Fin (n+1)), (partitionProduct r p : ℚ) *
            (((p.parts.card - 1 + r - 1).choose (r-1) : ℕ) : ℚ) := by
          apply sum_congr rfl
          intro p _
          rw [inverseCoefficient, ite_eq_right (hpos p), partitionProduct, Int.cast_prod, mul_comm]
        _ = _ := by
          exact_mod_cast partition_inverse_recurrence r hr (n+1) (Nat.succ_pos _)
    rw [hsum] at h
    rw [coeff_X]
    by_cases hn : n = 0
    · subst n
      norm_num at h ⊢
      exact h.symm
    · have hh : n+1 ≠ 1 := by omega
      simp only [ite_eq_right hh] at h ⊢
      exact ((mul_eq_zero.mp h.symm).resolve_left (by positivity))

def markedBlockEGF (r : ℕ) : PowerSeries (Polynomial ℚ) :=
  blockSeries fun n => Polynomial.C (muComplete r n : ℚ) * Polynomial.X ^ (n-1)

theorem psiComplete_exponential (n r : ℕ) :
    psiComplete n r = (n.factorial : Polynomial ℚ) *
      coeff n ((PowerSeries.exp (Polynomial ℚ)).subst (markedBlockEGF r)) := by
  have h := labeled_subst (R := Polynomial ℚ) (univ : Finset (Fin n)) (fun _ => 1)
    (fun j => Polynomial.C (muComplete r j : ℚ) * Polynomial.X ^ (j-1))
  simp only [card_univ, Fintype.card_fin, assemblyKernel_one, one_mul] at h
  rw [psiComplete_partition, markedBlockEGF, ← h]
  apply sum_congr rfl
  intro p _
  rw [prod_mul_distrib, ← map_prod, ← Int.cast_prod, prod_pow_eq_pow_sum]
  congr 2
  have ht : (∑ B ∈ p.parts, (B.card - 1)) + p.parts.card = n := by
    calc
      _ = ∑ B ∈ p.parts, ((B.card - 1) + 1) := by simp [sum_add_distrib]
      _ = ∑ B ∈ p.parts, B.card := sum_congr rfl fun B hB =>
        Nat.sub_add_cancel (p.nonempty_of_mem_parts hB).card_pos
      _ = _ := by simp [p.sum_card_parts]
  omega

end
end D5.S3.Combinatorics.WeightedBond

set_option autoImplicit false
open Finset PowerSeries

namespace D5.S3.Combinatorics.WeightedBond
noncomputable section

/-- The polynomial factor for r = q + 2, viewed as a formal series. -/
def inverseFactor {R : Type*} [CommRing R] [Algebra ℚ R] (q : ℕ) : PowerSeries R :=
  PowerSeries.mk fun j => algebraMap ℚ R ((q.choose j : ℚ) / ((j+1).factorial : ℚ))

private theorem inverse_choose (q k : ℕ) :
    (q+k+1).choose (q+1) =
      ∑ j ∈ range (k+1), q.choose j * (k+1).choose (j+1) := by
  rw [show q+k+1 = (k+1)+q by omega, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (k+1).choose i * q.choose j), sum_range_succ']
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self q),
    mul_zero, add_zero, Nat.add_sub_add_right]
  have hsum (m : ℕ) (hm : q+1 ≤ m) :
      (∑ j ∈ range (q+1), (k+1).choose (j+1) * q.choose (q-j)) =
        ∑ j ∈ range m, q.choose j * (k+1).choose (j+1) := by
    calc
      _ = ∑ j ∈ range (q+1), q.choose j * (k+1).choose (j+1) := by
        apply sum_congr rfl
        intro j hj
        rw [Nat.choose_symm (Nat.le_of_lt_succ (mem_range.mp hj)), mul_comm]
      _ = _ := sum_subset (range_subset_range.mpr hm) fun j _ hj => by
        rw [Nat.choose_eq_zero_of_lt (by simpa using hj), zero_mul]
  rw [hsum (max (q+1) (k+1)) (le_max_left _ _)]
  symm
  exact sum_subset (range_subset_range.mpr (le_max_right _ _)) fun j _ hj => by
    rw [Nat.choose_eq_zero_of_lt (n := k+1) (k := j+1) (by simpa using hj), mul_zero]

theorem inverseEGF_factor (q : ℕ) :
    inverseEGF (q+2) = X * (inverseFactor q * PowerSeries.exp ℚ) := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (inverseFactor q) * coeff j (PowerSeries.exp ℚ))]
    simp only [inverseEGF, assemblyKernel, coeff_mk, inverseCoefficient, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel, Algebra.algebraMap_self, RingHom.id_apply, inverseFactor, coeff_exp]
    have hb : k + (q+2) - 1 = q+k+1 := by omega
    have hc : q+2-1 = q+1 := by omega
    rw [hb, hc, inverse_choose, Nat.cast_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjk : j+1 ≤ k+1 := by simpa using hj
    have h := Nat.choose_mul_factorial_mul_factorial hjk
    rw [Nat.add_sub_add_right] at h
    have hq : ((k+1).choose (j+1) : ℚ) * (j+1).factorial * (k-j).factorial =
        (k+1).factorial := by exact_mod_cast h
    push_cast
    field_simp
    linear_combination q.choose j * hq

end
end D5.S3.Combinatorics.WeightedBond
