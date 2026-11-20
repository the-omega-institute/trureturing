/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ModThreeContactSupport
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Modulo-three potential and support sizes of signed two-step Q9 contacts. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactParity

/-! The potential and coordinate-pair support count in §4 of q9-saturated-tree-square-pro.txt. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ModThreeContactSupport

open scoped BigOperators

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsSwitching switchingVector)
open Q9SignedContactParity (signedPairingOnParityInt signedPairingOnParityInt_triangle_mod3
  signedPairingOnParityInt_row_sum)
open private cubeParity cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private intGamma intSwitchingVector from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

/-- The triangle identity recovers the potential from any base column. Zero row sums
force the potential to sum to zero because nine vanishes in characteristic three. -/
theorem exists_zero_sum_potential (M : Fin 9 → Fin 9 → ZMod 3)
    (htriangle : ∀ i j k, M i j + M j k = M i k)
    (hrow : ∀ i, ∑ j, M i j = 0) :
    ∃ a : Fin 9 → ZMod 3, (∀ i j, M i j = a i - a j) ∧ ∑ i, a i = 0 := by
  let a : Fin 9 → ZMod 3 := fun i => M i 8
  have hdiff (i j : Fin 9) : M i j = a i - a j :=
    eq_sub_iff_add_eq.mpr (htriangle i j 8)
  have h := hrow 8
  simp only [hdiff, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  have hnine : ((9 : ℕ) : ZMod 3) = 0 := by decide
  rw [hnine, zero_mul, zero_sub, neg_eq_zero] at h
  exact ⟨a, hdiff, h⟩

private def residueClass (x : ZMod 3) : Fin 3 :=
  ⟨x.val, ZMod.val_lt x⟩

private theorem residueClass_injective : Function.Injective residueClass :=
  fun _ _ h => ZMod.val_injective 3 (congrArg Fin.val h)

/-- The number of axes in the residue class indexed by its representative in `Fin 3`. -/
def residueClassSize (a : Fin 9 → ZMod 3) (r : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => residueClass (a i) = r).card

/-- Unordered axis pairs with nonzero residue, represented by their increasing order. -/
def nonzeroAxisPairs (M : Fin 9 → Fin 9 → ZMod 3) : Finset (Fin 9 × Fin 9) :=
  Finset.univ.filter fun ij => ij.1 < ij.2 ∧ M ij.1 ij.2 ≠ 0

/-- The three residue classes of a zero-sum potential have total size nine and
congruent sizes modulo three. -/
theorem zero_sum_class_sizes (a : Fin 9 → ZMod 3) (ha : ∑ i, a i = 0) :
    residueClassSize a 0 + residueClassSize a 1 + residueClassSize a 2 = 9 ∧
    residueClassSize a 0 % 3 = residueClassSize a 1 % 3 ∧
    residueClassSize a 1 % 3 = residueClassSize a 2 % 3 := by
  let label := residueClass ∘ a
  let n := residueClassSize a
  have hcard : n 0 + n 1 + n 2 = 9 := by
    simpa [Fin.sum_univ_three, residueClassSize, label, n] using
      (Finset.card_eq_sum_card_fiberwise (f := label) (s := Finset.univ)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm
  have hsum : (∑ r : Fin 3, (n r : ZMod 3) * (r.val : ZMod 3)) = ∑ i, a i := by
    simpa [residueClassSize, n, label, residueClass, nsmul_eq_mul, ZMod.cast_id] using
      (Finset.sum_fiberwise' (Finset.univ : Finset (Fin 9)) label
        (fun r => (r.val : ZMod 3)))
  have hweighted : ((n 1 : ZMod 3) + (n 2 : ZMod 3) * 2) = 0 := by
    simpa [Fin.sum_univ_three] using hsum.trans ha
  have hdvd : 3 ∣ n 1 + n 2 * 2 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hweighted
  refine ⟨hcard, ?_⟩
  dsimp only [n] at hcard hdvd
  constructor <;> omega

private theorem card_pairs_by_class (a : Fin 9 → ZMod 3) :
    (nonzeroAxisPairs (fun i j => a i - a j)).card =
      (Finset.univ.filter fun ij : Fin 9 × Fin 9 =>
        residueClass (a ij.1) < residueClass (a ij.2)).card := by
  let label := residueClass ∘ a
  let byClass := fun ij : Fin 9 × Fin 9 => if label ij.1 < label ij.2 then ij else ij.swap
  let byAxis := fun ij : Fin 9 × Fin 9 => if ij.1 < ij.2 then ij else ij.swap
  refine Finset.card_nbij' byClass byAxis ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    have hne : label i ≠ label j := fun he =>
      (Finset.mem_filter.mp h).2.2 (sub_eq_zero.mpr (residueClass_injective he))
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change label (byClass (i, j)).1 < label (byClass (i, j)).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simpa only [byClass, ite_eq_left hlt] using hlt
    · simpa only [byClass, ite_eq_right (not_lt_of_gt hgt), Prod.swap_prod_mk] using hgt
  · rintro ⟨i, j⟩ h
    have hlt : label i < label j := (Finset.mem_filter.mp h).2
    have hne : a i ≠ a j := fun he => hlt.ne (congrArg residueClass he)
    have haxis : i ≠ j := fun he => hne (congrArg a he)
    rcases lt_or_gt_of_ne haxis with hij | hji
    · simp [byAxis, nonzeroAxisPairs, hij, sub_ne_zero.mpr hne]
    · simp [byAxis, nonzeroAxisPairs, not_lt_of_gt hji, hji, sub_ne_zero.mpr hne.symm]
  · rintro ⟨i, j⟩ h
    obtain ⟨hij, hnonzero⟩ := (Finset.mem_filter.mp h).2
    have hne : label i ≠ label j := fun he =>
      hnonzero (sub_eq_zero.mpr (residueClass_injective he))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp [byClass, byAxis, hlt, hij]
    · simp [byClass, byAxis, not_lt_of_gt hgt, not_lt_of_gt hij]
  · rintro ⟨i, j⟩ h
    have hlt : label i < label j := (Finset.mem_filter.mp h).2
    have hne : i ≠ j := fun he => hlt.ne (congrArg label he)
    rcases lt_or_gt_of_ne hne with hij | hji
    · simp [byClass, byAxis, hlt, hij]
    · simp [byClass, byAxis, not_lt_of_gt hji, not_lt_of_gt hlt]

/-- Each pair of distinct residue classes contributes the product of its two sizes. -/
theorem nonzeroAxisPairs_card_eq_class_products (a : Fin 9 → ZMod 3) :
    (nonzeroAxisPairs (fun i j => a i - a j)).card =
      residueClassSize a 0 * residueClassSize a 1 + residueClassSize a 0 * residueClassSize a 2 +
        residueClassSize a 1 * residueClassSize a 2 := by
  rw [card_pairs_by_class]
  let key := fun ij : Fin 9 × Fin 9 => (residueClass (a ij.1), residueClass (a ij.2))
  let classes : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}
  let pairs := Finset.univ.filter fun ij : Fin 9 × Fin 9 => (key ij).1 < (key ij).2
  have hclasses : ∀ r s : Fin 3, (r, s) ∈ classes ↔ r < s := by decide
  have hmaps : (pairs : Set (Fin 9 × Fin 9)).MapsTo key classes :=
    fun ij h => (hclasses _ _).mpr ((Finset.mem_filter.mp h).2)
  change pairs.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (rs : Fin 3 × Fin 3) (hrs : rs ∈ classes) :
      (pairs.filter fun ij => key ij = rs).card =
        residueClassSize a rs.1 * residueClassSize a rs.2 := by
    rw [residueClassSize, residueClassSize, ← Finset.card_product]
    congr 1
    obtain ⟨r, s⟩ := rs
    have hrs' := (hclasses r s).mp hrs
    ext ⟨i, j⟩
    simp only [pairs, key, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
      Finset.mem_product]
    exact ⟨And.right, fun h => ⟨by simpa only [h.1, h.2] using hrs', h⟩⟩
  rw [Finset.sum_congr rfl hfiber]
  have h01 : (0, 1) ∉ ({(0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) := by decide
  have h02 : (0, 2) ∉ ({(1, 2)} : Finset (Fin 3 × Fin 3)) := by decide
  simp only [classes, Finset.sum_insert h01, Finset.sum_insert h02, Finset.sum_singleton]
  ac_rfl

private theorem class_products_finite :
    ∀ a b c : Fin 10, a.val + b.val + c.val = 9 →
      a.val % 3 = b.val % 3 → b.val % 3 = c.val % 3 →
      a.val * b.val + a.val * c.val + b.val * c.val ∈ ({0, 15, 18, 24, 27} : Finset ℕ) := by
  decide

private theorem class_products_mem {a b c : ℕ} (hsum : a + b + c = 9)
    (hab : a % 3 = b % 3) (hbc : b % 3 = c % 3) :
    a * b + a * c + b * c ∈ ({0, 15, 18, 24, 27} : Finset ℕ) :=
  class_products_finite ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ hsum hab hbc

open Classical in
/-- On either parity, the actual signed contact residues have a zero-sum potential. -/
theorem signedPairingOnParity_mod3_potential {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) :
    ∃ a : Fin 9 → ZMod 3,
      (∀ i j, (signedPairingOnParityInt C D σ τ p i j : ZMod 3) = a i - a j) ∧
      ∑ i, a i = 0 := by
  apply exists_zero_sum_potential
  · intro i j k
    have h :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr
        (signedPairingOnParityInt_triangle_mod3 hC hD hσ hτ hsep p i j k)
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub, Int.cast_add] using h)
  · intro i
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod 3))
        (signedPairingOnParityInt_row_sum hC hD hσ hτ hsep p i)

open Classical in
/-- The number of unordered axis pairs with a signed contact residue on either parity
belongs to the five-value spectrum. -/
theorem signedPairingOnParity_mod3_support_card {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) :
    (nonzeroAxisPairs (fun i j => (signedPairingOnParityInt C D σ τ p i j : ZMod 3))).card ∈
      ({0, 15, 18, 24, 27} : Finset ℕ) := by
  obtain ⟨a, hdiff, hsum⟩ := signedPairingOnParity_mod3_potential hC hD hσ hτ hsep p
  have hmatrix : (fun i j => (signedPairingOnParityInt C D σ τ p i j : ZMod 3)) =
      fun i j => a i - a j := funext fun i => funext (hdiff i)
  rw [hmatrix, nonzeroAxisPairs_card_eq_class_products]
  obtain ⟨htotal, h01, h12⟩ := zero_sum_class_sizes a hsum
  exact class_products_mem htotal h01 h12

/-- A nonzero residue witnesses a genuine same-parity contact along the given axes,
with the intermediate vertex of the ordered two-step walk outside both supports. -/
theorem exists_contact_of_nonzero_residue {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hdisj : Disjoint C D) (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {p : Bool} {i j : Fin 9}
    (hresidue : (signedPairingOnParityInt C D σ τ p i j : ZMod 3) ≠ 0) :
    i ≠ j ∧ ∃ x ∈ C, ∃ y ∈ D, cubeParity x = p ∧ cubeParity y = p ∧
      (Finset.univ.filter fun k => y k ≠ x k) = {i, j} ∧
      flip x i ∉ C ∧ flip x i ∉ D := by
  have hpairing : signedPairingOnParityInt C D σ τ p i j ≠ 0 :=
    fun h => hresidue (by rw [h, Int.cast_zero])
  let contribution := fun x => intSwitchingVector C σ x *
    intGamma i (intGamma j (intSwitchingVector D τ)) x
  have hterm : ∃ x ∈ (Finset.univ.filter fun x : Q 9 => cubeParity x = p),
      contribution x ≠ 0 := by
    by_contra! hzero
    exact hpairing (Finset.sum_eq_zero hzero)
  obtain ⟨x, hp, hnonzero⟩ := hterm
  have hx : x ∈ C := by
    by_contra h
    exact hnonzero (by simp [contribution, intSwitchingVector, switchingVector, h])
  have hy : flip (flip x i) j ∈ D := by
    by_contra h
    exact hnonzero (by simp [contribution, intGamma, intSwitchingVector, switchingVector, h])
  have hij : i ≠ j := by
    rintro rfl
    rw [BalancedCriticalSpectrum.flip_flip] at hy
    exact Finset.disjoint_left.mp hdisj hx hy
  have hxp := (Finset.mem_filter.mp hp).2
  have hyp : cubeParity (flip (flip x i) j) = p := by
    have h₁ := cubeParity_ne_of_adj (flip_adj x i)
    have h₂ := cubeParity_ne_of_adj (flip_adj (flip x i) j)
    cases hz : cubeParity (flip x i) <;>
      cases hw : cubeParity (flip (flip x i) j) <;> cases p <;> simp_all
  have hfirst : diff (flip x i) x = {i} := by
    rw [diff_flip]
    simp [diff]
  have hdiff : diff (flip (flip x i) j) x = {i, j} := by
    rw [diff_flip, hfirst, ite_eq_right (by simpa using hij.symm), Finset.pair_comm]
  exact ⟨hij, x, hx, _, hy, hxp, hyp, hdiff,
    fun hz => hsep _ hz _ hy (flip_adj _ j),
    fun hz => hsep x hx _ hz (flip_adj x i)⟩

#print axioms exists_zero_sum_potential
#print axioms zero_sum_class_sizes
#print axioms nonzeroAxisPairs_card_eq_class_products
#print axioms signedPairingOnParity_mod3_potential
#print axioms signedPairingOnParity_mod3_support_card
#print axioms exists_contact_of_nonzero_residue

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ModThreeContactSupport
