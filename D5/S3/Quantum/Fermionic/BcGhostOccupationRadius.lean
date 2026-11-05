/- GID: D5/S3/Quantum/Fermionic/BcGhostOccupationRadius
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostOccupationRadius
   mirror-E: none(waiver:algebraic-ghost-radius)
   anchors: []
   utility: none
   digest: Finite occupation radii give the actual integer ghost annihilation cutoff. -/

import D5.S3.Quantum.Fermionic.BcGhostVirasoro

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

/-- Sites of b creators with labels in `[-A,-2]` and c creators in `[-A,1]`. -/
def sites (A : ℕ) : Finset ℕ :=
  ((Finset.range (A-1)).image (fun j => 2*j)) ∪
    ((Finset.range (A+2)).image (fun j => 2*j+1))

/-- Every occupation in the state's support lies in the indicated finite prefix. -/
def Radius (A : ℕ) (w : Fock) : Prop := ∀ S ∈ w.support, S ⊆ sites A

private theorem sites_mono {A B : ℕ} (h : A ≤ B) : sites A ⊆ sites B := by
  apply Finset.union_subset_union <;>
    exact Finset.image_subset_image (Finset.range_mono (by omega))

private theorem radius_mono {A B : ℕ} (h : A ≤ B) {w : Fock}
    (hw : Radius A w) : Radius B w :=
  fun S hS => (hw S hS).trans (sites_mono h)

private theorem radius_zero (A : ℕ) : Radius A 0 := by simp [Radius]

private theorem radius_add {A : ℕ} {v w : Fock}
    (hv : Radius A v) (hw : Radius A w) : Radius A (v+w) := by
  intro S hS
  rcases Finset.mem_union.mp (Finsupp.support_add hS) with h | h
  · exact hv S h
  · exact hw S h

private theorem radius_smul {A : ℕ} {w : Fock} (a : ℂ)
    (hw : Radius A w) : Radius A (a • w) :=
  fun S hS => hw S (Finsupp.support_smul hS)

private theorem radius_sum {ι : Type*} (s : Finset ι) {A : ℕ} (f : ι → Fock)
    (h : ∀ i ∈ s, Radius A (f i)) : Radius A (∑ i ∈ s, f i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simpa using radius_zero A
  | @insert i s hi ih =>
    intro h
    rw [Finset.sum_insert hi]
    exact radius_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

private theorem radius_ket {A : ℕ} {S : Finset ℕ} (h : S ⊆ sites A) :
    Radius A (ket S) := by
  simpa [Radius, ket] using h

private theorem expand (w : Fock) :
    w = ∑ S ∈ w.support, w S • ket S := by
  simpa [Finsupp.sum, ket] using (Finsupp.sum_single w).symm

private theorem radius_map {A B : ℕ} (T : Module.End ℂ Fock)
    (hT : ∀ S, S ⊆ sites A → Radius B (T (ket S)))
    {w : Fock} (hw : Radius A w) : Radius B (T w) := by
  rw [expand w]
  simp only [map_sum, map_smul]
  exact radius_sum w.support _ (fun S hS => radius_smul _ (hT S (hw S hS)))

private theorem sites_mem_of_small {A j : ℕ} (hA : 2 ≤ A) (hj : j+2 ≤ A) :
    j ∈ sites A := by
  by_cases he : j % 2 = 0
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨j/2, Finset.mem_range.mpr (by omega), by omega⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j/2, Finset.mem_range.mpr (by omega), by omega⟩

/-- Every actual finite-excitation state admits an occupation radius. -/
theorem exists_radius (w : Fock) : ∃ A : ℕ, 2 ≤ A ∧ Radius A w := by
  classical
  let P := (w.support.biUnion id).sup id
  refine ⟨max 2 (P+2), le_max_left _ _, ?_⟩
  intro S hS j hj
  apply sites_mem_of_small (le_max_left _ _)
  have hjP : j ≤ P := Finset.le_sup (f := id)
    (Finset.mem_biUnion.mpr ⟨S, hS, hj⟩)
  omega

private theorem annihilate_radius {A : ℕ} (j : ℕ) {w : Fock}
    (hw : Radius A w) : Radius A (annihilate j w) := by
  apply radius_map (annihilate j) _ hw
  intro S hS
  rw [annihilate_ket]
  split_ifs
  · exact radius_smul _ (radius_ket ((Finset.erase_subset _ _).trans hS))
  · exact radius_zero _

private theorem create_radius {A : ℕ} (j : ℕ) (hj : j ∈ sites A) {w : Fock}
    (hw : Radius A w) : Radius A (create j w) := by
  apply radius_map (create j) _ hw
  intro S hS
  rw [create_ket]
  split_ifs
  · exact radius_zero _
  · exact radius_smul _ (radius_ket (Finset.insert_subset hj hS))

private theorem annihilate_eq_zero {A : ℕ} (j : ℕ) (hj : j ∉ sites A)
    {w : Fock} (hw : Radius A w) : annihilate j w = 0 := by
  rw [expand w]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro S hS
  have hn : j ∉ S := fun h => hj (hw S hS h)
  simp [annihilate_ket, hn]

/-- Both original positive ghost tails annihilate a state in radius A. -/
theorem high_modes {A : ℕ} (hA : 2 ≤ A) {w : Fock} (hw : Radius A w)
    (t : ℤ) (ht : (A : ℤ) < t) : b t w = 0 ∧ c t w = 0 := by
  have hb : ¬ t ≤ -2 := by omega
  have hc : ¬ t ≤ 1 := by omega
  have hn (j : ℕ) (hj : j ∈ sites A) :
      (∃ k < A-1, 2*k = j) ∨ (∃ k < A+2, 2*k+1 = j) := by
    simpa [sites, Finset.mem_image, Finset.mem_range] using hj
  constructor
  · rw [b, if_neg hb]
    apply annihilate_eq_zero _ _ hw
    intro hj
    rcases hn _ hj with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ <;> omega
  · rw [c, if_neg hc]
    apply annihilate_eq_zero _ _ hw
    intro hj
    rcases hn _ hj with ⟨k, hk, he⟩ | ⟨k, hk, he⟩ <;> omega

/-- A single actual ghost action needs only the larger of the input and mode radii. -/
theorem mode_radius {A : ℕ} (hA : 2 ≤ A) {w : Fock} (hw : Radius A w)
    (t : ℤ) :
    Radius (max A (max t.natAbs 2)) (b t w) ∧
      Radius (max A (max t.natAbs 2)) (c t w) := by
  let R := max A (max t.natAbs 2)
  have hwR : Radius R w := radius_mono (le_max_left _ _) hw
  have habs : t.natAbs ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have ht₁ : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
  constructor
  · by_cases ht : t ≤ -2
    · rw [b, if_pos ht]
      apply create_radius _ _ hwR
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(-t-2).toNat, Finset.mem_range.mpr (by omega), rfl⟩
    · rw [b, if_neg ht]
      exact annihilate_radius _ hwR
  · by_cases ht : t ≤ 1
    · rw [c, if_pos ht]
      apply create_radius _ _ hwR
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(1-t).toNat, Finset.mem_range.mpr (by omega), rfl⟩
    · rw [c, if_neg ht]
      exact annihilate_radius _ hwR

private theorem normal_tail {A : ℕ} (hA : 2 ≤ A) {w : Fock} (hw : Radius A w)
    (r q : ℤ) (hq : q < r-(A : ℤ) ∨ (A : ℤ) < q) :
    BcGhostVirasoro.normal (r-q) q w = 0 := by
  rcases hq with hq | hq
  · have hp : ¬ r-q ≤ -2 := by omega
    simp only [BcGhostVirasoro.normal, if_neg hp, LinearMap.neg_apply,
      Module.End.mul_apply]
    rw [(high_modes hA hw (r-q) (by omega)).1, map_zero, neg_zero]
  · by_cases hp : r-q ≤ -2
    · simp only [BcGhostVirasoro.normal, if_pos hp, Module.End.mul_apply]
      rw [(high_modes hA hw q hq).2, map_zero]
    · simp only [BcGhostVirasoro.normal, if_neg hp, LinearMap.neg_apply,
        Module.End.mul_apply]
      have hb : Radius A (b (r-q) w) := by
        rw [b, if_neg hp]
        exact annihilate_radius _ hw
      rw [(high_modes hA hb q hq).2, neg_zero]

/-- The original ghost Virasoro action has the sharp statewise radius bound. -/
theorem virasoro_radius {A : ℕ} (hA : 2 ≤ A) {w : Fock} (hw : Radius A w)
    (r : ℤ) : Radius (A+(-r).toNat) (BcGhostVirasoro.L r w) := by
  classical
  let Z := A+(-r).toNat
  have hAZ : A ≤ Z := by dsimp [Z]; omega
  have hZ : 2 ≤ Z := hA.trans hAZ
  have hfinite : BcGhostVirasoro.L r w =
      ∑ q ∈ Finset.Icc (r-(A : ℤ)) (A : ℤ), BcGhostVirasoro.summand r q w := by
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    have ht : q < r-(A : ℤ) ∨ (A : ℤ) < q := by
      simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn
    exact hq (by simp [BcGhostVirasoro.summand, normal_tail hA hw r q ht])
  rw [hfinite]
  apply radius_sum
  intro q hq
  obtain ⟨hql, hqu⟩ := Finset.mem_Icc.mp hq
  have hpabs : (r-q).natAbs ≤ Z := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    apply abs_le.mpr
    dsimp [Z]
    constructor <;> omega
  have hqabs : q.natAbs ≤ Z := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    apply abs_le.mpr
    dsimp [Z]
    constructor <;> omega
  have hb {v : Fock} (hv : Radius Z v) : Radius Z (b (r-q) v) := by
    have h := (mode_radius hZ hv (r-q)).1
    exact radius_mono (by dsimp [Z] at *; omega) h
  have hc {v : Fock} (hv : Radius Z v) : Radius Z (c q v) := by
    have h := (mode_radius hZ hv q).2
    exact radius_mono (by omega) h
  simp only [BcGhostVirasoro.summand, LinearMap.smul_apply]
  apply radius_smul
  unfold BcGhostVirasoro.normal
  split_ifs
  · exact hb (hc (radius_mono hAZ hw))
  · simpa only [LinearMap.neg_apply, Module.End.mul_apply, neg_one_smul] using
      radius_smul (-1 : ℂ) (hc (hb (radius_mono hAZ hw)))

end D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
