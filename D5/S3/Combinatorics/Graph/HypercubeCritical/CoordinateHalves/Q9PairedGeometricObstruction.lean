/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedWeightSixteenSyndrome]
   utility: none
   digest: Bound the signed energy of paired syndrome lifts and exclude their order-seventy-two fold. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedWeightSixteenSyndrome
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! A weighted covering obstruction for the paired weight-sixteen syndrome. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction

open scoped BigOperators
open Finset
open EightCubeBits (Vertex Word cube toggle cube_toggle toggle_injective shell_card shell shell_symm parity)
open Q9PairedWeightSixteenSyndrome (pairedSyndrome)
open BalancedCriticalSpectrum (Q flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold (transverse)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (flipSign)
open private huangMatrix huang_energy from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private coeff matrix_coeff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-- A cover by sites of variable capacities costs at least the number of covered rows. -/
theorem card_le_weighted_cover {α β : Type*} (Z : Finset α) (T : Finset β)
    (r : α → β → Prop) [∀ z t, Decidable (r z t)] (w : α → ℤ)
    (hcover : ∀ t ∈ T, ∃ z ∈ Z, r z t)
    (hcap : ∀ z ∈ Z, ((T.bipartiteAbove r z).card : ℤ) ≤ w z) :
    (T.card : ℤ) ≤ ∑ z ∈ Z, w z := by
  calc
    (T.card : ℤ) = ∑ _t ∈ T, (1 : ℤ) := by simp
    _ ≤ ∑ t ∈ T, ((Z.bipartiteBelow r t).card : ℤ) := by
      apply sum_le_sum
      intro t ht
      obtain ⟨z, hz, hr⟩ := hcover t ht
      have hp : 0 < (Z.bipartiteBelow r t).card :=
        card_pos.mpr ⟨z, by simp [Finset.bipartiteBelow, hz, hr]⟩
      exact_mod_cast hp
    _ = ∑ z ∈ Z, ((T.bipartiteAbove r z).card : ℤ) := by
      exact_mod_cast (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Z) (t := T) r).symm
    _ ≤ _ := sum_le_sum hcap

/-- The shell of the fixed paired syndrome. -/
def pairedShell : Word :=
  {5, 6, 9, 10, 17, 18, 20, 23, 24, 27, 29, 30, 33, 34, 36, 39, 40, 43, 45, 46,
    53, 54, 57, 58, 85, 86, 89, 90, 101, 102, 105, 106, 149, 150, 153, 154,
    165, 166, 169, 170, 197, 198, 201, 202, 209, 210, 212, 215, 216, 219, 221,
    222, 225, 226, 228, 231, 232, 235, 237, 238, 245, 246, 249, 250}

private def activeDirections (S : Word) (x : Vertex) : Finset (Fin 8) :=
  univ.filter fun i => toggle x i ∈ S

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the fixed 256-vertex geometry.
/-- Every shell row has two syndrome neighbors, and every exterior row has zero. -/
theorem pairedShell_degree (x : Vertex) :
    (activeDirections pairedSyndrome x).card = if x ∈ pairedShell then 2 else 0 := by
  have h : (univ : Word).filter (fun y =>
      (activeDirections pairedSyndrome y).card = if y ∈ pairedShell then 2 else 0) = univ := by
    decide +kernel
  exact filter_eq_self.mp h x (mem_univ x)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the fixed 256-vertex geometry.
/-- An odd exterior correction can meet at most four rows of the paired shell. -/
theorem pairedShell_exterior_capacity (x : Vertex) (hodd : parity x = 1)
    (hout : x ∉ pairedSyndrome) : (shell x ∩ pairedShell).card ≤ 4 := by
  have h : (univ : Word).filter (fun y =>
      parity y = 1 ∧ y ∉ pairedSyndrome → (shell y ∩ pairedShell).card ≤ 4) = univ := by
    decide +kernel
  exact filter_eq_self.mp h x (mem_univ x) ⟨hodd, hout⟩

private theorem pairedSyndrome_card : pairedSyndrome.card = 16 := by
  decide +kernel

private theorem transverse_cast (f : Q 8 → ℤ) (x : Q 8) :
    (transverse f x : ℝ) = (huangMatrix 8).mulVec (fun y => (f y : ℝ)) x := by
  rw [matrix_row]
  change _ = ∑ i : Fin 8, huangMatrix 8 x (flip x i) * (f (flip x i) : ℝ)
  simp only [transverse, Int.cast_sum, Int.cast_mul, flipSign_cast]

private theorem transverse_energy (f : Q 8 → ℤ) :
    (∑ x, transverse f x ^ 2) = 8 * ∑ x, f x ^ 2 := by
  apply Int.cast_injective (α := ℝ)
  simpa only [Int.cast_sum, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, transverse_cast,
    Nat.cast_ofNat] using huang_energy 8 (fun x => (f x : ℝ))

theorem transverse_square (f : Q 8 → ℤ) (x : Q 8) :
    transverse (transverse f) x = 8 * f x := by
  have hmatrix (z : Q 8 → ℝ) :
      (huangMatrix 8).mulVec ((huangMatrix 8).mulVec z) = (8 : ℝ) • z := by
    rw [matrix_coeff, matrix_coeff, (coeff 8).symm_apply_apply, Sensitivity.f_squared,
      map_smul]
    norm_num
  apply Int.cast_injective (α := ℝ)
  rw [transverse_cast (transverse f) x]
  rw [show (fun y => (transverse f y : ℝ)) =
    (huangMatrix 8).mulVec (fun y => (f y : ℝ)) from funext (transverse_cast f)]
  rw [hmatrix]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]

/-- The repository transverse operator in the existing little-endian cube chart. -/
def bitRow (f : Vertex → ℤ) (x : Vertex) : ℤ :=
  transverse (f ∘ cube.symm) (cube x)

theorem bitRow_sum (f : Vertex → ℤ) (x : Vertex) :
    bitRow f x = ∑ i : Fin 8, flipSign i (cube x) * f (toggle x i) := by
  unfold bitRow transverse
  apply sum_congr rfl
  intro i _
  have ht := congrArg cube.symm (cube_toggle x i)
  simp only [Equiv.symm_apply_apply] at ht
  rw [Function.comp_apply, ← ht]

private theorem bitRow_energy (f : Vertex → ℤ) :
    (∑ x, bitRow f x ^ 2) = 8 * ∑ x, f x ^ 2 := by
  have h := transverse_energy (f ∘ cube.symm)
  calc
    (∑ x, bitRow f x ^ 2) = ∑ y : Q 8, transverse (f ∘ cube.symm) y ^ 2 :=
      Equiv.sum_comp cube (fun y : Q 8 => transverse (f ∘ cube.symm) y ^ 2)
    _ = 8 * ∑ y : Q 8, (f ∘ cube.symm) y ^ 2 := h
    _ = 8 * ∑ x, f x ^ 2 := by
      congr 1
      exact Equiv.sum_comp cube.symm (fun x => f x ^ 2)

theorem flipSign_unit {n : ℕ} (i : Fin n) (x : Q n) :
    flipSign i x = 1 ∨ flipSign i x = -1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · rcases ih j (Sensitivity.π x) with h | h <;>
        cases hx : x 0 <;> simp [flipSign, hx, h]

private theorem unit_rows {g : Vertex → ℤ}
    (hunit : ∀ x ∈ pairedSyndrome, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ pairedSyndrome, g x = 0) (x : Vertex) :
    (bitRow g x = 0 ∨ bitRow g x = 2 ∨ bitRow g x = -2) ∧
      (x ∉ pairedShell → bitRow g x = 0) := by
  let A := activeDirections pairedSyndrome x
  let a := fun i : Fin 8 => flipSign i (cube x) * g (toggle x i)
  have hrow : bitRow g x = ∑ i ∈ A, a i := by
    rw [bitRow_sum]
    symm
    apply sum_subset (subset_univ A)
    intro i _ hi
    have hz : toggle x i ∉ pairedSyndrome := by simpa [A, activeDirections] using hi
    simp [a, hzero _ hz]
  have ha (i : Fin 8) (hi : i ∈ A) : a i = 1 ∨ a i = -1 := by
    have hs : toggle x i ∈ pairedSyndrome := (mem_filter.mp hi).2
    rcases flipSign_unit i (cube x) with h | h <;>
      rcases hunit _ hs with h' | h' <;> simp [a, h, h']
  have hd := pairedShell_degree x
  change A.card = _ at hd
  by_cases hx : x ∈ pairedShell
  · rw [ite_eq_left hx] at hd
    obtain ⟨i, j, hij, hA⟩ := card_eq_two.mp hd
    have hi := ha i (by simp [hA])
    have hj := ha j (by simp [hA])
    rw [hrow, hA, sum_pair hij]
    refine ⟨?_, fun h => False.elim (h hx)⟩
    omega
  · rw [ite_eq_right hx] at hd
    rw [hrow, card_eq_zero.mp hd, sum_empty]
    simp

private theorem unit_energy {g : Vertex → ℤ}
    (hunit : ∀ x ∈ pairedSyndrome, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ pairedSyndrome, g x = 0) :
    (∑ x, g x ^ 2) = 16 := by
  calc
    _ = ∑ x ∈ pairedSyndrome, g x ^ 2 := by
      symm
      apply sum_subset (subset_univ _)
      intro x _ hx
      simp [hzero x hx]
    _ = ∑ _x ∈ pairedSyndrome, (1 : ℤ) := by
      apply sum_congr rfl
      intro x hx
      rcases hunit x hx with h | h <;> norm_num [h]
    _ = 16 := by simp [pairedSyndrome_card]

private theorem unit_row_support_card {g : Vertex → ℤ}
    (hunit : ∀ x ∈ pairedSyndrome, g x = 1 ∨ g x = -1)
    (hzero : ∀ x ∉ pairedSyndrome, g x = 0) :
    ((univ : Word).filter (fun x => bitRow g x ≠ 0)).card = 32 := by
  let T := (univ : Word).filter fun x => bitRow g x ≠ 0
  have henergy := bitRow_energy g
  rw [unit_energy hunit hzero] at henergy
  have hsum : (∑ x, bitRow g x ^ 2) = 4 * (T.card : ℤ) := by
    calc
      _ = ∑ x ∈ T, bitRow g x ^ 2 := by
        symm
        apply sum_subset (subset_univ _)
        intro x _ hx
        have hz : bitRow g x = 0 := by simpa [T] using hx
        simp [hz]
      _ = ∑ _x ∈ T, (4 : ℤ) := by
        apply sum_congr rfl
        intro x hx
        have hn : bitRow g x ≠ 0 := (mem_filter.mp hx).2
        rcases (unit_rows hunit hzero x).1 with h | h | h
        · exact False.elim (hn h)
        · norm_num [h]
        · norm_num [h]
      _ = _ := by simp [mul_comm]
  rw [hsum] at henergy
  change T.card = 32
  omega

/-- Any integer word supported on odd vertices with the paired odd support and
all transverse rows divisible by four has squared norm at least 48. -/
theorem paired_energy_ge_48 (v : Vertex → ℤ)
    (hodd : ∀ x, v x ≠ 0 → parity x = 1)
    (hsyndrome : ∀ x, v x % 2 = 1 ↔ x ∈ pairedSyndrome)
    (hdiv : ∀ x, 4 ∣ transverse (v ∘ cube.symm) (cube x)) :
    48 ≤ ∑ x, v x ^ 2 := by
  classical
  let g : Vertex → ℤ := fun x =>
    if x ∈ pairedSyndrome then if v x < 0 then -1 else 1 else 0
  have hg_unit (x : Vertex) (hx : x ∈ pairedSyndrome) : g x = 1 ∨ g x = -1 := by
    simp only [g, ite_eq_left hx]
    split <;> simp
  have hg_zero (x : Vertex) (hx : x ∉ pairedSyndrome) : g x = 0 := by simp [g, hx]
  let T := (univ : Word).filter fun x => bitRow g x ≠ 0
  let Z := (univ : Word).filter fun x => v x ≠ g x
  let w := fun x => v x ^ 2 - g x ^ 2
  have hT : T.card = 32 := unit_row_support_card hg_unit hg_zero
  have hTB : T ⊆ pairedShell := by
    intro x hx
    by_contra hn
    exact (mem_filter.mp hx).2 ((unit_rows hg_unit hg_zero x).2 hn)
  have hcover (t : Vertex) (ht : t ∈ T) :
      ∃ z ∈ Z, t ∈ shell z := by
    by_contra! hn
    have he : bitRow v t = bitRow g t := by
      rw [bitRow_sum, bitRow_sum]
      apply sum_congr rfl
      intro i _
      have hs : t ∈ shell (toggle t i) :=
        shell_symm.mp (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
      have hz : toggle t i ∉ Z := fun h => hn _ h hs
      have hv : v (toggle t i) = g (toggle t i) := by simpa [Z] using hz
      rw [hv]
    have hd : 4 ∣ bitRow g t := by
      rw [← he]
      exact hdiv t
    have hne : bitRow g t ≠ 0 := (mem_filter.mp ht).2
    rcases (unit_rows hg_unit hg_zero t).1 with h | h | h <;> omega
  have hcost (x : Vertex) (hx : x ∈ Z) :
      (if x ∈ pairedSyndrome then (8 : ℤ) else 4) ≤ w x := by
    have hne : v x ≠ g x := (mem_filter.mp hx).2
    by_cases hs : x ∈ pairedSyndrome
    · have hm := (hsyndrome x).2 hs
      simp only [ite_eq_left hs, w, g]
      by_cases hn : v x < 0
      · have h : v x ≤ -3 := by simp [g, hs, hn] at hne; omega
        simp [hn]
        nlinarith
      · have h : 3 ≤ v x := by simp [g, hs, hn] at hne; omega
        simp [hn]
        nlinarith
    · have hm : v x % 2 = 0 := by
        have hh := Int.emod_two_eq_zero_or_one (v x)
        have hno : v x % 2 ≠ 1 := fun h => hs ((hsyndrome x).1 h)
        omega
      have hv : v x ≠ 0 := by simpa [hg_zero x hs] using hne
      simp only [ite_eq_right hs, w, hg_zero x hs, zero_pow (by decide : 2 ≠ 0), sub_zero]
      have h : v x ≤ -2 ∨ 2 ≤ v x := by omega
      rcases h with h | h <;> nlinarith
  have hcap (z : Vertex) (hz : z ∈ Z) :
      ((T.bipartiteAbove (fun z t : Vertex => t ∈ shell z) z).card : ℤ) ≤ w z := by
    have hsub : T.bipartiteAbove (fun z t : Vertex => t ∈ shell z) z ⊆ shell z ∩ pairedShell := by
      intro t ht
      have ht' : t ∈ T ∧ t ∈ shell z := by simpa [Finset.bipartiteAbove] using ht
      obtain ⟨htT, htS⟩ := ht'
      exact mem_inter.mpr ⟨htS, hTB htT⟩
    have hle := card_le_card hsub
    have hc := hcost z hz
    by_cases hs : z ∈ pairedSyndrome
    · have hb : (shell z ∩ pairedShell).card ≤ 8 := by
        exact (card_le_card inter_subset_left).trans (shell_card z).le
      simp only [ite_eq_left hs] at hc
      omega
    · have hv : v z ≠ 0 := by
        have hn : v z ≠ g z := (mem_filter.mp hz).2
        simpa [hg_zero z hs] using hn
      have hb := pairedShell_exterior_capacity z (hodd z hv) hs
      simp only [ite_eq_right hs] at hc
      omega
  have hweighted := card_le_weighted_cover Z T (fun z t : Vertex => t ∈ shell z) w hcover hcap
  rw [hT] at hweighted
  have hsum : (∑ x ∈ Z, w x) = ∑ x, w x := by
    apply sum_subset (subset_univ _)
    intro x _ hx
    have he : v x = g x := by simpa [Z] using hx
    simp [w, he]
  rw [hsum] at hweighted
  change (32 : ℤ) ≤ ∑ x, (v x ^ 2 - g x ^ 2) at hweighted
  rw [sum_sub_distrib, unit_energy hg_unit hg_zero] at hweighted
  omega

/-- The obstruction stated directly for the native eight-cube transverse operator. -/
theorem paired_energy_ge_48_native (v : Q 8 → ℤ)
    (hodd : ∀ x, v x ≠ 0 → parity (cube.symm x) = 1)
    (hsyndrome : ∀ x, v x % 2 = 1 ↔ cube.symm x ∈ pairedSyndrome)
    (hdiv : ∀ x, 4 ∣ transverse v x) :
    48 ≤ ∑ x, v x ^ 2 := by
  have he : (v ∘ cube) ∘ cube.symm = v := by
    funext x
    simp
  have h := paired_energy_ge_48 (v ∘ cube)
    (fun x hx => by simpa using hodd (cube x) hx)
    (fun x => by simpa using hsyndrome (cube x))
    (fun x => by rw [he]; exact hdiv (cube x))
  calc
    48 ≤ ∑ x : Vertex, (v ∘ cube) x ^ 2 := h
    _ = ∑ x : Q 8, v x ^ 2 := Equiv.sum_comp cube (fun x => v x ^ 2)

/-- In the signed axial fold, a paired dimer syndrome forces at least
twenty-four even singleton sites when their coefficients are units. -/
theorem paired_fold_even_singleton_energy_ge_24
    (d e o : Q 8 → ℤ)
    (hfold : ∀ x, transverse o x = 4 * d x + 2 * e x)
    (hodd : ∀ x, transverse d x - 2 * o x ≠ 0 → parity (cube.symm x) = 1)
    (hsyndrome : ∀ x,
      (transverse d x - 2 * o x) % 2 = 1 ↔ cube.symm x ∈ pairedSyndrome) :
    24 ≤ ∑ x, e x ^ 2 := by
  let v : Q 8 → ℤ := fun x => transverse d x - 2 * o x
  have hrow (x : Q 8) : transverse v x = -4 * e x := by
    have hlinear : transverse v x = transverse (transverse d) x - 2 * transverse o x := by
      unfold v transverse
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hlinear, transverse_square, hfold]
    ring
  have hnorm := paired_energy_ge_48_native v hodd hsyndrome (fun x => ⟨-e x, by
    rw [hrow]
    ring⟩)
  have henergy := transverse_energy v
  simp_rw [hrow] at henergy
  have hsum : (∑ x, (-4 * e x) ^ 2) = 16 * ∑ x, e x ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  rw [hsum] at henergy
  omega

/-- The folded equations for order 72 with twelve even dimers and forty-eight
singletons are impossible when the dimer syndrome is the paired support. -/
theorem no_paired_fold_at_order_72
    (d e o : Q 8 → ℤ)
    (hd : (∑ x, d x ^ 2) = 12)
    (hdisj : ∀ x, d x * e x = 0)
    (hcount : (∑ x, e x ^ 2) + (∑ x, o x ^ 2) = 48)
    (hsum : ∀ x, transverse (fun y => 2 * d y + e y) x = 4 * o x)
    (hfold : ∀ x, transverse o x = 4 * d x + 2 * e x)
    (hodd : ∀ x, transverse d x - 2 * o x ≠ 0 → parity (cube.symm x) = 1)
    (hsyndrome : ∀ x,
      (transverse d x - 2 * o x) % 2 = 1 ↔ cube.symm x ∈ pairedSyndrome) :
    False := by
  have hbound := paired_fold_even_singleton_energy_ge_24 d e o hfold hodd hsyndrome
  have henergy := transverse_energy (fun x => 2 * d x + e x)
  simp_rw [hsum] at henergy
  have hout : (∑ x, (4 * o x) ^ 2) = 16 * ∑ x, o x ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  have hin : (∑ x, (2 * d x + e x) ^ 2) = 48 + ∑ x, e x ^ 2 := by
    have hsite (x : Q 8) : (2 * d x + e x) ^ 2 = 4 * d x ^ 2 + e x ^ 2 := by
      linear_combination 4 * hdisj x
    simp_rw [hsite]
    rw [sum_add_distrib, ← mul_sum, hd]
    norm_num
  rw [hout, hin] at henergy
  omega

#print axioms paired_energy_ge_48_native
#print axioms paired_fold_even_singleton_energy_ge_24
#print axioms no_paired_fold_at_order_72
#print axioms pairedShell_degree
#print axioms pairedShell_exterior_capacity
#print axioms card_le_weighted_cover
#print axioms paired_energy_ge_48

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction
