/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9BinaryAxialCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction]
   utility: none
   digest: Characterize signed weight-thirty-two axial completion by binary adjacency and recover the actual cubic graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction
import Mathlib.Algebra.BigOperators.ModEq

/-! Binary completion of the unit weight-thirty-two axial residual on Q8.
The raw TRUE and FALSE layers have transverse operators A and -A, respectively.
The binary criterion is on the entire even half. Writing it on all of Q8
adds only zero equations on the odd half. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion

open scoped BigOperators
open Finset
open BalancedCriticalSpectrum (Q flip)
open ComponentBoundary.Q9SignedAxialFold (transverse paritySign paritySign_flip)
open ComponentBoundary.Q9IsotropicHuang (flipSign)
open private transverse_square transverse_energy flipSign_unit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction
open private transverse_add transverse_sub from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedAxialFold
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
attribute [local instance] Classical.propDecidable

/-- Unit integer amplitudes, including zero off the support. -/
def UnitWord (f : Q 8 → ℤ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1 ∨ f x = -1

/-- The unsigned transverse degree, counted in actual cube directions. -/
def rowDegree (f : Q 8 → ℤ) (x : Q 8) : ℤ :=
  ∑ i : Fin 8, if f (flip x i) ≠ 0 then 1 else 0

/-- The binary neighbor sum on the support of the odd residual. -/
def binaryRow (v l : Q 8 → ℤ) (x : Q 8) : ℤ :=
  ∑ i : Fin 8, if v (flip x i) ≠ 0 then l (flip x i) else 0

/-- The odd residual with a binary choice of singleton layer. -/
def chosenWord (v l : Q 8 → ℤ) (x : Q 8) : ℤ :=
  (1 - 2 * l x) * v x

/-- The dimer sites read from the transverse signed row. -/
def dimerSites (e w : Q 8 → ℤ) : Finset (Q 8) :=
  univ.filter fun x => e x = 0 ∧ (transverse w x = 4 ∨ transverse w x = -4)

private theorem parity_unit (x : Q 8) : paritySign x = 1 ∨ paritySign x = -1 := by
  unfold paritySign
  split <;> simp

private theorem chosen_cases {v l : Q 8 → ℤ}
    (hl : ∀ x, l x = 0 ∨ l x = 1) (x : Q 8) :
    chosenWord v l x = v x ∨ chosenWord v l x = -v x := by
  rcases hl x with h | h <;> norm_num [chosenWord, h]

private theorem chosen_unit {v l : Q 8 → ℤ} (hv : UnitWord v)
    (hl : ∀ x, l x = 0 ∨ l x = 1) : UnitWord (chosenWord v l) := by
  intro x
  rcases chosen_cases (v := v) hl x with hw | hw <;>
    rcases hv x with h | h | h <;> norm_num [hw, h]

private theorem chosen_zero_iff {v l : Q 8 → ℤ}
    (hl : ∀ x, l x = 0 ∨ l x = 1) (x : Q 8) :
    chosenWord v l x = 0 ↔ v x = 0 := by
  rcases chosen_cases (v := v) hl x with h | h <;> simp [h]

private theorem row_bounds {f : Q 8 → ℤ} (hf : UnitWord f) (x : Q 8) :
    -rowDegree f x ≤ transverse f x ∧ transverse f x ≤ rowDegree f x := by
  have hterm (i : Fin 8) :
      -(if f (flip x i) ≠ 0 then (1 : ℤ) else 0) ≤ flipSign i x * f (flip x i) ∧
      flipSign i x * f (flip x i) ≤ (if f (flip x i) ≠ 0 then (1 : ℤ) else 0) := by
    rcases hf (flip x i) with h | h | h <;>
      rcases flipSign_unit i x with hs | hs <;> norm_num [h, hs]
  constructor
  · unfold rowDegree transverse
    rw [← sum_neg_distrib]
    exact sum_le_sum fun i _ => (hterm i).1
  · unfold rowDegree transverse
    exact sum_le_sum fun i _ => (hterm i).2

private theorem chosen_rowDegree {v l : Q 8 → ℤ}
    (hl : ∀ x, l x = 0 ∨ l x = 1) (x : Q 8) :
    rowDegree (chosenWord v l) x = rowDegree v x := by
  unfold rowDegree
  apply sum_congr rfl
  intro i _
  by_cases hz : v (flip x i) = 0
  · have hw := (chosen_zero_iff (v := v) hl (flip x i)).2 hz
    simp [hw, hz]
  · have hw : chosenWord v l (flip x i) ≠ 0 :=
      fun h => hz ((chosen_zero_iff (v := v) hl (flip x i)).1 h)
    simp [hw, hz]

private theorem transverse_smul (a : ℤ) (f : Q 8 → ℤ) (x : Q 8) :
    transverse (fun y => a * f y) x = a * transverse f x := by
  unfold transverse
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

private theorem chosen_transverse (v l : Q 8 → ℤ) (x : Q 8) :
    transverse (chosenWord v l) x =
      transverse v x - 2 * transverse (fun y => l y * v y) x := by
  unfold transverse chosenWord
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

private theorem binaryRow_mod_two {v l : Q 8 → ℤ} (hv : UnitWord v)
    (hl : ∀ x, l x = 0 ∨ l x = 1) (x : Q 8) :
    transverse (fun y => l y * v y) x % 2 = binaryRow v l x % 2 := by
  change (transverse (fun y => l y * v y) x) ≡ binaryRow v l x [ZMOD 2]
  unfold transverse binaryRow
  apply Int.ModEq.sum
  intro i _
  rcases hv (flip x i) with h | h | h <;>
    rcases hl (flip x i) with h' | h' <;>
    rcases flipSign_unit i x with hs | hs <;> norm_num [Int.ModEq, h, h', hs]

/-- The exact unsigned binary equation is equivalent to the signed mod-four
criterion for the chosen odd word. -/
theorem binaryRow_iff_mod_four {e v l : Q 8 → ℤ} (hv : UnitWord v)
    (hl : ∀ x, l x = 0 ∨ l x = 1)
    (hvrow : ∀ x, transverse v x = -4 * e x) (x : Q 8) :
    binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0) ↔
      transverse (chosenWord v l) x % 4 = (if e x ≠ 0 then 2 else 0) := by
  have h := binaryRow_mod_two hv hl x
  rw [chosen_transverse, hvrow]
  by_cases he : e x = 0 <;> simp [he] <;> omega

/-- Under the global row bound, the mod-four equations give exactly the
allowed row amplitudes at singleton and dimer sites. -/
theorem binaryRow_iff_eligible {e v l : Q 8 → ℤ} (hv : UnitWord v)
    (hl : ∀ x, l x = 0 ∨ l x = 1)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4) (x : Q 8) :
    binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0) ↔
      (if e x ≠ 0 then
        transverse (chosenWord v l) x = 2 ∨ transverse (chosenWord v l) x = -2
      else
        transverse (chosenWord v l) x = 0 ∨ transverse (chosenWord v l) x = 4 ∨
          transverse (chosenWord v l) x = -4) := by
  have hb := row_bounds (chosen_unit hv hl) x
  rw [chosen_rowDegree hl] at hb
  have hc := hcap x
  rw [binaryRow_iff_mod_four hv hl hvrow]
  by_cases he : e x = 0 <;> simp [he] <;> omega

private theorem unit_energy {f : Q 8 → ℤ} (hf : UnitWord f) :
    (∑ x, f x ^ 2) = ((univ.filter fun x => f x ≠ 0).card : ℤ) := by
  have h (x : Q 8) : f x ^ 2 = if f x ≠ 0 then (1 : ℤ) else 0 := by
    rcases hf x with h | h | h <;> norm_num [h]
  simp_rw [h]
  exact Finset.sum_boole _ _

private theorem chosen_energy {v l : Q 8 → ℤ}
    (hl : ∀ x, l x = 0 ∨ l x = 1) :
    (∑ x, chosenWord v l x ^ 2) = ∑ x, v x ^ 2 := by
  apply sum_congr rfl
  intro x _
  rcases chosen_cases (v := v) hl x with h | h
  · rw [h]
  · rw [h, neg_sq]

/-- Every eligible choice has precisely twelve dimer sites. The signed row
energy is 256, of which 64 is on the sixteen nonzero even residual sites. -/
theorem binary_dimer_count {e v l : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (he16 : (∑ x, e x ^ 2) = 16) (hv32 : (∑ x, v x ^ 2) = 32)
    (hl : ∀ x, l x = 0 ∨ l x = 1)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4)
    (hbinary : ∀ x, binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0)) :
    (dimerSites e (chosenWord v l)).card = 12 := by
  let w := chosenWord v l
  let D := dimerSites e w
  have henergy := transverse_energy w
  rw [chosen_energy hl, hv32] at henergy
  have hsite (x : Q 8) :
      transverse w x ^ 2 = 4 * e x ^ 2 + 16 * (if x ∈ D then (1 : ℤ) else 0) := by
    have hr := (binaryRow_iff_eligible hv hl hvrow hcap x).mp (hbinary x)
    rcases he x with hz | hp | hn
    · rw [if_neg (not_not_intro hz)] at hr
      rcases hr with h | h | h <;> norm_num [D, dimerSites, w, hz, h]
    · have hne : e x ≠ 0 := by simp [hp]
      rw [if_pos hne] at hr
      rcases hr with h | h <;> norm_num [D, dimerSites, w, hp, h]
    · have hne : e x ≠ 0 := by simp [hn]
      rw [if_pos hne] at hr
      rcases hr with h | h <;> norm_num [D, dimerSites, w, hn, h]
  simp_rw [hsite] at henergy
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, he16, Finset.sum_boole] at henergy
  have hfilter : univ.filter (fun x => x ∈ D) = D := by ext x; simp
  simp only [hfilter] at henergy
  change D.card = 12
  omega

/-- Unit raw layers with the prescribed residuals, only even axial dimers,
and the ambient signed eigen-equations. TRUE comes first. -/
structure AxialCompletion (e v p q : Q 8 → ℤ) : Prop where
  true_unit : UnitWord p
  false_unit : UnitWord q
  even_site : ∀ x, paritySign x = 1 →
    e x = p x - q x ∧ (p x = 0 ∨ q x = 0 ∨ p x = q x)
  odd_site : ∀ x, paritySign x = -1 →
    v x = -(p x + q x) ∧ (p x = 0 ∨ q x = 0)
  true_row : ∀ x, transverse p x + q x = 3 * p x
  false_row : ∀ x, p x - transverse q x = 3 * q x

private theorem transverse_even_zero {v : Q 8 → ℤ}
    (hv : ∀ x, paritySign x = 1 → v x = 0) (x : Q 8)
    (hx : paritySign x = -1) : transverse v x = 0 := by
  unfold transverse
  apply sum_eq_zero
  intro i _
  rw [hv _ (by rw [paritySign_flip, hx]; norm_num), mul_zero]

/-- Every row selected as a dimer is even, exterior to the even singleton
support, and has exactly four neighbors in the odd singleton support. -/
theorem binary_dimer_geometry {e v l : Q 8 → ℤ} (hv : UnitWord v)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (hl : ∀ x, l x = 0 ∨ l x = 1)
    (hcap : ∀ x, rowDegree v x ≤ 4) {x : Q 8}
    (hx : x ∈ dimerSites e (chosenWord v l)) :
    paritySign x = 1 ∧ e x = 0 ∧ rowDegree v x = 4 := by
  have hmem : e x = 0 ∧ (transverse (chosenWord v l) x = 4 ∨
      transverse (chosenWord v l) x = -4) := by
    simpa [dimerSites] using hx
  have hwzero (y : Q 8) (hy : paritySign y = 1) : chosenWord v l y = 0 :=
    (chosen_zero_iff hl y).2 (hveven y hy)
  have heven : paritySign x = 1 := by
    rcases parity_unit x with h | h
    · exact h
    · have hz := transverse_even_zero hwzero x h
      rcases hmem.2 with hr | hr <;> omega
  have hb := row_bounds (chosen_unit hv hl) x
  rw [chosen_rowDegree hl] at hb
  have hc := hcap x
  refine ⟨heven, hmem.1, ?_⟩
  rcases hmem.2 with hr | hr <;> omega

private theorem eigen_other_residual {e v : Q 8 → ℤ}
    (hvrow : ∀ x, transverse v x = -4 * e x) (x : Q 8) :
    transverse e x = -2 * v x := by
  have hs := transverse_square v x
  rw [show transverse v = (fun y => -4 * e y) from funext hvrow,
    transverse_smul] at hs
  omega

/-- Construct both raw signed layers explicitly from a binary solution. -/
theorem completion_of_binary {e v l : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (heodd : ∀ x, paritySign x = -1 → e x = 0)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (hl : ∀ x, l x = 0 ∨ l x = 1)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4)
    (hbinary : ∀ x, binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0)) :
    ∃ p q, AxialCompletion e v p q := by
  let w := chosenWord v l
  let g : Q 8 → ℤ := fun x => -(transverse w x) / 2
  let p : Q 8 → ℤ := fun x => (g x + e x - w x - v x) / 2
  let q : Q 8 → ℤ := fun x => (g x - e x + w x - v x) / 2
  have hwcases (x : Q 8) : w x = v x ∨ w x = -v x := chosen_cases hl x
  have hweven (x : Q 8) (hx : paritySign x = 1) : w x = 0 :=
    (chosen_zero_iff hl x).2 (hveven x hx)
  have hF (x : Q 8) : if e x ≠ 0 then transverse w x = 2 ∨ transverse w x = -2
      else transverse w x = 0 ∨ transverse w x = 4 ∨ transverse w x = -4 :=
    (binaryRow_iff_eligible hv hl hvrow hcap x).mp (hbinary x)
  have hwrow (x : Q 8) : transverse w x = -2 * g x := by
    have hh := hF x
    dsimp only [g]
    by_cases hx : e x = 0
    · rw [if_neg (not_not_intro hx)] at hh
      rcases hh with h | h | h <;> norm_num [h]
    · rw [if_pos hx] at hh
      rcases hh with h | h <;> norm_num [h]
  have hgrow (x : Q 8) : transverse g x = -4 * w x := by
    have hs := transverse_square w x
    rw [show transverse w = (fun y => -2 * g y) from funext hwrow,
      transverse_smul] at hs
    omega
  have hgeven (x : Q 8) (hx : paritySign x = 1) :
      (e x = 0 ∧ (g x = 0 ∨ g x = 2 ∨ g x = -2)) ∨
      (e x = 1 ∨ e x = -1) ∧ (g x = 1 ∨ g x = -1) := by
    have hh := hF x
    have hh' := hwrow x
    rcases he x with h | h | h <;> simp [h] at hh ⊢ <;> omega
  have hgodd (x : Q 8) (hx : paritySign x = -1) : g x = 0 := by
    have hh := hwrow x
    rw [transverse_even_zero hweven x hx] at hh
    omega
  have hlocal (x : Q 8) :
      (p x = 0 ∨ p x = 1 ∨ p x = -1) ∧
      (q x = 0 ∨ q x = 1 ∨ q x = -1) ∧
      2 * p x = g x + e x - w x - v x ∧
      2 * q x = g x - e x + w x - v x ∧
      (paritySign x = 1 →
        e x = p x - q x ∧ (p x = 0 ∨ q x = 0 ∨ p x = q x)) ∧
      (paritySign x = -1 →
        v x = -(p x + q x) ∧ (p x = 0 ∨ q x = 0)) := by
    rcases parity_unit x with hx | hx
    · have hv0 := hveven x hx
      have hw0 := hweven x hx
      rcases hgeven x hx with ⟨he0, hg0 | hg0 | hg0⟩ | ⟨he0 | he0, hg0 | hg0⟩ <;>
        norm_num [p, q, hx, hv0, hw0, he0, hg0]
    · have he0 := heodd x hx
      have hg0 := hgodd x hx
      rcases hv x with hv0 | hv0 | hv0 <;>
        rcases hwcases x with hw0 | hw0 <;>
        norm_num [p, q, hx, he0, hg0, hv0, hw0]
  have hp (x : Q 8) : 2 * p x = g x + e x - w x - v x := (hlocal x).2.2.1
  have hq (x : Q 8) : 2 * q x = g x - e x + w x - v x := (hlocal x).2.2.2.1
  have hpr (x : Q 8) :
      2 * transverse p x = transverse g x + transverse e x -
        transverse w x - transverse v x := by
    calc
      _ = transverse (fun y => 2 * p y) x := (transverse_smul 2 p x).symm
      _ = transverse (fun y => g y + e y - w y - v y) x := by
        rw [show (fun y => 2 * p y) = (fun y => g y + e y - w y - v y) from funext hp]
      _ = _ := by
        change transverse (g + e - w - v) x = _
        rw [transverse_sub, transverse_sub, transverse_add]
  have hqr (x : Q 8) :
      2 * transverse q x = transverse g x - transverse e x +
        transverse w x - transverse v x := by
    calc
      _ = transverse (fun y => 2 * q y) x := (transverse_smul 2 q x).symm
      _ = transverse (fun y => g y - e y + w y - v y) x := by
        rw [show (fun y => 2 * q y) = (fun y => g y - e y + w y - v y) from funext hq]
      _ = _ := by
        change transverse (g - e + w - v) x = _
        rw [transverse_sub, transverse_add, transverse_sub]
  refine ⟨p, q, ⟨fun x => (hlocal x).1, fun x => (hlocal x).2.1,
    fun x => (hlocal x).2.2.2.2.1, fun x => (hlocal x).2.2.2.2.2, ?_, ?_⟩⟩
  · intro x
    have hr := hpr x
    rw [hgrow, eigen_other_residual hvrow, hwrow, hvrow] at hr
    linarith [hp x, hq x]
  · intro x
    have hr := hqr x
    rw [hgrow, eigen_other_residual hvrow, hwrow, hvrow] at hr
    linarith [hp x, hq x]

/-- Recover a binary solution from the ambient signed layer equations. -/
theorem binary_of_completion {e v p q : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (heodd : ∀ x, paritySign x = -1 → e x = 0)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hc : AxialCompletion e v p q) :
    ∃ l : Q 8 → ℤ, (∀ x, l x = 0 ∨ l x = 1) ∧
      (∀ x, binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0)) ∧
      (∀ x, transverse (chosenWord v l) x = -2 * (p x + q x + v x)) := by
  let l : Q 8 → ℤ := fun x => if q x = 0 then 0 else 1
  let w := chosenWord v l
  let g : Q 8 → ℤ := fun x => p x + q x + v x
  have hl (x : Q 8) : l x = 0 ∨ l x = 1 := by dsimp only [l]; split <;> simp
  have hdiff (x : Q 8) : p x - q x = e x - w x := by
    rcases parity_unit x with hx | hx
    · have hz := hveven x hx
      have hw : w x = 0 := (chosen_zero_iff hl x).2 hz
      rw [hw, sub_zero]
      exact (hc.even_site x hx).1.symm
    · have he0 := heodd x hx
      obtain ⟨hv', hp | hq⟩ := hc.odd_site x hx
      · by_cases hq : q x = 0
        · have hv0 : v x = 0 := by omega
          simp [w, chosenWord, l, hp, hq, he0, hv0]
        · simp [w, chosenWord, l, hp, hq, he0] <;> omega
      · simp [w, chosenWord, l, hq, he0] <;> omega
  have hrow (x : Q 8) : transverse w x = -2 * g x := by
    have h := congrArg (fun f : Q 8 → ℤ => transverse f x)
      (show p - q = e - w from funext hdiff)
    rw [transverse_sub, transverse_sub, eigen_other_residual hvrow] at h
    dsimp only [g]
    linarith [hc.true_row x, hc.false_row x]
  refine ⟨l, hl, fun x => (binaryRow_iff_mod_four hv hl hvrow x).mpr ?_, hrow⟩
  rw [hrow]
  rcases parity_unit x with hx | hx
  · have hv0 := hveven x hx
    obtain ⟨he', _⟩ := hc.even_site x hx
    rcases he x with h | h | h <;>
      rcases hc.true_unit x with hp | hp | hp <;>
      rcases hc.false_unit x with hq | hq | hq <;>
      norm_num [h, hp, hq] at he' <;>
      norm_num [g, hv0, h, hp, hq]
  · have he0 := heodd x hx
    have hg : g x = 0 := by
      dsimp only [g]
      linarith [(hc.odd_site x hx).1]
    norm_num [hg, he0]

/-- Exact binary-completion equivalence at the level of raw signed words.
The next lemma supplies the induced-degree and edge-sign consequences. -/
theorem binary_completion_iff {e v : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (heodd : ∀ x, paritySign x = -1 → e x = 0)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4) :
    (∃ l : Q 8 → ℤ, (∀ x, l x = 0 ∨ l x = 1) ∧
      ∀ x, binaryRow v l x % 2 = (if e x ≠ 0 then 1 else 0)) ↔
    ∃ p q, AxialCompletion e v p q := by
  constructor
  · rintro ⟨l, hl, hb⟩
    exact completion_of_binary he hv heodd hveven hl hvrow hcap hb
  · rintro ⟨p, q, hc⟩
    obtain ⟨l, hl, hb, _⟩ := binary_of_completion he hv heodd hveven hvrow hc
    exact ⟨l, hl, hb⟩

/-- The actual raw layer intersection has twelve sites, the residual supports
have sixteen and thirty-two sites, and the sum of layer support sizes is 72. -/
theorem completion_sizes {e v p q : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (heodd : ∀ x, paritySign x = -1 → e x = 0)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (he16 : (∑ x, e x ^ 2) = 16) (hv32 : (∑ x, v x ^ 2) = 32)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4)
    (hc : AxialCompletion e v p q) :
    (univ.filter fun x => e x ≠ 0).card = 16 ∧
    (univ.filter fun x => v x ≠ 0).card = 32 ∧
    (univ.filter fun x => p x ≠ 0 ∧ q x ≠ 0).card = 12 ∧
    (univ.filter fun x => p x ≠ 0).card + (univ.filter fun x => q x ≠ 0).card = 72 := by
  obtain ⟨l, hl, hb, hr⟩ := binary_of_completion he hv heodd hveven hvrow hc
  let D := univ.filter fun x => p x ≠ 0 ∧ q x ≠ 0
  have hD : dimerSites e (chosenWord v l) = D := by
    ext x
    simp only [dimerSites, D, mem_filter, mem_univ, true_and, hr]
    rcases parity_unit x with hx | hx
    · have hv0 := hveven x hx
      obtain ⟨he', hpat⟩ := hc.even_site x hx
      rcases hc.true_unit x with hp | hp | hp <;>
        rcases hc.false_unit x with hq | hq | hq <;>
        norm_num [hp, hq] at hpat <;>
        norm_num [he', hp, hq, hv0]
    · have he0 := heodd x hx
      obtain ⟨hv', hp | hq⟩ := hc.odd_site x hx
      · simp [he0, hv', hp]
      · simp [he0, hv', hq]
  have hd12 := binary_dimer_count he hv he16 hv32 hl hvrow hcap hb
  rw [hD] at hd12
  have hs (x : Q 8) : p x ^ 2 + q x ^ 2 =
      e x ^ 2 + v x ^ 2 + 2 * (if x ∈ D then (1 : ℤ) else 0) := by
    rcases parity_unit x with hx | hx
    · have hv0 := hveven x hx
      obtain ⟨he', hpat⟩ := hc.even_site x hx
      rcases hc.true_unit x with hp | hp | hp <;>
        rcases hc.false_unit x with hq | hq | hq <;>
        norm_num [hp, hq] at hpat <;>
        norm_num [D, he', hv0, hp, hq]
    · have he0 := heodd x hx
      obtain ⟨hv', hp | hq⟩ := hc.odd_site x hx
      · norm_num [D, he0, hv', hp]
      · norm_num [D, he0, hv', hq]
  have hsum : (∑ x, (p x ^ 2 + q x ^ 2)) =
      ∑ x, (e x ^ 2 + v x ^ 2 + 2 * (if x ∈ D then (1 : ℤ) else 0)) :=
    sum_congr rfl (fun x _ => hs x)
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, he16, hv32,
    Finset.sum_boole] at hsum
  have hfilter : univ.filter (fun x => x ∈ D) = D := by ext x; simp
  simp only [hfilter] at hsum
  rw [hd12, unit_energy hc.true_unit, unit_energy hc.false_unit] at hsum
  rw [unit_energy he] at he16
  rw [unit_energy hv] at hv32
  refine ⟨?_, ?_, hd12, ?_⟩ <;> omega

private theorem sign_flip (x : Q 8) (i : Fin 8) :
    flipSign i (flip x i) = flipSign i x := by
  apply Int.cast_injective (α := ℝ)
  rw [flipSign_cast, flipSign_cast, BalancedCriticalSpectrum.flip_flip, huangMatrix_symmetric]

private theorem row_saturated {f : Q 8 → ℤ} (hf : UnitWord f)
    (x : Q 8) (s a : ℤ) (hs : s = 1 ∨ s = -1) (ha : a = 1 ∨ a = -1)
    (hr : s * transverse f x = a * rowDegree f x) (i : Fin 8)
    (hi : f (flip x i) ≠ 0) : s * flipSign i x * f (flip x i) = a := by
  let d : Fin 8 → ℤ := fun j =>
    (if f (flip x j) ≠ 0 then 1 else 0) - (a * s) * (flipSign j x * f (flip x j))
  have hn (j : Fin 8) : 0 ≤ d j := by
    rcases hs with hs | hs <;> rcases ha with ha | ha <;>
      rcases hf (flip x j) with h | h | h <;>
      rcases flipSign_unit j x with h' | h' <;> norm_num [d, hs, ha, h, h']
  have hz : (∑ j, d j) = 0 := by
    dsimp only [d]
    rw [sum_sub_distrib, ← mul_sum]
    change rowDegree f x - (a * s) * transverse f x = 0
    rcases hs with hs | hs <;> rcases ha with ha | ha <;>
      norm_num [hs, ha] at hr ⊢ <;> omega
  have hi0 := (sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz i (mem_univ i)
  rcases hs with hs | hs <;> rcases ha with ha | ha <;>
    norm_num [d, hi, hs, ha, mul_assoc] at hi0 ⊢ <;> omega

/-- At an even site the two transverse rows share the degree budget of four.
An occupied layer saturates its signed row, giving its exact unsigned degree
and the positive switching identity on each occupied transverse contact. -/
private theorem even_layer_saturated {p q : Q 8 → ℤ} (hp : UnitWord p) (hq : UnitWord q)
    (x : Q 8) (s : ℤ) (hs : s = 1 ∨ s = -1) (hpx : p x ≠ 0)
    (hcompatible : p x = 0 ∨ q x = 0 ∨ p x = q x)
    (hcap : rowDegree p x + rowDegree q x ≤ 4)
    (hrowP : s * transverse p x + q x = 3 * p x)
    (hrowQ : -s * transverse q x + p x = 3 * q x) :
    rowDegree p x + (if q x ≠ 0 then 1 else 0) = 3 ∧
    ∀ i : Fin 8, p (flip x i) ≠ 0 → s * flipSign i x * p (flip x i) = p x := by
  have ha : p x = 1 ∨ p x = -1 := (hp x).resolve_left hpx
  have hb := row_bounds hp x
  have hb' := row_bounds hq x
  have h : rowDegree p x + (if q x ≠ 0 then 1 else 0) = 3 ∧
      s * transverse p x = p x * rowDegree p x := by
    rcases ha with ha | ha <;> rcases hs with hs | hs <;>
      rcases hq x with hq0 | hq0 | hq0 <;>
      norm_num [ha, hq0] at hcompatible <;>
      norm_num [ha, hs, hq0] at hrowP hrowQ ⊢ <;> omega
  exact ⟨h.1, fun i hi => row_saturated hp x s (p x) hs ha h.2 i hi⟩

private theorem even_degree_budget {v p q : Q 8 → ℤ}
    (hodd : ∀ x, paritySign x = -1 →
      v x = -(p x + q x) ∧ (p x = 0 ∨ q x = 0)) (x : Q 8)
    (hx : paritySign x = 1) :
    rowDegree p x + rowDegree q x = rowDegree v x := by
  unfold rowDegree
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  obtain ⟨hv, hp | hq⟩ := hodd (flip x i) (by rw [paritySign_flip, hx])
  · simp [hv, hp]
  · simp [hv, hq]

private theorem layer_local {v p q : Q 8 → ℤ}
    (hp : UnitWord p) (hq : UnitWord q)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (heven : ∀ x, paritySign x = 1 → p x = 0 ∨ q x = 0 ∨ p x = q x)
    (hodd : ∀ x, paritySign x = -1 →
      v x = -(p x + q x) ∧ (p x = 0 ∨ q x = 0))
    (hcap : ∀ x, rowDegree v x ≤ 4)
    (hrowP : ∀ x, s * transverse p x + q x = 3 * p x)
    (hrowQ : ∀ x, -s * transverse q x + p x = 3 * q x) :
    ∀ x, p x ≠ 0 →
      rowDegree p x + (if q x ≠ 0 then 1 else 0) = 3 ∧
      ∀ i : Fin 8, p (flip x i) ≠ 0 → s * flipSign i x * p (flip x i) = p x := by
  have hev (x : Q 8) (hx : paritySign x = 1) (hpx : p x ≠ 0) :=
    even_layer_saturated hp hq x s hs hpx (heven x hx)
      (by rw [even_degree_budget hodd x hx]; exact hcap x) (hrowP x) (hrowQ x)
  intro x hpx
  rcases parity_unit x with hx | hx
  · exact hev x hx hpx
  · have hq0 : q x = 0 := ((hodd x hx).2).resolve_left hpx
    have hcontact (i : Fin 8) (hi : p (flip x i) ≠ 0) :
        s * flipSign i x * p (flip x i) = p x := by
      have hy : paritySign (flip x i) = 1 := by rw [paritySign_flip, hx]; norm_num
      have h := (hev (flip x i) hy hi).2 i
        (by simpa only [BalancedCriticalSpectrum.flip_flip] using hpx)
      rw [sign_flip, BalancedCriticalSpectrum.flip_flip] at h
      rcases hs with hs | hs <;> rcases flipSign_unit i x with hsign | hsign <;>
        norm_num [hs, hsign] at h ⊢ <;> omega
    have hr : s * transverse p x = p x * rowDegree p x := by
      unfold transverse rowDegree
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro i _
      by_cases hi : p (flip x i) = 0
      · simp [hi]
      · simpa [hi, mul_assoc] using hcontact i hi
    have hp' := hrowP x
    rw [hr, hq0] at hp'
    have ha : p x = 1 ∨ p x = -1 := (hp x).resolve_left hpx
    refine ⟨?_, hcontact⟩
    rcases ha with ha | ha <;> norm_num [hq0, ha] at hp' ⊢ <;> omega

/-- Complete local signed-degree invariant for the raw Q9 layers.
Each occupied TRUE or FALSE vertex has three occupied cube directions, every
occupied transverse contact is compatible with native Huang signs, and every
occupied axial contact has equal amplitudes. -/
theorem completion_local {e v p q : Q 8 → ℤ}
    (hc : AxialCompletion e v p q) (hcap : ∀ x, rowDegree v x ≤ 4) :
    (∀ x, p x ≠ 0 →
      rowDegree p x + (if q x ≠ 0 then 1 else 0) = 3 ∧
      ∀ i : Fin 8, p (flip x i) ≠ 0 → flipSign i x * p (flip x i) = p x) ∧
    (∀ x, q x ≠ 0 →
      rowDegree q x + (if p x ≠ 0 then 1 else 0) = 3 ∧
      ∀ i : Fin 8, q (flip x i) ≠ 0 → -flipSign i x * q (flip x i) = q x) ∧
    (∀ x, p x ≠ 0 → q x ≠ 0 → p x = q x) := by
  have he (x : Q 8) (hx : paritySign x = 1) := (hc.even_site x hx).2
  have htrue := layer_local hc.true_unit hc.false_unit 1 (Or.inl rfl)
    he hc.odd_site hcap (fun x => by simpa using hc.true_row x)
    (fun x => by simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using hc.false_row x)
  have hfalse := layer_local hc.false_unit hc.true_unit (-1) (Or.inr rfl)
    (fun x hx => by
      rcases he x hx with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm))
    (fun x hx => by
      obtain ⟨h, hh⟩ := hc.odd_site x hx
      exact ⟨by simpa only [add_comm] using h, hh.symm⟩)
    hcap (fun x => by simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using hc.false_row x)
    (fun x => by simpa only [neg_neg, one_mul] using hc.true_row x)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [one_mul] using htrue
  · simpa only [neg_one_mul] using hfalse
  · intro x hp hq
    rcases parity_unit x with hx | hx
    · exact ((he x hx).resolve_left hp).resolve_left hq
    · exact False.elim (hq ((hc.odd_site x hx).2.resolve_left hp))

#print axioms binaryRow_iff_mod_four
#print axioms binary_dimer_count
#print axioms binary_dimer_geometry
#print axioms binary_completion_iff
#print axioms completion_sizes
#print axioms completion_local

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion

open scoped BigOperators Classical
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsSwitching)
open BalancedCubeComponentBoundary (directions directions_card)
open BalancedCubeGirth (adjacent_exists_flip)
open SupportedEigenSaturation (selected_neighbor_card)
open ComponentBoundary.Q9SignedAxialFold (transverse paritySign)
open ComponentBoundary.Q9IsotropicHuang (flipSign)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private flip_cons_zero flip_cons_succ from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-- The raw layers of a weight-32 axial completion give the actual 72-vertex
induced cubic cube restriction, switched by their signed amplitudes.
The binary criterion supplies `hc` via `completion_of_binary`. -/
theorem completion_graph {e v p q : Q 8 → ℤ} (he : UnitWord e) (hv : UnitWord v)
    (heodd : ∀ x, paritySign x = -1 → e x = 0)
    (hveven : ∀ x, paritySign x = 1 → v x = 0)
    (he16 : (∑ x, e x ^ 2) = 16) (hv32 : (∑ x, v x ^ 2) = 32)
    (hvrow : ∀ x, transverse v x = -4 * e x)
    (hcap : ∀ x, rowDegree v x ≤ 4)
    (hc : AxialCompletion e v p q) :
    let C : Finset (Q 9) :=
      ((univ.filter fun x => p x ≠ 0).image (Fin.cons true)) ∪
        ((univ.filter fun x => q x ≠ 0).image (Fin.cons false))
    let w : Q 9 → ℤ := fun z => if z 0 then p (Fin.tail z) else q (Fin.tail z)
    C.card = 72 ∧ ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsSwitching C (fun z => (w z : ℝ)) := by
  let T : Finset (Q 8) := univ.filter fun x => p x ≠ 0
  let F : Finset (Q 8) := univ.filter fun x => q x ≠ 0
  let C : Finset (Q 9) := T.image (Fin.cons true) ∪ F.image (Fin.cons false)
  let w : Q 9 → ℤ := fun z => if z 0 then p (Fin.tail z) else q (Fin.tail z)
  change C.card = 72 ∧ ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
    IsSwitching C (fun z => (w z : ℝ))
  have hmem_true (x : Q 8) : Fin.cons true x ∈ C ↔ p x ≠ 0 := by
    simp [C, T, F, mem_image, Fin.cons_inj]
  have hmem_false (x : Q 8) : Fin.cons false x ∈ C ↔ q x ≠ 0 := by
    simp [C, T, F, mem_image, Fin.cons_inj]
  have hword_true (x : Q 8) : w (Fin.cons true x) = p x := by simp [w]
  have hword_false (x : Q 8) : w (Fin.cons false x) = q x := by simp [w]
  obtain ⟨htrue, hfalse, haxial⟩ := completion_local hc hcap
  have hunit_cons (b : Bool) (x : Q 8) (hx : Fin.cons b x ∈ C) :
      (w (Fin.cons b x) : ℝ) = 1 ∨ (w (Fin.cons b x) : ℝ) = -1 := by
    cases b
    · rcases (hc.false_unit x).resolve_left ((hmem_false x).mp hx) with h | h <;>
        simp [hword_false, h]
    · rcases (hc.true_unit x).resolve_left ((hmem_true x).mp hx) with h | h <;>
        simp [hword_true, h]
  have hcount_cons (b : Bool) (x : Q 8) (hx : Fin.cons b x ∈ C) :
      (∑ i : Fin 9, if flip (Fin.cons b x) i ∈ C then (1 : ℤ) else 0) = 3 := by
    rw [Fin.sum_univ_succ, add_comm]
    simp only [flip_cons_zero, flip_cons_succ]
    cases b
    · simpa only [rowDegree, Bool.not_false, hmem_true, hmem_false] using
        (hfalse x ((hmem_false x).mp hx)).1
    · simpa only [rowDegree, Bool.not_true, hmem_true, hmem_false] using
        (htrue x ((hmem_true x).mp hx)).1
  have hcontact_cons (b : Bool) (x : Q 8) (i : Fin 9)
      (hx : Fin.cons b x ∈ C) (hy : flip (Fin.cons b x) i ∈ C) :
      flipSign i (Fin.cons b x) * w (flip (Fin.cons b x) i) = w (Fin.cons b x) := by
    revert hy
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hy
      rw [flip_cons_zero] at hy ⊢
      change 1 * w (Fin.cons (!b) x) = w (Fin.cons b x)
      cases b
      · simpa only [Bool.not_false, one_mul, hword_true, hword_false] using
          haxial x ((hmem_true x).mp (by simpa only [Bool.not_false] using hy))
            ((hmem_false x).mp hx)
      · simpa only [Bool.not_true, one_mul, hword_true, hword_false] using
          (haxial x ((hmem_true x).mp hx)
            ((hmem_false x).mp (by simpa only [Bool.not_true] using hy))).symm
    · intro hy
      rw [flip_cons_succ] at hy ⊢
      change ((if b then 1 else -1) * flipSign j x) * w (Fin.cons b (flip x j)) =
        w (Fin.cons b x)
      cases b
      · simpa only [Bool.false_eq_true, if_false, neg_one_mul, hword_false] using
          (hfalse x ((hmem_false x).mp hx)).2 j ((hmem_false _).mp hy)
      · change (1 * flipSign j x) * w (Fin.cons true (flip x j)) = w (Fin.cons true x)
        simpa only [one_mul, hword_true] using
          (htrue x ((hmem_true x).mp hx)).2 j ((hmem_true _).mp hy)
  refine ⟨?_, ?_, ?_⟩
  · have hdisjoint : Disjoint
        (T.image (fun x : Q 8 => (Fin.cons true x : Q 9)))
        (F.image (fun x : Q 8 => (Fin.cons false x : Q 9))) := by
      apply Finset.disjoint_left.mpr
      intro z hzT hzF
      obtain ⟨x, _, rfl⟩ := mem_image.mp hzT
      obtain ⟨y, _, hy⟩ := mem_image.mp hzF
      exact Bool.false_ne_true (Fin.cons_inj.mp hy).1
    change (T.image (fun x : Q 8 => (Fin.cons true x : Q 9)) ∪
      F.image (fun x : Q 8 => (Fin.cons false x : Q 9))).card = 72
    rw [card_union_of_disjoint hdisjoint,
      card_image_of_injective _ (Fin.cons_right_injective (α := fun _ : Fin 9 => Bool) true),
      card_image_of_injective _ (Fin.cons_right_injective (α := fun _ : Fin 9 => Bool) false)]
    exact (completion_sizes he hv heodd hveven he16 hv32 hvrow hcap hc).2.2.2
  · rintro ⟨z, hz⟩
    change z ∈ C at hz
    change ((hypercube 9).induce (C : Set (Q 9))).degree ⟨z, hz⟩ = 3
    have hneighbors : (hypercube 9).neighborFinset z ∩ C =
        C.filter (fun y => (hypercube 9).Adj z y) := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [← selected_neighbor_card hz, hneighbors, ← directions_card]
    have hcount := hcount_cons (z 0) (Fin.tail z) (by simpa only [Fin.cons_self_tail] using hz)
    simp only [Fin.cons_self_tail, Finset.sum_boole] at hcount
    change ((directions C z).card : ℤ) = 3 at hcount
    exact_mod_cast hcount
  · have hunit (z : Q 9) (hz : z ∈ C) : (w z : ℝ) = 1 ∨ (w z : ℝ) = -1 := by
      simpa only [Fin.cons_self_tail] using
        hunit_cons (z 0) (Fin.tail z) (by simpa only [Fin.cons_self_tail] using hz)
    refine ⟨hunit, ?_⟩
    intro z hz y hy hadj
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj
    change huangMatrix 9 z (flip z i) = (w z : ℝ) * (w (flip z i) : ℝ)
    have hrel : (flipSign i z : ℝ) * (w (flip z i) : ℝ) = (w z : ℝ) := by
      have h := hcontact_cons (z 0) (Fin.tail z) i
        (by simpa only [Fin.cons_self_tail] using hz)
        (by simpa only [Fin.cons_self_tail] using hy)
      have hrow : flipSign i z * w (flip z i) = w z := by
        simpa only [Fin.cons_self_tail] using h
      rw [← Int.cast_mul, hrow]
    rw [← flipSign_cast i z]
    rcases hunit (flip z i) hy with h | h <;> rw [h] at hrel ⊢ <;> linarith

#print axioms completion_graph

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion
