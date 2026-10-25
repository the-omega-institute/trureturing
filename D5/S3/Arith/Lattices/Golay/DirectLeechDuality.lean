/- GID: D5/S3/Arith/Lattices/Golay/DirectLeechDuality
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Golay/DirectLeechDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real selfduality follows directly from integral coordinate and binary-code probes. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega



namespace D5.S3.Arith.Lattices.Golay.DirectLeechDuality

open scoped BigOperators

abbrev Coord := Fin 24
abbrev RealSpace := Coord → ℝ
abbrev BinarySpace := Coord → ZMod 2

noncomputable def B : LinearMap.BilinForm ℝ RealSpace :=
  (1 / 8 : ℝ) • dotProductBilin ℝ ℝ

def castVector (a : Coord → ℤ) : RealSpace := fun i => (a i : ℝ)

def RawMembership (C : Submodule (ZMod 2) BinarySpace)
    (x : RealSpace) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ z : Coord → ℤ,
    (∀ i, x i = (m : ℝ) + 2 * (z i : ℝ)) ∧
    (fun i => (z i : ZMod 2)) ∈ C ∧
    ∃ q : ℤ, (∑ i, (m + 2 * z i)) = 4 * m + 8 * q

def spike (i : Coord) (v : ℤ) : Coord → ℤ :=
  fun j => if j = i then v else 0

private lemma sum_spike (i : Coord) (v : ℤ) :
    (∑ j, spike i v j) = v := by
  classical
  simp [spike]

private lemma dot_spike (a : Coord → ℤ) (i : Coord) (v : ℤ) :
    (∑ j, a j * spike i v j) = a i * v := by
  classical
  simp [spike, mul_ite]

private lemma B_apply (x y : RealSpace) :
    B x y = (1 / 8 : ℝ) * ∑ i, x i * y i := rfl

private lemma B_integer (a b : Coord → ℤ) :
    B (castVector a) (castVector b) =
      (1 / 8 : ℝ) * ((∑ i, a i * b i : ℤ) : ℝ) := by
  simp only [B_apply, castVector, Int.cast_sum, Int.cast_mul]

private lemma mem_from_integer_data
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x)
    {a z : Coord → ℤ} {m : ℤ}
    (hm : m = 0 ∨ m = 1)
    (ha : ∀ i, a i = m + 2 * z i)
    (hz : (fun i => (z i : ZMod 2)) ∈ C)
    (hsum : ∃ q : ℤ, (∑ i, a i) = 4 * m + 8 * q) :
    castVector a ∈ K := by
  apply (hmem _).mpr
  refine ⟨m, hm, z, ?_, hz, ?_⟩
  · intro i
    dsimp [castVector]
    rw [ha i]
    push_cast <;> ring
  · obtain ⟨q, hq⟩ := hsum
    refine ⟨q, ?_⟩
    calc
      (∑ i, (m + 2 * z i)) = ∑ i, a i :=
        Finset.sum_congr rfl (fun i _ => (ha i).symm)
      _ = 4 * m + 8 * q := hq

/- The 8e_i probes: raw parity zero, z = 4e_i, and sum = 8. -/
lemma eight_mem
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x) (i : Coord) :
    castVector (spike i 8) ∈ K := by
  classical
  refine mem_from_integer_data hmem (m := 0) (z := spike i 4)
    (Or.inl rfl) ?_ ?_ ?_
  · intro j
    simp only [spike]
    split_ifs <;> norm_num <;> decide
  · have hz : (fun j => (spike i 4 j : ZMod 2)) = 0 := by
      funext j
      simp only [spike]
      split_ifs <;> norm_num <;> decide
    rw [hz]
    exact C.zero_mem
  · refine ⟨1, ?_⟩
    norm_num [sum_spike]

/- The i = 0 case is included: then both the probe and its half-vector are zero. -/
private lemma four_difference_mem
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x) (i : Coord) :
    castVector (fun j => spike i 4 j - spike 0 4 j) ∈ K := by
  classical
  refine mem_from_integer_data hmem (m := 0)
    (z := fun j => spike i 2 j - spike 0 2 j) (Or.inl rfl) ?_ ?_ ?_
  · intro j
    simp only [spike]
    split_ifs <;> norm_num <;> decide
  · have hz :
        (fun j => ((spike i 2 j - spike 0 2 j : ℤ) : ZMod 2)) = 0 := by
      funext j
      simp only [spike]
      split_ifs <;> norm_num <;> decide
    rw [hz]
    exact C.zero_mem
  · refine ⟨0, ?_⟩
    simp [Finset.sum_sub_distrib, sum_spike]

/- Canonical 0/1 lift.  val_lt supplies the actual two-valued assertion. -/
private def lift (c : BinarySpace) : Coord → ℤ := fun i => ((c i).val : ℤ)

private lemma lift_mod (c : BinarySpace) (i : Coord) :
    (lift c i : ZMod 2) = c i := by
  simpa only [lift, Int.cast_natCast] using ZMod.natCast_zmod_val (c i)

private lemma lift_reduction (c : BinarySpace) :
    (fun i => (lift c i : ZMod 2)) = c := funext (lift_mod c)

private lemma lift_sum (c : BinarySpace) :
    (∑ i, lift c i) =
      (((Finset.univ.filter (fun i => c i ≠ 0)).card : ℕ) : ℤ) := by
  classical
  have hval (i : Coord) : (c i).val = if c i ≠ 0 then 1 else 0 := by
    by_cases hi : c i = 0
    · simp [hi]
    · have hlt := ZMod.val_lt (c i)
      have hnz : (c i).val ≠ 0 := fun h => hi ((ZMod.val_eq_zero (c i)).mp h)
      simp only [if_pos hi]
      omega
  have hnat : (∑ i, (c i).val) =
      (Finset.univ.filter (fun i => c i ≠ 0)).card := by
    calc
      (∑ i, (c i).val) = ∑ i : Coord, if c i ≠ 0 then 1 else 0 :=
        Finset.sum_congr rfl (fun i _ => hval i)
      _ = (Finset.univ.filter (fun i => c i ≠ 0)).card := by
        simp [Finset.sum_ite]
  change (∑ i, ((c i).val : ℤ)) = _
  exact_mod_cast hnat

private lemma lift_sum_four
    {C : Submodule (ZMod 2) BinarySpace}
    (hdoubly : ∀ c ∈ C,
      (4 : ℕ) ∣ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    {c : BinarySpace} (hc : c ∈ C) :
    ∃ r : ℤ, (∑ i, lift c i) = 4 * r := by
  obtain ⟨r, hr⟩ := hdoubly c hc
  refine ⟨(r : ℤ), ?_⟩
  rw [lift_sum]
  exact_mod_cast hr

/- 2 lift(c) is a raw member because weight(c) = 4r, hence its sum is 8r. -/
private lemma code_probe_mem
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x)
    (hdoubly : ∀ c ∈ C,
      (4 : ℕ) ∣ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    {c : BinarySpace} (hc : c ∈ C) :
    castVector (fun i => 2 * lift c i) ∈ K := by
  obtain ⟨r, hr⟩ := lift_sum_four hdoubly hc
  refine mem_from_integer_data hmem (m := 0) (z := lift c)
    (Or.inl rfl) ?_ ?_ ?_
  · intro i
    ring
  · rw [lift_reduction]
    exact hc
  · refine ⟨r, ?_⟩
    rw [← Finset.mul_sum, hr]
    ring

/- t = 1 - 4e_0: m = 1, z = -2e_0, binary reduction zero, sum = 20. -/
private lemma glue_mem
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x) :
    castVector (fun j => 1 - spike 0 4 j) ∈ K := by
  classical
  refine mem_from_integer_data hmem (m := 1) (z := spike 0 (-2))
    (Or.inr rfl) ?_ ?_ ?_
  · intro j
    simp only [spike]
    split_ifs <;> norm_num <;> decide
  · have hz : (fun j => (spike 0 (-2) j : ZMod 2)) = 0 := by
      funext j
      simp only [spike]
      split_ifs <;> norm_num <;> decide
    rw [hz]
    exact C.zero_mem
  · refine ⟨2, ?_⟩
    norm_num [Finset.sum_sub_distrib, sum_spike]

/- All real coordinates of a dual vector are integers, proved with the 8e_i. -/
private lemma dual_integer_coordinates
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x)
    {y : RealSpace} (hy : y ∈ B.dualSubmodule K) :
    ∃ a : Coord → ℤ, castVector a = y := by
  classical
  have hcoord (i : Coord) : ∃ a : ℤ, (a : ℝ) = y i := by
    have hp := (LinearMap.BilinForm.mem_dualSubmodule B).mp hy
      (castVector (spike i 8)) (eight_mem hmem i)
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hp
    change (a : ℝ) = B y (castVector (spike i 8)) at ha
    have hs : (∑ j, y j * castVector (spike i 8) j) = y i * 8 := by
      simp [castVector, spike, apply_ite, mul_ite]
    have he : B y (castVector (spike i 8)) = y i := by
      rw [B_apply, hs]
      ring
    exact ⟨a, ha.trans he⟩
  choose a ha using hcoord
  exact ⟨a, funext ha⟩

/- Integral real pairing becomes the exact integer equation dot(a,b) = 8n. -/
private lemma dual_integer_dot
    {K : Submodule ℤ RealSpace} {a : Coord → ℤ}
    (ha : castVector a ∈ B.dualSubmodule K)
    {b : Coord → ℤ} (hb : castVector b ∈ K) :
    ∃ n : ℤ, (∑ i, a i * b i) = 8 * n := by
  have hp := ((LinearMap.BilinForm.mem_dualSubmodule B).mp ha) (castVector b) hb
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hp
  change (n : ℝ) = B (castVector a) (castVector b) at hn
  rw [B_integer] at hn
  refine ⟨n, ?_⟩
  have he : ((∑ i, a i * b i : ℤ) : ℝ) = 8 * (n : ℝ) := by
    linarith
  exact_mod_cast he

private lemma dual_le_raw
    {C : Submodule (ZMod 2) BinarySpace} {K : Submodule ℤ RealSpace}
    (hself : ∀ w : BinarySpace,
      w ∈ C ↔ ∀ c ∈ C, (∑ i, w i * c i) = 0)
    (hdoubly : ∀ c ∈ C,
      (4 : ℕ) ∣ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    (hmem : ∀ x, x ∈ K ↔ RawMembership C x) :
    B.dualSubmodule K ≤ K := by
  classical
  intro y hy
  obtain ⟨a, hay⟩ := dual_integer_coordinates hmem hy
  have ha : castVector a ∈ B.dualSubmodule K := by
    simpa only [hay] using hy

  -- Every difference from the zeroth integer coordinate is twice an integer.
  have hdiff (i : Coord) : ∃ d : ℤ, a i = a 0 + 2 * d := by
    obtain ⟨n, hn⟩ := dual_integer_dot ha (four_difference_mem hmem i)
    have hs : (∑ j, a j * (spike i 4 j - spike 0 4 j)) =
        4 * (a i - a 0) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [dot_spike, dot_spike]
      ring
    rw [hs] at hn
    exact ⟨n, by omega⟩
  choose d hd using hdiff

  -- Euclidean division is used, so the argument includes negative a_0.
  let m : ℤ := a 0 % 2
  let z : Coord → ℤ := fun i => a 0 / 2 + d i
  have hm : m = 0 ∨ m = 1 := by
    have hlo := Int.emod_nonneg (a 0) (by norm_num : (2 : ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos (a 0) (by norm_num : (0 : ℤ) < 2)
    dsimp [m]
    omega
  have hdivision : a 0 % 2 + 2 * (a 0 / 2) = a 0 :=
    Int.emod_add_mul_ediv (a 0) 2
  have haz (i : Coord) : a i = m + 2 * z i := by
    have hi := hd i
    dsimp [m, z]
    omega

  -- Pair with each genuine lifted codeword, then reduce the exact even dot sum.
  have hzC : (fun i => (z i : ZMod 2)) ∈ C := by
    apply (hself _).mpr
    intro c hc
    obtain ⟨r, hr⟩ := lift_sum_four hdoubly hc
    obtain ⟨n, hn⟩ := dual_integer_dot ha (code_probe_mem hmem hdoubly hc)
    have hs : (∑ i, a i * (2 * lift c i)) =
        2 * m * (∑ i, lift c i) + 4 * (∑ i, z i * lift c i) := by
      calc
        (∑ i, a i * (2 * lift c i)) =
            ∑ i, (2 * m * lift c i + 4 * (z i * lift c i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [haz i]
          ring
        _ = 2 * m * (∑ i, lift c i) + 4 * (∑ i, z i * lift c i) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hs, hr] at hn
    have heven : (2 : ℤ) ∣ (∑ i, z i * lift c i) := by
      refine ⟨n - m * r, ?_⟩
      nlinarith only [hn]
    have hred : ((∑ i, z i * lift c i : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr heven
    simpa only [Int.cast_sum, Int.cast_mul, lift_mod] using hred

  -- The last probe recovers the full modulo-eight sum condition.
  obtain ⟨n, hn⟩ := dual_integer_dot ha (glue_mem hmem)
  have hglue : (∑ i, a i * (1 - spike 0 4 i)) =
      (∑ i, a i) - 4 * a 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [dot_spike]
    ring
  rw [hglue] at hn
  have hsum : ∃ q : ℤ, (∑ i, a i) = 4 * m + 8 * q := by
    refine ⟨n + z 0, ?_⟩
    have hzero := haz 0
    omega
  rw [← hay]
  exact mem_from_integer_data hmem hm haz hzC hsum

/-- Direct real integral-pairing selfduality of the exact raw construction.

The hypotheses concern the binary code and the literal integer construction.
The actual Golay lattice consumer discharges them from its original suppliers. -/
theorem raw_integer_construction_dual_eq
    (C : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (K : Submodule ℤ (Fin 24 → ℝ))
    (hself : ∀ w : Fin 24 → ZMod 2,
      w ∈ C ↔ ∀ c ∈ C, (∑ i, w i * c i) = 0)
    (hdoubly : ∀ c ∈ C,
      (4 : ℕ) ∣ (Finset.univ.filter (fun i => c i ≠ 0)).card)
    (hmem : ∀ x : Fin 24 → ℝ, x ∈ K ↔
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ z : Fin 24 → ℤ,
        (∀ i, x i = (m : ℝ) + 2 * (z i : ℝ)) ∧
        (fun i => (z i : ZMod 2)) ∈ C ∧
        ∃ q : ℤ, (∑ i, (m + 2 * z i)) = 4 * m + 8 * q)
    (hintegral : ∀ x ∈ K, ∀ y ∈ K, ∃ k : ℤ,
      B x y = (k : ℝ)) :
    B.dualSubmodule K = K := by
  change B.dualSubmodule K = K
  refine le_antisymm (dual_le_raw hself hdoubly hmem) ?_
  intro x hx
  apply (LinearMap.BilinForm.mem_dualSubmodule B).mpr
  intro y hy
  obtain ⟨k, hk⟩ := hintegral x hx y hy
  exact Submodule.mem_one.mpr ⟨k, hk.symm⟩

end D5.S3.Arith.Lattices.Golay.DirectLeechDuality
