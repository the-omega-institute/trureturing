/- GID: D5/S3/Arith/DiophantineApproximation/StablePositiveSemigroup
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/StablePositiveSemigroup
   mirror-E: none(waiver:compactness-and-finite-approximation)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: A finite positive semigroup mesh survives moving generators. -/
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. The only density input is the existing
`dense_addSubgroupClosure_pair_iff`. No irrationality of moving ratios is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup
open Set Finset Filter Real
open scoped Topology

private theorem pair_representation {α γ x : ℝ}
    (hx : x ∈ AddSubgroup.closure ({γ, α} : Set ℝ)) :
    ∃ u v : ℤ, x = (u : ℝ) * α + (v : ℝ) * γ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, 1, by ring⟩
    · exact ⟨1, 0, by ring⟩
  | zero => exact ⟨0, 0, by ring⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨s, t, rfl⟩ := hy
    exact ⟨u + s, v + t, by push_cast; ring⟩
  | neg x _ hx =>
    obtain ⟨u, v, rfl⟩ := hx
    exact ⟨-u, -v, by push_cast; ring⟩

/- Compactness is applied once at the LIMIT generators. The perturbation
bound subsequently uses that same finite set, rather than O(Δ) approximants. -/
private theorem finite_stable_mesh {α₀ γ₀ ε : ℝ} (hα : 0 < α₀)
    (hirr : Irrational (γ₀ / α₀)) (hε : 0 < ε) :
    ∃ F : Finset (ℤ × ℤ), ∃ δ : ℝ, 0 < δ ∧
      ∀ α γ : ℝ, |α - α₀| < δ → |γ - γ₀| < δ →
      ∀ x ∈ Icc (0 : ℝ) (2 * α₀),
        ∃ z ∈ F, |(z.1 : ℝ) * α + (z.2 : ℝ) * γ - x| < ε := by
  classical
  have hd := dense_addSubgroupClosure_pair_iff.mpr hirr
  let U : ℤ × ℤ → Set ℝ := fun z =>
    Ioo ((z.1 : ℝ) * α₀ + (z.2 : ℝ) * γ₀ - ε / 2)
      ((z.1 : ℝ) * α₀ + (z.2 : ℝ) * γ₀ + ε / 2)
  have hcover : Icc (0 : ℝ) (2 * α₀) ⊆ ⋃ z, U z := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := hd.exists_mem_open
      (U := Ioo (x - ε / 2) (x + ε / 2)) isOpen_Ioo
      ⟨x, by constructor <;> linarith⟩
    obtain ⟨u, v, rfl⟩ := pair_representation hy
    refine mem_iUnion.mpr ⟨(u, v), ?_⟩
    change _ < x ∧ x < _
    constructor <;> linarith [hxy.1, hxy.2]
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U
    (fun _ => isOpen_Ioo) hcover
  let N : ℝ := 1 + ∑ z ∈ F, (|(z.1 : ℝ)| + |(z.2 : ℝ)|)
  have hN : 0 < N := by
    have : 0 ≤ ∑ z ∈ F, (|(z.1 : ℝ)| + |(z.2 : ℝ)|) :=
      sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    dsimp [N]
    linarith
  refine ⟨F, ε / (4 * N), by positivity, ?_⟩
  intro α γ ha hg x hx
  obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (hF hx)
  have hc : |(z.1 : ℝ)| + |(z.2 : ℝ)| ≤ N := by
    have hs := single_le_sum
      (f := fun z : ℤ × ℤ => |(z.1 : ℝ)| + |(z.2 : ℝ)|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hz
    dsimp [N]
    linarith
  have herr : |(z.1 : ℝ) * (α - α₀) + (z.2 : ℝ) * (γ - γ₀)| ≤ ε / 4 := by
    calc
      _ ≤ |(z.1 : ℝ)| * |α - α₀| + |(z.2 : ℝ)| * |γ - γ₀| := by
        simpa only [abs_mul] using abs_add_le
          ((z.1 : ℝ) * (α - α₀)) ((z.2 : ℝ) * (γ - γ₀))
      _ ≤ (|(z.1 : ℝ)| + |(z.2 : ℝ)|) * (ε / (4 * N)) := by
        nlinarith [mul_le_mul_of_nonneg_left ha.le (abs_nonneg (z.1 : ℝ)),
          mul_le_mul_of_nonneg_left hg.le (abs_nonneg (z.2 : ℝ))]
      _ ≤ N * (ε / (4 * N)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ε / 4 := by field_simp [hN.ne']
  have hbase : |(z.1 : ℝ) * α₀ + (z.2 : ℝ) * γ₀ - x| < ε / 2 := by
    change _ < x ∧ x < _ at hzx
    exact abs_lt.mpr ⟨by linarith [hzx.2], by linarith [hzx.1]⟩
  refine ⟨z, hz, ?_⟩
  have ht := abs_add_le
    ((z.1 : ℝ) * (α - α₀) + (z.2 : ℝ) * (γ - γ₀))
    ((z.1 : ℝ) * α₀ + (z.2 : ℝ) * γ₀ - x)
  have he : (z.1 : ℝ) * (α - α₀) + (z.2 : ℝ) * (γ - γ₀) +
      ((z.1 : ℝ) * α₀ + (z.2 : ℝ) * γ₀ - x) =
      (z.1 : ℝ) * α + (z.2 : ℝ) * γ - x := by ring
  rw [he] at ht
  linarith

/-- One finite bound on the second coefficient survives both generator
perturbations; the first coefficient is nonnegative and O(Δ). All finite data
and the threshold precede X and Δ. There is no rate assumption on either limit. -/
theorem stable_positive_mesh {α γ : ℝ → ℝ} {α₀ γ₀ : ℝ}
    (hα₀ : 0 < α₀) (hγ₀ : 0 < γ₀)
    (hirr : Irrational (γ₀ / α₀))
    (hα : Tendsto α atTop (𝓝 α₀)) (hγ : Tendsto γ atTop (𝓝 γ₀)) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ D T : ℝ,
      ∀ X : ℝ, T ≤ X → ∀ Δ : ℝ, D ≤ Δ →
        ∃ a b : ℕ, b ≤ B ∧ (a : ℝ) ≤ 2 * Δ / α₀ ∧
          Δ - ε / 2 ≤ (a : ℝ) * α X + (b : ℝ) * γ X ∧
          (a : ℝ) * α X + (b : ℝ) * γ X ≤ Δ - ε / 4 := by
  intro ε hε
  classical
  obtain ⟨F, δ, hδ, hmesh⟩ := finite_stable_mesh hα₀ hirr (by positivity : 0 < ε / 8)
  let B₀ : ℕ := F.sup (fun z => z.2.natAbs)
  have hB (z : ℤ × ℤ) (hz : z ∈ F) : -(B₀ : ℤ) ≤ z.2 ∧ z.2 ≤ B₀ := by
    have h := le_sup (f := fun z : ℤ × ℤ => z.2.natAbs) hz
    have hl : -z.2 ≤ (z.2.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -z.2))
    have hu := Int.le_natAbs (a := z.2)
    have hc : (z.2.natAbs : ℤ) ≤ B₀ := by exact_mod_cast h
    exact ⟨by omega, by omega⟩
  have hevent : ∀ᶠ X : ℝ in atTop,
      |α X - α₀| < δ ∧ |γ X - γ₀| < δ ∧
      α₀ / 2 ≤ α X ∧ α X ≤ 2 * α₀ ∧ 0 < γ X ∧ γ X ≤ 2 * γ₀ := by
    filter_upwards [(Metric.tendsto_nhds.mp hα) δ hδ,
      (Metric.tendsto_nhds.mp hγ) δ hδ,
      hα.eventually (eventually_gt_nhds (by linarith : α₀ / 2 < α₀)),
      hα.eventually (eventually_lt_nhds (by linarith : α₀ < 2 * α₀)),
      hγ.eventually (eventually_gt_nhds hγ₀),
      hγ.eventually (eventually_lt_nhds (by linarith : γ₀ < 2 * γ₀))]
      with X ha hg hal hau hgl hgu
    exact ⟨by simpa only [dist_eq] using ha,
      by simpa only [dist_eq] using hg, hal.le, hau.le, hgl, hgu.le⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨2 * B₀, 4 * (B₀ : ℝ) * γ₀ + ε, T, ?_⟩
  intro X hXT Δ hΔ
  obtain ⟨ha, hg, hal, hau, hgl, hgu⟩ := hT X hXT
  have hapos : 0 < α X := by linarith
  let y := Δ - 3 * ε / 8 - (B₀ : ℝ) * γ X
  let n : ℤ := ⌊y / α X⌋
  let x : ℝ := y - (n : ℝ) * α X
  have hx : x ∈ Icc (0 : ℝ) (2 * α₀) :=
    ⟨Int.sub_floor_div_mul_nonneg y hapos,
      (Int.sub_floor_div_mul_lt y hapos).le.trans hau⟩
  obtain ⟨z, hz, hzx⟩ := hmesh (α X) (γ X) ha hg x hx
  let u : ℤ := n + z.1
  let v : ℤ := z.2 + B₀
  have hvi : 0 ≤ v ∧ v ≤ 2 * (B₀ : ℤ) := by
    obtain ⟨hl, hu⟩ := hB z hz
    dsimp [v]
    omega
  have happrox : |(u : ℝ) * α X + (v : ℝ) * γ X - (Δ - 3 * ε / 8)| < ε / 8 := by
    have he : (u : ℝ) * α X + (v : ℝ) * γ X - (Δ - 3 * ε / 8) =
        (z.1 : ℝ) * α X + (z.2 : ℝ) * γ X - x := by
      dsimp [u, v, x, y]
      push_cast
      ring
    rw [he]
    exact hzx
  obtain ⟨hl, hu⟩ := abs_lt.mp happrox
  have hlo : Δ - ε / 2 ≤ (u : ℝ) * α X + (v : ℝ) * γ X := by linarith
  have hup : (u : ℝ) * α X + (v : ℝ) * γ X ≤ Δ - ε / 4 := by linarith
  have hv0 : (0 : ℝ) ≤ v := by exact_mod_cast hvi.1
  have hvB : (v : ℝ) ≤ 2 * (B₀ : ℝ) := by exact_mod_cast hvi.2
  have hvg : (v : ℝ) * γ X ≤ 4 * (B₀ : ℝ) * γ₀ := by
    have hh := mul_le_mul hvB hgu hgl.le (by positivity : (0 : ℝ) ≤ 2 * B₀)
    nlinarith only [hh]
  have hu0 : (0 : ℝ) ≤ u := by
    have hmul : 0 ≤ (u : ℝ) * α X := by linarith
    exact nonneg_of_mul_nonneg_left hmul hapos
  have hui : 0 ≤ u := by exact_mod_cast hu0
  have hua : (u : ℝ) * (α₀ / 2) ≤ Δ := by
    have hg0 := mul_nonneg hv0 hgl.le
    have hh := mul_le_mul_of_nonneg_left hal hu0
    linarith
  have hub : (u : ℝ) ≤ 2 * Δ / α₀ := by
    apply (le_div_iff₀ hα₀).mpr
    nlinarith only [hua]
  have hucast : (u.toNat : ℝ) = (u : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hui
  have hvcast : (v.toNat : ℝ) = (v : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hvi.1
  refine ⟨u.toNat, v.toNat, ?_, ?_, ?_, ?_⟩
  · have hh : (v.toNat : ℝ) ≤ ((2 * B₀ : ℕ) : ℝ) := by
      push_cast
      rw [hvcast]
      exact hvB
    exact_mod_cast hh
  · simpa only [hucast] using hub
  · simpa only [hucast, hvcast] using hlo
  · simpa only [hucast, hvcast] using hup

#print axioms stable_positive_mesh
end D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup
