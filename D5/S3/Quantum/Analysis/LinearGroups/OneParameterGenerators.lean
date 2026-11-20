/- GID: D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Escape lemma; one-parameter generators of a locally compact group form a Lie algebra. -/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Sequences

/-!
# One-parameter generators of a locally compact group in a Banach algebra

Let `A` be a real Banach algebra, `G` a locally compact topological group and `ρ : G →* Aˣ` a
continuous injective homomorphism. An element `X : A` is a one-parameter generator
(`IsOneParameterGenerator`) if the curve `t ↦ exp (t • X)` lifts through `ρ` to a continuous
curve `γ : ℝ → G`.

* Escape lemma (`isOneParameterGenerator_of_mapClusterPt`): if `g i → 1` in `G` along a filter
  and eventually `ρ (g i) = exp (Y i)` with `Y i → 0`, then every cluster point of the directions
  `‖Y i‖⁻¹ • Y i` is a generator. Local compactness of `G` and injectivity of `ρ` replace the
  closedness of a linear group used in the closed-subgroup theorem: on a compact neighbourhood
  `V` of `1` the map `ρ` reflects convergence, the powers `g i ^ n` stay in `V` as long as
  `n * ‖Y i‖` is small, and limits of `ρ (g i ^ n)` are values of `ρ` on `V`.
* The set of generators is closed (`isClosed_setOf_isOneParameterGenerator`) and stable under
  real multiples (`IsOneParameterGenerator.smul`).
* Sums (`IsOneParameterGenerator.add`): if a curve `c` in `G` through `1` has `ρ ∘ c`
  differentiable at `0` with velocity `D`, the local logarithms of `ρ (c s)` approach `0` along
  the direction of `D`, so `D` is a generator; the product of the curves of `X` and `Y` has
  velocity `X + Y`.
* Commutators (`IsOneParameterGenerator.commutator`): conjugating the curve of `Y` by the curve
  of `X` at time `s` lifts `exp (s • X) * Y * exp (s • -X)`, so these elements are generators;
  their difference quotients at `s = 0` are generators and converge to `X * Y - Y * X`.
* The generators form a Lie subalgebra `generatorSubalgebra` of `A` with the commutator bracket.
-/

namespace D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators

open Filter
open scoped Topology

section Generators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  {G : Type*} [TopologicalSpace G] [Group G]

/-- `X` generates a continuous one-parameter subgroup of `G` through `ρ`: the curve
`t ↦ exp (t • X)` lifts through `ρ` to a continuous curve in `G`. -/
def IsOneParameterGenerator (ρ : G →* Aˣ) (X : A) : Prop :=
  ∃ γ : ℝ → G, Continuous γ ∧ ∀ t : ℝ, ((ρ (γ t) : Aˣ) : A) = NormedSpace.exp (t • X)

/-- Real multiples of a generator are generators. -/
theorem IsOneParameterGenerator.smul {ρ : G →* Aˣ} {X : A} (hX : IsOneParameterGenerator ρ X)
    (c : ℝ) : IsOneParameterGenerator ρ (c • X) := by
  obtain ⟨γ, hγc, hγ⟩ := hX
  exact ⟨fun t => γ (t * c), hγc.comp (continuous_id.mul continuous_const),
    fun t => by rw [hγ, mul_smul]⟩

/-- The zero element is a generator, lifted by the constant curve at `1`. -/
private theorem isOneParameterGenerator_zero (ρ : G →* Aˣ) :
    IsOneParameterGenerator ρ (0 : A) :=
  ⟨fun _ => 1, continuous_const, fun t => by simp⟩

omit [NormedAlgebra ℝ A] in
/-- On a compact set `V`, a continuous injective homomorphism into the units reflects
convergence: if `f` eventually takes values in `V` and `ρ ∘ f` tends to `ρ a`, then `f`
tends to `a`. -/
private theorem tendsto_of_tendsto_val {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {V : Set G} (hV : IsCompact V) {ι : Type*} {l : Filter ι}
    {f : ι → G} (hf : ∀ᶠ i in l, f i ∈ V) {a : G}
    (h : Tendsto (fun i => ((ρ (f i) : Aˣ) : A)) l (𝓝 ((ρ a : Aˣ) : A))) :
    Tendsto f l (𝓝 a) := by
  refine hV.tendsto_nhds_of_unique_mapClusterPt hf fun x _ hx => ?_
  have hx' := hx.tendsto_comp ((Units.continuous_val.comp hc).tendsto x)
  exact hi (Units.ext (eq_of_nhds_neBot (hx'.clusterPt.neBot.mono (inf_le_inf_left _ h))))

/-- Uniform control of powers: for a compact neighbourhood `V` of `1` there are `δ > 0` and a
neighbourhood `U` of `1` such that `g ^ n ∈ V` whenever `g ∈ U`, `ρ g = exp Y` and
`n * ‖Y‖ ≤ δ`. -/
private theorem exists_pow_mem [CompleteSpace A] [IsTopologicalGroup G] {ρ : G →* Aˣ}
    (hc : Continuous ρ) (hi : Function.Injective ρ) {V : Set G} (hV : IsCompact V)
    (hV1 : V ∈ 𝓝 (1 : G)) :
    ∃ δ > 0, ∃ U ∈ 𝓝 (1 : G), ∀ g ∈ U, ∀ Y : A, ((ρ g : Aˣ) : A) = NormedSpace.exp Y →
      ∀ n : ℕ, (n : ℝ) * ‖Y‖ ≤ δ → g ^ n ∈ V := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨W, hW, hWW⟩ := exists_nhds_one_split hV1
  have hle : comap (fun x : G => ((ρ x : Aˣ) : A)) (𝓝 ((ρ 1 : Aˣ) : A)) ⊓ 𝓟 V ≤ 𝓝 (1 : G) :=
    tendsto_id'.1 (tendsto_of_tendsto_val (f := fun x => x) hc hi hV
      (mem_inf_of_right (mem_principal_self V)) (tendsto_comap.mono_left inf_le_left))
  obtain ⟨O, hO, hOW⟩ := mem_comap.1 (mem_inf_principal.1 (hle hW))
  rw [map_one, Units.val_one] at hO
  have hO' : NormedSpace.exp ⁻¹' O ∈ 𝓝 (0 : A) :=
    NormedSpace.exp_continuous.continuousAt.preimage_mem_nhds (by rwa [NormedSpace.exp_zero])
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.1 hO'
  refine ⟨ε / 2, half_pos hε, W, hW, fun g hg Y hY n => ?_⟩
  induction n with
  | zero => intro _; rw [pow_zero]; exact mem_of_mem_nhds hV1
  | succ n ih =>
    intro hn
    have hnY : (n : ℝ) * ‖Y‖ ≤ ε / 2 :=
      le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ n)) (norm_nonneg Y)) hn
    have hgn : ((ρ (g ^ n) : Aˣ) : A) = NormedSpace.exp ((n : ℝ) • Y) := by
      rw [map_pow, Units.val_pow_eq_pow_val, hY, ← NormedSpace.exp_nsmul,
        Nat.cast_smul_eq_nsmul]
    have hmemO : ((ρ (g ^ n) : Aˣ) : A) ∈ O := by
      rw [hgn]
      apply hεO
      rw [mem_ball_zero_iff, norm_smul, Real.norm_natCast]
      linarith
    have hgnW : g ^ n ∈ W := hOW hmemO (ih hnY)
    rw [pow_succ]
    exact hWW _ hgnW _ hg

/-- Cluster points of normalized logarithms give exponentials in the image of a compact
set, for times in `[0, δ]`. -/
private theorem exists_mem_eq_exp_smul [CompleteSpace A] {ρ : G →* Aˣ} (hc : Continuous ρ)
    {V : Set G} (hV : IsCompact V) {δ : ℝ} {U : Set G}
    (hU : ∀ g ∈ U, ∀ Y : A, ((ρ g : Aˣ) : A) = NormedSpace.exp Y →
      ∀ n : ℕ, (n : ℝ) * ‖Y‖ ≤ δ → g ^ n ∈ V)
    {ι : Type*} {l : Filter ι} [l.NeBot] {g : ι → G} {Y : ι → A}
    (hgU : ∀ᶠ i in l, g i ∈ U) (hY0 : Tendsto Y l (𝓝 0))
    (hY : ∀ᶠ i in l, ((ρ (g i) : Aˣ) : A) = NormedSpace.exp (Y i) ∧ Y i ≠ 0) {X : A}
    (hX : Tendsto (fun i => ‖Y i‖⁻¹ • Y i) l (𝓝 X)) {t : ℝ} (ht : 0 ≤ t) (htδ : t ≤ δ) :
    ∃ v ∈ V, ((ρ v : Aˣ) : A) = NormedSpace.exp (t • X) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hfloor : ∀ i, Y i ≠ 0 →
      t - ‖Y i‖ ≤ (⌊t / ‖Y i‖⌋₊ : ℝ) * ‖Y i‖ ∧ (⌊t / ‖Y i‖⌋₊ : ℝ) * ‖Y i‖ ≤ t := by
    intro i hYi
    have hpos : 0 < ‖Y i‖ := norm_pos_iff.2 hYi
    have h1 := Nat.lt_floor_add_one (t / ‖Y i‖)
    have h2 := Nat.floor_le (div_nonneg ht hpos.le)
    rw [div_lt_iff₀ hpos] at h1
    rw [le_div_iff₀ hpos] at h2
    constructor <;> nlinarith
  have hmem : ∀ᶠ i in l, g i ^ ⌊t / ‖Y i‖⌋₊ ∈ V := by
    filter_upwards [hgU, hY] with i hgi hYi
    exact hU (g i) hgi (Y i) hYi.1 _ ((hfloor i hYi.2).2.trans htδ)
  obtain ⟨v, hvV, hv⟩ := hV.exists_mapClusterPt_of_frequently hmem.frequently
  refine ⟨v, hvV, ?_⟩
  have hscal : Tendsto (fun i => (⌊t / ‖Y i‖⌋₊ : ℝ) * ‖Y i‖) l (𝓝 t) := by
    have hlow : Tendsto (fun i => t - ‖Y i‖) l (𝓝 t) := by
      simpa using tendsto_const_nhds.sub hY0.norm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hY] with i hYi
      exact (hfloor i hYi.2).1
    · filter_upwards [hY] with i hYi
      exact (hfloor i hYi.2).2
  have hlim : Tendsto (fun i => ((ρ (g i ^ ⌊t / ‖Y i‖⌋₊) : Aˣ) : A)) l
      (𝓝 (NormedSpace.exp (t • X))) := by
    refine (hscal.smul hX).exp.congr' ?_
    filter_upwards [hY] with i hYi
    rw [map_pow, Units.val_pow_eq_pow_val, hYi.1, ← NormedSpace.exp_nsmul, smul_smul, mul_assoc,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hYi.2), mul_one, Nat.cast_smul_eq_nsmul]
  have hv' := hv.tendsto_comp ((Units.continuous_val.comp hc).tendsto v)
  exact eq_of_nhds_neBot (hv'.clusterPt.neBot.mono (inf_le_inf_left _ hlim))

/-- A local lift on `[-δ, δ]` with values in a compact set extends to a continuous
one-parameter subgroup. -/
private theorem isOneParameterGenerator_of_forall_abs_le [CompleteSpace A]
    [IsTopologicalGroup G] {ρ : G →* Aˣ} (hc : Continuous ρ) (hi : Function.Injective ρ)
    {V : Set G} (hV : IsCompact V) {X : A} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| ≤ δ → ∃ v ∈ V, ((ρ v : Aˣ) : A) = NormedSpace.exp (t • X)) :
    IsOneParameterGenerator ρ X := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hval : ∀ x y : G, ((ρ x : Aˣ) : A) = ((ρ y : Aˣ) : A) → x = y :=
    fun x y hxy => hi (Units.ext hxy)
  have hrange : ∀ t : ℝ, ∃ x : G, ((ρ x : Aˣ) : A) = NormedSpace.exp (t • X) := by
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (|t| / δ)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hN
    have hsmall : |t / N| ≤ δ := by
      rw [abs_div, Nat.abs_cast, div_le_iff₀ hNpos]
      rw [div_lt_iff₀ hδ] at hN
      linarith
    obtain ⟨v, -, hv⟩ := h (t / N) hsmall
    refine ⟨v ^ N, ?_⟩
    rw [map_pow, Units.val_pow_eq_pow_val, hv, ← NormedSpace.exp_nsmul,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ t hNpos.ne']
  choose γ hγ using hrange
  have hγadd : ∀ s t : ℝ, γ (s + t) = γ s * γ t := fun s t => hval _ _ (by
    rw [map_mul, Units.val_mul, hγ, hγ, hγ, add_smul,
      NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left s).smul_right t)])
  have hγV : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ V := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with t ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    obtain ⟨v, hvV, hv⟩ := h t ht
    rw [hval (γ t) v (by rw [hγ, hv])]
    exact hvV
  have hγ0 : Tendsto γ (𝓝 0) (𝓝 1) := by
    refine tendsto_of_tendsto_val hc hi hV hγV ?_
    have : Tendsto (fun t : ℝ => NormedSpace.exp (t • X)) (𝓝 0)
        (𝓝 (NormedSpace.exp ((0 : ℝ) • X))) :=
      ((continuous_id.smul continuous_const).tendsto 0).exp
    simpa [hγ] using this
  refine ⟨γ, continuous_iff_continuousAt.2 fun t => ?_, hγ⟩
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 t)).sub_const t
  have h1 : Tendsto (fun s => γ t * γ (s - t)) (𝓝 t) (𝓝 (γ t * 1)) :=
    tendsto_const_nhds.mul (hγ0.comp hsub)
  rw [mul_one] at h1
  refine h1.congr fun s => ?_
  rw [← hγadd]
  congr 1
  ring

/-- Escape along an arbitrary filter: if `g i → 1`, `ρ (g i) = exp (Y i)` with `Y i → 0`,
`Y i ≠ 0`, and the directions `‖Y i‖⁻¹ • Y i` tend to `X`, then `X` is a generator. -/
private theorem isOneParameterGenerator_of_tendsto [CompleteSpace A] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {ρ : G →* Aˣ} (hc : Continuous ρ) (hi : Function.Injective ρ)
    {ι : Type*} {l : Filter ι} [l.NeBot] {g : ι → G} (hg : Tendsto g l (𝓝 1)) {Y : ι → A}
    (hY0 : Tendsto Y l (𝓝 0))
    (hY : ∀ᶠ i in l, ((ρ (g i) : Aˣ) : A) = NormedSpace.exp (Y i) ∧ Y i ≠ 0) {X : A}
    (hX : Tendsto (fun i => ‖Y i‖⁻¹ • Y i) l (𝓝 X)) : IsOneParameterGenerator ρ X := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨δ, hδ, U, hU1, hU⟩ := exists_pow_mem hc hi hV hV1
  refine isOneParameterGenerator_of_forall_abs_le hc hi hV hδ fun t ht => ?_
  rcases le_total 0 t with h0 | h0
  · exact exists_mem_eq_exp_smul hc hV hU (hg.eventually_mem hU1) hY0 hY hX h0
      ((le_abs_self t).trans ht)
  · have hginv : Tendsto (fun i => (g i)⁻¹) l (𝓝 1) := by simpa using hg.inv
    have hinv : ∀ᶠ i in l,
        ((ρ (g i)⁻¹ : Aˣ) : A) = NormedSpace.exp (-Y i) ∧ -Y i ≠ 0 := by
      filter_upwards [hY] with i hYi
      refine ⟨?_, neg_ne_zero.2 hYi.2⟩
      rw [map_inv]
      refine (Units.eq_inv_of_mul_eq_one_left ?_).symm
      rw [hYi.1, ← NormedSpace.exp_add_of_commute (Commute.refl (Y i)).neg_right,
        add_neg_cancel, NormedSpace.exp_zero]
    have hXneg : Tendsto (fun i => ‖-Y i‖⁻¹ • -Y i) l (𝓝 (-X)) := by
      simpa only [norm_neg, smul_neg] using hX.neg
    obtain ⟨v, hvV, hv⟩ := exists_mem_eq_exp_smul hc hV hU (hginv.eventually_mem hU1)
      (by simpa using hY0.neg) hinv hXneg (neg_nonneg.2 h0) ((neg_le_abs t).trans ht)
    exact ⟨v, hvV, by rw [hv, neg_smul_neg]⟩

variable [CompleteSpace A] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Escape lemma: if `g i → 1` along a filter and eventually `ρ (g i) = exp (Y i)` with
`Y i → 0`, then every cluster point of the directions `‖Y i‖⁻¹ • Y i` along that filter is a
one-parameter generator. Indices with `Y i = 0` contribute the direction `0`, which is a
generator. -/
theorem isOneParameterGenerator_of_mapClusterPt (ρ : G →* Aˣ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) {ι : Type*} {l : Filter ι} {g : ι → G}
    (hg : Tendsto g l (𝓝 1)) {Y : ι → A} (hY0 : Tendsto Y l (𝓝 0))
    (hY : ∀ᶠ i in l, ((ρ (g i) : Aˣ) : A) = NormedSpace.exp (Y i))
    {X : A} (hX : MapClusterPt X l (fun i => ‖Y i‖⁻¹ • Y i)) :
    IsOneParameterGenerator ρ X := by
  by_cases hX0 : X = 0
  · rw [hX0]
    exact isOneParameterGenerator_zero ρ
  obtain ⟨U, hUl, hUX⟩ := mapClusterPt_iff_ultrafilter.1 hX
  refine isOneParameterGenerator_of_tendsto hc hi (hg.mono_left hUl) (hY0.mono_left hUl) ?_ hUX
  filter_upwards [hUl hY, hUX.eventually_ne hX0] with i hi1 hi2
  refine ⟨hi1, fun h0 => hi2 ?_⟩
  rw [h0, smul_zero]

/-- The set of one-parameter generators is closed. -/
theorem isClosed_setOf_isOneParameterGenerator {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) : IsClosed {X : A | IsOneParameterGenerator ρ X} := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  refine IsSeqClosed.isClosed ?_
  intro Xn X hXn hlim
  by_cases hX0 : X = 0
  · rw [hX0]
    simpa using (hXn 0).smul 0
  choose γ hγc hγ using hXn
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hγ0 : ∀ n, γ n 0 = 1 := fun n => hi (Units.ext (by
    rw [hγ, zero_smul, NormedSpace.exp_zero, map_one, Units.val_one]))
  have hs : ∀ n : ℕ, ∃ s : ℝ, 0 < s ∧ s < 1 / ((n : ℝ) + 1) ∧ γ n s ∈ V := by
    intro n
    have hV' : γ n ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      (hγc n).continuousAt.preimage_mem_nhds (by rwa [hγ0 n])
    have hlt : Set.Iio (1 / ((n : ℝ) + 1)) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), γ n s ∈ V := nhdsWithin_le_nhds hV'
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 / ((n : ℝ) + 1) := nhdsWithin_le_nhds hlt
    have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hsV, hslt, hs0⟩ := (h1.and (h2.and h3)).exists
    exact ⟨s, hs0, hslt, hsV⟩
  choose s hs0 hs1 hsV using hs
  have hsl : Tendsto s atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hs0 n).le) (fun n => (hs1 n).le)
  have hYl : Tendsto (fun n => s n • Xn n) atTop (𝓝 0) := by
    simpa using hsl.smul hlim
  have hgl : Tendsto (fun n => γ n (s n)) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_val hc hi hV (Eventually.of_forall hsV) ?_
    simpa [hγ] using hYl.exp
  have hY : ∀ᶠ n in atTop, ((ρ (γ n (s n)) : Aˣ) : A) = NormedSpace.exp (s n • Xn n) ∧
      s n • Xn n ≠ 0 := by
    filter_upwards [hlim.eventually_ne hX0] with n hn
    exact ⟨hγ n (s n), smul_ne_zero (hs0 n).ne' hn⟩
  have hdir : Tendsto (fun n => ‖s n • Xn n‖⁻¹ • (s n • Xn n)) atTop (𝓝 (‖X‖⁻¹ • X)) := by
    refine ((hlim.norm.inv₀ (norm_ne_zero_iff.2 hX0)).smul hlim).congr fun n => ?_
    rw [norm_smul, Real.norm_of_nonneg (hs0 n).le, smul_smul, mul_inv, mul_comm (s n)⁻¹,
      mul_assoc, inv_mul_cancel₀ (hs0 n).ne', mul_one]
  have hgen := (isOneParameterGenerator_of_tendsto hc hi hgl hYl hY hdir).smul ‖X‖
  rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hX0), one_smul] at hgen

/-- Velocity lemma: if a curve `c` in `G` is continuous at `0` with `ρ (c 0) = 1` and
`s ↦ ρ (c s)` has derivative `D` at `0`, then `D` is a generator. -/
private theorem isOneParameterGenerator_of_hasDerivAt {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {c : ℝ → G} (hcc : ContinuousAt c 0)
    (h1 : ((ρ (c 0) : Aˣ) : A) = 1) {D : A}
    (hD : HasDerivAt (fun s => ((ρ (c s) : Aˣ) : A)) D 0) : IsOneParameterGenerator ρ D := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  by_cases hD0 : D = 0
  · rw [hD0]
    exact isOneParameterGenerator_zero ρ
  have hc0 : c 0 = 1 := hi (Units.ext (by rw [h1, map_one, Units.val_one]))
  -- a local logarithm: the local inverse of `exp` at `0`
  have hexp : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A) using 1
    ext
    simp
  set ell : A → A := hexp.localInverse NormedSpace.exp _ 0
  have hell0 : ell 1 = 0 := by
    simpa [ell, NormedSpace.exp_zero] using hexp.localInverse_apply_image
  have hell : HasFDerivAt ell (ContinuousLinearMap.id ℝ A) 1 := by
    simpa [ell, NormedSpace.exp_zero] using hexp.to_localInverse.hasFDerivAt
  have hinv : ∀ᶠ y in 𝓝 (1 : A), NormedSpace.exp (ell y) = y := by
    simpa [ell, NormedSpace.exp_zero] using hexp.eventually_right_inverse
  -- the logarithm `Z` of the curve has derivative `D` at `0`
  set Z : ℝ → A := fun s => ell ((ρ (c s) : Aˣ) : A)
  have hZ : HasDerivAt Z D 0 := by
    simpa [Z, Function.comp_def] using hell.comp_hasDerivAt_of_eq (0 : ℝ) hD h1.symm
  have hZ0 : Z 0 = 0 := by simp [Z, h1, hell0]
  have hslope : Tendsto (fun s : ℝ => s⁻¹ • Z s) (𝓝[>] 0) (𝓝 D) := by
    simpa [hZ0] using hZ.tendsto_slope_zero_right
  have hval : Tendsto (fun s : ℝ => ((ρ (c s) : Aˣ) : A)) (𝓝[>] 0) (𝓝 1) := by
    simpa [h1] using hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hP : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ((ρ (c s) : Aˣ) : A) = NormedSpace.exp (Z s) ∧ Z s ≠ 0 := by
    filter_upwards [hval.eventually hinv, hslope.eventually_ne hD0] with s hs hs'
    refine ⟨hs.symm, fun h => hs' ?_⟩
    rw [h, smul_zero]
  have hdir : Tendsto (fun s : ℝ => ‖Z s‖⁻¹ • Z s) (𝓝[>] 0) (𝓝 (‖D‖⁻¹ • D)) := by
    refine ((hslope.norm.inv₀ (norm_ne_zero_iff.2 hD0)).smul hslope).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hs), smul_smul, mul_inv, inv_inv,
      mul_comm s, mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), mul_one]
  have hg : Tendsto c (𝓝[>] 0) (𝓝 1) := by
    have h := hcc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [hc0] at h
    exact h
  have hY0 : Tendsto Z (𝓝[>] 0) (𝓝 0) := by
    have h := hZ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rw [hZ0] at h
    exact h
  have hgen := isOneParameterGenerator_of_tendsto hc hi hg hY0 hP hdir
  have hgen' := hgen.smul ‖D‖
  rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hD0), one_smul] at hgen'

/-- The sum of two one-parameter generators is a one-parameter generator. -/
theorem IsOneParameterGenerator.add {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {X Y : A} (hX : IsOneParameterGenerator ρ X)
    (hY : IsOneParameterGenerator ρ Y) : IsOneParameterGenerator ρ (X + Y) := by
  obtain ⟨γ, hγc, hγ⟩ := hX
  obtain ⟨β, hβc, hβ⟩ := hY
  refine isOneParameterGenerator_of_hasDerivAt hc hi (c := fun s => γ s * β s)
    (hγc.mul hβc).continuousAt (by simp [hγ, hβ]) ?_
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)
  simp only [map_mul, Units.val_mul, hγ, hβ]
  convert h using 1
  simp

/-- The commutator of two one-parameter generators is a one-parameter generator. -/
theorem IsOneParameterGenerator.commutator {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {X Y : A} (hX : IsOneParameterGenerator ρ X)
    (hY : IsOneParameterGenerator ρ Y) :
    IsOneParameterGenerator ρ (X * Y - Y * X) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨γ, hγc, hγ⟩ := hX
  have hinv : ∀ s : ℝ, (((ρ (γ s))⁻¹ : Aˣ) : A) = NormedSpace.exp (s • -X) := fun s =>
    Units.inv_eq_of_mul_eq_one_right (by
      rw [hγ, ← NormedSpace.exp_add_of_commute
        (((Commute.refl X).neg_right.smul_left s).smul_right s), ← smul_add, add_neg_cancel,
        smul_zero, NormedSpace.exp_zero])
  -- conjugates of `Y` by the curve of `X` are generators
  have hconj : ∀ s : ℝ, IsOneParameterGenerator ρ
      (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X)) := by
    intro s
    obtain ⟨β, hβc, hβ⟩ := hY
    refine ⟨fun t => γ s * β t * (γ s)⁻¹, (continuous_const.mul hβc).mul continuous_const,
      fun t => ?_⟩
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, hβ,
      ← NormedSpace.exp_units_conj, ← hγ s, ← hinv s, mul_smul_comm, smul_mul_assoc]
  -- the derivative of the conjugates at `0` is the commutator
  have hderiv : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X))
      (X * Y - Y * X) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
    convert h using 1
    simp [sub_eq_add_neg]
  have hlim := hderiv.tendsto_slope_zero
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hlim
  refine (isClosed_setOf_isOneParameterGenerator hc hi).mem_of_tendsto hlim
    (Eventually.of_forall fun t => ?_)
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y]
  exact ((hconj t).add hc hi (hY.smul (-1))).smul t⁻¹

section LieSubalgebra

attribute [local instance] LieRing.ofAssociativeRing

/-- The Lie subalgebra of one-parameter generators. -/
noncomputable def generatorSubalgebra (ρ : G →* Aˣ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) : LieSubalgebra ℝ A where
  carrier := {X | IsOneParameterGenerator ρ X}
  add_mem' := fun hX hY => hX.add hc hi hY
  zero_mem' := isOneParameterGenerator_zero ρ
  smul_mem' := fun c _ hX => hX.smul c
  lie_mem' := fun hX hY => by
    rw [Ring.lie_def]
    exact hX.commutator hc hi hY

end LieSubalgebra

end Generators

end D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
