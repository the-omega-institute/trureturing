/- GID: D5/S3/StatisticalMechanics/InversePowerLineBasics
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/InversePowerLineBasics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered inverse-power configurations and affine lattices. -/

/-
admission_basis: escape-witness
question_answered: https://github.com/the-omega-institute/trureturing/issues/27202
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27401
IsSEquilibrium:
  proof_shape: bind-only; escape_witness: none.
  consumers: equilibrium_has_right, equilibrium_has_left, equilibrium_enumeration,
    equilibrium_indexed_force, equilibrium_indexed_total, progression_equilibrium,
    equilibrium_exists, InversePowerLineEquilibria.claim,
    InversePowerLineEquilibria.equilibrium_is_progression, InversePowerLineEquilibria.result.
arithmeticProgression:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_nontrivial, progression_locally_finite, progression_puncture_equiv,
    progression_equilibrium, equilibrium_exists, InversePowerLineEquilibria.claim,
    InversePowerLineEquilibria.equilibrium_is_progression, InversePowerLineEquilibria.result.
equilibrium_has_right:
  proof_shape: content; escape_witness: equilibrium_has_right.
  consumers: equilibrium_enumeration.
equilibrium_has_left:
  proof_shape: content; escape_witness: equilibrium_has_left.
  consumers: equilibrium_enumeration.
equilibrium_enumeration:
  proof_shape: content; escape_witness: equilibrium_has_right.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
indexedForce:
  proof_shape: bind-only; escape_witness: none.
  consumers: equilibrium_indexed_force, InversePowerLineConductance.force_difference_nonneg,
    InversePowerLineConductance.adjacent_force_loss,
    InversePowerLineConductance.equilibrium_gap_ratio,
    InversePowerLineConductance.equilibrium_gap_reverse,
    InversePowerLineConductance.conductance_force_difference,
    InversePowerLineConductance.gaps_harmonic_difference,
    InversePowerLineConductance.gaps_harmonic,
    InversePowerLineEquilibria.equilibrium_is_progression.
enumeration_puncture_equiv:
  proof_shape: bind-only; escape_witness: none.
  consumers: equilibrium_indexed_force, equilibrium_indexed_total.
equilibrium_indexed_force:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
equilibrium_indexed_total:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
constant_gap_affine:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.equilibrium_is_progression.
progression_injective:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_nontrivial, progression_puncture_equiv.
progression_nontrivial:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_equilibrium.
progression_locally_finite:
  proof_shape: content; escape_witness: progression_locally_finite.
  consumers: progression_equilibrium.
signed_lattice_hasSum:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_equilibrium.
positive_scale_sign:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_equilibrium.
progression_puncture_equiv:
  proof_shape: bind-only; escape_witness: none.
  consumers: progression_equilibrium.
progression_equilibrium:
  proof_shape: content; escape_witness: progression_locally_finite.
  consumers: equilibrium_exists, InversePowerLineEquilibria.result.
equilibrium_exists:
  proof_shape: content; escape_witness: progression_locally_finite.
  consumers: InversePowerLineEquilibria.result.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Basic.Real.Sign
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Ordered configurations and affine inverse-power equilibria
-/

namespace D5.S3.StatisticalMechanics.InversePowerLineBasics



def IsSEquilibrium (s : ℝ) (X : Set ℝ) : Prop :=
  1 < s ∧
    X.Nontrivial ∧
    (∀ u v : ℝ, (X ∩ Set.Icc u v).Finite) ∧
    ∀ x : ℝ, x ∈ X →
      Summable (fun y : {y : ℝ // y ∈ X ∧ y ≠ x} =>
        Real.rpow |(y : ℝ) - x| (-s)) ∧
      HasSum (fun y : {y : ℝ // y ∈ X ∧ y ≠ x} =>
        Real.sign ((y : ℝ) - x) * Real.rpow |(y : ℝ) - x| (-s)) 0

/-- The set {α n + β : n ∈ ℤ} from Theorem 1.2. -/
def arithmeticProgression (α β : ℝ) : Set ℝ :=
  Set.range (fun n : ℤ => α * (n : ℝ) + β)

private theorem equilibrium_has_right {s : ℝ} {X : Set ℝ}
    (hX : IsSEquilibrium s X) {x : ℝ} (hx : x ∈ X) :
    ∃ y ∈ X, x < y := by
  by_contra hright
  push Not at hright
  have hex : ∃ y ∈ X, y ≠ x := hX.2.1.exists_ne x
  obtain ⟨y, hy, hyx⟩ := hex
  have hforce := (hX.2.2.2 x hx).2
  have hneg (z : {y : ℝ // y ∈ X ∧ y ≠ x}) :
      Real.sign ((z : ℝ) - x) * Real.rpow |(z : ℝ) - x| (-s) < 0 := by
    have hz : (z : ℝ) < x := lt_of_le_of_ne (hright z z.property.1) z.property.2
    rw [Real.sign_of_neg (sub_neg.mpr hz)]
    have hp := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr z.property.2)) (-s)
    simpa only [neg_one_mul, Real.rpow_eq_pow] using (neg_lt_zero.mpr hp)
  have hlt := hasSum_lt
    (f := fun _ : {y : ℝ // y ∈ X ∧ y ≠ x} => (0 : ℝ))
    (g := fun z => -(Real.sign ((z : ℝ) - x) * Real.rpow |(z : ℝ) - x| (-s)))
    (fun z => (neg_pos.mpr (hneg z)).le)
    (i := ⟨y, hy, hyx⟩) (neg_pos.mpr (hneg ⟨y, hy, hyx⟩))
    hasSum_zero hforce.neg
  norm_num at hlt

private theorem equilibrium_has_left {s : ℝ} {X : Set ℝ}
    (hX : IsSEquilibrium s X) {x : ℝ} (hx : x ∈ X) :
    ∃ y ∈ X, y < x := by
  by_contra hleft
  push Not at hleft
  have hex : ∃ y ∈ X, y ≠ x := hX.2.1.exists_ne x
  obtain ⟨y, hy, hyx⟩ := hex
  have hforce := (hX.2.2.2 x hx).2
  have hpos (z : {y : ℝ // y ∈ X ∧ y ≠ x}) :
      0 < Real.sign ((z : ℝ) - x) * Real.rpow |(z : ℝ) - x| (-s) := by
    have hz : x < (z : ℝ) := lt_of_le_of_ne (hleft z z.property.1) z.property.2.symm
    rw [Real.sign_of_pos (sub_pos.mpr hz), one_mul]
    exact Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr z.property.2)) (-s)
  have hlt := hasSum_lt
    (f := fun _ : {y : ℝ // y ∈ X ∧ y ≠ x} => (0 : ℝ))
    (g := fun z => Real.sign ((z : ℝ) - x) * Real.rpow |(z : ℝ) - x| (-s))
    (fun z => (hpos z).le)
    (i := ⟨y, hy, hyx⟩) (hpos ⟨y, hy, hyx⟩) hasSum_zero hforce
  norm_num at hlt

theorem equilibrium_enumeration {s : ℝ} {X : Set ℝ}
    (hX : IsSEquilibrium s X) :
    ∃ a : ℤ → ℝ, StrictMono a ∧ Set.range a = X := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hX.2.1
  letI : Nonempty X := ⟨⟨x, hx⟩⟩
  letI : NoMaxOrder X := ⟨fun x => by
    obtain ⟨y, hy, hxy⟩ := equilibrium_has_right hX x.property
    exact ⟨⟨y, hy⟩, hxy⟩⟩
  letI : NoMinOrder X := ⟨fun x => by
    obtain ⟨y, hy, hyx⟩ := equilibrium_has_left hX x.property
    exact ⟨⟨y, hy⟩, hyx⟩⟩
  letI : LocallyFiniteOrder X := LocallyFiniteOrder.ofFiniteIcc (fun a b => by
    have hf := (hX.2.2.1 a.val b.val).preimage (f := fun z : X => (z : ℝ))
      Subtype.val_injective.injOn
    convert hf using 1
    ext z
    simp only [Set.mem_Icc, Set.mem_preimage, Set.mem_inter_iff, z.property, true_and]
    rfl)
  letI := LinearLocallyFiniteOrder.succOrder X
  letI := LinearLocallyFiniteOrder.predOrder X
  let e : ℤ ≃o X := (orderIsoIntOfLinearSuccPredArch (ι := X)).symm
  refine ⟨fun n => (e n : ℝ), ?_, ?_⟩
  · intro n m hnm
    exact e.strictMono hnm
  · ext z
    constructor
    · rintro ⟨n, rfl⟩
      exact (e n).property
    · intro hz
      obtain ⟨n, hn⟩ := e.surjective ⟨z, hz⟩
      exact ⟨n, congrArg Subtype.val hn⟩

noncomputable def indexedForce (s : ℝ) (a : ℤ → ℝ) (n j : ℤ) : ℝ :=
  Real.sign (a j - a n) * |a j - a n| ^ (-s)

private noncomputable def enumeration_puncture_equiv {a : ℤ → ℝ} (ha : StrictMono a)
    {X : Set ℝ} (hX : Set.range a = X) (n : ℤ) :
    {j : ℤ // j ≠ n} ≃ {y : ℝ // y ∈ X ∧ y ≠ a n} :=
  Equiv.ofBijective (fun j => ⟨a j.val, ⟨hX ▸ ⟨j.val, rfl⟩,
    fun heq => j.property (ha.injective heq)⟩⟩) (by
    constructor
    · intro j k h
      apply Subtype.ext
      exact ha.injective (congrArg Subtype.val h)
    · rintro ⟨y, hy, hyn⟩
      obtain ⟨j, rfl⟩ := hX.symm ▸ hy
      exact ⟨⟨j, fun heq => hyn (by rw [heq])⟩, rfl⟩)

theorem equilibrium_indexed_force {s : ℝ} {X : Set ℝ}
    (hX : IsSEquilibrium s X) {a : ℤ → ℝ} (ha : StrictMono a) (hrange : Set.range a = X) :
    ∀ n : ℤ, HasSum (indexedForce s a n) 0 := by
  intro n
  have hn : a n ∈ X := hrange ▸ ⟨n, rfl⟩
  let e := enumeration_puncture_equiv ha hrange n
  have hindexed : HasSum (fun j : {j : ℤ // j ≠ n} => indexedForce s a n j.val) 0 := by
    have H := e.hasSum_iff.mpr (hX.2.2.2 (a n) hn).2
    change HasSum (fun j : {j : ℤ // j ≠ n} => indexedForce s a n j.val) 0 at H
    exact H
  apply (hasSum_subtype_iff_of_support_subset (f := indexedForce s a n) (s := {j : ℤ | j ≠ n}) ?_).mp hindexed
  intro j hj
  change j ≠ n
  intro heq
  subst j
  simpa [Function.mem_support, indexedForce] using hj

theorem equilibrium_indexed_total {s : ℝ} {X : Set ℝ}
    (hX : IsSEquilibrium s X) {a : ℤ → ℝ} (ha : StrictMono a) (hrange : Set.range a = X) :
    ∀ n : ℤ, Summable (fun j : ℤ => |a j - a n| ^ (-s)) := by
  intro n
  have hn : a n ∈ X := hrange ▸ ⟨n, rfl⟩
  let e := enumeration_puncture_equiv ha hrange n
  have hindexed : Summable (fun j : {j : ℤ // j ≠ n} => |a j.val - a n| ^ (-s)) := by
    have H := e.summable_iff.mpr (hX.2.2.2 (a n) hn).1
    change Summable (fun j : {j : ℤ // j ≠ n} => |a j.val - a n| ^ (-s)) at H
    exact H
  apply ((hasSum_subtype_iff_of_support_subset (f := fun j : ℤ => |a j - a n| ^ (-s)) (s := {j : ℤ | j ≠ n}) ?_).mp hindexed.hasSum).summable
  intro j hj
  change j ≠ n
  intro heq
  subst j
  have hs : s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hX.1)
  simpa [Function.mem_support, Real.zero_rpow (neg_ne_zero.mpr hs)] using hj

theorem constant_gap_affine {a : ℤ → ℝ} {α : ℝ}
    (hgap : ∀ n : ℤ, a (n + 1) - a n = α) :
    ∀ n : ℤ, a n = α * (n : ℝ) + a 0 := by
  have hp : Function.Periodic (fun n : ℤ => a n - α * (n : ℝ)) 1 := by
    intro n
    push_cast
    linarith [hgap n]
  intro n
  have h : a n - α * (n : ℝ) = a 0 := by simpa using hp.int_mul_eq n
  linarith

private theorem progression_injective {α β : ℝ} (hα : 0 < α) :
    Function.Injective (fun n : ℤ => α * (n : ℝ) + β) := by
  exact (((strictMono_id.const_mul hα).add_const β).comp Int.cast_strictMono).injective

private theorem progression_nontrivial {α β : ℝ} (hα : 0 < α) :
    (arithmeticProgression α β).Nontrivial := by
  have hinj := progression_injective (β := β) hα
  simpa only [arithmeticProgression, Set.image_univ] using
    (Set.nontrivial_univ : (Set.univ : Set ℤ).Nontrivial).image hinj

private theorem progression_locally_finite {α β : ℝ} (hα : 0 < α) (u v : ℝ) :
    (arithmeticProgression α β ∩ Set.Icc u v).Finite := by
  apply ((Set.finite_Icc (⌊(u - β) / α⌋ : ℤ) (⌈(v - β) / α⌉ : ℤ)).image
    (fun n : ℤ => α * (n : ℝ) + β)).subset
  rintro x ⟨⟨n, rfl⟩, hx⟩
  have hu := hx.1
  have hv := hx.2
  dsimp at hu hv
  refine ⟨n, ⟨?_, ?_⟩, rfl⟩
  · apply (Int.cast_le (R := ℝ)).mp
    exact (Int.floor_le ((u - β) / α)).trans ((div_le_iff₀ hα).mpr (by linarith))
  · apply (Int.cast_le (R := ℝ)).mp
    exact ((le_div_iff₀ hα).mpr (by linarith)).trans (Int.le_ceil ((v - β) / α))

private theorem signed_lattice_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : {n : ℤ // n ≠ 0} =>
      Real.sign (n : ℝ) * |(n : ℝ)| ^ (-s)) 0 := by
  let F : ℤ → ℝ := fun n => Real.sign (n : ℝ) * |(n : ℝ)| ^ (-s)
  have hF : Summable F := by
    apply (Real.summable_abs_int_rpow hs).of_norm_bounded
    intro n
    rcases Real.sign_apply_eq (n : ℝ) with h | h | h <;>
      simp [F, h, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (n : ℝ)) (-s))]
    exact Real.rpow_nonneg (abs_nonneg (n : ℝ)) (-s)
  have he := hF.hasSum.nat_add_neg
  have heq : (fun n : ℕ => F (n : ℤ) + F (-(n : ℤ))) = fun _ => (0 : ℝ) := by
    funext n
    simp [F, Real.sign_neg, abs_neg]
  rw [heq] at he
  have hz : (∑' n : ℤ, F n) = 0 := by
    simpa [F] using he.unique hasSum_zero
  have hfull : HasSum F 0 := hz ▸ hF.hasSum
  apply (hasSum_subtype_iff_of_support_subset (f := F) (s := {n : ℤ | n ≠ 0}) ?_).mpr hfull
  intro n hn
  change n ≠ 0
  intro hn0
  subst n
  simpa [Function.mem_support, F] using hn

private theorem positive_scale_sign {α x : ℝ} (hα : 0 < α) :
    Real.sign (α * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hα h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hα h)]

private noncomputable def progression_puncture_equiv {α β : ℝ} (hα : 0 < α) (k : ℤ) :
    {n : ℤ // n ≠ 0} ≃
      {y : ℝ // y ∈ arithmeticProgression α β ∧ y ≠ α * (k : ℝ) + β} :=
  Equiv.ofBijective
    (fun n => ⟨α * ((n.val + k : ℤ) : ℝ) + β,
      ⟨⟨n.val + k, rfl⟩, by
        intro h
        have ht := progression_injective hα h
        have hn : n.val = 0  := by exact add_eq_right.mp ht

        exact n.property hn⟩⟩)
    (by
      constructor
      · intro n m h
        apply Subtype.ext
        have hm := progression_injective hα (congrArg Subtype.val h)
        exact add_right_cancel hm
      · rintro ⟨y, ⟨⟨m, rfl⟩, hmk⟩⟩
        refine ⟨⟨m - k, ?_⟩, ?_⟩
        · intro h
          have : m = k := Int.eq_of_sub_eq_zero h
          exact hmk (by rw [this])
        · apply Subtype.ext
          simp)

theorem progression_equilibrium {s α β : ℝ} (hs : 1 < s) (hα : 0 < α) :
    IsSEquilibrium s (arithmeticProgression α β) := by
  refine ⟨hs, progression_nontrivial hα, progression_locally_finite hα, ?_⟩
  rintro x ⟨k, rfl⟩
  simp only [Real.rpow_eq_pow]
  let e := progression_puncture_equiv (β := β) hα k
  have hd (n : {n : ℤ // n ≠ 0}) :
      (e n : ℝ) - (α * (k : ℝ) + β) = α * (n : ℝ) := by
    change α * ((n.val + k : ℤ) : ℝ) + β - (α * (k : ℝ) + β) = _
    push_cast
    ring
  have hp (n : {n : ℤ // n ≠ 0}) :
      |(e n : ℝ) - (α * (k : ℝ) + β)| ^ (-s) =
        α ^ (-s) * |(n : ℝ)| ^ (-s) := by
    rw [hd, abs_mul, abs_of_pos hα, Real.mul_rpow hα.le (abs_nonneg _)]
  constructor
  · apply e.summable_iff.mp
    change Summable (fun n => |(e n : ℝ) - (α * (k : ℝ) + β)| ^ (-s))
    simp_rw [hp]
    exact Summable.mul_left _ ((Real.summable_abs_int_rpow hs).subtype (fun n : ℤ => n ≠ 0))
  · apply e.hasSum_iff.mp
    change HasSum (fun n => Real.sign ((e n : ℝ) - (α * (k : ℝ) + β)) *
      |(e n : ℝ) - (α * (k : ℝ) + β)| ^ (-s)) 0
    have heq (n : {n : ℤ // n ≠ 0}) :
        Real.sign ((e n : ℝ) - (α * (k : ℝ) + β)) *
        |(e n : ℝ) - (α * (k : ℝ) + β)| ^ (-s) =
        α ^ (-s) * (Real.sign (n : ℝ) * |(n : ℝ)| ^ (-s)) := by
      rw [hp, hd, positive_scale_sign hα]
      ring
    simp_rw [heq]
    simpa using HasSum.mul_left (α ^ (-s)) (signed_lattice_hasSum hs)

theorem equilibrium_exists {s : ℝ} (hs : 1 < s) :
    ∃ X : Set ℝ, IsSEquilibrium s X := by
  exact ⟨arithmeticProgression 1 0, progression_equilibrium hs (by norm_num)⟩

end D5.S3.StatisticalMechanics.InversePowerLineBasics
