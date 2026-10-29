/- GID: D5/S1/Solenoid/DyadicTimeSeparation
   generality: I
   mirror-B: D5/B/S1/Solenoid/DyadicTimeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dyadic solenoid separates algebraic rational time from continuous time. -/

import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.SpecificLimits.Basic

/-! The dyadic inverse limit and its torsion point separate algebraic and continuous time. -/

noncomputable section

namespace D5.S1.Solenoid

/-- Compatible circle coordinates under doubling. The topology is inherited from the product. -/
def dyadicSubgroup : AddSubgroup (ℕ → AddCircle (1 : ℝ)) where
  carrier := {x | ∀ n, 2 • x (n + 1) = x n}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy n; simp only [Pi.add_apply, nsmul_add, hx n, hy n]
  neg_mem' := by intro x hx n; simpa using congrArg Neg.neg (hx n)

abbrev DyadicSolenoid := dyadicSubgroup

namespace DyadicSolenoid

private theorem closed_carrier : IsClosed (dyadicSubgroup : Set (ℕ → AddCircle (1 : ℝ))) := by
  change IsClosed {x : ℕ → AddCircle (1 : ℝ) | ∀ n, 2 • x (n + 1) = x n}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun n => isClosed_eq (by fun_prop) (by fun_prop)

instance : CompactSpace DyadicSolenoid := closed_carrier.isClosedEmbedding_subtypeVal.compactSpace

/-- The real flow has coordinate `t / 2^n` modulo one. -/
def realFlow : ℝ →+ DyadicSolenoid where
  toFun t := ⟨fun n => ((t / (2 : ℝ)^n : ℝ) : AddCircle (1 : ℝ)), by
    intro n
    rw [← AddCircle.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul, pow_succ]
    field_simp
    ring⟩
  map_zero' := by ext n; simp
  map_add' s t := by ext n; simp [add_div]

private theorem continuous_flow : Continuous realFlow := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun n => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_id.div_const ((2 : ℝ)^n))

private theorem coordinates (x : DyadicSolenoid) (n k : ℕ) :
    (2 ^ k : ℕ) • x.1 (n + k) = x.1 n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, show n + (k + 1) = (n + k) + 1 by omega,
      x.2 (n + k)]
    exact ih

private theorem finite_match (x : DyadicSolenoid) (s : Finset ℕ) :
    ∃ t : ℝ, ∀ n ∈ s, (realFlow t).1 n = x.1 n := by
  let N := s.sup id
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) (x.1 N)
  change (r : AddCircle (1 : ℝ)) = x.1 N at hr
  refine ⟨(2 : ℝ)^N * r, ?_⟩
  intro n hn
  have hnN : n ≤ N := Finset.le_sup (f := id) hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnN
  have heq : (realFlow ((2 : ℝ)^N * r)).1 n = (2 ^ k : ℕ) • (r : AddCircle (1 : ℝ)) := by
    change (((2 : ℝ)^N * r / 2^n : ℝ) : AddCircle (1 : ℝ)) = _
    rw [← AddCircle.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul, hk, pow_add]
    push_cast
    field_simp
  rw [heq, hr, hk]
  exact coordinates x n k

private theorem dense_flow : DenseRange realFlow := by
  rw [DenseRange]
  intro x
  rw [mem_closure_iff_nhds']
  intro neighborhood hn
  change neighborhood ∈ @nhds DyadicSolenoid
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace (ℕ → AddCircle (1 : ℝ)))) x at hn
  rw [mem_nhds_induced] at hn
  obtain ⟨ambient, ha, hsub⟩ := hn
  classical
  simp only [nhds_pi, Filter.mem_pi'] at ha
  obtain ⟨indices, coordinateSets, hx, hc⟩ := ha
  obtain ⟨t, ht⟩ := finite_match x indices
  refine ⟨⟨realFlow t, ⟨t, rfl⟩⟩, hsub ?_⟩
  apply hc
  intro n hn
  rw [ht n hn]
  exact mem_of_mem_nhds (hx n)

instance : PreconnectedSpace DyadicSolenoid :=
  DenseRange.preconnectedSpace dense_flow continuous_flow

instance : ConnectedSpace DyadicSolenoid := ⟨⟨0⟩⟩

private theorem multiply_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (fun x : DyadicSolenoid => m • x) := by
  have hclosed : IsClosed (Set.range (fun x : DyadicSolenoid => m • x)) :=
    (isCompact_range (continuous_id.nsmul m)).isClosed
  have hsub : Set.range realFlow ⊆ Set.range (fun x : DyadicSolenoid => m • x) := by
    rintro _ ⟨t, rfl⟩
    refine ⟨realFlow (t / m), ?_⟩
    change m • realFlow (t / m) = realFlow t
    rw [← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]
  intro x
  exact (closure_minimal hsub hclosed) (dense_flow x)

private theorem no_two_torsion (x : DyadicSolenoid) (hx : 2 • x = 0) : x = 0 := by
  ext n
  have he := congrArg (fun y : DyadicSolenoid => y.1 (n + 1)) hx
  change 2 • x.1 (n + 1) = 0 at he
  rw [x.2 n] at he
  exact he

private def third : AddCircle (1 : ℝ) := ((1 / 3 : ℝ) : AddCircle (1 : ℝ))

private theorem third_three : 3 • third = 0 := by
  rw [third, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  norm_num

private theorem third_two : 2 • third = -third := by
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [show 3 = 2 + 1 from rfl, add_nsmul, one_nsmul] using third_three

/-- The nonzero alternating order-three point, with coordinate `(-1)^n / 3` modulo one. -/
def thirdPoint : DyadicSolenoid :=
  ⟨fun n => ((-1 : ℤ)^n) • third, by
    intro n
    simp only [pow_succ, mul_smul, neg_one_zsmul, smul_neg]
    rw [smul_comm, third_two, smul_neg, neg_neg]⟩

private theorem point_nonzero : thirdPoint ≠ 0 := by
  intro h
  have he := congrArg (fun x : DyadicSolenoid => x.1 0) h
  have ht : third = 0 := by simpa [thirdPoint] using he
  have hmem : (1 / 3 : ℝ) ∈ Set.Ico 0 1 := by constructor <;> norm_num
  have := (AddCircle.coe_eq_zero_iff_of_mem_Ico hmem).mp ht
  norm_num at this

private theorem point_three : 3 • thirdPoint = 0 := by
  ext n
  change 3 • (((-1 : ℤ)^n) • third) = 0
  rw [smul_comm, third_three, smul_zero]

private theorem algebraic_time : ∃ phi : ℚ →+ DyadicSolenoid, phi 1 = thirdPoint := by
  let : DivisibleBy DyadicSolenoid ℕ :=
    divisibleByOfSMulRightSurj DyadicSolenoid ℕ
      (fun {n} hn => multiply_surjective n (Nat.pos_of_ne_zero hn))
  let : DivisibleBy DyadicSolenoid ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨phi, hp⟩ := (Module.Baer.of_divisible DyadicSolenoid).extension_property_addMonoidHom
    (Int.castAddHom ℚ) (by intro a b h; exact Int.cast_injective h)
    (zmultiplesHom DyadicSolenoid thirdPoint)
  refine ⟨phi, ?_⟩
  have := DFunLike.congr_fun hp (1 : ℤ)
  simpa using this

private theorem quarter_sequence (phi : ℚ →+ DyadicSolenoid) (hp : phi 1 = thirdPoint) :
    ∀ n : ℕ, phi ((1 / 4 : ℚ)^n) = thirdPoint := by
  have hinj2 : Function.Injective (fun x : DyadicSolenoid => 2 • x) := by
    intro x y he
    change 2 • x = 2 • y at he
    have hz : 2 • (x - y) = 0 := by rw [smul_sub, he, sub_self]
    exact sub_eq_zero.mp (no_two_torsion _ hz)
  have hinj4 : Function.Injective (fun x : DyadicSolenoid => 4 • x) := by
    intro x y he
    apply hinj2
    apply hinj2
    simpa only [← mul_smul, show (2 : ℕ) * 2 = 4 from rfl] using he
  have hfour : 4 • thirdPoint = thirdPoint := by
    simp only [show 4 = 3 + 1 from rfl, add_nsmul, one_nsmul, point_three, zero_add]
  intro n
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    apply hinj4
    change 4 • phi ((1 / 4 : ℚ)^(n + 1)) = 4 • thirdPoint
    rw [← map_nsmul, nsmul_eq_mul]
    have hq : (4 : ℚ) * (1 / 4 : ℚ)^(n + 1) = (1 / 4 : ℚ)^n := by
      rw [pow_succ]; ring
    norm_num only [Nat.cast_ofNat]
    rw [hq, ih, hfour]

private theorem discontinuous_time (phi : ℚ →+ DyadicSolenoid) (hp : phi 1 = thirdPoint) :
    ¬ Continuous phi := by
  intro hc
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℚ) ≤ 1 / 4 by norm_num) (show (1 / 4 : ℚ) < 1 by norm_num)
  have hlim := (hc.tendsto 0).comp ht
  have hconst : (fun n : ℕ => phi ((1 / 4 : ℚ)^n)) = fun _ => thirdPoint := by
    funext n
    exact quarter_sequence phi hp n
  change Filter.Tendsto (fun n : ℕ => phi ((1 / 4 : ℚ)^n))
    Filter.atTop (nhds (phi 0)) at hlim
  rw [hconst, map_zero] at hlim
  exact point_nonzero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- Algebraic rational time exists at the order-three point; every such choice has the
same discontinuity sequence, and neither rational nor real continuous time reaches it. -/
theorem dyadic_time_separation :
    CompactSpace DyadicSolenoid ∧ ConnectedSpace DyadicSolenoid ∧
    Continuous realFlow ∧ DenseRange realFlow ∧
    (∀ m : ℕ, 0 < m → Function.Surjective (fun x : DyadicSolenoid => m • x)) ∧
    (∀ x : DyadicSolenoid, 2 • x = 0 → x = 0) ∧
    thirdPoint ≠ 0 ∧ 3 • thirdPoint = 0 ∧
    (∃ phi : ℚ →+ DyadicSolenoid, phi 1 = thirdPoint) ∧
    (∀ phi : ℚ →+ DyadicSolenoid, phi 1 = thirdPoint →
      (∀ n : ℕ, phi ((1 / 4 : ℚ)^n) = thirdPoint) ∧ ¬ Continuous phi) ∧
    (¬ ∃ psi : ℝ →+ DyadicSolenoid, Continuous psi ∧ psi 1 = thirdPoint) := by
  refine ⟨inferInstance, inferInstance, continuous_flow, dense_flow, multiply_surjective,
    no_two_torsion, point_nonzero, point_three, algebraic_time, ?_, ?_⟩
  · intro phi hp
    exact ⟨quarter_sequence phi hp, discontinuous_time phi hp⟩
  · rintro ⟨psi, hc, hp⟩
    let ratCast : ℚ →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom
    have hrat : Continuous ratCast := Rat.continuous_coe_real
    exact discontinuous_time (psi.comp ratCast) (by simpa [ratCast] using hp)
      (hc.comp hrat)

end DyadicSolenoid
end D5.S1.Solenoid
