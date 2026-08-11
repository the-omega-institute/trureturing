/- GID: D5/S1/Dynamics/SolenoidCharacter
   generality: I
   mirror-B: D5/B/S1/Dynamics/SolenoidCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Solenoid characters are exactly the rational coordinate characters. -/

import D5.S1.Dynamics.UniversalSolenoidCompact
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

/- Provenance: the pinned library supplies the additive-circle covering map,
   unique continuous lifts, and real-linearity of continuous additive maps.
   It has no universal-solenoid character classification, so the finite
   coordinate argument and rational-slope equivalence are proved here. -/

namespace D5.S1.Dynamics.SolenoidCharacter

open AddSubgroup Filter Function Real Set Topology
open D5.S1.Dynamics

/-- Continuous additive characters of the universal solenoid. -/
abbrev Character := UniversalSolenoid →ₜ+ UnitAddCircle

/-- Evaluation at one positive coordinate. -/
private def coordinateProjection (m : ℕ+) :
    UniversalSolenoid →ₜ+ UnitAddCircle where
  toFun theta := theta.1 m
  map_zero' := rfl
  map_add' _ _ := rfl
  continuous_toFun :=
    (continuous_apply m).comp continuous_subtype_val

private def commonIndex (indices : Finset ℕ+) : ℕ+ :=
  ⟨indices.prod (fun m => m.1), Finset.prod_pos fun m _ => m.2⟩

private theorem divides_commonIndex {indices : Finset ℕ+} {m : ℕ+}
    (hm : m ∈ indices) : m.1 ∣ (commonIndex indices).1 := by
  exact Finset.dvd_prod_of_mem (fun k : ℕ+ => k.1) hm

private theorem exists_coordinate_kernel_subset
    {neighborhood : Set UniversalSolenoid}
    (hneighborhood : neighborhood ∈ nhds (0 : UniversalSolenoid)) :
    ∃ m : ℕ+,
      (coordinateProjection m).toAddMonoidHom.ker ≤ neighborhood := by
  change neighborhood ∈ @nhds UniversalSolenoid
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace (ℕ+ → UnitAddCircle))) 0 at hneighborhood
  rw [mem_nhds_induced] at hneighborhood
  rcases hneighborhood with ⟨ambient, hambient, hsubset⟩
  classical
  simp only [nhds_pi, Filter.mem_pi'] at hambient
  rcases hambient with ⟨indices, coordinateSets, hzero, hcoordinateSets⟩
  refine ⟨commonIndex indices, ?_⟩
  intro theta htheta
  apply hsubset
  apply hcoordinateSets
  intro m hm
  rcases divides_commonIndex hm with ⟨n, hn⟩
  have hnpos : 0 < n := by
    by_contra hnzero
    have : n = 0 := Nat.eq_zero_of_not_pos hnzero
    subst n
    simp only [mul_zero] at hn
    exact (Nat.ne_of_gt (commonIndex indices).2) hn
  let npos : ℕ+ := ⟨n, hnpos⟩
  have hindex :
      (⟨m.1 * npos.1, Nat.mul_pos m.2 npos.2⟩ : ℕ+) = commonIndex indices := by
    apply Subtype.ext
    exact hn.symm
  have hcoordinate : theta.1 m = 0 := by
    change theta.1 (commonIndex indices) = 0 at htheta
    rw [← hindex] at htheta
    rw [← theta.2 m npos]
    simp [htheta]
  rw [hcoordinate]
  exact mem_of_mem_nhds (hzero m)

private theorem exists_coordinate_kernel_le_character_kernel
    (chi : Character) :
    ∃ m : ℕ+,
      (coordinateProjection m).toAddMonoidHom.ker ≤
        chi.toAddMonoidHom.ker := by
  let neighborhood : Set UniversalSolenoid :=
    {theta | AddCircle.toCircle (chi theta) ∈
      Circle.centeredArc (Real.pi / 2)}
  have hopen : IsOpen neighborhood := by
    exact Circle.isOpen_centeredArc (Real.pi / 2) |>.preimage
      (AddCircle.continuous_toCircle.comp chi.continuous_toFun)
  have hzero : (0 : UniversalSolenoid) ∈ neighborhood := by
    change AddCircle.toCircle (chi (0 : UniversalSolenoid)) ∈
      Circle.centeredArc (Real.pi / 2)
    rw [show chi (0 : UniversalSolenoid) = 0 by simp,
      AddCircle.toCircle_zero]
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rcases exists_coordinate_kernel_subset (hopen.mem_nhds hzero) with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro theta htheta
  rw [AddMonoidHom.mem_ker]
  apply AddCircle.injective_toCircle one_ne_zero
  simp only [AddCircle.toCircle_zero]
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n hn
  have hnTheta : n • theta ∈
      (coordinateProjection m).toAddMonoidHom.ker := by
    rw [AddMonoidHom.mem_ker, map_nsmul,
      AddMonoidHom.mem_ker.mp htheta, nsmul_zero]
  have hmem := hm hnTheta
  change AddCircle.toCircle (chi (n • theta)) ∈
    Circle.centeredArc (Real.pi / 2) at hmem
  rw [map_nsmul, AddCircle.toCircle_nsmul] at hmem
  exact hmem

private def rationalDenominator (q : ℚ) : ℕ+ :=
  ⟨q.den, q.den_pos⟩

/-- The coordinate character represented by the reduced rational q.num/q.den. -/
noncomputable def rationalCharacter (q : ℚ) : Character where
  toFun theta := q.num • theta.1 (rationalDenominator q)
  map_zero' := by
    change q.num • (0 : UnitAddCircle) = 0
    exact zsmul_zero q.num
  map_add' theta eta := by
    change q.num • (theta.1 _ + eta.1 _) =
      q.num • theta.1 _ + q.num • eta.1 _
    rw [zsmul_add]
  continuous_toFun :=
    ((continuous_apply (rationalDenominator q)).comp
      continuous_subtype_val).zsmul q.num

private theorem rationalCharacter_realFlow (q : ℚ) (t : ℝ) :
    rationalCharacter q (UniversalSolenoid.realFlow t) =
      ((q : ℝ) * t : UnitAddCircle) := by
  change q.num • ((t / (rationalDenominator q).1 : ℝ) : UnitAddCircle) = _
  change q.num • ((t / q.den : ℝ) : UnitAddCircle) = _
  rw [← AddCircle.coe_zsmul]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  rw [zsmul_eq_mul, Rat.cast_def]
  field_simp [q.den_nz]

private noncomputable def characterOnRealFlow (chi : Character) :
    C(ℝ, UnitAddCircle) where
  toFun t := chi (UniversalSolenoid.realFlow t)
  continuous_toFun := chi.continuous_toFun.comp
    UniversalSolenoid.continuous_realFlow

private theorem exists_real_lift (chi : Character) :
    ∃! lift : C(ℝ, ℝ),
      lift 0 = 0 ∧
      ((fun t : ℝ => (t : UnitAddCircle)) ∘ lift) =
        characterOnRealFlow chi := by
  apply (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
  simp [characterOnRealFlow, UniversalSolenoid.realFlow_zero]

private theorem real_lift_additive (chi : Character)
    (lift : C(ℝ, ℝ))
    (hlift : ((fun t : ℝ => (t : UnitAddCircle)) ∘ lift) =
      characterOnRealFlow chi)
    (hliftUnique : ∀ other : C(ℝ, ℝ),
      other 0 = 0 ∧
        ((fun t : ℝ => (t : UnitAddCircle)) ∘ other) =
          characterOnRealFlow chi →
      other = lift) :
    ∀ s t : ℝ, lift (s + t) = lift s + lift t := by
  intro s
  let translated : C(ℝ, ℝ) :=
    ⟨fun t => lift (s + t) - lift s,
      (lift.continuous.comp (continuous_const.add continuous_id)).sub
        continuous_const⟩
  have htranslatedZero : translated 0 = 0 := by
    simp [translated]
  have htranslatedLift :
      ((fun t : ℝ => (t : UnitAddCircle)) ∘ translated) =
        characterOnRealFlow chi := by
    funext t
    have hs := congrFun hlift s
    have hst := congrFun hlift (s + t)
    change ((lift s : ℝ) : UnitAddCircle) =
      chi (UniversalSolenoid.realFlow s) at hs
    change ((lift (s + t) : ℝ) : UnitAddCircle) =
      chi (UniversalSolenoid.realFlow (s + t)) at hst
    change ((lift (s + t) - lift s : ℝ) : UnitAddCircle) =
      chi (UniversalSolenoid.realFlow t)
    calc
      ((lift (s + t) - lift s : ℝ) : UnitAddCircle) =
          ((lift (s + t) : ℝ) : UnitAddCircle) -
            ((lift s : ℝ) : UnitAddCircle) := by rw [AddCircle.coe_sub]
      _ = chi (UniversalSolenoid.realFlow (s + t)) -
            chi (UniversalSolenoid.realFlow s) := by rw [hst, hs]
      _ = chi (UniversalSolenoid.realFlow t) := by
        rw [UniversalSolenoid.realFlow_add, map_add]
        simp
  have heq : translated = lift :=
    hliftUnique translated ⟨htranslatedZero, htranslatedLift⟩
  intro t
  have := congrFun (congrArg DFunLike.coe heq) t
  change lift (s + t) - lift s = lift t at this
  linarith

private theorem character_realFlow_has_rational_slope
    (chi : Character) :
    ∃ q : ℚ, ∀ t : ℝ,
      chi (UniversalSolenoid.realFlow t) =
        ((q : ℝ) * t : UnitAddCircle) := by
  rcases exists_real_lift chi with ⟨lift, hlift, hliftUnique⟩
  let liftHom : ℝ →+ ℝ :=
    { toFun := lift
      map_zero' := hlift.1
      map_add' := real_lift_additive chi lift hlift.2 hliftUnique }
  have hliftLinear (t : ℝ) : lift t = t * lift 1 := by
    have hlinear := map_real_smul liftHom lift.continuous t (1 : ℝ)
    simpa [liftHom, smul_eq_mul] using hlinear
  rcases exists_coordinate_kernel_le_character_kernel chi with ⟨m, hm⟩
  have hcoordinate : UniversalSolenoid.realFlow (m.1 : ℝ) ∈
      (coordinateProjection m).toAddMonoidHom.ker := by
    rw [AddMonoidHom.mem_ker]
    change (((m.1 : ℝ) / m.1 : ℝ) : UnitAddCircle) = 0
    rw [div_self (by exact_mod_cast (Nat.ne_of_gt m.2))]
    exact AddCircle.coe_period (1 : ℝ)
  have hcharacter :
      chi (UniversalSolenoid.realFlow (m.1 : ℝ)) = 0 :=
    AddMonoidHom.mem_ker.mp (hm hcoordinate)
  have hliftM := congrFun hlift.2 (m.1 : ℝ)
  change ((lift (m.1 : ℝ) : ℝ) : UnitAddCircle) =
    chi (UniversalSolenoid.realFlow (m.1 : ℝ)) at hliftM
  have hliftMZero : ((lift (m.1 : ℝ) : ℝ) : UnitAddCircle) = 0 :=
    hliftM.trans hcharacter
  rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hliftMZero with ⟨z, hz⟩
  have hslope : lift 1 = (z : ℝ) / m.1 := by
    rw [hliftLinear] at hz
    simp only [zsmul_eq_mul, mul_one] at hz
    rw [eq_div_iff (by exact_mod_cast (Nat.ne_of_gt m.2))]
    nlinarith
  refine ⟨(z : ℚ) / m.1, ?_⟩
  intro t
  have hliftT := congrFun hlift.2 t
  change ((lift t : ℝ) : UnitAddCircle) =
    chi (UniversalSolenoid.realFlow t) at hliftT
  rw [← hliftT, hliftLinear, hslope]
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  norm_num
  ring

private theorem character_ext_of_realFlow
    {chi psi : Character}
    (h : ∀ t : ℝ,
      chi (UniversalSolenoid.realFlow t) =
        psi (UniversalSolenoid.realFlow t)) :
    chi = psi := by
  apply ContinuousAddMonoidHom.ext
  intro theta
  have heq := UniversalSolenoid.denseRange_realFlow.equalizer
    chi.continuous_toFun psi.continuous_toFun (funext h)
  exact congrFun heq theta

/-- Rational slopes, sent additively to their coordinate characters. -/
noncomputable def rationalCharacterHom : ℚ →+ Character where
  toFun := rationalCharacter
  map_zero' := by
    apply character_ext_of_realFlow
    intro t
    rw [rationalCharacter_realFlow]
    simp
  map_add' q r := by
    apply character_ext_of_realFlow
    intro t
    rw [rationalCharacter_realFlow, ContinuousAddMonoidHom.add_apply,
      rationalCharacter_realFlow, rationalCharacter_realFlow]
    rw [Rat.cast_add, add_mul, AddCircle.coe_add]

private theorem real_slopes_unique {c d : ℝ}
    (h : ∀ t : ℝ,
      ((c * t : ℝ) : UnitAddCircle) =
        ((d * t : ℝ) : UnitAddCircle)) :
    c = d := by
  by_contra hne
  let t : ℝ := 1 / (2 * (c - d))
  have heq := h t
  have hzero : (((c - d) * t : ℝ) : UnitAddCircle) = 0 := by
    calc
      (((c - d) * t : ℝ) : UnitAddCircle) =
          ((c * t - d * t : ℝ) : UnitAddCircle) := by ring_nf
      _ = ((c * t : ℝ) : UnitAddCircle) -
          ((d * t : ℝ) : UnitAddCircle) := by rw [AddCircle.coe_sub]
      _ = 0 := sub_eq_zero.mpr heq
  have hhalf : (c - d) * t = (1 / 2 : ℝ) := by
    dsimp [t]
    field_simp [sub_ne_zero.mpr hne]
  rw [hhalf] at hzero
  rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero with ⟨z, hz⟩
  have hz' : (2 : ℝ) * z = 1 := by
    norm_num [zsmul_eq_mul] at hz
    linarith
  have : (2 : ℤ) * z = 1 := by exact_mod_cast hz'
  omega

/-- Every continuous character of the universal solenoid is represented by
exactly one rational slope, acting through its reduced denominator coordinate. -/
theorem continuous_solenoid_characters_are_rational :
    Function.Bijective rationalCharacterHom := by
  constructor
  · intro q r hqr
    have hcast : (q : ℝ) = (r : ℝ) := by
      apply real_slopes_unique
      intro t
      rw [← rationalCharacter_realFlow, ← rationalCharacter_realFlow]
      exact congrArg (fun chi : Character =>
        chi (UniversalSolenoid.realFlow t)) hqr
    exact_mod_cast hcast
  · intro chi
    rcases character_realFlow_has_rational_slope chi with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply character_ext_of_realFlow
    intro t
    exact (rationalCharacter_realFlow q t).trans (hq t).symm

/-- The additive character group of the universal solenoid is equivalent to
the additive group of rational numbers. -/
noncomputable def characterEquivRational :
    Character ≃+ ℚ :=
  (AddEquiv.ofBijective rationalCharacterHom
    continuous_solenoid_characters_are_rational).symm

end D5.S1.Dynamics.SolenoidCharacter
