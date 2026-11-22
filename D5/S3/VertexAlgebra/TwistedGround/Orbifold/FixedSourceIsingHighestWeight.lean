/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null coefficients and descendant relations for odd Ising highest weights. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

/-! The fourth and third null coefficients on the actual odd highest-weight space.
The coefficient recursion is transported from the earlier orbifold proof. Here
every iterate and translation of a source takes place in the fixed lattice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticeInvolution (FixedCarrier fixedMode fixedVacuum fixedTranslation)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open HalfFock.NormFourFirstGradeSpectrum (normFourFixedSource)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private fixedY_ncoeff mixed_vacuum from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField
open private mixedMode from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open scoped VertexOperator BigOperators

variable {D : LatticeData} {hu : IsUnit D.G.det} {a : Charge D} {s : ℂ}

local notation "Odd" => (paritySpace D hu (-1))
local notation "e" => normFourFixedSource D a s
local notation "L" => oddAxisMode D hu a s
local notation "F" => fun m => fixedMode D e (m+1)
local notation "ρ" => fun v n => (fixedParitySlice D hu (-1) v)[[n]]

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    AddCommGroup (paritySpace D hu (-1)) := (paritySpace D hu (-1)).addCommGroup

local instance (D : LatticeData) (hu : IsUnit D.G.det) :
    Module ℂ (paritySpace D hu (-1)) := (paritySpace D hu (-1)).module

local instance (D : LatticeData) :
    AddCommGroup (FixedCarrier D) := (LatticeInvolution.fixedSpace D).addCommGroup

local instance (D : LatticeData) :
    Module ℂ (FixedCarrier D) := (LatticeInvolution.fixedSpace D).module

private theorem odd_coefficient (v : FixedCarrier D) (n : ℤ) :
    (fixedParitySlice D hu (-1) v)[[n]] = mixedMode D hu n v := rfl

private theorem translate_descendant (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (v : FixedCarrier D) (k : ℤ) (hk : 2 ≤ k)
    (hv : F (-1) v = fixedTranslation D v) :
    F (-1) (F (-k) v) = fixedTranslation D (F (-k) v) := by
  have hop := fixed_virasoro D a s ha hs (-1) (-k)
  rw [ite_eq_right (show (-1 : ℤ) + -k ≠ 0 by omega), add_zero] at hop
  have h := LinearMap.congr_fun hop v
  simp only [LinearMap.smul_apply] at h
  change F (-1) (F (-k) v) - F (-k) (F (-1) v) = _ at h
  rw [hv] at h
  have cov := OriginalOrbifoldTranslation.vv_covariance D (-k+1) e v
  have hc : (((-1 : ℤ) : ℂ) - ((-k : ℤ) : ℂ)) = -((-k + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hc, show (-1 : ℤ) + -k = -k - 1 by omega] at h
  rw [show -k + 1 - 1 = (-k - 1) + 1 by omega] at cov
  exact sub_left_inj.mp (h.trans cov.symm)

private theorem commute_axis_zero (v : FixedCarrier D) (x : Odd) (q : ℤ)
    (hv : F (-1) v = fixedTranslation D v) :
    ρ v q (L (-1) x) = L (-1) (ρ v q x) + (q : ℂ) • ρ v (q-1) x := by
  have h := odd_commutator e v x 0 q
  rw [finsum_eq_single _ 0] at h
  · simp only [integerBinomial, Ring.choose_zero_right, Int.cast_one, one_smul,
      Nat.cast_zero, zero_add, sub_zero] at h
    change L (-1) (ρ v q x) - ρ v q (L (-1) x) = ρ (F (-1) v) q x at h
    rw [hv, OriginalOrbifoldTranslation.vm_translation] at h
    rw [← sub_sub_cancel (L (-1) (ρ v q x)) (ρ v q (L (-1) x)), h]
    simp only [neg_smul, sub_neg_eq_add]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

variable (x : ↥(paritySpace D hu (-1))) (h : ℂ)

include x

private theorem iterate_at_or_above_top
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0)
    (v : FixedCarrier D) (d k n : ℤ) (hn : d - 1 ≤ n)
    (high : ∀ q : ℤ, d ≤ q → ρ v q x = 0) :
    ρ (F (-k) v) n x = L (-k) (ρ v n x) - epsilon (1-k) •
      (ρ v (n+1-k) (L (-1) x) + (((k : ℂ)-1)*h) • ρ v (n-k) x) := by
  classical
  let term (i : ℕ) := ((-1 : ℂ)^i * integerBinomial (1-k) i) •
    (ρ e (1-k-i) (ρ v (n+i) x) - epsilon (1-k) • ρ v (n+(1-k)-i) (ρ e i x))
  have iter := odd_iterate e v x (1-k) n
  change ρ (fixedMode D e (1-k) v) n x = ∑ᶠ i : ℕ, term i at iter
  have hmode (y : Odd) : ρ e (1-k) y = L (-k) y := by
    rw [show 1-k = -k+1 by omega]
  rw [show 1-k = -k+1 by omega] at iter
  have ht (i : ℕ) (hi : 2 ≤ i) : ρ e i x = 0 := by
    have hz := hp ((i : ℤ)-1) (by omega)
    simpa only [oddAxisMode, show (i : ℤ)-1+1 = (i : ℤ) by omega] using hz
  have finite : (∑ᶠ i : ℕ, term i) = ∑ i ∈ Finset.range 2, term i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply Finset.mem_range.mpr
    by_contra hout
    exact hi (by simp [term, high (n+i) (by omega), ht i (by omega)])
  have t0 : term 0 = L (-k) (ρ v n x) - epsilon (1-k) • ρ v (n+1-k) (L (-1) x) := by
    simp only [term, Nat.cast_zero, sub_zero, add_zero, pow_zero, integerBinomial,
      Ring.choose_zero_right, Int.cast_one, mul_one, one_smul, show n+(1-k) = n+1-k by omega]
    rw [hmode]
    rfl
  have hw : (-1 : ℂ)^1 * integerBinomial (1-k) 1 = (k : ℂ)-1 := by
    simp only [integerBinomial, Ring.choose_one_right, pow_one, Int.cast_sub, Int.cast_one]
    ring
  have t1 : term 1 = -epsilon (1-k) • ((((k : ℂ)-1)*h) • ρ v (n-k) x) := by
    have hx' : ρ e 1 x = h • x := hx
    simp only [term, Nat.cast_one, high (n+1) (by omega : d ≤ n+1),
      map_zero, zero_sub, hw, hx', map_smul, smul_smul,
      ← neg_smul, show n+(1-k)-1 = n-k by omega]
    congr 1
    ring
  rw [iter, finite]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [t0, t1]
  module

private theorem two_term_iterate
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0)
    (v : FixedCarrier D) (d k n : ℤ) (hn : d ≤ n)
    (high : ∀ q : ℤ, d ≤ q → ρ v q x = 0) :
    ρ (F (-k) v) n x = -epsilon (1-k) •
      (ρ v (n+1-k) (L (-1) x) + (((k : ℂ)-1)*h) • ρ v (n-k) x) := by
  rw [iterate_at_or_above_top x h hx hp v d k n (by omega) high,
    high n hn, map_zero, zero_sub, neg_smul]

private def coefficientData (v : FixedCarrier D) (d : ℤ) (c b : ℂ) : Prop :=
  F (-1) v = fixedTranslation D v ∧
    (∀ q : ℤ, d ≤ q → ρ v q x = 0) ∧
    ρ v (d-1) x = c • x ∧ ρ v (d-2) x = b • L (-1) x

local notation "Data" => coefficientData (a := a) (s := s) x

private theorem vacuum_data : Data (fixedVacuum D) 0 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change fixedMode D e 0 (fixedVacuum D) = fixedTranslation D (fixedVacuum D)
    apply Subtype.ext
    have hz := LatticeInvolution.fixed_creativity D e 0 (by decide)
    rw [fixedY_ncoeff] at hz
    change _ = LatticeSugawaraConformal.translation D (LatticeAllStateField.vacuum D)
    exact (congrArg Subtype.val hz).trans (LatticeSugawaraConformal.translation_vacuum D).symm
  · intro q hq
    change mixedMode D hu q (fixedVacuum D) x = 0
    rw [mixed_vacuum, ite_eq_right (by omega)]
  · norm_num [odd_coefficient, mixed_vacuum]
  · norm_num [odd_coefficient, mixed_vacuum]

private theorem coefficient_step (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0)
    (v : FixedCarrier D) (d k : ℤ) (hk : 2 ≤ k) (c b : ℂ)
    (data : Data v d c b) :
    Data (F (-k) v) (d+k)
      (-epsilon (1-k) * ((d : ℂ) + ((k : ℂ)-1)*h) * c)
      (-epsilon (1-k) * (c + (((d : ℂ)-1) + ((k : ℂ)-1)*h)*b)) := by
  obtain ⟨translated, high, top, next⟩ := data
  have iterate (q : ℤ) (hq : d ≤ q) :=
    two_term_iterate x h hx hp v d k q hq high
  have commute (q : ℤ) :=
    commute_axis_zero v x q translated
  refine ⟨translate_descendant ha hs v k hk translated, ?_, ?_, ?_⟩
  · intro q hq
    rw [iterate q (by omega), commute (q+1-k), high (q+1-k) (by omega),
      high (q+1-k-1) (by omega), high (q-k) (by omega)]
    simp
  · rw [iterate (d+k-1) (by omega), show d+k-1+1-k = d by omega, show d+k-1-k = d-1 by omega,
      commute d, high d le_rfl, top]
    simp only [map_zero, zero_add]
    module
  · rw [iterate (d+k-2) (by omega), show d+k-2+1-k = d-1 by omega,
      show d+k-2-k = d-2 by omega, commute (d-1),
      show d-1-1 = d-2 by omega, top, next, map_smul]
    simp only [Int.cast_sub, Int.cast_one]
    module

/-- The fourth coefficient on an actual odd highest-weight vector. -/
theorem nullState_fourth_mode (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    ρ (nullState D a s) 4 x =
      (6 * (2*h-1) * (16*h-1)) • L (-1) x := by
  have step := coefficient_step x h ha hs hx hp
  have v0 := vacuum_data (a := a) (s := s) x
  have v2 : Data (F (-2) (fixedVacuum D)) 2 h 1 := by
    convert step _ 0 2 (by decide) 1 0 v0 using 1 <;> norm_num [epsilon]
  have v3 : Data (F (-3) (fixedVacuum D)) 3 (-2*h) (-1) := by
    convert step _ 0 3 (by decide) 1 0 v0 using 1 <;> norm_num [epsilon]
  have v22 := step _ 2 2 (by decide) h 1 v2
  have b222 := (step _ 4 2 (by decide) _ _ v22).2.2.2
  have b33 := (step _ 3 3 (by decide) _ _ v3).2.2.2
  have b42 := (step _ 2 4 (by decide) _ _ v2).2.2.2
  have b6 := (step _ 0 6 (by decide) _ _ v0).2.2.2
  norm_num [epsilon] at b222 b33 b42 b6
  simp only [nullState, odd_coefficient, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [odd_coefficient] at b222 b33 b42 b6
  norm_num only [Int.reduceNeg, Int.reduceAdd]
  rw [b222, b33, b42, b6]
  module

private def levelTwoData (v : FixedCarrier D) (d : ℤ) (c b f g : ℂ) : Prop :=
  Data v d c b ∧ ρ v (d-3) x = f • L (-1) (L (-1) x) + g • L (-2) x

local notation "LevelTwoData" => levelTwoData (a := a) (s := s) x

private theorem vacuum_level_two_data : LevelTwoData (fixedVacuum D) 0 1 0 0 0 :=
  ⟨vacuum_data (a := a) (s := s) x, by norm_num [odd_coefficient, mixed_vacuum]⟩

private theorem level_two_step (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0)
    (v : FixedCarrier D) (d k : ℤ) (hk : 2 ≤ k) (c b f g : ℂ)
    (data : LevelTwoData v d c b f g) :
    LevelTwoData (F (-k) v) (d+k)
      (-epsilon (1-k) * ((d : ℂ) + ((k : ℂ)-1)*h) * c)
      (-epsilon (1-k) * (c + (((d : ℂ)-1) + ((k : ℂ)-1)*h)*b))
      (-epsilon (1-k) * (b + (((d : ℂ)-2) + ((k : ℂ)-1)*h)*f))
      ((if k = 2 then c else 0) - epsilon (1-k) * (((d : ℂ)-2) + ((k : ℂ)-1)*h) * g) := by
  refine ⟨coefficient_step x h ha hs hx hp v d k hk c b data.1, ?_⟩
  obtain ⟨⟨translated, high, top, next⟩, second⟩ := data
  -- The first Borcherds summand has coefficient one at index zero.
  -- At this defect it can survive only when the outer mode has k = 2.
  have first : L (-k) (ρ v (d+k-3) x) =
      (if k = 2 then c else 0) • L (-2) x := by
    split_ifs with htwo
    · subst k
      rw [show d+2-3 = d-1 by omega, top, map_smul]
    · rw [high _ (by omega), map_zero, zero_smul]
  rw [iterate_at_or_above_top x h hx hp v d k (d+k-3) (by omega) high,
    first, show d+k-3+1-k = d-2 by omega, show d+k-3-k = d-3 by omega,
    commute_axis_zero v x (d-2) translated, show d-2-1 = d-3 by omega,
    next, second, map_smul, Int.cast_sub, Int.cast_ofNat]
  module

/-- The third coefficient on an actual odd highest-weight vector. -/
theorem nullState_third_mode (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    ρ (nullState D a s) 3 x =
      (3 * (64*h+7)) • L (-1) (L (-1) x) + (24*h*(8*h-17)) • L (-2) x := by
  have step := level_two_step x h ha hs hx hp
  have v0 := vacuum_level_two_data (a := a) (s := s) x
  have v2 : LevelTwoData (F (-2) (fixedVacuum D)) 2 h 1 0 1 := by
    convert step _ 0 2 (by decide) 1 0 0 0 v0 using 1 <;> norm_num [epsilon]
  have v3 : LevelTwoData (F (-3) (fixedVacuum D)) 3 (-2*h) (-1) 0 0 := by
    convert step _ 0 3 (by decide) 1 0 0 0 v0 using 1 <;> norm_num [epsilon]
  have v22 := step _ 2 2 (by decide) h 1 0 1 v2
  have b222 := (step _ 4 2 (by decide) _ _ _ _ v22).2
  have b33 := (step _ 3 3 (by decide) _ _ _ _ v3).2
  have b42 := (step _ 2 4 (by decide) _ _ _ _ v2).2
  have b6 := (step _ 0 6 (by decide) _ _ _ _ v0).2
  norm_num [epsilon] at b222 b33 b42 b6
  simp only [nullState, odd_coefficient, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [odd_coefficient] at b222 b33 b42 b6
  norm_num only [Int.reduceNeg, Int.reduceAdd]
  rw [b222, b33, b42, b6]
  module

theorem highest_weight_null_constraint (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = h • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    (6 * (2*h-1) * (16*h-1)) • L (-1) x = 0 := by
  exact (nullState_fourth_mode x h ha hs hx hp).symm.trans
    (show ρ (nullState D a s) 4 x = 0 from
      LinearMap.congr_fun (odd_vacuum_null D hu a s ha hs 4) x)

/-- A highest-weight vector of weight zero has vanishing first descendant. -/
theorem highest_weight_zero_level_one (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = 0) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    L (-1) x = 0 := by
  have hz := highest_weight_null_constraint x 0 ha hs
    (by simpa only [zero_smul] using hx) hp
  norm_num at hz
  exact hz

/-- At weight one half the second descendant is three quarters of the iterated first. -/
theorem highest_weight_half_level_two (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = (1 / 2 : ℂ) • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    L (-2) x = (3 / 4 : ℂ) • L (-1) (L (-1) x) := by
  have hz := (nullState_third_mode x (1 / 2) ha hs hx hp).symm.trans
    (show ρ (nullState D a s) 3 x = 0 from
      LinearMap.congr_fun (odd_vacuum_null D hu a s ha hs 3) x)
  norm_num at hz
  calc
    L (-2) x = (-1 / 156 : ℂ) • ((117 : ℂ) • L (-1) (L (-1) x) + -((156 : ℂ) • L (-2) x)) +
        (3 / 4 : ℂ) • L (-1) (L (-1) x) := by module
    _ = _ := by rw [hz, smul_zero, zero_add]

/-- At weight one sixteenth the second descendant is four thirds of the iterated first. -/
theorem highest_weight_sixteenth_level_two (ha : bilinear D a a = 4) (hs : s ^ 2 = 1)
    (hx : L 0 x = (1 / 16 : ℂ) • x) (hp : ∀ n : ℤ, 0 < n → L n x = 0) :
    L (-2) x = (4 / 3 : ℂ) • L (-1) (L (-1) x) := by
  have hz := (nullState_third_mode x (1 / 16) ha hs hx hp).symm.trans
    (show ρ (nullState D a s) 3 x = 0 from
      LinearMap.congr_fun (odd_vacuum_null D hu a s ha hs 3) x)
  norm_num at hz
  calc
    L (-2) x = (-4 / 99 : ℂ) • ((33 : ℂ) • L (-1) (L (-1) x) + -((99 / 4 : ℂ) • L (-2) x)) +
        (4 / 3 : ℂ) • L (-1) (L (-1) x) := by module
    _ = _ := by rw [hz, smul_zero, zero_add]


end D5.S3.VertexAlgebra.TwistedGround.Orbifold.FixedSourceIsing
