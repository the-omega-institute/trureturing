/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRecords
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRecords
   mirror-E: none(waiver:open-original-good-record-count)
   anchors: []
   utility: none
   digest: Fixed good records have uniformly subpower many actual physical realizations. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalLattice
import D5.S3.Arith.CharacterSums.PascadiModularZeroPartners
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Actual realizations of a fixed good record

The record consists of the actual anchor and two ordered endpoint pairs in
integer basis coordinates. Its realizations are physical reduced lattice
bases, subject to the original word equations. They are counted by simple
prime-cube roots, actual products of the first basis coordinates, and exact
reconstruction of the complementary basis vector.
-/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def recordReduction (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)

private theorem root_eq_of_nilpotent_sub {A : Type*} [CommRing A]
    (P : A[X]) {x y : A} (hx : P.eval x = 0) (hy : P.eval y = 0)
    (hu : IsUnit (P.derivative.eval x)) (hn : IsNilpotent (y - x)) : x = y := by
  obtain ⟨a, ha⟩ := P.exists_mul_sq_add_linear_part_eq_eval_add x (y - x)
  have hn' : IsNilpotent (a * (y - x)) :=
    (Commute.all a (y - x)).isNilpotent_mul_left hn
  have hunit : IsUnit (P.derivative.eval x + a * (y - x)) :=
    hn'.isUnit_add_left_of_commute hu (Commute.all _ _)
  have hzero : (P.derivative.eval x + a * (y - x)) * (y - x) = 0 := by
    simp only [add_sub_cancel, hx, hy, add_zero] at ha
    linear_combination ha
  have hd : y - x = 0 := hunit.mul_left_cancel (by simpa using hzero)
  exact (sub_eq_zero.mp hd).symm

private theorem isUnit_of_recordReduction_ne_zero {p : ℕ} (hp : p.Prime)
    {a : ZMod (p ^ 3)} (ha : recordReduction p a ≠ 0) : IsUnit a := by
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val a]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr
  intro hd
  apply ha
  have hz : (a.val : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff a.val p).mpr hd
  simpa only [← map_natCast (recordReduction p) a.val, ZMod.natCast_zmod_val] using hz

private theorem nilpotent_of_recordReduction_eq_zero {p : ℕ} (hp : p.Prime)
    {a : ZMod (p ^ 3)} (ha : recordReduction p a = 0) : IsNilpotent a := by
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hz : (a.val : ZMod p) = 0 := by
    simpa only [← map_natCast (recordReduction p) a.val, ZMod.natCast_zmod_val] using ha
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff a.val p).mp hz
  have heq : a = (p : ZMod (p ^ 3)) * k := by
    rw [← ZMod.natCast_zmod_val a, hk, Nat.cast_mul]
  refine ⟨3, ?_⟩
  rw [heq, mul_pow, ← Nat.cast_pow]
  simp

private theorem record_eval_reduction {p : ℕ} (P : ℤ[X]) (β : ZMod (p ^ 3)) :
    recordReduction p (P.eval₂ (Int.castRingHom (ZMod (p ^ 3))) β) =
      P.eval₂ (Int.castRingHom (ZMod p)) (recordReduction p β) := by
  have hcomp : (recordReduction p).comp (Int.castRingHom (ZMod (p ^ 3))) =
      Int.castRingHom (ZMod p) := by ext z; simp
  simpa only [hcomp] using
    Polynomial.hom_eval₂ P (Int.castRingHom (ZMod (p ^ 3))) (recordReduction p) β

private theorem simple_root_reduction_injective {p : ℕ} (hp : p.Prime)
    (P : ℤ[X]) {β γ : ZMod (p ^ 3)}
    (hβ : P.eval₂ (Int.castRingHom (ZMod (p ^ 3))) β = 0)
    (hγ : P.eval₂ (Int.castRingHom (ZMod (p ^ 3))) γ = 0)
    (hder : P.derivative.eval₂ (Int.castRingHom (ZMod p)) (recordReduction p β) ≠ 0)
    (heq : recordReduction p β = recordReduction p γ) : β = γ := by
  apply root_eq_of_nilpotent_sub (P.map (Int.castRingHom (ZMod (p ^ 3))))
  · simpa only [eval_map] using hβ
  · simpa only [eval_map] using hγ
  · apply isUnit_of_recordReduction_ne_zero hp
    simpa only [derivative_map, eval_map, record_eval_reduction] using hder
  · apply nilpotent_of_recordReduction_eq_zero hp
    simp only [map_sub, heq, sub_self]

private def recordSimpleRoots (p : ℕ) (hp : p.Prime) (P : ℤ[X]) :
    Finset (ZMod (p ^ 3)) := by
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact Finset.univ.filter fun β =>
    P.eval₂ (Int.castRingHom (ZMod (p ^ 3))) β = 0 ∧
      P.derivative.eval₂ (Int.castRingHom (ZMod p)) (recordReduction p β) ≠ 0

private theorem mem_recordSimpleRoots {p : ℕ} (hp : p.Prime) (P : ℤ[X])
    (β : ZMod (p ^ 3)) : β ∈ recordSimpleRoots p hp P ↔
      P.eval₂ (Int.castRingHom (ZMod (p ^ 3))) β = 0 ∧
      P.derivative.eval₂ (Int.castRingHom (ZMod p)) (recordReduction p β) ≠ 0 := by
  simp [recordSimpleRoots]

private theorem card_recordSimpleRoots {p : ℕ} (hp : p.Prime)
    (P : ℤ[X]) (hd : P.natDegree ≤ 3) : (recordSimpleRoots p hp P).card ≤ 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f := Int.castRingHom (ZMod p)
  by_cases hP : P.map f = 0
  · have hz : recordSimpleRoots p hp P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro β hβ
      have hder := ((mem_recordSimpleRoots hp P β).mp hβ).2
      have hdz : (P.derivative).map f = 0 := by rw [← derivative_map, hP]; simp
      apply hder
      rw [← eval_map, hdz, eval_zero]
    simp [hz]
  have hmem : ∀ β ∈ recordSimpleRoots p hp P,
      recordReduction p β ∈ (P.map f).roots.toFinset := by
    intro β hβ
    rw [Multiset.mem_toFinset, mem_roots hP]
    have hz := congrArg (recordReduction p) ((mem_recordSimpleRoots hp P β).mp hβ).1
    simpa only [IsRoot, f, map_zero, record_eval_reduction, eval_map] using hz
  have hinj : Set.InjOn (recordReduction p) (recordSimpleRoots p hp P : Set _) := by
    intro β hβ γ hγ heq
    exact simple_root_reduction_injective hp P
      ((mem_recordSimpleRoots hp P β).mp hβ).1
      ((mem_recordSimpleRoots hp P γ).mp hγ).1
      ((mem_recordSimpleRoots hp P β).mp hβ).2 heq
  calc
    _ ≤ (P.map f).roots.toFinset.card := Finset.card_le_card_of_injOn _ hmem hinj
    _ ≤ (P.map f).roots.card := Multiset.toFinset_card_le _
    _ ≤ (P.map f).natDegree := Polynomial.card_roots' _
    _ ≤ P.natDegree := natDegree_map_le
    _ ≤ 3 := hd

/-- The residue ratio of the actual first coordinates of a physical basis. -/
def recordBeta (c : ℕ) (R V : Coordinate) : ZMod c :=
  (V.1 : ZMod c) * (R.1 : ZMod c)⁻¹

/-- The coefficient recovered from the actual base word at a fixed ratio. -/
def recordAlpha (c : ℕ) (q : Coordinate) (base : Endpoint) (β : ZMod c) : ZMod c :=
  -(endpointQ base).eval₂ (Int.castRingHom _) β *
    ((endpointL q base).eval₂ (Int.castRingHom _) β)⁻¹

/-- The physical first-vector product reconstructed from the fixed record. -/
def recordProduct (c : ℕ) (g : ZMod c) (q : Coordinate) (base : Endpoint)
    (β : ZMod c) : ZMod c :=
  (g * recordAlpha c q base β * ((q.1 : ZMod c) + β * q.2))⁻¹

/-- Actual reduced physical bases realizing one fixed good record. The middle
letters are the literal negative anchor coordinates; no independent lifts or
quotient keys enter this set. -/
structure GoodRecordRealization (p : ℕ) (X Y : ℝ) (a₁ a₂ : ZMod (p^3))
    (q : Coordinate) (base e : Endpoint) (RV : Coordinate × Coordinate) : Prop where
  reduced : ∃ B : ReducedMiddleBasis (p^3)
    (-(physical RV.1 RV.2 q).2) (-(physical RV.1 RV.2 q).1) X Y,
    B.R = RV.1 ∧ B.V = RV.2
  long : (p^3 : ℝ)^2 < (X * Y) * weightedSq X Y RV.1
  unitR : IsUnit (RV.1.1 : ZMod (p^3))
  unitT : IsUnit (-(physical RV.1 RV.2 q).2 : ZMod (p^3))
  wordBase : WordSolution (p^3) a₁ a₂ RV.1 RV.2 q base
  wordEnd : WordSolution (p^3) a₁ a₂ RV.1 RV.2 q e
  baseFirstUnit : IsUnit ((physical RV.1 RV.2 base.1).1 : ZMod (p^3))
  baseSecondUnit : IsUnit ((physical RV.1 RV.2 base.2).1 : ZMod (p^3))
  regular : (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
    (recordReduction p (recordBeta (p^3) RV.1 RV.2)) ≠ 0

private theorem record_physical_eval {c : ℕ} (R V z : Coordinate)
    (hr : IsUnit (R.1 : ZMod c)) :
    ((physical R V z).1 : ZMod c) =
      (R.1 : ZMod c) * ((z.1 : ZMod c) + recordBeta c R V * z.2) := by
  have hinv := ZMod.mul_inv_of_unit (R.1 : ZMod c) hr
  dsimp [physical, recordBeta]
  push_cast
  linear_combination -(V.1 : ZMod c) * (z.2 : ZMod c) * hinv

private theorem recordAlpha_eq_original {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (hw : WordSolution c a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod c))
    (hy : IsUnit ((physical R V base.2).1 : ZMod c)) :
    recordAlpha c q base (recordBeta c R V) =
      -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c) := by
  let β := recordBeta c R V
  let α : ZMod c := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
  have hβ : (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c) = β := by
    simp [β, recordBeta, ← ZMod.inv_coe_unit, hr.unit_spec]
  have hid : α * (endpointL q base).eval₂ (Int.castRingHom _) β +
      (endpointQ base).eval₂ (Int.castRingHom _) β = 0 := by
    simpa only [hβ] using original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q base hr ht hw
  rw [record_physical_eval R V base.1 hr] at hx
  rw [record_physical_eval R V base.2 hr] at hy
  have hx' := (IsUnit.mul_iff.mp hx).2
  have hy' := (IsUnit.mul_iff.mp hy).2
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod c)) β =
      (n : ZMod c) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod c)) β) n
  have hQ : (endpointQ base).eval₂ (Int.castRingHom (ZMod c)) β =
      ((base.1.1 : ZMod c) + β * base.1.2) *
        ((base.2.1 : ZMod c) + β * base.2.2) := by
    simp [endpointQ, PrimeCube.quadratic, coeffQ, coeffR, coeffS, heval]
    ring
  have hαL : α * (endpointL q base).eval₂ (Int.castRingHom _) β =
      -(endpointQ base).eval₂ (Int.castRingHom _) β := by linear_combination hid
  have hL : IsUnit ((endpointL q base).eval₂ (Int.castRingHom _) β) := by
    have hu : IsUnit (α * (endpointL q base).eval₂ (Int.castRingHom _) β) := by
      rw [hαL, hQ]
      exact (hx'.mul hy').neg
    exact (IsUnit.mul_iff.mp hu).2
  change -(endpointQ base).eval₂ (Int.castRingHom _) β *
    ((endpointL q base).eval₂ (Int.castRingHom _) β)⁻¹ = α
  rw [← hαL, mul_assoc, ZMod.mul_inv_of_unit _ hL, mul_one]

private theorem actual_record_product {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (hw : WordSolution c a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod c))
    (hy : IsUnit ((physical R V base.2).1 : ZMod c))
    (hR : R ∈ middleLattice c (-(physical R V q).2) (-(physical R V q).1)) :
    recordProduct c (a₁*a₂) q base (recordBeta c R V) = (R.1 * R.2 : ℤ) := by
  let β := recordBeta c R V
  let Z : ZMod c := (q.1 : ZMod c) + β * q.2
  let α : ZMod c := -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c)
  have hα : recordAlpha c q base β = α :=
    recordAlpha_eq_original a₁ a₂ ha₁ ha₂ R V q base hr ht hw hx hy
  have htR : IsUnit ((-(physical R V q).2 : ZMod c) * (R.1 : ZMod c)) := ht.mul hr
  have hαgtr : α * ((a₁*a₂) * (-(physical R V q).2 : ZMod c) * R.1) = -1 := by
    change -(↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod c) *
      ((a₁*a₂) * (-(physical R V q).2 : ZMod c) * R.1) = -1
    have hh : ((a₁*a₂) * (-(physical R V q).2 : ZMod c) * R.1) =
        (↑(ha₁.unit * ha₂.unit * ht.unit * hr.unit) : ZMod c) := by
      simp only [Units.val_mul, ha₁.unit_spec, ha₂.unit_spec, ht.unit_spec, hr.unit_spec]
    rw [hh, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRq : (R.1 : ZMod c) * Z = ((physical R V q).1 : ZMod c) :=
    (record_physical_eval R V q hr).symm
  have hRS : (-(physical R V q).1 : ZMod c) * (R.2 : ZMod c) =
      (-(physical R V q).2 : ZMod c) * (R.1 : ZMod c) := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (-(physical R V q).1 * R.2 - -(physical R V q).2 * R.1) c).mpr hR
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hinv : (a₁*a₂) * α * Z * ((R.1 : ZMod c) * R.2) = 1 := by
    apply htR.mul_right_cancel
    linear_combination
      (Z * (R.1 : ZMod c) * R.2) * hαgtr -
      (R.2 : ZMod c) * hRq + hRS
  unfold recordProduct
  rw [hα]
  simpa only [Int.cast_mul] using ZMod.inv_eq_of_mul_eq_one c _ _ hinv

private theorem weighted_product_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (R : Coordinate) : 2 * |((R.1 * R.2 : ℤ) : ℝ)| ≤ weightedSq X Y R := by
  have hid := weighted_det_identity hX hY R (R.1, -R.2)
  have hnorm : weightedSq X Y (R.1, -R.2) = weightedSq X Y R := by
    simp [weightedSq]
  rw [hnorm] at hid
  have hdet : (((R.1 * (R.1, -R.2).2 - (R.1, -R.2).1 * R.2 : ℤ) : ℝ)) ^ 2 =
      4 * (((R.1 * R.2 : ℤ) : ℝ))^2 := by
    push_cast
    ring
  rw [hdet] at hid
  have hA := weightedSq_nonneg hX hY R
  have habs := abs_nonneg (((R.1 * R.2 : ℤ) : ℝ))
  nlinarith [sq_nonneg (weightedDot X Y R (R.1, -R.2)),
    sq_abs (((R.1 * R.2 : ℤ) : ℝ))]

private theorem actual_record_second_unit {c : ℕ} (R V q : Coordinate)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (hR : R ∈ middleLattice c (-(physical R V q).2) (-(physical R V q).1)) :
    IsUnit (R.2 : ZMod c) := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (-(physical R V q).1 * R.2 - -(physical R V q).2 * R.1) c).mpr hR
  push_cast at hz
  have heq := sub_eq_zero.mp hz
  have hu := ht.mul hr
  rw [← heq] at hu
  exact (IsUnit.mul_iff.mp hu).2

private theorem actual_record_product_bounds {p : ℕ} (hp : p.Prime)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {a₁ a₂ : ZMod (p^3)} {q : Coordinate} {base e : Endpoint}
    {RV : Coordinate × Coordinate}
    (h : GoodRecordRealization p X Y a₁ a₂ q base e RV) :
    0 < |((RV.1.1 * RV.1.2 : ℤ) : ℝ)| ∧
      |((RV.1.1 * RV.1.2 : ℤ) : ℝ)| < (p^3 : ℝ) := by
  letI : Fact (1 < p^3) := ⟨one_lt_pow' hp.one_lt (by decide)⟩
  obtain ⟨B, hBR, hBV⟩ := h.reduced
  have hR : RV.1 ∈ middleLattice (p^3)
      (-(physical RV.1 RV.2 q).2) (-(physical RV.1 RV.2 q).1) := by
    simpa only [hBR] using B.memR
  have hs := actual_record_second_unit RV.1 RV.2 q h.unitR h.unitT hR
  have hr0 : RV.1.1 ≠ 0 := by
    intro hz
    exact h.unitR.ne_zero (by simp [hz])
  have hs0 : RV.1.2 ≠ 0 := by
    intro hz
    exact hs.ne_zero (by simp [hz])
  have hmul0 : ((RV.1.1 * RV.1.2 : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast mul_ne_zero hr0 hs0
  refine ⟨abs_pos.mpr hmul0, ?_⟩
  have hb := (B.reduction_bounds (pow_pos hp.pos _) hX hY).2.1
  rw [hBR] at hb
  have hw := weighted_product_le hX hY RV.1
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hb
  linarith

private theorem actual_record_V_bound {p : ℕ} (hp : p.Prime)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {a₁ a₂ : ZMod (p^3)} {q : Coordinate} {base e : Endpoint}
    {RV : Coordinate × Coordinate}
    (h : GoodRecordRealization p X Y a₁ a₂ q base e RV) :
    |(RV.2.1 : ℝ)| < 3 * X / 2 := by
  obtain ⟨B, hBR, hBV⟩ := h.reduced
  have hA : 0 < weightedSq X Y RV.1 := by
    rw [← hBR]
    exact weightedSq_pos hX hY (B.first_ne_zero (pow_pos hp.pos _))
  have hb := (B.reduction_bounds (pow_pos hp.pos _) hX hY).2.2
  rw [hBR, hBV] at hb
  have hlong : ((p^3 : ℕ) : ℝ)^2 < (X * Y) * weightedSq X Y RV.1 := by
    simpa only [Nat.cast_pow] using h.long
  have hVsmall : weightedSq X Y RV.2 < 2 * (X * Y) := by
    nlinarith
  have hn : 0 ≤ X / Y * (RV.2.2 : ℝ)^2 := by positivity
  have h₁ : Y / X * (RV.2.1 : ℝ)^2 < 2 * (X * Y) := by
    unfold weightedSq at hVsmall
    linarith
  have hmul := mul_lt_mul_of_pos_right h₁ hX
  have heq : Y / X * (RV.2.1 : ℝ)^2 * X = Y * (RV.2.1 : ℝ)^2 := by
    field_simp [ne_of_gt hX]
  rw [heq] at hmul
  have hs : (RV.2.1 : ℝ)^2 < 2 * X^2 := by
    nlinarith
  have ha := abs_nonneg (RV.2.1 : ℝ)
  nlinarith [sq_abs (RV.2.1 : ℝ)]

private theorem actual_record_reconstruction {p : ℕ} (hp : p.Prime)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hsmall : 3 * Y < (p : ℝ)^2)
    {a₁ a₂ : ZMod (p^3)} {q : Coordinate} {base e : Endpoint}
    {RV RV' : Coordinate × Coordinate}
    (h : GoodRecordRealization p X Y a₁ a₂ q base e RV)
    (h' : GoodRecordRealization p X Y a₁ a₂ q base e RV')
    (hβ : recordBeta (p^3) RV.1 RV.2 = recordBeta (p^3) RV'.1 RV'.2)
    (hR : RV.1 = RV'.1) : RV = RV' := by
  have hVmod : (RV.2.1 : ZMod (p^3)) = (RV'.2.1 : ZMod (p^3)) := by
    have hh := congrArg (fun z : ZMod (p^3) => z * (RV.1.1 : ZMod (p^3))) hβ
    simp only [recordBeta, ← hR, mul_assoc,
      ZMod.inv_mul_of_unit _ h.unitR, mul_one] at hh
    exact hh
  have hdvd : ((p^3 : ℕ) : ℤ) ∣ RV'.2.1 - RV.2.1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hVmod
  have hV := actual_record_V_bound hp hX hY h
  have hV' := actual_record_V_bound hp hX hY h'
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hdiff : |((RV'.2.1 - RV.2.1 : ℤ) : ℝ)| < ((p^3 : ℕ) : ℝ) := by
    have ha := abs_sub (RV'.2.1 : ℝ) (RV.2.1 : ℝ)
    have hpow : (p : ℝ)^2 ≤ (p : ℝ)^3 := by nlinarith [sq_nonneg (p : ℝ)]
    push_cast
    nlinarith
  have hfirst : RV.2.1 = RV'.2.1 := by
    have hi : |RV'.2.1 - RV.2.1| < ((p^3 : ℕ) : ℤ) := by exact_mod_cast hdiff
    exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hi)).symm
  obtain ⟨B, hBR, hBV⟩ := h.reduced
  obtain ⟨B', hBR', hBV'⟩ := h'.reduced
  have hd := B.det
  have hd' := B'.det
  rw [hBR, hBV] at hd
  rw [hBR', hBV', ← hR, ← hfirst] at hd'
  have hr0 : RV.1.1 ≠ 0 := by
    intro hz
    have hh := (actual_record_product_bounds hp hX hY h).1
    simp [hz] at hh
  have hsecond : RV.2.2 = RV'.2.2 := by
    apply mul_left_cancel₀ hr0
    linarith
  exact Prod.ext hR (Prod.ext hfirst hsecond)

private def recordFactors (c : ℕ) (z : ZMod c) : Finset Coordinate :=
  Int.divisorsAntidiag (z.val : ℤ) ∪ Int.divisorsAntidiag ((z.val : ℤ) - c)

private theorem mem_recordFactors {c : ℕ} (hc : 0 < c) (z : ZMod c)
    (R : Coordinate) (hprod : (R.1 * R.2 : ℤ) ≠ 0)
    (hsmall : |R.1 * R.2| < (c : ℤ))
    (hres : ((R.1 * R.2 : ℤ) : ZMod c) = z) : R ∈ recordFactors c z := by
  letI : NeZero c := ⟨ne_of_gt hc⟩
  have hres' : ((R.1 * R.2 : ℤ) : ZMod c) = ((z.val : ℤ) : ZMod c) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hres
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hres'
  have hn0 : (0 : ℤ) ≤ z.val := Int.natCast_nonneg _
  have hn : (z.val : ℤ) < c := by exact_mod_cast ZMod.val_lt z
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  obtain ⟨hklo, hkhi⟩ := abs_lt.mp hsmall
  have hmlo : 0 ≤ m := by
    by_contra! h
    have hh : m ≤ -1 := by omega
    nlinarith
  have hmhi : m ≤ 1 := by
    by_contra! h
    have hh : 2 ≤ m := by omega
    nlinarith
  have hcases : m = 0 ∨ m = 1 := by omega
  rw [recordFactors, Finset.mem_union, Int.mem_divisorsAntidiag,
    Int.mem_divisorsAntidiag]
  rcases hcases with rfl | rfl
  · left
    have heq : R.1 * R.2 = (z.val : ℤ) := by nlinarith [hm]
    exact ⟨heq, heq ▸ hprod⟩
  · right
    have heq : R.1 * R.2 = (z.val : ℤ) - c := by nlinarith [hm]
    exact ⟨heq, heq ▸ hprod⟩

private def recordCandidates (p : ℕ) (hp : p.Prime) (g : ZMod (p^3))
    (q : Coordinate) (base e : Endpoint) : Finset (ZMod (p^3) × Coordinate) := by
  classical
  exact (recordSimpleRoots p hp (pencil q base e)).biUnion fun β =>
    (recordFactors (p^3) (recordProduct (p^3) g q base β)).image fun R => (β, R)

private theorem actual_record_mem_candidates {p : ℕ} (hp : p.Prime)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {a₁ a₂ : ZMod (p^3)} (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    {q : Coordinate} {base e : Endpoint} {RV : Coordinate × Coordinate}
    (h : GoodRecordRealization p X Y a₁ a₂ q base e RV) :
    (recordBeta (p^3) RV.1 RV.2, RV.1) ∈
      recordCandidates p hp (a₁*a₂) q base e := by
  classical
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hβ : (RV.2.1 : ZMod (p^3)) * (↑h.unitR.unit⁻¹ : ZMod (p^3)) =
      recordBeta (p^3) RV.1 RV.2 := by
    simp only [recordBeta, ← ZMod.inv_coe_unit, h.unitR.unit_spec]
  have hroot := original_pencil_root a₁ a₂ ha₁ ha₂ RV.1 RV.2 q base e
    h.unitR h.unitT h.wordBase h.wordEnd
  rw [hβ] at hroot
  have hrootmem := (mem_recordSimpleRoots hp (pencil q base e) _).mpr ⟨hroot, h.regular⟩
  obtain ⟨B, hBR, hBV⟩ := h.reduced
  have hR : RV.1 ∈ middleLattice (p^3)
      (-(physical RV.1 RV.2 q).2) (-(physical RV.1 RV.2 q).1) := by
    simpa only [hBR] using B.memR
  have hprod := actual_record_product a₁ a₂ ha₁ ha₂ RV.1 RV.2 q base
    h.unitR h.unitT h.wordBase h.baseFirstUnit h.baseSecondUnit hR
  have hb := actual_record_product_bounds hp hX hY h
  have hsmall : |RV.1.1 * RV.1.2| < ((p^3 : ℕ) : ℤ) := by
    exact_mod_cast hb.2
  have hnonzero : RV.1.1 * RV.1.2 ≠ 0 := by
    intro hz
    simp [hz] at hb
  have hfac := mem_recordFactors (pow_pos hp.pos _) _ RV.1 hnonzero hsmall hprod.symm
  exact Finset.mem_biUnion.mpr ⟨_, hrootmem, Finset.mem_image.mpr ⟨RV.1, hfac, rfl⟩⟩

private theorem actual_record_finite_count {p : ℕ} (hp : p.Prime)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hsmall : 3 * Y < (p : ℝ)^2)
    {a₁ a₂ : ZMod (p^3)} (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (q : Coordinate) (base e : Endpoint) :
    Set.Finite {RV | GoodRecordRealization p X Y a₁ a₂ q base e RV} ∧
      {RV | GoodRecordRealization p X Y a₁ a₂ q base e RV}.ncard ≤
        (recordCandidates p hp (a₁*a₂) q base e).card := by
  let f : Coordinate × Coordinate → ZMod (p^3) × Coordinate :=
    fun RV => (recordBeta (p^3) RV.1 RV.2, RV.1)
  have hm : Set.MapsTo f {RV | GoodRecordRealization p X Y a₁ a₂ q base e RV}
      (recordCandidates p hp (a₁*a₂) q base e : Set _) := by
    intro RV hRV
    exact actual_record_mem_candidates hp hX hY ha₁ ha₂ hRV
  have hi : Set.InjOn f {RV | GoodRecordRealization p X Y a₁ a₂ q base e RV} := by
    intro RV h RV' h' heq
    exact actual_record_reconstruction hp hX hY hXY hsmall h h'
      (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  refine ⟨Set.Finite.of_injOn hm hi (Finset.finite_toSet _), ?_⟩
  have hh := Set.ncard_le_ncard_of_injOn f hm hi (Finset.finite_toSet _)
  simpa only [Set.ncard_coe_finset] using hh

private theorem card_recordFactors_bound (ε : ℝ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hdiv : ∀ k : ℤ, k ≠ 0 →
      ((Int.divisorsAntidiag k).card : ℝ) ≤ C * (k.natAbs : ℝ)^(ε / 3))
    (p : ℕ) (hp : p.Prime) (z : ZMod (p^3)) :
    ((recordFactors (p^3) z).card : ℝ) ≤ 2 * C * (p : ℝ)^ε := by
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hsingle (k : ℤ) (hk : (k.natAbs : ℝ) ≤ (p : ℝ)^3) :
      ((Int.divisorsAntidiag k).card : ℝ) ≤ C * (p : ℝ)^ε := by
    by_cases hz : k = 0
    · subst k
      simp only [Int.divisorsAntidiag_zero, Finset.card_empty, Nat.cast_zero]
      positivity
    have hpow : (k.natAbs : ℝ)^(ε / 3) ≤ (p : ℝ)^ε := by
      have hh := Real.rpow_le_rpow (Nat.cast_nonneg k.natAbs) hk
        (by positivity : (0 : ℝ) ≤ ε / 3)
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p) 3 (ε / 3)] at hh
      simpa only [Nat.cast_ofNat, show (3 : ℝ) * (ε / 3) = ε by ring] using hh
    exact (hdiv k hz).trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hn : (z.val : ℝ) < (p : ℝ)^3 := by
    exact_mod_cast ZMod.val_lt z
  have hn0 : (0 : ℝ) ≤ z.val := Nat.cast_nonneg _
  have hfirst : (((z.val : ℤ)).natAbs : ℝ) ≤ (p : ℝ)^3 := by
    simpa only [Int.natAbs_natCast] using hn.le
  have hsecond : ((((z.val : ℤ) - (p^3 : ℕ))).natAbs : ℝ) ≤ (p : ℝ)^3 := by
    rw [Nat.cast_natAbs]
    push_cast
    rw [abs_of_neg (by linarith : (z.val : ℝ) - (p : ℝ)^3 < 0)]
    linarith
  have hu := Finset.card_union_le (Int.divisorsAntidiag (z.val : ℤ))
    (Int.divisorsAntidiag ((z.val : ℤ) - (p^3 : ℕ)))
  have huR : ((recordFactors (p^3) z).card : ℝ) ≤
      ((Int.divisorsAntidiag (z.val : ℤ)).card : ℝ) +
        ((Int.divisorsAntidiag ((z.val : ℤ) - (p^3 : ℕ))).card : ℝ) := by
    unfold recordFactors
    exact_mod_cast hu
  have hu0 := hsingle (z.val : ℤ) hfirst
  have hu1 := hsingle ((z.val : ℤ) - (p^3 : ℕ)) hsecond
  exact huR.trans (by linarith)

/-- Uniform subpower multiplicity of a fixed good record in the actual physical
prime-cube problem. The set contains all reduced oriented physical bases
satisfying the original word equations and the simple-root chart conditions;
no canonical-basis uniqueness or abstract realization key is assumed. -/
theorem actual_good_record_realizations_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate) (base e : Endpoint),
      0 < X → X ≤ Y → 3 * Y < (p : ℝ)^2 → IsUnit a₁ → IsUnit a₂ →
      Set.Finite {RV | GoodRecordRealization p X Y a₁ a₂ q base e RV} ∧
        ({RV | GoodRecordRealization p X Y a₁ a₂ q base e RV}.ncard : ℝ) ≤
          C * (p : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hdiv⟩ := signed_divisors_antidiag_subpower (ε / 3) (by positivity)
  refine ⟨6 * C, mul_pos (by norm_num) hC, ?_⟩
  intro p hp X Y a₁ a₂ q base e hX hXY hsmall ha₁ ha₂
  have hY : 0 < Y := lt_of_lt_of_le hX hXY
  obtain ⟨hfinite, hcard⟩ := actual_record_finite_count hp hX hY hXY hsmall ha₁ ha₂ q base e
  refine ⟨hfinite, ?_⟩
  let roots := recordSimpleRoots p hp (pencil q base e)
  let factors : ZMod (p^3) → Finset Coordinate :=
    fun β => recordFactors (p^3) (recordProduct (p^3) (a₁*a₂) q base β)
  have hcandidates : (recordCandidates p hp (a₁*a₂) q base e).card ≤
      ∑ β ∈ roots, (factors β).card := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun β _ => Finset.card_image_le
  have hcandidatesR : ((recordCandidates p hp (a₁*a₂) q base e).card : ℝ) ≤
      ∑ β ∈ roots, ((factors β).card : ℝ) := by exact_mod_cast hcandidates
  have hrootcard : (roots.card : ℝ) ≤ 3 := by
    exact_mod_cast card_recordSimpleRoots hp (pencil q base e) (pencil_natDegree q base e)
  have hsum : (∑ β ∈ roots, ((factors β).card : ℝ)) ≤
      ∑ _β ∈ roots, 2 * C * (p : ℝ)^ε := by
    apply Finset.sum_le_sum
    intro β _
    exact card_recordFactors_bound ε hε C hC hdiv p hp _
  calc
    _ ≤ ((recordCandidates p hp (a₁*a₂) q base e).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ β ∈ roots, ((factors β).card : ℝ) := hcandidatesR
    _ ≤ ∑ _β ∈ roots, 2 * C * (p : ℝ)^ε := hsum
    _ = (roots.card : ℝ) * (2 * C * (p : ℝ)^ε) := by simp
    _ ≤ 3 * (2 * C * (p : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hrootcard (by positivity)
    _ = (6 * C) * (p : ℝ)^ε := by ring

end
end D5.S3.Arith.CharacterSums.Original
