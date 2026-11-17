/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalLattice
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalLattice
   mirror-E: none(waiver:open-original-lattice-reduction)
   anchors: []
   utility: none
   digest: Reduced basis and literal coordinate bounds for the original prime-cube lattice. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The original physical lattice

The congruence lattice is defined using the literal middle letters. The basis
and coordinate bounds below do not rescale those letters by the fixed units. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

/-- The lattice of physical endpoint vectors for the fixed middle letters. -/
def middleLattice (c : ℕ) (t w : ℤ) : Set Coordinate :=
  {z | (c : ℤ) ∣ w * z.2 - t * z.1}

/-- The literal endpoint rectangle. -/
def literalBox (X Y : ℝ) : Set Coordinate :=
  {z | |(z.1 : ℝ)| ≤ X ∧ |(z.2 : ℝ)| ≤ Y}

private theorem middleLattice_add {c : ℕ} {t w : ℤ} {z z' : Coordinate}
    (hz : z ∈ middleLattice c t w) (hz' : z' ∈ middleLattice c t w) :
    z + z' ∈ middleLattice c t w := by
  change (c : ℤ) ∣ w * (z.2 + z'.2) - t * (z.1 + z'.1)
  convert dvd_add hz hz' using 1 <;> ring

private theorem middleLattice_smul {c : ℕ} {t w n : ℤ} {z : Coordinate}
    (hz : z ∈ middleLattice c t w) : n • z ∈ middleLattice c t w := by
  change (c : ℤ) ∣ w * (n * z.2) - t * (n * z.1)
  convert dvd_mul_of_dvd_right hz n using 1 <;> ring

/-- The anchor always belongs to the same literal box section as the endpoints. -/
theorem anchor_mem_middleLattice (c : ℕ) (t w : ℤ) :
    (-w, -t) ∈ middleLattice c t w := by
  change (c : ℤ) ∣ w * (-t) - t * (-w)
  simp [mul_comm]

theorem anchor_mem_literalBox {X Y : ℝ} {t w : ℤ}
    (hw : |(w : ℝ)| ≤ X) (ht : |(t : ℝ)| ≤ Y) :
    (-w, -t) ∈ literalBox X Y := by
  simpa [literalBox] using And.intro hw ht

/-- An oriented integer basis of the physical congruence lattice. -/
structure MiddleBasis (c : ℕ) (t w : ℤ) where
  R : Coordinate
  V : Coordinate
  det : R.1 * V.2 - V.1 * R.2 = c
  memR : R ∈ middleLattice c t w
  memV : V ∈ middleLattice c t w
  decompose : ∀ z ∈ middleLattice c t w, ∃ i j : ℤ, physical R V (i, j) = z

/-- The explicit kernel basis; later reduction changes this basis inside the same lattice. -/
noncomputable def middleBasis_of_slope (c : ℕ) (t w k : ℤ)
    (hk : (c : ℤ) ∣ w * k - t)
    (hcancel : ∀ m : ℤ, (c : ℤ) ∣ w * m → (c : ℤ) ∣ m) :
    MiddleBasis c t w := by
  refine ⟨(1, k), (0, c), ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [middleLattice] using hk
  · change (c : ℤ) ∣ w * (c : ℤ) - t * 0
    simp
  · intro z hz
    have hdiff : (c : ℤ) ∣ w * (z.2 - k * z.1) := by
      have h := dvd_sub hz (dvd_mul_of_dvd_right hk z.1)
      convert h using 1 <;> ring
    obtain ⟨j, hj⟩ := hcancel _ hdiff
    refine ⟨z.1, j, ?_⟩
    apply Prod.ext
    · simp [physical]
    · dsimp [physical]
      linear_combination -hj

noncomputable def middleBasis_of_unit (c : ℕ) [NeZero c] (t w : ℤ)
    (hw : IsUnit (w : ZMod c)) : MiddleBasis c t w := by
  let k : ℤ := (((t : ZMod c) * (↑hw.unit⁻¹ : ZMod c)).val : ℤ)
  have hwu : (w : ZMod c) * (↑hw.unit⁻¹ : ZMod c) = 1 := by
    simpa only [hw.unit_spec] using
      (show (↑hw.unit : ZMod c) * (↑hw.unit⁻¹ : ZMod c) = 1 by simp)
  have hkmod : ((w * k - t : ℤ) : ZMod c) = 0 := by
    have hku : (k : ZMod c) = (t : ZMod c) * (↑hw.unit⁻¹ : ZMod c) := by
      simp [k]
    push_cast
    rw [hku]
    calc
      (w : ZMod c) * ((t : ZMod c) * (↑hw.unit⁻¹ : ZMod c)) - t =
          (t : ZMod c) * ((w : ZMod c) * (↑hw.unit⁻¹ : ZMod c)) - t := by ring
      _ = 0 := by rw [hwu]; ring
  have hk : (c : ℤ) ∣ w * k - t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hkmod
  apply middleBasis_of_slope c t w k hk
  intro m hm
  have hmod : ((w * m : ℤ) : ZMod c) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hm
  have hmzero : (m : ZMod c) = 0 := by
    have hwu' : (↑hw.unit⁻¹ : ZMod c) * (w : ZMod c) = 1 := by
      simpa only [mul_comm] using hwu
    calc
      (m : ZMod c) = ((↑hw.unit⁻¹ : ZMod c) * (w : ZMod c)) * m := by rw [hwu']; ring
      _ = (↑hw.unit⁻¹ : ZMod c) * ((w : ZMod c) * m) := by ring
      _ = 0 := by simpa only [← Int.cast_mul, hmod, mul_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmzero

theorem MiddleBasis.coordinates_unique {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) (hc : 0 < c) {z z' : Coordinate}
    (h : physical B.R B.V z = physical B.R B.V z') : z = z' := by
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hx : (c : ℤ) * (z.1 - z'.1) = 0 := by
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp [physical] at h₁ h₂
    linear_combination B.V.2 * h₁ - B.V.1 * h₂ -
      (z.1 - z'.1) * B.det
  have hy : (c : ℤ) * (z.2 - z'.2) = 0 := by
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp [physical] at h₁ h₂
    linear_combination -B.R.2 * h₁ + B.R.1 * h₂ -
      (z.2 - z'.2) * B.det
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hc'))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hc'))

theorem MiddleBasis.physical_mem {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) (z : Coordinate) :
    physical B.R B.V z ∈ middleLattice c t w := by
  change (c : ℤ) ∣ w * (z.1 * B.R.2 + z.2 * B.V.2) -
    t * (z.1 * B.R.1 + z.2 * B.V.1)
  have hR := B.memR
  have hV := B.memV
  change (c : ℤ) ∣ w * B.R.2 - t * B.R.1 at hR
  change (c : ℤ) ∣ w * B.V.2 - t * B.V.1 at hV
  convert dvd_add (dvd_mul_of_dvd_right hR z.1)
    (dvd_mul_of_dvd_right hV z.2) using 1 <;> ring

theorem MiddleBasis.anchor_coordinates {c : ℕ} {t w : ℤ}
    (B : MiddleBasis c t w) :
    ∃ q : Coordinate, physical B.R B.V q = (-w, -t) := by
  obtain ⟨i, j, hij⟩ := B.decompose _ (anchor_mem_middleLattice c t w)
  exact ⟨(i, j), hij⟩

/-- Weighted squared norm, with area-preserving anisotropic metric. -/
def weightedSq (X Y : ℝ) (z : Coordinate) : ℝ :=
  Y / X * (z.1 : ℝ)^2 + X / Y * (z.2 : ℝ)^2

/-- The weighted bilinear pairing behind `weightedSq`. -/
def weightedDot (X Y : ℝ) (z z' : Coordinate) : ℝ :=
  Y / X * (z.1 : ℝ) * z'.1 + X / Y * (z.2 : ℝ) * z'.2

theorem weightedSq_nonneg {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (z : Coordinate) : 0 ≤ weightedSq X Y z := by
  unfold weightedSq
  positivity

theorem weightedSq_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {z : Coordinate} (hz : z ≠ 0) : 0 < weightedSq X Y z := by
  have hx : (z.1 : ℝ) ≠ 0 ∨ (z.2 : ℝ) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz
    exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)
  unfold weightedSq
  rcases hx with hx | hy
  · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hY hX) (sq_pos_of_ne_zero hx))
      (mul_nonneg (le_of_lt (div_pos hX hY)) (sq_nonneg _))
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt (div_pos hY hX)) (sq_nonneg _))
      (mul_pos (div_pos hX hY) (sq_pos_of_ne_zero hy))

/-- The anisotropic metric has determinant one. -/
theorem weighted_det_identity {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (z z' : Coordinate) :
    weightedSq X Y z * weightedSq X Y z' - weightedDot X Y z z' ^ 2 =
      ((z.1 * z'.2 - z'.1 * z.2 : ℤ) : ℝ) ^ 2 := by
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hY0 : Y ≠ 0 := ne_of_gt hY
  unfold weightedSq weightedDot
  push_cast
  field_simp [hX0, hY0]
  ring

private theorem weighted_det_sq_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (z z' : Coordinate) :
    (((z.1 * z'.2 - z'.1 * z.2 : ℤ) : ℝ)) ^ 2 ≤
      weightedSq X Y z * weightedSq X Y z' := by
  nlinarith [weighted_det_identity hX hY z z',
    sq_nonneg (weightedDot X Y z z')]

private theorem exists_centering_shift (A D : ℝ) (hA : 0 < A) :
    ∃ m : ℤ, (2 * (D - (m : ℝ) * A)) ^ 2 ≤ A ^ 2 := by
  let m : ℤ := ⌊D / A + 1 / 2⌋
  have hlo : (m : ℝ) ≤ D / A + 1 / 2 := Int.floor_le _
  have hhi : D / A + 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hmul₁ := mul_le_mul_of_nonneg_right hlo hA.le
  have hmul₂ := mul_lt_mul_of_pos_right hhi hA
  have hAd : A ≠ 0 := ne_of_gt hA
  have hcancel : D / A * A = D := div_mul_cancel₀ D hAd
  have hlow : -(A / 2) ≤ D - (m : ℝ) * A := by
    nlinarith [hcancel]
  have hupp : D - (m : ℝ) * A < A / 2 := by
    nlinarith [hcancel]
  refine ⟨m, ?_⟩
  have hp := mul_nonneg (sub_nonneg.mpr hupp.le)
    (by linarith : 0 ≤ A / 2 + (D - (m : ℝ) * A))
  nlinarith

/-- Shortest first vector and centered second vector in the actual lattice. -/
structure ReducedMiddleBasis (c : ℕ) (t w : ℤ) (X Y : ℝ)
    extends MiddleBasis c t w where
  shortest : ∀ z ∈ middleLattice c t w, z ≠ 0 →
    weightedSq X Y R ≤ weightedSq X Y z
  centered : (2 * weightedDot X Y R V) ^ 2 ≤ (weightedSq X Y R) ^ 2

theorem ReducedMiddleBasis.first_ne_zero {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (hc : 0 < c) : B.R ≠ 0 := by
  intro h
  have hd := B.det
  simp [h] at hd
  omega

theorem ReducedMiddleBasis.second_ne_zero {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (hc : 0 < c) : B.V ≠ 0 := by
  intro h
  have hd := B.det
  simp [h] at hd
  omega

/-- Rational versions of the reduction constants suffice for every endpoint scale. -/
theorem ReducedMiddleBasis.reduction_bounds {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) :
    3 * (weightedSq X Y B.R)^2 ≤ 4 * (c : ℝ)^2 ∧
    weightedSq X Y B.R < 2 * c ∧
    weightedSq X Y B.V * weightedSq X Y B.R ≤ 2 * (c : ℝ)^2 := by
  let A := weightedSq X Y B.R
  let D := weightedDot X Y B.R B.V
  let Vq := weightedSq X Y B.V
  have hA : 0 < A := weightedSq_pos hX hY (B.first_ne_zero hc)
  have hV : A ≤ Vq := B.shortest B.V B.memV (B.second_ne_zero hc)
  have hdet := weighted_det_identity hX hY B.R B.V
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have heq : A * Vq - D^2 = (c : ℝ)^2 := by
    have hdetcast : (((B.R.1 * B.V.2 - B.V.1 * B.R.2 : ℤ) : ℝ)) = c := by
      exact_mod_cast B.det
    rw [hdetcast] at hdet
    exact hdet
  have hcenter : 4 * D^2 ≤ A^2 := by
    nlinarith [B.centered]
  have hAV : A^2 ≤ A * Vq := by nlinarith [mul_nonneg (le_of_lt hA) (sub_nonneg.mpr hV)]
  have hthree : 3 * A^2 ≤ 4 * (c : ℝ)^2 := by nlinarith
  have hAless : A < 2 * c := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ A + 2 * c)]
  have hAVupper : Vq * A ≤ 2 * (c : ℝ)^2 := by nlinarith
  exact ⟨hthree, hAless, hAVupper⟩

theorem literalBox_weightedSq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {z : Coordinate} (hz : z ∈ literalBox X Y) :
    weightedSq X Y z ≤ 2 * (X * Y) := by
  rcases hz with ⟨hx, hy⟩
  have hx' : (z.1 : ℝ)^2 ≤ X^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (z.1 : ℝ)) (le_of_lt hX)).mpr hx
  have hy' : (z.2 : ℝ)^2 ≤ Y^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (z.2 : ℝ)) (le_of_lt hY)).mpr hy
  unfold weightedSq
  have h₁ := mul_le_mul_of_nonneg_left hx' (le_of_lt (div_pos hY hX))
  have h₂ := mul_le_mul_of_nonneg_left hy' (le_of_lt (div_pos hX hY))
  calc
    _ ≤ Y / X * X^2 + X / Y * Y^2 := add_le_add h₁ h₂
    _ = 2 * (X * Y) := by field_simp [ne_of_gt hX, ne_of_gt hY]; ring

/-- Determinants with the reduced basis control the two integer coordinates. -/
theorem ReducedMiddleBasis.coordinate_sq_bounds {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
    (z.1 : ℝ)^2 * weightedSq X Y B.R ≤ 4 * (X * Y) ∧
    (z.2 : ℝ)^2 * (c : ℝ)^2 ≤ 2 * (X * Y) * weightedSq X Y B.R := by
  let P := physical B.R B.V z
  let A := weightedSq X Y B.R
  let Vq := weightedSq X Y B.V
  have hA : 0 < A := weightedSq_pos hX hY (B.first_ne_zero hc)
  have hVq : 0 ≤ Vq := weightedSq_nonneg hX hY B.V
  have hP : 0 ≤ weightedSq X Y P := weightedSq_nonneg hX hY P
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hbox : weightedSq X Y P ≤ 2 * (X * Y) := literalBox_weightedSq hX hY hz
  have hVbound : Vq * A ≤ 2 * (c : ℝ)^2 := (B.reduction_bounds hc hX hY).2.2
  have hdetR : B.R.1 * P.2 - P.1 * B.R.2 = z.2 * c := by
    dsimp [P, physical]
    linear_combination z.2 * B.det
  have hdetV : B.V.1 * P.2 - P.1 * B.V.2 = -(z.1 * c) := by
    dsimp [P, physical]
    linear_combination -z.1 * B.det
  have hj := weighted_det_sq_le hX hY B.R P
  have hi := weighted_det_sq_le hX hY B.V P
  have hdetR' : (((B.R.1 * P.2 - P.1 * B.R.2 : ℤ) : ℝ)) = (z.2 : ℝ) * c := by
    exact_mod_cast hdetR
  have hdetV' : (((B.V.1 * P.2 - P.1 * B.V.2 : ℤ) : ℝ)) = -((z.1 : ℝ) * c) := by
    exact_mod_cast hdetV
  rw [hdetR'] at hj
  rw [hdetV'] at hi
  have hPboundA := mul_le_mul_of_nonneg_left hbox hA.le
  have hPboundV := mul_le_mul_of_nonneg_left hbox hVq
  have hjbound : (z.2 : ℝ)^2 * (c : ℝ)^2 ≤ 2 * (X * Y) * A := by
    nlinarith
  have hileft := mul_le_mul_of_nonneg_right hi hA.le
  have hiupper := mul_le_mul_of_nonneg_left hVbound
    (by positivity : 0 ≤ 2 * (X * Y))
  have hiprod : ((z.1 : ℝ)^2 * A) * (c : ℝ)^2 ≤
      (4 * (X * Y)) * (c : ℝ)^2 := by
    nlinarith [hPboundV, hileft, hiupper]
  have hibound : (z.1 : ℝ)^2 * A ≤ 4 * (X * Y) := by
    by_contra! h
    have hpos := mul_pos (sub_pos.mpr h) (sq_pos_of_pos hcR)
    nlinarith
  exact ⟨hibound, hjbound⟩

/-- Every literal endpoint has bounded integer coordinates in a reduced chart. -/
theorem ReducedMiddleBasis.coordinate_bound {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (H s₀ : ℝ) (hH : 0 < H) (hHsq : H ^ 2 = X * Y)
    (hs₀ : 0 < s₀)
    (hs₀lower : s₀ ^ 2 ≤ weightedSq X Y B.R)
    (hs₀upper : weightedSq X Y B.R < 4 * s₀ ^ 2)
    (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
    CoordinateBound (8 * H / s₀) (4 * H * s₀ / c) z := by
  obtain ⟨hi, hj⟩ := B.coordinate_sq_bounds hc hX hY z hz
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hi₀ : (z.1 : ℝ)^2 * s₀^2 ≤ 4 * H^2 := by
    have h := mul_le_mul_of_nonneg_left hs₀lower (sq_nonneg (z.1 : ℝ))
    nlinarith [hi]
  have hparallel : |(z.1 : ℝ)| * s₀ ≤ 2 * H := by
    apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hs₀.le) (by positivity)).mp
    calc
      (|(z.1 : ℝ)| * s₀)^2 = (z.1 : ℝ)^2 * s₀^2 := by rw [mul_pow, sq_abs]
      _ ≤ 4 * H^2 := hi₀
      _ = (2 * H)^2 := by ring
  have hfirst : |(z.1 : ℝ)| ≤ 8 * H / s₀ := by
    apply (le_div_iff₀ hs₀).mpr
    nlinarith
  have hj₀ : (z.2 : ℝ)^2 * (c : ℝ)^2 ≤ 8 * H^2 * s₀^2 := by
    have h := mul_le_mul_of_nonneg_left hs₀upper.le (by positivity : 0 ≤ 2 * H^2)
    nlinarith [hj]
  have hperp : |(z.2 : ℝ)| * c ≤ 4 * H * s₀ := by
    apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hcR.le) (by positivity)).mp
    calc
      (|(z.2 : ℝ)| * c)^2 = (z.2 : ℝ)^2 * (c : ℝ)^2 := by rw [mul_pow, sq_abs]
      _ ≤ 8 * H^2 * s₀^2 := hj₀
      _ ≤ (4 * H * s₀)^2 := by nlinarith [sq_nonneg H, sq_nonneg s₀]
  have hsecond : |(z.2 : ℝ)| ≤ 4 * H * s₀ / c := by
    apply (le_div_iff₀ hcR).mpr
    nlinarith
  exact ⟨hfirst, hsecond⟩

/-- The anchor uses the very same coordinate bound as every endpoint. -/
theorem ReducedMiddleBasis.anchor_coordinate_bound {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (H s₀ : ℝ) (hH : 0 < H) (hHsq : H ^ 2 = X * Y)
    (hs₀ : 0 < s₀)
    (hs₀lower : s₀ ^ 2 ≤ weightedSq X Y B.R)
    (hs₀upper : weightedSq X Y B.R < 4 * s₀ ^ 2)
    (hw : |(w : ℝ)| ≤ X) (ht : |(t : ℝ)| ≤ Y) :
    ∃ q : Coordinate, physical B.R B.V q = (-w, -t) ∧
      CoordinateBound (8 * H / s₀) (4 * H * s₀ / c) q := by
  obtain ⟨q, hq⟩ := B.toMiddleBasis.anchor_coordinates
  refine ⟨q, hq, ?_⟩
  apply B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper
  rw [hq]
  exact anchor_mem_literalBox hw ht

/-- The long chart supplies the exact scales consumed by the prime-cube cover. -/
theorem ReducedMiddleBasis.long_scale_bounds {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (H s₀ : ℝ) (hH : 0 < H) (hHsq : H ^ 2 = X * Y)
    (hs₀ : 0 < s₀)
    (hs₀lower : s₀ ^ 2 ≤ weightedSq X Y B.R)
    (hs₀upper : weightedSq X Y B.R < 4 * s₀ ^ 2)
    (hlong : (c : ℝ) ^ 2 < H ^ 2 * weightedSq X Y B.R) :
    let J₁ := 8 * H / s₀
    let J₂ := 4 * H * s₀ / c
    J₂ ≤ J₁ ∧ 2 < J₂ ∧ J₁ * J₂ = 32 * (X * Y / c) ∧
      J₁ < 16 * (X * Y / c) ∧ J₂ < 5 * Real.sqrt (X * Y / c) := by
  dsimp
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hA := (B.reduction_bounds hc hX hY).2.1
  have hs₀sq : s₀^2 < 2 * c := hs₀lower.trans_lt hA
  have horder : 4 * H * s₀ / c ≤ 8 * H / s₀ := by
    apply (div_le_div_iff₀ hcR hs₀).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ H) (sub_nonneg.mpr hs₀sq.le)]
  have hlong' : (c : ℝ)^2 < (2 * H * s₀)^2 := by
    have hmul := mul_lt_mul_of_pos_left hs₀upper (sq_pos_of_pos hH)
    nlinarith
  have hcs : (c : ℝ) < 2 * H * s₀ :=
    (sq_lt_sq₀ hcR.le (by positivity)).mp hlong'
  have hJ₂ : 2 < 4 * H * s₀ / c := by
    apply (lt_div_iff₀ hcR).mpr
    nlinarith
  have hprod : (8 * H / s₀) * (4 * H * s₀ / c) = 32 * (X * Y / c) := by
    field_simp [ne_of_gt hs₀, ne_of_gt hcR]
    nlinarith [hHsq]
  have hJ₁ : 8 * H / s₀ < 16 * (X * Y / c) := by
    have hJ₁' : 8 * H / s₀ < (16 * (X * Y)) / c := by
      apply (div_lt_div_iff₀ hs₀ hcR).mpr
      have hmul := mul_lt_mul_of_pos_left hcs (by positivity : 0 < 8 * H)
      nlinarith [hHsq]
    convert hJ₁' using 1 <;> ring
  have hA₃ := (B.reduction_bounds hc hX hY).1
  have hAupper : weightedSq X Y B.R < 3 * (c : ℝ) / 2 := by
    by_contra h
    have hge : 3 * (c : ℝ) / 2 ≤ weightedSq X Y B.R := le_of_not_gt h
    have hpos := mul_nonneg (sub_nonneg.mpr hge)
      (by linarith [weightedSq_nonneg hX hY B.R] :
        0 ≤ weightedSq X Y B.R + 3 * (c : ℝ) / 2)
    nlinarith [sq_pos_of_pos hcR]
  have hs₀upper' : s₀ ^ 2 < 3 * (c : ℝ) / 2 :=
    hs₀lower.trans_lt hAupper
  have hJ₂sq : (4 * H * s₀ / c) ^ 2 < 24 * (X * Y / c) := by
    calc
      _ = (16 * H ^ 2 / (c : ℝ) ^ 2) * s₀ ^ 2 := by ring
      _ < (16 * H ^ 2 / (c : ℝ) ^ 2) * (3 * (c : ℝ) / 2) :=
        mul_lt_mul_of_pos_left hs₀upper' (by positivity)
      _ = 24 * (X * Y / c) := by
        rw [← hHsq]
        field_simp [ne_of_gt hcR]
        ring
  have hBpos : 0 < X * Y / (c : ℝ) := div_pos (mul_pos hX hY) hcR
  have hJ₂sq' : (4 * H * s₀ / c) ^ 2 <
      (5 * Real.sqrt (X * Y / c)) ^ 2 := by
    calc
      _ < 24 * (X * Y / c) := hJ₂sq
      _ < 25 * (X * Y / c) := by nlinarith
      _ = (5 * Real.sqrt (X * Y / c)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hBpos.le]
        ring
  have hJ₂upper : 4 * H * s₀ / c < 5 * Real.sqrt (X * Y / c) :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mp hJ₂sq'
  exact ⟨horder, hJ₂, hprod, hJ₁, hJ₂upper⟩

private theorem finite_short_ball (c : ℕ) (X Y : ℝ)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) :
    {z : Coordinate | weightedSq X Y z ≤ weightedSq X Y (c, 0)}.Finite := by
  let d : ℝ := Y / X
  have hd : 0 < d := div_pos hY hX
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  let K : ℤ := ⌈d * c⌉
  have hK : d * c ≤ (K : ℝ) := Int.le_ceil _
  have hK0 : 0 ≤ K := by exact_mod_cast (le_trans (by positivity : (0 : ℝ) ≤ d * c) hK)
  apply (Set.finite_Icc ((-(c : ℤ), -K) : Coordinate) ((c, K) : Coordinate)).subset
  intro z hz
  have hq : d * (z.1 : ℝ)^2 + X / Y * (z.2 : ℝ)^2 ≤ d * (c : ℝ)^2 := by
    simpa [weightedSq, d] using hz
  have hterm : 0 ≤ X / Y * (z.2 : ℝ)^2 := by positivity
  have huProd : d * (z.1 : ℝ)^2 ≤ d * (c : ℝ)^2 := by linarith
  have huSq : (z.1 : ℝ)^2 ≤ (c : ℝ)^2 := by
    by_contra h
    have hstrict : (c : ℝ)^2 < (z.1 : ℝ)^2 := lt_of_not_ge h
    have hm := mul_lt_mul_of_pos_left hstrict hd
    linarith
  have huAbs : |(z.1 : ℝ)| ≤ c := by
    apply (sq_le_sq₀ (abs_nonneg _) hcR.le).mp
    simpa only [sq_abs] using huSq
  have huTerm : 0 ≤ d * (z.1 : ℝ)^2 := by positivity
  have hzProd : X / Y * (z.2 : ℝ)^2 ≤ d * (c : ℝ)^2 := by linarith
  have hde : d * (X / Y) = 1 := by
    dsimp [d]
    field_simp [ne_of_gt hX, ne_of_gt hY]
  have hzMult := mul_le_mul_of_nonneg_left hzProd hd.le
  have hzSq : (z.2 : ℝ)^2 ≤ (d * c)^2 := by
    nlinarith [hzMult]
  have hzAbs : |(z.2 : ℝ)| ≤ d * c := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hzSq
  change ((-(c : ℤ), -K) : Coordinate) ≤ z ∧ z ≤ ((c : ℤ), K)
  constructor
  · constructor
    · exact_mod_cast (abs_le.mp huAbs).1
    · exact_mod_cast (by linarith [abs_le.mp hzAbs] : -(K : ℝ) ≤ z.2)
  · constructor
    · exact_mod_cast (abs_le.mp huAbs).2
    · exact_mod_cast (by linarith [abs_le.mp hzAbs] : (z.2 : ℝ) ≤ K)

/-- The actual congruence lattice has a shortest nonzero physical vector. -/
theorem exists_shortest_middle_vector (c : ℕ) (t w : ℤ) (X Y : ℝ)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) :
    ∃ R : Coordinate, R ∈ middleLattice c t w ∧ R ≠ 0 ∧
      ∀ z ∈ middleLattice c t w, z ≠ 0 →
        weightedSq X Y R ≤ weightedSq X Y z := by
  let u : Coordinate := (c, 0)
  have hu : u ∈ middleLattice c t w := by
    change (c : ℤ) ∣ w * 0 - t * c
    simp
  have hu0 : u ≠ 0 := by
    intro h
    have : c = 0 := by simpa [u] using congrArg Prod.fst h
    omega
  let S : Set Coordinate :=
    {z | z ∈ middleLattice c t w ∧ z ≠ 0 ∧
      weightedSq X Y z ≤ weightedSq X Y u}
  have hfin : S.Finite :=
    (finite_short_ball c X Y hc hX hY).subset (by intro z hz; exact hz.2.2)
  have hne : S.Nonempty := ⟨u, hu, hu0, le_rfl⟩
  obtain ⟨R, hR, hmin⟩ := Set.exists_min_image S (weightedSq X Y) hfin hne
  refine ⟨R, hR.1, hR.2.1, ?_⟩
  intro z hz hz0
  by_cases hzu : weightedSq X Y z ≤ weightedSq X Y u
  · exact hmin z ⟨hz, hz0, hzu⟩
  · exact hR.2.2.trans (le_of_lt (lt_of_not_ge hzu))

private theorem shortest_coordinates_coprime {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B₀ : MiddleBasis c t w) (hX : 0 < X) (hY : 0 < Y)
    (R : Coordinate) (hR : R ∈ middleLattice c t w) (hR0 : R ≠ 0)
    (hmin : ∀ z ∈ middleLattice c t w, z ≠ 0 →
      weightedSq X Y R ≤ weightedSq X Y z) :
    ∃ i j : ℤ, physical B₀.R B₀.V (i, j) = R ∧ Int.gcd i j = 1 := by
  obtain ⟨i, j, hij⟩ := B₀.decompose R hR
  have hgpos : 0 < Int.gcd i j := by
    by_contra h
    have hg0 : Int.gcd i j = 0 := by omega
    have hi0 : i = 0 := by
      have hd : ((Int.gcd i j : ℕ) : ℤ) ∣ i := Int.gcd_dvd_left i j
      simpa [hg0] using hd
    have hj0 : j = 0 := by
      have hd : ((Int.gcd i j : ℕ) : ℤ) ∣ j := Int.gcd_dvd_right i j
      simpa [hg0] using hd
    apply hR0
    simpa [hi0, hj0, physical, Prod.zero_eq_mk] using hij.symm
  obtain ⟨g, i', j', hgpos', hgcd, hi, hj⟩ := Int.exists_gcd_one' hgpos
  let T : Coordinate := physical B₀.R B₀.V (i', j')
  have hT : T ∈ middleLattice c t w := B₀.physical_mem _
  have hRT : R = ((g : ℤ) * T.1, (g : ℤ) * T.2) := by
    rw [← hij]
    apply Prod.ext
    · dsimp [physical, T]
      rw [hi, hj]
      ring
    · dsimp [physical, T]
      rw [hi, hj]
      ring
  have hT0 : T ≠ 0 := by
    intro h
    apply hR0
    rw [hRT, h]
    simp
  have hTpos : 0 < weightedSq X Y T := weightedSq_pos hX hY hT0
  have hscale : weightedSq X Y R = (g : ℝ)^2 * weightedSq X Y T := by
    rw [hRT]
    simp only [weightedSq, Int.cast_mul, Int.cast_natCast, mul_pow]
    ring
  have hg1 : g = 1 := by
    by_contra h
    have hg2 : 2 ≤ g := by omega
    have hg2R : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have hgt : 0 < (g : ℝ)^2 - 1 := by nlinarith
    have hstrict := mul_pos hgt hTpos
    have hminimal := hmin T hT hT0
    nlinarith
  have hi' : i = i' := by simpa [hg1] using hi
  have hj' : j = j' := by simpa [hg1] using hj
  exact ⟨i, j, hij, by simpa [hi', hj'] using hgcd⟩

private def complete_primitive_middle_basis {c : ℕ} {t w : ℤ}
    (B₀ : MiddleBasis c t w) (i j : ℤ) (hij : Int.gcd i j = 1) :
    MiddleBasis c t w := by
  let a := Int.gcdA i j
  let b := Int.gcdB i j
  have hbez : i * a + j * b = 1 := by
    simpa [a, b, hij] using (Int.gcd_eq_gcd_ab i j).symm
  let R := physical B₀.R B₀.V (i, j)
  let V := physical B₀.R B₀.V (-b, a)
  refine ⟨R, V, ?_, B₀.physical_mem _, B₀.physical_mem _, ?_⟩
  · have hd : R.1 * V.2 - V.1 * R.2 =
        (i * a + j * b) * (B₀.R.1 * B₀.V.2 - B₀.V.1 * B₀.R.2) := by
      dsimp [R, V, physical]
      ring
    rw [hd, hbez, B₀.det]
    ring
  · intro z hz
    obtain ⟨x, y, hxy⟩ := B₀.decompose z hz
    let u := a * x + b * y
    let v := -(j * x) + i * y
    have hu : u * i + v * (-b) = x := by
      dsimp [u, v]
      calc
        _ = x * (i * a + j * b) := by ring
        _ = x := by rw [hbez]; ring
    have hv : u * j + v * a = y := by
      dsimp [u, v]
      calc
        _ = y * (i * a + j * b) := by ring
        _ = y := by rw [hbez]; ring
    refine ⟨u, v, ?_⟩
    rw [← hxy]
    apply Prod.ext
    · dsimp [R, V, physical]
      linear_combination B₀.R.1 * hu + B₀.V.1 * hv
    · dsimp [R, V, physical]
      linear_combination B₀.R.2 * hu + B₀.V.2 * hv

private def center_shortest_middle_basis {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : MiddleBasis c t w) (hX : 0 < X) (hY : 0 < Y)
    (hR0 : B.R ≠ 0)
    (hshort : ∀ z ∈ middleLattice c t w, z ≠ 0 →
      weightedSq X Y B.R ≤ weightedSq X Y z) :
    ReducedMiddleBasis c t w X Y := by
  let A := weightedSq X Y B.R
  let D := weightedDot X Y B.R B.V
  have hA : 0 < A := weightedSq_pos hX hY hR0
  let m : ℤ := (exists_centering_shift A D hA).choose
  have hm : (2 * (D - (m : ℝ) * A)) ^ 2 ≤ A ^ 2 :=
    (exists_centering_shift A D hA).choose_spec
  let Vc := physical B.R B.V (-m, 1)
  have hdot : weightedDot X Y B.R Vc = D - (m : ℝ) * A := by
    dsimp [Vc, physical, weightedDot, weightedSq, D, A]
    push_cast
    ring
  refine ⟨⟨B.R, Vc, ?_, B.memR, B.physical_mem _, ?_⟩, hshort, ?_⟩
  · dsimp [Vc, physical]
    linear_combination B.det
  · intro z hz
    obtain ⟨i, j, hij⟩ := B.decompose z hz
    refine ⟨i + j * m, j, ?_⟩
    rw [← hij]
    apply Prod.ext
    · dsimp [Vc, physical]
      ring
    · dsimp [Vc, physical]
      ring
  · rw [hdot]
    exact hm

/-- A shortest, centered, oriented basis of the original prime-cube lattice exists. -/
theorem exists_reduced_middle_basis (c : ℕ) (t w : ℤ) (X Y : ℝ)
    [NeZero c] (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (hw : IsUnit (w : ZMod c)) :
    Nonempty (ReducedMiddleBasis c t w X Y) := by
  let B₀ := middleBasis_of_unit c t w hw
  obtain ⟨R, hR, hR0, hshort⟩ := exists_shortest_middle_vector c t w X Y hc hX hY
  obtain ⟨i, j, hij, hgcd⟩ :=
    shortest_coordinates_coprime B₀ hX hY R hR hR0 hshort
  let B₁ := complete_primitive_middle_basis B₀ i j hgcd
  have hB₁ : B₁.R = R := hij
  have hB₁0 : B₁.R ≠ 0 := by simpa [hB₁] using hR0
  have hB₁short : ∀ z ∈ middleLattice c t w, z ≠ 0 →
      weightedSq X Y B₁.R ≤ weightedSq X Y z := by
    simpa only [hB₁] using hshort
  exact ⟨center_shortest_middle_basis B₁ hX hY hB₁0 hB₁short⟩

/-- The reduced length lies in one uniquely chosen dyadic annulus. -/
theorem exists_dyadic_middle_scale (A : ℝ) (hA : 0 < A) :
    ∃ n : ℤ, let s₀ := (2 : ℝ) ^ n;
      0 < s₀ ∧ s₀ ^ 2 ≤ A ∧ A < 4 * s₀ ^ 2 := by
  let S := Real.sqrt A
  have hS : 0 < S := Real.sqrt_pos.2 hA
  have hSsq : S ^ 2 = A := Real.sq_sqrt hA.le
  let n : ℤ := ⌊Real.logb 2 S⌋
  let s₀ : ℝ := (2 : ℝ) ^ n
  have hs₀ : 0 < s₀ := by positivity
  have hfloor : (n : ℝ) ≤ Real.logb 2 S := Int.floor_le _
  have hceil : Real.logb 2 S < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hlow : s₀ ≤ S := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hfloor
    rw [Real.rpow_intCast, Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hS] at h
    exact h
  have hupp : S < 2 * s₀ := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hceil
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hS,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast] at h
    norm_num at h
    dsimp [s₀]
    nlinarith
  refine ⟨n, hs₀, ?_, ?_⟩
  · rw [← hSsq]
    exact (sq_le_sq₀ hs₀.le hS.le).mpr hlow
  · rw [← hSsq]
    have hs : S ^ 2 < (2 * s₀)^2 :=
      (sq_lt_sq₀ hS.le (by positivity)).mpr hupp
    nlinarith

/-- Literal endpoint membership realizes the coefficient and height inputs of
`PrimeCube.actual_singular_factor_cover` in the chosen reduced chart. -/
theorem ReducedMiddleBasis.actual_endpoint_inputs {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y)
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y)
    (H s₀ : ℝ) (hH : 0 < H) (hHsq : H ^ 2 = X * Y)
    (hs₀ : 0 < s₀)
    (hs₀lower : s₀ ^ 2 ≤ weightedSq X Y B.R)
    (hs₀upper : weightedSq X Y B.R < 4 * s₀ ^ 2)
    (hlong : (c : ℝ) ^ 2 < H ^ 2 * weightedSq X Y B.R)
    (q : Coordinate) (base e : Endpoint)
    (hq : physical B.R B.V q ∈ literalBox X Y)
    (hb₁ : physical B.R B.V base.1 ∈ literalBox X Y)
    (hb₂ : physical B.R B.V base.2 ∈ literalBox X Y)
    (he₁ : physical B.R B.V e.1 ∈ literalBox X Y)
    (he₂ : physical B.R B.V e.2 ∈ literalBox X Y) :
    let J₁ := 8 * H / s₀
    let J₂ := 4 * H * s₀ / c
    J₂ ≤ J₁ ∧ 1 ≤ J₂ ∧
      (|(coeffL q e : ℝ)| ≤ 3 * J₁ ∧ |(coeffM q e : ℝ)| ≤ 3 * J₂ ∧
       |(coeffQ e : ℝ)| ≤ J₁ ^ 2 ∧ |(coeffR e : ℝ)| ≤ 2 * J₁ * J₂ ∧
       |(coeffS e : ℝ)| ≤ J₂ ^ 2) ∧
      (∀ j ≤ (pencil q base e).natDegree,
        |((pencil q base e).coeff j : ℝ)| ≤
          18 * J₁ ^ (3 - j) * J₂ ^ j) := by
  dsimp
  have hscale := B.long_scale_bounds hc hX hY H s₀ hH hHsq hs₀
    hs₀lower hs₀upper hlong
  have hqb := B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper q hq
  have hbb₁ := B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper base.1 hb₁
  have hbb₂ := B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper base.2 hb₂
  have heb₁ := B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper e.1 he₁
  have heb₂ := B.coordinate_bound hc hX hY H s₀ hH hHsq hs₀ hs₀lower hs₀upper e.2 he₂
  exact ⟨hscale.1, by linarith [hscale.2.1],
    actual_coefficient_bounds _ _ q e hqb heb₁ heb₂,
    actual_pencil_height _ _ q base e hqb hbb₁ hbb₂ heb₁ heb₂⟩

end
end D5.S3.Arith.CharacterSums.Original
