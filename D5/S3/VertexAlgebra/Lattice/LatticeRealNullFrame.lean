/- GID: D5/S3/VertexAlgebra/Lattice/LatticeRealNullFrame
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeRealNullFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original real Lorentzian signature geometry and positive transverse complexification. -/

/- Original integral-lattice real Gram coordinates. The source-only draft at
ba3cb869 was fallible input, repaired against Lean 4.35 and pinned Mathlib.
The original native run used cbbea638. Delivery uses the accepted corrected
coordinate supplier from PR #25556, merge 835f8774. Classical Sylvester
signature theory supplies the normal form; the charge-adapted plane, projection inverse, positive real complement
and faithful conjugation-fixed complex basis are proved here.
proof_shape: content
admission_basis: escape-witness
escape_witness: The signature-derived real charge-adapted plane contains the
selected nonzero integral charge, has a detecting null orientation, and its
actual Gram complement admits a positive real orthonormal complexification.
No BPZ polynomial, full no-ghost/BRST/string/Monster/AdS claim is made. -/
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic

/-! Real Lorentzian geometry on the original integral-lattice coordinates. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeRealNullFrame

open LatticeGeneratingFieldLocality LatticeLightConeCoordinates
open scoped BigOperators

/-- The real scalar extension of the original finite integral coordinates. -/
abbrev E_R (D : LatticeData) := Fin D.rank → ℝ

def gramReal (D : LatticeData) : Matrix (Fin D.rank) (Fin D.rank) ℝ :=
  fun i j => (D.G i j : ℝ)

abbrev B_R (D : LatticeData) : LinearMap.BilinForm ℝ (E_R D) :=
  (gramReal D).toBilin'

def g_R (D : LatticeData) (v w : E_R D) : ℝ := B_R D v w

theorem g_R_apply (D : LatticeData) (v w : E_R D) :
    g_R D v w = ∑ i, ∑ j, v i * (D.G i j : ℝ) * w j :=
  Matrix.toBilin'_apply (gramReal D) v w

theorem g_R_symm (D : LatticeData) (v w : E_R D) : g_R D v w = g_R D w v := by
  simp only [g_R_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [D.symmetric j i]
  ring

@[simp] theorem g_R_zero_right (D : LatticeData) (v : E_R D) : g_R D v 0 = 0 := by
  exact map_zero (B_R D v)

@[simp] theorem g_R_add_right (D : LatticeData) (v w x : E_R D) :
    g_R D v (w + x) = g_R D v w + g_R D v x := by
  exact map_add (B_R D v) w x

@[simp] theorem g_R_smul_right (D : LatticeData) (v w : E_R D) (c : ℝ) :
    g_R D v (c • w) = c * g_R D v w := by
  exact map_smul (B_R D v) c w

@[simp] theorem g_R_sub_right (D : LatticeData) (v w x : E_R D) :
    g_R D v (w - x) = g_R D v w - g_R D v x := by
  exact map_sub (B_R D v) w x

@[simp] theorem g_R_add_left (D : LatticeData) (v w x : E_R D) :
    g_R D (v + w) x = g_R D v x + g_R D w x := by
  rw [g_R_symm, g_R_add_right, g_R_symm D x v, g_R_symm D x w]

@[simp] theorem g_R_smul_left (D : LatticeData) (v w : E_R D) (c : ℝ) :
    g_R D (c • v) w = c * g_R D v w := by
  rw [g_R_symm, g_R_smul_right, g_R_symm]

@[simp] theorem g_R_sub_left (D : LatticeData) (v w x : E_R D) :
    g_R D (v - w) x = g_R D v x - g_R D w x := by
  rw [g_R_symm, g_R_sub_right, g_R_symm D x v, g_R_symm D x w]


def Q_R (D : LatticeData) : QuadraticForm ℝ (E_R D) := (B_R D).toQuadraticMap

@[simp] theorem Q_R_apply (D : LatticeData) (v : E_R D) : Q_R D v = g_R D v v := rfl

theorem real_polarization (D : LatticeData) (v w : E_R D) :
    Q_R D (v + w) - Q_R D v - Q_R D w = 2 * g_R D v w := by
  simp only [Q_R_apply, g_R_add_left, g_R_add_right, g_R_symm D w v]
  ring

@[simp] theorem finrank_E_R (D : LatticeData) : Module.finrank ℝ (E_R D) = D.rank := by
  simp [E_R]

/-- No change of integral charge carrier is made. -/
def realCharge {D : LatticeData} (p : Charge D) : E_R D := fun i => (p i : ℝ)

theorem realCharge_injective (D : LatticeData) : Function.Injective (@realCharge D) := by
  intro p q h
  funext i
  have hi : (p i : ℝ) = (q i : ℝ) := congrFun h i
  exact_mod_cast hi

@[simp] theorem realCharge_zero (D : LatticeData) : realCharge (0 : Charge D) = 0 := by
  ext i
  simp [realCharge]

theorem realCharge_ne_zero {D : LatticeData} {p : Charge D} (hp : p ≠ 0) :
    realCharge p ≠ 0 := by
  intro h
  exact hp (realCharge_injective D (h.trans (realCharge_zero D).symm))

def complexify (D : LatticeData) : E_R D →ₗ[ℝ] E D where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp [Complex.real_smul]

def realPart {D : LatticeData} (z : E D) : E_R D := fun i => (z i).re
def imagPart {D : LatticeData} (z : E D) : E_R D := fun i => (z i).im

@[simp] theorem realPart_complexify (D : LatticeData) (v : E_R D) :
    realPart (complexify D v) = v := by ext i; simp [complexify, realPart]

@[simp] theorem imagPart_complexify (D : LatticeData) (v : E_R D) :
    imagPart (complexify D v) = 0 := by ext i; simp [complexify, imagPart]

@[simp] theorem complexify_charge {D : LatticeData} (p : Charge D) :
    complexify D (realCharge p) = chargeVector p := by
  ext i
  simp [complexify, realCharge, chargeVector]

theorem complexify_decomposition {D : LatticeData} (z : E D) :
    complexify D (realPart z) + Complex.I • complexify D (imagPart z) = z := by
  ext i
  simpa [complexify, realPart, imagPart, smul_eq_mul, mul_comm] using Complex.re_add_im (z i)

/-- Literal finite-sum scalar extension of the original Gram form. -/
theorem complexify_gram (D : LatticeData) (v w : E_R D) :
    g D (complexify D v) (complexify D w) = (g_R D v w : ℂ) := by
  simp [complexify, g, g_R_apply, Complex.ofReal_sum, Complex.ofReal_mul]

@[simp] theorem gram_real_left_re (D : LatticeData) (v : E_R D) (z : E D) :
    (g D (complexify D v) z).re = g_R D v (realPart z) := by
  simp [complexify, g, g_R_apply, realPart, Complex.mul_re, Complex.mul_im]

@[simp] theorem gram_real_left_im (D : LatticeData) (v : E_R D) (z : E D) :
    (g D (complexify D v) z).im = g_R D v (imagPart z) := by
  simp [complexify, g, g_R_apply, imagPart, Complex.mul_re, Complex.mul_im]

/- The following is an extracted normal form, not an additional hypothesis of
   the existence result. Its construction counts the literal Sylvester weights. -/
structure LorentzNormalForm (D : LatticeData) where
  weights : Fin D.rank → ℝ
  iso : QuadraticMap.IsometryEquiv (Q_R D) (QuadraticMap.weightedSumSquares ℝ weights)
  negativeIndex : Fin D.rank
  negative_weight : weights negativeIndex = -1
  other_weight : ∀ i, i ≠ negativeIndex → weights i = 1

theorem exists_lorentzNormalForm (D : LatticeData)
    (hneg : sigNeg (Q_R D) = 1) (hpos : sigPos (Q_R D) = D.rank - 1) :
    Nonempty (LorentzNormalForm D) := by
  classical
  have hsyl : ∃ w : Fin D.rank → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (Q_R D) (QuadraticMap.weightedSumSquares ℝ w) := by
    have h := QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared (Q_R D)
    rw [finrank_E_R D] at h
    exact h
  obtain ⟨w, hw, he⟩ := hsyl
  have hn : {i | w i < 0}.ncard = 1 := by
    rw [← QuadraticForm.sigNeg_of_equiv_weightedSumSquares he, hneg]
  have hp : {i | 0 < w i}.ncard = D.rank - 1 := by
    rw [← QuadraticForm.sigPos_of_equiv_weightedSumSquares he, hpos]
  obtain ⟨m, hm⟩ := Set.ncard_eq_one.mp hn
  have hwm : w m = -1 := by
    have hlt : w m < 0 := by
      change m ∈ {i | w i < 0}
      rw [hm]
      simp
    rcases hw m with h | h | h <;> linarith
  have hsub : {i | 0 < w i} ⊆ {i | w i < 0}ᶜ := by
    intro i hi
    change ¬ w i < 0
    change 0 < w i at hi
    linarith
  have hcard : ({i | w i < 0}ᶜ : Set (Fin D.rank)).ncard = D.rank - 1 := by
    rw [Set.ncard_compl, hn, Nat.card_fin]
  have hcover : {i | 0 < w i} = {i | w i < 0}ᶜ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hp])
  have hother (i : Fin D.rank) (hi : i ≠ m) : w i = 1 := by
    have hnot : i ∉ {j | w j < 0} := by simpa [hm] using hi
    have hlt : 0 < w i := by
      change i ∈ {j | 0 < w j}
      rw [hcover]
      exact hnot
    rcases hw i with h | h | h <;> linarith
  obtain ⟨e⟩ := he
  exact ⟨⟨w, e, m, hwm, hother⟩⟩

namespace LorentzNormalForm

variable {D : LatticeData} (N : LorentzNormalForm D)

theorem quadratic_coordinates (v : E_R D) :
    Q_R D v = ∑ i, N.weights i * (N.iso v i) ^ 2 := by
  simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using
    (N.iso.map_app v).symm

/-- Polarization of the actual quadratic isometry, with the factor two checked. -/
theorem bilinear_coordinates (v w : E_R D) :
    g_R D v w = ∑ i, N.weights i * N.iso v i * N.iso w i := by
  have hpolar := real_polarization D v w
  rw [N.quadratic_coordinates, N.quadratic_coordinates, N.quadratic_coordinates] at hpolar
  have hexpand :
      (∑ i, N.weights i * (N.iso (v + w) i) ^ 2) -
          (∑ i, N.weights i * (N.iso v i) ^ 2) -
          (∑ i, N.weights i * (N.iso w i) ^ 2) =
        2 * ∑ i, N.weights i * N.iso v i * N.iso w i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_add, Pi.add_apply]
    ring
  linarith

def time : E_R D := N.iso.symm (Pi.single N.negativeIndex 1)

@[simp] theorem iso_time : N.iso N.time = Pi.single N.negativeIndex 1 := by
  simp [time]

@[simp] theorem time_norm : g_R D N.time N.time = -1 := by
  rw [N.bilinear_coordinates]
  simp [N.negative_weight, Pi.single_apply]

theorem time_pairing (v : E_R D) : g_R D N.time v = -N.iso v N.negativeIndex := by
  rw [N.bilinear_coordinates]
  simp [N.negative_weight, Pi.single_apply]

theorem positive_perp (v : E_R D) (hv : g_R D N.time v = 0) (hv0 : v ≠ 0) :
    0 < Q_R D v := by
  classical
  have hm : N.iso v N.negativeIndex = 0 := by
    rw [N.time_pairing] at hv
    linarith
  have hex : ∃ i, N.iso v i ≠ 0 := by
    by_contra! h
    apply hv0
    apply N.iso.injective
    ext i
    simpa using h i
  obtain ⟨j, hj⟩ := hex
  have hjm : j ≠ N.negativeIndex := by rintro rfl; exact hj hm
  rw [N.quadratic_coordinates]
  apply Finset.sum_pos'
  · intro i hi
    by_cases him : i = N.negativeIndex
    · simp [him, hm]
    · rw [N.other_weight i him]
      positivity
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [N.other_weight j hjm]
    exact mul_pos zero_lt_one (sq_pos_of_ne_zero hj)

/-- rank ≥ 2 supplies an actual spatial unit, including when the spatial
component of the selected charge is zero. -/
theorem exists_spatial_unit (hrank : 2 ≤ D.rank) :
    ∃ u : E_R D, g_R D N.time u = 0 ∧ g_R D u u = 1 := by
  let i0 : Fin D.rank := ⟨0, by omega⟩
  let i1 : Fin D.rank := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    change 0 = 1 at this
    omega
  have hex : ∃ j : Fin D.rank, j ≠ N.negativeIndex := by
    by_cases h : i0 = N.negativeIndex
    · exact ⟨i1, fun h' => h01 (h.trans h'.symm)⟩
    · exact ⟨i0, h⟩
  obtain ⟨j, hj⟩ := hex
  refine ⟨N.iso.symm (Pi.single j 1), ?_, ?_⟩
  · rw [N.time_pairing]
    simp [Ne.symm hj]
  · rw [N.bilinear_coordinates]
    simp [Pi.single_apply, N.other_weight j hj]

end LorentzNormalForm

/-- A proved real orthonormal Lorentz plane with positive time-orthogonal space.
The final existence theorem constructs this object from signatures alone. -/
structure PositivePlane (D : LatticeData) where
  time : E_R D
  space : E_R D
  time_norm : g_R D time time = -1
  space_norm : g_R D space space = 1
  time_space : g_R D time space = 0
  positive_perp : ∀ v : E_R D, g_R D time v = 0 → v ≠ 0 → 0 < Q_R D v

/-- The explicit a,s,sqrt,epsilon construction, without a causality restriction
on p. In particular s=0 and both nonzero null orientations are included. -/
theorem exists_charge_plane (D : LatticeData) (hrank : 2 ≤ D.rank)
    (hneg : sigNeg (Q_R D) = 1) (hpos : sigPos (Q_R D) = D.rank - 1)
    (p : Charge D) (hp : p ≠ 0) :
    ∃ P : PositivePlane D, ∃ a c : ℝ,
      realCharge p = a • P.time + c • P.space ∧ -a + c ≠ 0 := by
  classical
  obtain ⟨N⟩ := exists_lorentzNormalForm D hneg hpos
  let t := N.time
  let q := realCharge p
  let a := -g_R D t q
  let s := q - a • t
  have htt : g_R D t t = -1 := N.time_norm
  have hts : g_R D t s = 0 := by
    simp only [s, g_R_sub_right, g_R_smul_right, htt, a]
    ring
  have hsq : 0 ≤ Q_R D s := by
    by_cases hs : s = 0
    · simp [hs]
    · exact (N.positive_perp s hts hs).le
  let b := Real.sqrt (Q_R D s)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = Q_R D s := Real.sq_sqrt hsq
  have hu0 : ∃ u0 : E_R D,
      g_R D t u0 = 0 ∧ g_R D u0 u0 = 1 ∧ s = b • u0 := by
    by_cases hs : s = 0
    · obtain ⟨u0, htu0, hu0⟩ := N.exists_spatial_unit hrank
      refine ⟨u0, htu0, hu0, ?_⟩
      have hb0 : b = 0 := by simp [b, hs]
      simp [hs, hb0]
    · have hbpos : 0 < b := Real.sqrt_pos.2 (N.positive_perp s hts hs)
      have hb0 : b ≠ 0 := ne_of_gt hbpos
      refine ⟨b⁻¹ • s, ?_, ?_, ?_⟩
      · simp [hts]
      · simp only [g_R_smul_left, g_R_smul_right]
        rw [← Q_R_apply, ← hb2]
        field_simp [hb0]
      · rw [smul_smul, mul_inv_cancel₀ hb0, one_smul]
  obtain ⟨u0, htu0, hu0, hs⟩ := hu0
  have hq : q = a • t + b • u0 := by
    rw [← hs]
    dsimp [s]
    abel
  have hab : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨ha, hb0⟩
    apply realCharge_ne_zero hp
    change q = 0
    rw [hq, ha, hb0, zero_smul, zero_smul, add_zero]
  let eps : ℝ := if a ≠ b then 1 else -1
  have heps : eps ^ 2 = 1 := by
    dsimp [eps]
    split_ifs <;> norm_num
  have hdetect : -a + eps * b ≠ 0 := by
    by_cases h : a ≠ b
    · simp only [eps, ite_eq_left h, one_mul]
      intro hz
      exact h (by linarith)
    · have hab' : a = b := not_ne_iff.mp h
      have hb0 : b ≠ 0 := by intro hz; exact hab ⟨hab'.trans hz, hz⟩
      simp only [eps, ite_eq_right h, neg_mul, one_mul]
      intro hz
      exact hb0 (by linarith)
  let u := eps • u0
  have huu : g_R D u u = 1 := by
    simp only [u, g_R_smul_left, g_R_smul_right, hu0]
    nlinarith [heps]
  have htu : g_R D t u = 0 := by simp [u, htu0]
  let P : PositivePlane D := ⟨t, u, htt, huu, htu, N.positive_perp⟩
  refine ⟨P, a, eps * b, ?_, hdetect⟩
  change q = a • t + (eps * b) • (eps • u0)
  rw [smul_smul]
  have hcoeff : eps * b * eps = b := by
    calc
      eps * b * eps = eps ^ 2 * b := by ring
      _ = b := by rw [heps, one_mul]
  rw [hcoeff]
  exact hq

def pairingR (D : LatticeData) (v : E_R D) : E_R D →ₗ[ℝ] ℝ := B_R D v

namespace PositivePlane

variable {D : LatticeData} (P : PositivePlane D)

@[simp] theorem space_time : g_R D P.space P.time = 0 := by
  rw [g_R_symm, P.time_space]

def ePlus : E_R D := P.time + P.space
def eMinus : E_R D := (1 / 2 : ℝ) • (P.space - P.time)

theorem plus_null : g_R D P.ePlus P.ePlus = 0 := by
  simp only [ePlus, g_R_add_left, g_R_add_right, P.time_norm, P.space_norm,
    P.time_space, P.space_time]
  norm_num

theorem minus_null : g_R D P.eMinus P.eMinus = 0 := by
  simp only [eMinus, g_R_smul_left, g_R_smul_right, g_R_sub_left, g_R_sub_right,
    P.time_norm, P.space_norm, P.time_space, P.space_time]
  norm_num

theorem plus_minus : g_R D P.ePlus P.eMinus = 1 := by
  simp only [ePlus, eMinus, g_R_smul_right, g_R_add_left, g_R_sub_right,
    P.time_norm, P.space_norm, P.time_space, P.space_time]
  norm_num

/-- The actual two Gram kernels, not an abstract supplied complement. -/
def K_R : Submodule ℝ (E_R D) := (pairingR D P.ePlus).ker ⊓ (pairingR D P.eMinus).ker

theorem mem_K_R_iff (v : E_R D) :
    v ∈ P.K_R ↔ g_R D P.time v = 0 ∧ g_R D P.space v = 0 := by
  change (g_R D P.ePlus v = 0 ∧ g_R D P.eMinus v = 0) ↔ _
  simp only [ePlus, eMinus, g_R_add_left, g_R_smul_left, g_R_sub_left]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

@[simp] theorem time_K (k : P.K_R) : g_R D P.time (k : E_R D) = 0 :=
  (P.mem_K_R_iff k).mp k.property |>.1

@[simp] theorem space_K (k : P.K_R) : g_R D P.space (k : E_R D) = 0 :=
  (P.mem_K_R_iff k).mp k.property |>.2

def projectionVector : E_R D →ₗ[ℝ] E_R D :=
  LinearMap.id + (pairingR D P.time).smulRight P.time -
    (pairingR D P.space).smulRight P.space

def projection : E_R D →ₗ[ℝ] P.K_R :=
  P.projectionVector.codRestrict P.K_R (by
    intro v
    rw [P.mem_K_R_iff]
    constructor <;>
      simp [projectionVector, pairingR, P.time_norm, P.space_norm, P.time_space, P.space_time] <;>
        simp [g_R])

@[simp] theorem coe_projection (v : E_R D) :
    (P.projection v : E_R D) =
      v + g_R D P.time v • P.time - g_R D P.space v • P.space := rfl

/-- The real direct sum, with proved inverse; only the complex counterpart
is delegated to the existing coordinate machinery. -/
def splitting : E_R D ≃ₗ[ℝ] ℝ × ℝ × P.K_R where
  toFun v := (-g_R D P.time v, g_R D P.space v, P.projection v)
  invFun x := x.1 • P.time + x.2.1 • P.space + (x.2.2 : E_R D)
  left_inv v := by
    change -g_R D P.time v • P.time + g_R D P.space v • P.space +
      (v + g_R D P.time v • P.time - g_R D P.space v • P.space) = v
    simp only [neg_smul]
    abel
  right_inv x := by
    rcases x with ⟨a, b, k⟩
    have ht : g_R D P.time (a • P.time + b • P.space + (k : E_R D)) = -a := by
      simp [P.time_norm, P.time_space]
    have hu : g_R D P.space (a • P.time + b • P.space + (k : E_R D)) = b := by
      simp [P.space_norm, P.space_time]
    apply Prod.ext (by simpa using congrArg Neg.neg ht)
    apply Prod.ext hu
    apply Subtype.ext
    change a • P.time + b • P.space + (k : E_R D) +
      g_R D P.time (a • P.time + b • P.space + (k : E_R D)) • P.time -
      g_R D P.space (a • P.time + b • P.space + (k : E_R D)) • P.space = _
    rw [ht, hu, neg_smul]
    abel
  map_add' v w := by simp [map_add, add_comm]
  map_smul' c v := by simp [map_smul, smul_eq_mul]

theorem finrank_K_R_add_two : Module.finrank ℝ P.K_R + 2 = D.rank := by
  have h := P.splitting.finrank_eq
  have hdim : D.rank = 1 + (1 + Module.finrank ℝ P.K_R) := by
    simpa only [finrank_E_R, Module.finrank_prod, Module.finrank_self] using h
  omega

theorem finrank_K_R : Module.finrank ℝ P.K_R = D.rank - 2 := by
  have := P.finrank_K_R_add_two
  omega

theorem positive_K_R : ((Q_R D).restrict P.K_R).PosDef := by
  intro k hk
  exact P.positive_perp k (P.time_K k) (by simpa using hk)

theorem projection_charge_zero (p : Charge D) (a c : ℝ)
    (hp : realCharge p = a • P.time + c • P.space) :
    P.projection (realCharge p) = 0 := by
  apply Subtype.ext
  simp only [Submodule.coe_zero]
  simp only [coe_projection, hp, g_R_add_right, g_R_smul_right,
    P.time_norm, P.space_norm, P.time_space, P.space_time, mul_zero, add_zero,
    zero_add, mul_one, mul_neg_one]
  simp only [neg_smul]
  abel

theorem charge_pairing (p : Charge D) (a c : ℝ)
    (hp : realCharge p = a • P.time + c • P.space) :
    g_R D P.ePlus (realCharge p) = -a + c := by
  simp [ePlus, hp, P.time_norm, P.space_norm, P.time_space, P.space_time]

/-- Coordinatewise complexification supplies every field of the EXISTING
NullFrame, with exactly its plus/minus convention. -/
def complexFrame : NullFrame D where
  ePlus := complexify D P.ePlus
  eMinus := complexify D P.eMinus
  plus_null := by rw [complexify_gram, P.plus_null]; norm_num
  minus_null := by rw [complexify_gram, P.minus_null]; norm_num
  plus_minus := by rw [complexify_gram, P.plus_minus]; norm_num

theorem mem_complex_K_iff (z : E D) :
    z ∈ P.complexFrame.K ↔ realPart z ∈ P.K_R ∧ imagPart z ∈ P.K_R := by
  change (g D (complexify D P.ePlus) z = 0 ∧
    g D (complexify D P.eMinus) z = 0) ↔
      ((g_R D P.ePlus (realPart z) = 0 ∧ g_R D P.eMinus (realPart z) = 0) ∧
       (g_R D P.ePlus (imagPart z) = 0 ∧ g_R D P.eMinus (imagPart z) = 0))
  simp only [Complex.ext_iff, gram_real_left_re, gram_real_left_im,
    Complex.zero_re, Complex.zero_im]
  tauto

def realK (z : P.complexFrame.K) : P.K_R :=
  ⟨realPart (z : E D), ((P.mem_complex_K_iff z).mp z.property).1⟩

def imagK (z : P.complexFrame.K) : P.K_R :=
  ⟨imagPart (z : E D), ((P.mem_complex_K_iff z).mp z.property).2⟩

def includeK (v : P.K_R) : P.complexFrame.K :=
  ⟨complexify D (v : E_R D), by
    rw [P.mem_complex_K_iff, realPart_complexify, imagPart_complexify]
    exact ⟨v.property, P.K_R.zero_mem⟩⟩

theorem complex_projection_bridge (v : E_R D) :
    (P.complexFrame.projK (complexify D v) : E D) =
      complexify D (P.projection v : E_R D) := by
  rw [NullFrame.coe_projK, coe_projection]
  change complexify D v -
    g D (complexify D P.eMinus) (complexify D v) • complexify D P.ePlus -
    g D (complexify D P.ePlus) (complexify D v) • complexify D P.eMinus = _
  simp only [complexify_gram, ePlus, eMinus, g_R_add_left, g_R_smul_left, g_R_sub_left]
  ext i
  simp [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, smul_eq_mul]
  ring

theorem complex_projection_charge_zero (p : Charge D) (a c : ℝ)
    (hp : realCharge p = a • P.time + c • P.space) :
    P.complexFrame.projK (chargeVector p) = 0 := by
  apply Subtype.ext
  rw [← complexify_charge, P.complex_projection_bridge,
    P.projection_charge_zero p a c hp]
  exact map_zero (complexify D)

end PositivePlane

namespace PositivePlane

variable {D : LatticeData} (P : PositivePlane D)

/-- A real Sylvester isometry on the ACTUAL positive restriction produces an
orthonormal basis. All weights are forced to +1 by positivity of coordinate
vectors. This also applies to the empty basis at rank two. -/
theorem exists_real_orthonormalBasis :
    ∃ b : Module.Basis (Fin (D.rank - 2)) ℝ P.K_R,
      ∀ i j, g_R D (b i : E_R D) (b j : E_R D) = if i = j then 1 else 0 := by
  classical
  have hsyl : ∃ w : Fin (D.rank - 2) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      QuadraticMap.Equivalent ((Q_R D).restrict P.K_R)
        (QuadraticMap.weightedSumSquares ℝ w) := by
    have h := QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared
      ((Q_R D).restrict P.K_R)
    rw [P.finrank_K_R] at h
    exact h
  obtain ⟨w, hw, ⟨e⟩⟩ := hsyl
  have hw1 (i : Fin (D.rank - 2)) : w i = 1 := by
    have hunit : (Pi.single i (1 : ℝ) : Fin (D.rank - 2) → ℝ) ≠ 0 := by
      intro h
      have hi := congrFun h i
      simp at hi
    have hv : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      apply hunit
      have := congrArg e h
      simp at this
    have hval : ((Q_R D).restrict P.K_R) (e.symm (Pi.single i 1)) = w i := by
      have := e.map_app (e.symm (Pi.single i 1))
      simp [QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
    have hpos : 0 < w i := by
      rw [← hval]
      exact P.positive_K_R _ hv
    rcases hw i with h | h | h <;> linarith
  have hquad (v : P.K_R) : Q_R D (v : E_R D) = ∑ i, (e v i) ^ 2 := by
    simpa only [QuadraticMap.restrict_apply, QuadraticMap.weightedSumSquares_apply,
      hw1, smul_eq_mul, one_mul, pow_two] using (e.map_app v).symm
  have hbilin (v x : P.K_R) :
      g_R D (v : E_R D) (x : E_R D) = ∑ i, e v i * e x i := by
    have hpolar := real_polarization D (v : E_R D) (x : E_R D)
    have hvx := hquad (v + x)
    change Q_R D ((v : E_R D) + (x : E_R D)) = _ at hvx
    rw [hvx, hquad v, hquad x] at hpolar
    have hexpand : (∑ i, (e (v + x) i) ^ 2) -
        (∑ i, (e v i) ^ 2) - (∑ i, (e x i) ^ 2) = 2 * ∑ i, e v i * e x i := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [map_add, Pi.add_apply]
      ring
    linarith
  let b : Module.Basis (Fin (D.rank - 2)) ℝ P.K_R :=
    (Pi.basisFun ℝ (Fin (D.rank - 2))).map e.toLinearEquiv.symm
  have hb (i : Fin (D.rank - 2)) : e (b i) = Pi.single i 1 := by
    simp [b, Module.Basis.map_apply, Pi.basisFun_apply]
  refine ⟨b, ?_⟩
  intro i j
  rw [hbilin, hb, hb]
  simp [Pi.single_apply, eq_comm]

def realBasis : Module.Basis (Fin (D.rank - 2)) ℝ P.K_R :=
  Classical.choose P.exists_real_orthonormalBasis

theorem realBasis_gram (i j : Fin (D.rank - 2)) :
    g_R D (P.realBasis i : E_R D) (P.realBasis j : E_R D) =
      if i = j then 1 else 0 :=
  Classical.choose_spec P.exists_real_orthonormalBasis i j

theorem realBasis_coeff (v : P.K_R) (j : Fin (D.rank - 2)) :
    P.realBasis.repr v j = g_R D (P.realBasis j : E_R D) (v : E_R D) := by
  classical
  let f : P.K_R →ₗ[ℝ] ℝ :=
    (B_R D (P.realBasis j : E_R D)).comp P.K_R.subtype
  have h := congrArg f (P.realBasis.sum_repr v)
  rw [map_sum] at h
  simp only [map_smul] at h
  change (∑ i, P.realBasis.repr v i *
    g_R D (P.realBasis j : E_R D) (P.realBasis i : E_R D)) =
      g_R D (P.realBasis j : E_R D) (v : E_R D) at h
  simpa only [P.realBasis_gram, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem realBasis_expansion (v : P.K_R) :
    ∑ j, g_R D (P.realBasis j : E_R D) (v : E_R D) • P.realBasis j = v := by
  simpa only [← P.realBasis_coeff] using P.realBasis.sum_repr v

/-- The proposed complex basis vectors have explicit original real coordinates. -/
def basisVector (j : Fin (D.rank - 2)) : P.complexFrame.K :=
  P.includeK (P.realBasis j)

@[simp] theorem basisVector_coe (j : Fin (D.rank - 2)) :
    (P.basisVector j : E D) = complexify D (P.realBasis j : E_R D) := rfl

theorem basisVector_gram (i j : Fin (D.rank - 2)) :
    g D (P.basisVector i : E D) (P.basisVector j : E D) =
      if i = j then 1 else 0 := by
  rw [basisVector_coe, basisVector_coe, complexify_gram, P.realBasis_gram]
  split_ifs <;> norm_num

/-- Real and imaginary spanning are proved separately, using the actual real
basis. This proves spanning in F.K without a dimension-only identification. -/
theorem complex_spanning (z : P.complexFrame.K) :
    ∑ j, g D (P.basisVector j : E D) (z : E D) • P.basisVector j = z := by
  apply Subtype.ext
  funext i
  apply Complex.ext
  · have h := congrArg (fun v : P.K_R => (v : E_R D) i)
      (P.realBasis_expansion (P.realK z))
    simp [basisVector, includeK, realK, realPart, Complex.mul_re, Complex.mul_im, smul_eq_mul]
    simpa [complexify, realK, realPart, smul_eq_mul] using h
  · have h := congrArg (fun v : P.K_R => (v : E_R D) i)
      (P.realBasis_expansion (P.imagK z))
    simp [basisVector, includeK, imagK, imagPart, Complex.mul_re, Complex.mul_im, smul_eq_mul]
    simpa [complexify, imagK, imagPart, smul_eq_mul] using h

/-- Coordinates are actual original Gram pairings, with a proved inverse. -/
def complexCoordinates : P.complexFrame.K ≃ₗ[ℂ] (Fin (D.rank - 2) → ℂ) where
  toFun z j := g D (P.basisVector j : E D) (z : E D)
  invFun c := ∑ j, c j • P.basisVector j
  left_inv z := P.complex_spanning z
  right_inv c := by
    funext j
    change (pairing D (P.basisVector j : E D))
      ((∑ k, c k • P.basisVector k : P.complexFrame.K) : E D) = c j
    have hcoe : ((∑ k, c k • P.basisVector k : P.complexFrame.K) : E D) =
        ∑ k, c k • (P.basisVector k : E D) := by simp
    rw [hcoe, map_sum]
    simp only [map_smul]
    change (∑ k, c k * g D (P.basisVector j : E D) (P.basisVector k : E D)) = c j
    simp only [P.basisVector_gram]
    simp
  map_add' z w := by ext j; simp [g_add_right]
  map_smul' c z := by ext j; simp [g_smul_right, smul_eq_mul]

/-- A complex basis derived from the real orthonormal basis, ready for the
existing completeBasis/coordinateEquiv/current-transport declarations. -/
def complexBasis : Module.Basis (Fin (D.rank - 2)) ℂ P.complexFrame.K :=
  Module.Basis.ofEquivFun P.complexCoordinates

theorem complexBasis_apply (j : Fin (D.rank - 2)) : P.complexBasis j = P.basisVector j := by
  classical
  change Module.Basis.ofEquivFun P.complexCoordinates j = _
  rw [Module.Basis.coe_ofEquivFun]
  change (∑ k, (Pi.single j (1 : ℂ) : Fin (D.rank - 2) → ℂ) k • P.basisVector k) = _
  simp [Pi.single_apply]

theorem complexBasis_gram (i j : Fin (D.rank - 2)) :
    g D (P.complexBasis i : E D) (P.complexBasis j : E D) =
      if i = j then 1 else 0 := by
  rw [P.complexBasis_apply, P.complexBasis_apply, P.basisVector_gram]

theorem complexBasis_real (j : Fin (D.rank - 2)) :
    (P.complexBasis j : E D) = complexify D (P.realBasis j : E_R D) := by
  rw [P.complexBasis_apply, P.basisVector_coe]

end PositivePlane

/-- Coordinatewise conjugation, not conjugation of the charge labels. -/
def conjugateVector {D : LatticeData} (z : E D) : E D := fun i => star (z i)

theorem complexify_conjugate (D : LatticeData) (v : E_R D) :
    conjugateVector (complexify D v) = complexify D v := by
  ext i
  simp [complexify, conjugateVector]

theorem conjugate_gram (D : LatticeData) (v w : E D) :
    star (g D v w) = g D (conjugateVector v) (conjugateVector w) := by
  simp [g, conjugateVector, mul_comm, mul_left_comm]

theorem hermitian_symmetry (D : LatticeData) (v w : E D) :
    star (g D (conjugateVector v) w) = g D (conjugateVector w) v := by
  rw [conjugate_gram, g_symm]
  have hv : conjugateVector (conjugateVector v) = v := by
    ext i
    simp [complexify, conjugateVector]
  rw [hv]

/-- The real and imaginary Gram expansions establish the relevant Hermitian
diagonal identity. There is no positivity assertion for complex bilinear g. -/
theorem hermitian_realPart (D : LatticeData) (z : E D) :
    (g D (conjugateVector z) z).re =
      Q_R D (realPart z) + Q_R D (imagPart z) := by
  have hterm (i j : Fin D.rank) :
      (star (z i) * (D.G i j : ℂ) * z j).re =
        (z i).re * (D.G i j : ℝ) * (z j).re +
        (z i).im * (D.G i j : ℝ) * (z j).im := by
    simp [Complex.mul_re, Complex.mul_im]
  simp only [g, conjugateVector, Complex.re_sum, hterm, Q_R_apply,
    g_R_apply, realPart, imagPart, Finset.sum_add_distrib]

theorem hermitian_imagPart (D : LatticeData) (z : E D) :
    (g D (conjugateVector z) z).im = 0 := by
  have h := congrArg Complex.im (hermitian_symmetry D z z)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

theorem hermitian_diagonal (D : LatticeData) (z : E D) :
    g D (conjugateVector z) z =
      ((Q_R D (realPart z) + Q_R D (imagPart z) : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa using hermitian_realPart D z
  · simpa using hermitian_imagPart D z

namespace PositivePlane

variable {D : LatticeData} (P : PositivePlane D)

theorem complexBasis_conjugation_fixed (j : Fin (D.rank - 2)) :
    conjugateVector (P.complexBasis j : E D) = (P.complexBasis j : E D) := by
  rw [P.complexBasis_real, complexify_conjugate]

theorem hermitian_positive (z : P.complexFrame.K) (hz : z ≠ 0) :
    0 < (g D (conjugateVector (z : E D)) (z : E D)).re := by
  rw [hermitian_diagonal]
  change 0 < Q_R D (realPart (z : E D)) + Q_R D (imagPart (z : E D))
  have hxnonneg : 0 ≤ Q_R D (realPart (z : E D)) :=
    P.positive_K_R.nonneg (P.realK z)
  have hynonneg : 0 ≤ Q_R D (imagPart (z : E D)) :=
    P.positive_K_R.nonneg (P.imagK z)
  by_cases hx : P.realK z = 0
  · have hy : P.imagK z ≠ 0 := by
      intro hy
      apply hz
      apply Subtype.ext
      simp only [Submodule.coe_zero]
      have hx' : realPart (z : E D) = 0 := congrArg Subtype.val hx
      have hy' : imagPart (z : E D) = 0 := congrArg Subtype.val hy
      have h := complexify_decomposition (z : E D)
      simpa only [hx', hy', map_zero, smul_zero, add_zero] using h.symm
    have hpos := P.positive_K_R (P.imagK z) hy
    change 0 < Q_R D (imagPart (z : E D)) at hpos
    linarith
  · have hpos := P.positive_K_R (P.realK z) hx
    change 0 < Q_R D (realPart (z : E D)) at hpos
    linarith

end PositivePlane

/-- Final scope: FOR EACH nonzero original integral p there exists a real
charge-detecting frame with positive rank-minus-two transverse geometry and
an actual conjugation-fixed orthonormal complex basis. Every geometric object
below is constructed, not supplied in the premises. -/
theorem exists_original_real_geometry (D : LatticeData) (hrank : 2 ≤ D.rank)
    (hneg : sigNeg (Q_R D) = 1) (hpos : sigPos (Q_R D) = D.rank - 1)
    (p : Charge D) (hp : p ≠ 0) :
    ∃ P : PositivePlane D,
      g_R D P.ePlus P.ePlus = 0 ∧
      g_R D P.eMinus P.eMinus = 0 ∧
      g_R D P.ePlus P.eMinus = 1 ∧
      g_R D P.ePlus (realCharge p) ≠ 0 ∧
      P.complexFrame.pPlus p ≠ 0 ∧
      P.projection (realCharge p) = 0 ∧
      P.complexFrame.projK (chargeVector p) = 0 ∧
      Module.finrank ℝ P.K_R = D.rank - 2 ∧
      Module.finrank ℂ P.complexFrame.K = D.rank - 2 ∧
      ((Q_R D).restrict P.K_R).PosDef ∧
      (∀ i j : Fin (D.rank - 2),
        g D (P.complexBasis i : E D) (P.complexBasis j : E D) =
          if i = j then 1 else 0) ∧
      (∀ j : Fin (D.rank - 2),
        conjugateVector (P.complexBasis j : E D) = (P.complexBasis j : E D)) ∧
      (∀ z : P.complexFrame.K, z ≠ 0 →
        0 < (g D (conjugateVector (z : E D)) (z : E D)).re) := by
  obtain ⟨P, a, c, hpdec, hdetect⟩ := exists_charge_plane D hrank hneg hpos p hp
  have hreal : g_R D P.ePlus (realCharge p) ≠ 0 := by
    rw [P.charge_pairing p a c hpdec]
    exact hdetect
  have hcomplex : P.complexFrame.pPlus p ≠ 0 := by
    change g D (complexify D P.ePlus) (chargeVector p) ≠ 0
    rw [← complexify_charge, complexify_gram]
    exact_mod_cast hreal
  exact ⟨P, P.plus_null, P.minus_null, P.plus_minus, hreal, hcomplex,
    P.projection_charge_zero p a c hpdec, P.complex_projection_charge_zero p a c hpdec,
    P.finrank_K_R, P.complexFrame.finrank_K, P.positive_K_R,
    P.complexBasis_gram, P.complexBasis_conjugation_fixed, P.hermitian_positive⟩

end D5.S3.VertexAlgebra.LatticeRealNullFrame
