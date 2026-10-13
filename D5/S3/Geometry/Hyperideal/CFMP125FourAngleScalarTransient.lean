import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Static candidate, not kernel checked. Scalar algebra for the native
four-coordinate specialization of the six-edge cosine formula. -/

set_option autoImplicit false
noncomputable section
namespace FourAngleScalar

@[ext] structure Quad where
  r : ℝ
  o : ℝ
  a : ℝ
  b : ℝ

def d (z : Quad) : ℝ := z.r^2 + z.a^2 + z.b^2 + 2*z.r*z.a*z.b - 1
def e (z : Quad) : ℝ := z.o^2 + z.a^2 + z.b^2 + 2*z.o*z.a*z.b - 1
def Nr (z : Quad) : ℝ := 2*z.a*z.b + z.r*(z.a^2+z.b^2) - (z.r^2-1)*z.o
def No (z : Quad) : ℝ := 2*z.a*z.b + z.o*(z.a^2+z.b^2) - (z.o^2-1)*z.r
def Na (z : Quad) : ℝ := z.b*(z.r+z.o) + z.a*(z.r*z.o+z.b^2-z.a^2+1)
def Nb (z : Quad) : ℝ := z.a*(z.r+z.o) + z.b*(z.r*z.o+z.a^2-z.b^2+1)
def L (z : Quad) : ℝ := (z.a+z.b)^2 - (z.r-1)*(z.o-1)
def M (z : Quad) : ℝ := (z.r+1)*(z.o+1) - (z.a-z.b)^2
def K (z : Quad) : ℝ := L z * M z

private def W (z : Quad) (s : ℝ) : Quad :=
  ⟨Nr z / d z, No z / e z, Na z / s, Nb z / s⟩
def T (z : Quad) : Quad :=
  ⟨Nr z / d z, No z / e z,
    Na z / Real.sqrt (d z * e z), Nb z / Real.sqrt (d z * e z)⟩

private theorem d_add (z : Quad) : d z + Nr z = (z.r+1)*L z := by
  dsimp [d, Nr, L]; ring
private theorem d_sub (z : Quad) : d z - Nr z = (z.r-1)*M z := by
  dsimp [d, Nr, M]; ring
private theorem e_add (z : Quad) : e z + No z = (z.o+1)*L z := by
  dsimp [e, No, L]; ring
private theorem e_sub (z : Quad) : e z - No z = (z.o-1)*M z := by
  dsimp [e, No, M]; ring
private theorem n_add (z : Quad) : Na z + Nb z = (z.a+z.b)*M z := by
  dsimp [Na, Nb, M]; ring
private theorem n_sub (z : Quad) : Na z - Nb z = -(z.a-z.b)*L z := by
  dsimp [Na, Nb, L]; ring

private theorem w_relations (z : Quad) (s : ℝ) (hd : d z ≠ 0) (he : e z ≠ 0) :
    (W z s).r + 1 = (z.r+1)*L z / d z ∧
    (W z s).r - 1 = (1-z.r)*M z / d z ∧
    (W z s).o + 1 = (z.o+1)*L z / e z ∧
    (W z s).o - 1 = (1-z.o)*M z / e z ∧
    (W z s).a + (W z s).b = (z.a+z.b)*M z / s ∧
    (W z s).a - (W z s).b = -(z.a-z.b)*L z / s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [W]
    calc
      Nr z / d z + 1 = (d z + Nr z) / d z := by
        rw [add_div, div_self hd]; ring
      _ = _ := by rw [d_add]
  · dsimp [W]
    calc
      Nr z / d z - 1 = (Nr z - d z) / d z := by rw [sub_div, div_self hd]
      _ = _ := by
        congr 1
        nlinarith only [d_sub z]
  · dsimp [W]
    calc
      No z / e z + 1 = (e z + No z) / e z := by
        rw [add_div, div_self he]; ring
      _ = _ := by rw [e_add]
  · dsimp [W]
    calc
      No z / e z - 1 = (No z - e z) / e z := by rw [sub_div, div_self he]
      _ = _ := by
        congr 1
        nlinarith only [e_sub z]
  · dsimp [W]
    rw [← add_div, n_add]
  · dsimp [W]
    rw [← sub_div, n_sub]

private theorem lm_transform (z : Quad) (s : ℝ)
    (hd : d z ≠ 0) (he : e z ≠ 0) (hs2 : s^2 = d z * e z) :
    L (W z s) = L z * M z^2 / (d z * e z) ∧
    M (W z s) = L z^2 * M z / (d z * e z) := by
  obtain ⟨hrp, hrm, hop, hom, hap, ham⟩ := w_relations z s hd he
  constructor
  · change ((W z s).a + (W z s).b)^2 -
      ((W z s).r-1)*((W z s).o-1) = _
    rw [hap, hrm, hom, div_pow, hs2]
    field_simp [hd, he] <;> dsimp [L] <;> ring
  · change ((W z s).r+1)*((W z s).o+1) -
      ((W z s).a-(W z s).b)^2 = _
    rw [hrp, hop, ham, div_pow, hs2]
    field_simp [hd, he] <;> dsimp [M] <;> ring

/-- The second-pass data are recovered from the same six sum/difference laws.
The transverse factor is positive even when the input coordinates a,b are negative. -/
private theorem second_data (z : Quad) (s : ℝ)
    (hd : d z ≠ 0) (he : e z ≠ 0) (hs : s ≠ 0) (hs2 : s^2 = d z * e z) :
    d (W z s) = K z^2 / (d z^2 * e z) ∧
    e (W z s) = K z^2 / (d z * e z^2) ∧
    Nr (W z s) = z.r * (K z^2 / (d z^2 * e z)) ∧
    No (W z s) = z.o * (K z^2 / (d z * e z^2)) ∧
    Na (W z s) = z.a * (K z^2 / (d z * e z * s)) ∧
    Nb (W z s) = z.b * (K z^2 / (d z * e z * s)) := by
  obtain ⟨hrp, hrm, hop, hom, hap, ham⟩ := w_relations z s hd he
  obtain ⟨hl, hm⟩ := lm_transform z s hd he hs2
  have h1 : d (W z s) + Nr (W z s) =
      (z.r+1) * (K z^2 / (d z^2 * e z)) := by
    rw [d_add, hrp, hl]
    dsimp [K]
    field_simp [hd, he] <;> ring
  have h2 : d (W z s) - Nr (W z s) =
      (1-z.r) * (K z^2 / (d z^2 * e z)) := by
    rw [d_sub, hrm, hm]
    dsimp [K]
    field_simp [hd, he] <;> ring
  have h3 : e (W z s) + No (W z s) =
      (z.o+1) * (K z^2 / (d z * e z^2)) := by
    rw [e_add, hop, hl]
    dsimp [K]
    field_simp [hd, he] <;> ring
  have h4 : e (W z s) - No (W z s) =
      (1-z.o) * (K z^2 / (d z * e z^2)) := by
    rw [e_sub, hom, hm]
    dsimp [K]
    field_simp [hd, he] <;> ring
  have h5 : Na (W z s) + Nb (W z s) =
      (z.a+z.b) * (K z^2 / (d z * e z * s)) := by
    rw [n_add, hap, hm]
    dsimp [K]
    field_simp [hd, he, hs] <;> ring
  have h6 : Na (W z s) - Nb (W z s) =
      (z.a-z.b) * (K z^2 / (d z * e z * s)) := by
    rw [n_sub, ham, hl]
    dsimp [K]
    field_simp [hd, he, hs] <;> ring
  exact ⟨by nlinarith only [h1,h2], by nlinarith only [h3,h4],
    by nlinarith only [h1,h2], by nlinarith only [h3,h4],
    by nlinarith only [h5,h6], by nlinarith only [h5,h6]⟩

/-- Scalar involution, with an explicit positive square-root branch. -/
theorem transform_involution (z : Quad) (hd : 0 < d z) (he : 0 < e z)
    (hk : K z ≠ 0) : 0 < d (T z) ∧ 0 < e (T z) ∧ T (T z) = z := by
  let s := Real.sqrt (d z * e z)
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos hd he)
  have hs2 : s^2 = d z * e z := Real.sq_sqrt (mul_pos hd he).le
  obtain ⟨hD,hE,hN,hO,hA,hB⟩ := second_data z s hd.ne' he.ne' hs.ne' hs2
  change d (T z) = _ at hD
  change e (T z) = _ at hE
  change Nr (T z) = _ at hN
  change No (T z) = _ at hO
  change Na (T z) = _ at hA
  change Nb (T z) = _ at hB
  have hk2 : 0 < K z^2 := sq_pos_of_ne_zero hk
  have hdp : 0 < d (T z) := by rw [hD]; positivity
  have hep : 0 < e (T z) := by rw [hE]; positivity
  have hp : 0 < K z^2 / (d z * e z * s) := by positivity
  have hroot : Real.sqrt (d (T z) * e (T z)) = K z^2 / (d z * e z * s) := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_pos hdp hep).le hp.le).2
    rw [hD, hE]
    simp only [div_pow, mul_pow, hs2]
    field_simp [hd.ne', he.ne'] <;> ring
  refine ⟨hdp, hep, ?_⟩
  apply Quad.ext
  · change Nr (T z) / d (T z) = z.r
    rw [hN, ← hD]
    exact mul_div_cancel_right₀ _ hdp.ne'
  · change No (T z) / e (T z) = z.o
    rw [hO, ← hE]
    exact mul_div_cancel_right₀ _ hep.ne'
  · change Na (T z) / Real.sqrt (d (T z) * e (T z)) = z.a
    rw [hA, hroot]
    exact mul_div_cancel_right₀ _ hp.ne'
  · change Nb (T z) / Real.sqrt (d (T z) * e (T z)) = z.b
    rw [hB, hroot]
    exact mul_div_cancel_right₀ _ hp.ne'

/-- Algebraic producer for the positive branch. The trigonometric consumer
supplies every premise from B4; no sign premise survives into the native theorem. -/
theorem positive_branch (z : Quad) (p : ℝ)
    (hp : 0 < p) (hp2 : p^2 = (1-z.a^2)*(1-z.b^2))
    (hx : p < z.r+z.a*z.b) (hy : p < z.o+z.a*z.b)
    (hr : z.r < 1) (ho : -1 < z.o ∧ z.o < 1)
    (ht : -1 < p-z.a*z.b ∧ p-z.a*z.b < 1)
    (ha : 0 < 1-z.a^2) (hb : 0 < 1-z.b^2)
    (hba : 0 < z.b+z.a*z.o) (hab : 0 < z.a+z.b*z.o) :
    0 < d z ∧ 0 < e z ∧ 0 < K z ∧
    1 < (T z).r ∧ 1 < (T z).o ∧ 1 < (T z).a ∧ 1 < (T z).b := by
  have hdid : d z = (z.r+z.a*z.b-p)*(z.r+z.a*z.b+p) := by
    dsimp [d]
    nlinarith only [hp2]
  have heid : e z = (z.o+z.a*z.b-p)*(z.o+z.a*z.b+p) := by
    dsimp [e]
    nlinarith only [hp2]
  have hd : 0 < d z := by rw [hdid]; exact mul_pos (by linarith) (by linarith)
  have he : 0 < e z := by rw [heid]; exact mul_pos (by linarith) (by linarith)
  have hLid : L z = (z.r-(p-z.a*z.b))*(1-z.o) +
      (z.o-(p-z.a*z.b)+2*p)*(1-(p-z.a*z.b)) := by
    dsimp [L]
    nlinarith only [hp2]
  have hMid : M z = (z.r-(p-z.a*z.b))*(1+z.o) +
      (z.o-(p-z.a*z.b)+2*p)*(1+(p-z.a*z.b)) := by
    dsimp [M]
    nlinarith only [hp2]
  have hL : 0 < L z := by
    rw [hLid]
    exact add_pos (mul_pos (by linarith) (by linarith [ho.2]))
      (mul_pos (by linarith) (by linarith [ht.2]))
  have hM : 0 < M z := by
    rw [hMid]
    exact add_pos (mul_pos (by linarith) (by linarith [ho.1]))
      (mul_pos (by linarith) (by linarith [ht.1]))
  have hA : 0 < Na z := by
    have hid : Na z = (z.r+z.a*z.b)*(z.b+z.a*z.o) +
        (1-z.a^2)*(z.a+z.b*z.o) := by dsimp [Na]; ring
    rw [hid]
    exact add_pos (mul_pos (by linarith) hba) (mul_pos ha hab)
  have hB : 0 < Nb z := by
    have hid : Nb z = (z.r+z.a*z.b)*(z.a+z.b*z.o) +
        (1-z.b^2)*(z.b+z.a*z.o) := by dsimp [Nb]; ring
    rw [hid]
    exact add_pos (mul_pos (by linarith) hab) (mul_pos hb hba)
  have hAsq : Na z^2 - d z*e z = (1-z.a^2)*L z*M z := by
    dsimp [Na, d, e, L, M]; ring
  have hBsq : Nb z^2 - d z*e z = (1-z.b^2)*L z*M z := by
    dsimp [Nb, d, e, L, M]; ring
  have hs : 0 < Real.sqrt (d z*e z) := Real.sqrt_pos.2 (mul_pos hd he)
  have hs2 := Real.sq_sqrt (mul_pos hd he).le
  have has : Real.sqrt (d z*e z) < Na z := by
    by_contra h
    have hprod : 0 ≤ (Real.sqrt (d z*e z) - Na z) *
        (Real.sqrt (d z*e z) + Na z) :=
      mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) (by linarith only [hs,hA])
    nlinarith only [hAsq,hs2,hprod,mul_pos (mul_pos ha hL) hM]
  have hbs : Real.sqrt (d z*e z) < Nb z := by
    by_contra h
    have hprod : 0 ≤ (Real.sqrt (d z*e z) - Nb z) *
        (Real.sqrt (d z*e z) + Nb z) :=
      mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) (by linarith only [hs,hB])
    nlinarith only [hBsq,hs2,hprod,mul_pos (mul_pos hb hL) hM]
  refine ⟨hd, he, mul_pos hL hM, ?_, ?_, ?_, ?_⟩
  · change 1 < Nr z / d z
    apply (lt_div_iff₀ hd).2
    have h := d_sub z
    nlinarith only [h,mul_pos (sub_pos.mpr hr) hM]
  · change 1 < No z / e z
    apply (lt_div_iff₀ he).2
    have h := e_sub z
    nlinarith only [h,mul_pos (sub_pos.mpr ho.2) hM]
  · change 1 < Na z / Real.sqrt (d z*e z)
    exact (lt_div_iff₀ hs).2 (by simpa using has)
  · change 1 < Nb z / Real.sqrt (d z*e z)
    exact (lt_div_iff₀ hs).2 (by simpa using hbs)

end FourAngleScalar
