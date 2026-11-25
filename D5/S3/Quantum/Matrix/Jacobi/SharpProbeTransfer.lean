/- GID: D5/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Jacobi/SharpProbeTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Quantum.Matrix.JacobiEndpointResolvent]
   utility: none
   digest: Opposite-half-plane Green probes detect changes on the initial Jacobi component. -/

import D5.S3.Quantum.Matrix.JacobiEndpointResolvent
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp full-column probe count for Hermitian nearest-neighbor perturbations

Two full endpoint Green columns at probes in opposite half-planes detect
the action of a bandwidth-one Hermitian perturbation on the initial component.
The transfer includes the first zero bond. For every prescribed nonreal probe,
a two-site rank-one perturbation shows that one column can miss a change.
-/

noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer

open JacobiEndpointResolvent

variable {n : ℕ}

/-- The sites in the initial Jacobi component, up to and including the site
immediately before the first zero bond. -/
def EndpointConnected (H : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Prop :=
  ∀ p < j, bond H p ≠ 0

private theorem EndpointConnected.of_le {H : Matrix (Fin n) (Fin n) ℂ}
    {i j : Fin n} (hj : EndpointConnected H j) (hij : i ≤ j) :
    EndpointConnected H i :=
  fun p hp => hj p (lt_of_lt_of_le hp hij)

section NonrealShift

variable {ι : Type*} [Fintype ι]

private theorem sum_normSq_pos {x : ι → ℂ} (hx : x ≠ 0) :
    0 < ∑ j, Complex.normSq (x j) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
    (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x k)) (Finset.mem_univ j))

private theorem star_dot_self (x : ι → ℂ) :
    star x ⬝ᵥ x = ((∑ j, Complex.normSq (x j) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]

variable [DecidableEq ι]

private theorem shift_quadratic_im {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (z : ℂ) (x : ι → ℂ) :
    (star x ⬝ᵥ ((z • (1 : Matrix ι ι ℂ) - H) *ᵥ x)).im =
      z.im * ∑ j, Complex.normSq (x j) := by
  have hreal : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
    have h := congrArg Complex.im (hH.star_dotProduct_mulVec_comm x x)
    rw [Complex.star_def, Complex.conj_im] at h
    linarith only [h]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, star_dot_self, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, hreal, mul_zero, zero_add, sub_zero]

private theorem shift_det_isUnit {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) : IsUnit (z • (1 : Matrix ι ι ℂ) - H).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hne
  have hzero : (z • (1 : Matrix ι ι ℂ) - H) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h := shift_quadratic_im hH z (x - y)
  rw [hzero, dotProduct_zero, Complex.zero_im] at h
  exact mul_ne_zero hz (sum_normSq_pos (sub_ne_zero.mpr hne)).ne' h.symm

private theorem inverse_col_equation (A : Matrix ι ι ℂ) (hA : IsUnit A.det) (i : ι) :
    A *ᵥ (A⁻¹).col i = Pi.single i 1 := by
  rw [← Matrix.col_mul_eq_mulVec_col, Matrix.mul_nonsing_inv A hA,
    ← Matrix.one_mulVec (Pi.single i (1 : ℂ)), Matrix.mulVec_single_one]

private theorem inv_diagonal_im {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : ι) :
    ∃ q : ℝ, 0 < q ∧ (((z • (1 : Matrix ι ι ℂ) - H)⁻¹) i i).im = -(z.im * q) := by
  let A := z • (1 : Matrix ι ι ℂ) - H
  let u := (A⁻¹).col i
  have hu : A *ᵥ u = Pi.single i 1 := inverse_col_equation A (shift_det_isUnit hH hz) i
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hu
    exact zero_ne_one (by simpa only [Pi.zero_apply, Pi.single_eq_same] using congrFun hu i)
  have him := shift_quadratic_im hH z u
  change (star u ⬝ᵥ (A *ᵥ u)).im = _ at him
  rw [hu, dotProduct_single_one, Pi.star_apply, Complex.star_def, Complex.conj_im] at him
  refine ⟨∑ j, Complex.normSq (u j), sum_normSq_pos hu_ne, ?_⟩
  change (u i).im = _
  linarith only [him]

end NonrealShift

private theorem tail_shift (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (i : Fin n) :
    tail (spectralShift H z) i = z • (1 : Matrix (Tail i) (Tail i) ℂ) - tail H i := by
  let includeTail : Tail i → Fin n := Subtype.val
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix includeTail includeTail = 1 :=
    Matrix.submatrix_one includeTail Subtype.val_injective
  change z • (1 : Matrix (Fin n) (Fin n) ℂ).submatrix includeTail includeTail -
    tail H i = _
  rw [hone]

private theorem tail_det_isUnit {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : Fin n) : IsUnit (tail (spectralShift H z) i).det := by
  rw [tail_shift]
  exact shift_det_isUnit (hH.submatrix Subtype.val) hz

private theorem tail_diagonal_im {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : Fin n) :
    ∃ q : ℝ, 0 < q ∧ (tailDiagonal (spectralShift H z) i).im = -(z.im * q) := by
  unfold tailDiagonal
  rw [tail_shift]
  exact inv_diagonal_im (hH.submatrix Subtype.val) hz (tailFirst i)

section Columns

variable [NeZero n]

private theorem column_eq_zero_iff {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (htri : IsTridiagonal H) {z : ℂ} (hz : z.im ≠ 0) (j : Fin n) :
    firstColumn (spectralShift H z) j = 0 ↔ ¬ EndpointConnected H j := by
  classical
  rw [firstColumn_eq_zero_iff H z htri (tail_det_isUnit hH hz) j]
  constructor
  · rintro ⟨p, hp, hb⟩ hconnected
    exact hconnected p hp hb
  · intro hnot
    by_contra hprefix
    apply hnot
    intro p hp hb
    exact hprefix ⟨p, hp, hb⟩

/-- The two-node Vandermonde determinant of the actual adjacent Green coordinates.
Its factorization holds even at a zero bond. -/
theorem adjacent_green_minor (H : Matrix (Fin n) (Fin n) ℂ) (z₀ z₁ : ℂ)
    (htri : IsTridiagonal H)
    (hinv₀ : ∀ j, IsUnit (tail (spectralShift H z₀) j).det)
    (hinv₁ : ∀ j, IsUnit (tail (spectralShift H z₁) j).det)
    (p i : Fin n) (hpi : p.val + 1 = i.val) :
    firstColumn (spectralShift H z₀) p * firstColumn (spectralShift H z₁) i -
        firstColumn (spectralShift H z₁) p * firstColumn (spectralShift H z₀) i =
      (firstColumn (spectralShift H z₀) p * firstColumn (spectralShift H z₁) p) *
        bond H p * (tailDiagonal (spectralShift H z₁) i - tailDiagonal (spectralShift H z₀) i) := by
  rw [firstColumn_step H z₀ htri hinv₀ p i hpi, firstColumn_step H z₁ htri hinv₁ p i hpi]
  ring

private theorem adjacent_coefficients_eq_zero {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (htri : IsTridiagonal H) {z₀ z₁ : ℂ}
    (hz₀ : 0 < z₀.im) (hz₁ : z₁.im < 0) {p i : Fin n} (hpi : p.val + 1 = i.val)
    (hi : EndpointConnected H i) {a b : ℂ}
    (e₀ : a * firstColumn (spectralShift H z₀) p + b * firstColumn (spectralShift H z₀) i = 0)
    (e₁ : a * firstColumn (spectralShift H z₁) p + b * firstColumn (spectralShift H z₁) i = 0) :
    a = 0 ∧ b = 0 := by
  let g₀ := firstColumn (spectralShift H z₀)
  let g₁ := firstColumn (spectralShift H z₁)
  change a * g₀ p + b * g₀ i = 0 at e₀
  change a * g₁ p + b * g₁ i = 0 at e₁
  have hpi_lt : p < i := by
    change p.val < i.val
    omega
  have hg₀p : g₀ p ≠ 0 := fun h =>
    (column_eq_zero_iff hH htri hz₀.ne' p).mp h (hi.of_le hpi_lt.le)
  have hg₁p : g₁ p ≠ 0 := fun h =>
    (column_eq_zero_iff hH htri hz₁.ne p).mp h (hi.of_le hpi_lt.le)
  have hg₀i : g₀ i ≠ 0 := fun h => (column_eq_zero_iff hH htri hz₀.ne' i).mp h hi
  obtain ⟨q₀, hq₀, hm₀⟩ := tail_diagonal_im hH hz₀.ne' i
  obtain ⟨q₁, hq₁, hm₁⟩ := tail_diagonal_im hH hz₁.ne i
  have hm : tailDiagonal (spectralShift H z₁) i ≠ tailDiagonal (spectralShift H z₀) i := by
    intro h
    have he := congrArg Complex.im h
    change (tailDiagonal (spectralShift H z₁) i).im =
      (tailDiagonal (spectralShift H z₀) i).im at he
    rw [hm₁, hm₀] at he
    exact (ne_of_gt (lt_trans (neg_neg_of_pos (mul_pos hz₀ hq₀))
      (neg_pos.mpr (mul_neg_of_neg_of_pos hz₁ hq₁)))) he
  have hdet : g₀ p * g₁ i - g₁ p * g₀ i ≠ 0 := by
    change firstColumn (spectralShift H z₀) p * firstColumn (spectralShift H z₁) i -
      firstColumn (spectralShift H z₁) p * firstColumn (spectralShift H z₀) i ≠ 0
    rw [adjacent_green_minor H z₀ z₁ htri (tail_det_isUnit hH hz₀.ne')
      (tail_det_isUnit hH hz₁.ne) p i hpi]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hg₀p hg₁p) (hi p hpi_lt)) (sub_ne_zero.mpr hm)
  have ha_det : a * (g₀ p * g₁ i - g₁ p * g₀ i) = 0 := by
    calc
      _ = (a * g₀ p + b * g₀ i) * g₁ i - (a * g₁ p + b * g₁ i) * g₀ i := by ring
      _ = 0 := by rw [e₀, e₁, zero_mul, zero_mul, sub_self]
  have ha := (mul_eq_zero.mp ha_det).resolve_right hdet
  rw [ha, zero_mul, zero_add] at e₀
  exact ⟨ha, (mul_eq_zero.mp e₀).resolve_right hg₀i⟩

private theorem firstColumn_eq_iff_mulVec (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hinv₀ : IsUnit (spectralShift H₀ z).det) (hinv₁ : IsUnit (spectralShift H₁ z).det) :
    firstColumn (spectralShift H₁ z) = firstColumn (spectralShift H₀ z) ↔
      (H₁ - H₀) *ᵥ firstColumn (spectralShift H₀ z) = 0 := by
  let A₀ := spectralShift H₀ z
  let A₁ := spectralShift H₁ z
  let g₀ := firstColumn A₀
  let g₁ := firstColumn A₁
  have hshift : A₀ - A₁ = H₁ - H₀ := by
    change (z • (1 : Matrix (Fin n) (Fin n) ℂ) - H₀) -
      (z • (1 : Matrix (Fin n) (Fin n) ℂ) - H₁) = _
    abel
  have hu₀ : A₀ *ᵥ g₀ = Pi.single (0 : Fin n) 1 := inverse_col_equation A₀ hinv₀ 0
  have hu₁ : A₁ *ᵥ g₁ = Pi.single (0 : Fin n) 1 := inverse_col_equation A₁ hinv₁ 0
  have hres : (H₁ - H₀) *ᵥ g₀ = A₁ *ᵥ (g₁ - g₀) := by
    rw [← hshift, Matrix.sub_mulVec, Matrix.mulVec_sub, hu₀, hu₁]
  change g₁ = g₀ ↔ (H₁ - H₀) *ᵥ g₀ = 0
  rw [hres]
  constructor
  · intro h
    rw [h, sub_self, Matrix.mulVec_zero]
  · intro h
    have hinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A₁).mpr hinv₁)
    exact sub_eq_zero.mp (hinj (h.trans (Matrix.mulVec_zero A₁).symm))

omit [NeZero n] in
private theorem row_mulVec_single (V : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ)
    (r j : Fin n) (h : ∀ k ≠ j, V r k * g k = 0) :
    (V *ᵥ g) r = V r j * g j := by
  rw [Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun k _ hk => h k hk)

omit [NeZero n] in
private theorem row_mulVec_pair (V : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ)
    (r j k : Fin n) (hjk : j ≠ k) (h : ∀ l ≠ j, l ≠ k → V r l * g l = 0) :
    (V *ᵥ g) r = V r j * g j + V r k * g k := by
  rw [Matrix.mulVec_apply_eq_sum]
  calc
    _ = ∑ l ∈ ({j, k} : Finset (Fin n)), V r l * g l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact h l hl.1 hl.2
    _ = _ := by simp [Finset.sum_insert, hjk]

private theorem mulVec_zero_of_prefix_columns {H V : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (htri : IsTridiagonal H) {z : ℂ} (hz : z.im ≠ 0)
    (hcol : ∀ j, EndpointConnected H j → V.col j = 0) :
    V *ᵥ firstColumn (spectralShift H z) = 0 := by
  classical
  funext r
  rw [Matrix.mulVec_apply_eq_sum, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : EndpointConnected H j
  · have h := congrFun (hcol j hj) r
    change V r j = 0 at h
    rw [h, zero_mul]
  · rw [(column_eq_zero_iff hH htri hz j).mpr hj, mul_zero]

/-- Two full endpoint resolvent columns, sampled in opposite half-planes, agree
exactly when the perturbation annihilates the reference's initial component.
The perturbation has bandwidth at most one. Within the component the proof uses
Hermiticity and the adjacent Vandermonde minor. The first disconnected row has
one accessible site, and all later disconnected rows have none. -/
theorem two_probe_eq_iff (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (htri : IsTridiagonal H₀) (hband : IsTridiagonal (H₁ - H₀))
    {z₀ z₁ : ℂ} (hz₀ : 0 < z₀.im) (hz₁ : z₁.im < 0) :
    (firstColumn (spectralShift H₁ z₀) = firstColumn (spectralShift H₀ z₀) ∧
      firstColumn (spectralShift H₁ z₁) = firstColumn (spectralShift H₀ z₁)) ↔
      ∀ j, EndpointConnected H₀ j → (H₁ - H₀).col j = 0 := by
  classical
  let V := H₁ - H₀
  change IsTridiagonal V at hband
  let g₀ := firstColumn (spectralShift H₀ z₀)
  let g₁ := firstColumn (spectralShift H₀ z₁)
  have hV : V.IsHermitian := hH₁.sub hH₀
  have hres {z : ℂ} (hz : z.im ≠ 0) :=
    firstColumn_eq_iff_mulVec H₀ H₁ z (shift_det_isUnit hH₀ hz) (shift_det_isUnit hH₁ hz)
  rw [hres hz₀.ne', hres hz₁.ne]
  change (V *ᵥ g₀ = 0 ∧ V *ᵥ g₁ = 0) ↔ ∀ j, EndpointConnected H₀ j → V.col j = 0
  refine ⟨?_, fun h => ⟨mulVec_zero_of_prefix_columns hH₀ htri hz₀.ne' h,
    mulVec_zero_of_prefix_columns hH₀ htri hz₁.ne h⟩⟩
  rintro ⟨he₀, he₁⟩
  suffices h : ∀ (m : ℕ) (j : Fin n), j.val = m → EndpointConnected H₀ j → ∀ r, V r j = 0 by
    intro j hj
    exact funext (h j.val j rfl hj)
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro j hjm hj
    have earlier (k : Fin n) (hk : k.val < j.val) : V j k = 0 := by
      have hkj : k ≤ j := le_of_lt (show k < j from hk)
      have hkm : k.val < m := by simpa only [← hjm] using hk
      exact ih k.val hkm k rfl (hj.of_le hkj) j
    have row_outside_pair (k : Fin n) (hkj : k ≠ j) (hk : k.val ≠ j.val + 1) : V j k = 0 := by
      by_cases hlt : k.val < j.val
      · exact earlier k hlt
      · have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        exact hband j k (Or.inl (by omega))
    have singleton (r : Fin n) (hs : ∀ l ≠ j, V r l * g₀ l = 0) : V r j = 0 := by
      have hrow := congrFun he₀ r
      rw [row_mulVec_single V g₀ r j hs, Pi.zero_apply] at hrow
      exact (mul_eq_zero.mp hrow).resolve_right
        (fun h => (column_eq_zero_iff hH₀ htri hz₀.ne' j).mp h hj)
    have finish (hdiag : V j j = 0) (hsucc : ∀ r, r.val = j.val + 1 → V r j = 0)
        (r : Fin n) : V r j = 0 := by
      rcases lt_trichotomy r.val j.val with hr | hr | hr
      · rw [← hV.apply r j, earlier r hr, star_zero]
      · simpa only [Fin.ext hr] using hdiag
      · by_cases hrs : r.val = j.val + 1
        · exact hsucc r hrs
        · exact hband r j (Or.inr (by omega))
    by_cases hnext : j.val + 1 < n
    · let k : Fin n := ⟨j.val + 1, hnext⟩
      have hkval : k.val = j.val + 1 := rfl
      have hjk : j ≠ k := by
        intro h
        have hval := congrArg Fin.val h
        omega
      have hsupp (l : Fin n) (hlj : l ≠ j) (hlk : l ≠ k) : V j l = 0 :=
        row_outside_pair l hlj (fun h => hlk (Fin.ext (h.trans hkval.symm)))
      by_cases hk : EndpointConnected H₀ k
      · have e₀ : V j j * g₀ j + V j k * g₀ k = 0 := by
          rw [← row_mulVec_pair V g₀ j j k hjk
            (fun l hlj hlk => by rw [hsupp l hlj hlk, zero_mul])]
          exact congrFun he₀ j
        have e₁ : V j j * g₁ j + V j k * g₁ k = 0 := by
          rw [← row_mulVec_pair V g₁ j j k hjk
            (fun l hlj hlk => by rw [hsupp l hlj hlk, zero_mul])]
          exact congrFun he₁ j
        obtain ⟨hdiag, hupper⟩ := adjacent_coefficients_eq_zero hH₀ htri hz₀ hz₁
          (p := j) (i := k) hkval.symm hk e₀ e₁
        apply finish hdiag
        intro r hr
        have hrk : r = k := Fin.ext (hr.trans hkval.symm)
        rw [hrk, ← hV.apply k j, hupper, star_zero]
      · have hkzero : g₀ k = 0 := (column_eq_zero_iff hH₀ htri hz₀.ne' k).mpr hk
        have hdiag : V j j = 0 := by
          apply singleton j
          intro l hlj
          by_cases hlk : l = k
          · rw [hlk, hkzero, mul_zero]
          · rw [hsupp l hlj hlk, zero_mul]
        have hboundary : V k j = 0 := by
          apply singleton k
          intro l hlj
          by_cases hlt : l.val < j.val
          · rw [hband k l (Or.inr (by omega)), zero_mul]
          · have hne : l.val ≠ j.val := fun h => hlj (Fin.ext h)
            have hkl : k ≤ l := by
              change k.val ≤ l.val
              omega
            have hl : ¬ EndpointConnected H₀ l := fun h => hk (h.of_le hkl)
            have hgl : g₀ l = 0 := (column_eq_zero_iff hH₀ htri hz₀.ne' l).mpr hl
            rw [hgl, mul_zero]
        apply finish hdiag
        intro r hr
        rwa [show r = k from Fin.ext (hr.trans hkval.symm)]
    · have hdiag : V j j = 0 := by
        apply singleton j
        intro l hlj
        have hne : l.val ≠ j.val + 1 := fun h => hnext (h ▸ l.isLt)
        rw [row_outside_pair l hlj hne, zero_mul]
      exact finish hdiag (fun r hr => (hnext (hr ▸ r.isLt)).elim)

/-- Agreement at the two probes propagates to the full endpoint column at
every nonreal spectral parameter. -/
theorem firstColumn_eq_of_two_probes (H₀ H₁ : Matrix (Fin n) (Fin n) ℂ)
    (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (htri : IsTridiagonal H₀) (hband : IsTridiagonal (H₁ - H₀))
    {z₀ z₁ z : ℂ} (hz₀ : 0 < z₀.im) (hz₁ : z₁.im < 0) (hz : z.im ≠ 0)
    (e₀ : firstColumn (spectralShift H₁ z₀) = firstColumn (spectralShift H₀ z₀))
    (e₁ : firstColumn (spectralShift H₁ z₁) = firstColumn (spectralShift H₀ z₁)) :
    firstColumn (spectralShift H₁ z) = firstColumn (spectralShift H₀ z) := by
  have hcol := (two_probe_eq_iff H₀ H₁ hH₀ hH₁ htri hband hz₀ hz₁).mp ⟨e₀, e₁⟩
  exact (firstColumn_eq_iff_mulVec H₀ H₁ z (shift_det_isUnit hH₀ hz)
    (shift_det_isUnit hH₁ hz)).mpr (mulVec_zero_of_prefix_columns hH₀ htri hz hcol)

end Columns

/-- A two-site Jacobi reference with real lower bond `b`. -/
def twoSiteReference (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (b : ℂ); (b : ℂ), 0]

/-- The scalar multiple of the outer product built from `(b, -conj z)`. -/
def twoSitePerturbation (b ε : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let x : Fin 2 → ℂ := ![(b : ℂ), -star z]
  (ε : ℂ) • Matrix.vecMulVec x (star x)

/-- Every prescribed nonreal single probe has a connected two-site Hermitian
adversary. The bond and the positive perturbation scale can both be chosen
arbitrarily small. The perturbation already acts nontrivially on site zero. -/
theorem one_probe_two_site_adversary {b ε : ℝ} (hb : b ≠ 0) (hε : 0 < ε)
    {z : ℂ} (hz : z.im ≠ 0) :
    let H₀ := twoSiteReference b
    let V := twoSitePerturbation b ε z
    let H₁ := H₀ + V
    H₀.IsHermitian ∧ H₁.IsHermitian ∧ IsTridiagonal H₀ ∧ IsTridiagonal V ∧
      (∀ j, EndpointConnected H₀ j) ∧
      firstColumn (spectralShift H₁ z) = firstColumn (spectralShift H₀ z) ∧ V 0 0 ≠ 0 := by
  intro H₀ V H₁
  have hH₀ : H₀.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [H₀, twoSiteReference, Complex.star_def]
  let x : Fin 2 → ℂ := ![(b : ℂ), -star z]
  have houter : (Matrix.vecMulVec x (star x)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul, star_star]
  have hεstar : IsSelfAdjoint (ε : ℂ) := by
    change star (ε : ℂ) = (ε : ℂ)
    simp [Complex.star_def]
  have hV : V.IsHermitian := houter.smul hεstar
  have hH₁ : H₁.IsHermitian := hH₀.add hV
  have htri (A : Matrix (Fin 2) (Fin 2) ℂ) : IsTridiagonal A := by
    intro i j hj
    have hi := i.isLt
    have hj' := j.isLt
    rcases hj with hj | hj <;> omega
  have hbC : (b : ℂ) ≠ 0 := fun h => hb (by simpa using congrArg Complex.re h)
  have hconnected (j : Fin 2) : EndpointConnected H₀ j := by
    intro p hp
    have hj := j.isLt
    have hpj : p.val < j.val := hp
    have hp0 : p = 0 := Fin.ext (by change p.val = 0; omega)
    rw [hp0]
    change (b : ℂ) ≠ 0
    exact hbC
  let g := firstColumn (spectralShift H₀ z)
  have hrow : -(b : ℂ) * g 0 + z * g 1 = 0 := by
    have hu := congrFun (inverse_col_equation (spectralShift H₀ z) (shift_det_isUnit hH₀ hz) 0)
      (1 : Fin 2)
    change (spectralShift H₀ z *ᵥ g) 1 = (Pi.single 0 1 : Fin 2 → ℂ) 1 at hu
    rw [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at hu
    simpa [spectralShift, H₀, twoSiteReference, Matrix.mulVec_apply_eq_sum,
      Fin.sum_univ_two, Matrix.one_apply, smul_eq_mul] using hu
  have hx₀ : (star x) 0 = (b : ℂ) := by
    change star (b : ℂ) = (b : ℂ)
    simp [Complex.star_def]
  have hx₁ : (star x) 1 = -z := by
    change star (-star z) = -z
    simp
  have hdot : star x ⬝ᵥ g = 0 := by
    calc
      _ = -(-(b : ℂ) * g 0 + z * g 1) := by
        rw [dotProduct, Fin.sum_univ_two, hx₀, hx₁]
        ring
      _ = 0 := by rw [hrow, neg_zero]
  have hkill : V *ᵥ g = 0 := by
    change ((ε : ℂ) • Matrix.vecMulVec x (star x)) *ᵥ g = 0
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hdot]
    simp
  have hsame : firstColumn (spectralShift H₁ z) = g := by
    apply (firstColumn_eq_iff_mulVec H₀ H₁ z (shift_det_isUnit hH₀ hz)
      (shift_det_isUnit hH₁ hz)).mpr
    change (H₀ + V - H₀) *ᵥ g = 0
    rw [show H₀ + V - H₀ = V by abel]
    exact hkill
  have hεC : (ε : ℂ) ≠ 0 := fun h => hε.ne' (by simpa using congrArg Complex.re h)
  refine ⟨hH₀, hH₁, htri _, htri _, hconnected, hsame, ?_⟩
  change (ε : ℂ) * (x 0 * (star x) 0) ≠ 0
  rw [hx₀]
  exact mul_ne_zero hεC (mul_ne_zero hbC hbC)

end D5.S3.Quantum.Matrix.Jacobi.SharpProbeTransfer
