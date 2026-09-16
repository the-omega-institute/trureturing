/- GID: D5/S3/Observer/Monodromy/TransvectionCovarianceFiltration
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionCovarianceFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed-pulse variance effects have exactly the paired-reachability span at every depth. -/

import D5.S3.Observer.Monodromy.TransvectionLieFiltration
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic

/-!
# Exact second-moment observability of signed transvection histories

The effects are obtained by actual matrix congruences, starting from one
quadrature square. An independent two-endpoint graph process determines their
exact span. Unlike first moments, the two endpoints of a correlation may split;
when they coincide, one pulse can transport both. This is the reason one-body
reachability does not by itself determine covariance observability.

The field theorem needs only 2 != 0. A bosonic interpretation additionally needs
real invertible alternating H, a CCR representation, calibrated reversible
quadratic controls and identically prepared copies. No finite-dimensional CCR
matrices, state-positivity certificate, measurement backaction model or geometric
Fano lift is asserted by this source.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionCovarianceFiltration

open D5.S3.Observer.Monodromy.TransvectionLieFiltration

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- In the ell=H*x readout coordinates, this is the actual dual pulse matrix. -/
def dualPulse (H : Matrix I I K) (i : I) (t : K) : Matrix I I K :=
  1 + t • increment H.transpose i

/-- Actual effect of a signed control word; one measures its pairing with a
covariance matrix. The seed is e_a e_a^t and the head acts after the tail. -/
def effect (H : Matrix I I K) (a : I) : List (I × Bool) → Matrix I I K
  | [] => Matrix.single a a 1
  | (i, positive) :: w =>
      let P := dualPulse H i (if positive then 1 else -1)
      P * effect H a w * P.transpose

/-- Span of the actual finite set of variance measurements at the given budget. -/
def varianceLayer (H : Matrix I I K) (a : I) (k : ℕ) :
    Submodule K (Matrix I I K) :=
  Submodule.span K {X | ∃ w : List (I × Bool), w.length ≤ k ∧ X = effect H a w}

/-- Symmetric coordinate tensor, including D_ii=2E_ii. -/
def dyad (i j : I) : Matrix I I K :=
  Matrix.single i j 1 + Matrix.single j i 1

/-- Independent two-endpoint propagation in the graph of actual nonzero H entries.
A diagonal pair can move together in one pulse; a split pair moves one endpoint. -/
inductive PairReach (H : Matrix I I K) (a : I) : ℕ → I → I → Prop
  | start : PairReach H a 0 a a
  | keep {k : ℕ} {u v : I} :
      PairReach H a k u v → PairReach H a (k+1) u v
  | moveLeft {k : ℕ} {u v i : I} :
      PairReach H a k u v → H u i ≠ 0 → PairReach H a (k+1) i v
  | moveRight {k : ℕ} {u v i : I} :
      PairReach H a k u v → H v i ≠ 0 → PairReach H a (k+1) u i
  | moveTogether {k : ℕ} {u i : I} :
      PairReach H a k u u → H u i ≠ 0 → PairReach H a (k+1) i i

/-- The graph band has no reference to pulse products or covariance values. -/
def pairBand (H : Matrix I I K) (a : I) (k : ℕ) :
    Submodule K (Matrix I I K) :=
  Submodule.span K {X | ∃ u v, PairReach H a k u v ∧ X = dyad u v}

/-- Exact all-depth equality between genuine measurement effects and the
independently defined paired graph process. Singular and directed H are allowed.
Only signed unit pulses are used; arbitrary real amplitude control is not assumed. -/
theorem variance_layer_eq_pair_band (H : Matrix I I K) (a : I)
    (h2 : (2 : K) ≠ 0) (k : ℕ) :
    varianceLayer H a k = pairBand H a k := by
  classical
  let advance (i : I) (t : K) (X : Matrix I I K) :=
    dualPulse H i t * X * (dualPulse H i t).transpose
  have dsymm (u v : I) : dyad (K := K) u v = dyad v u := by
    simp only [dyad, add_comm]
  have dself (u : I) : dyad (K := K) u u = (2 : K) • Matrix.single u u 1 := by
    simp only [dyad, two_smul]
  have asingle (P : Matrix I I K) (u v r c : I) :
      (P * Matrix.single u v 1 * P.transpose) r c = P r u * P c v := by
    simp [Matrix.mul_apply, Matrix.single, Matrix.transpose_apply]
  have expansion (i u v : I) (t : K) :
      advance i t (dyad u v) = dyad u v +
        (t * H u i) • dyad i v + (t * H v i) • dyad u i +
        (t^2 * H u i * H v i) • dyad i i := by
    have hp (r c : I) : dualPulse H i t r c =
        (if r = c then 1 else 0) + t * (if r = i then H c i else 0) := by
      simp [dualPulse, increment, Matrix.one_apply, Matrix.transpose_apply]
    change (dualPulse H i t * dyad u v * (dualPulse H i t).transpose) = _
    rw [dyad, Matrix.mul_add, Matrix.add_mul]
    ext r c
    simp only [Matrix.add_apply, asingle, Matrix.smul_apply, smul_eq_mul, hp,
      dyad, Matrix.single_apply]
    split_ifs <;> simp_all <;> ring
  have odd_formula (i u v : I) :
      (2 : K)⁻¹ • (advance i 1 (dyad u v) - advance i (-1) (dyad u v)) =
        H u i • dyad i v + H v i • dyad u i := by
    rw [expansion, expansion]
    ext r c
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [h2]
    <;> ring
  have even_formula (i u v : I) :
      (2 : K)⁻¹ • (advance i 1 (dyad u v) + advance i (-1) (dyad u v) -
        (2 : K) • dyad u v) = (H u i * H v i) • dyad i i := by
    rw [expansion, expansion]
    ext r c
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [h2]
    <;> ring
  have reach_diagonal : ∀ {n : ℕ} {u v : I}, PairReach H a n u v →
      PairReach H a n u u ∧ PairReach H a n v v := by
    intro n u v h
    induction h with
    | start => exact ⟨.start, .start⟩
    | keep h ih => exact ⟨.keep ih.1, .keep ih.2⟩
    | moveLeft h he ih => exact ⟨.moveTogether ih.1 he, .keep ih.2⟩
    | moveRight h he ih => exact ⟨.keep ih.1, .moveTogether ih.2 he⟩
    | moveTogether h he ih => exact ⟨.moveTogether h he, .moveTogether h he⟩
  have reach_mono : ∀ {n m : ℕ} {u v : I}, n ≤ m →
      PairReach H a n u v → PairReach H a m u v := by
    intro n m u v hnm hp
    induction hnm with
    | refl => exact hp
    | step _ ih => exact .keep ih
  have band_mono : ∀ {n m : ℕ}, n ≤ m → pairBand H a n ≤ pairBand H a m := by
    intro n m h
    apply Submodule.span_mono
    rintro X ⟨u, v, hp, rfl⟩
    exact ⟨u, v, reach_mono h hp, rfl⟩
  have layer_mono : ∀ {n m : ℕ}, n ≤ m →
      varianceLayer H a n ≤ varianceLayer H a m := by
    intro n m h
    apply Submodule.span_mono
    rintro X ⟨w, hw, rfl⟩
    exact ⟨w, hw.trans h, rfl⟩
  have dyad_in_band : ∀ {n : ℕ} {u v : I}, PairReach H a n u v →
      dyad (K := K) u v ∈ pairBand H a n := by
    intro n u v h
    exact Submodule.subset_span ⟨u, v, h, rfl⟩
  have transported_layer : ∀ {n : ℕ} {X : Matrix I I K},
      X ∈ varianceLayer H a n → ∀ (i : I) (s : Bool),
        advance i (if s then 1 else -1) X ∈ varianceLayer H a (n+1) := by
    intro n X hX i s
    induction hX using Submodule.span_induction with
    | mem X hX =>
        rcases hX with ⟨w, hw, rfl⟩
        exact Submodule.subset_span ⟨(i,s)::w, by simpa using Nat.add_le_add_right hw 1, rfl⟩
    | zero => simp [advance]
    | add X Y _ _ hX hY =>
        simpa only [advance, Matrix.mul_add, Matrix.add_mul] using
          (varianceLayer H a (n+1)).add_mem hX hY
    | smul b X _ hX =>
        simpa only [advance, Matrix.mul_smul, Matrix.smul_mul] using
          (varianceLayer H a (n+1)).smul_mem b hX
  have odd_member : ∀ {n : ℕ} {u v : I},
      dyad (K := K) u v ∈ varianceLayer H a n → ∀ i,
        H u i • dyad i v + H v i • dyad u i ∈ varianceLayer H a (n+1) := by
    intro n u v h i
    have hplus : advance i 1 (dyad u v) ∈ varianceLayer H a (n+1) :=
      transported_layer h i true
    have hminus : advance i (-1) (dyad u v) ∈ varianceLayer H a (n+1) :=
      transported_layer h i false
    have hout := (varianceLayer H a (n+1)).smul_mem (2 : K)⁻¹
      ((varianceLayer H a (n+1)).sub_mem hplus hminus)
    rw [odd_formula] at hout
    exact hout
  have diagonal_step : ∀ {n : ℕ} {u i : I},
      dyad (K := K) u u ∈ varianceLayer H a n → H u i ≠ 0 →
        dyad (K := K) i i ∈ varianceLayer H a (n+1) := by
    intro n u i h he
    have hplus : advance i 1 (dyad u u) ∈ varianceLayer H a (n+1) :=
      transported_layer h i true
    have hminus : advance i (-1) (dyad u u) ∈ varianceLayer H a (n+1) :=
      transported_layer h i false
    have hold := layer_mono (Nat.le_succ n) h
    have hout := (varianceLayer H a (n+1)).smul_mem (2 : K)⁻¹
      ((varianceLayer H a (n+1)).sub_mem
        ((varianceLayer H a (n+1)).add_mem hplus hminus)
        ((varianceLayer H a (n+1)).smul_mem 2 hold))
    have heven : (H u i * H u i) • dyad i i ∈ varianceLayer H a (n+1) := by
      rwa [even_formula] at hout
    have hres := (varianceLayer H a (n+1)).smul_mem (H u i * H u i)⁻¹ heven
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero he he), one_smul] using hres
  have diagonal_cross : ∀ {n : ℕ} {u i : I},
      dyad (K := K) u u ∈ varianceLayer H a n → H u i ≠ 0 →
        dyad (K := K) u i ∈ varianceLayer H a (n+1) := by
    intro n u i h he
    have hm := odd_member h i
    rw [dsymm i u, ← add_smul] at hm
    have hcoef : H u i + H u i = (2 : K) * H u i := by ring
    rw [hcoef] at hm
    have hres := (varianceLayer H a (n+1)).smul_mem (2 * H u i)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 he), one_smul] using hres
  have move_right : ∀ {n : ℕ} {u v i : I},
      dyad (K := K) u v ∈ varianceLayer H a n →
      dyad (K := K) u u ∈ varianceLayer H a n → H v i ≠ 0 →
        dyad (K := K) u i ∈ varianceLayer H a (n+1) := by
    intro n u v i huv huu he
    by_cases hui : H u i = 0
    · have hm := odd_member huv i
      simp only [hui, zero_smul, zero_add] at hm
      have hres := (varianceLayer H a (n+1)).smul_mem (H v i)⁻¹ hm
      simpa only [smul_smul, inv_mul_cancel₀ he, one_smul] using hres
    · exact diagonal_cross huu hui
  have reachable_members : ∀ {n : ℕ} {u v : I}, PairReach H a n u v →
      dyad (K := K) u v ∈ varianceLayer H a n ∧
      dyad (K := K) u u ∈ varianceLayer H a n ∧
      dyad (K := K) v v ∈ varianceLayer H a n := by
    intro n u v h
    induction h with
    | start =>
        have hseed : Matrix.single a a (1 : K) ∈ varianceLayer H a 0 :=
          Submodule.subset_span ⟨[], by simp, rfl⟩
        have hd : dyad (K := K) a a ∈ varianceLayer H a 0 := by
          rw [dself]
          exact (varianceLayer H a 0).smul_mem 2 hseed
        exact ⟨hd, hd, hd⟩
    | keep h ih =>
        exact ⟨layer_mono (Nat.le_succ _) ih.1,
          layer_mono (Nat.le_succ _) ih.2.1, layer_mono (Nat.le_succ _) ih.2.2⟩
    | @moveLeft n u v i h he ih =>
        have hswap : dyad (K := K) v u ∈ varianceLayer H a n := by
          rw [dsymm v u]; exact ih.1
        have hcross := move_right hswap ih.2.2 he
        rw [dsymm v i] at hcross
        exact ⟨hcross, diagonal_step ih.2.1 he,
          layer_mono (Nat.le_succ n) ih.2.2⟩
    | @moveRight n u v i h he ih =>
        exact ⟨move_right ih.1 ih.2.1 he,
          layer_mono (Nat.le_succ n) ih.2.1, diagonal_step ih.2.2 he⟩
    | moveTogether h he ih =>
        have hd := diagonal_step ih.1 he
        exact ⟨hd, hd, hd⟩
  have transported_band : ∀ {n : ℕ} {X : Matrix I I K},
      X ∈ pairBand H a n → ∀ i t, advance i t X ∈ pairBand H a (n+1) := by
    intro n X hX i t
    induction hX using Submodule.span_induction with
    | mem X hX =>
        rcases hX with ⟨u, v, hp, rfl⟩
        rw [expansion]
        apply (pairBand H a (n+1)).add_mem
        · apply (pairBand H a (n+1)).add_mem
          · apply (pairBand H a (n+1)).add_mem
            · exact dyad_in_band (.keep hp)
            · by_cases he : H u i = 0
              · simp [he]
              · exact (pairBand H a (n+1)).smul_mem _ (dyad_in_band (.moveLeft hp he))
          · by_cases he : H v i = 0
            · simp [he]
            · exact (pairBand H a (n+1)).smul_mem _ (dyad_in_band (.moveRight hp he))
        · by_cases he : H u i = 0
          · simp [he]
          · exact (pairBand H a (n+1)).smul_mem _
              (dyad_in_band (.moveTogether (reach_diagonal hp).1 he))
    | zero => simp [advance]
    | add X Y _ _ hX hY =>
        simpa only [advance, Matrix.mul_add, Matrix.add_mul] using
          (pairBand H a (n+1)).add_mem hX hY
    | smul b X _ hX =>
        simpa only [advance, Matrix.mul_smul, Matrix.smul_mul] using
          (pairBand H a (n+1)).smul_mem b hX
  have effect_in_band (w : List (I × Bool)) : effect H a w ∈ pairBand H a w.length := by
    induction w with
    | nil =>
        have hd := (pairBand H a 0).smul_mem (2 : K)⁻¹ (dyad_in_band PairReach.start)
        rw [dself, smul_smul, inv_mul_cancel₀ h2, one_smul] at hd
        exact hd
    | cons p w ih =>
        rcases p with ⟨i,s⟩
        exact transported_band ih i (if s then 1 else -1)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro X ⟨w, hw, rfl⟩
    exact band_mono hw (effect_in_band w)
  · apply Submodule.span_le.mpr
    rintro X ⟨u, v, hp, rfl⟩
    exact (reachable_members hp).1

#print axioms variance_layer_eq_pair_band

end D5.S3.Observer.Monodromy.TransvectionCovarianceFiltration
