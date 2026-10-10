/- GID: D5/S3/Quantum/Petz/SpectralKernel
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labelled spectral curvature, its pair-transfer derivative and conditional monotonicity. -/

import D5.S3.Quantum.Petz.KernelSmoothness
import D5.S3.Quantum.Petz.SpectralSymmetrization
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

namespace D5.S3.Quantum.Petz.SpectralKernel

open D5.S3.Quantum.Petz.SymmetricKernel
open D5.S3.Quantum.Petz.KernelSmoothness
open D5.S3.Quantum.Petz.SpectralSymmetrization
open Filter Set
open scoped BigOperators Topology

noncomputable def spectralS {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k, d (lam i) (lam j) (lam k)) - ∑ i, d (lam i) (lam i) (lam i)

noncomputable def spectralHs {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k, hs (lam i) (lam j) (lam k)) - ∑ i, hs (lam i) (lam i) (lam i)

/-- A transfer acts on labelled positions, including repeated spectral values. -/
def pairTransfer {n : ℕ} (lam : Fin n → ℝ) (p q : Fin n) (t : ℝ) (i : Fin n) : ℝ :=
  lam i + t * ((if i = p then 1 else 0) - (if i = q then 1 else 0))

private def velocity {n : ℕ} (p q i : Fin n) : ℝ :=
  (if i = p then 1 else 0) - (if i = q then 1 else 0)

private lemma triple_chain (H : ℝ × ℝ × ℝ → ℝ) {x y z t a b c : ℝ}
    {f g h : ℝ → ℝ} (hH : DifferentiableAt ℝ H (x,y,z))
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) (hh : HasDerivAt h c t)
    (hx : f t = x) (hy : g t = y) (hz : h t = z) :
    HasDerivAt (fun u => H (f u,g u,h u))
      (a * deriv (fun u => H (u,y,z)) x +
       b * deriv (fun u => H (x,u,z)) y +
       c * deriv (fun u => H (x,y,u)) z) t := by
  let D := fderiv ℝ H (x,y,z)
  have hd : HasFDerivAt H D (f t,g t,h t) := by simpa [hx,hy,hz,D] using hH.hasFDerivAt
  have hd0 := hd.comp_hasDerivAt t (hf.prodMk (hg.prodMk hh))
  have hx0 := hH.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z)))
  have hy0 := hH.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z)))
  have hz0 := hH.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z x).prodMk ((hasDerivAt_const z y).prodMk (hasDerivAt_id z)))
  have hxD : deriv (fun u => H (u,y,z)) x = D (1,0,0) := by
    simpa only [Function.comp_def,id_eq] using hx0.deriv
  have hyD : deriv (fun u => H (x,u,z)) y = D (0,1,0) := by
    simpa only [Function.comp_def,id_eq] using hy0.deriv
  have hzD : deriv (fun u => H (x,y,u)) z = D (0,0,1) := by
    simpa only [Function.comp_def,id_eq] using hz0.deriv
  have hv : (a,b,c) = a • ((1,0,0) : ℝ × ℝ × ℝ) +
      b • ((0,1,0) : ℝ × ℝ × ℝ) + c • ((0,0,1) : ℝ × ℝ × ℝ) := by ext <;> simp
  have he : D (a,b,c) = a * deriv (fun u => H (u,y,z)) x +
      b * deriv (fun u => H (x,u,z)) y + c * deriv (fun u => H (x,y,u)) z := by
    rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [hxD,hyD,hzD]
  simpa only [Function.comp_def, he] using hd0

private lemma hs_path {x y z t a b c : ℝ} {f g h : ℝ → ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hf : HasDerivAt f a t) (hg : HasDerivAt g b t) (hh : HasDerivAt h c t)
    (hfx : f t = x) (hgy : g t = y) (hhz : h t = z) :
    HasDerivAt (fun u => hs (f u) (g u) (h u))
      (a * hs1 x y z + b * hs1 y x z + c * hs1 z x y) t := by
  have he : deriv (fun u => hs x y u) z = hs1 z x y := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hz] with u hu
    exact (hs_symm_right hx hy hu).trans (hs_symm hx hu hy)
  have hd := triple_chain (fun v => hs v.1 v.2.1 v.2.2) (hs_differentiableAt hx hy hz)
    hf hg hh hfx hgy hhz
  change HasDerivAt (fun u => hs (f u) (g u) (h u))
    (a * hs1 x y z + b * deriv (fun u => hs x u z) y +
      c * deriv (fun u => hs x y u) z) t at hd
  rw [hs1_swap hx hy hz,he] at hd
  exact hd

private lemma transfer_deriv {n : ℕ} (lam : Fin n → ℝ) (p q i : Fin n) :
    HasDerivAt (fun t => pairTransfer lam p q t i) (velocity p q i) 0 := by
  convert! (hasDerivAt_const (0 : ℝ) (lam i)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (velocity p q i)) using 1
  simp [velocity]

private lemma velocity_sum {n : ℕ} (p q : Fin n) (f : Fin n → ℝ) :
    (∑ i, velocity p q i * f i) = f p - f q := by
  classical
  simp [velocity,sub_mul,Finset.sum_sub_distrib,ite_mul]

/-- A genuine path derivative, usable when integrating finite transfer steps. -/
theorem spectralHs_transfer_hasDerivAt {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (p q : Fin n) :
    HasDerivAt (fun t => spectralHs (pairTransfer lam p q t))
      (3 * ((∑ j, ∑ k, (hs1 (lam p) (lam j) (lam k) - hs1 (lam q) (lam j) (lam k))) -
        (hs1 (lam p) (lam p) (lam p) - hs1 (lam q) (lam q) (lam q)))) 0 := by
  have hd (i j k : Fin n) := hs_path (hlam i) (hlam j) (hlam k)
    (transfer_deriv lam p q i) (transfer_deriv lam p q j) (transfer_deriv lam p q k)
    (by simp [pairTransfer]) (by simp [pairTransfer]) (by simp [pairTransfer])
  have ht := HasDerivAt.fun_sum (u := Finset.univ) (fun i hi =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j hj =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun k hk => hd i j k)))
  have hb := HasDerivAt.fun_sum (u := Finset.univ) (fun i hi => hd i i i)
  convert! ht.sub hb using 1
  simp only [Finset.sum_add_distrib]
  have hj : (∑ i, ∑ j, ∑ k, velocity p q j * hs1 (lam j) (lam i) (lam k)) =
      ∑ i, ∑ j, ∑ k, velocity p q i * hs1 (lam i) (lam j) (lam k) := by
    rw [Finset.sum_comm]
  have hk : (∑ i, ∑ j, ∑ k, velocity p q k * hs1 (lam k) (lam i) (lam j)) =
      ∑ i, ∑ j, ∑ k, velocity p q i * hs1 (lam i) (lam j) (lam k) := by
    have hc (i : Fin n) :
        (∑ j, ∑ k, velocity p q k * hs1 (lam k) (lam i) (lam j)) =
        ∑ k, ∑ j, velocity p q k * hs1 (lam k) (lam i) (lam j) := Finset.sum_comm
    simp_rw [hc]
    rw [Finset.sum_comm]
  rw [hj,hk]
  simp_rw [← Finset.mul_sum]
  simp_rw [velocity_sum]
  simp_rw [← Finset.sum_sub_distrib]
  ring

/-- The derivative before separating the two transferred positions. -/
theorem spectralHs_transfer_deriv_full {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (p q : Fin n) :
    deriv (fun t => spectralHs (pairTransfer lam p q t)) 0 =
      3 * ((∑ j, ∑ k, (hs1 (lam p) (lam j) (lam k) - hs1 (lam q) (lam j) (lam k))) -
        (hs1 (lam p) (lam p) (lam p) - hs1 (lam q) (lam q) (lam q))) :=
  (spectralHs_transfer_hasDerivAt lam hlam p q).deriv

/-- Relabelling positions does not change spectral curvature. -/
theorem spectralHs_perm {n : ℕ} (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    spectralHs (lam ∘ σ) = spectralHs lam := by
  unfold spectralHs
  simp only [Function.comp_def]
  have ht : (∑ i, ∑ j, ∑ k, hs (lam (σ i)) (lam (σ j)) (lam (σ k))) =
      ∑ i, ∑ j, ∑ k, hs (lam i) (lam j) (lam k) := by
    have hk (i j : Fin n) : (∑ k, hs (lam (σ i)) (lam (σ j)) (lam (σ k))) =
        ∑ k, hs (lam (σ i)) (lam (σ j)) (lam k) :=
      Equiv.sum_comp σ (fun k => hs (lam (σ i)) (lam (σ j)) (lam k))
    have hj (i : Fin n) : (∑ j, ∑ k, hs (lam (σ i)) (lam (σ j)) (lam k)) =
        ∑ j, ∑ k, hs (lam (σ i)) (lam j) (lam k) :=
      Equiv.sum_comp σ (fun j => ∑ k, hs (lam (σ i)) (lam j) (lam k))
    simp_rw [hk,hj]
    exact Equiv.sum_comp σ (fun i => ∑ j, ∑ k, hs (lam i) (lam j) (lam k))
  have hd : (∑ i, hs (lam (σ i)) (lam (σ i)) (lam (σ i))) =
      ∑ i, hs (lam i) (lam i) (lam i) :=
    Equiv.sum_comp σ (fun i => hs (lam i) (lam i) (lam i))
  rw [ht,hd]

/-- Residual positions; equal numerical eigenvalues remain separate summands. -/
def residualIndices {n : ℕ} (p q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ≠ p ∧ i ≠ q)

private lemma sum_split {n : ℕ} (p q : Fin n) (hpq : p ≠ q) (f : Fin n → ℝ) :
    (∑ i, f i) = f p + f q + ∑ i ∈ residualIndices p q, f i := by
  classical
  have he (i : Fin n) : f i = (if i = p then f p else 0) +
      (if i = q then f q else 0) + (if i ≠ p ∧ i ≠ q then f i else 0) := by
    by_cases hip : i = p <;> by_cases hiq : i = q <;> simp_all
  calc
    (∑ i, f i) = ∑ i, ((if i = p then f p else 0) + (if i = q then f q else 0) +
        (if i ≠ p ∧ i ≠ q then f i else 0)) := Finset.sum_congr rfl (fun i hi => he i)
    _ = _ := by simp [residualIndices,Finset.sum_add_distrib,Finset.sum_filter]

private lemma sum_pair_decomposition {n : ℕ} (p q : Fin n) (hpq : p ≠ q)
    (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = f p p + 2 * f p q + f q q +
      2 * (∑ i ∈ residualIndices p q, (f p i + f q i)) +
      ∑ i ∈ residualIndices p q, ∑ j ∈ residualIndices p q, f i j := by
  rw [sum_split p q hpq (fun i => ∑ j, f i j)]
  simp_rw [sum_split p q hpq (fun j => f _ j)]
  simp only [Finset.sum_add_distrib]
  have hleft : (∑ i ∈ residualIndices p q, f i p) =
      ∑ i ∈ residualIndices p q, f p i := Finset.sum_congr rfl (fun i hi => hf i p)
  have hright : (∑ i ∈ residualIndices p q, f i q) =
      ∑ i ∈ residualIndices p q, f q i := Finset.sum_congr rfl (fun i hi => hf i q)
  rw [hf q p,hleft,hright]
  ring

/-- Dittmann's corrected derivative identity for an arbitrary pair of positions. -/
theorem spectralHs_transfer_deriv {n : ℕ} (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (p q : Fin n) (hpq : p ≠ q) :
    (1 / 3 : ℝ) * deriv (fun t => spectralHs (pairTransfer lam p q t)) 0 =
      2 * hs1 (lam p) (lam p) (lam q) - hs1 (lam q) (lam p) (lam p) -
        2 * hs1 (lam q) (lam p) (lam q) + hs1 (lam p) (lam q) (lam q) +
      2 * (∑ i ∈ residualIndices p q,
        (hs1 (lam p) (lam p) (lam i) - hs1 (lam q) (lam q) (lam i) +
         hs1 (lam p) (lam q) (lam i) - hs1 (lam q) (lam p) (lam i))) +
      ∑ i ∈ residualIndices p q, ∑ j ∈ residualIndices p q,
        (hs1 (lam p) (lam i) (lam j) - hs1 (lam q) (lam i) (lam j)) := by
  rw [spectralHs_transfer_deriv_full lam hlam p q]
  rw [sum_pair_decomposition p q hpq
    (fun i j => hs1 (lam p) (lam i) (lam j) - hs1 (lam q) (lam i) (lam j))
    (fun i j => by
      apply congrArg₂ (fun a b : ℝ => a - b)
      · apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_gt_nhds (hlam p)] with u hu
        exact hs_symm_right hu (hlam i) (hlam j)
      · apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_gt_nhds (hlam q)] with u hu
        exact hs_symm_right hu (hlam i) (hlam j))]
  have he : (∑ i ∈ residualIndices p q,
      ((hs1 (lam p) (lam p) (lam i) - hs1 (lam q) (lam p) (lam i)) +
       (hs1 (lam p) (lam q) (lam i) - hs1 (lam q) (lam q) (lam i)))) =
      ∑ i ∈ residualIndices p q,
        (hs1 (lam p) (lam p) (lam i) - hs1 (lam q) (lam q) (lam i) +
         hs1 (lam p) (lam q) (lam i) - hs1 (lam q) (lam p) (lam i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

/-- Literal Lemma 4 hypotheses imply a nonnegative pair-transfer derivative. -/
theorem spectralHs_transfer_monotone
    (claim62 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ 2 * hs1 x x y - hs1 y x x - 2 * hs1 y x y + hs1 x y y)
    (claim63 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x x lam - hs1 y y lam)
    (claim64 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x y lam - hs1 y x lam)
    (claim65 : ∀ x y lam mu : ℝ, 0 < x → 0 < y → 0 < lam → 0 < mu → x < y →
      0 ≤ hs1 x lam mu - hs1 y lam mu)
    {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (p q : Fin n) (hxy : lam p < lam q) :
    0 ≤ deriv (fun t => spectralHs (pairTransfer lam p q t)) 0 := by
  have hpq : p ≠ q := fun h => (ne_of_lt hxy) (congrArg lam h)
  have h0 := claim62 (lam p) (lam q) 1 1 (hlam p) (hlam q) zero_lt_one zero_lt_one hxy
  have h1 : 0 ≤ ∑ i ∈ residualIndices p q,
      (hs1 (lam p) (lam p) (lam i) - hs1 (lam q) (lam q) (lam i) +
       hs1 (lam p) (lam q) (lam i) - hs1 (lam q) (lam p) (lam i)) := by
    apply Finset.sum_nonneg
    intro i hi
    have ha := claim63 (lam p) (lam q) (lam i) 1
      (hlam p) (hlam q) (hlam i) zero_lt_one hxy
    have hb := claim64 (lam p) (lam q) (lam i) 1
      (hlam p) (hlam q) (hlam i) zero_lt_one hxy
    linarith
  have h2 : 0 ≤ ∑ i ∈ residualIndices p q, ∑ j ∈ residualIndices p q,
      (hs1 (lam p) (lam i) (lam j) - hs1 (lam q) (lam i) (lam j)) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact claim65 (lam p) (lam q) (lam i) (lam j) (hlam p) (hlam q) (hlam i) (hlam j) hxy
  have hd := spectralHs_transfer_deriv lam hlam p q hpq
  linarith

private lemma triple_cyclic {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact Finset.sum_comm

/-- The ordered-triple curvature sum agrees with the symmetric-kernel sum. -/
theorem spectralS_eq_spectralHs {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    spectralS lam = spectralHs lam := by
  have hc := triple_cyclic (fun i j k => d (lam i) (lam j) (lam k))
  have hc2 := (triple_cyclic (fun i j k => d (lam k) (lam i) (lam j))).symm
  have ht :
      (∑ i, ∑ j, ∑ k, d (lam i) (lam j) (lam k)) +
      (∑ i, ∑ j, ∑ k, d (lam j) (lam k) (lam i)) +
      (∑ i, ∑ j, ∑ k, d (lam k) (lam i) (lam j)) =
      3 * (∑ i, ∑ j, ∑ k, hs (lam i) (lam j) (lam k)) := by
    simp_rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    linarith [d_symmetrization (hlam i) (hlam j) (hlam k)]
  rw [hc,hc2] at ht
  have hd : (∑ i, d (lam i) (lam i) (lam i)) = ∑ i, hs (lam i) (lam i) (lam i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [d_self (hlam i),hs_self (hlam i)]
  unfold spectralS spectralHs
  rw [hd]
  linarith

end D5.S3.Quantum.Petz.SpectralKernel
