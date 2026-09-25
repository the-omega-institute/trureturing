/- GID: D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pronko's Fredkin operators Sigma are finite anti-adjoint expansions in S. -/

/-
proof_shape: result: content
escape_witness: step_z (three-term recurrence of X ↦ {S^+, {S^-, X}} on the count patterns Z_r)
admission_basis: open-problem-resolution (issue #9982)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation (sigmaPlus, sigmaMinus, tensor, site, sigmaPow, Sigma)
-/

import D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation

open scoped BigOperators Matrix
open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation

namespace D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion

/-- The anti-adjoint action `(ãd a) b = {a, b} = a b + b a` (printed page 7). -/
def antiAd {N : ℕ} (a b : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  a * b + b * a

/-- (2.1): `S^+ = Σ_{j=1}^{N} σ_j^+`. -/
def totalPlus (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ∑ j, site N j sigmaPlus

/-- (2.1): `S^- = Σ_{j=1}^{N} σ_j^-`. -/
def totalMinus (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ∑ j, site N j sigmaMinus

/-- Conjecture 2 (printed page 7): for every `N` there are coefficients
`γ_1, …, γ_{⌈N/2⌉}` with `Σ^± = Σ_k γ_k (ãd S^± ãd S^∓)^{k-1} S^±`, one family of
coefficients serving both signs. The printed index `k` is `k.val + 1` here, and
`⌈N/2⌉ = (N + 1) / 2`. -/
def claim : Prop := ∀ N : ℕ, ∃ γ : Fin ((N + 1) / 2) → ℂ,
  Sigma N 1 = ∑ k, γ k •
      (fun X => antiAd (totalPlus N) (antiAd (totalMinus N) X))^[k] (totalPlus N) ∧
    Sigma N (-1) = ∑ k, γ k •
      (fun X => antiAd (totalMinus N) (antiAd (totalPlus N) X))^[k] (totalMinus N)

/-- Number of sites `i` with `(y i, x i) = (p, q)`. -/
private def cnt {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) : ℤ :=
  ∑ i, if y i = p ∧ x i = q then 1 else 0

/-- A matrix whose entry at `(y, x)` depends only on the counts of up-down and
down-up sites. -/
private def patt (N : ℕ) (F : ℤ → ℤ → ℂ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun y x => F (cnt 0 1 y x) (cnt 1 0 y x)

private lemma cnt_nonneg {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) : 0 ≤ cnt p q y x :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

private lemma cnt_partition {N : ℕ} (y x : Fin N → Fin 2) :
    cnt 0 0 y x + cnt 0 1 y x + cnt 1 0 y x + cnt 1 1 y x = N := by
  unfold cnt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin N, ((if y i = 0 ∧ x i = 0 then (1 : ℤ) else 0) +
      (if y i = 0 ∧ x i = 1 then 1 else 0) + (if y i = 1 ∧ x i = 0 then 1 else 0) +
      (if y i = 1 ∧ x i = 1 then 1 else 0)) = 1 := by
    intro i
    generalize y i = u
    generalize x i = w
    fin_cases u <;> fin_cases w <;> simp
  simp [h]

private lemma cnt_update_left {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) (j : Fin N)
    (v : Fin 2) :
    cnt p q (Function.update y j v) x =
      cnt p q y x - (if y j = p ∧ x j = q then 1 else 0) +
        (if v = p ∧ x j = q then 1 else 0) := by
  have h : cnt p q (Function.update y j v) x - cnt p q y x =
      (if v = p ∧ x j = q then 1 else 0) - (if y j = p ∧ x j = q then 1 else 0) := by
    unfold cnt
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Function.update_of_ne hij]
    · simp
  linarith

private lemma cnt_update_right {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) (j : Fin N)
    (v : Fin 2) :
    cnt p q y (Function.update x j v) =
      cnt p q y x - (if y j = p ∧ x j = q then 1 else 0) +
        (if y j = p ∧ v = q then 1 else 0) := by
  have h : cnt p q y (Function.update x j v) - cnt p q y x =
      (if y j = p ∧ v = q then 1 else 0) - (if y j = p ∧ x j = q then 1 else 0) := by
    unfold cnt
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Function.update_of_ne hij]
    · simp
  linarith

/-- Summing a site-type indicator produces the count. -/
private lemma sum_indicator {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) (K : ℂ) :
    (∑ j, if y j = p ∧ x j = q then K else 0) = (cnt p q y x : ℂ) * K := by
  unfold cnt
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

private lemma site_apply {N : ℕ} (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : Fin N → Fin 2) :
    site N j A y z = if z = Function.update y j (z j) then A (y j) (z j) else 0 := by
  classical
  unfold site tensor
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ j)]
  simp only [if_true]
  by_cases hz : z = Function.update y j (z j)
  · rw [if_pos hz, Finset.prod_eq_one, mul_one]
    intro i hi
    have hij : i ≠ j := by simpa using hi
    have hyz : y i = z i := by
      have := congrFun hz i
      rw [Function.update_of_ne hij] at this
      exact this.symm
    simp only [hij, if_false, Matrix.one_apply, hyz]
    simp
  · rw [if_neg hz]
    have hex : ∃ i, i ≠ j ∧ y i ≠ z i := by
      by_contra hne
      push Not at hne
      apply hz
      funext i
      by_cases hij : i = j
      · subst hij
        simp
      · rw [Function.update_of_ne hij]
        exact (hne i hij).symm
    obtain ⟨i, hij, hyz⟩ := hex
    rw [Finset.prod_eq_zero (i := i) (by simpa using hij), mul_zero]
    simp only [hij, if_false, Matrix.one_apply, hyz]

private lemma site_mul_apply {N : ℕ} (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (y x : Fin N → Fin 2) :
    (site N j A * M) y x = ∑ v : Fin 2, A (y j) v * M (Function.update y j v) x := by
  classical
  rw [Matrix.mul_apply]
  have h : ∀ z : Fin N → Fin 2, site N j A y z * M z x =
      ∑ v : Fin 2, if z = Function.update y j v then A (y j) v * M z x else 0 := by
    intro z
    rw [site_apply, Finset.sum_eq_single (z j)]
    · split_ifs <;> simp
    · intro v _ hv
      rw [if_neg]
      intro hz
      apply hv
      have := congrFun hz j
      simpa using this.symm
    · simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq']
  simp

private lemma mul_site_apply {N : ℕ} (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) (y x : Fin N → Fin 2) :
    (M * site N j A) y x = ∑ v : Fin 2, M y (Function.update x j v) * A v (x j) := by
  classical
  rw [Matrix.mul_apply]
  have hcond : ∀ z : Fin N → Fin 2,
      (x = Function.update z j (x j)) ↔ (z = Function.update x j (z j)) := by
    intro z
    constructor
    · intro h
      funext i
      by_cases hij : i = j
      · subst hij
        simp
      · have := congrFun h i
        rw [Function.update_of_ne hij] at this
        rw [Function.update_of_ne hij]
        exact this.symm
    · intro h
      funext i
      by_cases hij : i = j
      · subst hij
        simp
      · have := congrFun h i
        rw [Function.update_of_ne hij] at this
        rw [Function.update_of_ne hij]
        exact this.symm
  have h : ∀ z : Fin N → Fin 2, M y z * site N j A z x =
      ∑ v : Fin 2, if z = Function.update x j v then M y z * A v (x j) else 0 := by
    intro z
    rw [site_apply, Finset.sum_eq_single (z j)]
    · by_cases hz : z = Function.update x j (z j)
      · rw [if_pos ((hcond z).2 hz), if_pos hz]
      · rw [if_neg (fun h => hz ((hcond z).1 h)), if_neg hz, mul_zero]
    · intro v _ hv
      rw [if_neg]
      intro hz
      apply hv
      have := congrFun hz j
      simpa using this.symm
    · simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_eq']
  simp

private lemma minus_mul_apply {N : ℕ} (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (y x : Fin N → Fin 2) :
    (totalMinus N * M) y x =
      ∑ j, if y j = 1 then M (Function.update y j 0) x else 0 := by
  unfold totalMinus
  rw [Finset.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [site_mul_apply, Fin.sum_univ_two]
  generalize y j = u
  fin_cases u <;> simp [sigmaMinus]

private lemma mul_minus_apply {N : ℕ} (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (y x : Fin N → Fin 2) :
    (M * totalMinus N) y x =
      ∑ j, if x j = 0 then M y (Function.update x j 1) else 0 := by
  unfold totalMinus
  rw [Finset.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_site_apply, Fin.sum_univ_two]
  generalize x j = u
  fin_cases u <;> simp [sigmaMinus]

private lemma plus_mul_apply {N : ℕ} (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (y x : Fin N → Fin 2) :
    (totalPlus N * M) y x =
      ∑ j, if y j = 0 then M (Function.update y j 1) x else 0 := by
  unfold totalPlus
  rw [Finset.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [site_mul_apply, Fin.sum_univ_two]
  generalize y j = u
  fin_cases u <;> simp [sigmaPlus]

private lemma mul_plus_apply {N : ℕ} (M : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (y x : Fin N → Fin 2) :
    (M * totalPlus N) y x =
      ∑ j, if x j = 1 then M y (Function.update x j 0) else 0 := by
  unfold totalPlus
  rw [Finset.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_site_apply, Fin.sum_univ_two]
  generalize x j = u
  fin_cases u <;> simp [sigmaPlus]

private lemma partition_cast {N : ℕ} (y x : Fin N → Fin 2) :
    (cnt 0 0 y x : ℂ) + cnt 1 1 y x = N - cnt 0 1 y x - cnt 1 0 y x := by
  have h' : ((cnt 0 0 y x + cnt 0 1 y x + cnt 1 0 y x + cnt 1 1 y x : ℤ) : ℂ) = (N : ℂ) := by
    rw [cnt_partition y x]
    push_cast
    ring
  push_cast at h'
  linear_combination h'

/-- `{S^-, patt F}` is again a count pattern. -/
private lemma antiAd_minus_patt {N : ℕ} (F : ℤ → ℤ → ℂ) :
    antiAd (totalMinus N) (patt N F) =
      patt N (fun b c => ((N : ℂ) - b - c) * F (b + 1) c + 2 * c * F b (c - 1)) := by
  ext y x
  have hL : (totalMinus N * patt N F) y x =
      (cnt 1 1 y x : ℂ) * F (cnt 0 1 y x + 1) (cnt 1 0 y x) +
        (cnt 1 0 y x : ℂ) * F (cnt 0 1 y x) (cnt 1 0 y x - 1) := by
    rw [minus_mul_apply, ← sum_indicator 1 1, ← sum_indicator 1 0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [patt]
    rw [cnt_update_left, cnt_update_left]
    generalize y j = u
    generalize x j = w
    fin_cases u <;> fin_cases w <;> simp
  have hR : (patt N F * totalMinus N) y x =
      (cnt 0 0 y x : ℂ) * F (cnt 0 1 y x + 1) (cnt 1 0 y x) +
        (cnt 1 0 y x : ℂ) * F (cnt 0 1 y x) (cnt 1 0 y x - 1) := by
    rw [mul_minus_apply, ← sum_indicator 0 0, ← sum_indicator 1 0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [patt]
    rw [cnt_update_right, cnt_update_right]
    generalize y j = u
    generalize x j = w
    fin_cases u <;> fin_cases w <;> simp
  simp only [antiAd, Matrix.add_apply, hL, hR, patt]
  linear_combination (F (cnt 0 1 y x + 1) (cnt 1 0 y x)) * partition_cast y x

/-- `{S^+, patt F}` is again a count pattern. -/
private lemma antiAd_plus_patt {N : ℕ} (F : ℤ → ℤ → ℂ) :
    antiAd (totalPlus N) (patt N F) =
      patt N (fun b c => ((N : ℂ) - b - c) * F b (c + 1) + 2 * b * F (b - 1) c) := by
  ext y x
  have hL : (totalPlus N * patt N F) y x =
      (cnt 0 0 y x : ℂ) * F (cnt 0 1 y x) (cnt 1 0 y x + 1) +
        (cnt 0 1 y x : ℂ) * F (cnt 0 1 y x - 1) (cnt 1 0 y x) := by
    rw [plus_mul_apply, ← sum_indicator 0 0, ← sum_indicator 0 1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [patt]
    rw [cnt_update_left, cnt_update_left]
    generalize y j = u
    generalize x j = w
    fin_cases u <;> fin_cases w <;> simp
  have hR : (patt N F * totalPlus N) y x =
      (cnt 1 1 y x : ℂ) * F (cnt 0 1 y x) (cnt 1 0 y x + 1) +
        (cnt 0 1 y x : ℂ) * F (cnt 0 1 y x - 1) (cnt 1 0 y x) := by
    rw [mul_plus_apply, ← sum_indicator 1 1, ← sum_indicator 0 1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [patt]
    rw [cnt_update_right, cnt_update_right]
    generalize y j = u
    generalize x j = w
    fin_cases u <;> fin_cases w <;> simp
  simp only [antiAd, Matrix.add_apply, hL, hR, patt]
  linear_combination (F (cnt 0 1 y x) (cnt 1 0 y x + 1)) * partition_cast y x

/-- `Z_r(y, x) = [b = r + 1 ∧ c = r]`: `r + 1` up-flips and `r` down-flips. -/
private def zPatt (N : ℕ) (r : ℤ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  patt N fun b c => if b = r + 1 ∧ c = r then 1 else 0

/-- `E_s(y, x) = [b = s ∧ c = s]`. -/
private def ePatt (N : ℕ) (s : ℤ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  patt N fun b c => if b = s ∧ c = s then 1 else 0

/-- (M1): `{S^-, Z_r} = 2(r + 1) E_{r+1} + (N - 2r) E_r`. -/
private lemma antiAd_minus_z {N : ℕ} (r : ℤ) :
    antiAd (totalMinus N) (zPatt N r) =
      (2 * ((r : ℂ) + 1)) • ePatt N (r + 1) + ((N : ℂ) - 2 * r) • ePatt N r := by
  unfold zPatt ePatt
  rw [antiAd_minus_patt]
  ext y x
  simp only [patt, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  generalize cnt 0 1 y x = b
  generalize cnt 1 0 y x = c
  have e1 : (b + 1 = r + 1 ∧ c = r) ↔ (b = r ∧ c = r) := by omega
  have e2 : (b = r + 1 ∧ c - 1 = r) ↔ (b = r + 1 ∧ c = r + 1) := by omega
  simp only [e1, e2]
  by_cases h1 : b = r ∧ c = r
  · rw [if_pos h1, if_neg (by omega)]
    have hb : (b : ℂ) = r := by exact_mod_cast h1.1
    have hc : (c : ℂ) = r := by exact_mod_cast h1.2
    rw [hb, hc]
    ring
  · by_cases h2 : b = r + 1 ∧ c = r + 1
    · rw [if_neg h1, if_pos h2]
      have hc : (c : ℂ) = r + 1 := by exact_mod_cast h2.2
      rw [hc]
      ring
    · rw [if_neg h1, if_neg h2]
      ring

/-- (M2): `{S^+, E_s} = 2(s + 1) Z_s + (N - 2s + 1) Z_{s-1}`. -/
private lemma antiAd_plus_e {N : ℕ} (s : ℤ) :
    antiAd (totalPlus N) (ePatt N s) =
      (2 * ((s : ℂ) + 1)) • zPatt N s + ((N : ℂ) - 2 * s + 1) • zPatt N (s - 1) := by
  unfold zPatt ePatt
  rw [antiAd_plus_patt]
  ext y x
  simp only [patt, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  generalize cnt 0 1 y x = b
  generalize cnt 1 0 y x = c
  have e1 : (b = s ∧ c + 1 = s) ↔ (b = s ∧ c = s - 1) := by omega
  have e2 : (b - 1 = s ∧ c = s) ↔ (b = s + 1 ∧ c = s) := by omega
  have e3 : (b = s - 1 + 1 ∧ c = s - 1) ↔ (b = s ∧ c = s - 1) := by omega
  simp only [e1, e2, e3]
  by_cases h1 : b = s ∧ c = s - 1
  · rw [if_pos h1, if_neg (by omega)]
    have hb : (b : ℂ) = s := by exact_mod_cast h1.1
    have hc : (c : ℂ) = s - 1 := by exact_mod_cast h1.2
    rw [hb, hc]
    ring
  · by_cases h2 : b = s + 1 ∧ c = s
    · rw [if_neg h1, if_pos h2]
      have hb : (b : ℂ) = s + 1 := by exact_mod_cast h2.1
      rw [hb]
      ring
    · rw [if_neg h1, if_neg h2]
      ring

private lemma antiAd_smul_add {N : ℕ} (a X Y : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)
    (p q : ℂ) : antiAd a (p • X + q • Y) = p • antiAd a X + q • antiAd a Y := by
  simp only [antiAd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  abel

/-- The map `X ↦ {S^+, {S^-, X}}` as a linear map. -/
private def stepL (N : ℕ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ →ₗ[ℂ] Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ where
  toFun X := antiAd (totalPlus N) (antiAd (totalMinus N) X)
  map_add' X Y := by
    simp only [antiAd, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    simp only [antiAd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, RingHom.id_apply]

/-- (E): `{S^+, {S^-, Z_r}}` is a three-term combination of `Z_{r+1}`, `Z_r`, `Z_{r-1}`. -/
private lemma step_z {N : ℕ} (r : ℤ) :
    stepL N (zPatt N r) =
      (2 * ((r : ℂ) + 1)) • ((2 * ((r : ℂ) + 1 + 1)) • zPatt N (r + 1) +
          ((N : ℂ) - 2 * (r + 1) + 1) • zPatt N r) +
        ((N : ℂ) - 2 * r) • ((2 * ((r : ℂ) + 1)) • zPatt N r +
          ((N : ℂ) - 2 * r + 1) • zPatt N (r - 1)) := by
  change antiAd (totalPlus N) (antiAd (totalMinus N) (zPatt N r)) = _
  rw [antiAd_minus_z, antiAd_smul_add, antiAd_plus_e, antiAd_plus_e]
  simp only [add_sub_cancel_right]
  push_cast
  ring_nf

private def krylov (N n : ℕ) : Submodule ℂ (Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :=
  Submodule.span ℂ (Set.range fun i : Fin n => (⇑(stepL N))^[i] (totalPlus N))

private lemma krylov_mono {N n m : ℕ} (h : n ≤ m) : krylov N n ≤ krylov N m := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castLE h i, rfl⟩

private lemma krylov_step {N n : ℕ} {X : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ}
    (hX : X ∈ krylov N n) : stepL N X ∈ krylov N (n + 1) := by
  have h : stepL N X ∈ (krylov N n).map (stepL N) := Submodule.mem_map_of_mem hX
  rw [krylov, Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  refine ⟨i.succ, ?_⟩
  simp only [Fin.val_succ]
  rw [Function.iterate_succ_apply']

private lemma cnt_eq_zero_iff {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) :
    cnt p q y x = 0 ↔ ∀ i, ¬ (y i = p ∧ x i = q) := by
  unfold cnt
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by split_ifs <;> norm_num)]
  constructor
  · intro h i hi
    have := h i (Finset.mem_univ i)
    rw [if_pos hi] at this
    norm_num at this
  · intro h i _
    rw [if_neg (h i)]

private lemma ePatt_zero (N : ℕ) : ePatt N 0 = 1 := by
  ext y x
  simp only [ePatt, patt, Matrix.one_apply]
  by_cases hyx : y = x
  · subst hyx
    rw [if_pos rfl, if_pos]
    constructor
    · rw [cnt_eq_zero_iff]
      intro i hi
      rw [hi.1] at hi
      exact absurd hi.2 (by decide)
    · rw [cnt_eq_zero_iff]
      intro i hi
      rw [hi.1] at hi
      exact absurd hi.2 (by decide)
  · rw [if_neg hyx, if_neg]
    rintro ⟨h01, h10⟩
    rw [cnt_eq_zero_iff] at h01 h10
    apply hyx
    funext i
    have a := h01 i
    have b := h10 i
    generalize y i = u at a b ⊢
    generalize x i = w at a b ⊢
    fin_cases u <;> fin_cases w <;> simp_all

private lemma zPatt_neg_one (N : ℕ) : zPatt N (-1) = 0 := by
  ext y x
  simp only [zPatt, patt, Matrix.zero_apply]
  rw [if_neg]
  rintro ⟨_, h⟩
  have := cnt_nonneg 1 0 y x
  omega

/-- `S^+ = Z_0`. -/
private lemma totalPlus_eq_z (N : ℕ) : totalPlus N = zPatt N 0 := by
  have h := antiAd_plus_e (N := N) 0
  simp only [Int.cast_zero, zero_sub, zPatt_neg_one, smul_zero, add_zero, ePatt_zero,
    zero_add, mul_one] at h
  simp only [antiAd, Matrix.mul_one, Matrix.one_mul] at h
  rw [← two_smul ℂ (totalPlus N)] at h
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) h

private lemma zPatt_mem (N : ℕ) : ∀ r : ℕ, zPatt N r ∈ krylov N (r + 1) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | r
    · rw [Nat.cast_zero, ← totalPlus_eq_z]
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hr : zPatt N r ∈ krylov N (r + 2) :=
        krylov_mono (by omega) (ih r (by omega))
      have hr1 : zPatt N ((r : ℤ) - 1) ∈ krylov N (r + 2) := by
        rcases r with _ | r
        · rw [Nat.cast_zero, zero_sub, zPatt_neg_one]
          exact Submodule.zero_mem _
        · have e : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by push_cast; ring
          rw [e]
          exact krylov_mono (by omega) (ih r (by omega))
      have hstep : stepL N (zPatt N r) ∈ krylov N (r + 2) := krylov_step (ih r (by omega))
      have hα : (2 * ((r : ℂ) + 1)) * (2 * ((r : ℂ) + 1 + 1)) ≠ 0 := by
        have h1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
        have h2 : (r : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r + 1)
        exact mul_ne_zero (mul_ne_zero two_ne_zero h1) (mul_ne_zero two_ne_zero h2)
      have hcomb : ((2 * ((r : ℂ) + 1)) * (2 * ((r : ℂ) + 1 + 1))) • zPatt N ((r : ℤ) + 1) =
          stepL N (zPatt N r) -
            (2 * ((r : ℂ) + 1)) • (((N : ℂ) - 2 * (r + 1) + 1) • zPatt N r) -
            ((N : ℂ) - 2 * r) • ((2 * ((r : ℂ) + 1)) • zPatt N r +
              ((N : ℂ) - 2 * r + 1) • zPatt N ((r : ℤ) - 1)) := by
        rw [step_z]
        push_cast
        module
      have hmem : ((2 * ((r : ℂ) + 1)) * (2 * ((r : ℂ) + 1 + 1))) • zPatt N ((r : ℤ) + 1) ∈
          krylov N (r + 2) := by
        rw [hcomb]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ hstep ?_) ?_
        · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hr)
        · exact Submodule.smul_mem _ _
            (Submodule.add_mem _ (Submodule.smul_mem _ _ hr) (Submodule.smul_mem _ _ hr1))
      have := (Submodule.smul_mem_iff _ hα).1 hmem
      push_cast
      exact this

/-- The exponent `r_i ∈ {-1, 0, 1}` (encoded in `Fin 3`) of the unique Kronecker monomial
of (3.1) that is nonzero at the site pair `(a, b)`. -/
private def stepCode (a b : Fin 2) : Fin 3 := if a = b then 1 else if a = 0 then 2 else 0

/-- `Σ^ε(y, x) = [b - c = ε]`, read off from the Kronecker sum (3.1). -/
private lemma sigma_apply {N : ℕ} (ε : ℤ) (y x : Fin N → Fin 2) :
    Sigma N ε y x = if cnt 0 1 y x - cnt 1 0 y x = ε then 1 else 0 := by
  classical
  have hpow : ∀ (q : Fin 3) (a b : Fin 2),
      sigmaPow q a b = if q = stepCode a b then 1 else 0 := by
    intro q a b
    fin_cases q <;> fin_cases a <;> fin_cases b <;>
      norm_num [stepCode, sigmaPow, sigmaPlus, sigmaMinus, Matrix.one_apply, Fin.ext_iff]
  have htensor : ∀ r : Fin N → Fin 3,
      tensor N (fun i => sigmaPow (r i)) y x =
        if r = fun i => stepCode (y i) (x i) then 1 else 0 := by
    intro r
    rw [tensor]
    simp_rw [hpow]
    rw [Finset.prod_ite_zero]
    simp [funext_iff]
  have hlocal : ∀ a b : Fin 2, (((stepCode a b : Fin 3) : ℕ) : ℤ) - 1 =
      (if a = 0 ∧ b = 1 then 1 else 0) - (if a = 1 ∧ b = 0 then 1 else 0) := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num [stepCode, Fin.ext_iff]
  have hstep : (∑ i, ((((stepCode (y i) (x i) : Fin 3) : ℕ) : ℤ) - 1)) =
      cnt 0 1 y x - cnt 1 0 y x := by
    unfold cnt
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hlocal (y i) (x i)
  rw [PronkoFredkinNonCyclicAnnihilation.Sigma, Matrix.sum_apply]
  simp only [htensor]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hstep]

/-- `Σ^+ = Σ_{r < ⌈N/2⌉} Z_r`. -/
private lemma sigma_plus_eq_sum (N : ℕ) :
    Sigma N 1 = ∑ r ∈ Finset.range ((N + 1) / 2), zPatt N r := by
  ext y x
  rw [sigma_apply, Matrix.sum_apply]
  simp only [zPatt, patt]
  have hb := cnt_nonneg 0 1 y x
  have hc := cnt_nonneg 1 0 y x
  have ha := cnt_nonneg 0 0 y x
  have hd := cnt_nonneg 1 1 y x
  have hpart := cnt_partition y x
  by_cases h : cnt 0 1 y x - cnt 1 0 y x = 1
  · rw [if_pos h, Finset.sum_eq_single_of_mem (cnt 1 0 y x).toNat]
    · rw [if_pos]
      constructor <;> omega
    · rw [Finset.mem_range]
      omega
    · intro r _ hr
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply hr
      omega
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply h
    omega

private lemma cnt_swap {N : ℕ} (p q : Fin 2) (y x : Fin N → Fin 2) :
    cnt p q x y = cnt q p y x := by
  unfold cnt
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [and_comm]

private lemma sigma_minus_eq_transpose (N : ℕ) : Sigma N (-1) = (Sigma N 1)ᵀ := by
  ext y x
  rw [Matrix.transpose_apply, sigma_apply, sigma_apply, cnt_swap 0 1 y x, cnt_swap 1 0 y x]
  congr 1
  apply propext
  omega

private lemma site_transpose {N : ℕ} (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (site N j A)ᵀ = site N j Aᵀ := by
  ext y x
  simp only [Matrix.transpose_apply, site, tensor]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, if_false, Matrix.one_apply]
    simp [eq_comm]

private lemma totalPlus_transpose (N : ℕ) : (totalPlus N)ᵀ = totalMinus N := by
  have h : sigmaPlusᵀ = sigmaMinus := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  simp only [totalPlus, totalMinus, Matrix.transpose_sum, site_transpose, h]

private lemma totalMinus_transpose (N : ℕ) : (totalMinus N)ᵀ = totalPlus N := by
  rw [← totalPlus_transpose, Matrix.transpose_transpose]

private lemma antiAd_transpose {N : ℕ} (a b : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    (antiAd a b)ᵀ = antiAd aᵀ bᵀ := by
  simp only [antiAd, Matrix.transpose_add, Matrix.transpose_mul]
  abel

private lemma iterate_transpose (N k : ℕ) (X : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ) :
    ((fun X => antiAd (totalPlus N) (antiAd (totalMinus N) X))^[k] X)ᵀ =
      (fun X => antiAd (totalMinus N) (antiAd (totalPlus N) X))^[k] Xᵀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      antiAd_transpose, antiAd_transpose, totalPlus_transpose, totalMinus_transpose]

/-- Conjecture 2 holds for every `N`, with one family of coefficients for both signs. -/
theorem result : claim := by
  intro N
  have hmem : Sigma N 1 ∈ krylov N ((N + 1) / 2) := by
    rw [sigma_plus_eq_sum]
    refine Submodule.sum_mem _ fun r hr => ?_
    exact krylov_mono (by rw [Finset.mem_range] at hr; omega) (zPatt_mem N r)
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨γ, hγ.symm, ?_⟩
  rw [sigma_minus_eq_transpose, ← hγ, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_smul]
  congr 1
  have h := iterate_transpose N k (totalPlus N)
  rw [totalPlus_transpose] at h
  exact h

#print axioms result

end D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
