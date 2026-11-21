/- GID: D5/S1/Recurrence/Asymptotic/DominantRootForcing
   generality: G
   mirror-B: D5/B/S1/Recurrence/Asymptotic/DominantRootForcing
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.Asymptotics.AsymptoticEquivalent]
   utility: none
   digest: A forced linear recurrence with a simple dominant real root R has solutions L R^j + O(q^j), with L the leading coefficient. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#349)
escape_witness: peel (a factor S - z with |z| < q maps only O(q^j) sequences to O(q^j)
  sequences, by the one-step bound |u_(j+1)| <= |z| |u_j| + C q^j), rstep (a factor S - R with
  0 < q < |R| sends d to O(q^j) only if d = L R^j + O(q^j), via the convergent series of the
  normalized forcing and its geometric tail) and dominant (factoring P = (X - R) Q, applying
  rstep to Q(S) b and peeling every root of Q); given_L (the leading coefficient of the
  O(q^j) expansion equals any L with b = L R^j + o(R^j), by comparing limits of b_j / R^j).
proof_shape:
  shift: definition; consumers: every lemma below.
  shift_pow_apply, aeval_apply, aeval_X_sub_C_apply, aeval_geom, global_bound: bind-only helpers;
    consumers: peel, rstep, dominant.
  peel, rstep: content; consumers: peel_prod, dominant.
  peel_prod: content (multiset induction over peel); consumer: dominant.
  dominant: content; consumers: given_L, result.
  given_L: content (dominant and uniqueness of the leading coefficient); consumer: result.
  result: content (after inlining the helpers added here, its live proof path runs through
    peel, rstep, dominant and given_L).
Direct frozen dependencies: none (Mathlib only).
Search record (§3.1): pinned Mathlib has linear recurrences only through LinearRecurrence
  (homogeneous solution spaces) and no asymptotic statement for inhomogeneous recurrences; no D5
  declaration states dominant-root forcing (searched D5 for rootMultiplicity, IsEquivalent and
  recurrence asymptotics).
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

/-! # Dominant-root forcing for linear recurrences

Let `P` be a real polynomial with a simple real root `R`, let `0 < q < |R|`, let every other complex
root of `P` have modulus below `q`, and let a real sequence satisfy
`∑ₖ P.coeff k * b (j + k) = e j` with `e = O(q^j)`. Then `b j = L R^j + O(q^j)` for a real `L`,
and any real `L` with `b j = L R^j + o(R^j)` is this coefficient. Lemma 2 of Ma–Zhang states the
case of a monic `P` with distinct roots, `R > 1`, other roots of modulus at most one and `q > 1`,
and the case `q = √R` under `b ~ L R^j`, `L > 0` and `e = O(√(b j))`.
-/

namespace D5.S1.Recurrence.Asymptotic.DominantRootForcing

open Polynomial Asymptotics Filter

/-- The shift `u ↦ (j ↦ u (j + 1))` on complex sequences. -/
def shift : Module.End ℂ (ℕ → ℂ) := LinearMap.funLeft ℂ ℂ (· + 1)

private theorem shift_pow_apply (k : ℕ) (u : ℕ → ℂ) (j : ℕ) : (shift ^ k) u j = u (j + k) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp [shift, LinearMap.funLeft_apply, Nat.add_assoc]

/-- Evaluating a polynomial at the shift gives the recurrence sum. -/
theorem aeval_apply (p : ℂ[X]) (u : ℕ → ℂ) (j : ℕ) :
    (aeval shift p) u j = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * u (j + k) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow_apply, smul_eq_mul]

theorem aeval_X_sub_C_apply (z : ℂ) (u : ℕ → ℂ) (j : ℕ) :
    (aeval shift (X - C z)) u j = u (j + 1) - z * u j := by
  simp [shift, LinearMap.funLeft_apply, Module.algebraMap_end_apply]

/-- Geometric sequences are eigenvectors of every polynomial in the shift. -/
private theorem aeval_geom (p : ℂ[X]) (w : ℂ) :
    (aeval shift p) (fun j => w ^ j) = fun j => p.eval w * w ^ j := by
  funext j
  rw [aeval_apply, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- For `q > 0`, a sequence that is `O(q^j)` is bounded by a single constant times `q^j`. -/
private theorem global_bound {E : Type} [SeminormedAddCommGroup E] {q : ℝ} (hq : 0 < q)
    {f : ℕ → E} (hf : f =O[atTop] (fun j => q ^ j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖f j‖ ≤ C * q ^ j := by
  obtain ⟨c, hc⟩ := hf.bound
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  refine ⟨|c| + ∑ j ∈ Finset.range N, ‖f j‖ / q ^ j, by positivity, fun j => ?_⟩
  have hqj : 0 < q ^ j := pow_pos hq j
  have hS : 0 ≤ ∑ j ∈ Finset.range N, ‖f j‖ / q ^ j := by positivity
  rcases Nat.lt_or_ge j N with hj | hj
  · have h1 : ‖f j‖ / q ^ j ≤ ∑ j ∈ Finset.range N, ‖f j‖ / q ^ j :=
      Finset.single_le_sum (f := fun i => ‖f i‖ / q ^ i) (fun i _ => by positivity)
        (Finset.mem_range.mpr hj)
    have h2 : ‖f j‖ = ‖f j‖ / q ^ j * q ^ j := by field_simp
    rw [h2]
    nlinarith [abs_nonneg c]
  · have h1 := hN j hj
    rw [Real.norm_eq_abs, abs_of_nonneg hqj.le] at h1
    nlinarith [le_abs_self c, abs_nonneg c]

/-- One factor of modulus below `q`: if `(S - z) u = O(q^j)` with `‖z‖ < q`, then
`u = O(q^j)`. -/
private theorem peel (z : ℂ) {q : ℝ} (hz : ‖z‖ < q) (u : ℕ → ℂ)
    (h : (aeval shift (X - C z)) u =O[atTop] (fun j => q ^ j)) :
    u =O[atTop] (fun j => q ^ j) := by
  have hq : 0 < q := lt_of_le_of_lt (norm_nonneg z) hz
  obtain ⟨C, hC0, hC⟩ := global_bound hq h
  have hgap : 0 < q - ‖z‖ := by linarith
  set M := max ‖u 0‖ (C / (q - ‖z‖)) with hM
  have hM0 : ‖u 0‖ ≤ M := le_max_left _ _
  have hM1 : C / (q - ‖z‖) ≤ M := le_max_right _ _
  have hMC : C ≤ (q - ‖z‖) * M := by
    rw [div_le_iff₀ hgap] at hM1
    linarith
  have hstep : ∀ j, ‖u (j + 1)‖ ≤ ‖z‖ * ‖u j‖ + C * q ^ j := fun j => by
    have := hC j
    rw [aeval_X_sub_C_apply] at this
    calc ‖u (j + 1)‖ = ‖z * u j + (u (j + 1) - z * u j)‖ := by ring_nf
      _ ≤ ‖z * u j‖ + ‖u (j + 1) - z * u j‖ := norm_add_le _ _
      _ ≤ ‖z‖ * ‖u j‖ + C * q ^ j := by
        rw [norm_mul]
        linarith
  have hall : ∀ j, ‖u j‖ ≤ M * q ^ j := by
    intro j
    induction j with
    | zero => simpa using hM0
    | succ j ih =>
      have hqj : 0 ≤ q ^ j := (pow_pos hq j).le
      calc ‖u (j + 1)‖ ≤ ‖z‖ * ‖u j‖ + C * q ^ j := hstep j
        _ ≤ ‖z‖ * (M * q ^ j) + (q - ‖z‖) * M * q ^ j := by
          gcongr
        _ = M * q ^ (j + 1) := by ring
  refine IsBigO.of_bound M (Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs (q ^ j), abs_of_nonneg (pow_pos hq j).le]
  exact hall j

/-- All factors of modulus below `q` peel off. -/
private theorem peel_prod {q : ℝ} (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ < q) :
    ∀ u : ℕ → ℂ, (aeval shift (s.map (fun z => X - C z)).prod) u =O[atTop] (fun j => q ^ j) →
      u =O[atTop] (fun j => q ^ j) := by
  induction s using Multiset.induction_on with
  | empty => intro u h; simpa using h
  | cons a s ih =>
    intro u h
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply] at h
    exact ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz)) u
      (peel a (hs a (Multiset.mem_cons_self a s)) _ h)

/-- The dominant factor: if `(S - R) d = O(q^j)` with `0 < q < |R|`, then
`d = L R^j + O(q^j)`. -/
private theorem rstep {R q : ℝ} (hq : 0 < q) (hqR : q < |R|) (d : ℕ → ℂ)
    (h : (aeval shift (X - C (R : ℂ))) d =O[atTop] (fun j => q ^ j)) :
    ∃ L : ℂ, (fun j => d j - L * (R : ℂ) ^ j) =O[atTop] (fun j => q ^ j) := by
  obtain ⟨C, hC0, hC⟩ := global_bound hq h
  have hR : 0 < |R| := by linarith
  have hR0 : R ≠ 0 := abs_pos.mp hR
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0
  have hRa : |R| ≠ 0 := hR.ne'
  let f : ℕ → ℂ := fun j => d (j + 1) - R * d j
  have hf : ∀ j, ‖f j‖ ≤ C * q ^ j := fun j => by
    have := hC j
    rwa [aeval_X_sub_C_apply] at this
  let w : ℕ → ℂ := fun i => f i / (R : ℂ) ^ (i + 1)
  have hρ0 : 0 ≤ q / |R| := by positivity
  have hρ1 : q / |R| < 1 := (div_lt_one hR).mpr hqR
  have hw : ∀ i, ‖w i‖ ≤ (C / |R|) * (q / |R|) ^ i := fun i => by
    have hRi : (0 : ℝ) < |R| ^ (i + 1) := by positivity
    simp only [w, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ hRi]
    calc ‖f i‖ ≤ C * q ^ i := hf i
      _ = C / |R| * (q / |R|) ^ i * |R| ^ (i + 1) := by
        rw [div_pow, pow_succ]
        field_simp
  have hsumw : Summable w :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (C / |R|)) hw
  have hclosed : ∀ j, d j = (R : ℂ) ^ j * (d 0 + ∑ i ∈ Finset.range j, w i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hfj : d (j + 1) = f j + R * d j := by simp [f]
      have hwj : (R : ℂ) ^ (j + 1) * w j = f j := by
        simp only [w]
        field_simp
      rw [hfj, ih, ← hwj]
      ring
  refine ⟨d 0 + ∑' i, w i, IsBigO.of_bound (C / (|R| - q)) (Eventually.of_forall fun j => ?_)⟩
  have htail := hsumw.sum_add_tsum_nat_add j
  have heq : d j - (d 0 + ∑' i, w i) * (R : ℂ) ^ j = -((R : ℂ) ^ j * ∑' i, w (i + j)) := by
    rw [hclosed j, ← htail]
    ring
  have hg : HasSum (fun i => (C / |R|) * (q / |R|) ^ j * (q / |R|) ^ i)
      ((C / |R|) * (q / |R|) ^ j * (1 - q / |R|)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hbound : ‖∑' i, w (i + j)‖ ≤ (C / |R|) * (q / |R|) ^ j * (1 - q / |R|)⁻¹ :=
    tsum_of_norm_bounded hg fun i => by
      have := hw (i + j)
      rw [pow_add] at this
      linarith [this]
  rw [heq, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q ^ j)]
  have hRq : 0 < |R| - q := by linarith
  calc |R| ^ j * ‖∑' i, w (i + j)‖
      ≤ |R| ^ j * ((C / |R|) * (q / |R|) ^ j * (1 - q / |R|)⁻¹) := by gcongr
    _ = C / (|R| - q) * q ^ j := by
        rw [div_pow]
        field_simp

/-- A linear recurrence whose characteristic polynomial has a simple root `R` and all other
complex roots of modulus below `q`, forced by `O(q^j)` with `0 < q < |R|`, has solutions
`b j = L R^j + O(q^j)`. -/
private theorem dominant (P : ℝ[X]) (R q : ℝ) (hmult : P.rootMultiplicity R = 1)
    (hq : 0 < q) (hqR : q < |R|)
    (hother : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q)
    (b e : ℕ → ℝ)
    (hrec : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j)
    (he : e =O[atTop] (fun j => q ^ j)) :
    ∃ L : ℝ, (fun j => b j - L * R ^ j) =O[atTop] (fun j => q ^ j) := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hmult
  have hroot : P.IsRoot R := (rootMultiplicity_pos hP0).mp (by omega)
  set PR := P /ₘ (X - C R) with hPRdef
  have hfac : (X - C R) * PR = P := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hPRR : PR.eval R ≠ 0 := by
    intro h0
    have h1 : (X - C R) ∣ PR := dvd_iff_isRoot.mpr h0
    have h2 : (X - C R) ^ 2 ∣ P := by
      obtain ⟨g, hg⟩ := h1
      exact ⟨g, by rw [← hfac, hg]; ring⟩
    have := (le_rootMultiplicity_iff hP0).mpr h2
    omega
  set PC := P.map (algebraMap ℝ ℂ) with hPCdef
  set Q := PR.map (algebraMap ℝ ℂ) with hQdef
  have hfacC : PC = (X - C (R : ℂ)) * Q := by
    rw [hPCdef, hQdef, ← hfac, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    rfl
  have hQR : Q.eval (R : ℂ) ≠ 0 := by
    rw [hQdef, eval_map, show (R : ℂ) = algebraMap ℝ ℂ R from rfl, eval₂_at_apply]
    intro h
    exact hPRR ((map_eq_zero_iff _ (algebraMap ℝ ℂ).injective).mp h)
  have hQ0 : Q ≠ 0 := fun h => hQR (by rw [h, eval_zero])
  -- the recurrence over ℂ
  let bC : ℕ → ℂ := fun j => (b j : ℂ)
  have hdeg : PC.natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective P
  have hrecC : (aeval shift PC) bC = fun j => (e j : ℂ) := by
    funext j
    rw [aeval_apply, hdeg, ← hrec j]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hPCdef, coeff_map]
    rfl
  have heC : (fun j => (e j : ℂ)) =O[atTop] (fun j => q ^ j) :=
    isBigO_norm_left.mp (by simpa [Complex.norm_real] using he.norm_left)
  -- the dominant step
  set d := (aeval shift Q) bC with hd
  have hd1 : (aeval shift (X - C (R : ℂ))) d = fun j => (e j : ℂ) := by
    rw [hd, ← Module.End.mul_apply, ← map_mul, ← hfacC, hrecC]
  obtain ⟨L', hL'⟩ := rstep hq hqR d (by rw [hd1]; exact heC)
  -- subtract the dominant geometric term and peel the remaining roots
  set Lc := L' / Q.eval (R : ℂ) with hLc
  let c : ℕ → ℂ := fun j => bC j - Lc * (R : ℂ) ^ j
  have hc : c = bC - Lc • (fun j => (R : ℂ) ^ j) := by
    funext j
    simp [c]
  have hQc : (aeval shift Q) c = fun j => d j - L' * (R : ℂ) ^ j := by
    rw [hc, map_sub, map_smul, aeval_geom]
    funext j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hLc, ← hd]
    field_simp
  have hsplit : Multiset.card Q.roots = Q.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits Q)
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hlead : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hroots : ∀ z ∈ Q.roots, ‖z‖ < q := fun z hz => by
    have hzQ : Q.IsRoot z := (mem_roots hQ0).mp hz
    apply hother z
    · rw [hfacC]
      simp [IsRoot, eval_mul, hzQ.eq_zero]
    · rintro rfl
      exact hQR hzQ.eq_zero
  have hQapp : (aeval shift Q) c =
      Q.leadingCoeff • (aeval shift (Q.roots.map (fun z => X - C z)).prod) c := by
    conv_lhs => rw [← hprod]
    rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  have hpr : (aeval shift (Q.roots.map (fun z => X - C z)).prod) c =
      Q.leadingCoeff⁻¹ • (aeval shift Q) c := by
    rw [hQapp, smul_smul, inv_mul_cancel₀ hlead, one_smul]
  have hcO : c =O[atTop] (fun j => q ^ j) :=
    peel_prod Q.roots hroots c (by rw [hpr, hQc]; exact hL'.const_smul_left _)
  refine ⟨Lc.re, IsBigO.trans (IsBigO.of_bound 1 (Eventually.of_forall fun j => ?_)) hcO⟩
  rw [one_mul, Real.norm_eq_abs]
  have hre : (c j).re = b j - Lc.re * R ^ j := by
    simp [c, bC, Complex.mul_re, ← Complex.ofReal_pow]
  rw [← hre]
  exact Complex.abs_re_le_norm (c j)

/-- If `0 < q < |R|`, the other roots have modulus below `q`, `b = L R^j + o(R^j)` and the
forcing is `O(q^j)`, then `b = L R^j + O(q^j)` with the same `L`. -/
private theorem given_L (P : ℝ[X]) (R q : ℝ) (hmult : P.rootMultiplicity R = 1)
    (hq : 0 < q) (hqR : q < |R|)
    (hother : ∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q)
    (b e : ℕ → ℝ) (L : ℝ)
    (hrec : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j)
    (hlo : (fun j => b j - L * R ^ j) =o[atTop] (fun j => R ^ j))
    (he : e =O[atTop] (fun j => q ^ j)) :
    (fun j => b j - L * R ^ j) =O[atTop] (fun j => q ^ j) := by
  have hR0 : 0 < |R| := by linarith
  have hRne : R ≠ 0 := abs_pos.mp hR0
  obtain ⟨L', hL'⟩ := dominant P R q hmult hq hqR hother b e hrec he
  -- the constants agree
  have hlimL : Tendsto (fun j => b j / R ^ j) atTop (nhds L) := by
    have h0' := hlo.tendsto_div_nhds_zero.add_const L
    rw [zero_add] at h0'
    refine h0'.congr fun j => ?_
    have : R ^ j ≠ 0 := pow_ne_zero j hRne
    field_simp
    ring
  have hlimL' : Tendsto (fun j => b j / R ^ j) atTop (nhds L') := by
    have hρ : Tendsto (fun j : ℕ => (q / |R|) ^ j) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hR0).mpr hqR)
    have hO : (fun j => (b j - L' * R ^ j) * (R ^ j)⁻¹) =O[atTop]
        (fun j => q ^ j * (R ^ j)⁻¹) := hL'.mul (isBigO_refl _ _)
    have hcomp : (fun j => q ^ j * (R ^ j)⁻¹) =O[atTop] (fun j => (q / |R|) ^ j) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun j => by
        rw [one_mul, norm_mul, norm_inv, norm_pow, norm_pow, norm_pow, Real.norm_eq_abs,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hq, div_pow,
          div_eq_mul_inv])
    have h0 : Tendsto (fun j => (b j - L' * R ^ j) * (R ^ j)⁻¹) atTop (nhds 0) :=
      (hO.trans hcomp).trans_tendsto hρ
    have h0' := h0.add_const L'
    rw [zero_add] at h0'
    refine h0'.congr fun j => ?_
    have : R ^ j ≠ 0 := pow_ne_zero j hRne
    field_simp
    ring
  have hLL : L' = L := tendsto_nhds_unique hlimL' hlimL
  rw [← hLL]
  exact hL'

/-- Dominant-root forcing for linear recurrences. Let `P` be a real polynomial with a simple
real root `R`, let `0 < q < |R|`, let every other complex root of `P` have modulus below `q`, and
let `∑ₖ P.coeff k * b (j + k) = e j` with `e = O(q^j)`. Then `b j = L R^j + O(q^j)` for some real
`L`, and for every real `L` with `b j = L R^j + o(R^j)` this `L` satisfies
`b j = L R^j + O(q^j)`. -/
theorem result :
    (∀ (P : ℝ[X]) (R q : ℝ), P.rootMultiplicity R = 1 → 0 < q → q < |R| →
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q) →
      ∀ b e : ℕ → ℝ,
      (∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j) →
      e =O[atTop] (fun j => q ^ j) →
      ∃ L : ℝ, (fun j => b j - L * R ^ j) =O[atTop] (fun j => q ^ j)) ∧
    (∀ (P : ℝ[X]) (R q : ℝ), P.rootMultiplicity R = 1 → 0 < q → q < |R| →
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q) →
      ∀ (b e : ℕ → ℝ) (L : ℝ),
      (∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j) →
      (fun j => b j - L * R ^ j) =o[atTop] (fun j => R ^ j) →
      e =O[atTop] (fun j => q ^ j) →
      (fun j => b j - L * R ^ j) =O[atTop] (fun j => q ^ j)) :=
  ⟨fun P R q hmult hq hqR hother b e hrec he => dominant P R q hmult hq hqR hother b e hrec he,
    fun P R q hmult hq hqR hother b e L hrec hlo he =>
      given_L P R q hmult hq hqR hother b e L hrec hlo he⟩

end D5.S1.Recurrence.Asymptotic.DominantRootForcing
