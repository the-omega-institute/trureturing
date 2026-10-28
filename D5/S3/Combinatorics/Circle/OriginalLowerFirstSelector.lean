/- GID: D5/S3/Combinatorics/Circle/OriginalLowerFirstSelector
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalLowerFirstSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Supported first LOWER selection, paid next-row mask and exact complement. -/
module
public import D5.S3.Combinatorics.Circle.OriginalLowerFullBank
public import D5.S3.Combinatorics.Circle.OriginalRowBounds
import all D5.S3.Combinatorics.Circle.OriginalLowerFullBank
import all D5.S3.Combinatorics.Circle.OriginalRowBounds
import all D5.S3.Combinatorics.Circle.OriginalLowerSelectorArithmetic
import all D5.S3.Combinatorics.Circle.M5SourceRows
import all D5.S3.Combinatorics.Circle.SourcePrefixInventory
import all D5.S3.Combinatorics.Circle.M5AttainedMesh
import all D5.S3.Combinatorics.Circle.TwoLargeOrdering

/-! The sole new public theorem has the original source telescope. Numerical
reflection weights are never treated as physical labels. In particular the
next negative SMALL mask is debited, and its complement is never restored.
The first selector proof is transcribed from the supplied primary §§3–6 and
independent HAND audit §§4–8; these are fallible mathematical sources.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
@[expose] public section
namespace D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
open SourceWidth M5FullWordConsumer SourcePrefixInventory OriginalLowerFullBank
open scoped BigOperators

/- Source forcing of the actual row-seven factor and the numerical record.
The row-eight coordinate remains actual a0; it has no upper bound by z. -/
private theorem source_arithmetic {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (hm : 5 < m)
    (he : (sourceCoordinates h).e = 1)
    (hF : 4 ≤ (sourceCoordinates h).F)
    (hLower : (sourceCoordinates h).F ≤ (sourceCoordinates h).H / 4)
    (hy : (sourceCoordinates h).y ≤ 2 * b - 3)
    (ha0 : 2 * b + 1 ≤ (sourceCoordinates h).a0)
    (A : ℤ) (hA : 1 ≤ A)
    (hprev : 2 * ((sourceCoordinates h).w - (sourceCoordinates h).n) * (A - 1) <
      (sourceCoordinates h).n + (sourceCoordinates h).Δ + 1) :
    ∃ D : SelectorArithmetic,
      D.b = b ∧ D.n = (sourceCoordinates h).n ∧ D.w = (sourceCoordinates h).w ∧
      D.q = (sourceCoordinates h).q ∧ D.tau = (2 : ℤ) ^ sourceLength t x 6 ∧ D.A = A ∧
      D.y = (sourceCoordinates h).y ∧ D.a0 = (sourceCoordinates h).a0 ∧
      D.f0 = (2 : ℤ) ^ sourceLength t x 8 ∧
      D.E = ((sourceCoordinates h).N + (sourceCoordinates h).z - 2 * (sourceCoordinates h).a0) / 2 ∧
      sourceLength t x 7 = L - 1 ∧
      (2 : ℤ) ^ sourceLength t x 7 = (sourceCoordinates h).H / 4 := by
  let B := OriginalLowerFullBank.sourcePrefixArithmetic h
  let R := OriginalLowerFullBank.sourceData h
  let delta := B.b - B.n
  let tau := (2 : ℤ) ^ sourceLength t x 6
  let eta := B.F * (B.w - B.b) - B.b
  let kappa := (B.z - B.n) / 2
  let a0 := sourceSeed t x 8
  let E := (B.N + B.z - 2 * a0) / 2
  have hpairs := h.pairs
  have hk := (OriginalLowerFullBank.source_count h).1
  have hcount := (OriginalLowerFullBank.source_count h).2
  have hL := (OriginalLowerFullBank.source_core h).2.1
  change B.e = 1 at he
  change 4 ≤ B.F at hF
  change B.F ≤ B.H / 4 at hLower
  change B.y ≤ 2 * B.b - 3 at hy
  change 2 * B.b + 1 ≤ a0 at ha0
  change 2 * (B.w - B.n) * (A - 1) < B.n + B.Δ + 1 at hprev
  obtain ⟨hn, hz, hb, hw, hv, hu, hG, hq, hHw, hwb, hza⟩ := arithmetic_geometry B
  have hFtau : B.F = 2 * tau := by change (2 : ℤ) ^ (_ + 1) = 2 * (2 : ℤ) ^ _; rw [pow_succ]; ring
  have htau : 2 ≤ tau := by omega
  have hroom : 4 * tau ≤ B.q := by have h4 := B.H_four; have hh := B.H_q; omega
  have hdelta : delta = B.H * B.Δ := by dsimp [delta]; nlinarith only [B.b_n]
  have hd : 0 < delta := by have hnb := B.nzb; dsimp [delta]; omega
  have hdn : delta < B.n := by rw [hdelta]; exact B.delta_n
  have hdsmall : 2 * delta < B.b := by dsimp [delta]; have hh := B.ab.2; have hn' := B.n_minimum; omega
  have hdgap : B.Δ + 2 ≤ delta := by
    have hm' := mul_nonneg (show 0 ≤ B.H - 2 by have hh := B.H_eight; omega)
      (show 0 ≤ B.Δ by have hh := B.delta_two; omega)
    rw [hdelta]
    have hh := B.delta_two
    nlinarith only [hm', hh]
  have huEq : B.u = B.H * B.w - B.N := by
    have hh := congrArg (fun q : ℤ => q * B.w) B.H_q
    have hs := B.u_source
    rw [he] at hs
    nlinarith only [hs, B.v_source, hh]
  have heta : B.H * eta = (B.F + 1) * B.n - B.y := by
    have hys := B.y_source
    rw [huEq] at hys
    have hNb := congrArg (fun z : ℤ => (B.F + 1) * z) B.N_b
    dsimp [eta]
    nlinarith only [hys, hNb]
  have hn2b : B.b < 2 * B.n := by have ha := B.n_minimum; have hab := B.ab.2; omega
  have heta0 : 0 < eta := by
    have hm' := mul_nonneg (show 0 ≤ B.F - 4 by omega) (le_of_lt hn)
    by_contra hh
    have hm'' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ B.H by have hH := B.H_eight; omega)
      (show eta ≤ 0 by omega)
    nlinarith only [heta, hm', hm'', hy, hn2b, hn]
  have hetaFn : B.H * eta < B.F * B.n := by have hy' := B.y_minimum; have hnb := B.nzb; nlinarith only [heta, hy', hnb.1, hnb.2]
  have heta4 : 4 * eta < B.b := by
    have h4F : 4 * B.F ≤ B.H := by have hh := B.H_four; omega
    have hm' := mul_le_mul_of_nonneg_right h4F (le_of_lt hn)
    have hprod : B.H * (4 * eta - B.n) < 0 := by nlinarith only [hetaFn, hm']
    have hneta : 4 * eta < B.n := by
      by_contra hh
      have hm'' := mul_nonneg (show 0 ≤ B.H by have hH := B.H_eight; omega)
        (show 0 ≤ 4 * eta - B.n by omega)
      omega
    have hnb := B.nzb
    omega
  have hb1 : 0 < B.b1 := by have hh := B.b1_hard; have ha := B.a_positive; omega
  have hr4 : 4 * B.r ≤ B.H := by have hh := B.r_bounds.2; have h4 := B.H_four; omega
  have hmul := mul_le_mul_of_nonneg_right hr4 (le_of_lt hb1)
  have hbn : B.H * B.b = B.H * B.n + B.H * delta := by dsimp [delta]; ring
  have hb1eq : B.b1 = B.n + B.H * delta := by rw [hdelta]; nlinarith only [B.b1_n]
  have hb1H := congrArg (fun z : ℤ => B.H * z) hb1eq
  have hwmax : B.w ≤ 2 * B.n - 3 := by have hh := B.w_bounds.2; have hna := B.n_minimum; omega
  have hpoly : (B.H - 2) * (B.n - B.H * delta) ≤ -6 := by
    nlinarith only [hmul, B.w_source, hwmax, B.N_b, hbn, hb1H]
  have hHd : B.n < B.H * delta := by
    by_contra hh
    have hm' := mul_nonneg (show 0 ≤ B.H - 2 by have hh := B.H_eight; omega)
      (show 0 ≤ B.n - B.H * delta by omega)
    omega
  have hetaD : eta < B.F * delta := by
    have hm' := mul_lt_mul_of_pos_left hHd (show 0 < B.F by omega)
    by_contra hh
    have hm'' := mul_le_mul_of_nonneg_left (le_of_not_gt hh)
      (show 0 ≤ B.H by have hh := B.H_eight; omega)
    nlinarith only [hm', hm'', hetaFn]
  have hAt : A ≤ tau := OriginalLowerFullBank.source_A_le_tau h he hF hy A hprev
  have core : OriginalRowBounds.RowCore k t L a b p := {
    dimension := hk, nonzero := h.nonzero, a_positive := h.a_positive,
    a_le_b := le_of_lt h.minimum_inequalities.1,
    negative_minimum := h.negative_minimum, positive_minimum := h.positive_minimum,
    negative_attained := h.negative_attained, p_maximum := h.p_maximum, p_row := h.p_row }
  have bounds7 := OriginalRowBounds.computed_row_bounds core x
    (h.x_positive_large.trans (le_abs_self _)) 7 (by omega)
  have bounds8 := OriginalRowBounds.computed_row_bounds core x
    (h.x_positive_large.trans (le_abs_self _)) 8 (by omega)
  change sourceLength t x 7 ≤ L ∧ _ at bounds7
  change sourceLength t x 8 ≤ L ∧ _ at bounds8
  have hs7 := OriginalLowerFullBank.source_terminal_formula h 7 (by omega)
  norm_num only [Nat.reduceMod, one_ne_zero, ite_false] at hs7
  have hs8 := OriginalLowerFullBank.source_seed_formula h 8 (by omega)
  norm_num only [Nat.reduceMod, ite_true] at hs8
  have hgb : (B.H / 4) * B.b < B.Q := by
    have hj : L - 1 < R.len 1 := by change L - 1 < sourceLength t x 1; rw [h.d_row_length]; omega
    have hh := R.small 1 ⟨L - 1, hj⟩
    rw [R.values] at hh
    change |(2 : ℤ) ^ (L - 1) * R.base 1| ≤ B.Q - 1 at hh
    rw [show R.base 1 = B.b from R.base1] at hh
    have hp : (0 : ℤ) ≤ 2 ^ (L - 1) * B.b := mul_nonneg (by positivity) (le_of_lt hb)
    rw [abs_of_nonneg hp] at hh
    have hpow : (2 : ℤ) ^ (L - 1) = B.H / 4 := by
      change (2 : ℤ) ^ (L - 1) = (2 : ℤ) ^ (L + 1) / 4
      rw [show L + 1 = (L - 1) + 2 by omega, pow_add]; norm_num
    rw [hpow] at hh
    omega
  have hgpos : (0 : ℤ) < 2 ^ sourceLength t x 7 := by positivity
  have hlen7 : sourceLength t x 7 = L - 1 := by
    by_contra hbad
    by_cases heqL : sourceLength t x 7 = L
    · rw [heqL] at hs7
      change actualSource k t (sourceParent t x 8) = B.q * B.y at hs7
      have hm' := mul_le_mul_of_nonneg_left B.y_minimum (show 0 ≤ B.q by omega)
      have hqB := congrArg (fun q : ℤ => q * B.b) B.H_q
      change a0 = B.N - 2 * actualSource k t (sourceParent t x 8) at hs8
      nlinarith only [hs7, hs8, hm', hqB, B.N_b, ha0, B.nzb.1, B.nzb.2, hb]
    · have hlen : sourceLength t x 7 + 1 ≤ L - 1 := by omega
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hlen
      have hGpow : (2 : ℤ) ^ (L - 1) = B.H / 4 := by
        change (2 : ℤ) ^ (L - 1) = (2 : ℤ) ^ (L + 1) / 4
        rw [show L + 1 = (L - 1) + 2 by omega, pow_add]; norm_num
      rw [pow_succ, hGpow] at hpow
      have hm' := mul_nonneg (show 0 ≤ B.H / 4 - 2 * (2 : ℤ) ^ sourceLength t x 7 by omega) (le_of_lt hb)
      have hm'' := mul_pos hgpos (show 0 < 2 * B.b - B.y by omega)
      have hterm : B.Q ≤ (2 : ℤ) ^ sourceLength t x 7 * B.y := bounds7.2.2.2.1
      nlinarith only [hm', hm'', hgb, hterm]
  have hg : (2 : ℤ) ^ sourceLength t x 7 = B.H / 4 := by
    rw [hlen7]
    change (2 : ℤ) ^ (L - 1) = (2 : ℤ) ^ (L + 1) / 4
    rw [show L + 1 = (L - 1) + 2 by omega, pow_add]; norm_num
  have ha0eq : a0 = B.N - B.q * B.y := by
    change actualSource k t (sourceParent t x 8) = (2 : ℤ) ^ sourceLength t x 7 * B.y at hs7
    rw [hg] at hs7
    have hqY := congrArg (fun q : ℤ => q * B.y) hq
    change a0 = B.N - 2 * actualSource k t (sourceParent t x 8) at hs8
    nlinarith only [hs7, hs8, hqY]
  have hkappa : 2 * kappa = B.z - B.n := by dsimp [kappa]; have hz' := B.odd_z; have hn' := B.odd_n; omega
  have hkappaD : 2 * kappa = delta - B.Δ := by dsimp [delta] at *; nlinarith only [hkappa, B.z_n, B.b_n]
  have hk0 : 0 ≤ kappa := by have hnz := B.nzb.1; omega
  have hnk : B.n + kappa < B.b := by
    dsimp only [delta] at hkappaD
    nlinarith only [hkappaD, B.delta_two, hd]
  have h2E : 2 * E = B.N + B.z - 2 * a0 := by
    dsimp [E]
    have hN := B.N_quarter
    have ho := B.odd_z
    omega
  have hqB := congrArg (fun q : ℤ => q * B.b) B.H_q
  have hEfront : E = B.q * B.b + B.n + kappa - a0 := by
    nlinarith only [h2E, hkappa, hqB, B.N_b]
  have hEsource : E = B.q * (B.y - B.b) + kappa := by
    nlinarith only [hEfront, ha0eq, hqB, B.N_b]
  have ha0bound : a0 ≤ B.C := by
    have hh := abs_le.mpr (source_bounds k t hk (advance (sourceParent t x 8) 1))
    exact hh
  have h2C : 2 * B.C = B.N - 1 := by have hN := B.N_quarter; have hC := B.C_quarter; omega
  have hE0 : 0 ≤ E := by nlinarith only [h2E, ha0bound, h2C, hz]
  have hetaSource : 2 * B.q * eta = 2 * tau * B.n - delta - (B.y - B.b) := by
    rw [B.H_q, hFtau] at heta
    dsimp only [delta]
    nlinarith only [heta]
  let D : SelectorArithmetic := {
    b := B.b, n := B.n, w := B.w, delta := delta, Delta := B.Δ,
    q := B.q, tau := tau, A := A, y := B.y, kappa := kappa, E := E,
    a0 := a0, f0 := (2 : ℤ) ^ sourceLength t x 8, Q := B.Q,
    b_pos := hb, delta_pos := hd, delta_small := hdsmall,
    n_eq := by dsimp [delta]; ring,
    delta_gap := hdgap, Delta_pos := by have hh := B.delta_two; omega,
    dw_pos := by omega, tau_two := htau, q_room := hroom,
    A_pos := hA, A_le := hAt, ceiling := hprev,
    eta_pos := by simpa only [eta, hFtau] using heta0,
    eta_small := by simpa only [eta, hFtau] using heta4,
    eta_delta := by simpa only [eta, hFtau] using hetaD,
    eta_source := by simpa only [eta, hFtau] using hetaSource,
    y_lower := B.y_minimum, y_upper := hy,
    y_odd := OriginalLowerFullBank.source_seed_odd h 7 (by omega),
    kappa_eq := hkappaD, kappa_nonneg := hk0, nk_small := hnk,
    E_source := hEsource, E_front := hEfront, E_nonneg := hE0,
    a0_pos := by omega, f0_one := one_le_pow₀ (by norm_num),
    terminal := bounds8.2.2.2.1,
    quarter := by nlinarith only [B.N_b, hqB, B.N_quarter, hn] }
  exact ⟨D, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlen7, hg⟩

/-- Actual chronological labels from a cut onward, excluding the boundary x. -/
def laterLabels {k : ℕ} (m t : ℕ) (x : Fin k) (start : ℕ) : Finset (Fin k) :=
  ((Finset.range (2 * m)).filter (fun i => start ≤ i)).biUnion
    (fun i => insert (sourceParent t x i) (sourceMask t x i Finset.univ))

private theorem mem_laterLabels {m k t start : ℕ} {x z : Fin k} :
    z ∈ laterLabels m t x start ↔ ∃ i, i < 2 * m ∧ start ≤ i ∧
      (z = sourceParent t x i ∨ z ∈ sourceMask t x i Finset.univ) := by
  classical
  simp [laterLabels, Finset.mem_biUnion, Finset.mem_insert, and_assoc]

private theorem later_step {m k t start : ℕ} (x : Fin k) (hs : start < 2 * m) :
    laterLabels m t x start = insert (sourceParent t x start)
      (sourceMask t x start Finset.univ ∪ laterLabels m t x (start + 1)) := by
  classical
  ext z
  simp only [mem_laterLabels, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨i, hi, his, he⟩
    by_cases heq : i = start
    · subst i; tauto
    · exact Or.inr (Or.inr ⟨i, hi, by omega, he⟩)
  · rintro (rfl | hz | ⟨i, hi, his, he⟩)
    · exact ⟨start, hs, le_refl _, Or.inl rfl⟩
    · exact ⟨start, hs, le_refl _, Or.inr hz⟩
    · exact ⟨i, hi, by omega, he⟩

private theorem future_eq_later {m k t : ℕ} (x : Fin k) :
    futureLabels m t x = laterLabels m t x 7 := by
  classical
  ext z
  simp only [futureLabels, List.mem_toFinset, List.mem_flatMap, List.mem_filter,
    List.mem_range, List.mem_cons, decide_eq_true_eq, mem_laterLabels]
  simp only [rowLabels, List.mem_ofFn, sourceMask, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨hi, his⟩, he | ⟨j, he⟩⟩
    · exact ⟨i, hi, his, Or.inl he⟩
    · exact ⟨i, hi, his, Or.inr ⟨j, he⟩⟩
  · rintro ⟨i, hi, his, he | ⟨j, he⟩⟩
    · exact ⟨i, ⟨hi, his⟩, Or.inl he⟩
    · exact ⟨i, ⟨hi, his⟩, Or.inr ⟨j, he⟩⟩

private theorem physical_mask_sum {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < 2 * m)
    (S : Finset (Fin (sourceLength t x i))) :
    (∑ z ∈ sourceMask t x i S, actualSource k t z) =
      weight S * (OriginalLowerFullBank.sourceData h).base i := by
  classical
  let R := OriginalLowerFullBank.sourceData h
  rw [← OriginalLowerFullBank.physical_mask_image x i S, Finset.sum_image]
  · exact row_sum R i S
  · intro o ho o' ho' heq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ho
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp ho'
    exact OriginalLowerFullBank.physical_injective_on h
      (OriginalLowerFullBank.mem_occurrences.mpr hi)
      (OriginalLowerFullBank.mem_occurrences.mpr hi) heq

private theorem physical_rows_disjoint {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i j : ℕ)
    (hi : i < 2 * m) (hj : j < 2 * m) (hne : i ≠ j)
    (S : Finset (Fin (sourceLength t x i)))
    (T : Finset (Fin (sourceLength t x j))) :
    Disjoint (sourceMask t x i S) (sourceMask t x j T) := by
  classical
  rw [← OriginalLowerFullBank.physical_mask_image x i S,
    ← OriginalLowerFullBank.physical_mask_image x j T]
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨o', ho', heq⟩ := Finset.mem_image.mp hz'
  have hvalid {r : ℕ} {U : Finset (Fin (sourceLength t x r))}
      {v : Occ (fun i => sourceLength t x i)} (hr : r < 2 * m) (hv : v ∈ rowMask _ r U) :
      v ∈ OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact OriginalLowerFullBank.mem_occurrences.mpr hr
  have he := OriginalLowerFullBank.physical_injective_on h (hvalid hj ho') (hvalid hi ho) heq
  subst o'
  exact Finset.disjoint_left.mp (rowMask_disjoint _ i j S T hne) ho ho'

private theorem parent_not_row {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i j : ℕ)
    (hi : i < 2 * m) (hj : j < 2 * m)
    (S : Finset (Fin (sourceLength t x j))) :
    sourceParent t x i ∉ sourceMask t x j S := by
  classical
  intro hz
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
  have heq := OriginalLowerFullBank.physical_injective_on h
    (show (Sum.inr ⟨j, v⟩ : Occ (fun i => sourceLength t x i)) ∈
      OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
      OriginalLowerFullBank.mem_occurrences.mpr hj)
    (show (Sum.inl i : Occ (fun i => sourceLength t x i)) ∈
      OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
      OriginalLowerFullBank.mem_occurrences.mpr hi) he
  cases heq

private theorem parent_ne {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i j : ℕ)
    (hi : i < 2 * m) (hj : j < 2 * m) (hne : i ≠ j) :
    sourceParent t x i ≠ sourceParent t x j := by
  intro he
  have hh := OriginalLowerFullBank.physical_injective_on h
    (show (Sum.inl i : Occ (fun i => sourceLength t x i)) ∈
      OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
      OriginalLowerFullBank.mem_occurrences.mpr hi)
    (show (Sum.inl j : Occ (fun i => sourceLength t x i)) ∈
      OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
      OriginalLowerFullBank.mem_occurrences.mpr hj) he
  exact hne (Sum.inl.inj hh)

private theorem mask_mono {k t i : ℕ} {x : Fin k}
    {S T : Finset (Fin (sourceLength t x i))} (h : S ⊆ T) :
    sourceMask t x i S ⊆ sourceMask t x i T := Finset.image_mono _ h

private theorem mask_difference {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (i : ℕ) (hi : i < 2 * m)
    (S T : Finset (Fin (sourceLength t x i))) :
    sourceMask t x i (S \ T) = sourceMask t x i S \ sourceMask t x i T := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_sdiff.mp hj).1, rfl⟩, ?_⟩
    intro hz'
    obtain ⟨j', hj', he⟩ := Finset.mem_image.mp hz'
    have heq := OriginalLowerFullBank.physical_injective_on h
      (show (Sum.inr ⟨i, j'⟩ : Occ (fun i => sourceLength t x i)) ∈
        OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
        OriginalLowerFullBank.mem_occurrences.mpr hi)
      (show (Sum.inr ⟨i, j⟩ : Occ (fun i => sourceLength t x i)) ∈
        OriginalLowerFullBank.occurrences (2 * m) (fun i => sourceLength t x i) from
        OriginalLowerFullBank.mem_occurrences.mpr hi) he
    have hjj : j' = j := by simpa using heq
    subst j'
    exact (Finset.mem_sdiff.mp hj).2 hj'
  · intro hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hz).1
    exact Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hj, fun hj' =>
      (Finset.mem_sdiff.mp hz).2 (Finset.mem_image.mpr ⟨j, hj', rfl⟩)⟩, rfl⟩

/-- A first-step conclusion with an explicit observational source readout. Source hypotheses always use actualSource;
only the output word, charges and strip observations use s. This definition
contains no existential premise and supplies no theorem by itself. -/
def FirstStep {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (s : Fin k → ℤ) : Prop :=
  let D := sourceCoordinates h
  let E := (D.N + D.z - 2 * D.a0) / 2
  ∃ (A f : ℤ) (c : ℕ)
    (Sn : Finset (Fin (sourceLength t x 2)))
    (Sw : Finset (Fin (sourceLength t x 4)))
    (Sz : Finset (Fin (sourceLength t x 0)))
    (Nsel : Finset (Fin (sourceLength t x 2)))
    (Wsel : Finset (Fin (sourceLength t x 4)))
    (Bsel : Finset (Fin (sourceLength t x 1)))
    (pay : ℕ) (Sp : Finset (Fin (sourceLength t x 8)))
    (Pfull post : List (Fin k)) (rho : ℤ),
    let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
      sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
    let Hsel := sourceMask t x 1 Bsel ∪ sourceMask t x 2 Nsel ∪ sourceMask t x 4 Wsel
    let Bfirst := (Kfull \ Hsel) ∪ sourceMask t x 7 Finset.univ ∪ sourceMask t x 8 Sp
    let P1 := Pfull ++ post ++ [sourceParent t x 8, sourceParent t x 7]
    let remaining := Hsel ∪ sourceMask t x 8 Spᶜ ∪ {sourceParent t x 9} ∪
      sourceMask t x 9 Finset.univ ∪ {sourceParent t x 10} ∪
      sourceMask t x 10 Finset.univ ∪ laterLabels m t x 11
    1 ≤ A ∧ A ≤ D.H / 4 ∧ 0 ≤ f ∧ f ≤ (D.w - 1) / 2 ∧
    2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n) ∧
    2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 ∧
    D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A ∧
    weight Sn = A ∧ weight Sw = D.H / 4 - A ∧ weight Sz = (c : ℤ) ∧ (c : ℤ) ≤ D.q - 1 ∧
    Pfull.Nodup ∧ Pfull.head? = some x ∧
    (∀ j : ℕ, 0 ≤ ((Pfull.take j).map s).sum ∧ ((Pfull.take j).map s).sum ≤ D.C) ∧
    Pfull.toFinsetᶜ = Kfull ∪ futureLabels m t x ∧
    Disjoint Kfull (futureLabels m t x) ∧
    2 * ((Pfull.map s).sum + ∑ z ∈ Kfull, s z) = D.z + D.y ∧
    Nsel ⊆ Sn ∧ Wsel ⊆ Sw ∧ Hsel ⊆ Kfull ∧
    weight Sp = (pay : ℤ) ∧ (pay : ℤ) ≤ (2 : ℤ) ^ sourceLength t x 8 - 1 ∧
    weight Spᶜ = (2 : ℤ) ^ sourceLength t x 8 - 1 - (pay : ℤ) ∧
    weight (Sn \ Nsel) = A - weight Nsel ∧
    weight (Sw \ Wsel) = D.H / 4 - A - weight Wsel ∧
    0 ≤ rho ∧ rho ≤ (D.y - 1) / 2 ∧
    E - (pay : ℤ) * D.a0 - (∑ z ∈ Hsel, s z) = rho ∧
    (∑ z ∈ Bfirst, s z) =
      (D.q - 1 - weight Bsel) * D.b + (D.H / 4 - 1) * D.y -
        ((A - weight Nsel) * D.n + (D.H / 4 - A - weight Wsel) * D.w +
          (c : ℤ) * D.z + ((2 : ℤ) ^ sourceLength t x 6 - 1) * D.u + (pay : ℤ) * D.a0) ∧
    post.Perm Bfirst.toList ∧
    0 ≤ (Pfull.map s).sum + (post.map s).sum ∧
    (Pfull.map s).sum + (post.map s).sum ≤ D.C ∧
    0 ≤ (Pfull.map s).sum + (post.map s).sum + s (sourceParent t x 8) ∧
    (Pfull.map s).sum + (post.map s).sum + s (sourceParent t x 8) ≤ D.C ∧
    (P1.map s).sum = rho ∧ P1.Nodup ∧ P1.head? = some x ∧
    (∀ j : ℕ, 0 ≤ ((P1.take j).map s).sum ∧ ((P1.take j).map s).sum ≤ D.C) ∧
    P1.toFinsetᶜ = remaining ∧
    sourceParent t x 9 ≠ x ∧ sourceParent t x 10 ≠ x ∧
    sourceParent t x (2 * m) = x

private theorem debit_partition_logic (P K F H Y R Pa T U V RC : Prop)
    (hc : ¬P ↔ K ∨ F) (hf : F ↔ U ∨ Y ∨ V ∨ R ∨ T)
    (hkn : K → ¬F) (hhs : H → K) (hsp : RC ↔ R ∧ ¬Pa)
    (hpas : Pa → R) (hr8 : R → ¬U ∧ ¬V ∧ ¬Y)
    (ht : T → ¬U ∧ ¬V ∧ ¬Y ∧ ¬Pa) :
    ¬((P ∨ (K ∧ ¬H ∨ Y) ∨ Pa) ∨ V ∨ U) ↔ (H ∨ RC) ∨ T := by
  classical
  constructor
  · intro hn
    rcases not_or.mp hn with ⟨hn1, hn2⟩
    have hnP : ¬P := fun hp => hn1 (Or.inl hp)
    have hnB : ¬(K ∧ ¬H ∨ Y) := fun hb => hn1 (Or.inr (Or.inl hb))
    have hnPa : ¬Pa := fun hp => hn1 (Or.inr (Or.inr hp))
    have hnV : ¬V := fun hv => hn2 (Or.inl hv)
    have hnU : ¬U := fun hu => hn2 (Or.inr hu)
    rcases hc.mp hnP with hk | hF
    · by_cases hh : H
      · exact Or.inl (Or.inl hh)
      · exact False.elim (hnB (Or.inl ⟨hk, hh⟩))
    · rcases hf.mp hF with hu | hy | hv | hr | hT
      · exact False.elim (hnU hu)
      · exact False.elim (hnB (Or.inr hy))
      · exact False.elim (hnV hv)
      · exact Or.inl (Or.inr (hsp.mpr ⟨hr, hnPa⟩))
      · exact Or.inr hT
  · intro hrem
    have hsafe : ¬P ∧ ¬(K ∧ ¬H ∨ Y) ∧ ¬Pa ∧ ¬V ∧ ¬U := by
      rcases hrem with (hh | hRC) | hT
      · have hk := hhs hh
        have hnF := hkn hk
        have hnY : ¬Y := fun hy => hnF (hf.mpr (Or.inr (Or.inl hy)))
        have hnR : ¬R := fun hr => hnF (hf.mpr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))
        refine ⟨hc.mpr (Or.inl hk), ?_, fun hp => hnR (hpas hp), ?_, ?_⟩
        · rintro (hkh | hy)
          · exact hkh.2 hh
          · exact hnY hy
        · exact fun hv => hnF (hf.mpr (Or.inr (Or.inr (Or.inl hv))))
        · exact fun hu => hnF (hf.mpr (Or.inl hu))
      · obtain ⟨hr, hnPa⟩ := hsp.mp hRC
        have hF := hf.mpr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
        obtain ⟨hnU, hnV, hnY⟩ := hr8 hr
        refine ⟨hc.mpr (Or.inr hF), ?_, hnPa, hnV, hnU⟩
        rintro (hkh | hy)
        · exact hkn hkh.1 hF
        · exact hnY hy
      · have hF := hf.mpr (Or.inr (Or.inr (Or.inr (Or.inr hT))))
        obtain ⟨hnU, hnV, hnY, hnPa⟩ := ht hT
        refine ⟨hc.mpr (Or.inr hF), ?_, hnPa, hnV, hnU⟩
        rintro (hkh | hy)
        · exact hkn hkh.1 hF
        · exact hnY hy
    obtain ⟨hnP, hnB, hnPa, hnV, hnU⟩ := hsafe
    rintro ((hp | hb | hpa) | hv | hu)
    · exact hnP hp
    · exact hnB hb
    · exact hnPa hpa
    · exact hnV hv
    · exact hnU hu

private theorem strip_of_takes {α : Type*} (s : α → ℤ) (C h : ℤ) (word : List α)
    (ht : ∀ j : ℕ, 0 ≤ h + ((word.take j).map s).sum ∧
      h + ((word.take j).map s).sum ≤ C) : InStrip s C h word := by
  induction word generalizing h with
  | nil => simpa [InStrip] using ht 0
  | cons i word ih =>
    have hzero := ht 0
    refine ⟨by simpa using hzero.1, by simpa using hzero.2, ih (h + s i) ?_⟩
    intro j
    simpa only [List.take_succ_cons, List.map_cons, List.sum_cons, add_assoc] using ht (j + 1)

set_option maxHeartbeats 4000000 in
/-- Supported first selection on the source-attained full LOWER bank. This
constructs masks and prepayment; no supported-selector conclusion is a premise.
The quotient restrictions deliberately retain the approved entry scope. -/
theorem canonical_lower_first_selector {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x) (hm : 5 < m)
    (he : (sourceCoordinates h).e = 1)
    (hF : 4 ≤ (sourceCoordinates h).F)
    (hLower : (sourceCoordinates h).F ≤ (sourceCoordinates h).H / 4)
    (hy : (sourceCoordinates h).y ≤ 2 * b - 3)
    (ha0 : 2 * b + 1 ≤ (sourceCoordinates h).a0)
    (hell : ((sourceCoordinates h).N + (sourceCoordinates h).z -
      2 * (sourceCoordinates h).a0) / 2 / b ≤ (sourceCoordinates h).q - 3)
    (hr : ((sourceCoordinates h).y - 1) / 2 <
      (((sourceCoordinates h).N + (sourceCoordinates h).z -
        2 * (sourceCoordinates h).a0) / 2) % b) :
    FirstStep h (actualSource k t) := by
  classical
  let D := sourceCoordinates h
  let R := OriginalLowerFullBank.sourceData h
  let s := actualSource k t
  let E := (D.N + D.z - 2 * D.a0) / 2
  have hpair := h.pairs
  have hk := (OriginalLowerFullBank.source_count h).1
  obtain ⟨A, f, c, Sn, Sw, Sz, Pfull, hA, hAG, hf, hfg, heq, hprev, hnext,
    hSn, hSw, hSz, hcq, hmin, hgate0, hgate1, hnd, hhead, hlegal,
    hdis, hcomp, hbfuture, hcharge, hparts⟩ := canonical_lower_full_bank h hLower
  change weight Sn = A at hSn
  change weight Sw = D.H / 4 - A at hSw
  change weight Sz = (c : ℤ) at hSz
  let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
    sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
  change Disjoint Pfull.toFinset Kfull at hdis
  change Pfull.toFinsetᶜ = Kfull ∪ futureLabels m t x at hcomp
  change Disjoint Kfull (futureLabels m t x) at hbfuture
  change 2 * ((Pfull.map s).sum + ∑ z ∈ Kfull, s z) = D.z + D.y at hcharge
  obtain ⟨hrw, Slow, hSlow, hlow, hlowdis, hWeq, hlowphys, htopphys, hdeplete⟩ := hparts he hF hy
  let top : Fin (sourceLength t x 4) := ⟨sourceLength t x 6, hrw⟩
  have hSlowSub : Slow ⊆ Sw := by rw [hWeq]; exact Finset.subset_union_right
  have hTop : top ∈ Sw := by rw [hWeq]; simp [top]
  obtain ⟨B, hbB, hnB, hwB, hqB, htB, hAB, hyB, ha0B, hf0B, hEB, hlen7, hg⟩ :=
    source_arithmetic h hm he hF hLower hy ha0 A hA hprev
  have hlw (j : Fin (sourceLength t x 4)) (hj : j ∈ Slow) :
      2 * (2 : ℤ) ^ j.val ≤ B.tau := by
    rw [htB]
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show j.val + 1 ≤ sourceLength t x 6 by have hh := hlow j hj; omega)
    rw [pow_succ] at hh
    nlinarith only [hh]
  have hEdiv : B.E = (B.E / B.b) * B.b + B.E % B.b := by
    nlinarith only [Int.emod_add_mul_ediv B.E B.b]
  have hremB : (B.y - 1) / 2 < B.E % B.b := by simpa only [hyB, hEB, hbB] using hr
  obtain ⟨Ns, Ws, j, rho, pay, hNs, hWs, hj0, hjq, hpay, hrho0, hrhoM, hselect⟩ :=
    numerical_selection B Sn Sw Slow top
      (by simpa only [weight, hAB] using hSn)
      (by simpa only [weight, htB, hAB] using hSlow)
      hSlowSub hTop (by simp [top, htB]) hlw
      (B.E / B.b) (B.E % B.b) hEdiv
      (Int.ediv_nonneg B.E_nonneg (le_of_lt B.b_pos))
      ⟨Int.emod_nonneg _ (ne_of_gt B.b_pos), Int.emod_lt_of_pos _ B.b_pos⟩ hremB
  have hjq' : j < (2 : ℤ) ^ sourceLength t x 1 := by
    have hp : (2 : ℤ) ^ sourceLength t x 1 = D.q := by change (2 : ℤ) ^ R.len 1 = _; exact R.pow1
    rw [hp]; rw [hqB] at hjq; change j < (sourceCoordinates h).q; omega
  obtain ⟨Sb, hSb⟩ := mask_exists (sourceLength t x 1) j hj0 hjq'
  have hpay' : (pay : ℤ) < (2 : ℤ) ^ sourceLength t x 8 := by simpa only [hf0B] using hpay
  obtain ⟨Sp, hSp⟩ := mask_exists (sourceLength t x 8) (pay : ℤ) (Nat.cast_nonneg _) hpay'
  let Hsel := sourceMask t x 1 Sb ∪ sourceMask t x 2 Ns ∪ sourceMask t x 4 Ws
  let Ry := sourceMask t x 7 (Finset.univ : Finset (Fin (sourceLength t x 7)))
  let Pa := sourceMask t x 8 Sp
  let Bfirst := (Kfull \ Hsel) ∪ Ry ∪ Pa
  let V := sourceParent t x 8
  let U := sourceParent t x 7
  have hNsub := mask_mono (t := t) (x := x) hNs
  have hWsub := mask_mono (t := t) (x := x) hWs
  have hBsub := mask_mono (t := t) (x := x) (Finset.subset_univ Sb)
  have hHsub : Hsel ⊆ Kfull := by
    intro z hz
    simp only [Hsel, Finset.mem_union] at hz
    simp only [Kfull, Finset.mem_union]
    rcases hz with (hz | hz) | hz
    · exact Or.inl (Or.inl (Or.inr (hBsub hz)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (hNsub hz))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (hWsub hz))))
  have hds (i j : ℕ) (hi : i < 2 * m) (hj : j < 2 * m) (hne : i ≠ j)
      (S : Finset (Fin (sourceLength t x i))) (T : Finset (Fin (sourceLength t x j))) :=
    physical_rows_disjoint h i j hi hj hne S T
  have hHsum : (∑ z ∈ Hsel, s z) = j * D.b - weight Ns * D.n - weight Ws * D.w := by
    dsimp only [Hsel]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨hds 1 4 (by omega) (by omega) (by decide) _ _,
        hds 2 4 (by omega) (by omega) (by decide) _ _⟩),
      Finset.sum_union (hds 1 2 (by omega) (by omega) (by decide) _ _),
      physical_mask_sum h 1 (by omega), physical_mask_sum h 2 (by omega),
      physical_mask_sum h 4 (by omega)]
    rw [(show R.base 1 = D.b from R.base1), (show R.base 2 = -D.n from R.base2),
      (show R.base 4 = -D.w from R.base4)]
    change weight Sb * D.b + weight Ns * (-D.n) + weight Ws * (-D.w) = _
    rw [hSb]; ring
  have hselected : E - (pay : ℤ) * D.a0 - (∑ z ∈ Hsel, s z) = rho := by
    rw [hHsum]
    simpa only [hEB, ha0B, hbB, hnB, hwB, E, D, sourceCoordinates] using hselect
  have hKsum : (∑ z ∈ Kfull, s z) =
      -A * D.n - (D.H / 4 - A) * D.w + (D.q - 1) * D.b -
        (c : ℤ) * D.z - ((2 : ℤ) ^ sourceLength t x 6 - 1) * D.u := by
    have hd6 : Disjoint (sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
        sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz)
        (sourceMask t x 6 Finset.univ) := by
      simp only [Finset.disjoint_union_left]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> apply physical_rows_disjoint h <;> omega
    have hd0 : Disjoint (sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
        sourceMask t x 1 Finset.univ) (sourceMask t x 0 Sz) := by
      simp only [Finset.disjoint_union_left]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply physical_rows_disjoint h <;> omega
    have hd1 : Disjoint (sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw)
        (sourceMask t x 1 Finset.univ) := by
      simp only [Finset.disjoint_union_left]
      constructor <;> apply physical_rows_disjoint h <;> omega
    dsimp only [Kfull]
    rw [Finset.sum_union hd6, Finset.sum_union hd0, Finset.sum_union hd1,
      Finset.sum_union (hds 2 4 (by omega) (by omega) (by decide) _ _),
      physical_mask_sum h 2 (by omega), physical_mask_sum h 4 (by omega),
      physical_mask_sum h 1 (by omega), physical_mask_sum h 0 (by omega),
      physical_mask_sum h 6 (by omega), hSn, hSw, hSz]
    simp only [weight_full]
    rw [(show R.base 2 = -D.n from R.base2), (show R.base 4 = -D.w from R.base4),
      (show R.base 1 = D.b from R.base1), (show R.base 0 = -D.z from R.base0),
      (show R.base 6 = -D.u from R.base6)]
    change A * (-D.n) + (D.H / 4 - A) * (-D.w) +
      ((2 : ℤ) ^ R.len 1 - 1) * D.b + (c : ℤ) * (-D.z) +
      ((2 : ℤ) ^ sourceLength t x 6 - 1) * (-D.u) = _
    rw [show (2 : ℤ) ^ R.len 1 = D.q from R.pow1]; ring
  have hbase7 : R.base 7 = D.y := by
    have hs := OriginalLowerFullBank.source_parent_sign h 7 (by omega)
    have hl := OriginalLowerFullBank.source_parent_large h 7 (by omega)
    norm_num only [Nat.reduceMod, one_ne_zero, ite_false] at hs
    rw [abs_of_neg hs] at hl
    have hn := (source_negative_step k t hk (sourceParent t x 7) (by omega)).2
    change s (advance (sourceParent t x 7) 1) = |s (advance (sourceParent t x 7) 1)|
    exact (abs_of_pos hn).symm
  have hbase8 : R.base 8 = -D.a0 := by
    have hs := OriginalLowerFullBank.source_parent_sign h 8 (by omega)
    have hl := OriginalLowerFullBank.source_parent_large h 8 (by omega)
    norm_num only [Nat.reduceMod, ite_true] at hs
    rw [abs_of_pos hs] at hl
    have hn := (source_positive_step k t hk (sourceParent t x 8) hl).2
    change s (advance (sourceParent t x 8) 1) = -|s (advance (sourceParent t x 8) 1)|
    rw [abs_of_neg hn]; ring
  have hRysum : (∑ z ∈ Ry, s z) = (D.H / 4 - 1) * D.y := by
    dsimp only [Ry]
    rw [physical_mask_sum h 7 (by omega), weight_full, hbase7, hg]
  have hPasum : (∑ z ∈ Pa, s z) = -(pay : ℤ) * D.a0 := by
    dsimp only [Pa]
    rw [physical_mask_sum h 8 (by omega), hSp, hbase8]; ring
  have hrowfuture (i : ℕ) (hi : 7 ≤ i) (hib : i < 2 * m)
      (S : Finset (Fin (sourceLength t x i))) : sourceMask t x i S ⊆ futureLabels m t x := by
    rw [future_eq_later]
    intro z hz
    exact mem_laterLabels.mpr ⟨i, hib, hi, Or.inr (mask_mono (Finset.subset_univ S) hz)⟩
  have hparentfuture (i : ℕ) (hi : 7 ≤ i) (hib : i < 2 * m) : sourceParent t x i ∈ futureLabels m t x := by
    rw [future_eq_later]
    exact mem_laterLabels.mpr ⟨i, hib, hi, Or.inl rfl⟩
  have hRyfuture : Ry ⊆ futureLabels m t x := hrowfuture 7 (le_refl _) (by omega) _
  have hPafuture : Pa ⊆ futureLabels m t x := hrowfuture 8 (by omega) (by omega) _
  have hKry : Disjoint Kfull Ry := hbfuture.mono_right hRyfuture
  have hKpa : Disjoint Kfull Pa := hbfuture.mono_right hPafuture
  have hrypa : Disjoint Ry Pa := hds 7 8 (by omega) (by omega) (by decide) _ _
  have hBsum : (∑ z ∈ Bfirst, s z) =
      (∑ z ∈ Kfull, s z) - (∑ z ∈ Hsel, s z) +
        (D.H / 4 - 1) * D.y - (pay : ℤ) * D.a0 := by
    dsimp only [Bfirst]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨hKpa.mono_left Finset.sdiff_subset, hrypa⟩),
      Finset.sum_union (hKry.mono_left Finset.sdiff_subset), hRysum, hPasum]
    have hh := Finset.sum_sdiff hHsub (f := s)
    linarith only [hh]
  have hcost : (∑ z ∈ Bfirst, s z) =
      (D.q - 1 - weight Sb) * D.b + (D.H / 4 - 1) * D.y -
        ((A - weight Ns) * D.n + (D.H / 4 - A - weight Ws) * D.w +
          (c : ℤ) * D.z + ((2 : ℤ) ^ sourceLength t x 6 - 1) * D.u + (pay : ℤ) * D.a0) := by
    rw [hBsum, hKsum, hHsum, hSb]; ring
  have hV : 2 * s V = D.N - D.a0 := by
    have hh := OriginalLowerFullBank.source_seed_formula h 8 (by omega)
    norm_num only [Nat.reduceMod, ite_true] at hh
    change D.a0 = D.N - 2 * s V at hh
    omega
  have hU : 2 * s U = D.y - D.N := by
    have hh := OriginalLowerFullBank.source_seed_formula h 7 (by omega)
    norm_num only [Nat.reduceMod, one_ne_zero, ite_false] at hh
    change D.y = D.N + 2 * s U at hh
    omega
  have hVpos : 0 < s V := by
    have hh := OriginalLowerFullBank.source_parent_sign h 8 (by omega)
    simpa only [Nat.reduceMod, ite_true] using hh
  have hUneg : s U < 0 := by
    have hh := OriginalLowerFullBank.source_parent_sign h 7 (by omega)
    simpa only [Nat.reduceMod, one_ne_zero, ite_false] using hh
  have ha0eq : D.a0 = D.N - 2 * (D.H / 4) * D.y := by
    have hh := OriginalLowerFullBank.source_seed_recurrence h 7 (by omega)
    norm_num only [Nat.reduceAdd, pow_succ] at hh
    rw [hg] at hh
    change D.a0 = D.N - (D.H / 4) * 2 * D.y at hh
    nlinarith only [hh]
  have h2E : 2 * E = D.N + D.z - 2 * D.a0 := by
    have hN := (OriginalLowerFullBank.sourcePrefixArithmetic h).N_quarter
    have hz := (OriginalLowerFullBank.sourcePrefixArithmetic h).odd_z
    change D.N = 4 * D.Q - 1 at hN
    change D.z % 2 = 1 at hz
    dsimp [E]; omega
  have hledger : (Pfull.map s).sum + (∑ z ∈ Kfull, s z) +
      (D.H / 4 - 1) * D.y + s V + s U = E := by
    nlinarith only [hcharge, ha0eq, hV, hU, h2E]
  have hfinal : (Pfull.map s).sum + (∑ z ∈ Bfirst, s z) + s V + s U = rho := by
    linarith only [hledger, hBsum, hselected]
  have h2C : 2 * D.C = D.N - 1 := by
    have hN := (OriginalLowerFullBank.sourcePrefixArithmetic h).N_quarter
    have hC := (OriginalLowerFullBank.sourcePrefixArithmetic h).C_quarter
    change D.N = 4 * D.Q - 1 at hN
    change D.C = 2 * D.Q - 1 at hC
    omega
  have hyodd : D.y % 2 = 1 := by simpa only [hyB] using B.y_odd
  have hrhoM' : rho ≤ (D.y - 1) / 2 := by simpa only [hyB] using hrhoM
  have hrho2 : 2 * rho ≤ D.y - 1 := by omega
  have hbefore : 0 ≤ (Pfull.map s).sum + (∑ z ∈ Bfirst, s z) ∧
      (Pfull.map s).sum + (∑ z ∈ Bfirst, s z) ≤ D.C := by
    constructor <;> nlinarith only [hfinal, hV, hU, ha0, hy, hrho0, hrho2, h2C, hVpos]
  have hafterV : 0 ≤ (Pfull.map s).sum + (∑ z ∈ Bfirst, s z) + s V ∧
      (Pfull.map s).sum + (∑ z ∈ Bfirst, s z) + s V ≤ D.C := by
    constructor <;> nlinarith only [hfinal, hU, hUneg, hrho0, hrho2, h2C]
  have hafterU : 0 ≤ rho ∧ rho ≤ D.C := by
    constructor
    · exact hrho0
    · nlinarith only [hfinal, hafterV.2, hUneg]
  have hBfuture : Bfirst ⊆ Kfull ∪ futureLabels m t x := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hz).1
      · exact Finset.mem_union_right _ (hRyfuture hz)
    · exact Finset.mem_union_right _ (hPafuture hz)
  have hdisB : Disjoint Pfull.toFinset Bfirst := by
    apply Finset.disjoint_left.mpr
    intro z hz hb
    have hc : z ∈ Pfull.toFinsetᶜ := by rw [hcomp]; exact hBfuture hb
    exact (Finset.mem_compl.mp hc) hz
  have hmaskSmall (i : ℕ) (S : Finset (Fin (sourceLength t x i))) :
      ∀ z ∈ sourceMask t x i S, |s z| ≤ D.Q - 1 := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact R.small i j
  have hKsmall : ∀ z ∈ Kfull, |s z| ≤ D.Q - 1 := by
    intro z hz
    simp only [Kfull, Finset.mem_union] at hz
    rcases hz with (((hz | hz) | hz) | hz) | hz
    · exact hmaskSmall 2 Sn z hz
    · exact hmaskSmall 4 Sw z hz
    · exact hmaskSmall 1 Finset.univ z hz
    · exact hmaskSmall 0 Sz z hz
    · exact hmaskSmall 6 Finset.univ z hz
  have hBsmall : ∀ z ∈ Bfirst, |s z| ≤ D.Q - 1 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact hKsmall z (Finset.mem_sdiff.mp hz).1
      · exact hmaskSmall 7 Finset.univ z hz
    · exact hmaskSmall 8 Sp z hz
  have hstart := hlegal Pfull.length
  simp only [List.take_length] at hstart
  have hQ : 0 ≤ D.Q - 1 := by
    have hh := (OriginalLowerFullBank.sourcePrefixArithmetic h).Q_positive
    change 0 < D.Q at hh
    omega
  have hQC : 2 * (D.Q - 1) ≤ D.C := by
    have hh := (OriginalLowerFullBank.sourcePrefixArithmetic h).C_quarter
    change D.C = 2 * D.Q - 1 at hh
    omega
  have hsumList : (Bfirst.toList.map s).sum = ∑ z ∈ Bfirst, s z := by
    rw [← List.sum_toFinset _ Bfirst.nodup_toList, Finset.toList_toFinset]
  obtain ⟨post, hpost, hpostStrip⟩ := ThreeRowSource.small_batch s D.C (D.Q - 1) hQ hQC
    Bfirst.toList.length Bfirst.toList (Pfull.map s).sum (le_refl _) Bfirst.nodup_toList
    hstart (by simpa only [hsumList] using hbefore)
    (fun i hi => hBsmall i (Finset.mem_toList.mp hi))
  have hpostSum : (post.map s).sum = ∑ z ∈ Bfirst, s z := (hpost.map s).sum_eq.trans hsumList
  have hpostSet : post.toFinset = Bfirst := by
    ext z
    simp only [List.mem_toFinset, hpost.mem_iff, Finset.mem_toList]
  have hdisList : List.Disjoint Pfull post := by
    rw [List.disjoint_left]
    intro z hz hp
    exact Finset.disjoint_left.mp hdisB (List.mem_toFinset.mpr hz)
      (Finset.mem_toList.mp (hpost.mem_iff.mp hp))
  have hsmallND : (Pfull ++ post).Nodup :=
    hnd.append (hpost.nodup_iff.mpr Bfirst.nodup_toList) hdisList
  have hPstrip : InStrip s D.C 0 Pfull := strip_of_takes s D.C 0 Pfull
    (by simpa only [zero_add, s, D, sourceCoordinates] using hlegal)
  have hsmallStrip : InStrip s D.C 0 (Pfull ++ post) :=
    inStrip_append hPstrip (by simpa only [zero_add] using hpostStrip)
  have hVnotK : V ∉ Kfull := fun hv => Finset.disjoint_left.mp hbfuture hv
    (hparentfuture 8 (by omega) (by omega))
  have hUnotK : U ∉ Kfull := fun hu => Finset.disjoint_left.mp hbfuture hu
    (hparentfuture 7 (by omega) (by omega))
  have hVnotB : V ∉ Bfirst := by
    simp only [Bfirst, Finset.mem_union, Finset.mem_sdiff, not_or]
    exact ⟨⟨fun hz => hVnotK hz.1, parent_not_row h 8 7 (by omega) (by omega) _⟩,
      parent_not_row h 8 8 (by omega) (by omega) _⟩
  have hUnotB : U ∉ Bfirst := by
    simp only [Bfirst, Finset.mem_union, Finset.mem_sdiff, not_or]
    exact ⟨⟨fun hz => hUnotK hz.1, parent_not_row h 7 7 (by omega) (by omega) _⟩,
      parent_not_row h 7 8 (by omega) (by omega) _⟩
  have hVnotP : V ∉ Pfull := by
    have hh : V ∈ Pfull.toFinsetᶜ := by rw [hcomp]; exact Finset.mem_union_right _ (hparentfuture 8 (by omega) (by omega))
    simpa only [Finset.mem_compl, List.mem_toFinset] using hh
  have hUnotP : U ∉ Pfull := by
    have hh : U ∈ Pfull.toFinsetᶜ := by rw [hcomp]; exact Finset.mem_union_right _ (hparentfuture 7 (by omega) (by omega))
    simpa only [Finset.mem_compl, List.mem_toFinset] using hh
  have hVneU : V ≠ U := parent_ne h 8 7 (by omega) (by omega) (by decide)
  have hVnot : V ∉ Pfull ++ post := by
    simp only [List.mem_append, not_or]
    exact ⟨hVnotP, fun hz => hVnotB (by rw [← hpostSet]; exact List.mem_toFinset.mpr hz)⟩
  have hUnot : U ∉ Pfull ++ post ++ [V] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨⟨hUnotP, fun hz => hUnotB (by rw [← hpostSet]; exact List.mem_toFinset.mpr hz)⟩, Ne.symm hVneU⟩
  let P1 := Pfull ++ post ++ [V, U]
  have hP1nd : P1.Nodup := by
    have hvnd : (Pfull ++ post ++ [V]).Nodup := by
      simpa only [List.concat_eq_append] using List.Nodup.concat hVnot hsmallND
    have hund := List.Nodup.concat hUnot hvnd
    simpa only [P1, List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append] using hund
  have hlaststrip : InStrip s D.C ((Pfull ++ post).map s).sum [V, U] := by
    simp only [InStrip, List.map_append, List.sum_append, hpostSum]
    refine ⟨hbefore.1, hbefore.2, hafterV.1, hafterV.2, ?_, ?_⟩
    · rw [hfinal]; exact hafterU.1
    · rw [hfinal]; exact hafterU.2
  have hP1strip : InStrip s D.C 0 P1 := by
    apply inStrip_append hsmallStrip
    simpa only [zero_add] using hlaststrip
  have hP1sum : (P1.map s).sum = rho := by
    simpa only [P1, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, hpostSum, add_assoc] using hfinal
  have hPnonempty : Pfull ≠ [] := by intro hh; simp [hh] at hhead
  have hP1head : P1.head? = some x := by
    simpa only [P1, List.append_assoc, List.head?_append_of_ne_nil Pfull hPnonempty] using hhead
  have htailNo (z : Fin k) (hz : z ∈ laterLabels m t x 9) :
      z ≠ U ∧ z ≠ V ∧ z ∉ Ry ∧ z ∉ Pa := by
    obtain ⟨i, hi, hi9, hz⟩ := mem_laterLabels.mp hz
    rcases hz with rfl | hz
    · exact ⟨parent_ne h i 7 hi (by omega) (by omega),
        parent_ne h i 8 hi (by omega) (by omega),
        parent_not_row h i 7 hi (by omega) _, parent_not_row h i 8 hi (by omega) _⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq; subst z
        exact parent_not_row h 7 i (by omega) hi _ hz
      · intro heq; subst z
        exact parent_not_row h 8 i (by omega) hi _ hz
      · intro hyz
        exact Finset.disjoint_left.mp (hds i 7 hi (by omega) (by omega) _ _) hz hyz
      · intro hpz
        exact Finset.disjoint_left.mp (hds i 8 hi (by omega) (by omega) _ _) hz
          (mask_mono (Finset.subset_univ Sp) hpz)
  have hR8diff : sourceMask t x 8 Spᶜ =
      sourceMask t x 8 Finset.univ \ Pa := by
    simpa only [← Finset.compl_eq_univ_sdiff] using mask_difference h 8 (by omega) Finset.univ Sp
  have hcomp9 : P1.toFinsetᶜ = Hsel ∪ sourceMask t x 8 Spᶜ ∪ laterLabels m t x 9 := by
    ext z
    have hc : z ∉ Pfull.toFinset ↔ z ∈ Kfull ∨ z ∈ futureLabels m t x := by
      rw [← Finset.mem_compl, hcomp, Finset.mem_union]
    have hfuture : z ∈ futureLabels m t x ↔
        z = U ∨ z ∈ Ry ∨ z = V ∨ z ∈ sourceMask t x 8 Finset.univ ∨ z ∈ laterLabels m t x 9 := by
      rw [future_eq_later, later_step x (show 7 < 2 * m by omega),
        later_step x (show 8 < 2 * m by omega)]
      simp only [Finset.mem_insert, Finset.mem_union, Ry, U, V]
    have hkn : z ∈ Kfull → z ∉ futureLabels m t x :=
      fun hz => Finset.disjoint_left.mp hbfuture hz
    have hhs : z ∈ Hsel → z ∈ Kfull := fun hz => hHsub hz
    have hsp : z ∈ sourceMask t x 8 Spᶜ ↔ z ∈ sourceMask t x 8 Finset.univ ∧ z ∉ Pa := by
      rw [hR8diff, Finset.mem_sdiff]
    have hpas : z ∈ Pa → z ∈ sourceMask t x 8 Finset.univ :=
      fun hz => mask_mono (Finset.subset_univ Sp) hz
    have hr8 : z ∈ sourceMask t x 8 Finset.univ → z ≠ U ∧ z ≠ V ∧ z ∉ Ry := by
      intro hz
      refine ⟨?_, ?_, ?_⟩
      · intro heq; subst z; exact parent_not_row h 7 8 (by omega) (by omega) _ hz
      · intro heq; subst z; exact parent_not_row h 8 8 (by omega) (by omega) _ hz
      · exact fun hyz => Finset.disjoint_left.mp
          (hds 8 7 (by omega) (by omega) (by decide) _ _) hz hyz
    have ht : z ∈ laterLabels m t x 9 → z ≠ U ∧ z ≠ V ∧ z ∉ Ry ∧ z ∉ Pa := htailNo z
    simp only [P1, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
      hpostSet, Finset.mem_compl, Finset.mem_union, Finset.mem_insert,
      Finset.notMem_empty, or_false, Bfirst, Finset.mem_sdiff]
    exact debit_partition_logic _ _ _ _ _ _ _ _ _ _ _ hc hfuture hkn hhs hsp hpas hr8 ht
  have hcompFinal : P1.toFinsetᶜ = Hsel ∪ sourceMask t x 8 Spᶜ ∪
      {sourceParent t x 9} ∪ sourceMask t x 9 Finset.univ ∪
      {sourceParent t x 10} ∪ sourceMask t x 10 Finset.univ ∪ laterLabels m t x 11 := by
    rw [hcomp9, later_step x (show 9 < 2 * m by omega),
      later_step x (show 10 < 2 * m by omega)]
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
  have hNrem : weight (Sn \ Ns) = A - weight Ns := by
    have hh := Finset.sum_sdiff hNs (f := fun j => (2 : ℤ) ^ j.val)
    dsimp only [weight] at hSn ⊢
    linarith only [hh, hSn]
  have hWrem : weight (Sw \ Ws) = D.H / 4 - A - weight Ws := by
    have hh := Finset.sum_sdiff hWs (f := fun j => (2 : ℤ) ^ j.val)
    dsimp only [weight] at hSw ⊢
    linarith only [hh, hSw]
  have hprem : weight Spᶜ = (2 : ℤ) ^ sourceLength t x 8 - 1 - (pay : ℤ) := by
    rw [weight_compl, hSp]
  refine ⟨A, f, c, Sn, Sw, Sz, Ns, Ws, Sb, pay, Sp, Pfull, post, rho,
    hA, hAG, hf, hfg, heq, hprev, hnext, hSn, hSw, hSz, hcq,
    hnd, hhead, hlegal, hcomp, hbfuture, hcharge, hNs, hWs, hHsub,
    hSp, by omega, hprem, hNrem, hWrem, hrho0, hrhoM', hselected,
    hcost, hpost, ?_, ?_, ?_, ?_, hP1sum, hP1nd, hP1head, ?_,
    hcompFinal, ?_, ?_, OriginalLowerFullBank.source_parent_boundary h⟩
  · change 0 ≤ (Pfull.map s).sum + (post.map s).sum
    rw [hpostSum]
    exact hbefore.1
  · change (Pfull.map s).sum + (post.map s).sum ≤ D.C
    rw [hpostSum]
    exact hbefore.2
  · change 0 ≤ (Pfull.map s).sum + (post.map s).sum + s V
    rw [hpostSum]
    exact hafterV.1
  · change (Pfull.map s).sum + (post.map s).sum + s V ≤ D.C
    rw [hpostSum]
    exact hafterV.2
  · intro j
    simpa only [zero_add] using inStrip_prefix hP1strip j
  · intro heq
    apply parent_ne h 9 0 (by omega) (by omega) (by decide)
    exact heq.trans (OriginalLowerFullBank.source_parent_zero h).symm
  · intro heq
    apply parent_ne h 10 0 (by omega) (by omega) (by decide)
    exact heq.trans (OriginalLowerFullBank.source_parent_zero h).symm

end D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
