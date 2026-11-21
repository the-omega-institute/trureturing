/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformZeroCorner
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformZeroCorner
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity, lake/module/D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords]
   utility: none
   digest: A nonzero periodic binary bond-two amplitude with zero adjacent-ones population has a square-zero occupied core. -/
/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformZeroCorner
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSUniformZeroCorner
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords]
   utility: none
   digest: Zero adjacent-ones probability forces a square-zero core at every length at least four. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
import D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Uniform restrictions from a vanishing adjacent-ones marginal for binary bond-two cores. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformZeroCorner

open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open PeriodicMPSTwoSiteAmbiguity (rawTwo flattening_entry)
open UniformMPSExpectedDimensionRefutation (traceWord)
open D5.S0.Observation.MatrixTracePowerSum (pow_add_two trace_pow_eq_add_pow)
open scoped BigOperators Matrix ComplexConjugate

open private graded mon invariants word word_reduction sandwich
  from D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords

noncomputable section

/-- The trace of a product in list order. -/
def listTrace (P : Fin 2 → Bond) (w : List (Fin 2)) : ℂ :=
  (w.map P).prod.trace

private theorem graded_eval_eq {P Q : Fin 2 → Bond} (h : invariants P = invariants Q)
    {k : ℤ} {f : (Fin 2 → Bond) → ℂ} (hf : f ∈ graded k) : f P = f Q := by
  change f ∈ Submodule.span ℂ _ at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨e, _, rfl⟩
    simp only [mon, h]
  | zero => rfl
  | add g j _ _ hg hj =>
    change g P + j P = g Q + j Q
    rw [hg, hj]
  | smul z g _ hg =>
    change z • g P = z • g Q
    rw [hg]

/-- The traces and determinants of both generators and their mixed trace determine
all binary word traces. -/
theorem listTrace_eq_of_invariants (P Q : Fin 2 → Bond)
    (h₀ : (P 0).trace = (Q 0).trace) (h₁ : (P 1).trace = (Q 1).trace)
    (hd₀ : (P 0).det = (Q 0).det) (hd₁ : (P 1).det = (Q 1).det)
    (hm : (P 0 * P 1).trace = (Q 0 * Q 1).trace)
    (w : List (Fin 2)) : listTrace P w = listTrace Q w := by
  have hinv : invariants P = invariants Q := by
    funext j
    fin_cases j
    · exact h₀
    · exact h₁
    · exact hd₀
    · exact hd₁
    · exact hm
  obtain ⟨r, hr₀, hr₁, hr₂, hr₃, hword⟩ := word_reduction w
  change (word w P).trace = (word w Q).trace
  rw [hword P, hword Q]
  simp only [Matrix.trace_add, Matrix.trace_smul, graded_eval_eq hinv hr₀,
    graded_eval_eq hinv hr₁, graded_eval_eq hinv hr₂, graded_eval_eq hinv hr₃,
    h₀, h₁, hm]

/-- Negating both traceless generators preserves the five trace invariants.
The induced sign on an odd word forces its trace to vanish. -/
theorem listTrace_eq_zero_of_odd_of_traceless (P : Fin 2 → Bond)
    (h₀ : (P 0).trace = 0) (h₁ : (P 1).trace = 0)
    (w : List (Fin 2)) (hw : Odd w.length) : listTrace P w = 0 := by
  have hd (M : Bond) : M.det = (-M).det := by
    norm_num [Matrix.det_neg, Fintype.card_fin]
  have htrace := listTrace_eq_of_invariants P (fun i => -P i)
    (by simp [h₀]) (by simp [h₁]) (hd (P 0)) (hd (P 1)) (by simp) w
  have hprod := List.smul_prod (w.map P) (-1 : ℂ)
  rw [List.length_map, hw.neg_one_pow] at hprod
  simp only [neg_smul, one_smul, List.map_map, Function.comp_def] at hprod
  have hsign : listTrace P w = -listTrace P w := by
    calc
      listTrace P w = listTrace (fun i => -P i) w := htrace
      _ = -listTrace P w := by
        change (w.map (fun i => -P i)).prod.trace = -(w.map P).prod.trace
        rw [← hprod, Matrix.trace_neg]
  linear_combination hsign / 2

/-- Every positive power of a singular two-by-two matrix has trace equal to
the corresponding power of its trace. -/
theorem trace_pow_succ_of_det_eq_zero (B : Bond) (h : B.det = 0) (k : ℕ) :
    (B ^ (k + 1)).trace = B.trace ^ (k + 1) := by
  simpa only [add_zero, zero_pow (Nat.succ_ne_zero k)] using
    trace_pow_eq_add_pow B B.trace 0 (by simp) (by simp [h]) (k + 1)

private theorem pow_two_eq_zero_of_trace_det_eq_zero (B : Bond)
    (ht : B.trace = 0) (hd : B.det = 0) : B ^ 2 = 0 := by
  simpa [ht, hd] using pow_add_two B 0

private theorem upper_product_entries (P : Fin 2 → Bond) (b c : ℂ)
    (htri : ∀ i, P i 1 0 = 0) (hdiag : ∀ i, b * P i 1 1 = c * P i 0 0)
    (w : List (Fin 2)) :
    (w.map P).prod 1 0 = 0 ∧
      b ^ w.length * (w.map P).prod 1 1 = c ^ w.length * (w.map P).prod 0 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    obtain ⟨hlo, hscale⟩ := ih
    let M := (w.map P).prod
    change (P i * M) 1 0 = 0 ∧
      b ^ (w.length + 1) * (P i * M) 1 1 = c ^ (w.length + 1) * (P i * M) 0 0
    have h10 : M 1 0 = 0 := hlo
    have h11 : (P i * M) 1 1 = P i 1 1 * M 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, htri i]
    have h00 : (P i * M) 0 0 = P i 0 0 * M 0 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, h10]
    refine ⟨by simp [Matrix.mul_apply, Fin.sum_univ_two, htri i, h10], ?_⟩
    rw [h11, h00, pow_succ' b, pow_succ' c]
    calc
      _ = (b * P i 1 1) * (b ^ w.length * M 1 1) := by ring
      _ = (c * P i 0 0) * (c ^ w.length * M 0 0) := by
        rw [hdiag i, show b ^ w.length * M 1 1 = c ^ w.length * M 0 0 from hscale]
      _ = _ := by ring

/-- A common triangular presentation with proportional diagonal characters
has zero word trace when the two length powers cancel. -/
theorem listTrace_eq_zero_of_upper_triangular (P : Fin 2 → Bond) (b c : ℂ)
    (hb : b ≠ 0) (htri : ∀ i, P i 1 0 = 0)
    (hdiag : ∀ i, b * P i 1 1 = c * P i 0 0)
    (w : List (Fin 2)) (hpow : b ^ w.length + c ^ w.length = 0) :
    listTrace P w = 0 := by
  obtain ⟨_, hscale⟩ := upper_product_entries P b c htri hdiag w
  have hz : b ^ w.length * listTrace P w = 0 := by
    rw [listTrace, Matrix.trace_fin_two, mul_add, hscale, ← add_mul, hpow, zero_mul]
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero w.length hb)

/-- For the diagonal second core and first-core diagonal entries `a,d`,
the first two vanishings impose `b*d = c*a`. The third forces either a
zero off-diagonal product or opposite second-core eigenvalues. -/
theorem scalar_reduction_of_three_traces {b c a d e : ℂ} (k : ℕ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h₀ : b ^ (k + 2) + c ^ (k + 2) = 0)
    (h₁ : a * b ^ (k + 1) + d * c ^ (k + 1) = 0)
    (h₂ : (a ^ 2 + e) * b ^ k + (d ^ 2 + e) * c ^ k = 0) :
    b * d = c * a ∧ (e = 0 ∨ b + c = 0) := by
  rw [pow_add b k 2, pow_add c k 2] at h₀
  rw [pow_succ b k, pow_succ c k] at h₁
  have hd : b * d = c * a := by
    have hm : (b * d - c * a) * (c * c ^ k) = 0 := by
      linear_combination b * h₁ - a * h₀
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (mul_ne_zero hc (pow_ne_zero _ hc)))
  have hdsq : b ^ 2 * d ^ 2 = c ^ 2 * a ^ 2 := by
    have hsq : (b * d) ^ 2 = (c * a) ^ 2 := congrArg (fun z : ℂ => z ^ 2) hd
    rwa [mul_pow, mul_pow] at hsq
  have hdiag : a ^ 2 * b ^ k + d ^ 2 * c ^ k = 0 := by
    have hm : b ^ 2 * (a ^ 2 * b ^ k + d ^ 2 * c ^ k) = 0 := by
      linear_combination a ^ 2 * h₀ + c ^ k * hdsq
    exact (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hb)
  have hprod : e * (b ^ k + c ^ k) = 0 := by
    linear_combination h₂ - hdiag
  refine ⟨hd, ?_⟩
  rcases mul_eq_zero.mp hprod with he | hz
  · exact Or.inl he
  · right
    have hm : (b - c) * (b + c) * b ^ k = 0 := by
      linear_combination h₀ - c ^ 2 * hz
    have hdiff := (mul_eq_zero.mp hm).resolve_right (pow_ne_zero _ hb)
    exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hbc)

private theorem exists_vieta (B : Bond) :
    ∃ b c : ℂ, B.trace = b + c ∧ B.det = b * c := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (B.trace ^ 2 - 4 * B.det)
    (n := 2) (by decide)
  refine ⟨(B.trace + r) / 2, (B.trace - r) / 2, ?_, ?_⟩
  · ring
  · linear_combination hr / 4

private theorem trace_mul_diagonal_pow (M : Bond) (b c : ℂ) (k : ℕ) :
    (M * Matrix.diagonal (![b, c] : Fin 2 → ℂ) ^ k).trace =
      M 0 0 * b ^ k + M 1 1 * c ^ k := by
  simp only [Matrix.diagonal_pow, Matrix.trace_fin_two, Matrix.mul_diagonal, Pi.pow_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem listTrace_replicate_append (P : Fin 2 → Bond) (i j : ℕ) :
    listTrace P (List.replicate i 0 ++ List.replicate j 1) =
      (P 0 ^ i * P 1 ^ j).trace := by
  simp only [listTrace, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate]

private theorem traceWord_eq_listTrace (P : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    traceWord 2 2 n P w = listTrace P (List.ofFn w) := by
  simp only [traceWord, listTrace, List.map_ofFn, Function.comp_def]

/-- For a nonzero binary trace tensor, vanishing of the three ordered traces
with zero, one, or two copies of the first core forces the second core to be nilpotent. -/
theorem trace_det_second_eq_zero_of_three_traces (P : Fin 2 → Bond) (k : ℕ)
    (hne : traceWord 2 2 (k + 2) P ≠ 0)
    (h₀ : (P 1 ^ (k + 2)).trace = 0)
    (h₁ : (P 0 * P 1 ^ (k + 1)).trace = 0)
    (h₂ : (P 0 ^ 2 * P 1 ^ k).trace = 0) :
    (P 1).trace = 0 ∧ (P 1).det = 0 := by
  by_cases hsing : (P 1).det = 0
  · refine ⟨?_, hsing⟩
    rw [trace_pow_succ_of_det_eq_zero (P 1) hsing (k + 1)] at h₀
    exact (pow_eq_zero_iff (by omega : k + 2 ≠ 0)).mp h₀
  exfalso
  obtain ⟨b, c, ht, hdet⟩ := exists_vieta (P 1)
  have hbcprod : b * c ≠ 0 := by
    rw [← hdet]
    exact hsing
  have hb : b ≠ 0 := fun h => hbcprod (by simp [h])
  have hc : c ≠ 0 := fun h => hbcprod (by simp [h])
  have hp : b ^ (k + 2) + c ^ (k + 2) = 0 := by
    simpa only [trace_pow_eq_add_pow (P 1) b c ht hdet] using h₀
  have hbc : b ≠ c := by
    intro h
    have hdouble : (2 : ℂ) * b ^ (k + 2) = 0 := by
      rw [← h] at hp
      linear_combination hp
    exact (mul_ne_zero (by norm_num) (pow_ne_zero _ hb)) hdouble
  let a := ((P 0 * P 1).trace - c * (P 0).trace) / (b - c)
  let d := (P 0).trace - a
  let e := a * d - (P 0).det
  let Q : Fin 2 → Bond := ![!![a, 1; e, d], Matrix.diagonal ![b, c]]
  have ha : a * (b - c) = (P 0 * P 1).trace - c * (P 0).trace :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hbc)
  have had : a + d = (P 0).trace := by dsimp only [d]; ring
  have hQ₀ : (P 0).trace = (Q 0).trace := by
    rw [Matrix.trace_fin_two (Q 0)]
    exact had.symm
  have hQ₁ : (P 1).trace = (Q 1).trace := by
    simpa only [Q, Matrix.cons_val_one, Matrix.trace_diagonal, Fin.sum_univ_two,
      Matrix.cons_val_zero] using ht
  have hQd₀ : (P 0).det = (Q 0).det := by
    rw [Matrix.det_fin_two (Q 0)]
    change (P 0).det = a * d - 1 * e
    dsimp only [e]
    ring
  have hQd₁ : (P 1).det = (Q 1).det := by
    simpa only [Q, Matrix.cons_val_one, Matrix.det_diagonal, Fin.prod_univ_two,
      Matrix.cons_val_zero] using hdet
  have hQm : (P 0 * P 1).trace = (Q 0 * Q 1).trace := by
    rw [show Q 1 = Matrix.diagonal ![b, c] from rfl]
    simp only [Matrix.trace_fin_two (Q 0 * Matrix.diagonal ![b, c]), Matrix.mul_diagonal]
    change (P 0 * P 1).trace = a * b + d * c
    linear_combination -ha - c * had
  have hlist := listTrace_eq_of_invariants P Q hQ₀ hQ₁ hQd₀ hQd₁ hQm
  have hordered (i j : ℕ) : (P 0 ^ i * P 1 ^ j).trace = (Q 0 ^ i * Q 1 ^ j).trace := by
    rw [← listTrace_replicate_append P, ← listTrace_replicate_append Q]
    exact hlist _
  have hm₁ : (P 0 * P 1 ^ (k + 1)).trace = (Q 0 * Q 1 ^ (k + 1)).trace := by
    simpa only [pow_one] using hordered 1 (k + 1)
  have hscalar₁ : a * b ^ (k + 1) + d * c ^ (k + 1) = 0 := by
    have hm := hm₁.symm.trans h₁
    rw [show Q 1 = Matrix.diagonal ![b, c] from rfl, trace_mul_diagonal_pow] at hm
    exact hm
  have hscalar₂ : (a ^ 2 + e) * b ^ k + (d ^ 2 + e) * c ^ k = 0 := by
    have hm := (hordered 2 k).symm.trans h₂
    rw [show Q 1 = Matrix.diagonal ![b, c] from rfl, trace_mul_diagonal_pow] at hm
    simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at hm
    change (a * a + 1 * e) * b ^ k + (e * 1 + d * d) * c ^ k = 0 at hm
    linear_combination hm
  obtain ⟨hdiag, he | hopp⟩ := scalar_reduction_of_three_traces k hb hc hbc hp hscalar₁ hscalar₂
  · apply hne
    funext w
    change traceWord 2 2 (k + 2) P w = 0
    rw [traceWord_eq_listTrace, hlist]
    have htri (i : Fin 2) : Q i 1 0 = 0 := by
      fin_cases i
      · exact he
      · exact Matrix.diagonal_apply_ne _ (by decide)
    have hchar (i : Fin 2) : b * Q i 1 1 = c * Q i 0 0 := by
      fin_cases i
      · exact hdiag
      · exact mul_comm b c
    apply listTrace_eq_zero_of_upper_triangular Q b c hb htri hchar
    simpa only [List.length_ofFn] using hp
  · have hneg : c = -b := by linear_combination hopp
    have hsign : (-1 : ℂ) ^ (k + 2) = -1 := by
      have hmul : ((-1 : ℂ) ^ (k + 2) + 1) * b ^ (k + 2) = 0 := by
        rw [hneg, show -b = (-1 : ℂ) * b by simp, mul_pow] at hp
        linear_combination hp
      have hz := (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero _ hb)
      linear_combination hz
    have hodd : Odd (k + 2) :=
      (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)).mp hsign
    have ht₀ : (P 0).trace = 0 := by
      rw [← had]
      have hmul : b * (a + d) = 0 := by
        rw [hneg] at hdiag
        linear_combination hdiag
      exact (mul_eq_zero.mp hmul).resolve_left hb
    apply hne
    funext w
    change traceWord 2 2 (k + 2) P w = 0
    rw [traceWord_eq_listTrace]
    exact listTrace_eq_zero_of_odd_of_traceless P ht₀ (ht.trans hopp) (List.ofFn w)
      (by simpa only [List.length_ofFn] using hodd)

private theorem forall_lists_of_length {n : ℕ} {p : List (Fin 2) → Prop}
    (h : ∀ w : Word n, p (List.ofFn w)) (l : List (Fin 2)) (hl : l.length = n) : p l := by
  subst n
  simpa only [List.ofFn_get] using h l.get

/-- At every length at least four, vanishing on all words beginning with `11`
forces the second core to be traceless, singular, and square-zero. -/
theorem trace_det_sq_second_eq_zero_of_prefix_zero (P : Fin 2 → Bond)
    (n : ℕ) (hn : 4 ≤ n) (hne : traceWord 2 2 n P ≠ 0)
    (h : ∀ w : Word (n - 2), (P 1 * P 1 * wordMatrix P w).trace = 0) :
    (P 1).trace = 0 ∧ (P 1).det = 0 ∧ P 1 ^ 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have hlen : k + 2 - 2 = k := by omega
  rw [hlen] at h
  have hlist (l : List (Fin 2)) (hl : l.length = k) :
      (P 1 * P 1 * (l.map P).prod).trace = 0 :=
    forall_lists_of_length (n := k) (p := fun u => (P 1 * P 1 * (u.map P).prod).trace = 0)
      (fun w => by simpa only [List.map_ofFn, Function.comp_def, wordMatrix] using h w) l hl
  have hord (i j : ℕ) (hij : i + j = k) : (P 0 ^ i * P 1 ^ (j + 2)).trace = 0 := by
    have hlen : (List.replicate i (0 : Fin 2) ++ List.replicate j 1).length = k := by
      simpa only [List.length_append, List.length_replicate] using hij
    have hz := hlist _ hlen
    rw [pow_add, ← mul_assoc, Matrix.trace_mul_comm, pow_two]
    simpa only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate] using hz
  have h₀ : (P 1 ^ (k + 2)).trace = 0 := by
    simpa only [pow_zero, one_mul] using hord 0 k (Nat.zero_add k)
  have h₁ : (P 0 * P 1 ^ (k + 1)).trace = 0 := by
    simpa only [pow_one, show k - 1 + 2 = k + 1 by omega] using hord 1 (k - 1) (by omega)
  have h₂ : (P 0 ^ 2 * P 1 ^ k).trace = 0 := by
    simpa only [show k - 2 + 2 = k by omega] using hord 2 (k - 2) (by omega)
  obtain ⟨ht, hd⟩ := trace_det_second_eq_zero_of_three_traces P k hne h₀ h₁ h₂
  exact ⟨ht, hd, pow_two_eq_zero_of_trace_det_eq_zero (P 1) ht hd⟩

/-- The literal two-site Gram corner vanishes exactly when every word with
prefix `11` has zero trace. -/
theorem rawTwo_corner_zero_iff (P : Fin 2 → Bond) (r : ℕ) :
    rawTwo P r (1, 1) (1, 1) = 0 ↔
      ∀ w : Word (r + 2), (P 1 * P 1 * wordMatrix P w).trace = 0 := by
  let F := PeriodicMPSParentIntersection.twoFlattening P r
  constructor
  · intro h w
    have hs : ∑ j : Word (r + 2), Complex.normSq (F (1, 1) j) = 0 := by
      have hre := congrArg Complex.re h
      simpa [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj, F] using hre
    rw [← flattening_entry P r 1 1 w]
    exact Complex.normSq_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (F (1, 1) j))).mp hs w (Finset.mem_univ _)
  · intro h
    have hz (w : Word (r + 2)) : F (1, 1) w = 0 :=
      (flattening_entry P r 1 1 w).trans (h w)
    change (F * F.conjTranspose) (1, 1) (1, 1) = 0
    simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero]

/-- A nonzero periodic binary bond-two trace tensor of length `2 + (r + 2)`
with zero adjacent-ones Gram corner has a square-zero second core. -/
theorem trace_det_sq_second_eq_zero_of_rawTwo_corner_zero (P : Fin 2 → Bond) (r : ℕ)
    (hne : traceWord 2 2 (2 + (r + 2)) P ≠ 0)
    (h : rawTwo P r (1, 1) (1, 1) = 0) :
    (P 1).trace = 0 ∧ (P 1).det = 0 ∧ P 1 ^ 2 = 0 := by
  have hn : 4 ≤ r + 4 := by omega
  have hne' : traceWord 2 2 (r + 4) P ≠ 0 := by
    rw [show r + 4 = 2 + (r + 2) by omega]
    exact hne
  exact trace_det_sq_second_eq_zero_of_prefix_zero P (r + 4) hn hne'
    ((rawTwo_corner_zero_iff P r).mp h)

private theorem nilpotent_gap_product (A B : Bond) (hd : B.det = 0) (gaps : List ℕ) :
    B * (gaps.map (fun g => A ^ g * B)).prod =
      (gaps.map (fun g => (A ^ g * B).trace)).prod • B := by
  induction gaps with
  | nil => simp
  | cons g gaps ih =>
    have h := sandwich (A ^ g) B
    rw [hd, zero_smul, mul_zero, zero_smul, add_zero, sub_zero] at h
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ← mul_assoc, h, smul_mul_assoc, ih, smul_smul]

/-- In the square-zero slice, the trace amplitude of a cyclic word with at least one
second-core letter factors into the scalar traces of its first-core gaps. -/
theorem trace_gap_product (A B : Bond) (hd : B.det = 0) (g : ℕ) (gaps : List ℕ) :
    (((g :: gaps).map (fun j => A ^ j * B)).prod).trace =
      ((g :: gaps).map (fun j => (A ^ j * B).trace)).prod := by
  simp only [List.map_cons, List.prod_cons, mul_assoc, nilpotent_gap_product A B hd]
  rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, mul_comm]

/-- The gap factors satisfy the two-by-two Cayley–Hamilton recurrence. -/
theorem trace_gap_recurrence (A B : Bond) (g : ℕ) :
    (A ^ (g + 2) * B).trace = A.trace * (A ^ (g + 1) * B).trace -
      A.det * (A ^ g * B).trace := by
  rw [pow_add_two, sub_mul, smul_mul_assoc, smul_mul_assoc, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformZeroCorner
