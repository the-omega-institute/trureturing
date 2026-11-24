/- GID: D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Jacobi/NeumannHeatGramianInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Quantum.Jacobi.NeumannHeatGramianJet]
   utility: none
   digest: Sparse centered heat Gramian coefficients identify a positive path of known total length at the sharp finite degree. -/

module

public import D5.S3.Quantum.Jacobi.NeumannHeatGramianJet
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The sharp finite Gramian jet of a positive Neumann path -/

@[expose] public section
namespace D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse

open Finset PowerSeries NeumannHeatGramianJet EndpointMomentTruncation
noncomputable section

private theorem coeff_product (F G : ℝ⟦X⟧) (r : ℕ) :
    coeff r (F * G) = ∑ i ∈ range (r + 1), coeff i F * coeff (r - i) G := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij => coeff ij.1 F * coeff ij.2 G) r

private theorem variance_cubic (H : ℝ⟦X⟧) :
    (∀ d < 3, coeff d (gramian H) = 0) ∧
    coeff 3 (gramian H) = coeff 1 H ^ 2 / 12 := by
  have h (r : ℕ) : coeff (r + 1) (gramian H) =
      (∑ i ∈ range (r + 1), coeff i H * coeff (r - i) H) / (r + 1 : ℝ) -
      ∑ i ∈ range (r + 1), (coeff i H / (i + 1 : ℝ)) *
        (coeff (r - i) H / (↑(r - i) + 1 : ℝ)) := by
    simp [gramian, coeff_succ_X_mul, timeAverage, coeff_product]
  constructor
  · intro d hd
    obtain rfl | rfl | rfl : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    · simp [gramian]
    · norm_num [h 0, sum_range_succ]
    · norm_num [h 1, sum_range_succ] <;> ring
  · norm_num [h 2, sum_range_succ] <;> ring

/-- The first nonzero coefficient of the centered physical Gramian is cubic.
Its value depends only on the first edge, even with a constant heat offset. -/
theorem cubic_coefficient {n : ℕ} (p : Path n) (c : ℝ) (hn : 0 < n) :
    (∀ d < 3, coeff d (gramian (p.heat c)) = 0) ∧
    coeff 3 (gramian (p.heat c)) = 4 / (3 * p.edge 0 ^ 6) := by
  obtain ⟨hbelow, hcubic⟩ := variance_cubic (p.heat c)
  have he : 0 < p.edge 0 := by simpa [Path.edge, hn] using p.positive ⟨0, hn⟩
  have hm : p.moment 1 = 4 / p.edge 0 ^ 3 := by
    unfold Path.moment
    have hn₀ : 0 < n + 1 := by omega
    norm_num [amplitude, Option.elim, hn₀, Path.diagonal, Path.mass]
    field_simp [he.ne']
    <;> ring
  refine ⟨hbelow, ?_⟩
  rw [hcubic]
  norm_num [Path.heat, coeff_C, hm]
  field_simp [he.ne']
  <;> ring

/-- The coefficient read at edge index k, counting from the measured endpoint. -/
def readoutDegree (k : ℕ) : ℕ := if k = 0 then 3 else 2 * k + 2

private theorem first_unequal_readout {n k : ℕ} (p q : Path n) (c e : ℝ) (hk : k < n)
    (hprefix : ∀ i < k, p.edge i = q.edge i) (hne : p.edge k ≠ q.edge k) :
    (∀ d < readoutDegree k, coeff d (gramian (p.heat c)) = coeff d (gramian (q.heat e))) ∧
    coeff (readoutDegree k) (gramian (p.heat c)) ≠
      coeff (readoutDegree k) (gramian (q.heat e)) := by
  by_cases hz : k = 0
  · subst k
    obtain ⟨hp, hp₃⟩ := cubic_coefficient p c hk
    obtain ⟨hq, hq₃⟩ := cubic_coefficient q e hk
    simp only [readoutDegree, if_pos rfl]
    refine ⟨fun d hd => (hp d hd).trans (hq d hd).symm, ?_⟩
    rw [hp₃, hq₃]
    intro h
    apply hne
    have hpos (a : Path n) : 0 < a.edge 0 := by
      simpa [Path.edge, hk] using a.positive ⟨0, hk⟩
    have hpow : p.edge 0 ^ 6 = q.edge 0 ^ 6 := by
      have hcancel := (div_eq_div_iff (by positivity) (by positivity)).mp h
      linarith
    exact (pow_left_strictMonoOn₀ (by decide : (6 : ℕ) ≠ 0)).injOn
      (hpos p).le (hpos q).le hpow
  · obtain ⟨hbelow, _, hgap⟩ := first_reveal p q k c e (Nat.pos_of_ne_zero hz) hk hprefix hne
    simpa only [readoutDegree, if_neg hz, map_sub, sub_eq_zero] using And.intro hbelow hgap

private theorem eq_of_prefix_and_total {n : ℕ} (p q : Path n)
    (htotal : ∑ i, p.length i = ∑ i, q.length i)
    (hprefix : ∀ i, i + 1 < n → p.edge i = q.edge i) : p = q := by
  have hlength : p.length = q.length := by
    funext i
    cases n with
    | zero => exact i.elim0
    | succ m =>
      have hinit (j : Fin m) : p.length j.castSucc = q.length j.castSucc := by
        simpa [Path.edge, j.castSucc.isLt] using hprefix j.val (by omega)
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at htotal
      have hlast : p.length (Fin.last m) = q.length (Fin.last m) := by
        rw [sum_congr rfl (fun j _ => hinit j)] at htotal
        exact add_left_cancel htotal
      exact Fin.lastCases hlast hinit i
  cases p
  cases q
  cases hlength
  rfl

/-- At equal total length the sparse readouts determine the whole ordered path.
Each response can carry its own unknown constant offset. -/
theorem sparse_injective {n : ℕ} (p q : Path n) (c e : ℝ)
    (htotal : ∑ i, p.length i = ∑ i, q.length i)
    (hread : ∀ k, k + 1 < n →
      let d := readoutDegree k
      coeff d (gramian (p.heat c)) = coeff d (gramian (q.heat e))) : p = q := by
  apply eq_of_prefix_and_total p q htotal
  intro i hi
  by_contra hne
  have h : ∃ k, p.edge k ≠ q.edge k := ⟨i, hne⟩
  have hk := Nat.find_min' h hne
  have hprefix : ∀ j < Nat.find h, p.edge j = q.edge j := by
    intro j hj
    exact not_ne_iff.mp (Nat.find_min h hj)
  exact (first_unequal_readout p q c e (by omega) hprefix (Nat.find_spec h)).2
    (hread (Nat.find h) (by omega))

/-- Least full-jet degree at a fixed positive total length. -/
def jetCutoff (n : ℕ) : ℕ := if n ≤ 1 then 0 else readoutDegree (n - 2)

private theorem readout_le_cutoff {n k : ℕ} (hk : k + 1 < n) :
    readoutDegree k ≤ jetCutoff n := by
  unfold jetCutoff
  rw [if_neg (by omega)]
  unfold readoutDegree
  split <;> split <;> omega

private theorem swap_last_pair (m : ℕ) (L : ℝ) (hL : 0 < L) :
    ∃ p q : Path (m + 2), (∑ i, p.length i) = L ∧ (∑ i, q.length i) = L ∧
      (∀ i < m, p.edge i = q.edge i) ∧ p.edge m ≠ q.edge m := by
  let a := L / (↑m + 3)
  have ha : 0 < a := by dsimp [a]; positivity
  let last := Fin.last (m + 1)
  let penult := (Fin.last m).castSucc
  have hpos (i : Fin (m + 2)) : 0 < a + (if i = last then a else 0) := by
    split <;> positivity
  let p : Path (m + 2) := ⟨fun i => a + (if i = last then a else 0), hpos⟩
  let swap := Equiv.swap penult last
  let q : Path (m + 2) := ⟨fun i => p.length (swap i), fun i => p.positive (swap i)⟩
  have hp : (∑ i, p.length i) = L := by
    simp [p, sum_add_distrib, a]
    field_simp
    <;> ring
  have hq : (∑ i, q.length i) = L := (Equiv.sum_comp swap p.length).trans hp
  have hlast : penult ≠ last := by
    intro h
    have := congrArg Fin.val h
    change m = m + 1 at this
    omega
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · intro i hi
    have hin : i < m + 2 := by omega
    have h₁ : (⟨i, hin⟩ : Fin (m + 2)) ≠ penult := by
      intro h
      have : i = m := congrArg Fin.val h
      omega
    have h₂ : (⟨i, hin⟩ : Fin (m + 2)) ≠ last := by
      intro h
      have : i = m + 1 := congrArg Fin.val h
      omega
    simp [Path.edge, hin, q, swap, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  · simp [Path.edge, show m < m + 2 by omega, q, swap, p, hlast, ← show
        (⟨m, by omega⟩ : Fin (m + 2)) = penult from rfl, ha.ne']

/-- Full jets through degree d distinguish all positive paths of a given positive
total exactly at and above the cutoff. The two offsets are independently arbitrary. -/
theorem finite_jet_injective_iff (n d : ℕ) (L : ℝ) (hL : 0 < L) (c e : ℝ) :
    (∀ p q : Path n, (∑ i, p.length i) = L → (∑ i, q.length i) = L →
      (∀ j ≤ d, coeff j (gramian (p.heat c)) = coeff j (gramian (q.heat e))) → p = q) ↔
    jetCutoff n ≤ d := by
  constructor
  · intro hinj
    by_contra! hd
    have hn : 2 ≤ n := by
      by_contra! hn
      simp [jetCutoff, show n ≤ 1 by omega] at hd
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hd' : d < readoutDegree m := by simpa [jetCutoff] using hd
    obtain ⟨p, q, hp, hq, hprefix, hne⟩ := swap_last_pair m L hL
    have hbelow := (first_unequal_readout p q c e (by omega) hprefix hne).1
    exact hne (congrArg (fun p : Path (m + 2) => p.edge m)
      (hinj p q hp hq (fun j hj => hbelow j (hj.trans_lt hd'))))
  · intro hd p q hp hq hjet
    exact sparse_injective p q c e (hp.trans hq.symm)
      (fun k hk => hjet _ ((readout_le_cutoff hk).trans hd))

end
end D5.S3.Quantum.Jacobi.NeumannHeatGramianInverse
