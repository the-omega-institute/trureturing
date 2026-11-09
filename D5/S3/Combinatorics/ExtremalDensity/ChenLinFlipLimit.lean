/- GID: D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   mirror-E: none(waiver:formal-unit-only)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Finite tournament path transfer, reflection, padding and the defect-spectrum convergence criterion. -/

import D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! Finite path transfers and the asymptotic defect criterion. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit

open Filter Matrix

abbrev IsTournament {V : Type*} (R : V → V → Prop) : Prop :=
  D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence.IsTournament R

/-- True encodes a forward edge, false a backward edge. -/
def flips : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: w => (if a = b then 0 else 1) + flips (b :: w)

/-- All vertex maps are allowed; only the arc conditions constrain a map. -/
def ArcPreserving {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool)
    (φ : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ i : Fin w.length,
    if w[i] then R (φ i.castSucc) (φ i.succ) else R (φ i.succ) (φ i.castSucc)

noncomputable def homCount {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool) : ℕ :=
  Nat.card {φ : Fin (w.length + 1) → Fin N // ArcPreserving R w φ}

noncomputable def homDensity {N : ℕ} (R : Fin N → Fin N → Prop) (w : List Bool) : ℝ :=
  (homCount R w : ℝ) / (N : ℝ) ^ (w.length + 1)

def TAS (w : List Bool) : Prop :=
  ∀ N : ℕ, 0 < N → ∀ R : Fin N → Fin N → Prop,
    IsTournament R → homDensity R w ≤ (1 / 2 : ℝ) ^ w.length

noncomputable def thresholds (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (k + 1)).filter fun m =>
    ∀ w : List Bool, w.length = k → flips w < m → TAS w

private theorem thresholds_nonempty (k : ℕ) : (thresholds k).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [thresholds]

/-- The source's exact maximum, including its strict flip threshold. -/
noncomputable def f (k : ℕ) : ℕ := (thresholds k).max' (thresholds_nonempty k)

theorem f_le (k : ℕ) : f k ≤ k := by
  classical
  have hm := (thresholds k).max'_mem (thresholds_nonempty k)
  have : f k ∈ Finset.range (k + 1) := (Finset.mem_filter.mp hm).1
  exact Nat.le_of_lt_succ (Finset.mem_range.mp this)

theorem tas_of_flips_lt {k : ℕ} {w : List Bool} (hlen : w.length = k)
    (hflip : flips w < f k) : TAS w := by
  classical
  have hm := (thresholds k).max'_mem (thresholds_nonempty k)
  exact (Finset.mem_filter.mp hm).2 w hlen hflip

theorem f_le_flips_of_not_tas {w : List Bool} (hbad : ¬ TAS w) :
    f w.length ≤ flips w := by
  by_contra h
  exact hbad (tas_of_flips_lt rfl (by omega))

theorem exists_bad_at_f {k : ℕ} (hlt : f k < k) :
    ∃ w : List Bool, w.length = k ∧ flips w = f k ∧ ¬ TAS w := by
  classical
  have hnot : f k + 1 ∉ thresholds k := by
    intro hmem
    have hle := (thresholds k).le_max' (f k + 1) hmem
    change f k + 1 ≤ f k at hle
    omega
  have hex : ¬ ∀ w : List Bool, w.length = k → flips w < f k + 1 → TAS w := by
    intro h
    apply hnot
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), h⟩
  push Not at hex
  obtain ⟨w, hlen, hflips, hbad⟩ := hex
  refine ⟨w, hlen, ?_, hbad⟩
  have hmin := f_le_flips_of_not_tas hbad
  rw [hlen] at hmin
  omega

/-- Its value at zero is immaterial: the quantifiers below only use positive lengths. -/
def FullConvergence : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧
    ∀ k : ℕ, K ≤ k → |(f k : ℝ) / (k : ℝ) - L| < ε

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

def step (A : Matrix V V ℝ) (b : Bool) : Matrix V V ℝ := if b then A else Aᵀ

def transfer (A : Matrix V V ℝ) (w : List Bool) : Matrix V V ℝ :=
  (w.map (step A)).prod

noncomputable def mass (M : Matrix V V ℝ) : ℝ :=
  (∑ i, ∑ j, M i j) / (Fintype.card V : ℝ)

def reflect (w : List Bool) : List Bool := w.reverse.map Bool.not

theorem transfer_append (A : Matrix V V ℝ) (u v : List Bool) :
    transfer A (u ++ v) = transfer A u * transfer A v := by
  simp [transfer]

omit [Fintype V] [DecidableEq V] in
private theorem step_not (A : Matrix V V ℝ) (b : Bool) :
    step A (!b) = (step A b)ᵀ := by
  cases b <;> simp [step]

theorem transfer_reflect (A : Matrix V V ℝ) (w : List Bool) :
    transfer A (reflect w) = (transfer A w)ᵀ := by
  induction w with
  | nil => simp [reflect, transfer]
  | cons b w ih =>
    simp only [reflect, List.reverse_cons, List.map_append, List.map_singleton]
    rw [transfer_append]
    rw [show transfer A [!b] = step A (!b) by simp [transfer]]
    change transfer A (reflect w) * step A (!b) = (step A b * transfer A w)ᵀ
    rw [ih, step_not, Matrix.transpose_mul]

theorem reflected_pair_transfer (A : Matrix V V ℝ) (w : List Bool) :
    transfer A (w ++ reflect w) = transfer A w * (transfer A w)ᵀ := by
  rw [transfer_append, transfer_reflect]

theorem transfer_nonneg (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (w : List Bool) : ∀ i j, 0 ≤ transfer A w i j := by
  induction w with
  | nil => intro i j; simp [transfer, Matrix.one_apply]; split_ifs <;> norm_num
  | cons b w ih =>
    intro i j
    change 0 ≤ (step A b * transfer A w) i j
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg _ (ih x j)
    cases b <;> simp [step, hA]

/-- A nonnegative reflected transfer has average at least the square of the old average. -/
theorem reflected_mass_sq_le (B : Matrix V V ℝ) [Nonempty V] :
    (mass B) ^ 2 ≤ mass (B * Bᵀ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : V => (1 : ℝ)) (fun j : V => ∑ i, B i j)
  have hs : (∑ i, ∑ j, (B * Bᵀ) i j) = ∑ j, (∑ i, B i j) ^ 2 := by
    calc
      _ = ∑ i, ∑ x, ∑ j, B i x * B j x := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        congr 1
        funext x
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        congr 1
        funext i
        simp only [mul_comm]
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  rw [Finset.sum_comm] at hcs
  dsimp [mass]
  rw [hs, div_pow]
  apply (div_le_div_iff₀ (pow_pos hN 2) hN).mpr
  nlinarith

/-- A row-sum identity for the sum of forward and backward one-edge transfers. -/
theorem extension_mass_sum (A M : Matrix V V ℝ) (d : ℝ)
    (hrow : ∀ i, (∑ j, (A i j + A j i)) = d) :
    mass (M * A) + mass (M * Aᵀ) = d * mass M := by
  classical
  unfold mass
  rw [← add_div, ← mul_div_assoc]
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  calc
    _ = ∑ i, ∑ j, ∑ x, M i x * (A x j + A j x) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ i, ∑ x, M i x * (∑ j, (A x j + A j x)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp_rw [hrow]; simp only [← Finset.sum_mul]; ring

/-- Padding is chosen from the two signs using their sum; no specified sign is assumed safe. -/
theorem exists_one_edge_padding (A M : Matrix V V ℝ) (c : ℝ)
    (hsum : mass (M * A) + mass (M * Aᵀ) = 2 * c * mass M) :
    ∃ b : Bool, c * mass M ≤ mass (M * step A b) := by
  by_cases h : c * mass M ≤ mass (M * A)
  · exact ⟨true, by simpa [step] using h⟩
  · exact ⟨false, by dsimp [step]; linarith⟩

/-- A bounded remainder can be extended with a rigorously controlled density loss. -/
theorem exists_padding (A : Matrix V V ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ w : List Bool, ∃ b : Bool,
      c * mass (transfer A w) ≤ mass (transfer A (w ++ [b])))
    (w : List Bool) (s : ℕ) :
    ∃ v : List Bool, v.length = s ∧
      c ^ s * mass (transfer A w) ≤ mass (transfer A (w ++ v)) := by
  induction s with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ s ih =>
    obtain ⟨v, hvlen, hv⟩ := ih
    obtain ⟨b, hb⟩ := hstep (w ++ v)
    refine ⟨v ++ [b], by simp [hvlen], ?_⟩
    have hm := mul_le_mul_of_nonneg_left hv hc
    have hpow : c * (c ^ s * mass (transfer A w)) =
        c ^ (s + 1) * mass (transfer A w) := by rw [pow_succ]; ring
    rw [hpow] at hm
    simpa only [List.append_assoc] using hm.trans hb

noncomputable def normalizedArcMatrix (R : V → V → Prop) : Matrix V V ℝ := by
  classical
  exact fun i j => if R i j then 2 / (Fintype.card V : ℝ) else 0

theorem normalizedArcMatrix_complement (R : V → V → Prop) (hT : IsTournament R)
    (i j : V) : normalizedArcMatrix R i j + normalizedArcMatrix R j i =
      if i = j then 0 else 2 / (Fintype.card V : ℝ) := by
  classical
  by_cases hij : i = j
  · subst j; simp [normalizedArcMatrix, hT.1 i]
  · rcases hT.2 i j hij with ⟨h, hn⟩ | ⟨h, hn⟩
    · simp [normalizedArcMatrix, h, hn, hij]
    · simp [normalizedArcMatrix, h, hn, hij]

theorem normalizedArcMatrix_row_sum (R : V → V → Prop) (hT : IsTournament R)
    [Nonempty V] (i : V) :
    (∑ j, (normalizedArcMatrix R i j + normalizedArcMatrix R j i)) =
      2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ) := by
  classical
  simp_rw [normalizedArcMatrix_complement R hT]
  have heq (j : V) : (if i = j then (0 : ℝ) else 2 / (Fintype.card V : ℝ)) =
      2 / (Fintype.card V : ℝ) - (if i = j then 2 / (Fintype.card V : ℝ) else 0) := by
    split_ifs <;> ring
  simp_rw [heq]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- All remainders are covered in the same original finite host. -/
theorem tournament_padding (R : V → V → Prop) (hT : IsTournament R) [Nonempty V]
    (w : List Bool) (s : ℕ) :
    ∃ v : List Bool, v.length = s ∧
      (((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) ^ s *
        mass (transfer (normalizedArcMatrix R) w) ≤
      mass (transfer (normalizedArcMatrix R) (w ++ v)) := by
  have hN : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_pos (α := V)
  apply exists_padding _ _ (div_nonneg (by linarith) (by positivity))
  intro u
  have he := extension_mass_sum (normalizedArcMatrix R)
    (transfer (normalizedArcMatrix R) u)
    (2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ))
    (normalizedArcMatrix_row_sum R hT)
  have he' : mass (transfer (normalizedArcMatrix R) u * normalizedArcMatrix R) +
      mass (transfer (normalizedArcMatrix R) u * (normalizedArcMatrix R)ᵀ) =
      2 * (((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) *
        mass (transfer (normalizedArcMatrix R) u) := by
    rw [he]; ring
  obtain ⟨b, hb⟩ := exists_one_edge_padding _ _ _ he'
  refine ⟨b, ?_⟩
  rw [transfer_append]
  simpa only [transfer, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] using hb

end Transfer

section MomentGrowth

/-- A positive log-convex moment sequence with zeroth moment one dominates its geometric mean. -/
theorem logconvex_geometric_lower (a : ℕ → ℝ) (hzero : a 0 = 1) (hone : 0 < a 1)
    (hcs : ∀ n, (a (n + 1)) ^ 2 ≤ a n * a (n + 2)) :
    ∀ n : ℕ, (a 1) ^ n ≤ a n := by
  have hstep : ∀ n : ℕ, 0 < a n ∧ a 1 * a n ≤ a (n + 1) := by
    intro n
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      have hpos : 0 < a (n + 1) := lt_of_lt_of_le (mul_pos hone ih.1) ih.2
      refine ⟨hpos, ?_⟩
      have hm := mul_le_mul_of_nonneg_right ih.2 hpos.le
      have h := hcs n
      have hprod : a n * (a 1 * a (n + 1)) ≤ a n * a (n + 2) := by
        nlinarith
      exact (mul_le_mul_iff_right₀ ih.1).mp hprod
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    calc
      a 1 ^ (n + 1) = a 1 * a 1 ^ n := by rw [pow_succ'];
      _ ≤ a 1 * a n := mul_le_mul_of_nonneg_left ih hone.le
      _ ≤ a (n + 1) := (hstep n).2

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem semidefinite_cauchy (C : Matrix V V ℝ) (hC : C.PosSemidef)
    (x y : V → ℝ) :
    (x ⬝ᵥ (C *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (C *ᵥ x)) * (y ⬝ᵥ (C *ᵥ y)) := by
  have hsym : y ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ (C *ᵥ y) := by
    simpa using (hC.isHermitian.star_dotProduct_mulVec_comm x y).symm
  have hquad (t : ℝ) := hC.dotProduct_mulVec_nonneg (x + t • y)
  have hnonneg : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (C *ᵥ y)) * (t * t) +
      (2 * (x ⬝ᵥ (C *ᵥ y))) * t + (x ⬝ᵥ (C *ᵥ x)) := by
    intro t
    have h := hquad t
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hsym] at h
    nlinarith
  have hd := discrim_le_zero hnonneg
  simp only [discrim] at hd
  nlinarith

noncomputable def moment (C : Matrix V V ℝ) (x : V → ℝ) (n : ℕ) : ℝ :=
  (x ⬝ᵥ ((C ^ n) *ᵥ x)) / (x ⬝ᵥ x)

private theorem moment_cs (C : Matrix V V ℝ) (hC : C.PosSemidef)
    (x : V → ℝ) (hx : 0 < x ⬝ᵥ x) (n : ℕ) :
    (moment C x (n + 1)) ^ 2 ≤ moment C x n * moment C x (n + 2) := by
  have hc := semidefinite_cauchy (C ^ n) (hC.pow n) x (C *ᵥ x)
  have ht : Cᵀ = C := by simpa using hC.isHermitian.eq
  have hleft : x ⬝ᵥ ((C ^ n) *ᵥ (C *ᵥ x)) = x ⬝ᵥ ((C ^ (n + 1)) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← pow_succ]
  have hright : (C *ᵥ x) ⬝ᵥ ((C ^ n) *ᵥ (C *ᵥ x)) =
      x ⬝ᵥ ((C ^ (n + 2)) *ᵥ x) := by
    calc
      _ = x ⬝ᵥ (C *ᵥ ((C ^ n) *ᵥ (C *ᵥ x))) := by
        rw [dotProduct_comm (C *ᵥ x) _]
        simpa only [ht] using
          (Matrix.dotProduct_transpose_mulVec C x ((C ^ n) *ᵥ (C *ᵥ x))).symm
      _ = _ := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_succ', ← pow_succ]
  rw [hleft, hright] at hc
  unfold moment
  rw [div_pow, div_mul_div_comm]
  simpa only [pow_two] using (div_le_div_iff_of_pos_right (sq_pos_of_pos hx)).mpr hc

/-- The finite-host amplification inequality needed for arbitrary repetition counts. -/
theorem moment_geometric_lower (C : Matrix V V ℝ) (hC : C.PosSemidef)
    (x : V → ℝ) (hx : 0 < x ⬝ᵥ x) (hfirst : 0 < moment C x 1) (n : ℕ) :
    (moment C x 1) ^ n ≤ moment C x n := by
  apply logconvex_geometric_lower (moment C x) _ hfirst (moment_cs C hC x hx) n
  simp [moment, ne_of_gt hx]

private theorem moment_ones (C : Matrix V V ℝ) (n : ℕ) :
    moment C (fun _ => 1) n = mass (C ^ n) := by
  simp [moment, mass, dotProduct, Matrix.mulVec]

theorem mass_power_geometric (C : Matrix V V ℝ) (hC : C.PosSemidef)
    [Nonempty V] (hfirst : 0 < mass C) (n : ℕ) :
    (mass C) ^ n ≤ mass (C ^ n) := by
  have hnorm : (0 : ℝ) < (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) := by
    simpa [dotProduct] using (Nat.cast_pos.mpr (Fintype.card_pos (α := V)) :
      (0 : ℝ) < Fintype.card V)
  have hp : 0 < moment C (fun _ => 1) 1 := by simpa [moment_ones] using hfirst
  simpa only [moment_ones, pow_one] using
    moment_geometric_lower C hC (fun _ => 1) hnorm hp n

/-- A violating finite transfer amplifies exponentially for every natural repetition count. -/
theorem reflected_power_amplification (B : Matrix V V ℝ) [Nonempty V]
    (hB : 1 < mass B) (m : ℕ) :
    (mass B) ^ (2 * m) ≤ mass ((B * Bᵀ) ^ m) := by
  have hC : (B * Bᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose B
  have hs := reflected_mass_sq_le B
  have hpos : 0 < mass (B * Bᵀ) := by nlinarith
  calc
    (mass B) ^ (2 * m) = ((mass B) ^ 2) ^ m := by rw [pow_mul]
    _ ≤ (mass (B * Bᵀ)) ^ m := pow_le_pow_left₀ (sq_nonneg _) hs m
    _ ≤ mass ((B * Bᵀ) ^ m) := mass_power_geometric _ hC hpos m

end MomentGrowth

section DefectSpectrum

/-- Every realizable defect contributes its flip count plus the cost of one join. -/
def defectSpectrum (Bad : ℕ → ℕ → Prop) : Set ℝ :=
  {x | x = 1 ∨ ∃ k r : ℕ, 0 < k ∧ Bad k r ∧ x = ((r : ℝ) + 1) / (k : ℝ)}

noncomputable def defectLimit (Bad : ℕ → ℕ → Prop) : ℝ := sInf (defectSpectrum Bad)

private theorem spectrum_nonempty (Bad : ℕ → ℕ → Prop) :
    (defectSpectrum Bad).Nonempty := ⟨1, Or.inl rfl⟩

private theorem spectrum_bddBelow (Bad : ℕ → ℕ → Prop) :
    BddBelow (defectSpectrum Bad) := by
  refine ⟨0, ?_⟩
  rintro x (rfl | ⟨k, r, hk, _, rfl⟩)
  · norm_num
  · positivity

/-- The analytic final step only needs eventual propagation of each finite defect.
The tournament application must still supply that propagation from its transfer matrices. -/
theorem convergence_of_defect_propagation (F : ℕ → ℕ) (Bad : ℕ → ℕ → Prop)
    (hbounded : ∀ k, F k ≤ k)
    (hwitness : ∀ k, 0 < k → F k < k → Bad k (F k))
    (hpropagate : ∀ k r, 0 < k → Bad k r → ∀ δ : ℝ, 0 < δ →
      ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < n →
        (F n : ℝ) / (n : ℝ) < ((r : ℝ) + 1) / (k : ℝ) + δ) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧ ∀ n : ℕ, K ≤ n →
      |(F n : ℝ) / (n : ℝ) - defectLimit Bad| < ε := by
  intro ε hε
  have hL1 : defectLimit Bad ≤ 1 := csInf_le (spectrum_bddBelow Bad) (Or.inl rfl)
  have hnear := exists_lt_of_csInf_lt (spectrum_nonempty Bad)
    (show defectLimit Bad < defectLimit Bad + ε / 2 by linarith)
  obtain ⟨x, hx, hxlt⟩ := hnear
  have hupper : ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < n →
      (F n : ℝ) / (n : ℝ) < defectLimit Bad + ε := by
    rcases hx with rfl | ⟨k, r, hk, hbad, rfl⟩
    · refine ⟨1, ?_⟩
      intro n _ hn
      have hrat : (F n : ℝ) / (n : ℝ) ≤ 1 :=
        (div_le_one (Nat.cast_pos.mpr hn)).mpr (Nat.cast_le.mpr (hbounded n))
      linarith
    · obtain ⟨K, hK⟩ := hpropagate k r hk hbad (ε / 2) (by linarith)
      exact ⟨K, fun n hn hp => lt_trans (hK n hn hp) (by linarith)⟩
  obtain ⟨Kupper, hKupper⟩ := hupper
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  refine ⟨max Kupper (M + 1), by omega, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hinv : 1 / (n : ℝ) < ε := by
    apply lt_of_le_of_lt _ hM
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (M : ℝ) + 1)
    exact_mod_cast (show M + 1 ≤ n by omega)
  have hlower : defectLimit Bad - ε < (F n : ℝ) / (n : ℝ) := by
    by_cases hlt : F n < n
    · have hm : ((F n : ℝ) + 1) / (n : ℝ) ∈ defectSpectrum Bad :=
        Or.inr ⟨n, F n, hnpos, hwitness n hnpos hlt, rfl⟩
      have hL := csInf_le (spectrum_bddBelow Bad) hm
      rw [add_div] at hL
      change defectLimit Bad ≤ (F n : ℝ) / (n : ℝ) + 1 / (n : ℝ) at hL
      linarith
    · have heq : F n = n := by have := hbounded n; omega
      rw [heq, div_self (ne_of_gt hnreal)]
      linarith
  exact abs_lt.mpr ⟨by linarith, by
    have := hKupper n (by omega) hnpos
    linarith⟩

end DefectSpectrum

/-
The remaining formal bridges to FullConvergence are:
* expansion of transfer as the count of all arc-preserving maps, including collisions;
* preservation of flips by reflection and exact flip/length formulas for repeated words;
* the all-length propagation construction from these bridges and the compiled inequalities;
* its substitution into convergence_of_defect_propagation for the exact maximum f.
No theorem of type FullConvergence is declared here.
-/

end D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
