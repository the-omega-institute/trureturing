/- GID: D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
   mirror-E: none(waiver:formal-unit-only)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Convergence of the strict tournament path flip threshold by finite-host amplification. -/

import D5.S3.ConceptDynamics.GraphIrregularity.LinkIrregularTournamentExistence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic

/-! Finite path transfers, defect propagation and source-faithful convergence of the flip threshold. -/

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
def ArcPreserving {V : Type*} (R : V → V → Prop) (w : List Bool)
    (φ : Fin (w.length + 1) → V) : Prop :=
  ∀ i : Fin w.length,
    if w[i] then R (φ i.castSucc) (φ i.succ) else R (φ i.succ) (φ i.castSucc)

noncomputable def homCount {V : Type*} (R : V → V → Prop) (w : List Bool) : ℕ :=
  Nat.card {φ : Fin (w.length + 1) → V // ArcPreserving R w φ}

noncomputable def homDensity {V : Type*} [Fintype V] (R : V → V → Prop) (w : List Bool) : ℝ :=
  (homCount R w : ℝ) / (Fintype.card V : ℝ) ^ (w.length + 1)

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

private theorem flips_snoc (w : List Bool) (b : Bool) :
    flips (w ++ [b]) = flips w +
      (match w.getLast? with | none => 0 | some a => if a = b then 0 else 1) := by
  induction w with
  | nil => simp [flips]
  | cons a w ih =>
    cases w with
    | nil => simp [flips]
    | cons c w => simp_all [flips, Nat.add_assoc]

private theorem flips_reverse (w : List Bool) : flips w.reverse = flips w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.reverse_cons, flips_snoc, ih, List.getLast?_reverse]
    cases w with
    | nil => simp [flips]
    | cons b w => simp [flips, eq_comm, Nat.add_comm]

private theorem flips_not (w : List Bool) : flips (w.map Bool.not) = flips w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases w with
    | nil => simp [flips]
    | cons b w => simpa [flips] using ih

private theorem flips_append_le (u v : List Bool) :
    flips (u ++ v) ≤ flips u + flips v + 1 := by
  induction u with
  | nil => simp [flips]
  | cons a u ih =>
    cases u with
    | nil =>
      cases v with
      | nil => simp [flips]
      | cons b v => simp only [List.cons_append, List.nil_append, flips]; split_ifs <;> omega
    | cons b u =>
      simp only [List.cons_append, flips] at *
      omega

private theorem flips_append_cost (u v : List Bool) :
    flips (u ++ v) ≤ flips u + v.length := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    rw [← List.append_assoc, flips_snoc]
    have h : (match (u ++ v).getLast? with
      | none => 0 | some a => if a = b then 0 else 1) ≤ 1 := by
      split <;> (try split_ifs) <;> omega
    simp only [List.length_append, List.length_singleton]
    omega

/-- Concatenation of the indicated number of identical words. -/
def repeatWord (w : List Bool) (m : ℕ) : List Bool := (List.replicate m w).flatten

private theorem repeatWord_length (w : List Bool) (m : ℕ) :
    (repeatWord w m).length = m * w.length := by
  simp [repeatWord, List.length_flatten, List.sum_replicate]

private theorem repeatWord_flips (w : List Bool) (m : ℕ) :
    flips (repeatWord w m) ≤ m * (flips w + 1) := by
  induction m with
  | zero => simp [repeatWord, flips]
  | succ m ih =>
    have h := flips_append_le w (repeatWord w m)
    change flips (w ++ repeatWord w m) ≤ _
    rw [Nat.succ_mul]
    omega

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
  simpa only [transfer, reflect, List.map_map, List.map_reverse, Function.comp_def,
    step_not] using (Matrix.transpose_list_prod (w.map (step A))).symm

theorem reflected_pair_transfer (A : Matrix V V ℝ) (w : List Bool) :
    transfer A (w ++ reflect w) = transfer A w * (transfer A w)ᵀ := by
  rw [transfer_append, transfer_reflect]

omit [DecidableEq V] in
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

omit [DecidableEq V] in
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

omit [DecidableEq V] in
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

omit [DecidableEq V] in
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


private theorem flips_reflect (w : List Bool) : flips (reflect w) = flips w := by
  rw [reflect, flips_not, flips_reverse]

private theorem transfer_repeatWord (A : Matrix V V ℝ) (w : List Bool) (m : ℕ) :
    transfer A (repeatWord w m) = (transfer A w) ^ m := by
  simp [transfer, repeatWord, List.map_flatten, List.prod_flatten]

omit [Fintype V] [DecidableEq V] in
private theorem arcPreserving_cons (R : V → V → Prop) (b : Bool) (w : List Bool)
    (φ : Fin ((b :: w).length + 1) → V) :
    ArcPreserving R (b :: w) φ ↔
      (if b then R (φ 0) (φ 1) else R (φ 1) (φ 0)) ∧
      ArcPreserving R w (fun i => φ i.succ) := by
  simp [ArcPreserving, Fin.forall_fin_succ]
  tauto

open scoped Classical in
private theorem row_transfer_count (R : V → V → Prop) (w : List Bool) (i : V) :
    (∑ j, transfer (normalizedArcMatrix R) w i j) =
      (2 / (Fintype.card V : ℝ)) ^ w.length *
        ∑ φ : Fin w.length → V, if ArcPreserving R w (Fin.cons i φ) then 1 else 0 := by
  classical
  induction w generalizing i with
  | nil => simp [transfer, Matrix.one_apply, ArcPreserving]
  | cons b w ih =>
    change (∑ j, (step (normalizedArcMatrix R) b *
      transfer (normalizedArcMatrix R) w) i j) =
        (2 / (Fintype.card V : ℝ)) ^ (w.length + 1) *
          ∑ φ : Fin (w.length + 1) → V,
            if ArcPreserving R (b :: w) (Fin.cons i φ) then 1 else 0
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih]
    rw [← (Fin.consEquiv fun _ : Fin (w.length + 1) => V).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk]
    simp_rw [arcPreserving_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [pow_succ']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : step (normalizedArcMatrix R) b i j =
        if (if b then R i j else R j i) then 2 / (Fintype.card V : ℝ) else 0 := by
      cases b <;> simp [step, normalizedArcMatrix, Matrix.transpose_apply]
    rw [hs]
    by_cases h : if b then R i j else R j i
    · simp [h, mul_assoc]
    · simp [h]

/-- Matrix multiplication sums over every map, retaining vertex collisions. -/
theorem mass_transfer_eq_density (R : V → V → Prop) [Nonempty V] (w : List Bool) :
    mass (transfer (normalizedArcMatrix R) w) =
      (2 : ℝ) ^ w.length * homDensity R w := by
  classical
  have hN : (Fintype.card V : ℝ) ≠ 0 := by positivity
  have hc : (homCount R w : ℝ) =
      ∑ φ : Fin (w.length + 1) → V, if ArcPreserving R w φ then 1 else 0 := by
    rw [homCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    rfl
  have hsum : (∑ i, ∑ j, transfer (normalizedArcMatrix R) w i j) =
      (2 / (Fintype.card V : ℝ)) ^ w.length * (homCount R w : ℝ) := by
    simp_rw [row_transfer_count]
    rw [← Finset.mul_sum, hc,
      ← (Fin.consEquiv fun _ : Fin (w.length + 1) => V).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk]
    rfl
  unfold mass homDensity
  rw [hsum, div_pow, pow_succ]
  field_simp

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

omit [DecidableEq V] in
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

/-- Any finite defect propagates to every sufficiently large length. -/
theorem defect_propagation (w : List Bool) (hk : 0 < w.length) (hbad : ¬ TAS w)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n → 0 < n →
      (f n : ℝ) / (n : ℝ) < ((flips w : ℝ) + 1) / (w.length : ℝ) + δ := by
  classical
  simp only [TAS, not_forall, not_le] at hbad
  obtain ⟨N, hN, R, hT, hviol⟩ := hbad
  letI : NeZero N := ⟨by omega⟩
  let A := normalizedArcMatrix R
  let B := transfer A w
  let q := mass B
  have hq : 1 < q := by
    have hmul := mul_lt_mul_of_pos_left hviol (by positivity : (0 : ℝ) < 2 ^ w.length)
    have hid : (2 : ℝ) ^ w.length * (1 / 2 : ℝ) ^ w.length = 1 := by
      rw [← mul_pow]; norm_num
    simpa only [q, B, A, mass_transfer_eq_density, hid] using hmul
  have hNtwo : 1 < N := by
    by_contra h
    have heq : N = 1 := by omega
    subst N
    have hA : A = 0 := by
      ext i j
      have hij : j = i := Subsingleton.elim _ _
      subst j
      simp [A, normalizedArcMatrix, hT.1 i]
    have hB : B = 0 := by
      cases w with
      | nil => simp at hk
      | cons b u => cases b <;> simp [B, transfer, step, hA]
    have hz : q = 0 := by simp [q, hB, mass]
    linarith
  let c : ℝ := ((N : ℝ) - 1) / (N : ℝ)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNtwo
  have hc : 0 < c := div_pos (by linarith) (by positivity)
  have hc1 : c ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < N)).mpr (by linarith)
  let d := 2 * w.length
  have hd : 0 < d := by dsimp [d]; omega
  let W := w ++ reflect w
  have hWlen : W.length = d := by simp [W, reflect, d]; omega
  have hWflip : flips W + 1 ≤ 2 * (flips w + 1) := by
    have h := flips_append_le w (reflect w)
    rw [flips_reflect] at h
    dsimp [W]
    omega
  have hpow : 1 < q ^ 2 := by nlinarith
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt hpow).const_mul_atTop (pow_pos hc d)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hlarge.eventually_gt_atTop 1)
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt (div_pos hδ (by positivity : (0 : ℝ) < d))
  refine ⟨max (d * M) (J + 1), ?_⟩
  intro n hn hnpos
  let m := n / d
  let s := n % d
  have hs : s < d := Nat.mod_lt n hd
  have hdecomp : d * m + s = n := by
    dsimp [m, s]
    nlinarith [Nat.mod_add_div n d]
  have hm : M ≤ m := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith [le_max_left (d * M) (J + 1)])
  obtain ⟨v, hvlen, hv⟩ := tournament_padding R hT (repeatWord W m) s
  have hamp : (q ^ 2) ^ m ≤ mass (transfer A (repeatWord W m)) := by
    simpa only [transfer_repeatWord, W, reflected_pair_transfer, B, q, pow_mul] using
      reflected_power_amplification B hq m
  have hmass : 1 < mass (transfer A (repeatWord W m ++ v)) := by
    have hcs : c ^ d ≤ c ^ s := pow_le_pow_of_le_one hc.le hc1 (by omega)
    have hbase : 1 < c ^ d * (q ^ 2) ^ m := hM m hm
    have hstep : c ^ s * (q ^ 2) ^ m ≤ c ^ s * mass (transfer A (repeatWord W m)) :=
      mul_le_mul_of_nonneg_left hamp (pow_nonneg hc.le s)
    have htail : c ^ s * mass (transfer A (repeatWord W m)) ≤
        mass (transfer A (repeatWord W m ++ v)) := by
      simpa only [A, c, Fintype.card_fin] using hv
    exact hbase.trans_le
      ((mul_le_mul_of_nonneg_right hcs (by positivity)).trans (hstep.trans htail))
  let u := repeatWord W m ++ v
  have hulen : u.length = n := by
    simp only [u, List.length_append, repeatWord_length, hWlen, hvlen]
    nlinarith
  have hubad : ¬ TAS u := by
    intro htas
    have ht := htas N hN R hT
    have ht' := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 ^ u.length)
    have hid : (2 : ℝ) ^ u.length * (1 / 2 : ℝ) ^ u.length = 1 := by
      rw [← mul_pow]; norm_num
    rw [hid, ← mass_transfer_eq_density R u] at ht'
    exact (not_le_of_gt hmass) ht'
  have huflip : flips u ≤ 2 * m * (flips w + 1) + s := by
    have h₁ := flips_append_cost (repeatWord W m) v
    have h₂ := repeatWord_flips W m
    have h₃ := Nat.mul_le_mul_left m hWflip
    rw [hvlen] at h₁
    dsimp [u]
    nlinarith
  have hf : f n ≤ 2 * m * (flips w + 1) + s := by
    have h := f_le_flips_of_not_tas hubad
    rw [hulen] at h
    exact h.trans huflip
  have hkr : (0 : ℝ) < w.length := by exact_mod_cast hk
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hsn : (s : ℝ) ≤ d := by exact_mod_cast (le_of_lt hs)
  have hfn : (f n : ℝ) ≤ 2 * (m : ℝ) * ((flips w : ℝ) + 1) + s := by exact_mod_cast hf
  have hdn : (n : ℝ) = 2 * (w.length : ℝ) * m + s := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) hdecomp
    push_cast at h
    dsimp [d] at h
    push_cast at h
    linarith
  have hscale : ((flips w : ℝ) + 1) / (w.length : ℝ) * n =
      2 * (m : ℝ) * ((flips w : ℝ) + 1) +
        ((flips w : ℝ) + 1) / (w.length : ℝ) * s := by
    rw [hdn]
    field_simp
  have hmain : (f n : ℝ) ≤ ((flips w : ℝ) + 1) / (w.length : ℝ) * n + d := by
    have hnonneg : 0 ≤ ((flips w : ℝ) + 1) / (w.length : ℝ) * s := by positivity
    linarith
  have hsmall : (d : ℝ) / (n : ℝ) < δ := by
    have hJ' : 1 / (n : ℝ) < δ / (d : ℝ) := by
      apply lt_of_le_of_lt _ hJ
      apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (J : ℝ) + 1)
      exact_mod_cast (show J + 1 ≤ n by omega)
    calc
      (d : ℝ) / (n : ℝ) = (1 / (n : ℝ)) * d := by ring
      _ < (δ / (d : ℝ)) * d := mul_lt_mul_of_pos_right hJ' hdr
      _ = δ := div_mul_cancel₀ δ (ne_of_gt hdr)
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hmain hnr.le) _
  rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hnr)]
  linarith

/-- The source maximum has a limit over all positive lengths, with no propagation premise. -/
theorem fullConvergence : FullConvergence := by
  let Bad : ℕ → ℕ → Prop := fun k r =>
    ∃ w : List Bool, w.length = k ∧ flips w = r ∧ ¬ TAS w
  refine ⟨defectLimit Bad, ?_⟩
  apply convergence_of_defect_propagation f Bad f_le
  · intro k _ hk
    exact exists_bad_at_f hk
  · intro k r hk hbad δ hδ
    obtain ⟨w, hw, hr, hb⟩ := hbad
    simpa only [hw, hr] using defect_propagation w (by omega) hb δ hδ

section SourceCorrespondence

/-- The paper's two integer signs. -/
abbrev Sign := {z : ℤ // z = -1 ∨ z = 1}

private def signEquiv : Bool ≃ Sign where
  toFun b := if b then ⟨1, Or.inr rfl⟩ else ⟨-1, Or.inl rfl⟩
  invFun z := decide (z.val = 1)
  left_inv b := by cases b <;> decide
  right_inv z := by
    apply Subtype.ext
    rcases z.property with h | h <;> simp [h]

private theorem sign_mul (a b : Bool) :
    (if (signEquiv a : ℤ) * (signEquiv b : ℤ) = -1 then (1 : ℕ) else 0) =
      if a = b then 0 else 1 := by
  cases a <;> cases b <;> decide

private theorem sign_pos (a : Bool) : (signEquiv a : ℤ) = 1 ↔ a = true := by
  cases a <;> decide

/-- Every sign vector and every list of the given length correspond bijectively. -/
def signVectors (k : ℕ) : {w : List Bool // w.length = k} ≃ (Fin k → Sign) :=
  (Equiv.vectorEquivFin Bool k).trans (Equiv.piCongrRight fun _ => signEquiv)

/-- Internal vertices are counted by the source condition that adjacent signs multiply to -1. -/
def sourceFlips {k : ℕ} (x : Fin k → Sign) : ℕ :=
  ∑ i : Fin k, if h : i.val + 1 < k then
    (if (x i : ℤ) * (x ⟨i.val + 1, h⟩ : ℤ) = -1 then 1 else 0) else 0

/-- The source arc condition on integer sign vectors, independently of list encoding. -/
def SourceArcPreserving {k : ℕ} {V : Type*} (R : V → V → Prop) (x : Fin k → Sign)
    (φ : Fin (k + 1) → V) : Prop :=
  ∀ i : Fin k, if (x i : ℤ) = 1 then R (φ i.castSucc) (φ i.succ)
    else R (φ i.succ) (φ i.castSucc)

noncomputable def sourceDensity {k : ℕ} {V : Type*} [Fintype V]
    (R : V → V → Prop) (x : Fin k → Sign) : ℝ :=
  (Nat.card {φ : Fin (k + 1) → V // SourceArcPreserving R x φ} : ℝ) /
    (Fintype.card V : ℝ) ^ (k + 1)

/-- All finite nonempty host types are included, without a prescribed enumeration. -/
def SourceTAS {k : ℕ} (x : Fin k → Sign) : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (R : V → V → Prop),
    IsTournament R → sourceDensity R x ≤ (1 / 2 : ℝ) ^ k

private theorem flips_eq_index_sum (w : List Bool) :
    flips w = ∑ i : Fin w.length,
      if h : i.val + 1 < w.length then
        (if w[i.val] = w[i.val + 1] then 0 else 1) else 0 := by
  induction w with
  | nil => simp [flips]
  | cons a w ih =>
    cases w with
    | nil => simp [flips, Fin.sum_univ_succ]
    | cons b w =>
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at *
      simp [flips, ih, Nat.add_assoc]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i.val + 2 ≤ w.length
      · have h' : i.val + 3 < w.length + 2 := by omega
        simp [h, h']
      · have h' : ¬ i.val + 3 < w.length + 2 := by omega
        simp [h, h']

private theorem signVectors_apply (w : List Bool) (i : Fin w.length) :
    signVectors w.length ⟨w, rfl⟩ i = signEquiv w[i.val] := rfl

private theorem sourceFlips_eq {k : ℕ} (w : List Bool) (hw : w.length = k) :
    sourceFlips (signVectors k ⟨w, hw⟩) = flips w := by
  subst k
  rw [flips_eq_index_sum]
  unfold sourceFlips
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val + 1 < w.length
  · simp only [dif_pos h, signVectors_apply]
    exact sign_mul _ _
  · simp only [dif_neg h]

private theorem sourceDensity_eq {k : ℕ} {V : Type*} [Fintype V]
    (R : V → V → Prop) (w : List Bool) (hw : w.length = k) :
    sourceDensity R (signVectors k ⟨w, hw⟩) = homDensity R w := by
  subst k
  have ha (φ : Fin (w.length + 1) → V) :
      SourceArcPreserving R (signVectors w.length ⟨w, rfl⟩) φ ↔ ArcPreserving R w φ := by
    unfold SourceArcPreserving ArcPreserving
    apply forall_congr'
    intro i
    simp only [signVectors_apply]
    simp only [sign_pos]
    rfl
  unfold sourceDensity homDensity homCount
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight ha)

private theorem homDensity_reindex {U V : Type*} [Fintype U] [Fintype V]
    (e : U ≃ V) (R : V → V → Prop) (w : List Bool) :
    homDensity (fun i j : U => R (e i) (e j)) w = homDensity R w := by
  let E : {φ : Fin (w.length + 1) → U // ArcPreserving (fun i j => R (e i) (e j)) w φ} ≃
      {φ : Fin (w.length + 1) → V // ArcPreserving R w φ} := {
    toFun := fun φ => ⟨fun i => e (φ.val i), φ.property⟩
    invFun := fun φ => ⟨fun i => e.symm (φ.val i), by simpa [ArcPreserving] using φ.property⟩
    left_inv := fun φ => by apply Subtype.ext; funext i; exact e.symm_apply_apply _
    right_inv := fun φ => by apply Subtype.ext; funext i; exact e.apply_symm_apply _ }
  have hc := Nat.card_congr E
  simp only [homDensity, homCount, hc, Fintype.card_congr e]

/-- A TAS list satisfies the same density bound in every arbitrary finite nonempty host. -/
theorem tas_arbitrary_host {V : Type*} [Fintype V] [Nonempty V]
    (w : List Bool) (h : TAS w) (R : V → V → Prop) (hT : IsTournament R) :
    homDensity R w ≤ (1 / 2 : ℝ) ^ w.length := by
  let e := (Fintype.equivFin V).symm
  have hT' : IsTournament (fun i j : Fin (Fintype.card V) => R (e i) (e j)) := by
    constructor
    · exact fun i => hT.1 _
    · intro i j hij
      exact hT.2 _ _ (fun heq => hij (e.injective heq))
  have ht := h (Fintype.card V) Fintype.card_pos _ hT'
  rwa [homDensity_reindex e R w] at ht

private theorem sourceTAS_iff {k : ℕ} (w : List Bool) (hw : w.length = k) :
    SourceTAS (signVectors k ⟨w, hw⟩) ↔ TAS w := by
  subst k
  constructor
  · intro h N hN R hR
    letI : NeZero N := ⟨by omega⟩
    simpa only [sourceDensity_eq] using h (Fin N) R hR
  · intro h V _ _ R hR
    rw [sourceDensity_eq]
    exact tas_arbitrary_host w h R hR

/-- The source threshold uses integer sign vectors and arbitrary finite hosts. -/
noncomputable def sourceThresholds (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (k + 1)).filter fun m =>
    ∀ x : Fin k → Sign, sourceFlips x < m → SourceTAS x

private theorem sourceThresholds_eq (k : ℕ) : sourceThresholds k = thresholds k := by
  classical
  ext m
  simp only [sourceThresholds, thresholds, Finset.mem_filter]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    intro w hw hf
    apply (sourceTAS_iff w hw).mp
    apply h (signVectors k ⟨w, hw⟩)
    rwa [sourceFlips_eq]
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_⟩
    intro x hf
    obtain ⟨⟨w, hw⟩, rfl⟩ := (signVectors k).surjective x
    apply (sourceTAS_iff w hw).mpr
    apply h w hw
    rwa [sourceFlips_eq] at hf

private theorem sourceThresholds_nonempty (k : ℕ) : (sourceThresholds k).Nonempty := by
  rw [sourceThresholds_eq]
  exact thresholds_nonempty k

/-- The independently defined exact source maximum, including saturation. -/
noncomputable def sourceF (k : ℕ) : ℕ :=
  (sourceThresholds k).max' (sourceThresholds_nonempty k)

/-- Both encodings have exactly the same maximum at every length. -/
theorem sourceF_eq_f (k : ℕ) : sourceF k = f k := by
  simp only [sourceF, f, sourceThresholds_eq]

/-- The literal source convergence assertion on sign vectors and arbitrary finite hosts. -/
def SourceFullConvergence : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1 ≤ K ∧
    ∀ k : ℕ, K ≤ k → |(sourceF k : ℝ) / (k : ℝ) - L| < ε

/-- Question 6.1, with its original maximum and every positive length. -/
theorem source_fullConvergence : SourceFullConvergence := by
  simpa only [SourceFullConvergence, FullConvergence, sourceF_eq_f] using fullConvergence

end SourceCorrespondence

end D5.S3.Combinatorics.ExtremalDensity.ChenLinFlipLimit
