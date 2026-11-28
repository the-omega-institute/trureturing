/- GID: D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The guarded local moves of the periodic Miao–Fukai Rydberg ladder. -/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import OmegaBuild.Commands

/-! Periodic basis words, projector charge, and the local matrix actions of
Miao and Fukai, arXiv:2611.29351v1, Eqs. (40), (45), and (69)–(70).
Matrix entries use the output word as the row and the input word as the column. -/

compile_only_with_mathlib

@[expose] public section

open scoped BigOperators Matrix

namespace D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves

inductive Rung where
  | e
  | plus
  | minus
  deriving DecidableEq

instance : Fintype Rung where
  elems := {Rung.e, Rung.plus, Rung.minus}
  complete r := by cases r <;> simp

abbrev Word (L : ℕ) := Fin L → Rung

def next {L : ℕ} (j : Fin L) : Fin L := finRotate L j

def prev {L : ℕ} (j : Fin L) : Fin L := (finRotate L).symm j

@[simp] private theorem next_prev {L : ℕ} (j : Fin L) : next (prev j) = j :=
  (finRotate L).apply_symm_apply j

@[simp] private theorem prev_next {L : ℕ} (j : Fin L) : prev (next j) = j :=
  (finRotate L).symm_apply_apply j

theorem next_val {L : ℕ} (j : Fin L) :
    (next j).val = if j.val + 1 < L then j.val + 1 else 0 := by
  cases L with
  | zero => exact Fin.elim0 j
  | succ n =>
    change (finRotate (n + 1) j).val = _
    rw [coe_finRotate]
    by_cases hj : j = Fin.last n
    · subst j
      simp
    · have hv : j.val < n := Fin.val_lt_last hj
      simp [hj, show j.val + 1 < n + 1 by omega]

theorem prev_val {L : ℕ} (j : Fin L) :
    (prev j).val = if j.val = 0 then L - 1 else j.val - 1 := by
  have h := next_val (prev j)
  rw [next_prev] at h
  have hp := (prev j).isLt
  have hj := j.isLt
  split <;> split at h <;> omega

def Blockade {L : ℕ} (w : Word L) : Prop :=
  ∀ j, w j = .e ∨ w (next j) = .e

abbrev Config (L : ℕ) := {w : Word L // Blockade w}

noncomputable instance configFintype (L : ℕ) : Fintype (Config L) := by
  classical
  unfold Config
  infer_instance

def bit (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

def pTriple (l c r : Rung) : ℕ :=
  bit (c = .minus) + bit (¬ ((l = .e) ↔ (r = .e)))

def p {L : ℕ} (x : Config L) (j : Fin L) : ℕ :=
  pTriple (x.val (prev j)) (x.val j) (x.val (next j))

def charge {L : ℕ} (x : Config L) : ℕ := ∑ j : Fin L, p x j

def Jammed {L : ℕ} (x : Config L) : Prop :=
  ∀ j, p x j = 0 → p x (prev j) = 1 ∧ p x (next j) = 1

def centerSwap : Rung → Rung
  | .e => .plus
  | .plus => .e
  | .minus => .minus

def signSwap : Rung → Rung
  | .e => .e
  | .plus => .minus
  | .minus => .plus

def centerAllowed {L : ℕ} (j : Fin L) (w : Word L) : Prop :=
  w (prev j) = .e ∧ w j ≠ .minus ∧ w (next j) = .e

def flanksAllowed {L : ℕ} (j : Fin L) (w : Word L) : Prop :=
  w (prev j) ≠ .e ∧ w (next j) ≠ .e

def centerMove {L : ℕ} (j : Fin L) (w : Word L) : Word L :=
  fun i => if i = j then centerSwap (w i) else w i

def flankMove {L : ℕ} (j : Fin L) (w : Word L) : Word L :=
  fun i => if i = prev j ∨ i = next j then signSwap (w i) else w i

private theorem center_involutive {L : ℕ} (j : Fin L) :
    Function.Involutive (centerMove j) := by
  intro w
  funext i
  by_cases h : i = j
  · subst i
    cases hwi : w j <;> simp [centerMove, hwi, centerSwap]
  · simp [centerMove, h]

private theorem flank_involutive {L : ℕ} (j : Fin L) :
    Function.Involutive (flankMove j) := by
  intro w
  funext i
  by_cases h : i = prev j ∨ i = next j
  · cases hwi : w i <;> simp [flankMove, h, hwi, signSwap]
  · simp [flankMove, h]

private theorem prev_ne_center {L : ℕ} (hL : 5 ≤ L) (j : Fin L) : prev j ≠ j := by
  intro h
  have hj := j.isLt
  have hv := prev_val j
  rw [h] at hv
  split at hv <;> omega

private theorem next_ne_center {L : ℕ} (hL : 5 ≤ L) (j : Fin L) : next j ≠ j := by
  intro h
  apply prev_ne_center hL j
  simpa using (congrArg prev h).symm

private theorem next_ne_prev {L : ℕ} (hL : 5 ≤ L) (j : Fin L) : next j ≠ prev j := by
  intro h
  have hj := j.isLt
  have hn := next_val j
  have hp := prev_val j
  rw [h] at hn
  split at hn <;> split at hp <;> omega

private theorem center_allowed {L : ℕ} (hL : 5 ≤ L) (j : Fin L) (w : Word L) :
    centerAllowed j (centerMove j w) ↔ centerAllowed j w := by
  have hs : ∀ r : Rung, centerSwap r ≠ .minus ↔ r ≠ .minus := by
    intro r
    cases r <;> decide
  simp [centerAllowed, centerMove, prev_ne_center hL, next_ne_center hL, hs]

private theorem flank_empty {L : ℕ} (j : Fin L) (w : Word L) (i : Fin L) :
    flankMove j w i = .e ↔ w i = .e := by
  by_cases h : i = prev j ∨ i = next j
  · cases hwi : w i <;> simp [flankMove, h, hwi, signSwap]
  · simp [flankMove, h]

private theorem flanks_allowed {L : ℕ} (j : Fin L) (w : Word L)
    (h : flanksAllowed j w) : flanksAllowed j (flankMove j w) :=
  ⟨fun hl => h.1 ((flank_empty j w (prev j)).mp hl),
    fun hr => h.2 ((flank_empty j w (next j)).mp hr)⟩

private theorem center_blockade {L : ℕ} (hL : 5 ≤ L) (j : Fin L) (x : Config L)
    (h : centerAllowed j x.val) : Blockade (centerMove j x.val) := by
  intro i
  by_cases hi : i = j
  · subst i
    right
    simpa [centerMove, next_ne_center hL] using h.2.2
  by_cases hin : next i = j
  · left
    have he : prev j = i := by simpa using (congrArg prev hin).symm
    simpa [centerMove, hi, he] using h.1
  simpa [centerMove, hi, hin] using x.property i

private theorem flank_blockade {L : ℕ} (j : Fin L) (x : Config L) :
    Blockade (flankMove j x.val) := by
  intro i
  simpa only [flank_empty] using x.property i

/-- The two Eq. (70) transitions restrict to involutions on their guarded
periodic blockade subtypes. -/
theorem guarded_moves {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    (∀ x : Config L, centerAllowed j x.val →
      Blockade (centerMove j x.val) ∧ centerAllowed j (centerMove j x.val) ∧
        centerMove j (centerMove j x.val) = x.val) ∧
    (∀ x : Config L, flanksAllowed j x.val →
      Blockade (flankMove j x.val) ∧ flanksAllowed j (flankMove j x.val) ∧
        flankMove j (flankMove j x.val) = x.val) := by
  refine ⟨fun x h => ⟨center_blockade hL j x h, (center_allowed hL j x.val).mpr h,
    center_involutive j x.val⟩, ?_⟩
  intro x h
  exact ⟨flank_blockade j x, flanks_allowed j _ h,
    flank_involutive j x.val⟩

private theorem p_zero_of_center {L : ℕ} {x : Config L} {j : Fin L}
    (h : centerAllowed j x.val) : p x j = 0 := by
  simp [p, pTriple, bit, h.1, h.2.1, h.2.2]

private theorem p_zero_of_flanks {L : ℕ} {x : Config L} {j : Fin L}
    (h : flanksAllowed j x.val) : p x j = 0 := by
  obtain hc | hr := x.property j
  · simp [p, pTriple, bit, h.1, h.2, hc]
  · exact (h.2 hr).elim

private theorem center_swap_minus (r : Rung) :
    centerSwap r = .minus ↔ r = .minus := by
  cases r <;> decide

private theorem center_keeps_p_away {L : ℕ} {j k : Fin L}
    {x y : Config L} (hy : y.val = centerMove j x.val)
    (hl : k ≠ prev j) (hr : k ≠ next j) : p y k = p x k := by
  have hprev : prev k ≠ j := by
    intro he
    exact hr (by simpa using congrArg next he)
  have hnext : next k ≠ j := by
    intro he
    exact hl (by simpa using congrArg prev he)
  by_cases he : k = j
  · subst k
    simp [p, pTriple, hy, centerMove, hprev, hnext, center_swap_minus]
  · simp [p, hy, centerMove, he, hprev, hnext]

private theorem flank_keeps_p_away {L : ℕ} {j k : Fin L}
    {x y : Config L} (hy : y.val = flankMove j x.val)
    (hl : k ≠ prev j) (hr : k ≠ next j) : p y k = p x k := by
  simp only [p, pTriple, hy, flank_empty]
  simp [flankMove, hl, hr]

private theorem center_complement (outer c : Rung) (hc : c ≠ .minus) :
    pTriple outer .e (centerSwap c) + pTriple outer .e c = 1 ∧
      pTriple (centerSwap c) .e outer + pTriple c .e outer = 1 := by
  cases outer <;> cases c <;> simp_all [pTriple, bit, centerSwap]

private theorem flank_complement (c : Rung) (hc : c ≠ .e) :
    pTriple .e (signSwap c) .e + pTriple .e c .e = 1 := by
  cases c <;> simp_all [pTriple, bit, signSwap]

private theorem center_flip_p {L : ℕ} (hL : 5 ≤ L) {j : Fin L}
    {x y : Config L} (h : centerAllowed j x.val) (hy : y.val = centerMove j x.val) :
    p y (prev j) + p x (prev j) = 1 ∧ p y (next j) + p x (next j) = 1 := by
  have hl : prev (prev j) ≠ j := by
    have hn := (next_ne_prev hL (prev j)).symm
    simpa using hn
  have hr : next (next j) ≠ j := by
    have hn := next_ne_prev hL (next j)
    simpa using hn
  have left := (center_complement (x.val (prev (prev j))) (x.val j) h.2.1).1
  have right := (center_complement (x.val (next (next j))) (x.val j) h.2.1).2
  constructor
  · simpa [p, hy, centerMove, hl, prev_ne_center hL, h.1] using left
  · simpa [p, hy, centerMove, hr, next_ne_center hL, h.2.2] using right

private theorem flank_flip_p {L : ℕ} {j : Fin L}
    {x y : Config L} (h : flanksAllowed j x.val) (hy : y.val = flankMove j x.val) :
    p y (prev j) + p x (prev j) = 1 ∧ p y (next j) + p x (next j) = 1 := by
  have hl : x.val (prev (prev j)) = .e := by
    have hb := x.property (prev (prev j))
    rw [next_prev] at hb
    exact hb.resolve_right h.1
  have hc : x.val j = .e := (x.property j).resolve_right h.2
  have hr : x.val (next (next j)) = .e := (x.property (next j)).resolve_left h.2
  have yl : y.val (prev (prev j)) = .e := by
    rw [hy, flank_empty]
    exact hl
  have yc : y.val j = .e := by
    rw [hy, flank_empty]
    exact hc
  have yr : y.val (next (next j)) = .e := by
    rw [hy, flank_empty]
    exact hr
  have yprev : y.val (prev j) = signSwap (x.val (prev j)) := by
    simp [hy, flankMove]
  have ynext : y.val (next j) = signSwap (x.val (next j)) := by
    simp [hy, flankMove]
  constructor
  · simpa [p, yl, yc, hl, hc, yprev] using flank_complement _ h.1
  · simpa [p, yc, yr, hc, hr, ynext] using flank_complement _ h.2


noncomputable section

abbrev Op (L : ℕ) := Matrix (Config L) (Config L) ℂ

def P {L : ℕ} (j : Fin L) : Op L := by
  classical
  exact Matrix.diagonal fun x => (p x j : ℂ)

def A {L : ℕ} (j : Fin L) : Op L := by
  classical
  exact fun y x =>
    if centerAllowed j x.val ∧ y.val = centerMove j x.val then 1 else 0

def F {L : ℕ} (j : Fin L) : Op L := by
  classical
  exact fun y x =>
    if flanksAllowed j x.val ∧ y.val = flankMove j x.val then 1 else 0

def S {L : ℕ} (j : Fin L) : Op L := A j + F j

def C {L : ℕ} (j : Fin L) : Op L := (P (prev j) - P (next j)) ^ 2

def T {L : ℕ} (j : Fin L) : Op L := C j * S j

private theorem T_apply {L : ℕ} (j : Fin L) (y x : Config L) :
    T j y x = ((p y (prev j) : ℂ) - (p y (next j) : ℂ)) ^ 2 * S j y x := by
  classical
  simp only [T, C, P, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul,
    Pi.pow_apply]

private theorem S_symm {L : ℕ} (hL : 5 ≤ L) (j : Fin L) (x y : Config L) :
    S j y x = S j x y := by
  classical
  have hA (u v : Config L) :
      centerAllowed j u.val ∧ v.val = centerMove j u.val →
      centerAllowed j v.val ∧ u.val = centerMove j v.val := by
    rintro ⟨h, e⟩
    rw [e, center_involutive]
    exact ⟨(center_allowed hL j u.val).mpr h, rfl⟩
  have hF (u v : Config L) :
      flanksAllowed j u.val ∧ v.val = flankMove j u.val →
      flanksAllowed j v.val ∧ u.val = flankMove j v.val := by
    rintro ⟨h, e⟩
    rw [e, flank_involutive]
    exact ⟨flanks_allowed j _ h, rfl⟩
  simp only [S, Matrix.add_apply, A, F]
  rw [if_congr ⟨hA x y, hA y x⟩ rfl rfl, if_congr ⟨hF x y, hF y x⟩ rfl rfl]

/-- A jammed basis word has a zero row for the paper's controlled generator. -/
private theorem jammed_zero_row {L : ℕ} (j : Fin L) {x : Config L} (hx : Jammed x)
    (y : Config L) (hL : 5 ≤ L) : T j x y = 0 := by
  rw [T_apply, S_symm hL j y x]
  by_cases hp : p x j = 0
  · obtain ⟨hl, hr⟩ := hx j hp
    simp [hl, hr]
  · classical
    have ha : ¬centerAllowed j x.val := fun h => hp (p_zero_of_center h)
    have hf : ¬flanksAllowed j x.val := fun h => hp (p_zero_of_flanks h)
    simp [S, A, F, ha, hf]

/-- A jammed basis word has a zero column and row for Eq. (40). -/
theorem jammed_zero_entries {L : ℕ} (hL : 5 ≤ L) (j : Fin L)
    {x : Config L} (hx : Jammed x) (y : Config L) : T j y x = 0 ∧ T j x y = 0 := by
  classical
  refine ⟨?_, jammed_zero_row j hx y hL⟩
  rw [T_apply]
  by_cases ha : centerAllowed j x.val ∧ y.val = centerMove j x.val
  · obtain ⟨hl, hr⟩ := hx j (p_zero_of_center ha.1)
    obtain ⟨al, ar⟩ := center_flip_p hL ha.1 ha.2
    have he : p y (prev j) = p y (next j) := by omega
    simp [he]
  by_cases hf : flanksAllowed j x.val ∧ y.val = flankMove j x.val
  · obtain ⟨hl, hr⟩ := hx j (p_zero_of_flanks hf.1)
    obtain ⟨al, ar⟩ := flank_flip_p hf.1 hf.2
    have he : p y (prev j) = p y (next j) := by omega
    simp [he]
  simp [S, A, F, ha, hf]

def ket {L : ℕ} (x : Config L) : Config L → ℂ := by
  classical
  exact Pi.single x 1

theorem jammed_kills {L : ℕ} (hL : 5 ≤ L) (j : Fin L)
    {x : Config L} (hx : Jammed x) : T j *ᵥ ket x = 0 ∧ ket x ᵥ* T j = 0 := by
  classical
  unfold ket
  rw [Matrix.mulVec_single_one, Matrix.single_one_vecMul]
  exact ⟨funext fun y => (jammed_zero_entries hL j hx y).1,
    funext fun y => (jammed_zero_entries hL j hx y).2⟩

/-- Every nonzero entry of Eq. (40) stays within the unextended charge sector. -/
theorem charge_of_nonzero_entry {L : ℕ} (hL : 5 ≤ L) (j : Fin L)
    {x y : Config L} (h : T j y x ≠ 0) : charge y = charge x := by
  classical
  have hne : p y (prev j) ≠ p y (next j) := by
    intro he
    exact h (by simp [T_apply, he])
  have hs : S j y x ≠ 0 := by
    intro he
    exact h (by simp [T_apply, he])
  have hm :
      (p y (prev j) + p x (prev j) = 1 ∧ p y (next j) + p x (next j) = 1) ∧
      (∀ k, k ≠ prev j → k ≠ next j → p y k = p x k) := by
    by_cases hl : centerAllowed j x.val ∧ y.val = centerMove j x.val
    · exact ⟨center_flip_p hL hl.1 hl.2, fun _ => center_keeps_p_away hl.2⟩
    by_cases hr : flanksAllowed j x.val ∧ y.val = flankMove j x.val
    · exact ⟨flank_flip_p hr.1 hr.2, fun _ => flank_keeps_p_away hr.2⟩
    exact (hs (by simp [S, A, F, hl, hr])).elim
  let rest := ((Finset.univ : Finset (Fin L)).erase (prev j)).erase (next j)
  have hsum : (∑ k ∈ rest, p y k) = ∑ k ∈ rest, p x k := by
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hr, hk⟩ := Finset.mem_erase.mp hk
    exact hm.2 k (Finset.mem_erase.mp hk).1 hr
  have hsplit (z : Config L) :
      (∑ k ∈ rest, p z k) + p z (next j) + p z (prev j) = charge z := by
    have hn : next j ∈ (Finset.univ : Finset (Fin L)).erase (prev j) :=
      Finset.mem_erase.mpr ⟨next_ne_prev hL j, Finset.mem_univ _⟩
    unfold rest
    rw [Finset.sum_erase_add _ _ hn, Finset.sum_erase_add _ _ (Finset.mem_univ _)]
    rfl
  have hx := hsplit x
  have hy := hsplit y
  obtain ⟨hl, hr⟩ := hm.1
  omega

def NP (L : ℕ) : Op L := ∑ j : Fin L, P j

/-- The unextended charge operator has the summed projector eigenvalue on every basis ket. -/
theorem charge_eigenvalue {L : ℕ} (x : Config L) :
    NP L *ᵥ ket x = (charge x : ℂ) • ket x := by
  classical
  have hd : NP L = Matrix.diagonal (fun y : Config L => (charge y : ℂ)) := by
    ext y z
    rw [NP, Matrix.sum_apply]
    by_cases he : y = z
    · subst z
      simp [P, charge, Nat.cast_sum]
    · simp [P, he]
  rw [hd]
  unfold ket
  rw [Matrix.diagonal_mulVec_single, mul_one]
  funext y
  by_cases he : y = x
  · subst y
    simp
  · simp [Pi.single_eq_of_ne he]

def E {L : ℕ} (j : Fin L) : Op L := by
  classical
  exact Matrix.diagonal fun x => (bit (x.val j = .e) : ℂ)

def Nminus {L : ℕ} (j : Fin L) : Op L := by
  classical
  exact Matrix.diagonal fun x => (bit (x.val j = .minus) : ℂ)

def Ue {L : ℕ} (j : Fin L) : Op L := (E (prev (prev j)) - E (next (next j))) ^ 2

def Um {L : ℕ} (j : Fin L) : Op L := (Nminus (prev j) - Nminus (next j)) ^ 2

def DA {L : ℕ} (j : Fin L) : Op L := E (prev j) * (1 - Nminus j) * E (next j)

def DF {L : ℕ} (j : Fin L) : Op L := (1 - E (prev j)) * (1 - E (next j))

private def control {L : ℕ} (j : Fin L) (x : Config L) : ℂ :=
  ((p x (prev j) : ℂ) - (p x (next j) : ℂ)) ^ 2

private theorem C_eq {L : ℕ} (j : Fin L) :
    C j = Matrix.diagonal (control j) := by
  classical
  simp only [C, P, Matrix.diagonal_sub, Matrix.diagonal_pow]
  rfl

private theorem p_le_one {L : ℕ} (x : Config L) (j : Fin L) : p x j ≤ 1 := by
  by_cases hm : x.val j = .minus
  · have he : x.val j ≠ .e := by simp [hm]
    have hl : x.val (prev j) = .e := by
      have hb := x.property (prev j)
      rw [next_prev] at hb
      exact hb.resolve_right he
    have hr := (x.property j).resolve_left he
    simp [p, pTriple, bit, hm, hl, hr]
  · simp only [p, pTriple, bit, ite_eq_right hm, zero_add]
    split <;> omega

private theorem control_bit {L : ℕ} (j : Fin L) (x : Config L) :
    control j x = 0 ∨ control j x = 1 := by
  have hl := p_le_one x (prev j)
  have hr := p_le_one x (next j)
  rcases (show p x (prev j) = 0 ∨ p x (prev j) = 1 by omega) with h0 | h1 <;>
    rcases (show p x (next j) = 0 ∨ p x (next j) = 1 by omega) with h2 | h3 <;>
    simp [control, *, zero_sub]

private theorem control_invariant {L : ℕ} {j : Fin L} {x y : Config L}
    (hl : p y (prev j) + p x (prev j) = 1)
    (hr : p y (next j) + p x (next j) = 1) : control j y = control j x := by
  have hl' : (p y (prev j) : ℂ) + (p x (prev j) : ℂ) = 1 := by
    exact_mod_cast hl
  have hr' : (p y (next j) : ℂ) + (p x (next j) : ℂ) = 1 := by
    exact_mod_cast hr
  unfold control
  rw [← neg_sq ((p x (prev j) : ℂ) - (p x (next j) : ℂ))]
  congr 1
  rw [neg_sub]
  exact sub_eq_sub_iff_add_eq_add.mpr (hl'.trans (hr'.symm.trans (add_comm _ _)))

private theorem center_flanks_disjoint {L : ℕ} {j : Fin L} {x : Word L}
    (ha : centerAllowed j x) (hf : flanksAllowed j x) : False :=
  hf.1 ha.1

private theorem C_comm_S {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    S j * C j = C j * S j := by
  classical
  ext y x
  rw [C_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (S j y x)]
  by_cases ha : centerAllowed j x.val ∧ y.val = centerMove j x.val
  · obtain ⟨hl, hr⟩ := center_flip_p hL ha.1 ha.2
    rw [control_invariant hl hr]
  by_cases hf : flanksAllowed j x.val ∧ y.val = flankMove j x.val
  · obtain ⟨hl, hr⟩ := flank_flip_p hf.1 hf.2
    rw [control_invariant hl hr]
  simp [S, A, F, ha, hf]

/-- The control commutes with the unextended move and removes no further factor on squaring. -/
theorem controlled_square {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    T j ^ 2 = C j * S j ^ 2 := by
  classical
  have hC : C j * C j = C j := by
    rw [C_eq, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    rcases control_bit j x with h | h <;> simp [h]
  rw [T, pow_two, pow_two, mul_assoc, ← mul_assoc (S j), C_comm_S hL,
    mul_assoc (C j), ← mul_assoc (C j), hC]

open scoped Classical in
private theorem guarded_sq {L : ℕ} (M : Op L) (g : Word L → Prop) (f : Word L → Word L)
    (hm : ∀ y x, M y x = if g x.val ∧ y.val = f x.val then 1 else 0)
    (hmove : ∀ x : Config L, g x.val → Blockade (f x.val) ∧ g (f x.val) ∧ f (f x.val) = x.val) :
    M ^ 2 = Matrix.diagonal (fun x => if g x.val then 1 else 0) := by
  classical
  ext y x
  rw [pow_two, Matrix.mul_apply]
  by_cases hg : g x.val
  · obtain ⟨hB, hguard, hinv⟩ := hmove x hg
    let z : Config L := ⟨f x.val, hB⟩
    rw [Finset.sum_eq_single z]
    · rw [hm y z, hm z x]
      have hz : z.val = f x.val := rfl
      by_cases hy : y = x
      · subst y
        simp [hg, hz, hguard, hinv]
      · have hv : y.val ≠ x.val := fun h => hy (Subtype.ext h)
        simp [hg, hz, hguard, hinv, hy, hv]
    · intro w _ hw
      have hne : w.val ≠ f x.val := fun h => hw (Subtype.ext h)
      simp [hm w x, hne]
    · simp
  · have hz : ∀ w : Config L, M w x = 0 := by intro w; simp [hm, hg]
    by_cases hy : y = x <;> simp [hy, hg, hz]

open scoped Classical in
private theorem DA_eq {L : ℕ} (j : Fin L) :
    DA j = Matrix.diagonal (fun x : Config L => if centerAllowed j x.val then 1 else 0) := by
  classical
  simp only [DA, E, Nminus, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hl : x.val (prev j) = .e <;> by_cases hc : x.val j = .minus <;>
    by_cases hr : x.val (next j) = .e <;> simp [centerAllowed, bit, hl, hc, hr]

open scoped Classical in
private theorem DF_eq {L : ℕ} (j : Fin L) :
    DF j = Matrix.diagonal (fun x : Config L => if flanksAllowed j x.val then 1 else 0) := by
  classical
  simp only [DF, E, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hl : x.val (prev j) = .e <;> by_cases hr : x.val (next j) = .e <;>
    simp [flanksAllowed, bit, hl, hr]

private theorem mixed_zero {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    A j * F j = 0 ∧ F j * A j = 0 := by
  classical
  constructor <;> ext y x <;> rw [Matrix.mul_apply, Matrix.zero_apply] <;>
    apply Finset.sum_eq_zero <;> intro z _
  · by_cases h : flanksAllowed j x.val ∧ z.val = flankMove j x.val
    · have hg : flanksAllowed j z.val := h.2 ▸ flanks_allowed j x.val h.1
      have ha : ¬centerAllowed j z.val := fun ha => center_flanks_disjoint ha hg
      simp [A, ha]
    · simp [F, h]
  · by_cases h : centerAllowed j x.val ∧ z.val = centerMove j x.val
    · have hg : centerAllowed j z.val := h.2 ▸ (center_allowed hL j x.val).mpr h.1
      have hf : ¬flanksAllowed j z.val := center_flanks_disjoint hg
      simp [F, hf]
    · simp [A, h]

private theorem center_control_value {L : ℕ} {j : Fin L} {x : Config L}
    (h : centerAllowed j x.val) :
    control j x = ((bit (x.val (prev (prev j)) = .e) : ℂ) -
      (bit (x.val (next (next j)) = .e) : ℂ)) ^ 2 := by
  obtain ⟨hl, hc, hr⟩ := h
  simp only [control, p, next_prev, prev_next, hl, hr]
  cases hleft : x.val (prev (prev j)) <;> cases hcenter : x.val j <;>
    cases hright : x.val (next (next j)) <;>
    simp_all [pTriple, bit, zero_sub]

private theorem flank_control_value {L : ℕ} {j : Fin L} {x : Config L}
    (h : flanksAllowed j x.val) :
    control j x = ((bit (x.val (prev j) = .minus) : ℂ) -
      (bit (x.val (next j) = .minus) : ℂ)) ^ 2 := by
  have hl : x.val (prev (prev j)) = .e := by
    have hb := x.property (prev (prev j))
    rw [next_prev] at hb
    exact hb.resolve_right h.1
  have hc := (x.property j).resolve_right h.2
  have hr := (x.property (next j)).resolve_left h.2
  simp [control, p, pTriple, bit, hl, hc, hr]

private theorem split_control {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    C j * A j = Ue j * A j ∧ C j * F j = Um j * F j := by
  classical
  constructor <;> ext y x <;> rw [C_eq, Matrix.diagonal_mul]
  · simp only [Ue, E, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply]
    by_cases h : centerAllowed j x.val ∧ y.val = centerMove j x.val
    · have hy : centerAllowed j y.val := h.2 ▸ (center_allowed hL j x.val).mpr h.1
      rw [center_control_value hy]
    · simp [A, h]
  · simp only [Um, Nminus, Matrix.diagonal_sub, Matrix.diagonal_pow,
      Matrix.diagonal_mul, Pi.pow_apply]
    by_cases h : flanksAllowed j x.val ∧ y.val = flankMove j x.val
    · have hy : flanksAllowed j y.val := h.2 ▸ flanks_allowed j x.val h.1
      rw [flank_control_value hy]
    · simp [F, h]

/-- The two five-rung controls and the two diagonal terms in Eq. (71)
give the linear and quadratic parts of the plus-sign density. -/
theorem ladder_density_parts {L : ℕ} (hL : 5 ≤ L) (j : Fin L) :
    T j = Ue j * A j + Um j * F j ∧
      T j ^ 2 = Ue j * DA j + Um j * DF j := by
  obtain ⟨ha, hf⟩ := split_control hL j
  obtain ⟨haf, hfa⟩ := mixed_zero hL j
  have hA : A j ^ 2 = DA j := by
    rw [DA_eq]
    exact guarded_sq (A j) (centerAllowed j) (centerMove j) (fun _ _ => rfl)
      (guarded_moves hL j).1
  have hF : F j ^ 2 = DF j := by
    rw [DF_eq]
    exact guarded_sq (F j) (flanksAllowed j) (flankMove j) (fun _ _ => rfl)
      (guarded_moves hL j).2
  constructor
  · rw [T, S, mul_add, ha, hf]
  have hs : S j ^ 2 = A j ^ 2 + F j ^ 2 := by
    rw [S, pow_two, add_mul, mul_add, mul_add, haf, hfa, add_zero, zero_add,
      ← pow_two, ← pow_two]
  rw [controlled_square hL, hs, mul_add, pow_two (A j), pow_two (F j),
    ← mul_assoc, ← mul_assoc, ha, hf, mul_assoc, mul_assoc,
    ← pow_two, ← pow_two, hA, hF]

private theorem ladder_parts_disjoint {L : ℕ} (j : Fin L) (y x : Config L) :
    ((Ue j * A j) y x = 0 ∨ (Um j * F j) y x = 0) ∧
      ((Ue j * DA j) y x = 0 ∨ (Um j * DF j) y x = 0) := by
  classical
  by_cases ha : centerAllowed j x.val
  · have hf : ¬flanksAllowed j x.val := center_flanks_disjoint ha
    constructor <;> right
    · simp [Um, Nminus, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul, F, hf]
    · simp [Um, Nminus, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul, DF_eq,
        Matrix.diagonal_apply, hf]
  · constructor <;> left
    · simp [Ue, E, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul, A, ha]
    · simp [Ue, E, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul, DA_eq,
        Matrix.diagonal_apply, ha]

private theorem split_jammed_action {L : ℕ} {M N : Op L} {x : Config L}
    (h : (M + N) *ᵥ ket x = 0 ∧ ket x ᵥ* (M + N) = 0)
    (hd : ∀ y z, M y z = 0 ∨ N y z = 0) :
    (M *ᵥ ket x = 0 ∧ ket x ᵥ* M = 0) ∧ (N *ᵥ ket x = 0 ∧ ket x ᵥ* N = 0) := by
  classical
  obtain ⟨hcol, hrow⟩ := h
  simp only [ket, Matrix.mulVec_single_one, Matrix.single_one_vecMul] at hcol hrow ⊢
  have split_entry (y z : Config L) (he : (M + N) y z = 0) :
      M y z = 0 ∧ N y z = 0 := by
    rw [Matrix.add_apply] at he
    rcases hd y z with hm | hn
    · exact ⟨hm, by simpa [hm] using he⟩
    · exact ⟨by simpa [hn] using he, hn⟩
  have hc (y : Config L) := split_entry y x (congrFun hcol y)
  have hr (y : Config L) := split_entry x y (congrFun hrow y)
  exact ⟨⟨funext fun y => (hc y).1, funext fun y => (hr y).1⟩,
    ⟨funext fun y => (hc y).2, funext fun y => (hr y).2⟩⟩

/-- Both the linear and quadratic contributions in each of Eq. (71)'s
two controlled summands separately kill a jammed basis word. -/
theorem ladder_parts_kill {L : ℕ} (hL : 5 ≤ L) {x : Config L} (hx : Jammed x) (j : Fin L) :
    ((Ue j * A j) *ᵥ ket x = 0 ∧ ket x ᵥ* (Ue j * A j) = 0) ∧
    ((Um j * F j) *ᵥ ket x = 0 ∧ ket x ᵥ* (Um j * F j) = 0) ∧
    ((Ue j * DA j) *ᵥ ket x = 0 ∧ ket x ᵥ* (Ue j * DA j) = 0) ∧
    ((Um j * DF j) *ᵥ ket x = 0 ∧ ket x ᵥ* (Um j * DF j) = 0) := by
  obtain ⟨hT, hSq⟩ := ladder_density_parts hL j
  have h := jammed_kills hL j hx
  have hs : T j ^ 2 *ᵥ ket x = 0 ∧ ket x ᵥ* T j ^ 2 = 0 := by
    simp [pow_two, ← Matrix.mulVec_mulVec, ← Matrix.vecMul_vecMul, h.1, h.2]
  rw [hT] at h
  rw [hSq] at hs
  obtain ⟨ha, hf⟩ := split_jammed_action h fun y z => (ladder_parts_disjoint j y z).1
  obtain ⟨hda, hdf⟩ := split_jammed_action hs fun y z => (ladder_parts_disjoint j y z).2
  exact ⟨ha, hf, hda, hdf⟩

end

end D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves
