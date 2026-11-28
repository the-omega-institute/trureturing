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

abbrev next {L : ℕ} (j : Fin L) : Fin L := finRotate L j

abbrev prev {L : ℕ} (j : Fin L) : Fin L := (finRotate L).symm j

@[simp] private theorem next_prev {L : ℕ} (j : Fin L) : next (prev j) = j :=
  (finRotate L).apply_symm_apply j

@[simp] private theorem prev_next {L : ℕ} (j : Fin L) : prev (next j) = j :=
  (finRotate L).symm_apply_apply j

private theorem next_val {L : ℕ} (j : Fin L) :
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

private theorem prev_val {L : ℕ} (j : Fin L) :
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
  · cases w i <;> simp [centerMove, h, centerSwap]
  · simp [centerMove, h]

private theorem flank_involutive {L : ℕ} (j : Fin L) :
    Function.Involutive (flankMove j) := by
  intro w
  funext i
  by_cases h : i = prev j ∨ i = next j
  · cases w i <;> simp [flankMove, h, signSwap]
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
  · cases w i <;> simp [flankMove, h, signSwap]
  · simp [flankMove, h]

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
  exact ⟨flank_blockade j x, by simpa only [flanksAllowed, flank_empty] using h,
    flank_involutive j x.val⟩

private theorem p_zero_of_center {L : ℕ} {x : Config L} {j : Fin L}
    (h : centerAllowed j x.val) : p x j = 0 := by
  simp [p, pTriple, bit, h.1, h.2.1, h.2.2]

private theorem p_zero_of_flanks {L : ℕ} {x : Config L} {j : Fin L}
    (h : flanksAllowed j x.val) : p x j = 0 := by
  obtain hc | hr := x.property j
  · simp [p, pTriple, bit, h.1, h.2, hc]
  · exact (h.2 hr).elim

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

def T {L : ℕ} (j : Fin L) : Op L := (P (prev j) - P (next j)) ^ 2 * S j

private theorem T_apply {L : ℕ} (j : Fin L) (y x : Config L) :
    T j y x = ((p y (prev j) : ℂ) - (p y (next j) : ℂ)) ^ 2 * S j y x := by
  classical
  simp only [T, P, Matrix.diagonal_sub, Matrix.diagonal_pow, Matrix.diagonal_mul,
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
    exact ⟨by simpa only [flanksAllowed, flank_empty] using h, rfl⟩
  simp only [S, Matrix.add_apply, A, F]
  rw [if_congr ⟨hA x y, hA y x⟩ rfl rfl, if_congr ⟨hF x y, hF y x⟩ rfl rfl]

/-- A jammed basis word has a zero row for the paper's controlled generator. -/
theorem jammed_zero_row {L : ℕ} (j : Fin L) {x : Config L} (hx : Jammed x)
    (y : Config L) (hL : 5 ≤ L) : T j x y = 0 := by
  rw [T_apply, S_symm hL j y x]
  by_cases hp : p x j = 0
  · obtain ⟨hl, hr⟩ := hx j hp
    simp [hl, hr]
  · classical
    have ha : ¬centerAllowed j x.val := fun h => hp (p_zero_of_center h)
    have hf : ¬flanksAllowed j x.val := fun h => hp (p_zero_of_flanks h)
    simp [S, A, F, ha, hf]

end

end D5.S3.Quantum.SpinChains.MiaoFukaiGuardedMoves
