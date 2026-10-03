/- GID: D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Adamaszek's necklace cycle period conjecture (arXiv:1202.1655, 7.4). -/
/-
proof_shape: result: content
escape_witness: form (2), result itself: compressed free motion, cyclic ordering,
  integer-lift representation, and winding/parity recovery on its live proof path.
admission_basis: open-problem-resolution (#11582; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
namespace D5.S3.StatisticalMechanics.HardCore.HardSquareNecklacePeriod
inductive Vec where
  | negTwo | negOne | posOne | posTwo
namespace Vec
def value : Vec → ℤ
  | negTwo => -2 | negOne => -1 | posOne => 1 | posTwo => 2
def length : Vec → ℤ
  | negTwo | posTwo => 2
  | negOne | posOne => 1
def positive : Vec → Prop
  | posOne | posTwo => True
  | negOne | negTwo => False
private instance (v : Vec) : Decidable v.positive := by cases v <;> simp [positive] <;> infer_instance
private def sign : Vec → ℤ
  | posOne | posTwo => 1
  | negOne | negTwo => -1
def turn : Vec → Vec
  | negTwo => posOne | negOne => posTwo | posOne => negTwo | posTwo => negOne
def negate : Vec → Vec
  | negTwo => posTwo | negOne => posOne | posOne => negOne | posTwo => negTwo
def shorten : Vec → Vec
  | negTwo => negOne | posTwo => posOne | v => v
private def velocity (v : Vec) : ℤ := v.sign * (2 * v.length - 3)
end Vec
abbrev Config (n : ℕ) := ZMod n → Option Vec
def HasStone {n : ℕ} (N : Config n) (p : ZMod n) : Prop := ∃ v, N p = some v
def clockwiseDistance {n : ℕ} (p q : ZMod n) : ℕ := (q - p).val
def Consecutive {n : ℕ} (N : Config n) (p q : ZMod n) : Prop :=
  p ≠ q ∧ HasStone N p ∧ HasStone N q ∧
    ∀ r, 0 < clockwiseDistance p r →
      clockwiseDistance p r < clockwiseDistance p q → N r = none
def PairAdmissible (d : ℤ) (v w : Vec) : Prop :=
  0 < d ∧
  (v.positive ↔ ¬ w.positive) ∧
  (¬ v.positive → w.positive → Odd d) ∧
  (v.positive → ¬ w.positive → Odd (d + v.length + w.length)) ∧
  (v.positive → ¬ w.positive →
    3 ≤ d ∧ (d = 3 → v.length = 1 ∧ w.length = 1))
def IsNecklace {n : ℕ} (k : ℕ) (N : Config n) : Prop :=
  0 < n ∧
  (∃ S : Finset (ZMod n), S.card = 2 * k ∧ ∀ p, p ∈ S ↔ HasStone N p) ∧
  ∀ p q v w, Consecutive N p q → N p = some v → N q = some w →
    PairAdmissible (clockwiseDistance p q : ℤ) v w
noncomputable def jumpTurn (n : ℕ) (N : Config n) : Config n := by
  classical
  exact fun q =>
  if h : ∃ a : ZMod n × Vec, N a.1 = some a.2 ∧ q = a.1 + (a.2.value : ZMod n)
  then some (Classical.choose h).2.turn
  else none
noncomputable def fix (n : ℕ) (M : Config n) : Config n := by
  classical
  exact fun p =>
  match M p with
  | none => none
  | some v =>
    if (if v.positive then
        ∃ w, M (p + 3) = some w ∧ ¬ w.positive
      else ∃ w, M (p - 3) = some w ∧ w.positive)
    then some v.shorten else some v
noncomputable def necklaceT (n : ℕ) (N : Config n) : Config n :=
  fix n (jumpTurn n N)
def circleIsometryAct {n : ℕ} (g : DihedralGroup n) (N : Config n) : Config n :=
  match g with
  | .r c => fun q => N (q - c)
  | .sr c => fun q => (N (-q + c)).map Vec.negate
instance circleIsometrySMul {n : ℕ} : SMul (DihedralGroup n) (Config n) := ⟨circleIsometryAct⟩
def claim : Prop :=
  ∀ n k : ℕ, Even n → 1 ≤ k → ∀ N : Config n, IsNecklace k N →
    ∃ g : DihedralGroup n, (necklaceT n)^[n - 3 * k] N = g • N
private def compressed (x i : ℤ) (v : Vec) : ℤ := 2 * x + v.value - 3 * i
private def jumpedGap (d : ℤ) (v w : Vec) : ℤ := d + w.value - v.value
private def fixesPair (d : ℤ) (v w : Vec) : Prop :=
  v.turn.positive ∧ ¬ w.turn.positive ∧ jumpedGap d v w = 3
private instance (d : ℤ) (v w : Vec) : Decidable (fixesPair d v w) :=
  inferInstanceAs (Decidable (v.turn.positive ∧ ¬ w.turn.positive ∧ jumpedGap d v w = 3))
private structure Lifted where
  x : ℤ → ℤ
  v : ℤ → Vec
private def Lifted.Admissible (A : Lifted) : Prop :=
  ∀ i, PairAdmissible (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1))
private def Lifted.Periodic (A : Lifted) (h n : ℤ) : Prop :=
  (∀ i, A.x (i + h) = A.x i + n) ∧ (∀ i, A.v (i + h) = A.v i)
private def Lifted.y (A : Lifted) (i : ℤ) : ℤ := compressed (A.x i) i (A.v i)
private def Lifted.u (A : Lifted) (i : ℤ) : ℤ := (A.v i).velocity
private def Lifted.collision (A : Lifted) (i : ℤ) : Prop :=
  fixesPair (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1))
private instance (A : Lifted) (i : ℤ) : Decidable (A.collision i) :=
  inferInstanceAs (Decidable (fixesPair (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1))))
private def Lifted.step (A : Lifted) : Lifted where
  x i := A.x i + (A.v i).value
  v i := if A.collision i ∨ A.collision (i - 1) then (A.v i).turn.shorten else (A.v i).turn
private def Lifted.swapIndex (A : Lifted) (i : ℤ) : ℤ :=
  if A.collision i then i + 1 else if A.collision (i - 1) then i - 1 else i
private def Lifted.Represents (n : ℕ) (A : Lifted) (N : Config n) : Prop :=
  ∀ p v, N p = some v ↔ ∃ i : ℤ, (A.x i : ZMod n) = p ∧ A.v i = v
open scoped BigOperators
private def Lifted.collisionIndicator (A : Lifted) (i : ℤ) : ℤ := if A.collision i then 1 else 0
private def Vec.negativeVelocity (v : Vec) : ℤ := if v.velocity = -1 then 1 else 0
open scoped Fin.IntCast
private def cyclicPosition {h : ℕ} (hh : 0 < h) (n : ℤ) (f : Fin h → ℤ) (i : ℤ) : ℤ := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  exact f (i : Fin h) + n * (i / (h : ℤ))
private def Lifted.jumped (A : Lifted) : Lifted where
  x i := A.x i + (A.v i).value
  v i := (A.v i).turn
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 2048 in
theorem result : claim := by
  have aux_jump_does_not_cross {d : ℤ} {v w : Vec} (h : PairAdmissible d v w) : 0 < jumpedGap d v w := by
    cases v <;> cases w <;> simp [PairAdmissible, Vec.positive, Vec.length, Vec.value, jumpedGap, Int.odd_iff] at * <;> omega
  have aux_compressed_strict {d x i : ℤ} {v w : Vec} (h : PairAdmissible d v w) : compressed x i v < compressed (x + d) (i + 1) w := by
    clear aux_jump_does_not_cross; cases v <;> cases w <;> simp [PairAdmissible, Vec.positive, Vec.length, Vec.value, compressed, Int.odd_iff] at * <;> omega
  have aux_fix_characterization {d : ℤ} {v w : Vec} (h : PairAdmissible d v w) : fixesPair d v w ↔ d = 1 ∧ v = .negOne ∧ w = .posOne := by
    clear aux_jump_does_not_cross aux_compressed_strict; cases v <;> cases w <;> simp [PairAdmissible, Vec.positive, Vec.length, Vec.value, Vec.turn, fixesPair, jumpedGap, Int.odd_iff] at * <;> omega
  have aux_collision_disjoint {A : Lifted} (hA : A.Admissible) (i : ℤ) : A.collision i → ¬ A.collision (i + 1) ∧ ¬ A.collision (i - 1) := by
    clear aux_jump_does_not_cross aux_compressed_strict; intro hi; obtain ⟨_, hv, hw⟩ := (aux_fix_characterization (hA i)).mp hi; constructor
    · intro hh
      obtain ⟨_, hv', _⟩ := (aux_fix_characterization (hA (i + 1))).mp hh
      rw [hw] at hv'; cases hv'
    · intro hh
      obtain ⟨_, _, hw'⟩ := (aux_fix_characterization (hA (i - 1))).mp hh
      have he : i - 1 + 1 = i := by omega
      rw [he, hv] at hw'; cases hw'
  have aux_swapIndex_involutive {A : Lifted} (hA : A.Admissible) : Function.Involutive A.swapIndex := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization; intro i; by_cases hi : A.collision i
    · have hn := ((aux_collision_disjoint (A := A)) hA i hi).1
      simp [Lifted.swapIndex, hi, hn]
    · by_cases hp : A.collision (i - 1)
      · have hn := ((aux_collision_disjoint (A := A)) hA (i - 1) hp).2
        have he : i - 1 + 1 = i := by omega
        simp [Lifted.swapIndex, hi, hp, he]
      · simp [Lifted.swapIndex, hi, hp]
  have aux_step_conjugacy {A : Lifted} (hA : A.Admissible) (i : ℤ) : A.step.y i = A.y (A.swapIndex i) + A.u (A.swapIndex i) ∧ A.step.u i = A.u (A.swapIndex i) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_collision_disjoint aux_swapIndex_involutive; by_cases hi : A.collision i
    · obtain ⟨hd, hv, hw⟩ := (aux_fix_characterization (hA i)).mp hi
      simp [Lifted.step, Lifted.y, Lifted.u, Lifted.swapIndex, hi, hv, hw, compressed, Vec.value, Vec.velocity, Vec.sign, Vec.length, Vec.turn, Vec.shorten]
      omega
    · by_cases hp : A.collision (i - 1)
      · obtain ⟨hd, hv, hw⟩ := (aux_fix_characterization (hA (i - 1))).mp hp
        have he : i - 1 + 1 = i := by omega
        rw [he] at hd hw; simp [Lifted.step, Lifted.y, Lifted.u, Lifted.swapIndex, hi, hp, hv, hw, compressed, Vec.value, Vec.velocity, Vec.sign, Vec.length, Vec.turn, Vec.shorten]; omega
      · have e := (show
            compressed (A.x i + (A.v i).value) i (A.v i).turn = A.y i + A.u i ∧
              (A.v i).turn.velocity = A.u i from by
            cases hv : A.v i <;> simp [Lifted.y, Lifted.u, hv, compressed, Vec.value, Vec.turn, Vec.velocity, Vec.sign, Vec.length] <;> omega)
        simpa [Lifted.step, Lifted.y, Lifted.u, Lifted.swapIndex, hi, hp] using e
  have aux_two_pair_bound {d e : ℤ} {v w z : Vec} (hd : PairAdmissible d v w) (he : PairAdmissible e w z) : 4 ≤ d + e := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy; cases v <;> cases w <;> cases z <;> simp [PairAdmissible, Vec.positive, Vec.length, Int.odd_iff] at * <;> omega
  have aux_two_gap_bound {A : Lifted} (hA : A.Admissible) (i : ℤ) : A.x i + 4 ≤ A.x (i + 2) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy; have hh := aux_two_pair_bound (hA i) (hA (i + 1)); have he : i + 1 + 1 = i + 2 := by omega
    rw [he] at hh; omega
  have aux_length_bound {A : Lifted} (k n : ℕ) (hA : A.Admissible) (hp : A.Periodic (2 * (k : ℤ)) n) : 4 * k ≤ n := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound; have hincr : ∀ j : ℕ, A.x (2 * (j : ℤ)) ≥ A.x 0 + 4 * (j : ℤ) := by
      intro j; induction j with
      | zero => simp
      | succ j ih =>
        have hh := (aux_two_gap_bound (A := A)) hA (2 * (j : ℤ)); simp only [Nat.cast_succ] at *; have he : 2 * ((j : ℤ) + 1) = 2 * (j : ℤ) + 2 := by omega
        rw [he]; omega
    have ht := hp.1 0; have hb := hincr k; simp only [zero_add] at ht; omega
  have aux_pair_step_admissible (d : ℤ) (v w : Vec) (b c : Bool) (h : PairAdmissible d v w) (hb : b = true → v = .posOne) (hc : c = true → w = .negOne) : PairAdmissible (jumpedGap d v w) (if fixesPair d v w ∨ b = true then v.turn.shorten else v.turn) (if fixesPair d v w ∨ c = true then w.turn.shorten else w.turn) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound; by_cases hf : fixesPair d v w <;> cases v <;> cases w <;> cases b <;> cases c <;> simp only [hf, or_true, or_false, Bool.false_eq_true, ite_true, ite_false] <;> simp_all [PairAdmissible, jumpedGap, fixesPair, Vec.positive, Vec.length, Vec.value, Vec.turn, Vec.shorten, Int.odd_iff, Int.even_iff] <;> omega
  have aux_step_admissible {A : Lifted} (hA : A.Admissible) : A.step.Admissible := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound; intro i; have he : i + 1 - 1 = i := by omega
    have hb : decide (A.collision (i - 1)) = true → A.v i = .posOne := by
      intro h; have hh := of_decide_eq_true h; obtain ⟨_, _, hw⟩ := (aux_fix_characterization (hA (i - 1))).mp hh; simpa using hw
    have hc : decide (A.collision (i + 1)) = true → A.v (i + 1) = .negOne := by
      intro h; have hh := of_decide_eq_true h; exact ((aux_fix_characterization (hA (i + 1))).mp hh).2.1
    have hh := aux_pair_step_admissible (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1))
      (decide (A.collision (i - 1))) (decide (A.collision (i + 1))) (hA i) hb hc
    have hb' : decide (A.collision (i - 1)) = true ↔ A.collision (i - 1) :=
      ⟨of_decide_eq_true, fun h => decide_eq_true h⟩
    have hc' : decide (A.collision (i + 1)) = true ↔ A.collision (i + 1) :=
      ⟨of_decide_eq_true, fun h => decide_eq_true h⟩
    simp only [hb', hc'] at hh; have hg : jumpedGap (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1)) =
        (A.x (i + 1) + (A.v (i + 1)).value) - (A.x i + (A.v i).value) := by
      dsimp [jumpedGap]; omega
    change PairAdmissible (jumpedGap (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1)))
      (if A.collision i ∨ A.collision (i - 1) then (A.v i).turn.shorten else (A.v i).turn)
      (if A.collision i ∨ A.collision (i + 1) then (A.v (i + 1)).turn.shorten else (A.v (i + 1)).turn) at hh
    change PairAdmissible
      ((A.x (i + 1) + (A.v (i + 1)).value) - (A.x i + (A.v i).value))
      (if A.collision i ∨ A.collision (i - 1) then (A.v i).turn.shorten else (A.v i).turn)
      (if A.collision (i + 1) ∨ A.collision (i + 1 - 1) then
        (A.v (i + 1)).turn.shorten else (A.v (i + 1)).turn)
    rw [he, ← hg]; by_cases h0 : A.collision i <;> by_cases h1 : A.collision (i - 1) <;> by_cases h2 : A.collision (i + 1) <;> simp only [h0, h1, h2, or_true, or_false, ite_true, ite_false] at hh ⊢ <;> exact hh
  have aux_compressed_period {A : Lifted} {h n : ℤ} (hp : A.Periodic h n) (i : ℤ) : A.y (i + h) = A.y i + 2 * n - 3 * h ∧ A.u (i + h) = A.u i := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible; simp only [Lifted.y, Lifted.u, compressed, hp.1, hp.2]; constructor
    · omega
    · trivial
  have aux_collision_periodic {A : Lifted} {h n : ℤ} (hp : A.Periodic h n) (i : ℤ) : A.collision (i + h) ↔ A.collision i := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period; unfold Lifted.collision; have he : i + h + 1 = i + 1 + h := by omega
    rw [he, hp.1 (i + 1), hp.1 i, hp.2 (i + 1), hp.2 i]; simp
  have aux_step_periodic {A : Lifted} {h n : ℤ} (hp : A.Periodic h n) : A.step.Periodic h n := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period; constructor
    · intro i
      change A.x (i + h) + (A.v (i + h)).value = A.x i + (A.v i).value + n; rw [hp.1 i, hp.2 i]; omega
    · intro i
      have he : i + h - 1 = i - 1 + h := by omega
      dsimp only [Lifted.step]; rw [he, hp.2 i]; simp only [(aux_collision_periodic (A := A)) hp i, (aux_collision_periodic (A := A)) hp (i - 1)]
  have aux_iterate_conjugacy {A : Lifted} (hA : A.Admissible) (t : ℕ) : ((Lifted.step)^[t] A).Admissible ∧ ∃ σ : ℤ ≃ ℤ, ∀ i, ((Lifted.step)^[t] A).y i = A.y (σ i) + (t : ℤ) * A.u (σ i) ∧ ((Lifted.step)^[t] A).u i = A.u (σ i) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic; induction t with
    | zero =>
      refine ⟨hA, Equiv.refl ℤ, ?_⟩
      intro i; simp
    | succ t ih =>
      obtain ⟨hB, σ, hσ⟩ := ih
      let B := (Lifted.step)^[t] A; let τ : ℤ ≃ ℤ := ((aux_swapIndex_involutive (A := B)) hB).toPerm B.swapIndex; rw [Function.iterate_succ_apply']; refine ⟨(aux_step_admissible (A := B)) hB, τ.trans σ, ?_⟩; intro i; have hs := (aux_step_conjugacy (A := B)) hB i; have ht := hσ (B.swapIndex i); change B.step.y i = A.y (σ (B.swapIndex i)) + (t.succ : ℤ) * A.u (σ (B.swapIndex i)) ∧
        B.step.u i = A.u (σ (B.swapIndex i))
      constructor
      · rw [hs.1, ht.1, ht.2]
        simp only [Nat.cast_succ]; ring
      · exact hs.2.trans ht.2
  have aux_strict_order {A : Lifted} (hA : A.Admissible) : StrictMono A.x ∧ StrictMono A.y := by
    clear aux_jump_does_not_cross aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy; constructor
    · apply strictMono_int_of_lt_succ
      intro i; have hh := (hA i).1; omega
    · apply strictMono_int_of_lt_succ
      intro i; have hh := aux_compressed_strict (x := A.x i) (i := i) (hA i); have he : A.x i + (A.x (i + 1) - A.x i) = A.x (i + 1) := by omega
      simpa only [he, Lifted.y] using hh
  have aux_int_strictMono_surjective_translation (f : ℤ → ℤ) (hf : StrictMono f) (hsurj : Function.Surjective f) : ∀ i, f i = i + f 0 := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order; have hsucc : ∀ i, f (i + 1) = f i + 1 := by
      intro i; have hi := hf (show i < i + 1 by omega); by_contra hne; have hgap : f i + 1 < f (i + 1) := by omega
      obtain ⟨j, hj⟩ := hsurj (f i + 1)
      have hij : i < j := hf.lt_iff_lt.mp (by rw [hj]; omega)
      have hji : j < i + 1 := hf.lt_iff_lt.mp (by rw [hj]; exact hgap)
      omega
    intro i; induction i using Int.induction_on with
    | zero => simp
    | succ j ih =>
      rw [hsucc, ih]; omega
    | pred j ih =>
      have hh := hsucc (-(j : ℤ) - 1); have he : -(j : ℤ) - 1 + 1 = -(j : ℤ) := by omega
      rw [he, ih] at hh; omega
  have aux_half_period_relabel {A : Lifted} (hA : A.Admissible) (L h n : ℕ) (hp : A.Periodic h n) (hc : 2 * (n : ℤ) - 3 * (h : ℤ) = 2 * (L : ℤ)) : ∃ r : ℤ, ∀ i, ((Lifted.step)^[L] A).y i = A.y (i + r) + (L : ℤ) ∧ ((Lifted.step)^[L] A).u i = A.u (i + r) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_collision_periodic aux_step_periodic
    classical
    let B := (Lifted.step)^[L] A; obtain ⟨hB, σ, hσ⟩ := (aux_iterate_conjugacy (A := A)) hA L; have hY : ∀ i, A.y (i + (h : ℤ)) = A.y i + 2 * (L : ℤ) := by
      intro i; have hh := ((aux_compressed_period (A := A)) hp i).1; omega
    have hU : ∀ i, A.u (i + (h : ℤ)) = A.u i := fun i => ((aux_compressed_period (A := A)) hp i).2; have hvel : ∀ i, A.u i = 1 ∨ A.u i = -1 := by
      intro i; cases he : A.v i <;> simp [Lifted.u, he, Vec.velocity, Vec.sign, Vec.length]
    have hforward : ∀ i, ∃ j, B.y i = A.y j + (L : ℤ) ∧ B.u i = A.u j := by
      intro i; obtain ⟨hy, hu⟩ := hσ i; rcases hvel (σ i) with hv | hv
      · refine ⟨σ i, ?_, hu⟩
        rw [hv] at hy; simpa using hy
      · have hy' := hY (σ i - (h : ℤ))
        have hu' := hU (σ i - (h : ℤ)); have he : σ i - (h : ℤ) + (h : ℤ) = σ i := by omega
        rw [he] at hy' hu'; rw [hv] at hy; refine ⟨σ i - (h : ℤ), ?_, hu.trans hu'⟩; dsimp [B]; omega
    have hbackward : ∀ j, ∃ i, B.y i = A.y j + (L : ℤ) ∧ B.u i = A.u j := by
      intro j; rcases hvel j with hv | hv
      · obtain ⟨i, hi⟩ := σ.surjective j
        obtain ⟨hy, hu⟩ := hσ i
        rw [hi] at hy hu; rw [hv] at hy; exact ⟨i, by simpa using hy, hu⟩
      · obtain ⟨i, hi⟩ := σ.surjective (j + (h : ℤ))
        obtain ⟨hy, hu⟩ := hσ i
        rw [hi, hY j, hU j, hv] at hy; rw [hi, hU j] at hu; refine ⟨i, ?_, hu⟩; dsimp [B]; omega
    let η : ℤ → ℤ := fun i => Classical.choose (hforward i); have hη : ∀ i, B.y i = A.y (η i) + (L : ℤ) ∧ B.u i = A.u (η i) :=
      fun i => Classical.choose_spec (hforward i)
    have hyA := ((aux_strict_order (A := A)) hA).2; have hyB := ((aux_strict_order (A := B)) hB).2; have hmono : StrictMono η := by
      intro i j hij; have hh := hyB hij; have hi := (hη i).1; have hj := (hη j).1; apply hyA.lt_iff_lt.mp; omega
    have hsurj : Function.Surjective η := by
      intro j; obtain ⟨i, hi, _⟩ := hbackward j; have hh := (hη i).1; refine ⟨i, hyA.injective ?_⟩; omega
    have hshift := aux_int_strictMono_surjective_translation η hmono hsurj; refine ⟨η 0, ?_⟩; intro i; have hh := hη i; rw [hshift i] at hh; exact hh
  have aux_reconstruct_shift {A B : Lifted} {r δ : ℤ} (hy : ∀ i, B.y i = A.y (i + r) + δ) (hu : ∀ i, B.u i = A.u (i + r)) (hs : ∀ i, (B.v i).sign = (A.v (i + r)).sign) : (∀ i, B.v i = A.v (i + r)) ∧ (∀ i, B.x i = A.x (i + r) + (δ - 3 * r) / 2) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel; have hv : ∀ i, B.v i = A.v (i + r) := by
      intro i; have hh := hu i; have hh' := hs i; cases he : B.v i <;> cases he' : A.v (i + r) <;> simp [Lifted.u, he, he', Vec.velocity, Vec.sign, Vec.length] at *
    refine ⟨hv, ?_⟩
    intro i; have hh := hy i; simp only [Lifted.y, compressed, hv i] at hh; omega
  have aux_rotation_of_represented_shift {n : ℕ} {A B : Lifted} {N M : Config n} (hA : A.Represents n N) (hB : B.Represents n M) (r c : ℤ) (hx : ∀ i, B.x i = A.x (i + r) + c) (hv : ∀ i, B.v i = A.v (i + r)) : M = (DihedralGroup.r (c : ZMod n)) • N := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift; funext p; change M p = N (p - (c : ZMod n)); cases hm : M p with
    | some v =>
      obtain ⟨i, hip, hiv⟩ := (hB p v).mp hm
      have hpos : (A.x (i + r) : ZMod n) = p - (c : ZMod n) := by
        apply eq_sub_iff_add_eq.mpr
        rw [← hip, hx i, Int.cast_add]
      have hn : N (p - (c : ZMod n)) = some v :=
        (hA _ v).mpr ⟨i + r, hpos, (hv i).symm.trans hiv⟩
      exact hn.symm
    | none =>
      cases hn : N (p - (c : ZMod n)) with
      | none => rfl
      | some v =>
        obtain ⟨j, hjp, hjv⟩ := (hA _ v).mp hn
        have hj : j - r + r = j := by omega
        have hpos : (B.x (j - r) : ZMod n) = p := by
          rw [hx, hj, Int.cast_add, hjp]; exact sub_add_cancel p (c : ZMod n)
        have hm' : M p = some v := (hB _ v).mpr ⟨j - r, hpos, by rw [hv, hj, hjv]⟩
        rw [hm] at hm'; cases hm'
  have aux_integer_window_shift (f : ℤ → ℤ) (h : ℕ) (C : ℤ) (hp : ∀ i, f (i + (h : ℤ)) = f i + C) (r : ℤ) : (∑ i ∈ Finset.range h, f ((i : ℤ) + r)) = (∑ i ∈ Finset.range h, f i) + C * r := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift; let W (r : ℤ) := ∑ i ∈ Finset.range h, f ((i : ℤ) + r); have hs : ∀ r, W (r + 1) = W r + C := by
      intro r; have ht := Finset.sum_range_sub (fun i : ℕ => f ((i : ℤ) + r)) h; have he : (∑ i ∈ Finset.range h, (f ((i : ℤ) + r + 1) - f ((i : ℤ) + r))) =
          W (r + 1) - W r := by
        rw [Finset.sum_sub_distrib]; dsimp [W]; congr 1; apply Finset.sum_congr rfl; intro i hi; congr 1; omega
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at ht; rw [show (h : ℤ) + r = r + h by omega, hp r] at ht; have hh : (∑ i ∈ Finset.range h, (f ((i : ℤ) + r + 1) - f ((i : ℤ) + r))) = C := by
        convert ht using 1
        · apply Finset.sum_congr rfl
          intro i hi; congr 2; omega
        · omega
      omega
    change W r = _; have h0 : W 0 = ∑ i ∈ Finset.range h, f i := by simp [W]
    rw [← h0]; induction r using Int.induction_on with
    | zero => simp
    | succ j ih => rw [hs, ih]; ring
    | pred j ih =>
      have ht := hs (-(j : ℤ) - 1); have he : -(j : ℤ) - 1 + 1 = -(j : ℤ) := by omega
      rw [he, ih] at ht; calc W (-(j : ℤ) - 1) = W 0 + C * -(j : ℤ) - C := by omega
        _ = W 0 + C * (-(j : ℤ) - 1) := by ring
  have aux_step_balance {A : Lifted} (hA : A.Admissible) (i : ℤ) : A.step.y i = A.y i + A.u i - A.collisionIndicator i + A.collisionIndicator (i - 1) ∧ A.step.u i = A.u i - 2 * A.collisionIndicator i + 2 * A.collisionIndicator (i - 1) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift; by_cases hi : A.collision i
    · obtain ⟨hd, hv, hw⟩ := (aux_fix_characterization (hA i)).mp hi
      have hn := ((aux_collision_disjoint (A := A)) hA i hi).2; simp [Lifted.step, Lifted.y, Lifted.u, Lifted.collisionIndicator, hi, hn, compressed, hv, Vec.value, Vec.turn, Vec.shorten, Vec.velocity, Vec.sign, Vec.length]; omega
    · by_cases hm : A.collision (i - 1)
      · obtain ⟨hd, hv, hw⟩ := (aux_fix_characterization (hA (i - 1))).mp hm
        have he : i - 1 + 1 = i := by omega
        rw [he] at hw; simp [Lifted.step, Lifted.y, Lifted.u, Lifted.collisionIndicator, hi, hm, compressed, hw, Vec.value, Vec.turn, Vec.shorten, Vec.velocity, Vec.sign, Vec.length]; omega
      · cases hv : A.v i <;> simp [Lifted.step, Lifted.y, Lifted.u, Lifted.collisionIndicator, hi, hm, compressed, hv, Vec.value, Vec.turn, Vec.shorten, Vec.velocity, Vec.sign, Vec.length] <;> omega
  have aux_window_balance {A : Lifted} (hA : A.Admissible) (h : ℕ) (n : ℤ) (hp : A.Periodic h n) : (∑ i ∈ Finset.range h, A.step.y i) = (∑ i ∈ Finset.range h, A.y i) + (∑ i ∈ Finset.range h, A.u i) ∧ (∑ i ∈ Finset.range h, A.step.u i) = (∑ i ∈ Finset.range h, A.u i) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift; have hflux := aux_integer_window_shift A.collisionIndicator h 0 (by
      intro i; simp [Lifted.collisionIndicator, (aux_collision_periodic (A := A)) hp]) (-1)
    simp only [mul_neg, mul_one] at hflux; have hy : (∑ i ∈ Finset.range h, A.step.y i) =
        (∑ i ∈ Finset.range h, A.y i) + (∑ i ∈ Finset.range h, A.u i) -
          (∑ i ∈ Finset.range h, A.collisionIndicator i) +
          (∑ i ∈ Finset.range h, A.collisionIndicator ((i : ℤ) - 1)) := by
      simp_rw [(aux_step_balance (A := A)) hA]; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hu : (∑ i ∈ Finset.range h, A.step.u i) =
        (∑ i ∈ Finset.range h, A.u i) - 2 * (∑ i ∈ Finset.range h, A.collisionIndicator i) +
          2 * (∑ i ∈ Finset.range h, A.collisionIndicator ((i : ℤ) - 1)) := by
      simp_rw [((aux_step_balance (A := A)) hA _).2]; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hf : (∑ i ∈ Finset.range h, A.collisionIndicator ((i : ℤ) - 1)) =
        ∑ i ∈ Finset.range h, A.collisionIndicator i := by simpa only [sub_eq_add_neg, neg_zero, add_zero] using hflux
    rw [hf] at hy hu; constructor <;> omega
  have aux_iterate_window_balance {A : Lifted} (hA : A.Admissible) (h : ℕ) (n : ℤ) (hp : A.Periodic h n) (t : ℕ) : (∑ i ∈ Finset.range h, ((Lifted.step)^[t] A).y i) = (∑ i ∈ Finset.range h, A.y i) + (t : ℤ) * (∑ i ∈ Finset.range h, A.u i) ∧ (∑ i ∈ Finset.range h, ((Lifted.step)^[t] A).u i) = (∑ i ∈ Finset.range h, A.u i) ∧ ((Lifted.step)^[t] A).Admissible ∧ ((Lifted.step)^[t] A).Periodic h n := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_compressed_period aux_collision_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance; induction t with
    | zero =>
      simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]; exact ⟨True.intro, True.intro, hA, hp⟩
    | succ t ih =>
      obtain ⟨hy, hu, had, hper⟩ := ih
      have hs := aux_window_balance had h n hper; rw [Function.iterate_succ_apply']; refine ⟨?_, ?_, aux_step_admissible had, aux_step_periodic hper⟩
      · rw [hs.1, hy, hu]
        simp only [Nat.cast_succ]; ring
      · exact hs.2.trans hu
  have aux_half_period_index {A : Lifted} (hA : A.Admissible) (L h n : ℕ) (hL : 0 < L) (hp : A.Periodic h n) (hc : 2 * (n : ℤ) - 3 * (h : ℤ) = 2 * (L : ℤ)) (r : ℤ) (hr : ∀ i, ((Lifted.step)^[L] A).y i = A.y (i + r) + (L : ℤ)) : r = -(∑ i ∈ Finset.range h, (A.v i).negativeVelocity) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_step_balance aux_window_balance; have hY : ∀ i, A.y (i + (h : ℤ)) = A.y i + 2 * (L : ℤ) := by
      intro i; have hh := ((aux_compressed_period (A := A)) hp i).1; omega
    have hs := aux_integer_window_shift A.y h (2 * (L : ℤ)) hY r; have hb := ((aux_iterate_window_balance (A := A)) hA h n hp L).1; simp_rw [hr] at hb; rw [Finset.sum_add_distrib, hs] at hb; simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb; have hu : (∑ i ∈ Finset.range h, A.u i) =
        (h : ℤ) - 2 * (∑ i ∈ Finset.range h, (A.v i).negativeVelocity) := by
      have he : ∀ i, A.u i = 1 - 2 * (A.v i).negativeVelocity := by
        intro i; cases hv : A.v i <;> simp [Lifted.u, hv, Vec.negativeVelocity, Vec.velocity, Vec.sign, Vec.length]
      simp_rw [he]; rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
    rw [hu] at hb; have he : (L : ℤ) * (2 * r) = (L : ℤ) * (-(2 * ∑ i ∈ Finset.range h, (A.v i).negativeVelocity)) := by
      calc
        (L : ℤ) * (2 * r) = 2 * (L : ℤ) * r := by ring
        _ = (L : ℤ) * ((h : ℤ) - 2 * ∑ i ∈ Finset.range h, (A.v i).negativeVelocity) - (h : ℤ) * (L : ℤ) := by omega
        _ = (L : ℤ) * (-(2 * ∑ i ∈ Finset.range h, (A.v i).negativeVelocity)) := by ring
    have hh := mul_left_cancel₀ (show (L : ℤ) ≠ 0 by omega) he
    omega
  have aux_sign_succ {A : Lifted} (hA : A.Admissible) (i : ℤ) : (A.v (i + 1)).sign = -(A.v i).sign := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index; have h := (hA i).2.1; cases hv : A.v i <;> cases hw : A.v (i + 1) <;> simp [hv, hw, Vec.positive, Vec.sign] at *
  have aux_sign_periodic {A : Lifted} (hA : A.Admissible) : Function.Periodic (fun i => (A.v i).sign) 2 := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index; intro i; have h1 := (aux_sign_succ (A := A)) hA i; have h2 := (aux_sign_succ (A := A)) hA (i + 1); have he : i + 1 + 1 = i + 2 := by omega
    rw [he, h1] at h2; simpa using h2
  have aux_sign_congr {A : Lifted} (hA : A.Admissible) (i j : ℤ) (he : i % 2 = j % 2) : (A.v i).sign = (A.v j).sign := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ; have hp := (aux_sign_periodic (A := A)) hA; have hi := (hp.int_mul (i / 2)) (i % 2); have hj := (hp.int_mul (j / 2)) (j % 2); simp only [Int.cast_id, Int.emod_add_ediv_mul] at hi hj; rw [hi, hj, he]
  have aux_iterate_sign {A : Lifted} (hA : A.Admissible) (t : ℕ) (i : ℤ) : (((Lifted.step)^[t] A).v i).sign = (A.v (i + (t : ℤ))).sign := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_periodic aux_sign_congr; have hstep : ∀ (D : Lifted) j, (D.step.v j).sign = -(D.v j).sign := by
      intro D j; dsimp [Lifted.step]; split_ifs <;> cases D.v j <;> rfl
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply', hstep, ih]; have hs := (aux_sign_succ (A := A)) hA (i + (t : ℤ)); simpa [Nat.cast_succ, add_assoc] using hs.symm
  have aux_positive_two_gap_parity {d e : ℤ} {v w z : Vec} (hd : PairAdmissible d v w) (he : PairAdmissible e w z) (hv : v.positive) : z.positive ∧ (d + e + v.negativeVelocity + w.negativeVelocity) % 2 = 1 := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign; cases v <;> cases w <;> cases z <;> simp [PairAdmissible, Vec.positive, Vec.length, Vec.negativeVelocity, Vec.velocity, Vec.sign, Int.odd_iff, Int.even_iff] at * <;> omega
  have aux_negative_count_parity {A : Lifted} (hA : A.Admissible) (n k : ℕ) (hn : Even n) (hp : A.Periodic (2 * (k : ℤ)) n) : (∑ i ∈ Finset.range (2 * k), (A.v i).negativeVelocity) % 2 = (k : ℤ) % 2 := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign; have hb : ∃ b : ℤ, (A.v b).positive := by
      by_cases h : (A.v 0).positive
      · exact ⟨0, h⟩
      · exact ⟨1, by
          have hw : (A.v (0 + 1)).positive := not_not.mp (fun hw => h ((hA 0).2.1.mpr hw)); simpa using hw⟩
    obtain ⟨b, hb⟩ := hb
    let Q (j : ℕ) : ℤ := ∑ i ∈ Finset.range (2 * j), (A.v (b + (i : ℤ))).negativeVelocity; have hi : ∀ j : ℕ, (A.v (b + 2 * (j : ℤ))).positive ∧
        (A.x (b + 2 * (j : ℤ)) - A.x b + Q j) % 2 = (j : ℤ) % 2 := by
      intro j; induction j with
      | zero => simpa [Q] using hb
      | succ j ih =>
        let a := b + 2 * (j : ℤ); have hp2 := aux_positive_two_gap_parity (hA a) (hA (a + 1)) ih.1; have he : a + 1 + 1 = a + 2 := by omega
        rw [he] at hp2; have hQ : Q (j + 1) = Q j + (A.v a).negativeVelocity + (A.v (a + 1)).negativeVelocity := by
          dsimp [Q]; rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]; simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]; dsimp [a]; simp only [add_assoc]
        constructor
        · convert hp2.1 using 1
          congr 1
          dsimp [a]
          try simp only [Nat.cast_succ]
          omega
        · have hh := ih.2
          change (A.x a - A.x b + Q j) % 2 = (j : ℤ) % 2 at hh; rw [hQ]; simp only [Nat.cast_succ]; have he : b + 2 * ((j : ℤ) + 1) = a + 2 := by dsimp [a]; omega
          rw [he]; have hh' := hp2.2; omega
    have hh := (hi k).2; rw [hp.1 b] at hh; have hQ : Q k = ∑ i ∈ Finset.range (2 * k), (A.v i).negativeVelocity := by
      have he := aux_integer_window_shift (fun i => (A.v i).negativeVelocity) (2 * k) 0 (by
        intro i; simp only [Nat.cast_mul, Nat.cast_ofNat, hp.2, add_zero]) b
      simpa [Q, add_comm] using he
    rw [hQ] at hh; rcases hn with ⟨m, hm⟩; simp only [hm, Nat.cast_add] at hh; omega
  have aux_cyclic_reconstruction : ∀ n k : ℕ, Even n → 1 ≤ k → ∀ A : Lifted, A.Admissible → A.Periodic (2 * (k : ℤ)) n → let L := n - 3 * k; let B := (Lifted.step)^[L] A; ∃ r : ℤ, (∀ i, B.y i = A.y (i + r) + (L : ℤ)) ∧ (∀ i, B.u i = A.u (i + r)) ∧ (∀ i, (B.v i).sign = (A.v (i + r)).sign) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_sign_succ aux_sign_periodic aux_positive_two_gap_parity; intro n k hn hk A hA hp; have hbound := (aux_length_bound (A := A)) k n hA hp; let L := n - 3 * k; have hL : 0 < L := by dsimp [L]; omega
    have hc : 2 * (n : ℤ) - 3 * ((2 * k : ℕ) : ℤ) = 2 * (L : ℤ) := by
      dsimp [L]
      try simp only [Nat.cast_mul, Nat.cast_ofNat]
      omega
    have hp' : A.Periodic (2 * k : ℕ) n := by simpa using hp
    obtain ⟨r, hr⟩ := (aux_half_period_relabel (A := A)) hA L (2 * k) n hp' hc
    have hind := (aux_half_period_index (A := A)) hA L (2 * k) n hL hp' hc r (fun i => (hr i).1); have hpar := (aux_negative_count_parity (A := A)) hA n k hn hp; have hpar' : r % 2 = (L : ℤ) % 2 := by
      rcases hn with ⟨m, hm⟩; dsimp [L]; rw [hind]; omega
    refine ⟨r, fun i => (hr i).1, fun i => (hr i).2, ?_⟩
    intro i; rw [(aux_iterate_sign (A := A)) hA L i]; exact (aux_sign_congr (A := A)) hA (i + (L : ℤ)) (i + r) (by omega)
  have aux_periodic_int_mul {A : Lifted} {h n : ℤ} (hp : A.Periodic h n) (i q : ℤ) : A.x (i + q * h) = A.x i + q * n ∧ A.v (i + q * h) = A.v i := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction; induction q using Int.induction_on with
    | zero => simp
    | succ j ih =>
      have he : i + ((j : ℤ) + 1) * h = (i + (j : ℤ) * h) + h := by ring
      rw [he, hp.1, hp.2, ih.1, ih.2]; constructor
      · ring
      · rfl
    | pred j ih =>
      have he : i + (-(j : ℤ) - 1) * h + h = i + -(j : ℤ) * h := by ring
      have hx := hp.1 (i + (-(j : ℤ) - 1) * h); have hv := hp.2 (i + (-(j : ℤ) - 1) * h); rw [he, ih.1] at hx; rw [he, ih.2] at hv; constructor
      · calc
          A.x (i + (-(j : ℤ) - 1) * h) = A.x i + -(j : ℤ) * n - n := by omega
          _ = A.x i + (-(j : ℤ) - 1) * n := by ring
      · exact hv.symm
  have aux_normalize_index {A : Lifted} {h n : ℕ} (hh : 0 < h) (hp : A.Periodic h n) (i j : ℤ) : ∃ a : ℤ, i ≤ a ∧ a < i + h ∧ (A.x a : ZMod n) = (A.x j : ZMod n) ∧ A.v a = A.v j := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction; let a := i + (j - i) % (h : ℤ); have hm0 : 0 ≤ (j - i) % (h : ℤ) := Int.emod_nonneg _ (by omega); have hmh : (j - i) % (h : ℤ) < (h : ℤ) := Int.emod_lt_of_pos _ (by omega); have he : a + ((j - i) / (h : ℤ)) * (h : ℤ) = j := by
      have he := Int.emod_add_ediv_mul (j - i) (h : ℤ); dsimp [a]; omega
    have ht := (aux_periodic_int_mul (A := A)) hp a ((j - i) / (h : ℤ)); rw [he] at ht; refine ⟨a, by dsimp [a]; omega, by dsimp [a]; omega, ?_, ht.2.symm⟩
    rw [ht.1, Int.cast_add, Int.cast_mul]; simp
  have aux_position_window_injective {A : Lifted} {h n : ℕ} (hx : StrictMono A.x) (hp : A.Periodic h n) (i a b : ℤ) (ha : i ≤ a ∧ a < i + h) (hb : i ≤ b ∧ b < i + h) (he : (A.x a : ZMod n) = (A.x b : ZMod n)) : a = b := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index; have ha0 : 0 ≤ A.x a - A.x i := by have := hx.monotone ha.1; omega
    have hb0 : 0 ≤ A.x b - A.x i := by have := hx.monotone hb.1; omega
    have han : A.x a - A.x i < (n : ℤ) := by have := hx ha.2; rw [hp.1 i] at this; omega
    have hbn : A.x b - A.x i < (n : ℤ) := by have := hx hb.2; rw [hp.1 i] at this; omega
    have he' : ((A.x a - A.x i : ℤ) : ZMod n) = ((A.x b - A.x i : ℤ) : ZMod n) := by
      simpa only [Int.cast_sub] using congrArg (fun p : ZMod n => p - (A.x i : ZMod n)) he
    have hm := (ZMod.intCast_eq_intCast_iff' _ _ n).mp he'; rw [Int.emod_eq_of_lt ha0 han, Int.emod_eq_of_lt hb0 hbn] at hm; apply hx.injective; omega
  have aux_clockwiseDistance_cast {n : ℕ} (hn : 0 < n) (x y : ℤ) (h0 : 0 ≤ y - x) (hlt : y - x < (n : ℤ)) : (clockwiseDistance (x : ZMod n) (y : ZMod n) : ℤ) = y - x := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective; letI : NeZero n := ⟨by omega⟩; unfold clockwiseDistance; rw [← Int.cast_sub, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]
  have aux_consecutive_project {A : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 0 < n) (hx : StrictMono A.x) (hp : A.Periodic h n) {N : Config n} (hr : A.Represents n N) (i : ℤ) : Consecutive N (A.x i : ZMod n) (A.x (i + 1) : ZMod n) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul; have hgap0 : 0 < A.x (i + 1) - A.x i := by have := hx (show i < i + 1 by omega); omega
    have hgapn : A.x (i + 1) - A.x i < (n : ℤ) := by
      have := hx (show i + 1 < i + h by omega)
      rw [hp.1 i] at this; omega
    have hd := aux_clockwiseDistance_cast hn (A.x i) (A.x (i + 1)) (by omega) hgapn
    refine ⟨?_, ⟨A.v i, (hr _ _).mpr ⟨i, rfl, rfl⟩⟩,
      ⟨A.v (i + 1), (hr _ _).mpr ⟨i + 1, rfl, rfl⟩⟩, ?_⟩
    · intro he
      have hh := (aux_position_window_injective (A := A)) hx hp i i (i + 1) ⟨le_rfl, by omega⟩
        ⟨by omega, by omega⟩ he
      omega
    · intro p hp0 hpd
      cases hv : N p with
      | none => rfl
      | some v =>
        obtain ⟨j, hjp, hjv⟩ := (hr p v).mp hv
        obtain ⟨a, hai, hah, hax, hav⟩ := (aux_normalize_index (A := A)) (by omega) hp i j
        have hpcast : (A.x a : ZMod n) = p := hax.trans hjp; have hag0 : 0 ≤ A.x a - A.x i := by have := hx.monotone hai; omega
        have hagn : A.x a - A.x i < (n : ℤ) := by
          have := hx hah; rw [hp.1 i] at this; omega
        have hda := aux_clockwiseDistance_cast hn (A.x i) (A.x a) hag0 hagn; rw [hpcast] at hda; have h1 : A.x i < A.x a := by omega
        have h2 : A.x a < A.x (i + 1) := by omega
        have hia := hx.lt_iff_lt.mp h1; have hai' := hx.lt_iff_lt.mp h2; omega
  have aux_necklace_of_represented {A : Lifted} {n k : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hA : A.Admissible) (hp : A.Periodic (2 * (k : ℤ)) n) {N : Config n} (hr : A.Represents n N) : IsNecklace k N := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_consecutive_project
    classical
    let h := 2 * k; have hh : 2 ≤ h := by dsimp [h]; omega
    have hp' : A.Periodic h n := by simpa [h] using hp
    have hx := ((aux_strict_order (A := A)) hA).1
    let f (i : Fin h) : ZMod n := A.x (i : ℤ)
    have hf : Function.Injective f := by
      intro i j he
      have hh := (aux_position_window_injective (A := A)) hx hp' 0 (i : ℤ) (j : ℤ)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
      apply Fin.ext
      omega
    refine ⟨hn, ⟨Finset.univ.image f, ?_, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    · intro p
      constructor
      · intro hmem
        obtain ⟨i, _, hip⟩ := Finset.mem_image.mp hmem
        exact ⟨A.v (i : ℤ), (hr p _).mpr ⟨(i : ℤ), hip, rfl⟩⟩
      · rintro ⟨v, hv⟩
        obtain ⟨j, hjp, hjv⟩ := (hr p v).mp hv
        obtain ⟨a, ha0, hah, hap, hav⟩ := (aux_normalize_index (A := A)) (by omega) hp' 0 j
        let i : Fin h := ⟨a.toNat, by omega⟩
        have hi : (i : ℤ) = a := by dsimp [i]; exact Int.toNat_of_nonneg ha0
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        dsimp [f]
        rw [hi]
        exact hap.trans hjp
    · intro p q v w hcon hpv hqw
      obtain ⟨i, hip, hiv⟩ := (hr p v).mp hpv
      obtain ⟨j, hjq, hjw⟩ := (hr q w).mp hqw
      obtain ⟨a, hai, hah, hap, hav⟩ := (aux_normalize_index (A := A)) (by omega) hp' i j
      have haq : (A.x a : ZMod n) = q := hap.trans hjq
      have hia : i < a := by
        by_contra h
        have he : a = i := by omega
        rw [he, hip] at haq
        exact hcon.1 haq
      have hag0 : 0 ≤ A.x a - A.x i := by have := hx.monotone hai; omega
      have hagn : A.x a - A.x i < (n : ℤ) := by
        have := hx hah
        rw [hp'.1 i] at this
        omega
      have hda := aux_clockwiseDistance_cast hn (A.x i) (A.x a) hag0 hagn
      rw [hip, haq] at hda
      have ha : a = i + 1 := by
        by_contra hne
        have hsmall : i + 1 < a := by omega
        have hg0 : 0 < A.x (i + 1) - A.x i := by have := hx (show i < i + 1 by omega); omega
        have hgn : A.x (i + 1) - A.x i < (n : ℤ) := by have := hx hsmall; omega
        have hd := aux_clockwiseDistance_cast hn (A.x i) (A.x (i + 1)) (by omega) hgn
        rw [hip] at hd
        have hs := hcon.2.2.2 (A.x (i + 1) : ZMod n)
          (by omega) (by have := hx hsmall; omega)
        have ht := (hr _ (A.v (i + 1))).mpr ⟨i + 1, rfl, rfl⟩
        rw [hs] at ht
        cases ht
      rw [ha] at hav hda
      have hval := hA i
      rw [hiv, hav.trans hjw, ← hda] at hval
      exact hval
  have aux_cyclicPosition_strict {h : ℕ} (hh : 0 < h) (n : ℤ) (_hn : 0 < n) (f : Fin h → ℤ) (hf : StrictMono f) (hb : ∀ j, 0 ≤ f j ∧ f j < n) (hh2 : 2 ≤ h) : StrictMono (cyclicPosition hh n f) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented
    letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
    apply strictMono_int_of_lt_succ
    intro i
    have hi := Fin.val_intCast (n := h) i
    have hj := Fin.val_intCast (n := h) (i + 1)
    have hquot := Int.emod_add_ediv_mul i (h : ℤ)
    have hquot' := Int.emod_add_ediv_mul (i + 1) (h : ℤ)
    have hr0 := Int.emod_nonneg i (show (h : ℤ) ≠ 0 by omega)
    have hrlt := Int.emod_lt_of_pos i (show 0 < (h : ℤ) by omega)
    have hs0 := Int.emod_nonneg (i + 1) (show (h : ℤ) ≠ 0 by omega)
    have hslt := Int.emod_lt_of_pos (i + 1) (show 0 < (h : ℤ) by omega)
    have hmod : (i + 1) % (h : ℤ) = (i % (h : ℤ) + 1) % (h : ℤ) := by
      rw [Int.add_emod]
      rw [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < h)]
    have hdiv := Int.add_ediv_of_pos (a := i) (b := 1) (show 0 < (h : ℤ) by omega)
    rw [Int.ediv_eq_zero_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < h), Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < h)] at hdiv
    dsimp [cyclicPosition]
    by_cases hlast : i % (h : ℤ) + 1 < (h : ℤ)
    · have hr : (i + 1) % (h : ℤ) = i % (h : ℤ) + 1 := by
        rw [hmod, Int.emod_eq_of_lt (by omega) hlast]
      have hq : (i + 1) / (h : ℤ) = i / (h : ℤ) := by
        simpa [show ¬ (h : ℤ) ≤ i % (h : ℤ) + 1 by omega] using hdiv
      have hindex : (i : Fin h) < ((i + 1 : ℤ) : Fin h) := by
        change ((i : Fin h)).val < (((i + 1 : ℤ) : Fin h)).val
        omega
      rw [hq]
      have := hf hindex
      omega
    · have hr : (i + 1) % (h : ℤ) = 0 := by
        rw [hmod, show i % (h : ℤ) + 1 = h by omega, Int.emod_self]
      have hq : (i + 1) / (h : ℤ) = i / (h : ℤ) + 1 := by
        simpa [show (h : ℤ) ≤ i % (h : ℤ) + 1 by omega] using hdiv
      rw [hq, mul_add, mul_one]
      have h1 := (hb ((i : Fin h))).2
      have h2 := (hb (((i + 1 : ℤ) : Fin h))).1
      omega
  have aux_cyclicPosition_period {h : ℕ} (hh : 0 < h) (n : ℤ) (f : Fin h → ℤ) (i : ℤ) : cyclicPosition hh n f (i + (h : ℤ)) = cyclicPosition hh n f i + n := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict
    letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
    unfold cyclicPosition
    have hindex : ((i + (h : ℤ) : ℤ) : Fin h) = (i : Fin h) := by
      apply Fin.ext
      simp only [Fin.val_intCast, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
    rw [hindex]
    have he : (i + (h : ℤ)) / (h : ℤ) = i / (h : ℤ) + 1 := by
      rw [Int.add_ediv_of_dvd_right (show (h : ℤ) ∣ (h : ℤ) by exact dvd_refl _)]
      rw [Int.ediv_self (show (h : ℤ) ≠ 0 by omega)]
    rw [he]
    ring
  have aux_representation : ∀ n k : ℕ, Even n → 1 ≤ k → ∀ N : Config n, IsNecklace k N → ∃ A : Lifted, A.Admissible ∧ A.Periodic (2 * (k : ℤ)) n ∧ A.Represents n N := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_necklace_of_represented
    classical
    intro n k hn hk N hN
    have hnpos := hN.1
    letI : NeZero n := ⟨by omega⟩
    obtain ⟨S, hSc, hS⟩ := hN.2.1
    let U : Finset ℕ := S.image ZMod.val
    have hUc : U.card = 2 * k := by
      rw [Finset.card_image_of_injective _ (ZMod.val_injective n)]
      exact hSc
    let h := 2 * k
    have hh : 0 < h := by dsimp [h]; omega
    have hh2 : 2 ≤ h := by dsimp [h]; omega
    letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
    let e : Fin h ↪o ℕ := U.orderEmbOfFin hUc
    let f (j : Fin h) : ℤ := e j
    let V (j : Fin h) : Vec := (N ((e j : ℕ) : ZMod n)).getD Vec.posOne
    have heN : ∀ j : Fin h, N ((e j : ℕ) : ZMod n) = some (V j) := by
      intro j
      have hemem : e j ∈ U := U.orderEmbOfFin_mem hUc j
      obtain ⟨p, hpS, hep⟩ := Finset.mem_image.mp hemem
      have hcast : ((e j : ℕ) : ZMod n) = p := by rw [← hep, ZMod.natCast_zmod_val]
      obtain ⟨v, hv⟩ := (hS p).mp hpS
      simp [V, hcast, hv]
    have hb : ∀ j : Fin h, 0 ≤ f j ∧ f j < (n : ℤ) := by
      intro j
      have hemem : e j ∈ U := U.orderEmbOfFin_mem hUc j
      obtain ⟨p, hpS, hep⟩ := Finset.mem_image.mp hemem
      have hpn := ZMod.val_lt p
      dsimp [f]
      omega
    let A : Lifted := ⟨cyclicPosition hh n f, fun i => V ((i : Fin h))⟩
    have hx : StrictMono A.x := aux_cyclicPosition_strict hh n (by omega) f
      (by intro i j hij; have := e.strictMono hij; dsimp [f]; omega) hb hh2
    have hp : A.Periodic h n := by
      constructor
      · exact aux_cyclicPosition_period hh n f
      · intro i
        apply congrArg V
        apply Fin.ext
        simp only [Fin.val_intCast, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
    have hr : A.Represents n N := by
      intro p v
      constructor
      · intro hNv
        have hps : p ∈ S := (hS p).mpr ⟨v, hNv⟩
        have hpU : p.val ∈ U := Finset.mem_image.mpr ⟨p, hps, rfl⟩
        obtain ⟨j, hj⟩ : ∃ j : Fin h, e j = p.val := by
          have hh : p.val ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hpU
          exact hh
        have hidx : ((j : ℤ) : Fin h) = j := by
          apply Fin.ext
          simp only [Fin.val_intCast, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ j) (by omega : (j : ℤ) < h), Int.toNat_natCast]
        refine ⟨(j : ℤ), ?_, ?_⟩
        · change ((cyclicPosition hh n f (j : ℤ) : ℤ) : ZMod n) = p
          simp [cyclicPosition, hidx, Int.ediv_eq_zero_of_lt (by omega : (0 : ℤ) ≤ j) (by omega : (j : ℤ) < h), f, hj]
        · change V (((j : ℤ) : Fin h)) = v
          rw [hidx]
          have hv := heN j
          rw [hj, ZMod.natCast_zmod_val, hNv] at hv
          exact Option.some.inj hv.symm
      · rintro ⟨i, hip, hiv⟩
        have hcast : (A.x i : ZMod n) = ((e ((i : Fin h)) : ℕ) : ZMod n) := by
          change ((f ((i : Fin h)) + (n : ℤ) * (i / h) : ℤ) : ZMod n) = _
          simp [f]
        have hv := heN ((i : Fin h))
        rw [← hcast, hip] at hv
        exact hv.trans (congrArg some hiv)
    have had : A.Admissible := by
      intro i
      have hcon := (aux_consecutive_project (A := A)) hh2 hnpos hx hp hr i
      have hv := (hr _ (A.v i)).mpr ⟨i, rfl, rfl⟩
      have hw := (hr _ (A.v (i + 1))).mpr ⟨i + 1, rfl, rfl⟩
      have ht := hN.2.2 _ _ _ _ hcon hv hw
      have hg0 : 0 < A.x (i + 1) - A.x i := by have := hx (show i < i + 1 by omega); omega
      have hgn : A.x (i + 1) - A.x i < (n : ℤ) := by
        have := hx (show i + 1 < i + h by omega)
        rw [hp.1 i] at this
        omega
      rw [aux_clockwiseDistance_cast hnpos (A.x i) (A.x (i + 1)) (by omega) hgn] at ht
      exact ht
    refine ⟨A, had, ?_, hr⟩
    simpa [h] using hp
  have aux_jumped_strict {A : Lifted} (hA : A.Admissible) : StrictMono A.jumped.x := by
    clear aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation
    apply strictMono_int_of_lt_succ
    intro i
    have hg := aux_jump_does_not_cross (hA i)
    dsimp [jumpedGap, Lifted.jumped] at *
    omega
  have aux_jumped_periodic {A : Lifted} {h n : ℤ} (hp : A.Periodic h n) : A.jumped.Periodic h n := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict
    constructor
    · intro i
      dsimp [Lifted.jumped]
      rw [hp.1, hp.2]
      omega
    · intro i
      dsimp [Lifted.jumped]
      rw [hp.2]
  have aux_jump_inflow_unique {A : Lifted} {h n : ℕ} (hh : 0 < h) (hA : A.Admissible) (hp : A.Periodic h n) {N : Config n} (hr : A.Represents n N) (i : ℤ) (p : ZMod n) (v : Vec) (hv : N p = some v) (hq : (A.jumped.x i : ZMod n) = p + (v.value : ZMod n)) : A.v i = v := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation
    obtain ⟨j, hjp, hjv⟩ := (hr p v).mp hv
    obtain ⟨b, hbi, hbh, hbx, hbv⟩ := (aux_normalize_index (A := A)) hh hp i j
    have hcast : (A.jumped.x b : ZMod n) = p + (v.value : ZMod n) := by
      dsimp [Lifted.jumped]
      rw [Int.cast_add, hbx, hjp, hbv, hjv]
    have hbe := (aux_position_window_injective (A := A.jumped)) ((aux_jumped_strict (A := A)) hA) ((aux_jumped_periodic (A := A)) hp)
      i b i ⟨hbi, hbh⟩ ⟨le_rfl, by omega⟩ (hcast.trans hq.symm)
    rw [hbe] at hbv
    exact hbv.trans hjv
  have aux_jumpTurn_represents {A : Lifted} {h n : ℕ} (hh : 0 < h) (hA : A.Admissible) (hp : A.Periodic h n) {N : Config n} (hr : A.Represents n N) : A.jumped.Represents n (jumpTurn n N) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic
    classical
    intro q v
    constructor
    · intro hv
      change (if hd : ∃ a : ZMod n × Vec, N a.1 = some a.2 ∧ q = a.1 + (a.2.value : ZMod n)
        then some (Classical.choose hd).2.turn else none) = some v at hv
      split_ifs at hv with hd
      · obtain ⟨hs, hq⟩ := Classical.choose_spec hd
        obtain ⟨i, hip, hiv⟩ := (hr _ _).mp hs
        refine ⟨i, ?_, ?_⟩
        · dsimp [Lifted.jumped]
          rw [Int.cast_add, hip, hiv]
          exact hq.symm
        · dsimp [Lifted.jumped]
          rw [hiv]
          exact Option.some.inj hv
    · rintro ⟨i, hip, hiv⟩
      have hd : ∃ a : ZMod n × Vec, N a.1 = some a.2 ∧ q = a.1 + (a.2.value : ZMod n) := by
        refine ⟨⟨(A.x i : ZMod n), A.v i⟩, (hr _ _).mpr ⟨i, rfl, rfl⟩, ?_⟩
        rw [← hip]
        simp [Lifted.jumped]
      change (if hd' : ∃ a : ZMod n × Vec, N a.1 = some a.2 ∧ q = a.1 + (a.2.value : ZMod n)
        then some (Classical.choose hd').2.turn else none) = some v
      rw [dif_pos hd]
      obtain ⟨hs, hq⟩ := Classical.choose_spec hd
      have he := (aux_jump_inflow_unique (A := A)) hh hA hp hr i (Classical.choose hd).1
        (Classical.choose hd).2 hs (hip.trans hq)
      rw [← he]
      exact congrArg some hiv
  have aux_jumped_two_gap_bound {d e : ℤ} {v w z : Vec} (hd : PairAdmissible d v w) (he : PairAdmissible e w z) : 4 ≤ jumpedGap d v w + jumpedGap e w z := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents
    cases v <;> cases w <;> cases z <;> simp [PairAdmissible, Vec.positive, Vec.length, Vec.value, jumpedGap, Int.odd_iff, Int.even_iff] at * <;> omega
  have aux_jumped_two_gap {A : Lifted} (hA : A.Admissible) (i : ℤ) : A.jumped.x i + 4 ≤ A.jumped.x (i + 2) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents
    have hh := aux_jumped_two_gap_bound (hA i) (hA (i + 1))
    have he : i + 1 + 1 = i + 2 := by omega
    rw [he] at hh
    dsimp [jumpedGap, Lifted.jumped] at *
    omega
  have aux_at_three_forward {J : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 4 ≤ n) (hx : StrictMono J.x) (hp : J.Periodic h n) (h2 : ∀ i, J.x i + 4 ≤ J.x (i + 2)) (i j : ℤ) (he : (J.x j : ZMod n) = (J.x i : ZMod n) + 3) : J.x (i + 1) = J.x i + 3 ∧ J.v (i + 1) = J.v j := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_jumped_two_gap
    obtain ⟨b, hbi, hbh, hbx, hbv⟩ := (aux_normalize_index (A := J)) (by omega) hp i j
    have hb0 : 0 ≤ J.x b - J.x i := by have := hx.monotone hbi; omega
    have hbn : J.x b - J.x i < (n : ℤ) := by have := hx hbh; rw [hp.1 i] at this; omega
    have he' : ((J.x b - J.x i : ℤ) : ZMod n) = ((3 : ℤ) : ZMod n) := by
      simp only [Int.cast_sub, Int.cast_ofNat]
      rw [hbx, he]
      ring
    have hm := (ZMod.intCast_eq_intCast_iff' _ _ n).mp he'
    rw [Int.emod_eq_of_lt hb0 hbn, Int.emod_eq_of_lt (by omega) (by omega)] at hm
    have hb : b = i + 1 := by
      have hia : i < b := hx.lt_iff_lt.mp (by omega)
      by_contra hne
      have hbi2 : i + 2 ≤ b := by omega
      have hxb := hx.monotone hbi2
      have hbound := h2 i
      omega
    rw [hb] at hm hbv
    exact ⟨by omega, hbv⟩
  have aux_at_three_backward {J : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 4 ≤ n) (hx : StrictMono J.x) (hp : J.Periodic h n) (h2 : ∀ i, J.x i + 4 ≤ J.x (i + 2)) (i j : ℤ) (he : (J.x j : ZMod n) = (J.x i : ZMod n) - 3) : J.x (i - 1) = J.x i - 3 ∧ J.v (i - 1) = J.v j := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_jumped_two_gap aux_at_three_forward
    obtain ⟨b, hbi, hbh, hbx, hbv⟩ := (aux_normalize_index (A := J)) (by omega) hp (i - (h : ℤ)) j
    have hper : J.x (i - (h : ℤ)) = J.x i - n := by
      have he := hp.1 (i - (h : ℤ))
      have hi : i - (h : ℤ) + h = i := by omega
      rw [hi] at he
      omega
    have hb0 : 0 ≤ J.x b - J.x (i - (h : ℤ)) := by have := hx.monotone hbi; omega
    have hbn : J.x b - J.x (i - (h : ℤ)) < (n : ℤ) := by
      have := hx (show b < i by omega)
      omega
    have he' : ((J.x b - J.x (i - (h : ℤ)) : ℤ) : ZMod n) = (((n : ℤ) - 3 : ℤ) : ZMod n) := by
      simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, ZMod.natCast_self]
      rw [hbx, he, hper, Int.cast_sub, Int.cast_natCast, ZMod.natCast_self]
      ring
    have hm := (ZMod.intCast_eq_intCast_iff' _ _ n).mp he'
    rw [Int.emod_eq_of_lt hb0 hbn, Int.emod_eq_of_lt (by omega) (by omega)] at hm
    rw [hper] at hm
    have hb : b = i - 1 := by
      have hia : b < i := hx.lt_iff_lt.mp (by omega)
      by_contra hne
      have hbi2 : b ≤ i - 2 := by omega
      have hxb := hx.monotone hbi2
      have hbound := h2 (i - 2)
      have hi : i - 2 + 2 = i := by omega
      rw [hi] at hbound
      omega
    rw [hb] at hm hbv
    exact ⟨by omega, hbv⟩
  have aux_fix_forward {A : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 4 ≤ n) (hA : A.Admissible) (hp : A.Periodic h n) {M : Config n} (hr : A.jumped.Represents n M) (i : ℤ) (hpos : (A.v i).turn.positive) : (∃ w, M ((A.jumped.x i : ZMod n) + 3) = some w ∧ ¬ w.positive) ↔ A.collision i := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_at_three_backward
    constructor
    · rintro ⟨w, hw, hneg⟩
      obtain ⟨j, hjp, hjv⟩ := (hr _ _).mp hw
      have ht := (aux_at_three_forward (J := A.jumped)) hh hn ((aux_jumped_strict (A := A)) hA) ((aux_jumped_periodic (A := A)) hp)
        ((aux_jumped_two_gap (A := A)) hA) i j hjp
      have hv : (A.v (i + 1)).turn = w := ht.2.trans hjv
      change (A.v i).turn.positive ∧ ¬ (A.v (i + 1)).turn.positive ∧
        jumpedGap (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1)) = 3
      refine ⟨hpos, by rw [hv]; exact hneg, ?_⟩
      have he := ht.1
      dsimp [Lifted.jumped, jumpedGap] at *
      omega
    · intro hc
      have hcond := hc
      change (A.v i).turn.positive ∧ ¬ (A.v (i + 1)).turn.positive ∧
        jumpedGap (A.x (i + 1) - A.x i) (A.v i) (A.v (i + 1)) = 3 at hcond
      refine ⟨(A.v (i + 1)).turn, ?_, hcond.2.1⟩
      apply (hr _ _).mpr
      refine ⟨i + 1, ?_, rfl⟩
      have hx : A.jumped.x (i + 1) = A.jumped.x i + 3 := by
        dsimp [Lifted.jumped, jumpedGap] at *
        omega
      rw [hx, Int.cast_add, Int.cast_ofNat]
  have aux_fix_backward {A : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 4 ≤ n) (hA : A.Admissible) (hp : A.Periodic h n) {M : Config n} (hr : A.jumped.Represents n M) (i : ℤ) (hneg : ¬ (A.v i).turn.positive) : (∃ w, M ((A.jumped.x i : ZMod n) - 3) = some w ∧ w.positive) ↔ A.collision (i - 1) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_at_three_forward aux_fix_forward
    constructor
    · rintro ⟨w, hw, hpos⟩
      obtain ⟨j, hjp, hjv⟩ := (hr _ _).mp hw
      have ht := (aux_at_three_backward (J := A.jumped)) hh hn ((aux_jumped_strict (A := A)) hA) ((aux_jumped_periodic (A := A)) hp)
        ((aux_jumped_two_gap (A := A)) hA) i j hjp
      have hv : (A.v (i - 1)).turn = w := ht.2.trans hjv
      have hi : i - 1 + 1 = i := by omega
      change (A.v (i - 1)).turn.positive ∧ ¬ (A.v (i - 1 + 1)).turn.positive ∧
        jumpedGap (A.x (i - 1 + 1) - A.x (i - 1)) (A.v (i - 1)) (A.v (i - 1 + 1)) = 3
      rw [hi]
      refine ⟨by rw [hv]; exact hpos, hneg, ?_⟩
      have he := ht.1
      dsimp [Lifted.jumped, jumpedGap] at *
      omega
    · intro hc
      have hcond := hc
      have hi : i - 1 + 1 = i := by omega
      change (A.v (i - 1)).turn.positive ∧ ¬ (A.v (i - 1 + 1)).turn.positive ∧
        jumpedGap (A.x (i - 1 + 1) - A.x (i - 1)) (A.v (i - 1)) (A.v (i - 1 + 1)) = 3 at hcond
      rw [hi] at hcond
      refine ⟨(A.v (i - 1)).turn, ?_, hcond.1⟩
      apply (hr _ _).mpr
      refine ⟨i - 1, ?_, rfl⟩
      have hx : A.jumped.x (i - 1) = A.jumped.x i - 3 := by
        dsimp [Lifted.jumped, jumpedGap] at *
        omega
      rw [hx, Int.cast_sub, Int.cast_ofNat]
  have aux_fix_at_index {A : Lifted} {h n : ℕ} (hh : 2 ≤ h) (hn : 4 ≤ n) (hA : A.Admissible) (hp : A.Periodic h n) {M : Config n} (hr : A.jumped.Represents n M) (i : ℤ) : fix n M (A.jumped.x i : ZMod n) = some (A.step.v i) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_jumped_two_gap aux_at_three_forward aux_at_three_backward
    have hm : M (A.jumped.x i : ZMod n) = some (A.v i).turn :=
      (hr _ _).mpr ⟨i, rfl, rfl⟩
    classical
    unfold fix
    rw [hm]
    by_cases hpos : (A.v i).turn.positive
    · have hno : ¬ A.collision (i - 1) := by
        intro hc
        have hv := ((aux_fix_characterization (hA (i - 1))).mp hc).2.2
        have hi : i - 1 + 1 = i := by omega
        rw [hi] at hv
        simp [hv, Vec.turn, Vec.positive] at hpos
      simp only [if_pos hpos, (aux_fix_forward (A := A)) hh hn hA hp hr i hpos]
      dsimp [Lifted.step]
      simp only [hno, or_false]
      split_ifs <;> rfl
    · have hno : ¬ A.collision i := by
        intro hc
        have hv := ((aux_fix_characterization (hA i)).mp hc).2.1
        simp [hv, Vec.turn, Vec.positive] at hpos
      simp only [if_neg hpos, (aux_fix_backward (A := A)) hh hn hA hp hr i hpos]
      dsimp [Lifted.step]
      simp only [hno, false_or]
      split_ifs <;> rfl
  have aux_necklaceT_represents {A : Lifted} {n k : ℕ} (hk : 1 ≤ k) (hA : A.Admissible) (hp : A.Periodic (2 * (k : ℤ)) n) {N : Config n} (hr : A.Represents n N) : A.step.Represents n (necklaceT n N) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_pair_step_admissible aux_step_admissible aux_compressed_period aux_collision_periodic aux_step_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_necklace_of_represented aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumped_two_gap_bound aux_jumped_two_gap aux_at_three_forward aux_at_three_backward aux_fix_forward aux_fix_backward
    classical
    let h := 2 * k
    have hh : 2 ≤ h := by dsimp [h]; omega
    have hp' : A.Periodic h n := by simpa [h] using hp
    have hn : 4 ≤ n := by have := (aux_length_bound (A := A)) k n hA hp; omega
    have hM := (aux_jumpTurn_represents (A := A)) (by omega) hA hp' hr
    have hfix := (aux_fix_at_index (A := A)) hh hn hA hp' hM
    intro p v
    constructor
    · intro hv
      change fix n (jumpTurn n N) p = some v at hv
      have hstone : HasStone (jumpTurn n N) p := by
        cases hm : jumpTurn n N p with
        | none => simp [fix, hm] at hv
        | some w => exact ⟨w, hm⟩
      obtain ⟨w, hw⟩ := hstone
      obtain ⟨i, hip, hiv⟩ := (hM p w).mp hw
      have ht := hfix i
      rw [hip, hv] at ht
      exact ⟨i, hip, Option.some.inj ht.symm⟩
    · rintro ⟨i, hip, hiv⟩
      have ht := hfix i
      change (A.jumped.x i : ZMod n) = p at hip
      rw [hip, hiv] at ht
      exact ht
  have aux_physical_step : ∀ n k : ℕ, Even n → 1 ≤ k → ∀ (N : Config n) (A : Lifted), IsNecklace k N → A.Admissible → A.Periodic (2 * (k : ℤ)) n → A.Represents n N → IsNecklace k (necklaceT n N) ∧ A.step.Represents n (necklaceT n N) := by
    clear aux_jump_does_not_cross aux_compressed_strict aux_fix_characterization aux_collision_disjoint aux_swapIndex_involutive aux_step_conjugacy aux_two_pair_bound aux_two_gap_bound aux_length_bound aux_pair_step_admissible aux_compressed_period aux_collision_periodic aux_iterate_conjugacy aux_strict_order aux_int_strictMono_surjective_translation aux_half_period_relabel aux_reconstruct_shift aux_rotation_of_represented_shift aux_integer_window_shift aux_step_balance aux_window_balance aux_iterate_window_balance aux_half_period_index aux_sign_succ aux_sign_periodic aux_sign_congr aux_iterate_sign aux_positive_two_gap_parity aux_negative_count_parity aux_cyclic_reconstruction aux_periodic_int_mul aux_normalize_index aux_position_window_injective aux_clockwiseDistance_cast aux_consecutive_project aux_cyclicPosition_strict aux_cyclicPosition_period aux_representation aux_jumped_strict aux_jumped_periodic aux_jump_inflow_unique aux_jumpTurn_represents aux_jumped_two_gap_bound aux_jumped_two_gap aux_at_three_forward aux_at_three_backward aux_fix_forward aux_fix_backward aux_fix_at_index
    intro n k hn hk N A hN hA hp hr
    have hrep := (aux_necklaceT_represents (A := A)) hk hA hp hr
    refine ⟨?_, hrep⟩
    exact (aux_necklace_of_represented (A := A.step)) hk hN.1 ((aux_step_admissible (A := A)) hA) ((aux_step_periodic (A := A)) hp) hrep
  have hrep := aux_representation
  have hstep := aux_physical_step
  have hrecon := aux_cyclic_reconstruction
  intro n k hn hk N hN
  obtain ⟨A, hAd, hp, hAN⟩ := hrep n k hn hk N hN
  have hi : ∀ t : ℕ,
      IsNecklace k ((necklaceT n)^[t] N) ∧
      ((Lifted.step)^[t] A).Admissible ∧
      ((Lifted.step)^[t] A).Periodic (2 * (k : ℤ)) n ∧
      ((Lifted.step)^[t] A).Represents n ((necklaceT n)^[t] N) := by
    intro t
    induction t with
    | zero => simpa using And.intro hN (And.intro hAd (And.intro hp hAN))
    | succ t ih =>
      obtain ⟨hNt, hAt, hpt, hrepT⟩ := ih
      have ht := hstep n k hn hk ((necklaceT n)^[t] N) ((Lifted.step)^[t] A)
        hNt hAt hpt hrepT
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ⟨ht.1, aux_step_admissible hAt, aux_step_periodic hpt, ht.2⟩
  let L := n - 3 * k
  obtain ⟨r, hy, hu, hs⟩ := hrecon n k hn hk A hAd hp
  obtain ⟨hv, hx⟩ := aux_reconstruct_shift hy hu hs
  refine ⟨DihedralGroup.r ((((L : ℤ) - 3 * r) / 2 : ℤ) : ZMod n), ?_⟩
  exact aux_rotation_of_represented_shift hAN (hi L).2.2.2 r
    (((L : ℤ) - 3 * r) / 2) hx hv
end D5.S3.StatisticalMechanics.HardCore.HardSquareNecklacePeriod
