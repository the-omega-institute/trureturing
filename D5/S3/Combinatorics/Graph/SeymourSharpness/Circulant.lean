/- GID: D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SeymourSharpness/Circulant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal first and exact second degrees of the short-arc modular circulant. -/

module

public import D5.S3.Combinatorics.Graph.SeymourSharpness.Neighborhoods
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega

/-! The circulant with offsets from one through half the nonzero residues. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SeymourSharpness

def half (n : ℕ) : ℕ := (n - 1) / 2

def circulant (n : ℕ) (x y : ZMod n) : Prop :=
  0 < (y - x).val ∧ (y - x).val ≤ half n

private lemma twice_half_lt {n : ℕ} [NeZero n] : 2 * half n < n := by
  have hn := NeZero.pos n
  unfold half
  omega

private lemma offset_sum {n : ℕ} (x y z : ZMod n) :
    z - x = (y - x) + (z - y) := by abel

theorem circulant_asymm (n : ℕ) [NeZero n] :
    ∀ ⦃x y : ZMod n⦄, circulant n x y → ¬ circulant n y x := by
  intro x y hxy hyx
  unfold circulant at hxy hyx
  have hh := twice_half_lt (n := n)
  have hlt : (y - x).val + (x - y).val < n := by omega
  have h := ZMod.val_add_of_lt hlt
  have he : (y - x) + (x - y) = 0 := by abel
  rw [he] at h
  simp only [ZMod.val_zero] at h
  omega

/-- Exact second offsets form the next interval, with no modular wraparound. -/
theorem circulant_exact_second (n : ℕ) [NeZero n] (x z : ZMod n) :
    ExactSecond (circulant n) x z ↔
      half n < (z - x).val ∧ (z - x).val ≤ 2 * half n := by
  have hh := twice_half_lt (n := n)
  constructor
  · rintro ⟨hne,hnadj,⟨y,hxy,hyz⟩⟩
    change 0 < (y - x).val ∧ (y - x).val ≤ half n at hxy
    change 0 < (z - y).val ∧ (z - y).val ≤ half n at hyz
    have hlt : (y - x).val + (z - y).val < n := by omega
    have hv : (z - x).val = (y - x).val + (z - y).val := by
      rw [offset_sum x y z, ZMod.val_add_of_lt hlt]
    have hz : 0 < (z - x).val := by omega
    change ¬ (0 < (z - x).val ∧ (z - x).val ≤ half n) at hnadj
    omega
  · rintro ⟨hlo,hhi⟩
    have ht : 0 < half n := by omega
    let y : ZMod n := x + (half n : ZMod n)
    have hy : (y - x).val = half n := by
      dsimp [y]
      rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
    have he : z - y = ((z - x).val - half n : ℕ) := by
      dsimp [y]
      rw [Nat.cast_sub (by omega : half n ≤ (z - x).val), ZMod.natCast_zmod_val]
      abel
    have hz : (z - y).val = (z - x).val - half n := by
      rw [he, ZMod.val_natCast_of_lt (by omega)]
    refine ⟨?_,?_,⟨y,?_,?_⟩⟩
    · intro h
      subst z
      simp only [sub_self, ZMod.val_zero] at hlo
      omega
    · change ¬ (0 < (z - x).val ∧ (z - x).val ≤ half n)
      omega
    · change 0 < (y - x).val ∧ (y - x).val ≤ half n
      omega
    · change 0 < (z - y).val ∧ (z - y).val ≤ half n
      omega

private noncomputable def offsetEquiv (n : ℕ) [NeZero n] (x : ZMod n)
    (lo hi : ℕ) (hhi : hi < n) :
    {y : ZMod n // lo < (y - x).val ∧ (y - x).val ≤ hi} ≃ ↥(Finset.Ioc lo hi) := by
  classical
  apply Equiv.ofBijective (fun y => ⟨(y.1 - x).val, Finset.mem_Ioc.mpr y.2⟩)
  constructor
  · intro y z h
    apply Subtype.ext
    apply sub_left_injective (b := x)
    apply ZMod.val_injective n
    exact congrArg Subtype.val h
  · intro j
    have hj := Finset.mem_Ioc.mp j.2
    have hv : ((x + (j.1 : ZMod n)) - x).val = j.1 := by
      rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by omega)]
    refine ⟨⟨x + (j.1 : ZMod n),by rw [hv]; exact hj⟩,?_⟩
    apply Subtype.ext
    exact hv

private lemma offset_card (n : ℕ) [NeZero n] (x : ZMod n)
    (lo hi : ℕ) (hhi : hi < n) :
    Nat.card {y : ZMod n // lo < (y - x).val ∧ (y - x).val ≤ hi} = hi - lo := by
  rw [Nat.card_congr (offsetEquiv n x lo hi hhi), Nat.card_eq_fintype_card,
    Fintype.card_coe, Nat.card_Ioc]

theorem circulant_degrees (n : ℕ) [NeZero n] (x : ZMod n) :
    outDegree (circulant n) x = half n ∧ secondDegree (circulant n) x = half n := by
  have hh := twice_half_lt (n := n)
  constructor
  · exact offset_card n x 0 (half n) (by omega)
  · unfold secondDegree
    rw [Nat.card_congr (Equiv.subtypeEquivRight (circulant_exact_second n x))]
    rw [offset_card n x (half n) (2 * half n) hh]
    omega

end D5.S3.Combinatorics.Graph.SeymourSharpness
