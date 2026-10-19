/- GID: D5/S3/Observer/Linear/FiniteRealZeroFillRegister
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FiniteRealZeroFillRegister
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite real zero-fill register preserves every in-bound coordinate and reads the original sign pointwise through the horizon. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Observer.Linear.FiniteRealZeroFillRegister

abbrev X := ℕ → Bool
def bitSign (b : Bool) : ℝ := (-1 : ℝ) ^ b.toNat
def signal (t : ℕ) (x : X) : ℝ := bitSign (x t)
abbrev State (H : ℕ) := Fin (H + 1) → ℝ

def initState (H : ℕ) (x : X) : State H := fun i => signal i.val x

def update (H : ℕ) : State H →ₗ[ℝ] State H where
  toFun q i := if h : i.val + 1 < H + 1 then q ⟨i.val + 1, h⟩ else 0
  map_add' q v := by
    ext i
    change (if h : i.val + 1 < H + 1 then q ⟨i.val + 1, h⟩ + v ⟨i.val + 1, h⟩ else 0) =
      (if h : i.val + 1 < H + 1 then q ⟨i.val + 1, h⟩ else 0) +
      (if h : i.val + 1 < H + 1 then v ⟨i.val + 1, h⟩ else 0)
    split_ifs <;> simp only [add_zero]
  map_smul' c q := by
    ext i
    change (if h : i.val + 1 < H + 1 then c * q ⟨i.val + 1, h⟩ else 0) =
      c * (if h : i.val + 1 < H + 1 then q ⟨i.val + 1, h⟩ else 0)
    split_ifs <;> simp only [mul_zero]

def readout (H : ℕ) : State H →ₗ[ℝ] ℝ := LinearMap.proj 0

theorem update_iterate (H t : ℕ) (q : State H) (i : Fin (H + 1))
    (hi : i.val + t < H + 1) :
    (update H : State H → State H)^[t] q i = q ⟨i.val + t, hi⟩ := by
  induction t generalizing q i with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih (update H q) i (by omega)]
    change (if h : i.val + t + 1 < H + 1 then q ⟨i.val + t + 1, h⟩ else 0) = _
    rw [dif_pos (by omega)]
    congr 1 <;> omega

theorem pointwise_attainment (H : ℕ) (x : X) (t : ℕ) (ht : t ≤ H) :
    readout H ((update H : State H → State H)^[t] (initState H x)) = signal t x := by
  change (update H : State H → State H)^[t] (initState H x) 0 = _
  rw [update_iterate H t _ 0 (by simp; omega)]
  simp [initState]

#print axioms update_iterate
#print axioms pointwise_attainment

end D5.S3.Observer.Linear.FiniteRealZeroFillRegister
