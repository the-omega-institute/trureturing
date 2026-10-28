/- GID: D5/S3/Observer/CubicGain/RootJDeltaZero
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/RootJDeltaZero
   mirror-E: none(waiver:whole-original-kernel-source-coupling)
   anchors: []
   utility: none
   digest: Original chronological reference rows retain the whole cubic coefficient kernel. -/

import D5.S3.Observer.Linear.GainRayNuisance
import D5.S3.Observer.Linear.GainRayWordGeometry

/-! The complete original reference matrix and its zero-inclusive cubic domain. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.CubicGain.RootJDeltaZero
open D5.S3.Observer.Linear.GainRay

/-- Seven chronological binary digits, followed by the copy digit. J precedes M. -/
abbrev Slot := Fin 256
abbrev Blocks := Slot → Coeff 3

/-- Depth is stored minus one; a row lists every descendant after the first. -/
abbrev Row := (n : Fin 7) × Fin (2 ^ (n.val + 1)) × Fin (2 ^ (7 - n.val) - 1)

def prefixWord (n : ℕ) (p : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => p / 2 ^ (n - 1 - i.val) % 2 == 0)

private theorem block_power (n : Fin 7) :
    2 ^ (n.val + 1) * 2 ^ (7 - n.val) = 256 := by
  fin_cases n <;> norm_num

private theorem reference_bound (n : Fin 7) (p : Fin (2 ^ (n.val + 1))) :
    p.val * 2 ^ (7 - n.val) < 256 := by
  have h := block_power n
  have hp := p.isLt
  have hz : 0 < 2 ^ (7 - n.val) := by positivity
  nlinarith

def reference (r : Row) : Slot :=
  ⟨r.2.1.val * 2 ^ (7 - r.1.val), reference_bound r.1 r.2.1⟩

def descendant (r : Row) : Slot :=
  ⟨r.2.1.val * 2 ^ (7 - r.1.val) + r.2.2.val + 1, by
    have hp := r.2.1.isLt
    have hq := r.2.2.isLt
    have hn := block_power r.1
    have hz : 0 < 2 ^ (7 - r.1.val) := by positivity
    have hq' : r.2.2.val + 1 < 2 ^ (7 - r.1.val) := by omega
    nlinarith⟩

/-- The last row of the native response matrix, with the normalized initial drift. -/
def normalized (w : List Bool) (P : Mat) : Coeff 3 →ₗ[ℝ] ℝ :=
  (LinearMap.proj ⟨w.length, by omega⟩).comp (responseMatrix 3 w P).mulVecLin -
    LinearMap.proj 0

/-- Exactly the nonreference rows of the original complete matrix. -/
def B (P : Slot → Mat) : Blocks →ₗ[ℝ] (Row → ℝ) where
  toFun x r := normalized (prefixWord (r.1.val + 1) r.2.1.val) (P (descendant r))
      (x (descendant r)) -
    normalized (prefixWord (r.1.val + 1) r.2.1.val) (P (reference r)) (x (reference r))
  map_add' x y := by ext r; simp; ring
  map_smul' a x := by ext r; simp; ring

abbrev V (P : Slot → Mat) := LinearMap.ker (B P)

/-- The full native coefficient block, including its freely varying constant. -/
def block (P : Slot → Mat) (q : Slot) : V P →ₗ[ℝ] Coeff 3 :=
  (LinearMap.proj q).comp (V P).subtype

def sample (P : Slot → Mat) (q : Slot) (i : ℕ) : V P →ₗ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 1)).comp ((evaluate 3 1 (fun _ => (i : ℝ))).comp (block P q))

/-- H has the original four coefficients and identically zero constant coefficient. -/
def H (P : Slot → Mat) : V P →ₗ[ℝ] Coeff 3 :=
  block P 0 - (sample P 0 0).smulRight (Pi.single 0 1)

def history (P : Slot → Mat) (i : ℕ) : V P →ₗ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 1)).comp ((evaluate 3 1 (fun _ => (i : ℝ))).comp (H P))

def E (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := 3 • history P 4 - 2 • history P 2
def Delta (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := history P 3 - history P 1
def F (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := (1 / 2 : ℝ) •
  (history P 1 + history P 3) + E P

private theorem sample_eq (P : Slot → Mat) (q : Slot) (i : ℕ) (x : V P) :
    sample P q i x = (Linear.GainRay.gain 3 (x.val q)).eval (i : ℝ) := by
  exact evaluation_polynomial 3 1 (fun _ => (i : ℝ)) (x.val q) 0

private theorem sample_expand (P : Slot → Mat) (q : Slot) (i : ℕ) (x : V P) :
    sample P q i x = x.val q 0 + (i : ℝ) * x.val q 1 +
      (i : ℝ)^2 * x.val q 2 + (i : ℝ)^3 * x.val q 3 := by
  rw [sample_eq]
  simp [Linear.GainRay.gain, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ]
  ring

private theorem history_expand (P : Slot → Mat) (i : ℕ) (x : V P) :
    history P i x = (i : ℝ) * x.val 0 1 +
      (i : ℝ)^2 * x.val 0 2 + (i : ℝ)^3 * x.val 0 3 := by
  change evaluate 3 1 (fun _ => (i : ℝ)) (H P x) 0 = _
  rw [evaluation_polynomial]
  simp [Linear.GainRay.gain, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, H, sample_expand, block, Pi.single_apply]
  ring

theorem delta_zero_history_coordinates (P : Slot → Mat) (delta : Delta P = 0) (x : V P) :
    F P x = 5 * x.val 0 2 + 60 * x.val 0 3 ∧
    E P x = 8 * x.val 0 2 + 72 * x.val 0 3 ∧
    history P 5 x = F P x ∧
    history P 6 x = 2 * F P x + E P x / 4 ∧
    history P 7 x = 21 / 5 * F P x := by
  have hd := congrArg (fun f : V P →ₗ[ℝ] ℝ => f x) delta
  simp only [Delta, LinearMap.sub_apply, LinearMap.zero_apply, history_expand] at hd
  simp only [F, E, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, history_expand]
  norm_num at hd ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end D5.S3.Observer.CubicGain.RootJDeltaZero
