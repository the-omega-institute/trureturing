/- GID: D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Pi, mathlib/module/Mathlib.Data.Fintype.Prod, mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.Data.Nat.Choose.Central, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim1; result=D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.result1; claim=D5/S0/Certificates/FlorezCubicLatticePlanePathCountRefutation.claim1
   digest: Refutes both Florez plane-count conjectures at k = 3: 14 ≠ 36. -/

/- Formalization classification:
   proof_shape: result1: bind-only; result2: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9059)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S0.Certificates.FlorezCubicLatticePlanePathCountRefutation

/-- A signed coordinate step `±e_j` in the 3-dimensional cubic lattice: an axis and a sign. -/
abbrev Step := Fin 3 × Bool

/-- A path of length `k` is a sequence of `k` steps starting at the origin. -/
abbrev Path (k : ℕ) := Fin k → Step

/-- `V_r`: the coordinate vector after the first `r` steps. -/
def partialSum {k : ℕ} (P : Path k) (r : ℕ) : Fin 3 → ℤ := fun c =>
  ∑ i : Fin k, if (i : ℕ) < r ∧ (P i).1 = c then (if (P i).2 then 1 else -1) else 0

/-- Printed `C_3^+(k)`: the third coordinate of `V_r` is non-negative for all
`0 < r ≤ k`, and the third coordinate of `V_k` is zero. -/
def InCThreePlus {k : ℕ} (P : Path k) : Prop :=
  (∀ r : Fin (k + 1), 0 < (r : ℕ) → 0 ≤ partialSum P r 2) ∧ partialSum P k 2 = 0

/-- "Completely contained in the xz-plane": every vertex `V_r`, `0 < r ≤ k`,
has second coordinate zero. -/
def InXzPlane {k : ℕ} (P : Path k) : Prop :=
  ∀ r : Fin (k + 1), 0 < (r : ℕ) → partialSum P r 1 = 0

/-- "Completely contained in the yz-plane": every vertex `V_r`, `0 < r ≤ k`,
has first coordinate zero. -/
def InYzPlane {k : ℕ} (P : Path k) : Prop :=
  ∀ r : Fin (k + 1), 0 < (r : ℕ) → partialSum P r 0 = 0

instance instDecidablePredInCThreePlus {k : ℕ} : DecidablePred (@InCThreePlus k) := fun P => by
  unfold InCThreePlus
  infer_instance

instance instDecidablePredInXzPlane {k : ℕ} : DecidablePred (@InXzPlane k) := fun P => by
  unfold InXzPlane
  infer_instance

instance instDecidablePredInYzPlane {k : ℕ} : DecidablePred (@InYzPlane k) := fun P => by
  unfold InYzPlane
  infer_instance

/-- The number of paths in `C_3^+(k)` completely contained in the xz-plane. -/
def xzCount (k : ℕ) : ℕ :=
  (Finset.univ.filter fun P : Path k => InCThreePlus P ∧ InXzPlane P).card

/-- The number of paths in `C_3^+(k)` completely contained in the yz-plane. -/
def yzCount (k : ℕ) : ℕ :=
  (Finset.univ.filter fun P : Path k => InCThreePlus P ∧ InYzPlane P).card

/-- The printed right-hand side `Σ_{i=1}^{k+1} C(2i,i) C(k,i-1)/(i+1)`
(each summand's division is exact). -/
def formula (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 (k + 1), Nat.choose (2 * i) i * Nat.choose k (i - 1) / (i + 1)

/-- Conjecture 1 as printed: for `k ≥ 1`, the xz-plane count equals the formula. -/
def claim1 : Prop := ∀ k, 1 ≤ k → xzCount k = formula k

/-- Conjecture 2 as printed: for `k ≥ 1`, the yz-plane count equals the formula. -/
def claim2 : Prop := ∀ k, 1 ≤ k → yzCount k = formula k

/-- Conjecture 1 is false at `k = 3`: `14 ≠ 36`. -/
theorem result1 : ¬ claim1 := by
  intro h
  have hcount : xzCount 3 = 14 := by decide +kernel
  have hformula : formula 3 = 36 := by decide +kernel
  have hclaim := h 3 (by decide)
  rw [hcount, hformula] at hclaim
  exact (by decide : (14 : ℕ) ≠ 36) hclaim

/-- Conjecture 2 is false at `k = 3`: `14 ≠ 36`. -/
theorem result2 : ¬ claim2 := by
  intro h
  have hcount : yzCount 3 = 14 := by decide +kernel
  have hformula : formula 3 = 36 := by decide +kernel
  have hclaim := h 3 (by decide)
  rw [hcount, hformula] at hclaim
  exact (by decide : (14 : ℕ) ≠ 36) hclaim

-- Figure 2 checks the complete printed `C_3^+(2)` predicate.
example : (Finset.univ.filter fun P : Path 2 => InCThreePlus P).card = 17 := by
  decide +kernel

-- Proposition 20 controls, with the xy-plane predicate kept outside the public surface.
example :
    (Finset.univ.filter fun P : Path 1 =>
      InCThreePlus P ∧
        ∀ r : Fin 2, 0 < (r : ℕ) → partialSum P r 2 = 0).card = 4 ^ 1 := by
  decide +kernel

example :
    (Finset.univ.filter fun P : Path 2 =>
      InCThreePlus P ∧
        ∀ r : Fin 3, 0 < (r : ℕ) → partialSum P r 2 = 0).card = 4 ^ 2 := by
  decide +kernel

-- Small printed-reading and formula controls.
example : xzCount 1 = 2 := by decide +kernel
example : xzCount 2 = 5 := by decide +kernel
example : formula 1 = 3 := by decide +kernel
example : formula 2 = 10 := by decide +kernel
example : formula 3 = 36 := by decide +kernel
example : formula 4 = 137 := by decide +kernel

-- Natural-number division in every summand is exact.
example (k i : ℕ) :
    i + 1 ∣ Nat.choose (2 * i) i * Nat.choose k (i - 1) := by
  change i + 1 ∣ Nat.centralBinom i * Nat.choose k (i - 1)
  exact dvd_mul_of_dvd_left (Nat.succ_dvd_centralBinom i) _

-- The counterexamples are computed over all `6^3 = 216` paths.
example : xzCount 3 = 14 := by decide +kernel
example : yzCount 3 = 14 := by decide +kernel

-- Fidelity-gate witnesses for the quantified premise and path domain.
example : 1 ≤ (3 : ℕ) := by decide
example : Path 3 := fun _ => (0, false)

#print axioms result1
#print axioms result2

end D5.S0.Certificates.FlorezCubicLatticePlanePathCountRefutation
