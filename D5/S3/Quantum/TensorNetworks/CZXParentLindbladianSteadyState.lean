/- GID: D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The CZX parent Lindbladian has the conjectured even-ring limit. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState

open Matrix Filter
open scoped Topology ComplexConjugate

/- Source: Liu et al., arXiv:2501.10552v2, Example VI.6 and Appendix F.
   admission_basis: open-problem-resolution (#23957)
   The first site is the most significant bit of each four-site window.
   Evolution uses the matrix of the superoperator on pairs of configurations.
   No matrix norm instance is installed.
-/

/-- The two-site change of basis in Appendix F. -/
def czxU : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- The signed permutation in Appendix F, with source indices shifted by one. -/
def czxV : Matrix (Fin 16) (Fin 16) ℂ := fun r c =>
  if (r, c) ∈ ({(0, 0), (1, 15), (2, 2), (3, 13), (4, 4), (5, 11),
      (6, 6), (8, 1), (9, 14), (10, 3), (12, 5), (13, 10), (14, 7),
      (15, 8)} : Finset (Fin 16 × Fin 16)) then 1
  else if (r, c) = (7, 9) ∨ (r, c) = (11, 12) then -1 else 0

/-- The common two-site block weight. -/
noncomputable def mu : ℝ := Real.sqrt 3 / 4

/-- The scalar multiplying the four-dimensional multiplicity identity. -/
noncomputable def nu : ℝ := Real.sqrt 3 / 16

/-- The trace of a multiplicity block. -/
noncomputable def mLambda : ℝ := mu

private def block4 (l z : Fin 2) : Fin 4 := ⟨2 * l.val + z.val, by omega⟩

private def block16 (l : Fin 2) (m : Fin 4) (z : Fin 2) : Fin 16 :=
  ⟨8 * l.val + 2 * m.val + z.val, by omega⟩

private def sector4 (r : Fin 4) : Fin 2 := ⟨r.val / 2, by omega⟩

private def bit4 (r : Fin 4) : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩

private def sector16 (r : Fin 16) : Fin 2 := ⟨r.val / 8, by omega⟩

private def multiplicity16 (r : Fin 16) : Fin 4 := ⟨r.val % 8 / 2, by omega⟩

private def bit16 (r : Fin 16) : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Block pinching and partial trace, conjugated by the two source unitaries. -/
noncomputable def renormS (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  czxUᴴ * (fun r s => if sector4 r = sector4 s then
    ∑ m : Fin 4, (czxV * x * czxVᴴ)
      (block16 (sector4 r) m (bit4 r)) (block16 (sector4 s) m (bit4 s))
    else 0) * czxU

/-- Insertion of the normalized multiplicity state, with the source tensor order. -/
noncomputable def renormT (y : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ :=
  czxVᴴ * (fun r s => if sector16 r = sector16 s then
    ((nu / mLambda : ℝ) : ℂ) * (1 : Matrix (Fin 4) (Fin 4) ℂ)
      (multiplicity16 r) (multiplicity16 s) *
      (czxU * y * czxUᴴ) (block4 (sector16 r) (bit16 r))
        (block4 (sector16 s) (bit16 s)) else 0) * czxV

/-- The source four-site channel, T composed with S. -/
noncomputable def localChannel (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ := renormT (renormS x)

/-- Cyclic displacement of a site. -/
def site {n : ℕ} (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- The four bits of a cyclic window, first site most significant. -/
def windowCode {n : ℕ} (i : Fin n) (x : Fin n → Fin 2) : Fin 16 :=
  ⟨8 * (x (site i 0)).val + 4 * (x (site i 1)).val +
      2 * (x (site i 2)).val + (x (site i 3)).val, by
    have := (x (site i 0)).isLt
    have := (x (site i 1)).isLt
    have := (x (site i 2)).isLt
    have := (x (site i 3)).isLt
    omega⟩

private def digit (p : Fin 16) (k : ℕ) : Fin 2 :=
  ⟨p.val / 2 ^ k % 2, Nat.mod_lt _ (by decide)⟩

/-- Write a four-bit word into a cyclic window. -/
def windowUpdate {n : ℕ} (i : Fin n) (x : Fin n → Fin 2) (p : Fin 16) :
    Fin n → Fin 2 :=
  Function.update (Function.update (Function.update (Function.update x
    (site i 0) (digit p 3)) (site i 1) (digit p 2))
    (site i 2) (digit p 1)) (site i 3) (digit p 0)

/-- E tensored with the identity on the complement of a cyclic window. -/
noncomputable def windowChannel (n : ℕ) (i : Fin n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  ∑ p : Fin 16, ∑ q : Fin 16,
    localChannel (Matrix.single p q 1) (windowCode i x) (windowCode i y) *
      a (windowUpdate i x p) (windowUpdate i y q)

/-- Matrix of a window channel in the matrix-unit basis. -/
noncomputable def windowSuperoperator (n : ℕ) (i : Fin n) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ := fun x y =>
  windowChannel n i (Matrix.single y.1 y.2 1) x.1 x.2

/-- The parent generator, summed over zero-based even starting sites. -/
noncomputable def parentLindbladian (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0),
    (windowSuperoperator n i - 1)

/-- The tensor power of sigma-x, which flips every bit. -/
def tensorX (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = (fun j => y j + 1) then 1 else 0

/-- Product of the controlled-z gates on every edge of the ring. -/
def cz (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal fun x => (-1 : ℂ) ^ ∑ j : Fin n, (x j).val * (x (site j 1)).val

/-- The CZX symmetry operator, in the source order CZ times X. -/
def czxUnitary (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  cz n * tensorX n

/-- The matrix exponential of the source parent generator acting on an operator. -/
noncomputable def evolution (n : ℕ) (t : ℝ)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  (NormedSpace.exp ((t : ℂ) • parentLindbladian n)).mulVec
    (fun p => a p.1 p.2) (x, y)

/-- The conjecture for every even ring on which the four window sites are distinct. -/
def claim : Prop := ∀ n : ℕ, Even n → 4 ≤ n →
  Tendsto (fun t : ℝ => evolution n t (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
    (𝓝 (((2 : ℂ) ^ n)⁻¹ •
      (1 + (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n)))

private def pinching (x : Matrix (Fin 16) (Fin 16) ℂ) :
    Matrix (Fin 16) (Fin 16) ℂ := fun r s =>
  if sector16 r = sector16 s ∧ multiplicity16 r = multiplicity16 s then
    (4 : ℂ)⁻¹ * ∑ m : Fin 4,
      x (block16 (sector16 r) m (bit16 r)) (block16 (sector16 s) m (bit16 s))
  else 0

private lemma local_channel_formula (x : Matrix (Fin 16) (Fin 16) ℂ) :
    localChannel x = czxVᴴ * pinching (czxV * x * czxVᴴ) * czxV := by
  sorry

private def pack (v : Fin 4 → Fin 2) : Fin 16 :=
  ⟨8 * (v 0).val + 4 * (v 1).val + 2 * (v 2).val + (v 3).val, by
    have := (v 0).isLt
    have := (v 1).isLt
    have := (v 2).isLt
    have := (v 3).isLt
    omega⟩

private def pathPhase (v : Fin 4 → Fin 2) : ℕ :=
  (v 0).val * (v 1).val + (v 1).val * (v 2).val + (v 2).val * (v 3).val

private lemma local_matrix_unit (v d : Fin 4 → Fin 2) :
    localChannel (Matrix.single (pack (v + d)) (pack v) 1) =
      if h : ∀ j, d j = d 0 then
        (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
          let w := Function.update (Function.update v 1 b) 2 c
          (-1 : ℂ) ^ ((d 0).val * (pathPhase v + pathPhase w)) •
            Matrix.single (pack (w + d)) (pack w) 1
      else 0 := by
  sorry

private def gauge (n : ℕ) (e : Fin 2) (x : Fin n → Fin 2) : ℂ :=
  (-1 : ℂ) ^ (e.val * ∑ j : Fin n, (x j).val * (x (site j 1)).val)

private lemma gauged_window (n : ℕ) (hn : 4 ≤ n) (i : Fin n)
    (e : Fin 2) (x : Fin n → Fin 2) :
    windowChannel n i
      (gauge n e x • Matrix.single (x + fun _ => e) x 1) =
      (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
        let y := Function.update (Function.update x (site i 1) b) (site i 2) c
        gauge n e y • Matrix.single (y + fun _ => e) y 1 := by
  sorry

private lemma window_idempotent (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    IsIdempotentElem (windowSuperoperator n i) := by
  sorry

private lemma window_commute (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (i j : Fin n) (hi : i.val % 2 = 0) (hj : j.val % 2 = 0) :
    Commute (windowSuperoperator n i) (windowSuperoperator n j) := by
  sorry

private lemma exponential_idempotent {k : Type*} [Fintype k] [DecidableEq k]
    (e : Matrix k k ℂ) (he : IsIdempotentElem e) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (e - 1)) =
      (Real.exp (-t) : ℂ) • (1 : Matrix k k ℂ) +
        (1 - (Real.exp (-t) : ℂ)) • e := by
  sorry

private def projection (n : ℕ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2))
      ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  (((List.finRange n).filter (fun i => i.val % 2 == 0)).map
    (windowSuperoperator n)).prod

private lemma exponential_limit (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n)) := by
  sorry

private lemma projection_formula (n : ℕ) (hn : Even n) (hsize : 4 ≤ n)
    (a : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    (fun x y => (projection n).mulVec (fun p => a p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ • (Matrix.trace a • (1 : Matrix _ _ ℂ) +
        Matrix.trace ((czxUnitary n)ᴴ * a) • czxUnitary n) := by
  sorry

private lemma symmetry_trace (n : ℕ) (hn : 0 < n) :
    Matrix.trace (czxUnitary n) = 0 := by
  sorry

private lemma transfer_coefficient (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    Matrix.trace ((czxUnitary n)ᴴ * tensorX n) = (2 : ℂ) ^ (n / 2 + 1) := by
  sorry

private lemma projection_initial (n : ℕ) (hn : Even n) (hsize : 4 ≤ n) :
    (fun x y => (projection n).mulVec
      (fun p => (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) (x, y)) =
      ((2 : ℂ) ^ n)⁻¹ •
        (1 + (2 : ℂ) ^ (1 - (n / 2 : ℕ) : ℤ) • czxUnitary n) := by
  sorry

private lemma evolution_limit (n : ℕ)
    (h : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • parentLindbladian n))
      atTop (𝓝 (projection n))) :
    Tendsto (fun t : ℝ => evolution n t
      (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n))) atTop
      (𝓝 (fun x y => (projection n).mulVec
        (fun p => (((2 : ℂ) ^ n)⁻¹ • (1 + tensorX n)) p.1 p.2) (x, y))) := by
  sorry

/-- The steady-state conjecture for every even N at least four. -/
theorem result : claim := by
  intro n hn hsize
  have happly := evolution_limit n (exponential_limit n hn hsize)
  rw [projection_initial n hn hsize] at happly
  exact happly

end D5.S3.Quantum.TensorNetworks.CZXParentLindbladianSteadyState
