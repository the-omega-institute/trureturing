/- GID: D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Distinct optimal entanglement witnesses have an optimal sum and overlapping detection sets. -/
import D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Entanglement.WitnessKernelTraceCriteriaRefutation (blockPositive)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

/-- A Hermitian block-positive operator detecting a density matrix. -/
def IsWitness {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  A.IsHermitian ∧ blockPositive A ∧
    ∃ ρ, IsDensity ρ ∧ (A * ρ).trace.re < 0

/-- Membership in the detection set of an operator. -/
def Detects {d : ℕ} (A ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsDensity ρ ∧ (A * ρ).trace.re < 0

/-- No nonzero positive semidefinite subtraction preserves block positivity. -/
def IsOptimalWitness {d : ℕ} (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  IsWitness A ∧ ∀ ε : ℝ, 0 < ε →
    ∀ P, P.PosSemidef → P ≠ 0 → ¬ blockPositive (A - (ε : ℂ) • P)

/-- Optimal witnesses with an optimal sum and intersecting, distinct detection sets in every d ≥ 3. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ W M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      IsOptimalWitness W ∧ IsOptimalWitness M ∧ IsOptimalWitness (W + M) ∧
      (∃ ρ, Detects W ρ ∧ ¬ Detects M ρ) ∧
      (∃ ρ, Detects M ρ ∧ ¬ Detects W ρ) ∧
      (∃ ρ, Detects W ρ ∧ Detects M ρ)

private def tensor {d : ℕ} (x y : Fin d → ℂ) : Fin d × Fin d → ℂ :=
  fun p => x p.1 * y p.2

private def wr {d : ℕ} [NeZero d] (r : Fin d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  single (0, r) (0, r) 1 + single (r, 0) (r, 0) 1 -
    single (0, 0) (r, r) 1 - single (r, r) (0, 0) 1

private def pairVector {d : ℕ} [NeZero d] (r : Fin d) : Fin d × Fin d → ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ • (Pi.single (0, 0) 1 + Pi.single (r, r) 1)

private def omega {d : ℕ} : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then (Real.sqrt d : ℂ)⁻¹ else 0

private theorem wr_hermitian {d : ℕ} [NeZero d] (r : Fin d) : (wr r).IsHermitian := by
  sorry

private theorem wr_expectation {d : ℕ} [NeZero d] (r : Fin d)
    (v : Fin d × Fin d → ℂ) :
    star v ⬝ᵥ (wr r *ᵥ v) =
      star (v (0, r)) * v (0, r) + star (v (r, 0)) * v (r, 0) -
        star (v (0, 0)) * v (r, r) - star (v (r, r)) * v (0, 0) := by
  sorry

private theorem product_expectation {d : ℕ} [NeZero d] (r : Fin d) (x y : Fin d → ℂ) :
    star (tensor x y) ⬝ᵥ (wr r *ᵥ tensor x y) =
      (Complex.normSq (x 0 * star (y r) - x r * star (y 0)) : ℂ) := by
  sorry

private theorem wr_blockPositive {d : ℕ} [NeZero d] (r : Fin d) :
    blockPositive (wr r) := by
  sorry

private theorem trace_projector {n : Type*} [Fintype n] (A : Matrix n n ℂ) (v : n → ℂ) :
    (A * vecMulVec v (star v)).trace = star v ⬝ᵥ (A *ᵥ v) := by
  sorry

private theorem pair_density {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    IsDensity (vecMulVec (pairVector r) (star (pairVector r))) := by
  sorry

private theorem pair_expectation {d : ℕ} [NeZero d] (r s : Fin d)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    (wr r * vecMulVec (pairVector s) (star (pairVector s))).trace =
      if r = s then -1 else 0 := by
  sorry

private theorem omega_density {d : ℕ} [NeZero d] :
    IsDensity (vecMulVec (omega (d := d)) (star omega)) := by
  sorry

private theorem omega_expectation {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    (wr r * vecMulVec (omega (d := d)) (star omega)).trace = -2 / (d : ℂ) := by
  sorry

private theorem conjugate_products_span (d : ℕ) :
    Submodule.span ℂ (Set.range (fun x : Fin d → ℂ => tensor x (star x))) = ⊤ := by
  sorry

private theorem spanning_optimal {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hA : IsWitness A)
    (S : Set (Fin d × Fin d → ℂ)) (hS : Submodule.span ℂ S = ⊤)
    (hzero : ∀ v ∈ S, ∃ x y, v = tensor x y ∧ star v ⬝ᵥ (A *ᵥ v) = 0) :
    IsOptimalWitness A := by
  sorry

private theorem wr_zero {d : ℕ} [NeZero d] (r : Fin d) (x : Fin d → ℂ) :
    star (tensor x (star x)) ⬝ᵥ (wr r *ᵥ tensor x (star x)) = 0 := by
  sorry

private theorem wr_optimal {d : ℕ} [NeZero d] (r : Fin d) (hr : r ≠ 0) :
    IsOptimalWitness (wr r) := by
  sorry

private theorem sum_optimal {d : ℕ} [NeZero d] (r s : Fin d) (hr : r ≠ 0) (hs : s ≠ 0) :
    IsOptimalWitness (wr r + wr s) := by
  sorry

private theorem detection_separation {d : ℕ} [NeZero d] (r s : Fin d)
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    (∃ ρ, Detects (wr r) ρ ∧ ¬ Detects (wr s) ρ) ∧
    (∃ ρ, Detects (wr s) ρ ∧ ¬ Detects (wr r) ρ) ∧
    (∃ ρ, Detects (wr r) ρ ∧ Detects (wr s) ρ) := by
  sorry

/-- Every local dimension at least three admits the required generalized mirrored pair. -/
theorem result : claim := by
  intro d hd
  letI : NeZero d := ⟨by omega⟩
  let r : Fin d := ⟨1, by omega⟩
  let s : Fin d := ⟨2, by omega⟩
  have hr : r ≠ 0 := by intro h; have := congrArg Fin.val h; simp [r] at this
  have hs : s ≠ 0 := by intro h; have := congrArg Fin.val h; simp [s] at this
  have hrs : r ≠ s := by intro h; have := congrArg Fin.val h; simp [r, s] at this
  exact ⟨wr r, wr s, wr_optimal r hr, wr_optimal s hs, sum_optimal r s hr hs,
    detection_separation r s hr hs hrs⟩

end D5.S3.Quantum.Entanglement.Witness.MirroredOptimalWitnessSum
