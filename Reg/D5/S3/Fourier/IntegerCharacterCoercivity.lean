import D5.S3.Fourier.IntegerCharacterCoercivity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Metric Set
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Fourier.IntegerCharacterCoercivity
universe u

abbrev Params := Σ q : ℕ, Σ I : Type u, I → Fin q → ℤ

abbrev signature : Signature where
  Params := Params.{u}
  State p := EuclideanSpace ℝ (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Squared distance to the full simultaneous integer-character zero set. -/
def actual : Realization signature.{u} :=
  realize signature (fun _ p x =>
    (infDist x {y : EuclideanSpace ℝ (Fin p.1) |
      ∀ a, ∃ k : ℤ, (∑ i, (p.2.2 a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law r := ∀ (q : ℕ) {I : Type u} [Fintype I] (lam : I → Fin q → ℤ),
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin q),
      c * r.readout () ⟨q, I, lam⟩ x ≤
        ∑ a, (1 - Real.cos (∑ i, (lam a i : ℝ) * x i))

/-- The original zero-dimensional, empty-family boundary rejects constant one. -/
theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  obtain ⟨c, hc, hx⟩ := h 0 (I := ULift.{u} Empty) (fun a => nomatch a.down)
  have hh := hx 0
  have : c ≤ 0 := by simpa [rejected, realize] using hh
  exact (not_le_of_gt hc) this

/-- Dependence is witnessed by the closed cosine-one fiber at zero and pi. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let U : Set (EuclideanSpace ℝ (Fin 1)) :=
    {y | ∀ _ : ULift.{u} Unit, ∃ k : ℤ, (∑ j, ((1 : ℤ) : ℝ) * y j) = 2 * Real.pi * k}
  have hU : U = {y : EuclideanSpace ℝ (Fin 1) | Real.cos (y 0) = 1} := by
    ext y
    simp only [U, mem_setOf_eq, Int.cast_one, one_mul, Fin.sum_univ_one]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h ⟨()⟩
      rw [hk, mul_comm (2 * Real.pi), Real.cos_int_mul_two_pi]
    · intro h a
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (y 0)).mp h
      exact ⟨k, by linarith⟩
  have hclosed : IsClosed U := by
    rw [hU]
    exact isClosed_eq (Real.continuous_cos.comp (PiLp.continuous_apply 2 _ 0)) continuous_const
  have hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ U := by simp [hU]
  let y : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => Real.pi)
  have hy : y ∉ U := by norm_num [hU, y]
  have hd : 0 < infDist y U := (hclosed.notMem_iff_infDist_pos ⟨0, hzero⟩).mp hy
  refine ⟨⟨1, ULift.{u} Unit, fun _ _ => 1⟩, 0, y, ?_⟩
  change (infDist 0 U)^2 ≠ (infDist y U)^2
  rw [infDist_zero_of_mem hzero, zero_pow (by decide : 2 ≠ 0)]
  exact ne_of_lt (sq_pos_of_pos hd)

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem
  _root_.D5.S3.Fourier.IntegerCharacterCoercivity.integer_character_global_coercivity in arena
  readout via (realize signature.{u} (fun _ p x =>
    (infDist x {y : EuclideanSpace ℝ (Fin p.1) |
      ∀ a, ∃ k : ℤ, (∑ i, (p.2.2 a i : ℝ) * y i) = 2 * Real.pi * k}) ^ 2)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.IntegerCharacterCoercivity
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Fourier.IntegerCharacterCoercivity
