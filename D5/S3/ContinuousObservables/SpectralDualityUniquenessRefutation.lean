/- GID: D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/SpectralDualityUniquenessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.claim; result=D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.result; claim=D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.claim
   digest: Refute generic global uniqueness in the open range N ≤ m by an open matrix family. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#26267; Refuted)
Direct frozen dependencies: none (every declaration; no D5 imports).
Private theorem classifications (all bind-only; escape_witness none):
  base_positive -> result
  base_interior -> result
  base_independent -> result
  delta_kernel -> badSet_nonempty
  perturbation_coordinates -> badSet_failure
  second_interior -> family_coupling, badSet_failure
  second_ne -> badSet_failure
  second_algebra -> family_coupling
  family_h2 -> badSet_failure
  family_coupling -> badSet_failure
  badSet_open -> result
  badSet_nonempty -> result
  badSet_failure -> result
All proofs use finite evaluation, field/order normalization, linear independence
and open-set density infrastructure from pinned Mathlib. No escape content is claimed.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The source formulas are inlined in claim; the proof uses Matrix.vecMulVec for
the rank-one perturbation and the existing subtype topology.
The claim omits the source's additional null-complement requirement, so its
negation also rules out the extension with that stronger requirement.
The published N > m proposition and fixed-level uniqueness are outside this result.
-/

import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.LinearCombination

/-! # An open two-parameter obstruction to global uniqueness. -/

namespace D5.S3.ContinuousObservables.SpectralDualityUniquenessRefutation

open scoped BigOperators
open Set
noncomputable section

/-- The global uniqueness extension to the range N ≤ m, with every level included. -/
def claim : Prop :=
  ∀ (N m : ℕ) (A : Matrix (Fin N) (Fin m) ℝ) (π : Fin m → ℝ)
    (β : ℝ) (f : Fin N → Set.Ioo (0 : ℝ) 1 → ℝ),
    2 ≤ N → 2 ≤ m → N ≤ m →
    (∀ ν z, 0 < A ν z) → ((∀ z, 0 < π z) ∧ ∑ z, π z = 1) →
    0 < β → LinearIndependent ℝ f →
    ∃ G : Set {D : Matrix (Fin N) (Fin m) ℝ // D.mulVec π = 0},
      IsOpen G ∧ Dense G ∧
      ∀ D : {D : Matrix (Fin N) (Fin m) ℝ // D.mulVec π = 0},
        D ∈ G →
        (∀ z (γ : Set.Ioo (0 : ℝ) 1),
          0 < ∑ ν, f ν γ * (A ν z + (β * A ν z + D.1 ν z))) →
        ∀ (π' : Fin m → ℝ) (c : ℝ),
          ((∀ z, 0 ≤ π' z) ∧ ∑ z, π' z = 1) →
          (∀ γ : Set.Ioo (0 : ℝ) 1,
            (∑ z, π' z * (∑ ν, f ν γ * A ν z)) /
              (∑ z, π' z * (∑ ν, f ν γ * (A ν z + (β * A ν z + D.1 ν z)))) = c) →
          π' = π

private abbrev baseA : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 2], ![2, 1]]
private abbrev basePi : Fin 2 → ℝ := ![1/2, 1/2]
private abbrev baseF : Fin 2 → Set.Ioo (0 : ℝ) 1 → ℝ := ![fun _ => 1, fun γ => (γ : ℝ)]
private abbrev delta (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.vecMulVec ![a, b] ![1, -1]
private abbrev second (a b : ℝ) : Fin 2 → ℝ :=
  ![(2*b-a)/(a+b), (2*a-b)/(a+b)]

private def Family (a b : ℝ) : Prop :=
  0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ a/2 < b ∧ b < 2*a ∧ a ≠ b

private theorem base_positive : ∀ i j, 0 < baseA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [baseA]

private theorem base_interior : (∀ i, 0 < basePi i) ∧ ∑ i, basePi i = 1 := by
  constructor
  · intro i; fin_cases i <;> norm_num [basePi]
  · norm_num [basePi, Fin.sum_univ_two]

private theorem base_independent : LinearIndependent ℝ baseF := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h₁ := congrFun hg (⟨1/3, by norm_num [Set.mem_Ioo]⟩ : Set.Ioo (0 : ℝ) 1)
  have h₂ := congrFun hg (⟨2/3, by norm_num [Set.mem_Ioo]⟩ : Set.Ioo (0 : ℝ) 1)
  simp [Fin.sum_univ_two] at h₁ h₂
  norm_num at h₁ h₂
  fin_cases i <;> dsimp <;> linarith

private theorem delta_kernel (a b : ℝ) : Matrix.mulVec (delta a b) basePi = 0 := by
  change (Matrix.vecMulVec (![a, b] : Fin 2 → ℝ) (![1, -1] : Fin 2 → ℝ)).mulVec basePi = 0
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct, Fin.sum_univ_two, basePi]

private theorem perturbation_coordinates (D : {D : Matrix (Fin 2) (Fin 2) ℝ // D.mulVec basePi = 0}) :
    D.1 = delta (D.1 0 0) (D.1 1 0) := by
  have h₀ := congrFun D.2 0
  have h₁ := congrFun D.2 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, basePi] at h₀ h₁
  funext i j
  fin_cases i <;> fin_cases j <;> simp [delta, Matrix.vecMulVec] <;> linarith

private theorem second_interior {a b : ℝ} (h : Family a b) :
    (∀ i, 0 < second a b i) ∧ ∑ i, second a b i = 1 := by
  rcases h with ⟨ha, ha1, hb, hb1, hab, hba, hne⟩
  have hs : 0 < a+b := add_pos ha hb
  constructor
  · intro i
    fin_cases i
    · exact div_pos (by linarith) hs
    · exact div_pos (by linarith) hs
  · simp only [Fin.sum_univ_two, second, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [ne_of_gt hs]
    ring

private theorem second_ne {a b : ℝ} (h : Family a b) : second a b ≠ basePi := by
  rcases h with ⟨ha, ha1, hb, hb1, hab, hba, hne⟩
  intro he
  have he0 := congrFun he 0
  change (2*b-a)/(a+b) = 1/2 at he0
  have hs : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have heq := (div_eq_iff hs).mp he0
  apply hne
  linarith


private theorem second_algebra (a b : ℝ) :
    Matrix.mulVec (delta a b) (second a b) =
      (b-a) • Matrix.mulVec baseA (second a b) := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, delta, Matrix.vecMulVec, second, baseA] <;>
    ring

private theorem family_h2 {a b : ℝ} (h : Family a b) :
    ∀ z (γ : Set.Ioo (0 : ℝ) 1), 0 < ∑ ν, baseF ν γ * (baseA ν z + (1 * baseA ν z + delta a b ν z)) := by
  rcases h with ⟨ha, ha1, hb, hb1, hab, hba, hne⟩
  intro z γ
  have hg : 0 < (γ : ℝ) := γ.2.1
  fin_cases z <;>
    simp [baseA, baseF, delta, Matrix.vecMulVec, Fin.sum_univ_two]
  · nlinarith
  · nlinarith

private theorem family_coupling {a b : ℝ} (h : Family a b) :
    (∀ γ : Set.Ioo (0 : ℝ) 1, (∑ z, (second a b) z * (∑ ν, baseF ν γ * baseA ν z)) / (∑ z, (second a b) z * (∑ ν, baseF ν γ * (baseA ν z + (1 * baseA ν z + (delta a b) ν z)))) = 1/(2+b-a)) := by
  have hq := second_interior h
  intro γ
  rcases h with ⟨ha, ha1, hb, hb1, hab, hba, hne⟩
  have hs : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have ht : 2+b-a ≠ 0 := by linarith
  have hq0 : 0 < (2*b-a)/(a+b) := hq.1 0
  have hq1 : 0 < (2*a-b)/(a+b) := hq.1 1
  have hg : 0 < (γ : ℝ) := γ.2.1
  have hd : 0 < (2*b-a)/(a+b)*(2+a+(γ : ℝ)*(4+b)) +
      (2*a-b)/(a+b)*(4-a+(γ : ℝ)*(2-b)) := by
    apply add_pos
    · apply mul_pos hq0
      have hp : 0 < (γ : ℝ)*(4+b) := mul_pos hg (by linarith)
      linarith
    · apply mul_pos hq1
      have hp : 0 < (γ : ℝ)*(2-b) := mul_pos hg (by linarith)
      linarith
  have hV := second_algebra a b
  have hV₀ :
      a*((2*b-a)/(a+b)) - a*((2*a-b)/(a+b)) =
        (b-a)*((2*b-a)/(a+b) + 2*((2*a-b)/(a+b))) := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, delta, Matrix.vecMulVec,
      second, baseA, sub_eq_add_neg] using congrFun hV 0
  have hV₁ :
      b*((2*b-a)/(a+b)) - b*((2*a-b)/(a+b)) =
        (b-a)*(2*((2*b-a)/(a+b)) + (2*a-b)/(a+b)) := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, delta, Matrix.vecMulVec,
      second, baseA, sub_eq_add_neg] using congrFun hV 1
  have hc :
    ((2*b-a)/(a+b)*(1+(γ : ℝ)*2) + (2*a-b)/(a+b)*(2+(γ : ℝ))) /
    ((2*b-a)/(a+b)*(1+(1+a)+(γ : ℝ)*(2+(2+b))) +
     (2*a-b)/(a+b)*(2+(2+-a)+(γ : ℝ)*(1+(1+-b)))) = 1/(2+b-a) := by
    have hd' :
        (2*b-a)/(a+b)*(1+(1+a)+(γ : ℝ)*(2+(2+b))) +
        (2*a-b)/(a+b)*(2+(2+-a)+(γ : ℝ)*(1+(1+-b))) ≠ 0 := by
      convert ne_of_gt hd using 1
      ring
    apply (div_eq_div_iff hd' ht).2
    linear_combination -hV₀ - (γ : ℝ) * hV₁
  simpa [Fin.sum_univ_two, second, baseF, baseA, delta, Matrix.vecMulVec] using hc


private def badSet : Set ({D : Matrix (Fin 2) (Fin 2) ℝ // D.mulVec basePi = 0}) :=
  {D | Family (D.1 0 0) (D.1 1 0)}

private theorem badSet_open : IsOpen badSet := by
  have h₀ : Continuous (fun D : {D : Matrix (Fin 2) (Fin 2) ℝ // D.mulVec basePi = 0} => D.1 0 0) :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  have h₁ : Continuous (fun D : {D : Matrix (Fin 2) (Fin 2) ℝ // D.mulVec basePi = 0} => D.1 1 0) :=
    (continuous_apply 0).comp ((continuous_apply 1).comp continuous_subtype_val)
  exact (isOpen_lt continuous_const h₀).inter
    ((isOpen_lt h₀ continuous_const).inter
    ((isOpen_lt continuous_const h₁).inter
    ((isOpen_lt h₁ continuous_const).inter
    ((isOpen_lt (h₀.div_const 2) h₁).inter
    ((isOpen_lt h₁ (continuous_const.mul h₀)).inter
      (isOpen_ne_fun h₀ h₁))))))

private theorem badSet_nonempty : badSet.Nonempty := by
  refine ⟨⟨delta (1/2) (3/4), delta_kernel (1/2) (3/4)⟩, ?_⟩
  norm_num [badSet, Family, delta, Matrix.vecMulVec]

private theorem badSet_failure (D : {D : Matrix (Fin 2) (Fin 2) ℝ // D.mulVec basePi = 0}) (hD : D ∈ badSet) :
    (∀ z (γ : Set.Ioo (0 : ℝ) 1), 0 < ∑ ν, baseF ν γ * (baseA ν z + (1 * baseA ν z + D.1 ν z))) ∧
    ∃ q : Fin 2 → ℝ, ((∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) ∧ q ≠ basePi ∧
      (∀ γ : Set.Ioo (0 : ℝ) 1, (∑ z, q z * (∑ ν, baseF ν γ * baseA ν z)) / (∑ z, q z * (∑ ν, baseF ν γ * (baseA ν z + (1 * baseA ν z + D.1 ν z)))) = 1/(2+D.1 1 0-D.1 0 0)) := by
  have h : Family (D.1 0 0) (D.1 1 0) := hD
  have hd := perturbation_coordinates D
  constructor
  · rw [hd]
    exact family_h2 h
  · refine ⟨second (D.1 0 0) (D.1 1 0), ?_, second_ne h, ?_⟩
    · exact ⟨fun i => le_of_lt ((second_interior h).1 i), (second_interior h).2⟩
    · rw [hd]
      simpa [delta, Matrix.vecMulVec] using family_coupling h

theorem result : ¬ claim := by
  intro hc
  obtain ⟨G, hGo, hGd, hG⟩ := hc 2 2 baseA basePi 1 baseF
    (by norm_num) (by norm_num) (by norm_num) base_positive base_interior
    (by norm_num) base_independent
  obtain ⟨D, hDG, hDU⟩ := hGd.exists_mem_open badSet_open badSet_nonempty
  obtain ⟨h2, q, hq, hne, hI⟩ := badSet_failure D hDU
  exact hne (hG D hDG h2 q _ hq hI)


end
end D5.S3.ContinuousObservables.SpectralDualityUniquenessRefutation
