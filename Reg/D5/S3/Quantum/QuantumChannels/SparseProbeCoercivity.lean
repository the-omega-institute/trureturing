import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
import Reg.Support.DependentFamily

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
open LeanInformationAudit Matrix
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity

abbrev signature : Signature where
  Params := Σ d : ℕ, Fin d → ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p C => probeLoss C p.2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (hd : 0 < d) (hv : ∑ i, Complex.normSq (v i)=1)
    (μ : ℝ) (hμ : 0 < μ) (hfull : ∀ i, μ ≤ Complex.normSq (v i)),
    μ/(2+μ) * (hsSq C - Complex.normSq (trace C)/d) ≤ R.readout () ⟨d,v⟩ C

private theorem actual_law : arena.Law actual := by
  intro d C v hd hv μ hμ hfull
  exact sparse_probe_coercivity C v hd hv μ hμ hfull

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d:=1) 0 (fun _ => 1) (by decide) (by simp) 1 (by norm_num)
    (by intro i; simp)
  norm_num [rejected, realize, hsSq] at hh

def familyRegistration : Registration arena (type_of% (@sparse_probe_coercivity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, fun _ => (Real.sqrt (1/2) : ℂ)⟩, (fun _ _ => 0), Matrix.single 0 1 1, ?_⟩
    change probeLoss (fun (_ _ : Fin 2) => 0) (fun _ => (Real.sqrt (1/2) : ℂ)) ≠
      probeLoss (Matrix.single (0 : Fin 2) 1 1) (fun _ => (Real.sqrt (1/2) : ℂ))
    norm_num [probeLoss, offSq, survivalLoss,
      Matrix.mulVec, dotProduct, Matrix.single, Matrix.zero_apply, Matrix.one_apply,
      Fin.sum_univ_succ,
      Complex.normSq_ofReal, Real.sq_sqrt]

#print axioms familyRegistration

namespace Split

abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ C => hsSq C) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ),
    R.readout () d C = offSq C + ∑ i, Complex.normSq (C i i)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d:=1) 0
  norm_num [rejected, realize, offSq] at hh

def familyRegistration : Registration arena (type_of% (@hs_split)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hs_split, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨1, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    change hsSq (fun (_ _ : Fin 1) => (0 : ℂ)) ≠ hsSq (fun (_ _ : Fin 1) => (1 : ℂ))
    norm_num [hsSq, Fin.sum_univ_succ]

#print axioms familyRegistration
end Split
end Reg.D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
