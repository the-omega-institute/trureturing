import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.Newton
import Reg.Support.DependentFamily

/-! Source operand registrations for regular graph CHS coefficients. -/

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Interface
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Newton
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Matrix
open scoped BigOperators
noncomputable section
open Classical
universe u

private abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => x) (fun e => nomatch e)

private def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)

private abbrev bseq_nonnegArena : Arena where
  signature := scalarSignature
  Law R := ∀ n r m : ℕ, 0 ≤ R.readout () () (bseq n r m)

private theorem bseq_nonnegRejected : ¬ bseq_nonnegArena.Law rejected := by
  intro h
  have he := h 0 0 0
  change (0 : ℝ) ≤ -1 at he
  norm_num at he

def bseq_nonnegFamily : Registration bseq_nonnegArena (type_of% @bseq_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_nonneg, rejected, bseq_nonnegRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_nonnegRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_nonnegAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_nonneg) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_nonnegUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_nonnegFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_nonnegArena⟩
  objectArena := .source ⟨bseq_nonnegArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_nonnegArena ⟨bseq_nonnegFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev bseq_monoArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n r : ℕ}, 4 ≤ r → ∀ m, bseq n 4 m ≤ R.readout () () (bseq n r m)

private theorem bseq_monoRejected : ¬ bseq_monoArena.Law rejected := by
  intro h
  have he := @h 0 4 (by omega) 0
  norm_num [rejected, realize] at he

def bseq_monoFamily : Registration bseq_monoArena (type_of% @bseq_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_mono, rejected, bseq_monoRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_monoRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_monoAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_mono) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_monoUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_monoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_monoArena⟩
  objectArena := .source ⟨bseq_monoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_monoArena ⟨bseq_monoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev trace_pow_eq_closedWalksArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ),
    R.readout () () (((G.adjMatrix ℝ) ^ k).trace) = (closedWalks G k : ℝ)

private theorem trace_pow_eq_closedWalksRejected : ¬ trace_pow_eq_closedWalksArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  norm_num [rejected, realize, closedWalks] at he

def trace_pow_eq_closedWalksFamily : Registration trace_pow_eq_closedWalksArena (type_of% @trace_pow_eq_closedWalks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_pow_eq_closedWalks, rejected, trace_pow_eq_closedWalksRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, trace_pow_eq_closedWalksRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def trace_pow_eq_closedWalksAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_pow_eq_closedWalks) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.trace_pow_eq_closedWalksUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.trace_pow_eq_closedWalksFamily
  realizationSource := none
  generated := false
  arena := .source ⟨trace_pow_eq_closedWalksArena⟩
  objectArena := .source ⟨trace_pow_eq_closedWalksArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source trace_pow_eq_closedWalksArena ⟨trace_pow_eq_closedWalksFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev sum_eigenvalues_pow_eq_closedWalksArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ),
    R.readout () () (∑ i, (adjMatrix_isHermitian G).eigenvalues i ^ k) = (closedWalks G k : ℝ)

private theorem sum_eigenvalues_pow_eq_closedWalksRejected : ¬ sum_eigenvalues_pow_eq_closedWalksArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  norm_num [rejected, realize, closedWalks] at he

def sum_eigenvalues_pow_eq_closedWalksFamily : Registration sum_eigenvalues_pow_eq_closedWalksArena (type_of% @sum_eigenvalues_pow_eq_closedWalks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_eigenvalues_pow_eq_closedWalks, rejected, sum_eigenvalues_pow_eq_closedWalksRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, sum_eigenvalues_pow_eq_closedWalksRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def sum_eigenvalues_pow_eq_closedWalksAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_eigenvalues_pow_eq_closedWalks) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.sum_eigenvalues_pow_eq_closedWalksUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.sum_eigenvalues_pow_eq_closedWalksFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sum_eigenvalues_pow_eq_closedWalksArena⟩
  objectArena := .source ⟨sum_eigenvalues_pow_eq_closedWalksArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sum_eigenvalues_pow_eq_closedWalksArena ⟨sum_eigenvalues_pow_eq_closedWalksFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev hsymm_newtonArena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) (d : ℕ),
    ((d + 1 : ℕ) : ℝ) * R.readout () () (MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ (d + 1))) =
      ∑ k ∈ range (d + 1), (∑ i, a i ^ (k + 1)) *
        MvPolynomial.eval a (MvPolynomial.hsymm ι ℝ (d - k))

private theorem hsymm_newtonRejected : ¬ hsymm_newtonArena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} (Fin 0)) inferInstance inferInstance (fun _ => 0) 0
  norm_num [rejected, realize] at he

def hsymm_newtonFamily : Registration hsymm_newtonArena.{u} (type_of% @hsymm_newton.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hsymm_newton.{u}, rejected, hsymm_newtonRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hsymm_newtonRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def hsymm_newtonAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hsymm_newton.{u}) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.hsymm_newtonUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.hsymm_newtonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hsymm_newtonArena.{u}⟩
  objectArena := .source ⟨hsymm_newtonArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hsymm_newtonArena.{u} ⟨hsymm_newtonFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_newtonArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ),
    ((d + 1 : ℕ) : ℝ) * R.readout () () (chs G (d + 1)) =
      ∑ k ∈ range (d + 1), (closedWalks G (k + 1) : ℝ) * chs G (d - k)

private theorem chs_newtonRejected : ¬ chs_newtonArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  norm_num [rejected, realize, closedWalks] at he

def chs_newtonFamily : Registration chs_newtonArena (type_of% @chs_newton) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_newton, rejected, chs_newtonRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_newtonRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_newtonAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_newton) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_newtonUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_newtonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_newtonArena⟩
  objectArena := .source ⟨chs_newtonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_newtonArena ⟨chs_newtonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_nonnegArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ), 0 ≤ R.readout () () (chs G d)

private theorem chs_nonnegRejected : ¬ chs_nonnegArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  change (0 : ℝ) ≤ -1 at he
  norm_num at he

def chs_nonnegFamily : Registration chs_nonnegArena (type_of% @chs_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_nonneg, rejected, chs_nonnegRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_nonnegRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_nonnegAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_nonneg) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_nonnegUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_nonnegFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_nonnegArena⟩
  objectArena := .source ⟨chs_nonnegArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_nonnegArena ⟨chs_nonnegFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_le_of_closedWalks_leArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (F G : SimpleGraph (Fin n)),
    (∀ k, 1 ≤ k → closedWalks F k ≤ closedWalks G k) →
    ∀ d, chs F d ≤ R.readout () () (chs G d)

private theorem chs_le_of_closedWalks_leRejected : ¬ chs_le_of_closedWalks_leArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) ⊥ (fun _ _ => le_rfl) 0
  norm_num [rejected, realize, chs] at he

def chs_le_of_closedWalks_leFamily : Registration chs_le_of_closedWalks_leArena (type_of% @chs_le_of_closedWalks_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_le_of_closedWalks_le, rejected, chs_le_of_closedWalks_leRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_le_of_closedWalks_leRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_le_of_closedWalks_leAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_le_of_closedWalks_le) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_le_of_closedWalks_leUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_le_of_closedWalks_leFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_le_of_closedWalks_leArena⟩
  objectArena := .source ⟨chs_le_of_closedWalks_leArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_le_of_closedWalks_leArena ⟨chs_le_of_closedWalks_leFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_le_topArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ),
    chs G d ≤ R.readout () () (chs (⊤ : SimpleGraph (Fin n)) d)

private theorem chs_le_topRejected : ¬ chs_le_topArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  norm_num [rejected, realize, chs] at he

def chs_le_topFamily : Registration chs_le_topArena (type_of% @chs_le_top) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_le_top, rejected, chs_le_topRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_le_topRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_le_topAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_le_top) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_le_topUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_le_topFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_le_topArena⟩
  objectArena := .source ⟨chs_le_topArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_le_topArena ⟨chs_le_topFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_two_mul_posArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ), 0 ≤ R.readout () () (chs G (2 * m))

private theorem chs_two_mul_posRejected : ¬ chs_two_mul_posArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0
  change (0 : ℝ) ≤ -1 at he
  norm_num at he

def chs_two_mul_posFamily : Registration chs_two_mul_posArena (type_of% @chs_two_mul_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_two_mul_pos, rejected, chs_two_mul_posRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_two_mul_posRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_two_mul_posAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_two_mul_pos) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_two_mul_posUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_two_mul_posFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_two_mul_posArena⟩
  objectArena := .source ⟨chs_two_mul_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_two_mul_posArena ⟨chs_two_mul_posFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev bseq_convolutionArena : Arena where
  signature := scalarSignature
  Law R := ∀ n r m : ℕ, (2 * m : ℝ) * R.readout () () (bseq n r m) =
    (n : ℝ) * ∑ j ∈ range m, (r : ℝ) ^ (j + 1) * bseq n r (m - 1 - j)

private theorem bseq_convolutionRejected : ¬ bseq_convolutionArena.Law rejected := by
  intro h
  have he := h 0 0 1
  norm_num [rejected, realize] at he

def bseq_convolutionFamily : Registration bseq_convolutionArena (type_of% @bseq_convolution) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_convolution, rejected, bseq_convolutionRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_convolutionRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_convolutionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_convolution) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_convolutionUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.bseq_convolutionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_convolutionArena⟩
  objectArena := .source ⟨bseq_convolutionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_convolutionArena ⟨bseq_convolutionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev chs_ge_bseqArena : Arena where
  signature := scalarSignature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ),
    (∀ j, 1 ≤ j → n * r ^ j ≤ closedWalks G (2 * j)) →
    ∀ m, bseq n r m ≤ R.readout () () (chs G (2 * m))

private theorem chs_ge_bseqRejected : ¬ chs_ge_bseqArena.Law rejected := by
  intro h
  have he := h (⊥ : SimpleGraph (Fin 0)) 0 (fun _ _ => by simp) 0
  norm_num [rejected, realize] at he

def chs_ge_bseqFamily : Registration chs_ge_bseqArena (type_of% @chs_ge_bseq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_ge_bseq, rejected, chs_ge_bseqRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, chs_ge_bseqRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def chs_ge_bseqAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chs_ge_bseq) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_ge_bseqUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton.chs_ge_bseqFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chs_ge_bseqArena⟩
  objectArena := .source ⟨chs_ge_bseqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chs_ge_bseqArena ⟨chs_ge_bseqFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RegularCHS.Newton
