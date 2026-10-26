import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraCoreResidual
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Source-bound dependent-family evidence for the actual mathematical operands. -/

namespace Reg.D5.S3.Combinatorics.Geometry.MiuraCoreResidual

open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
open MiuraCoreResidual
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- Dimensions and deletion coordinate remain in the original physical grid. -/
structure Parameter where
  m : ℕ
  n : ℕ
  hm : 0 < m
  j : Fin n

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter
    (fun p => {h : Cell p.m p.n → ℤ // frozenColumn h p.j})
    (fun p => Cell p.m (p.n - 1) → ℤ)

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property)
    (fun e => nomatch e)

/-- The complete source telescope, replacing only the actual contracted array. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (a b : ℕ) (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j), Residual a b h →
      Residual a b (R.readout () ⟨m, n, hm, j⟩ ⟨h, hfrz⟩)

theorem bridge :
    (type_of% (@contractAt_residual)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := contractAt_residual

def rejected : Realization signature :=
  realize signature
    (fun (_ : Unit) p x v => actual.readout () p x v + 1)
    (fun e => nomatch e)

/-- A real residual input makes the translated readout violate normalization. -/
theorem rejected_not_law_of_residual {m n : ℕ} (a b : ℕ)
    (h : Cell m n → ℤ) (hm : 0 < m) (j : Fin n)
    (hfrz : frozenColumn h j) (hr : Residual a b h) :
    ¬ arena.Law rejected := by
  intro hbad
  have hb := hbad a b h hm j hfrz hr
  have hgood := contractAt_residual a b h hm j hfrz hr
  have hn : 0 < n - 1 := by have := hfrz.1; have := hfrz.2.1; omega
  let origin : Cell m (n - 1) := (⟨0, hm⟩, ⟨0, hn⟩)
  have hzero := hb.1.2 origin rfl rfl
  have hactual := hgood.1.2 origin rfl rfl
  change contractAt h hm j hfrz origin + 1 = 0 at hzero
  omega

abbrev lineParameter : Parameter := ⟨1, 3, by decide, ⟨1, by decide⟩⟩

def lineState (k : ℤ) : signature.State lineParameter :=
  ⟨fun v => (v.2.val : ℤ) + k, by
    refine ⟨by decide, by decide, ?_⟩
    intro i
    norm_num
    ring⟩

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  intro heq
  have hvalue := congrFun heq ((0 : Fin 1), (0 : Fin 2))
  norm_num [actual, realize, signature, lineParameter, lineState, contractAt] at hvalue

/-- Full family variation and sensitivity use an actual residual source input. -/
def realization_of_residual {m n : ℕ} (a b : ℕ)
    (h : Cell m n → ℤ) (hm : 0 < m) (j : Fin n)
    (hfrz : frozenColumn h j) (hr : Residual a b h) :
    Registration arena (type_of% (@contractAt_residual)) := by
  have hbad := rejected_not_law_of_residual a b h hm j hfrz hr
  exact {
    actual := actual
    bridge := bridge
    variation := ⟨actual_law, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := actual_dependence }

end

end Reg.D5.S3.Combinatorics.Geometry.MiuraCoreResidual
