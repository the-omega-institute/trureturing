module
public import D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic
public import LeanInformationAuditInterface.Contract.Registration
public import Reg.Support.DependentFamily

@[expose] public section

/-! Full-telescope source-family audit attempts for the mathematical target. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.SparseNecklaceRounding

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ l => bits l) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def law (observe : List ℕ → ℤ) : Prop :=
  ∀ (l r : List ℕ) (a : ℕ), (∀ b ∈ (l ++ [a]) ++ r, 2 ≤ b) →
    let k := l.sum + a + r.sum
    let e := (observe ((l ++ [a]) ++ r)).toNat
    let N := modulus k
    let h := observe (r ++ (l ++ [a]))
    let h' := observe ((a :: r) ++ l)
    let z := observe r
    let z' := observe (a :: r)
    let n := (N - h') / 2
    let tau := (z' + 1) / 2
    2 ≤ k ∧ 0 < (e : ℤ) ∧ 3 * (e : ℤ) ≤ N ∧
    0 < h ∧ 3 * h ≤ N ∧ 0 < h' ∧ 3 * h' ≤ N ∧
    h % 2 = 1 ∧ h' % 2 = 1 ∧
    0 ≤ z ∧ z < h ∧ 0 < z' ∧ z' ≤ h' ∧ z' % 2 = 1 ∧
    (2 : ℤ) ^ a * h = N + h' ∧ z' = (2 : ℤ) ^ a * z + 1 ∧
    (2 : ℤ) ^ r.sum * e = h + N * z ∧
    2 * n = N - h' ∧ 2 * tau = z' + 1 ∧
    N ≤ 3 * n ∧ n ≤ N / 2 ∧ 1 ≤ tau ∧ tau ≤ h' ∧
    ((2 : ℤ) ^ (a - 1) - 1) * h = n + h' - h ∧
    ((2 : ℤ) ^ (a - 1) - 1) * z + tau = z' - z ∧
    0 < n + h' - (e : ℤ) ∧ 2 * n + z' ≤ N ∧
    actualSource (k + 1) (2 * e) (Fin.last k) = (e : ℤ) ∧
    (∀ t : ℕ, t ≤ a - 2 → ∃ hi : r.sum + t < k,
      let i : Fin k := ⟨r.sum + t, hi⟩
      let mass := (2 : ℤ) ^ t * h
      let charge := (2 : ℤ) ^ t * z
      0 < mass ∧ 3 * mass ≤ N ∧ 0 ≤ charge ∧ charge < mass ∧
      actualSource k e i = mass ∧
      actualSource (k + 1) (2 * e) i.castSucc = 2 * mass - charge) ∧
    (∃ hi : r.sum + a - 1 < k,
      let i : Fin k := ⟨r.sum + a - 1, hi⟩
      actualSource k e i = -n ∧
      actualSource (k + 1) (2 * e) i.castSucc = -2 * n - tau ∧
      0 < n ∧ 0 < 2 * n + tau ∧ 2 * n + tau ≤ N)

abbrev arena : Arena where
  signature := signature
  Law R := law (R.readout () ())

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] [] 2 (by intro b hb; simp only [List.nil_append,List.append_nil,List.mem_singleton] at hb; omega)
  norm_num [law,rejected,realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),[],[2],?_⟩
  norm_num [actual,realize,bits]

/-- Full telescope, exact reconstruction, actual law, variation, sensitivity,
and observational dependence. The Contract sourceSelection and its compiled
binding evidence are separate unfinished integration obligations. -/
def source_registration : Registration arena (type_of% (@native_chain_coordinates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_chain_coordinates,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := actual_dependence

/-- The full dependent source law is proved above. Exact compiler source
occurrence selection is still absent, so this typed attempt does not claim a
validated four-slot binding. -/
noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@native_chain_coordinates) (type_of% (realize signature (fun _ _ l => bits l) (fun e => nomatch e))) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic.native_chain_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => bits l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.SparseNecklaceRounding.Arithmetic
