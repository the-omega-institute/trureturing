import LeanInformationAuditRegTests.SearchReduction.Model

/-! A finite executable rule system: seed → bridge → target. A one-step
reference search finds bridge from seed, but needs the independently checked
bridge to find target in the same budget. No nonemptiness hypothesis is used. -/

namespace LeanInformationAudit.Tests.SearchReduction.FiniteModel

inductive Atom where
  | seed | bridge | target
  deriving DecidableEq, Repr

/-- Supported presentations normalize before any search or target exclusion. -/
inductive Surface where
  | original | renamed | definition | projection | packing | transport
  deriving DecidableEq, Repr

abbrev Declaration := Surface × Atom

def normalize (d : Declaration) : Atom := d.2

def support (bundle : List Declaration) : List Atom :=
  (bundle.map normalize).eraseDups

/-- All branching is explicit and bounded; there is no oracle for derivability. -/
def search : Nat → List Atom → Atom → Bool
  | 0, known, t => known.contains t
  | n + 1, known, t => known.contains t || match t with
    | .seed => false
    | .bridge => search n known .seed
    | .target => search n known .bridge

def baseline : List Atom := [.seed]

/-- Compilation in this toy system checks an actual two-step derivation. -/
def checked (t : Atom) : Bool := search 2 baseline t

def run (known : List Atom) (t : Atom) : Run :=
  if search 1 known t then .found else .exhausted

/-- The search environment removes T and every presentation of T even when a
malformed submission contains them. The clean flag also rejects that submission. -/
def additions (t : Atom) (bundle : List Declaration) : List Atom :=
  (support bundle).filter (· != t)

def audit (t : Atom) (bundle : List Declaration) : Verdict :=
  classify (checked t) (baseline.contains t) (run baseline t)
    ((support bundle).all checked) ((support bundle).all (· != t))
    (run (baseline ++ additions t bundle) t)

def usefulStructure : List Declaration := [(.original, .bridge)]

/-- T3: both classes are inhabited by direct evaluation of the rule system. -/
theorem concrete_nondegeneracy :
    audit .bridge [] = .bindOnly ∧ audit .target usefulStructure = .nonBindOnly := by
  decide

/-- The useful helper is easy itself; the paired target is different from it. -/
theorem genuine_paired_reduction :
    run baseline .target = .exhausted ∧
    run (baseline ++ additions .target usefulStructure) .target = .found ∧
    checked .bridge = true ∧ Atom.bridge ≠ .target := by
  decide

/-- T1 has a concrete counterpart: unbounded closure reaches all three tasks. -/
theorem finite_closure_degenerate (t : Atom) :
    checked t = true ∧ ¬ unboundedContent (fun a => search 2 baseline a = true) t := by
  change checked t = true ∧ ¬ ¬ search 2 baseline t = true
  cases t <;> decide

/-- T2 is witnessed by an actual compiled alias of the seed. -/
theorem finite_literal_alias_endpoint :
    checked (normalize (.renamed, .seed)) = true ∧
    literal (checked (normalize (.renamed, .seed))) = .nonBindOnly ∧
    audit (normalize (.renamed, .seed)) [] = .bindOnly := by
  decide

/-- T4: each supported presentation of an existing baseline statement is bound. -/
theorem all_baseline_presentations_bind (surface : Surface) :
    audit (normalize (surface, .seed)) [] = .bindOnly := by
  cases surface <;> decide

/-- Renaming a declaration changes no normalized input. -/
theorem helper_renaming_invariant (s₁ s₂ : Surface) (a t : Atom) :
    audit t [(s₁, a)] = audit t [(s₂, a)] := rfl

/-- Duplicate presentation pieces share the same support and do not buy budget. -/
theorem helper_splitting_invariant (s₁ s₂ : Surface) (a t : Atom) :
    audit t [(s₁, a), (s₂, a)] = audit t [(.original, a)] := by
  cases a <;> cases t <;> rfl

theorem normalized_structure_invariant (s₁ s₂ : List Declaration) (t : Atom)
    (same : support s₁ = support s₂) : audit t s₁ = audit t s₂ := by
  simp only [audit, additions, same]

/-- T6: target-only self exposure, including each alias, is filtered and rejected. -/
theorem target_alias_cannot_close (surface : Surface) :
    additions .target [(surface, .target)] = [] ∧
    audit .target [(surface, .target)] = .insufficient := by
  cases surface <;> decide

/-- Even adding a real bridge does not excuse retaining a forbidden target. -/
theorem mixed_target_leak_rejected :
    run (baseline ++ additions .target [(.original, .bridge), (.packing, .target)])
      .target = .found ∧
    audit .target [(.original, .bridge), (.packing, .target)] = .insufficient := by
  decide

theorem empty_structure_not_content : audit .target [] = .insufficient := by decide

#eval (audit .bridge [], audit .target usefulStructure,
  audit .target [(.renamed, .target)], audit .target [])

#print axioms concrete_nondegeneracy
#print axioms genuine_paired_reduction
#print axioms finite_closure_degenerate
#print axioms finite_literal_alias_endpoint
#print axioms all_baseline_presentations_bind
#print axioms helper_renaming_invariant
#print axioms helper_splitting_invariant
#print axioms normalized_structure_invariant
#print axioms target_alias_cannot_close
#print axioms mixed_target_leak_rejected
#print axioms empty_structure_not_content

end LeanInformationAudit.Tests.SearchReduction.FiniteModel
