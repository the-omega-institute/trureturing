import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.MathParameter
open LeanInformationAudit.Contract
def entry : Seal := { rootId := `root, options := #[] }
def count (s : Seal) : Nat := s.options.size
def ordinary : Nat := count entry
def dependentCount : Fin (entry.options.size + 1) := ⟨0, Nat.zero_lt_succ _⟩
def dependentSize : Fin (sizeOf entry + 1) := ⟨0, Nat.zero_lt_succ _⟩
def plainProposition : Prop := entry = entry
def propositionProof : plainProposition := rfl
end Boundary.MathParameter
