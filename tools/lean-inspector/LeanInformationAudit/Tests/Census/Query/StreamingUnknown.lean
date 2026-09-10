import LeanInformationAudit.Tests.Census.Query.StreamingOutside

open LeanInformationAudit

namespace LeanInformationAudit.Tests.Census.Query.StreamingUnknown

-- The compiler can evaluate this key, but its raw type is not literal syntax.
-- A streaming absence claim must therefore fail closed for this scope.
def key : StatementKey :=
  ⟨``StreamingTarget.target, "sha256:" ++ String.ofList (List.replicate 64 '0')⟩

def evidence : AnalysisDisposition key :=
  .unreachable ⟨.noCanonicalObjectCarrier, ``StreamingOutside.evidence⟩

end LeanInformationAudit.Tests.Census.Query.StreamingUnknown
