import Lean

namespace LeanInformationAudit

syntax (name := sealInformationTheoryCmd) "#seal_information_theory" : command

syntax (name := stageInformationAnalysisCmd)
  "#stage_information_analysis" ident ident : command

syntax (name := exportInformationAnalysisCmd)
  "#export_information_analysis" ident ident (" output " str)?
    (" analysis_output " str)? (" ascii_output " str)? : command

end LeanInformationAudit
