import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
import Reg.Support.PathCurrentRegistrationTemplates

namespace Reg.Catalogs.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.RootCatalog
open LeanInformationAudit

def rootCatalog.{u_1} : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current.{u_1}), theoremName := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena, statementIdentity := some "sha256:9fe0bf0ee41c6c4aa060ac168ffce94a11bf8a412657c49411610c9ce698f7de", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current.{u_1}), theoremName := `D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.log_forward_div_reverse_eq_current, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.arena, statementIdentity := some "sha256:9fe0bf0ee41c6c4aa060ac168ffce94a11bf8a412657c49411610c9ce698f7de", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent } }

end Reg.Catalogs.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent.RootCatalog
