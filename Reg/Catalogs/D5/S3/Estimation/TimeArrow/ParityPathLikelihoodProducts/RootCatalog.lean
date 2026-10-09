import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
import Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts
import Reg.Support.ParityKernelRegistrationTemplates

namespace Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena, statementIdentity := some "sha256:a891173e65cbf5af11a95ddf1a099bdec3a5eda44491c72a02b867ff47de6a7b", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts },
    { statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena, statementIdentity := some "sha256:d49f17e68a06f102643e57b4c4f20e141fd73603830a548a891b99afc9e25075", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts },
    { statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena, statementIdentity := some "sha256:b7882b0ca03e87b9976e128c5c7b46e0e307aa5758dd075b0f6ba9695fc5bd01", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forwardArena, statementIdentity := some "sha256:a891173e65cbf5af11a95ddf1a099bdec3a5eda44491c72a02b867ff47de6a7b", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts },
    { statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.backwardArena, statementIdentity := some "sha256:d49f17e68a06f102643e57b4c4f20e141fd73603830a548a891b99afc9e25075", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts },
    { statement := (_), proof := (@_root_.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product), theoremName := `D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.forward_backward_inner_product, objectArenaName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.mixedArena, statementIdentity := some "sha256:b7882b0ca03e87b9976e128c5c7b46e0e307aa5758dd075b0f6ba9695fc5bd01", registrationModuleName := `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts } }

end Reg.Catalogs.D5.S3.Estimation.TimeArrow.ParityPathLikelihoodProducts.RootCatalog
