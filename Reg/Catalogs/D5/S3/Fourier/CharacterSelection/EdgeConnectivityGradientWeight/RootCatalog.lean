import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
import Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
import Reg.Support.GraphCutRegistrationTemplates

namespace Reg.Catalogs.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.RootCatalog
open LeanInformationAudit

def rootCatalog.{u_1} : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight.{u_1}), theoremName := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, objectArenaName := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena, statementIdentity := some "sha256:1adc10ad04469401acae8c1ce04439ddd5de2c262b30eb8bb5df995be3588364", registrationModuleName := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight.{u_1}), theoremName := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, objectArenaName := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena, statementIdentity := some "sha256:1adc10ad04469401acae8c1ce04439ddd5de2c262b30eb8bb5df995be3588364", registrationModuleName := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight } }

end Reg.Catalogs.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.RootCatalog
