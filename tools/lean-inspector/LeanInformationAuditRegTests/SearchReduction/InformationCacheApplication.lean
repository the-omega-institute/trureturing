import LeanInformationAuditRegTests.SearchReduction.InformationCache.LawFixture
namespace LeanInformationAudit.Tests.SearchReduction.InformationCacheApplication
open LeanInformationAudit.AuricFib.Contract
open LeanInformationAuditRegTests.SearchReduction.InformationCache.LawFixture
private noncomputable def currentApplication : Application.{0,0,0,0,0,0} RegisteredPos.target :=
  RegisteredPos.strict
noncomputable def application : Application.{0,0,0,0,0,0} RegisteredPos.target :=
  currentApplication
end LeanInformationAudit.Tests.SearchReduction.InformationCacheApplication
