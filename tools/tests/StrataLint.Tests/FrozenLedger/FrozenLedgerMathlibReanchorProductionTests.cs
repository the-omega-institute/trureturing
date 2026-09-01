using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void MathlibReanchorProductionServiceReportsPropositionSourceAuthorizationFailure()
    {
        var result = ValidateMathlibReanchor(
            baseModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : False := by\n  contradiction\n",
                    statementMaterial: "old elaborated False"),
                Module("B"),
            ],
            candidateModules:
            [
                ModuleWithReport(
                    "A",
                    "theorem a : True := by\n  trivial\n",
                    statementMaterial: "new elaborated True"),
                Module("B"),
            ],
            replacedModules: ["A"],
            environment: ReanchorEnvironment.PinUpgrade,
            validateProductionPath: true);

        Assert.NotNull(result.Recognition);
        Assert.False(result.Authorized);
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(result.ProductionOutcome);
        var diagnostic = Assert.Single(rejected.Diagnostics);
        Assert.Equal(RepoPathFor("A").Value, diagnostic.Path);
        Assert.Contains(
            "proposition-source-equivalent",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "reused an active case ID",
            diagnostic.Message,
            StringComparison.Ordinal);
    }
}
