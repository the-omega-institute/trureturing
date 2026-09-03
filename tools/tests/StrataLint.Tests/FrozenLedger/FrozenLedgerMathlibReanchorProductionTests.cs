using StrataLint.Engine;
using StrataLint.Cli;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void ProductionAdmissionRejectsAReplacementThatLeavesAnOldDependentIdentity()
    {
        var exception = Assert.Throws<FrozenLedgerAdmissionPreparationException>(() =>
            ValidateMathlibReanchor(
                baseModules: [Module("A"), Module("B", imports: ["A"])],
                candidateModules:
                [
                    ModuleWithReport(
                        "A",
                        "theorem a : True := by trivial\n",
                        statementMaterial: "drifted A"),
                    Module("B", imports: ["A"]),
                ],
                replacedModules: ["A"],
                environment: ReanchorEnvironment.PinUpgrade));

        var baseCatalog = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var baseEvents = EventFiles(baseCatalog);
        var oldA = Assert.Single(LoadEvents(baseEvents), item =>
            item.DescriptorPath == RepoPathFor("A"));
        var oldB = Assert.Single(LoadEvents(baseEvents), item =>
            item.DescriptorPath == RepoPathFor("B"));
        Assert.Contains(oldA.FrozenNodeId.Value, exception.Message, StringComparison.Ordinal);
        Assert.Contains(oldB.EventHash, exception.Message, StringComparison.Ordinal);
        Assert.Contains(RepoPathFor("B").Value, exception.Message, StringComparison.Ordinal);
        Assert.Contains(oldB.SourcePath.Value, exception.Message, StringComparison.Ordinal);
    }

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
