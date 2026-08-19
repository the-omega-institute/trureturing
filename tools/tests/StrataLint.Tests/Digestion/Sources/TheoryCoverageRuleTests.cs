using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The check that makes an undigested volume impossible to miss. A digestion source has
/// always had to name a governed document; nothing asked the question the other way round,
/// so a governed theory document with no source produced no symptom at all — the reader
/// that would have noticed was the one that was missing.
/// </summary>
public sealed class TheoryCoverageRuleTests
{
    private const string GovernedPath = "docs/develop/theory/GOVERNED.md";
    private const string DigestedPath = "docs/develop/theory/DIGESTED.md";

    /// <summary>The loader requires canonical bytes, so the paths go in sorted position.</summary>
    private static string Registry(params string[] theoryDocuments) =>
        TestRegistry.Canonical.Replace(
            "  - \"docs/develop/spec/golden-ledger-repo-spec.md\"\n",
            "  - \"docs/develop/spec/golden-ledger-repo-spec.md\"\n"
            + string.Concat(theoryDocuments
                .Order(StringComparer.Ordinal)
                .Select(static path => $"  - \"{path}\"\n")),
            StringComparison.Ordinal);

    private static string[] Findings(string registry)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        var policy = RegistryLoadAssert.Accepted(outcome).Policy;
        var snapshot = DigestionTestSupport.Snapshot(
            (GovernedPath, Encoding.UTF8.GetBytes("# 未消化\n")),
            (DigestedPath, Encoding.UTF8.GetBytes("# 已消化\n")));
        return BackfillInventoryRule.EvaluateDocument(
                new BackfillInventoryValidationContext(
                    snapshot,
                    snapshot,
                    policy,
                    DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
                    null),
                DigestionTestSupport.Document(
                    AtomizerRegistry.GenericId,
                    [],
                    "digested",
                    DigestedPath,
                    GenreRegistryCheck.Collected([])))
            .Select(static finding => finding.Message)
            .ToArray();
    }

    [Fact]
    public void AGovernedTheoryDocumentWithNoDigestionSourceIsReported()
    {
        var findings = Findings(Registry(GovernedPath, DigestedPath));

        var finding = Assert.Single(findings, message =>
            message.Contains("has no digestion source", StringComparison.Ordinal));
        Assert.Contains(GovernedPath, finding, StringComparison.Ordinal);
        Assert.Contains("make ingest", finding, StringComparison.Ordinal);
    }

    // 断言指名到 DigestedPath,不是「什么都不该报」。理论卷改按路径规则治理后,本检查
    // 迭代的是**文件树**而非 registry 清单,而本夹具的树里本就还有一个未消化的
    // GOVERNED.md——它被报出来正是新行为要的。旧的宽断言只在「清单决定哪些理论卷受治理」
    // 的前提下成立,而那个前提已被移除。
    [Fact]
    public void ATheoryDocumentThatHasASourceIsNotReported()
    {
        var findings = Findings(Registry(DigestedPath));

        Assert.DoesNotContain(
            findings,
            static message => message.Contains(DigestedPath, StringComparison.Ordinal)
                && message.Contains("has no digestion source", StringComparison.Ordinal));
    }
}
