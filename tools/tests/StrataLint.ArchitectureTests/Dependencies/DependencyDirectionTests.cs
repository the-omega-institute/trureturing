using StrataLint.Engine;
using StrataLint.Scribe;
using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

public sealed class DependencyDirectionTests
{
    /// <summary>
    /// The list is the declaration point for a new trust root, which is why it is written
    /// out rather than derived: anything the engine links against can decide what the
    /// harness admits. Markdig parses the block AST behind the default atomizer; it is
    /// BSD-2-Clause, pure managed code, and has no package dependencies of its own on this
    /// target framework, so adopting it adds exactly one name here and nothing beneath it.
    /// Trureturing.Truth is the packable truth-graph read/write/verify library at the bottom
    /// of the graph; it references nothing StrataLint and only the BCL, so linking the engine
    /// against it adds exactly one name here and nothing beneath it.
    /// </summary>
    [Fact]
    public void EngineReferencesExactlyBclDunetMarkdigPidginRoslynAndTruth()
    {
        Assert.Equal(
            ["Dunet", "Markdig", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp", "Pidgin", "Trureturing.Truth"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(AdmissionPipeline).Assembly));
    }

    [Fact]
    public void CliReferencesExactlyEngineScribeTomlynTruthAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "StrataLint.Scribe", "Tomlyn", "Trureturing.Truth", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    /// <summary>
    /// Jint runs the vendored KaTeX so the markdown gate parses formulas with the site's
    /// own parser rather than a second reading of its grammar. It is BSD-2-Clause pure
    /// managed code and brings one name beneath it, Acornima (BSD-3-Clause), its
    /// JavaScript parser; nothing it runs is trusted, because the gate keeps the parse
    /// verdict and discards the rendered HTML.
    /// </summary>
    [Fact]
    public void ScribeReferencesExactlyEngineJintQuestPdfTomlynAndTruth()
    {
        Assert.Equal(
            ["Jint", "QuestPDF", "StrataLint.Engine", "Tomlyn", "Trureturing.Truth"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(ScribeEmitter).Assembly));
    }

    [Fact]
    public void FunctionalTestsReferenceOnlyCliEngineAndScribe()
    {
        Assert.Equal(
            ["StrataLint", "StrataLint.Engine", "StrataLint.Scribe"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.Tests.AdmissionTests).Assembly));
        Assert.Equal(
            // Engine 经 Cli 传递可得,故这条直接引用是多余的 extra-production-reference 存量债;
            // 本 PR 顺手还掉它(拓扑棘轮要求碰债务面即严格减债)。程序集级引用集不变。
            ["../../StrataLint.Cli/StrataLint.Cli.csproj"],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.Tests",
                "StrataLint.Tests.csproj"))));
    }

    [Fact]
    public void EngineeringScopeTestsReferenceOnlyEngineeringScope()
    {
        Assert.Equal(
            ["StrataLint.EngineeringScope"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.EngineeringScope.Tests.TestProcessRunnerTests).Assembly));
        Assert.Equal(
            ["../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj"],
            ProjectReferences(XDocument.Load(Path.Combine(
                RepositoryLayout.FindRoot(),
                "tools",
                "tests",
                "StrataLint.EngineeringScope.Tests",
                "StrataLint.EngineeringScope.Tests.csproj"))));
    }

    [Fact]
    public void ScribeTestsReferenceOnlyEngineAndScribe()
    {
        Assert.Equal(
            ["StrataLint.Engine", "StrataLint.Scribe"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.Scribe.Tests.DocumentAstTests).Assembly));
    }

    [Fact]
    public void EnginePolicyRejectsCliAsARedFixture()
    {
        var unexpected = AssemblyReferencePolicy.UnexpectedReferences(
            typeof(StrataLint.Cli.Program).Assembly,
            "Dunet",
            "Pidgin");

        Assert.Contains("StrataLint.Engine", unexpected);
        Assert.Contains("YamlDotNet", unexpected);
    }

    private static string[] ProjectReferences(XDocument project) => project
        .Descendants()
        .Where(static element => element.Name.LocalName == "ProjectReference")
        .Select(static element => (string?)element.Attribute("Include"))
        .OfType<string>()
        .Order(StringComparer.Ordinal)
        .ToArray();
}
