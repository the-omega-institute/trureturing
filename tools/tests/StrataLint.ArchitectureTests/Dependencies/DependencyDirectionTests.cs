using StrataLint.Engine;
using StrataLint.Scribe;

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

    [Fact]
    public void ScribeReferencesExactlyEngineQuestPdfTomlynAndTruth()
    {
        Assert.Equal(
            ["QuestPDF", "StrataLint.Engine", "Tomlyn", "Trureturing.Truth"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(ScribeEmitter).Assembly));
    }

    [Fact]
    public void FunctionalTestsReferenceOnlyCliEngineEngineeringScopeAndScribe()
    {
        Assert.Equal(
            ["StrataLint", "StrataLint.Engine", "StrataLint.EngineeringScope", "StrataLint.Scribe"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.Tests.AdmissionTests).Assembly));
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
}
