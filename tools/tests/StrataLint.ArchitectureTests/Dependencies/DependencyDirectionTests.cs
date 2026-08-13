using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class DependencyDirectionTests
{
    [Fact]
    public void EngineReferencesExactlyBclDunetPidginAndRoslyn()
    {
        Assert.Equal(
            ["Dunet", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp", "Pidgin"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(AdmissionPipeline).Assembly));
    }

    [Fact]
    public void CliReferencesExactlyEngineScribeTomlynAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "StrataLint.Scribe", "Tomlyn", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    [Fact]
    public void ScribeReferencesExactlyEngineQuestPdfAndTomlyn()
    {
        Assert.Equal(
            ["QuestPDF", "StrataLint.Engine", "Tomlyn"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(ScribeEmitter).Assembly));
    }

    [Fact]
    public void FunctionalTestsReferenceOnlyCliAndEngine()
    {
        Assert.Equal(
            ["StrataLint", "StrataLint.Engine"],
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
