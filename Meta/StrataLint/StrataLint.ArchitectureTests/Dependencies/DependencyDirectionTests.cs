using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class DependencyDirectionTests
{
    [Fact]
    public void DefinitionsReferencesOnlyPlatformAssemblies()
    {
        Assert.Empty(AssemblyReferencePolicy.NonPlatformReferences(typeof(Anchor).Assembly));
    }

    [Fact]
    public void EngineReferencesExactlyBclDunetAndPidgin()
    {
        Assert.Equal(
            ["Dunet", "Pidgin"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(AdmissionPipeline).Assembly));
    }

    [Fact]
    public void CliReferencesExactlyEngineAndYamlDotNet()
    {
        Assert.Equal(
            ["StrataLint.Engine", "YamlDotNet"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(StrataLint.Cli.Program).Assembly));
    }

    [Fact]
    public void ScribeReferencesExactlyDefinitionsEngineAndQuestPdf()
    {
        Assert.Equal(
            ["QuestPDF", "StrataLint.Definitions", "StrataLint.Engine"],
            AssemblyReferencePolicy.NonPlatformReferences(typeof(ScribeEmitter).Assembly));
    }

    [Fact]
    public void FunctionalTestsReferenceOnlyCliDefinitionsAndEngine()
    {
        Assert.Equal(
            ["StrataLint", "StrataLint.Definitions", "StrataLint.Engine"],
            AssemblyReferencePolicy.ApplicationReferences(
                typeof(StrataLint.Tests.AdmissionTests).Assembly));
    }

    [Fact]
    public void ScribeTestsReferenceOnlyDefinitionsEngineAndScribe()
    {
        Assert.Equal(
            ["StrataLint.Definitions", "StrataLint.Engine", "StrataLint.Scribe"],
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
