namespace StrataLint.ArchitectureTests;

public sealed class ScriptTestOwnershipPolicyTests
{
    private const string ScriptProject = "tools/tests/StrataLint.ScriptTests";
    private const string UnitProject = "tools/tests/StrataLint.Tests";
    private const string PreflightSubject = "tools/scripts/preflight.sh";
    private const string ScriptNamespaceDeclaration = "namespace StrataLint.ScriptTests;";

    [Fact]
    public void ScriptOwnedMethodOutsideScriptTestsIsRejected()
    {
        var findings = Inspect(
            [PreflightSubject],
            Source(
                UnitProject,
                "tools/tests/StrataLint.Tests/Commands/PreflightTests.cs",
                OwnerSource(PreflightSubject, "PreflightTests")));

        Assert.Single(findings, finding => finding.Code == "SCRIPT-OWNER-PROJECT");
    }

    [Fact]
    public void ScriptTestUnitWithoutOneLegalSubjectIsRejected()
    {
        var findings = Inspect(
            [PreflightSubject],
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Scripts/preflight.Tests.cs",
                "namespace StrataLint.ScriptTests; public sealed class PreflightTests { [Fact] public void Runs() { } }"));

        Assert.Single(findings, finding => finding.Code == "SCRIPT-OWNER-SUBJECT");
    }

    [Fact]
    public void SubjectWithMultipleOwnerUnitsIsRejected()
    {
        var source = $$"""
            {{ScriptNamespaceDeclaration}}
            [ScriptSubject("{{PreflightSubject}}")] public sealed class FirstPreflightTests { [Fact] public void First() { } }
            [ScriptSubject("{{PreflightSubject}}")] public sealed class SecondPreflightTests { [Fact] public void Second() { } }
            """;

        var findings = Inspect(
            [PreflightSubject],
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Scripts/preflight.Tests.cs",
                source));

        Assert.Single(findings, finding => finding.Code == "SCRIPT-OWNER-DUPLICATE");
    }

    [Fact]
    public void OwnerMirrorPathMustMatchSubject()
    {
        var findings = Inspect(
            [PreflightSubject],
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Scripts/wrong.Tests.cs",
                OwnerSource(PreflightSubject, "PreflightTests")));

        Assert.Single(findings, finding => finding.Code == "SCRIPT-OWNER-MIRROR");
    }

    [Fact]
    public void ValidMirroredScriptOwnerIsAccepted()
    {
        var sources = new[]
        {
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Scripts/preflight.Tests.cs",
                OwnerSource(PreflightSubject, "PreflightTests")),
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Makefiles/RootMakefile.Tests.cs",
                OwnerSource("Makefile", "RootMakefileTests")),
            Source(
                ScriptProject,
                "tools/tests/StrataLint.ScriptTests/Makefiles/ToolsMakefile.Tests.cs",
                OwnerSource("tools/Makefile", "ToolsMakefileTests")),
        };

        Assert.Empty(Inspect([PreflightSubject, "Makefile", "tools/Makefile"], sources));
    }

    [Fact]
    public void SubjectWithoutOwnerIsAccepted() =>
        Assert.Empty(Inspect([PreflightSubject]));

    [Fact]
    public void RepositoryScriptOwnersAreClosed()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var subjects = ProtectedBaseScriptSubjects.Enumerate(repositoryRoot);
        var sources = GitIndexRepositoryFiles.EnumerateDeclared(repositoryRoot, "tools/tests")
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => new ScriptOwnershipSource(
                ProjectPartition(file.RelativePath),
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();

        Assert.Empty(ScriptTestOwnershipPolicy.Inspect(subjects, sources));
    }

    private static IReadOnlyList<ScriptOwnershipFinding> Inspect(
        IReadOnlyList<string> subjects,
        params ScriptOwnershipSource[] sources) =>
        ScriptTestOwnershipPolicy.Inspect(subjects, sources);

    private static ScriptOwnershipSource Source(string project, string path, string content) =>
        new(project, path, content);

    private static string OwnerSource(string subject, string typeName) => $$"""
        {{ScriptNamespaceDeclaration}}
        [ScriptSubject("{{subject}}")] public sealed class {{typeName}} { [Fact] public void Runs() { } }
        """;

    private static string ProjectPartition(string sourcePath)
    {
        var slash = sourcePath.IndexOf('/', "tools/tests/".Length);
        return slash < 0 ? sourcePath : sourcePath[..slash];
    }
}
