namespace StrataLint.ArchitectureTests;

public sealed class ScriptTestOwnershipPolicyTests
{
    private const string ScriptProject =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
    private const string UnitProject =
        "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj";

    [Fact]
    public void ProtectedSubjectsComeFromTheGitIndexWithoutAnInstanceList()
    {
        var root = RepositoryLayout.FindRoot();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;

        var subjects = ScriptTestOwnershipPolicy.DeriveProtectedSubjects(snapshot);

        Assert.Equal(35, subjects.Count);
        Assert.Contains(".github/scripts/harness-gate.sh", subjects);
        Assert.Contains("tools/lean-inspector/inspect.sh", subjects);
        Assert.Contains("Makefile", subjects);
        Assert.Contains("tools/Makefile", subjects);
    }

    [Fact]
    public void NewUnitProjectMethodThatExecutesAProtectedScriptBlocks()
    {
        const string path = "tools/tests/StrataLint.Tests/NewPreflightTests.cs";
        const string source = """
            class NewPreflightTests {
              [Fact] public void RunsPreflight() => TestProcessRunner.Run(
                "/bin/bash",
                [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")],
                ".",
                TestBudgets.ScriptProcessHangGuard,
                1024);
            }
            """;
        var forkPoint = Case(("tools/scripts/preflight.sh", "#!/bin/sh\n"));
        var current = Case(
            ("tools/scripts/preflight.sh", "#!/bin/sh\n"),
            Source(path, UnitProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Equal(path, finding.Path);
        Assert.Contains("must compile into StrataLint.ScriptTests", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredSubjectMustEqualTheTouchedSubject()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        const string other = "tools/scripts/preflight.sh";
        var path = ScriptTestOwnershipPolicy.MirrorPath(subject);
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void RunsWrongScript() => RepositoryAccessor.CopyTo(
                RepositoryRelativePath.Create("{{other}}"), "fixture");
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"), (other, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            (other, "#!/bin/sh\n"),
            Source(path, ScriptProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains("declares", finding.Message, StringComparison.Ordinal);
        Assert.Contains(other, finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CorrectlyOwnedMirroredScriptMethodIsAdmitted()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        var path = ScriptTestOwnershipPolicy.MirrorPath(subject);
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void RunsSubject() => RepositoryAccessor.CopyTo(
                RepositoryRelativePath.Create("{{subject}}"), "fixture");
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(path, ScriptProject, source));

        Assert.Empty(Evaluate(current, forkPoint));
    }

    [Fact]
    public void ScriptProjectMethodWithoutAStaticSubjectTouchBlocks()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        var path = ScriptTestOwnershipPolicy.MirrorPath(subject);
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void PureProgramTest() => Assert.Equal("{{subject}}", "{{subject}}");
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(path, ScriptProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains("must statically touch its declared subject", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnresolvedRepositoryPathBlocksInsteadOfFailingOpen()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        var path = ScriptTestOwnershipPolicy.MirrorPath(subject);
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void ReadsVariable() {
                var path = SubjectPath();
                File.ReadAllText(path);
              }
              private static string SubjectPath() => "{{subject}}";
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(path, ScriptProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains("unknown script path", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnresolvedExecutionPathBlocksInsteadOfFailingOpen()
    {
        const string subject = "tools/scripts/preflight.sh";
        const string path = "tools/tests/StrataLint.Tests/NewPreflightTests.cs";
        const string source = """
            class NewPreflightTests {
              [Fact] public void RunsVariableScript() {
                var script = SubjectPath();
                TestProcessRunner.Run(
                  "/bin/bash", [script], ".", TestBudgets.ScriptProcessHangGuard, 1024);
              }
              private static string SubjectPath() => "tools/scripts/preflight.sh";
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(path, UnitProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains("must compile into StrataLint.ScriptTests", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DirectoryEnumerateFilesBlocksAsUnknownEvenWithALiteralPattern()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        var path = ScriptTestOwnershipPolicy.MirrorPath(subject);
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void EnumeratesScripts() => Directory.EnumerateFiles(
                TestRepositoryLayout.FindRoot(), "*.sh", SearchOption.AllDirectories).ToArray();
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(path, ScriptProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains("unknown script path", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedCrossTypeHelperThatExecutesAProtectedScriptBlocks()
    {
        const string subject = "tools/scripts/preflight.sh";
        const string testPath = "tools/tests/StrataLint.Tests/NewPreflightTests.cs";
        const string helperPath = "tools/tests/StrataLint.Tests/PreflightInvoker.cs";
        const string testSource = """
            class NewPreflightTests {
              [Fact] public void RunsPreflight() => PreflightInvoker.Run();
            }
            """;
        const string originalHelper = """
            static class PreflightInvoker {
              public static void Run() { }
            }
            """;
        const string changedHelper = """
            static class PreflightInvoker {
              public static void Run() => TestProcessRunner.Run(
                "/bin/bash",
                [Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/preflight.sh")],
                ".",
                TestBudgets.ScriptProcessHangGuard,
                1024);
            }
            """;
        var forkPoint = Case(
            (subject, "#!/bin/sh\n"),
            Source(testPath, UnitProject, testSource),
            Source(helperPath, UnitProject, originalHelper));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(testPath, UnitProject, testSource),
            Source(helperPath, UnitProject, changedHelper));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Equal(testPath, finding.Path);
        Assert.Contains("must compile into StrataLint.ScriptTests", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnchangedLegacyUnitScriptTestIsOutsideTheDelta()
    {
        const string subject = "tools/lean-inspector/inspect.sh";
        const string path = "tools/tests/StrataLint.Tests/Commands/LeanReport/LeanInspectorScriptTests.cs";
        const string source = """
            class LeanInspectorScriptTests {
              [Fact] public void RunsInspector() => File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/inspect.sh"));
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"), Source(path, UnitProject, source));
        var current = Case((subject, "#!/bin/sh\n"), Source(path, UnitProject, source));

        Assert.Empty(Evaluate(current, forkPoint));
    }

    [Fact]
    public void PartialFragmentsFormOneUnitAndShareOneDeclaration()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        var mirror = ScriptTestOwnershipPolicy.MirrorPath(subject);
        const string declarationPath =
            "tools/tests/StrataLint.ScriptTests/Scripts/worktree/WarmDonor.Subject.cs";
        var declaration = $$"""
            [ScriptSubject("{{subject}}")] public sealed partial class WarmDonorTests { }
            """;
        var runnable = $$"""
            public sealed partial class WarmDonorTests {
              [Fact] public void RunsSubject() => RepositoryAccessor.CopyTo(
                RepositoryRelativePath.Create("{{subject}}"), "fixture");
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(declarationPath, ScriptProject, declaration),
            Source(mirror, ScriptProject, runnable));

        Assert.Empty(Evaluate(current, forkPoint));
    }

    [Fact]
    public void RunnableFragmentMustUseTheSubjectsMirrorPath()
    {
        const string subject = "tools/scripts/worktree/warm-donor.sh";
        const string wrongPath =
            "tools/tests/StrataLint.ScriptTests/Scripts/worktree/WarmDonorTests.cs";
        var source = $$"""
            [ScriptSubject("{{subject}}")] class WarmDonorTests {
              [Fact] public void RunsSubject() => RepositoryAccessor.CopyTo(
                RepositoryRelativePath.Create("{{subject}}"), "fixture");
            }
            """;
        var forkPoint = Case((subject, "#!/bin/sh\n"));
        var current = Case(
            (subject, "#!/bin/sh\n"),
            Source(wrongPath, ScriptProject, source));

        var finding = Assert.Single(Evaluate(current, forkPoint));

        Assert.Contains(ScriptTestOwnershipPolicy.MirrorPath(subject), finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Makefile", "tools/tests/StrataLint.ScriptTests/Makefiles/RootMakefile.Tests.cs")]
    [InlineData("tools/Makefile", "tools/tests/StrataLint.ScriptTests/Makefiles/ToolsMakefile.Tests.cs")]
    [InlineData(
        ".github/scripts/harness-gate.sh",
        "tools/tests/StrataLint.ScriptTests/Scripts/github/harness-gate.Tests.cs")]
    [InlineData(
        "tools/lean-inspector/inspect.sh",
        "tools/tests/StrataLint.ScriptTests/Scripts/lean-inspector/inspect.Tests.cs")]
    public void MirrorRulesCoverMakefilesAndTheTwoNonstandardScripts(
        string subject,
        string expected) =>
        Assert.Equal(expected, ScriptTestOwnershipPolicy.MirrorPath(subject));

    private static IReadOnlyList<ScriptTestOwnershipFinding> Evaluate(
        OwnershipCase current,
        OwnershipCase forkPoint) =>
        ScriptTestOwnershipPolicy.Evaluate(
            Snapshot(current.Files),
            Snapshot(forkPoint.Files),
            Map(current),
            Map(forkPoint));

    private static OwnershipCase Case(params OwnershipFile[] files) => new(files);

    private static OwnershipFile Source(string path, string project, string content) =>
        new(path, content, project);

    private static ScribeTestMap Map(OwnershipCase testCase)
    {
        var sources = testCase.Files
            .Where(static file => file.Project is not null)
            .Select(static file =>
            {
                var project = file.Project!;
                return new TestMapSource(
                    file.Path,
                    file.Content,
                    project[..project.LastIndexOf('/')]);
            })
            .ToArray();
        var projects = testCase.Files
            .Where(static file => file.Project is not null)
            .ToDictionary(static file => file.Path, static file => file.Project!, StringComparer.Ordinal);
        return ScribeTestMapDeriver.DeriveSources(
            sources,
            [],
            compileProjectBySourcePath: projects);
    }

    private static RepositorySnapshot Snapshot(IEnumerable<OwnershipFile> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static file =>
            RawRepositoryEntry.FromText(file.Path, file.Content)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private sealed record OwnershipCase(IReadOnlyList<OwnershipFile> Files);

    private sealed record OwnershipFile(string Path, string Content, string? Project)
    {
        public static implicit operator OwnershipFile((string Path, string Content) file) =>
            new(file.Path, file.Content, null);
    }
}
