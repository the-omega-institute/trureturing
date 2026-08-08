using System.Diagnostics;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class GitIndexRepositoryScanTests
{
    [Fact]
    public void IgnoredNestedRepositoryCopyIsExcludedFromAllCanonicalSourceScans()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var relativeFixtureRoot = $".claude/architecture-tests/ignored-repository-copy-{Guid.NewGuid():N}";
        var fixtureRoot = Path.Combine(
            repositoryRoot,
            relativeFixtureRoot.Replace('/', Path.DirectorySeparatorChar));

        try
        {
            Directory.CreateDirectory(fixtureRoot);
            AssertGitIgnored(repositoryRoot, relativeFixtureRoot);
            WriteCanonicalSourceCopies(repositoryRoot, fixtureRoot);

            var repositoryTests = new (string Name, Action Run)[]
            {
                (
                    nameof(TargetFrameworkSingleSourceTests.RepositoryReadsTargetFrameworkFromMsbuild),
                    new TargetFrameworkSingleSourceTests().RepositoryReadsTargetFrameworkFromMsbuild),
                (
                    nameof(TheoryIsolationTests.RepositoryProgramAndFormalSourcesHaveNoInternalTheoryReferences),
                    new TheoryIsolationTests().RepositoryProgramAndFormalSourcesHaveNoInternalTheoryReferences),
                (
                    nameof(RepositoryPathLiteralTests.RepositoryCSharpDoesNotCopyExistingRepositoryFilePaths),
                    new RepositoryPathLiteralTests().RepositoryCSharpDoesNotCopyExistingRepositoryFilePaths),
                (
                    nameof(CanonicalSourceDuplicationTests.RepositoryCSharpDoesNotCopyLedgerAtomizerIdsOutsideTheRegistry),
                    new CanonicalSourceDuplicationTests().RepositoryCSharpDoesNotCopyLedgerAtomizerIdsOutsideTheRegistry),
                (
                    nameof(CanonicalSourceDuplicationTests.RepositoryCSharpDoesNotCopyCanonicalBackfillTicketMappings),
                    new CanonicalSourceDuplicationTests().RepositoryCSharpDoesNotCopyCanonicalBackfillTicketMappings),
            };
            var failures = repositoryTests
                .Select(test => (test.Name, Exception: Record.Exception(test.Run)))
                .Where(static result => result.Exception is not null)
                .ToArray();

            Assert.True(
                failures.Length == 0,
                string.Join(
                    Environment.NewLine,
                    failures.Select(static failure =>
                        $"{failure.Name}: {failure.Exception!.Message}")));
        }
        finally
        {
            if (Directory.Exists(fixtureRoot))
            {
                Directory.Delete(fixtureRoot, recursive: true);
            }
        }
    }

    private static void WriteCanonicalSourceCopies(string repositoryRoot, string fixtureRoot)
    {
        var inventory = BackfillInventoryLoader.LoadDirectory(repositoryRoot);
        var ticket = inventory.RequireTickets().First();
        var atomizer = inventory.RequireDigestionSources()
            .Select(static source => source.Atomizer)
            .First(static id => id != AtomizerRegistry.NoAtomizerId);
        var targetFramework = string.Concat("net", "99.0");
        var theoryToken = string.Concat("P", "ZG");
        var source = $$"""
            var path = "{{BootstrapGate.SpecificationPath}}";
            var targetFramework = "{{targetFramework}}";
            var theory = "{{theoryToken}}";
            var ticket = new Dictionary<string, string>
            {
                ["{{ticket.Gid}}"] = "{{ticket.CaseId}}",
            };
            var atomizer = "{{atomizer}}";
            """;

        File.WriteAllText(Path.Combine(fixtureRoot, "CanonicalCopies.cs"), source);
    }

    private static void AssertGitIgnored(string repositoryRoot, string relativePath)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = repositoryRoot,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        startInfo.ArgumentList.Add("check-ignore");
        startInfo.ArgumentList.Add("--quiet");
        startInfo.ArgumentList.Add("--");
        startInfo.ArgumentList.Add(relativePath);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git check-ignore");
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();

        Assert.True(
            process.ExitCode == 0,
            $"synthetic nested repository must be gitignored: {error}");
    }
}
