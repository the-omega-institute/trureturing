using System.Diagnostics;

namespace StrataLint.ArchitectureTests;

public sealed class OperationalEntrypointTests
{
    [Fact]
    public void RepositoryOperationalEntrypointsAreTrackedRegularFilesAndUnique()
    {
        var findings = OperationalEntrypointPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding => $"{finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void TrackedRegularImplementationIsAccepted()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");

                Assert.Empty(OperationalEntrypointPolicy.InspectRepository(repository));
            });
    }

    [Fact]
    public void ImplementationAbsentFromGitIndexIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("absent from the git index", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void AbsoluteImplementationPathIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "/tmp/synthetic-maintenance.sh")],
            repository =>
            {
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("absolute path", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void ImplementationPathEscapingRepositoryRootIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "../synthetic-maintenance.sh")],
            repository =>
            {
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("escapes the repository root", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void SymlinkImplementationIsRejectedFromIndexMode()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackSymlinkMode(repository, "ops/scripts/synthetic-maintenance.sh");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("symlink", finding.Message, StringComparison.Ordinal);
                Assert.Contains("120000", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void DuplicateOperationIdWithTwoTrackedImplementationsIsRejected()
    {
        WithRepository(
            [
                Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh"),
                Operation("hourly-maintenance", "ops/scripts/other-maintenance.sh"),
            ],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                TrackFile(repository, "ops/scripts/other-maintenance.sh");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("claimed by multiple tracked implementations", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void ExactDuplicateOperationRowsAreRejected()
    {
        var operation = Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh");
        WithRepository(
            [operation, operation],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("duplicate operation id", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void DeclaredTestAbsentFromGitIndexIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                Git(repository, "rm", "--cached", "--", "tests/synthetic-test.sh");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains(
                    "declared test is absent from the git index",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    [Fact]
    public void MakeTargetDelegatingToDifferentImplementationIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                WriteFile(
                    repository,
                    "Makefile",
                    "hourly-maintenance:\n\t@/bin/bash ops/scripts/different-maintenance.sh\n");
                Git(repository, "add", "--", "Makefile");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository));

                Assert.Contains("does not delegate exactly", finding.Message, StringComparison.Ordinal);
            });
    }

    private static void WithRepository(
        IReadOnlyList<string> operations,
        Action<string> assertion)
    {
        var root = Directory.CreateTempSubdirectory("stratalint-operational-entrypoint-").FullName;
        try
        {
            Git(root, "init", "--initial-branch=dev");
            var inventory = "schema_version = 1\n\n" + string.Join("\n", operations);
            WriteFile(root, ".fkst/operations.toml", inventory);
            WriteFile(
                root,
                "Makefile",
                "hourly-maintenance:\n\t@/bin/bash ops/scripts/synthetic-maintenance.sh\n");
            WriteFile(root, "tests/synthetic-test.sh", "#!/usr/bin/env bash\nexit 0\n");
            Git(
                root,
                "add",
                "--",
                ".fkst/operations.toml",
                "Makefile",
                "tests/synthetic-test.sh");

            assertion(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static string Operation(string id, string implementation) => $$"""
        [[operations]]
        id = "{{id}}"
        make_target = "hourly-maintenance"
        implementation = "{{implementation}}"
        tests = ["tests/synthetic-test.sh"]
        external_tools = ["bash", "git"]
        """;

    private static void TrackFile(string repository, string path)
    {
        WriteFile(repository, path, "#!/usr/bin/env bash\nexit 0\n");
        Git(repository, "add", "--", path);
    }

    private static void TrackSymlinkMode(string repository, string path)
    {
        var blobSource = Path.Combine(repository, "symlink-target.txt");
        File.WriteAllText(blobSource, "hourly-maintenance-target\n");
        var oid = Git(repository, "hash-object", "-w", blobSource);
        Git(repository, "update-index", "--add", "--cacheinfo", $"120000,{oid},{path}");
    }

    private static void WriteFile(string repository, string path, string contents)
    {
        var fullPath = Path.Combine(repository, path.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, contents);
    }

    private static string Git(string repository, params string[] arguments)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = repository,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(
            process.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {process.ExitCode}: {error}");
        return output.TrimEnd('\r', '\n');
    }
}
