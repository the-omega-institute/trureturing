using System.Diagnostics;

namespace StrataLint.ArchitectureTests;

public sealed class OperationalEntrypointTests
{
    [Fact]
    public void RepositoryOperationalEntrypointsAreTrackedRegularFilesAndUnique()
    {
        var findings = OperationalEntrypointPolicy.InspectRepository(RepositoryLayout.FindRoot(), []);

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

                Assert.Empty(OperationalEntrypointPolicy.InspectRepository(repository, []));
            });
    }

    [Fact]
    public void ImplementationAbsentFromGitIndexIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

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

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains("does not delegate exactly", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void MissingHostContractSchemaDeclarationIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                var exception = Assert.Throws<InvalidDataException>(
                    () => OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "must declare host_contract_schema",
                    exception.Message,
                    StringComparison.Ordinal);
            },
            declareHostContractSchema: false);
    }

    [Fact]
    public void MissingLaunchdUnitsDeclarationIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                var exception = Assert.Throws<InvalidDataException>(
                    () => OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "must declare launchd_units",
                    exception.Message,
                    StringComparison.Ordinal);
            },
            declareLaunchdUnits: false);
    }

    [Fact]
    public void HostContractSchemaAbsentFromGitIndexIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                Git(repository, "rm", "--cached", "--", "ops/host-contract.schema");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "host contract schema is absent from the git index",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    [Fact]
    public void LaunchdUnitTemplateAbsentFromGitIndexIsRejected()
    {
        WithRepository(
            LaunchdOperations("synthetic"),
            repository =>
            {
                PrepareLaunchdUnit(repository, "synthetic", includeTemplate: false);

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "launchd unit synthetic template is absent from the git index",
                    finding.Message,
                    StringComparison.Ordinal);
            },
            launchdUnits: ["synthetic"]);
    }

    [Fact]
    public void HostContractSchemaSymlinkIsRejectedFromIndexMode()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                Git(repository, "rm", "--cached", "--", "ops/host-contract.schema");
                TrackSymlinkMode(repository, "ops/host-contract.schema");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains("host contract schema is a symlink", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void LaunchdUnitTemplateSymlinkIsRejectedFromIndexMode()
    {
        WithRepository(
            LaunchdOperations("synthetic"),
            repository =>
            {
                PrepareLaunchdUnit(repository, "synthetic", includeTemplate: false);
                TrackSymlinkMode(repository, ".fkst/launchd/synthetic.plist.in");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains("launchd unit synthetic template is a symlink", finding.Message, StringComparison.Ordinal);
            },
            launchdUnits: ["synthetic"]);
    }

    [Fact]
    public void LaunchdUnitWithoutRendererIsRejected()
    {
        WithRepository(
            LaunchdOperations("synthetic", includeRenderer: false),
            repository =>
            {
                PrepareLaunchdUnit(repository, "synthetic", includeRenderer: false);

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "launchd unit synthetic has no render operation synthetic-launcher-render",
                    finding.Message,
                    StringComparison.Ordinal);
            },
            launchdUnits: ["synthetic"]);
    }

    [Fact]
    public void LaunchdUnitWithoutCheckTargetIsRejected()
    {
        WithRepository(
            LaunchdOperations("synthetic"),
            repository =>
            {
                PrepareLaunchdUnit(repository, "synthetic", includeCheckTarget: false);

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "make target synthetic-launcher-check does not delegate exactly",
                    finding.Message,
                    StringComparison.Ordinal);
            },
            launchdUnits: ["synthetic"]);
    }

    [Fact]
    public void UntrackedLaunchdUnitAbsentFromOperationalInventoryIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                WriteFile(repository, ".fkst/launchd/synthetic.plist", "<plist/>\n");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains(
                    "launchd unit synthetic is absent from operational inventory",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    [Theory]
    [InlineData("local.fkst.synthetic.worker.plist")]
    [InlineData("synthetic_worker.plist")]
    [InlineData("SyntheticWorker.plist.in")]
    public void NoncanonicalLaunchdPlistCandidateIsRejected(string fileName)
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");
                WriteFile(repository, $".fkst/launchd/{fileName}", "<plist/>\n");

                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Equal($".fkst/launchd/{fileName}", finding.Path);
                Assert.Contains(
                    "noncanonical launchd plist candidate",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    [Fact]
    public void ExternalOperationalLaunchdMemberAbsentFromInventoryIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "ops/scripts/synthetic-maintenance.sh")],
            repository =>
            {
                TrackFile(repository, "ops/scripts/synthetic-maintenance.sh");

                var finding = Assert.Single(
                    OperationalEntrypointPolicy.InspectRepository(repository, ["worker"]));

                Assert.Contains(
                    "operational launchd unit worker is absent from operational inventory",
                    finding.Message,
                    StringComparison.Ordinal);
            });
    }

    [Fact]
    public void OperationNamingAHostLocalImplementationPathIsRejected()
    {
        WithRepository(
            [Operation("hourly-maintenance", "~/.fkst/synthetic-maintenance.sh")],
            repository =>
            {
                var finding = Assert.Single(OperationalEntrypointPolicy.InspectRepository(repository, []));

                Assert.Contains("declares a host-local path", finding.Message, StringComparison.Ordinal);
            });
    }

    private static void WithRepository(
        IReadOnlyList<string> operations,
        Action<string> assertion,
        bool declareHostContractSchema = true,
        bool declareLaunchdUnits = true,
        IReadOnlyList<string>? launchdUnits = null)
    {
        var root = Directory.CreateTempSubdirectory("stratalint-operational-entrypoint-").FullName;
        try
        {
            Git(root, "init", "--initial-branch=dev");
            var declarations = new List<string> { "schema_version = 3" };
            if (declareHostContractSchema)
            {
                declarations.Add("host_contract_schema = \"ops/host-contract.schema\"");
            }
            if (declareLaunchdUnits)
            {
                var unitIds = launchdUnits ?? [];
                declarations.Add(
                    $"launchd_units = [{string.Join(", ", unitIds.Select(static id => $"\"{id}\""))}]");
            }
            var inventory = string.Join("\n", declarations) + "\n\n" + string.Join("\n", operations);
            WriteFile(root, ".fkst/operations.toml", inventory);
            WriteFile(
                root,
                "Makefile",
                "hourly-maintenance:\n\t@/bin/bash ops/scripts/synthetic-maintenance.sh\n");
            WriteFile(root, "tests/synthetic-test.sh", "#!/usr/bin/env bash\nexit 0\n");
            WriteFile(root, "ops/host-contract.schema", "schema_version|1\n");
            Git(
                root,
                "add",
                "--",
                ".fkst/operations.toml",
                "Makefile",
                "ops/host-contract.schema",
                "tests/synthetic-test.sh");

            assertion(root);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    private static string Operation(
        string id,
        string implementation,
        string makeTarget = "hourly-maintenance") => $$"""
        [[operations]]
        id = "{{id}}"
        make_target = "{{makeTarget}}"
        implementation = "{{implementation}}"
        tests = ["tests/synthetic-test.sh"]
        external_tools = ["bash", "git"]
        """;

    private static IReadOnlyList<string> LaunchdOperations(
        string id,
        bool includeRenderer = true,
        bool includeCheck = true)
    {
        var operations = new List<string>();
        if (includeRenderer)
        {
            operations.Add(Operation(
                $"{id}-launcher-render",
                $".fkst/scripts/render-{id}-launcher.sh",
                $"{id}-launcher-render"));
        }
        if (includeCheck)
        {
            operations.Add(Operation(
                $"{id}-launcher-check",
                $".fkst/scripts/check-{id}-launcher.sh",
                $"{id}-launcher-check"));
        }
        return operations;
    }

    private static void PrepareLaunchdUnit(
        string repository,
        string id,
        bool includeTemplate = true,
        bool includeRenderer = true,
        bool includeCheck = true,
        bool includeCheckTarget = true)
    {
        if (includeTemplate) TrackFile(repository, $".fkst/launchd/{id}.plist.in");
        if (includeRenderer) TrackFile(repository, $".fkst/scripts/render-{id}-launcher.sh");
        if (includeCheck) TrackFile(repository, $".fkst/scripts/check-{id}-launcher.sh");

        var makefile = new List<string>
        {
            "hourly-maintenance:",
            "\t@/bin/bash ops/scripts/synthetic-maintenance.sh",
        };
        if (includeRenderer)
        {
            makefile.AddRange(
            [
                $"{id}-launcher-render:",
                $"\t@/bin/bash .fkst/scripts/render-{id}-launcher.sh",
            ]);
        }
        if (includeCheck && includeCheckTarget)
        {
            makefile.AddRange(
            [
                $"{id}-launcher-check:",
                $"\t@/bin/bash .fkst/scripts/check-{id}-launcher.sh",
            ]);
        }
        WriteFile(repository, "Makefile", string.Join('\n', makefile) + "\n");
        Git(repository, "add", "--", "Makefile");
    }

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
